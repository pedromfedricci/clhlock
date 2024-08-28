#[cfg(all(not(loom), test))]
pub use core::ops::DerefMut as Guard;

#[cfg(all(loom, test))]
pub use crate::loom::Guard;

/// A trait for lock types that can hold user defined values.
pub trait LockNew {
    /// The type of the value this lock holds.
    type Target: ?Sized;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized;
}

/// A trait for lock types that can run closures against the guard.
pub trait LockWith: LockNew {
    /// The guard type that holds exclusive access to the underlying data.
    type Guard<'a>: Guard<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Acquires a mutex and then runs the closure against its guard.
    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Self::Guard<'_>) -> Ret;
}

/// A trait for lock types that can return either the underlying value (by
// consuming the mutex) or a exclusive reference to it.
#[cfg(not(loom))]
pub trait LockData: LockNew {
    /// Returns a mutable reference to the underlying data.
    fn get_mut(&mut self) -> &mut Self::Target;
}

#[cfg(all(not(loom), test))]
pub mod tests {
    // Test suite from the Rust's Mutex implementation with minor modifications
    // since the API is not compatible with this crate implementation and some
    // new tests as well.
    //
    // Copyright 2014 The Rust Project Developers.
    //
    // Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
    // http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
    // <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
    // option. This file may not be copied, modified, or distributed
    // except according to those terms.

    use std::fmt::{Debug, Display};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    use super::{LockData, LockWith};

    type Int = u32;

    #[derive(Eq, PartialEq, Debug)]
    pub struct NonCopy(u32);

    const ITERS: Int = 1000;
    const CONCURRENCY: Int = 3;
    const EXPECTED_VALUE: Int = ITERS * CONCURRENCY * 2;

    fn inc<L: LockWith<Target = Int>>(data: &Arc<L>) {
        data.lock_with(|mut guard| *guard += 1);
    }

    fn inc_for<L: LockWith<Target = Int>>(data: &Arc<L>) {
        for _ in 0..ITERS {
            inc::<L>(data);
        }
    }

    fn lots_and_lots<L>(f: fn(&Arc<L>)) -> Int
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let data = Arc::new(L::new(0));
        let (tx, rx) = channel();
        for _ in 0..CONCURRENCY {
            let data1 = Arc::clone(&data);
            let tx2 = tx.clone();
            thread::spawn(move || {
                f(&data1);
                tx2.send(()).unwrap();
            });
            let data2 = Arc::clone(&data);
            let tx2 = tx.clone();
            thread::spawn(move || {
                f(&data2);
                tx2.send(()).unwrap();
            });
        }

        drop(tx);
        for _ in 0..2 * CONCURRENCY {
            rx.recv().unwrap();
        }
        data.lock_with(|guard| *guard)
    }

    pub fn lots_and_lots_lock<L>()
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let value = lots_and_lots(inc_for::<L>);
        assert_eq!(value, EXPECTED_VALUE);
    }

    pub fn smoke<L>()
    where
        L: LockWith<Target = Int>,
    {
        let mutex = L::new(1);
        mutex.lock_with(|guard| drop(guard));
        mutex.lock_with(|guard| drop(guard));
    }

    pub fn test_guard_debug_display<L>()
    where
        L: LockWith<Target = Int>,
        for<'a> <L as LockWith>::Guard<'a>: Debug + Display,
    {
        let data = 42;
        let mutex = L::new(data);
        mutex.lock_with(|guard| {
            assert_eq!(format!("{data:?}"), format!("{guard:?}"));
            assert_eq!(format!("{data}"), format!("{guard}"));
        });
    }

    pub fn test_mutex_debug<L>()
    where
        L: LockWith<Target = Int> + Debug + Send + Sync + 'static,
    {
        let data = 42;
        let mutex = Arc::new(L::new(data));
        let msg = format!("Mutex {{ data: {data:?} }}");
        assert_eq!(msg, format!("{mutex:?}"));
    }

    pub fn test_mutex_default<L>()
    where
        L: LockData<Target = Int> + Default,
    {
        let mut mutex: L = Default::default();
        assert_eq!(u32::default(), *mutex.get_mut());
    }

    pub fn test_mutex_from<L>()
    where
        L: LockData<Target = Int> + From<Int>,
    {
        let data = 42;
        let mut mutex = L::from(data);
        assert_eq!(data, *mutex.get_mut());
    }

    pub fn test_get_mut<M>()
    where
        M: LockData<Target = NonCopy>,
    {
        let mut mutex = M::new(NonCopy(10));
        *mutex.get_mut() = NonCopy(20);
        assert_eq!(*mutex.get_mut(), NonCopy(20));
    }

    pub fn test_lock_arc_nested<L1, L2>()
    where
        L1: LockWith<Target = Int>,
        L2: LockWith<Target = Arc<L1>> + Send + Sync + 'static,
    {
        // Tests nested locks and access
        // to underlying data.
        let arc = Arc::new(L1::new(1));
        let arc2 = Arc::new(L2::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let val = arc2.lock_with(|arc2| arc2.lock_with(|g| *g));
            assert_eq!(val, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    pub fn test_acquire_more_than_one_lock<L>()
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let (tx, rx) = channel();
        for _ in 0..4 {
            let tx2 = tx.clone();
            let c_arc = Arc::clone(&arc);
            let _t = thread::spawn(move || {
                c_arc.lock_with(|_g| {
                    let mutex = L::new(1);
                    mutex.lock_with(|_g| ());
                });
                tx2.send(()).unwrap();
            });
        }
        drop(tx);
        for _ in 0..4 {
            rx.recv().unwrap();
        }
    }

    pub fn test_lock_arc_access_in_unwind<L>()
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder<T: LockWith<Target = Int>> {
                i: Arc<T>,
            }
            impl<T: LockWith<Target = Int>> Drop for Unwinder<T> {
                fn drop(&mut self) {
                    self.i.lock_with(|mut g| *g += 1);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = arc.lock_with(|g| *g);
        assert_eq!(value, 2);
    }

    pub fn test_lock_unsized<L>()
    where
        L: LockWith<Target = [Int; 3]>,
    {
        let lock: &L = &L::new([1, 2, 3]);
        {
            lock.lock_with(|mut g| {
                g[0] = 4;
                g[2] = 5;
            });
        }
        let comp: &[Int] = &[4, 2, 5];
        lock.lock_with(|g| assert_eq!(&*g, comp));
    }
}
