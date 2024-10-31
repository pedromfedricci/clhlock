pub use core::ops::{Deref, DerefMut};

/// A trait for convertion from `&Self` to a type that implements the [`Deref`]
/// trait.
pub trait AsDeref {
    /// The type of the value that `Self::Deref` dereferences to.
    type Target: ?Sized;

    /// The type that implements [`Deref`] trait.
    type Deref<'a>: Deref<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Returns a instance of the type that implements the [`Deref`] trait.
    fn as_deref(&self) -> Self::Deref<'_>;
}

/// A trait for convertion from `&mut Self` to a type that implements the
/// [`DerefMut`] trait.
pub trait AsDerefMut: AsDeref {
    /// The type that implements [`DerefMut`] trait.
    type DerefMut<'a>: DerefMut<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Returns a instance of the type that implements the [`DerefMut`] trait.
    fn as_deref_mut(&mut self) -> Self::DerefMut<'_>;
}

/// A trait for lock types that can hold user defined values.
pub trait LockNew {
    /// The type of the value this lock holds.
    type Target: ?Sized;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized;
}

/// A trait for lock types that can run closures against the protected data.
pub trait LockThen: LockNew {
    /// A `guard` has access to a type that can can give shared and exclusive
    /// references to the protected data.
    type Guard<'a>: AsDerefMut<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Acquires a mutex and then runs the closure against the protected data.
    fn lock_then<F, Ret>(&self, f: F) -> Ret
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

// Trivial implementation of `AsDeref` for `T` where `T: Deref`.
impl<T: Deref> AsDeref for T {
    type Target = <Self as Deref>::Target;

    type Deref<'a> = &'a <Self as Deref>::Target
    where
        Self: 'a;

    fn as_deref(&self) -> Self::Deref<'_> {
        self
    }
}

// Trivial implementation of `AsDerefMut` for `T` where `T: DerefMut`.
impl<T: DerefMut> AsDerefMut for T {
    type DerefMut<'a> = &'a mut <Self as Deref>::Target
    where
        Self: 'a;

    fn as_deref_mut(&mut self) -> Self::DerefMut<'_> {
        self
    }
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

    use super::{AsDeref, AsDerefMut, LockData, LockThen};

    type Int = u32;

    #[derive(Eq, PartialEq, Debug)]
    pub struct NonCopy(u32);

    const ITERS: Int = 1000;
    const CONCURRENCY: Int = 3;
    const EXPECTED_VALUE: Int = ITERS * CONCURRENCY * 2;

    fn inc<L: LockThen<Target = Int>>(data: &Arc<L>) {
        data.lock_then(|mut data| *data.as_deref_mut() += 1);
    }

    fn inc_for<L: LockThen<Target = Int>>(data: &Arc<L>) {
        for _ in 0..ITERS {
            inc::<L>(data);
        }
    }

    fn lots_and_lots<L>(f: fn(&Arc<L>)) -> Int
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
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
        data.lock_then(|data| *data.as_deref())
    }

    pub fn lots_and_lots_lock<L>()
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let value = lots_and_lots(inc_for::<L>);
        assert_eq!(value, EXPECTED_VALUE);
    }

    pub fn smoke<L>()
    where
        L: LockThen<Target = Int>,
    {
        let mutex = L::new(1);
        mutex.lock_then(|guard| drop(guard));
        mutex.lock_then(|guard| drop(guard));
    }

    pub fn test_guard_debug_display<L>()
    where
        L: LockThen<Target = Int>,
        for<'a> <L as LockThen>::Guard<'a>: Debug + Display,
    {
        let value = 42;
        let mutex = L::new(value);
        mutex.lock_then(|data| {
            assert_eq!(format!("{value:?}"), format!("{data:?}"));
            assert_eq!(format!("{value}"), format!("{data}"));
        });
    }

    pub fn test_mutex_debug<L>()
    where
        L: LockThen<Target = Int> + Debug + Send + Sync + 'static,
    {
        let value = 42;
        let mutex = Arc::new(L::new(value));
        let msg = format!("Mutex {{ data: {value:?} }}");
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
        let value = 42;
        let mut mutex = L::from(value);
        assert_eq!(value, *mutex.get_mut());
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
        L1: LockThen<Target = Int>,
        L2: LockThen<Target = Arc<L1>> + Send + Sync + 'static,
    {
        // Tests nested locks and access
        // to underlying data.
        let arc = Arc::new(L1::new(1));
        let arc2 = Arc::new(L2::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let val = arc2.lock_then(|arc2| {
                let deref = arc2.as_deref();
                deref.lock_then(|d| *d.as_deref())
            });
            assert_eq!(val, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    pub fn test_acquire_more_than_one_lock<L>()
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let (tx, rx) = channel();
        for _ in 0..4 {
            let tx2 = tx.clone();
            let c_arc = Arc::clone(&arc);
            let _t = thread::spawn(move || {
                c_arc.lock_then(|_d| {
                    let mutex = L::new(1);
                    mutex.lock_then(|_g| ());
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
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder<T: LockThen<Target = Int>> {
                i: Arc<T>,
            }
            impl<T: LockThen<Target = Int>> Drop for Unwinder<T> {
                fn drop(&mut self) {
                    self.i.lock_then(|mut d| *d.as_deref_mut() += 1);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = arc.lock_then(|d| *d.as_deref());
        assert_eq!(value, 2);
    }

    pub fn test_lock_unsized<L>()
    where
        L: LockThen<Target = [Int; 3]>,
    {
        let lock: &L = &L::new([1, 2, 3]);
        {
            lock.lock_then(|mut d| {
                d.as_deref_mut()[0] = 4;
                d.as_deref_mut()[2] = 5;
            });
        }
        let comp: &[Int] = &[4, 2, 5];
        lock.lock_then(|d| assert_eq!(&*d.as_deref(), comp));
    }
}
