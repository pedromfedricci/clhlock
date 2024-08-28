use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use loom::cell::{ConstPtr, MutPtr, UnsafeCell};

/// A trait for guard types that hold exclusive access to the underlying data
/// behind Loom's [`UnsafeCell`].
///
/// # Safety
///
/// Must guarantee that an instance of the guard holds exclusive access to its
/// underlying data through all its lifetime.
pub unsafe trait Guard: Sized {
    /// The target type after dereferencing [`GuardDeref`] or [`GuardDerefMut`].
    type Target: ?Sized;

    /// Returns a shared reference to the underlying [`UnsafeCell`].
    fn get(&self) -> &UnsafeCell<Self::Target>;

    /// Get a Loom immutable pointer bounded by this guard lifetime.
    fn deref(&self) -> GuardDeref<'_, Self> {
        GuardDeref::new(self)
    }

    /// Get a Loom mutable pointer bounded by this guard lifetime.
    fn deref_mut(&self) -> GuardDerefMut<'_, Self> {
        GuardDerefMut::new(self)
    }
}

/// A Loom immutable pointer borrowed from a guard instance.
pub struct GuardDeref<'a, G: Guard> {
    ptr: ConstPtr<G::Target>,
    marker: PhantomData<(&'a G::Target, &'a G)>,
}

impl<G: Guard> GuardDeref<'_, G> {
    fn new(guard: &G) -> Self {
        let ptr = guard.get().get();
        Self { ptr, marker: PhantomData }
    }
}

impl<G: Guard> Deref for GuardDeref<'_, G> {
    type Target = G::Target;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A Loom mutable pointer borrowed from a guard instance.
pub struct GuardDerefMut<'a, G: Guard> {
    ptr: MutPtr<G::Target>,
    marker: PhantomData<(&'a G::Target, &'a G)>,
}

impl<G: Guard> GuardDerefMut<'_, G> {
    fn new(guard: &G) -> Self {
        let ptr = guard.get().get_mut();
        Self { ptr, marker: PhantomData }
    }
}

impl<G: Guard> Deref for GuardDerefMut<'_, G> {
    type Target = G::Target;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

impl<G: Guard> DerefMut for GuardDerefMut<'_, G> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

pub mod models {
    use core::array;

    use loom::sync::Arc;
    use loom::{model, thread};

    use crate::test::{Guard, LockWith};

    type Int = usize;
    const LOCKS: Int = 3;

    /// Increments a shared integer.
    fn inc<L: LockWith<Target = Int>>(lock: &Arc<L>) {
        lock.lock_with(|guard| *guard.deref_mut() += 1);
    }

    /// Get the shared integer.
    fn get<L: LockWith<Target = Int>>(lock: &Arc<L>) -> Int {
        lock.lock_with(|guard| *guard.deref())
    }

    /// Evaluates that concurrent `lock` calls will serialize all mutations
    /// against the shared data, therefore no data races.
    pub fn lock_join<L: LockWith<Target = Int> + 'static>() {
        model(|| {
            const RUNS: Int = LOCKS;
            let data = Arc::new(L::new(0));
            let handles: [_; RUNS] = array::from_fn(|_| {
                let data = Arc::clone(&data);
                thread::spawn(move || inc(&data))
            });
            for handle in handles {
                handle.join().unwrap();
            }
            let data = get(&data);
            assert_eq!(RUNS, data);
        });
    }
}
