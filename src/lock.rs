use core::sync::atomic::Ordering::{Relaxed, Release};

use crate::cfg::atomic::AtomicBool;
use crate::relax::Relax;

/// A `Lock` is some arbitrary data type used by a lock implementation to
/// manage the state of the lock.
pub trait Lock {
    /// Creates a new locked `Lock` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const LOCKED: Self;

    /// Creates a new unlocked `Lock` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const UNLOCKED: Self;

    /// Creates a new locked `Lock` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn locked() -> Self;

    /// Creates a new unlocked `Lock` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn unlocked() -> Self;

    /// Changes the lock state to `locked` through an exclusive reference.
    fn lock(&mut self);

    /// Blocks the thread untill the lock is acquired, applies some arbitrary
    /// waiting policy while the lock is still on hold somewhere else.
    ///
    /// The lock is loaded with a relaxed ordering.
    fn wait_lock_relaxed<W: Wait>(&self);

    /// Changes the state of the lock and, possibly, notifies that change
    /// to some other interested party.
    fn notify_release(&self);
}

/// The waiting policy that should be applied while the lock state has not
/// reached some target state.
pub trait Wait {
    /// The relax operation that will be excuted during lock waiting loops.
    type LockRelax: Relax;
}

impl Lock for AtomicBool {
    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const LOCKED: Self = Self::new(true);

    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const UNLOCKED: Self = Self::new(false);

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self {
        Self::new(true)
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn unlocked() -> Self {
        Self::new(false)
    }

    #[cfg(not(all(loom, test)))]
    fn lock(&mut self) {
        *self = Self::LOCKED;
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn lock(&mut self) {
        *self = Self::locked();
    }

    fn wait_lock_relaxed<W: Wait>(&self) {
        // Block the thread with a relaxed loop until the load returns `false`,
        // indicating that the lock was handed off to the current thread.
        let mut relax = W::LockRelax::new();
        while self.load(Relaxed) {
            relax.relax();
        }
    }

    fn notify_release(&self) {
        self.store(false, Release);
    }
}
