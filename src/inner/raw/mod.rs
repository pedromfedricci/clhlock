use alloc::boxed::Box;

use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::ptr::NonNull;
use core::sync::atomic::Ordering::{AcqRel, Acquire};

use crate::cfg::atomic::{fence, AtomicPtr, UnsyncLoad};
use crate::cfg::cell::{Cell, CellNullMut, UnsafeCell, UnsafeCellWith};
use crate::lock::{Lock, Wait};

/// The heap allocated queue node, which is managed by the [`MutexNode`] type.
#[derive(Debug)]
struct MutexNodeInner<L> {
    prev: Cell<*mut Self>,
    lock: L,
}

impl<L: Lock> MutexNodeInner<L> {
    /// Creates a new, locked and core based inner node (const).
    #[cfg(not(all(loom, test)))]
    const fn locked() -> Self {
        let prev = Cell::NULL_MUT;
        let lock = Lock::LOCKED;
        Self { prev, lock }
    }

    /// Creates a new, locked and loom based inner node (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self {
        let prev = Cell::null_mut();
        let lock = Lock::locked();
        Self { prev, lock }
    }

    /// Creates a new, unlocked and core based inner node (const).
    #[cfg(not(all(loom, test)))]
    const fn unlocked() -> Self {
        let prev = Cell::NULL_MUT;
        let lock = Lock::UNLOCKED;
        Self { prev, lock }
    }

    /// Creates a new, unlocked and loom based inner node (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn unlocked() -> Self {
        let prev = Cell::null_mut();
        let lock = Lock::unlocked();
        Self { prev, lock }
    }

    /// Change the inner lock state to `locked`.
    fn lock(&mut self) {
        self.lock.lock();
    }
}

/// A owning pointer that manages the heap allocated queue node.
#[derive(Debug)]
#[repr(transparent)]
pub struct MutexNode<L> {
    inner: NonNull<MutexNodeInner<L>>,
}

// SAFETY: Public APIs that mutate state require exclusive references.
unsafe impl<L> Send for MutexNode<L> {}
unsafe impl<L> Sync for MutexNode<L> {}

impl<L> MutexNode<L> {
    /// Creates a new `MutexNode` instance from a raw pointer.
    ///
    /// # Safety
    ///
    /// The pointer is required to be non-null, it must have been allocated
    /// with the [memory layout] used by Box, and this function mut not be
    /// called twice on the same raw pointer.
    ///
    /// [memory layout]: https://doc.rust-lang.org/alloc/boxed/index.html#memory-layout
    const unsafe fn from_ptr(ptr: *mut MutexNodeInner<L>) -> Self {
        // SAFETY: Caller guaranteed that `ptr` is non-null.
        Self { inner: unsafe { NonNull::new_unchecked(ptr) } }
    }

    /// Sets the inner pointer of this node.
    ///
    /// The allocation pointed by the previous inner pointer will not be freed
    /// when calling this function. It is expected that a successor node will
    /// be responsible to do so. See: [`MutexNode::from_ptr`].
    ///
    /// # Safety
    ///
    /// The pointer is required to be non-null, it must have been allocated
    /// with the [memory layout] used by Box, and this function mut not be
    /// called twice on the same raw pointer.
    ///
    /// [memory layout]: https://doc.rust-lang.org/alloc/boxed/index.html#memory-layout
    unsafe fn set(&mut self, ptr: *mut MutexNodeInner<L>) {
        // SAFETY: Caller guaranteed that `ptr` is non-null.
        self.inner = unsafe { NonNull::new_unchecked(ptr) };
    }
}

impl<L: Lock> MutexNode<L> {
    /// Creates new, locked `MutexNode` instance.
    pub fn new() -> Self {
        Self::locked()
    }

    /// Creates a new, locked `MutexNode` instance.
    fn locked() -> Self {
        let node = MutexNodeInner::locked();
        let ptr = Box::into_raw(Box::new(node));
        // SAFETY: The returned `ptr` is guarenteed to be properly aligned and
        // non-null by the `Box::into_raw` function contract.
        let inner = unsafe { NonNull::new_unchecked(ptr) };
        Self { inner }
    }

    /// Creates a new, heap allocated `MutexNodeInner` and returns a leaked,
    /// raw pointer to it.
    ///
    /// Caller is responsible for freeing the node.
    fn unlocked() -> *mut MutexNodeInner<L> {
        let node = MutexNodeInner::unlocked();
        Box::into_raw(Box::new(node))
    }
}

impl<L> Drop for MutexNode<L> {
    fn drop(&mut self) {
        let inner = self.inner.as_ptr();
        // SAFETY: The memory was allocated through the Box API, therefore it
        // fulfills the layout requirements. The pointer is guaranteed to not
        // be null, since the tail is initialized with a valid allocation, and
        // all tail updates point to valid, heap allocated nodes. The drop call
        // is only ever run once for any value, and this instance is the only
        // pointer to this heap allocated node at drop call time.
        drop(unsafe { Box::from_raw(inner) });
    }
}

#[cfg(not(tarpaulin_include))]
impl<L: Lock> Default for MutexNode<L> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive implementing the CLH lock protocol, useful for
/// protecting shared data.
pub struct Mutex<T: ?Sized, L, W> {
    tail: AtomicPtr<MutexNodeInner<L>>,
    wait: PhantomData<W>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, L, W> Send for Mutex<T, L, W> {}
unsafe impl<T: ?Sized + Send, L, W> Sync for Mutex<T, L, W> {}

impl<T, L: Lock, W> Mutex<T, L, W> {
    /// Creates a new mutex in an unlocked state ready for use.
    pub fn new(value: T) -> Self {
        let initial = MutexNode::unlocked();
        let tail = AtomicPtr::new(initial);
        let data = UnsafeCell::new(value);
        Self { tail, data, wait: PhantomData }
    }
}

impl<T: ?Sized, L: Lock, W: Wait> Mutex<T, L, W> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    pub fn lock_with(&self, mut node: MutexNode<L>) -> MutexGuard<'_, T, L, W> {
        // SAFETY: The inner pointer always points to valid nodes allocations
        // and we have exclusive access over the node since it has not been
        // added to the waiting queue yet.
        unsafe { node.inner.as_mut() }.lock();
        let pred = self.tail.swap(node.inner.as_ptr(), AcqRel);
        // SAFETY: The inner pointer always points to valid nodes allocations.
        unsafe { node.inner.as_ref() }.prev.set(pred);
        // SAFETY: The predecessor is guaranteed to be not null, since the tail
        // is initialized with a valid allocation, and all tail updates point
        // to valid, heap allocated nodes that outlive the predecessor thread.
        unsafe { &(*pred).lock }.wait_lock_relaxed::<W>();
        fence(Acquire);
        MutexGuard::new(self, node)
    }
}

impl<T: ?Sized, L, W> Drop for Mutex<T, L, W> {
    fn drop(&mut self) {
        let tail = self.tail.load_unsynced();
        // SAFETY: The memory was allocated through the Box API, therefore it
        // fulfills the layout requirements. The pointer is guaranteed to not
        // be null, since the tail is initialized with a valid allocation, and
        // all tail updates point to valid, heap allocated nodes. The drop call
        // is only ever run once for any value, and this instance is the only
        // pointer to this heap allocated node at drop call time.
        drop(unsafe { MutexNode::from_ptr(tail) });
    }
}

impl<T: ?Sized, L, W> Mutex<T, L, W> {
    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }
}

impl<T: ?Sized + Debug, L: Lock, W: Wait> Debug for Mutex<T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let node = MutexNode::new();
        let mut d = f.debug_struct("Mutex");
        self.lock_with(node).with(|data| d.field("data", &data));
        d.finish()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, L: Lock, W> {
    lock: &'a Mutex<T, L, W>,
    head: MutexNode<L>,
}

// Rust's `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// impl is safe to be Send. Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Send, L: Lock, W> Send for MutexGuard<'_, T, L, W> {}
unsafe impl<T: ?Sized + Sync, L: Lock, W> Sync for MutexGuard<'_, T, L, W> {}

impl<'a, T: ?Sized, L: Lock, W> MutexGuard<'a, T, L, W> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, L, W>, head: MutexNode<L>) -> Self {
        Self { lock, head }
    }

    /// Runs `f` against a shared reference pointing to the underlying data.
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }

    /// Unlocks the mutex and returns a node instance that can be reused by
    /// another locking operation.
    ///
    /// Consumes the guard without calling `drop`.
    #[must_use]
    pub fn into_node(mut self) -> MutexNode<L> {
        // SAFETY: We are only ever calling unlock once, since we "forget" the
        // guard, therefore the guard's `drop` call will not be called.
        unsafe { self.unlock() }
        let inner = self.head.inner;
        core::mem::forget(self);
        MutexNode { inner }
    }

    /// Unlocks the mutex associated with this guard.
    ///
    /// # Safety
    ///
    /// This function mut not be called twice over the same `self` reference.
    unsafe fn unlock(&mut self) {
        // SAFETY: The inner pointer always points to valid nodes allocations.
        let inner = unsafe { self.head.inner.as_ref() };
        let pred = inner.prev.get();
        inner.lock.notify_release();
        // SAFETY: The memory was allocated through the Box API, therefore it
        // fulfills the layout requirements. The pointer is guaranteed to not
        // be null, since the tail is initialized with a valid allocation, and
        // all tail updates point to valid, heap allocated nodes. The caller
        // guaranteed that this function is only ever called once over the same
        // self reference.
        unsafe { self.head.set(pred) };
    }
}

impl<'a, T: ?Sized, L: Lock, W> Drop for MutexGuard<'a, T, L, W> {
    #[inline]
    fn drop(&mut self) {
        // The drop call is only ever run once for any value, and this instance
        // is the only pointer to this heap allocated node at drop call time.
        unsafe { self.unlock() }
    }
}

impl<'a, T: ?Sized + Debug, L: Lock, W> Debug for MutexGuard<'a, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<'a, T: ?Sized + Display, L: Lock, W> Display for MutexGuard<'a, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, W> core::ops::Deref for MutexGuard<'a, T, L, W> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, W> core::ops::DerefMut for MutexGuard<'a, T, L, W> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, L: Lock, W> crate::loom::Guard for MutexGuard<'_, T, L, W> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
