use core::fmt::{self, Debug, Display, Formatter};

use crate::inner::raw as inner;
use crate::parking::park::{Park, ParkWait};
use crate::parking::parker::Parker;

#[cfg(test)]
use crate::test::{Lock, LockNew, LockThen, LockWith, LockWithThen};

#[cfg(all(loom, test))]
use crate::loom::{Guard, GuardDeref, GuardDerefMut};
#[cfg(all(loom, test))]
use crate::test::{AsDeref, AsDerefMut};

// The inner type of the mutex node, with a `futex` compatible atomic value.
type MutexNodeInner = inner::MutexNode<Parker>;

/// A locally-accessible handle to a heap allocated node for forming
/// waiting queue.
///
/// `MutexNode` is an opaque type that holds metadata for the [`Mutex`]'s
/// waiting queue. To acquire a CLH lock, an instance of queue node handle must
/// be consumed by the locking APIs to create a [`MutexGuard`] instance. Once
/// the locking thread is done with its critical section, it may reacquire a
/// node and reuse it as the backing allocation for another lock acquisition
/// through the [`unlock`] method of a `MutexGuard`.
///
/// See the [`lock_with`] method on [`Mutex`] for more information.
///
/// [`lock_with`]: Mutex::lock_with
/// [`unlock`]: MutexGuard::unlock
#[derive(Debug)]
#[repr(transparent)]
pub struct MutexNode {
    inner: MutexNodeInner,
}

// SAFETY: `inner::MutexNode` is `Send`.
unsafe impl Send for MutexNode {}
// SAFETY: `inner::MutexNode` is `Sync`.
unsafe impl Sync for MutexNode {}

impl MutexNode {
    /// Creates new `MutexNode` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use clhlock::parking::raw::MutexNode;
    ///
    /// let node = MutexNode::new();
    /// ```
    #[must_use]
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: inner::MutexNode::new() }
    }
}

#[cfg(not(tarpaulin_include))]
impl Default for MutexNode {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
impl<T: ?Sized, P> From<MutexGuard<'_, T, P>> for MutexNode {
    fn from(guard: MutexGuard<'_, T, P>) -> Self {
        guard.unlock()
    }
}

// The inner type of the mutex, with a `futext` compatible atomic value.
type MutexInner<T, P> = inner::Mutex<T, Parker, ParkWait<P>>;

pub struct Mutex<T: ?Sized, P> {
    pub(super) inner: MutexInner<T, P>,
}

// SAFETY: `inner::Mutex` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
// SAFETY: `inner::Mutex` is `Sync` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Sync for Mutex<T, P> {}

impl<T, P> Mutex<T, P> {
    #[inline]
    pub fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }
}

impl<T: ?Sized, P: Park> Mutex<T, P> {
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, T, P> {
        self.lock_with(MutexNode::new())
    }

    #[inline]
    pub fn lock_with(&self, node: MutexNode) -> MutexGuard<'_, T, P> {
        self.inner.lock_with(node.inner).into()
    }

    #[inline]
    pub fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        f(self.lock())
    }

    #[inline]
    pub fn lock_with_then<F, Ret>(&self, node: MutexNode, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        f(self.lock_with(node))
    }
}

impl<T: ?Sized, P> Mutex<T, P> {
    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use clhlock::parking::raw::{self, MutexNode};
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// let node = MutexNode::new();
    /// assert_eq!(*mutex.lock_with(node), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: Default, P> Default for Mutex<T, P> {
    /// Creates a `Mutex<T, P>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, P> From<T> for Mutex<T, P> {
    /// Creates a `Mutex<T, P>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, P: Park> Debug for Mutex<T, P> {
    /// Formats the mutex's value using the given formatter.
    ///
    /// This will lock the mutex to do so. If the lock is already held by the
    /// thread, calling this function will cause a deadlock.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P> LockNew for Mutex<T, P> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockWith for Mutex<T, P> {
    type Node = MutexNode;

    type Guard<'a>
        = MutexGuard<'a, T, P>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with(&self, node: Self::Node) -> Self::Guard<'_> {
        self.lock_with(node)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> Lock for Mutex<T, P> {
    fn lock(&self) -> Self::Guard<'_> {
        self.lock()
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockWithThen for Mutex<T, P> {
    fn lock_with_then<F, Ret>(&self, node: Self::Node, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        self.lock_with_then(node, f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockThen for Mutex<T, P> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        self.lock_then(f)
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, P> crate::test::LockData for Mutex<T, P> {
    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

// The inner type of the mutex's guard, with a `futex` compatible atomic value.
type GuardInner<'a, T, P> = inner::MutexGuard<'a, T, Parker, ParkWait<P>>;

#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, P> {
    inner: GuardInner<'a, T, P>,
}

// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Send for MutexGuard<'_, T, P> {}
// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Sync, P> Sync for MutexGuard<'_, T, P> {}

impl<T: ?Sized, P> MutexGuard<'_, T, P> {
    #[must_use]
    #[inline]
    pub fn unlock(self) -> MutexNode {
        let inner = self.inner.into_node();
        MutexNode { inner }
    }
}

#[doc(hidden)]
impl<'a, T: ?Sized, P> From<GuardInner<'a, T, P>> for MutexGuard<'a, T, P> {
    #[inline(always)]
    fn from(inner: GuardInner<'a, T, P>) -> Self {
        Self { inner }
    }
}

impl<T: ?Sized + Debug, P> Debug for MutexGuard<'_, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ?Sized + Display, P> Display for MutexGuard<'_, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, P> core::ops::Deref for MutexGuard<'_, T, P> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, P> core::ops::DerefMut for MutexGuard<'_, T, P> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
// SAFETY: A guard instance hold the lock locked, with exclusive access to the
// underlying data.
unsafe impl<T: ?Sized, P> crate::loom::Guard for MutexGuard<'_, T, P> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, P> AsDeref for MutexGuard<'_, T, P> {
    type Target = T;

    type Deref<'a>
        = GuardDeref<'a, Self>
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref(&self) -> Self::Deref<'_> {
        self.get_ref()
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, P> AsDerefMut for MutexGuard<'_, T, P> {
    type DerefMut<'a>
        = GuardDerefMut<'a, Self>
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref_mut(&mut self) -> Self::DerefMut<'_> {
        self.get_mut()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::raw::yields::Mutex;
    use crate::test::tests;

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<Mutex<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
    }

    #[test]
    fn test_guard_debug_display() {
        tests::test_guard_debug_display::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_debug() {
        tests::test_mutex_debug::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_from() {
        tests::test_mutex_from::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_default() {
        tests::test_mutex_default::<Mutex<_>>();
    }

    #[test]
    fn test_get_mut() {
        tests::test_get_mut::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<Mutex<_>, Mutex<_>>();
    }

    #[test]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<Mutex<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<Mutex<_>>();
    }

    #[test]
    fn test_guard_into_node() {
        tests::test_guard_into_node::<Mutex<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::parking::raw::yields::Mutex;

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }
}
