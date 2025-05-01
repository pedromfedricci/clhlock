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

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can created via a [`new`] constructor. Each mutex has a type parameter
/// which represents the data that it is protecting. The data can only be accessed
/// through the RAII guards returned by the [`lock`]  and [`lock_with`] methods,
/// but also as the closure parameter for [`lock_with_then`] method, which
/// guarantees that the data is only ever accessed when the mutex is locked.
///
/// # Examples
///
/// ```
/// use std::sync::Arc;
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// use clhlock::parking::raw::{self, MutexNode};
/// use clhlock::parking::park::SpinThenPark;
///
/// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
///
/// const N: usize = 10;
///
/// // Spawn a few threads to increment a shared variable (non-atomically), and
/// // let the main thread know once all increments are done.
/// //
/// // Here we're using an Arc to share memory among threads, and the data inside
/// // the Arc is protected with a mutex.
/// let data = Arc::new(Mutex::new(0));
///
/// let (tx, rx) = channel();
/// for _ in 0..N {
///     let (data, tx) = (data.clone(), tx.clone());
///     thread::spawn(move || {
///         // A queue node must be consumed.
///         let node = MutexNode::new();
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         let mut data = data.lock_with(node);
///         *data += 1;
///         if *data == N {
///             tx.send(()).unwrap();
///         }
///         // the lock is unlocked here when `data` goes out of scope.
///     });
/// }
///
/// rx.recv().unwrap();
/// ```
/// [`new`]: Mutex::new
/// [`lock`]: Mutex::lock
/// [`lock_with`]: Mutex::lock_with
/// [`lock_with_then`]: Mutex::lock_with_then
pub struct Mutex<T: ?Sized, P> {
    pub(super) inner: MutexInner<T, P>,
}

// SAFETY: `inner::Mutex` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
// SAFETY: `inner::Mutex` is `Sync` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Sync for Mutex<T, P> {}

impl<T, P> Mutex<T, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use clhlock::parking::raw;
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Mutex::new(0);
    /// ```
    #[inline]
    pub fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }
}

impl<T: ?Sized, P: Park> Mutex<T, P> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// This function transparently allocates a [`MutexNode`] for each call,
    /// and so it will not reuse the same node for other calls. Consider calling
    /// [`lock_with`] if you want to reuse node allocations returned by the
    /// [`MutexGuard`]'s [`unlock`] method.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::parking::raw;
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     *c_mutex.lock() = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    /// [`lock_with`]: Mutex::lock_with
    /// [`unlock`]: MutexGuard::unlock
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, T, P> {
        self.lock_with(MutexNode::new())
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// To acquire a CLH lock through this function, it's also required to
    /// consume queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::parking::raw::{self, MutexNode};
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let node = MutexNode::new();
    ///     *c_mutex.lock_with(node) = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let node = MutexNode::new();
    /// assert_eq!(*mutex.lock_with(node), 10);
    /// ```
    #[inline]
    pub fn lock_with(&self, node: MutexNode) -> MutexGuard<'_, T, P> {
        self.inner.lock_with(node.inner).into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function transparently allocates a [`MutexNode`] for each call,
    /// and so it will not reuse the same node for other calls. Consider calling
    /// [`lock_with_then`] if you want to reuse node allocations returned by the
    /// [`MutexGuard`]'s [`unlock`] method.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::parking::raw;
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_then(|mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_then(|guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use clhlock::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_then(|guard| &*guard);
    /// ```
    /// [`lock_with_then`]: Mutex::lock_with_then
    /// [`unlock`]: MutexGuard::unlock
    #[inline]
    pub fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        f(self.lock())
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// To acquire a CLH lock through this function, it's also required to
    /// consume queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::parking::raw::{self, MutexNode};
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let node = MutexNode::new();
    ///     c_mutex.lock_with_then(node, |mut data| *data = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let node = MutexNode::new();
    /// assert_eq!(mutex.lock_with_then(node, |data| *data), 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use clhlock::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(1);
    /// let node = MutexNode::new();
    /// let borrow = mutex.lock_with_then(node, |data| &*data);
    /// ```
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

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is returned by the [`lock`] method on [`Mutex`]. It is also
/// given as closure parameter by the [`lock_with`] method.
///
/// A guard may be explicitly unlocked by the [`unlock`] method, which returns
/// a instance of [`MutexNode`], that may be reused by other locking operations
/// that require taking ownership over the nodes.
///
/// [`Deref`]: core::ops::Deref
/// [`DerefMut`]: core::ops::DerefMut
/// [`lock`]: Mutex::lock
/// [`lock_with`]: Mutex::lock_with
/// [`unlock`]: MutexGuard::unlock
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, P> {
    inner: GuardInner<'a, T, P>,
}

// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Send for MutexGuard<'_, T, P> {}
// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Sync, P> Sync for MutexGuard<'_, T, P> {}

impl<T: ?Sized, P> MutexGuard<'_, T, P> {
    /// Unlocks the mutex and returns a node instance that can be reused by
    /// another locking operation.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::parking::raw::{self, MutexNode};
    /// use clhlock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    ///
    /// let mut guard = mutex.lock_with(node);
    /// *guard += 1;
    ///
    /// node = guard.unlock();
    /// assert_eq!(*mutex.lock_with(node), 1);
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
    use crate::parking::raw::{immediate, yields};
    use crate::test::tests;

    type Mutex<T> = immediate::Mutex<T>;

    #[test]
    fn lots_and_lots_lock_yield_backoff_then_park() {
        tests::lots_and_lots_lock::<yields::backoff::Mutex<_>>();
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
