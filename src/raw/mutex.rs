use core::fmt::{self, Debug, Display, Formatter};

use crate::cfg::atomic::AtomicBool;
use crate::inner::raw as inner;
use crate::relax::{Relax, RelaxWait};

#[cfg(test)]
use crate::test::{Lock, LockNew, LockThen, LockWith, LockWithThen};

#[cfg(all(loom, test))]
use crate::loom::{Guard, GuardDeref, GuardDerefMut};
#[cfg(all(loom, test))]
use crate::test::{AsDeref, AsDerefMut};

// The inner type of the mutex node, with a boolean as the atomic data.
type MutexNodeInner = inner::MutexNode<AtomicBool>;

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
    /// use clhlock::raw::MutexNode;
    ///
    /// let node = MutexNode::new();
    /// ```
    #[must_use]
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: MutexNodeInner::new() }
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
impl<T: ?Sized, R> From<MutexGuard<'_, T, R>> for MutexNode {
    fn from(guard: MutexGuard<'_, T, R>) -> Self {
        guard.unlock()
    }
}

// The inner type of the mutex, with a boolean as the atomic data.
type MutexInner<T, R> = inner::Mutex<T, AtomicBool, RelaxWait<R>>;

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
/// use clhlock::raw::{self, MutexNode};
/// use clhlock::relax::Spin;
///
/// type Mutex<T> = raw::Mutex<T, Spin>;
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
pub struct Mutex<T: ?Sized, R> {
    pub(super) inner: MutexInner<T, R>,
}

// SAFETY: `inner::Mutex` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, R> Send for Mutex<T, R> {}
// SAFETY: `inner::Mutex` is `Sync` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, R> Sync for Mutex<T, R> {}

impl<T, R> Mutex<T, R> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use clhlock::raw;
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
    ///
    /// let mutex = Mutex::new(0);
    /// ```
    #[inline]
    pub fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
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
    /// use clhlock::raw;
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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
    pub fn lock(&self) -> MutexGuard<'_, T, R> {
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
    /// use clhlock::raw::{self, MutexNode};
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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
    pub fn lock_with(&self, node: MutexNode) -> MutexGuard<'_, T, R> {
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
    /// use clhlock::raw;
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
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
    /// use clhlock::raw::{self, MutexNode};
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        f(self.lock_with(node))
    }
}

impl<T: ?Sized, R> Mutex<T, R> {
    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use clhlock::raw::{self, MutexNode};
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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

impl<T: Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, R: Relax> Debug for Mutex<T, R> {
    /// Formats the mutex's value using the given formatter.
    ///
    /// This will lock the mutex to do so. If the lock is already held by the
    /// thread, calling this function will cause a deadlock.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, R> LockNew for Mutex<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWith for Mutex<T, R> {
    type Node = MutexNode;

    type Guard<'a>
        = MutexGuard<'a, T, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with(&self, node: Self::Node) -> Self::Guard<'_> {
        self.lock_with(node)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> Lock for Mutex<T, R> {
    fn lock(&self) -> Self::Guard<'_> {
        self.lock()
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWithThen for Mutex<T, R> {
    fn lock_with_then<F, Ret>(&self, node: Self::Node, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.lock_with_then(node, f)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockThen for Mutex<T, R> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.lock_then(f)
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for Mutex<T, R> {
    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

// The inner type of the mutex's guard, with a boolean as the atomic data.
type GuardInner<'a, T, R> = inner::MutexGuard<'a, T, AtomicBool, RelaxWait<R>>;

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
pub struct MutexGuard<'a, T: ?Sized, R> {
    inner: GuardInner<'a, T, R>,
}

// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, R> Send for MutexGuard<'_, T, R> {}
// SAFETY: `inner::MutexGuard` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Sync, R> Sync for MutexGuard<'_, T, R> {}

impl<T: ?Sized, R> MutexGuard<'_, T, R> {
    /// Unlocks the mutex and returns a node instance that can be reused by
    /// another locking operation.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::raw::{self, MutexNode};
    /// use clhlock::relax::Spin;
    ///
    /// type Mutex<T> = raw::Mutex<T, Spin>;
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
impl<'a, T: ?Sized, R> From<GuardInner<'a, T, R>> for MutexGuard<'a, T, R> {
    #[inline(always)]
    fn from(inner: GuardInner<'a, T, R>) -> Self {
        Self { inner }
    }
}

impl<T: ?Sized + Debug, R> Debug for MutexGuard<'_, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ?Sized + Display, R> Display for MutexGuard<'_, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, R> core::ops::Deref for MutexGuard<'_, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, R> core::ops::DerefMut for MutexGuard<'_, T, R> {
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
unsafe impl<T: ?Sized, R> crate::loom::Guard for MutexGuard<'_, T, R> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, R> AsDeref for MutexGuard<'_, T, R> {
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
impl<T: ?Sized, R> AsDerefMut for MutexGuard<'_, T, R> {
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

#[cfg(any(all(test, not(miri), not(loom)), all(miri, ignore_leaks)))]
mod test_leaks_expected {
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    use crate::raw::yields::{Mutex, MutexGuard};
    use crate::raw::MutexNode;

    fn assert_forget_guard<T, F>(f: F)
    where
        F: FnOnce(MutexGuard<i32>) -> T,
    {
        let (tx1, rx1) = channel();
        let (tx2, rx2) = channel();
        let data = Arc::new(Mutex::new(0));
        let handle = Arc::clone(&data);
        let node = MutexNode::new();
        let guard = data.lock_with(node);
        thread::spawn(move || {
            rx2.recv().unwrap();
            let node = MutexNode::new();
            let guard = handle.lock_with(node);
            core::mem::forget(guard);
            tx1.send(()).unwrap();
        });
        let _t = f(guard);
        tx2.send(()).unwrap();
        rx1.recv().unwrap();
        // NOTE: deadlocks.
        // let guard = data.lock();
        // assert_eq!(*guard, 0);
    }

    #[test]
    fn test_forget_guard_drop_predecessor() {
        assert_forget_guard(|guard| drop(guard));
    }

    #[test]
    #[allow(clippy::redundant_closure_for_method_calls)]
    fn test_foget_guard_unlock_predecessor() {
        assert_forget_guard(|guard| guard.unlock());
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::raw::yields::Mutex;

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }
}
