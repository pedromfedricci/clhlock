use core::fmt::{self, Debug, Display, Formatter};
use core::ops::{Deref, DerefMut};

use crate::cfg::atomic::AtomicBool;
use crate::inner::raw as inner;
use crate::relax::{Relax, RelaxWait};

#[cfg(test)]
use crate::test::{LockNew, LockWith};

/// A locally-accessible handle to a heap allocated node for forming
/// waiting queue.
///
/// `MutexNode` is an opaque type that holds metadata for the [`Mutex`]'s
/// waiting queue. To acquire a CLH lock, an instance of queue node handle must
/// be reachable and mutably borrowed for the duration of some associated
/// [`MutexGuard`]. Once the guard is dropped, the node handle can be reused as
/// the backing allocation for another lock acquisition. See the [`lock`] method
/// on [`Mutex`].
///
/// The inner
///
/// [`lock`]: Mutex::lock
#[repr(transparent)]
#[derive(Debug)]
pub struct MutexNode {
    inner: inner::MutexNode<AtomicBool>,
}

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
        Self { inner: inner::MutexNode::new() }
    }
}

#[cfg(not(tarpaulin_include))]
#[doc(hidden)]
impl Deref for MutexNode {
    type Target = inner::MutexNode<AtomicBool>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[doc(hidden)]
impl DerefMut for MutexNode {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(not(tarpaulin_include))]
impl Default for MutexNode {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can created via a [`new`] constructor. Each mutex has a type parameter
/// which represents the data that it is protecting. The data can only be accessed
/// through the RAII guards returned by the [`lock`] method, which guarantees
/// that the data is only ever accessed when the mutex is locked.
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
///         // A queue node must be mutably accessible.
///         let mut node = MutexNode::new();
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         let mut data = data.lock(&mut node);
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
pub struct Mutex<T: ?Sized, R> {
    pub(super) inner: inner::Mutex<T, AtomicBool, RelaxWait<R>>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, R> Send for Mutex<T, R> {}
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
    /// To acquire a CLH lock through this function, it's also required a mutably
    /// borrowed queue node, which is a record that keeps a link for forming the
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
    ///     let mut node = MutexNode::new();
    ///     *c_mutex.lock(&mut node) = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[inline]
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T, R> {
        self.inner.lock(&mut node.inner).into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function instantiates a [`MutexNode`] for each call, which is
    /// convenient for one-liners by not particularly efficient on hot paths.
    /// If that is your use case, consider calling [`lock`] in the busy loop
    /// while reusing one single node allocation.
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
    ///     c_mutex.lock_with(|mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use clhlock::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with(|guard| &*guard);
    /// ```
    /// [`lock`]: Mutex::lock
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.lock(&mut node))
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
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
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
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.lock_with(f)
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for Mutex<T, R> {
    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is returned by the [`lock`] method on [`Mutex`]. It is also
/// given as closure argument by the [`lock_with`] method.
///
/// [`Deref`]: core::ops::Deref
/// [`DerefMut`]: core::ops::DerefMut
/// [`lock`]: Mutex::lock
/// [`lock_with`]: Mutex::lock_with
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, R> {
    inner: inner::MutexGuard<'a, T, AtomicBool, RelaxWait<R>>,
}

// Same unsafe impls as `crate::inner::raw::MutexGuard`.
// unsafe impl<T: ?Sized + Send, R> Send for MutexGuard<'_, T, R> {}
unsafe impl<T: ?Sized + Sync, R> Sync for MutexGuard<'_, T, R> {}

#[doc(hidden)]
impl<'a, T: ?Sized, R> From<inner::MutexGuard<'a, T, AtomicBool, RelaxWait<R>>>
    for MutexGuard<'a, T, R>
{
    #[inline(always)]
    fn from(inner: inner::MutexGuard<'a, T, AtomicBool, RelaxWait<R>>) -> Self {
        Self { inner }
    }
}

impl<'a, T: ?Sized + Debug, R> Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, R> Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> DerefMut for MutexGuard<'a, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, R> crate::loom::Guard for MutexGuard<'_, T, R> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
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
