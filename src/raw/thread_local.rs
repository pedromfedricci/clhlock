use core::cell::RefCell;

use super::{Mutex, MutexGuard, MutexNode};
use crate::cfg::thread::LocalKey;
use crate::inner::raw as inner;
use crate::relax::Relax;

#[cfg(test)]
use crate::test::{LockNew, LockWith};

type StaticNode = &'static LocalMutexNode;

/// Declares a new [`raw::LocalMutexNode`] key, which is a handle to the thread
/// local node of the currently running thread.
///
/// The macro wraps any number of static declarations and make them thread
/// local. Each provided name is associated with a single thread local key. The
/// keys are wrapped and managed by the [`LocalMutexNode`] type, which are the
/// actual handles meant to be used with the `lock_with_local` API family from
/// [`raw::Mutex`]. Handles are provided by reference to functions.
///
/// See: [`lock_with_local`] and [`lock_with_local_unchecked`].
///
/// # Sintax
///
/// * Allows multiple static definitions, must be separated with semicolons.
/// * Visibility is optional (private by default).
/// * Requires `static` keyword and a **UPPER_SNAKE_CASE** name.
///
/// # Example
///
/// ```
/// use clhlock::raw::spins::Mutex;
///
/// // Multiple difenitions.
/// clhlock::thread_local_node! {
///     pub static NODE;
///     static OTHER_NODE1;
/// }
///
/// // Single definition.
/// clhlock::thread_local_node!(pub static OTHER_NODE2);
///
/// let mutex = Mutex::new(0);
/// // Keys are provided to APIs by reference.
/// mutex.lock_with_local(&NODE, |mut guard| *guard = 10);
/// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
/// ```
/// [`raw::Mutex`]: Mutex
/// [`raw::LocalMutexNode`]: LocalMutexNode
/// [`lock_with_local`]: Mutex::lock_with_local
/// [`lock_with_local_unchecked`]: Mutex::lock_with_local_unchecked
#[macro_export]
macro_rules! thread_local_node {
    // Empty (base for recursion).
    () => {};
    // Process multiply definitions (recursive).
    ($vis:vis static $node:ident; $($rest:tt)*) => {
        $crate::__thread_local_node_inner!($vis $node, raw);
        $crate::thread_local_node!($($rest)*);
    };
    // Process single declaration.
    ($vis:vis static $node:ident) => {
        $crate::__thread_local_node_inner!($vis $node, raw);
    };
}

/// A handle to a [`MutexNode`] stored at the thread local storage.
///
/// Thread local nodes can be claimed for temporary, exclusive access during
/// runtime for locking purposes. Node handles refer to the node stored at
/// the current running thread.
///
/// Just like `MutexNode`, this is an opaque type that holds metadata for the
/// [`raw::Mutex`]'s waiting queue. You must declare a thread local node with
/// the [`thread_local_node!`] macro, and provide the generated handle to the
/// appropriate [`raw::Mutex`] locking APIs. Attempting to lock a mutex with a
/// thread local node that already is in use for the locking thread will cause
/// a panic. Handles are provided by reference to functions.
///
/// See: [`lock_with_local`] and [`lock_with_local_unchecked`].
///
/// [`MutexNode`]: MutexNode
/// [`raw::Mutex`]: Mutex
/// [`thread_local_node!`]: crate::thread_local_node
/// [`lock_with_local`]: Mutex::lock_with_local
/// [`lock_with_local_unchecked`]: Mutex::lock_with_local_unchecked
#[repr(transparent)]
#[derive(Debug)]
pub struct LocalMutexNode {
    inner: inner::LocalMutexNode<MutexNode>,
}

#[cfg(not(tarpaulin_include))]
impl LocalMutexNode {
    /// Creates a new `LocalMutexNode` key from the provided thread local node
    /// key.
    ///
    /// This function is **NOT** part of the public API and so must not be
    /// called directly by user's code. It is subjected to changes **WITHOUT**
    /// prior notice or accompanied with relevant SemVer changes.
    #[cfg(not(all(loom, test)))]
    #[doc(hidden)]
    #[must_use]
    #[inline(always)]
    pub const fn __new(key: LocalKey<RefCell<MutexNode>>) -> Self {
        let inner = inner::LocalMutexNode::new(key);
        Self { inner }
    }

    /// Creates a new Loom based `LocalMutexNode` key from the provided thread
    /// local node key.
    #[cfg(all(loom, test))]
    #[must_use]
    pub(crate) const fn new(key: &'static LocalKey<RefCell<MutexNode>>) -> Self {
        let inner = inner::LocalMutexNode::new(key);
        Self { inner }
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// To acquire a CLH lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_with_local(&NODE, |mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with_local(&NODE, |guard| &*guard);
    /// ```
    ///
    /// Panic: thread local node cannot be borrowed more than once at the same
    /// time:
    ///
    #[doc = concat!("```should_panic,", already_borrowed_error!())]
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| {
    ///     // `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.lock_with_local(&NODE, |_guard| ());
    /// });
    /// ```
    #[inline]
    #[track_caller]
    pub fn lock_with_local<F, Ret>(&self, node: StaticNode, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.inner.lock_with_local(&node.inner, |guard| f(From::from(guard)))
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// To acquire a CLH lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Safety
    ///
    /// Unlike [`lock_with_local`], this method is unsafe because it does not
    /// check if the current thread local node is already mutably borrowed. If
    /// the current thread local node is already borrowed, calling this
    /// function is undefined behavior.
    ///
    /// # Panics
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || unsafe {
    ///     c_mutex.lock_with_local_unchecked(&NODE, |mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = unsafe {
    ///     mutex.lock_with_local_unchecked(&NODE, |g| &*g)
    /// };
    /// ```
    ///
    /// Undefined behavior: thread local node cannot be borrowed more than once
    /// at the same time:
    ///
    /// ```no_run
    /// use clhlock::raw::spins::Mutex;
    ///
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| unsafe {
    ///     // UB: `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.lock_with_local_unchecked(&NODE, |_guard| ());
    /// });
    /// ```
    /// [`lock_with_local`]: Mutex::lock_with_local
    #[inline]
    pub unsafe fn lock_with_local_unchecked<F, Ret>(&self, node: StaticNode, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.inner.lock_with_local_unchecked(&node.inner, |guard| f(From::from(guard)))
    }

    /// Guard cannot outlive the closure or else it would allow the guard drop
    /// call to access the thread local node even though its exclusive borrow
    /// has already expired at the end of the closure.
    ///
    /// ```compile_fail
    /// use clhlock::raw::spins::Mutex;
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let guard = mutex.lock_with_local(&NODE, |guard| guard);
    /// ```
    ///
    /// ```compile_fail,E0521
    /// use std::thread;
    /// use clhlock::raw::spins::Mutex;
    /// clhlock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// mutex.lock_with_local(&NODE, |guard| {
    ///     thread::spawn(move || {
    ///         let guard = guard;
    ///     });
    /// });
    /// ```
    #[cfg(not(tarpaulin_include))]
    const fn __guard_cant_escape_closure() {}
}

// A thread local node definition used for testing.
#[cfg(test)]
#[cfg(not(tarpaulin_include))]
thread_local_node!(static TEST_NODE);

/// A Mutex wrapper type that calls `lock_with_local` when implementing testing
// traits.
#[cfg(test)]
struct MutexPanic<T: ?Sized, R>(Mutex<T, R>);

#[cfg(test)]
impl<T: ?Sized, R> LockNew for MutexPanic<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWith for MutexPanic<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.0.lock_with_local(&TEST_NODE, f)
    }
}

/// A Mutex wrapper type that calls `lock_with_local_unchecked` when
/// implementing testing traits.
#[cfg(test)]
struct MutexUnchecked<T: ?Sized, R>(Mutex<T, R>);

#[cfg(test)]
impl<T: ?Sized, R> LockNew for MutexUnchecked<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWith for MutexUnchecked<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        // SAFETY: caller must guarantee that this thread local node is not
        // already mutably borrowed for some other lock acquisition.
        unsafe { self.0.lock_with_local_unchecked(&TEST_NODE, f) }
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::relax::Yield;
    use crate::test::tests;

    type MutexPanic<T> = super::MutexPanic<T, Yield>;
    type MutexUnchecked<T> = super::MutexUnchecked<T, Yield>;

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<MutexPanic<_>>();
    }

    #[test]
    fn lots_and_lots_lock_unchecked() {
        tests::lots_and_lots_lock::<MutexUnchecked<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<MutexPanic<_>>();
    }

    #[test]
    fn smoke_unchecked() {
        tests::smoke::<MutexUnchecked<_>>();
    }

    #[test]
    #[should_panic = already_borrowed_error!()]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<MutexPanic<_>, MutexPanic<_>>();
    }

    #[test]
    #[should_panic = already_borrowed_error!()]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind_unchecked() {
        tests::test_lock_arc_access_in_unwind::<MutexUnchecked<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_unsized_unchecked() {
        tests::test_lock_unsized::<MutexUnchecked<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::relax::Yield;

    type MutexPanic<T> = super::MutexPanic<T, Yield>;
    type MutexUnchecked<T> = super::MutexUnchecked<T, Yield>;

    #[test]
    fn lock_join() {
        models::lock_join::<MutexPanic<_>>();
    }

    #[test]
    fn lock_join_unchecked() {
        models::lock_join::<MutexUnchecked<_>>();
    }
}
