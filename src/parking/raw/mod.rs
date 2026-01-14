//! CLH lock implementation with thread parking support.
//!
//! The `raw` implementation of MCS lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin and park against its own, locally-accessible atomic
//! lock state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that **is not** `no_std` compatible,
//! and it also requires that queue nodes must be allocated by the callers.
//! Queue nodes are represented by the [`MutexNode`] type.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] method. Guards are also accessible as the closure parameter for the
//! [`lock_with`] method.
//!
//! This Mutex is generic over the parking policy. User may choose a policy as
//! long as it implements the [`Park`] trait.
//!
//! There is a number of parking policies provided by the [`park`] module. The
//! following modules provide type aliases for [`Mutex`] associated with a parking
//! policy. See their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`lock_with`]: Mutex::lock_with
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

/// A CLH lock that implements a `spin then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock spins
/// while signaling the processor that it is running a busy-wait spin-loop. Once
/// all attempts have been tried, puts the thread to sleep.
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`SpinThenPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::parking::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let value = mutex.lock_with_then(node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, SpinThenPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`SpinThenPark`] parking
    /// policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinThenPark>;

    /// A CLH lock that implements a `spin with backoff then park`
    /// policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff spinning, signaling the processor that
    /// its is running a busy-wait spin-loop. Once all attempts have been tried,
    /// puts the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::SpinBackoffThenPark;

        /// A [`parking::raw::Mutex`] that implements the [`SpinBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use clhlock::parking::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let node = MutexNode::new();
        /// let value = mutex.lock_with_then(node, |data| *data);
        /// assert_eq!(value, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThenPark>;

        /// A [`parking::raw::MutexGuard`] that implements the [`SpinBackoffThenPark`]
        /// parking policy.
        ///
        /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoffThenPark>;
    }
}

/// A CLH lock that implements a `yield then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock will
/// yield the current time slice to the OS scheduler. Once all attempts have
/// been tried, puts the thread to sleep.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`YieldThenPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::parking::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock_with(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, YieldThenPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`YieldThenPark`] parking
    /// policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldThenPark>;

    /// A CLH lock that implements a `yield with backoff then park`
    /// parking policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff while spinning, up to a threshold, then
    /// yields back to the OS scheduler. Once all attempts have been tried, it
    /// will then put the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::YieldBackoffThenPark;

        /// A [`parking::raw::Mutex`] that implements the [`YieldBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use clhlock::parking::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let node = MutexNode::new();
        /// let guard = mutex.lock_with(node);
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThenPark>;

        /// A [`parking::raw::MutexGuard`] that implements the [`YieldBackoffThenPark`]
        /// parking policy.
        ///
        /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoffThenPark>;
    }
}

/// A CLH lock that implements a `loop then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock
/// will rapidly spin without telling the CPU to do any power down. Once all
/// attempts have been tried, it will then put the thread to sleep.
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`LoopThenPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::parking::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock_with(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, LoopThenPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`LoopThenPark`] parking
    /// policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, LoopThenPark>;
}

/// A CLH lock that implements an `immediate park` parking policy.
///
/// During lock contention, this lock will immediately put the thread to sleep.
pub mod immediate {
    use super::mutex;
    use crate::parking::park::ImmediatePark;

    /// A [`parking::raw::Mutex`] that implements the [`ImmediatePark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::parking::raw::{immediate::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock_with(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`ImmediatePark`] parking
    /// policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, ImmediatePark>;
}
