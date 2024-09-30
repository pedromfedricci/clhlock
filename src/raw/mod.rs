//! CLH lock implementation.
//!
//! The `raw` implementation of CLH lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin against its own, locally-accessible atomic lock
//! state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that is `no_std` compatible, and
//! it also requires that queue nodes must be allocated by the callers. Queue
//! nodes are represented by the [`MutexNode`] type.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] method. Guards are also accessible as the closure argument for the
//! [`lock_with`] method.
//!
//! This Mutex is generic over the relax policy. User may choose a policy as long
//! as it implements the [`Relax`] trait.
//!
//! There is a number of relax policies provided by the [`relax`] module. The
//! following modules provide type aliases for [`Mutex`] and [`MutexGuard`]
//! associated with a relax policy. See their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`lock_with`]: Mutex::lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

/// A CLH lock that implements a `spin` relax policy.
///
/// During lock contention, this lock spins while signaling the processor that
/// it is running a busy-wait spin-loop.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A [`raw::Mutex`] that implements the [`Spin`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    /// A [`raw::MutexGuard`] that implements the [`Spin`] relax policy.
    ///
    /// [`raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin>;

    /// A CLH lock that implements a `spin with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff
    /// while spinning, signaling the processor that it is running a busy-wait
    /// spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        /// A [`raw::Mutex`] that implements the [`SpinBackoff`] relax policy.
        ///
        /// # Example
        ///
        /// ```
        /// use clhlock::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let node = MutexNode::new();
        /// let guard = mutex.lock(node);
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;

        /// A [`raw::MutexGuard`] that implements the [`SpinBackoff`] relax
        /// policy.
        ///
        /// [`raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff>;
    }
}

/// A CLH lock that implements a `yield` relax policy.
///
/// During lock contention, this lock will yield the current time slice to the
/// OS scheduler.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// A [`raw::Mutex`] that implements the [`Yield`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    /// A [`raw::MutexGuard`] that implements the [`Yield`] relax policy.
    ///
    /// [`raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield>;

    /// A CLH lock that implements a `yield with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff while
    /// spinning, up to a threshold, then yields back to the OS scheduler.
    #[cfg(feature = "yield")]
    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        /// A [`raw::Mutex`] that implements the [`YieldBackoff`] relax policy.
        ///
        /// # Example
        ///
        /// ```
        /// use clhlock::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let node = MutexNode::new();
        /// let guard = mutex.lock(node);
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;

        /// A [`raw::MutexGuard`] that implements the [`YieldBackoff`] relax
        /// policy.
        ///
        /// [`raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff>;
    }
}

/// A CLH lock that implements a `loop` relax policy.
///
/// During lock contention, this lock will rapidly spin without telling the CPU
/// to do any power down.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A [`raw::Mutex`] that implements the [`Loop`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use clhlock::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let node = MutexNode::new();
    /// let guard = mutex.lock(node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Loop>;

    /// A [`raw::MutexGuard`] that implements the [`Loop`] relax policy.
    ///
    /// [`raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop>;
}
