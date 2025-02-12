//! A safe, opinionated implementation of Craig's and, indenpendently,
//! Magnussen, Landin, and Hagersten's [lock] for mutual exclusion, referred to
//! as CLH lock.
//!
//! CLH lock is a List-Based Queuing Lock that avoids network contention by
//! having threads spin and on locally accessible memory locations. The main
//! properties of this mechanism are:
//!
//! - guarantees FIFO ordering of lock acquisitions;
//! - spins on locally-accessible flag variables only;
//! - requires a small constant amount of space per lock; and
//! - works equally well (requiring only O(1) network transactions per lock
//!   acquisition) on machines with and without coherent caches.
//! - avoids the "handshake" runtime overhead between the lock holder and
//!   its successor during lock release.
//!
//! This algorithm was indenpendently introduced by [Craig] and
//! [Magnussen, Landin, and Hagersten] papers.
//!
//! ## Spinlock use cases
//!
//! It is noteworthy to mention that [spinlocks are usually not what you want].
//! The majority of use cases are well covered by OS-based mutexes like
//! [`std::sync::Mutex`], [`parking_lot::Mutex`]. These implementations will
//! notify the system that the waiting thread should be parked, freeing the
//! processor to work on something else.
//!
//! Spinlocks are only efficient in very few circunstances where the overhead
//! of context switching or process rescheduling are greater than busy waiting
//! for very short periods. Spinlocks can be useful inside operating-system
//! kernels, on embedded systems or even complement other locking designs.
//!
//! ## Waiting queue node allocations
//!
//! Queue nodes are allocated in the heap, and their ownership is transparently
//! moved from the lock holding thread to its successor. Allocating the nodes
//! directly in the stack is not possible since the CLH lock protocol does not
//! guarantee that a predecessor thread will be live by the time a successor access
//! its associated locking node. Locking operations require taking ownership over
//! node handles that manage the heap allocations. Node handles are represented
//! by the [`raw::MutexNode`] type. Therefore, this crate requires linking with
//! Rust's core [alloc] library.
//!
//! ## Locking with a raw CLH spinlock
//!
//! This implementation operates under FIFO. Raw locking APIs require taking
//! taking ownership over node handle that manage the heap allocated queue nodes.
//! These node handles are represented by the [`raw::MutexNode`] type. This
//! implementation is `no_std` compatible. See the [`raw`] module for more
//! information.
//!
//! ```
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Simply spins during contention.
//! use clhlock::raw::{spins::Mutex, MutexNode};
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     // A handle to a heap allocated queue node.
//!     let node = MutexNode::new();
//!     // The queue node handle must consumed.
//!     *c_mutex.lock_with(node) = 10;
//! })
//! .join().expect("thread::spawn failed");
//!
//! // A node may also be transparently allocated.
//! assert_eq!(*mutex.lock(), 10);
//! ```
//!
//! ## Features
//!
//! This crate dos not provide any default features. Features that can be enabled
//! are:
//!
//! ### yield
//!
//! The `yield` feature requires linking to the standard library, so it is not
//! suitable for `no_std` environments. By enabling the `yield` feature, instead
//! of busy-waiting during lock acquisitions and releases, this will call
//! [`std::thread::yield_now`], which cooperatively gives up a timeslice to the
//! OS scheduler. This may cause a context switch, so you may not want to enable
//! this feature if your intention is to to actually do optimistic spinning. The
//! default implementation calls [`core::hint::spin_loop`], which does in fact
//! just simply busy-waits. This feature is not `not_std` compatible.
//!
//! [lock]: https://en.wikipedia.org/wiki/Lock_(computer_science)
//! [Craig]: https://dada.cs.washington.edu/research/tr/1993/02/UW-CSE-93-02-02.pdf
//! [Magnussen, Landin, and Hagersten]: https://www2.it.uu.se/research/group/uart/pub/magnusson_1994_jan/magnusson_1994_jan.pdf
//! [spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
//!
//! [`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html

#![no_std]
#![allow(clippy::doc_markdown)]
#![allow(clippy::inline_always)]
#![allow(clippy::module_name_repetitions)]
#![warn(missing_docs)]
#![warn(rust_2024_compatibility)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![cfg_attr(docsrs, feature(doc_cfg))]

extern crate alloc;

#[cfg(any(feature = "yield", loom, test))]
extern crate std;

pub mod raw;
pub mod relax;

pub(crate) mod cfg;
pub(crate) mod inner;
pub(crate) mod lock;

#[cfg(test)]
pub(crate) mod test;

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin))]
pub(crate) mod loom;
