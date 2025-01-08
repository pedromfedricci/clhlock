# A simple and correct implementation of the CLH lock

[![MIT][mit-badge]][mit]
[![Apache 2.0][apache2-badge]][apache2]
[![Crates][crates-badge]][crates]
[![Docs][docs-badge]][docs]
[![CI][ci-badge]][ci]
[![Codecov][codecov-badge]][codecov]
![No_std][no_std-badge]

CLH lock is a List-Based Queuing Lock that avoids network contention by
having threads spin and on locally accessible memory locations. The main
properties of this mechanism are:

- guarantees FIFO ordering of lock acquisitions;
- spins on locally-accessible flag variables only;
- requires a small constant amount of space per lock; and
- works equally well (requiring only O(1) network transactions per lock
  acquisition) on machines with and without coherent caches.
- avoids the "handshake" runtime overhead between the lock holder and
  its successor during lock hand-off.

This algorithm was indenpendently introduced by [Craig] and
[Magnussen, Landin, and Hagersten] papers.

## Spinlock use cases

It is noteworthy to mention that [spinlocks are usually not what you want].
The majority of use cases are well covered by OS-based mutexes like
[`std::sync::Mutex`], [`parking_lot::Mutex`]. These implementations will
notify the system that the waiting thread should be parked, freeing the
processor to work on something else.

Spinlocks are only efficient in very few circunstances where the overhead
of context switching or process rescheduling are greater than busy waiting
for very short periods. Spinlocks can be useful inside operating-system
kernels, on embedded systems or even complement other locking designs.

## Install

Run the following Cargo command in your project directory:

```bash
cargo add clhlock
```

Or add a entry under the `[dependencies]` section in your `Cargo.toml`:

```toml
# Cargo.toml

[dependencies]
# Features: `yield`.
clhlock = { version = "0.2", features = ["yield"] }
```

## Documentation

This project documentation is hosted at [docs.rs][docs]. Or you can build it
locally with the following command:

```bash
RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features --open
```

## Waiting queue node allocations

Queue nodes are allocated in the heap, and their ownership is transparently
moved from the lock holding thread to its successor. Allocating the nodes
directly in the stack is not possible since the CLH lock protocol does not
guarantee that a predecessor thread will be live by the time a successor access
its associated locking node. Locking operations require taking ownership over
node handles that manage the heap allocations. Node handles are represented 
by the [`raw::MutexNode`] type. Therefore, this crate requires linking with
Rust's core [alloc] library.

## Locking with a raw CLH spinlock

This implementation operates under FIFO. Raw locking APIs require taking
ownership over node handles that manage the heap allocated queue nodes. These
node handles are represented by the [`raw::MutexNode`] type. This implementation
is `no_std` compatible. See the [`raw`] module for more information.

```rust
use std::sync::Arc;
use std::thread;

// Simply spins during contention.
use clhlock::raw::{spins::Mutex, MutexNode};

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // A handle to a heap allocated queue node.
        let node = MutexNode::new();
        // The queue node handle must be consumed.
        *c_mutex.lock_with(node) = 10;
    })
    .join().expect("thread::spawn failed");

    // A node may also be transparently allocated.
    assert_eq!(*mutex.lock(), 10);
}
```

## Features

This crate dos not provide any default features. Features that can be enabled
are:

### yield

The `yield` feature requires linking to the standard library, so it is not
suitable for `no_std` environments. By enabling the `yield` feature, instead
of busy-waiting during lock acquisitions and releases, this will call
[`std::thread::yield_now`], which cooperatively gives up a timeslice to the
OS scheduler. This may cause a context switch, so you may not want to enable
this feature if your intention is to to actually do optimistic spinning. The
default implementation calls [`core::hint::spin_loop`], which does in fact
just simply busy-waits. This feature is not `not_std` compatible.

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on a Minimum Supported Rust Version (MSRV)
of 1.65.0 and above. This version will not be changed without a minor version
bump.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.

## Code review

It is recommended to always use [cargo-crev] to verify the trustworthiness of
each of your dependencies, including this one.

[mit-badge]: https://img.shields.io/badge/License-MIT-blue.svg
[apache2-badge]: https://img.shields.io/badge/License-Apache_2.0-yellow.svg
[docs-badge]: https://img.shields.io/docsrs/clhlock
[crates-badge]: https://img.shields.io/crates/v/clhlock
[ci-badge]: https://github.com/pedromfedricci/clhlock/actions/workflows/ci.yml/badge.svg
[codecov-badge]: https://codecov.io/gh/pedromfedricci/clhlock/graph/badge.svg?token=A54PAF1K74
[no_std-badge]: https://img.shields.io/badge/no__std-compatible-success.svg

[mit]: https://opensource.org/licenses/MIT
[apache2]: https://opensource.org/licenses/Apache-2.0
[docs]: https://docs.rs/clhlock
[crates]: https://crates.io/crates/clhlock
[ci]: https://github.com/pedromfedricci/clhlock/actions/workflows/ci.yml
[codecov]: https://codecov.io/gh/pedromfedricci/clhlock
[cargo-crev]: https://github.com/crev-dev/cargo-crev

[Craig]: https://dada.cs.washington.edu/research/tr/1993/02/UW-CSE-93-02-02.pdf
[Magnussen, Landin, and Hagersten]: https://www2.it.uu.se/research/group/uart/pub/magnusson_1994_jan/magnusson_1994_jan.pdf
[spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html

[`raw`]: https://docs.rs/clhlock/latest/clhlock/raw/index.html
[`raw::Mutex`]: https://docs.rs/clhlock/latest/clhlock/raw/struct.Mutex.html
[`raw::MutexNode`]: https://docs.rs/clhlock/latest/clhlock/raw/struct.MutexNode.html

[alloc]: https://doc.rust-lang.org/alloc/index.html
[`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
[`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
[`core::hint::spin_loop`]: https://doc.rust-lang.org/core/hint/fn.spin_loop.html

[`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
