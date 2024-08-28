pub mod atomic {
    pub use sealed::UnsyncLoad;

    #[cfg(not(all(loom, test)))]
    pub use core::sync::atomic::{fence, AtomicBool, AtomicPtr};

    #[cfg(all(loom, test))]
    pub use loom::sync::atomic::{fence, AtomicBool, AtomicPtr};

    impl<T> UnsyncLoad for AtomicPtr<T> {
        type Target = T;

        #[cfg(not(all(loom, test)))]
        unsafe fn load_unsynced(&self) -> *mut Self::Target {
            // SAFETY: Caller guaranteed that the atomic value is not currently
            // visible by any other thread.
            unsafe { *self.as_ptr() }
        }

        #[cfg(all(loom, test))]
        #[cfg(not(tarpaulin_include))]
        unsafe fn load_unsynced(&self) -> *mut Self::Target {
            // SAFETY: Caller guaranteed that the atomic value is not currently
            // visible by any other thread.
            unsafe { self.unsync_load() }
        }
    }

    mod sealed {
        /// A trait that extends [`AtomicPtr`] so that it will allow loading the
        /// value without any synchronization.
        ///
        /// # Safety
        ///
        /// Caller must guarantee that the atomic value is not currently visible
        /// by any other thread, as this is equivalent to a non-atomic load over
        /// the value.
        pub trait UnsyncLoad {
            /// The type of the pointed to value.
            type Target;

            /// Load the value without any synchronization.
            unsafe fn load_unsynced(&self) -> *mut Self::Target;
        }
    }
}

pub mod cell {
    pub use sealed::{CellNullMut, WithUnchecked};

    #[cfg(not(all(loom, test)))]
    pub use core::cell::UnsafeCell;

    #[cfg(all(loom, test))]
    pub use loom::cell::UnsafeCell;

    #[cfg(not(all(loom, test)))]
    pub use core::cell::Cell;

    #[cfg(all(loom, test))]
    pub use loom::cell::Cell;

    impl<T: ?Sized> WithUnchecked for UnsafeCell<T> {
        type Target = T;

        #[cfg(not(all(loom, test)))]
        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&Self::Target) -> Ret,
        {
            // SAFETY: Caller guaranteed that there are no mutable aliases.
            f(unsafe { &*self.get() })
        }

        #[cfg(all(loom, test))]
        #[cfg(not(tarpaulin_include))]
        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&Self::Target) -> Ret,
        {
            // SAFETY: Caller guaranteed that there are no mutable aliases.
            self.with(|ptr| f(unsafe { &*ptr }))
        }
    }

    impl<T> CellNullMut for Cell<*mut T> {
        type Target = T;

        #[rustfmt::skip]
        #[cfg(not(all(loom, test)))]
        const NULL_MUT: Cell<*mut Self::Target> = {
            Self::new(core::ptr::null_mut())
        };

        #[cfg(all(loom, test))]
        fn null_mut() -> Cell<*mut Self::Target> {
            Self::new(core::ptr::null_mut())
        }
    }

    mod sealed {
        use super::Cell;

        /// A trait that extends [`UnsafeCell`] to allow running closures against
        /// its underlying data.
        pub trait WithUnchecked {
            /// The type of the underlying data.
            type Target: ?Sized;

            /// Runs `f` against a shared reference borrowed from a [`UnsafeCell`].
            ///
            /// # Safety
            ///
            /// Caller must guarantee there are no mutable aliases to the
            /// underlying data.
            unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
            where
                F: FnOnce(&Self::Target) -> Ret;
        }

        /// A trait that extends [`Cell`] to allow creating `null` values.
        pub trait CellNullMut {
            /// The type of the data inner pointer points to.
            type Target;

            /// A compiler time evaluable [`Cell`] holding a `null` pointer.
            #[cfg(not(all(loom, test)))]
            #[allow(clippy::declare_interior_mutable_const)]
            const NULL_MUT: Cell<*mut Self::Target>;

            /// Returns a Loom based [`Cell`] holding a `null` pointer (non-const).
            #[cfg(all(loom, test))]
            fn null_mut() -> Cell<*mut Self::Target>;
        }
    }
}

pub mod hint {
    #[cfg(not(all(loom, test)))]
    pub use core::hint::spin_loop;

    #[cfg(all(loom, test))]
    pub use loom::hint::spin_loop;
}

pub mod thread {
    #[cfg(all(any(feature = "yield", test), not(all(loom, test))))]
    pub use std::thread::yield_now;

    #[cfg(all(loom, test))]
    pub use loom::thread::yield_now;

    #[cfg(all(feature = "thread_local", not(all(loom, test))))]
    pub use std::thread::LocalKey;

    #[cfg(all(feature = "thread_local", loom, test))]
    pub use loom::thread::LocalKey;
}
