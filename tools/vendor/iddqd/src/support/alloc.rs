// Adapted from the hashbrown crate, which is licensed under MIT OR Apache-2.0.
// Copyright (c) 2016-2025 Amanieu d'Antras and others
// SPDX-License-Identifier: MIT OR Apache-2.0

pub use self::inner::Global;
pub(crate) use self::inner::{AllocWrapper, Allocator, global_alloc};

// TODO: support nightly.

// Basic non-nightly case.
#[cfg(feature = "allocator-api2")]
mod inner {
    use allocator_api2::alloc::AllocError;
    pub use allocator_api2::alloc::{Allocator, Global, Layout};
    use core::ptr::NonNull;

    #[inline]
    pub(crate) const fn global_alloc() -> Global {
        Global
    }

    #[derive(Clone, Copy, Default)]
    pub(crate) struct AllocWrapper<T>(pub(crate) T);

    // SAFETY: These functions just forward to the wrapped allocator.
    unsafe impl<T: Allocator> allocator_api2::alloc::Allocator for AllocWrapper<T> {
        #[inline]
        fn allocate(
            &self,
            layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            allocator_api2::alloc::Allocator::allocate(&self.0, layout)
        }

        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            allocator_api2::alloc::Allocator::deallocate(&self.0, ptr, layout);
        }
    }
}

// No-defaults case.
#[cfg(not(feature = "allocator-api2"))]
mod inner {
    use crate::alloc::alloc::Layout;
    use allocator_api2::alloc::AllocError;
    use core::ptr::NonNull;

    #[inline]
    pub(crate) const fn global_alloc() -> Global {
        Global::new()
    }

    #[allow(clippy::missing_safety_doc)] // not exposed outside of this crate
    pub unsafe trait Allocator {
        fn allocate(&self, layout: Layout)
        -> Result<NonNull<[u8]>, AllocError>;
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
    }

    #[derive(Copy, Clone, Default)]
    #[doc(hidden)]
    pub struct Global(allocator_api2::alloc::Global);

    impl Global {
        #[inline]
        pub const fn new() -> Self {
            Global(allocator_api2::alloc::Global)
        }
    }

    // SAFETY: These functions just forward to the wrapped allocator.
    unsafe impl Allocator for Global {
        #[inline]
        fn allocate(
            &self,
            layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            allocator_api2::alloc::Allocator::allocate(&self.0, layout)
        }

        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            allocator_api2::alloc::Allocator::deallocate(&self.0, ptr, layout);
        }
    }

    #[derive(Clone, Copy, Default)]
    pub(crate) struct AllocWrapper<T>(pub(crate) T);

    // SAFETY: These functions just forward to the wrapped allocator.
    unsafe impl<T: Allocator> allocator_api2::alloc::Allocator for AllocWrapper<T> {
        #[inline]
        fn allocate(
            &self,
            layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            Allocator::allocate(&self.0, layout)
        }
        #[inline]
        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            Allocator::deallocate(&self.0, ptr, layout);
        }
    }
}
