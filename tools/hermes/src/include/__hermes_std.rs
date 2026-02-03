pub use ::std::*;

// Re-export the prelude so 'use std::prelude::rust_2021::*' works.
pub mod prelude {
    pub mod rust_2021 {
        pub use ::std::prelude::rust_2021::*;
    }
}

pub mod ptr {
    pub use ::std::ptr::*;

    // TODO: Also require "valid for reads".

    ///@ lean model read [Layout T] [Verifiable T] (src : ConstPtr T)
    ///@ requires h_align : (Memory.addr src) % (Layout.align T) = 0
    ///@ requires h_init  : Memory.is_initialized src
    ///@ ensures |ret| Verifiable.is_valid ret
    pub unsafe fn read<T>(src: *const T) -> T {
        unsafe { ::std::ptr::read(src) }
    }
}

// Allow this module to act as 'core' as well (since std re-exports core items).
pub use ::std as core_shim;
