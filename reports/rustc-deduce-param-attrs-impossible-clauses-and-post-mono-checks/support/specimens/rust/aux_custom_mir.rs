#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused)]
extern crate core;
use core::intrinsics::mir::*;

pub struct Big {
    pub blah: [u64; 8],
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_copy_arg(a: Big) {
    mir! {
        {
            Call(RET = custom_call_copy_arg(a), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_move_arg(a: Big) {
    mir! {
        {
            Call(RET = custom_call_move_arg(Move(a)), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
