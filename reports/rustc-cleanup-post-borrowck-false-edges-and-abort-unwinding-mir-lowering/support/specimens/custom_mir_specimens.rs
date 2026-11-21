#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, dead_code, unused_variables)]

extern crate core;
use core::intrinsics::mir::*;

#[inline(never)]
pub extern "C-unwind" fn helper_c_unwind(v: u8) -> u8 {
    if v == 0 {
        panic!("custom_mir callee panic");
    }
    v + 1
}

/// Hand-written analysis-dialect MIR inside an `extern "C"` body calling an
/// `extern "C-unwind"` callee with `UnwindContinue()` (testing `AbortUnwindingCalls`
/// lowering `Continue -> Terminate(Abi)` even when `RemoveNoopLandingPads` did not run).
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub extern "C" fn custom_extern_c_unwind_continue(v: u8) -> u8 {
    mir! {
        {
            Call(RET = helper_c_unwind(v), ReturnTo(bb_ret), UnwindContinue())
        }
        bb_ret = {
            Return()
        }
    }
}

/// Hand-written analysis-dialect MIR inside an `extern "C"` body calling an
/// `extern "C-unwind"` callee with `UnwindCleanup(bb_pad)` terminating in `UnwindResume()`.
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub extern "C" fn custom_extern_c_unwind_cleanup_pad(v: u8) -> u8 {
    mir! {
        {
            Call(RET = helper_c_unwind(v), ReturnTo(bb_ret), UnwindCleanup(bb_pad))
        }
        bb_ret = {
            Return()
        }
        bb_pad (cleanup) = {
            UnwindResume()
        }
    }
}

pub fn main() {
    assert_eq!(custom_extern_c_unwind_continue(41), 42);
    assert_eq!(custom_extern_c_unwind_cleanup_pad(41), 42);
}
