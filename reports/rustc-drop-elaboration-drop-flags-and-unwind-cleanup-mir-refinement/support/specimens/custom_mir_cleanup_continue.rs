// Hand-written runtime-dialect MIR (`#[custom_mir]`, an unstable internal
// testing feature) in which a drop inside a cleanup block carries
// `UnwindContinue()` instead of `UnwindTerminate(ReasonInCleanup)`.
//
// The MIR validator rejects this shape when it is enabled (`-Zvalidate-mir`).
// `support/probe_drop_elaboration.py` compiles this file both with and without
// the validator and, when a binary is produced, runs it.

#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused_variables, unused_assignments, dead_code)]

use core::intrinsics::mir::*;

pub struct Loud {
    name: &'static str,
    bomb: bool,
}

impl Drop for Loud {
    fn drop(&mut self) {
        println!("drop {}", self.name);
        if self.bomb {
            panic!("destructor of {} panics", self.name);
        }
    }
}

#[inline(never)]
pub fn make_bomb() -> Loud {
    Loud { name: "bomb", bomb: true }
}

#[inline(never)]
pub fn make_rest() -> Loud {
    Loud { name: "rest", bomb: false }
}

#[inline(never)]
pub fn boom() {
    panic!("explicit panic");
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn cleanup_continue(c: bool) {
    mir! {
        let a: Loud;
        let b: Loud;
        let u: ();
        {
            Call(b = make_rest(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            Call(a = make_bomb(), ReturnTo(bb2), UnwindCleanup(bb6))
        }
        bb2 = {
            Call(u = boom(), ReturnTo(bb3), UnwindCleanup(bb5))
        }
        bb3 = {
            Drop(a, ReturnTo(bb4), UnwindCleanup(bb6))
        }
        bb4 = {
            Drop(b, ReturnTo(bb8), UnwindContinue())
        }
        bb5 (cleanup) = {
            Drop(a, ReturnTo(bb6), UnwindContinue())
        }
        bb6 (cleanup) = {
            Drop(b, ReturnTo(bb7), UnwindTerminate(ReasonInCleanup))
        }
        bb7 (cleanup) = {
            UnwindResume()
        }
        bb8 = {
            Return()
        }
    }
}

fn main() {
    let r = std::panic::catch_unwind(|| cleanup_continue(false));
    println!("caught-unwind {}", r.is_err());
    println!("main-returned");
}
