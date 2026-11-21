// Hand-written MIR specimens (`#[custom_mir]`, an unstable internal testing
// feature) compiled by `support/probe_drop_elaboration.py`.
//
// These bodies are NOT produced by MIR building. They exist to feed the real
// `ElaborateDrops` pass (analysis-dialect bodies) or the real code generator
// (runtime-dialect bodies) with control-flow shapes that surface Rust cannot
// express, so that the behaviour of the compiler on them can be observed.

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
pub fn make() -> Loud {
    Loud { name: "x", bomb: false }
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
pub fn consume(x: Loud) {
    println!("consume {}", x.name);
}

#[inline(never)]
pub fn boom() {
    panic!("explicit panic");
}

// Analysis-dialect body: `x` is dropped on one branch (a drop that the pass
// classifies as always-initialized) and then dropped again at the join point,
// where the dataflow sees "maybe initialized, maybe uninitialized".
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub fn stale_flag_join(c: bool) {
    mir! {
        let x: Loud;
        {
            Call(x = make(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match c { true => bb2, _ => bb3 }
        }
        bb2 = {
            Drop(x, ReturnTo(bb3), UnwindContinue())
        }
        bb3 = {
            Drop(x, ReturnTo(bb4), UnwindContinue())
        }
        bb4 = {
            Return()
        }
    }
}

// Control for `stale_flag_join`: identical, except that the first drop is
// followed by `StorageDead(x)`, as MIR building emits at scope exit.
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub fn stale_flag_join_storage_dead(c: bool) {
    mir! {
        let x: Loud;
        {
            StorageLive(x);
            Call(x = make(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match c { true => bb2, _ => bb3 }
        }
        bb2 = {
            Drop(x, ReturnTo(bb5), UnwindContinue())
        }
        bb5 = {
            StorageDead(x);
            Goto(bb3)
        }
        bb3 = {
            Drop(x, ReturnTo(bb4), UnwindContinue())
        }
        bb4 = {
            Return()
        }
    }
}

// Analysis-dialect reference for the conditional-move join: the real pass
// inserts a drop flag.
#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
pub fn join_reference(c: bool) {
    mir! {
        let x: Loud;
        let u: ();
        {
            Call(x = make(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match c { true => bb2, _ => bb3 }
        }
        bb2 = {
            Call(u = consume(Move(x)), ReturnTo(bb3), UnwindContinue())
        }
        bb3 = {
            Drop(x, ReturnTo(bb4), UnwindContinue())
        }
        bb4 = {
            Return()
        }
    }
}

// Runtime-dialect body (drops are unconditional): the conditional-move join
// lowered WITHOUT a drop flag, keeping the drop.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn join_no_flag_always_drop(c: bool) {
    mir! {
        let x: Loud;
        let u: ();
        {
            Call(x = make(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match c { true => bb2, _ => bb3 }
        }
        bb2 = {
            Call(u = consume(Move(x)), ReturnTo(bb3), UnwindContinue())
        }
        bb3 = {
            Drop(x, ReturnTo(bb4), UnwindContinue())
        }
        bb4 = {
            Return()
        }
    }
}

// Runtime-dialect body: the conditional-move join lowered WITHOUT a drop flag,
// removing the drop.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn join_no_flag_never_drop(c: bool) {
    mir! {
        let x: Loud;
        let u: ();
        {
            Call(x = make(), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match c { true => bb2, _ => bb3 }
        }
        bb2 = {
            Call(u = consume(Move(x)), ReturnTo(bb3), UnwindContinue())
        }
        bb3 = {
            Goto(bb4)
        }
        bb4 = {
            Return()
        }
    }
}

// Runtime-dialect body with a well-formed cleanup chain: `boom()` unwinds into a
// cleanup block that drops `a` (whose destructor panics) with
// `UnwindTerminate(ReasonInCleanup)`, then would drop `b`.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn cleanup_terminate(c: bool) {
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
            Drop(a, ReturnTo(bb6), UnwindTerminate(ReasonInCleanup))
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
    let args: Vec<String> = std::env::args().collect();
    let name = args.get(1).map(String::as_str).unwrap_or("");
    let c = args.get(2).map(String::as_str) == Some("1");
    match name {
        "stale_flag_join" => stale_flag_join(c),
        "stale_flag_join_storage_dead" => stale_flag_join_storage_dead(c),
        "join_reference" => join_reference(c),
        "join_no_flag_always_drop" => join_no_flag_always_drop(c),
        "join_no_flag_never_drop" => join_no_flag_never_drop(c),
        "cleanup_terminate" => cleanup_terminate(c),
        other => {
            eprintln!("unknown specimen {:?}", other);
            std::process::exit(2);
        }
    }
    println!("main-returned");
}
