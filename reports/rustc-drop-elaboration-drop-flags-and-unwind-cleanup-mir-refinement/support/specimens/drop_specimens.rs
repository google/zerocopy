// Drop-elaboration specimens compiled by `support/probe_drop_elaboration.py`.
//
// Every specimen is a `#[inline(never)]` function whose MIR is dumped immediately
// before and after the `ElaborateDrops` pass, and which is also executed natively
// through `main` (first argument: specimen name, second argument: `0` or `1`).
//
// `Loud` prints one line per destructor run, so the standard output of a run is
// the destructor trace. A `Loud` built with `Loud::bomb` panics inside
// `Drop::drop` after printing its line.

#![allow(unused_variables, unused_assignments, dead_code)]

use std::mem::{ManuallyDrop, MaybeUninit};

pub struct Loud {
    name: &'static str,
    bomb: bool,
}

impl Loud {
    #[inline(never)]
    pub fn new(name: &'static str) -> Loud {
        Loud { name, bomb: false }
    }
    #[inline(never)]
    pub fn bomb(name: &'static str) -> Loud {
        Loud { name, bomb: true }
    }
}

impl Drop for Loud {
    fn drop(&mut self) {
        println!("drop {}", self.name);
        if self.bomb {
            panic!("destructor of {} panics", self.name);
        }
    }
}

#[derive(Clone, Copy)]
pub struct Plain(pub u32);

pub struct Triple {
    pub a: Loud,
    pub b: Loud,
    pub c: Loud,
}

#[inline(never)]
pub fn consume(x: Loud) {
    println!("consume {}", x.name);
}

#[inline(never)]
pub fn effect(label: &'static str) {
    println!("effect {}", label);
}

#[inline(never)]
pub fn may_panic(do_panic: bool) {
    if do_panic {
        panic!("explicit panic");
    }
}

#[inline(never)]
pub fn make(name: &'static str, do_panic: bool) -> Loud {
    if do_panic {
        panic!("constructor of {} panics", name);
    }
    Loud::new(name)
}

// ---- static / dead / conditional single-place drops -------------------------

#[inline(never)]
pub fn static_drop(c: bool) {
    let x = Loud::new("x");
    effect("body");
}

#[inline(never)]
pub fn dead_drop(c: bool) {
    let x = Loud::new("x");
    consume(x);
    effect("after");
}

#[inline(never)]
pub fn cond_move(c: bool) {
    let x = Loud::new("x");
    if c {
        consume(x);
    }
    effect("join");
}

#[inline(never)]
pub fn cond_init(c: bool) {
    let x;
    if c {
        x = Loud::new("x");
    }
    effect("join");
}

#[inline(never)]
pub fn loop_break_move(c: bool) {
    let x = Loud::new("x");
    let mut i = 0u32;
    loop {
        if c && i == 1 {
            consume(x);
            break;
        }
        i += 1;
        if i > 2 {
            break;
        }
    }
    effect("after-loop");
}

#[inline(never)]
pub fn early_return(c: bool) {
    let a = Loud::new("a");
    if c {
        return;
    }
    let b = Loud::new("b");
    effect("tail");
}

#[inline(never)]
pub fn two_cond_moves(c: bool) {
    let x = Loud::new("x");
    let y = Loud::new("y");
    if c {
        consume(x);
    } else {
        consume(y);
    }
    effect("join");
}

// ---- partial moves out of aggregates ----------------------------------------

#[inline(never)]
pub fn partial_move_tuple(c: bool) {
    let p = (Loud::new("p0"), Loud::new("p1"));
    consume(p.0);
    effect("after");
}

#[inline(never)]
pub fn cond_partial_move_tuple(c: bool) {
    let p = (Loud::new("p0"), Loud::new("p1"));
    if c {
        consume(p.0);
    }
    effect("join");
}

#[inline(never)]
pub fn cond_partial_move_struct(c: bool) {
    let s = Triple { a: Loud::new("s.a"), b: Loud::new("s.b"), c: Loud::new("s.c") };
    if c {
        consume(s.b);
    }
    effect("join");
}

#[inline(never)]
pub fn cond_partial_move_nested(c: bool) {
    let n = ((Loud::new("n00"), Loud::new("n01")), Loud::new("n1"));
    if c {
        consume((n.0).1);
    }
    effect("join");
}

#[inline(never)]
pub fn option_cond_move(c: bool) {
    let o = Some(Loud::new("o"));
    if c {
        if let Some(v) = o {
            consume(v);
        }
    }
    effect("join");
}

#[inline(never)]
pub fn box_cond_move(c: bool) {
    let b = Box::new(Loud::new("boxed"));
    if c {
        consume(*b);
    }
    effect("join");
}

#[inline(never)]
pub fn array_cond_move(c: bool) {
    let arr = [Loud::new("arr0"), Loud::new("arr1")];
    if c {
        let [first, _] = arr;
        consume(first);
    }
    effect("join");
}

#[inline(never)]
pub fn array_static_drop(c: bool) {
    let arr = [Loud::new("arr0"), Loud::new("arr1")];
    effect("body");
}

#[inline(never)]
pub fn generic_cond_move<T>(x: T, c: bool) {
    if c {
        drop(x);
    }
    effect("join");
}

#[inline(never)]
pub fn generic_cond_move_loud(c: bool) {
    generic_cond_move(Loud::new("g"), c);
}

#[inline(never)]
pub fn generic_cond_move_copy(c: bool) {
    generic_cond_move(Plain(7), c);
}

// ---- assignment overwriting an initialized place -----------------------------

#[inline(never)]
pub fn assign_overwrite(c: bool) {
    let mut x = Loud::new("old");
    x = make("new", c);
    effect("after-assign");
}

#[inline(never)]
pub fn assign_overwrite_old_dtor_panics(c: bool) {
    let mut x = Loud::bomb("old");
    x = Loud::new("new");
    effect("after-assign");
}

#[inline(never)]
pub fn cond_assign_overwrite(c: bool) {
    let mut x = Loud::new("old");
    if c {
        consume(x);
    }
    x = Loud::new("new");
    effect("after-assign");
}

// ---- panics inside destructors -----------------------------------------------

#[inline(never)]
pub fn dtor_panics_normal_path(c: bool) {
    let b = Loud::new("b");
    let a = Loud::bomb("a");
    effect("body");
}

#[inline(never)]
pub fn tuple_first_dtor_panics(c: bool) {
    let t = (Loud::bomb("t0"), Loud::new("t1"), Loud::new("t2"));
    effect("body");
}

#[inline(never)]
pub fn tuple_two_dtors_panic(c: bool) {
    let t = (Loud::bomb("t0"), Loud::bomb("t1"), Loud::new("t2"));
    effect("body");
}

#[inline(never)]
pub fn double_panic(c: bool) {
    let b = Loud::new("b");
    let a = Loud::bomb("a");
    may_panic(true);
}

#[inline(never)]
pub fn static_glue_in_cleanup(c: bool) {
    let after = Loud::new("after");
    let t = (Loud::bomb("t0"), Loud::new("t1"), Loud::new("t2"));
    may_panic(true);
}

#[inline(never)]
pub fn open_ladder_in_cleanup(c: bool) {
    let after = Loud::new("after");
    let t = (Loud::bomb("t0"), Loud::new("t1"), Loud::new("t2"));
    if c {
        consume(t.2);
    }
    may_panic(true);
}

#[inline(never)]
pub fn open_ladder_normal_two_panics(c: bool) {
    let t = (Loud::bomb("t0"), Loud::bomb("t1"), Loud::new("t2"));
    if c {
        consume(t.2);
    }
    effect("body");
}

// ---- needs_drop = false -------------------------------------------------------

#[inline(never)]
pub fn manually_drop(c: bool) {
    let m = ManuallyDrop::new(Loud::new("m"));
    effect("body");
}

#[inline(never)]
pub fn maybe_uninit(c: bool) {
    let u: MaybeUninit<Loud> = MaybeUninit::new(Loud::new("u"));
    effect("body");
}

#[inline(never)]
pub fn copy_type(c: bool) {
    let p = Plain(3);
    let q = p;
    effect("body");
}

// ---- function whose ABI cannot unwind ----------------------------------------

#[inline(never)]
pub extern "C" fn nounwind_abi(c: bool) {
    let g = Loud::new("g");
    may_panic(c);
    effect("body");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let name = args.get(1).map(String::as_str).unwrap_or("");
    let c = args.get(2).map(String::as_str) == Some("1");
    match name {
        "static_drop" => static_drop(c),
        "dead_drop" => dead_drop(c),
        "cond_move" => cond_move(c),
        "cond_init" => cond_init(c),
        "loop_break_move" => loop_break_move(c),
        "early_return" => early_return(c),
        "two_cond_moves" => two_cond_moves(c),
        "partial_move_tuple" => partial_move_tuple(c),
        "cond_partial_move_tuple" => cond_partial_move_tuple(c),
        "cond_partial_move_struct" => cond_partial_move_struct(c),
        "cond_partial_move_nested" => cond_partial_move_nested(c),
        "option_cond_move" => option_cond_move(c),
        "box_cond_move" => box_cond_move(c),
        "array_cond_move" => array_cond_move(c),
        "array_static_drop" => array_static_drop(c),
        "generic_cond_move_loud" => generic_cond_move_loud(c),
        "generic_cond_move_copy" => generic_cond_move_copy(c),
        "assign_overwrite" => assign_overwrite(c),
        "assign_overwrite_old_dtor_panics" => assign_overwrite_old_dtor_panics(c),
        "cond_assign_overwrite" => cond_assign_overwrite(c),
        "dtor_panics_normal_path" => dtor_panics_normal_path(c),
        "tuple_first_dtor_panics" => tuple_first_dtor_panics(c),
        "tuple_two_dtors_panic" => tuple_two_dtors_panic(c),
        "double_panic" => double_panic(c),
        "static_glue_in_cleanup" => static_glue_in_cleanup(c),
        "open_ladder_in_cleanup" => open_ladder_in_cleanup(c),
        "open_ladder_normal_two_panics" => open_ladder_normal_two_panics(c),
        "manually_drop" => manually_drop(c),
        "maybe_uninit" => maybe_uninit(c),
        "copy_type" => copy_type(c),
        "nounwind_abi" => nounwind_abi(c),
        other => {
            eprintln!("unknown specimen {:?}", other);
            std::process::exit(2);
        }
    }
    println!("main-returned");
}
