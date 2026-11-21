extern crate crate_callee;

use crate_callee::{
    callee_cast_12, callee_direct, callee_indirect_sret, callee_noreturn_panic, callee_pair_niche,
    record_event, take_events, BigSretDrop, DropToken, MixedCast12, CALLEE_GLOBAL_BIAS,
};
use std::num::NonZeroU64;
use std::panic::{catch_unwind, AssertUnwindSafe};

/// Aggregate with no custom `Drop` impl whose 2 fields have `Drop` glue (`build_drop_shim` ladder).
pub struct StaticPair {
    pub f0: DropToken,
    pub f1: DropToken,
}

/// Aggregate with 3 fields used for double-panic comparison (`Static` `drop_in_place` vs `Open` inline cleanup).
pub struct TripleFields {
    pub f0: DropToken,
    pub f1: DropToken,
    pub f2: DropToken,
}

#[inline(never)]
fn consume_token(tok: DropToken) {
    record_event(&format!("consume:{}", tok.label));
    drop(tok);
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum AbiCase {
    Direct = 0,
    PairNiche = 1,
    Cast12 = 2,
    IndirectSret = 3,
}

/// Exercises `Static`, `Conditional`, and partial-move `Open` drop ladders simultaneously
/// across all 4 cross-crate `FnAbi` `PassMode` variants (`Direct`, `Pair`, `Cast`, `Indirect` sret).
#[no_mangle]
#[inline(never)]
pub fn caller_four_way_seam(case: AbiCase, cond_move: bool, callee_panics: bool) -> u64 {
    // 1. Static drop local: never moved out before or after the call (`DropStyle::Static`).
    let _static_pair = StaticPair {
        f0: DropToken::new("static_0"),
        f1: DropToken::new("static_1"),
    };

    // 2. Conditional drop local: moved on one branch before the cross-crate invoke (`DropStyle::Conditional`).
    let cond_tok = DropToken::new("cond_0");
    if cond_move {
        consume_token(cond_tok);
    }

    // 3. Partial-move Open drop local: `.1` is unconditionally moved before the invoke (`DropStyle::Open`),
    // while `.0` and `.2` remain live and must be dropped in declaration order `.0` then `.2`.
    let open_triple = (
        DropToken::new("open_0"),
        DropToken::new("open_1"),
        DropToken::new("open_2"),
    );
    consume_token(open_triple.1);

    let out = match case {
        AbiCase::Direct => callee_direct(42, callee_panics),
        AbiCase::PairNiche => {
            let inp = Some((NonZeroU64::new(99).unwrap(), 500));
            let res = callee_pair_niche(inp, callee_panics);
            let (nz, v) = res.unwrap();
            nz.get() + v
        }
        AbiCase::Cast12 => {
            let inp = MixedCast12 { a: 10, b: 20, c: 1.5 };
            let res = callee_cast_12(inp, callee_panics);
            (res.a as u64) + (res.b as u64) + (res.c as u64)
        }
        AbiCase::IndirectSret => {
            let sret_val: BigSretDrop = callee_indirect_sret(1000, callee_panics);
            record_event("caller:received_sret");
            sret_val.words[0] + sret_val.words[3]
        }
    };

    record_event("caller:normal_after_call");
    // Read cross-crate static to ensure `R_X86_64_GOTPCREL` / `R_X86_64_REX_GOTPCRELX` data load in caller.
    let global_low = unsafe { std::ptr::read_volatile(&CALLEE_GLOBAL_BIAS) } & 0xff;
    out.wrapping_add(global_low)
}

/// Trailing `noreturn` cross-crate `invoke` (`-> !`) with live `DropToken` cleanup.
/// Under `NoTrapAfterNoreturn = true`, the diverging call has no trailing `ud2`;
/// `ret_rip - 1` must still resolve inside the caller's FDE and LSDA `[cs_start, cs_start + cs_len)`.
#[no_mangle]
#[inline(never)]
pub fn caller_trailing_noreturn_with_cleanup(tag: u64) -> ! {
    let _guard = DropToken::new("trailing_cleanup_guard");
    callee_noreturn_panic(tag)
}

/// Pure tail-end `noreturn` call with NO local cleanup (`cs_lpad == 0` / no landing pad),
/// so `call callee_noreturn_panic` sits at the literal last bytes `[fde_end - call_len, fde_end)`
/// of the function's FDE (`ret_rip == fde_end`)!
#[no_mangle]
#[inline(never)]
pub fn caller_bare_trailing_noreturn(tag: u64) -> ! {
    callee_noreturn_panic(tag)
}

/// Exact 16-byte-aligned variant (`push %rax` + `9`-byte setup + `6`-byte `call *got` = `16` B in PIC,
/// or `push %rax` + `add` + `call` = `16` B) to observe zero-padding adjacency (`fde_end == next_fde.pc_begin`).
#[no_mangle]
#[inline(never)]
pub fn caller_aligned_trailing_noreturn(tag: u64) -> ! {
    callee_noreturn_panic(tag.wrapping_add(0x1122_3344))
}

/// Adjacent function placed right after `caller_aligned_trailing_noreturn` to observe
/// inter-function padding (`0xCC` in `rust-lld` vs. `NOP` in `GNU ld`, or `0` bytes if 16B-aligned).
#[no_mangle]
#[inline(never)]
pub fn adjacent_after_noreturn(x: u64) -> u64 {
    std::hint::black_box(x.wrapping_mul(3).wrapping_add(1))
}

/// `>32 KiB` (`41,500` B = `10 * 4096 + 540` B) stack frame triggering
/// `X86FrameLowering::emitStackProbeInlineGenericLoop` (`4096`-byte stack-clash loop with
/// `DW_CFA_def_cfa_register %r11` plus a non-zero `TailOffset` remainder) at both `-O0` and `-O2`.
#[no_mangle]
#[inline(never)]
pub fn caller_stack_clash_loop_unwind(should_panic: bool) -> u64 {
    let mut big_buf = [0u8; 41500];
    let _guard = DropToken::new("stack_clash_40k_guard");
    unsafe {
        std::ptr::write_volatile(&mut big_buf[0], 0xAA);
        std::ptr::write_volatile(&mut big_buf[41499], 0x55);
    }
    std::hint::black_box(big_buf.as_mut_ptr());
    let v = callee_direct(
        (unsafe { std::ptr::read_volatile(&big_buf[0]) } as u64)
            + (unsafe { std::ptr::read_volatile(&big_buf[41499]) } as u64),
        should_panic,
    );
    std::hint::black_box(&big_buf);
    v
}

/// Double-panic Variant A (`DropStyle::Static`):
/// `TripleFields` is never partially moved, so `caller`'s cleanup block calls `drop_in_place::<TripleFields>`
/// (`unwind terminate(cleanup)`). Inside `drop_in_place`, `f0` panics, entering `drop_in_place`'s own
/// cleanup half-ladder, which runs BOTH `f1` and `f2` destructors BEFORE `_Unwind_Resume` hits `terminate`!
#[no_mangle]
#[inline(never)]
pub fn caller_double_panic_static() {
    let _triple = TripleFields {
        f0: DropToken::bomb("dp_static_f0_bomb"),
        f1: DropToken::new("dp_static_f1_sibling"),
        f2: DropToken::new("dp_static_f2_sibling"),
    };
    let _ = callee_direct(1, true);
}

/// Double-panic Variant B (`DropStyle::Open`):
/// Moving `_triple.2` before the call forces `ElaborateDrops` to open-drop `_triple.0` then `_triple.1`
/// INLINE inside `caller`'s cleanup block (`data.is_cleanup == true`), so `_triple.0`'s drop terminator
/// carries `UnwindAction::Terminate(Reason::InCleanup)` directly! When `f0` panics, `rust_eh_personality`
/// installs the `filter_landing_pad` (`panic_in_cleanup`) immediately, aborting BEFORE `f1` ever runs!
#[no_mangle]
#[inline(never)]
pub fn caller_double_panic_open() {
    let triple = TripleFields {
        f0: DropToken::bomb("dp_open_f0_bomb"),
        f1: DropToken::new("dp_open_f1_sibling"),
        f2: DropToken::new("dp_open_f2_moved"),
    };
    consume_token(triple.f2);
    let _ = callee_direct(1, true);
}

fn run_single_scenario(name: &str, case: AbiCase, cond_move: bool, callee_panics: bool) -> String {
    let _ = take_events();
    let res = catch_unwind(AssertUnwindSafe(|| {
        caller_four_way_seam(case, cond_move, callee_panics)
    }));
    let events = take_events();
    let outcome = match res {
        Ok(v) => format!("ok:{}", v),
        Err(_) => "unwound".to_string(),
    };
    format!("{}|{}|{}", name, outcome, events.join(","))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        match args[1].as_str() {
            "double_panic_static" => {
                let _ = catch_unwind(AssertUnwindSafe(caller_double_panic_static));
                return;
            }
            "double_panic_open" => {
                let _ = catch_unwind(AssertUnwindSafe(caller_double_panic_open));
                return;
            }
            _ => {}
        }
    }

    let cases = [
        ("direct", AbiCase::Direct),
        ("pair_niche", AbiCase::PairNiche),
        ("cast12", AbiCase::Cast12),
        ("indirect_sret", AbiCase::IndirectSret),
    ];
    for (cname, ckind) in cases {
        for cond_move in [false, true] {
            for callee_panics in [false, true] {
                let label = format!(
                    "{}_cm{}_pan{}",
                    cname,
                    if cond_move { 1 } else { 0 },
                    if callee_panics { 1 } else { 0 }
                );
                println!("{}", run_single_scenario(&label, ckind, cond_move, callee_panics));
            }
        }
    }

    // Trailing noreturn with cleanup
    let _ = take_events();
    let r_tn1 = catch_unwind(AssertUnwindSafe(|| caller_trailing_noreturn_with_cleanup(77)));
    assert!(r_tn1.is_err());
    println!("trailing_noreturn_cleanup|unwound|{}", take_events().join(","));

    // Bare trailing noreturn (`ret_rip == fde_end`)
    let _ = take_events();
    let r_tn2 = catch_unwind(AssertUnwindSafe(|| caller_bare_trailing_noreturn(88)));
    assert!(r_tn2.is_err());
    println!(
        "bare_trailing_noreturn|unwound:adj={}|{}",
        adjacent_after_noreturn(10),
        take_events().join(",")
    );

    // Aligned trailing noreturn (`fde_end % 16 == 0` check)
    let _ = take_events();
    let r_tn3 = catch_unwind(AssertUnwindSafe(|| caller_aligned_trailing_noreturn(99)));
    assert!(r_tn3.is_err());
    println!("aligned_trailing_noreturn|unwound|{}", take_events().join(","));

    // >32 KiB stack-clash probe loop normal + unwind
    let _ = take_events();
    let r_sc_ok = caller_stack_clash_loop_unwind(false);
    println!("stack_clash_40k_ok|ok:{}|{}", r_sc_ok, take_events().join(","));

    let _ = take_events();
    let r_sc_unw = catch_unwind(AssertUnwindSafe(|| caller_stack_clash_loop_unwind(true)));
    assert!(r_sc_unw.is_err());
    println!("stack_clash_40k_unwind|unwound|{}", take_events().join(","));
}
