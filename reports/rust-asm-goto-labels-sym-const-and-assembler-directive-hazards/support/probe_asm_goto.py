#!/usr/bin/env python3
"""Standalone probe for Rust asm_goto (label operands, asm_goto_with_outputs,
MIR drop elaboration, callbr LLVM IR, critical edges, llvm#74483, and vzeroupper).

Runs across pinned rustup toolchains without leaving temporary files behind.
"""
import json
import os
import subprocess
import tempfile
from pathlib import Path

TOOLCHAINS = ["nightly-2026-06-01", "1.99.1", "1.100.0", "nightly"]

def run(cmd, env=None, cwd=None):
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    p = subprocess.run(cmd, capture_output=True, text=True, env=merged_env, cwd=cwd)
    return p.returncode, p.stdout, p.stderr

def compile_snippet(tc, code, extra_args=None, bootstrap=False, crate_type="lib"):
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.rs"
        src.write_text(code)
        cmd = ["rustc", f"+{tc}", f"--crate-type={crate_type}", "--edition=2024", str(src), "--out-dir", td]
        if extra_args:
            cmd.extend(extra_args)
        env = {"RUSTC_BOOTSTRAP": "1"} if bootstrap else None
        rc, out, err = run(cmd, env=env, cwd=td)
        artifacts = {}
        for p in sorted(Path(td).rglob("*")):
            if p.is_file() and p.name != "probe.rs":
                rel = str(p.relative_to(td))
                if p.suffix in (".mir", ".ll", ".s"):
                    artifacts[rel] = p.read_text(errors="replace")
        return rc, out, err, artifacts

def compile_and_run_bin(tc, code, extra_args=None, bootstrap=False):
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.rs"
        bin_path = Path(td) / "probe_bin"
        src.write_text(code)
        cmd = ["rustc", f"+{tc}", "--edition=2024", str(src), "-o", str(bin_path)]
        if extra_args:
            cmd.extend(extra_args)
        env = {"RUSTC_BOOTSTRAP": "1"} if bootstrap else None
        rc, out, err = run(cmd, env=env, cwd=td)
        if rc != 0:
            return {"compile_rc": rc, "compile_err": err}
        rrc, rout, rerr = run([str(bin_path)], cwd=td)
        return {"compile_rc": 0, "run_rc": rrc, "run_out": rout, "run_err": rerr}

def main():
    results = {}

    # 1. Feature matrix & validation checks across all 4 toolchains
    validation_cases = {
        "stable_label_basic": """
use core::arch::asm;
pub unsafe fn f() { unsafe { asm!("jmp {}", label {}); } }
""",
        "stable_label_with_discarded_out_and_clobber_abi": """
use core::arch::asm;
pub unsafe fn f() {
    unsafe {
        asm!("jmp {}", label {}, out("rax") _, clobber_abi("C"));
    }
}
""",
        "stable_label_with_split_inout_discarded": """
use core::arch::asm;
pub unsafe fn f(a: u64) {
    unsafe {
        asm!("/* {0} */ jmp {1}", inout(reg) a => _, label {});
    }
}
""",
        "stable_label_with_real_out_rejected": """
use core::arch::asm;
pub unsafe fn f() -> u64 {
    let x: u64;
    unsafe { asm!("mov {}, 1", "jmp {}", out(reg) x, label {}); }
    x
}
""",
        "label_with_may_unwind_rejected": """
#![feature(asm_unwind)]
use core::arch::asm;
pub unsafe fn f() {
    unsafe { asm!("jmp {}", label {}, options(may_unwind)); }
}
""",
        "label_with_pure_nomem_out": """
#![feature(asm_goto_with_outputs)]
use core::arch::asm;
pub unsafe fn f(a: u64) -> u64 {
    let x: u64;
    unsafe { asm!("mov {}, {}", "jmp {}", out(reg) x, in(reg) a, label { return x + 1; }, options(pure, nomem)); }
    x
}
""",
        "label_with_pure_nomem_no_out_rejected": """
use core::arch::asm;
pub unsafe fn f() {
    unsafe { asm!("jmp {}", label {}, options(pure, nomem)); }
}
""",
        "label_with_noreturn_unit_type": """
use core::arch::asm;
pub unsafe fn f() -> u64 {
    let a: u64;
    unsafe {
        let _: () = asm!("jmp {}", label { a = 7; }, options(noreturn));
    }
    a
}
""",
        "label_with_noreturn_never_type_tail_expr": """
use core::arch::asm;
pub unsafe fn f() -> ! {
    unsafe {
        asm!("jmp {}", label { loop {} }, options(noreturn))
    }
}
""",
        "label_with_noreturn_never_type_loop_semi": """
use core::arch::asm;
pub unsafe fn f() -> ! {
    unsafe {
        asm!("jmp {}", label { loop {}; }, options(noreturn))
    }
}
""",
        "label_with_noreturn_never_type_return_no_semi": """
use core::arch::asm;
pub unsafe fn f() -> u64 {
    unsafe {
        asm!("jmp {}", label { return 42 }, options(noreturn))
    }
}
""",
        "label_with_noreturn_never_type_return_stmt": """
use core::arch::asm;
pub unsafe fn f() -> u64 {
    unsafe {
        asm!("jmp {}", label { return 42; }, options(noreturn))
    }
}
""",
        "label_with_noreturn_and_out_nightly": """
#![feature(asm_goto_with_outputs)]
use core::arch::asm;
pub unsafe fn f() -> u64 {
    let x: u64;
    unsafe {
        asm!("mov {}, 42", "jmp {}", out(reg) x, label { return x; }, options(noreturn));
    }
}
""",
        "label_safe_context_reset_rejects_unsafe": """
use core::arch::asm;
unsafe extern "C" { fn ext(); }
pub unsafe fn f() {
    unsafe { asm!("jmp {}", label { ext(); }); }
}
""",
        "transparent_drop_wrapper_out_rejected": """
use core::arch::asm;
#[repr(transparent)]
pub struct DropU64(u64);
impl Drop for DropU64 { fn drop(&mut self) {} }
pub unsafe fn f() -> DropU64 {
    let x: DropU64;
    unsafe { asm!("mov {}, 1", out(reg) x); }
    x
}
""",
    }

    val_results = {}
    for name, code in validation_cases.items():
        val_results[name] = {}
        for tc in TOOLCHAINS:
            rc, _, err, _ = compile_snippet(tc, code, ["--emit=metadata"])
            first_err = next((l for l in err.splitlines() if l.startswith("error")), "")
            val_results[name][tc] = {"rc": rc, "first_error": first_err, "full_err": err if rc != 0 else ""}
    results["validation_matrix"] = val_results

    # 2. Detailed MIR dump at Runtime(PostCleanup) and Runtime(Optimized) on nightly-2026-06-01 and nightly
    mir_probe_code = """
#![feature(asm_goto_with_outputs)]
use core::arch::asm;

pub struct DropGuard(pub u64);
impl Drop for DropGuard {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.0);
    }
}

#[unsafe(no_mangle)]
pub unsafe fn mir_fallthrough_and_drop(cond: u64) -> u64 {
    let g = DropGuard(10);
    let mut res = 0u64;
    unsafe {
        asm!(
            "test {c}, {c}",
            "jnz {lbl}",
            c = in(reg) cond,
            lbl = label {
                drop(g);
                res = 1;
            }
        );
    }
    res
}

#[unsafe(no_mangle)]
pub unsafe fn mir_noreturn_unit_label() -> u64 {
    let a: u64;
    unsafe {
        asm!(
            "jmp {lbl}",
            lbl = label { a = 99; },
            options(noreturn)
        );
    }
    a
}

#[unsafe(no_mangle)]
pub unsafe fn mir_goto_with_outputs_critical(mut a: u32) -> u32 {
    unsafe {
        asm!(
            "jmp {l1}",
            "jmp {l2}",
            l1 = label {},
            l2 = label {},
            inout("eax") a,
        );
    }
    a
}

#[unsafe(no_mangle)]
pub unsafe fn mir_dup_label_placeholder_with_out(a: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!(
            "mov {o}, {a}",
            "test {a}, {a}",
            "jz {lbl}",
            "jnz {lbl}",
            o = out(reg) out,
            a = in(reg) a,
            lbl = label { return out + 1; },
        );
    }
    out
}

#[unsafe(no_mangle)]
pub unsafe fn mir_noreturn_out_read_in_label() -> u64 {
    let x: u64;
    unsafe {
        asm!(
            "mov {x}, 42",
            "jmp {lbl}",
            x = out(reg) x,
            lbl = label { return x; },
            options(noreturn)
        );
    }
}
"""
    mir_results = {}
    for tc in ["nightly-2026-06-01", "nightly"]:
        rc, _, err, arts = compile_snippet(
            tc,
            mir_probe_code,
            [
                "-C", "opt-level=0",
                "--emit=llvm-ir",
                "-Z", "dump-mir=mir_fallthrough_and_drop | mir_noreturn_unit_label | mir_goto_with_outputs_critical | mir_dup_label_placeholder_with_out | mir_noreturn_out_read_in_label",
                "-Z", "dump-mir-exclude-pass-number",
            ],
            bootstrap=True,
        )
        selected = {}
        for k, v in arts.items():
            if "runtime-post-cleanup" in k or "runtime-optimized" in k or k.endswith(".ll"):
                selected[k] = v
        mir_results[tc] = {"rc": rc, "err": err, "files": list(selected.keys()), "artifacts": selected}
    results["mir_and_ir"] = mir_results

    # 3. Execute llvm#74483 (goto_multi_out) + heavier multi-out stress + dup-label-placeholder across -O0 and -O3
    runtime_code = r"""
#![feature(asm_goto_with_outputs)]
use core::arch::asm;

#[inline(never)]
fn goto_multi_out(a: usize, b: usize) -> usize {
    let mut x: usize;
    let mut y: usize;
    let mut z: usize;
    unsafe {
        asm!(
            "mov {x}, {a}",
            "test {a}, {a}",
            "jnz {label1}",
            "/* {y} {z} {b} {label2} */",
            x = out(reg) x,
            y = out(reg) y,
            z = out(reg) z,
            a = in(reg) a,
            b = in(reg) b,
            label1 = label { return x },
            label2 = label { return 1 },
        );
        0
    }
}

#[inline(never)]
fn goto_5_outputs_both_edges(take: usize, seed: usize) -> usize {
    let (a, b, c, d, e): (usize, usize, usize, usize, usize);
    unsafe {
        asm!(
            "lea {a}, [{s} + 1]",
            "lea {b}, [{s} + 2]",
            "lea {c}, [{s} + 3]",
            "lea {d}, [{s} + 4]",
            "lea {e}, [{s} + 5]",
            "test {t}, {t}",
            "jnz {lbl}",
            a = out(reg) a,
            b = out(reg) b,
            c = out(reg) c,
            d = out(reg) d,
            e = out(reg) e,
            s = in(reg) seed,
            t = in(reg) take,
            lbl = label { return a + b + c + d + e + 1000; },
        );
    }
    a + b + c + d + e
}

#[inline(never)]
fn goto_dup_label(a: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!(
            "mov {o}, {a}",
            "add {o}, 10",
            "test {a}, {a}",
            "jz {lbl}",
            "jnz {lbl}",
            o = out(reg) out,
            a = in(reg) a,
            lbl = label { return out; },
        );
    }
    out + 1000
}

#[inline(never)]
fn goto_lateout_read_in_label(a: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!(
            "lea {o}, [{a} + 5]",
            "jmp {lbl}",
            o = lateout(reg) out,
            a = in(reg) a,
            lbl = label { return out; },
            options(noreturn),
        );
    }
}

#[inline(never)]
fn goto_drop_flag_test(take_label: bool) -> (u64, u64) {
    use core::sync::atomic::{AtomicU64, Ordering};
    static DROPS: AtomicU64 = AtomicU64::new(0);
    struct G(u64);
    impl Drop for G {
        fn drop(&mut self) { DROPS.fetch_add(self.0, Ordering::SeqCst); }
    }
    DROPS.store(0, Ordering::SeqCst);
    let g = G(1);
    let mut path = 0u64;
    let flag: u64 = if take_label { 1 } else { 0 };
    unsafe {
        asm!(
            "test {f}, {f}",
            "jnz {lbl}",
            f = in(reg) flag,
            lbl = label {
                drop(g);
                path = 100 + DROPS.load(Ordering::SeqCst);
            }
        );
    }
    let after_asm = DROPS.load(Ordering::SeqCst);
    (path, after_asm)
}

fn main() {
    let r_multi = goto_multi_out(11, 22);
    let r_5_fall = goto_5_outputs_both_edges(0, 10);
    let r_5_lbl = goto_5_outputs_both_edges(1, 10);
    let r_dup0 = goto_dup_label(0);
    let r_dup5 = goto_dup_label(5);
    let r_late = goto_lateout_read_in_label(37);
    let r_drop_fall = goto_drop_flag_test(false);
    let r_drop_lbl = goto_drop_flag_test(true);
    println!("multi_out={} r5=({},{}) dup=({},{}) late={} drop_fall={:?} drop_lbl={:?}",
             r_multi, r_5_fall, r_5_lbl, r_dup0, r_dup5, r_late, r_drop_fall, r_drop_lbl);
}
"""
    rt_results = {}
    for tc in ["nightly-2026-06-01", "nightly"]:
        rt_results[tc] = {}
        for opt in ["0", "3"]:
            rt_results[tc][f"O{opt}"] = compile_and_run_bin(tc, runtime_code, ["-C", f"opt-level={opt}"])
    results["runtime_tests"] = rt_results

    # 4. X86InsertVZeroUpper & flags across callbr (INLINEASM_BR) edges
    vzu_callbr_code = """
#![feature(asm_goto_with_outputs)]
use core::arch::asm;
use core::arch::x86_64::__m256i;

unsafe extern "C" {
    fn ext_sse_callee(x: u64);
}

#[unsafe(no_mangle)]
#[target_feature(enable = "avx2")]
pub unsafe fn callbr_vzu_typed_ymm(cond: u64) {
    let _tmp: __m256i;
    unsafe {
        asm!(
            "vpcmpeqb ymm0, ymm0, ymm0",
            "test {c}, {c}",
            "jnz {lbl}",
            c = in(reg) cond,
            lbl = label {
                unsafe { ext_sse_callee(1); }
            },
            out("ymm0") _tmp,
        );
        ext_sse_callee(2);
    }
}

#[unsafe(no_mangle)]
#[target_feature(enable = "avx2")]
pub unsafe fn callbr_vzu_discarded_ymm(cond: u64) {
    unsafe {
        asm!(
            "vpcmpeqb ymm0, ymm0, ymm0",
            "test {c}, {c}",
            "jnz {lbl}",
            c = in(reg) cond,
            lbl = label {
                unsafe { ext_sse_callee(1); }
            },
            out("ymm0") _,
        );
        ext_sse_callee(2);
    }
}

#[unsafe(no_mangle)]
pub unsafe fn callbr_flags_default(a: u64, b: u64) -> u64 {
    let cmp = a < b;
    unsafe {
        asm!(
            "test {a}, {a}",
            "jnz {lbl}",
            a = in(reg) a,
            lbl = label {
                return if cmp { 10 } else { 20 };
            }
        );
    }
    if cmp { 1 } else { 2 }
}

#[unsafe(no_mangle)]
pub unsafe fn callbr_flags_preserves(a: u64, b: u64) -> u64 {
    let cmp = a < b;
    unsafe {
        asm!(
            "/* {a} */",
            "jz {lbl}",
            a = in(reg) a,
            lbl = label {
                return if cmp { 10 } else { 20 };
            },
            options(preserves_flags)
        );
    }
    if cmp { 1 } else { 2 }
}
"""
    vzu_results = {}
    for tc in ["nightly-2026-06-01", "nightly"]:
        rc, _, err, arts = compile_snippet(tc, vzu_callbr_code, ["-C", "opt-level=3", "--emit=llvm-ir,asm"])
        vzu_results[tc] = {"rc": rc, "err": err, "asm": arts.get("probe.s", ""), "ll": arts.get("probe.ll", "")}
    results["vzu_and_flags_callbr"] = vzu_results

    print("=== VALIDATION MATRIX ===")
    for k, v in val_results.items():
        summary = {tc: (d["rc"], d["first_error"][:95]) for tc, d in v.items()}
        print(f"  {k}: {summary}")

    print("\n=== SPECIAL ERROR DETAIL: label_with_noreturn_never_type_tail_expr ===")
    print(val_results["label_with_noreturn_never_type_tail_expr"]["nightly"]["full_err"])
    print("\n=== SPECIAL ERROR DETAIL: transparent_drop_wrapper_out_rejected ===")
    print(val_results["transparent_drop_wrapper_out_rejected"]["nightly"]["full_err"])

    print("\n=== RUNTIME TESTS ===")
    for tc, opts in rt_results.items():
        for opt, res in opts.items():
            print(f"  {tc} -{opt}: {res}")

    print("\n=== VZU & FLAGS CALLBR ASM (nightly -O3) ===")
    asm_txt = vzu_results["nightly"]["asm"]
    for fn in ["callbr_vzu_typed_ymm:", "callbr_vzu_discarded_ymm:", "callbr_flags_default:", "callbr_flags_preserves:"]:
        idx = asm_txt.find(fn)
        if idx != -1:
            end = asm_txt.find(".Lfunc_end", idx)
            print(asm_txt[idx:end if end != -1 else idx+900])

    print("\n=== NORETURN OUT READ IN LABEL LLVM IR (nightly -O0) ===")
    ll_txt = mir_results["nightly"]["artifacts"].get("probe.ll", "")
    idx = ll_txt.find("@mir_noreturn_out_read_in_label")
    if idx != -1:
        end = ll_txt.find("\n}\n", idx)
        print(ll_txt[idx:end+3])

    out_path = os.environ.get("PROBE_OUT")
    if out_path:
        Path(out_path).write_text(json.dumps(results, indent=2))

if __name__ == "__main__":
    main()
