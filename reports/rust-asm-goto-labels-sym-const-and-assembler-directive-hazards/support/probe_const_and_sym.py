#!/usr/bin/env python3
"""Standalone probe for Rust inline assembly `const` and `sym` operands:
- Runtime(PostCleanup) vs Runtime(Optimized) MIR representations (including generics)
- Signed/unsigned/128-bit/negative/default-i32 formatting (asm_const_to_str)
- RFC 3848 `asm_const_ptr` across 1.98-nightly vs 1.99.1 vs 1.102-nightly
  (pointers with/without provenance, static+offset, negative offset, ZST align, closures, wide ptrs)
- SymFn / SymStatic (generic fn, static, static mut, #[thread_local], #[export_name],
  #[link_name], #[linkage = "weak"], PIC/GOT/PLT/TPOFF ELF relocations)
- Monomorphization & dead-code reachability via `sym` in comments vs raw strings.
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
                elif p.suffix == ".o":
                    _, r_rel, _ = run(["readelf", "-rW", str(p)])
                    _, r_sym, _ = run(["readelf", "-sW", str(p)])
                    _, r_obj, _ = run(["objdump", "-dr", "-M", "intel", str(p)])
                    artifacts[rel + ".readelf_r"] = r_rel
                    artifacts[rel + ".readelf_s"] = r_sym
                    artifacts[rel + ".objdump"] = r_obj
        return rc, out, err, artifacts

def main():
    results = {}

    # 1. Const formatting, edge cases, and asm_const_ptr matrix across toolchains
    const_cases = {
        "signed_unsigned_and_128bit": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn const_fmt() {
    unsafe {
        asm!(
            "/* def={def} i8min={i8m} u8max={u8m} i64min={i64m} u64max={u64m} i128min={i128m} u128max={u128m} */",
            "add rax, {neg}",
            "mov rax, [rdi + {neg_off}]",
            def = const -1,
            i8m = const i8::MIN,
            u8m = const u8::MAX,
            i64m = const i64::MIN,
            u64m = const u64::MAX,
            i128m = const i128::MIN,
            u128m = const u128::MAX,
            neg = const -5i32,
            neg_off = const -8i32,
            out("rax") _,
            in("rdi") 0usize,
        );
    }
}
""",
        "const_u128_in_mov_fails_mc": r"""
use core::arch::asm;
pub unsafe fn f() {
    unsafe { asm!("mov rax, {}", const u128::MAX, out("rax") _); }
}
""",
        "const_u128_in_octa_ok": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn const_octa() {
    unsafe { asm!("jmp 2f", ".octa {}", "2:", const u128::MAX); }
}
""",
        "const_att_negative": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn const_att_neg() -> i64 {
    let mut x: i64 = 10;
    unsafe { asm!("addq ${c}, {x}", c = const -3i32, x = inout(reg) x, options(att_syntax)); }
    x
}
""",
        "const_zst_unit_rejected": r"""
use core::arch::asm;
pub unsafe fn f() { unsafe { asm!("/* {} */", const ()); } }
""",
        "const_bool_rejected": r"""
use core::arch::asm;
pub unsafe fn f() { unsafe { asm!("/* {} */", const true); } }
""",
        "const_ptr_without_feature_rejected": r"""
use core::arch::asm;
static S: u64 = 1;
pub unsafe fn f() { unsafe { asm!("/* {} */", const &S as *const u64); } }
""",
        "const_ptr_with_feature": r"""
#![feature(asm_const_ptr)]
use core::arch::asm;

static MY_ARR: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

#[repr(align(16))]
struct ZstAlign16;
static ZST_STATIC: ZstAlign16 = ZstAlign16;

extern "C" fn target_fn() {}

#[unsafe(no_mangle)]
pub unsafe fn const_ptr_kinds() {
    unsafe {
        asm!(
            "/* raw_int={raw_int} st={st} st_pos={st_pos} st_neg={st_neg} zst_const={zst_c} zst_static={zst_s} promoted={prom} fn_item={fni} closure={clo} */",
            raw_int = const (0x1234usize as *const u8),
            st = const (&MY_ARR as *const [u8; 8]),
            st_pos = const ((&MY_ARR as *const [u8; 8]).cast::<u8>().wrapping_add(3)),
            st_neg = const ((&MY_ARR as *const [u8; 8]).cast::<u8>().wrapping_sub(4)),
            zst_c = const (&ZstAlign16 as *const ZstAlign16),
            zst_s = const (&ZST_STATIC as *const ZstAlign16),
            prom = const (&42u32 as *const u32),
            fni = const target_fn,
            clo = const (|| {}),
        );
    }
}
""",
        "const_ptr_wide_rejected": r"""
#![feature(asm_const_ptr)]
use core::arch::asm;
pub unsafe fn f() { unsafe { asm!("/* {} */", const ("hi" as *const str)); } }
""",
    }

    const_results = {}
    for name, code in const_cases.items():
        const_results[name] = {}
        for tc in TOOLCHAINS:
            emit = "--emit=obj,llvm-ir,asm" if name in ("signed_unsigned_and_128bit", "const_u128_in_mov_fails_mc", "const_u128_in_octa_ok", "const_att_negative", "const_ptr_with_feature") else "--emit=metadata"
            rc, _, err, arts = compile_snippet(tc, code, [emit])
            first_err = next((l for l in err.splitlines() if l.startswith("error")), "")
            entry = {"rc": rc, "first_error": first_err}
            if rc == 0 and "probe.ll" in arts:
                entry["ll"] = arts["probe.ll"]
            if rc == 0 and "probe.s" in arts:
                entry["asm"] = arts["probe.s"]
            const_results[name][tc] = entry
    results["const_matrix"] = const_results

    # 2. Generic const + generic SymFn + SymStatic MIR at Runtime(PostCleanup) vs Runtime(Optimized)
    mir_code = r"""
#![feature(thread_local, linkage)]
use core::arch::{asm, global_asm};

static IMMUT_ST: u64 = 0x11223344;
static mut MUT_ST: u64 = 0x55667788;
#[thread_local]
static TLS_ST: u64 = 0x99aabbcc;

unsafe extern "C" {
    #[link_name = "custom_ext_sym"]
    static EXT_LINK_ST: u64;
    #[link_name = "custom_ext_fn"]
    fn ext_link_fn();
}

#[unsafe(export_name = "exported_rust_fn")]
#[inline(never)]
pub extern "C" fn rust_exported_fn() -> u64 { 7 }

#[linkage = "weak"]
#[unsafe(no_mangle)]
pub static WEAK_ST: u64 = 123;

#[inline(never)]
fn generic_callee<T: Copy>(x: T) -> T { x }

#[inline(never)]
fn only_in_asm_comment_fn<T>() -> usize { core::mem::size_of::<T>() }

static ONLY_IN_ASM_COMMENT_ST: u64 = 0xdead_beef_cafe_babe;

pub unsafe fn generic_const_and_sym<T: Copy, const N: i32>() {
    unsafe {
        asm!(
            "/* const_param={n} const_expr={np1} */",
            "/* sym_generic={gf} */",
            "/* sym_immut={si} sym_mut={sm} sym_tls={st} sym_ext_st={ses} sym_ext_fn={sef} sym_exp={sexp} sym_weak={sw} */",
            n = const N,
            np1 = const (N + 1),
            gf = sym generic_callee::<T>,
            si = sym IMMUT_ST,
            sm = sym MUT_ST,
            st = sym TLS_ST,
            ses = sym EXT_LINK_ST,
            sef = sym ext_link_fn,
            sexp = sym rust_exported_fn,
            sw = sym WEAK_ST,
        );
    }
}

#[unsafe(no_mangle)]
pub unsafe fn concrete_caller_pic_relocs() -> u64 {
    let val: u64;
    unsafe {
        generic_const_and_sym::<u32, -42>();
        asm!(
            "/* keep_alive={ka_fn} {ka_st} */",
            "call {exp}",
            "add rax, qword ptr [rip + {st}]",
            "add rax, qword ptr fs:[{tls}@TPOFF]",
            ka_fn = sym only_in_asm_comment_fn::<u64>,
            ka_st = sym ONLY_IN_ASM_COMMENT_ST,
            exp = sym rust_exported_fn,
            st = sym IMMUT_ST,
            tls = sym TLS_ST,
            out("rax") val,
            clobber_abi("C"),
        );
    }
    val
}

#[unsafe(no_mangle)]
pub unsafe fn pic_call_plt_vs_direct() {
    unsafe {
        asm!(
            "call {f}@PLT",
            "lea rax, [rip + {s}@GOTPCREL]",
            f = sym ext_link_fn,
            s = sym EXT_LINK_ST,
            out("rax") _,
            clobber_abi("C"),
        );
    }
}

global_asm!(
    "/* global_asm_sym={gfn} */",
    gfn = sym only_in_asm_comment_fn::<u16>,
);
"""
    sym_results = {}
    for tc in ["nightly-2026-06-01", "nightly"]:
        rc, _, err, arts = compile_snippet(
            tc,
            mir_code,
            [
                "-C", "opt-level=2",
                "-C", "relocation-model=pic",
                "--emit=llvm-ir,asm,obj",
                "-Z", "dump-mir=generic_const_and_sym | concrete_caller_pic_relocs",
                "-Z", "dump-mir-exclude-pass-number",
            ],
            bootstrap=True,
        )
        sym_results[tc] = {"rc": rc, "err": err, "artifacts": arts}
    results["sym_and_generic_mir"] = sym_results

    # 3. Dead-code reachability test: raw string symbol vs `sym` operand in executable link
    reach_sym_ok = r"""
#[inline(never)]
#[unsafe(no_mangle)]
fn hidden_target() -> u64 { 123 }

fn main() {
    let x: u64;
    unsafe {
        core::arch::asm!(
            "call {}",
            sym hidden_target,
            out("rax") x,
            clobber_abi("C"),
        );
    }
    assert_eq!(x, 123);
}
"""
    reach_raw_generic_fail = r"""
#[inline(never)]
fn generic_never_called<T>() -> usize { core::mem::size_of::<T>() }

fn main() {
    // Even if we guessed a symbol name in raw text, generic_never_called::<u128> is never monomorphized!
    unsafe {
        core::arch::asm!("/* raw text only */");
    }
    let _ = generic_never_called::<u8>;
}
"""
    reach_private_fn_sym_in_comment = r"""
#[inline(never)]
fn private_generic_only_in_sym_comment<T>() -> usize {
    core::hint::black_box(core::mem::size_of::<T>())
}
static PRIVATE_STATIC_ONLY_IN_SYM_COMMENT: u64 = 0x1337_c0de;

#[unsafe(no_mangle)]
pub fn entry() {
    unsafe {
        core::arch::asm!(
            "/* {f} {s} */",
            f = sym private_generic_only_in_sym_comment::<[u8; 37]>,
            s = sym PRIVATE_STATIC_ONLY_IN_SYM_COMMENT,
        );
    }
}
"""
    rc_reach, _, err_reach, arts_reach = compile_snippet("nightly", reach_private_fn_sym_in_comment, ["-C", "opt-level=2", "--emit=obj,llvm-ir"])
    syms_in_obj = [l for l in arts_reach.get("probe.o.readelf_s", "").splitlines()
                   if "private_generic_only_in_sym_comment" in l or "PRIVATE_STATIC_ONLY_IN_SYM_COMMENT" in l]
    results["mono_reachability"] = {
        "rc": rc_reach,
        "err": err_reach,
        "matching_elf_symbols": syms_in_obj,
        "ll_has_fn": "private_generic_only_in_sym_comment" in arts_reach.get("probe.ll", ""),
        "ll_has_static": "PRIVATE_STATIC_ONLY_IN_SYM_COMMENT" in arts_reach.get("probe.ll", ""),
    }

    # 4. Additional `sym` target edge cases (trait method, #[track_caller] reify shim, ZST static,
    #    extern_weak, const item rejected, and core_intrinsics reification ICE)
    sym_edge_cases = {
        "sym_const_item_rejected": ('use core::arch::asm; const C: u64 = 1; pub fn f() { unsafe { asm!("/* {} */", sym C); } }', ["--emit=metadata"]),
        "sym_trait_method": ('use core::arch::asm; trait T { fn m(); } impl T for u32 { fn m() {} } pub fn f() { unsafe { asm!("/* {} */", sym <u32 as T>::m); } }', ["--emit=obj"]),
        "sym_track_caller_reify_shim": ('use core::arch::asm; #[track_caller] fn tc() -> u32 { core::panic::Location::caller().line() } #[unsafe(no_mangle)] pub fn f() { unsafe { asm!("/* {} */", sym tc); } }', ["--emit=llvm-ir"]),
        "sym_zst_static": ('use core::arch::asm; static Z: () = (); pub fn f() { unsafe { asm!("/* {} */", sym Z); } }', ["--emit=obj"]),
        "sym_extern_weak": ('#![feature(linkage)] use core::arch::asm; unsafe extern "C" { #[linkage = "extern_weak"] static EW: *const u8; } pub fn f() { unsafe { asm!("/* {} */", sym EW); } }', ["--emit=obj"]),
        "sym_intrinsic_reify_ice": ('#![feature(core_intrinsics)] use core::arch::asm; pub fn f() { unsafe { asm!("/* {} */", sym core::intrinsics::black_box::<u64>); } }', ["--emit=llvm-ir"]),
    }
    sym_edges = {}
    for name, (code, args) in sym_edge_cases.items():
        rc, _, err, arts = compile_snippet("nightly", code, args)
        first_err = next((l for l in err.splitlines() if l.startswith("error")), "")
        sym_edges[name] = {
            "rc": rc,
            "first_error": first_err,
            "has_reify_shim": "reify" in arts.get("probe.ll", ""),
        }
    results["sym_edge_cases"] = sym_edges

    print("=== CONST MATRIX ===")
    for name, tc_map in const_results.items():
        print(f"  {name}: " + str({tc: (d["rc"], d["first_error"][:90]) for tc, d in tc_map.items()}))

    print("\n=== CONST_FMT LLVM IR (nightly) ===")
    ll = const_results["signed_unsigned_and_128bit"]["nightly"].get("ll", "")
    idx = ll.find("@const_fmt")
    if idx != -1:
        print(ll[idx:ll.find("\n}\n", idx)+3])

    print("\n=== CONST_PTR_WITH_FEATURE LLVM IR (nightly) ===")
    ll2 = const_results["const_ptr_with_feature"]["nightly"].get("ll", "")
    idx = ll2.find("@const_ptr_kinds")
    if idx != -1:
        print(ll2[idx:ll2.find("\n}\n", idx)+3])

    print("\n=== GENERIC CONST & SYM MIR (nightly runtime-post-cleanup) ===")
    for k, v in sym_results["nightly"]["artifacts"].items():
        if "generic_const_and_sym" in k and "runtime-post-cleanup" in k:
            print(f"--- {k} ---")
            print(v)

    print("\n=== SYM ELF RELOCATIONS (nightly PIC) ===")
    print(sym_results["nightly"]["artifacts"].get("probe.o.readelf_r", ""))

    print("\n=== MONO REACHABILITY OF COMMENT-ONLY SYM ===")
    print(json.dumps(results["mono_reachability"], indent=2))

    print("\n=== SYM EDGE CASES ===")
    print(json.dumps(results["sym_edge_cases"], indent=2))

    out_path = os.environ.get("PROBE_OUT")
    if out_path:
        Path(out_path).write_text(json.dumps(results, indent=2))

if __name__ == "__main__":
    main()
