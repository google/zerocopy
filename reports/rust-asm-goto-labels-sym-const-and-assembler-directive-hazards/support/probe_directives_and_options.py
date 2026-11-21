#!/usr/bin/env python3
"""Standalone probe for Rust inline/naked/global assembly directives, escape hatches,
syntax/dialect/modifier edge cases, and options(...) LLVM optimization behavior.

Covers:
1. Directives in asm!/naked_asm!/global_asm! via rustc and llvm-mc:
   - .init_array constructor injection (including from a runtime-unexecuted branch!)
   - .include and .incbin arbitrary filesystem read + dep-info (.d) tracking check
   - .macro/.endm, .rept/.endr, .if/.endif, .set/.equ persistence & instruction mnemonic
     hijacking across SEPARATE Rust functions in the same CGU!
   - .section/.pushsection/.popsection (extable pattern & unbalanced section corruption)
   - .globl/.weak/.hidden symbol export & #[inline(always)] duplicate-symbol collision
   - Numeric local labels (2:/2f/2b) across #[inline(always)] vs #[allow(binary_asm_labels)]
     MASM binary literal ambiguity (llvm/llvm-project#99547) in Intel vs AT&T vs global_asm!
   - .cfi_* directives inside asm! vs naked_asm! vs global_asm!
   - Raw byte emission (.byte/.long/.quad) bypassing mnemonic inspection
2. Template syntax, raw, att_syntax, modifiers, duplicate/unused operands, and
   `options(pure|nomem|readonly|nostack)` LLVM IR MemoryEffects + DCE/CSE/DSE/LICM.
"""
import json
import os
import subprocess
import tempfile
from pathlib import Path

TOOLCHAINS = ["nightly-2026-06-01", "1.99.1", "1.100.0", "nightly"]

def run(cmd, env=None, cwd=None, stdin_text=None):
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    p = subprocess.run(cmd, input=stdin_text, capture_output=True, text=True, env=merged_env, cwd=cwd)
    return p.returncode, p.stdout, p.stderr

def compile_snippet(tc, code, extra_args=None, crate_type="lib", extra_files=None):
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        if extra_files:
            for name, content in extra_files.items():
                p = td_path / name
                if isinstance(content, bytes):
                    p.write_bytes(content)
                else:
                    p.write_text(content)
        src = td_path / "probe.rs"
        src.write_text(code.replace("__TMPDIR__", str(td_path)))
        cmd = ["rustc", f"+{tc}", f"--crate-type={crate_type}", "--edition=2024", str(src), "--out-dir", td]
        if extra_args:
            cmd.extend(extra_args)
        rc, out, err = run(cmd, cwd=td)
        artifacts = {}
        for p in sorted(td_path.rglob("*")):
            if p.is_file() and p.name != "probe.rs" and (not extra_files or p.name not in extra_files):
                rel = str(p.relative_to(td_path))
                if p.suffix in (".ll", ".s", ".d"):
                    artifacts[rel] = p.read_text(errors="replace")
                elif p.suffix == ".o":
                    _, r_sec, _ = run(["readelf", "-SW", str(p)])
                    _, r_rel, _ = run(["readelf", "-rW", str(p)])
                    _, r_sym, _ = run(["readelf", "-sW", str(p)])
                    _, r_obj, _ = run(["objdump", "-dr", "-M", "intel", str(p)])
                    artifacts[rel + ".sections"] = r_sec
                    artifacts[rel + ".relocs"] = r_rel
                    artifacts[rel + ".syms"] = r_sym
                    artifacts[rel + ".objdump"] = r_obj
        return rc, out, err, artifacts

def compile_and_run_bin(tc, code, extra_args=None, extra_files=None):
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        if extra_files:
            for name, content in extra_files.items():
                p = td_path / name
                if isinstance(content, bytes):
                    p.write_bytes(content)
                else:
                    p.write_text(content)
        src = td_path / "probe.rs"
        bin_path = td_path / "probe_bin"
        src.write_text(code.replace("__TMPDIR__", str(td_path)))
        cmd = ["rustc", f"+{tc}", "--edition=2024", str(src), "-o", str(bin_path)]
        if extra_args:
            cmd.extend(extra_args)
        rc, out, err = run(cmd, cwd=td)
        dep_info = ""
        for p in td_path.glob("*.d"):
            dep_info += p.read_text(errors="replace")
        if rc != 0:
            return {"compile_rc": rc, "compile_err": err, "dep_info": dep_info}
        rrc, rout, rerr = run([str(bin_path)], cwd=td)
        return {"compile_rc": 0, "run_rc": rrc, "run_out": rout, "run_err": rerr, "dep_info": dep_info}

def main():
    results = {}

    # 1. LIVE .init_array injection from a runtime-NEVER-EXECUTED asm! block
    init_array_code = r"""
use core::arch::asm;
use core::sync::atomic::{AtomicU64, Ordering};

static HIJACKED: AtomicU64 = AtomicU64::new(0);

#[unsafe(no_mangle)]
extern "C" fn secret_ctor() {
    HIJACKED.store(0xCAFE_BABE, Ordering::SeqCst);
}

#[inline(never)]
fn dead_runtime_branch(run_it: bool) -> u64 {
    let mut out: u64 = 0;
    if run_it {
        unsafe {
            asm!(
                ".pushsection .init_array,\"aw\",@init_array",
                ".quad {ctor}",
                ".popsection",
                "mov {out}, 1",
                ctor = sym secret_ctor,
                out = out(reg) out,
                options(pure, nomem, nostack, preserves_flags),
            );
        }
    }
    out
}

fn main() {
    let before = HIJACKED.load(Ordering::SeqCst);
    let ret = dead_runtime_branch(core::hint::black_box(false));
    println!("before_call=0x{:X} dead_branch_ret={}", before, ret);
}
"""
    results["init_array_injection"] = {
        tc: compile_and_run_bin(tc, init_array_code, ["-C", "opt-level=2"])
        for tc in TOOLCHAINS
    }

    # 2. LIVE .include and .incbin arbitrary filesystem read + dep-info check
    inc_code = r"""
use core::arch::{asm, global_asm, naked_asm};

global_asm!(
    ".pushsection .rodata",
    ".globl incbin_blob",
    "incbin_blob:",
    ".incbin \"__TMPDIR__/secret.bin\"",
    ".popsection",
);

unsafe extern "C" {
    static incbin_blob: [u8; 12];
}

#[unsafe(naked)]
#[unsafe(no_mangle)]
pub extern "C" fn naked_included_fn() -> u64 {
    naked_asm!(
        ".include \"__TMPDIR__/inc_body.s\"",
        "ret",
    );
}

#[inline(never)]
fn inline_include_and_incbin() -> (u64, [u8; 4]) {
    let v: u64;
    let p: *const u8;
    unsafe {
        asm!(
            ".include \"__TMPDIR__/inc_inline.s\"",
            "jmp 3f",
            "2: .incbin \"__TMPDIR__/secret.bin\"",
            "3: lea {p}, [rip + 2b]",
            out("rax") v,
            p = out(reg) p,
        );
        let s = core::slice::from_raw_parts(p, 4);
        (v, [s[0], s[1], s[2], s[3]])
    }
}

fn main() {
    let (v_inline, inline_magic) = inline_include_and_incbin();
    let v_naked = naked_included_fn();
    let global_bytes = unsafe { &incbin_blob };
    println!("inline_v=0x{:X} inline_magic={} naked_v=0x{:X} global_str={}",
             v_inline,
             core::str::from_utf8(&inline_magic).unwrap(),
             v_naked,
             core::str::from_utf8(global_bytes).unwrap());
}
"""
    inc_files = {
        "secret.bin": b"INCBIN_OK_42",
        "inc_body.s": "mov rax, 0x2222\n",
        "inc_inline.s": "mov rax, 0x1111\n",
    }
    results["include_and_incbin"] = {}
    for tc in TOOLCHAINS:
        r = compile_and_run_bin(tc, inc_code, ["--emit=dep-info,link"], extra_files=inc_files)
        r["dep_mentions_secret_bin"] = "secret.bin" in r.get("dep_info", "")
        r["dep_mentions_inc_inline"] = "inc_inline.s" in r.get("dep_info", "")
        r["dep_mentions_inc_body"] = "inc_body.s" in r.get("dep_info", "")
        results["include_and_incbin"][tc] = r

    # 3. LIVE .macro mnemonic hijacking across SEPARATE Rust functions in the same CGU!
    macro_hijack_code = r"""
use core::arch::asm;

#[unsafe(no_mangle)]
#[inline(never)]
pub fn a_poison_mnemonic() {
    unsafe {
        asm!(
            ".macro add dst, src",
            "sub \\dst, \\src",
            ".endm",
            "nop",
        );
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn b_victim_add(mut x: i64, y: i64) -> i64 {
    unsafe {
        asm!(
            "add {x}, {y}",
            x = inout(reg) x,
            y = in(reg) y,
        );
    }
    x
}

fn main() {
    // Note: a_poison_mnemonic() is NEVER even called, yet its CGU emission order
    // poisons `add` in b_victim_add!
    let _ = core::hint::black_box(a_poison_mnemonic as fn());
    let res = b_victim_add(core::hint::black_box(10), core::hint::black_box(3));
    println!("victim_add(10, 3)={}", res);
}
"""
    results["macro_mnemonic_hijack"] = {
        tc: compile_and_run_bin(tc, macro_hijack_code, ["-C", "codegen-units=1", "-C", "opt-level=2"])
        for tc in TOOLCHAINS
    }

    # 4. LIVE llvm#99547 MASM binary literal vs numeric local label execution probe!
    masm_live_code = r"""
#![allow(binary_asm_labels)]
use core::arch::asm;

#[inline(never)]
fn masm_imm_101b() -> u64 {
    let x: u64;
    unsafe {
        asm!("mov {x}, 101b", x = out(reg) x);
    }
    x
}

#[inline(never)]
fn masm_label_10_vs_binary() -> u64 {
    let mut x: u64 = 0;
    unsafe {
        // Under setLexMasmIntegers(true) in Intel inline asm, is `10b` a backward jump to `10:`
        // or the MASM binary literal `2` (`0b10`)?!
        asm!(
            "10:",
            "add {x}, 1",
            "cmp {x}, 3",
            "jb 10b",
            x = inout(reg) x,
        );
    }
    x
}

fn main() {
    println!("imm_101b={}", masm_imm_101b());
}
"""
    # Compile masm_imm_101b alone and masm_label_10_vs_binary separately to inspect exact MC behavior!
    masm_imm_only = r"""
use core::arch::asm;
fn main() {
    let x: u64;
    let y: u64;
    unsafe {
        asm!("mov {x}, 101b", "mov {y}, 0ffh", x = out(reg) x, y = out(reg) y);
    }
    println!("101b={} 0ffh={}", x, y);
}
"""
    masm_lbl_only = r"""
#![allow(binary_asm_labels)]
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn lbl_10b(mut x: u64) -> u64 {
    unsafe {
        asm!(
            "10:",
            "add {x}, 1",
            "cmp {x}, 3",
            "jb 10b",
            x = inout(reg) x,
        );
    }
    x
}
"""
    masm_lbl_only_att = r"""
#![allow(binary_asm_labels)]
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn lbl_10b_att(mut x: u64) -> u64 {
    unsafe {
        asm!(
            "10:",
            "addq $1, {x}",
            "cmpq $3, {x}",
            "jb 10b",
            x = inout(reg) x,
            options(att_syntax),
        );
    }
    x
}
"""
    results["masm_imm_live"] = compile_and_run_bin("nightly", masm_imm_only)
    rc_ml, _, err_ml, arts_ml = compile_snippet("nightly", masm_lbl_only, ["-C", "opt-level=2", "--emit=obj,asm"])
    rc_mla, _, err_mla, arts_mla = compile_snippet("nightly", masm_lbl_only_att, ["-C", "opt-level=2", "--emit=obj,asm"])
    results["masm_label_10b_intel"] = {"rc": rc_ml, "err": err_ml, "objdump": arts_ml.get("probe.o.objdump", ""), "relocs": arts_ml.get("probe.o.relocs", "")}
    results["masm_label_10b_att"] = {"rc": rc_mla, "err": err_mla, "objdump": arts_mla.get("probe.o.objdump", ""), "relocs": arts_mla.get("probe.o.relocs", "")}

    # 5. Directive matrix (with proper label digits >= 2 and #[allow(...)] where probing post-lint MC behavior)
    directive_cases = {
        "macro_rept_if_set_in_asm": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f() -> u64 {
    let x: u64;
    unsafe {
        asm!(
            ".macro add_k dst, k",
            "add \\dst, \\k",
            ".endm",
            ".set BASE_VAL, 10",
            "mov {x}, BASE_VAL",
            ".rept 3",
            "add_k {x}, 2",
            ".endr",
            ".if BASE_VAL == 10",
            "add {x}, 100",
            ".endif",
            ".purgem add_k",
            x = out(reg) x,
        );
    }
    x
}
""", []),
        "extable_pushsection_popsection": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn extable_load(ptr: *const u64) -> u64 {
    let val: u64;
    unsafe {
        asm!(
            "2: mov {v}, qword ptr [{p}]",
            "3:",
            ".pushsection .extable,\"a\"",
            ".balign 4",
            ".long 2b - .",
            ".long 3b - .",
            ".popsection",
            p = in(reg) ptr,
            v = out(reg) val,
        );
    }
    val
}
""", []),
        "unbalanced_section_default_uwtable_fails": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn unbalanced_sec() -> u64 {
    unsafe { asm!(".section .rodata.hijack,\"a\",@progbits", ".byte 0x41"); }
    42
}
""", []),
        "unbalanced_section_no_uwtable_corrupts_obj": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn unbalanced_sec_no_uw() -> u64 {
    unsafe { asm!(".section .rodata.hijack,\"a\",@progbits", ".byte 0x41"); }
    42
}
""", ["-C", "force-unwind-tables=no", "-C", "panic=abort"]),
        "globl_weak_hidden_in_asm_allow_lint": (r"""
#![allow(named_asm_labels)]
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn sym_directives() {
    unsafe {
        asm!(
            ".globl asm_exported_global",
            ".weak asm_exported_weak",
            ".hidden asm_exported_hidden",
            ".globl asm_exported_hidden",
            "asm_exported_global:",
            "asm_exported_weak:",
            "asm_exported_hidden:",
            "nop",
        );
    }
}
""", []),
        "inline_named_label_collision_allow_lint": (r"""
#![allow(named_asm_labels)]
use core::arch::asm;
#[inline(always)]
fn helper() {
    unsafe { asm!(".Lnon_unique_lbl:", "nop"); }
}
#[unsafe(no_mangle)]
pub fn caller() {
    helper();
    helper();
}
""", []),
        "inline_numeric_label_2_no_collision": (r"""
use core::arch::asm;
#[inline(always)]
fn helper(x: u64) -> u64 {
    let mut y = x;
    unsafe {
        asm!(
            "2:",
            "add {y}, 1",
            "cmp {y}, 5",
            "jb 2b",
            y = inout(reg) y,
        );
    }
    y
}
#[unsafe(no_mangle)]
pub fn caller(a: u64) -> u64 {
    helper(a) + helper(a + 1)
}
""", []),
        "masm_binary_in_global_asm_rejected": (r"""
use core::arch::global_asm;
global_asm!(
    ".globl global_masm_fn",
    "global_masm_fn:",
    "mov rax, 101b",
    "ret",
);
""", []),
        "masm_binary_in_naked_asm_rejected": (r"""
use core::arch::naked_asm;
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub extern "C" fn naked_masm_fn() -> u64 {
    naked_asm!("mov rax, 101b", "ret");
}
""", []),
        "cfi_adjust_in_asm_ok": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn cfi_in_asm() {
    unsafe {
        asm!(
            "push rax",
            ".cfi_adjust_cfa_offset 8",
            "pop rax",
            ".cfi_adjust_cfa_offset -8",
        );
    }
}
""", []),
        "cfi_startproc_in_asm_rejected": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn cfi_start_in_asm() {
    unsafe { asm!(".cfi_startproc", "nop", ".cfi_endproc"); }
}
""", []),
        "cfi_in_naked_asm_ok": (r"""
use core::arch::naked_asm;
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub extern "C" fn cfi_naked() {
    naked_asm!(
        ".cfi_startproc",
        "push rbp",
        ".cfi_def_cfa_offset 16",
        "pop rbp",
        ".cfi_def_cfa_offset 8",
        "ret",
        ".cfi_endproc",
    );
}
""", []),
        "raw_byte_opcode_emission_under_nomem": (r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe fn hidden_store_raw_bytes(p: *mut u64) {
    unsafe {
        asm!(
            ".byte 0x48, 0xc7, 0x07, 0x2a, 0x00, 0x00, 0x00",
            in("rdi") p,
            options(nomem, nostack, preserves_flags),
        );
    }
}
""", []),
    }

    dir_results = {}
    for name, (code, extra) in directive_cases.items():
        rc, _, err, arts = compile_snippet("nightly", code, ["-C", "opt-level=2", "-C", "codegen-units=1", "--emit=obj,asm"] + extra)
        rc98, _, _, _ = compile_snippet("nightly-2026-06-01", code, ["-C", "opt-level=2", "-C", "codegen-units=1", "--emit=obj"] + extra)
        first_err = next((l for l in err.splitlines() if "error" in l.lower()), "")
        entry = {"nightly_rc": rc, "n98_rc": rc98, "first_error": first_err}
        if name in ("extable_pushsection_popsection", "unbalanced_section_no_uwtable_corrupts_obj", "globl_weak_hidden_in_asm_allow_lint", "raw_byte_opcode_emission_under_nomem"):
            entry["objdump"] = arts.get("probe.o.objdump", "")
            entry["sections"] = arts.get("probe.o.sections", "")
            entry["syms"] = arts.get("probe.o.syms", "")
            entry["relocs"] = arts.get("probe.o.relocs", "")
        dir_results[name] = entry
    results["directives"] = dir_results

    # 6. LICM hoisting of pure+nomem without panicking bounds check vs with panicking bounds check
    licm_code = r"""
use core::arch::asm;

#[unsafe(no_mangle)]
pub fn licm_pure_nomem_no_panic(x: u64, n: usize) -> u64 {
    let mut acc = 0u64;
    for _ in 0..n {
        let v: u64;
        unsafe {
            asm!("lea {o}, [{i} + 7]", o = out(reg) v, i = in(reg) x, options(pure, nomem, nostack));
        }
        acc = acc.wrapping_add(v);
    }
    acc
}

#[unsafe(no_mangle)]
pub fn licm_pure_readonly_no_panic(p: *const u64, n: usize) -> u64 {
    let mut acc = 0u64;
    for _ in 0..n {
        let v: u64;
        unsafe {
            asm!("mov {o}, qword ptr [{p}]", o = out(reg) v, p = in(reg) p, options(pure, readonly, nostack));
        }
        acc = acc.wrapping_add(v);
    }
    acc
}

#[unsafe(no_mangle)]
pub fn licm_impure_nomem_no_panic(x: u64, n: usize) -> u64 {
    let mut acc = 0u64;
    for _ in 0..n {
        let v: u64;
        unsafe {
            asm!("lea {o}, [{i} + 7]", o = out(reg) v, i = in(reg) x, options(nomem, nostack));
        }
        acc = acc.wrapping_add(v);
    }
    acc
}
"""
    rc_l, _, err_l, arts_l = compile_snippet("nightly", licm_code, ["-C", "opt-level=3", "--emit=llvm-ir,asm"])
    results["licm_probe"] = {"rc": rc_l, "err": err_l, "ll": arts_l.get("probe.ll", ""), "asm": arts_l.get("probe.s", "")}

    # 7. Template syntax, raw, att_syntax, modifiers, duplicate/unused operands, clobber_abi
    syntax_cases = {
        "raw_with_braces_and_att_dollar": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f() {
    unsafe { asm!("/* {literal_braces} */ movq $42, %rax", options(raw, att_syntax)); }
}
""",
        "raw_with_operand_rejected": r"""
use core::arch::asm;
pub fn f(x: u64) { unsafe { asm!("nop", in(reg) x, options(raw)); } }
""",
        "raw_blocks_llvm_dollar_uid": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f() {
    unsafe { asm!("/* ${:uid} $0 */ nop", options(raw)); }
}
""",
        "modifier_c_on_sym_rejected": r"""
use core::arch::asm;
fn g() {}
pub fn f() { unsafe { asm!("call {0:c}", sym g); } }
""",
        "modifier_l_on_label_rejected": r"""
use core::arch::asm;
pub fn f() { unsafe { asm!("jmp {0:l}", label {}); } }
""",
        "modifier_c_on_const_rejected": r"""
use core::arch::asm;
pub fn f() { unsafe { asm!("mov rax, {0:c}", const 1); } }
""",
        "modifier_h_on_reg_abcd_x86_64": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f(mut x: u64) -> u64 {
    unsafe { asm!("mov {0:h}, 0xab", inout(reg_abcd) x); }
    x
}
""",
        "explicit_ah_on_x86_64_rejected": r"""
use core::arch::asm;
pub fn f(x: u8) { unsafe { asm!("nop", in("ah") x); } }
""",
        "modifier_e_on_u64_and_dup_modifiers": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f(x: u64) -> u64 {
    let mut y = x;
    unsafe { asm!("add {0:e}, {1:e}", "add {0:r}, {1:r}", inout(reg) y, in(reg) x); }
    y
}
""",
        "unused_named_operand_rejected": r"""
use core::arch::asm;
pub fn f(x: u64) { unsafe { asm!("nop", a = in(reg) x); } }
""",
        "explicit_reg_referenced_rejected": r"""
use core::arch::asm;
pub fn f(x: u64) { unsafe { asm!("mov {0}, 1", in("rax") x); } }
""",
        "clobber_abi_with_lateout_regclass_rejected": r"""
use core::arch::asm;
pub fn f() -> u64 {
    let x: u64;
    unsafe { asm!("mov {0}, 1", lateout(reg) x, clobber_abi("C")); }
    x
}
""",
        "same_place_two_outputs_rightmost_wins": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub fn f() -> u64 {
    let mut y: u64;
    unsafe { asm!("mov {0}, 11", "mov {1}, 22", out(reg) y, out(reg) y); }
    y
}
""",
        "raw_with_bad_asm_style_lint": r"""
#![deny(bad_asm_style)]
use core::arch::asm;
pub fn f() { unsafe { asm!(".att_syntax\nnop\n.intel_syntax noprefix", options(raw)); } }
""",
    }
    syn_results = {}
    for name, code in syntax_cases.items():
        rc, _, err, arts = compile_snippet("nightly", code, ["--emit=llvm-ir"])
        first_err = next((l for l in err.splitlines() if l.startswith("error")), "")
        syn_results[name] = {"rc": rc, "first_error": first_err}
    results["syntax_and_modifiers"] = syn_results

    # 8. LLVM IR MemoryEffects + DCE / CSE / DSE across options(...)
    opt_code = r"""
#![feature(asm_goto_with_outputs)]
use core::arch::asm;

#[unsafe(no_mangle)]
pub fn opt_pure_nomem_dce(x: u64) -> u64 {
    let _unused: u64;
    unsafe { asm!("lea {o}, [{i} + 1]", o = out(reg) _unused, i = in(reg) x, options(pure, nomem, nostack)); }
    x
}
#[unsafe(no_mangle)]
pub fn opt_impure_nomem_no_dce(x: u64) -> u64 {
    let _unused: u64;
    unsafe { asm!("lea {o}, [{i} + 1]", o = out(reg) _unused, i = in(reg) x, options(nomem, nostack)); }
    x
}
#[unsafe(no_mangle)]
pub unsafe fn opt_pure_readonly_cse_blocked_by_store(p: *mut u64) -> (u64, u64) {
    let (a, b, c): (u64, u64, u64);
    unsafe {
        asm!("mov {o}, qword ptr [{p}]", o = out(reg) a, p = in(reg) p, options(pure, readonly, nostack));
        asm!("mov {o}, qword ptr [{p}]", o = out(reg) b, p = in(reg) p, options(pure, readonly, nostack));
        *p = 999;
        asm!("mov {o}, qword ptr [{p}]", o = out(reg) c, p = in(reg) p, options(pure, readonly, nostack));
    }
    (a.wrapping_add(b), c)
}
#[unsafe(no_mangle)]
pub unsafe fn opt_nomem_dse_across_asm(p: *mut u64, x: u64) -> u64 {
    let out: u64;
    unsafe {
        *p = 1;
        asm!("lea {o}, [{i} + 3]", o = out(reg) out, i = in(reg) x, options(nomem, nostack));
        *p = 2;
    }
    out
}
#[unsafe(no_mangle)]
pub unsafe fn opt_readonly_blocks_dse(p: *mut u64, x: u64) -> u64 {
    let out: u64;
    unsafe {
        *p = 1;
        asm!("lea {o}, [{i} + 3]", o = out(reg) out, i = in(reg) x, options(readonly, nostack));
        *p = 2;
    }
    out
}
#[unsafe(no_mangle)]
pub fn opt_pure_callbr(x: u64) -> u64 {
    let _unused: u64;
    unsafe {
        asm!("mov {o}, {i}", "test {i}, {i}", "jnz {lbl}",
             o = out(reg) _unused, i = in(reg) x,
             lbl = label { return 99; },
             options(pure, nomem, nostack));
    }
    0
}
"""
    rc_opt, _, err_opt, arts_opt = compile_snippet("nightly", opt_code, ["-C", "opt-level=3", "--emit=llvm-ir"])
    results["option_effects_o3"] = {"rc": rc_opt, "err": err_opt, "ll": arts_opt.get("probe.ll", "")}

    # 9. Direct llvm-mc differential probe
    mc_probes = {
        "mc_intel_masm_101b": (["llvm-mc", "-triple=x86_64-unknown-linux-gnu", "-x86-asm-syntax=intel", "--show-encoding"], ".intel_syntax noprefix\nmov rax, 101b\n"),
        "mc_intel_label_10b": (["llvm-mc", "-triple=x86_64-unknown-linux-gnu", "-x86-asm-syntax=intel", "--show-encoding"], ".intel_syntax noprefix\n10:\njne 10b\n"),
        "mc_raw_byte_store": (["llvm-mc", "-triple=x86_64-unknown-linux-gnu", "--disassemble"], "0x48 0xc7 0x07 0x2a 0x00 0x00 0x00\n"),
    }
    results["llvm_mc_probes"] = {
        k: dict(zip(("rc", "out", "err"), run(cmd, stdin_text=inp)))
        for k, (cmd, inp) in mc_probes.items()
    }

    print("=== 1. INIT_ARRAY INJECTION ===")
    for tc, r in results["init_array_injection"].items():
        print(f"  {tc}: rc={r['compile_rc']}/{r.get('run_rc')} out={r.get('run_out','').strip()!r}")

    print("\n=== 2. INCLUDE & INCBIN ESCAPE HATCH ===")
    for tc, r in results["include_and_incbin"].items():
        print(f"  {tc}: rc={r['compile_rc']}/{r.get('run_rc')} out={r.get('run_out','').strip()!r} dep_tracked=({r['dep_mentions_secret_bin']},{r['dep_mentions_inc_inline']},{r['dep_mentions_inc_body']})")

    print("\n=== 3. LIVE MACRO MNEMONIC HIJACKING ACROSS FUNCTIONS ===")
    for tc, r in results["macro_mnemonic_hijack"].items():
        print(f"  {tc}: rc={r['compile_rc']}/{r.get('run_rc')} out={r.get('run_out','').strip()!r}")

    print("\n=== 4. MASM BINARY LITERAL VS NUMERIC LABEL (llvm#99547) ===")
    print("  masm_imm_live:", results["masm_imm_live"])
    print("  masm_label_10b_intel rc:", results["masm_label_10b_intel"]["rc"], "err:", results["masm_label_10b_intel"]["err"])
    print("  masm_label_10b_intel objdump:\n", results["masm_label_10b_intel"]["objdump"])
    print("  masm_label_10b_att objdump:\n", results["masm_label_10b_att"]["objdump"])

    print("\n=== 5. DIRECTIVES MATRIX ===")
    for k, v in dir_results.items():
        print(f"  {k}: nightly={v['nightly_rc']} n98={v['n98_rc']} err={v['first_error'][:95]}")

    print("\n=== 5b. EXTABLE RELOCS & SECTIONS ===")
    print(dir_results["extable_pushsection_popsection"].get("relocs", ""))
    print("\n=== 5c. UNBALANCED SECTION (no-uwtable) OBJDUMP ===")
    print(dir_results["unbalanced_section_no_uwtable_corrupts_obj"].get("objdump", ""))
    print("\n=== 5d. GLOBL/WEAK/HIDDEN SYMS ===")
    for l in dir_results["globl_weak_hidden_in_asm_allow_lint"].get("syms", "").splitlines():
        if "asm_exported" in l or "Num:" in l:
            print(" ", l)

    print("\n=== 6. LICM PROBE LLVM IR (-O3) ===")
    print(results["licm_probe"]["ll"])

    out_path = os.environ.get("PROBE_OUT")
    if out_path:
        Path(out_path).write_text(json.dumps(results, indent=2))

if __name__ == "__main__":
    main()
