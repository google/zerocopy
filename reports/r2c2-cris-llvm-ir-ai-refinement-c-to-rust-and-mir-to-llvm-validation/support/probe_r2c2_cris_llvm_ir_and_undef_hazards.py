#!/usr/bin/env python3
"""Empirical compiler probe: `undef` lowering, source-vs-IR UB, attributes, unwinding.

This probe compiles small embedded C and Rust programs with a real `clang` and a
real `rustc`, parses the LLVM IR they emit, applies the two textual `undef`
rewrites described in prose by arXiv:2611.18036v1 (C side: `undef` -> `poison`;
Rust side: `undef` -> zero / `null`), and asks LLVM's own `opt` to constant-fold
the rewritten and the original IR.

Every number and every boolean written to the result file is computed from tool
output produced during the run.  Nothing in the result is a literal copied from
an earlier run.  The EXPECTATIONS below state what the accompanying report
claims; when a toolchain behaves differently the corresponding check is reported
as failed and the process exits with status 1, so drift is visible rather than
silently absorbed.

The rewrites implemented here are reconstructions from the paper's prose.  The
R2C2 implementation itself was not available and was not executed.

Usage:
    python3 probe_r2c2_cris_llvm_ir_and_undef_hazards.py \
        --clang /path/to/clang --rustc /path/to/rustc --opt /path/to/opt \
        --out probe_results.json [--keep-ir DIR]

Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

# --------------------------------------------------------------------------
# Embedded probe sources
# --------------------------------------------------------------------------

C_UNINIT = r"""
extern int cond(void);
extern char next(void);

struct S { unsigned a : 1; unsigned b : 7; };
struct S3 { unsigned a : 1; unsigned b : 3; unsigned c : 4; };
struct Two { struct S3 x; struct S3 y; };
struct T { char a; char b; };
struct TT { struct T x; struct T y; };
struct P { long tag; long val; };
struct Q { char tag; int val; };
struct A { int v[2]; };
struct F { float f; int i; };
struct D { double a; double b; };
struct LI { long a; int b; };
union U { int i; char c; };

/* --- indeterminate bits share one integer with initialized bits ---------- */

/* bit-field written into an uninitialized local; only that bit-field read */
unsigned bf_read_back(int x) { struct S s; s.a = x & 1; return s.a; }

/* same store; the whole struct is returned by value */
struct S bf_return_whole(int x) { struct S s; s.a = x & 1; return s; }

/* storage unit possibly written by a countable loop before the store */
struct S bf_loop_then_set(int x, int n) {
  struct S s;
  for (int i = 0; i < n; i++) s.b = i;
  s.a = x & 1;
  return s;
}

/* storage unit left uninitialized on the default path of a switch */
struct S bf_switch_then_set(int x, int c) {
  struct S s;
  switch (c) {
    case 1: s.b = 5; break;
    case 2: s.b = 9; break;
    case 3: s.b = 33; break;
    default: break;
  }
  s.a = x & 1;
  return s;
}

/* storage unit possibly written by a loop with opaque trip count */
struct S bf_loop_ext(int x) {
  struct S s;
  while (cond()) s.b = next();
  s.a = x & 1;
  return s;
}

/* plain two-byte struct, second byte possibly never written */
struct T plain_loop(char x) {
  struct T t;
  while (cond()) t.b = next();
  t.a = x;
  return t;
}

/* union: one byte written, the four-byte member read */
int pun(char x) { union U u; u.c = x; return u.i; }

/* aggregates coerced into one integer register with an unwritten part */
struct Q partial_coerced(char t) { struct Q q; q.tag = t; return q; }
struct A arr_part(int x) { struct A a; a.v[0] = x; return a; }
struct F fi(int i) { struct F r; r.i = i; return r; }

/* the possibly-unwritten byte is copied into two results */
struct TT two_copies(char x, char y) {
  struct T t, u;
  struct TT r;
  (void)&t;
  while (cond()) t.b = next();
  u = t;
  t.a = x;
  u.a = y;
  r.x = t;
  r.y = u;
  return r;
}

/* the possibly-unwritten bit-field storage unit reaches two different masks */
struct Two two_masks(int x) {
  struct S3 s, s2;
  struct Two r;
  (void)&s;
  while (cond()) s.b = next();
  s2 = s;
  s.a = x & 1;
  s2.c = 2;
  r.x = s;
  r.y = s2;
  return r;
}

/* --- a whole member is left unwritten and returned in its own register --- */

struct P partial_pair(long t) { struct P p; p.tag = t; return p; }
struct D dd(double a) { struct D d; d.a = a; return d; }
struct LI li(int b) { struct LI r; r.b = b; return r; }
struct P pair_loop(long t) {
  struct P p;
  while (cond()) p.val = next();
  p.tag = t;
  return p;
}
"""

C_VLA = r"""
extern void use(void *);
_Bool vla2d(int n, int sum) {
  _Bool subset[n + 1][sum + 1];
  use(subset);
  return subset[0][0];
}
int vla1d(int n) {
  int arr[n + 1];
  use(arr);
  return arr[0];
}
"""

RUST_UNINIT = r"""
#![crate_type = "lib"]
use std::mem::MaybeUninit;

// Entirely safe Rust: the first component is never initialized.
#[no_mangle]
pub fn uninit_pair(x: i32) -> (MaybeUninit<i32>, i32) {
    (MaybeUninit::uninit(), x)
}

#[repr(C)]
pub struct Padded { pub tag: u8, pub val: i32 }
#[no_mangle]
pub fn make_padded(x: u8, v: i32) -> Padded { Padded { tag: x, val: v } }

#[no_mangle]
pub fn none_or(x: u32, c: bool) -> Option<u32> { if c { Some(x) } else { None } }

pub enum E { A(u8), B(u32) }
#[no_mangle]
pub fn mk_e(x: u8) -> E { E::A(x) }
"""

RUST_VEC = r"""
#![crate_type = "lib"]
#[no_mangle]
pub fn vec2d(n: i32, sum: i32) -> usize {
    let subset = vec![vec![false; (sum + 1) as usize]; (n + 1) as usize];
    subset.len()
}
#[no_mangle]
pub fn vec1d(n: i32) -> usize {
    let arr = vec![0_i32; (n + 1) as usize];
    arr.len()
}
"""

RUST_ABI = r"""
#![crate_type = "lib"]
extern "C-unwind" { fn foreign_may_unwind(x: i32) -> i32; }
extern "C" { fn foreign_nounwind(x: i32) -> i32; }

pub struct Guard<'a>(&'a mut i32);
impl Drop for Guard<'_> {
    fn drop(&mut self) { *self.0 += 1; }
}

#[no_mangle]
pub fn call_cunwind_with_guard(slot: &mut i32, x: i32) -> i32 {
    let _g = Guard(slot);
    unsafe { foreign_may_unwind(x) }
}
#[no_mangle]
pub fn call_cunwind_no_guard(x: i32) -> i32 {
    unsafe { foreign_may_unwind(x) }
}
#[no_mangle]
pub fn call_c_with_guard(slot: &mut i32, x: i32) -> i32 {
    let _g = Guard(slot);
    unsafe { foreign_nounwind(x) }
}
#[no_mangle]
pub fn slice_and_opt_string(a: &[i32], flag: bool) -> Option<String> {
    if flag && !a.is_empty() { Some(String::from("ok")) } else { None }
}
#[no_mangle]
pub fn has_duplicate(a: &[i32]) -> bool {
    let mut s = a.to_vec();
    s.sort();
    s.windows(2).any(|w| w[0] == w[1])
}
#[no_mangle]
pub fn takes_ref_and_bool(r: &u32, b: bool, m: &mut u64) -> u32 {
    if b { *m += 1; }
    *r
}
"""

RUST_TRIVIAL = "pub fn f(x: u32) -> u32 { x.wrapping_add(1) }\n"

# Flags named in the paper's compilation-settings appendix that are meaningful
# for these probes.  Flags the appendix names only as "and others", and the
# LLVM `-force-attribute` options that depend on R2C2's library list, are not
# applied.
CLANG_FLAGS = [
    "-std=gnu11", "-O1", "-fno-unroll-loops", "-fno-vectorize",
    "-fno-slp-vectorize", "-ffp-contract=off", "-S", "-emit-llvm",
]
RUSTC_FLAGS = [
    "--edition=2021", "-Copt-level=1", "-Zinline-mir=no",
    "-Cno-vectorize-loops", "-Cno-vectorize-slp",
    "-Cllvm-args=--unroll-threshold=0", "--emit=llvm-ir",
]
OPT_FOLD_PIPELINE = "cgscc(inline),function(simplifycfg,instsimplify)"
# `instsimplify` does not forward `extractvalue` through an `insertvalue` at a
# different index; `instcombine` does, without choosing a value for `undef`.
OPT_EXTRACT_PIPELINE = "cgscc(inline),function(instcombine)"

# --------------------------------------------------------------------------
# IR helpers
# --------------------------------------------------------------------------

# `noundef` contains the substring `undef`; a substring test is therefore wrong.
_TOKEN_TMPL = r"(?<![A-Za-z0-9_.%@]){}(?![A-Za-z0-9_.])"
UNDEF_TOKEN = re.compile(_TOKEN_TMPL.format("undef"))
POISON_TOKEN = re.compile(_TOKEN_TMPL.format("poison"))
DEFINE_RE = re.compile(r"^define\b.*?@([A-Za-z0-9_.$]+)\(")


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=str(cwd), env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def first_line(text: str) -> str:
    return text.strip().splitlines()[0] if text.strip() else ""


def functions(ir: str) -> dict[str, str]:
    """Map each defined function name to its full textual body."""
    out: dict[str, str] = {}
    name: str | None = None
    buf: list[str] = []
    for line in ir.splitlines():
        if name is None:
            match = DEFINE_RE.match(line)
            if match:
                name = match.group(1)
                buf = [line]
        else:
            buf.append(line)
            if line == "}":
                out[name] = "\n".join(buf)
                name = None
    return out


def body_lines(fn_text: str) -> list[str]:
    """Instruction lines of a function, without the `define` header and `}`."""
    return [ln for ln in fn_text.splitlines()[1:-1] if ln.strip()]


def undef_lines(fn_text: str) -> list[str]:
    return [ln.strip() for ln in fn_text.splitlines() if UNDEF_TOKEN.search(ln)]


def count_instr(ir: str, opcode: str) -> int:
    pattern = re.compile(r"^\s*(?:%[\w.]+\s*=\s*)?(?:tail |musttail |notail )?" + re.escape(opcode) + r"\b", re.M)
    return len(pattern.findall(ir))


def count_calls_to(fn_text: str, symbol_fragment: str) -> int:
    """Call instructions (not `; call ...` comment lines) whose callee mentions the fragment."""
    total = 0
    for line in fn_text.splitlines():
        stripped = line.strip()
        if stripped.startswith(";"):
            continue
        if re.search(r"\bcall\b", stripped) and symbol_fragment in stripped:
            total += 1
    return total


def ret_operands(fn_text: str) -> list[str]:
    return [ln.strip() for ln in body_lines(fn_text) if ln.strip().startswith("ret ")]


def rewrite_undef_to_poison(ir: str) -> tuple[str, int]:
    """C-side rule from the paper's prose: every `undef` becomes `poison`."""
    return UNDEF_TOKEN.subn("poison", ir)


_TYPED_UNDEF = re.compile(
    r"(?P<ty>\{[^{}]*\}|\[[^\[\]]*\]|i\d+|ptr|float|double)\s+undef(?![A-Za-z0-9_.])"
)


def rewrite_undef_to_zero(ir: str) -> tuple[str, int]:
    """Rust-side rule from the paper's prose: `undef` becomes zero or `null`,
    depending on the value's type.  Aggregates become `zeroinitializer`.
    Raises if an `undef` remains whose type this reconstruction cannot classify.
    """
    def repl(match: re.Match) -> str:
        ty = match.group("ty")
        if ty.startswith("{") or ty.startswith("["):
            zero = "zeroinitializer"
        elif ty == "ptr":
            zero = "null"
        elif ty in ("float", "double"):
            zero = "0.0"
        else:
            zero = "0"
        return f"{ty} {zero}"

    new, count = _TYPED_UNDEF.subn(repl, ir)
    leftover = [ln for ln in new.splitlines() if UNDEF_TOKEN.search(ln)]
    if leftover:
        raise RuntimeError("unclassified undef operand: " + leftover[0].strip())
    return new, count


def strip_declarations(ir: str, names: list[str]) -> str:
    for name in names:
        ir = re.sub(r"^declare[^\n]*@" + re.escape(name) + r"\([^\n]*\n", "", ir, flags=re.M)
    return ir


# --------------------------------------------------------------------------
# Probe stages
# --------------------------------------------------------------------------

class Probe:
    def __init__(self, clang: str, rustc: str, opt: str, work: Path, keep: Path | None):
        self.clang, self.rustc, self.opt = clang, rustc, opt
        self.work, self.keep = work, keep
        self.checks: list[dict[str, Any]] = []
        self.result: dict[str, Any] = {"schema": "r2c2-undef-hazard-probe/1"}

    # -- utilities ---------------------------------------------------------
    def check(self, ident: str, description: str, observed: Any, passed: bool) -> None:
        self.checks.append({"id": ident, "description": description,
                            "observed": observed, "pass": bool(passed)})

    def save(self, name: str, text: str) -> None:
        if self.keep is not None:
            (self.keep / name).write_text(text)

    def compile_c(self, stem: str, source: str) -> str:
        (self.work / f"{stem}.c").write_text(source)
        proc = run([self.clang, *CLANG_FLAGS, "-o", f"{stem}.ll", f"{stem}.c"], self.work)
        if proc.returncode != 0:
            raise RuntimeError(f"clang failed on {stem}.c: {proc.stderr[:400]}")
        ir = (self.work / f"{stem}.ll").read_text()
        self.save(f"{stem}.clang.O1.ll", ir)
        return ir

    def compile_rust(self, stem: str, source: str, panic: str,
                     env: dict[str, str] | None = None, check: bool = True) -> tuple[int, str, str]:
        (self.work / f"{stem}.rs").write_text(source)
        cmd = [self.rustc, *RUSTC_FLAGS, f"-Cpanic={panic}", "-o", f"{stem}.{panic}.ll", f"{stem}.rs"]
        proc = run(cmd, self.work, env)
        if check and proc.returncode != 0:
            raise RuntimeError(f"rustc failed on {stem}.rs: {proc.stderr[:400]}")
        path = self.work / f"{stem}.{panic}.ll"
        return proc.returncode, (path.read_text() if path.exists() else ""), proc.stderr

    def opt_fold(self, name: str, ir: str, pipeline: str = OPT_FOLD_PIPELINE) -> str:
        (self.work / name).write_text(ir)
        proc = run([self.opt, f"-passes={pipeline}", "-S", name, "-o", name + ".out"], self.work)
        if proc.returncode != 0:
            raise RuntimeError(f"opt failed on {name}: {proc.stderr[:400]}")
        return (self.work / (name + ".out")).read_text()

    # -- stage 0 -----------------------------------------------------------
    def versions(self) -> None:
        clang_v = first_line(run([self.clang, "--version"], self.work).stdout)
        rustc_vv = run([self.rustc, "--version", "--verbose"], self.work).stdout.strip().splitlines()
        opt_v = [ln.strip() for ln in run([self.opt, "--version"], self.work).stdout.splitlines()
                 if "LLVM version" in ln]
        self.result["toolchain"] = {
            "clang": clang_v,
            "rustc": rustc_vv,
            "opt": opt_v[0] if opt_v else "",
            "clang_flags": CLANG_FLAGS,
            "rustc_flags": RUSTC_FLAGS,
            "opt_fold_pipeline": OPT_FOLD_PIPELINE,
            "opt_extract_pipeline": OPT_EXTRACT_PIPELINE,
        }
        token_selftest = {
            "noundef_parameter": len(UNDEF_TOKEN.findall("define i32 @f(i32 noundef %x)")),
            "undef_operand": len(UNDEF_TOKEN.findall("insertvalue { i64, i64 } %2, i64 undef, 1")),
            "undef_in_phi": len(UNDEF_TOKEN.findall("%12 = phi i8 [ undef, %1 ], [ %10, %8 ]")),
        }
        self.result["token_selftest"] = token_selftest
        self.check("tokenizer.noundef_is_not_undef",
                   "the standalone-token scanner ignores `noundef` and finds real `undef` operands",
                   token_selftest,
                   token_selftest == {"noundef_parameter": 0, "undef_operand": 1, "undef_in_phi": 1})

    # -- stage 1: C-side undef --------------------------------------------
    def c_undef(self) -> None:
        ir = self.compile_c("c_uninit", C_UNINIT)
        fns = functions(ir)
        per_fn = {name: undef_lines(text) for name, text in fns.items()}
        section: dict[str, Any] = {
            "standalone_undef_lines_by_function": per_fn,
            "module_mustprogress_occurrences": len(re.findall(r"\bmustprogress\b", ir)),
            "functions": {name: text for name, text in fns.items()},
        }

        mixed_free = ["bf_read_back", "bf_return_whole", "bf_loop_then_set", "bf_switch_then_set",
                      "bf_loop_ext", "plain_loop", "pun", "partial_coerced", "arr_part", "fi",
                      "two_copies"]
        whole_field = ["partial_pair", "dd", "li", "pair_loop"]
        self.check("c.single_use_indeterminate_bits_are_folded",
                   "shapes whose indeterminate bits meet one mask/extension emit no standalone `undef`",
                   {name: len(per_fn.get(name, ["<missing>"])) for name in mixed_free},
                   all(name in per_fn and not per_fn[name] for name in mixed_free))
        self.check("c.whole_member_undef_survives",
                   "an entirely unwritten member returned in its own register is a literal `undef`",
                   {name: per_fn.get(name, []) for name in whole_field},
                   all(per_fn.get(name) for name in whole_field))

        # two_masks: a phi with an `undef` incoming value feeding >= 2 distinct `and` masks
        text = fns.get("two_masks", "")
        phi = re.search(r"(%[\w.]+) = phi (i\d+) [^\n]*(?<![A-Za-z0-9_.])undef(?![A-Za-z0-9_.])", text)
        masks: list[str] = []
        if phi:
            reg, ty = re.escape(phi.group(1)), re.escape(phi.group(2))
            masks = re.findall(r"= and " + ty + " " + reg + r", (-?\d+)", text)
        section["two_masks_phi"] = next((ln.strip() for ln in text.splitlines()
                                         if phi and ln.strip().startswith(phi.group(1) + " = phi")), None)
        section["two_masks_and_masks_on_phi"] = masks
        self.check("c.undef_phi_reaches_two_masks",
                   "`two_masks` keeps a phi with an `undef` incoming value that is masked twice "
                   "and OR-ed with defined bits",
                   {"phi": section["two_masks_phi"], "and_masks": masks},
                   bool(phi) and len(set(masks)) >= 2)

        # LLVM's constant folder on the zero-trip path, original vs `undef -> poison`
        harness_tail = (
            "\ndefine i32 @cond() {\n  ret i32 0\n}\n"
            "define signext i8 @next() {\n  ret i8 0\n}\n"
        )
        base = strip_declarations(ir, ["cond", "next"])
        poisoned, n_sub = rewrite_undef_to_poison(base)
        folded_undef = functions(self.opt_fold("h1_undef.ll", base + harness_tail))
        folded_poison = functions(self.opt_fold("h1_poison.ll", poisoned + harness_tail))
        tm_u, tm_p = folded_undef.get("two_masks", ""), folded_poison.get("two_masks", "")
        section["undef_to_poison_substitutions_in_module"] = n_sub
        section["two_masks_zero_trip_folded_original"] = tm_u
        section["two_masks_zero_trip_folded_after_undef_to_poison"] = tm_p
        rets_u, rets_p = ret_operands(tm_u), ret_operands(tm_p)
        self.check("c.zero_trip_original_keeps_defined_bit",
                   "with `undef` kept, LLVM folds the zero-trip path of `two_masks` to a value "
                   "that still depends on the argument and is not `poison`",
                   {"ret": rets_u, "instructions": len(body_lines(tm_u))},
                   bool(rets_u) and not any(POISON_TOKEN.search(r) for r in rets_u)
                   and "%0" in tm_u.split("\n", 1)[1])
        self.check("c.zero_trip_poison_rewrite_returns_poison",
                   "after the textual `undef -> poison` rewrite, LLVM folds the same path to `ret poison`",
                   {"ret": rets_p, "instructions": len(body_lines(tm_p))},
                   len(rets_p) == 1 and bool(POISON_TOKEN.search(rets_p[0])) and len(body_lines(tm_p)) == 1)
        self.result["c_undef"] = section

    # -- stage 2: Rust-side undef -----------------------------------------
    def rust_undef(self) -> None:
        _, ir, _ = self.compile_rust("rust_uninit", RUST_UNINIT, "abort")
        fns = functions(ir)
        wanted = ["uninit_pair", "make_padded", "none_or", "mk_e"]
        per_fn = {name: undef_lines(fns.get(name, "")) for name in wanted}
        section: dict[str, Any] = {
            "standalone_undef_lines_by_function": per_fn,
            "functions": {name: fns.get(name, "<missing>") for name in wanted},
        }
        self.check("rust.safe_maybeuninit_return_is_undef",
                   "safe Rust returning `(MaybeUninit<i32>, i32)` emits an `undef` aggregate operand",
                   per_fn["uninit_pair"],
                   any("insertvalue" in ln for ln in per_fn["uninit_pair"]))

        wrapper = (
            "\ndefine i32 @field0_of_uninit_pair(i32 %x) {\n"
            "  %r = call { i32, i32 } @uninit_pair(i32 %x)\n"
            "  %f = extractvalue { i32, i32 } %r, 0\n"
            "  ret i32 %f\n}\n"
        )
        only = fns.get("uninit_pair", "")
        only = re.sub(r"\) unnamed_addr #\d+", ")", only)
        only = re.sub(r" !\w+ !\d+", "", only)
        zeroed, n_sub = rewrite_undef_to_zero(only)
        folded_u = functions(self.opt_fold("h2_undef.ll", only + "\n" + wrapper, OPT_EXTRACT_PIPELINE))
        folded_z = functions(self.opt_fold("h2_zero.ll", zeroed + "\n" + wrapper, OPT_EXTRACT_PIPELINE))
        ret_u = ret_operands(folded_u.get("field0_of_uninit_pair", ""))
        ret_z = ret_operands(folded_z.get("field0_of_uninit_pair", ""))
        section["undef_to_zero_substitutions"] = n_sub
        section["uninit_pair_after_undef_to_zero"] = zeroed
        section["field0_folded_original"] = ret_u
        section["field0_folded_after_undef_to_zero"] = ret_z
        self.check("rust.field0_original_is_undef",
                   "LLVM folds the uninitialized component of the original IR to `undef`",
                   ret_u, ret_u == ["ret i32 undef"])
        self.check("rust.field0_zero_rewrite_is_zero",
                   "after the textual `undef -> zero` rewrite the same component folds to the constant 0",
                   ret_z, ret_z == ["ret i32 0"])
        self.result["rust_undef"] = section

    # -- stage 3: source-level UB that the C front end makes defined in IR --
    def vla_vs_vec(self) -> None:
        c_ir = self.compile_c("c_vla", C_VLA)
        c_fns = functions(c_ir)
        _, r_ir, _ = self.compile_rust("rust_vec", RUST_VEC, "abort")
        r_fns = functions(r_ir)

        def summarize(text: str) -> dict[str, Any]:
            return {
                "add_nsw_i32": len(re.findall(r"= add nsw i32 ", text)),
                "add_plain_i32": len(re.findall(r"= add i32 ", text)),
                "zext_i32_to_i64": len(re.findall(r"= zext (?:nneg )?i32 [^\n]* to i64", text)),
                "zext_nneg_i32_to_i64": len(re.findall(r"= zext nneg i32 [^\n]* to i64", text)),
                "sext_i32_to_i64": len(re.findall(r"= sext i32 [^\n]* to i64", text)),
                "alloca_dynamic": len(re.findall(r"= alloca [^\n]*, i64 %", text)),
                "calls_handle_error": count_calls_to(text, "handle_error"),
            }

        section = {
            "c": {name: summarize(c_fns.get(name, "")) for name in ("vla2d", "vla1d")},
            "rust": {name: summarize(r_fns.get(name, "")) for name in ("vec2d", "vec1d")},
            "c_functions": {name: c_fns.get(name, "<missing>") for name in ("vla2d", "vla1d")},
            "rust_vec1d": r_fns.get("vec1d", "<missing>"),
        }
        c2, c1 = section["c"]["vla2d"], section["c"]["vla1d"]
        r2, r1 = section["rust"]["vec2d"], section["rust"]["vec1d"]
        self.check("c.vla_bound_is_nsw_add_then_zext",
                   "clang lowers an `int` VLA bound `n + 1` to `add nsw i32` followed by a plain "
                   "`zext` to i64 feeding a dynamic `alloca`",
                   {"vla2d": c2, "vla1d": c1},
                   c2["add_nsw_i32"] == 2 and c2["zext_i32_to_i64"] == 2 and c2["sext_i32_to_i64"] == 0
                   and c2["zext_nneg_i32_to_i64"] == 0 and c2["alloca_dynamic"] == 1
                   and c1["add_nsw_i32"] == 1 and c1["zext_i32_to_i64"] == 1 and c1["sext_i32_to_i64"] == 0)
        self.check("rust.vec_len_is_wrapping_add_then_sext",
                   "rustc lowers `(n + 1) as usize` to a flag-free `add i32` followed by `sext` to "
                   "i64, and reaches the allocation-error path",
                   {"vec2d": r2, "vec1d": r1},
                   r2["add_plain_i32"] == 2 and r2["add_nsw_i32"] == 0 and r2["sext_i32_to_i64"] == 2
                   and r1["add_plain_i32"] == 1 and r1["sext_i32_to_i64"] == 1
                   and r1["calls_handle_error"] >= 1)
        unwind = {"invoke": count_instr(r_ir, "invoke"), "landingpad": count_instr(r_ir, "landingpad"),
                  "resume": count_instr(r_ir, "resume"),
                  "defines_with_personality": len(re.findall(r"^define[^\n]*\bpersonality\b", r_ir, re.M)),
                  "defines": len(re.findall(r"^define\b", r_ir, re.M))}
        section["rust_safe_only_module_unwinding_under_panic_abort"] = unwind
        self.check("rust.safe_only_panic_abort_has_no_invoke",
                   "a safe-Rust-only module compiled with `-Cpanic=abort` has no `invoke`, "
                   "`landingpad` or `resume`",
                   unwind, unwind["invoke"] == 0 and unwind["landingpad"] == 0 and unwind["resume"] == 0)
        self.result["source_ub_vs_ir"] = section

    # -- stage 4: attributes and unwinding ---------------------------------
    def abi_and_unwind(self) -> None:
        section: dict[str, Any] = {}
        per_mode: dict[str, Any] = {}
        abort_fns: dict[str, str] = {}
        for mode in ("abort", "unwind"):
            _, ir, _ = self.compile_rust("rust_abi", RUST_ABI, mode)
            fns = functions(ir)
            if mode == "abort":
                abort_fns = fns
                section["module_mustprogress_occurrences_abort"] = len(re.findall(r"\bmustprogress\b", ir))
            per_mode[mode] = {
                "module": {"invoke": count_instr(ir, "invoke"),
                           "landingpad": count_instr(ir, "landingpad"),
                           "resume": count_instr(ir, "resume")},
                "per_function": {
                    name: {"invoke": count_instr(fns.get(name, ""), "invoke"),
                           "landingpad": count_instr(fns.get(name, ""), "landingpad"),
                           "calls_panic_cannot_unwind": count_calls_to(fns.get(name, ""), "panic_cannot_unwind"),
                           "personality": "personality" in fns.get(name, "").split("\n", 1)[0]}
                    for name in ("call_cunwind_with_guard", "call_cunwind_no_guard", "call_c_with_guard")
                },
            }
        section["unwinding"] = per_mode
        section["functions_abort"] = {
            name: abort_fns.get(name, "<missing>")
            for name in ("call_cunwind_with_guard", "call_cunwind_no_guard", "call_c_with_guard")
        }
        a = per_mode["abort"]["per_function"]
        self.check("rust.c_unwind_call_is_invoke_under_panic_abort",
                   "under `-Cpanic=abort`, a call to an `extern \"C-unwind\"` function is an "
                   "`invoke` with a `landingpad` that reaches `panic_cannot_unwind`, with or "
                   "without a `Drop` guard; a call to an `extern \"C\"` function is not",
                   a,
                   a["call_cunwind_with_guard"]["invoke"] == 1 and a["call_cunwind_with_guard"]["landingpad"] == 1
                   and a["call_cunwind_with_guard"]["calls_panic_cannot_unwind"] >= 1
                   and a["call_cunwind_no_guard"]["invoke"] == 1 and a["call_cunwind_no_guard"]["landingpad"] == 1
                   and a["call_c_with_guard"]["invoke"] == 0 and a["call_c_with_guard"]["landingpad"] == 0)
        guard_text = abort_fns.get("call_cunwind_with_guard", "")
        pad = guard_text.split("landingpad", 1)[1].split("panic_cannot_unwind", 1)[0] if "landingpad" in guard_text else ""
        store_in_pad = len(re.findall(r"^\s*store ", pad, re.M))
        section["stores_between_landingpad_and_abort"] = store_in_pad
        self.check("rust.cleanup_pad_runs_drop_before_abort",
                   "the landing pad of the guarded call performs the guard's store before aborting",
                   store_in_pad, store_in_pad >= 1)

        headers = {name: abort_fns.get(name, "").split("\n", 1)[0]
                   for name in ("takes_ref_and_bool", "slice_and_opt_string", "has_duplicate")}
        section["headers_abort"] = headers
        attrs = {
            name: {attr: bool(re.search(r"(?<![A-Za-z])" + re.escape(attr) + r"(?![A-Za-z])", hdr))
                   for attr in ("noundef", "noalias", "nonnull", "readonly", "dereferenceable",
                                "sret", "range", "zeroext")}
            for name, hdr in headers.items()
        }
        section["parameter_attributes"] = attrs
        self.check("rust.parameter_attributes_present",
                   "rustc attaches `noundef`/`noalias`/`dereferenceable` to reference parameters, "
                   "`range` to a slice length, and `sret` to an `Option<String>` return slot",
                   attrs,
                   attrs["takes_ref_and_bool"]["noundef"] and attrs["takes_ref_and_bool"]["noalias"]
                   and attrs["takes_ref_and_bool"]["dereferenceable"]
                   and attrs["slice_and_opt_string"]["sret"] and attrs["slice_and_opt_string"]["range"]
                   and attrs["has_duplicate"]["nonnull"])
        self.check("rust.mustprogress_is_routine",
                   "`mustprogress` occurs in the attribute groups of an ordinary rustc -O1 module",
                   section["module_mustprogress_occurrences_abort"],
                   section["module_mustprogress_occurrences_abort"] > 0)
        self.check("c.mustprogress_is_routine",
                   "`mustprogress` occurs in the attribute groups of an ordinary clang -O1 C module",
                   self.result["c_undef"]["module_mustprogress_occurrences"],
                   self.result["c_undef"]["module_mustprogress_occurrences"] > 0)

        # `-Z` gating: RUSTC_BOOTSTRAP=-1 makes a nightly build apply stable-channel rules.
        env = dict(os.environ)
        env["RUSTC_BOOTSTRAP"] = "-1"
        rc_stable, _, err_stable = self.compile_rust("rust_trivial", RUST_TRIVIAL.replace(
            "pub fn", "#![crate_type = \"lib\"]\npub fn", 1), "abort", env=env, check=False)
        env.pop("RUSTC_BOOTSTRAP")
        rc_default, _, _ = self.compile_rust("rust_trivial", RUST_TRIVIAL.replace(
            "pub fn", "#![crate_type = \"lib\"]\npub fn", 1), "abort", env=env, check=False)
        gating = {"rc_with_RUSTC_BOOTSTRAP_minus_1": rc_stable,
                  "first_error_line": first_line(err_stable),
                  "rc_without_RUSTC_BOOTSTRAP": rc_default}
        section["z_flag_gating"] = gating
        self.check("rustc.z_flag_rejected_under_stable_rules",
                   "with stable-channel rules forced, `-Zinline-mir=no` is rejected with the "
                   "nightly-only diagnostic; without them this toolchain accepts it",
                   gating,
                   rc_stable != 0 and "only accepted on the nightly compiler" in err_stable
                   and rc_default == 0)
        self.result["abi_and_unwind"] = section

    def finish(self) -> int:
        self.result["checks"] = self.checks
        failed = [c["id"] for c in self.checks if not c["pass"]]
        self.result["summary"] = {"checks": len(self.checks), "failed": failed}
        return 1 if failed else 0


def resolve(tool: str | None, env_var: str, default: str) -> str:
    candidate = tool or os.environ.get(env_var) or shutil.which(default)
    if not candidate or not Path(candidate).exists():
        raise SystemExit(f"cannot find {default}; pass --{default} or set {env_var}")
    return candidate


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--clang")
    parser.add_argument("--rustc")
    parser.add_argument("--opt")
    parser.add_argument("--out", default="probe_results.json")
    parser.add_argument("--keep-ir", help="directory that receives the emitted C-side IR modules")
    args = parser.parse_args()

    clang = resolve(args.clang, "R2C2_PROBE_CLANG", "clang")
    rustc = resolve(args.rustc, "R2C2_PROBE_RUSTC", "rustc")
    opt = resolve(args.opt, "R2C2_PROBE_OPT", "opt")
    keep = Path(args.keep_ir).resolve() if args.keep_ir else None
    if keep is not None:
        keep.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="r2c2_probe_") as tmp:
        probe = Probe(clang, rustc, opt, Path(tmp), keep)
        probe.versions()
        probe.c_undef()
        probe.rust_undef()
        probe.vla_vs_vec()
        probe.abi_and_unwind()
        status = probe.finish()

    Path(args.out).write_text(json.dumps(probe.result, indent=2, sort_keys=True) + "\n")
    for item in probe.checks:
        print(("PASS  " if item["pass"] else "FAIL  ") + item["id"])
    print(f"{len(probe.checks)} checks, {len(probe.result['summary']['failed'])} failed")
    return status


if __name__ == "__main__":
    sys.exit(main())
