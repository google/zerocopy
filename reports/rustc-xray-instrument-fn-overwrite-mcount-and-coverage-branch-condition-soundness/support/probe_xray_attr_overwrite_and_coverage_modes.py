#!/usr/bin/env python3
"""Probe rustc function-entry instrumentation attributes and coverage levels.

Everything this script reports is measured by running the given nightly `rustc`
and the LLVM tools shipped in its sysroot (`llvm-tools` component). Nothing is
read from a table of expected results; the only values not produced by a tool
are the *oracles* (clearly named `oracle_*`), which are recomputed here from
the probe inputs by ordinary Python boolean evaluation, and the *push
sequences* of part A3, which transliterate a quoted upstream Rust function and
are labelled `derived_from_source`.

Parts
  A1  real rustc, 7 `-Z instrument-xray` / `-Z instrument-mcount` command lines,
      functions without any per-function attribute (works on every nightly).
  A2  real rustc, the same 7 command lines against functions carrying
      `#[instrument_fn = "on" | "off"]`. Runs only when the given rustc accepts
      `#![feature(instrument_fn)]`; otherwise the rejection is recorded.
  A3  LLVM-level replay. For each (command-line state, attribute) cell the
      sequence of `"function-instrument"` string attributes that the quoted
      upstream function pushes is (i) handed to the toolchain's own compiled
      `LLVMRustAddFunctionAttributes` and (ii) written, in push order, into an
      LLVM IR attribute group that is assembled and compiled by the toolchain's
      `llvm-as`, `llvm-dis` and `llc`. The surviving attribute, the XRay sleds
      and the `xray_instr_map` relocations are read back from the tools.
  B   real rustc `-C instrument-coverage -Z coverage-options=block|branch|
      condition`, real `llvm-profdata` and `llvm-cov export`, plus built-MIR
      shape counts from `-Z dump-mir`.

Usage
  python3 probe_xray_attr_overwrite_and_coverage_modes.py \
      [--rustc PATH] [--out results.json]

Only x86-64 ELF targets are analysed (the sled byte patterns are x86-64).
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

TARGET = "x86_64-unknown-linux-gnu"

# ----------------------------------------------------------------------------
# Probe inputs
# ----------------------------------------------------------------------------

XRAY_CLI_ONLY_RS = r"""
#![crate_type = "lib"]
#![allow(dead_code)]

#[no_mangle]
#[inline(never)]
pub fn fn_default(x: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[inline(always)]
fn inlined_callee(x: u64) -> u64 {
    x ^ 0x5a5a
}

#[no_mangle]
#[inline(never)]
pub fn caller_inlines_callee(x: u64) -> u64 {
    inlined_callee(x).wrapping_add(7)
}

#[no_mangle]
#[inline(never)]
pub fn fn_with_loop(n: u64) -> u64 {
    let mut s = 0u64;
    let mut i = 0u64;
    while i < n {
        s = s.rotate_left(5) ^ i;
        i += 1;
    }
    s
}
""".lstrip()

XRAY_CLI_ONLY_FUNCTIONS = ["fn_default", "caller_inlines_callee", "fn_with_loop"]

# Same shape as upstream `tests/codegen-llvm/instrument_fn.rs`, with real bodies
# and an `#[inline(always)]` callee that opts out while its caller opts in.
XRAY_INSTRUMENT_FN_RS = r"""
#![crate_type = "lib"]
#![feature(instrument_fn)]
#![allow(dead_code)]

#[no_mangle]
#[inline(never)]
pub fn fn_default(x: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[no_mangle]
#[inline(never)]
#[instrument_fn = "on"]
pub fn fn_explicit_on(x: u64) -> u64 {
    x.wrapping_mul(5).wrapping_add(2)
}

#[no_mangle]
#[inline(never)]
#[instrument_fn = "off"]
pub fn fn_explicit_off(x: u64) -> u64 {
    x.wrapping_mul(7).wrapping_add(3)
}

#[inline(always)]
#[instrument_fn = "off"]
fn excluded_inline_callee(x: u64) -> u64 {
    x ^ 0x5a5a
}

#[no_mangle]
#[inline(never)]
#[instrument_fn = "on"]
pub fn caller_inlines_excluded(x: u64) -> u64 {
    excluded_inline_callee(x).wrapping_add(7)
}
""".lstrip()

XRAY_INSTRUMENT_FN_FUNCTIONS = [
    "fn_default",
    "fn_explicit_on",
    "fn_explicit_off",
    "caller_inlines_excluded",
]

FEATURE_GATE_RS = r"""
#![crate_type = "lib"]
#![feature(instrument_fn)]

#[instrument_fn = "off"]
pub fn gated() {}
""".lstrip()

INSTRUMENT_CONFIGS = [
    ("xray_default", ["-Zinstrument-xray"]),
    ("xray_always", ["-Zinstrument-xray=always"]),
    ("xray_never", ["-Zinstrument-xray=never"]),
    ("xray_always_then_never_cli", ["-Zinstrument-xray=always", "-Zinstrument-xray=never"]),
    ("xray_always_comma_never_single_arg", ["-Zinstrument-xray=always,never"]),
    ("mcount_default", ["-Zinstrument-mcount"]),
    ("mcount_fentry", ["-Zinstrument-mcount=fentry"]),
]

# One function, one attribute group. `{PUSHES}` is replaced by string attributes
# in push order; later text never reorders or removes them.
REPLAY_LL_TEMPLATE = """
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i64 @replay_target(i64 %x) #0 {
start:
  %m = mul i64 %x, 3
  %r = add i64 %m, 1
  ret i64 %r
}

attributes #0 = { nounwind {PUSHES} }
""".lstrip()

ADD_FN_ATTRS_HARNESS_C = r"""
/* Calls the toolchain's own compiled `LLVMRustAddFunctionAttributes` (a
 * non-exported function of librustc_driver, located through the ELF symbol
 * table) with a caller-chosen sequence of "function-instrument" string
 * attributes and prints the value that survives on the function.
 * librustc_driver uses initial-exec TLS, so it is linked at startup rather
 * than opened with dlopen; RTLD_NOLOAD only fetches its load address. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <link.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void *Ref;
typedef void (*add_fn_attrs_t)(Ref fn, unsigned index, Ref *attrs, size_t n);

static void *must_sym(const char *name) {
  void *p = dlsym(RTLD_DEFAULT, name);
  if (!p) { fprintf(stderr, "missing symbol %s\n", name); exit(3); }
  return p;
}

int main(int argc, char **argv) {
  if (argc < 3) return 2;
  void *h = dlopen(argv[1], RTLD_NOW | RTLD_NOLOAD);
  if (!h) { fprintf(stderr, "driver library is not loaded\n"); return 3; }
  struct link_map *lm = NULL;
  if (dlinfo(h, RTLD_DI_LINKMAP, &lm) != 0 || !lm) return 3;
  add_fn_attrs_t add =
      (add_fn_attrs_t)((uintptr_t)lm->l_addr + (uintptr_t)strtoull(argv[2], NULL, 16));

  Ref (*ctx_create)(void) = must_sym("LLVMContextCreate");
  Ref (*mod_create)(const char *, Ref) = must_sym("LLVMModuleCreateWithNameInContext");
  Ref (*void_ty)(Ref) = must_sym("LLVMVoidTypeInContext");
  Ref (*fn_ty)(Ref, Ref *, unsigned, int) = must_sym("LLVMFunctionType");
  Ref (*add_function)(Ref, const char *, Ref) = must_sym("LLVMAddFunction");
  Ref (*mk_attr)(Ref, const char *, unsigned, const char *, unsigned) =
      must_sym("LLVMCreateStringAttribute");
  Ref (*get_attr)(Ref, unsigned, const char *, unsigned) =
      must_sym("LLVMGetStringAttributeAtIndex");
  const char *(*attr_val)(Ref, unsigned *) = must_sym("LLVMGetStringAttributeValue");

  Ref ctx = ctx_create();
  Ref m = mod_create("replay", ctx);
  Ref f = add_function(m, "f", fn_ty(void_ty(ctx), NULL, 0, 0));

  static const char key[] = "function-instrument";
  size_t n = (size_t)(argc - 3);
  Ref *attrs = calloc(n ? n : 1, sizeof(Ref));
  for (size_t i = 0; i < n; i++)
    attrs[i] = mk_attr(ctx, key, (unsigned)strlen(key), argv[3 + i],
                       (unsigned)strlen(argv[3 + i]));
  /* rustc's `apply_to_llfn` skips the call for an empty slice. */
  if (n) add(f, 0xFFFFFFFFu /* AttributePlace::Function */, attrs, n);

  Ref got = get_attr(f, 0xFFFFFFFFu, key, (unsigned)strlen(key));
  unsigned len = 0;
  const char *v = got ? attr_val(got, &len) : NULL;
  if (v) printf("SURVIVOR=%.*s\n", (int)len, v);
  else printf("SURVIVOR=\n");
  return 0;
}
""".lstrip()

COVERAGE_RS = r"""
// Probe program for `-C instrument-coverage -Z coverage-options=block|branch|condition`.
#![feature(coverage_attribute)]
use std::hint::black_box;

macro_rules! def_site_if {
    ($x:expr) => {{
        let v: u32 = $x;
        if v > 5 { 1u32 } else { 2u32 }
    }};
}

macro_rules! call_site_if {
    ($cond:expr) => {
        if $cond { 1u32 } else { 2u32 }
    };
}

macro_rules! define_macro_fn {
    ($name:ident) => {
        #[inline(never)]
        fn $name(x: u32) -> u32 {
            if x > 5 { 1 } else { 2 }
        }
    };
}

macro_rules! define_fn_with_call_site_body {
    ($name:ident, $arg:ident, $body:block) => {
        #[inline(never)]
        fn $name($arg: u32) -> u32 $body
    };
}

#[inline(never)]
fn normal_if(x: u32) -> u32 {
    if x > 5 { 1 } else { 2 }
}

#[inline(never)]
fn macro_def_site_condition(x: u32) -> u32 {
    def_site_if!(x)
}

#[inline(never)]
fn macro_call_site_condition(x: u32) -> u32 {
    call_site_if!(x > 5)
}

define_macro_fn!(macro_generated_fn);

define_fn_with_call_site_body!(macro_fn_call_site_body, x, {
    if x > 5 { 1 } else { 2 }
});

#[inline(never)]
fn standalone_conditions(x: u32, y: u32) -> u32 {
    let cond_pair: bool = (x > 10) && (y < 50);
    let single: bool = x > 10;
    let or_pair: bool = (x > 100) || (y < 5);
    let nested: bool = (x > 1) && ((y > 1) || (x > 2));
    (cond_pair as u32) + (single as u32) + (or_pair as u32) + (nested as u32)
}

#[inline(never)]
fn negated_conditions(x: u32, y: u32, z: u32) -> u32 {
    let mut acc = 0;
    if !(x > 100) {
        acc += 1;
    }
    if !!(y < 50) {
        acc += 2;
    }
    if !!!(z == 0) {
        acc += 4;
    }
    acc
}

#[coverage(off)]
#[inline(always)]
fn excluded_inline_callee(x: u32) -> u32 {
    if x > 5 { x * 2 } else { x + 1 }
}

#[inline(never)]
fn caller_of_excluded(x: u32) -> u32 {
    excluded_inline_callee(x) + 1
}

fn main() {
    let mut sink = 0u32;
    for x in [1u32, 9, 10] {
        sink ^= normal_if(black_box(x));
        sink ^= macro_def_site_condition(black_box(x));
        sink ^= macro_call_site_condition(black_box(x));
        sink ^= macro_generated_fn(black_box(x));
        sink ^= macro_fn_call_site_body(black_box(x));
        sink ^= caller_of_excluded(black_box(x));
    }
    for (x, y) in [(20u32, 10u32), (20, 60), (5, 10), (200, 3), (20, 0), (0, 0)] {
        sink ^= standalone_conditions(black_box(x), black_box(y));
    }
    for (x, y, z) in [(1u32, 10u32, 0u32), (2, 20, 0), (3, 60, 0), (4, 70, 0), (200, 80, 5)] {
        sink ^= negated_conditions(black_box(x), black_box(y), black_box(z));
    }
    black_box(sink);
}
""".lstrip()

# The same argument lists as `main` above; the oracles are computed from these.
SIMPLE_INPUTS = [(1,), (9,), (10,)]
STANDALONE_INPUTS = [(20, 10), (20, 60), (5, 10), (200, 3), (20, 0), (0, 0)]
NEGATED_INPUTS = [(1, 10, 0), (2, 20, 0), (3, 60, 0), (4, 70, 0), (200, 80, 5)]

COVERAGE_FUNCTIONS = [
    "normal_if",
    "macro_def_site_condition",
    "macro_call_site_condition",
    "macro_generated_fn",
    "macro_fn_call_site_body",
    "standalone_conditions",
    "negated_conditions",
    "caller_of_excluded",
    "main",
]

# Each site: function, anchor line fragment, expression text, lowest coverage
# level at which upstream source says a branch region exists, the inputs, a
# reachability predicate and the source-level truth of the expression.
BRANCH_SITES = [
    dict(site="normal_if: x > 5", function="normal_if", anchor="fn normal_if(",
         text="x > 5", level="branch", inputs=SIMPLE_INPUTS,
         reached=lambda x: True, truth=lambda x: x > 5),
    dict(site="macro_call_site_condition: x > 5 (tokens written at the macro call site)",
         function="macro_call_site_condition", anchor="fn macro_call_site_condition(",
         text="x > 5", level="branch", inputs=SIMPLE_INPUTS,
         reached=lambda x: True, truth=lambda x: x > 5),
    dict(site="macro_fn_call_site_body: x > 5 (function item from a macro, body block from the call site)",
         function="macro_fn_call_site_body",
         anchor="define_fn_with_call_site_body!(macro_fn_call_site_body",
         text="x > 5", level="branch", inputs=SIMPLE_INPUTS,
         reached=lambda x: True, truth=lambda x: x > 5),
    dict(site="standalone: (x > 10) [lhs of &&]", function="standalone_conditions",
         anchor="let cond_pair", text="(x > 10)", level="branch", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: True, truth=lambda x, y: x > 10),
    dict(site="standalone: (y < 50) [rhs of &&]", function="standalone_conditions",
         anchor="let cond_pair", text="(y < 50)", level="condition", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: x > 10, truth=lambda x, y: y < 50),
    dict(site="standalone: (x > 100) [lhs of ||]", function="standalone_conditions",
         anchor="let or_pair", text="(x > 100)", level="branch", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: True, truth=lambda x, y: x > 100),
    dict(site="standalone: (y < 5) [rhs of ||]", function="standalone_conditions",
         anchor="let or_pair", text="(y < 5)", level="condition", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: not (x > 100), truth=lambda x, y: y < 5),
    dict(site="standalone: (x > 1) [lhs of outer &&]", function="standalone_conditions",
         anchor="let nested", text="(x > 1)", level="branch", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: True, truth=lambda x, y: x > 1),
    dict(site="standalone: (y > 1) [lhs of inner ||]", function="standalone_conditions",
         anchor="let nested", text="(y > 1)", level="branch", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: x > 1, truth=lambda x, y: y > 1),
    dict(site="standalone: (x > 2) [rhs of inner ||]", function="standalone_conditions",
         anchor="let nested", text="(x > 2)", level="condition", inputs=STANDALONE_INPUTS,
         reached=lambda x, y: x > 1 and not (y > 1), truth=lambda x, y: x > 2),
    dict(site="negated: !(x > 100)", function="negated_conditions",
         anchor="fn negated_conditions(", text="!(x > 100)", level="branch",
         inputs=NEGATED_INPUTS, reached=lambda x, y, z: True,
         truth=lambda x, y, z: not (x > 100)),
    dict(site="negated: !!(y < 50)", function="negated_conditions",
         anchor="fn negated_conditions(", text="!!(y < 50)", level="branch",
         inputs=NEGATED_INPUTS, reached=lambda x, y, z: True,
         truth=lambda x, y, z: not (not (y < 50))),
    dict(site="negated: !!!(z == 0)", function="negated_conditions",
         anchor="fn negated_conditions(", text="!!!(z == 0)", level="branch",
         inputs=NEGATED_INPUTS, reached=lambda x, y, z: True,
         truth=lambda x, y, z: not (not (not (z == 0)))),
]

# (rhs site, lhs site, lhs outcome that leads to evaluating the rhs)
FLOW_PAIRS = [
    ("standalone: (y < 50) [rhs of &&]", "standalone: (x > 10) [lhs of &&]", "true"),
    ("standalone: (y < 5) [rhs of ||]", "standalone: (x > 100) [lhs of ||]", "false"),
    ("standalone: (x > 2) [rhs of inner ||]", "standalone: (y > 1) [lhs of inner ||]", "false"),
    ("standalone: (y > 1) [lhs of inner ||]", "standalone: (x > 1) [lhs of outer &&]", "true"),
]

LEVEL_RANK = {"block": 0, "branch": 1, "condition": 2}

# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------


class Ctx:
    def __init__(self, rustc: str, work: str):
        self.rustc = rustc
        self.work = work
        self.sysroot = run([rustc, "--print", "sysroot"]).stdout.strip()
        self.tool_dir = os.path.join(self.sysroot, "lib", "rustlib", TARGET, "bin")
        self.scrub_map = [(self.work, "<work>"), (self.sysroot, "<sysroot>")]

    def tool(self, name: str) -> str:
        path = os.path.join(self.tool_dir, name)
        if not os.path.exists(path):
            raise SystemExit(f"missing {name} in the sysroot tool directory; "
                             "install the llvm-tools component")
        return path

    def scrub(self, text: str) -> str:
        for needle, repl in self.scrub_map:
            text = text.replace(needle, repl)
        text = re.sub(r"/rustc(-dev)?/[0-9a-f]{40}/", "/rustc/<commit>/", text)
        home = os.path.expanduser("~")
        if home and home != "/":
            text = text.replace(home, "<home>")
        return text


def run(cmd, cwd=None, env=None, timeout=300):
    return subprocess.run(cmd, cwd=cwd, env=env, timeout=timeout,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


def first_error(stderr: str) -> str:
    for line in stderr.splitlines():
        if line.startswith("error"):
            return line
    return stderr.strip().splitlines()[0] if stderr.strip() else ""


INTERESTING_ATTR = re.compile(
    r'"(function-instrument|xray-[a-z-]+|instrument-function-entry-inlined|'
    r'fentry-call|mnop-mcount|mrecord-mcount)"(?:="([^"]*)")?')


def ir_function_attrs(ll_text: str, functions) -> dict:
    groups = {}
    for m in re.finditer(r"^attributes #(\d+) = \{(.*)\}\s*$", ll_text, re.M):
        groups[m.group(1)] = m.group(2)
    out = {}
    for fn in functions:
        m = re.search(r"^define [^\n]*@%s\([^\n]*?#(\d+)[^\n]*\{\s*$" % re.escape(fn), ll_text, re.M)
        if not m:
            out[fn] = None
            continue
        body = groups.get(m.group(1), "")
        out[fn] = [f'"{k}"="{v}"' if f'"{k}"="{v}"' in body else f'"{k}"'
                   for k, v in INTERESTING_ATTR.findall(body)]
    return out


ENTRY_SLED = "eb 09 66 0f 1f 84 00 00 02 00 00"
EXIT_SLED = "c3 2e 66 0f 1f 84 00 00 02 00 00"


def object_function_facts(ctx: Ctx, obj: str, functions) -> dict:
    """Per function: sled counts (byte patterns), first instructions, call relocations."""
    dis = run([ctx.tool("llvm-objdump"), "-d", "-r", obj]).stdout
    facts = {fn: dict(defined=False, entry_sleds=0, exit_sleds=0, first_instructions=[],
                      last_instructions=[], call_relocation_targets=[]) for fn in functions}
    current, raw, relocs, insns = None, [], [], []

    def flush():
        if current in facts:
            stream = " ".join(raw)
            f = facts[current]
            f["defined"] = True
            f["entry_sleds"] = stream.count(ENTRY_SLED)
            f["exit_sleds"] = stream.count(EXIT_SLED)
            f["first_instructions"] = insns[:3]
            f["last_instructions"] = insns[-2:]
            f["call_relocation_targets"] = relocs[:]

    for line in dis.splitlines():
        m = re.match(r"^[0-9a-f]+ <([^>]+)>:\s*$", line)
        if m:
            flush()
            current, raw, relocs, insns = m.group(1), [], [], []
            continue
        m = re.match(r"^\s*[0-9a-f]+:\s((?:[0-9a-f]{2}\s)+)\s*(.*)$", line)
        if m and current is not None:
            raw.extend(m.group(1).split())
            text = re.sub(r"\s+", " ", m.group(2)).strip()
            if text:
                insns.append(text)
            continue
        m = re.match(r"^\s+[0-9a-f]+:\s+(R_X86_64_\S+)\s+(\S+)$", line)
        if m and current is not None:
            relocs.append(f"{m.group(1)} {m.group(2)}")
    flush()

    # xray_instr_map relocations, attributed through the `.text.<fn>` section symbol.
    rel = run([ctx.tool("llvm-readobj"), "-r", obj]).stdout
    in_xray = False
    counts = {fn: 0 for fn in functions}
    for line in rel.splitlines():
        m = re.match(r"^\s*Section \(\d+\) (\S+) \{", line)
        if m:
            in_xray = m.group(1) == ".relaxray_instr_map"
            continue
        if in_xray:
            m = re.match(r"^\s*0x[0-9A-Fa-f]+ R_X86_64_PC64 \.text\.(\S+) ", line)
            if m and m.group(1) in counts:
                counts[m.group(1)] += 1
    for fn in functions:
        f = facts[fn]
        f["xray_instr_map_pc64_relocations"] = counts[fn]
        f["mcount_or_fentry_call_relocations"] = sum(
            1 for r in f["call_relocation_targets"]
            if re.search(r"\b(mcount|_mcount|__fentry__)\b", r))
    return facts


def compile_instrument_matrix(ctx: Ctx, source_name: str, functions) -> dict:
    out = {}
    for name, flags in INSTRUMENT_CONFIGS:
        ll, obj = f"{name}.ll", f"{name}.o"
        cmd = [ctx.rustc, "--edition", "2021", "--target", TARGET, "-C", "opt-level=2",
               "-C", "codegen-units=1", *flags, f"--emit=llvm-ir={ll},obj={obj}", source_name]
        proc = run(cmd, cwd=ctx.work)
        entry = dict(flags=flags, rc=proc.returncode)
        if proc.returncode != 0:
            entry["first_error"] = ctx.scrub(first_error(proc.stderr))
            out[name] = entry
            continue
        ll_text = open(os.path.join(ctx.work, ll)).read()
        attrs = ir_function_attrs(ll_text, functions)
        facts = object_function_facts(ctx, os.path.join(ctx.work, obj), functions)
        entry["llvm_ir_defined_functions"] = sorted(
            re.findall(r"^define [^\n]*?@([\w.$]+)\(", ll_text, re.M))
        entry["functions"] = {
            fn: dict(llvm_ir_instrument_attributes=attrs[fn], **facts[fn]) for fn in functions}
        out[name] = entry
        for path in (ll, obj):
            os.remove(os.path.join(ctx.work, path))
    return out


# ----------------------------------------------------------------------------
# Part A3: push sequences transliterated from quoted upstream source
# ----------------------------------------------------------------------------


def pushes_independent_booleans_never_first(cli: str, attr: str):
    """`instrument_function_attr` once `#[instrument_fn]` exists (quoted in REPORT.md):

        let mut never = options.never;
        let mut always = options.always;
        match instrument_fn {
            Some(InstrumentFnAttr::On) => { always = true; }
            Some(InstrumentFnAttr::Off) => { never = true; }
            None => {}
        }
        if never { push("function-instrument", "xray-never") }
        if always { push("function-instrument", "xray-always") }
    """
    never, always = cli == "never", cli == "always"
    if attr == "on":
        always = True
    elif attr == "off":
        never = True
    out = []
    if never:
        out.append("xray-never")
    if always:
        out.append("xray-always")
    return out


def pushes_independent_booleans_always_first(cli: str, attr: str):
    """Same two booleans, pushed in the order used before `#[instrument_fn]` existed
    (`if options.always { .. } if options.never { .. }`). Counterfactual for cells
    with an attribute: shows that no push order repairs the two-boolean encoding."""
    never, always = cli == "never", cli == "always"
    if attr == "on":
        always = True
    elif attr == "off":
        never = True
    out = []
    if always:
        out.append("xray-always")
    if never:
        out.append("xray-never")
    return out


def pushes_three_state(cli: str, attr: str):
    """Candidate repair: one three-valued mode, overridden wholesale by the attribute."""
    mode = {"on": "always", "off": "never"}.get(attr, cli)
    return {"always": ["xray-always"], "never": ["xray-never"], "threshold": []}[mode]


PUSH_VARIANTS = [
    ("independent_booleans_never_pushed_first", pushes_independent_booleans_never_first),
    ("independent_booleans_always_pushed_first", pushes_independent_booleans_always_first),
    ("three_state_mode", pushes_three_state),
]


def attribute_override_spec(cli: str, attr: str) -> str:
    """Intended meaning used as the comparison point: the attribute overrides the flag."""
    return {"on": "xray-always", "off": "xray-never"}.get(
        attr, {"always": "xray-always", "never": "xray-never", "threshold": ""}[cli])


def build_wrapper_harness(ctx: Ctx):
    """Returns (callable or None, availability record)."""
    cc = shutil.which("cc") or shutil.which("gcc")
    drivers = glob.glob(os.path.join(ctx.sysroot, "lib", "librustc_driver-*.so"))
    if not cc or len(drivers) != 1:
        return None, dict(available=False, reason="no C compiler or no unique librustc_driver")
    driver = drivers[0]
    nm = run([ctx.tool("llvm-nm"), driver], timeout=600).stdout
    offset = None
    for line in nm.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[2] == "LLVMRustAddFunctionAttributes":
            offset, kind = parts[0], parts[1]
            break
    if offset is None:
        return None, dict(available=False,
                          reason="LLVMRustAddFunctionAttributes not in the ELF symbol table")
    src = os.path.join(ctx.work, "add_fn_attrs_harness.c")
    exe = os.path.join(ctx.work, "add_fn_attrs_harness")
    open(src, "w").write(ADD_FN_ATTRS_HARNESS_C)
    libdir = os.path.join(ctx.sysroot, "lib")
    proc = run([cc, "-O1", "-o", exe, src, "-Wl,--no-as-needed", f"-L{libdir}",
                f"-l:{os.path.basename(driver)}", "-ldl", f"-Wl,-rpath,{libdir}"])
    if proc.returncode != 0:
        return None, dict(available=False, reason="harness link failed: "
                          + ctx.scrub(first_error(proc.stderr)))

    def call(values):
        p = run([exe, driver, offset, *values], timeout=120)
        if p.returncode != 0:
            return dict(rc=p.returncode, error=ctx.scrub(p.stderr.strip())[:200])
        m = re.search(r"^SURVIVOR=(.*)$", p.stdout, re.M)
        return dict(rc=0, survivor=m.group(1) if m else None)

    return call, dict(available=True, symbol="LLVMRustAddFunctionAttributes",
                      symbol_type=kind, located_with="llvm-nm on the sysroot's librustc_driver")


def llvm_replay(ctx: Ctx, attr_text: str, tag: str) -> dict:
    """Assemble + disassemble + compile one function whose attribute group contains
    `attr_text` verbatim, and read the result back from the LLVM tools."""
    ll = os.path.join(ctx.work, f"replay_{tag}.ll")
    bc = os.path.join(ctx.work, f"replay_{tag}.bc")
    obj = os.path.join(ctx.work, f"replay_{tag}.o")
    open(ll, "w").write(REPLAY_LL_TEMPLATE.replace("{PUSHES}", attr_text))
    res = dict(attribute_group_text_written=attr_text)
    p = run([ctx.tool("llvm-as"), ll, "-o", bc])
    res["llvm_as_rc"] = p.returncode
    if p.returncode != 0:
        res["llvm_as_error"] = ctx.scrub(first_error(p.stderr))
        return res
    dis = run([ctx.tool("llvm-dis"), bc, "-o", "-"]).stdout
    m = re.search(r"^attributes #0 = \{(.*)\}\s*$", dis, re.M)
    surviving = INTERESTING_ATTR.findall(m.group(1)) if m else []
    res["attributes_after_llvm_as_llvm_dis"] = [
        f'"{k}"="{v}"' if v else f'"{k}"' for k, v in surviving]
    p = run([ctx.tool("llc"), "-O2", "-filetype=obj", "-function-sections", bc, "-o", obj])
    res["llc_rc"] = p.returncode
    if p.returncode == 0:
        f = object_function_facts(ctx, obj, ["replay_target"])["replay_target"]
        res.update(entry_sleds=f["entry_sleds"], exit_sleds=f["exit_sleds"],
                   first_instructions=f["first_instructions"],
                   last_instructions=f["last_instructions"],
                   xray_instr_map_pc64_relocations=f["xray_instr_map_pc64_relocations"],
                   mcount_or_fentry_call_relocations=f["mcount_or_fentry_call_relocations"],
                   call_relocation_targets=f["call_relocation_targets"])
    else:
        res["llc_error"] = ctx.scrub(first_error(p.stderr))
    for path in (ll, bc, obj):
        if os.path.exists(path):
            os.remove(path)
    return res


def part_a3(ctx: Ctx, a1: dict) -> dict:
    wrapper, wrapper_info = build_wrapper_harness(ctx)
    out = dict(
        derived_from_source=("push sequences are computed by Python transliterations of the "
                             "upstream function quoted in REPORT.md; every other field is "
                             "tool output"),
        tools=dict(
            llc=run([ctx.tool("llc"), "--version"]).stdout.strip().splitlines()[1].strip(),
            direct_wrapper_call=wrapper_info),
        xray_cells={}, mcount_cells={})

    for variant, fn in PUSH_VARIANTS:
        cells = {}
        for cli in ("threshold", "always", "never"):
            for attr in ("none", "on", "off"):
                pushes = fn(cli, attr)
                text = " ".join(f'"function-instrument"="{v}"' for v in pushes)
                text += ' "xray-instruction-threshold"="200"'
                cell = dict(pushes_in_order=pushes,
                            llvm_tools=llvm_replay(ctx, text, f"{variant}_{cli}_{attr}"))
                if wrapper is not None:
                    cell["direct_wrapper_call"] = wrapper(pushes)
                survivors = [a for a in cell["llvm_tools"].get(
                    "attributes_after_llvm_as_llvm_dis", []) if "function-instrument" in a]
                survivor = survivors[0].split("=")[1].strip('"') if survivors else ""
                spec = attribute_override_spec(cli, attr)
                cell["surviving_function_instrument"] = survivor
                cell["attribute_override_spec"] = spec
                cell["agrees_with_attribute_override_spec"] = survivor == spec
                if wrapper is not None and cell["direct_wrapper_call"].get("rc") == 0:
                    cell["direct_wrapper_call_agrees_with_llvm_as"] = (
                        cell["direct_wrapper_call"]["survivor"] == survivor)
                cells[f"cli={cli},attr={attr}"] = cell
        out["xray_cells"][variant] = dict(
            cells=cells,
            disagreeing_cells=[k for k, c in cells.items()
                               if not c["agrees_with_attribute_override_spec"]])

    # mcount / fentry: the attribute is either pushed once or not at all.
    for kind, attr_text in (("mcount", '"instrument-function-entry-inlined"="mcount"'),
                            ("fentry", '"fentry-call"="true"')):
        for attr in ("none", "on", "off"):
            instrument_entry = attr != "off"  # `Some(On) | None => true, Some(Off) => false`
            text = attr_text if instrument_entry else ""
            out["mcount_cells"][f"mode={kind},attr={attr}"] = dict(
                attribute_pushed=instrument_entry,
                llvm_tools=llvm_replay(ctx, text, f"{kind}_{attr}"))

    # Cross-check the replay against real rustc where real rustc can express the cell:
    # no per-function attribute, the three command-line states.
    cross = {}
    for cli, cfg in (("threshold", "xray_default"), ("always", "xray_always"),
                     ("never", "xray_never")):
        real = a1.get(cfg, {}).get("functions", {}).get("fn_default")
        cell = out["xray_cells"]["independent_booleans_never_pushed_first"]["cells"][
            f"cli={cli},attr=none"]
        if real is None:
            cross[cli] = dict(compared=False)
            continue
        real_attr = [a for a in real["llvm_ir_instrument_attributes"]
                     if "function-instrument" in a]
        real_value = real_attr[0].split("=")[1].strip('"') if real_attr else ""
        cross[cli] = dict(
            compared=True,
            real_rustc_fn_default_function_instrument=real_value,
            replay_function_instrument=cell["surviving_function_instrument"],
            same_attribute=real_value == cell["surviving_function_instrument"],
            real_rustc_fn_default_entry_sleds=real["entry_sleds"],
            replay_entry_sleds=cell["llvm_tools"].get("entry_sleds"),
            same_sled_presence=(real["entry_sleds"] > 0)
            == (cell["llvm_tools"].get("entry_sleds", 0) > 0))
    out["cross_check_against_real_rustc_without_attribute"] = cross
    return out


# ----------------------------------------------------------------------------
# Part B: coverage
# ----------------------------------------------------------------------------


def locate(source_lines, anchor: str, text: str):
    """1-based (line, col_start, col_end_exclusive) of `text` on the first line at or
    after the line containing `anchor`."""
    start = next(i for i, line in enumerate(source_lines) if anchor in line)
    for i in range(start, len(source_lines)):
        col = source_lines[i].find(text)
        if col >= 0:
            return i + 1, col + 1, col + 1 + len(text)
    raise AssertionError((anchor, text))


def short_fn_name(mangled: str):
    for name in COVERAGE_FUNCTIONS + ["excluded_inline_callee"]:
        if mangled.endswith(f"{len(name)}{name}"):
            return name
    return None


def coverage_run(ctx: Ctx, level: str, opt: str, source_lines) -> dict:
    tag = f"{level}_O{opt}"
    exe, ll = f"cov_{tag}", f"cov_{tag}.ll"
    cmd = [ctx.rustc, "--edition", "2021", "--target", TARGET, "-C", f"opt-level={opt}",
           "-C", "codegen-units=1", "-C", "symbol-mangling-version=v0",
           "-C", "instrument-coverage", "-Z", f"coverage-options={level}",
           f"--emit=link={exe},llvm-ir={ll}", "coverage_modes.rs"]
    p = run(cmd, cwd=ctx.work)
    res = dict(rustc_rc=p.returncode)
    if p.returncode != 0:
        res["first_error"] = ctx.scrub(first_error(p.stderr))
        return res
    raw, prof = os.path.join(ctx.work, f"{tag}.profraw"), os.path.join(ctx.work, f"{tag}.profdata")
    env = dict(os.environ, LLVM_PROFILE_FILE=raw)
    res["program_rc"] = run([os.path.join(ctx.work, exe)], cwd=ctx.work, env=env).returncode
    res["llvm_profdata_rc"] = run([ctx.tool("llvm-profdata"), "merge", "-sparse", raw,
                                   "-o", prof]).returncode
    exp = run([ctx.tool("llvm-cov"), "export", "--format=text", f"--instr-profile={prof}",
               os.path.join(ctx.work, exe)])
    res["llvm_cov_export_rc"] = exp.returncode
    data = json.loads(exp.stdout)["data"][0]
    res["totals"] = {k: {kk: vv for kk, vv in v.items()} for k, v in data["totals"].items()}

    functions, by_name = {}, {}
    for f in data["functions"]:
        name = short_fn_name(f["name"])
        if name is None:
            continue
        code = [r for r in f["regions"] if r[7] == 0]
        branches = [dict(span=b[0:4], true_count=b[4], false_count=b[5], kind=b[-1])
                    for b in f["branches"]]
        functions[name] = dict(
            execution_count=f["count"],
            code_regions=len(code), code_regions_executed=sum(1 for r in code if r[4] > 0),
            source_lines_spanned=[min(r[0] for r in f["regions"]), max(r[2] for r in f["regions"])],
            branch_regions=branches,
            mcdc_records=len(f.get("mcdc_records", [])))
        by_name[name] = branches
    res["functions"] = functions
    res["function_record_names"] = sorted(functions)
    res["excluded_inline_callee_has_function_record"] = "excluded_inline_callee" in functions

    # `#[coverage(off)] #[inline(always)]` callee: no counters, no regions on its lines.
    ll_text = open(os.path.join(ctx.work, ll)).read()
    callee_line = next(i for i, l in enumerate(source_lines)
                       if "fn excluded_inline_callee" in l) + 1
    callee_lines = set(range(callee_line, callee_line + 3))
    res["excluded_inline_callee"] = dict(
        llvm_ir_defines_it=bool(re.search(r"^define [^\n]*excluded_inline_callee", ll_text, re.M)),
        llvm_ir_calls_it=bool(re.search(r"\bcall [^\n]*excluded_inline_callee", ll_text)),
        profile_counter_globals_naming_it=len(
            re.findall(r"^@__profc_\S*excluded_inline_callee", ll_text, re.M)),
        profile_counter_globals_total=len(re.findall(r"^@__profc_\S+ =", ll_text, re.M)),
        regions_of_any_function_on_its_lines=sum(
            1 for f in data["functions"] for r in f["regions"]
            if set(range(r[0], r[2] + 1)) & callee_lines))

    # Branch sites against the independent oracle.
    sites = []
    for s in BRANCH_SITES:
        line, c1, c2 = locate(source_lines, s["anchor"], s["text"])
        reached = [args for args in s["inputs"] if s["reached"](*args)]
        oracle_true = sum(1 for args in reached if s["truth"](*args))
        oracle_false = len(reached) - oracle_true
        found = [b for b in by_name.get(s["function"], []) if b["span"] == [line, c1, line, c2]]
        expected_present = LEVEL_RANK[level] >= LEVEL_RANK[s["level"]]
        rec = dict(site=s["site"], function=s["function"], span=[line, c1, line, c2],
                   lowest_level_per_source=s["level"],
                   expected_present_per_source=expected_present,
                   present=bool(found),
                   oracle_true_count=oracle_true, oracle_false_count=oracle_false)
        if found:
            rec.update(true_count=found[0]["true_count"], false_count=found[0]["false_count"],
                       counts_match_oracle=(found[0]["true_count"] == oracle_true
                                            and found[0]["false_count"] == oracle_false),
                       counts_match_swapped_oracle=(found[0]["true_count"] == oracle_false
                                                    and found[0]["false_count"] == oracle_true))
        sites.append(rec)
    res["branch_sites"] = sites
    res["all_sites_presence_as_source_predicts"] = all(
        s["present"] == s["expected_present_per_source"] for s in sites)
    res["all_present_sites_match_oracle"] = all(
        s.get("counts_match_oracle", True) for s in sites)

    by_site = {s["site"]: s for s in sites}
    flows = []
    for rhs, lhs, outcome in FLOW_PAIRS:
        r, l = by_site[rhs], by_site[lhs]
        if r["present"] and l["present"]:
            feeding = l["true_count"] if outcome == "true" else l["false_count"]
            flows.append(dict(rhs=rhs, lhs=lhs, lhs_outcome_feeding_rhs=outcome,
                              lhs_outcome_count=feeding,
                              rhs_true_plus_false=r["true_count"] + r["false_count"],
                              conserved=feeding == r["true_count"] + r["false_count"]))
    res["flow_conservation"] = flows

    for path in (exe, ll, f"{tag}.profraw", f"{tag}.profdata"):
        full = os.path.join(ctx.work, path)
        if os.path.exists(full):
            os.remove(full)
    return res


def built_mir_shape(ctx: Ctx, level: str) -> dict:
    out = {}
    for fn in ("standalone_conditions", "negated_conditions"):
        d = os.path.join(ctx.work, f"mir_{level}_{fn}")
        os.makedirs(d, exist_ok=True)
        p = run([ctx.rustc, "--edition", "2021", "--target", TARGET, "-C", "opt-level=0",
                 "-C", "instrument-coverage", "-Z", f"coverage-options={level}",
                 "-Z", f"dump-mir={fn}", "-Z", f"dump-mir-dir={d}",
                 "--emit=metadata", "-o", os.path.join(d, "probe.rmeta"), "coverage_modes.rs"],
                cwd=ctx.work)
        files = glob.glob(os.path.join(d, f"*.{fn}.*built.after.mir"))
        if p.returncode != 0 or len(files) != 1:
            out[fn] = dict(available=False, rustc_rc=p.returncode, built_mir_files=len(files))
        else:
            text = open(files[0]).read()
            out[fn] = dict(
                available=True,
                basic_blocks=len(re.findall(r"^    bb\d+(?: \(cleanup\))?: \{", text, re.M)),
                switch_int_terminators=len(re.findall(r"\bswitchInt\(", text)),
                switch_int_on_copy_operand=len(re.findall(r"\bswitchInt\(copy ", text)),
                coverage_block_markers=len(re.findall(r"Coverage::BlockMarker\(", text)),
                coverage_statements=len(re.findall(r"Coverage::", text)))
        shutil.rmtree(d, ignore_errors=True)
    return out


def part_b(ctx: Ctx) -> dict:
    open(os.path.join(ctx.work, "coverage_modes.rs"), "w").write(COVERAGE_RS)
    source_lines = COVERAGE_RS.splitlines()
    out = dict(inputs=dict(simple=SIMPLE_INPUTS, standalone=STANDALONE_INPUTS,
                           negated=NEGATED_INPUTS), runs={}, built_mir={})
    for level in ("block", "branch", "condition"):
        for opt in ("0", "2"):
            out["runs"][f"{level}_opt{opt}"] = coverage_run(ctx, level, opt, source_lines)
        out["built_mir"][level] = built_mir_shape(ctx, level)
    p = run([ctx.rustc, "--edition", "2021", "--target", TARGET, "-C", "instrument-coverage",
             "-Z", "coverage-options=mcdc", "--emit=metadata", "-o",
             os.path.join(ctx.work, "mcdc.rmeta"), "coverage_modes.rs"], cwd=ctx.work)
    out["coverage_options_mcdc"] = dict(rc=p.returncode,
                                        first_error=ctx.scrub(first_error(p.stderr)))
    return out


# ----------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--out", default="-")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="xray_cov_probe_") as work:
        ctx = Ctx(args.rustc, work)
        version = run([args.rustc, "-vV"]).stdout.strip()
        result = dict(
            rustc_version_verbose=version,
            target=TARGET,
            llvm_tool_versions={
                t: re.search(r"LLVM version \S+", run([ctx.tool(t), "--version"]).stdout).group(0)
                for t in ("llvm-objdump", "llvm-cov", "llvm-profdata", "llc", "llvm-as")})

        open(os.path.join(work, "gate.rs"), "w").write(FEATURE_GATE_RS)
        gate = run([args.rustc, "--edition", "2021", "--target", TARGET, "--emit=metadata",
                    "-o", os.path.join(work, "gate.rmeta"), "gate.rs"], cwd=work)
        supported = gate.returncode == 0
        result["instrument_fn_attribute"] = dict(
            accepted_by_this_rustc=supported,
            first_error=None if supported else ctx.scrub(first_error(gate.stderr)))

        open(os.path.join(work, "xray_cli_only.rs"), "w").write(XRAY_CLI_ONLY_RS)
        a1 = compile_instrument_matrix(ctx, "xray_cli_only.rs", XRAY_CLI_ONLY_FUNCTIONS)
        result["part_a1_real_rustc_command_line_matrix_no_attribute"] = a1

        if supported:
            open(os.path.join(work, "xray_instrument_fn.rs"), "w").write(XRAY_INSTRUMENT_FN_RS)
            result["part_a2_real_rustc_instrument_fn_matrix"] = dict(
                executed=True,
                configs=compile_instrument_matrix(ctx, "xray_instrument_fn.rs",
                                                  XRAY_INSTRUMENT_FN_FUNCTIONS))
        else:
            result["part_a2_real_rustc_instrument_fn_matrix"] = dict(
                executed=False,
                reason="this rustc rejects #![feature(instrument_fn)]; see instrument_fn_attribute")

        result["part_a3_llvm_level_replay"] = part_a3(ctx, a1)
        result["part_b_coverage_levels"] = part_b(ctx)

    text = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if args.out == "-":
        sys.stdout.write(text)
    else:
        with open(args.out, "w") as fh:
            fh.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
