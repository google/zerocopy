#!/usr/bin/env python3
"""Empirical probe: Box-deref elaboration, critical call-edge splitting, unneeded-drop removal,
return duplication, and constructor MIR, observed on one concrete nightly `rustc` (+ Miri).

Everything this script reports is read from the output of the toolchain it is pointed at.
It makes no claim about any other toolchain. Standard library only (Python 3.10+).

Usage:
    python3 probe_boxraw_call_guards_and_pipeline_closure.py \
        --rustc /path/to/nightly/bin/rustc \
        [--miri /path/to/nightly/bin/miri --miri-sysroot /path/to/miri-sysroot] \
        [--out results.json] [--keep-workdir DIR]

`--miri-sysroot` is the directory printed by `cargo miri setup --print-sysroot`. Without Miri the
Miri sections are recorded as skipped (not as passed).

Exit status: 0 if every check that was *run* held, 1 if any check that was run failed,
2 on usage or toolchain errors. Skipped checks are reported as skipped and never count as passes.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

PROBE_RS = r'''
#![cfg_attr(not(no_asm_gate), feature(asm_goto_with_outputs))]
#![allow(unused, dead_code, stable_features)]
#![crate_type = "lib"]
use std::arch::asm;

// 1. ElaborateBoxDerefs: a read and a write through a Box.
pub fn read_box_u64(b: &Box<u64>) -> u64 { **b }
pub fn write_box_u64(b: &mut Box<u64>, v: u64) { **b = v; }

// 2. RemoveUnneededDrops after Inline: `drop_val::<u32>` has a Drop of a type without drop glue.
#[inline(always)]
pub fn drop_val<T>(x: T) {}
pub fn drop_caller_u32(x: u32) -> u32 { drop_val(x); x.wrapping_add(1) }
pub fn drop_caller_string(x: String) -> u32 { drop_val(x); 1 }

// 3. AddCallGuards::CriticalCallEdges.
pub struct Guard(pub u32);
impl Drop for Guard { #[inline(never)] fn drop(&mut self) { std::hint::black_box(self.0); } }
#[inline(never)]
pub fn opaque(x: u32) -> u32 { std::hint::black_box(x) }
// The live `Guard` gives the call an unwind edge; the call's return target is the join block.
pub fn crit_call(c: bool) -> u32 {
    let _g = Guard(1);
    let y = if c { opaque(1) } else { 7 };
    y
}
// Same shape without anything to drop on unwind: the call has no unwind edge.
pub fn noncrit_call_no_unwind_edge(c: bool) -> u32 {
    let y = if c { opaque(1) } else { 7 };
    y
}
// Inline asm with an output operand and a label whose block joins the fallthrough path.
#[cfg(target_arch = "x86_64")]
pub fn asm_goto_out(c: u64) -> u64 {
    let mut out: u64;
    unsafe {
        asm!(
            "mov {o}, {c}",
            "test {c}, {c}",
            "jnz {l}",
            c = in(reg) c,
            o = out(reg) out,
            l = label {},
            options(nostack),
        );
    }
    out
}

// 4. MultipleReturnTerminators.
pub fn multi_return_branch(x: u32) -> u32 { match x { 0 => 10, 1 => 20, _ => 30 } }

// 5. Tuple-struct / enum-variant constructors used as functions.
pub struct Pair(pub u32, pub u32);
pub enum E { V(u8), W }
pub fn reify_ctors(xs: &[u8]) -> (Pair, usize) {
    let f: fn(u32, u32) -> Pair = Pair;
    let n = xs.iter().copied().map(E::V).filter(|e| matches!(e, E::V(v) if *v > 1)).count();
    (f(3, 4), n)
}
'''

MIRI_MAIN_RS = r'''
#![allow(unused)]
pub struct Pair(pub u32, pub u32);
#[derive(Debug, PartialEq)]
pub enum E { V(u8), W }
struct Loud<'a>(&'a std::cell::Cell<u32>);
impl Drop for Loud<'_> { fn drop(&mut self) { self.0.set(self.0.get() + 1); } }
#[inline(always)]
fn drop_val<T>(x: T) {}
fn read_box_u64(b: &Box<u64>) -> u64 { **b }
fn main() {
    // Tuple-struct and enum-variant constructors reified as fn pointers / fn items.
    let f: fn(u32, u32) -> Pair = Pair;
    let p = f(3, 4);
    assert_eq!((p.0, p.1), (3, 4));
    let g: fn(u8) -> E = E::V;
    assert_eq!(g(9), E::V(9));
    let v: Vec<E> = [1u8, 2, 3].iter().copied().map(E::V).collect();
    assert_eq!(v, vec![E::V(1), E::V(2), E::V(3)]);
    let some: Vec<Option<u8>> = [5u8].iter().copied().map(Some).collect();
    assert_eq!(some, vec![Some(5)]);
    // Box deref through the elaborated raw-pointer path.
    let b = Box::new(0xDEAD_BEEF_u64);
    assert_eq!(read_box_u64(&b), 0xDEAD_BEEF_u64);
    // Dropping a type without drop glue does nothing; dropping one with glue runs it once.
    let c = std::cell::Cell::new(0u32);
    drop_val(7u32);
    assert_eq!(c.get(), 0);
    drop_val(Loud(&c));
    assert_eq!(c.get(), 1);
    println!("miri_main ok");
}
'''

# A dangling Box used ONLY in a place expression (no load through it).
DANGLING_PLACE_RS = r'''
use std::alloc::{dealloc, Layout};
fn main() {
    let mut b: Box<u8> = Box::new(5u8);
    let p: *mut u8 = &raw mut *b;
    unsafe { dealloc(p, Layout::new::<u8>()); }
    let q: *const u8 = &raw const *b; // place expression on a dangling Box; nothing is read
    std::hint::black_box(q);
    std::process::exit(0); // never drop or move `b` again
}
'''

# Control for the above: the same program but with a real load through the dangling Box.
DANGLING_LOAD_RS = r'''
use std::alloc::{dealloc, Layout};
fn main() {
    let mut b: Box<u8> = Box::new(5u8);
    let p: *mut u8 = &raw mut *b;
    unsafe { dealloc(p, Layout::new::<u8>()); }
    let v: u8 = *b; // load through a dangling Box
    std::hint::black_box(v);
    std::process::exit(0);
}
'''

DUMP_RE = re.compile(r"^(?P<crate>[^.]+)\.(?P<fn>.+)\.(?P<a>\d+)-(?P<b>\d+)-(?P<n>\d+)\."
                     r"(?P<pass>[A-Za-z0-9_-]+)\.(?P<when>before|after)\.mir$")
BB_RE = re.compile(r"^\s+bb\d+( \(cleanup\))?: \{", re.M)
RET_RE = re.compile(r"^\s+return;", re.M)
DROP_RE = re.compile(r"^\s+drop\(", re.M)


def run(argv, cwd, timeout=600, env=None):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)
    return p.returncode, p.stdout, p.stderr


def strip_comments(mir: str) -> str:
    """Drop the `// MIR for ...` header and blank lines so before/after bodies can be compared."""
    return "\n".join(l for l in mir.splitlines() if l.strip() and not l.lstrip().startswith("//"))


def body_lines(mir: str):
    """Statement/terminator lines only (no declarations, scopes, storage markers)."""
    out = []
    for l in strip_comments(mir).splitlines():
        s = l.strip()
        if s.startswith(("debug ", "let ", "scope ", "StorageLive", "StorageDead")) or s == "}":
            continue
        out.append(l.rstrip())
    return out


class Dumps:
    """Index of one `-Zdump-mir=all` directory."""

    def __init__(self, directory: str):
        self.dir = directory
        self.by_fn: dict[str, list[dict]] = {}
        for name in sorted(os.listdir(directory)):
            m = DUMP_RE.match(name)
            if not m:
                continue
            d = m.groupdict()
            d["key"] = (int(d["a"]), int(d["b"]), int(d["n"]))
            d["file"] = name
            self.by_fn.setdefault(d["fn"], []).append(d)
        for v in self.by_fn.values():
            v.sort(key=lambda d: (d["key"], d["when"] == "after"))

    def read(self, entry) -> str:
        with open(os.path.join(self.dir, entry["file"]), encoding="utf-8") as f:
            return f.read()

    def passes(self, fn: str, pass_name: str):
        """[(tag, before_text, after_text)] for each run of `pass_name` on `fn`, in order."""
        runs: dict[tuple, dict] = {}
        for d in self.by_fn.get(fn, []):
            if d["pass"] == pass_name:
                runs.setdefault(d["key"], {})[d["when"]] = self.read(d)
        return [("%d-%d-%03d.%s" % (*k, pass_name), v.get("before"), v.get("after"))
                for k, v in sorted(runs.items())]

    def single(self, fn: str, pass_name: str, when: str):
        for d in self.by_fn.get(fn, []):
            if d["pass"] == pass_name and d["when"] == when:
                return self.read(d)
        return None

    def sequence(self, fn: str):
        """Ordered, de-duplicated list of dump tags = passes that produced a dump for `fn`."""
        seen, out = set(), []
        for d in self.by_fn.get(fn, []):
            tag = "%d-%d-%03d.%s" % (*d["key"], d["pass"])
            if tag not in seen:
                seen.add(tag)
                out.append(tag)
        return out


def block_transition(runs):
    return [{"dump": tag,
             "blocks_before": None if b is None else len(BB_RE.findall(b)),
             "blocks_after": None if a is None else len(BB_RE.findall(a))} for tag, b, a in runs]


def classify_box_lowering(after_mir: str | None):
    if after_mir is None:
        return {"era": "no-dump", "cast_lines": []}
    lines = [l.strip() for l in after_mir.splitlines()
             if re.search(r"\((BoxDerefTransmute|Transmute)\);", l) and " as *" in l]
    era = "unrecognized"
    if lines:
        if all("(BoxDerefTransmute)" in l and "BoxRaw<" in l for l in lines):
            era = "BoxDerefTransmute-of-BoxRaw"
        elif all("(BoxDerefTransmute)" in l for l in lines):
            era = "BoxDerefTransmute-of-other"
        elif all("(Transmute)" in l and "Unique<" in l and "NonNull<" in l for l in lines):
            era = "Transmute-of-Unique-NonNull"
    return {"era": era, "cast_lines": lines}


def compile_probe(rustc, work, tag, flags):
    out_dir = os.path.join(work, tag)
    os.makedirs(out_dir, exist_ok=True)
    base = [rustc, "../probe.rs", "--edition", "2024", "-C", "panic=unwind", *flags,
            "-Zdump-mir=all", "-Zdump-mir-dir=mir", "--emit=mir=probe.mir"]
    rc, so, se = run(base, out_dir)
    gate = "feature(asm_goto_with_outputs)"
    if rc != 0:
        # The feature gate may have been stabilized-and-removed on a newer toolchain.
        rc2, so2, se2 = run(base + ["--cfg", "no_asm_gate"], out_dir)
        if rc2 == 0:
            rc, so, se, gate = rc2, so2, se2, "none (retried without the feature gate)"
    cmd = ["<rustc>"] + base[1:]
    return out_dir, rc, se, cmd, gate


def analyse_level(out_dir):
    d = Dumps(os.path.join(out_dir, "mir"))
    res = {}
    # --- 1. Box deref elaboration
    res["elaborate_box_derefs"] = {}
    for fn in ("read_box_u64", "write_box_u64"):
        before = d.single(fn, "ElaborateBoxDerefs", "before")
        after = d.single(fn, "ElaborateBoxDerefs", "after")
        res["elaborate_box_derefs"][fn] = {
            "before_body": None if before is None else body_lines(before),
            "after_body": None if after is None else body_lines(after),
            **classify_box_lowering(after),
        }
    # --- 3. critical call edges
    cce = {}
    for fn in ("crit_call", "noncrit_call_no_unwind_edge", "asm_goto_out"):
        if fn not in d.by_fn:
            cce[fn] = {"present": False}
            continue
        acg = d.passes(fn, "AddCallGuards")
        pre = d.passes(fn, "SimplifyCfg-pre-optimizations")
        entry = {"present": True,
                 "add_call_guards_runs": block_transition(acg),
                 "simplify_cfg_pre_optimizations": block_transition(pre)}
        if acg and acg[0][1] and acg[0][2]:
            b, a = body_lines(acg[0][1]), body_lines(acg[0][2])
            entry["first_run_before_body"] = b
            entry["first_run_lines_only_after"] = [l for l in a if l not in b]
        if acg and acg[-1][1] and acg[-1][2]:
            entry["last_run_before_body"] = body_lines(acg[-1][1])
            entry["last_run_after_body"] = body_lines(acg[-1][2])
        cce[fn] = entry
    res["critical_call_edges"] = cce
    # --- 2. RemoveUnneededDrops
    rud = {}
    for fn in ("drop_caller_u32", "drop_caller_string"):
        runs = d.passes(fn, "RemoveUnneededDrops")
        if not runs or runs[0][1] is None or runs[0][2] is None:
            rud[fn] = {"ran": False}
            continue
        _, b, a = runs[0]
        rud[fn] = {"ran": True, "dump": runs[0][0],
                   "drop_terminators_before": len(DROP_RE.findall(b)),
                   "drop_terminators_after": len(DROP_RE.findall(a)),
                   "blocks_before": len(BB_RE.findall(b)), "blocks_after": len(BB_RE.findall(a)),
                   "before_body": body_lines(b), "after_body": body_lines(a)}
    res["remove_unneeded_drops"] = rud
    # --- 4. MultipleReturnTerminators
    fn = "multi_return_branch"
    final = d.single(fn, "runtime-optimized", "after")
    res["multiple_return_terminators"] = {
        "pass_dump_files": sum(1 for x in d.by_fn.get(fn, [])
                               if x["pass"] == "MultipleReturnTerminators"),
        "return_terminators_in_optimized_mir": None if final is None else len(RET_RE.findall(final)),
        "optimized_body": None if final is None else body_lines(final),
    }
    # --- 5. constructors
    ctors = {}
    for name, entries in d.by_fn.items():
        if "{constructor#" in name:
            ctors[name] = {"dump_files": len(entries),
                           "dumps": sorted({"%d-%d-%03d.%s" % (*e["key"], e["pass"])
                                            for e in entries})}
    res["constructors"] = {
        "dump_files_per_constructor": ctors,
        "dump_files_for_ordinary_fn_reify_ctors": len(d.by_fn.get("reify_ctors", [])),
    }
    emitted = os.path.join(out_dir, "probe.mir")
    if os.path.exists(emitted):
        with open(emitted, encoding="utf-8") as f:
            text = f.read()
        blocks = re.split(r"\n(?=// MIR FOR CTFE\n|fn |// MIR )", text)
        res["constructors"]["emitted_mir_for_Pair_ctor"] = [
            b.strip().splitlines() for b in blocks if re.search(r"^fn Pair\(", b, re.M)]
    # --- pass sequence that produced dumps, for one ordinary function
    res["dump_sequence_crit_call"] = d.sequence("crit_call")
    return res


def miri_run(miri, sysroot, work, filename, extra=()):
    env = dict(os.environ)
    env["MIRI_SYSROOT"] = sysroot
    rc, so, se = run([miri, filename, "--edition", "2024", "--sysroot", sysroot, *extra], work,
                     env=env)
    first_err = next((l.strip() for l in se.splitlines() if l.startswith("error")), None)
    return {"argv": ["<miri>", filename, "--edition", "2024", "--sysroot", "<miri-sysroot>",
                     *extra],
            "exit_code": rc, "stdout_last_line": (so.strip().splitlines() or [None])[-1],
            "first_error_line": first_err}


def scrub(obj, needles):
    """Replace every absolute path fragment in `needles` and fail closed if any path survives."""
    text = json.dumps(obj, indent=1, sort_keys=True)
    for needle, repl in needles:
        if needle:
            text = text.replace(needle, repl)
    # Any absolute POSIX path (a slash that starts a token, then at least one directory segment).
    leak = re.search(r"""(?:^|[\s"'=:,\[(])/(?:[A-Za-z0-9._+-]+/)+[A-Za-z0-9._+-]*""", text, re.M)
    if leak:
        raise SystemExit(f"refusing to write output: absolute path survived scrubbing: "
                         f"{leak.group(0)[:60]!r}")
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--miri", default=None)
    ap.add_argument("--miri-sysroot", default=os.environ.get("MIRI_SYSROOT"))
    ap.add_argument("--out", default=None, help="write JSON here (default: stdout)")
    ap.add_argument("--keep-workdir", default=None, help="use and keep this directory")
    args = ap.parse_args()

    rc, vv, se = run([args.rustc, "-vV"], os.getcwd())
    if rc != 0:
        print(f"cannot run {args.rustc} -vV: {se}", file=sys.stderr)
        return 2
    toolchain = dict(l.split(": ", 1) for l in vv.strip().splitlines()[1:] if ": " in l)
    toolchain["version_line"] = vv.strip().splitlines()[0]
    if "nightly" not in toolchain["version_line"] and "dev" not in toolchain["version_line"]:
        print("this probe needs a nightly toolchain (-Z flags)", file=sys.stderr)
        return 2

    def body(work):
        for name, text in (("probe.rs", PROBE_RS), ("miri_main.rs", MIRI_MAIN_RS),
                           ("dangling_box_place.rs", DANGLING_PLACE_RS),
                           ("dangling_box_load.rs", DANGLING_LOAD_RS)):
            with open(os.path.join(work, name), "w", encoding="utf-8") as f:
                f.write(text.lstrip("\n"))
        result = {"schema": "probe-boxraw-call-guards/1", "toolchain": toolchain, "levels": {},
                  "commands": {}}
        for tag, lvl in (("mir_opt_level_2", 2), ("mir_opt_level_4", 4)):
            out_dir, crc, cse, cmd, gate = compile_probe(
                args.rustc, work, tag, ["-C", "opt-level=3", f"-Zmir-opt-level={lvl}"])
            result["commands"][tag] = {"argv": cmd, "cwd": f"<workdir>/{tag}", "exit_code": crc,
                                       "asm_feature_gate": gate}
            if crc != 0:
                result["commands"][tag]["stderr_tail"] = cse.strip().splitlines()[-12:]
                result["levels"][tag] = {"compiled": False}
                continue
            result["levels"][tag] = {"compiled": True, **analyse_level(out_dir)}

        # --- which passes produce dumps under other flag sets (sequence only)
        result["dump_sequences_crit_call"] = {}
        for tag in ("mir_opt_level_2", "mir_opt_level_4"):
            if result["levels"][tag].get("compiled"):
                result["dump_sequences_crit_call"][tag] = result["levels"][tag].pop(
                    "dump_sequence_crit_call")
        for tag, flags in (
                # the MIR-affecting flags Miri passes by default
                ("miri_like_flags", ["-Zmir-opt-level=0", "-Zmir-preserve-ub",
                                     "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums"]),
                # plain unoptimized build: no -C opt-level, no -Zmir-opt-level
                ("unoptimized_default", [])):
            out_dir, crc, cse, cmd, gate = compile_probe(args.rustc, work, tag, flags)
            result["commands"][tag] = {"argv": cmd, "cwd": f"<workdir>/{tag}", "exit_code": crc,
                                       "asm_feature_gate": gate}
            if crc == 0:
                result["dump_sequences_crit_call"][tag] = Dumps(
                    os.path.join(out_dir, "mir")).sequence("crit_call")
            else:
                result["commands"][tag]["stderr_tail"] = cse.strip().splitlines()[-12:]

        # --- Miri
        miri = args.miri
        if miri is None:
            cand = os.path.join(os.path.dirname(os.path.abspath(args.rustc)), "miri")
            miri = cand if os.path.exists(cand) else None
        if miri is None or not args.miri_sysroot:
            result["miri"] = {"status": "skipped",
                              "reason": "no miri binary and/or no --miri-sysroot given"}
        else:
            mrc, mv, _ = run([miri, "--version"], work)
            result["miri"] = {
                "status": "ran", "miri_version_line": mv.strip().splitlines()[0] if mv else None,
                "constructors_box_and_drops": miri_run(miri, args.miri_sysroot, work,
                                                       "miri_main.rs"),
                "dangling_box_load_control": miri_run(miri, args.miri_sysroot, work,
                                                      "dangling_box_load.rs"),
                "dangling_box_place_only": {
                    "stacked_borrows_default": miri_run(miri, args.miri_sysroot, work,
                                                        "dangling_box_place.rs"),
                    "tree_borrows": miri_run(miri, args.miri_sysroot, work,
                                             "dangling_box_place.rs", ("-Zmiri-tree-borrows",)),
                    "aliasing_model_disabled": miri_run(miri, args.miri_sysroot, work,
                                                   "dangling_box_place.rs",
                                                   ("-Zmiri-disable-stacked-borrows",)),
                },
            }

        # --- checks: each is {"held": bool} or {"skipped": reason}
        checks = {}

        def check(name, fn):
            try:
                checks[name] = {"held": bool(fn())}
            except (KeyError, IndexError, TypeError) as e:
                checks[name] = {"skipped": f"data unavailable ({type(e).__name__}: {e})"}

        l2 = result["levels"].get("mir_opt_level_2", {})
        l4 = result["levels"].get("mir_opt_level_4", {})
        era = l2.get("elaborate_box_derefs", {}).get("read_box_u64", {}).get("era", "no-data")
        result["box_deref_lowering_era"] = era
        check("box_deref_is_lowered_to_a_raw_pointer_cast",
              lambda: era in ("BoxDerefTransmute-of-BoxRaw", "BoxDerefTransmute-of-other",
                              "Transmute-of-Unique-NonNull"))
        cc = lambda: l2["critical_call_edges"]["crit_call"]
        check("unwinding_call_critical_edge_split_by_first_add_call_guards",
              lambda: cc()["add_call_guards_runs"][0]["blocks_after"]
              == cc()["add_call_guards_runs"][0]["blocks_before"] + 1)
        check("simplify_cfg_pre_optimizations_undoes_the_split",
              lambda: cc()["simplify_cfg_pre_optimizations"][0]["blocks_after"]
              == cc()["simplify_cfg_pre_optimizations"][0]["blocks_before"] - 1)
        check("unwinding_call_critical_edge_split_again_by_last_add_call_guards",
              lambda: len(cc()["add_call_guards_runs"]) >= 2
              and cc()["add_call_guards_runs"][-1]["blocks_after"]
              == cc()["add_call_guards_runs"][-1]["blocks_before"] + 1)
        check("call_without_unwind_edge_is_never_split",
              lambda: all(r["blocks_before"] == r["blocks_after"] for r in
                          l2["critical_call_edges"]["noncrit_call_no_unwind_edge"]
                          ["add_call_guards_runs"]))
        asm = lambda: l2["critical_call_edges"]["asm_goto_out"]
        if l2.get("critical_call_edges", {}).get("asm_goto_out", {}).get("present"):
            check("asm_goto_with_output_critical_edge_split_by_first_add_call_guards",
                  lambda: asm()["add_call_guards_runs"][0]["blocks_after"]
                  > asm()["add_call_guards_runs"][0]["blocks_before"])
            check("asm_goto_with_output_critical_edges_split_by_last_add_call_guards",
                  lambda: asm()["add_call_guards_runs"][-1]["blocks_after"]
                  > asm()["add_call_guards_runs"][-1]["blocks_before"])
        else:
            checks["asm_goto_with_output_critical_edge"] = {
                "skipped": "asm probe not compiled on this target (x86_64 only)"}
        check("drop_of_u32_after_inlining_is_removed",
              lambda: l2["remove_unneeded_drops"]["drop_caller_u32"]["drop_terminators_before"] >= 1
              and l2["remove_unneeded_drops"]["drop_caller_u32"]["drop_terminators_after"] == 0)
        check("drop_of_string_is_kept",
              lambda: l2["remove_unneeded_drops"]["drop_caller_string"]["drop_terminators_before"]
              == l2["remove_unneeded_drops"]["drop_caller_string"]["drop_terminators_after"] >= 1)
        check("level_2_keeps_one_return_and_does_not_run_the_pass",
              lambda: l2["multiple_return_terminators"]["pass_dump_files"] == 0
              and l2["multiple_return_terminators"]["return_terminators_in_optimized_mir"] == 1)
        check("level_4_duplicates_the_return_into_each_arm",
              lambda: l4["multiple_return_terminators"]["pass_dump_files"] > 0
              and l4["multiple_return_terminators"]["return_terminators_in_optimized_mir"] == 3)
        check("constructors_have_at_most_one_mir_dump_while_ordinary_fns_have_many",
              lambda: len(l2["constructors"]["dump_files_per_constructor"]) >= 2
              and all(v["dump_files"] <= 1 for v in
                      l2["constructors"]["dump_files_per_constructor"].values())
              and l2["constructors"]["dump_files_for_ordinary_fn_reify_ctors"] > 20)
        seqs = result["dump_sequences_crit_call"]
        names = lambda tag: [t.split(".", 1)[1] for t in seqs[tag]]
        check("miri_like_flags_still_run_add_call_guards_twice_and_remove_unneeded_drops",
              lambda: names("miri_like_flags").count("AddCallGuards") == 2
              and "RemoveUnneededDrops" in names("miri_like_flags")
              and "ElaborateBoxDerefs" in names("miri_like_flags"))
        check("miri_like_flags_do_not_run_inline_gvn_or_multiple_return_terminators",
              lambda: not ({"Inline", "GVN", "MultipleReturnTerminators", "RemovePlaceMention"}
                           & set(names("miri_like_flags"))))
        if result["miri"]["status"] == "ran":
            m = result["miri"]
            check("miri_accepts_constructor_reification_box_deref_and_drops",
                  lambda: m["constructors_box_and_drops"]["exit_code"] == 0
                  and m["constructors_box_and_drops"]["stdout_last_line"] == "miri_main ok")
            check("miri_reports_ub_for_a_load_through_a_dangling_box",
                  lambda: m["dangling_box_load_control"]["exit_code"] != 0
                  and "Undefined Behavior" in (m["dangling_box_load_control"]["first_error_line"]
                                               or ""))
            place_rcs = {k: v["exit_code"] for k, v in m["dangling_box_place_only"].items()}
            result["dangling_box_place_only_summary"] = {
                "exit_codes": place_rcs,
                "ub_reported": {k: rc != 0 for k, rc in place_rcs.items()},
                "note": ("Observation only. Whether UB is reported here depends on how this "
                         "toolchain lowers Box derefs (see box_deref_lowering_era); this script "
                         "does not assert an expected outcome for it."),
            }
        else:
            for name in ("miri_accepts_constructor_reification_box_deref_and_drops",
                         "miri_reports_ub_for_a_load_through_a_dangling_box"):
                checks[name] = {"skipped": result["miri"]["reason"]}
        result["checks"] = checks
        result["summary"] = {
            "held": sorted(k for k, v in checks.items() if v.get("held") is True),
            "failed": sorted(k for k, v in checks.items() if v.get("held") is False),
            "skipped": sorted(k for k, v in checks.items() if "skipped" in v),
        }
        return result

    if args.keep_workdir:
        os.makedirs(args.keep_workdir, exist_ok=True)
        work = os.path.abspath(args.keep_workdir)
        result = body(work)
    else:
        with tempfile.TemporaryDirectory(prefix="probe_boxraw_") as work:
            result = body(work)

    needles = [(work, "<workdir>"), (os.path.dirname(os.path.abspath(args.rustc)), "<toolchain-bin>"),
               (args.miri_sysroot or "", "<miri-sysroot>"), (os.path.expanduser("~"), "<home>")]
    text = scrub(result, needles)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    else:
        print(text)
    s = result["summary"]
    print(f"held={len(s['held'])} failed={len(s['failed'])} skipped={len(s['skipped'])}",
          file=sys.stderr)
    for k in s["failed"]:
        print(f"FAILED: {k}", file=sys.stderr)
    return 1 if s["failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
