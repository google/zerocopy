#!/usr/bin/env python3
"""Probe a real `rustc` (and Miri) for allocator-shim symbols, `Box`/`Vec` allocation
accounting, `Box` MIR lowering, allocation-failure behaviour and allocator-contract UB detection.

Everything is measured from the toolchain given on the command line; nothing is read from a
previous run. The script compiles the specimens under `specimens/`, runs them, and writes

    probe_output/probe_results.json              all measurements and the checks derived from them
    probe_output/global_allocator_expansion.txt  `-Zunpretty=expanded` of a minimal global allocator
    probe_output/mir/<configuration>/<function>.<point>.mir   selected MIR dumps
    probe_output/mir/<configuration>/final.mir                final MIR of the whole specimen

Parts:

  A  runtime accounting  `specimens/alloc_lifecycle.rs` under a recording `#[global_allocator]`
  B  symbols and IR      `nm` on saved codegen objects, LLVM IR declarations and call lists
  C  MIR                 `-Zdump-mir` for `specimens/mir_specimens.rs`
  D  Miri                `specimens/miri/*.rs`, each with an expected outcome
  E  allocation failure  `specimens/oom_abort.rs`

Usage:

    python3 support/probe_allocator_shims_and_box.py            # rustc and cargo from PATH
    python3 support/probe_allocator_shims_and_box.py --rustc /path/to/rustc --skip-miri

Requirements: a nightly `rustc` (parts B and C use `-Z` flags and one specimen uses a feature
gate), a C linker, binutils `nm`, and for part D the `miri` component (its sysroot is located with
`cargo miri setup --print-sysroot` unless `--miri-sysroot` is given).

The script exits non-zero if any check fails. All host paths are removed from what it writes.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = HERE / "specimens"
OUT = HERE / "probe_output"

MIR_FUNCTIONS = [
    "box_new_sized",
    "box_new_zst",
    "write_via_move_direct",
    "box_new_uninit_mid_init",
    "box_partial_move",
    "box_conditional_partial_move",
    "box_full_move_out",
    "box_plain_drop",
    "box_deref_read",
    "vec_literal",
]

# Label of a point in the MIR pipeline -> suffix of the `-Zdump-mir` file name that selects it.
MIR_POINTS = {
    "built": ".built.after.mir",
    "ElaborateDrops.before": ".ElaborateDrops.before.mir",
    "ElaborateDrops.after": ".ElaborateDrops.after.mir",
    "ElaborateBoxDerefs.before": ".ElaborateBoxDerefs.before.mir",
    "ElaborateBoxDerefs.after": ".ElaborateBoxDerefs.after.mir",
}

# Raises the MIR inliner's cost thresholds far enough that `Box::new` is inlined into its callers.
FORCED_MIR_INLINE = ["-Zinline-mir=yes", "-Zinline-mir-threshold=10000", "-Zinline-mir-hint-threshold=10000"]

# Names that older compilers used for `Box` construction and destruction. None may occur in any
# MIR dump produced by the probed compiler.
LEGACY_MIR_NAMES = ["ShallowInitBox", "exchange_malloc", "box_free", "NullaryOp", "SizeOf("]

# (specimen file, expected exit status, regular expression that must match the diagnostics)
MIRI_CASES = [
    ("ub_dealloc_wrong_align.rs", 1,
     r"Undefined Behavior: incorrect layout on deallocation: alloc\d+ has size 8 and alignment 8, but gave size 8 and alignment 4"),
    ("ub_dealloc_wrong_size.rs", 1,
     r"Undefined Behavior: incorrect layout on deallocation: alloc\d+ has size 8 and alignment 8, but gave size 16 and alignment 8"),
    ("ub_alloc_zero_size.rs", 1, r"Undefined Behavior: creating allocation with size 0"),
    ("ub_dealloc_zst_dangling.rs", 1,
     r"Undefined Behavior: pointer not dereferenceable: pointer must point to some allocation, but got 0x1\[noalloc\] which is a dangling pointer"),
    ("ub_box_from_raw_wrong_layout.rs", 1,
     r"Undefined Behavior: incorrect layout on deallocation: alloc\d+ has size 8 and alignment 8, but gave size 4 and alignment 4"),
    ("ub_box_from_raw_wrong_align_only.rs", 1,
     r"Undefined Behavior: incorrect layout on deallocation: alloc\d+ has size 8 and alignment 8, but gave size 8 and alignment 1"),
    ("ub_full_drop_after_partial_move.rs", 1,
     r"Undefined Behavior: memory access failed: alloc\d+ has been freed, so this pointer is dangling"),
    ("ub_full_drop_of_uninit_box.rs", 1,
     r"Undefined Behavior: reading memory at alloc\d+\[0x8\.\.0x10\], but memory is uninitialized"),
    ("ub_double_free.rs", 1,
     r"Undefined Behavior: memory access failed: alloc\d+ has been freed, so this pointer is dangling"),
    ("leak_uninit_box_unwind_owning_field.rs", 1,
     r"error: memory leaked: alloc\d+ \(Rust heap, size: 8, align: 8\)"),
    ("ok_partial_move_unwind.rs", 0, r"^ok$"),
    ("ok_uninit_box_unwind_plain_fields.rs", 0, r"^ok$"),
    ("ok_zst_box_and_vec.rs", 0, r"^ok$"),
    ("ok_box_lifecycle.rs", 0, r"^ok$"),
]

# Expected counts per scenario of `alloc_lifecycle.rs`:
#   (allocations with alignment 64, deallocations with alignment 64, destructor runs by tag).
# These are the counts at `-C opt-level=0`; part A reports where an optimized build differs.
LIFECYCLE_EXPECT = {
    "zst_box_unit": (0, 0, {}),
    "zst_box_align64": (0, 0, {}),
    "zst_vec_unit_capacity": (0, 0, {}),
    "sized_box_roundtrip": (1, 1, {"1": 1, "2": 1}),
    "box_new_uninit_dropped": (1, 1, {}),
    "box_new_uninit_mid_init_panic": (1, 1, {}),
    "box_new_uninit_completed": (1, 1, {"5": 1, "6": 1}),
    "box_write_uninit": (1, 1, {"7": 1, "8": 1}),
    "box_partial_move_then_panic_forget": (1, 1, {"11": 1}),
    "box_partial_move_then_panic_keep": (1, 1, {"12": 1, "13": 1}),
    "box_partial_move_no_panic": (1, 1, {"14": 1, "15": 1}),
    "box_move_both_fields_then_panic": (1, 1, {"16": 1, "17": 1}),
    "box_full_move_out": (1, 1, {"18": 1, "19": 1}),
    "box_argument_panics_before_allocation": (0, 0, {}),
    "vec_macro_literal": (1, 1, {"20": 1, "21": 1, "22": 1}),
    "boxed_slice_and_dyn_dealloc": (2, 2, {"23": 1, "24": 1, "25": 1, "26": 1, "27": 1}),
    "box_leak": (1, 0, {}),
    "box_into_raw_from_raw": (1, 1, {"30": 1, "31": 1}),
    "vec_growth_realloc": (1, 1, {"32": 1, "33": 1, "34": 1, "35": 1, "36": 1}),
    "vec_try_reserve_refused": (0, 0, {}),
}


class Probe:
    def __init__(self, args):
        self.args = args
        self.rustc = args.rustc
        self.checks: list[dict] = []
        self.scrub_pairs: list[tuple[str, str]] = []

    # -- helpers ------------------------------------------------------------------------------

    def run(self, cmd, cwd=None, timeout=600, env=None):
        proc = subprocess.run(
            [str(c) for c in cmd], cwd=cwd, timeout=timeout, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        return proc.returncode, proc.stdout.decode("utf-8", "replace"), proc.stderr.decode("utf-8", "replace")

    def scrub(self, text: str) -> str:
        for needle, repl in self.scrub_pairs:
            text = text.replace(needle, repl)
        # The standard library's own source paths, as embedded in the toolchain.
        text = re.sub(r"/rustc/[0-9a-f]{40}/", "<rust-src>/", text)
        # Thread ids in panic messages differ from run to run.
        text = re.sub(r"thread '([^']*)' \(\d+\) panicked", r"thread '\1' (<tid>) panicked", text)
        return text

    def check(self, name: str, ok: bool, detail=None):
        self.checks.append({"check": name, "passed": bool(ok), **({"detail": detail} if detail is not None else {})})
        return bool(ok)

    def rustc_cmd(self, *extra):
        # Remap the specimen directory so that no host path reaches diagnostics, MIR or binaries.
        return [self.rustc, "--edition", "2021", f"--remap-path-prefix={SPEC}=specimens", *extra]

    # -- toolchain ----------------------------------------------------------------------------

    def toolchain(self):
        rc, out, err = self.run([self.rustc, "-Vv"])
        if rc != 0:
            raise SystemExit(f"cannot run {self.rustc}: {err}")
        info = dict(line.split(": ", 1) for line in out.splitlines() if ": " in line)
        info["version_line"] = out.splitlines()[0]
        rc, sysroot, _ = self.run([self.rustc, "--print", "sysroot"])
        self.sysroot = Path(sysroot.strip())
        self.scrub_pairs.append((str(self.sysroot), "<sysroot>"))
        self.scrub_pairs.append((str(SPEC), "specimens"))
        self.scrub_pairs.append((str(HERE), "support"))
        rc, nm_v, _ = self.run(["nm", "--version"])
        info["nm"] = nm_v.splitlines()[0] if nm_v else None
        return info

    # -- part A: runtime accounting ---------------------------------------------------------------

    def part_a(self, tmp: Path):
        result = {}
        for opt in ("0", "3"):
            exe = tmp / f"alloc_lifecycle_o{opt}"
            rc, out, err = self.run(self.rustc_cmd(
                "-C", f"opt-level={opt}", "-C", "panic=unwind", "-o", exe, SPEC / "alloc_lifecycle.rs"))
            if rc != 0:
                raise SystemExit("alloc_lifecycle.rs does not compile:\n" + err)
            rc, out, err = self.run([exe])
            scenarios = {}
            for line in out.splitlines():
                obj = json.loads(line)
                scenarios[obj.pop("scenario")] = obj
            result[f"opt_level_{opt}"] = {"exit_status": rc, "scenarios": scenarios}
            self.check(f"A.o{opt}.exit_status_zero", rc == 0, rc)
            totals = scenarios.get("_totals", {})
            self.check(f"A.o{opt}.no_layout_mismatch_no_unknown_free_no_bad_request",
                       totals and all(v == 0 for v in totals.values()), totals)
            for name, (allocs, deallocs, drops) in LIFECYCLE_EXPECT.items():
                got = scenarios.get(name)
                ok = (got is not None and got["align64_allocs"] == allocs
                      and got["align64_deallocs"] == deallocs and got["drops_by_tag"] == drops)
                self.check(f"A.o{opt}.{name}", ok,
                           None if ok else {"expected": [allocs, deallocs, drops], "got": got})
            sc = scenarios
            self.check(f"A.o{opt}.zst_addresses_equal_alignment",
                       sc["zst_box_unit"]["addr"] == 1 and sc["zst_box_align64"]["addr_align64"] == 64
                       and sc["zst_box_align64"]["addr_align8"] == 8 and sc["zst_box_align64"]["dyn_addr"] == 64
                       and sc["zst_vec_unit_capacity"]["addr"] == 1)
            self.check(f"A.o{opt}.zst_scenarios_reach_allocator_zero_times",
                       all(sc[n]["events"] == [] for n in ("zst_box_unit", "zst_box_align64", "zst_vec_unit_capacity")))
            self.check(f"A.o{opt}.zst_vec_capacity_is_usize_max",
                       sc["zst_vec_unit_capacity"]["capacity_is_usize_max"] is True
                       and sc["zst_vec_unit_capacity"]["len"] == 1000000)
            # Every deallocation in every window names the same block ordinal, size and alignment
            # as an earlier allocation (or reallocation result) in that window.
            pairing_ok = True
            for name, got in scenarios.items():
                live = {}
                for ev in got.get("events", []):
                    if ev["refused"]:
                        continue
                    if ev["op"] in ("alloc", "alloc_zeroed"):
                        live[ev["block"]] = (ev["size"], ev["align"])
                    elif ev["op"] == "realloc":
                        pairing_ok &= live.pop(ev["block"], None) == (ev["size"], ev["align"])
                        live["realloc-result"] = (ev["new_size"], ev["align"])
                    elif ev["op"] == "dealloc":
                        want = live.pop(ev["block"], None)
                        if want is None:
                            want = live.pop("realloc-result", None)
                        pairing_ok &= want == (ev["size"], ev["align"])
            self.check(f"A.o{opt}.every_dealloc_layout_equals_its_alloc_layout", pairing_ok)
            self.check(f"A.o{opt}.vec_try_reserve_refused_returns_err_without_abort",
                       sc["vec_try_reserve_refused"]["is_err"] is True
                       and sc["vec_try_reserve_refused"]["refused"] == 1
                       and sc["vec_try_reserve_refused"]["over_isize_max_is_err"] is True
                       and len(sc["vec_try_reserve_refused"]["events"]) == 1)
            panic_rt = [(e["op"], e["size"], e["align"]) for e in sc["box_argument_panics_before_allocation"]["events"]]
            result[f"opt_level_{opt}"]["panic_runtime_events"] = panic_rt
        o0 = result["opt_level_0"]["scenarios"]["unpinned_box_roundtrip"]
        o3 = result["opt_level_3"]["scenarios"]["unpinned_box_roundtrip"]
        result["unpinned_box_roundtrip_allocator_calls"] = {
            "opt_level_0": len(o0["events"]), "opt_level_3": len(o3["events"]),
            "note": "with a #[global_allocator] defined in the same crate",
        }
        return result

    # -- part B: symbols and IR ---------------------------------------------------------------------

    INTERNAL = re.compile(r"_RNvCs[0-9A-Za-z]+_7___rustc(\d+)(\w+)")

    def demangle_internal(self, sym: str):
        """Name of a `#[rustc_std_internal_symbol]` item from its v0-mangled form.

        Such items are mangled as a value in a crate called `__rustc`:
        `_RNvCs<crate hash>_7___rustc<len>[_]<name>`. The v0 grammar inserts the `_` separator
        after the length when the name starts with `_` or a digit.
        """
        m = self.INTERNAL.fullmatch(sym)
        if not m:
            return None
        n, rest = int(m.group(1)), m.group(2)
        if len(rest) == n + 1 and rest.startswith("_"):
            rest = rest[1:]
        return rest if len(rest) == n else None

    def nm_internal(self, path: Path):
        rc, out, err = self.run(["nm", path])
        defined, undefined, mangled = {}, [], {}
        for line in out.splitlines():
            parts = line.split()
            if len(parts) < 2:
                continue
            kind, sym = parts[-2], parts[-1]
            name = self.demangle_internal(sym)
            if name is None:
                continue
            mangled[name] = re.sub(r"_RNvCs[0-9A-Za-z]+_", "_RNvCs<crate-hash>_", sym)
            if kind == "U":
                undefined.append(name)
            else:
                defined[name] = kind
        return {"defined": dict(sorted(defined.items())), "undefined": sorted(undefined)}, mangled

    def ir_function(self, ll: str, name: str):
        m = re.search(r"^define [^\n]*@" + re.escape(name) + r"\(.*?^}", ll, re.S | re.M)
        if not m:
            return None
        body = m.group(0)
        calls = []
        for callee in re.findall(r"(?:call|invoke)[^\n]*?@([A-Za-z0-9_.$]+)\(", body):
            calls.append(self.demangle_internal(callee) or re.sub(r"Cs[0-9A-Za-z]+_", "Cs<h>_", callee))
        return {"callees_in_order": calls, "stores_inttoptr_1": "inttoptr (i64 1 to ptr)" in body}

    def part_b(self, tmp: Path):
        result = {}
        for label, src in (("default_allocator", "default_alloc.rs"), ("global_allocator", "alloc_lifecycle.rs")):
            d = tmp / f"sym_{label}"
            d.mkdir()
            stem = src[:-3]
            rc, out, err = self.run(self.rustc_cmd(
                "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "save-temps", "-C", "panic=unwind",
                "--emit=link,llvm-ir", "--out-dir", d, SPEC / src))
            if rc != 0:
                raise SystemExit(f"{src} does not compile:\n" + err)
            objs = sorted(d.glob("*.rcgu.o"))
            shim = [o for o in objs if "-cgu." not in o.name]
            crate = [o for o in objs if "-cgu." in o.name]
            entry = {"object_count": len(objs)}
            mangled_examples = {}
            if len(shim) == 1 and len(crate) == 1:
                entry["allocator_shim_object"], m1 = self.nm_internal(shim[0])
                entry["crate_object"], m2 = self.nm_internal(crate[0])
                mangled_examples.update(m1)
                mangled_examples.update(m2)
            exe_syms, m3 = self.nm_internal(d / stem)
            entry["linked_executable"] = exe_syms
            entry["mangled_names"] = {k: v for k, v in sorted({**m3, **mangled_examples}.items())
                                      if k.startswith("__rust_") or k.startswith("__rdl_")}
            ll = (d / f"{stem}.ll").read_text(errors="replace")
            attrs = dict(re.findall(r"^attributes #(\d+) = \{(.*)\}$", ll, re.M))
            decls = {}
            for line in ll.splitlines():
                m = re.match(r"^(declare|define) (.*?)@(_RNvCs[0-9A-Za-z]+_7___rustc\d+\w+)\((.*)\)(.*)$", line)
                if not m:
                    continue
                name = self.demangle_internal(m.group(3))
                if not name or not (name.startswith("__rust_") and "panic" not in name):
                    continue
                attr_ids = re.findall(r"#(\d+)", m.group(5))
                fn_attrs = " ".join(attrs.get(a, "") for a in attr_ids)
                decls[name] = {
                    "kind": m.group(1),
                    "return": m.group(2).strip(),
                    "params": m.group(4),
                    "allockind": (re.search(r'allockind\("([^"]*)"\)', fn_attrs) or [None, None])[1],
                    "allocsize": (re.search(r"allocsize\(([^)]*)\)", fn_attrs) or [None, None])[1],
                    "alloc_family": (re.search(r'"alloc-family"="([^"]*)"', fn_attrs) or [None, None])[1],
                    "alloc_variant_zeroed": bool(re.search(r'"alloc-variant-zeroed"=', fn_attrs)),
                    "nounwind": "nounwind" in fn_attrs.split(),
                }
            entry["llvm_ir"] = {"internal_allocator_symbols": dict(sorted(decls.items()))}
            if label == "default_allocator":
                entry["llvm_ir"]["functions"] = {
                    n: self.ir_function(ll, n) for n in ("unpinned_roundtrip", "pinned_roundtrip", "zst_box")
                }
            result[label] = entry

        d = result["default_allocator"]
        g = result["global_allocator"]
        four = ["__rust_alloc", "__rust_alloc_zeroed", "__rust_dealloc", "__rust_realloc"]
        marker = "__rust_no_alloc_shim_is_unstable_v2"
        self.check("B.default.shim_object_defines_four_methods_and_marker",
                   sorted(d["allocator_shim_object"]["defined"]) == sorted(four + [marker]),
                   d["allocator_shim_object"])
        self.check("B.default.shim_object_forwards_to_rdl",
                   d["allocator_shim_object"]["undefined"] ==
                   ["__rdl_alloc", "__rdl_alloc_zeroed", "__rdl_dealloc", "__rdl_realloc"])
        self.check("B.default.error_handler_defined_in_executable_not_in_shim",
                   "__rust_alloc_error_handler" in d["linked_executable"]["defined"]
                   and "__rust_alloc_error_handler" not in d["allocator_shim_object"]["defined"])
        self.check("B.global.shim_object_defines_only_marker",
                   list(g["allocator_shim_object"]["defined"]) == [marker] and g["allocator_shim_object"]["undefined"] == [],
                   g["allocator_shim_object"])
        self.check("B.global.crate_object_defines_four_methods",
                   all(n in g["crate_object"]["defined"] for n in four)
                   and marker in g["crate_object"]["undefined"], g["crate_object"])
        self.check("B.global.no_rdl_symbols_referenced_by_shim_or_crate",
                   not any(n.startswith("__rdl_") for n in
                           list(g["crate_object"]["defined"]) + g["crate_object"]["undefined"]
                           + g["allocator_shim_object"]["undefined"]))
        every = set()
        for e in (d, g):
            for part in ("allocator_shim_object", "crate_object", "linked_executable"):
                every |= set(e[part]["defined"]) | set(e[part]["undefined"])
        absent = ["__rust_alloc_error_handler_should_panic_v2", "__rust_alloc_error_handler_should_panic",
                  "__rust_no_alloc_shim_is_unstable", "__rg_alloc", "__rg_dealloc", "__rg_oom", "__rdl_oom"]
        self.check("B.absent_symbols", not any(a in every for a in absent), sorted(every & set(absent)))
        result["absent_symbols_checked"] = absent
        ir = d["llvm_ir"]["internal_allocator_symbols"]
        self.check("B.ir.alloc_attributes",
                   ir.get("__rust_alloc", {}).get("allockind") == "alloc,uninitialized,aligned"
                   and ir["__rust_alloc"]["allocsize"] == "0" and ir["__rust_alloc"]["alloc_family"] == "__rust_alloc"
                   and ir["__rust_alloc"]["alloc_variant_zeroed"] and ir["__rust_alloc"]["nounwind"]
                   and "allocalign" in ir["__rust_alloc"]["params"] and "noalias" in ir["__rust_alloc"]["return"],
                   ir.get("__rust_alloc"))
        self.check("B.ir.dealloc_attributes",
                   ir.get("__rust_dealloc", {}).get("allockind") == "free"
                   and ir["__rust_dealloc"]["alloc_family"] == "__rust_alloc"
                   and "allocptr" in ir["__rust_dealloc"]["params"] and ir["__rust_dealloc"]["nounwind"],
                   ir.get("__rust_dealloc"))
        self.check("B.ir.marker_has_no_allocator_attributes",
                   ir.get(marker, {}).get("allockind") is None and ir[marker]["params"] == "", ir.get(marker))
        fns = d["llvm_ir"]["functions"]
        self.check("B.ir.unpinned_roundtrip_allocation_removed_marker_call_kept",
                   fns["unpinned_roundtrip"]["callees_in_order"] == [marker], fns["unpinned_roundtrip"])
        self.check("B.ir.pinned_roundtrip_calls_marker_then_alloc_then_dealloc",
                   [c for c in fns["pinned_roundtrip"]["callees_in_order"] if c.startswith("__rust")]
                   == [marker, "__rust_alloc", "__rust_dealloc"], fns["pinned_roundtrip"])
        self.check("B.ir.zst_box_has_no_allocator_call_and_stores_address_1",
                   not any(c.startswith("__rust") for c in fns["zst_box"]["callees_in_order"])
                   and fns["zst_box"]["stores_inttoptr_1"], fns["zst_box"])

        # The source-level expansion of `#[global_allocator]`.
        src = tmp / "expansion.rs"
        src.write_text(
            "use std::alloc::{GlobalAlloc, Layout, System};\n"
            "struct Forward;\n"
            "unsafe impl GlobalAlloc for Forward {\n"
            "    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { unsafe { System.alloc(layout) } }\n"
            "    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) { unsafe { System.dealloc(ptr, layout) } }\n"
            "}\n"
            "#[global_allocator]\n"
            "static GLOBAL: Forward = Forward;\n"
            "fn main() {}\n")
        rc, out, err = self.run([self.rustc, "--edition", "2021", "-Zunpretty=expanded", src])
        start = out.find("static GLOBAL")
        expansion = out[start:] if start >= 0 else out
        (OUT / "global_allocator_expansion.txt").write_text(self.scrub(expansion))
        sigs = re.findall(r"unsafe fn (__rust_\w+)\(([^)]*)\)", re.sub(r"\s+", " ", expansion))
        result["global_allocator_expansion_signatures"] = {n: p.strip() for n, p in sigs}
        self.check("B.expansion.four_functions_with_alignment_typed_align",
                   sorted(n for n, _ in sigs) == sorted(four)
                   and all("align: ::core::mem::Alignment" in p for _, p in sigs)
                   and expansion.count("#[rustc_std_internal_symbol]") == 4
                   and expansion.count("from_size_alignment_unchecked") == 4,
                   result["global_allocator_expansion_signatures"])
        return result

    # -- part C: MIR ---------------------------------------------------------------------------------

    def part_c(self, tmp: Path):
        result = {"functions": {}}
        mir_out = OUT / "mir"
        if mir_out.exists():
            shutil.rmtree(mir_out)
        texts = {}
        # "3f" is opt-level 3 with the MIR inliner's cost thresholds raised, which makes it inline
        # `Box::new` into the specimen functions and so exposes the library body in their MIR.
        configs = {
            "0": ("opt_level_0", ["-C", "opt-level=0"]),
            "3": ("opt_level_3", ["-C", "opt-level=3"]),
            "3f": ("opt_level_3_forced_mir_inline", ["-C", "opt-level=3"] + FORCED_MIR_INLINE),
        }
        result["configurations"] = {label: " ".join(flags) for label, flags in configs.values()}
        for opt, (label, flags) in configs.items():
            d = tmp / f"mir_o{opt}"
            d.mkdir()
            rc, out, err = self.run(self.rustc_cmd(
                "--crate-type=lib", *flags, "-C", "panic=unwind",
                "-Zdump-mir=" + " | ".join(MIR_FUNCTIONS), f"-Zdump-mir-dir={d}",
                "--emit=mir", "--out-dir", d / "out", SPEC / "mir_specimens.rs"))
            if rc != 0:
                raise SystemExit("mir_specimens.rs does not compile:\n" + err)
            dest = mir_out / label
            dest.mkdir(parents=True)
            final = (d / "out" / "mir_specimens.mir").read_text()
            texts[(opt, "*", "final")] = final
            if opt == "3f":
                # Only the two functions whose inlined bodies are examined are kept from this
                # configuration; the complete final MIR is kept for the other two.
                for fn in ("box_new_sized", "box_new_zst"):
                    m = re.search(r"^fn " + re.escape(fn) + r"\(.*?^}", final, re.S | re.M)
                    if m:
                        (dest / f"{fn}.final.mir").write_text(self.scrub(m.group(0)) + "\n")
            else:
                (dest / "final.mir").write_text(self.scrub(final))
            for fn in MIR_FUNCTIONS:
                for point, suffix in MIR_POINTS.items():
                    if opt != "0":
                        continue  # these passes run before optimization and do not depend on it
                    hits = [p for p in d.glob(f"mir_specimens.{fn}.*") if p.name.endswith(suffix)]
                    if len(hits) != 1:
                        continue
                    text = hits[0].read_text()
                    texts[(opt, fn, point)] = text
                    if opt == "0":
                        (dest / f"{fn}.{point}.mir").write_text(self.scrub(text))
        result["dump_files_kept"] = sorted(str(p.relative_to(OUT)) for p in mir_out.rglob("*.mir"))

        every = "\n".join(texts.values())
        legacy = {n: every.count(n) for n in LEGACY_MIR_NAMES}
        result["legacy_name_occurrences_in_all_dumps"] = legacy
        self.check("C.no_legacy_box_names_in_any_dump", all(v == 0 for v in legacy.values()), legacy)

        def t(fn, point, opt="0"):
            return texts.get((opt, fn, point), "")

        def final_fn(fn, opt):
            m = re.search(r"^fn " + re.escape(fn) + r"\(.*?^}", texts[(opt, "*", "final")], re.S | re.M)
            return m.group(0) if m else ""

        def cleanup_blocks(text):
            return re.findall(r"^    bb\d+ \(cleanup\): \{.*?^    \}", text, re.S | re.M)

        def normal_blocks(text):
            return re.findall(r"^    bb\d+: \{.*?^    \}", text, re.S | re.M)

        f = result["functions"]

        wvm = t("write_via_move_direct", "built")
        f["write_via_move_direct"] = {
            "built_has_plain_assignment": bool(re.search(r"\(\*_\d+\) = move _2;", wvm)),
            "built_mentions_write_via_move_call": "write_via_move" in wvm.split("{", 1)[-1],
        }
        self.check("C.write_via_move_is_an_assignment_in_built_mir",
                   f["write_via_move_direct"]["built_has_plain_assignment"]
                   and not f["write_via_move_direct"]["built_mentions_write_via_move_call"])

        bns = t("box_new_sized", "built")
        o0, o3, o3f = final_fn("box_new_sized", "0"), final_fn("box_new_sized", "3"), final_fn("box_new_sized", "3f")
        f["box_new_sized"] = {
            "built_calls_box_new": "= Box::<Pair>::new(move _" in bns,
            "final_opt0_calls_box_new": "Box::<Pair>::new(" in o0,
            "final_opt3_calls_box_new": "Box::<Pair>::new(" in o3,
            "forced_inline_calls_box_new": "Box::<Pair>::new(" in o3f,
            "forced_inline_scope_inlined_box_new": "(inlined Box::<Pair>::new)" in o3f,
            "forced_inline_calls_box_new_uninit_with_layout_16_8": bool(re.search(
                r"= boxed::box_new_uninit\(const Layout \{\{ size: 16_usize, align: [^\n]*_Align1Shl3 \}\} \}\}\)", o3f)),
            "forced_inline_has_deref_assignment": bool(re.search(r"\(\*_\d+\) = move _\d+;", o3f)),
            "forced_inline_has_transmute_to_box": bool(re.search(r"= copy _\d+ as std::boxed::Box<Pair> \(Transmute\)", o3f)),
        }
        # The block that stores the value: it must hold the transmute too and end in `return`,
        # so that nothing between the store and the return can unwind.
        store_blocks = [blk for blk in normal_blocks(o3f) if re.search(r"\(\*_\d+\) = move _\d+;", blk)]
        f["box_new_sized"]["forced_inline_store_block_has_transmute_and_returns_without_unwind_edge"] = (
            len(store_blocks) == 1 and "(Transmute)" in store_blocks[0]
            and "return;" in store_blocks[0] and "->" not in store_blocks[0])
        b = f["box_new_sized"]
        self.check("C.box_new.is_an_ordinary_call_in_built_and_default_optimized_mir",
                   b["built_calls_box_new"] and b["final_opt0_calls_box_new"] and b["final_opt3_calls_box_new"], b)
        self.check("C.box_new.inlined_body_is_box_new_uninit_then_store_then_transmute",
                   b["forced_inline_scope_inlined_box_new"] and not b["forced_inline_calls_box_new"]
                   and b["forced_inline_calls_box_new_uninit_with_layout_16_8"]
                   and b["forced_inline_has_deref_assignment"] and b["forced_inline_has_transmute_to_box"]
                   and b["forced_inline_store_block_has_transmute_and_returns_without_unwind_edge"], b)

        pm_before, pm_after = t("box_partial_move", "ElaborateDrops.before"), t("box_partial_move", "ElaborateDrops.after")
        f["box_partial_move"] = {
            "before_whole_box_drop_terminators": len(re.findall(r"drop\(_1\)", pm_before)),
            "after_whole_box_drop_terminators": len(re.findall(r"drop\(_1\)", pm_after)),
            "after_drops_of_moved_field_0": len(re.findall(r"drop\(\(\(\*_\d+\)\.0: Counted\)\)", pm_after)),
            "after_drops_of_remaining_field_1": len(re.findall(r"drop\(\(\(\*_\d+\)\.1: Counted\)\)", pm_after)),
            "after_remaining_field_drops_in_cleanup": sum(
                len(re.findall(r"drop\(\(\(\*_\d+\)\.1: Counted\)\)", b)) for b in cleanup_blocks(pm_after)),
            "after_box_drop_calls": len(re.findall(r"<Box<Pair> as Drop>::drop\(", pm_after)),
            "after_box_drop_calls_in_cleanup": sum(
                len(re.findall(r"<Box<Pair> as Drop>::drop\(", b)) for b in cleanup_blocks(pm_after)),
            "after_box_drop_calls_on_normal_path": sum(
                len(re.findall(r"<Box<Pair> as Drop>::drop\(", b)) for b in normal_blocks(pm_after)),
            "after_pointer_transmutes": len(re.findall(
                r"= copy \(\(_1\.0: std::ptr::Unique<Pair>\)\.0: std::ptr::NonNull<Pair>\) as \*const Pair \(Transmute\)", pm_after)),
            "after_drop_flag_assignments": len(re.findall(r"_\d+ = const (true|false);", pm_after)),
            "after_moved_out_local_dropped_in_cleanup": sum(len(re.findall(r"drop\(_3\)", b)) for b in cleanup_blocks(pm_after)),
        }
        pm = f["box_partial_move"]
        self.check("C.partial_move.open_drop_never_drops_moved_field", pm["after_drops_of_moved_field_0"] == 0, pm)
        self.check("C.partial_move.remaining_field_dropped_on_normal_and_unwind_paths",
                   pm["after_drops_of_remaining_field_1"] >= 2 and pm["after_remaining_field_drops_in_cleanup"] >= 1, pm)
        self.check("C.partial_move.box_destructor_called_on_normal_and_unwind_paths",
                   pm["after_box_drop_calls_on_normal_path"] == 1 and pm["after_box_drop_calls_in_cleanup"] >= 2
                   and pm["after_whole_box_drop_terminators"] == 0, pm)
        self.check("C.partial_move.static_case_needs_no_drop_flag", pm["after_drop_flag_assignments"] == 0, pm)

        cm_after = t("box_conditional_partial_move", "ElaborateDrops.after")
        f["box_conditional_partial_move"] = {
            "after_drop_flag_assignments": len(re.findall(r"_\d+ = const (true|false);", cm_after)),
            "after_switch_on_flag": len(re.findall(r"switchInt\(copy _\d+\) -> \[0: bb\d+, otherwise: bb\d+\]", cm_after)),
            "after_drops_of_field_0": len(re.findall(r"drop\(\(\(\*_\d+\)\.0: Counted\)\)", cm_after)),
            "after_drops_of_field_1": len(re.findall(r"drop\(\(\(\*_\d+\)\.1: Counted\)\)", cm_after)),
            "after_box_drop_calls": len(re.findall(r"<Box<Pair> as Drop>::drop\(", cm_after)),
        }
        cm = f["box_conditional_partial_move"]
        self.check("C.conditional_partial_move.uses_drop_flag_for_field_0",
                   cm["after_drop_flag_assignments"] >= 2 and cm["after_switch_on_flag"] >= 1
                   and cm["after_drops_of_field_0"] >= 1 and cm["after_drops_of_field_1"] >= 1
                   and cm["after_box_drop_calls"] >= 2, cm)

        mi_after = t("box_new_uninit_mid_init", "ElaborateDrops.after")
        f["box_new_uninit_mid_init"] = {
            "after_whole_box_drops_in_cleanup": sum(len(re.findall(r"drop\(_2\)", b)) for b in cleanup_blocks(mi_after)),
            "after_field_drops": len(re.findall(r"drop\(\(\(\*_\d+\)\.\d+: Counted\)\)", mi_after)),
            "after_box_type_is_maybe_uninit": "let mut _2: std::boxed::Box<std::mem::MaybeUninit<Pair>>;" in mi_after,
            "after_has_drop_flag_switch": bool(re.search(r"switchInt\(copy _\d+\) -> \[0: bb\d+, otherwise: bb\d+\]", mi_after)),
        }
        mi = f["box_new_uninit_mid_init"]
        self.check("C.uninit_mid_init.cleanup_drops_the_box_and_no_field",
                   mi["after_whole_box_drops_in_cleanup"] == 1 and mi["after_field_drops"] == 0
                   and mi["after_box_type_is_maybe_uninit"], mi)

        fm_after = t("box_full_move_out", "ElaborateDrops.after")
        f["box_full_move_out"] = {
            "after_field_or_content_drops": len(re.findall(r"drop\(\(\*_\d+\)", fm_after)),
            "after_box_drop_calls": len(re.findall(r"<Box<Pair> as Drop>::drop\(", fm_after)),
            "after_moves_whole_content": bool(re.search(r"_0 = move \(\*_1\);", fm_after)),
        }
        self.check("C.full_move_out.frees_box_without_dropping_content",
                   f["box_full_move_out"]["after_field_or_content_drops"] == 0
                   and f["box_full_move_out"]["after_box_drop_calls"] >= 1
                   and f["box_full_move_out"]["after_moves_whole_content"], f["box_full_move_out"])

        bd_before, bd_after = t("box_deref_read", "ElaborateBoxDerefs.before"), t("box_deref_read", "ElaborateBoxDerefs.after")
        f["box_deref_read"] = {
            "before_derefs_box_directly": bool(re.search(r"= copy \(\*_\d+\);", bd_before)),
            "after_transmutes_nonnull_to_raw": bool(re.search(
                r"= copy \(\(_\d+\.0: std::ptr::Unique<usize>\)\.0: std::ptr::NonNull<usize>\) as \*const usize \(Transmute\)", bd_after)),
        }
        self.check("C.box_deref_elaborated_to_transmuted_raw_pointer",
                   f["box_deref_read"]["after_transmutes_nonnull_to_raw"], f["box_deref_read"])

        vl = t("vec_literal", "built")
        f["vec_literal"] = {
            "built_calls_box_new_uninit": "Box::<[Counted; 2]>::new_uninit()" in vl,
            "built_calls_box_assume_init_into_vec_unsafe": "box_assume_init_into_vec_unsafe" in vl,
            "built_mentions_write_box_via_move_call": "write_box_via_move" in vl.split("{", 1)[-1],
            "built_assigns_through_box": bool(re.search(r"\(\(\(\(\*_\d+\)\.1: [^\n]*= \[move _\d+, move _\d+\];", vl)),
        }
        self.check("C.vec_literal_uses_new_uninit_and_in_place_store",
                   f["vec_literal"]["built_calls_box_new_uninit"]
                   and f["vec_literal"]["built_calls_box_assume_init_into_vec_unsafe"]
                   and not f["vec_literal"]["built_mentions_write_box_via_move_call"], f["vec_literal"])

        z3f = final_fn("box_new_zst", "3f")
        f["box_new_zst"] = {
            "forced_inline_calls_box_new_uninit_with_layout_0_1": bool(re.search(
                r"= boxed::box_new_uninit\(const Layout \{\{ size: 0_usize, align: [^\n]*_Align1Shl0 \}\} \}\}\)", z3f)),
            "forced_inline_has_deref_assignment": bool(re.search(r"\(\*_\d+\) = ", z3f)),
            "forced_inline_has_transmute_to_box": bool(re.search(r"= copy _\d+ as std::boxed::Box<\(\)> \(Transmute\)", z3f)),
        }
        z = f["box_new_zst"]
        self.check("C.box_new_zst.still_calls_box_new_uninit_with_size_0_and_stores_nothing",
                   z["forced_inline_calls_box_new_uninit_with_layout_0_1"] and not z["forced_inline_has_deref_assignment"]
                   and z["forced_inline_has_transmute_to_box"], z)
        return result

    # -- part D: Miri ----------------------------------------------------------------------------------

    def part_d(self, tmp: Path):
        if self.args.skip_miri:
            return {"skipped": True}
        miri = self.args.miri or str(self.sysroot / "bin" / "miri")
        sysroot = self.args.miri_sysroot
        if not sysroot:
            rc, out, err = self.run([self.args.cargo, "miri", "setup", "--print-sysroot"], timeout=1800)
            if rc != 0 or not out.strip():
                raise SystemExit("cannot locate a Miri sysroot (use --miri-sysroot or --skip-miri):\n" + err)
            sysroot = out.strip().splitlines()[-1]
        self.scrub_pairs.append((str(sysroot), "<miri-sysroot>"))
        rc, version, _ = self.run([miri, "--version"])
        result = {"miri_version": version.strip(), "cases": {}}
        env = dict(os.environ, MIRI_SYSROOT=str(sysroot))
        for name, want_rc, pattern in MIRI_CASES:
            rc, out, err = self.run(
                [miri, "--sysroot", sysroot, "--edition", "2021",
                 f"--remap-path-prefix={SPEC}=specimens", SPEC / "miri" / name],
                cwd=tmp, env=env, timeout=900)
            text = self.scrub(out + err)
            first_error = next((l for l in text.splitlines() if l.startswith("error")), None)
            matched = bool(re.search(pattern, text, re.M))
            result["cases"][name] = {
                "exit_status": rc,
                "expected_exit_status": want_rc,
                "first_error_line": first_error,
                "expected_pattern": pattern,
                "pattern_matched": matched,
                "undefined_behavior_reported": "Undefined Behavior" in text,
                "leak_reported": "memory leaked" in text,
            }
            self.check(f"D.{name}", rc == want_rc and matched, None if rc == want_rc and matched else text[-1500:])
        return result

    # -- part E: allocation failure ----------------------------------------------------------------------

    def part_e(self, tmp: Path):
        exe = tmp / "oom_abort"
        rc, out, err = self.run(self.rustc_cmd("-C", "opt-level=0", "-o", exe, SPEC / "oom_abort.rs"))
        if rc != 0:
            raise SystemExit("oom_abort.rs does not compile:\n" + err)
        result = {}
        env = {k: v for k, v in os.environ.items() if k != "RUST_BACKTRACE"}
        for mode in ("box", "vec", "try_reserve", "raw", "overflow"):
            rc, out, err = self.run([exe, mode], env=env)
            result[mode] = {
                "exit_status": rc if rc >= 0 else None,
                "signal": signal.Signals(-rc).name if rc < 0 else None,
                "stdout": self.scrub(out).strip().splitlines(),
                "stderr": [l for l in self.scrub(err).strip().splitlines() if l],
            }
        for mode in ("box", "vec"):
            r = result[mode]
            self.check(f"E.{mode}.aborts_with_allocation_failure_message",
                       r["signal"] == "SIGABRT" and r["stdout"] == []
                       and r["stderr"][:1] == ["memory allocation of 2199023255552 bytes failed"], r)
        self.check("E.try_reserve.returns_err_and_exits_normally",
                   result["try_reserve"]["exit_status"] == 0
                   and result["try_reserve"]["stdout"] == ["try_reserve_exact is_err=true refused_calls=1"],
                   result["try_reserve"])
        self.check("E.raw.returns_null_and_exits_normally",
                   result["raw"]["exit_status"] == 0
                   and result["raw"]["stdout"] == ["raw alloc is_null=true refused_calls=1"], result["raw"])
        self.check("E.overflow.panics_with_capacity_overflow",
                   result["overflow"]["exit_status"] == 101
                   and any(l == "capacity overflow" for l in result["overflow"]["stderr"]), result["overflow"])
        return result


def assert_no_host_paths(text: str, where: str):
    # Anything that looks like an absolute host path is a bug in the scrubbing above.
    bad = re.findall(r"(?<![\w<>.])/(?:tmp|home|usr|var|root|opt|mnt|private|Users)/[^\s\"']*", text)
    if bad:
        raise SystemExit(f"host path left in {where}: {bad[:5]}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--cargo", default="cargo", help="used only to locate the Miri sysroot")
    ap.add_argument("--miri", default=None, help="path of the `miri` driver (default: <sysroot>/bin/miri)")
    ap.add_argument("--miri-sysroot", default=None)
    ap.add_argument("--skip-miri", action="store_true")
    args = ap.parse_args(argv)

    OUT.mkdir(exist_ok=True)
    probe = Probe(args)
    results = {"schema": "allocator-box-probe/1", "generated_on": datetime.date.today().isoformat()}
    results["toolchain"] = probe.toolchain()
    with tempfile.TemporaryDirectory(prefix="alloc-box-probe-") as tmp_name:
        tmp = Path(tmp_name)
        probe.scrub_pairs.append((str(tmp), "<build>"))
        results["part_a_runtime_accounting"] = probe.part_a(tmp)
        results["part_b_symbols_and_ir"] = probe.part_b(tmp)
        results["part_c_mir"] = probe.part_c(tmp)
        results["part_d_miri"] = probe.part_d(tmp)
        results["part_e_allocation_failure"] = probe.part_e(tmp)
    results["checks"] = probe.checks
    failed = [c["check"] for c in probe.checks if not c["passed"]]
    results["summary"] = {"checks": len(probe.checks), "failed": failed, "passed": not failed}

    text = probe.scrub(json.dumps(results, indent=1, sort_keys=True)) + "\n"
    assert_no_host_paths(text, "probe_results.json")
    for p in OUT.rglob("*"):
        if p.is_file() and p.suffix in (".mir", ".txt"):
            assert_no_host_paths(p.read_text(errors="replace"), str(p.relative_to(OUT)))
    (OUT / "probe_results.json").write_text(text)

    print(f"{results['toolchain']['version_line']}")
    print(f"checks: {len(probe.checks)}, failed: {len(failed)}")
    for name in failed:
        print("FAILED", name)
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
