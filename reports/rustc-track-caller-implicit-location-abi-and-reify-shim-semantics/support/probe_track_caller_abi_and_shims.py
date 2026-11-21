#!/usr/bin/env python3
"""Probe `#[track_caller]`: implicit `&Location` ABI, MIR-inlining invariance, reify shims.

The probe compiles the Rust sources in `probe_src/` (next to this script) with a nightly `rustc`,
runs them natively and under Miri, inspects pretty-printed MIR, emitted x86-64 assembly and the
disassembled object file, and writes one JSON document with every observation plus a list of
self-checks. Every expected line number is derived from `@NAME` markers in the Rust sources, so
editing a source file does not invalidate the checks.

Usage:
    python3 probe_track_caller_abi_and_shims.py [--out FILE] [--rustc PATH] [--miri PATH]
        [--miri-sysroot DIR] [--objdump PATH] [--skip-miri]

Requirements: a nightly toolchain (the probe passes `-Z` flags) for x86_64-unknown-linux-gnu, GNU
`objdump`, and for the interpreter runs the `miri` component with a prepared Miri sysroot
(`cargo miri setup --print-sysroot`). Only the Python standard library is used. All work happens
in a temporary directory that is removed on exit; recorded text is scrubbed of local paths.

Exit status: 0 when every self-check passes, 1 otherwise, 2 on a setup problem.
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

HERE = Path(__file__).resolve().parent
SRC = HERE / "probe_src"
MARKER_RE = re.compile(r"@([A-Z][A-Z0-9_]+)")
EDITION = ["--edition", "2021"]


class Setup(Exception):
    """A missing tool or input that prevents the probe from running at all."""


# --------------------------------------------------------------------------------------------
# Small utilities
# --------------------------------------------------------------------------------------------


def run(cmd, cwd, env=None, timeout=600):
    proc = subprocess.run(
        [str(c) for c in cmd],
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, proc.stdout.decode("utf-8", "replace"), proc.stderr.decode("utf-8", "replace")


def markers(text: str) -> dict:
    """Map each `@NAME` marker to its 1-based line; a marker must be unique within a file."""
    found: dict = {}
    for number, line in enumerate(text.splitlines(), start=1):
        for name in MARKER_RE.findall(line):
            if name == "NAME":  # the placeholder used in explanatory comments
                continue
            if name in found:
                raise Setup(f"duplicate marker @{name}")
            found[name] = number
    return found


def key_values(stdout: str) -> dict:
    out = {}
    for line in stdout.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            out[key.strip()] = value.strip()
    return out


class Scrubber:
    """Replace local path prefixes by placeholders and refuse to emit anything that still leaks."""

    LEAK_RE = re.compile(r"(?<![\w$.])/(?:home|Users|root|usr|tmp|var|mnt|opt|private|google|x20)/")

    def __init__(self):
        self.pairs = []

    def add(self, path, placeholder):
        if not path:
            return
        text = str(path)
        self.pairs.append((text, placeholder))
        real = os.path.realpath(text)
        if real != text:
            self.pairs.append((real, placeholder))
        self.pairs.sort(key=lambda pair: -len(pair[0]))

    def __call__(self, text: str) -> str:
        for needle, placeholder in self.pairs:
            text = text.replace(needle, placeholder)
        return text

    def verify(self, text: str):
        leak = self.LEAK_RE.search(text)
        if leak:
            start = max(0, leak.start() - 60)
            raise Setup(f"refusing to write output with a local path: ...{text[start:leak.end() + 60]!r}")


class Checks:
    def __init__(self):
        self.items = []

    def add(self, name, ok, detail=""):
        self.items.append({"name": name, "pass": bool(ok), "detail": detail})
        return bool(ok)

    def eq(self, name, observed, expected):
        return self.add(name, observed == expected, f"observed={observed!r} expected={expected!r}")


# --------------------------------------------------------------------------------------------
# Toolchain discovery
# --------------------------------------------------------------------------------------------


def discover(args):
    rustc = args.rustc or shutil.which("rustc")
    if not rustc:
        raise Setup("rustc not found; pass --rustc")
    rc, verbose, err = run([rustc, "-Vv"], HERE)
    if rc != 0:
        raise Setup(f"`rustc -Vv` failed: {err}")
    if "nightly" not in verbose and "dev" not in verbose:
        raise Setup("the probe needs a nightly rustc (it passes -Z flags)")
    rc, sysroot, _ = run([rustc, "--print", "sysroot"], HERE)
    sysroot = sysroot.strip()
    tools = {"rustc": rustc, "rustc_verbose": verbose.strip(), "sysroot": sysroot}

    objdump = args.objdump or shutil.which("objdump")
    if not objdump:
        raise Setup("objdump not found; pass --objdump")
    rc, version, _ = run([objdump, "--version"], HERE)
    tools["objdump"] = objdump
    tools["objdump_version"] = version.splitlines()[0].strip() if version else "unknown"

    tools["miri"] = None
    if not args.skip_miri:
        miri = args.miri or os.path.join(sysroot, "bin", "miri")
        if not os.path.exists(miri):
            raise Setup("miri driver not found; install the `miri` component or pass --skip-miri")
        miri_sysroot = args.miri_sysroot or os.environ.get("MIRI_SYSROOT")
        if not miri_sysroot:
            cargo = shutil.which("cargo") or os.path.join(sysroot, "bin", "cargo")
            rc, out, err = run([cargo, "miri", "setup", "--print-sysroot"], HERE, timeout=1800)
            if rc != 0 or not out.strip():
                raise Setup(f"`cargo miri setup --print-sysroot` failed: {err[-400:]}")
            miri_sysroot = out.strip().splitlines()[-1]
        rc, version, _ = run([miri, "--version"], HERE)
        tools.update({"miri": miri, "miri_sysroot": miri_sysroot, "miri_version": version.strip()})
    return tools


# --------------------------------------------------------------------------------------------
# A. Regime matrix: native and interpreted, with and without MIR inlining
# --------------------------------------------------------------------------------------------


def regime_matrix(tools, work, scrub, checks):
    name = "track_caller_probe.rs"
    source = (work / name).read_text()
    mark = markers(source)
    result = {"markers": mark, "runs": {}, "commands": {}}

    def native(tag, flags):
        binary = f"native_{tag}"
        cmd = [tools["rustc"], *EDITION, *flags, "-o", binary, name]
        rc, _, err = run(cmd, work)
        result["commands"][f"native_{tag}"] = scrub(" ".join(["rustc", *EDITION, *flags, "-o", binary, name]))
        if rc != 0:
            checks.add(f"regimes/native_{tag}/compiles", False, scrub(err[-600:]))
            return
        rc, out, _ = run([work / binary], work)
        result["runs"][f"native_{tag}"] = {"exit": rc, "stdout": key_values(out)}

    native("o0_no_mir_inline", ["-C", "opt-level=0", "-Zinline-mir=no"])
    native("o3_mir_inline", ["-C", "opt-level=3", "-Zinline-mir=yes"])

    if tools["miri"]:
        base = [tools["miri"], "--sysroot", tools["miri_sysroot"], *EDITION]
        rc, out, err = run([*base, name], work)
        result["commands"]["miri_no_mir_opts"] = "miri --sysroot $MIRI_SYSROOT --edition 2021 " + name
        result["runs"]["miri_no_mir_opts"] = {"exit": rc, "stdout": key_values(out)}
        flags = ["-Zmir-opt-level=3", "-Zinline-mir=yes", "-Zdump-mir=direct_site", "-Zdump-mir-dir=miri_mir"]
        rc, out, err = run([*base, *flags, name], work)
        result["commands"]["miri_mir_inline"] = "miri --sysroot $MIRI_SYSROOT --edition 2021 " + " ".join(flags) + " " + name
        result["runs"]["miri_mir_inline"] = {"exit": rc, "stdout": key_values(out)}
        dumps = sorted((work / "miri_mir").glob("*direct_site*runtime-optimized.after.mir"))
        inlined = bool(dumps) and "(inlined #[track_caller] top_tracked)" in dumps[-1].read_text()
        checks.add(
            "regimes/miri_mir_inline/interpreted_body_is_inlined",
            inlined,
            "the MIR that Miri executed for `direct_site` contains `(inlined #[track_caller] top_tracked)`",
        )

    def line(marker):
        return mark[marker]

    expected = {
        "UNTRACKED_SELF": line("UNTRACKED_SELF"),
        "DIRECT": line("DIRECT_SITE"),
        "WRAPPER": line("WRAPPER_DEF_SITE"),
        "TRACKED_OUTER_WRAPPER": line("WRAPPER_DEF_SITE"),
        "FP1": line("FNPTR_DEF"),
        "FP2": line("FNPTR_DEF"),
        "FNPTR_DIRECT": line("FNPTR_DIRECT_CALL"),
        "DYN_DECL_TRACKED": line("DYN_DECL_TRACKED_CALL"),
        "DYN_PROVIDED": line("DYN_PROVIDED_CALL"),
        "DYN_IMPL_ONLY": line("IMPL_ONLY_DEF"),
        "STATIC_IMPL_ONLY": line("STATIC_IMPL_ONLY_CALL"),
        "GENERIC_STATIC": line("GENERIC_SITE"),
        "GENERIC_DYN": line("IMPL_ONLY_DEF"),
    }
    result["expected_lines"] = expected

    reference = None
    for tag, data in result["runs"].items():
        checks.eq(f"regimes/{tag}/exit", data["exit"], 0)
        observed = data["stdout"]
        for key, want in expected.items():
            got = observed.get(key, "missing")
            checks.eq(f"regimes/{tag}/{key}_line", got.split(":")[0], str(want))
        if reference is None:
            reference = observed
        else:
            checks.add(f"regimes/{tag}/identical_to_first_configuration", observed == reference, "line:column pairs agree")
    if reference:
        checks.eq("regimes/FP1_equals_FP2", reference.get("FP1"), reference.get("FP2"))
        checks.add(
            "regimes/wrapper_call_site_never_reported",
            str(line("WRAPPER_CALL_SITE")) not in {v.split(":")[0] for v in reference.values()},
        )
        checks.add(
            "regimes/tracked_outer_call_site_never_reported",
            str(line("TRACKED_OUTER_CALL_SITE")) not in {v.split(":")[0] for v in reference.values()},
        )
        checks.add(
            "regimes/dyn_impl_only_call_site_never_reported",
            str(line("DYN_IMPL_ONLY_CALL")) not in {v.split(":")[0] for v in reference.values()},
        )
    result["reference_output"] = reference
    return result


# --------------------------------------------------------------------------------------------
# B. MIR evidence: scope trees after inlining, and the reify shim body
# --------------------------------------------------------------------------------------------

SCOPE_RE = re.compile(
    r"^\s*scope (\d+)(?: \(inlined (#\[track_caller\] )?(.+?)\))? \{(?:\s*// at \S+?:(\d+):(\d+): \d+:\d+)?\s*$"
)
INTRINSIC_RE = re.compile(r"=\s*caller_location\(\).*?// scope (\d+) at")


def mir_function(text: str, fn_name: str):
    match = re.search(r"^fn " + re.escape(fn_name) + r"\(.*?^}\n", text, re.S | re.M)
    return match.group(0) if match else None


def scope_table(fn_text: str):
    """Recover `inlined` and `inlined_parent_scope` for every scope of a pretty-printed body."""
    table = {0: {"inlined": None, "inlined_parent_scope": None, "parent_scope": None}}
    stack = [0]
    for line in fn_text.splitlines():
        if re.match(r"^\s*bb\d+", line):
            break
        match = SCOPE_RE.match(line)
        if match:
            scope = int(match.group(1))
            inlined = None
            if match.group(3) is not None:
                inlined = {
                    "callee": match.group(3),
                    "requires_caller_location": match.group(2) is not None,
                    "callsite": f"{match.group(4)}:{match.group(5)}" if match.group(4) else None,
                }
            parent = stack[-1]
            # Nearest strict ancestor that is the root of an inlined body.
            nearest, cursor = None, parent
            while cursor is not None:
                if table[cursor]["inlined"] is not None:
                    nearest = cursor
                    break
                cursor = table[cursor]["parent_scope"]
            table[scope] = {"inlined": inlined, "inlined_parent_scope": nearest, "parent_scope": parent}
            stack.append(scope)
        elif line.strip() == "}" and len(stack) > 1:
            stack.pop()
    return table


def caller_location_span(table, scope, span, caller_location):
    """Python transcription of `rustc_middle::mir::Body::caller_location_span`."""
    while True:
        data = table[scope]
        if data["inlined"] is not None:
            if not data["inlined"]["requires_caller_location"]:
                return span
            span = data["inlined"]["callsite"]
        if data["inlined_parent_scope"] is None:
            break
        scope = data["inlined_parent_scope"]
    return caller_location if caller_location is not None else span


def strip_comments(fn_text: str):
    body = []
    seen_block = False
    for line in fn_text.splitlines():
        line = re.sub(r"\s*//.*$", "", line).rstrip()
        if re.match(r"^\s*bb\d+", line):
            seen_block = True
        if seen_block and line.strip():
            body.append(line)
    return body


def mir_evidence(tools, work, scrub, checks, regimes):
    name = "track_caller_probe.rs"
    mark = regimes["markers"]
    reference = regimes.get("reference_output") or {}
    result = {}

    flags = ["-C", "opt-level=3", "-Zinline-mir=yes", "-Zmir-include-spans=on", "--emit=mir", "-o", "inlined.mir"]
    rc, _, err = run([tools["rustc"], *EDITION, *flags, name], work)
    result["command_inlined"] = "rustc --edition 2021 " + " ".join(flags) + " " + name
    if not checks.add("mir/inlined/emits", rc == 0, scrub(err[-400:])):
        return result
    inlined = (work / "inlined.mir").read_text()

    bodies = {}
    for fn_name, output_key in (
        ("direct_site", "DIRECT"),
        ("wrapper_site", "WRAPPER"),
        ("tracked_outer_site", "TRACKED_OUTER_WRAPPER"),
    ):
        text = mir_function(inlined, fn_name)
        if not checks.add(f"mir/inlined/{fn_name}/present", text is not None):
            continue
        table = scope_table(text)
        intrinsic = INTRINSIC_RE.search(text)
        checks.add(f"mir/inlined/{fn_name}/caller_location_intrinsic_call_survives", intrinsic is not None)
        checks.add(f"mir/inlined/{fn_name}/no_residual_call_to_top_tracked", "top_tracked()" not in text)
        predicted = None
        if intrinsic:
            # The intrinsic's own span lies in the standard library; it is overwritten by the first
            # tracked call site, so a placeholder suffices. These bodies are untracked functions.
            predicted = caller_location_span(table, int(intrinsic.group(1)), "<intrinsic>", None)
            checks.eq(f"mir/inlined/{fn_name}/scope_walk_predicts_executed_output", predicted, reference.get(output_key))
        chain = [
            {
                "scope": scope,
                "inlined_callee": data["inlined"]["callee"] if data["inlined"] else None,
                "requires_caller_location": data["inlined"]["requires_caller_location"] if data["inlined"] else None,
                "callsite_line_col": data["inlined"]["callsite"] if data["inlined"] else None,
                "inlined_parent_scope": data["inlined_parent_scope"],
            }
            for scope, data in sorted(table.items())
        ]
        bodies[fn_name] = {
            "pretty_mir": scrub(text),
            "scopes": chain,
            "intrinsic_scope": int(intrinsic.group(1)) if intrinsic else None,
            "scope_walk_prediction": predicted,
        }
    result["inlined_bodies"] = bodies

    direct, wrapper = mir_function(inlined, "direct_site"), mir_function(inlined, "wrapper_site")
    if direct and wrapper:
        checks.add(
            "mir/inlined/direct_and_wrapper_blocks_identical_modulo_scopes",
            strip_comments(direct) == strip_comments(wrapper),
            "the two bodies differ only in their scope trees",
        )
        wrapper_scopes = [row for row in bodies.get("wrapper_site", {}).get("scopes", []) if row["inlined_callee"]]
        outer = wrapper_scopes[0] if wrapper_scopes else {}
        checks.add(
            "mir/inlined/wrapper_outermost_inlined_scope_is_untracked_wrapper",
            outer.get("inlined_callee") == "untracked_wrapper" and outer.get("requires_caller_location") is False,
        )
        checks.eq(
            "mir/inlined/wrapper_scope_callsite_is_wrapper_call_site",
            (outer.get("callsite_line_col") or "").split(":")[0],
            str(mark["WRAPPER_CALL_SITE"]),
        )

    flags = ["-C", "opt-level=0", "-Zinline-mir=no", "--emit=mir", "-o", "plain.mir"]
    rc, _, err = run([tools["rustc"], *EDITION, *flags, name], work)
    result["command_not_inlined"] = "rustc --edition 2021 " + " ".join(flags) + " " + name
    if checks.add("mir/not_inlined/emits", rc == 0, scrub(err[-400:])):
        text = mir_function((work / "plain.mir").read_text(), "direct_site") or ""
        checks.add("mir/not_inlined/direct_site_calls_top_tracked", "top_tracked()" in text and "inlined" not in text)
        result["not_inlined_direct_site"] = scrub(text)

    flags = [
        "-C", "opt-level=3", "-Zmir-include-spans=on",
        "-Zdump-mir=leaf_tracked_noinline", "-Zdump-mir-dir=shim_mir", "-o", "shim_bin",
    ]
    rc, _, err = run([tools["rustc"], *EDITION, *flags, name], work)
    result["command_shim"] = "rustc --edition 2021 " + " ".join(flags) + " " + name
    dumps = sorted((work / "shim_mir").glob("*make_shim.after.mir")) if rc == 0 else []
    if checks.add("mir/shim/dump_present", bool(dumps), scrub(err[-300:])):
        text = dumps[0].read_text()
        calls = re.findall(r"= leaf_tracked_noinline\(\) -> .*?// scope 0 at \S+?:(\d+):(\d+): (\d+):(\d+)", text)
        checks.eq("mir/shim/single_direct_call", len(calls), 1)
        if calls:
            checks.eq("mir/shim/call_span_is_definition_header_line", int(calls[0][0]), mark["FNPTR_DEF"])
            checks.eq("mir/shim/call_span_starts_at_column_one", int(calls[0][1]), 1)
        checks.add("mir/shim/no_inlined_scope", "inlined" not in text)
        result["reify_shim_mir"] = scrub(text)
        result["reify_shim_dump_file"] = dumps[0].name
    return result


# --------------------------------------------------------------------------------------------
# C. ABI evidence: emitted assembly and disassembled object code
# --------------------------------------------------------------------------------------------

ESCAPES = {"n": 10, "t": 9, "r": 13, "f": 12, "b": 8, "\\": 92, '"': 34}


def decode_c_string(literal: str) -> bytes:
    out, i = bytearray(), 0
    while i < len(literal):
        char = literal[i]
        if char != "\\":
            out.append(ord(char))
            i += 1
            continue
        nxt = literal[i + 1]
        if nxt in "01234567":
            j = i + 1
            while j < len(literal) and j < i + 4 and literal[j] in "01234567":
                j += 1
            out.append(int(literal[i + 1:j], 8) & 0xFF)
            i = j
        else:
            out.append(ESCAPES[nxt])
            i += 2
    return bytes(out)


def parse_assembly(text: str):
    """Split AT&T assembly into function bodies and data objects (bytes with symbolic quads)."""
    functions, data = {}, {}
    current, kind = None, None
    for raw in text.splitlines():
        line = raw.strip()
        label = re.match(r"^([A-Za-z_.$][\w.$]*):$", line)
        if label:
            name = label.group(1)
            if name.startswith(".Lfunc_end") or name.startswith(".Lcfi") or name.startswith(".Ltmp"):
                current = None
            elif name.startswith(".L"):
                current, kind = name, "data"
                data[name] = []
            else:
                current, kind = name, "fn"
                functions[name] = []
            continue
        if current is None or not line:
            continue
        if kind == "fn":
            if line.startswith(".") and not line.startswith(".L"):
                continue  # directives such as .cfi_startproc
            functions[current].append(line)
            continue
        directive = re.match(r"^\.(\w+)\s*(.*)$", line)
        if not directive:
            continue
        op, operand = directive.group(1), directive.group(2).strip()
        if op in ("asciz", "ascii"):
            payload = decode_c_string(operand[1:-1]) + (b"\0" if op == "asciz" else b"")
            data[current].append(("bytes", payload))
        elif op == "quad":
            if re.fullmatch(r"-?\d+", operand):
                data[current].append(("bytes", int(operand).to_bytes(8, "little", signed=int(operand) < 0)))
            else:
                data[current].append(("symbol", operand))
        elif op == "long":
            data[current].append(("bytes", (int(operand) & 0xFFFFFFFF).to_bytes(4, "little")))
        elif op == "byte":
            data[current].append(("bytes", (int(operand) & 0xFF).to_bytes(1, "little")))
        elif op == "zero":
            data[current].append(("bytes", b"\0" * int(operand.split(",")[0])))
        elif op in ("section", "text", "data"):
            current = None
    return functions, data


def flat_bytes(items):
    return b"".join(payload for tag, payload in items if tag == "bytes")


def decode_location(data, label):
    """Decode a `core::panic::Location` constant: file pointer, file length, line, column."""
    items = data.get(label)
    if not items or items[0][0] != "symbol":
        return None
    payload = flat_bytes(items[1:])
    if len(payload) < 16:
        return None
    file_items = data.get(items[0][1], [])
    file_name = flat_bytes(file_items).split(b"\0")[0].decode("utf-8", "replace")
    return {
        "label": label,
        "file": file_name,
        "file_len": int.from_bytes(payload[0:8], "little"),
        "line": int.from_bytes(payload[8:12], "little"),
        "column": int.from_bytes(payload[12:16], "little"),
        "size_bytes": 8 + len(payload),
    }


def shim_suffix(symbol: str):
    """Disambiguator of a v0-mangled shim symbol (`_RNS...<len><suffix>`), or `None`."""
    match = re.match(r"^_RNS\w*?\d+(reify(?:_fnptr|_vtable)?)$", symbol)
    return match.group(1) if match else None


def find_symbol(names, pattern):
    hits = [name for name in names if re.search(pattern, name)]
    return hits[0] if len(hits) == 1 else None


def parse_objdump(text: str):
    functions, current = {}, None
    for line in text.splitlines():
        header = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
        if header:
            current = header.group(1)
            functions[current] = []
            continue
        if current is None:
            continue
        instruction = re.match(r"^\s*[0-9a-f]+:\s+(.*)$", line)
        if instruction and instruction.group(1).strip():
            functions[current].append(re.sub(r"\s+", " ", instruction.group(1).strip()))
    return functions


def abi_evidence(tools, work, scrub, checks):
    name = "abi_probe.rs"
    mark = markers((work / name).read_text())
    result = {"markers": mark}
    flags = [
        "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "debuginfo=0",
        "-C", "symbol-mangling-version=v0", "--emit=asm,obj", "--out-dir", "abi_out",
    ]
    rc, _, err = run([tools["rustc"], *EDITION, *flags, name], work)
    result["command"] = "rustc --edition 2021 " + " ".join(flags) + " " + name
    if not checks.add("abi/compiles", rc == 0, scrub(err[-400:])):
        return result
    asm_functions, asm_data = parse_assembly((work / "abi_out" / "abi_probe.s").read_text())
    rc, dis, err = run([tools["objdump"], "-d", "-r", "--no-show-raw-insn", "abi_out/abi_probe.o"], work)
    result["objdump_command"] = "objdump -d -r --no-show-raw-insn abi_out/abi_probe.o"
    if not checks.add("abi/objdump_runs", rc == 0, scrub(err[-300:])):
        return result
    obj_functions = parse_objdump(dis)
    names = list(asm_functions)

    def plain(item):
        return find_symbol(names, rf"(?<!\d){len(item)}{item}$")

    def shim(item):
        return find_symbol(names, rf"(?<!\d){len(item)}{item}5reify$")

    symbols = {
        "abi_tracked0": plain("abi_tracked0"),
        "abi_tracked1": plain("abi_tracked1"),
        "abi_tracked2": plain("abi_tracked2"),
        "abi_tracked6": plain("abi_tracked6"),
        "abi_untracked1": plain("abi_untracked1"),
        "call_tracked0": plain("call_tracked0"),
        "call_tracked1": plain("call_tracked1"),
        "call_tracked2": plain("call_tracked2"),
        "forward_tracked1": plain("forward_tracked1"),
        "call_through_pointer": plain("call_through_pointer"),
        "reify0": plain("reify0"),
        "reify1": plain("reify1"),
        "reify2": plain("reify2"),
        "reify_untracked1": plain("reify_untracked1"),
        "virtual_call_decl_tracked": plain("virtual_call_decl_tracked"),
        "virtual_call_decl_untracked": plain("virtual_call_decl_untracked"),
        "make_dyn_decl_tracked": plain("make_dyn_decl_tracked"),
        "make_dyn_decl_untracked": plain("make_dyn_decl_untracked"),
        "abi_tracked0::{shim:reify}": shim("abi_tracked0"),
        "abi_tracked1::{shim:reify}": shim("abi_tracked1"),
        "abi_tracked2::{shim:reify}": shim("abi_tracked2"),
        "<A as DeclTracked>::m": find_symbol(names, r"11DeclTracked1m$"),
        "<B as DeclUntracked>::m": find_symbol(names, r"13DeclUntracked1m$"),
        "<B as DeclUntracked>::m::{shim:reify}": find_symbol(names, r"13DeclUntracked1m5reify$"),
    }
    result["symbols"] = symbols
    for label, symbol in symbols.items():
        checks.add(f"abi/symbol_found/{label}", symbol is not None)
    checks.add("abi/no_shim_symbol_for_untracked_function", shim("abi_untracked1") is None)
    checks.add("abi/no_shim_symbol_for_decl_tracked_impl", find_symbol(names, r"11DeclTracked1m5reify$") is None)

    def asm(label):
        return asm_functions.get(symbols.get(label) or "", [])

    def obj(label):
        return obj_functions.get(symbols.get(label) or "", [])

    result["assembly"] = {label: asm(label) for label in symbols}
    result["disassembly"] = {label: obj(label) for label in symbols}

    # C.1 Callee side: which register is dereferenced to read `Location::line` (offset 16)?
    def line_field_registers(label):
        return sorted(set(re.findall(r"0x10\(%(\w+)\)", " ".join(obj(label)))))

    expectations = {
        "abi_tracked0": ["rdi"],
        "abi_tracked1": ["rsi"],
        "abi_tracked2": ["rdx"],
        "<A as DeclTracked>::m": ["rdx"],
        "<B as DeclUntracked>::m": ["rdx"],
    }
    callee_registers = {}
    for label, want in expectations.items():
        got = line_field_registers(label)
        callee_registers[label] = got
        checks.eq(f"abi/callee/{label}/location_pointer_register", got, want)
    stack_load = re.search(r"mov 0x8\(%rsp\),%(\w+)", " ".join(obj("abi_tracked6")))
    got6 = line_field_registers("abi_tracked6")
    callee_registers["abi_tracked6"] = {"loaded_from": "0x8(%rsp)" if stack_load else None, "dereferenced": got6}
    checks.add(
        "abi/callee/abi_tracked6/location_pointer_is_first_stack_argument",
        bool(stack_load) and got6 == [stack_load.group(1)],
        "seventh integer-class argument: read from 8(%rsp), then dereferenced at offset 16",
    )
    checks.eq("abi/callee/abi_untracked1/no_location_dereference", line_field_registers("abi_untracked1"), [])
    result["callee_location_registers"] = callee_registers

    # C.2 Caller side and shims: which register receives the address of which `Location` constant?
    def location_loads(label):
        loads = []
        for instruction in asm(label):
            match = re.match(r"leaq\s+(\.Lanon\.[\w.]+)\(%rip\),\s*%(\w+)", instruction)
            if match:
                decoded = decode_location(asm_data, match.group(1))
                if decoded and decoded["file"].endswith(".rs"):
                    loads.append({"register": match.group(2), **decoded})
        return loads

    def references(label, symbol):
        return bool(symbol) and any(symbol in instruction for instruction in asm(label))

    callers = {}
    for label, register, marker, column in (
        ("abi_tracked0::{shim:reify}", "rdi", "ABI0_DEF", 1),
        ("abi_tracked1::{shim:reify}", "rsi", "ABI1_DEF", 1),
        ("abi_tracked2::{shim:reify}", "rdx", "ABI2_DEF", 1),
        ("<B as DeclUntracked>::m::{shim:reify}", "rdx", "IMPL_ONLY_DEF", 5),
        ("call_tracked0", "rdi", "CALL0_SITE", 5),
        ("call_tracked1", "rsi", "CALL1_SITE", 5),
        ("call_tracked2", "rdx", "CALL2_SITE", 5),
    ):
        loads = location_loads(label)
        callers[label] = loads
        ok = len(loads) == 1
        checks.add(f"abi/caller/{label}/materialises_exactly_one_location_constant", ok)
        if ok:
            checks.eq(f"abi/caller/{label}/register", loads[0]["register"], register)
            checks.eq(f"abi/caller/{label}/line", loads[0]["line"], mark[marker])
            checks.eq(f"abi/caller/{label}/column", loads[0]["column"], column)
            checks.eq(f"abi/caller/{label}/constant_size_bytes", loads[0]["size_bytes"], 24)
    for label, target in (
        ("abi_tracked0::{shim:reify}", "abi_tracked0"),
        ("abi_tracked1::{shim:reify}", "abi_tracked1"),
        ("abi_tracked2::{shim:reify}", "abi_tracked2"),
        ("<B as DeclUntracked>::m::{shim:reify}", "<B as DeclUntracked>::m"),
    ):
        checks.add(f"abi/shim/{label}/transfers_to_tracked_callee", references(label, symbols.get(target)))
    result["location_constants_loaded"] = callers

    loads = location_loads("virtual_call_decl_tracked")
    callers["virtual_call_decl_tracked"] = loads
    checks.add(
        "abi/virtual/decl_tracked_call_site_passes_its_own_location",
        len(loads) == 1 and loads[0]["line"] == mark["VCALL_TRACKED_SITE"],
        f"loads={loads}",
    )
    checks.eq("abi/virtual/decl_untracked_call_site_passes_no_location", location_loads("virtual_call_decl_untracked"), [])
    checks.eq("abi/forward/tracked_caller_materialises_no_constant", location_loads("forward_tracked1"), [])
    checks.add("abi/forward/tracked_caller_transfers_to_callee", references("forward_tracked1", symbols.get("abi_tracked1")))
    checks.eq("abi/pointer_call/passes_no_location", location_loads("call_through_pointer"), [])
    checks.add(
        "abi/pointer_call/is_indirect",
        any(re.match(r"(jmp|call)q?\s+\*%", instruction) for instruction in asm("call_through_pointer")),
    )

    # C.3 Reification results and vtable contents.
    for index in (0, 1, 2):
        checks.add(
            f"abi/reify/reify{index}_returns_shim_address",
            references(f"reify{index}", symbols.get(f"abi_tracked{index}::{{shim:reify}}")),
        )
    checks.add("abi/reify/untracked_returns_function_itself", references("reify_untracked1", symbols.get("abi_untracked1")))

    def vtable_methods(label):
        for instruction in asm(label):
            match = re.match(r"leaq\s+(\.Lanon\.[\w.]+)\(%rip\)", instruction)
            if match:
                return [payload for tag, payload in asm_data.get(match.group(1), []) if tag == "symbol"]
        return []

    tracked_vtable = vtable_methods("make_dyn_decl_tracked")
    untracked_vtable = vtable_methods("make_dyn_decl_untracked")
    result["vtable_method_entries"] = {"A as DeclTracked": tracked_vtable, "B as DeclUntracked": untracked_vtable}
    checks.eq("abi/vtable/decl_tracked_slot_is_impl_itself", tracked_vtable, [symbols.get("<A as DeclTracked>::m")])
    checks.eq(
        "abi/vtable/impl_only_slot_is_reify_shim",
        untracked_vtable,
        [symbols.get("<B as DeclUntracked>::m::{shim:reify}")],
    )

    # C.4 Symbol suffixes when KCFI makes `ReifyReason` observable. Assembly only; never executed.
    flags = [
        "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "debuginfo=0",
        "-C", "symbol-mangling-version=v0", "-Zsanitizer=kcfi", "-C", "panic=abort",
        "-Cunsafe-allow-abi-mismatch=sanitizer", "--emit=asm", "--out-dir", "kcfi_out",
    ]
    rc, _, err = run([tools["rustc"], *EDITION, *flags, name], work)
    kcfi = {"command": "rustc --edition 2021 " + " ".join(flags) + " " + name, "exit": rc}
    if rc == 0:
        kcfi_functions, _ = parse_assembly((work / "kcfi_out" / "abi_probe.s").read_text())
        counts = {}
        for symbol in kcfi_functions:
            suffix = shim_suffix(symbol)
            if suffix:
                counts[suffix] = counts.get(suffix, 0) + 1
        kcfi["shim_symbol_suffix_counts"] = counts
        checks.eq("kcfi/shim_suffixes", counts, {"reify_fnptr": 3, "reify_vtable": 1})
    else:
        kcfi["note"] = "KCFI assembly emission is not available with this toolchain or target"
        kcfi["stderr_tail"] = scrub(err[-300:])
    plain_counts = {}
    for symbol in names:
        suffix = shim_suffix(symbol)
        if suffix:
            plain_counts[suffix] = plain_counts.get(suffix, 0) + 1
    result["shim_symbol_suffix_counts"] = plain_counts
    checks.eq("abi/shim_suffixes_without_kcfi", plain_counts, {"reify": 4})
    result["kcfi"] = kcfi
    return result


# --------------------------------------------------------------------------------------------
# D. Front-end acceptance matrix
# --------------------------------------------------------------------------------------------

COMPILE_MATRIX = {
    "extern_c_fn.rs": {"codes": ["E0737"]},
    "extern_rust_call_fn.rs": {"codes": ["E0737"]},
    "explicit_extern_rust_fn.rs": {"accepted": True},
    "main_fn.rs": {"message": "`main` function is not allowed to be `#[track_caller]`"},
    "foreign_block_c.rs": {"codes": ["E0737"]},
    "foreign_block_rust.rs": {"accepted": True},
    "naked_fn.rs": {"codes": ["E0736"]},
    "closure_without_feature.rs": {"codes": ["E0658"]},
    "struct_item.rs": {"rejected": True},
    "tail_call_from_tracked.rs": {"message": "cannot perform a tail-call"},
    "trait_decl_and_impl.rs": {"accepted": True},
}


def compile_matrix(tools, work, scrub, checks):
    result = {}
    for file_name, want in COMPILE_MATRIX.items():
        cmd = [tools["rustc"], *EDITION, "--error-format=json", "--emit=metadata", "--out-dir", "matrix_out",
               f"compile_matrix/{file_name}"]
        rc, _, err = run(cmd, work)
        errors = []
        for line in err.splitlines():
            try:
                diagnostic = json.loads(line)
            except ValueError:
                continue
            if diagnostic.get("level") == "error" and not diagnostic.get("message", "").startswith("aborting due to"):
                code = (diagnostic.get("code") or {}).get("code")
                errors.append({"code": code, "message": scrub(diagnostic.get("message", ""))})
        result[file_name] = {"exit": rc, "errors": errors}
        codes = [e["code"] for e in errors if e["code"]]
        if want.get("accepted"):
            checks.add(f"compile_matrix/{file_name}/accepted", rc == 0 and not errors, f"errors={errors}")
        if want.get("rejected"):
            checks.add(f"compile_matrix/{file_name}/rejected", rc != 0 and bool(errors), f"errors={errors}")
        for code in want.get("codes", []):
            checks.add(f"compile_matrix/{file_name}/{code}", rc != 0 and code in codes, f"codes={codes}")
        if "message" in want:
            checks.add(
                f"compile_matrix/{file_name}/message",
                rc != 0 and any(want["message"] in e["message"] for e in errors),
                f"errors={errors}",
            )
    result["command_template"] = "rustc --edition 2021 --error-format=json --emit=metadata --out-dir matrix_out compile_matrix/<file>"
    return result


# --------------------------------------------------------------------------------------------
# E-G. Declaration mismatch, closures, tail calls
# --------------------------------------------------------------------------------------------


def miri_run(tools, work, file_name, extra=()):
    return run([tools["miri"], "--sysroot", tools["miri_sysroot"], *EDITION, *extra, file_name], work)


def extern_declarations(tools, work, scrub, checks):
    result = {}
    name = "extern_decl_match.rs"
    mark = markers((work / name).read_text())
    rc, _, err = run([tools["rustc"], *EDITION, "-C", "opt-level=0", "-o", "decl_match", name], work)
    runs = {}
    if checks.add("extern_decl/match/compiles", rc == 0, scrub(err[-300:])):
        rc, out, _ = run([work / "decl_match"], work)
        runs["native"] = key_values(out)
    if tools["miri"]:
        rc, out, _ = miri_run(tools, work, name)
        runs["miri"] = key_values(out)
    for tag, observed in runs.items():
        checks.eq(f"extern_decl/match/{tag}/reports_call_site", observed.get("EXTERN_DECL_MATCH"), str(mark["EXTERN_DECL_CALL"]))
    result["match"] = {"markers": mark, "runs": runs}

    name = "extern_decl_mismatch_interpreter_only.rs"
    mark = markers((work / name).read_text())
    mismatch = {"markers": mark, "native": "deliberately not executed: undefined behaviour"}
    if tools["miri"]:
        rc, out, err = miri_run(tools, work, name)
        observed = key_values(out)
        if rc == 0 and observed.get("MISMATCH_NOT_DETECTED") == str(mark["MISMATCH_CALL"]):
            outcome = "not_detected_reports_call_site_of_mismatched_declaration"
        elif rc != 0 and "Undefined Behavior" in err:
            outcome = "undefined_behaviour_reported"
        else:
            outcome = "other"
        first_error = next((l for l in err.splitlines() if l.startswith("error")), "")
        mismatch["miri"] = {"exit": rc, "stdout": observed, "outcome": outcome, "first_error_line": scrub(first_error)}
        checks.add(
            "extern_decl/mismatch/miri_outcome_classified",
            outcome != "other",
            f"outcome={outcome}",
        )
    result["mismatch"] = mismatch
    return result


def closures(tools, work, scrub, checks):
    name = "closure_probe.rs"
    mark = markers((work / name).read_text())
    runs = {}
    for tag, flags in (("native_o0", ["-C", "opt-level=0"]), ("native_o3", ["-C", "opt-level=3", "-Zinline-mir=yes"])):
        rc, _, err = run([tools["rustc"], *EDITION, *flags, "-o", f"closure_{tag}", name], work)
        if checks.add(f"closures/{tag}/compiles", rc == 0, scrub(err[-300:])):
            rc, out, _ = run([work / f"closure_{tag}"], work)
            runs[tag] = key_values(out)
    if tools["miri"]:
        rc, out, _ = miri_run(tools, work, name)
        runs["miri"] = key_values(out)

    fn_trait_lines = {}
    library = Path(tools["sysroot"]) / "lib/rustlib/src/rust/library/core/src/ops/function.rs"
    if library.exists():
        for number, line in enumerate(library.read_text().splitlines(), start=1):
            for method in ("call", "call_mut", "call_once"):
                if re.search(rf'extern "rust-call" fn {method}\(', line):
                    fn_trait_lines.setdefault(method, number)
    for tag, observed in runs.items():
        checks.eq(f"closures/{tag}/direct", observed.get("CLOSURE_DIRECT"), f"{name}:{mark['CLOSURE_DIRECT_SITE']}")
        checks.eq(f"closures/{tag}/generic_fn", observed.get("CLOSURE_GENERIC_FN"), f"{name}:{mark['CLOSURE_GENERIC_FN_SITE']}")
        checks.eq(f"closures/{tag}/generic_once", observed.get("CLOSURE_GENERIC_ONCE"), f"{name}:{mark['CLOSURE_GENERIC_ONCE_SITE']}")
        for key, method in (("CLOSURE_DYN", "call"), ("CLOSURE_BOX_ONCE", "call_once")):
            value = observed.get(key, "")
            checks.add(f"closures/{tag}/{key}_points_into_core_ops_function_rs", value.startswith("ops/function.rs:"), value)
            if method in fn_trait_lines:
                checks.eq(f"closures/{tag}/{key}_is_Fn_trait_method_declaration", value, f"ops/function.rs:{fn_trait_lines[method]}")
    return {"markers": mark, "runs": runs, "fn_trait_method_declaration_lines": fn_trait_lines}


def tail_calls(tools, work, scrub, checks):
    name = "tail_call_probe.rs"
    mark = markers((work / name).read_text())
    runs, warnings = {}, {}
    for tag, flags in (("native_o0", ["-C", "opt-level=0"]), ("native_o3", ["-C", "opt-level=3"])):
        rc, _, err = run([tools["rustc"], *EDITION, "--error-format=short", *flags, "-o", f"tail_{tag}", name], work)
        if checks.add(f"tail_call/{tag}/compiles", rc == 0, scrub(err[-300:])):
            warnings[tag] = [scrub(l) for l in err.splitlines() if "tail calling" in l]
            checks.add(f"tail_call/{tag}/lint_emitted", bool(warnings[tag]), str(warnings[tag]))
            rc, out, _ = run([work / f"tail_{tag}"], work)
            runs[tag] = key_values(out)
            checks.eq(f"tail_call/{tag}/reports_definition_of_callee", runs[tag].get("TAIL_CALL"), str(mark["TAIL_TARGET_DEF"]))
            checks.eq(f"tail_call/{tag}/plain_call_reports_call_site", runs[tag].get("PLAIN_CALL"), str(mark["PLAIN_CALL_SITE"]))
    result = {"markers": mark, "runs": runs, "warnings": warnings}
    if tools["miri"]:
        rc, out, _ = miri_run(tools, work, name)
        observed = key_values(out)
        runs["miri"] = observed
        value = observed.get("TAIL_CALL")
        outcome = {
            str(mark["TAIL_TARGET_DEF"]): "definition_of_callee",
            str(mark["TAIL_CALL_SITE"]): "tail_call_site",
            str(mark["TAIL_CALLER_CALL_SITE"]): "call_site_of_the_tail_calling_function",
        }.get(value, "other")
        result["miri_tail_call_outcome"] = outcome
        checks.add("tail_call/miri/outcome_classified", outcome != "other", f"TAIL_CALL={value} -> {outcome}")
        checks.eq("tail_call/miri/plain_call_reports_call_site", observed.get("PLAIN_CALL"), str(mark["PLAIN_CALL_SITE"]))
    return result


# --------------------------------------------------------------------------------------------
# Driver
# --------------------------------------------------------------------------------------------


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", default="-", help="output JSON file (default: stdout)")
    parser.add_argument("--rustc")
    parser.add_argument("--miri")
    parser.add_argument("--miri-sysroot")
    parser.add_argument("--objdump")
    parser.add_argument("--skip-miri", action="store_true")
    args = parser.parse_args(argv)

    try:
        if not SRC.is_dir():
            raise Setup(f"missing probe sources directory: {SRC.name}/")
        tools = discover(args)
        scrub = Scrubber()
        checks = Checks()
        with tempfile.TemporaryDirectory(prefix="track_caller_probe_") as tmp:
            work = Path(tmp)
            shutil.copytree(SRC, work, dirs_exist_ok=True)
            scrub.add(tmp, "$WORK")
            scrub.add(tools["sysroot"], "$SYSROOT")
            scrub.add(tools.get("miri_sysroot"), "$MIRI_SYSROOT")
            scrub.add(os.path.expanduser("~"), "$HOME")

            document = {
                "probe": "probe_track_caller_abi_and_shims",
                "toolchain": {
                    "rustc_verbose": tools["rustc_verbose"],
                    "miri_version": tools.get("miri_version"),
                    "objdump_version": tools["objdump_version"],
                    "miri_runs": bool(tools["miri"]),
                },
            }
            document["regime_matrix"] = regime_matrix(tools, work, scrub, checks)
            document["mir"] = mir_evidence(tools, work, scrub, checks, document["regime_matrix"])
            document["abi"] = abi_evidence(tools, work, scrub, checks)
            document["compile_matrix"] = compile_matrix(tools, work, scrub, checks)
            document["extern_declarations"] = extern_declarations(tools, work, scrub, checks)
            document["closures"] = closures(tools, work, scrub, checks)
            document["tail_calls"] = tail_calls(tools, work, scrub, checks)

        failed = [item["name"] for item in checks.items if not item["pass"]]
        document["checks"] = checks.items
        document["summary"] = {
            "total_checks": len(checks.items),
            "passed": len(checks.items) - len(failed),
            "failed": failed,
            "all_checks_passed": not failed,
        }
        text = scrub(json.dumps(document, indent=2, sort_keys=True)) + "\n"
        scrub.verify(text)
    except Setup as problem:
        print(f"probe setup problem: {problem}", file=sys.stderr)
        return 2

    if args.out == "-":
        sys.stdout.write(text)
    else:
        Path(args.out).write_text(text)
    print(
        f"checks: {document['summary']['passed']}/{document['summary']['total_checks']} passed",
        file=sys.stderr,
    )
    for name in failed:
        print(f"FAILED: {name}", file=sys.stderr)
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
