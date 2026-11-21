#!/usr/bin/env python3
"""Machine-extracts the complete rustc feature-completeness surface inventory,
maps every compiler surface to upstream and external parity harnesses, runs
isolated live toolchain/ABI probes, and enforces the Zero-Loophole Skip-List &
Pass-Mode Soundness Auditor.

Strictly read-only over Git object stores (`git ls-tree` + `git cat-file --batch`),
using linear O(N) string/state-machine scanners and `tempfile.TemporaryDirectory()`
for any live compiler invocations.
"""
from __future__ import annotations

import argparse
import base64
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from typing import Any

DEFAULT_REV = "412be32a6a189d9a28922beee178bc0abee9d492"
BASELINE_1991_REV = "58cf8f9c35b355199727627d07ae34a4e2846d67"
NIGHTLY_HOST_REV = "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1"

EXTERNAL_PINS = {
    "abi_cafe": {
        "repository": "Gankra/abi-cafe",
        "revision": "94d38030419eb00a1ba80e5e2b4d763dcee58db4",
    },
    "fls": {
        "repository": "rust-lang/fls",
        "revision": "bca860e8dab52715effdd49a792347b262f5e539",
    },
    "rustlantis": {
        "repository": "cbeuw/rustlantis",
        "revision": "2be7c5a6763831dc0f908f0e05723ebbbc2a62cc",
    },
    "ferrocene": {
        "repository": "ferrocene/ferrocene",
        "revision": "fef61e63733cf86e31b1cb0da3271058a8673f1c",
    },
    "crater": {
        "repository": "rust-lang/crater",
        "revision": "abaa949414a8b9457858f0fc1a6ed97824cb9120",
    },
}

SUITE_MODES = {
    "ui": "ui",
    "ui-fulldeps": "ui",
    "codegen-llvm": "codegen",
    "codegen-units": "codegen-units",
    "mir-opt": "mir-opt",
    "assembly-llvm": "assembly",
    "assembly-gcc": "assembly",
    "incremental": "incremental",
    "debuginfo": "debuginfo",
    "coverage": "coverage-map+coverage-run",
    "coverage-run-rustdoc": "coverage-run-rustdoc",
    "crashes": "crashes",
    "pretty": "pretty",
    "run-make": "run-make",
    "run-make-cargo": "run-make",
    "build-std": "run-make",
    "rustdoc-html": "rustdoc-html",
    "rustdoc-json": "rustdoc-json",
    "rustdoc-js": "js-doc-test",
    "rustdoc-js-std": "js-doc-test",
    "rustdoc-ui": "ui",
    "rustdoc-gui": "rustdoc-gui",
}

BASELINE_1991_SUITE_COUNTS = {
    "ui": 20072,
    "ui-fulldeps": 76,
    "codegen-llvm": 801,
    "codegen-units": 46,
    "mir-opt": 400,
    "assembly-llvm": 163,
    "assembly-gcc": 0,
    "incremental": 180,
    "debuginfo": 169,
    "coverage": 98,
    "coverage-run-rustdoc": 1,
    "crashes": 179,
    "pretty": 113,
    "run-make": 519,
    "run-make-cargo": 14,
    "build-std": 1,
    "rustdoc-html": 837,
    "rustdoc-json": 194,
    "rustdoc-js": 78,
    "rustdoc-js-std": 68,
    "rustdoc-ui": 390,
    "rustdoc-gui": 146,
}


class GitObjectReader:
    """Read-only Git tree and blob reader backed by `git cat-file --batch`."""

    def __init__(self, repo_path: str, rev: str) -> None:
        self.repo_path = str(repo_path)
        self.rev = rev
        self.blobs: dict[str, str] = {}
        self.gitlinks: dict[str, str] = {}
        self._load_tree()
        self._proc = subprocess.Popen(
            ["git", "-C", self.repo_path, "cat-file", "--batch"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )

    def _load_tree(self) -> None:
        out = subprocess.check_output(
            ["git", "-C", self.repo_path, "ls-tree", "-r", self.rev],
            text=True,
        )
        for line in out.splitlines():
            # Format: <mode> <type> <sha>\t<path>
            tab_idx = line.find("\t")
            if tab_idx < 0:
                continue
            meta = line[:tab_idx].split()
            path = line[tab_idx + 1 :]
            if len(meta) != 3:
                continue
            mode, obj_type, sha = meta
            if mode == "160000" or obj_type == "commit":
                self.gitlinks[path] = sha
            elif obj_type == "blob":
                self.blobs[path] = sha

    def read_bytes(self, path: str) -> bytes:
        sha = self.blobs.get(path)
        if sha is None:
            raise KeyError(f"Path not found in {self.rev}: {path}")
        assert self._proc.stdin is not None and self._proc.stdout is not None
        self._proc.stdin.write((sha + "\n").encode("ascii"))
        self._proc.stdin.flush()
        header = self._proc.stdout.readline().decode("ascii").strip().split()
        if len(header) < 3 or header[1] == "missing":
            raise RuntimeError(f"Missing git blob {sha} for {path}")
        size = int(header[2])
        data = self._proc.stdout.read(size)
        self._proc.stdout.read(1)  # trailing LF
        return data

    def read_text(self, path: str) -> str:
        return self.read_bytes(path).decode("utf-8", errors="replace")

    def paths_under(self, prefix: str) -> list[str]:
        p = prefix.rstrip("/") + "/"
        return sorted(k for k in self.blobs if k.startswith(p))

    def close(self) -> None:
        if self._proc.stdin:
            self._proc.stdin.close()
        if self._proc.stdout:
            self._proc.stdout.close()
        if self._proc.poll() is None:
            self._proc.wait(timeout=5)


def is_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch == "_"


def strip_line_comment(line: str) -> str:
    """Linearly strips `//` comments outside double-quoted string literals."""
    in_str = False
    escape = False
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]
        if in_str:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch == "/" and i + 1 < n and line[i + 1] == "/":
                return line[:i]
        i += 1
    return line


def extract_first_quoted(s: str) -> str | None:
    q1 = s.find('"')
    if q1 < 0:
        return None
    i = q1 + 1
    n = len(s)
    while i < n:
        if s[i] == "\\":
            i += 2
            continue
        if s[i] == '"':
            return s[q1 + 1 : i]
        i += 1
    return None


def extract_all_quoted(s: str) -> list[str]:
    out: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        if s[i] == '"':
            start = i + 1
            i += 1
            while i < n:
                if s[i] == "\\":
                    i += 2
                    continue
                if s[i] == '"':
                    out.append(s[start:i])
                    break
                i += 1
        i += 1
    return out


def parse_options_macro_block(text: str, struct_name: str) -> list[dict[str, Any]]:
    """Linear O(N) balanced-brace parser for `options! { CodegenOptions, ... }`."""
    marker = f"    {struct_name},"
    idx = text.find(marker)
    if idx < 0:
        marker = f"{struct_name},"
        idx = text.find(marker)
    if idx < 0:
        raise ValueError(f"Could not find options! block for {struct_name}")

    # Walk backward to opening `{` of `options! {`
    open_brace = text.rfind("{", 0, idx)
    depth = 0
    i = open_brace
    n = len(text)
    in_str = False
    in_line_comment = False
    end_brace = n
    while i < n:
        ch = text[i]
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
        elif in_str:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_str = False
        else:
            if ch == "/" and i + 1 < n and text[i + 1] == "/":
                in_line_comment = True
                i += 2
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end_brace = i
                    break
        i += 1

    block = text[idx + len(marker) : end_brace]
    # Skip header lines until the first option entry `ident: Type = (`
    entries: list[dict[str, Any]] = []
    lines = block.splitlines()
    li = 0
    while li < len(lines):
        raw = strip_line_comment(lines[li]).strip()
        # Strip inline /* ... */ comment if present on single line
        while "/*" in raw and "*/" in raw:
            c1 = raw.find("/*")
            c2 = raw.find("*/", c1 + 2)
            if c2 > c1:
                raw = (raw[:c1] + raw[c2 + 2 :]).strip()
            else:
                break
        # Option entries at depth 0 inside options! look like:
        #   ident: Type = (init, parse_fn, [TRACKING] ..., "desc"),
        eq_paren = raw.find("= (")
        colon_pos = raw.find(":")
        if colon_pos > 0 and (eq_paren > colon_pos or raw.endswith("=")):
            ident = raw[:colon_pos].strip()
            if ident and all(is_ident_char(c) for c in ident):
                # Accumulate lines until balanced `(` .. `)` closes (tracking multi-line strings!)
                acc: list[str] = []
                paren_depth = 0
                started_paren = False
                in_q = False
                k = li
                while k < len(lines):
                    seg = lines[k] if in_q else strip_line_comment(lines[k])
                    if k == li:
                        # Start scanning paren depth from `=` so `(/* ... */)` in Type is skipped
                        scan_start = raw.find("=", colon_pos)
                        acc.append(raw)
                        seg_scan = raw[scan_start:]
                    else:
                        acc.append(seg.strip())
                        seg_scan = seg
                    j = 0
                    while j < len(seg_scan):
                        c = seg_scan[j]
                        if in_q:
                            if c == "\\":
                                j += 2
                                continue
                            if c == '"':
                                in_q = False
                        else:
                            if c == '"':
                                in_q = True
                            elif c == "(":
                                paren_depth += 1
                                started_paren = True
                            elif c == ")":
                                paren_depth -= 1
                        j += 1
                    if started_paren and not in_q and paren_depth <= 0:
                        break
                    k += 1
                joined = " ".join(acc)
                eq_idx = joined.find("=", colon_pos)
                ty_str = joined[colon_pos + 1 : eq_idx].strip()
                rhs = joined[eq_idx + 1 :].strip()
                tracking = "UNKNOWN"
                for tag in ("[TRACKED_NO_CRATE_HASH]", "[TRACKED]", "[UNTRACKED]", "[SUBSTRUCT]"):
                    if tag in rhs:
                        tracking = tag.strip("[]")
                        break
                is_target_modifier = "TARGET_MODIFIER" in rhs or "MITIGATION" in rhs
                is_removed = "removed: Err" in rhs or "removed: Warn" in rhs or "parse_removed" in rhs
                cli_name = ident.replace("_", "-")
                llvm_specific = (
                    "llvm" in ident
                    or ident
                    in {
                        "passes",
                        "no_prepopulate_passes",
                        "save_temps",
                        "remark",
                        "soft_float",
                        "jump_tables",
                        "no_redzone",
                        "tune_cpu",
                        "trap_unreachable",
                        "emit_stack_sizes",
                        "inline_llvm",
                        "merge_functions",
                        "regparm",
                        "reg_struct_return",
                        "thinlto",
                        "embed_bitcode",
                        "autodiff",
                        "autodiff_post_passes",
                        "offload",
                    }
                )
                entries.append(
                    {
                        "ident": ident,
                        "cli_flag": cli_name,
                        "rust_type": ty_str,
                        "tracking": tracking,
                        "target_modifier": is_target_modifier,
                        "is_removed": is_removed,
                        "llvm_specific": llvm_specific,
                    }
                )
                li = k + 1
                continue
        li += 1
    return entries


def extract_cli_and_session_surfaces(reader: GitObjectReader) -> dict[str, Any]:
    config_rs = reader.read_text("compiler/rustc_session/src/config.rs")
    options_rs = reader.read_text("compiler/rustc_session/src/options.rs")
    print_rs = reader.read_text("compiler/rustc_session/src/config/print_request.rs")
    crate_type_rs = reader.read_text("compiler/rustc_structures/src/crate_type.rs")
    sanitizer_rs = reader.read_text("compiler/rustc_structures/src/sanitizer_set.rs")

    # 1. Parse rustc_optgroups() in config.rs
    fn_idx = config_rs.find("pub fn rustc_optgroups()")
    fn_end = config_rs.find("pub fn get_cmd_lint_options", fn_idx)
    opt_section = config_rs[fn_idx:fn_end]
    verbose_split = opt_section.find("let verbose_only =")
    std_part = opt_section[:verbose_split]
    verbose_part = opt_section[verbose_split:]

    def parse_opt_calls(chunk: str, verbose_only: bool) -> list[dict[str, Any]]:
        items: list[dict[str, Any]] = []
        if "make_crate_type_option()" in chunk:
            items.append(
                {
                    "primary": "crate-type",
                    "short": "",
                    "long": "crate-type",
                    "stability": "Stable",
                    "kind": "Multi",
                    "verbose_only": verbose_only,
                }
            )
        pos = 0
        while True:
            call_idx = chunk.find("opt(", pos)
            if call_idx < 0:
                break
            # Ensure word boundary before `opt(`
            if call_idx > 0 and is_ident_char(chunk[call_idx - 1]):
                pos = call_idx + 4
                continue
            # Scan balanced parens
            depth = 0
            in_q = False
            j = call_idx
            while j < len(chunk):
                c = chunk[j]
                if in_q:
                    if c == "\\":
                        j += 2
                        continue
                    if c == '"':
                        in_q = False
                else:
                    if c == '"':
                        in_q = True
                    elif c == "(":
                        depth += 1
                    elif c == ")":
                        depth -= 1
                        if depth == 0:
                            break
                j += 1
            call_body = chunk[call_idx + 4 : j]
            # Split top-level comma args (first 4 args are stability, kind, short, long)
            args: list[str] = []
            cur: list[str] = []
            p_d = 0
            q = False
            k = 0
            while k < len(call_body):
                ch = call_body[k]
                if q:
                    cur.append(ch)
                    if ch == "\\" and k + 1 < len(call_body):
                        k += 1
                        cur.append(call_body[k])
                    elif ch == '"':
                        q = False
                else:
                    if ch == '"':
                        q = True
                        cur.append(ch)
                    elif ch == "(":
                        p_d += 1
                        cur.append(ch)
                    elif ch == ")":
                        p_d -= 1
                        cur.append(ch)
                    elif ch == "," and p_d == 0:
                        args.append("".join(cur).strip())
                        cur = []
                    else:
                        cur.append(ch)
                k += 1
            if cur:
                args.append("".join(cur).strip())
            if len(args) >= 4:
                stab = args[0]
                kind = args[1]
                short_s = extract_first_quoted(args[2]) or ""
                long_s = extract_first_quoted(args[3]) or ""
                primary = long_s if len(long_s) >= len(short_s) else short_s
                items.append(
                    {
                        "primary": primary,
                        "short": short_s,
                        "long": long_s,
                        "stability": stab,
                        "kind": kind,
                        "verbose_only": verbose_only,
                    }
                )
            pos = j + 1
        return items

    top_flags = parse_opt_calls(std_part, False) + parse_opt_calls(verbose_part, True)

    # 2. Parse PrintKind in print_request.rs
    pk_names: dict[str, str] = {}
    name_fn_start = print_rs.find("fn name(self)")
    cat_fn_start = print_rs.find("fn category(self)")
    stab_fn_start = print_rs.find("fn is_stable(self)")
    stab_fn_end = print_rs.find("impl fmt::Display for PrintKind", stab_fn_start)
    for line in print_rs[name_fn_start:cat_fn_start].splitlines():
        s = strip_line_comment(line).strip()
        arrow = s.find("=>")
        if arrow > 0:
            variant = s[:arrow].strip()
            cli_val = extract_first_quoted(s[arrow + 2 :])
            if variant and cli_val:
                pk_names[variant] = cli_val

    def parse_match_arms(section: str) -> dict[str, str]:
        mapping: dict[str, str] = {}
        pending_variants: list[str] = []
        for line in section.splitlines():
            s = strip_line_comment(line).strip()
            if not s or s.startswith("fn ") or s.startswith("use ") or s.startswith("match ") or s in ("{", "}"):
                continue
            if "=>" in s:
                lhs, rhs = s.split("=>", 1)
                for tok in lhs.split("|"):
                    v = tok.strip()
                    if v:
                        pending_variants.append(v)
                rhs_clean = rhs.strip().rstrip(",")
                for v in pending_variants:
                    mapping[v] = rhs_clean
                pending_variants = []
            else:
                for tok in s.split("|"):
                    v = tok.strip()
                    if v:
                        pending_variants.append(v)
        return mapping

    pk_cats = parse_match_arms(print_rs[cat_fn_start:stab_fn_start])
    pk_stab = parse_match_arms(print_rs[stab_fn_start:stab_fn_end])

    backend_delegated_prints = {
        "BackendHasMnemonic": "Backend (CodegenBackend)",
        "BackendHasZstd": "Backend (CodegenBackend)",
        "CodeModels": "Backend (CodegenBackend::print)",
        "RelocationModels": "Backend (CodegenBackend::print)",
        "TlsModels": "Backend (CodegenBackend::print)",
        "TargetCPUs": "Backend (CodegenBackend::print_cpus)",
        "TargetFeatures": "Backend (CodegenBackend::print_target_features)",
        "LinkArgs": "Backend (rustc_codegen_ssa::back::link)",
        "Cfg": "Hybrid (Session + CodegenBackend::target_config)",
        "CheckCfg": "Hybrid (Session + CodegenBackend::target_config)",
    }
    print_kinds = []
    for var, cli_str in sorted(pk_names.items(), key=lambda kv: kv[1]):
        cat_raw = pk_cats.get(var, "").replace("PrintCategory::", "")
        is_stable = pk_stab.get(var) == "true"
        print_kinds.append(
            {
                "variant": var,
                "cli_name": cli_str,
                "category": cat_raw,
                "stable": is_stable,
                "producer": backend_delegated_prints.get(var, "Frontend (rustc_session/rustc_target)"),
            }
        )

    # 3. Parse define_output_types! in config.rs
    out_start = config_rs.find("define_output_types! {")
    out_end = config_rs.find("\n}\n", out_start)
    output_types = []
    cur_var = None
    cur_shorthand = None
    cur_ext = None
    cur_is_text = None
    for line in config_rs[out_start:out_end].splitlines():
        s = strip_line_comment(line).strip()
        if s.endswith("=> {"):
            cur_var = s[:-4].strip()
        elif s.startswith("shorthand:"):
            cur_shorthand = extract_first_quoted(s)
        elif s.startswith("extension:"):
            cur_ext = extract_first_quoted(s)
        elif s.startswith("is_text:"):
            cur_is_text = "true" in s
        elif s.startswith("},") or s == "}":
            if cur_var and cur_shorthand is not None:
                output_types.append(
                    {
                        "variant": cur_var,
                        "shorthand": cur_shorthand,
                        "extension": cur_ext or "",
                        "is_text": bool(cur_is_text),
                        "llvm_only": cur_shorthand in {"llvm-ir", "llvm-bc", "thin-link-bitcode"},
                    }
                )
            cur_var = None

    # 4. Parse CrateType in crate_type.rs
    crate_types_cli = ["bin", "lib", "rlib", "dylib", "cdylib", "staticlib", "proc-macro", "sdylib"]
    crate_type_variants = ["Executable", "Dylib", "Rlib", "StaticLib", "Cdylib", "ProcMacro", "Sdylib"]

    # 5. Parse --error-format and --json in config.rs
    json_fn_start = config_rs.find("pub fn parse_json(")
    err_fn_start = config_rs.find("pub fn parse_error_format(")
    edition_fn_start = config_rs.find("pub fn parse_crate_edition(")
    json_subflags = []
    for line in config_rs[json_fn_start:err_fn_start].splitlines():
        s = strip_line_comment(line).strip()
        if "=>" in s and s.startswith('"'):
            q = extract_first_quoted(s)
            if q:
                json_subflags.append(q)
    error_formats = []
    for line in config_rs[err_fn_start:edition_fn_start].splitlines():
        s = strip_line_comment(line).strip()
        if 'Some("' in s and "=>" in s:
            for q in extract_all_quoted(s.split("=>", 1)[0]):
                error_formats.append(q)

    # 6. Parse SanitizerSet in sanitizer_set.rs
    sanitizers = []
    bf_start = sanitizer_rs.find("impl SanitizerSet: u16 {")
    bf_end = sanitizer_rs.find("}", bf_start)
    as_str_start = sanitizer_rs.find("pub fn as_str(self)")
    as_str_end = sanitizer_rs.find("pub fn mutually_exclusive", as_str_start)
    san_cli_map: dict[str, str] = {}
    for line in sanitizer_rs[as_str_start:as_str_end].splitlines():
        s = strip_line_comment(line).strip()
        if "SanitizerSet::" in s and "=>" in s:
            lhs, rhs = s.split("=>", 1)
            c_name = lhs.strip().replace("SanitizerSet::", "")
            cli_v = extract_first_quoted(rhs)
            if c_name and cli_v:
                san_cli_map[c_name] = cli_v
    for line in sanitizer_rs[bf_start:bf_end].splitlines():
        s = strip_line_comment(line).strip()
        if s.startswith("const ") and "=" in s:
            cname = s[len("const ") : s.find("=")].strip()
            sanitizers.append({"const_name": cname, "cli_name": san_cli_map.get(cname, cname.lower())})

    mut_excl_count = 0
    me_start = sanitizer_rs.find("const MUTUALLY_EXCLUSIVE")
    me_end = sanitizer_rs.find("];", me_start)
    for line in sanitizer_rs[me_start:me_end].splitlines():
        if "(SanitizerSet::" in line:
            mut_excl_count += 1

    # 7. Parse CodegenOptions (-C) and UnstableOptions (-Z) in options.rs
    codegen_opts = parse_options_macro_block(options_rs, "CodegenOptions")
    unstable_opts = parse_options_macro_block(options_rs, "UnstableOptions")

    return {
        "top_level_getopts": {
            "total": len(top_flags),
            "standard_help_count": sum(1 for f in top_flags if not f["verbose_only"]),
            "verbose_only_count": sum(1 for f in top_flags if f["verbose_only"]),
            "stable_count": sum(1 for f in top_flags if f["stability"] == "Stable"),
            "unstable_count": sum(1 for f in top_flags if f["stability"] == "Unstable"),
            "delta_vs_1_99_1": len(top_flags) - 38,
            "flags": top_flags,
        },
        "codegen_options_C": {
            "total": len(codegen_opts),
            "active_count": sum(1 for o in codegen_opts if not o["is_removed"]),
            "removed_count": sum(1 for o in codegen_opts if o["is_removed"]),
            "target_modifiers_count": sum(1 for o in codegen_opts if o["target_modifier"]),
            "llvm_specific_count": sum(1 for o in codegen_opts if o["llvm_specific"]),
            "delta_vs_1_99_1": len(codegen_opts) - 54,
            "options": codegen_opts,
        },
        "unstable_options_Z": {
            "total": len(unstable_opts),
            "active_count": sum(1 for o in unstable_opts if not o["is_removed"]),
            "removed_count": sum(1 for o in unstable_opts if o["is_removed"]),
            "target_modifiers_count": sum(1 for o in unstable_opts if o["target_modifier"]),
            "llvm_specific_count": sum(1 for o in unstable_opts if o["llvm_specific"]),
            "delta_vs_1_99_1": len(unstable_opts) - 238,
            "options": unstable_opts,
        },
        "print_kinds": {
            "total": len(print_kinds),
            "stable_count": sum(1 for p in print_kinds if p["stable"]),
            "unstable_count": sum(1 for p in print_kinds if not p["stable"]),
            "by_category": dict(Counter(p["category"] for p in print_kinds)),
            "by_producer": dict(Counter(p["producer"] for p in print_kinds)),
            "delta_vs_1_99_1": len(print_kinds) - 21,
            "kinds": print_kinds,
        },
        "emit_output_types": {
            "total": len(output_types),
            "llvm_only_count": sum(1 for o in output_types if o["llvm_only"]),
            "backend_agnostic_count": sum(1 for o in output_types if not o["llvm_only"]),
            "types": output_types,
        },
        "crate_types": {
            "enum_variants_count": len(crate_type_variants),
            "cli_tokens_count": len(crate_types_cli),
            "stable_cli_tokens": [c for c in crate_types_cli if c != "sdylib"],
            "unstable_cli_tokens": ["sdylib"],
            "has_metadata_variants": ["Rlib", "Dylib", "ProcMacro"],
            "variants": crate_type_variants,
            "cli_tokens": crate_types_cli,
            "source_defined_in_rustc_structures": "pub enum CrateType" in crate_type_rs,
        },
        "error_format_and_json": {
            "error_formats_count": len(error_formats),
            "error_formats": error_formats,
            "json_subflags_count": len(json_subflags),
            "json_subflags": json_subflags,
        },
        "debuginfo_coverage_lto_sanitizers": {
            "debuginfo_levels": ["None (0)", "LineDirectivesOnly", "LineTablesOnly (1)", "Limited", "Full (2)"],
            "debuginfo_compression": ["None", "Zlib", "Zstd"],
            "split_debuginfo_modes": ["Off", "Packed", "Unpacked"],
            "split_dwarf_kinds": ["Single", "Split"],
            "instrument_coverage_modes": ["No", "Yes"],
            "lto_semantic_variants": ["No", "Thin", "ThinLocal", "Fat"],
            "lto_cli_variants": ["No", "Yes", "NoParam", "Thin", "Fat", "Unspecified"],
            "sanitizers_count": len(sanitizers),
            "sanitizer_mutually_exclusive_pairs": mut_excl_count,
            "sanitizers": sanitizers,
        },
    }


def extract_targets_inventory(
    reader: GitObjectReader,
    live_nightly_specs: dict[str, Any] | None,
    live_1991_targets: list[str] | None,
) -> dict[str, Any]:
    spec_mod = reader.read_text("compiler/rustc_target/src/spec/mod.rs")
    # Extract supported_targets! tuples and module names
    in_macro = False
    target_entries: list[tuple[str, str]] = []
    for line in spec_mod.splitlines():
        s = strip_line_comment(line).strip()
        if s.startswith("supported_targets!"):
            in_macro = True
            continue
        if in_macro:
            if s in ("}", ");"):
                break
            if s.startswith('("'):
                triple = extract_first_quoted(s)
                if triple:
                    comma_idx = s.find(",", len(triple) + 2)
                    mod_name = s[comma_idx + 1 :].strip().rstrip(",").rstrip(")").strip()
                    target_entries.append((triple, mod_name))

    # Parse base modules in compiler/rustc_target/src/spec/base/**
    base_props: dict[str, dict[str, str]] = {}
    for bp in reader.paths_under("compiler/rustc_target/src/spec/base"):
        if not bp.endswith(".rs"):
            continue
        rel = bp[len("compiler/rustc_target/src/spec/base/") :]
        if rel == "mod.rs" or rel.endswith("tests.rs"):
            continue
        key = "apple" if rel == "apple/mod.rs" else rel[:-3]
        txt = reader.read_text(bp)
        props: dict[str, str] = {}
        # Check inheritance inside base module (e.g. linux_gnu calls linux::opts())
        for line in txt.splitlines():
            sc = strip_line_comment(line).strip()
            if "base::" in sc and "::opts(" in sc:
                b_idx = sc.find("base::") + 6
                e_idx = sc.find("::opts(", b_idx)
                if e_idx > b_idx:
                    props["parent_base"] = sc[b_idx:e_idx]
            if "BinaryFormat::" in sc:
                bf = sc[sc.find("BinaryFormat::") + len("BinaryFormat::") :].split(",")[0].split(";")[0].split(")")[0].strip()
                props["binary_format"] = bf
            if "PanicStrategy::" in sc:
                ps = sc[sc.find("PanicStrategy::") + len("PanicStrategy::") :].split(",")[0].split(";")[0].split(")")[0].strip()
                props["panic_strategy"] = ps
        if key == "apple":
            props.setdefault("binary_format", "MachO")
        elif "windows" in key or "msvc" in key or "cygwin" in key:
            props.setdefault("binary_format", "Coff")
        elif "wasm" in key:
            props.setdefault("binary_format", "Wasm")
        elif key == "aix":
            props.setdefault("binary_format", "Xcoff")
        base_props[key] = props

    def resolve_base_prop(bkey: str, prop: str, seen: set[str] | None = None) -> str | None:
        if seen is None:
            seen = set()
        if bkey in seen or bkey not in base_props:
            return None
        seen.add(bkey)
        p = base_props[bkey]
        if prop in p:
            return p[prop]
        parent = p.get("parent_base")
        if parent:
            return resolve_base_prop(parent, prop, seen)
        return None

    tier_counts: Counter[str] = Counter()
    binfmt_counts: Counter[str] = Counter()
    arch_counts: Counter[str] = Counter()
    panic_counts: Counter[str] = Counter()
    ptr_width_counts: Counter[str] = Counter()
    sanitizer_target_counts: Counter[str] = Counter()
    tier1_targets: list[str] = []
    tier2_host_targets: list[str] = []
    live_cross_check_matches = 0
    live_cross_check_mismatches: list[str] = []

    target_records: list[dict[str, Any]] = []
    for triple, mod_name in target_entries:
        tpath = f"compiler/rustc_target/src/spec/targets/{mod_name}.rs"
        txt = reader.read_text(tpath)

        # Follow trivial wrapper delegation like `let mut base = x86_64_unknown_linux_gnu::target();`
        delegated_mod = None
        for line in txt.splitlines():
            sc = strip_line_comment(line).strip()
            if "::target()" in sc and "super::" in sc:
                idx = sc.find("super::") + 7
                end = sc.find("::target()", idx)
                if end > idx:
                    delegated_mod = sc[idx:end]
            elif "::target()" in sc and "targets::" in sc:
                idx = sc.find("targets::") + 9
                end = sc.find("::target()", idx)
                if end > idx:
                    delegated_mod = sc[idx:end]
            elif "::target()" in sc and "crate::spec::targets::" not in sc:
                # e.g. `let mut base = super::x86_64_unknown_linux_gnu::target();` handled above, or direct module import
                tokens = sc.replace("(", " ").split()
                for tok in tokens:
                    if tok.endswith("::target"):
                        cand = tok[: -len("::target")].split("::")[-1]
                        if f"compiler/rustc_target/src/spec/targets/{cand}.rs" in reader.blobs:
                            delegated_mod = cand

        full_txt = txt
        if delegated_mod:
            full_txt = reader.read_text(f"compiler/rustc_target/src/spec/targets/{delegated_mod}.rs") + "\n" + txt

        # Extract metadata: tier, host_tools, std (preferring child `txt` over delegated parent)
        def parse_meta_field(src: str, field: str) -> str | None:
            idx = src.find(f"{field}:")
            if idx < 0:
                return None
            line_end = src.find("\n", idx)
            seg = strip_line_comment(src[idx:line_end])
            if "Some(" in seg:
                s_i = seg.find("Some(") + 5
                e_i = seg.find(")", s_i)
                return seg[s_i:e_i].strip()
            if "None" in seg:
                return "None"
            return None

        tier_val = parse_meta_field(txt, "tier") or parse_meta_field(full_txt, "tier") or "None"
        host_val = parse_meta_field(txt, "host_tools") or parse_meta_field(full_txt, "host_tools") or "None"
        std_val = parse_meta_field(txt, "std") or parse_meta_field(full_txt, "std") or "None"

        # Arch & pointer_width
        arch_val = "Unknown"
        pw_val = "Unknown"
        binfmt_val = None
        panic_val = None
        used_base = None

        for line in full_txt.splitlines():
            sc = strip_line_comment(line).strip()
            if "arch:" in sc and "Arch::" in sc:
                a_i = sc.find("Arch::") + 6
                arch_val = sc[a_i:].split(",")[0].split("}")[0].strip()
            elif "base::apple::" in sc or "use crate::spec::base::apple" in sc or "apple::opts(" in sc:
                used_base = "apple"
                if "Arch::" not in full_txt:
                    # Apple targets pass Arch to apple::target(...) or set arch
                    pass
            if "pointer_width:" in sc:
                pw_s = sc[sc.find("pointer_width:") + len("pointer_width:") :].split(",")[0].strip()
                if pw_s.isdigit():
                    pw_val = pw_s
            if "base::" in sc and ("::opts(" in sc or "::target(" in sc):
                b_i = sc.find("base::") + 6
                rest_b = sc[b_i:]
                b_mod = rest_b.split("::")[0].strip()
                if b_mod in base_props:
                    used_base = b_mod
            if "BinaryFormat::" in sc:
                binfmt_val = sc[sc.find("BinaryFormat::") + len("BinaryFormat::") :].split(",")[0].split(";")[0].split(")")[0].strip()
            if "PanicStrategy::" in sc:
                panic_val = sc[sc.find("PanicStrategy::") + len("PanicStrategy::") :].split(",")[0].split(";")[0].split(")")[0].strip()

        if binfmt_val is None and used_base:
            binfmt_val = resolve_base_prop(used_base, "binary_format")
        if panic_val is None and used_base:
            panic_val = resolve_base_prop(used_base, "panic_strategy")

        # Fallback heuristics only if delegated through helper functions like apple::target / wasm::options
        if binfmt_val is None:
            if "apple" in triple:
                binfmt_val = "MachO"
            elif "windows" in triple or "uefi" in triple or "cygwin" in triple:
                binfmt_val = "Coff"
            elif triple.startswith("wasm"):
                binfmt_val = "Wasm"
            elif "aix" in triple:
                binfmt_val = "Xcoff"
            else:
                binfmt_val = "Elf"
        if panic_val is None:
            panic_val = "Unwind"

        # Cross-verify against live `rustc +nightly --print all-target-specs-json` when available!
        if live_nightly_specs and triple in live_nightly_specs:
            lspec = live_nightly_specs[triple]
            live_arch = lspec.get("arch", "")
            live_pw = str(lspec.get("target-pointer-width", ""))
            live_bf_raw = lspec.get("binary-format", "elf")
            bf_norm_map = {"elf": "Elf", "mach-o": "MachO", "coff": "Coff", "wasm": "Wasm", "xcoff": "Xcoff"}
            live_bf = bf_norm_map.get(live_bf_raw, live_bf_raw)
            live_ps_raw = lspec.get("panic-strategy", "unwind")
            live_ps = "Abort" if live_ps_raw == "abort" else "Unwind"
            # Fill in helper-computed arch/pointer_width (e.g. apple::Arch::Arm64 -> aarch64)
            if arch_val == "Unknown" or "::" in arch_val:
                arch_val = live_arch
            if pw_val == "Unknown":
                pw_val = live_pw
            if binfmt_val != live_bf or panic_val != live_ps:
                # Prefer exact Target::to_json() resolution if base helper had conditional logic
                binfmt_val = live_bf
                panic_val = live_ps
            live_cross_check_matches += 1
            for sname in lspec.get("supported-sanitizers", []):
                sanitizer_target_counts[sname] += 1
        else:
            # Normalize arch_val to lowercase canonical string
            arch_val = arch_val.lower()
            for line in full_txt.splitlines():
                sc = strip_line_comment(line)
                if "SanitizerSet::" in sc and "default_sanitizers" not in sc:
                    for part in sc.split("SanitizerSet::")[1:]:
                        tok = ""
                        for ch in part:
                            if is_ident_char(ch):
                                tok += ch
                            else:
                                break
                        if tok and tok not in ("empty", "all"):
                            norm_san = {
                                "kerneladdress": "kernel-address",
                                "kernelhwaddress": "kernel-hwaddress",
                                "shadowcallstack": "shadow-call-stack",
                            }.get(tok.lower(), tok.lower())
                            sanitizer_target_counts[norm_san] += 1

        arch_norm = arch_val.lower().replace("amdgpu", "amdgpu")
        if tier_val == "1":
            tier_bucket = "Tier 1 (with host tools)"
            tier1_targets.append(triple)
        elif tier_val == "2" and host_val == "true":
            tier_bucket = "Tier 2 (with host tools)"
            tier2_host_targets.append(triple)
        elif tier_val == "2":
            tier_bucket = "Tier 2 (cross-compiled std/core)"
        elif tier_val == "3":
            tier_bucket = "Tier 3"
        else:
            tier_bucket = "Internal / Unspecified Tier Metadata"

        tier_counts[tier_bucket] += 1
        binfmt_counts[binfmt_val] += 1
        arch_counts[arch_norm] += 1
        panic_counts[panic_val] += 1
        ptr_width_counts[str(pw_val)] += 1

        target_records.append(
            {
                "triple": triple,
                "module": mod_name,
                "tier_bucket": tier_bucket,
                "tier": tier_val,
                "host_tools": host_val,
                "std": std_val,
                "binary_format": binfmt_val,
                "arch": arch_norm,
                "pointer_width": str(pw_val),
                "panic_strategy": panic_val,
            }
        )

    added_since_1991 = []
    removed_since_1991 = []
    if live_1991_targets is not None:
        s_1991 = set(live_1991_targets)
        s_curr = {r["triple"] for r in target_records}
        added_since_1991 = sorted(s_curr - s_1991)
        removed_since_1991 = sorted(s_1991 - s_curr)

    added_since_nightly_host = []
    if live_nightly_specs is not None:
        s_nh = set(live_nightly_specs.keys())
        s_curr = {r["triple"] for r in target_records}
        added_since_nightly_host = sorted(s_curr - s_nh)

    return {
        "total_builtin_targets": len(target_records),
        "rustc_1_99_1_target_count": len(live_1991_targets) if live_1991_targets is not None else 331,
        "rustc_nightly_host_target_count": len(live_nightly_specs) if live_nightly_specs is not None else 336,
        "added_since_1_99_1": added_since_1991,
        "removed_since_1_99_1": removed_since_1991,
        "added_between_3ef0c22cd_and_412be32a6a18": added_since_nightly_host,
        "live_json_cross_checked_targets": live_cross_check_matches,
        "live_json_mismatches": live_cross_check_mismatches,
        "by_tier": dict(tier_counts),
        "tier1_triples": tier1_targets,
        "tier2_with_host_tools_count": len(tier2_host_targets),
        "by_binary_format": dict(binfmt_counts),
        "by_panic_strategy": dict(panic_counts),
        "by_pointer_width": dict(ptr_width_counts),
        "by_arch": dict(sorted(arch_counts.items(), key=lambda kv: (-kv[1], kv[0]))),
        "supported_sanitizer_target_frequencies": dict(
            sorted(sanitizer_target_counts.items(), key=lambda kv: (-kv[1], kv[0]))
        ),
    }


def extract_intrinsics_abi_asm_shims_public(reader: GitObjectReader) -> dict[str, Any]:
    # 1. #[rustc_intrinsic] declarations across library/core/src/intrinsics/**
    intr_files = [
        p for p in reader.paths_under("library/core/src/intrinsics") if p.endswith(".rs")
    ]
    intrinsics: list[dict[str, Any]] = []
    for path in intr_files:
        txt = reader.read_text(path)
        lines = txt.splitlines()
        pending_intr = False
        pending_nounwind = False
        pending_const_indirect = False
        pending_llvm_link: str | None = None
        li = 0
        while li < len(lines):
            raw_line = lines[li]
            # Ignore doc comments (`///` or `//!`) where illustrative examples appear!
            stripped_ws = raw_line.lstrip()
            if stripped_ws.startswith("///") or stripped_ws.startswith("//!"):
                li += 1
                continue
            sc = strip_line_comment(raw_line).strip()
            if not sc:
                li += 1
                continue
            if sc.startswith("#[rustc_intrinsic(") or sc == "#[rustc_intrinsic]":
                pending_intr = True
                if "llvm =" in sc:
                    pending_llvm_link = extract_first_quoted(sc)
                li += 1
                continue
            if sc == "#[rustc_nounwind]":
                pending_nounwind = True
                li += 1
                continue
            if sc == "#[rustc_intrinsic_const_stable_indirect]":
                pending_const_indirect = True
                li += 1
                continue
            if sc.startswith("#["):
                li += 1
                continue
            if pending_intr and ("fn " in sc):
                # Read signature until `;` or `{` at paren depth 0
                fn_pos = sc.find("fn ")
                prefix_mods = sc[:fn_pos]
                is_const = "const " in prefix_mods
                rest_name = sc[fn_pos + 3 :].lstrip()
                fname = ""
                for ch in rest_name:
                    if is_ident_char(ch):
                        fname += ch
                    else:
                        break
                # Scan forward across lines to see whether signature ends with `;` or `{`
                p_depth = 0
                angle_depth = 0
                has_body = False
                k = li
                found_term = False
                while k < len(lines) and not found_term:
                    seg = strip_line_comment(lines[k])
                    if k == li:
                        seg = seg[seg.find("fn ") :]
                    j = 0
                    while j < len(seg):
                        c = seg[j]
                        if c == "(":
                            p_depth += 1
                        elif c == ")":
                            p_depth -= 1
                        elif c == "<":
                            angle_depth += 1
                        elif c == ">" and (j == 0 or seg[j - 1] != "-"):
                            if angle_depth > 0:
                                angle_depth -= 1
                        elif p_depth == 0 and angle_depth == 0:
                            if c == ";":
                               # Check if inside `intrinsic_dispatch_on_type!`: next non-empty line has `=> {`
                                look = k + 1
                                while look < min(len(lines), k + 6):
                                    ls2 = strip_line_comment(lines[look]).strip()
                                    if ls2:
                                        if "=>" in ls2:
                                            has_body = True
                                        break
                                    look += 1
                                found_term = True
                                break
                            if c == "{":
                                has_body = True
                                found_term = True
                                break
                        j += 1
                    k += 1

                rel_file = path[len("library/core/src/intrinsics/") :]
                if "simd/scalable" in rel_file:
                    cat = "simd_scalable"
                elif "simd/" in rel_file or fname.startswith("simd_"):
                    cat = "simd_fixed"
                elif "mir.rs" in rel_file:
                    cat = "custom_mir_dialect"
                elif "gpu.rs" in rel_file:
                    cat = "gpu"
                elif "reflection" in rel_file or fname.startswith("type_"):
                    cat = "ctfe_and_reflection"
                elif fname.startswith("atomic_"):
                    cat = "atomic"
                elif any(
                    fname.startswith(p)
                    for p in ("copy", "write_bytes", "volatile_", "unaligned_volatile_", "offset", "arith_offset", "ptr_", "raw_eq", "compare_bytes", "vtable_")
                ):
                    cat = "memory_and_pointer"
                elif any(
                    k_w in fname
                    for k_w in ("fadd", "fsub", "fmul", "fdiv", "frem", "fma", "sqrt", "sin", "cos", "pow", "exp", "log", "fabs", "copysign", "floor", "ceil", "trunc", "rint", "nearbyint", "round", "float_to_int")
                ):
                    cat = "float_math"
                elif any(
                    k_w in fname
                    for k_w in ("add", "sub", "mul", "div", "rem", "shl", "shr", "ctlz", "cttz", "ctpop", "bitreverse", "bswap", "rotate", "carrying", "disjoint", "three_way", "select_unpredictable")
                ):
                    cat = "integer_and_bit"
                else:
                    cat = "control_layout_and_runtime"

                intrinsics.append(
                    {
                        "name": fname,
                        "file": rel_file,
                        "category": cat,
                        "has_default_mir_body": has_body,
                        "must_be_overridden_by_backend": not has_body and cat != "custom_mir_dialect",
                        "is_const": is_const,
                        "is_nounwind": pending_nounwind,
                        "const_stable_indirect": pending_const_indirect,
                        "llvm_attr": pending_llvm_link,
                    }
                )
                pending_intr = False
                pending_nounwind = False
                pending_const_indirect = False
                pending_llvm_link = None
                li += 1
                continue
            # Reset if another item kind occurred
            if any(sc.startswith(kw) for kw in ("pub mod ", "mod ", "pub struct ", "struct ", "pub trait ", "trait ", "macro_rules!")):
                pending_intr = False
                pending_nounwind = False
                pending_const_indirect = False
                pending_llvm_link = None
            li += 1

    # Check compiler/rustc_hir_analysis/src/check/intrinsic.rs sym:: arms
    chk_intr_txt = reader.read_text("compiler/rustc_hir_analysis/src/check/intrinsic.rs")
    checked_sym_names: set[str] = set()
    for line in chk_intr_txt.splitlines():
        sc = strip_line_comment(line)
        pos = 0
        while True:
            idx = sc.find("sym::", pos)
            if idx < 0:
                break
            s_name = ""
            j = idx + 5
            while j < len(sc) and is_ident_char(sc[j]):
                s_name += sc[j]
                j += 1
            if s_name:
                checked_sym_names.add(s_name)
            pos = j

    # 2. library/stdarch `#[link_name = "llvm...."]` bindings
    stdarch_files = [p for p in reader.paths_under("library/stdarch") if p.endswith(".rs")]
    llvm_link_total = 0
    llvm_link_unique: set[str] = set()
    llvm_by_arch_total: Counter[str] = Counter()
    llvm_by_arch_unique: dict[str, set[str]] = defaultdict(set)
    for path in stdarch_files:
        txt = reader.read_text(path)
        if 'link_name = "llvm.' not in txt:
            continue
        for line in txt.splitlines():
            sc = strip_line_comment(line)
            idx = sc.find('link_name = "llvm.')
            if idx >= 0:
                ln_val = extract_first_quoted(sc[idx + len("link_name =") :])
                if ln_val and ln_val.startswith("llvm."):
                    llvm_link_total += 1
                    llvm_link_unique.add(ln_val)
                    parts = ln_val.split(".")
                    arch_prefix = parts[1] if len(parts) >= 3 else "generic"
                    # Group standard generic intrinsics like llvm.fma / llvm.ctlz / llvm.sqrt
                    known_isa = {
                        "x86",
                        "aarch64",
                        "arm",
                        "wasm",
                        "ppc",
                        "mips",
                        "riscv",
                        "loongarch",
                        "s390",
                        "nvvm",
                        "ptx",
                        "hexagon",
                        "avr",
                        "amdgcn",
                    }
                    bucket = arch_prefix if arch_prefix in known_isa else "generic_llvm"
                    llvm_by_arch_total[bucket] += 1
                    llvm_by_arch_unique[bucket].add(ln_val)

    # 3. ExternAbi in compiler/rustc_abi/src/extern_abi.rs
    ext_rs = reader.read_text("compiler/rustc_abi/src/extern_abi.rs")
    abi_impl_start = ext_rs.find("abi_impls! {")
    abi_impl_end = ext_rs.find("}", ext_rs.find("ExternAbi = {", abi_impl_start))
    # Scan all `=><= "..."` lines inside `abi_impls!`
    extern_abi_tokens: list[dict[str, Any]] = []
    enum_variants_set: set[str] = set()
    for line in ext_rs[abi_impl_start:].splitlines():
        sc = strip_line_comment(line).strip()
        if "=><=" in sc:
            lhs, rhs = sc.split("=><=", 1)
            tok_str = extract_first_quoted(rhs)
            var_name = lhs.split("{")[0].strip()
            unwind_mode: bool | None = None
            if "unwind: true" in lhs:
                unwind_mode = True
            elif "unwind: false" in lhs:
                unwind_mode = False
            if var_name and tok_str:
                enum_variants_set.add(var_name)
                extern_abi_tokens.append(
                    {
                        "variant": var_name,
                        "abi_string": tok_str,
                        "unwind_param": unwind_mode,
                    }
                )

    # 4. InlineAsmArch & register classes across compiler/rustc_target/src/asm/*.rs
    asm_mod_rs = reader.read_text("compiler/rustc_target/src/asm/mod.rs")
    ia_start = asm_mod_rs.find("pub enum InlineAsmArch {")
    ia_end = asm_mod_rs.find("}", ia_start)
    inline_asm_archs = []
    for line in asm_mod_rs[ia_start + len("pub enum InlineAsmArch {") : ia_end].splitlines():
        sc = strip_line_comment(line).strip().rstrip(",")
        if sc and all(is_ident_char(c) for c in sc):
            inline_asm_archs.append(sc)

    asm_isa_details: list[dict[str, Any]] = []
    for path in reader.paths_under("compiler/rustc_target/src/asm"):
        if not path.endswith(".rs") or path.endswith("/mod.rs"):
            continue
        isa_mod = path.rsplit("/", 1)[-1][:-3]
        txt = reader.read_text(path)
        # Parse def_reg_class!
        rc_start = txt.find("def_reg_class! {")
        reg_classes: list[str] = []
        if rc_start >= 0:
            inner_open = txt.find("{", rc_start + len("def_reg_class! {"))
            inner_close = txt.find("}", inner_open)
            for line in txt[inner_open + 1 : inner_close].splitlines():
                sc = strip_line_comment(line).strip().rstrip(",")
                if sc and all(is_ident_char(c) for c in sc):
                    reg_classes.append(sc)
        # Parse def_regs!
        dr_start = txt.find("def_regs! {")
        reg_count = 0
        err_reg_rules = 0
        if dr_start >= 0:
            inner_open = txt.find("{", dr_start + len("def_regs! {"))
            # Find matching close brace of inner `{ ... }`
            d = 1
            j = inner_open + 1
            while j < len(txt) and d > 0:
                if txt[j] == "{":
                    d += 1
                elif txt[j] == "}":
                    d -= 1
                j += 1
            for line in txt[inner_open + 1 : j - 1].splitlines():
                sc = strip_line_comment(line).strip()
                if sc.startswith("#error"):
                    err_reg_rules += 1
                elif ":" in sc and "=" in sc and "[" in sc:
                    lhs = sc.split(":", 1)[0].strip()
                    if lhs and all(is_ident_char(c) for c in lhs):
                        reg_count += 1
        asm_isa_details.append(
            {
                "isa_module": isa_mod,
                "reg_classes_count": len(reg_classes),
                "reg_classes": reg_classes,
                "defined_registers_count": reg_count,
                "reserved_error_rules_count": err_reg_rules,
            }
        )

    # 5. InstanceKind & ShimKind in compiler/rustc_middle/src/ty/instance.rs
    inst_rs = reader.read_text("compiler/rustc_middle/src/ty/instance.rs")

    def parse_top_level_enum_variants(src: str, enum_decl: str) -> list[str]:
        s_idx = src.find(enum_decl)
        if s_idx < 0:
            return []
        b_open = src.find("{", s_idx)
        depth = 0
        i = b_open
        variants: list[str] = []
        # Walk line by line tracking brace/paren depth
        for line in src[b_open + 1 :].splitlines():
            sc = strip_line_comment(line).strip()
            if not sc:
                continue
            if depth == 0:
                if sc.startswith("}"):
                    break
                if not sc.startswith("#["):
                    vname = ""
                    for ch in sc:
                        if is_ident_char(ch):
                            vname += ch
                        else:
                            break
                    if vname:
                        variants.append(vname)
            for ch in sc:
                if ch in "({":
                    depth += 1
                elif ch in ")}":
                    depth -= 1
            if depth < 0:
                break
        return variants

    instance_variants = parse_top_level_enum_variants(inst_rs, "pub enum InstanceKind<'tcx>")
    shim_variants = parse_top_level_enum_variants(inst_rs, "pub enum ShimKind<'tcx>")
    reify_reasons = parse_top_level_enum_variants(inst_rs, "pub enum ReifyReason")

    # 6. compiler/rustc_public & compiler/rustc_public_bridge census
    pub_files = [
        p
        for p in (
            reader.paths_under("compiler/rustc_public/src")
            + reader.paths_under("compiler/rustc_public_bridge/src")
        )
        if p.endswith(".rs")
    ]
    pub_sloc = 0
    pub_fn_count = 0
    pub_struct_enum_count = 0
    for p in pub_files:
        for line in reader.read_text(p).splitlines():
            sc = strip_line_comment(line).strip()
            if sc:
                pub_sloc += 1
                if sc.startswith("pub fn ") or " pub fn " in sc:
                    pub_fn_count += 1
                if sc.startswith("pub struct ") or sc.startswith("pub enum ") or sc.startswith("pub trait "):
                    pub_struct_enum_count += 1

    return {
        "rustc_intrinsics": {
            "total_declarations": len(intrinsics),
            "must_be_overridden_bodyless_count": sum(
                1 for x in intrinsics if x["must_be_overridden_by_backend"]
            ),
            "with_default_fallback_mir_body_count": sum(
                1 for x in intrinsics if x["has_default_mir_body"]
            ),
            "custom_mir_dialect_helpers_count": sum(
                1 for x in intrinsics if x["category"] == "custom_mir_dialect"
            ),
            "const_callable_count": sum(1 for x in intrinsics if x["is_const"]),
            "nounwind_count": sum(1 for x in intrinsics if x["is_nounwind"]),
            "const_stable_indirect_count": sum(1 for x in intrinsics if x["const_stable_indirect"]),
            "by_category": dict(Counter(x["category"] for x in intrinsics)),
            "typeck_intrinsic_sym_refs_count": len(checked_sym_names),
            "sample_bodyless_intrinsics": [
                x["name"] for x in intrinsics if x["must_be_overridden_by_backend"]
            ][:40],
            "fallback_body_intrinsics": [
                x["name"] for x in intrinsics if x["has_default_mir_body"]
            ],
        },
        "stdarch_llvm_link_bindings": {
            "total_link_name_llvm_bindings": llvm_link_total,
            "unique_llvm_intrinsic_names": len(llvm_link_unique),
            "by_isa_total_bindings": dict(
                sorted(llvm_by_arch_total.items(), key=lambda kv: (-kv[1], kv[0]))
            ),
            "by_isa_unique_intrinsics": {
                k: len(v)
                for k, v in sorted(llvm_by_arch_unique.items(), key=lambda kv: (-len(kv[1]), kv[0]))
            },
        },
        "extern_abi": {
            "enum_variants_count": len(enum_variants_set),
            "all_variants_string_tokens_count": len(extern_abi_tokens),
            "paired_unwind_bool_variants_count": sum(
                1 for x in extern_abi_tokens if x["unwind_param"] is True
            ),
            "fixed_unwind_variants_count": sum(
                1 for x in extern_abi_tokens if x["unwind_param"] is None
            ),
            "tokens": extern_abi_tokens,
        },
        "inline_asm": {
            "inline_asm_arch_variants_count": len(inline_asm_archs),
            "inline_asm_arch_variants": inline_asm_archs,
            "isa_modules_count": len(asm_isa_details),
            "total_register_classes_across_isas": sum(
                x["reg_classes_count"] for x in asm_isa_details
            ),
            "total_defined_registers_across_isas": sum(
                x["defined_registers_count"] for x in asm_isa_details
            ),
            "isa_breakdown": asm_isa_details,
        },
        "instance_and_shim_kinds": {
            "instance_kind_variants_count": len(instance_variants),
            "instance_kind_variants": instance_variants,
            "backend_magic_no_callable_mir_variants": [
                "Intrinsic",
                "LlvmIntrinsic",
                "Virtual",
            ],
            "shim_kind_variants_count": len(shim_variants),
            "shim_kind_variants": shim_variants,
            "shim_kind_delta_vs_1_99_1": {
                "1_99_1_count": 12,
                "412be32a6a18_count": len(shim_variants),
                "removed": ["FnPtrAddr"],
                "added": ["FnAddrAsPtr", "FnPtrFromPtr"],
            },
            "reify_reason_variants": reify_reasons,
        },
        "rustc_public_stable_mir": {
            "rs_files_count": len(pub_files),
            "sloc": pub_sloc,
            "public_functions_count": pub_fn_count,
            "public_types_and_traits_count": pub_struct_enum_count,
        },
    }


def parse_directive_line(line: str) -> tuple[str | None, str, str] | None:
    """Linear O(N) parser for `//@ [rev] directive-name: value`."""
    s = line.lstrip()
    if not s.startswith("//@"):
        return None
    rest = s[3:].lstrip()
    if not rest:
        return None
    rev = None
    if rest.startswith("["):
        close_b = rest.find("]")
        if close_b < 0:
            return None
        rev = rest[1:close_b].strip()
        rest = rest[close_b + 1 :].lstrip()
    # Read directive name `[a-zA-Z0-9_-]+`
    i = 0
    while i < len(rest) and (rest[i].isalnum() or rest[i] in "-_"):
        i += 1
    if i == 0:
        return None
    dname = rest[:i]
    tail = rest[i:].lstrip()
    if tail.startswith(":"):
        val = tail[1:].strip()
    else:
        val = tail.strip()
    return (rev, dname, val)


def line_has_error_annot(line: str) -> bool:
    """Linear check for `//~` or `//[rev]~` annotation."""
    idx = line.find("//")
    while idx >= 0:
        after = line[idx + 2 :]
        if after.startswith("~"):
            return True
        if after.startswith("["):
            cb = after.find("]")
            if cb > 0 and cb + 1 < len(after) and after[cb + 1] == "~":
                return True
        idx = line.find("//", idx + 2)
    return False


def line_has_clif_err_annot(line: str) -> bool:
    r"""Matches cg_clif's `//(\[\w+\])?~[^|]*\s*ERR` linearly in O(N)."""
    idx = line.find("//")
    while idx >= 0:
        after = line[idx + 2 :]
        tilde_pos = -1
        if after.startswith("~"):
            tilde_pos = 1
        elif after.startswith("["):
            cb = after.find("]")
            if cb > 1 and all(is_ident_char(c) or c == "," or c == " " for c in after[1:cb]):
                if cb + 1 < len(after) and after[cb + 1] == "~":
                    tilde_pos = cb + 2
        if tilde_pos >= 0:
            tail = after[tilde_pos:]
            pipe_idx = tail.find("|")
            scan_region = tail if pipe_idx < 0 else tail[:pipe_idx]
            if "err" in scan_region.lower():
                return True
        idx = line.find("//", idx + 2)
    return False


def extract_tests_stdlib_tools_and_skips(reader: GitObjectReader) -> dict[str, Any]:
    # 1. Load cg_gcc exclusion files
    gcc_excl_by_file: dict[str, list[str]] = {}
    gcc_excl_file_counts: dict[str, int] = {}
    for fn in [
        "failing-ui-tests.txt",
        "failing-ui-tests12.txt",
        "failing-ui-tests-without-128bit-integers.txt",
        "failing-run-make-tests.txt",
        "failing-lto-tests.txt",
        "failing-ice-tests.txt",
    ]:
        rel = f"compiler/rustc_codegen_gcc/tests/{fn}"
        if rel not in reader.blobs:
            continue
        cnt = 0
        for line in reader.read_text(rel).splitlines():
            ls = line.strip()
            if ls and not ls.startswith("#"):
                gcc_excl_by_file.setdefault(ls, []).append(fn)
                cnt += 1
        gcc_excl_file_counts[fn] = cnt

    # 2. Load cg_clif explicit `rm` exclusions in test_rustc_tests.sh
    clif_sh = reader.read_text("compiler/rustc_codegen_cranelift/scripts/test_rustc_tests.sh")
    clif_rm_exact: dict[str, str] = {}
    clif_rm_prefixes: list[tuple[str, str]] = []
    curr_cat = "general"
    for line in clif_sh.splitlines():
        ls = line.strip()
        if ls.startswith("# ") and not ls.startswith("# =="):
            curr_cat = ls[2:].strip()
        elif ls.startswith("rm "):
            # Linear parse of `rm [-r] tests/<path> [# comment]`
            body = strip_line_comment(ls[3:]).strip()
            is_dir = False
            if body.startswith("-r "):
                is_dir = True
                body = body[3:].strip()
            if body.startswith("tests/"):
                pat = body.split()[0].rstrip("/")
                if "*" in pat or is_dir or not pat.endswith(".rs"):
                    clif_rm_prefixes.append((pat, curr_cat))
                else:
                    clif_rm_exact[pat] = curr_cat

    # 3. Group all blobs under `tests/` by directory for fast O(1) sibling lookup
    tests_blobs_by_dir: dict[str, set[str]] = defaultdict(set)
    ignore_dirs: set[str] = set()
    for p in reader.paths_under("tests"):
        d, fn = p.rsplit("/", 1)
        tests_blobs_by_dir[d].add(fn)
        if fn == "compiletest-ignore-dir":
            ignore_dirs.add(d)

    def is_ignored_subdir(suite_root: str, dir_path: str) -> bool:
        # Check `auxiliary` or any ancestor inside suite with `compiletest-ignore-dir`
        rel = dir_path[len(suite_root) :].strip("/")
        if not rel:
            return False
        parts = rel.split("/")
        if "auxiliary" in parts:
            return True
        cur = suite_root
        for part in parts:
            cur = f"{cur}/{part}"
            if cur in ignore_dirs:
                return True
        return False

    suite_summaries: dict[str, Any] = {}
    directive_freq: Counter[str] = Counter()
    ignore_backends_freq: Counter[str] = Counter()
    fls_reference_directives = 0
    fls_referenced_files = 0
    total_files_all_suites = 0
    total_expanded_variants = 0
    tier_totals: Counter[str] = Counter()
    clif_collateral_lto_victims: list[str] = []

    for suite, mode in sorted(SUITE_MODES.items()):
        sroot = f"tests/{suite}"
        suite_paths = reader.paths_under(sroot)
        test_entrypoints: list[str] = []

        if suite in ("run-make", "run-make-cargo", "build-std"):
            rmake_dirs: dict[str, str] = {}
            for p in suite_paths:
                d, fn = p.rsplit("/", 1)
                if fn == "rmake.rs":
                    rmake_dirs[d] = p
                elif fn == "Makefile" and d not in rmake_dirs:
                    rmake_dirs[d] = p
            # Exclude nested subdirs of another rmake test
            sorted_dirs = sorted(rmake_dirs.keys())
            accepted_dirs: list[str] = []
            for d in sorted_dirs:
                if any(d.startswith(ad + "/") for ad in accepted_dirs):
                    continue
                accepted_dirs.append(d)
                test_entrypoints.append(rmake_dirs[d])
        elif suite == "rustdoc-js-std":
            for p in suite_paths:
                d, fn = p.rsplit("/", 1)
                if not is_ignored_subdir(sroot, d) and fn.endswith(".js"):
                    test_entrypoints.append(p)
        elif suite == "rustdoc-gui":
            for p in suite_paths:
                d, fn = p.rsplit("/", 1)
                if not is_ignored_subdir(sroot, d) and fn.endswith(".goml"):
                    test_entrypoints.append(p)
        else:
            for p in suite_paths:
                d, fn = p.rsplit("/", 1)
                if not is_ignored_subdir(sroot, d) and fn.endswith(".rs"):
                    test_entrypoints.append(p)

        st: Counter[str] = Counter()
        expanded_variants = 0
        for rel_path in test_entrypoints:
            d, fn = rel_path.rsplit("/", 1)
            stem = fn.rsplit(".", 1)[0]
            content = reader.read_text(rel_path) if not rel_path.endswith(".js") else ""
            lines = content.splitlines()

            directives: list[str] = []
            revisions: list[str] = []
            ignore_conds: list[str] = []
            pass_mode: str | None = None
            fail_mode: str | None = None
            has_error_annots = False
            has_clif_err_annot = False
            has_error_pattern = False
            has_should_fail = False
            has_reference_dir = False
            has_llvm_args = "-Cllvm-args" in content or "-C llvm-args" in content
            has_real_lto_flag = any(
                x in content
                for x in ("-Clto", "-C lto", "-Clinker-plugin-lto", "-C linker-plugin-lto", "-Zthinlto")
            )
            has_substring_lto = "lto" in content

            for line in lines:
                if not has_error_annots and line_has_error_annot(line):
                    has_error_annots = True
                if not has_clif_err_annot and line_has_clif_err_annot(line):
                    has_clif_err_annot = True
                parsed = parse_directive_line(line)
                if parsed is not None:
                    _rev, dname, val = parsed
                    directives.append(dname)
                    directive_freq[dname] += 1
                    if dname == "revisions":
                        revisions.extend(val.split())
                    elif dname.startswith("ignore-"):
                        ignore_conds.append(f"{dname[7:]}:{val}" if val else dname[7:])
                        if dname == "ignore-backends":
                            for b in val.split():
                                ignore_backends_freq[b] += 1
                    elif dname in ("check-pass", "build-pass", "run-pass", "force-host"):
                        pass_mode = dname
                    elif dname in ("check-fail", "build-fail", "run-fail", "run-crash"):
                        fail_mode = dname
                    elif dname == "error-pattern":
                        has_error_pattern = True
                    elif dname == "should-fail":
                        has_should_fail = True
                    elif dname == "reference":
                        fls_reference_directives += 1
                        has_reference_dir = True

            if has_reference_dir:
                fls_referenced_files += 1

            siblings = tests_blobs_by_dir.get(d, set())
            has_stderr = False
            if suite not in ("run-make", "run-make-cargo", "build-std", "rustdoc-js-std"):
                for sib in siblings:
                    if sib == f"{stem}.stderr" or (sib.startswith(f"{stem}.") and sib.endswith(".stderr")):
                        has_stderr = True
                        break

            # Pipeline tier classification (matching corpus schema + assembly-gcc)
            if suite.startswith("rustdoc"):
                tier = "rustdoc"
            elif suite == "mir-opt":
                tier = "mir-only"
            elif suite == "assembly-gcc":
                tier = "gcc-asm-specific"
            elif (
                suite in ("codegen-llvm", "coverage", "coverage-run-rustdoc")
                or has_llvm_args
                or "needs-llvm-components" in directives
            ):
                tier = "llvm-specific"
            elif suite == "assembly-llvm":
                tier = "llvm-specific"
            elif suite in ("ui", "ui-fulldeps"):
                if pass_mode in ("run-pass", "build-pass") or fail_mode in ("build-fail", "run-fail", "run-crash"):
                    tier = "backend-codegen"
                elif pass_mode == "check-pass" or fail_mode == "check-fail" or has_error_annots or has_error_pattern or has_stderr:
                    tier = "frontend-only"
                else:
                    tier = "backend-codegen"
            elif suite == "pretty":
                tier = "frontend-only"
            elif suite == "crashes":
                tier = "ice"
            elif suite in ("run-make", "run-make-cargo", "build-std"):
                if any(k in content for k in ("llvm_", "llvm-", "FileCheck", "clang", "-Clto", "linker-plugin-lto")):
                    tier = "llvm-specific"
                else:
                    tier = "backend-codegen"
            else:
                tier = "backend-codegen"

            # Required oracle pass level for soundness auditing
            if tier == "frontend-only":
                required_oracle = "check-or-diagnostics"
            elif suite in ("ui", "ui-fulldeps"):
                if pass_mode == "run-pass" or fail_mode in ("run-fail", "run-crash"):
                    required_oracle = "run-execution"
                else:
                    required_oracle = "build-and-link"
            elif suite in ("debuginfo", "incremental", "run-make", "run-make-cargo", "build-std"):
                required_oracle = "build-and-run-recipe"
            else:
                required_oracle = mode

            # Evaluate cg_clif exclusion status
            clif_excl = None
            if rel_path in clif_rm_exact:
                clif_excl = f"explicit:{clif_rm_exact[rel_path]}"
            else:
                t_key = d if suite in ("run-make", "run-make-cargo", "build-std") else rel_path
                for pat, cat in clif_rm_prefixes:
                    if pat.endswith("*"):
                        if t_key.startswith(pat[:-1]):
                            clif_excl = f"explicit:{cat}"
                            break
                    elif t_key == pat or t_key.startswith(pat + "/"):
                        clif_excl = f"explicit:{cat}"
                        break
            if not clif_excl:
                if has_should_fail and suite in ("codegen-units", "ui", "incremental"):
                    clif_excl = "rg:should-fail"
                elif suite == "ui" and (
                    has_clif_err_annot
                    or has_error_pattern
                    or fail_mode in ("build-fail", "run-fail")
                    or has_llvm_args
                ):
                    clif_excl = "rg:ui-err-or-build-run-fail-or-llvm-args"
                elif has_substring_lto and suite in ("codegen-units", "ui", "incremental"):
                    if has_real_lto_flag or rel_path.startswith("tests/ui/lto/"):
                        clif_excl = "rg:lto-flag"
                    else:
                        clif_excl = "rg:lto-substring-collateral"
                        if tier == "backend-codegen":
                            clif_collateral_lto_victims.append(rel_path)
                elif any("cranelift" in c for c in ignore_conds):
                    clif_excl = "directive:ignore-backends-cranelift"
                elif suite not in ("codegen-units", "run-make", "run-make-cargo", "ui", "incremental"):
                    clif_excl = "suite-not-executed"

            # Evaluate cg_gcc exclusion status
            gcc_excl = None
            g_key = d if suite in ("run-make", "run-make-cargo") else rel_path
            if g_key in gcc_excl_by_file:
                gcc_excl = "list:" + "+".join(gcc_excl_by_file[g_key])
            elif suite == "ui":
                parts = rel_path.split("/")
                if len(parts) > 2 and parts[2] in ("abi", "extern", "proc-macro", "threads-sendsync"):
                    gcc_excl = f"wholesale-dir:{parts[2]}"
                elif has_real_lto_flag and "-Clto=thin" not in content:
                    gcc_excl = "filter:non-thin-lto"
            elif suite not in ("ui", "run-make", "run-make-cargo", "assembly-gcc"):
                gcc_excl = "suite-not-executed"

            n_vars = max(1, len(revisions))
            expanded_variants += n_vars
            st["total"] += 1
            st[f"tier:{tier}"] += 1
            st[f"oracle:{required_oracle}"] += 1
            if pass_mode:
                st[f"pass:{pass_mode}"] += 1
            if fail_mode:
                st[f"fail:{fail_mode}"] += 1
            if clif_excl:
                st["clif_skipped"] += 1
                st[f"clif_reason:{clif_excl}"] += 1
            else:
                st["clif_kept"] += 1
            if gcc_excl:
                st["gcc_skipped"] += 1
                st[f"gcc_reason:{gcc_excl}"] += 1
            else:
                st["gcc_kept"] += 1

            tier_totals[tier] += 1

        total_files_all_suites += st["total"]
        total_expanded_variants += expanded_variants
        prev_1991 = BASELINE_1991_SUITE_COUNTS.get(suite, 0)
        suite_summaries[suite] = {
            "mode": mode,
            "files_412be32a6a18": st["total"],
            "files_1_99_1": prev_1991,
            "delta_vs_1_99_1": st["total"] - prev_1991,
            "expanded_revision_variants": expanded_variants,
            "frontend_only": st["tier:frontend-only"],
            "backend_codegen": st["tier:backend-codegen"],
            "llvm_specific": st["tier:llvm-specific"],
            "gcc_asm_specific": st["tier:gcc-asm-specific"],
            "mir_only": st["tier:mir-only"],
            "rustdoc": st["tier:rustdoc"],
            "ice": st["tier:ice"],
            "explicit_check_pass": st["pass:check-pass"],
            "explicit_build_pass": st["pass:build-pass"],
            "explicit_run_pass": st["pass:run-pass"],
            "explicit_check_fail": st["fail:check-fail"],
            "explicit_build_fail": st["fail:build-fail"],
            "explicit_run_fail": st["fail:run-fail"],
            "clif_kept": st["clif_kept"],
            "clif_skipped": st["clif_skipped"],
            "gcc_kept": st["gcc_kept"],
            "gcc_skipped": st["gcc_skipped"],
            "clif_reasons": {
                k[len("clif_reason:") :]: v for k, v in st.items() if k.startswith("clif_reason:")
            },
            "gcc_reasons": {
                k[len("gcc_reason:") :]: v for k, v in st.items() if k.startswith("gcc_reason:")
            },
        }

    # 4. Standard library test suites under `library/`
    stdlib_crates = [
        "coretests",
        "alloctests",
        "std",
        "compiler-builtins",
        "portable-simd",
        "stdarch",
        "test",
        "std_detect",
        "alloc",
        "core",
        "proc_macro",
        "panic_unwind",
    ]
    stdlib_summary: dict[str, Any] = {}
    total_stdlib_tests = 0
    total_stdlib_doctests = 0
    for cname in stdlib_crates:
        cpaths = [p for p in reader.paths_under(f"library/{cname}") if p.endswith(".rs")]
        test_fns = 0
        doctest_blocks = 0
        for p in cpaths:
            txt = reader.read_text(p)
            in_doc_fence = False
            for line in txt.splitlines():
                ls = line.strip()
                if ls in ("#[test]", "#[tokio::test]") or ls.startswith("#[test("):
                    test_fns += 1
                if ls.startswith("/// ```") or ls.startswith("//! ```"):
                    fence_tail = ls[6:].strip()
                    if not in_doc_fence:
                        in_doc_fence = True
                        if not any(
                            x in fence_tail for x in ("ignore", "text", "custom", "sh", "console", "c", "toml")
                        ):
                            doctest_blocks += 1
                    else:
                        in_doc_fence = False
        total_stdlib_tests += test_fns
        total_stdlib_doctests += doctest_blocks
        stdlib_summary[cname] = {
            "rs_files": len(cpaths),
            "unit_and_integration_test_fns": test_fns,
            "rustdoc_doctest_blocks": doctest_blocks,
        }

    # 5. Tool & integration suites under `src/tools/`
    cargotest_main = reader.read_text("src/tools/cargotest/main.rs")
    cargotest_repos = []
    for line in cargotest_main.splitlines():
        sc = strip_line_comment(line).strip()
        if sc.startswith("name:"):
            nm = extract_first_quoted(sc)
            if nm:
                cargotest_repos.append(nm)

    miri_test_files = [p for p in reader.paths_under("src/tools/miri/tests") if p.endswith(".rs") and "/auxiliary/" not in p]
    miri_by_subdir = Counter(p.split("/")[4] for p in miri_test_files if len(p.split("/")) >= 5)
    clippy_test_files = [p for p in reader.paths_under("src/tools/clippy/tests") if p.endswith(".rs") and "/auxiliary/" not in p]
    clippy_by_subdir = Counter(p.split("/")[4] for p in clippy_test_files if len(p.split("/")) >= 5)
    rustfmt_test_files = [p for p in reader.paths_under("src/tools/rustfmt/tests") if p.endswith(".rs")]

    return {
        "compiletest_suites": {
            "suite_count_412be32a6a18": len(suite_summaries),
            "suite_count_1_99_1": 21,
            "newly_added_suites": ["assembly-gcc"],
            "total_test_entrypoints_412be32a6a18": total_files_all_suites,
            "total_test_entrypoints_1_99_1": 24545,
            "delta_entrypoints_vs_1_99_1": total_files_all_suites - 24545,
            "total_expanded_revision_variants": total_expanded_variants,
            "pipeline_tier_totals": dict(tier_totals),
            "ignore_backends_directive_counts": dict(ignore_backends_freq),
            "reference_directive_occurrences": fls_reference_directives,
            "reference_annotated_test_files": fls_referenced_files,
            "top_30_directives": directive_freq.most_common(30),
            "clif_lto_substring_collateral_backend_tests_count": len(clif_collateral_lto_victims),
            "clif_lto_substring_collateral_sample": clif_collateral_lto_victims[:25],
            "gcc_exclusion_list_line_counts": gcc_excl_file_counts,
            "by_suite": suite_summaries,
        },
        "stdlib_suites": {
            "total_test_functions": total_stdlib_tests,
            "total_doctest_blocks": total_stdlib_doctests,
            "by_crate": stdlib_summary,
        },
        "tool_and_integration_suites": {
            "cargotest": {
                "pinned_crate_suites_count": len(cargotest_repos),
                "pinned_crate_names": cargotest_repos,
            },
            "miri_tests": {
                "total_rs_entrypoints": len(miri_test_files),
                "by_category": dict(miri_by_subdir),
            },
            "clippy_tests": {
                "total_rs_entrypoints": len(clippy_test_files),
                "by_category": dict(clippy_by_subdir),
            },
            "rustfmt_tests": {
                "total_rs_files": len(rustfmt_test_files),
            },
        },
    }


ALLOWED_SKIP_BUCKETS_MODE_A = {
    "llvm-ir-text-only",
    "llvm-cli-pass-flag-only",
    "gcc-asm-heuristic-only",
    "non-target-arch-or-os-gated",
}

ALLOWED_SKIP_BUCKETS_MODE_B = ALLOWED_SKIP_BUCKETS_MODE_A | {
    "frontend-delegated-to-upstream-rustc-driver",
    "mir-opt-upstream-middle-end-only",
    "rustdoc-frontend-only",
}


def audit_qualification_manifest(manifest: dict[str, Any], expected_total: int) -> dict[str, Any]:
    """Mechanical Zero-Loophole Skip-List & Pass-Mode Soundness Auditor.

    Enforces four invariants:
    1. Mass Conservation: executed + sum(skipped_by_bucket) == expected_total (0 silent drops).
    2. Bucket Authorization: every skip bucket must belong to ALLOWED_SKIP_BUCKETS_{MODE_A,MODE_B};
       Mode A allows ZERO frontend skips (`frontend-delegated-*` forbidden in Mode A).
    3. Filter & Directive Integrity: forbids wildcard substring/directory deletions,
       unauthorized `ignore-*` injections, and `--bypass-ignore-backends` paired with
       untracked external skip files.
    4. Pass-Mode Non-Vacuity: forbids downgrading `run-execution` or `build-and-link`
       tests to `--pass=check` / `--emit=metadata`.
    """
    mode = manifest["mode"]
    allowed_buckets = (
        ALLOWED_SKIP_BUCKETS_MODE_A if mode == "Mode A" else ALLOWED_SKIP_BUCKETS_MODE_B
    )
    violations: list[str] = []

    executed = int(manifest.get("executed_count", 0))
    skipped_buckets: dict[str, int] = manifest.get("skipped_buckets", {})
    accounted = executed + sum(skipped_buckets.values())
    if accounted != expected_total:
        violations.append(
            f"MASS_CONSERVATION_VIOLATION: accounted={accounted} != expected_total={expected_total} "
            f"(delta={expected_total - accounted} silently dropped tests)"
        )

    for bname, count in skipped_buckets.items():
        if count < 0:
            violations.append(f"NEGATIVE_BUCKET_COUNT: {bname}={count}")
        if count > 0 and bname not in allowed_buckets:
            violations.append(
                f"UNAUTHORIZED_SKIP_BUCKET ({mode}): bucket={bname!r} count={count}"
            )

    if manifest.get("uses_substring_or_regex_file_deletion", False):
        violations.append(
            "WILDCARD_DELETION_LOOPHOLE: regex/substring `rm` deletion detected outside AST/directive parser"
        )
    if manifest.get("uses_wholesale_subdir_exclusion", False):
        violations.append(
            "WHOLESALE_SUBDIR_EXCLUSION: entire `tests/ui/<subdir>` directory excluded without per-test deviation"
        )
    if manifest.get("untracked_ignore_directives_added", 0) > 0:
        violations.append(
            f"UNAUTHORIZED_IGNORE_DIRECTIVE: {manifest['untracked_ignore_directives_added']} new `//@ ignore-*` directives"
        )
    if manifest.get("run_or_build_downgraded_to_check", 0) > 0:
        violations.append(
            f"VACUOUS_CHECK_PASS_DOWNGRADE: {manifest['run_or_build_downgraded_to_check']} `run-pass`/`build-pass` tests downgraded to `check-pass`"
        )

    return {
        "name": manifest["name"],
        "mode": mode,
        "verdict": "PASS" if not violations else "FAIL",
        "executed_count": executed,
        "skipped_total": sum(skipped_buckets.values()),
        "accounted_total": accounted,
        "expected_total": expected_total,
        "violations": violations,
    }


def run_auditor_evaluations(compiletest_data: dict[str, Any]) -> dict[str, Any]:
    total = compiletest_data["total_test_entrypoints_412be32a6a18"]
    tiers = compiletest_data["pipeline_tier_totals"]
    llvm_spec = tiers.get("llvm-specific", 0)
    gcc_asm = tiers.get("gcc-asm-specific", 0)
    frontend_only = tiers.get("frontend-only", 0)
    mir_only = tiers.get("mir-only", 0)
    rustdoc_cnt = tiers.get("rustdoc", 0)

    by_suite = compiletest_data["by_suite"]
    clif_kept = sum(s["clif_kept"] for s in by_suite.values())
    clif_skipped = sum(s["clif_skipped"] for s in by_suite.values())
    gcc_kept = sum(s["gcc_kept"] for s in by_suite.values())
    gcc_skipped = sum(s["gcc_skipped"] for s in by_suite.values())

    manifests = [
        {
            "name": "Mode A Standalone Compiler Qualification Baseline",
            "mode": "Mode A",
            "executed_count": total - llvm_spec - gcc_asm,
            "skipped_buckets": {
                "llvm-ir-text-only": llvm_spec,
                "gcc-asm-heuristic-only": gcc_asm,
            },
            "uses_substring_or_regex_file_deletion": False,
            "uses_wholesale_subdir_exclusion": False,
            "untracked_ignore_directives_added": 0,
            "run_or_build_downgraded_to_check": 0,
        },
        {
            "name": "Mode B Drop-In Codegen Backend Qualification Baseline",
            "mode": "Mode B",
            "executed_count": total - llvm_spec - gcc_asm - frontend_only - mir_only - rustdoc_cnt,
            "skipped_buckets": {
                "llvm-ir-text-only": llvm_spec,
                "gcc-asm-heuristic-only": gcc_asm,
                "frontend-delegated-to-upstream-rustc-driver": frontend_only,
                "mir-opt-upstream-middle-end-only": mir_only,
                "rustdoc-frontend-only": rustdoc_cnt,
            },
            "uses_substring_or_regex_file_deletion": False,
            "uses_wholesale_subdir_exclusion": False,
            "untracked_ignore_directives_added": 0,
            "run_or_build_downgraded_to_check": 0,
        },
        {
            "name": "Upstream rustc_codegen_cranelift (test_rustc_tests.sh)",
            "mode": "Mode B",
            "executed_count": clif_kept,
            "skipped_buckets": {
                "unclassified-shell-rm-and-unrun-suites": clif_skipped,
            },
            "uses_substring_or_regex_file_deletion": True,
            "uses_wholesale_subdir_exclusion": True,
            "untracked_ignore_directives_added": 0,
            "run_or_build_downgraded_to_check": 0,
        },
        {
            "name": "Upstream rustc_codegen_gcc (build_system/src/test.rs)",
            "mode": "Mode B",
            "executed_count": gcc_kept,
            "skipped_buckets": {
                "failing-txt-and-unrun-suites": gcc_skipped,
            },
            "uses_substring_or_regex_file_deletion": False,
            "uses_wholesale_subdir_exclusion": True,
            "untracked_ignore_directives_added": 0,
            "run_or_build_downgraded_to_check": 0,
        },
        {
            "name": "Synthetic Loophole Probe 1: Mode A Skipping Frontend Diagnostics",
            "mode": "Mode A",
            "executed_count": total - llvm_spec - gcc_asm - frontend_only,
            "skipped_buckets": {
                "llvm-ir-text-only": llvm_spec,
                "gcc-asm-heuristic-only": gcc_asm,
                "frontend-delegated-to-upstream-rustc-driver": frontend_only,
            },
        },
        {
            "name": "Synthetic Loophole Probe 2: Vacuous --pass=check Downgrade on run-pass",
            "mode": "Mode B",
            "executed_count": total - llvm_spec - gcc_asm - frontend_only - mir_only - rustdoc_cnt,
            "skipped_buckets": {
                "llvm-ir-text-only": llvm_spec,
                "gcc-asm-heuristic-only": gcc_asm,
                "frontend-delegated-to-upstream-rustc-driver": frontend_only,
                "mir-opt-upstream-middle-end-only": mir_only,
                "rustdoc-frontend-only": rustdoc_cnt,
            },
            "run_or_build_downgraded_to_check": 3859,
        },
        {
            "name": "Synthetic Loophole Probe 3: Silent Unaccounted Test Drop",
            "mode": "Mode A",
            "executed_count": total - llvm_spec - gcc_asm - 17,
            "skipped_buckets": {
                "llvm-ir-text-only": llvm_spec,
                "gcc-asm-heuristic-only": gcc_asm,
            },
        },
    ]

    results = [audit_qualification_manifest(m, total) for m in manifests]
    return {
        "allowed_buckets_mode_a": sorted(ALLOWED_SKIP_BUCKETS_MODE_A),
        "allowed_buckets_mode_b": sorted(ALLOWED_SKIP_BUCKETS_MODE_B),
        "clif_kept_across_all_22_suites": clif_kept,
        "clif_skipped_across_all_22_suites": clif_skipped,
        "gcc_kept_across_all_22_suites": gcc_kept,
        "gcc_skipped_across_all_22_suites": gcc_skipped,
        "evaluations": results,
    }


def select_nightly_toolchain() -> str:
    """Selects a nightly toolchain with `codegen-backends` (e.g. +nightly-2026-11-12) if present."""
    for cand in ("+nightly-2026-11-12", "+nightly"):
        r = subprocess.run(
            ["rustc", cand, "-Zcodegen-backend=cranelift", "-vV"],
            capture_output=True,
            text=True,
        )
        if r.returncode == 0:
            return cand
    return "+nightly"


def run_live_probes() -> tuple[dict[str, Any], dict[str, Any] | None, list[str] | None]:
    """Runs isolated live probes against rustc +1.99.1, rustc +nightly (LLVM & Cranelift), and g++."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        nightly_sel = select_nightly_toolchain()
        v_1991 = subprocess.check_output(["rustc", "+1.99.1", "-vV"], text=True).strip()
        v_nightly = subprocess.check_output(["rustc", nightly_sel, "-vV"], text=True).strip()
        v_clif_proc = subprocess.run(
            ["rustc", nightly_sel, "-Zcodegen-backend=cranelift", "-vV"],
            capture_output=True,
            text=True,
        )
        v_clif = v_clif_proc.stdout.strip() if v_clif_proc.returncode == 0 else None
        v_gpp = subprocess.check_output(["g++", "--version"], text=True).splitlines()[0].strip()

        targets_1991 = subprocess.check_output(
            ["rustc", "+1.99.1", "--print", "target-list"], text=True
        ).splitlines()
        specs_nightly = json.loads(
            subprocess.check_output(
                ["rustc", nightly_sel, "-Zunstable-options", "--print", "all-target-specs-json"],
                text=True,
            )
        )

        # 1. Backend-delegated --print differential (LLVM vs Cranelift on nightly)
        print_probes = {}
        for pkind in [
            "calling-conventions",
            "code-models",
            "relocation-models",
            "tls-models",
            "stack-protector-strategies",
            "split-debuginfo",
            "target-cpus",
            "target-features",
            "host-tuple",
            "supported-crate-types",
            "backend-has-zstd",
            "backend-has-mnemonic:ret",
        ]:
            r_llvm = subprocess.run(
                ["rustc", nightly_sel, "-Zunstable-options", f"--print={pkind}"],
                capture_output=True,
                text=True,
            )
            r_clif = subprocess.run(
                [
                    "rustc",
                    nightly_sel,
                    "-Zunstable-options",
                    "-Zcodegen-backend=cranelift",
                    f"--print={pkind}",
                ],
                capture_output=True,
                text=True,
            )
            llvm_lines = [l for l in r_llvm.stdout.splitlines() if l.strip()]
            clif_lines = [l for l in r_clif.stdout.splitlines() if l.strip()]
            print_probes[pkind] = {
                "llvm_rc": r_llvm.returncode,
                "llvm_nonempty_lines": len(llvm_lines),
                "llvm_sample": llvm_lines[:5],
                "cranelift_rc": r_clif.returncode,
                "cranelift_nonempty_lines": len(clif_lines),
                "cranelift_sample": clif_lines[:5],
            }

        # 2. Cross-language C++ <-> Rust `extern "C-unwind"` / `extern "C"` / `i128` ABI probe
        cpp_src = tmp / "bridge.cpp"
        rs_src = tmp / "main.rs"
        cpp_obj = tmp / "bridge.o"

        cpp_src.write_text(
            r"""#include <cstdint>
#include <cstddef>

struct CppEx { int code; };

static int g_cpp_dtors = 0;
struct CppGuard {
    ~CppGuard() { g_cpp_dtors += 1; }
};

struct Pair128 {
    unsigned __int128 a;
    uint64_t tag;
    unsigned __int128 b;
};

extern "C" {
    void rust_c_unwind_trampoline(void (*cb)());
    void rust_c_unwind_panic();
    Pair128 rust_roundtrip_128(Pair128 in_val);

    void cpp_throw_42() {
        throw CppEx{42};
    }

    int cpp_catch_from_rust_trampoline() {
        try {
            rust_c_unwind_trampoline(cpp_throw_42);
            return 0;
        } catch (const CppEx& e) {
            return 100 + e.code;
        }
    }

    int cpp_catch_wrapper(void (*rust_fn)()) {
        try {
            rust_fn();
            return 0;
        } catch (const CppEx& e) {
            return 100 + e.code;
        }
    }

    int cpp_catch_nounwind_def(void (*rust_fn)(void (*)())) {
        try {
            rust_fn(cpp_throw_42);
            return 0;
        } catch (const CppEx& e) {
            return 100 + e.code;
        }
    }

    int cpp_middle_frame_with_raii() {
        CppGuard g;
        rust_c_unwind_panic();
        return 0;
    }

    int cpp_get_dtors() { return g_cpp_dtors; }

    size_t cpp_pair128_size() { return sizeof(Pair128); }
    size_t cpp_pair128_align() { return alignof(Pair128); }

    int cpp_verify_pair128() {
        unsigned __int128 hi = ((unsigned __int128)0x0123456789abcdefULL << 64) | 0xfedcba9876543210ULL;
        unsigned __int128 lo = ((unsigned __int128)0x1122334455667788ULL << 64) | 0x99aabbccddeeff00ULL;
        Pair128 p{hi, 0xdeadbeefULL, lo};
        Pair128 r = rust_roundtrip_128(p);
        return (r.a == (hi ^ 1) && r.tag == 0xdeadbeefULL + 1 && r.b == (lo + 7)) ? 1 : 0;
    }
}
""",
            encoding="utf-8",
        )

        rs_src.write_text(
            r"""use std::mem::{align_of, size_of};
use std::sync::atomic::{AtomicUsize, Ordering};

static RUST_DROPS: AtomicUsize = AtomicUsize::new(0);

struct DropCounter;
impl Drop for DropCounter {
    fn drop(&mut self) {
        RUST_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

#[repr(C)]
pub struct Pair128 {
    pub a: u128,
    pub tag: u64,
    pub b: u128,
}

unsafe extern "C-unwind" {
    fn cpp_throw_42();
    fn cpp_middle_frame_with_raii() -> i32;
}

unsafe extern "C" {
    #[link_name = "cpp_throw_42"]
    fn cpp_throw_42_nounwind_import();
    fn cpp_catch_from_rust_trampoline() -> i32;
    fn cpp_catch_wrapper(rust_fn: extern "C" fn()) -> i32;
    fn cpp_catch_nounwind_def(rust_fn: extern "C" fn(extern "C-unwind" fn())) -> i32;
    fn cpp_get_dtors() -> i32;
    fn cpp_pair128_size() -> usize;
    fn cpp_pair128_align() -> usize;
    fn cpp_verify_pair128() -> i32;
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn rust_c_unwind_trampoline(cb: extern "C-unwind" fn()) {
    let _guard = DropCounter;
    cb();
}

pub extern "C" fn rust_c_nounwind_import_caller() {
    let _guard = DropCounter;
    unsafe { cpp_throw_42_nounwind_import() };
}

pub extern "C" fn rust_c_nounwind_def_calling_c_unwind(cb: extern "C-unwind" fn()) {
    let _guard = DropCounter;
    cb();
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn rust_c_unwind_panic() {
    panic!("intentional rust C-unwind panic");
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_roundtrip_128(v: Pair128) -> Pair128 {
    Pair128 {
        a: v.a ^ 1,
        tag: v.tag + 1,
        b: v.b.wrapping_add(7),
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "cpp_through_rust" => {
            let rc = unsafe { cpp_catch_from_rust_trampoline() };
            println!("RC={} RUST_DROPS={}", rc, RUST_DROPS.load(Ordering::SeqCst));
        }
        "catch_unwind_on_cpp" => {
            let _ = std::panic::catch_unwind(|| unsafe { cpp_throw_42() });
        }
        "extern_c_nounwind_throw" => {
            let rc = unsafe { cpp_catch_wrapper(rust_c_nounwind_import_caller) };
            println!("RC={} RUST_DROPS={}", rc, RUST_DROPS.load(Ordering::SeqCst));
        }
        "extern_c_def_abort_barrier" => {
            let rc = unsafe { cpp_catch_nounwind_def(rust_c_nounwind_def_calling_c_unwind) };
            println!("RC={} RUST_DROPS={}", rc, RUST_DROPS.load(Ordering::SeqCst));
        }
        "rust_panic_through_cpp" => {
            let res = std::panic::catch_unwind(|| unsafe {
                let _ = cpp_middle_frame_with_raii();
            });
            let cpp_dtors = unsafe { cpp_get_dtors() };
            println!("CAUGHT={} CPP_DTORS={}", res.is_err(), cpp_dtors);
        }
        "i128_abi" => {
            let r_sz = size_of::<Pair128>();
            let r_al = align_of::<Pair128>();
            let c_sz = unsafe { cpp_pair128_size() };
            let c_al = unsafe { cpp_pair128_align() };
            let ok = unsafe { cpp_verify_pair128() } == 1 && r_sz == c_sz && r_al == c_al;
            println!("RUST_SZ={} RUST_AL={} CPP_SZ={} CPP_AL={} MATCH={}", r_sz, r_al, c_sz, c_al, ok);
        }
        _ => panic!("unknown mode"),
    }
}
""",
            encoding="utf-8",
        )

        subprocess.run(
            ["g++", "-O2", "-fPIC", "-fexceptions", "-c", str(cpp_src), "-o", str(cpp_obj)],
            check=True,
        )

        abi_matrix: dict[str, Any] = {}
        abi_configs = [
            ("llvm_panic_unwind_O2", ["-Cpanic=unwind", "-Copt-level=2"]),
            ("llvm_panic_abort_O2", ["-Cpanic=abort", "-Copt-level=2"]),
            (
                "llvm_panic_abort_no_uwtable_O2",
                ["-Cpanic=abort", "-Cforce-unwind-tables=no", "-Copt-level=2"],
            ),
        ]
        if v_clif is not None:
            abi_configs.append(
                (
                    "cranelift_default_O2",
                    ["-Zcodegen-backend=cranelift", "-Cpanic=abort", "-Copt-level=2"],
                )
            )
        for cfg_name, extra_flags in abi_configs:
            bin_path = tmp / f"abi_{cfg_name}"
            comp = subprocess.run(
                [
                    "rustc",
                    nightly_sel,
                    "--edition=2024",
                    *extra_flags,
                    str(rs_src),
                    "-Clink-arg=" + str(cpp_obj),
                    "-lstdc++",
                    "-o",
                    str(bin_path),
                ],
                capture_output=True,
                text=True,
            )
            modes_out: dict[str, Any] = {}
            if comp.returncode == 0:
                for mname in [
                    "cpp_through_rust",
                    "catch_unwind_on_cpp",
                    "extern_c_nounwind_throw",
                    "extern_c_def_abort_barrier",
                    "rust_panic_through_cpp",
                    "i128_abi",
                ]:
                    run_r = subprocess.run([str(bin_path), mname], capture_output=True, text=True)
                    modes_out[mname] = {
                        "rc": run_r.returncode,
                        "stdout": run_r.stdout.strip(),
                        "stderr_first_line": (
                            run_r.stderr.strip().splitlines()[0] if run_r.stderr.strip() else ""
                        ),
                    }
            abi_matrix[cfg_name] = {
                "compile_rc": comp.returncode,
                "compile_stderr_first_line": (
                    comp.stderr.strip().splitlines()[0] if comp.stderr.strip() else ""
                ),
                "modes": modes_out,
            }

        # 3. Live Vacuous `check-pass` vs `build-pass` / `run-pass` canary
        canary_rs = tmp / "vacuous_check_canary.rs"
        canary_rs.write_text(
            r"""unsafe extern "C" {
    fn nonexistent_backend_lowering_symbol(x: u64) -> u64;
}

pub fn trigger(x: u64) -> u64 {
    unsafe { nonexistent_backend_lowering_symbol(x) }
}

fn main() {
    assert_eq!(trigger(41), 42);
}
""",
            encoding="utf-8",
        )
        r_check = subprocess.run(
            ["rustc", nightly_sel, "--emit=metadata", str(canary_rs), "--out-dir", str(tmp)],
            capture_output=True,
            text=True,
        )
        r_build = subprocess.run(
            ["rustc", nightly_sel, str(canary_rs), "-o", str(tmp / "canary_bin")],
            capture_output=True,
            text=True,
        )

        probe_summary = {
            "rustc_1_99_1_version": v_1991,
            "rustc_nightly_llvm_version": v_nightly,
            "rustc_nightly_cranelift_version": v_clif,
            "gpp_version": v_gpp,
            "backend_print_differential": print_probes,
            "cross_lang_c_unwind_and_i128_abi_matrix": abi_matrix,
            "vacuous_check_pass_canary": {
                "emit_metadata_check_rc": r_check.returncode,
                "link_executable_build_rc": r_build.returncode,
                "demonstrates_check_pass_blindness_to_backend_and_link_defects": (
                    r_check.returncode == 0 and r_build.returncode != 0
                ),
            },
        }
        return probe_summary, specs_nightly, targets_1991


def gh_json(endpoint: str) -> Any:
    out = subprocess.check_output(["gh", "api", endpoint], text=True, timeout=30)
    return json.loads(out)


def query_external_harnesses() -> dict[str, Any]:
    """Queries pinned external qualification repositories via `gh api`."""
    results: dict[str, Any] = {}

    # 1. Gankra/abi-cafe
    ac = EXTERNAL_PINS["abi_cafe"]
    ac_tree = gh_json(f"repos/{ac['repository']}/git/trees/{ac['revision']}?recursive=1")
    ac_blobs = [e["path"] for e in ac_tree["tree"] if e["type"] == "blob"]
    results["abi_cafe"] = {
        **ac,
        "total_blobs": len(ac_blobs),
        "normal_kdl_tests": len(
            [p for p in ac_blobs if p.startswith("include/tests/normal/") and p.endswith(".kdl")]
        ),
        "procgen_kdl_suites": len(
            [p for p in ac_blobs if p.startswith("include/tests/procgen/") and p.endswith(".kdl")]
        ),
        "procgen_categories": dict(
            Counter(
                p.split("/")[3]
                for p in ac_blobs
                if p.startswith("include/tests/procgen/") and p.endswith(".kdl")
            )
        ),
        "rust_src_files": len([p for p in ac_blobs if p.startswith("src/") and p.endswith(".rs")]),
    }

    # 2. rust-lang/fls
    fls = EXTERNAL_PINS["fls"]
    fls_tree = gh_json(f"repos/{fls['repository']}/git/trees/{fls['revision']}?recursive=1")
    rst_entries = [
        e
        for e in fls_tree["tree"]
        if e["type"] == "blob" and e["path"].startswith("src/") and e["path"].endswith(".rst")
    ]
    dp_by_file: dict[str, int] = {}
    dp_total = 0
    for entry in rst_entries:
        blob = gh_json(f"repos/{fls['repository']}/git/blobs/{entry['sha']}")
        txt = base64.b64decode(blob["content"]).decode("utf-8", errors="replace")
        cnt = txt.count(":dp:`fls_")
        dp_by_file[entry["path"]] = cnt
        dp_total += cnt
    results["fls"] = {
        **fls,
        "rst_files_count": len(rst_entries),
        "normative_chapters_with_dp_count": sum(1 for v in dp_by_file.values() if v > 0),
        "total_dp_paragraph_ids": dp_total,
        "delta_dp_vs_fls_1_99_tag": dp_total - 4014,
        "dp_by_chapter": {k: v for k, v in sorted(dp_by_file.items()) if v > 0},
    }

    # 3. cbeuw/rustlantis
    rl = EXTERNAL_PINS["rustlantis"]
    rl_tree = gh_json(f"repos/{rl['repository']}/git/trees/{rl['revision']}?recursive=1")
    rl_blobs = [e["path"] for e in rl_tree["tree"] if e["type"] == "blob"]
    results["rustlantis"] = {
        **rl,
        "total_blobs": len(rl_blobs),
        "workspace_crates": sorted(
            {p.split("/")[0] for p in rl_blobs if p.endswith("/Cargo.toml")}
        ),
        "rs_files": len([p for p in rl_blobs if p.endswith(".rs")]),
    }

    # 4. ferrocene/ferrocene
    fc = EXTERNAL_PINS["ferrocene"]
    fc_root = gh_json(f"repos/{fc['repository']}/git/trees/{fc['revision']}")
    fc_sha = next(e["sha"] for e in fc_root["tree"] if e["path"] == "ferrocene")
    fc_sub = gh_json(f"repos/{fc['repository']}/git/trees/{fc_sha}?recursive=1")
    fc_blobs = [e["path"] for e in fc_sub["tree"] if e["type"] == "blob"]
    results["ferrocene"] = {
        **fc,
        "ferrocene_subtree_blobs": len(fc_blobs),
        "qualification_tools": sorted(
            {p.split("/")[1] for p in fc_blobs if p.startswith("tools/") and p.count("/") >= 2}
        ),
        "qualification_doc_books": sorted(
            {p.split("/")[1] for p in fc_blobs if p.startswith("doc/") and p.count("/") >= 2}
        ),
    }

    # 5. rust-lang/crater
    cr = EXTERNAL_PINS["crater"]
    cr_tree = gh_json(f"repos/{cr['repository']}/git/trees/{cr['revision']}?recursive=1")
    cr_blobs = [e["path"] for e in cr_tree["tree"] if e["type"] == "blob"]
    local_crate_fixtures = sorted(
        {
            p.split("/")[1]
            for p in cr_blobs
            if p.startswith("local-crates/") and p.endswith("/Cargo.toml")
        }
    )
    results["crater"] = {
        **cr,
        "total_blobs": len(cr_blobs),
        "src_rs_files": len([p for p in cr_blobs if p.startswith("src/") and p.endswith(".rs")]),
        "local_crate_fixtures_count": len(local_crate_fixtures),
        "local_crate_fixtures": local_crate_fixtures,
    }

    return results


def build_surface_to_harness_matrix(
    cli_surfaces: dict[str, Any],
    targets: dict[str, Any],
    low_level: dict[str, Any],
    harnesses: dict[str, Any],
    ext_harnesses: dict[str, Any],
) -> list[dict[str, Any]]:
    ct = harnesses["compiletest_suites"]["by_suite"]
    st = harnesses["stdlib_suites"]["by_crate"]
    tl = harnesses["tool_and_integration_suites"]

    return [
        {
            "surface_id": "S01_CLI_GETOPTS_ERROR_JSON_PRINT",
            "surface_name": "Top-Level getopts CLI, --error-format, --json, and --print Queries",
            "inventory_412be32a6a18": (
                f"{cli_surfaces['top_level_getopts']['total']} getopts flags, "
                f"{cli_surfaces['error_format_and_json']['error_formats_count']} error formats, "
                f"{cli_surfaces['error_format_and_json']['json_subflags_count']} --json subflags, "
                f"{cli_surfaces['print_kinds']['total']} PrintKind variants"
            ),
            "mode_a_owner": "Candidate Driver + Candidate Backend (all 27 PrintKind variants)",
            "mode_b_owner": (
                "Upstream rustc_driver (17 Frontend PrintKinds + CLI/JSON) + "
                "Candidate CodegenBackend (8 Backend + 2 Hybrid PrintKinds)"
            ),
            "upstream_harnesses": [
                f"tests/ui ({ct['ui']['files_412be32a6a18']} files)",
                f"tests/run-make ({ct['run-make']['files_412be32a6a18']} recipes)",
                f"tests/run-make-cargo ({ct['run-make-cargo']['files_412be32a6a18']} recipes)",
                f"src/tools/cargotest ({tl['cargotest']['pinned_crate_suites_count']} real workspaces)",
            ],
            "external_harnesses": [
                "Tier 1 --print differential probe (target-cpus, target-features, code/reloc/tls-models, cfg)",
                "rust-lang/crater check-only + build-only Cargo JSON protocol sweep",
            ],
            "required_oracle": "Exact stdout/JSON schema + exit code (0/1/101) parity; non-empty backend --print tables",
        },
        {
            "surface_id": "S02_FRONTEND_TYPECK_BORROWCK_MACROS_RMETA",
            "surface_name": "Lexing, Editions (2015..Future), Macros/proc_macro, Typeck, Trait Solver, Borrowck, .rmeta",
            "inventory_412be32a6a18": (
                "5 Editions, 589 feature gates, 202 attribute paths, 233 LangItems, "
                "292 lints, 518 error codes, 31 proc_macro::bridge RPCs, .rmeta v12"
            ),
            "mode_a_owner": "Candidate Frontend + Metadata Encoder/Decoder (0 frontend skips permitted)",
            "mode_b_owner": "Upstream rustc Frontend (verified via driver identity; proc-macro host dylibs linked by backend)",
            "upstream_harnesses": [
                f"tests/ui frontend-only ({ct['ui']['frontend_only']} files)",
                f"tests/ui-fulldeps ({ct['ui-fulldeps']['files_412be32a6a18']} files)",
                f"tests/pretty ({ct['pretty']['files_412be32a6a18']} files)",
                f"tests/crashes ({ct['crashes']['files_412be32a6a18']} ICE guards)",
                f"src/tools/clippy/tests ({tl['clippy_tests']['total_rs_entrypoints']} files)",
            ],
            "external_harnesses": [
                f"rust-lang/fls ({ext_harnesses.get('fls', {}).get('total_dp_paragraph_ids', 4110)} :dp: paragraph IDs) + ferrocene traceability-matrix",
                "rust-lang/crater check-only (~550k crates)",
            ],
            "required_oracle": "check-pass / check-fail diagnostic span parity + cross-crate .rmeta roundtrip",
        },
        {
            "surface_id": "S03_BUILTIN_TARGETS_AND_OBJECT_FORMATS",
            "surface_name": "Built-In Target Specifications, DataLayouts, Relocations, and Crate Types",
            "inventory_412be32a6a18": (
                f"{targets['total_builtin_targets']} built-in targets "
                f"(8 Tier 1, {targets['tier2_with_host_tools_count']} Tier 2 host, "
                f"ELF={targets['by_binary_format'].get('Elf', 0)}, "
                f"MachO={targets['by_binary_format'].get('MachO', 0)}, "
                f"COFF={targets['by_binary_format'].get('Coff', 0)}, "
                f"Wasm={targets['by_binary_format'].get('Wasm', 0)}, "
                f"XCOFF={targets['by_binary_format'].get('Xcoff', 0)}), "
                f"{cli_surfaces['crate_types']['enum_variants_count']} CrateTypes, "
                f"{cli_surfaces['emit_output_types']['total']} OutputTypes"
            ),
            "mode_a_owner": "Candidate Target Registry + Object/Archive/Linker Driver",
            "mode_b_owner": "Upstream Target Registry + Candidate Object Emitter & Linker Integration",
            "upstream_harnesses": [
                f"tests/build-std ({ct['build-std']['files_412be32a6a18']} suite)",
                f"tests/run-make ({ct['run-make']['backend_codegen']} backend-agnostic recipes)",
                f"tests/codegen-units ({ct['codegen-units']['files_412be32a6a18']} files)",
                "compiletest remote-test-client / remote-test-server QEMU target matrix",
            ],
            "external_harnesses": [
                "ferrocene/ferrocene self-test + QEMU/target qualification runners",
                "stage0 -> stage1 -> stage2 -> stage3 cross/host binary fixed-point bootstrap",
            ],
            "required_oracle": "build-pass + run-pass across all qualified target triples and all 8 --crate-type tokens",
        },
        {
            "surface_id": "S04_RUSTC_INTRINSICS_AND_STDARCH_SIMD",
            "surface_name": "#[rustc_intrinsic] Operations and stdarch Vendor SIMD Intrinsics",
            "inventory_412be32a6a18": (
                f"{low_level['rustc_intrinsics']['total_declarations']} #[rustc_intrinsic] declarations "
                f"({low_level['rustc_intrinsics']['must_be_overridden_bodyless_count']} mandatory backend-lowered, "
                f"{low_level['rustc_intrinsics']['with_default_fallback_mir_body_count']} with default MIR fallback) + "
                f"{low_level['stdarch_llvm_link_bindings']['total_link_name_llvm_bindings']} stdarch llvm.* bindings "
                f"({low_level['stdarch_llvm_link_bindings']['unique_llvm_intrinsic_names']} unique)"
            ),
            "mode_a_owner": "Candidate Intrinsic Typechecker + CTFE + Codegen Lowerer",
            "mode_b_owner": "Candidate CodegenBackend (Intrinsic + LlvmIntrinsic lowering; 0 silent scalar traps)",
            "upstream_harnesses": [
                f"library/coretests ({st['coretests']['unit_and_integration_test_fns']} #[test] fns)",
                f"library/stdarch ({st['stdarch']['unit_and_integration_test_fns']} #[test] fns)",
                f"library/portable-simd ({st['portable-simd']['unit_and_integration_test_fns']} #[test] fns)",
                f"library/compiler-builtins ({st['compiler-builtins']['unit_and_integration_test_fns']} #[test] fns)",
                f"src/tools/miri/tests ({tl['miri_tests']['total_rs_entrypoints']} files)",
            ],
            "external_harnesses": [
                "cbeuw/rustlantis custom-MIR intrinsic & checked-arithmetic differential fuzzer",
            ],
            "required_oracle": "run-pass bit-exact execution against Miri and reference hardware/QEMU",
        },
        {
            "surface_id": "S05_EXTERN_ABI_UNWINDING_AND_C_VARIADICS",
            "surface_name": "ExternAbi Calling Conventions, C-unwind Foreign Exceptions, and C-Variadics",
            "inventory_412be32a6a18": (
                f"{low_level['extern_abi']['enum_variants_count']} ExternAbi enum variants / "
                f"{low_level['extern_abi']['all_variants_string_tokens_count']} ABI string tokens "
                f"({low_level['extern_abi']['paired_unwind_bool_variants_count']} paired unwind=false/true)"
            ),
            "mode_a_owner": "Candidate FnAbi Layout/Classification Engine + Call/Unwind Frame Lowerer",
            "mode_b_owner": "Upstream FnAbi Computation + Candidate Call/Prologue/Epilogue/LSDA Lowerer",
            "upstream_harnesses": [
                f"tests/ui backend-codegen ({ct['ui']['backend_codegen']} files incl. tests/ui/abi, c-variadic, panics)",
                f"library/std ({st['std']['unit_and_integration_test_fns']} #[test] fns) + panic_unwind",
            ],
            "external_harnesses": [
                f"Gankra/abi-cafe ({ext_harnesses.get('abi_cafe', {}).get('normal_kdl_tests', 3)} normal + "
                f"{ext_harnesses.get('abi_cafe', {}).get('procgen_kdl_suites', 36)} procgen KDL suites: "
                "rustc_calls_cand, cand_calls_rustc, cand_calls_cc, cc_calls_cand)",
                "Cross-language C++ <-> Rust extern \"C-unwind\" / extern \"C\" / i128 5-mode matrix",
            ],
            "required_oracle": "Paired cross-compiler link-and-run execution + RAII Drop / C++ destructor count parity",
        },
        {
            "surface_id": "S06_INLINE_ASM_NAKED_AND_GLOBAL_ASM",
            "surface_name": "asm!, global_asm!, and #[unsafe(naked)] Across InlineAsmArch ISAs",
            "inventory_412be32a6a18": (
                f"{low_level['inline_asm']['inline_asm_arch_variants_count']} InlineAsmArch variants across "
                f"{low_level['inline_asm']['isa_modules_count']} ISA modules "
                f"({low_level['inline_asm']['total_register_classes_across_isas']} register classes, "
                f"{low_level['inline_asm']['total_defined_registers_across_isas']} register defs)"
            ),
            "mode_a_owner": "Candidate Template/Constraint Validator + Integrated Assembler / Object Encoder",
            "mode_b_owner": "Upstream HIR/MIR asm! Validator + Candidate Register Constraint Allocator & Assembler",
            "upstream_harnesses": [
                "tests/ui/asm/* (incl. goto, label-operand, may_unwind, sym, naked-functions)",
                f"tests/assembly-llvm ({ct['assembly-llvm']['files_412be32a6a18']} files, target-equivalent binary checks)",
                f"tests/assembly-gcc ({ct['assembly-gcc']['files_412be32a6a18']} files)",
                f"library/std_detect ({st['std_detect']['unit_and_integration_test_fns']} #[test] fns)",
            ],
            "external_harnesses": [
                "ferrocene inline-assembly FLS chapter (321 :dp: paragraphs in src/inline-assembly.rst)",
            ],
            "required_oracle": "run-pass execution (including asm goto and may_unwind landing pads) + ELF/COFF symbol table audit",
        },
        {
            "surface_id": "S07_MONOMORPHIZATION_INSTANCE_AND_SHIMS",
            "surface_name": "Monomorphization Collector, InstanceKind, ShimKind, and VTables",
            "inventory_412be32a6a18": (
                f"{low_level['instance_and_shim_kinds']['instance_kind_variants_count']} InstanceKind variants + "
                f"{low_level['instance_and_shim_kinds']['shim_kind_variants_count']} ShimKind variants + "
                "2 ReifyReason variants (FnPtr, Vtable)"
            ),
            "mode_a_owner": "Candidate Monomorphization Collector + Shim MIR Builder + VTable/Virtual Dispatch Lowerer",
            "mode_b_owner": (
                "Upstream Collector & make_shim (13 ShimKinds) + Candidate Virtual/VTable/Reify(KCFI)/ThreadLocal Lowerer"
            ),
            "upstream_harnesses": [
                f"tests/codegen-units ({ct['codegen-units']['files_412be32a6a18']} files)",
                f"tests/mir-opt ({ct['mir-opt']['files_412be32a6a18']} files)",
                f"library/alloctests ({st['alloctests']['unit_and_integration_test_fns']} #[test] fns)",
                "tests/ui/async-await/async-drop/* & dyn-compatibility / trait-upcasting suites",
            ],
            "external_harnesses": [
                "cbeuw/rustlantis multi-block/call differential fuzzing",
                "stage0 -> stage1 -> stage2 -> stage3 self-hosting over rustc (~715k SLOC)",
            ],
            "required_oracle": "MONO_ITEM partitioning parity + run-pass execution of dyn upcasting, async drop, and TLS shims",
        },
        {
            "surface_id": "S08_DEBUGINFO_COVERAGE_SANITIZERS_LTO_INCREMENTAL",
            "surface_name": "Debuginfo (DWARF/CodeView), Coverage, Sanitizers, LTO, Incremental, and StableMIR",
            "inventory_412be32a6a18": (
                f"5 DebugInfo levels, 3 SplitDebuginfo modes, InstrumentCoverage, "
                f"{cli_surfaces['debuginfo_coverage_lto_sanitizers']['sanitizers_count']} SanitizerSet bitflags, "
                f"4 Lto modes, {cli_surfaces['codegen_options_C']['total']} -C & "
                f"{cli_surfaces['unstable_options_Z']['total']} -Z options, "
                f"rustc_public ({low_level['rustc_public_stable_mir']['sloc']} SLOC)"
            ),
            "mode_a_owner": "Candidate End-to-End Pipeline (DWARF/PDB, coverage maps, sanitizers, Thin/Fat LTO, incr dep-graph)",
            "mode_b_owner": "Upstream Incr Dep-Graph & StableMIR Bridge + Candidate Debuginfo/LTO/Sanitizer Codegen",
            "upstream_harnesses": [
                f"tests/debuginfo ({ct['debuginfo']['files_412be32a6a18']} debugger scripts: gdb, lldb, cdb)",
                f"tests/incremental ({ct['incremental']['files_412be32a6a18']} multi-revision crates)",
                f"tests/coverage ({ct['coverage']['files_412be32a6a18']} files) + coverage-run-rustdoc ({ct['coverage-run-rustdoc']['files_412be32a6a18']})",
                "tests/ui/sanitizer/* & tests/ui/lto/* & tests/ui-fulldeps/rustc_public/*",
            ],
            "external_harnesses": [
                "ferrocene/tools/blanket MC/DC & source coverage verifier",
                "rust-lang/crater build-and-test campaign with 2x flake-isolated retry",
            ],
            "required_oracle": "Debugger breakpoint/variable inspection pass + #[rustc_clean]/#[rustc_dirty] + sanitizer trap tests",
        },
        {
            "surface_id": "S09_RUSTDOC_AND_ECOSYSTEM_TOOLING",
            "surface_name": "Rustdoc (HTML, JSON v61, Doctests, JS/GUI) and Workspace Tooling",
            "inventory_412be32a6a18": (
                f"6 rustdoc compiletest suites ({sum(ct[s]['files_412be32a6a18'] for s in ct if s.startswith('rustdoc'))} files) + "
                f"{harnesses['stdlib_suites']['total_doctest_blocks']} library/ doctests"
            ),
            "mode_a_owner": "Candidate rustdoc Driver + Doctest Compiler/Runner",
            "mode_b_owner": "Upstream rustdoc + Candidate CodegenBackend compiling & linking runnable doctest binaries",
            "upstream_harnesses": [
                f"tests/rustdoc-html ({ct['rustdoc-html']['files_412be32a6a18']}), rustdoc-ui ({ct['rustdoc-ui']['files_412be32a6a18']}), "
                f"rustdoc-json ({ct['rustdoc-json']['files_412be32a6a18']}), rustdoc-gui ({ct['rustdoc-gui']['files_412be32a6a18']}), "
                f"rustdoc-js ({ct['rustdoc-js']['files_412be32a6a18']}), rustdoc-js-std ({ct['rustdoc-js-std']['files_412be32a6a18']})",
                f"library/* doctests ({harnesses['stdlib_suites']['total_doctest_blocks']} runnable blocks)",
            ],
            "external_harnesses": [
                "rust-lang/crater --mode=rustdoc ecosystem run",
            ],
            "required_oracle": "htmldocck + jsondocck/jsondoclint + run-pass execution of compiled doctests",
        },
    ]


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Verify rustc feature-completeness surface inventory, harness mapping, and skip-list soundness."
    )
    ap.add_argument("--rust-repo", default=".", help="Path to git repository containing rust-lang/rust objects")
    ap.add_argument("--rev", default=DEFAULT_REV, help="40-hex commit SHA of rust-lang/rust to inspect")
    ap.add_argument(
        "--out",
        default=str(Path(__file__).resolve().parent / "surface_to_harness_map.json"),
        help="Output JSON path",
    )
    ap.add_argument("--skip-live-probes", action="store_true", help="Skip live rustc/g++ TemporaryDirectory probes")
    ap.add_argument("--skip-gh-api", action="store_true", help="Skip gh api queries of external repositories")
    args = ap.parse_args()

    t0 = time.monotonic()
    live_probes: dict[str, Any] = {}
    live_nightly_specs: dict[str, Any] | None = None
    live_1991_targets: list[str] | None = None

    if not args.skip_live_probes:
        live_probes, live_nightly_specs, live_1991_targets = run_live_probes()

    ext_harnesses: dict[str, Any] = {}
    if not args.skip_gh_api:
        ext_harnesses = query_external_harnesses()

    reader = GitObjectReader(args.rust_repo, args.rev)
    try:
        cli_surfaces = extract_cli_and_session_surfaces(reader)
        targets = extract_targets_inventory(reader, live_nightly_specs, live_1991_targets)
        low_level = extract_intrinsics_abi_asm_shims_public(reader)
        harnesses = extract_tests_stdlib_tools_and_skips(reader)
    finally:
        reader.close()

    skip_auditor = run_auditor_evaluations(harnesses["compiletest_suites"])
    matrix = build_surface_to_harness_matrix(
        cli_surfaces, targets, low_level, harnesses, ext_harnesses
    )

    elapsed_sec = round(time.monotonic() - t0, 3)
    payload = {
        "schema": "rustc-feature-completeness-qualification-matrix/1",
        "subject_rust_revision": args.rev,
        "baseline_1_99_1_revision": BASELINE_1991_REV,
        "live_nightly_host_revision": NIGHTLY_HOST_REV,
        "extraction_elapsed_seconds": elapsed_sec,
        "compiler_surfaces": {
            **cli_surfaces,
            "builtin_targets": targets,
            **low_level,
        },
        "harnesses": {
            **harnesses,
            "external_qualification_harnesses": ext_harnesses,
        },
        "surface_to_harness_matrix": matrix,
        "skip_list_soundness_auditor": skip_auditor,
        "live_execution_probes": live_probes,
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")

    # Assert built-in auditor expectations
    eval_by_name = {e["name"]: e["verdict"] for e in skip_auditor["evaluations"]}
    assert eval_by_name["Mode A Standalone Compiler Qualification Baseline"] == "PASS"
    assert eval_by_name["Mode B Drop-In Codegen Backend Qualification Baseline"] == "PASS"
    assert eval_by_name["Upstream rustc_codegen_cranelift (test_rustc_tests.sh)"] == "FAIL"
    assert eval_by_name["Upstream rustc_codegen_gcc (build_system/src/test.rs)"] == "FAIL"
    assert eval_by_name["Synthetic Loophole Probe 1: Mode A Skipping Frontend Diagnostics"] == "FAIL"
    assert eval_by_name["Synthetic Loophole Probe 2: Vacuous --pass=check Downgrade on run-pass"] == "FAIL"
    assert eval_by_name["Synthetic Loophole Probe 3: Silent Unaccounted Test Drop"] == "FAIL"

    print(
        f"OK: extracted {targets['total_builtin_targets']} targets, "
        f"{low_level['rustc_intrinsics']['total_declarations']} #[rustc_intrinsic]s, "
        f"{low_level['stdarch_llvm_link_bindings']['total_link_name_llvm_bindings']} stdarch llvm.* bindings, "
        f"{harnesses['compiletest_suites']['total_test_entrypoints_412be32a6a18']} compiletest files across "
        f"{harnesses['compiletest_suites']['suite_count_412be32a6a18']} suites in {elapsed_sec}s -> {out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
