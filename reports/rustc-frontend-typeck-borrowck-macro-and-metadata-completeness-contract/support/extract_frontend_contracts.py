#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic Git-object and live-binary extractor for rustc frontend contracts.

Reads a pinned commit of a local rust-lang/rust Git repository strictly via
read-only `git ls-tree` and `git cat-file --batch` streams without reading or
mutating any working-tree files. Optionally runs isolated `tempfile.TemporaryDirectory`
execution probes against installed `rustc` and `rustdoc` toolchains to verify:
  1. Editions (`2015`, `2018`, `2021`, `2024`, `future`) and feature-gate
     inventories (`accepted.rs`, `unstable.rs`, `removed.rs`).
  2. Built-in attributes (`builtin_attrs.rs`, `rustc_attr_parsing`,
     `rustc_attr_ir`, `rustc_structures`), built-in macros/derives
     (`rustc_builtin_macros`, `rustc_expand_queries`), and lang items
     (`rustc_attr_ir/src/lang_items.rs`, `weak_lang_items.rs`, `library/*`).
  3. Built-in compiler lints (`rustc_lint_defs`, `rustc_lint`, `librustdoc`),
     lint groups, renamed/removed lints, and `E0xxx` diagnostic error codes.
  4. Type checking, trait solving (`rustc_next_trait_solver` vs legacy),
     pattern exhaustiveness (`rustc_pattern_analysis`), and borrow checking
     (`NLL` vs `Polonius` in `rustc_borrowck`).
  5. Procedural macro bridge wire protocol (`library/proc_macro/src/bridge/`
     and `compiler/rustc_expand/src/proc_macro_server.rs`).
  6. `.rmeta` binary metadata schema (`compiler/rustc_metadata/src/rmeta/`),
     `StableCrateId`, `Svh` (`StrictVersionHash`), and `rustdoc` JSON schema
     (`src/rustdoc-json-types/lib.rs`).
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import struct
import subprocess
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

DEFAULT_REV = "412be32a6a189d9a28922beee178bc0abee9d492"


class GitRevisionReader:
    """Read-only Git object reader backed by `git ls-tree` and `git cat-file --batch`."""

    def __init__(self, repo_path: str, rev: str) -> None:
        self.repo_path = repo_path
        self.rev = rev
        self.files: dict[str, tuple[str, int]] = {}
        self._load_tree()

    def _load_tree(self) -> None:
        out = subprocess.check_output(
            ["git", "-C", self.repo_path, "ls-tree", "-r", "-l", self.rev],
            text=True,
        )
        for line in out.splitlines():
            if not line.strip():
                continue
            meta, path = line.split("\t", 1)
            parts = meta.split()
            mode, obj_type, sha, size_s = parts[0], parts[1], parts[2], parts[3]
            if obj_type == "blob" and mode != "160000":
                self.files[path] = (sha, int(size_s))

    def read_many(self, paths: list[str]) -> dict[str, str]:
        wanted = [p for p in paths if p in self.files]
        if not wanted:
            return {}
        stdin_bytes = "".join(f"{self.files[p][0]}\n" for p in wanted).encode("utf-8")
        proc = subprocess.run(
            ["git", "-C", self.repo_path, "cat-file", "--batch"],
            input=stdin_bytes,
            capture_output=True,
            check=True,
        )
        buf = proc.stdout
        pos = 0
        res: dict[str, str] = {}
        for p in wanted:
            nl = buf.index(b"\n", pos)
            header = buf[pos:nl].decode("ascii")
            _, _, size_str = header.split()
            size = int(size_str)
            body = buf[nl + 1 : nl + 1 + size]
            pos = nl + 1 + size + 1
            res[p] = body.decode("utf-8", errors="replace")
        return res

    def read_text(self, path: str) -> str:
        return self.read_many([path])[path]

    def paths_under(self, prefix: str, suffix: str = "") -> list[str]:
        return sorted(
            p for p in self.files if p.startswith(prefix) and p.endswith(suffix)
        )


def strip_line_comments(src: str) -> str:
    return "\n".join(
        "" if line.lstrip().startswith("//") else line for line in src.splitlines()
    )


def extract_delimited(src: str, start_idx: int, open_ch: str, close_ch: str) -> str:
    """Linear O(N) balanced delimiter extractor starting at or after `start_idx`."""
    pos = src.find(open_ch, start_idx)
    if pos < 0:
        return ""
    depth = 0
    in_str = False
    escape = False
    for idx in range(pos, len(src)):
        ch = src[idx]
        if in_str:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return src[pos + 1 : idx]
    return src[pos + 1 :]


def count_sloc(src: str) -> tuple[int, int]:
    lines = src.splitlines()
    sloc = 0
    in_block = False
    for line in lines:
        s = line.strip()
        if not s:
            continue
        if in_block:
            if "*/" in s:
                in_block = False
                tail = s.split("*/", 1)[1].strip()
                if tail and not tail.startswith("//"):
                    sloc += 1
            continue
        if s.startswith("//"):
            continue
        if s.startswith("/*"):
            if "*/" not in s[2:]:
                in_block = True
            else:
                tail = s[2:].split("*/", 1)[1].strip()
                if tail and not tail.startswith("//"):
                    sloc += 1
            continue
        sloc += 1
    return len(lines), sloc


def parse_symbol_map(
    symbol_rs: str,
) -> tuple[dict[str, str], dict[str, str], dict[str, list[str]]]:
    """Linear O(N) parser for `Keywords { ... }` and `Symbols { ... }` in `symbol.rs`."""
    kw_map: dict[str, str] = {}
    sym_map: dict[str, str] = {}
    kw_categories: dict[str, list[str]] = defaultdict(list)

    kw_idx = symbol_rs.find("Keywords {")
    if kw_idx >= 0:
        kw_body = extract_delimited(symbol_rs, kw_idx, "{", "}")
        current_cat = "special"
        for line in kw_body.splitlines():
            s = line.strip()
            if "Keywords that are used in stable Rust" in s:
                current_cat = "strict_always"
            elif "Keywords that are used in unstable Rust or reserved" in s:
                current_cat = "reserved_always"
            elif "Edition-specific keywords that are used in stable Rust" in s:
                current_cat = "edition_strict"
            elif "Edition-specific keywords that are used in unstable Rust" in s:
                current_cat = "edition_reserved"
            elif '"Lifetime keywords"' in s:
                current_cat = "lifetime"
            elif "Weak keywords" in s:
                current_cat = "weak"
            m = re.match(r'^([A-Za-z0-9_]+)\s*:\s*"([^"]*)"\s*,', s)
            if m:
                ident, val = m.group(1), m.group(2)
                kw_map[ident] = val
                kw_categories[current_cat].append(f"{ident}={val}")

    sym_idx = symbol_rs.find("Symbols {")
    if sym_idx >= 0:
        sym_body = extract_delimited(symbol_rs, sym_idx, "{", "}")
        for line in sym_body.splitlines():
            s = line.strip()
            if not s or s.startswith("//"):
                continue
            m_kv = re.match(r'^([A-Za-z0-9_]+)\s*:\s*"([^"]*)"\s*,', s)
            if m_kv:
                sym_map[m_kv.group(1)] = m_kv.group(2)
                continue
            m_bare = re.match(r"^([A-Za-z0-9_]+)\s*,", s)
            if m_bare:
                ident = m_bare.group(1)
                sym_map[ident] = ident

    return kw_map, sym_map, dict(kw_categories)


def resolve_sym_expr(expr: str, kw_map: dict[str, str], sym_map: dict[str, str]) -> str:
    expr = expr.strip()
    if expr.startswith("rustc_span::"):
        expr = expr[len("rustc_span::") :].strip()
    if expr.startswith("sym::"):
        key = expr[5:].strip()
        return sym_map.get(key, key)
    if expr.startswith("kw::"):
        key = expr[4:].strip()
        return kw_map.get(key, key)
    return expr


def extract_editions_and_features(
    reader: GitRevisionReader,
    kw_categories: dict[str, list[str]],
) -> dict:
    edition_rs = reader.read_text("compiler/rustc_span/src/edition.rs")
    accepted_rs = reader.read_text("compiler/rustc_feature/src/accepted.rs")
    unstable_rs = reader.read_text("compiler/rustc_feature/src/unstable.rs")
    removed_rs = reader.read_text("compiler/rustc_feature/src/removed.rs")

    editions = []
    for m in re.finditer(r'Edition::(Edition\w+)\s*=>\s*"([^"]+)"', edition_rs):
        variant, name = m.group(1), m.group(2)
        if name.endswith("_compatibility"):
            continue
        if any(e["variant"] == variant for e in editions):
            continue
        editions.append({"variant": variant, "cli_name": name})
    lint_map = dict(
        re.findall(
            r'Edition::(Edition\w+)\s*=>\s*"([a-z0-9_]+_compatibility)"', edition_rs
        )
    )
    stable_map = dict(
        re.findall(r"Edition::(Edition\w+)\s*=>\s*(true|false)", edition_rs)
    )
    for e in editions:
        v = e["variant"]
        e["compatibility_lint_group"] = lint_map.get(v)
        e["is_stable"] = stable_map.get(v) == "true"

    compiler_rs_paths = reader.paths_under("compiler/", ".rs")
    compiler_texts = reader.read_many(compiler_rs_paths)
    edition_check_re = re.compile(
        r"\b(?:Edition::Edition\w+|at_least_rust_\d+|at_least_edition_future|is_rust_2015)\b"
    )
    edition_checks_by_crate: Counter[str] = Counter()
    for p, txt in compiler_texts.items():
        parts = p.split("/")
        if len(parts) >= 2:
            cnt = len(edition_check_re.findall(strip_line_comments(txt)))
            if cnt:
                edition_checks_by_crate[parts[1]] += cnt

    accepted_clean = strip_line_comments(accepted_rs)
    acc_body = extract_delimited(
        accepted_clean, accepted_clean.index("declare_features!"), "(", ")"
    )
    accepted = []
    for m in re.finditer(
        r'\(\s*accepted\s*,\s*([a-zA-Z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\s*\d+\s*\)|None)\s*\)',
        acc_body,
    ):
        name, since, issue_raw = m.group(1), m.group(2), m.group(3)
        m_num = re.search(r"\d+", issue_raw)
        issue = int(m_num.group(0)) if issue_raw.startswith("Some") and m_num else None
        accepted.append({"name": name, "since": since, "issue": issue})

    since_hist = Counter(f["since"] for f in accepted)

    unstable_clean = strip_line_comments(unstable_rs)
    unstable_decl = extract_delimited(
        unstable_clean, unstable_clean.index("declare_features!"), "(", ")"
    )
    active = []
    for m in re.finditer(
        r'\(\s*(unstable|incomplete|internal)\s*,\s*([a-zA-Z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\s*\d+\s*\)|None)\s*\)',
        unstable_decl,
    ):
        status, name, since, issue_raw = m.group(1), m.group(2), m.group(3), m.group(4)
        m_num = re.search(r"\d+", issue_raw)
        issue = int(m_num.group(0)) if issue_raw.startswith("Some") and m_num else None
        active.append({"name": name, "status": status, "since": since, "issue": issue})

    status_counts = Counter(f["status"] for f in active)

    removed_clean = strip_line_comments(removed_rs)
    rem_decl = extract_delimited(
        removed_clean, removed_clean.index("declare_features!"), "(", ")"
    )
    removed = []
    pos = 0
    while True:
        start = rem_decl.find("(removed,", pos)
        if start < 0:
            break
        entry = extract_delimited(rem_decl, start, "(", ")")
        pos = start + len(entry) + 2
        m = re.match(
            r'removed\s*,\s*([a-zA-Z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\s*\d+\s*\)|None)\s*,\s*(.*)',
            " ".join(entry.split()),
        )
        if not m:
            continue
        name, since, issue_raw, rest = m.groups()
        m_num = re.search(r"\d+", issue_raw)
        issue = int(m_num.group(0)) if issue_raw.startswith("Some") and m_num else None
        reason = None
        pull = None
        if rest.startswith('Some("'):
            end_q = rest.rfind('")')
            if end_q > 0:
                reason = rest[6:end_q].replace('\\"', '"')
                tail = rest[end_q + 2 :].strip().lstrip(",").strip()
                if tail.isdigit():
                    pull = int(tail)
        elif rest.startswith("None"):
            tail = rest[4:].strip().lstrip(",").strip()
            if tail.isdigit():
                pull = int(tail)
        removed.append(
            {"name": name, "since": since, "issue": issue, "pull": pull, "reason": reason}
        )

    return {
        "editions": {
            "count": len(editions),
            "default_edition": "2015",
            "latest_stable_edition": "2024",
            "variants": editions,
            "keyword_categories": kw_categories,
            "edition_checks_by_crate": dict(edition_checks_by_crate.most_common()),
            "total_edition_checks_in_compiler": sum(edition_checks_by_crate.values()),
        },
        "accepted_lang_features": {
            "count": len(accepted),
            "recent_versions": {
                k: since_hist[k]
                for k in sorted(
                    [v for v in since_hist if v.startswith(("1.9", "1.10"))],
                    key=lambda s: [int(x) if x.isdigit() else 0 for x in s.split(".")],
                )
            },
            "features": accepted,
        },
        "active_lang_features": {
            "total_count": len(active),
            "by_status": {
                "unstable": status_counts["unstable"],
                "incomplete": status_counts["incomplete"],
                "internal": status_counts["internal"],
            },
            "incomplete_feature_names": sorted(
                f["name"] for f in active if f["status"] == "incomplete"
            ),
            "internal_feature_names": sorted(
                f["name"] for f in active if f["status"] == "internal"
            ),
            "features": active,
        },
        "removed_lang_features": {
            "count": len(removed),
            "with_reason_count": sum(1 for r in removed if r["reason"] is not None),
            "with_pr_count": sum(1 for r in removed if r["pull"] is not None),
            "features": removed,
        },
    }


def extract_attrs_macros_and_lang_items(
    reader: GitRevisionReader,
    kw_map: dict[str, str],
    sym_map: dict[str, str],
) -> dict:
    builtin_attrs_rs = reader.read_text("compiler/rustc_feature/src/builtin_attrs.rs")
    attr_context_rs = reader.read_text("compiler/rustc_attr_parsing/src/context.rs")
    attr_data_rs = reader.read_text("compiler/rustc_attr_ir/src/data_structures.rs")
    structures_lib = reader.read_text("compiler/rustc_structures/src/lib.rs")
    builtin_macros_rs = reader.read_text("compiler/rustc_builtin_macros/src/lib.rs")
    lang_items_rs = reader.read_text("compiler/rustc_attr_ir/src/lang_items.rs")
    weak_lang_rs = reader.read_text("compiler/rustc_attr_ir/src/weak_lang_items.rs")

    gated_cfgs = []
    gcfg_idx = builtin_attrs_rs.find("const GATED_CFGS:")
    if gcfg_idx >= 0:
        gcfg_body = extract_delimited(
            builtin_attrs_rs, builtin_attrs_rs.find("= &[", gcfg_idx), "[", "]"
        )
        for m in re.finditer(
            r"\(\s*sym::([a-zA-Z0-9_]+)\s*,\s*sym::([a-zA-Z0-9_]+)\s*,\s*Features::([a-zA-Z0-9_]+)\s*,?\s*\)",
            strip_line_comments(gcfg_body),
        ):
            gated_cfgs.append(
                {
                    "cfg_name": resolve_sym_expr(f"sym::{m.group(1)}", kw_map, sym_map),
                    "feature_gate": resolve_sym_expr(f"sym::{m.group(2)}", kw_map, sym_map),
                }
            )

    builtin_attr_syms = []
    ba_idx = builtin_attrs_rs.find("pub static BUILTIN_ATTRIBUTES:")
    if ba_idx >= 0:
        ba_body = extract_delimited(
            builtin_attrs_rs, builtin_attrs_rs.find("= &[", ba_idx), "[", "]"
        )
        for m in re.finditer(r"sym::([a-zA-Z0-9_]+)", strip_line_comments(ba_body)):
            builtin_attr_syms.append(resolve_sym_expr(f"sym::{m.group(1)}", kw_map, sym_map))

    attr_files = reader.paths_under("compiler/rustc_attr_parsing/src/attributes/", ".rs")
    attr_texts = reader.read_many(attr_files)

    ap_idx = attr_context_rs.find("pub(crate) static ATTRIBUTE_PARSERS")
    registered_parsers: list[tuple[str, str]] = []
    if ap_idx >= 0:
        ap_body = extract_delimited(attr_context_rs, ap_idx, "[", "]")
        for raw_line in strip_line_comments(ap_body).splitlines():
            s = raw_line.strip().rstrip(",")
            if not s:
                continue
            if s.startswith("Single<WithoutArgs<") and s.endswith(">>"):
                registered_parsers.append(("WithoutArgs", s[len("Single<WithoutArgs<") : -2]))
            elif s.startswith("Single<") and s.endswith(">"):
                registered_parsers.append(("Single", s[len("Single<") : -1]))
            elif s.startswith("Combine<") and s.endswith(">"):
                registered_parsers.append(("Combine", s[len("Combine<") : -1]))
            else:
                registered_parsers.append(("AttributeParser", s))

    parser_alias_map = {"PathAttributeParser": "PathParser"}

    impl_blocks: dict[str, tuple[str, str]] = {}
    impl_re = re.compile(
        r"impl(?:\s*<[^>]*>)?\s+(AttributeParser|SingleAttributeParser|NoArgsAttributeParser|CombineAttributeParser)(?:\s*<[^>]*>)?\s+for\s+([A-Za-z0-9_]+)\s*\{"
    )
    for fp, src in attr_texts.items():
        for m in impl_re.finditer(src):
            struct_name = m.group(2)
            block = extract_delimited(src, m.end() - 1, "{", "}")
            impl_blocks[struct_name] = (fp, block)

    parsed_attributes_inventory = []
    unsafe_attributes = []
    safety_counts: Counter[str] = Counter()
    scope_counts: Counter[str] = Counter()
    gate_counts: Counter[str] = Counter()

    for wrapper_kind, reg_name in registered_parsers:
        lookup_name = parser_alias_map.get(reg_name, reg_name)
        fp, block = impl_blocks.get(lookup_name, ("unknown", ""))
        clean_block = strip_line_comments(block)

        paths: list[str] = []
        m_single_path = re.search(
            r"const\s+PATH\s*:\s*&\[[^\]]*Symbol\]\s*=\s*&\[([^\]]+)\]", clean_block
        )
        if m_single_path:
            toks = re.findall(r"(?:sym|kw)::[A-Za-z0-9_]+", m_single_path.group(1))
            if toks:
                paths.append("::".join(resolve_sym_expr(t, kw_map, sym_map) for t in toks))
        else:
            attrs_idx = clean_block.find("const ATTRIBUTES")
            search_region = (
                extract_delimited(clean_block, clean_block.find("&[", attrs_idx), "[", "]")
                if attrs_idx >= 0
                else clean_block
            )
            for mp in re.finditer(r"\(\s*&\[\s*([^\]]+)\]", search_region):
                toks = re.findall(r"(?:sym|kw)::[A-Za-z0-9_]+", mp.group(1))
                if toks:
                    p_str = "::".join(resolve_sym_expr(t, kw_map, sym_map) for t in toks)
                    if p_str not in paths:
                        paths.append(p_str)

        if "AttributeSafety::Unsafe" in clean_block:
            safety = "Unsafe"
            m_since = re.search(r"unsafe_since\s*:\s*(Some\([^)]+\)|None)", clean_block)
            unsafe_since = m_since.group(1) if m_since else "Unknown"
            m_note = re.search(r'note\s*:\s*"([^"]+)"', clean_block)
            note = m_note.group(1) if m_note else ""
            for p_str in paths:
                unsafe_attributes.append(
                    {
                        "path": p_str,
                        "parser": reg_name,
                        "file": fp,
                        "unsafe_since": unsafe_since,
                        "note": note,
                    }
                )
        else:
            safety = "Normal"

        t_idx = clean_block.find("const ALLOWED_TARGETS")
        target_expr = ""
        if t_idx >= 0:
            semi = clean_block.find(";", t_idx)
            target_expr = clean_block[t_idx:semi] if semi > t_idx else clean_block[t_idx:]
        allowed_list = re.findall(r"Allow\(\s*Target::([A-Za-z0-9_]+)", target_expr)
        if "ManuallyChecked" in target_expr:
            all_t = set(re.findall(r"Target::([A-Za-z0-9_]+)", clean_block))
            scope = "CrateLevel" if all_t == {"Crate"} else "Normal"
        elif allowed_list and set(allowed_list) == {"Crate"}:
            scope = "CrateLevel"
        else:
            scope = "Normal"

        gates = re.findall(r"unstable!\(\s*([a-zA-Z0-9_]+)", clean_block)
        has_stable = "AttributeStability::Stable" in clean_block
        if gates and not has_stable:
            unique_gates = sorted(set(gates))
            if unique_gates == ["compiler_builtins"]:
                gate_kind = "CompilerBuiltins"
            elif unique_gates == ["rustc_attrs"]:
                gate_kind = "Gated(rustc_attrs)"
            else:
                gate_kind = "Gated"
        elif gates and has_stable:
            gate_kind = "Mixed(Stable+Gated)"
        else:
            gate_kind = "Ungated"

        m_dup = re.search(
            r"const\s+ON_DUPLICATE\s*:\s*OnDuplicate\s*=\s*OnDuplicate::([A-Za-z0-9_]+)",
            clean_block,
        )
        on_dup = (
            m_dup.group(1)
            if m_dup
            else ("Combine" if wrapper_kind == "Combine" else "CustomOrError")
        )

        for p_str in paths:
            safety_counts[safety] += 1
            scope_counts[scope] += 1
            gate_counts[gate_kind] += 1
            parsed_attributes_inventory.append(
                {
                    "path": p_str,
                    "parser": reg_name,
                    "parser_wrapper": wrapper_kind,
                    "safety": safety,
                    "attribute_type": scope,
                    "gate_class": gate_kind,
                    "feature_gates": sorted(set(gates)),
                    "on_duplicate": on_dup,
                    "source_file": fp,
                }
            )

    ak_body = extract_delimited(
        attr_data_rs, attr_data_rs.index("pub enum AttributeKind {"), "{", "}"
    )
    attr_kind_variants = []
    depth = 0
    for line in strip_line_comments(ak_body).splitlines():
        s = line.strip()
        if depth == 0 and s:
            m_v = re.match(r"^([A-Z][A-Za-z0-9_]*)\b", s)
            if m_v:
                attr_kind_variants.append(m_v.group(1))
        depth += line.count("{") - line.count("}")

    rustc_structures_exports = sorted(
        re.findall(r"pub use [a-z0-9_]+::([A-Za-z0-9_]+);", structures_lib)
    )

    def parse_macro_reg_block(tag: str) -> list[dict]:
        idx = builtin_macros_rs.find(f"{tag}! {{")
        if idx < 0:
            return []
        body = extract_delimited(builtin_macros_rs, idx, "{", "}")
        items = []
        for line in strip_line_comments(body).splitlines():
            s = line.strip().rstrip(",")
            if not s or ":" not in s:
                continue
            name, handler = [x.strip() for x in s.split(":", 1)]
            items.append(
                {
                    "symbol": name,
                    "resolved_name": resolve_sym_expr(f"sym::{name}", kw_map, sym_map),
                    "handler": handler,
                }
            )
        return items

    bang_macros = parse_macro_reg_block("register_bang")
    attr_macros = parse_macro_reg_block("register_attr")
    derive_macros = parse_macro_reg_block("register_derive")
    manual_macros = [
        {"resolved_name": "quote", "kind": "BangProcMacro", "handler": "rustc_proc_macro::quote"},
        {
            "resolved_name": "contracts_requires",
            "kind": "AttrProcMacro",
            "handler": "contracts::ExpandRequires",
        },
        {
            "resolved_name": "contracts_ensures",
            "kind": "AttrProcMacro",
            "handler": "contracts::ExpandEnsures",
        },
    ]

    weak_map: dict[str, str] = {}
    w_idx = weak_lang_rs.find("weak_lang_items! {")
    if w_idx >= 0:
        w_body = extract_delimited(weak_lang_rs, w_idx, "{", "}")
        for m in re.finditer(
            r"([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*;", strip_line_comments(w_body)
        ):
            weak_map[m.group(1)] = resolve_sym_expr(f"sym::{m.group(2)}", kw_map, sym_map)

    li_idx = lang_items_rs.index("language_item_table! {")
    li_body = strip_line_comments(extract_delimited(lang_items_rs, li_idx, "{", "}"))
    lang_items = []
    for raw_entry in li_body.split(";"):
        s = " ".join(
            line.strip()
            for line in raw_entry.splitlines()
            if line.strip() and not line.strip().startswith("#[")
        )
        if not s:
            continue
        m_li = re.match(
            r"^([A-Za-z0-9_]+)\s*,\s*((?:sym|kw)::[A-Za-z0-9_]+)\s*,\s*([a-z0-9_]+)\s*,\s*(Target::.+)\s*,\s*(GenericRequirement::[A-Za-z0-9_()]+)\s*$",
            s,
        )
        if m_li:
            variant, sym_ref, getter, target_s, generics_s = m_li.groups()
            lang_name = resolve_sym_expr(sym_ref, kw_map, sym_map)
            lang_items.append(
                {
                    "variant": variant,
                    "lang_name": lang_name,
                    "getter": getter,
                    "target": target_s.strip(),
                    "generic_requirement": generics_s,
                    "is_weak": variant in weak_map,
                    "weak_link_symbol": weak_map.get(variant),
                }
            )

    lib_rs_paths = reader.paths_under("library/", ".rs")
    lib_texts = reader.read_many(lib_rs_paths)
    lang_defs_by_name: dict[str, list[str]] = defaultdict(list)
    lang_defs_by_crate: Counter[str] = Counter()
    lang_attr_re = re.compile(r'#\[\s*lang\s*=\s*"([^"]+)"\s*\]')
    for lp, ltxt in lib_texts.items():
        top_crate = "/".join(lp.split("/")[:2])
        for m in lang_attr_re.finditer(strip_line_comments(ltxt)):
            lname = m.group(1)
            if top_crate not in lang_defs_by_name[lname]:
                lang_defs_by_name[lname].append(top_crate)
            lang_defs_by_crate[top_crate] += 1

    for item in lang_items:
        item["defined_in_library_crates"] = sorted(lang_defs_by_name.get(item["lang_name"], []))

    li_target_counts = Counter(i["target"] for i in lang_items)
    li_generic_counts = Counter(i["generic_requirement"] for i in lang_items)

    return {
        "builtin_attributes": {
            "builtin_attributes_symbol_count": len(builtin_attr_syms),
            "gated_cfgs_count": len(gated_cfgs),
            "gated_cfgs": gated_cfgs,
            "registered_attribute_parsers_count": len(registered_parsers),
            "parsed_attribute_paths_count": len(parsed_attributes_inventory),
            "special_pre_lowering_attributes": ["cfg", "cfg_attr"],
            "attribute_kind_variant_count": len(attr_kind_variants),
            "rustc_structures_shared_types": rustc_structures_exports,
            "by_safety": dict(safety_counts),
            "by_attribute_type": dict(scope_counts),
            "by_gate_class": dict(gate_counts),
            "unsafe_attributes": unsafe_attributes,
            "crate_level_only_attributes": sorted(
                a["path"]
                for a in parsed_attributes_inventory
                if a["attribute_type"] == "CrateLevel"
            ),
            "compiler_builtins_gated_attributes": sorted(
                a["path"]
                for a in parsed_attributes_inventory
                if a["gate_class"] == "CompilerBuiltins"
            ),
            "parsed_attributes": parsed_attributes_inventory,
        },
        "builtin_macros_and_derives": {
            "total_registered_in_builtin_macros": (
                len(bang_macros) + len(attr_macros) + len(derive_macros) + len(manual_macros)
            ),
            "ast_bang_macros_count": len(bang_macros),
            "ast_attr_macros_count": len(attr_macros),
            "ast_derive_macros_count": len(derive_macros),
            "proc_macro_and_contract_builtins_count": len(manual_macros),
            "expand_queries_cache": {
                "crate": "compiler/rustc_expand_queries",
                "query_name": "derive_macro_expansion",
                "hook_static": "rustc_expand::proc_macro::EXPAND_DERIVE_MACRO_CACHED",
                "invalidation_dep": "tcx.crate_hash(macro_def_id.krate)",
            },
            "bang_macros": bang_macros,
            "attr_macros": attr_macros,
            "derive_macros": derive_macros,
            "manual_macros": manual_macros,
        },
        "lang_items": {
            "total_count": len(lang_items),
            "weak_lang_items_count": len(weak_map),
            "weak_lang_items": weak_map,
            "by_target": dict(li_target_counts.most_common()),
            "by_generic_requirement": dict(li_generic_counts.most_common()),
            "library_occurrences_by_tree": dict(lang_defs_by_crate.most_common()),
            "defined_in_core_count": sum(
                1 for i in lang_items if "library/core" in i["defined_in_library_crates"]
            ),
            "defined_in_alloc_count": sum(
                1 for i in lang_items if "library/alloc" in i["defined_in_library_crates"]
            ),
            "defined_in_std_count": sum(
                1 for i in lang_items if "library/std" in i["defined_in_library_crates"]
            ),
            "defined_in_rtstartup_count": sum(
                1 for i in lang_items if "library/rtstartup" in i["defined_in_library_crates"]
            ),
            "not_in_library_tree_test_or_internal": [
                i["lang_name"] for i in lang_items if not i["defined_in_library_crates"]
            ],
            "items": lang_items,
        },
    }


def extract_lints_and_error_codes(reader: GitRevisionReader) -> dict:
    lint_candidate_paths = (
        reader.paths_under("compiler/rustc_lint_defs/", ".rs")
        + reader.paths_under("compiler/rustc_lint/", ".rs")
        + reader.paths_under("compiler/rustc_session/", ".rs")
        + reader.paths_under("src/librustdoc/", ".rs")
    )
    texts = reader.read_many(lint_candidate_paths)

    lints = []
    tool_lints = []

    decl_lint_re = re.compile(r"\bdeclare_lint!\s*\{")
    decl_tool_re = re.compile(r"\bdeclare_tool_lint!\s*\{")
    decl_rustdoc_re = re.compile(r"\bdeclare_rustdoc_lint!\s*\{")

    for fp, src in sorted(texts.items()):
        if fp == "compiler/rustc_lint_defs/src/lib.rs":
            continue
        for m in decl_lint_re.finditer(src):
            body = strip_line_comments(extract_delimited(src, m.end() - 1, "{", "}"))
            mh = re.search(
                r"(?:pub(?:\([^)]*\))?\s+)?([A-Z][A-Z0-9_]+)\s*,\s*(Allow|Warn|Deny|Forbid)\s*,",
                body,
            )
            if not mh:
                continue
            ident, level = mh.group(1), mh.group(2)
            m_gate = re.search(r"@feature_gate\s*=\s*([a-zA-Z0-9_]+)", body)
            m_ed = re.search(
                r"@edition\s+(Edition\w+)\s*=>\s*(Allow|Warn|Deny|Forbid)", body
            )
            fcw_reason = None
            if "@future_incompatible" in body:
                m_fcw_kind = re.search(
                    r"fcw!\(\s*([A-Za-z0-9_]+)|FutureIncompatibilityReason::([A-Za-z0-9_]+)",
                    body,
                )
                fcw_reason = (
                    (m_fcw_kind.group(1) or m_fcw_kind.group(2))
                    if m_fcw_kind
                    else "FutureIncompatible"
                )
            lints.append(
                {
                    "ident": ident,
                    "name": ident.lower(),
                    "default_level": level,
                    "feature_gate": m_gate.group(1) if m_gate else None,
                    "edition_override": (
                        {"edition": m_ed.group(1), "level": m_ed.group(2)} if m_ed else None
                    ),
                    "future_incompatible_reason": fcw_reason,
                    "report_in_external_macro": "report_in_external_macro" in body,
                    "crate_level_only": "crate_level_only" in body,
                    "eval_always": "@eval_always = true" in body or "eval_always" in body,
                    "source_file": fp,
                }
            )

        for m in decl_tool_re.finditer(src):
            body = strip_line_comments(extract_delimited(src, m.end() - 1, "{", "}"))
            mh = re.search(
                r"(?:pub(?:\([^)]*\))?\s+)?([a-z0-9_]+)\s*::\s*([A-Z][A-Z0-9_]+)\s*,\s*(Allow|Warn|Deny|Forbid)\s*,",
                body,
            )
            if not mh:
                continue
            tool, ident, level = mh.group(1), mh.group(2), mh.group(3)
            m_gate = re.search(r"@feature_gate\s*=\s*([a-zA-Z0-9_]+)", body)
            tool_lints.append(
                {
                    "tool": tool,
                    "ident": ident,
                    "name": f"{tool}::{ident.lower()}",
                    "default_level": level,
                    "feature_gate": m_gate.group(1) if m_gate else None,
                    "source_file": fp,
                }
            )

        for m in decl_rustdoc_re.finditer(src):
            body = strip_line_comments(extract_delimited(src, m.end() - 1, "{", "}"))
            mh = re.search(
                r"([A-Z][A-Z0-9_]+)\s*,\s*(Allow|Warn|Deny|Forbid)\s*,",
                body,
            )
            if not mh:
                continue
            ident, level = mh.group(1), mh.group(2)
            m_gate = re.search(r"@feature_gate\s*=\s*([a-zA-Z0-9_]+)", body)
            tool_lints.append(
                {
                    "tool": "rustdoc",
                    "ident": ident,
                    "name": f"rustdoc::{ident.lower()}",
                    "default_level": level,
                    "feature_gate": m_gate.group(1) if m_gate else None,
                    "source_file": fp,
                }
            )

    lint_lib_rs = strip_line_comments(texts["compiler/rustc_lint/src/lib.rs"])
    rustdoc_lint_rs = strip_line_comments(texts["src/librustdoc/lint.rs"])

    lint_groups = []
    pos = 0
    while True:
        idx = lint_lib_rs.find("add_lint_group!(", pos)
        if idx < 0:
            break
        call_body = extract_delimited(lint_lib_rs, idx, "(", ")")
        pos = idx + len(call_body) + 2
        if "$name" in call_body:
            continue
        m_gn = re.match(r'\s*"([^"]+)"\s*,(.*)', call_body, re.S)
        if m_gn:
            gname = m_gn.group(1)
            members = [
                x.strip().lower()
                for x in m_gn.group(2).split(",")
                if re.fullmatch(r"[A-Z0-9_]+", x.strip())
            ]
            lint_groups.append({"name": gname, "kind": "static_builtin", "members": members})

    for src_label, src_txt in [("rustc_lint", lint_lib_rs), ("rustdoc", rustdoc_lint_rs)]:
        pos = 0
        while True:
            idx = src_txt.find(".register_group(", pos)
            if idx < 0:
                break
            call_body = extract_delimited(src_txt, idx, "(", ")")
            pos = idx + len(call_body) + 2
            if "$name" in call_body:
                continue
            m_rg = re.match(
                r'\s*(?:true|false)\s*,\s*"([^"]+)"\s*,\s*(Some\("[^"]+"\)|None)\s*,(.*)',
                call_body,
                re.S,
            )
            if m_rg:
                gname, depr, raw_vec = m_rg.groups()
                members = [
                    x.lower() for x in re.findall(r"LintId::of\(([A-Z0-9_]+)\)", raw_vec)
                ]
                lint_groups.append(
                    {
                        "name": gname,
                        "kind": f"explicit_{src_label}",
                        "deprecated_alias": depr[6:-2] if depr.startswith("Some") else None,
                        "members": members,
                    }
                )

    group_aliases = [
        {"target": m.group(1), "alias": m.group(2)}
        for m in re.finditer(
            r'register_group_alias\(\s*"([^"]+)"\s*,\s*"([^"]+)"\s*\)', lint_lib_rs
        )
    ]
    renamed_lints = [
        {"old": m.group(1), "new": m.group(2)}
        for m in re.finditer(
            r'register_renamed\(\s*"([^"]+)"\s*,\s*"([^"]+)"\s*\)', lint_lib_rs
        )
    ]
    removed_lints = [
        m.group(1) for m in re.finditer(r'register_removed\(\s*"([^"]+)"\s*,', lint_lib_rs)
    ]

    err_lib_rs = reader.read_text("compiler/rustc_error_codes/src/lib.rs")
    registered_codes = [f"E{c}" for c in re.findall(r"^\s*(\d{4})\s*,", err_lib_rs, re.M)]
    err_md_paths = reader.paths_under("compiler/rustc_error_codes/src/error_codes/", ".md")
    err_mds = reader.read_many(err_md_paths)
    no_longer_emitted = []
    active_emitted = []
    for p, md_txt in sorted(err_mds.items()):
        code = Path(p).stem
        low = md_txt.lower()
        if (
            "no longer emitted by the compiler" in low
            or "not emitted by the compiler any more" in low
        ):
            no_longer_emitted.append(code)
        else:
            active_emitted.append(code)

    level_counts = Counter(l["default_level"] for l in lints)
    fcw_counts = Counter(
        l["future_incompatible_reason"] for l in lints if l["future_incompatible_reason"]
    )
    lint_file_counts = Counter(l["source_file"] for l in lints)

    return {
        "compiler_lints": {
            "total_declare_lint_count": len(lints),
            "in_rustc_lint_defs_builtin_rs": sum(
                1 for l in lints if l["source_file"] == "compiler/rustc_lint_defs/src/builtin.rs"
            ),
            "in_rustc_lint_internal_and_passes": sum(
                1 for l in lints if l["source_file"] != "compiler/rustc_lint_defs/src/builtin.rs"
            ),
            "by_default_level": dict(level_counts),
            "future_incompatible_count": sum(
                1 for l in lints if l["future_incompatible_reason"] is not None
            ),
            "by_future_incompat_reason": dict(fcw_counts),
            "edition_overridden_count": sum(
                1 for l in lints if l["edition_override"] is not None
            ),
            "feature_gated_count": sum(1 for l in lints if l["feature_gate"] is not None),
            "crate_level_only_count": sum(1 for l in lints if l["crate_level_only"]),
            "by_source_file": dict(lint_file_counts.most_common()),
            "lints": lints,
        },
        "tool_lints": {
            "total_declare_tool_lint_count": len(tool_lints),
            "by_default_level": dict(Counter(t["default_level"] for t in tool_lints)),
            "lints": tool_lints,
        },
        "lint_groups": {
            "static_and_explicit_groups_count": len(lint_groups),
            "dynamic_groups": [
                "warnings",
                "future_incompatible",
                "rust_2018_compatibility",
                "rust_2021_compatibility",
                "rust_2024_compatibility",
                "edition_future_compatibility",
            ],
            "group_aliases": group_aliases,
            "renamed_lints_count": len(renamed_lints),
            "removed_lints_count": len(removed_lints),
            "groups": lint_groups,
            "renamed_lints": renamed_lints,
            "removed_lint_names": removed_lints,
        },
        "error_codes": {
            "registered_count": len(registered_codes),
            "markdown_files_count": len(err_md_paths),
            "active_emitted_docs_count": len(active_emitted),
            "retired_no_longer_emitted_docs_count": len(no_longer_emitted),
            "min_code": registered_codes[0] if registered_codes else None,
            "max_code": registered_codes[-1] if registered_codes else None,
            "codes": registered_codes,
            "retired_codes": no_longer_emitted,
        },
    }


def extract_typeck_solver_pattern_borrowck(reader: GitRevisionReader) -> dict:
    target_crates = [
        "rustc_hir_analysis",
        "rustc_hir_typeck",
        "rustc_infer",
        "rustc_trait_selection",
        "rustc_next_trait_solver",
        "rustc_type_ir",
        "rustc_pattern_analysis",
        "rustc_mir_build",
        "rustc_borrowck",
    ]
    crate_metrics = {}
    for c in target_crates:
        rs_files = reader.paths_under(f"compiler/{c}/src/", ".rs")
        texts = reader.read_many(rs_files)
        raw_total = 0
        sloc_total = 0
        for t in texts.values():
            r, s = count_sloc(t)
            raw_total += r
            sloc_total += s
        crate_metrics[c] = {
            "rs_files": len(rs_files),
            "raw_lines": raw_total,
            "sloc": sloc_total,
        }

    ctor_rs = reader.read_text("compiler/rustc_pattern_analysis/src/constructor.rs")
    ctor_idx = ctor_rs.find("pub enum Constructor<")
    ctor_variants = []
    if ctor_idx >= 0:
        ctor_body = extract_delimited(ctor_rs, ctor_idx, "{", "}")
        depth = 0
        for line in strip_line_comments(ctor_body).splitlines():
            s = line.strip()
            if depth == 0 and s:
                mv = re.match(r"^([A-Z][A-Za-z0-9_]*)\b", s)
                if mv:
                    ctor_variants.append(mv.group(1))
            depth += line.count("{") - line.count("}")

    solve_mod = reader.read_text("compiler/rustc_type_ir/src/solve/mod.rs")
    cs_idx = solve_mod.find("pub enum CandidateSource<")
    candidate_sources = []
    if cs_idx >= 0:
        cs_body = extract_delimited(solve_mod, cs_idx, "{", "}")
        for line in strip_line_comments(cs_body).splitlines():
            mv = re.match(r"^\s*([A-Z][A-Za-z0-9_]*)\b", line)
            if mv:
                candidate_sources.append(mv.group(1))

    facts_rs = reader.read_text("compiler/rustc_borrowck/src/polonius/legacy/facts.rs")
    polonius_fact_tables = sorted(
        set(re.findall(r'"([a-z_]+)\.facts"', strip_line_comments(facts_rs)))
    )

    return {
        "crate_metrics": crate_metrics,
        "next_trait_solver": {
            "config_enum": "rustc_session::config::NextSolverConfig",
            "modes": [
                "Coherence (default unless CFG_DEFAULT_NEXT_SOLVER_GLOBALLY)",
                "Globally (-Znext-solver=globally)",
            ],
            "candidate_sources": candidate_sources,
        },
        "pattern_analysis": {
            "constructor_variant_count": len(ctor_variants),
            "constructor_variants": ctor_variants,
        },
        "borrowck": {
            "polonius_enum": "rustc_session::config::Polonius",
            "modes": [
                "Off (default NLL)",
                "Legacy (-Zpolonius / -Zpolonius=legacy)",
                "Next (-Zpolonius=next)",
            ],
            "legacy_all_facts_tables": polonius_fact_tables,
        },
    }


def extract_proc_macro_bridge(reader: GitRevisionReader) -> dict:
    bridge_files = reader.paths_under("library/proc_macro/src/bridge/", ".rs")
    texts = reader.read_many(
        bridge_files + ["compiler/rustc_expand/src/proc_macro_server.rs"]
    )
    mod_rs = texts["library/proc_macro/src/bridge/mod.rs"]
    client_rs = texts["library/proc_macro/src/bridge/client.rs"]

    w_idx = mod_rs.find("macro_rules! with_api")
    m_call_idx = mod_rs.find("$m! {", w_idx)
    rpc_methods = []
    if m_call_idx >= 0:
        body = strip_line_comments(extract_delimited(mod_rs, m_call_idx, "{", "}"))
        for idx, raw_stmt in enumerate(body.split(";")):
            s = " ".join(raw_stmt.split())
            if not s.startswith("fn "):
                continue
            m = re.match(r"^fn\s+([a-z0-9_]+)\s*\((.*)\)\s*(?:->\s*(.+))?$", s)
            if not m:
                continue
            name, args, ret = m.group(1), m.group(2).strip(), (m.group(3) or "()").strip()
            category = (
                "token_stream"
                if name.startswith("ts_")
                else "span"
                if name.startswith("span_")
                else "symbol"
                if name.startswith("symbol_")
                else "session_and_diag"
            )
            rpc_methods.append(
                {
                    "tag_discriminant_u8": idx,
                    "name": name,
                    "category": category,
                    "args": args,
                    "return_type": ret,
                }
            )

    lk_idx = mod_rs.find("pub enum LitKind {")
    lit_kinds = []
    if lk_idx >= 0:
        lk_body = extract_delimited(mod_rs, lk_idx, "{", "}")
        for line in strip_line_comments(lk_body).splitlines():
            s = line.strip().rstrip(",")
            if s:
                lit_kinds.append(s)

    bridge_sloc = {}
    for p in bridge_files:
        r, s = count_sloc(texts[p])
        bridge_sloc[p] = {"raw_lines": r, "sloc": s}
    srv_r, srv_s = count_sloc(texts["compiler/rustc_expand/src/proc_macro_server.rs"])

    pm_idx = client_rs.find("pub enum ProcMacro {")
    pm_variants = []
    if pm_idx >= 0:
        pm_body = extract_delimited(client_rs, pm_idx, "{", "}")
        depth = 0
        for line in strip_line_comments(pm_body).splitlines():
            s = line.strip()
            if depth == 0 and s:
                mv = re.match(r"^([A-Z][A-Za-z0-9_]*)\b", s)
                if mv:
                    pm_variants.append(mv.group(1))
            depth += line.count("{") - line.count("}")

    return {
        "bridge_files_count": len(bridge_files),
        "bridge_total_sloc": sum(v["sloc"] for v in bridge_sloc.values()),
        "proc_macro_server_sloc": srv_s,
        "proc_macro_server_raw_lines": srv_r,
        "rpc_methods_count": len(rpc_methods),
        "rpc_methods_by_category": dict(Counter(m["category"] for m in rpc_methods)),
        "rpc_methods": rpc_methods,
        "lit_kind_variants": lit_kinds,
        "exported_proc_macro_variants": pm_variants,
        "handle_arenas": [
            {"type": "TokenStream", "store_kind": "OwnedStore", "wire_type": "NonZero<u32>"},
            {"type": "Span", "store_kind": "InternedStore", "wire_type": "NonZero<u32>"},
            {
                "type": "Symbol",
                "store_kind": "InternedStore (or Predefined)",
                "wire_type": "NonZero<u32>",
            },
        ],
    }


def extract_rmeta_and_rustdoc_json(reader: GitRevisionReader) -> dict:
    rmeta_mod = reader.read_text("compiler/rustc_metadata/src/rmeta/mod.rs")
    rustdoc_json_lib = reader.read_text("src/rustdoc-json-types/lib.rs")

    m_ver = re.search(r"const METADATA_VERSION:\s*u8\s*=\s*(\d+);", rmeta_mod)
    metadata_version = int(m_ver.group(1)) if m_ver else None

    def extract_struct_fields(src: str, struct_name: str) -> list[dict]:
        m = re.search(rf"pub(?:\([^)]*\))?\s+struct\s+{struct_name}\s*\{{", src)
        if not m:
            return []
        body = extract_delimited(src, m.end() - 1, "{", "}")
        fields = []
        for line in strip_line_comments(body).splitlines():
            s = line.strip().rstrip(",")
            if not s or s.startswith("#["):
                continue
            s = re.sub(r"^pub(?:\([^)]*\))?\s+", "", s)
            if ":" in s:
                fname, fty = [x.strip() for x in s.split(":", 1)]
                fields.append({"name": fname, "type": fty})
        return fields

    crate_header_fields = extract_struct_fields(rmeta_mod, "CrateHeader")
    crate_root_fields = extract_struct_fields(rmeta_mod, "CrateRoot")
    crate_root_unhashed_fields = extract_struct_fields(rmeta_mod, "CrateRootUnhashed")

    dt_idx = rmeta_mod.find("define_tables! {")
    defaulted_tables = []
    optional_tables = []
    if dt_idx >= 0:
        dt_body = strip_line_comments(extract_delimited(rmeta_mod, dt_idx, "{", "}"))
        if "- defaulted:" in dt_body and "- optional:" in dt_body:
            def_part = dt_body.split("- defaulted:", 1)[1].split("- optional:", 1)[0]
            opt_part = dt_body.split("- optional:", 1)[1]
            for line in def_part.splitlines():
                s = line.strip().rstrip(",")
                m = re.match(r"^([a-z0-9_]+)\s*:\s*Table<(.+)>$", s)
                if m:
                    defaulted_tables.append(
                        {"name": m.group(1), "element_type": m.group(2).strip()}
                    )
            for line in opt_part.splitlines():
                s = line.strip().rstrip(",")
                m = re.match(r"^([a-z0-9_]+)\s*:\s*Table<(.+)>$", s)
                if m:
                    optional_tables.append(
                        {"name": m.group(1), "element_type": m.group(2).strip()}
                    )

    m_fver = re.search(r"pub const FORMAT_VERSION:\s*u32\s*=\s*(\d+);", rustdoc_json_lib)
    m_latest = re.search(r"// Latest feature:\s*(.+)", rustdoc_json_lib)
    rustdoc_crate_fields = extract_struct_fields(rustdoc_json_lib, "Crate")

    ie_idx = rustdoc_json_lib.find("pub enum ItemEnum {")
    item_enum_variants = []
    if ie_idx >= 0:
        ie_body = extract_delimited(rustdoc_json_lib, ie_idx, "{", "}")
        depth = 0
        for line in strip_line_comments(ie_body).splitlines():
            s = line.strip().rstrip(",")
            if depth == 0 and s and not s.startswith("#["):
                mv = re.match(r"^([A-Z][A-Za-z0-9_]*)", s)
                if mv:
                    item_enum_variants.append(mv.group(1))
            depth += line.count("{") - line.count("}")

    pub_types = re.findall(r"^pub (?:struct|enum)\s+([A-Za-z0-9_]+)\b", rustdoc_json_lib, re.M)

    return {
        "rmeta": {
            "metadata_version": metadata_version,
            "magic_bytes_ascii": "rust\\x00\\x00\\x00\\x0c",
            "fixed_header_layout": [
                {"offset": 0, "size": 8, "field": "METADATA_HEADER (b'rust\\0\\0\\0\\x0c')"},
                {"offset": 8, "size": 8, "field": "ROOT_POS_OFFSET (u64 LE offset of CrateRoot)"},
                {
                    "offset": 16,
                    "size": 8,
                    "field": "UNHASHED_POS_OFFSET (u64 LE offset of CrateRootUnhashed)",
                },
                {
                    "offset": 24,
                    "size": 16,
                    "field": "CRATE_HASH_OFFSET (128-bit Fingerprint / Svh LE bytes)",
                },
                {
                    "offset": 40,
                    "size": "variable",
                    "field": "VERSION_OFFSET (length-prefixed rustc_version string)",
                },
            ],
            "crate_header_fields": crate_header_fields,
            "crate_root_fields_count": len(crate_root_fields),
            "crate_root_fields": crate_root_fields,
            "crate_root_unhashed_fields": crate_root_unhashed_fields,
            "lazy_tables_total_count": len(defaulted_tables) + len(optional_tables),
            "lazy_tables_defaulted_count": len(defaulted_tables),
            "lazy_tables_optional_count": len(optional_tables),
            "lazy_tables_defaulted": defaulted_tables,
            "lazy_tables_optional": optional_tables,
            "svh_algorithm": {
                "default_flag": "-Z metadata-crate-hash=yes",
                "hash_function": "XxHash3_128 (128-bit Fingerprint)",
                "seeded_supplement": "StableHasher(dep_tracking_hash(true) + compute_hir_hash(tcx))",
                "streamed_bytes": "All bytes flushed prior to CrateRootUnhashed",
                "excluded_unhashed_tail": "CrateRootUnhashed { extra_filename, dep_extra_filenames }",
            },
            "stable_crate_id_algorithm": {
                "hash_function": "StableHasher -> Hash64 (64-bit SipHash-1-3)",
                "inputs_in_order": [
                    "crate_name.as_str()",
                    "b'metadata' + sorted_deduped_c_metadata_with_len_prefixes",
                    "b'exe' if is_exe else b'lib'",
                    "RUSTC_FORCE_RUSTC_VERSION env or cfg_version.as_bytes()",
                ],
            },
        },
        "rustdoc_json_types": {
            "format_version": int(m_fver.group(1)) if m_fver else None,
            "latest_feature_comment": m_latest.group(1).strip() if m_latest else None,
            "public_structs_and_enums_count": len(pub_types),
            "crate_root_fields": rustdoc_crate_fields,
            "item_enum_variant_count": len(item_enum_variants),
            "item_enum_variants": item_enum_variants,
        },
    }


def decode_uleb_or_len_str(buf: bytes, offset: int) -> tuple[str, int]:
    val = 0
    shift = 0
    pos = offset
    while pos < len(buf):
        b = buf[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            break
        shift += 7
    s = buf[pos : pos + val].decode("utf-8", errors="replace")
    return s, pos + val


def parse_rmeta_binary_header(blob: bytes) -> dict:
    magic = blob[:4]
    zero3 = blob[4:7]
    ver = blob[7]
    info: dict = {
        "total_size_bytes": len(blob),
        "header_hex_first_16": blob[:16].hex(),
        "magic_ok": magic == b"rust" and zero3 == b"\x00\x00\x00",
        "metadata_version": ver,
    }
    if ver == 10:
        root_pos = struct.unpack_from("<Q", blob, 8)[0]
        ver_str, after_ver = decode_uleb_or_len_str(blob, 16)
        info.update(
            {
                "root_pos": root_pos,
                "version_offset": 16,
                "rustc_version_string": ver_str,
                "payload_after_version_offset": after_ver,
            }
        )
    elif ver >= 12:
        root_pos = struct.unpack_from("<Q", blob, 8)[0]
        unhashed_pos = struct.unpack_from("<Q", blob, 16)[0]
        svh_lo, svh_hi = struct.unpack_from("<QQ", blob, 24)
        ver_str, after_ver = decode_uleb_or_len_str(blob, 40)
        info.update(
            {
                "root_pos": root_pos,
                "unhashed_pos": unhashed_pos,
                "crate_hash_svh_hex": blob[24:40].hex(),
                "crate_hash_u64_pair": [hex(svh_lo), hex(svh_hi)],
                "version_offset": 40,
                "rustc_version_string": ver_str,
                "payload_after_version_offset": after_ver,
            }
        )
    else:
        root_pos = struct.unpack_from("<Q", blob, 8)[0]
        info["root_pos"] = root_pos
    return info


def run_live_toolchain_probes() -> dict:
    if not shutil.which("rustc") or not shutil.which("rustdoc"):
        return {"executed": False, "reason": "rustc/rustdoc not on PATH"}

    results: dict = {"executed": True, "toolchains": {}}
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)

        for tc in ("+1.99.1", "+nightly"):
            vv = subprocess.run(["rustc", tc, "-vV"], capture_output=True, text=True)
            if vv.returncode == 0:
                meta = {}
                for line in vv.stdout.strip().splitlines():
                    if ":" in line:
                        k, v = line.split(":", 1)
                        meta[k.strip()] = v.strip()
                    else:
                        meta["banner"] = line.strip()
                results["toolchains"][tc] = meta

        specimen_src = (
            "pub struct Pair<T>(pub T, pub u32);\n"
            "pub const MAGIC: u32 = 42;\n"
            "pub fn add(a: u32, b: u32) -> u32 { a.wrapping_add(b) }\n"
        )
        src_file = tmp_dir / "specimen.rs"
        src_file.write_text(specimen_src, encoding="utf-8")

        rmeta_probes = {}
        for label, tc in [("rust_1_99_1", "+1.99.1"), ("rust_nightly", "+nightly")]:
            if tc not in results["toolchains"]:
                continue
            out_a = tmp_dir / f"{label}_a.rmeta"
            r_a = subprocess.run(
                [
                    "rustc",
                    tc,
                    "--edition=2024",
                    "--crate-name=specimen",
                    "--crate-type=rlib",
                    "--emit=metadata",
                    "-Cmetadata=alpha1",
                    "-Cextra-filename=-ef1",
                    "-o",
                    str(out_a),
                    str(src_file),
                ],
                capture_output=True,
                text=True,
            )
            if r_a.returncode == 0 and out_a.is_file():
                hdr_a = parse_rmeta_binary_header(out_a.read_bytes())
                out_b = tmp_dir / f"{label}_b.rmeta"
                r_b = subprocess.run(
                    [
                        "rustc",
                        tc,
                        "--edition=2024",
                        "--crate-name=specimen",
                        "--crate-type=rlib",
                        "--emit=metadata",
                        "-Cmetadata=alpha1",
                        "-Cextra-filename=-ef2_longer_suffix",
                        "-o",
                        str(out_b),
                        str(src_file),
                    ],
                    capture_output=True,
                    text=True,
                )
                if r_b.returncode == 0 and out_b.is_file():
                    hdr_b = parse_rmeta_binary_header(out_b.read_bytes())
                    hdr_a["extra_filename_perturbation_size_delta_bytes"] = (
                        hdr_b["total_size_bytes"] - hdr_a["total_size_bytes"]
                    )
                    if "crate_hash_svh_hex" in hdr_a and "crate_hash_svh_hex" in hdr_b:
                        hdr_a["svh_invariant_under_extra_filename_change"] = (
                            hdr_a["crate_hash_svh_hex"] == hdr_b["crate_hash_svh_hex"]
                        )
                rmeta_probes[label] = hdr_a
        results["rmeta_header_probes"] = rmeta_probes

        if "+nightly" in results["toolchains"]:
            nocore_cases = [
                (
                    "empty_crate_zero_lang_items",
                    "#![feature(no_core)]\n#![no_core]\n",
                ),
                (
                    "unit_struct_without_lang_items",
                    "#![feature(no_core)]\n#![no_core]\npub struct Unit;\n",
                ),
                (
                    "fn_with_sized_hierarchy_only",
                    "#![feature(no_core, lang_items)]\n#![no_core]\n"
                    '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
                    '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
                    '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
                    "pub struct S(pub i32);\n"
                    "pub fn id(x: S) -> S { x }\n",
                ),
                (
                    "copy_and_sized_hierarchy_without_freeze",
                    "#![feature(no_core, lang_items)]\n#![no_core]\n"
                    '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
                    '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
                    '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
                    '#[lang = "copy"] pub trait Copy: Sized {}\n'
                    "pub struct S(pub i32);\n"
                    "pub fn id(x: S) -> S { x }\n",
                ),
                (
                    "copy_freeze_and_reference_floor",
                    "#![feature(no_core, lang_items, auto_traits)]\n#![no_core]\n"
                    '#[lang = "pointee_sized"] pub trait PointeeSized {}\n'
                    '#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}\n'
                    '#[lang = "sized"] pub trait Sized: MetaSized {}\n'
                    '#[lang = "copy"] pub trait Copy: Sized {}\n'
                    '#[lang = "freeze"] pub unsafe auto trait Freeze {}\n'
                    '#[lang = "legacy_receiver"] pub trait LegacyReceiver {}\n'
                    "impl<T: ?Sized> LegacyReceiver for &T {}\n"
                    "impl Copy for i32 {}\n"
                    "pub fn read_ref(r: &i32) -> i32 { *r }\n",
                ),
            ]
            nocore_results = []
            for cname, code in nocore_cases:
                p_rs = tmp_dir / f"{cname}.rs"
                p_out = tmp_dir / f"{cname}.rmeta"
                p_rs.write_text(code, encoding="utf-8")
                rc_proc = subprocess.run(
                    [
                        "rustc",
                        "+nightly",
                        "--edition=2024",
                        "--crate-type=rlib",
                        "--emit=metadata",
                        "-o",
                        str(p_out),
                        str(p_rs),
                    ],
                    capture_output=True,
                    text=True,
                )
                first_err = next(
                    (ln for ln in rc_proc.stderr.splitlines() if ln.startswith("error")),
                    None,
                )
                nocore_results.append(
                    {
                        "case": cname,
                        "exit_code": rc_proc.returncode,
                        "first_error": first_err,
                    }
                )
            results["no_core_lang_item_ladder"] = nocore_results

            rdoc_src = (
                "//! Specimen crate docs.\n"
                "pub mod sub {\n"
                "    /// Documented struct.\n"
                "    pub struct Widget<T> { pub val: T }\n"
                "}\n"
                "pub enum Choice { A, B(u32) }\n"
                "pub trait Action { fn run(&self) -> u32; }\n"
                "impl Action for Choice {\n"
                "    fn run(&self) -> u32 { match self { Self::A => 0, Self::B(v) => *v } }\n"
                "}\n"
                "#[macro_export]\n"
                "macro_rules! make_zero { () => { 0u32 }; }\n"
            )
            rdoc_rs = tmp_dir / "doc_specimen.rs"
            rdoc_out_dir = tmp_dir / "doc_json"
            rdoc_rs.write_text(rdoc_src, encoding="utf-8")
            rdoc_proc = subprocess.run(
                [
                    "rustdoc",
                    "+nightly",
                    "-Zunstable-options",
                    "--output-format=json",
                    "--edition=2024",
                    "--crate-name=doc_specimen",
                    "-o",
                    str(rdoc_out_dir),
                    str(rdoc_rs),
                ],
                capture_output=True,
                text=True,
            )
            json_file = rdoc_out_dir / "doc_specimen.json"
            if rdoc_proc.returncode == 0 and json_file.is_file():
                doc_obj = json.loads(json_file.read_text(encoding="utf-8"))
                item_kinds = Counter()
                for item in doc_obj.get("index", {}).values():
                    inner = item.get("inner")
                    if isinstance(inner, dict) and inner:
                        item_kinds[next(iter(inner.keys()))] += 1
                    elif isinstance(inner, str):
                        item_kinds[inner] += 1
                results["rustdoc_json_live_probe"] = {
                    "exit_code": 0,
                    "emitted_format_version": doc_obj.get("format_version"),
                    "top_level_keys": sorted(doc_obj.keys()),
                    "includes_private": doc_obj.get("includes_private"),
                    "index_item_count": len(doc_obj.get("index", {})),
                    "paths_entry_count": len(doc_obj.get("paths", {})),
                    "external_crates_count": len(doc_obj.get("external_crates", {})),
                    "index_item_inner_kinds": dict(item_kinds.most_common()),
                    "target_triple": doc_obj.get("target", {}).get("triple"),
                    "target_features_count": len(
                        doc_obj.get("target", {}).get("target_features", [])
                    ),
                }

            w_help_summary = {}
            for tc_key, tc_arg in [("rust_1_99_1", "+1.99.1"), ("rust_nightly", "+nightly")]:
                if tc_arg not in results["toolchains"]:
                    continue
                wh = subprocess.run(
                    ["rustc", tc_arg, "-W", "help"], capture_output=True, text=True
                )
                if wh.returncode == 0:
                    lines = wh.stdout.splitlines()
                    section = None
                    lint_lvls: Counter[str] = Counter()
                    group_cnt = 0
                    for ln in lines:
                        s = ln.strip()
                        if s.startswith("Lint checks provided by rustc"):
                            section = "lints"
                            continue
                        if s.startswith("Lint groups provided by rustc"):
                            section = "groups"
                            continue
                        if s.startswith("CompilerLintTools") or s.startswith("Lint tools"):
                            section = "other"
                            continue
                        if not s or s.startswith(("----", "name  ")):
                            continue
                        if section == "lints":
                            parts = s.split()
                            if len(parts) >= 2 and parts[1] in {"allow", "warn", "deny", "forbid"}:
                                lint_lvls[parts[1]] += 1
                        elif section == "groups":
                            if "  " in s or s.startswith("warnings"):
                                group_cnt += 1
                    w_help_summary[tc_key] = {
                        "total_lints_reported": sum(lint_lvls.values()),
                        "by_default_level": dict(lint_lvls),
                        "lint_groups_reported": group_cnt,
                    }
            results["rustc_w_help_live_probe"] = w_help_summary

    return results


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--rust-repo",
        default=".",
        help="Path to local rust-lang/rust Git clone (read-only object inspection; default: .)",
    )
    ap.add_argument(
        "--rev",
        default=DEFAULT_REV,
        help=f"Immutable Git commit SHA to inspect (default: {DEFAULT_REV})",
    )
    ap.add_argument(
        "--out",
        default=str(
            Path(__file__).resolve().parent / "frontend_features_attrs_langitems.json"
        ),
        help="Output JSON path",
    )
    ap.add_argument(
        "--skip-live-probes",
        action="store_true",
        help="Skip live rustc/rustdoc TemporaryDirectory probes",
    )
    args = ap.parse_args()

    reader = GitRevisionReader(args.rust_repo, args.rev)
    symbol_rs = reader.read_text("compiler/rustc_span/src/symbol.rs")
    kw_map, sym_map, kw_categories = parse_symbol_map(symbol_rs)

    sec1 = extract_editions_and_features(reader, kw_categories)
    sec2 = extract_attrs_macros_and_lang_items(reader, kw_map, sym_map)
    sec3 = extract_lints_and_error_codes(reader)
    sec4 = extract_typeck_solver_pattern_borrowck(reader)
    sec5 = extract_proc_macro_bridge(reader)
    sec6 = extract_rmeta_and_rustdoc_json(reader)
    live = {} if args.skip_live_probes else run_live_toolchain_probes()

    payload = {
        "schema_version": 1,
        "subject_repository": "rust-lang/rust",
        "subject_revision": args.rev,
        "surface_editions_and_features": sec1,
        "attributes_macros_and_lang_items": sec2,
        "lints_and_error_codes": sec3,
        "typeck_trait_solver_pattern_and_borrowck": sec4,
        "proc_macro_bridge_protocol": sec5,
        "rmeta_and_rustdoc_json_contracts": sec6,
        "live_toolchain_probes": live,
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
