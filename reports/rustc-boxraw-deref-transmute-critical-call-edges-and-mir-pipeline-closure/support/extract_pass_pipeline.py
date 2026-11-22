#!/usr/bin/env python3
"""Extract the MIR pass pipeline of `rustc_mir_transform` from source, line-accurately.

Reads `compiler/rustc_mir_transform/src/**` under `--root` (a `rust-lang/rust` checkout, or any
directory laid out the same way) and writes one JSON document with:

* `declared`  every pass named in the `declare_passes!` invocation in `lib.rs`;
* `lists`     every array literal of pass references handed to the pass manager anywhere in the
              crate, in file order, with the line of each entry, the pass-manager call it
              belongs to and the phase argument of that call;
* `policies`  for every `impl MirPass for T`, the text and line range of `fn policy` (newer
              trees) or of `fn is_enabled` / `fn is_required` (older trees);
* `census`    for every declared pass, where it is scheduled (file:line) or that it is not
              scheduled in any pass list.

Nothing is inferred beyond what the source text says; the classification fields are simple
pattern matches on the policy expression and are labelled as such.

`--fetch SHA` downloads the needed files of `rust-lang/rust` at that commit into `--root` first
(sequentially, from raw.githubusercontent.com; file list from the GitHub git-trees API).

Standard library only (Python 3.10+).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.request

CRATE = "compiler/rustc_mir_transform/src"


# ----------------------------------------------------------------------------- fetching
def http_get(url: str, tries: int = 4) -> bytes:
    last = None
    for _ in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "extract-pass-pipeline"})
            with urllib.request.urlopen(req, timeout=90) as r:
                return r.read()
        except Exception as e:  # noqa: BLE001 - retried, then re-raised
            last = e
            time.sleep(1.5)
    raise RuntimeError(f"GET {url} failed: {last}")


def fetch(sha: str, root: str) -> None:
    tree = json.loads(http_get(
        f"https://api.github.com/repos/rust-lang/rust/git/trees/{sha}:{CRATE}?recursive=1"))
    if tree.get("truncated"):
        raise RuntimeError("tree listing truncated")
    for entry in tree["tree"]:
        if entry["type"] != "blob" or not entry["path"].endswith(".rs"):
            continue
        rel = f"{CRATE}/{entry['path']}"
        dst = os.path.join(root, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        data = http_get(f"https://raw.githubusercontent.com/rust-lang/rust/{sha}/{rel}")
        with open(dst, "wb") as f:
            f.write(data)


# ----------------------------------------------------------------------------- parsing
def read(path: str) -> str:
    with open(path, encoding="utf-8") as f:
        return f.read().replace("\r", "")


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def strip_line_comment(s: str) -> str:
    return re.sub(r"//.*", "", s)


def blank_line_comments(text: str) -> str:
    """Replace every `// ...` comment by spaces of the same length (offsets stay valid)."""
    return re.sub(r"//[^\n]*", lambda m: " " * len(m.group(0)), text)


# A line that consists of exactly one pass reference, as in a multi-line pass list.
SOLO_ENTRY_LINE_RE = re.compile(
    r"^[ \t]*&(?:Lint\(|o1\()?(?:crate::)?[a-z_][a-z0-9_]*::[A-Z][A-Za-z0-9_:]*\)?,?[ \t]*$", re.M)


def parse_declared(lib: str):
    m = re.search(r"^declare_passes!\s*\{(.*?)^\}", lib, re.S | re.M)
    if not m:
        raise RuntimeError("declare_passes! invocation not found")
    body = "\n".join(strip_line_comment(l) for l in m.group(1).split("\n"))
    out = []
    for item in body.split(";"):
        item = " ".join(item.split())
        mm = re.match(r"(pub )?mod (\w+) ?: ?(.*)$", item)
        if not mm:
            continue
        module, rest = mm.group(2), mm.group(3)
        for g in re.finditer(r"(\w+)(?: ?\{([^}]*)\})?", rest):
            variants = [v.strip() for v in (g.group(2) or "").split(",") if v.strip()]
            out.append({"module": module, "type": g.group(1), "variants": variants})
    return out


ENTRY_RE = re.compile(
    r"^&(?P<lint>Lint\()?(?P<o1>o1\()?(?:crate::)?(?P<path>[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*)"
    r"(?:::default\(\))?(?P<fields> ?\{[^{}]*\})?\)?\)?$")


def parse_lists(rel: str, text: str, declared):
    """Every `&[ &a::B, ... ]` literal whose elements are pass references."""
    variant_owner = {}
    for d in declared:
        for v in d["variants"]:
            variant_owner.setdefault((d["module"], v), d["type"])
    types = {(d["module"], d["type"]) for d in declared}
    lists = []
    text = blank_line_comments(text)  # lists may start with, or contain, comment lines
    for m in re.finditer(r"&\[\s*(&[^\[\]]*?)\]", text, re.S):
        inner = m.group(1)
        base = m.start(1)
        entries, pos, ok = [], 0, True
        # split on top-level commas, keeping offsets
        depth, start = 0, 0
        parts = []
        for i, ch in enumerate(inner):
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            elif ch == "," and depth == 0:
                parts.append((start, inner[start:i]))
                start = i + 1
        parts.append((start, inner[start:]))
        for off, raw in parts:
            # drop comment lines, remember where the code token starts
            code_lines = []
            tok_off = None
            cur = off
            for ln in raw.split("\n"):
                stripped = strip_line_comment(ln).strip()
                if stripped and tok_off is None:
                    tok_off = cur + (len(ln) - len(ln.lstrip()))
                code_lines.append(stripped)
                cur += len(ln) + 1
            code = "".join(code_lines)
            if not code:
                continue
            em = ENTRY_RE.match(code)
            if not em:
                looks_like_pass_ref = re.match(
                    r"^&(?:Lint\(|o1\()?(?:crate::)?[a-z_][a-z0-9_]*::[A-Z]", code) \
                    and "'" not in code and "<" not in code
                if not looks_like_pass_ref:
                    ok = False  # not a list of pass references at all (e.g. a slice type)
                    break
                # Looks like a pass reference but has an unexpected shape: keep it, flagged.
                entries.append({"line": line_of(text, base + tok_off), "expr": code,
                                "wrapper": None, "module": None, "type": None, "variant": None,
                                "unparsed": True})
                continue
            path = em.group("path").split("::")
            entry = {"line": line_of(text, base + tok_off), "expr": code,
                     "wrapper": "Lint" if em.group("lint") else ("o1" if em.group("o1") else None)}
            if em.group("fields"):
                entry["constructed_with_fields"] = em.group("fields").strip()
            if len(path) == 1:  # a local variable holding a pass
                entry.update({"module": None, "type": path[0], "variant": None, "local_var": True})
            elif (path[0], path[1]) in types:
                entry.update({"module": path[0], "type": path[1],
                              "variant": path[2] if len(path) > 2 else None})
            elif (path[0], path[1]) in variant_owner:
                entry.update({"module": path[0], "type": variant_owner[(path[0], path[1])],
                              "variant": path[1]})
            else:
                entry.update({"module": path[0], "type": path[1],
                              "variant": path[2] if len(path) > 2 else None, "undeclared": True})
            entries.append(entry)
        if not ok or not entries:
            continue
        # the pass-manager call this literal belongs to: the nearest `run_passes*(` at or
        # before the literal within the same statement, else the next one after it.
        before = text.rfind("run_passes", 0, m.start())
        stmt_start = max(text.rfind(";", 0, m.start()), text.rfind("{", 0, m.start()))
        if before != -1 and before > stmt_start:
            call_at = before
        else:
            nxt = re.search(r"run_passes(_no_validate)?\(", text[m.end():])
            call_at = m.end() + nxt.start() if nxt else -1
        call = None
        phase = None
        if call_at != -1:
            cm = re.match(r"run_passes(_no_validate)?", text[call_at:])
            call = "run_passes_no_validate" if cm and cm.group(1) else "run_passes"
            # Arguments after the list, up to the end of the call statement. The phase argument
            # is the first `Some(MirPhase::..)` or bare `None` there (later arguments may follow).
            arg_start = max(call_at, m.end())
            stmt_end = text.find(");", arg_start)
            tail = text[arg_start: stmt_end if stmt_end != -1 else arg_start + 400]
            pm_ = re.search(r"Some\(\s*MirPhase::[A-Za-z]+\(\s*[A-Za-z]+::[A-Za-z]+\s*\)\s*\)|\bNone\b", tail)
            phase = "".join(pm_.group(0).split()) if pm_ else "<not found>"
        fn = None
        for fm in re.finditer(r"^(?:pub(?:\([a-z]+\))? )?fn (\w+)", text[:m.start()], re.M):
            fn = fm.group(1)
        lists.append({"file": rel, "enclosing_fn": fn, "first_line": entries[0]["line"],
                      "pass_manager_call": call, "phase_change_argument": phase,
                      "entries": entries})
    return lists


def parse_policies(rel: str, text: str):
    out = []
    lines = text.split("\n")
    impl_re = re.compile(r"\s*impl(?:<[^>]*>)?\s+(?:crate::)?(MirPass|MirLint)<'[a-z_]+>\s+for\s+([A-Za-z_][A-Za-z0-9_<>',\s]*?)\s*(\{|where|$)")
    cur = None
    i = 0
    while i < len(lines):
        m = impl_re.match(lines[i])
        if m:
            cur = {"trait": m.group(1), "type": re.sub(r"<.*", "", m.group(2).strip()),
                   "impl_line": i + 1, "file": rel, "methods": {}}
            out.append(cur)
        fm = re.match(r"\s*fn (policy|is_enabled|is_required|can_be_overridden)\(", lines[i])
        if fm and cur is not None:
            depth, j, started = 0, i, False
            while j < len(lines):
                depth += lines[j].count("{") - lines[j].count("}")
                started = started or "{" in lines[j]
                if started and depth == 0:
                    break
                j += 1
            body = lines[i + 1:j]
            cur["methods"][fm.group(1)] = {
                "lines": [i + 1, j + 1],
                "code": " ".join(strip_line_comment(l).strip() for l in body
                                 if strip_line_comment(l).strip()),
                "comment": " ".join(l.strip().lstrip("/ ").strip() for l in body
                                    if l.strip().startswith("//")),
            }
            i = j
        i += 1
    return out


def classify(methods: dict, wrapper):
    """Pattern-match the policy text. Purely syntactic; the `code` field is the ground truth."""
    c = {"kind": None, "min_mir_opt_level": None, "other_conditions": None}
    if "policy" in methods:
        code = methods["policy"]["code"]
        if code == "PassPolicy::Required":
            c["kind"] = "Required"
        else:
            m = re.fullmatch(r"PassPolicy::optional\((.*)\)", code, re.S)
            cond = m.group(1).strip().rstrip(",").strip() if m else None
            c["kind"] = "Optional"
            if cond == "true":
                c["default"] = "on at every MIR opt level"
            elif cond == "false":
                c["default"] = "off"
            elif cond is not None:
                lv = re.search(r"mir_opt_level\(\) >= (\d+)", cond)
                if lv:
                    c["min_mir_opt_level"] = int(lv.group(1))
                rest = re.sub(r"ctx\.mir_opt_level\(\) >= \d+\s*(&&)?\s*", "", cond).strip()
                c["other_conditions"] = rest or None
                c["default"] = "conditional"
            else:
                c["default"] = "see code"
                lv = [int(x) for x in re.findall(r"mir_opt_level\(\)[^=]*?(\d+)", code)]
    elif "is_required" in methods:
        req = methods["is_required"]["code"]
        c["kind"] = "is_required=" + req
        en = methods.get("is_enabled", {}).get("code")
        if en:
            lv = re.search(r"mir_opt_level\(\) >= (\d+)", en)
            if lv:
                c["min_mir_opt_level"] = int(lv.group(1))
            rest = re.sub(r"sess\.mir_opt_level\(\) >= \d+\s*(&&)?\s*", "", en).strip()
            c["other_conditions"] = rest or None
            c["default"] = "conditional"
        else:
            c["default"] = "on at every MIR opt level (default `is_enabled`)"
    if wrapper == "o1":
        c["min_mir_opt_level"] = max(1, c["min_mir_opt_level"] or 0)
        c["wrapper_note"] = "wrapped in WithMinOptLevel(1, _)"
    if wrapper == "Lint":
        c["wrapper_note"] = "MirLint behind the `Lint` adapter (cannot mutate the body)"
    return c


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--root", required=True, help="directory containing compiler/rustc_mir_transform/src")
    ap.add_argument("--fetch", metavar="SHA", default=None)
    ap.add_argument("--commit", default=None, help="label recorded in the output (40-hex commit)")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    if args.fetch:
        fetch(args.fetch, args.root)
    src = os.path.join(args.root, CRATE)
    files = []
    for dp, _dn, fn in os.walk(src):
        for f in fn:
            if f.endswith(".rs"):
                files.append(os.path.relpath(os.path.join(dp, f), src))
    files.sort()
    texts = {rel: read(os.path.join(src, rel)) for rel in files}
    declared = parse_declared(texts["lib.rs"])

    policies = []
    for rel in files:
        policies.extend(parse_policies(rel, texts[rel]))
    by_type = {}
    for p in policies:
        by_type.setdefault(p["type"], p)

    lists = []
    for rel in files:
        lists.extend(parse_lists(rel, texts[rel], declared))
    for lst in lists:
        for e in lst["entries"]:
            p = by_type.get(e["type"])
            if e.get("local_var"):
                # e.g. `let promote_pass = promote_consts::PromoteTemps::default();`
                vm = re.search(r"let %s\s*=\s*(\w+)::(\w+)" % re.escape(e["type"]), texts[lst["file"]])
                if vm:
                    e.update({"module": vm.group(1), "type": vm.group(2), "local_var": e["type"]})
                    p = by_type.get(e["type"])
            if p is None:
                e["policy"] = None
                continue
            if p["trait"] == "MirLint":
                e["policy"] = {"file": "pass_manager.rs", "via": "Lint<T> adapter",
                               **{k: v for k, v in by_type.get("Lint", {"methods": {}})["methods"].items()}}
                e["classification"] = classify(by_type.get("Lint", {"methods": {}})["methods"], "Lint")
            else:
                e["policy"] = {"file": p["file"], **p["methods"]}
                e["classification"] = classify(p["methods"], e["wrapper"])

    # Independent cross-check of the list parser. Count, per file, the lines that consist of
    # exactly one pass reference (a different, much simpler pattern than the list parser uses).
    # Every such line must be the line of some parsed entry; otherwise a list was missed.
    cross_check = {}
    for rel in files:
        nc = blank_line_comments(texts[rel])
        # `&[` ... matching `]` regions, by plain bracket-depth counting
        regions = []
        for om in re.finditer(r"&\[", nc):
            depth, k = 0, om.end() - 1
            while k < len(nc):
                if nc[k] == "[":
                    depth += 1
                elif nc[k] == "]":
                    depth -= 1
                    if depth == 0:
                        break
                k += 1
            regions.append((line_of(nc, om.start()), line_of(nc, k)))
        in_region = lambda ln: any(a <= ln <= b for a, b in regions)
        solo_lines = {ln for ln in (line_of(nc, m.start() + (len(m.group(0)) - len(m.group(0).lstrip())))
                                    for m in SOLO_ENTRY_LINE_RE.finditer(nc)) if in_region(ln)}
        parsed_lines = {e["line"] for l in lists if l["file"] == rel for e in l["entries"]}
        missed = sorted(solo_lines - parsed_lines)
        if solo_lines or parsed_lines:
            cross_check[rel] = {"solo_entry_lines": len(solo_lines),
                                "parsed_entries": sum(len(l["entries"]) for l in lists
                                                      if l["file"] == rel),
                                "solo_entry_lines_not_parsed": missed}
    unparsed = sorted(f"{l['file']}:{e['line']} {e['expr']}" for l in lists for e in l["entries"]
                      if e.get("unparsed"))
    if unparsed:
        print("ERROR: pass-list entries with an unrecognized shape: " + json.dumps(unparsed),
              file=sys.stderr)
        return 3
    missed_total = sum(len(v["solo_entry_lines_not_parsed"]) for v in cross_check.values())
    if missed_total:
        print(f"ERROR: list parser missed {missed_total} pass-reference line(s): "
              + json.dumps({k: v["solo_entry_lines_not_parsed"] for k, v in cross_check.items()
                            if v["solo_entry_lines_not_parsed"]}), file=sys.stderr)
        return 3

    # census
    census = []
    for d in declared:
        names = [(d["type"], v) for v in d["variants"]] or [(d["type"], None)]
        for ty, var in names:
            where = [f"{l['file']}:{e['line']}" for l in lists for e in l["entries"]
                     if e["type"] == ty and (var is None or e["variant"] == var)]
            census.append({"module": d["module"], "pass": ty + (f"::{var}" if var else ""),
                           "scheduled_at": where})
    undeclared = sorted({f"{l['file']}:{e['line']} {e['expr']}" for l in lists for e in l["entries"]
                         if e.get("undeclared")})

    doc = {
        "schema": "rustc-mir-pass-pipeline/1",
        "commit": args.commit or args.fetch,
        "crate_path": CRATE,
        "file_count": len(files),
        "sha256": {rel: hashlib.sha256(texts[rel].encode("utf-8")).hexdigest()
                   for rel in ("lib.rs", "pass_manager.rs", "add_call_guards.rs",
                               "elaborate_box_derefs.rs", "remove_unneeded_drops.rs",
                               "multiple_return_terminators.rs", "deref_separator.rs",
                               "erase_deref_temps.rs", "shim.rs", "validate.rs") if rel in texts},
        "line_counts": {rel: texts[rel].count("\n") + (0 if texts[rel].endswith("\n") else 1)
                        for rel in ("lib.rs", "add_call_guards.rs", "elaborate_box_derefs.rs",
                                    "remove_unneeded_drops.rs", "multiple_return_terminators.rs")
                        if rel in texts},
        "declared": declared,
        "lists": lists,
        "census": census,
        "list_parser_cross_check": cross_check,
        "summary": {
            "declared_pass_names": len(census),
            "declared_never_scheduled_in_a_pass_list": sorted(c["pass"] for c in census
                                                              if not c["scheduled_at"]),
            "entries_in_lib_rs_lists": sum(len(l["entries"]) for l in lists if l["file"] == "lib.rs"),
            "entries_in_other_files": sum(len(l["entries"]) for l in lists if l["file"] != "lib.rs"),
            "entries_referring_to_undeclared_names": undeclared,
        },
    }
    text = json.dumps(doc, indent=1, sort_keys=True)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
