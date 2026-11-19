#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compute bit layouts of seL4 bitfield (`.bf`) blocks for RV64 (non-MCS, non-SMP).

This is an independent re-implementation of the *layout rule only* of
seL4's `tools/bitfield_gen.py` (`Block.checks`: fields are allocated from the
top of the block downwards in declaration order; `field_ptr(align) f n` is
`padding n - canonical_size + align` followed by `field_high f canonical_size -
align`).  It does not run the upstream generator (which needs the `ply`
package) and does not generate accessors.

Usage:
    bf_layout.py <seL4 tree> [--define NAME ...]

Reads, from the given seL4 source tree:
    include/arch/riscv/arch/64/mode/object/structures.bf   (includes structures_64.bf)
    libsel4/mode_include/64/sel4/shared_types.bf
and prints, per block, `word[index] bits [hi:lo] kind name`.
Word index 0 is `words[0]` of the generated C struct.
"""
import re
import sys
from pathlib import Path

WORD = 64


def preprocess(path: Path, root: Path, defines: dict, seen=None) -> list:
    """Tiny cpp subset: #include <...> (only .bf files we know), #ifdef,
    #ifndef, #if (NAME == N), #else, #endif, #error (only if live)."""
    out = []
    stack = []  # list of [parent_live, this_branch_live]
    live = True
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("--", 1)[0].rstrip()
        s = line.strip()
        if s.startswith("#"):
            d = s[1:].strip()
            if d.startswith("ifdef"):
                name = d.split()[1]
                stack.append([live, name in defines])
            elif d.startswith("ifndef"):
                name = d.split()[1]
                stack.append([live, name not in defines])
            elif d.startswith("if"):
                m = re.match(r"if\s*\(?\s*(\w+)\s*(==|>|<=|<|>=)\s*(\d+)\s*\)?", d)
                if not m:
                    raise SystemExit(f"unsupported directive in {path}: {s}")
                lhs = int(defines.get(m.group(1), 0))
                rhs = int(m.group(3))
                ok = {"==": lhs == rhs, ">": lhs > rhs, "<": lhs < rhs,
                      "<=": lhs <= rhs, ">=": lhs >= rhs}[m.group(2)]
                stack.append([live, ok])
            elif d.startswith("else"):
                stack[-1][1] = not stack[-1][1]
            elif d.startswith("endif"):
                stack.pop()
            elif d.startswith("error"):
                if live:
                    raise SystemExit(f"#error reached in {path}: {s}")
            elif d.startswith("include"):
                if live:
                    inc = re.search(r"<([^>]+)>", d).group(1)
                    cand = {
                        "object/structures_64.bf": root / "include/object/structures_64.bf",
                    }.get(inc)
                    if cand is not None:
                        out.extend(preprocess(cand, root, defines))
                    # config.h and shared_types.bf includes are not needed here
            else:
                raise SystemExit(f"unsupported directive in {path}: {s}")
            live = all(p and b for p, b in stack) if stack else True
            continue
        if live and s:
            out.append(s)
    return out


def ev(expr: str, canonical: int) -> int:
    expr = expr.replace("word_size", str(WORD)).replace("canonical_size", str(canonical))
    if not re.fullmatch(r"[0-9+\-*/% ()]+", expr):
        raise SystemExit(f"bad size expression: {expr!r}")
    return int(eval(expr))  # arithmetic only, validated above


def parse(lines: list):
    canonical = WORD
    blocks = {}
    unions = {}
    i = 0
    while i < len(lines):
        s = lines[i]
        m = re.match(r"base\s+(\d+)(?:\((\d+)\s*,\s*([01])\))?", s)
        if m:
            canonical = int(m.group(2)) if m.group(2) else int(m.group(1))
            i += 1
            continue
        m = re.match(r"block\s+(\w+)", s)
        if m:
            name = m.group(1)
            while "{" not in lines[i]:
                i += 1
            i += 1
            fields = []  # (name|None, size, kind)
            while not lines[i].startswith("}"):
                t = lines[i]
                fm = re.match(r"field_ptr(?:\((\d+)\))?\s+(\w+)\s+(.+)", t)
                if fm:
                    align = int(fm.group(1) or 0)
                    size = ev(fm.group(3), canonical)
                    fields.append((None, size - canonical + align, "padding"))
                    fields.append((fm.group(2), canonical - align, f"field_high(ptr,align={align})"))
                elif t.startswith("field_high"):
                    _, fname, expr = t.split(None, 2)
                    fields.append((fname, ev(expr, canonical), "field_high"))
                elif t.startswith("field"):
                    _, fname, expr = t.split(None, 2)
                    fields.append((fname, ev(expr, canonical), "field"))
                elif t.startswith("padding"):
                    fields.append((None, ev(t.split(None, 1)[1], canonical), "padding"))
                else:
                    raise SystemExit(f"unparsed line in block {name}: {t!r}")
                i += 1
            blocks[name] = (fields, canonical)
            i += 1
            continue
        m = re.match(r"tagged_union\s+(\w+)\s+(\w+)", s)
        if m:
            uname = m.group(1)
            tags = []
            i += 1
            while not lines[i].startswith("}"):
                tm = re.match(r"tag\s+(\w+)\s+(\d+)", lines[i])
                if tm:
                    tags.append((tm.group(1), int(tm.group(2))))
                i += 1
            unions[uname] = (m.group(2), tags)
            i += 1
            continue
        i += 1
    return blocks, unions


def layout(fields):
    total = sum(sz for _, sz, _ in fields)
    assert total % WORD == 0, total
    off = total
    rows = []
    for name, sz, kind in fields:
        off -= sz
        if name is None or sz == 0:
            continue
        w, lo = divmod(off, WORD)
        assert lo + sz <= WORD, (name, off, sz)
        rows.append((w, lo + sz - 1, lo, kind, name))
    return total // WORD, rows


def main():
    root = Path(sys.argv[1])
    defines = {"CONFIG_PT_LEVELS": 3}
    args = sys.argv[2:]
    while args:
        if args[0] == "--define":
            defines[args[1]] = 1
            args = args[2:]
        else:
            raise SystemExit("usage: bf_layout.py <seL4 tree> [--define NAME ...]")
    kernel = preprocess(root / "include/arch/riscv/arch/64/mode/object/structures.bf", root, defines)
    shared = preprocess(root / "libsel4/mode_include/64/sel4/shared_types.bf", root, defines)
    for title, lines, wanted in (
        ("libsel4/mode_include/64/sel4/shared_types.bf", shared, None),
        ("include/arch/riscv/arch/64/mode/object/structures.bf (+ include/object/structures_64.bf)",
         kernel,
         ["null_cap", "untyped_cap", "endpoint_cap", "notification_cap", "reply_cap",
          "cnode_cap", "thread_cap", "irq_control_cap", "irq_handler_cap", "zombie_cap",
          "domain_cap", "frame_cap", "page_table_cap", "asid_control_cap", "asid_pool_cap",
          "endpoint", "notification", "mdb_node", "thread_state", "pte", "satp"]),
    ):
        blocks, unions = parse(lines)
        print(f"== {title}")
        for uname, (tagname, tags) in unions.items():
            if uname == "cap":
                print(f"tagged_union {uname} (tag field {tagname}): " +
                      ", ".join(f"{n}={v}" for n, v in sorted(tags, key=lambda t: t[1])))
        for name in (wanted or list(blocks)):
            fields, canonical = blocks[name]
            nwords, rows = layout(fields)
            print(f"block {name}: {nwords} word(s), canonical_size={canonical}")
            for w, hi, lo, kind, fname in rows:
                extra = ""
                if kind.startswith("field_high"):
                    extra = f"  (holds value bits [{canonical - 1}:{canonical - (hi - lo + 1)}])"
                print(f"  words[{w}] [{hi:2d}:{lo:2d}] {kind:28s} {fname}{extra}")
        print()


if __name__ == "__main__":
    main()
