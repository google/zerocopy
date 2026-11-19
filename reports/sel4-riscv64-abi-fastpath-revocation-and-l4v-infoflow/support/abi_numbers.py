#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Enumerate seL4 syscall numbers and invocation labels for RISC-V 64.

Re-implements only the numbering rules of the upstream generators:

* `libsel4/tools/syscall_header_gen.py` (`map_syscalls_neg`): syscalls listed
  in `libsel4/include/api/syscall.xml` are numbered -1, -2, ... in document
  order, API block (`api-master` or `api-mcs`) first, then the `debug` block.
* `libsel4/tools/invocation_header_gen.py`: `enum invocation_label` starts at
  `InvalidInvocation = 0`, then one enumerator per `<method id=...>` of
  `libsel4/include/interfaces/object-api.xml` in document order (an
  enumerator guarded by a false `<condition>` is omitted), then
  `nInvocationLabels`; the sel4_arch XML continues from `nInvocationLabels`
  and the arch XML continues from `nSeL4ArchInvocationLabels`.

Usage:
    abi_numbers.py <seL4 tree> [--define CONFIG_X ...]

`--define` names the config variables considered true (default: none, i.e.
non-MCS, non-SMP, no debug/benchmark/hardware-debug API).
"""
import sys
import xml.dom.minidom as minidom
from pathlib import Path


def cond_true(nodes, defines) -> bool:
    """Evaluate a <condition> element list (config/and/or/not) against defines."""
    def ev(n):
        if n.nodeType != n.ELEMENT_NODE:
            return None
        kids = [k for k in (ev(c) for c in n.childNodes) if k is not None]
        if n.tagName == "config":
            return n.getAttribute("var") in defines
        if n.tagName == "not":
            return not kids[0]
        if n.tagName == "and":
            return all(kids)
        if n.tagName == "or":
            return any(kids)
        if n.tagName == "condition":
            return all(kids) if kids else True
        raise SystemExit(f"unknown condition tag {n.tagName}")
    return all(ev(n) for n in nodes)


def syscalls(root: Path, defines):
    doc = minidom.parse(str(root / "libsel4/include/api/syscall.xml"))
    tag = "api-mcs" if "CONFIG_KERNEL_MCS" in defines else "api-master"
    n = -1
    rows = []
    for block, kind in ((doc.getElementsByTagName(tag)[0], "api"),
                        (doc.getElementsByTagName("debug")[0], "debug")):
        for cfg in block.getElementsByTagName("config"):
            live = cond_true(cfg.getElementsByTagName("condition"), defines)
            for sc in cfg.getElementsByTagName("syscall"):
                # Every listed syscall consumes a number whether or not its
                # config block is compiled in: the generator assigns explicit
                # values from one running counter over all blocks and only
                # wraps the enumerators in `#if <condition>`.
                rows.append((n, sc.getAttribute("name"), kind, live))
                n -= 1
    return rows


def labels(root: Path, defines):
    out = []
    n = 1  # InvalidInvocation = 0
    for rel, layer in (
        ("libsel4/include/interfaces/object-api.xml", "generic"),
        ("libsel4/sel4_arch_include/riscv64/interfaces/object-api-sel4-arch.xml", "sel4_arch"),
        ("libsel4/arch_include/riscv/interfaces/object-api-arch.xml", "arch"),
    ):
        doc = minidom.parse(str(root / rel))
        seen = set()
        for meth in doc.getElementsByTagName("method"):
            conds = meth.getElementsByTagName("condition")
            uid = meth.getAttribute("id") + "|" + "".join(c.toxml() for c in conds)
            if uid in seen:
                continue
            seen.add(uid)
            if not cond_true(conds, defines):
                continue
            iface = meth.parentNode.getAttribute("name")
            out.append((n, meth.getAttribute("id"), layer, iface, meth.getAttribute("name")))
            n += 1
        out.append((n, {"generic": "nInvocationLabels",
                        "sel4_arch": "nSeL4ArchInvocationLabels",
                        "arch": "nArchInvocationLabels"}[layer], layer, "", "(count)"))
    return out


def main():
    root = Path(sys.argv[1])
    defines = set()
    args = sys.argv[2:]
    while args:
        if args[0] == "--define":
            defines.add(args[1])
            args = args[2:]
        else:
            raise SystemExit(__doc__)
    print(f"defines: {sorted(defines) or '(none)'}")
    print("== syscall numbers (value passed in a7)")
    for n, name, kind, live in syscalls(root, defines):
        print(f"  {n:4d}  Sys{name:<34s} {kind:5s} {'' if live else '(config block disabled)'}")
    print("== invocation labels (label field of seL4_MessageInfo)")
    for n, ident, layer, iface, name in labels(root, defines):
        print(f"  {n:3d}  {ident:<32s} {layer:9s} {iface}{'_' if iface else ''}{name}")


if __name__ == "__main__":
    main()
