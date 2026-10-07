#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check compiled generated proofs, including attributes injected by other macros.

The __kani_contract_ name prefix is reserved for zerocopy-kani-macros. Ordinary
handwritten caller harnesses may use verified stubs; generated contract proofs
must execute implementations, without replacement stubs or expected panics.
"""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile


ATTRIBUTE_KEYS = {
    "kind", "should_panic", "solver", "unwind_value", "stubs", "verified_stubs",
}


def validate_generated(metadata):
    proofs = []
    for harness in metadata["proof_harnesses"] + metadata["test_harnesses"]:
        if not any(part.startswith("__kani_contract_") for part in
                   harness["pretty_name"].split("::")):
            continue
        attrs = harness["attributes"]
        if set(attrs) != ATTRIBUTE_KEYS:
            raise ValueError("unexpected generated proof metadata schema")
        kind = attrs["kind"]
        if not isinstance(kind, dict) or set(kind) != {"ProofForContract"}:
            raise ValueError("generated proof must verify a function contract")
        if attrs["should_panic"] or attrs["stubs"] or attrs["verified_stubs"]:
            raise ValueError("substitutions and expected panics are forbidden in generated proofs")
        if harness.get("contract", {}).get("recursion_tracker") is not None:
            raise ValueError("recursive contract assumptions are forbidden in generated proofs")
        if "{closure#" in harness["pretty_name"]:
            raise ValueError("generated proof was nested inside a contracted function")
        proofs.append(harness["pretty_name"])
    if len(proofs) != len(set(proofs)):
        raise ValueError("duplicate generated contract proof")
    # The compiler resolves contract targets. Its canonical function-to-proof
    # mapping catches missing discovery and a proof bound to a different
    # same-named function, even when every discovered proof verifies.
    linked = set()
    for function in metadata["contracted_functions"]:
        if (set(function) != {"function", "file", "harnesses"}
                or not isinstance(function["function"], str)
                or not isinstance(function["file"], str)
                or not isinstance(function["harnesses"], list)):
            raise ValueError("unexpected contracted-function metadata schema")
        names = function["harnesses"]
        if not names:
            raise ValueError(f"contract has no discovered generated proof: {function['function']}")
        for name in names:
            if name not in proofs or name in linked:
                raise ValueError("contract maps to a missing, ungenerated or multiply linked proof")
            linked.add(name)
    if linked != set(proofs):
        raise ValueError("generated proof is not linked to a contracted function")
    return proofs


def _json_payload(output, key):
    records = json.loads(output)
    if not isinstance(records, list):
        raise ValueError("unexpected GOTO JSON schema")
    values = [record[key] for record in records if isinstance(record, dict) and key in record]
    if len(values) != 1:
        raise ValueError("unexpected GOTO JSON schema")
    return values[0]


def validate_checking_graph(functions, graph, harness):
    """Reject nested Kani SimpleCheck dispatch, including other type instances.

    Kani 0.60 selects Check by DefId. Every invocation of that definition assumes
    its requires clauses, even a recursive call or another concrete instance.
    Its MIR transform stores mode 2 in the generated scalar kani_contract_mode
    local. Check closure locals can disappear for zero-sized closures, whereas
    this scalar marker is retained. Interpret the pinned unoptimized GOTO schema
    and conservatively include every edge, including function-pointer candidates.
    """
    u8 = {"id": "unsignedbv", "namedSub": {"width": {"id": "8"}}}
    false = {"id": "constant", "namedSub": {"type": {"id": "bool"}, "value": {"id": "false"}}}
    if not isinstance(functions, list):
        raise ValueError("unexpected GOTO function schema")
    bodies = {}
    checks = set()
    for function in functions:
        name = function["name"]
        if not isinstance(name, str) or name in bodies:
            raise ValueError("unexpected GOTO function schema")
        bodies[name] = function
        instructions = function.get("instructions", [])
        declared = set()
        modes = []
        for instruction in instructions:
            kind = instruction["instructionId"]
            if kind not in {"DECL", "ASSIGN"}:
                continue
            operands = instruction["operands"]
            lhs = operands[0]
            if lhs["id"] != "symbol":
                continue
            identifier = lhs["namedSub"]["identifier"]["id"]
            if not identifier.endswith("::kani_contract_mode"):
                continue
            if not identifier.startswith(name + "::") or lhs["namedSub"]["type"] != u8:
                raise ValueError("unexpected Kani contract mode marker")
            if kind == "DECL":
                declared.add(identifier)
                continue
            if len(operands) != 2:
                raise ValueError("unexpected Kani contract mode assignment")
            rhs = operands[1]
            if rhs["id"] != "constant" or rhs["namedSub"]["type"] != u8:
                raise ValueError("unexpected Kani contract mode assignment")
            mode = rhs["namedSub"]["value"]["id"]
            if mode not in {"0", "2", "4"}:
                raise ValueError("replacement or recursive contract checking is forbidden")
            modes.append((identifier, mode))
        if declared and not modes:
            # Unused generated closures are cleared to Unreachable, retaining
            # their declarations. An active dispatcher must retain its marker.
            if (any(i["instructionId"] == "FUNCTION_CALL" for i in instructions)
                    or not any(i["instructionId"] == "ASSUME" and i["guard"] == false
                               for i in instructions)):
                raise ValueError("missing Kani contract mode assignment")
        if modes:
            if len(modes) != 1 or declared != {modes[0][0]}:
                raise ValueError("unexpected Kani contract mode assignments")
            if modes[0][1] == "2":
                checks.add(name)
    entry = harness["mangled_name"]
    if entry not in bodies or not bodies[entry]["isBodyAvailable"]:
        raise ValueError("missing generated proof GOTO body")
    edges = {}
    messages = ("Reading GOTO program from ", "Function Pointer Removal",
                "Virtual function removal", "Cleaning inline assembler statements")
    for line in graph.splitlines():
        if " -> " in line:
            caller, callee = line.split(" -> ")
            if caller not in bodies or callee not in bodies:
                raise ValueError("unexpected GOTO call graph symbol")
            edges.setdefault(caller, set()).add(callee)
        elif line and not line.startswith(messages):
            raise ValueError("unexpected GOTO call graph schema")

    def reachable(starts, stop_at_check=False):
        seen = set()
        pending = list(starts)
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            if not (stop_at_check and current in checks):
                pending.extend(edges.get(current, ()))
        return seen

    first = reachable([entry], stop_at_check=True) & checks
    if len(first) != 1:
        raise ValueError("generated proof must reach exactly one initial checking dispatcher")
    checking = next(iter(first))
    below = reachable(edges.get(checking, ()))
    if below & checks:
        raise ValueError(f"nested contract checking is forbidden: {harness['pretty_name']}")
    wrapper = harness["contract"]["contracted_function_name"]
    if wrapper not in below or not bodies[wrapper]["isBodyAvailable"]:
        raise ValueError("selected contract wrapper is not reached by its checking dispatcher")


def validate_generated_models(metadata):
    """Validate metadata and each fresh only-codegen linked GOTO model."""
    proofs = validate_generated(metadata)
    # Kani's driver locates these bundled tools relative to its installation.
    # The GitHub action need only expose cargo-kani on PATH.
    directory = Path.home() / ".kani" / "kani-0.60.0" / "bin"
    goto_cc = shutil.which("goto-cc") or str(directory / "goto-cc")
    goto_instrument = shutil.which("goto-instrument") or str(directory / "goto-instrument")
    version = subprocess.check_output([goto_instrument, "--version"], text=True).strip()
    if version != "6.4.1 (cbmc-6.4.1)":
        raise ValueError("review the GOTO checking schema before changing CBMC")
    for harness in metadata["proof_harnesses"] + metadata["test_harnesses"]:
        if harness["pretty_name"] not in proofs:
            continue
        source = Path(harness["goto_file"])
        if not source.name.endswith(".symtab.out"):
            raise ValueError("unexpected generated proof GOTO filename")
        linked = source.with_name(source.name.removesuffix(".symtab.out") + ".out")
        if not linked.is_file():
            raise ValueError("missing fresh linked generated proof GOTO model")
        with tempfile.TemporaryDirectory(prefix="kani-check-graph-") as temporary:
            model = Path(temporary) / "proof.goto"
            subprocess.check_output([goto_cc, str(linked), "--function", harness["mangled_name"],
                                     "-o", str(model)], text=True)
            functions = _json_payload(subprocess.check_output(
                [goto_instrument, "--show-goto-functions", "--json-ui", str(model)], text=True),
                "functions")
            graph = subprocess.check_output([goto_instrument, "--call-graph", str(model)], text=True)
            try:
                validate_checking_graph(functions, graph, harness)
            except (KeyError, IndexError, TypeError) as error:
                raise ValueError("unexpected GOTO checking schema") from error
    return proofs
