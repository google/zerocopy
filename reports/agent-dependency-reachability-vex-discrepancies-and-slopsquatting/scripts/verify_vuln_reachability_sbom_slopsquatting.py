#!/usr/bin/env python3
"""Deterministic verification probe for vulnerability reachability, SBOM/VEX discrepancies, and slopsquatting.

Covers five primary-source verification suites (`Basis: source + derived`, with
normative specification checks under OSV Schema and OpenVEX v0.2.0):
  1. Probe 1 (`golang/vuln@ef4cb2f7`, `golang/tools@70e48cd7`, `google/osv-scanner@925d1b4c`):
     Two-pass `CHA -> VTA -> VTA` call-graph reachability (`utils.go:63-89`,
     `slicing.go:14-46`) using per-parameter/receiver `typePropGraph` propagation
     (`vta/vta.go:79-165`, `vta/graph.go:312-352, 660-698`), `reflect` & generic
     library entry-point false negatives (`vta.go:74-75`, `entries.go:17-46`),
     stripped-binary symbol blowup (`binary.go:107-114`), non-antisymmetric
     `moreSpecific` OpenVEX comparator defect (`internal/openvex/handler.go:83-128, 216-227`),
     and `osv-scanner` `scalibrenricher/govulncheck` unimported-module justification
     conflation (`govulncheck.go:117-139`).
  2. Probe 2 (`google/osv-scanner@925d1b4c`, `rustsec/rustsec@9284e112`,
     `ossf/osv-schema@e34af15e`):
     `cleanRustFunctionSymbols` `<[\\w,]+>` const-generic array / nested-generic /
     lifetime regex failures (`rust.go:288-304`), `functionsFromDWARF`
     `DW_TAG_inlined_subroutine` omission (`rust.go:154-174`), multi-rule Cargo `.d`
     depfile split error (`rust.go:275-280`), `go.go:104-137` missing version-range
     filter in `vulnHasImportsField`, `rustsec` `quitters` panic-string fallback
     (`binary_deps.rs:24-55`), and normative OSV `SEMVER` vs. `GIT` `fixed`/`limit`
     sibling-branch evaluation (`docs/schema.md:1144-1148, 1269-1398`).
  3. Probe 3 (`anchore/syft@9ad9aa5e`, `aquasecurity/trivy@edf9f5c1`):
     `requirements.txt` default unpinned/range omission vs. `GuessUnpinnedRequirements` /
     `useMinVersion` floor/ceiling divergence (`parse_requirements.go:129-250`,
     `pip/parse.go:39-116, 167-170`), `Trivy` `PyProject.MainDeps` extras inflation and
     Poetry shadowing (`pyproject.go:45-60`), and `Syft` CycloneDX vs. SPDX
     relationship edge loss (`cyclonedxhelpers/to_format_model.go:235-293`,
     `spdxhelpers/to_format_model.go:58-69, 170-218, 698-748`).
  4. Probe 4 (`openvex/go-vex@42a83ee2`, `openvex/spec@93139bd2`,
     `aquasecurity/trivy@edf9f5c1`):
     `SortStatements` + `Document.Matches` ASCII `GHSA-*`/`GO-*`/`RUSTSEC-*` vs.
     `CVE-*` cross-alias revocation bypass (`statement.go:142-173`, `vex.go:173-244`,
     `trivy/pkg/vex/openvex.go:60-87`), `Trivy` `reachRoot` disconnected-SBOM orphan
     failure across OpenVEX, CSAF `default_component_of`, and CycloneDX BOM-Links
     (`vex.go:178-219`, `csaf.go:36-115`, `cyclonedx.go:25-74`), and the two-sided
     Wild-SBOM impossibility vs. three-valued `{reachable, unreachable, unknown}`
     gating (`Zieba-Kozarzewski 2026`).
  5. Probe 5 (`Spracks/PackageHallucination@bd3031cc` + `Spracklen 2025`,
     `Churilov 2026`, `Djire 2026`):
     Caller-list aliasing in `refine_package_list` (`custom_parse_javascript.py:15`)
     and in-place `new_list.remove(item)` loop-skip false positives shared with
     `extract_npm_packages` (`L111-136`) and `extract_npm_install` (`L163-188`),
     `len(i) > 2` 1-2 char package erasure (`custom_parse_python.py:4-7`,
     `custom_parse_javascript.py:198-201`), separation of pure-PyPI stdlib omission
     (`Djire et al. ASE '26 §5.1 Table 2`) from `Spracks/PackageHallucination`'s
     `pypi_package_names.csv:500315-500565` 22-module stdlib gap (`package_detection.py:9-17, 63-93`),
     and an explicit `[illustrative analytical model]` (`Basis: derived`) of single-agent,
     5-of-5 cross-model consensus, and registry-snapshot/lockfile defenses over the
     53 registrable universal hallucinations.

Constraints: Python 3.10+ stdlib only, zero network calls, strict temporary
directory cleanup (`with tempfile.TemporaryDirectory():`), zero host paths in
stdout, deterministic under PYTHONHASHSEED=1 and PYTHONHASHSEED=2 in < 2.0s.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
import re
import sys
import tempfile
from typing import Callable


# ============================================================================
# PROBE 1: govulncheck CHA -> VTA -> VTA, Soundness Gaps, & OpenVEX Comparator
# ============================================================================


@dataclass(frozen=True)
class SSAFunc:
    name: str
    pkg: str
    exported: bool = False
    is_generic_template: bool = False
    implements_iface: str | None = None
    direct_calls: tuple[str, ...] = ()
    # `(param_idx, iface_name)`: dynamic interface method call on `local{fn:param<idx>}`
    iface_calls: tuple[tuple[int, str], ...] = ()
    # `param_idx`: dynamic higher-order call `fn_param()` on `local{fn:param<idx>}`
    calls_func_params: tuple[int, ...] = ()
    # `*ssa.Function` instruction operands visited by `forwardSlice` (`slicing.go:33-40`)
    func_val_refs: tuple[str, ...] = ()
    # `(callee, callee_param_idx, concrete_type)` passed at call sites (`graph.go:660-698`)
    type_arg_flows: tuple[tuple[str, int, str], ...] = ()
    # `(callee, callee_param_idx, func_name)` passed at call sites (`graph.go:660-698`)
    func_arg_flows: tuple[tuple[str, int, str], ...] = ()
    # `(src_param_idx, callee, dst_param_idx)` parameter-to-parameter flow (`graph.go:696`)
    param_arg_flows: tuple[tuple[int, str, int], ...] = ()
    reflect_target: str | None = None  # opaque to static CHA/VTA (`vta.go:74-75`)


def govulncheck_entry_points(
    funcs: dict[str, SSAFunc], top_pkgs: tuple[str, ...]
) -> list[str]:
    """Port of `golang/vuln/internal/vulncheck/entries.go:19-56`.

    Note lines 17-18 TODO(https://go.dev/issue/57221): parameterized generic
    functions (`TypeParams != nil`, no concrete instantiations in library scan)
    have `len(memberFuncs) == 0` and are omitted from `entryPoints`.
    """
    entries: list[str] = []
    for pkg in top_pkgs:
        pkg_funcs = [f for f in funcs.values() if f.pkg == pkg]
        if pkg == "main":
            for f in sorted(pkg_funcs, key=lambda x: x.name):
                short = f.name.split(".")[-1]
                if (
                    short == "main"
                    or short == "init"
                    or short.startswith("init#")
                ) and not f.is_generic_template:
                    entries.append(f.name)
        else:
            for f in sorted(pkg_funcs, key=lambda x: x.name):
                if f.is_generic_template:
                    continue
                short = f.name.split(".")[-1]
                if short == "init" or f.exported:
                    entries.append(f.name)
    return entries


def build_cha_callgraph(funcs: dict[str, SSAFunc]) -> dict[str, set[str]]:
    """Over-approximating Class Hierarchy Analysis (`cha.CallGraph(prog)`)."""
    cg: dict[str, set[str]] = {k: set() for k in funcs}
    iface_impls: dict[str, list[str]] = {}
    all_func_vals = [
        k for k in sorted(funcs) if "Closure" in k or "Sink" in k
    ]
    for f in funcs.values():
        if f.implements_iface:
            iface_impls.setdefault(f.implements_iface, []).append(f.name)
    for f in funcs.values():
        for callee in f.direct_calls:
            cg[f.name].add(callee)
        for _param_idx, iface in f.iface_calls:
            for impl in iface_impls.get(iface, ()):
                cg[f.name].add(impl)
        if f.calls_func_params:
            # CHA resolves indirect function-typed parameters to all signature-compatible functions.
            for cand in all_func_vals:
                cg[f.name].add(cand)
    return cg


def forward_slice(
    sources: set[str], cg: dict[str, set[str]], funcs: dict[str, SSAFunc]
) -> set[str]:
    """Port of `golang/vuln/internal/vulncheck/slicing.go:14-46`.

    Collects transitive callees in `cg` PLUS `*ssa.Function` instruction operands.
    """
    seen: set[str] = set()

    def visit(fn_name: str) -> None:
        if fn_name in seen:
            return
        seen.add(fn_name)
        for callee in sorted(cg.get(fn_name, ())):
            visit(callee)
        for op_fn in funcs[fn_name].func_val_refs:
            visit(op_fn)

    for s in sorted(sources):
        visit(s)
    return seen


def vta_callgraph(
    fslice: set[str], initial_cg: dict[str, set[str]], funcs: dict[str, SSAFunc]
) -> dict[str, set[str]]:
    """Port of `vta.CallGraph(fslice, initial)` (`vta.go:79-165`, `graph.go:312-352, 660-698`).

    Constructs the per-SSA-parameter/receiver `typePropGraph` (`b.visit(funcs)` over
    `fslice` using `siteCallees(call, callees)` from `initial_cg`), propagates
    `propType`s (`("type", T)` and `("func", f)`) along directed `addArgumentFlows`
    inflow edges, and resolves interface and higher-order calls strictly from each
    call site's own `local{val: c.Common().Value}` node intersected with `initial_cg`.
    """
    prop_types: dict[str, set[tuple[str, str]]] = {}
    inflow_edges: dict[str, set[str]] = {}

    # Phase 1: `typePropGraph(funcs, callees)` (`graph.go:312-352, 660-698`)
    for fn_name in sorted(fslice):
        fn = funcs[fn_name]
        active_callees = initial_cg.get(fn_name, set()) & fslice
        for callee, dst_idx, concrete_type in fn.type_arg_flows:
            if callee in active_callees:
                node = f"{callee}:param{dst_idx}"
                prop_types.setdefault(node, set()).add(("type", concrete_type))
        for callee, dst_idx, passed_fn in fn.func_arg_flows:
            if callee in active_callees and passed_fn in fslice:
                node = f"{callee}:param{dst_idx}"
                prop_types.setdefault(node, set()).add(("func", passed_fn))
        for src_idx, callee, dst_idx in fn.param_arg_flows:
            if callee in active_callees:
                src_node = f"{fn_name}:param{src_idx}"
                dst_node = f"{callee}:param{dst_idx}"
                inflow_edges.setdefault(src_node, set()).add(dst_node)

    # Phase 2: `propagate(vtaG, canon)` (`vta.go:82`)
    changed = True
    while changed:
        changed = False
        for src_node in sorted(inflow_edges):
            src_vals = prop_types.get(src_node)
            if not src_vals:
                continue
            for dst_node in sorted(inflow_edges[src_node]):
                dst_vals = prop_types.setdefault(dst_node, set())
                before = len(dst_vals)
                dst_vals.update(src_vals)
                if len(dst_vals) > before:
                    changed = True

    # Phase 3: `constructor.construct` + `resolves(call)` (`vta.go:97-165`)
    refined: dict[str, set[str]] = {fn_name: set() for fn_name in fslice}
    for fn_name in sorted(fslice):
        fn = funcs[fn_name]
        site_callees = initial_cg.get(fn_name, set()) & fslice
        for callee in fn.direct_calls:
            if callee in site_callees:
                refined[fn_name].add(callee)
        for param_idx, iface_name in fn.iface_calls:
            node = f"{fn_name}:param{param_idx}"
            flowing_types = {
                val for kind, val in prop_types.get(node, set()) if kind == "type"
            }
            for cand in sorted(site_callees):
                if funcs[cand].implements_iface == iface_name:
                    recv_type = cand.split(".")[0]
                    if recv_type in flowing_types:
                        refined[fn_name].add(cand)
        for param_idx in fn.calls_func_params:
            node = f"{fn_name}:param{param_idx}"
            flowing_funcs = {
                val for kind, val in prop_types.get(node, set()) if kind == "func"
            }
            for cand in sorted(site_callees):
                if cand in flowing_funcs:
                    refined[fn_name].add(cand)
    return refined


@dataclass(frozen=True)
class TraceFrame:
    module: str
    package: str = ""
    function: str = ""


@dataclass(frozen=True)
class Finding:
    osv: str
    trace: tuple[TraceFrame, ...]


def found_at_level(f: Finding) -> int:
    """Port of `golang/vuln/internal/openvex/handler.go:70-79` (`required=0, imported=1, called=2`)."""
    fr = f.trace[0]
    if fr.function != "":
        return 2  # called
    if fr.package != "":
        return 1  # imported
    return 0  # required


def more_specific_buggy(f1: Finding, f2: Finding) -> int:
    """Exact port of `golang/vuln/internal/openvex/handler.go:83-109`."""
    if len(f1.trace) > 1 and len(f2.trace) > 1:
        return 0
    if len(f1.trace) > 1:
        return -1
    if len(f2.trace) > 1:
        return 1
    fr1, fr2 = f1.trace[0], f2.trace[0]
    if fr1.function != "" and fr2.function == "":
        return -1
    if fr1.function == "" and fr2.function != "":
        return 1
    if fr1.package != "" and fr2.package == "":
        return -1
    if fr1.package == "" and fr2.package != "":
        return -1  # BUG at handler.go:106: returns -1 instead of +1!
    return 0


def more_specific_fixed(f1: Finding, f2: Finding) -> int:
    """Antisymmetric fix changing `handler.go:106` from `-1` to `+1`."""
    if len(f1.trace) > 1 and len(f2.trace) > 1:
        return 0
    if len(f1.trace) > 1:
        return -1
    if len(f2.trace) > 1:
        return 1
    fr1, fr2 = f1.trace[0], f2.trace[0]
    if fr1.function != "" and fr2.function == "":
        return -1
    if fr1.function == "" and fr2.function != "":
        return 1
    if fr1.package != "" and fr2.package == "":
        return -1
    if fr1.package == "" and fr2.package != "":
        return 1
    return 0


def openvex_consume_findings(
    stream: list[Finding],
    comparator: Callable[[Finding, Finding], int],
    scan_level: int = 2,
) -> tuple[str, str]:
    """Port of `handler.Finding` + `statements` (`handler.go:111-128, 216-227`)."""
    fs: list[Finding] = []
    for f in stream:
        if not fs:
            fs = [f]
        else:
            ms = comparator(f, fs[0])
            if ms == -1:
                fs = [f]
            elif ms == 0:
                fs.append(f)
    f_level = found_at_level(fs[0])
    if f_level >= scan_level:
        return ("affected", "")
    justification = "vulnerable_code_not_present"
    if f_level == 1:
        justification = "vulnerable_code_not_in_execute_path"
    return ("not_affected", justification)


def osv_scalibr_govulncheck_signal(findings: list[Finding]) -> str | None:
    """Port of `google/osv-scanner/internal/scalibrenricher/govulncheck/source/govulncheck.go:125-138`."""
    if not findings:
        return None
    is_reachable = any(
        len(f.trace) > 0 and f.trace[0].function != "" for f in findings
    )
    if not is_reachable:
        return "vulnerable_code_not_in_execute_path"
    return None


def run_probe_1_govulncheck_vta_and_openvex() -> dict[str, object]:
    # Program modelling (`golang/vuln/internal/vulncheck/utils.go:63-89`, `vta/graph.go:312-352, 660-698`):
    # - `main.main` calls `main.decodeInput(SafeJSON{})` and `main.runHook(main.safeSink)`,
    #   and also holds an unpassed function reference `main.unusedClosure` in a local variable
    #   (verifying VTA per-parameter `typePropGraph` precision vs RTA global function sets).
    # - `DeadXML.Decode` is an uninstantiated `Decoder` implementation that calls `vuln_xml.Parse`
    #   AND calls `main.runHook(main.evilSink)` (`evilSink -> vuln_yaml.Unmarshal`).
    #   In VTA Pass 1 (`fslice_0` from CHA), `DeadXML` is uninstantiated so `decodeInput -> DeadXML.Decode`
    #   (`GO-XML`) is pruned, BUT `DeadXML.Decode` is still visited in `fslice_0` (`graph.go:339-343`)
    #   and its static call `main.runHook(main.evilSink)` injects `func(main.evilSink) -> local{main.runHook:param0}`
    #   (`graph.go:696`), retaining `runHook -> evilSink` (`vta_pass1_flagged = ['GO-TAR', 'GO-YAML']`).
    #   Re-slicing `fslice_1` on `vta_1` evicts `DeadXML.Decode`, so VTA Pass 2 (`vta_2`) eliminates
    #   the `evilSink` parameter inflow and converges to `vta_pass2_flagged = ['GO-TAR']`!
    # - Reflection call in `main.main` (`reflect_target="reflSvc.Trigger" -> vuln_refl.Exec`) missed by VTA.
    # - Generic exported function `libpkg.ParseGeneric[T]` (`is_generic_template=True` -> `vuln_toml.Decode`)
    #   ignored by `entryPoints` (`entries.go:17-46`, Go issue #57221).
    funcs = {
        "main.main": SSAFunc(
            name="main.main",
            pkg="main",
            direct_calls=("main.decodeInput", "main.runHook"),
            func_val_refs=("main.safeSink", "main.unusedClosure"),
            type_arg_flows=(("main.decodeInput", 0, "SafeJSON"),),
            func_arg_flows=(("main.runHook", 0, "main.safeSink"),),
            reflect_target="reflSvc.Trigger",
        ),
        "main.decodeInput": SSAFunc(
            name="main.decodeInput",
            pkg="main",
            iface_calls=((0, "Decoder"),),
        ),
        "main.runHook": SSAFunc(
            name="main.runHook",
            pkg="main",
            calls_func_params=(0,),
        ),
        "main.safeSink": SSAFunc(name="main.safeSink", pkg="main"),
        "main.unusedClosure": SSAFunc(name="main.unusedClosure", pkg="main"),
        "main.evilSink": SSAFunc(
            name="main.evilSink",
            pkg="main",
            direct_calls=("vuln_yaml.Unmarshal",),
        ),
        "SafeJSON.Decode": SSAFunc(
            name="SafeJSON.Decode",
            pkg="codec",
            exported=True,
            implements_iface="Decoder",
            direct_calls=("vuln_tar.Extract",),
        ),
        "DeadXML.Decode": SSAFunc(
            name="DeadXML.Decode",
            pkg="codec",
            exported=True,
            implements_iface="Decoder",
            direct_calls=("vuln_xml.Parse", "main.runHook"),
            func_val_refs=("main.evilSink",),
            func_arg_flows=(("main.runHook", 0, "main.evilSink"),),
        ),
        "reflSvc.Trigger": SSAFunc(
            name="reflSvc.Trigger",
            pkg="refl",
            exported=True,
            direct_calls=("vuln_refl.Exec",),
        ),
        "libpkg.ParseGeneric[T]": SSAFunc(
            name="libpkg.ParseGeneric[T]",
            pkg="libpkg",
            exported=True,
            is_generic_template=True,
            direct_calls=("vuln_toml.Decode",),
        ),
        "vuln_tar.Extract": SSAFunc(name="vuln_tar.Extract", pkg="vuln_tar", exported=True),
        "vuln_xml.Parse": SSAFunc(name="vuln_xml.Parse", pkg="vuln_xml", exported=True),
        "vuln_yaml.Unmarshal": SSAFunc(
            name="vuln_yaml.Unmarshal", pkg="vuln_yaml", exported=True
        ),
        "vuln_refl.Exec": SSAFunc(name="vuln_refl.Exec", pkg="vuln_refl", exported=True),
        "vuln_toml.Decode": SSAFunc(name="vuln_toml.Decode", pkg="vuln_toml", exported=True),
    }
    vuln_sinks = {
        "GO-TAR": "vuln_tar.Extract",
        "GO-XML": "vuln_xml.Parse",
        "GO-YAML": "vuln_yaml.Unmarshal",
        "GO-REFL": "vuln_refl.Exec",
        "GO-TOML": "vuln_toml.Decode",
        "GO-MODONLY": "vuln_unused_mod.Danger",  # in go.mod only, never imported/linked
    }

    main_entries = set(govulncheck_entry_points(funcs, ("main",)))
    lib_entries = set(govulncheck_entry_points(funcs, ("libpkg",)))

    cha_cg = build_cha_callgraph(funcs)
    fslice_0 = forward_slice(main_entries, cha_cg, funcs)
    vta_1 = vta_callgraph(fslice_0, cha_cg, funcs)
    fslice_1 = forward_slice(main_entries, vta_1, funcs)
    vta_2 = vta_callgraph(fslice_1, vta_1, funcs)

    # Confirm VTA per-parameter isolation: `main.unusedClosure` is in `fslice_0` and `cha_cg["main.runHook"]`,
    # yet pruned immediately in `vta_1["main.runHook"]` because it never flows into `main.runHook:param0`.
    vta_unpassed_closure_pruned_pass1 = (
        "main.unusedClosure" in fslice_0
        and "main.unusedClosure" in cha_cg["main.runHook"]
        and "main.unusedClosure" not in vta_1["main.runHook"]
    )

    def reachable_sinks(entries: set[str], cg: dict[str, set[str]]) -> list[str]:
        visited: set[str] = set()
        stack = sorted(entries)
        while stack:
            cur = stack.pop()
            if cur in visited:
                continue
            visited.add(cur)
            for nxt in sorted(cg.get(cur, ())):
                if nxt not in visited:
                    stack.append(nxt)
        return sorted(v_id for v_id, sym in vuln_sinks.items() if sym in visited)

    cha_flagged = reachable_sinks(main_entries, cha_cg)
    vta1_flagged = reachable_sinks(main_entries, vta_1)
    vta2_flagged = reachable_sinks(main_entries, vta_2)
    lib_vta_flagged = reachable_sinks(lib_entries, vta_2)

    # Dynamic/ground-truth reachable for `main`: SafeJSON.Decode -> GO-TAR and reflection -> GO-REFL.
    ground_truth_main = ["GO-REFL", "GO-TAR"]

    # Binary mode (`binary.go:47, 107-114`):
    # Unstripped binary contains all symbols compiled into linked packages (no call graph).
    unstripped_symtab = {
        "vuln_tar.Extract",
        "vuln_xml.Parse",
        "vuln_yaml.Unmarshal",
        "vuln_refl.Exec",
    }
    bin_unstripped = sorted(
        v_id for v_id, sym in vuln_sinks.items() if sym in unstripped_symtab
    )
    # Stripped binary (`len(bin.PkgSymbols) == 0`): `allKnownVulnerableSymbols(affVulns)`!
    bin_stripped = sorted(vuln_sinks.keys())

    # OpenVEX `moreSpecific` antisymmetry audit across (required, imported, called):
    f_req = Finding("GO-2026-0001", (TraceFrame(module="example.com/mod"),))
    f_imp = Finding(
        "GO-2026-0001", (TraceFrame(module="example.com/mod", package="example.com/mod/p"),)
    )
    f_cal = Finding(
        "GO-2026-0001",
        (TraceFrame(module="example.com/mod", package="example.com/mod/p", function="Vuln"),),
    )
    sample_findings = [("required", f_req), ("imported", f_imp), ("called", f_cal)]
    antisymmetry_violations: list[str] = []
    for n1, x in sample_findings:
        for n2, y in sample_findings:
            c_xy = more_specific_buggy(x, y)
            c_yx = more_specific_buggy(y, x)
            if c_xy != -c_yx:
                antisymmetry_violations.append(f"({n1},{n2}):{c_xy}_vs_{c_yx}")

    # Normal emission order (`source.go:83,94`: required -> imported) vs reversed/replayed order:
    normal_order = openvex_consume_findings([f_req, f_imp], more_specific_buggy)
    reverse_buggy = openvex_consume_findings([f_imp, f_req], more_specific_buggy)
    reverse_fixed = openvex_consume_findings([f_imp, f_req], more_specific_fixed)
    scalibr_unimported_signal = osv_scalibr_govulncheck_signal([f_req])

    return {
        "cha_flagged": cha_flagged,
        "vta_pass1_flagged": vta1_flagged,
        "vta_pass2_flagged": vta2_flagged,
        "vta_unpassed_closure_pruned_pass1": vta_unpassed_closure_pruned_pass1,
        "ground_truth_main": ground_truth_main,
        "vta_missed_reflection": sorted(set(ground_truth_main) - set(vta2_flagged)),
        "generic_lib_entries_count": len(lib_entries),
        "generic_lib_flagged": lib_vta_flagged,
        "binary_unstripped_flagged": bin_unstripped,
        "binary_stripped_flagged": bin_stripped,
        "antisymmetry_violations": antisymmetry_violations,
        "openvex_req_then_imp": normal_order[1],
        "openvex_imp_then_req_buggy": reverse_buggy[1],
        "openvex_imp_then_req_fixed": reverse_fixed[1],
        "scalibr_unimported_mod_signal": scalibr_unimported_signal,
    }


# ============================================================================
# PROBE 2: OSV-Scanner Rust DWARF/Regex, Depfile, & OSV SEMVER/GIT Evaluation
# ============================================================================

ANTI_GENERIC_RE = re.compile(r"<[\w,]+>")
ANTI_TRAIT_IMPL_RE = re.compile(r"<(.*) as .*>")


def clean_rust_function_symbols_upstream(val: str) -> str:
    """Exact port of `google/osv-scanner/internal/sourceanalysis/rust.go:288-304`."""
    val = ANTI_GENERIC_RE.sub("", val)
    val = ANTI_TRAIT_IMPL_RE.sub(r"\1", val)
    return val


def clean_rust_function_symbols_balanced(val: str) -> str:
    """Balanced `<...>` generic/trait cleaner handling const generics, nested `<>`, & lifetimes."""
    if val.startswith("<"):
        depth = 0
        as_split = -1
        close_idx = -1
        i = 0
        while i < len(val):
            ch = val[i]
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
                if depth == 0:
                    close_idx = i
                    break
            elif depth == 1 and val.startswith(" as ", i):
                as_split = i
            i += 1
        if close_idx != -1 and as_split != -1:
            val = val[1:as_split] + val[close_idx + 1 :]

    out: list[str] = []
    depth = 0
    for ch in val:
        if ch == "<":
            depth += 1
        elif ch == ">" and depth > 0:
            depth -= 1
        elif depth == 0:
            out.append(ch)
    return "".join(out)


@dataclass(frozen=True)
class DwarfEntry:
    tag: str  # "DW_TAG_subprogram" or "DW_TAG_inlined_subroutine"
    demangled_linkage_name: str


def functions_from_dwarf_upstream(entries: list[DwarfEntry]) -> set[str]:
    """Port of `functionsFromDWARF` (`rust.go:154-174`)."""
    output: set[str] = set()
    for entry in entries:
        if entry.tag != "DW_TAG_subprogram":
            continue
        output.add(clean_rust_function_symbols_upstream(entry.demangled_linkage_name))
    return output


def parse_cargo_depfile_upstream(depfile_text: str) -> tuple[str | None, str | None]:
    """Exact port of `rustBuildSource` `.d` file split (`rust.go:275-280`)."""
    file_split = depfile_text.split(": ")
    if len(file_split) != 2:
        return (None, "file path contains ': ', which is unsupported")
    return (file_split[0], None)


def parse_semver_key(ver: str) -> tuple[int, int, int, tuple[int, tuple[tuple[int, object], ...]]]:
    """Strict SemVer 2.0.0 §11 precedence key (`0` sentinel sorts before everything)."""
    if ver == "0":
        return (-1, -1, -1, (0, ()))
    core_build = ver.split("+", 1)[0]
    if "-" in core_build:
        core, prerelease = core_build.split("-", 1)
        pre_parts: list[tuple[int, object]] = []
        for ident in prerelease.split("."):
            if ident.isdigit():
                pre_parts.append((0, int(ident)))
            else:
                pre_parts.append((1, ident))
        pre_key: tuple[int, tuple[tuple[int, object], ...]] = (0, tuple(pre_parts))
    else:
        core = core_build
        pre_key = (1, ())
    major, minor, patch = (int(x) for x in core.split("."))
    return (major, minor, patch, pre_key)


def osv_included_in_semver_range(ver: str, events: list[dict[str, str]]) -> bool:
    """Normative OSV `IncludedInRanges` + `BeforeLimits` for `SEMVER` (`schema.md:1286-1314`)."""
    v_key = parse_semver_key(ver)
    limits = [e["limit"] for e in events if "limit" in e]
    if limits and not any(
        lim == "*" or v_key < parse_semver_key(lim) for lim in limits
    ):
        return False

    def evt_ver(
        e: dict[str, str],
    ) -> tuple[int, int, int, tuple[int, tuple[tuple[int, object], ...]]]:
        val = next(iter(e.values()))
        return parse_semver_key(val)

    vulnerable = False
    for evt in sorted((e for e in events if "limit" not in e), key=evt_ver):
        if "introduced" in evt and v_key >= parse_semver_key(evt["introduced"]):
            vulnerable = True
        elif "fixed" in evt and v_key >= parse_semver_key(evt["fixed"]):
            vulnerable = False
        elif "last_affected" in evt and v_key > parse_semver_key(evt["last_affected"]):
            vulnerable = False
    return vulnerable


def git_ancestors(parents: dict[str, tuple[str, ...]], commit: str) -> set[str]:
    """Reflexive-transitive ancestors (`u <= v` iff `u` is `v` or an ancestor of `v`)."""
    seen: set[str] = set()
    stack = [commit]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        for p in parents.get(cur, ()):
            stack.append(p)
    return seen


def osv_included_in_git_range(
    commit: str,
    parents: dict[str, tuple[str, ...]],
    events: list[dict[str, str]],
) -> bool:
    """Normative OSV `GIT` commit-ancestry evaluation (`docs/schema.md:1144-1148, 1286-1398`)."""
    limits = [e["limit"] for e in events if "limit" in e]
    if limits:
        in_limit = False
        for lim in limits:
            if lim == "*":
                in_limit = True
                break
            lim_anc = git_ancestors(parents, lim)
            if commit != lim and commit in lim_anc:
                in_limit = True
                break
        if not in_limit:
            return False

    anc = git_ancestors(parents, commit)
    introduced = [e["introduced"] for e in events if "introduced" in e]
    fixed = [e["fixed"] for e in events if "fixed" in e]
    last_aff = [e["last_affected"] for e in events if "last_affected" in e]

    is_intro = any(i == "0" or i in anc for i in introduced)
    if not is_intro:
        return False
    if any(f in anc for f in fixed):
        return False
    if last_aff and not any(commit in git_ancestors(parents, la) for la in last_aff):
        return False
    return True


def vuln_has_imports_field_upstream(
    affected_entries: list[dict[str, object]], pkg_name: str, pkg_version: str
) -> bool:
    """Exact port of `google/osv-scanner/internal/sourceanalysis/go.go:104-126` (note L110 TODO)."""
    _ = pkg_version  # Ignored upstream (`TODO: Compare versions...` at go.go:110)!
    for aff in affected_entries:
        if aff.get("package_name") != pkg_name:
            continue
        eco = aff.get("ecosystem_specific")
        if isinstance(eco, dict) and "imports" in eco:
            return True
    return False


def run_probe_2_osv_scanner_rust_dwarf_and_osv_ranges(tmp_dir: str) -> dict[str, object]:
    demangled_cases = [
        ("smallvec::SmallVec<u8>::grow", "smallvec::SmallVec::grow"),
        ("smallvec::SmallVec<[u8; 4]>::grow", "smallvec::SmallVec::grow"),
        ("mycrate::Parser<alloc::vec::Vec<u8>>::parse", "mycrate::Parser::parse"),
        ("http::HeaderMap<&'static str>::insert", "http::HeaderMap::insert"),
        (
            "<libflate::gzip::MultiDecoder as std::io::Read>::read",
            "libflate::gzip::MultiDecoder::read",
        ),
        (
            "<smallvec::SmallVec<[u8; 4]> as core::ops::Drop>::drop",
            "smallvec::SmallVec::drop",
        ),
    ]
    upstream_matches = 0
    balanced_matches = 0
    failed_symbols: list[str] = []
    for raw_sym, advisory_sym in demangled_cases:
        cleaned_up = clean_rust_function_symbols_upstream(raw_sym)
        cleaned_bal = clean_rust_function_symbols_balanced(raw_sym)
        if cleaned_up == advisory_sym:
            upstream_matches += 1
        else:
            failed_symbols.append(f"{raw_sym} -> {cleaned_up}")
        if cleaned_bal == advisory_sym:
            balanced_matches += 1

    # DWARF LTO + opt-level=3 inlining vs dead #[no_mangle] / rlib export:
    dwarf_entries = [
        DwarfEntry("DW_TAG_subprogram", "app::main"),
        DwarfEntry("DW_TAG_inlined_subroutine", "byteorder::read_u32_vuln"),
        DwarfEntry("DW_TAG_subprogram", "uncalled_ffi::exported_vuln_fn"),
    ]
    dwarf_calls = functions_from_dwarf_upstream(dwarf_entries)
    inlined_detected = "byteorder::read_u32_vuln" in dwarf_calls
    dead_export_flagged = "uncalled_ffi::exported_vuln_fn" in dwarf_calls

    # Multi-rule Cargo `.d` depfile written in temp directory (`rust.go:275-280`):
    dep_path = os.path.join(tmp_dir, "app.d")
    with open(dep_path, "w", encoding="utf-8") as fh:
        fh.write(
            "target/release/app: src/main.rs src/lib.rs\n"
            "src/main.rs: src/include.rs\n"
        )
    with open(dep_path, "r", encoding="utf-8") as fh:
        dep_bin, dep_err = parse_cargo_depfile_upstream(fh.read())

    # OSV GIT commit graph (`ossf/osv-schema/docs/schema.md:1364-1397`):
    # root -> X -> A -> B -> C -> Y (main); A -> D -> E (release-1.x branch); X -> F (feature branch)
    commits = ("root", "X", "A", "B", "C", "Y", "D", "E", "F")
    parents: dict[str, tuple[str, ...]] = {
        "root": (),
        "X": ("root",),
        "A": ("X",),
        "B": ("A",),
        "C": ("B",),
        "Y": ("C",),
        "D": ("A",),
        "E": ("D",),
        "F": ("X",),
    }
    git_fixed_hits = [
        c
        for c in commits
        if osv_included_in_git_range(
            c, parents, [{"introduced": "X"}, {"fixed": "Y"}]
        )
    ]
    git_limit_hits = [
        c
        for c in commits
        if osv_included_in_git_range(
            c, parents, [{"introduced": "X"}, {"limit": "Y"}]
        )
    ]
    git_limit_missed = [c for c in git_fixed_hits if c not in git_limit_hits]

    # OSV SEMVER `fixed` vs `last_affected` on pre-release `1.0.2-rc.1 < 1.0.2`:
    semver_fixed_rc = osv_included_in_semver_range(
        "1.0.2-rc.1", [{"introduced": "1.0.0"}, {"fixed": "1.0.2"}]
    )
    semver_last_aff_rc = osv_included_in_semver_range(
        "1.0.1", [{"introduced": "1.0.0"}, {"last_affected": "1.0.1"}]
    )
    semver_last_aff_backport_fn = osv_included_in_semver_range(
        "1.0.2-rc.1", [{"introduced": "1.0.0"}, {"last_affected": "1.0.1"}]
    )

    # `go.go:104-137` missing version-range check:
    osv_multi_affected = [
        {"package_name": "example.com/lib", "range": "<2.0.0", "ecosystem_specific": {}},
        {
            "package_name": "example.com/lib",
            "range": ">=2.0.0,<2.1.0",
            "ecosystem_specific": {"imports": [{"path": "example.com/lib/v2/sub"}]},
        },
    ]
    v1_falsely_treated_as_symbol_annotated = vuln_has_imports_field_upstream(
        osv_multi_affected, "example.com/lib", "1.4.0"
    )

    return {
        "rust_regex_upstream_recall": f"{upstream_matches}/{len(demangled_cases)}",
        "rust_regex_balanced_recall": f"{balanced_matches}/{len(demangled_cases)}",
        "rust_regex_failed_count": len(failed_symbols),
        "dwarf_inlined_detected": inlined_detected,
        "dwarf_dead_export_flagged": dead_export_flagged,
        "cargo_depfile_multi_rule_err": dep_err is not None and dep_bin is None,
        "osv_git_fixed_affected": git_fixed_hits,
        "osv_git_limit_affected": git_limit_hits,
        "osv_git_limit_false_negatives": git_limit_missed,
        "osv_semver_prerelease_before_fix": semver_fixed_rc,
        "osv_semver_last_affected_ceiling_fn": (
            semver_last_aff_rc and not semver_last_aff_backport_fn
        ),
        "go_v1_false_imports_inheritance": v1_falsely_treated_as_symbol_annotated,
    }


# ============================================================================
# PROBE 3: Syft vs. Trivy Python Manifest Parsing & CycloneDX/SPDX Edge Loss
# ============================================================================


def syft_parse_pinned_version(constraint: str) -> str:
    """Exact port of `anchore/syft/.../python/parse_requirements.go:188-204`."""
    version = constraint.strip()
    if any(ch in version for ch in "*,<>") or "!=" in version:
        return ""
    for op in ("===", "=="):
        if version.startswith(op) and not version.startswith(op + "="):
            return version[len(op) :].strip()
    return ""


def _pep440_tuple(v: str) -> tuple[int, tuple[int, ...]] | None:
    v = v.strip()
    epoch = 0
    if "!" in v:
        ep_s, v = v.split("!", 1)
        if not ep_s.isdigit():
            return None
        epoch = int(ep_s)
    parts = v.split(".")
    nums: list[int] = []
    for p in parts:
        if not p.isdigit():
            return None
        nums.append(int(p))
    return (epoch, tuple(nums))


def _go_split_after(s: str, sep: str) -> list[str]:
    """Exact port of Go `strings.SplitAfter(s, sep)`."""
    if not sep:
        return list(s)
    chunks = s.split(sep)
    out = [c + sep for c in chunks[:-1]]
    out.append(chunks[-1])
    return out


def syft_guess_version(constraint: str) -> str:
    """Exact port of `anchore/syft/.../python/parse_requirements.go:206-250`.

    Note live upstream bug at lines 224-239: `strings.SplitAfter("==2.8.0", "=")`
    yields `["=", "=", "2.8.0"]`, so `parts[1]` is `"="`, which fails `pep440.Parse`
    at line 228 and skips the dead-code `strings.Cut(part, "==")` branch at line 237!
    """
    constraint = constraint.replace("*", "0")
    pinned = syft_parse_pinned_version(constraint)
    if pinned != "":
        return pinned
    constraints = constraint.split(",")
    filtered: set[str] = set()
    for part in constraints:
        if "!=" in part:
            _, excluded = part.split("!=", 1)
            filtered.add(excluded.strip())
    closest_str = ""
    closest_key: tuple[int, tuple[int, ...]] | None = None
    for part in constraints:
        parts = _go_split_after(part, "=")
        if len(parts) < 2:
            continue
        rhs_clean = parts[1].strip()
        parsed = _pep440_tuple(rhs_clean)
        if parsed is None or rhs_clean in filtered:
            continue
        if "==" in part:
            # Unreachable dead code in upstream Go (`parts[1]` contains trailing `=` whenever `==` is in `part`)!
            _, pinned_rhs = part.split("==", 1)
            return pinned_rhs.strip()
        if closest_key is None or parsed > closest_key:
            closest_key = parsed
            closest_str = rhs_clean
    return closest_str


def syft_parse_requirements_txt(text: str, guess_unpinned: bool) -> dict[str, str]:
    """Port of `anchore/syft/.../python/parse_requirements.go:129-186`."""
    pkgs: dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        # Upstream parse_requirements.go:29,67-87,129-148 skips "-e" at L129 and regex-matches "git+https://..." as Name="git", VersionConstraint="", dropping it identically at L142-148 (`version == ""`).
        if not line or line.startswith(("git+", "http://", "https://", "-")):
            continue
        line = line.split(";", 1)[0].strip()
        m = re.match(r"^([A-Za-z0-9._-]+)(?:\[[^\]]*\])?(.*)$", line)
        if not m:
            continue
        name, constraint = m.group(1), m.group(2).strip()
        ver = syft_parse_pinned_version(constraint)
        if ver == "" and guess_unpinned:
            ver = syft_guess_version(constraint)
        if ver != "":
            pkgs[name] = ver
    return pkgs


def trivy_parse_requirements_txt(text: str, use_min_version: bool) -> dict[str, str]:
    """Exact port of `aquasecurity/trivy/pkg/dependency/parser/python/pip/parse.go:39-116`."""
    pkgs: dict[str, str] = {}
    operators = ("~=", ">=", "==") if use_min_version else ("==",)
    for raw in text.splitlines():
        line = raw.replace(" ", "").replace("\\", "")
        for marker in ("#", ";", "--"):
            line = line.split(marker, 1)[0]
        if "[" in line and "]" in line:
            s_idx, e_idx = line.index("["), line.index("]")
            line = line[:s_idx] + line[e_idx + 1 :]
        if not line:
            continue
        i = 0
        while i < len(line) and (line[i].isalnum() or line[i] in "._-"):
            i += 1
        name, specs = line[:i], line[i:]
        if not name or not specs:
            continue
        chosen_ver = ""
        for op in operators:
            for spec in specs.split(","):
                if spec.startswith(op):
                    chosen_ver = spec[len(op) :]
                    break
            if chosen_ver:
                break
        if not chosen_ver:
            continue
        if use_min_version and chosen_ver.endswith(".*"):
            chosen_ver = chosen_ver[:-1] + "0"
        # `go-pep440-version` `version.Parse` (`pip/parse.go:108, 167-170`) accepts PEP 440
        # epochs (`1!2.0.0`) while rejecting `=2024.2.2` left by `CutPrefix("===...", "==")`.
        if _pep440_tuple(chosen_ver) is None:
            continue
        pkgs[name] = chosen_ver
    return pkgs


def trivy_pyproject_main_deps(
    project_deps: list[str] | None,
    optional_deps: dict[str, list[str]] | None,
    poetry_deps: list[str] | None,
) -> list[str]:
    """Exact port of `aquasecurity/trivy/.../pyproject/pyproject.go:45-60`."""
    deps: set[str] = set()
    if project_deps is not None or optional_deps is not None:
        if project_deps is not None:
            deps.update(project_deps)
        if optional_deps is not None:
            for extra_list in optional_deps.values():
                deps.update(extra_list)
    elif poetry_deps is not None:
        deps.update(poetry_deps)
    return sorted(deps)


def syft_cyclonedx_keep_relationship(rel_type: str) -> bool:
    """Exact port of `syft/format/common/cyclonedxhelpers/to_format_model.go:235-242`."""
    return rel_type == "dependency-of"


def syft_spdx_keep_relationship(from_id: str, to_id: str, rel_type: str) -> bool:
    """Exact port of `syft/format/common/spdxhelpers/to_format_model.go:58-69, 698-748`."""
    valid_types = {
        "contains",
        "dependency-of",
        "ownership-by-file-overlap",
        "evident-by",
    }
    if rel_type not in valid_types:
        return False
    is_from_pkg = from_id.startswith("pkg:")
    is_file_contains_pkg = (
        from_id.startswith("file:")
        and to_id.startswith("pkg:")
        and rel_type == "contains"
    )
    return is_from_pkg or is_file_contains_pkg


def run_probe_3_syft_trivy_python_sbom_and_edges(tmp_dir: str) -> dict[str, object]:
    req_txt = "\n".join(
        [
            "urllib3==2.0.7",
            "packaging==1!2.0.0",
            "certifi===2024.2.2",
            "requests>=2.31.0",
            "cryptography~=42.0.0",
            "jinja2==3.1.*",
            "werkzeug>=2.0.0,<=2.2.2",
            "pyjwt==2.8.0,!=2.8.1",
            "pyyaml",
            "git+https://github.com/psf/black.git@24.4.2#egg=black",
        ]
    )
    req_file = os.path.join(tmp_dir, "requirements.txt")
    with open(req_file, "w", encoding="utf-8") as fh:
        fh.write(req_txt)
    with open(req_file, "r", encoding="utf-8") as fh:
        disk_req = fh.read()

    total_declared = 10
    syft_default = syft_parse_requirements_txt(disk_req, guess_unpinned=False)
    trivy_default = trivy_parse_requirements_txt(disk_req, use_min_version=False)
    syft_guess = syft_parse_requirements_txt(disk_req, guess_unpinned=True)
    trivy_min = trivy_parse_requirements_txt(disk_req, use_min_version=True)

    pep621_with_extras = trivy_pyproject_main_deps(
        project_deps=[" httpx ", "pydantic"],
        optional_deps={"dev": ["pytest", "mypy"], "docs": ["sphinx"]},
        poetry_deps=None,
    )
    pep621_with_extras = [d.strip() for d in pep621_with_extras]

    poetry_shadowed = trivy_pyproject_main_deps(
        project_deps=None,
        optional_deps={"docs": ["mkdocs"]},
        poetry_deps=["fastapi", "sqlalchemy", "uvicorn"],
    )

    syft_rels = [
        ("pkg:deb/debian/libc6", "pkg:deb/debian/bash", "dependency-of"),
        ("file:/app/bundle.tar", "pkg:pypi/torch@2.3.0", "contains"),
        (
            "pkg:pypi/torch@2.3.0",
            "file:/usr/lib/python3/site-packages/torch/__init__.py",
            "evident-by",
        ),
        ("pkg:deb/debian/python3", "pkg:pypi/pip@24.0", "ownership-by-file-overlap"),
    ]
    cdx_kept = [
        r
        for r in syft_rels
        if syft_cyclonedx_keep_relationship(r[2])
        and r[0].startswith("pkg:")
        and r[1].startswith("pkg:")
    ]
    spdx_kept = [
        r for r in syft_rels if syft_spdx_keep_relationship(r[0], r[1], r[2])
    ]

    return {
        "total_declared_reqs": total_declared,
        "syft_default_count": len(syft_default),
        "trivy_default_count": len(trivy_default),
        "default_omitted_count": total_declared - len(syft_default),
        "syft_guess_werkzeug": syft_guess.get("werkzeug"),
        "trivy_min_werkzeug": trivy_min.get("werkzeug"),
        "syft_guess_pyjwt_splitafter_bug": syft_guess.get("pyjwt"),
        "trivy_default_pyjwt": trivy_default.get("pyjwt"),
        "syft_default_certifi_triple_eq": syft_default.get("certifi"),
        "trivy_default_certifi_triple_eq": trivy_default.get("certifi"),
        "trivy_pep621_extras_leaked": sorted(
            set(pep621_with_extras) - {"httpx", "pydantic"}
        ),
        "trivy_poetry_deps_retained_when_optional_set": [
            d for d in poetry_shadowed if d in {"fastapi", "sqlalchemy", "uvicorn"}
        ],
        "syft_cdx_relationships_kept": f"{len(cdx_kept)}/{len(syft_rels)}",
        "syft_spdx_relationships_kept": f"{len(spdx_kept)}/{len(syft_rels)}",
    }


# ============================================================================
# PROBE 4: go-vex Cross-Alias Bug & Trivy reachRoot Orphan-SBOM Impossibility
# ============================================================================


@dataclass(frozen=True)
class VexStatement:
    vuln_name: str
    aliases: tuple[str, ...]
    timestamp: str
    products: tuple[str, ...]
    subcomponents: tuple[str, ...]
    status: str  # "not_affected", "affected", "fixed", "under_investigation"
    justification: str = ""
    impact_statement: str = ""
    action_statement: str = ""

    def validate(self) -> str | None:
        """Port of `openvex/go-vex/pkg/vex/statement.go:69-137`."""
        valid_statuses = {
            "not_affected",
            "affected",
            "fixed",
            "under_investigation",
        }
        if self.status not in valid_statuses:
            return "invalid_status"
        if self.status == "not_affected":
            if not self.justification and not self.impact_statement:
                return "missing_justification_or_impact"
            if self.action_statement:
                return "unexpected_action_statement"
        elif self.status == "affected":
            if self.justification or self.impact_statement:
                return "unexpected_justification_or_impact"
            if not self.action_statement:
                return "missing_action_statement"
        else:
            if self.justification or self.impact_statement or self.action_statement:
                return "unexpected_status_specific_field"
        return None

    def matches_vuln(self, vuln_id: str) -> bool:
        """Port of `openvex/go-vex/pkg/vex/vulnerability.go:32-47`."""
        return self.vuln_name == vuln_id or vuln_id in self.aliases

    def matches_product(self, product: str, sub_id: str) -> bool:
        """Port of `openvex/go-vex/pkg/vex/product.go:29-47`."""
        if product not in self.products:
            return False
        if not self.subcomponents or sub_id == "":
            return True
        return sub_id in self.subcomponents

    def matches(self, vuln_id: str, product: str, subcomponents: list[str]) -> bool:
        """Port of `openvex/go-vex/pkg/vex/statement.go:177-196`."""
        if not self.matches_vuln(vuln_id):
            return False
        if not subcomponents:
            return self.matches_product(product, "")
        return any(self.matches_product(product, sc) for sc in subcomponents)


def govex_sort_statements(
    stmts: list[VexStatement], doc_timestamp: str
) -> list[VexStatement]:
    """Exact port of `SortStatements` (`openvex/go-vex/pkg/vex/statement.go:142-173`).

    Sorts FIRST by `Vulnerability.Name` ASCII order, and ONLY SECOND by `Timestamp`!
    """
    return sorted(
        stmts,
        key=lambda s: (s.vuln_name, s.timestamp if s.timestamp else doc_timestamp),
    )


def govex_effective_statement(
    stmts: list[VexStatement], doc_timestamp: str, product: str, vuln_id: str
) -> VexStatement | None:
    """Exact port of `Document.EffectiveStatement` (`openvex/go-vex/pkg/vex/vex.go:173-209`)."""
    ordered = govex_sort_statements(stmts, doc_timestamp)
    newest: VexStatement | None = None
    newest_time = ""
    for s in ordered:
        if not s.matches(vuln_id, product, []):
            continue
        s_time = s.timestamp if s.timestamp else doc_timestamp
        if newest is None or not (s_time < newest_time):
            newest = s
            newest_time = s_time
    return newest


def govex_document_matches(
    stmts: list[VexStatement],
    doc_timestamp: str,
    vuln_id: str,
    product: str,
    subcomponents: list[str],
) -> list[VexStatement]:
    """Exact port of `Document.Matches` (`openvex/go-vex/pkg/vex/vex.go:227-244`)."""
    matches: list[VexStatement] = []
    for i in range(len(stmts) - 1, -1, -1):
        if stmts[i].matches(vuln_id, product, subcomponents):
            matches.append(stmts[i])
    return govex_sort_statements(matches, doc_timestamp)


def trivy_openvex_not_affected(
    stmts: list[VexStatement],
    doc_timestamp: str,
    vuln_id: str,
    product_purl: str,
    subcomponent_purl: str | None,
) -> bool:
    """Exact port of `Trivy` `OpenVEX.NotAffected` (`aquasecurity/trivy/pkg/vex/openvex.go:60-87`)."""
    sub_arg = [subcomponent_purl if subcomponent_purl else ""]
    matched = govex_document_matches(stmts, doc_timestamp, vuln_id, product_purl, sub_arg)
    if not matched:
        return False
    stmt = matched[-1]  # `stmt := stmts[len(stmts)-1]` at openvex.go:69!
    return stmt.status in ("not_affected", "fixed")


@dataclass(frozen=True)
class SBOMComponent:
    uid: str
    purl: str
    root: bool = False


def trivy_reach_root(
    leaf: SBOMComponent,
    components: dict[str, SBOMComponent],
    parents: dict[str, list[str]],
    not_affected_fn: Callable[[SBOMComponent, SBOMComponent | None], bool],
) -> bool:
    """Exact port of `reachRoot` (`aquasecurity/trivy/pkg/vex/vex.go:178-219`)."""
    if not_affected_fn(leaf, None):
        return False

    def dfs(c: SBOMComponent, visited: set[str]) -> bool:
        if not_affected_fn(c, leaf):
            return False
        if c.root:
            return True
        unvisited_parents = set(parents.get(c.uid, ())) - visited
        if len(unvisited_parents) == 0:
            # vex.go:195-199: Orphan component fail-safe returns True BEFORE reaching root!
            return True
        visited_next = set(visited)
        visited_next.add(c.uid)
        for p_uid in parents.get(c.uid, ()):
            if p_uid in visited_next:
                continue
            if dfs(components[p_uid], set(visited_next)):
                return True
        return False

    return dfs(leaf, set())


def run_probe_4_vex_alias_revocation_and_orphan_impossibility() -> dict[str, object]:
    root_purl = "pkg:oci/myapp@sha256:1111"
    leaf_purl = "pkg:golang/golang.org/x/net@0.17.0"
    doc_ts = "2026-01-01T00:00:00Z"

    stmt_t1_ghsa = VexStatement(
        vuln_name="GHSA-4374-p667-p6c8",
        aliases=("CVE-2023-45288", "GO-2024-2687"),
        timestamp="2026-01-10T00:00:00Z",
        products=(root_purl,),
        subcomponents=(leaf_purl,),
        status="not_affected",
        justification="vulnerable_code_not_in_execute_path",
    )
    stmt_t2_cve = VexStatement(
        vuln_name="CVE-2023-45288",
        aliases=("GHSA-4374-p667-p6c8", "GO-2024-2687"),
        timestamp="2026-02-20T00:00:00Z",
        products=(root_purl,),
        subcomponents=(leaf_purl,),
        status="affected",
        action_statement="Upgrade golang.org/x/net to v0.23.0; HTTP/2 CONTINUATION flood reachable.",
    )
    assert stmt_t1_ghsa.validate() is None and stmt_t2_cve.validate() is None

    stmts = [stmt_t1_ghsa, stmt_t2_cve]
    eff = govex_effective_statement(stmts, doc_ts, root_purl, "CVE-2023-45288")
    trivy_suppressed_revoked_cve = trivy_openvex_not_affected(
        stmts, doc_ts, "CVE-2023-45288", root_purl, leaf_purl
    )

    advisory_prefixes = ("GHSA-", "GO-", "RUSTSEC-", "PYSEC-", "OSV-", "SNYK-")
    prefixes_sorting_after_cve = [p for p in advisory_prefixes if p > "CVE-"]

    root_comp = SBOMComponent("root", root_purl, root=True)
    comps: dict[str, SBOMComponent] = {"root": root_comp}
    connected_parents: dict[str, list[str]] = {}
    degen_parents: dict[str, list[str]] = {}
    for idx in range(100):
        uid = f"pkg-{idx:02d}"
        p = f"pkg:pypi/dep-{idx:02d}@1.0.0"
        comps[uid] = SBOMComponent(uid, p, root=False)
        connected_parents[uid] = ["root"]
        if idx < 3:
            degen_parents[uid] = ["root"]
        else:
            degen_parents[uid] = []

    all_leaf_purls = tuple(comps[f"pkg-{i:02d}"].purl for i in range(100))
    vex_root_scoped = [
        VexStatement(
            vuln_name="CVE-2026-9999",
            aliases=(),
            timestamp="2026-03-01T00:00:00Z",
            products=(root_purl,),
            subcomponents=all_leaf_purls,
            status="not_affected",
            justification="vulnerable_code_not_in_execute_path",
        )
    ]

    def openvex_cb(prod: SBOMComponent, sub: SBOMComponent | None) -> bool:
        return trivy_openvex_not_affected(
            vex_root_scoped,
            doc_ts,
            "CVE-2026-9999",
            prod.purl,
            sub.purl if sub is not None else "",
        )

    def csaf_rel_cb(prod: SBOMComponent, sub: SBOMComponent | None) -> bool:
        if sub is None:
            return False
        return prod.purl == root_purl and sub.purl in all_leaf_purls

    def cdx_leaf_bomlink_cb(prod: SBOMComponent, _sub: SBOMComponent | None) -> bool:
        return prod.purl in all_leaf_purls

    def cdx_root_bomlink_cb(prod: SBOMComponent, _sub: SBOMComponent | None) -> bool:
        return prod.purl == root_purl

    conn_openvex_suppressed = sum(
        1
        for i in range(100)
        if not trivy_reach_root(comps[f"pkg-{i:02d}"], comps, connected_parents, openvex_cb)
    )
    degen_openvex_suppressed = sum(
        1
        for i in range(100)
        if not trivy_reach_root(comps[f"pkg-{i:02d}"], comps, degen_parents, openvex_cb)
    )
    degen_csaf_suppressed = sum(
        1
        for i in range(100)
        if not trivy_reach_root(comps[f"pkg-{i:02d}"], comps, degen_parents, csaf_rel_cb)
    )
    degen_cdx_leaf_suppressed = sum(
        1
        for i in range(100)
        if not trivy_reach_root(
            comps[f"pkg-{i:02d}"], comps, degen_parents, cdx_leaf_bomlink_cb
        )
    )
    degen_cdx_root_suppressed = sum(
        1
        for i in range(100)
        if not trivy_reach_root(
            comps[f"pkg-{i:02d}"], comps, degen_parents, cdx_root_bomlink_cb
        )
    )

    wild_no_edges = 40756
    wild_degen = 6796
    wild_connected = 29540
    wild_parseable = wild_no_edges + wild_degen + wild_connected
    wild_non_connected_pct = round(
        100.0 * (wild_no_edges + wild_degen) / wild_parseable, 2
    )

    non_root_ids = [uid for uid, c in comps.items() if not c.root]
    orphans_in_degen = sum(1 for uid in non_root_ids if len(degen_parents[uid]) == 0)
    orphan_ratio = orphans_in_degen / len(non_root_ids)
    closed_world_kev_retained = sum(
        1 for uid in non_root_ids if len(degen_parents[uid]) > 0
    )
    open_world_kev_retained = sum(
        1
        for uid in non_root_ids
        if len(degen_parents[uid]) > 0 or orphan_ratio > 0.5
    )

    return {
        "govex_effective_stmt_status": eff.status if eff else None,
        "trivy_openvex_falsely_suppresses_revoked_cve": trivy_suppressed_revoked_cve,
        "prefixes_sorting_after_cve": f"{len(prefixes_sorting_after_cve)}/{len(advisory_prefixes)}",
        "connected_openvex_suppressed": f"{conn_openvex_suppressed}/100",
        "degen_97pct_orphan_openvex_suppressed": f"{degen_openvex_suppressed}/100",
        "degen_97pct_orphan_csaf_suppressed": f"{degen_csaf_suppressed}/100",
        "degen_97pct_orphan_cdx_root_suppressed": f"{degen_cdx_root_suppressed}/100",
        "degen_97pct_orphan_cdx_leaf_suppressed": f"{degen_cdx_leaf_suppressed}/100",
        "wild_sbom_parseable_total": wild_parseable,
        "wild_sbom_non_connected_pct": wild_non_connected_pct,
        "closed_world_kev_retained_on_degen": f"{closed_world_kev_retained}/100",
        "open_world_three_valued_kev_retained": f"{open_world_kev_retained}/100",
    }


# ============================================================================
# PROBE 5: PackageHallucination Parser Bugs, Stdlib Bias, & Slopsquatting Gate
# ============================================================================


def spracks_normalize_python(name: str) -> str:
    """Exact port of `Spracks/PackageHallucination` `package_detection.py:9-17`."""
    name = re.sub(r"\d\. ", "", name)
    name = re.sub(r"(?<=.)\n(?=.)", " ", name)
    name = re.sub(r"\n", "", name)
    return re.sub(r"[-_.]+", "-", name).strip(" `.-").lower()


def spracks_refine_package_list_upstream(
    lst: list[str], option_like: set[str], core_modules: set[str]
) -> list[str]:
    """Exact port of `Spracks/PackageHallucination` `custom_parse_javascript.py:5-52`.

    Note: `refine_package_list` (`L15`: `new_list = lst`) aliases and mutates the caller's
    list in-place, whereas `extract_npm_packages` (`L111`: `new_list = list(set(matches))`)
    and `extract_npm_install` (`L163`: `new_list = list(set(matches))`) allocate fresh lists
    and share the in-place `for item in new_list: new_list.remove(item)` loop-skip bug.
    """
    new_list = lst  # L15: aliases caller's list in-place!
    for item in new_list:  # L17: mutates `new_list` during iteration!
        if "./" in item:
            new_list.remove(item)
        elif "\n" in item:
            new_list.remove(item)
        elif " " in item:
            new_list.remove(item)
        elif len(item) > 2:
            if item[:2] == "--":
                if item not in option_like:
                    new_list.remove(item)
    for core_item in sorted(core_modules):
        if core_item in new_list:
            new_list.remove(core_item)
    new_list = [x for x in new_list if len(x) > 0]
    final_list: list[str] = []
    for item in new_list:
        if "(" in item or ")" in item:
            continue
        item = (
            item.replace('"', "")
            .replace(";", "")
            .replace("`", "")
            .replace("'", "")
            .strip()
            .strip("\n")
        )
        if item == "nan":
            continue
        if item[0:1] == "\n":
            item = item[1:]
        if "https://" not in item:
            final_list.append(item.lower())
    return final_list


def spracks_delete_dupes_and_empty(packages: list[str]) -> list[str]:
    """Exact port of `custom_parse_python.py:4-7` & `custom_parse_javascript.py:198-201`."""
    no_dupes = sorted(set(packages))
    no_dupes = [i for i in no_dupes if len(i) > 2]
    return [x for x in no_dupes if x]


# Exact 22 public `len > 2` `sys.stdlib_module_names` modules omitted from both
# `Data/Python/pypi_package_names.csv` (500,565L, appended stdlib block at L500315-500565)
# and `Data/Python/false_positive_packages.csv` (3,884L) at `Spracks/PackageHallucination@bd3031cc`.
SPRACKS_MISSING_22_PUBLIC_STDLIB_GT2 = (
    "atexit",
    "cProfile",
    "concurrent",
    "encodings",
    "genericpath",
    "idlelib",
    "mmap",
    "ntpath",
    "nturl2path",
    "opcode",
    "posixpath",
    "profile",
    "pstats",
    "pydoc_data",
    "pyexpat",
    "sre_compile",
    "sre_constants",
    "sre_parse",
    "stringprep",
    "this",
    "turtledemo",
    "xml",
)


def run_probe_5_package_hallucination_parser_and_slopsquatting() -> dict[str, object]:
    npm_registry = {"express", "lodash", "react", "q", "ws", "pg", "rx", "ms", "ip"}
    caller_tokens = [
        "./utils",
        "./config",
        "--save-exact-custom",
        "--legacy-peer-flag",
        "express",
        "ws",
        "pg",
    ]
    caller_snapshot = list(caller_tokens)
    refined = spracks_refine_package_list_upstream(
        caller_tokens, option_like=set(), core_modules={"fs", "path"}
    )
    caller_mutated_in_place = caller_tokens != caller_snapshot
    deduped = spracks_delete_dupes_and_empty(refined)
    false_hallucinations = [tok for tok in deduped if tok not in npm_registry]
    erased_valid_short_pkgs = [
        tok for tok in ("ws", "pg") if tok in refined and tok not in deduped
    ]

    # Distinguish two separate Python stdlib validation pitfalls:
    # (a) Pure PyPI registry-snapshot validation without `sys.stdlib_module_names`
    #     (`Djire et al. ASE '26 §5.1 Table 2`: `+7.6` to `+9.4 pp` Python PHR inflation).
    #     Note that PyPI-hosted backports (`dataclasses`, `pathlib`, `asyncio`, `graphlib`)
    #     exist in the pure PyPI snapshot (`pypi_package_names.csv:1-500314`), whereas
    #     stdlib-only modules (`os`, `math`, `json`, `zoneinfo`, `sqlite3`, `xml`,
    #     `concurrent`, `mmap`, `atexit`, `stringprep`) do not.
    # (b) `Spracks/PackageHallucination` (`package_detection.py:63-93`):
    #     `false_positive_packages.csv` (3,884L) holds markdown/punctuation noise (`!-git`,
    #     `!doctype`, `!function`) with 0 stdlib names; instead, `pypi_package_names.csv`
    #     appends a manual stdlib list at `L500315-500565` that includes `math`, `json`,
    #     `tomllib`, `zoneinfo`, `sqlite3`, `urllib`, etc., but pastes dotted doc headings
    #     (`collections.abc` [L500336], `os.path` [L500358], `concurrent.features` [L500406],
    #     `xml.etree` [L500429] -> rewritten by `normalize_python` into `'xml-etree'`,
    #     `'concurrent-features'`) and misspells `'stringprep'` as `'strinprep'` (`L500328`),
    #     leaving 22 public `len > 2` `sys.stdlib_module_names` modules missing!
    pure_pypi_snapshot = {
        "requests",
        "numpy",
        "pydantic",
        "fastapi",
        "dataclasses",  # PyPI backport package (`pypi_package_names.csv` pre-L500315)
        "pathlib",  # PyPI backport package (`pypi_package_names.csv` pre-L500315)
        "asyncio",
        "graphlib",
    }
    spracks_appended_tail_raw = (
        "os",
        "re",
        "strinprep",  # L500328 typo for `stringprep`
        "zoneinfo",  # L500333
        "collections.abc",  # L500336 -> `collections-abc`
        "graphlib",  # L500346
        "math",  # L500348
        "pathlib",  # L500357
        "os.path",  # L500358 -> `os-path`
        "sqlite3",  # L500372
        "tomllib",  # L500381
        "concurrent.features",  # L500406 -> `concurrent-features`
        "json",  # L500420
        "xml.etree",  # L500429 -> `xml-etree` (bare `xml` absent!)
        "urllib",  # L500440
    )
    spracks_false_positive_csv = {"!-git", "!doctype", "!function"}
    spracks_normalized_pypi_set = {
        spracks_normalize_python(p) for p in pure_pypi_snapshot
    } | {spracks_normalize_python(p) for p in spracks_appended_tail_raw}

    assert set(SPRACKS_MISSING_22_PUBLIC_STDLIB_GT2).issubset(sys.stdlib_module_names)
    assert all(
        spracks_normalize_python(m) not in spracks_normalized_pypi_set
        and spracks_normalize_python(m) not in spracks_false_positive_csv
        for m in SPRACKS_MISSING_22_PUBLIC_STDLIB_GT2
    )

    generated_python_imports = [
        # 6 PyPI packages (including 2 PyPI-hosted stdlib backports `dataclasses`, `pathlib`)
        "requests",
        "numpy",
        "pydantic",
        "fastapi",
        "dataclasses",
        "pathlib",
        # 1 two-char stdlib module (`len == 2`, erased from denominator by `len(i) > 2`)
        "os",
        # 4 stdlib-only modules absent from PyPI (`pre-L500315`) but present in Spracks's tail
        "math",
        "json",
        "zoneinfo",
        "sqlite3",
        # 5 stdlib-only modules in Spracks's 22-module missing/corrupted gap
        "xml",
        "concurrent",
        "mmap",
        "atexit",
        "stringprep",
        # 2 genuine hallucinated packages
        "fast-json-magic",
        "py-auto-cloud",
    ]
    normalized_imports = [spracks_normalize_python(x) for x in generated_python_imports]
    valid_clean = spracks_delete_dupes_and_empty(normalized_imports)
    stdlib_normalized = {spracks_normalize_python(m) for m in sys.stdlib_module_names}

    pure_pypi_flagged = [p for p in valid_clean if p not in pure_pypi_snapshot]
    spracks_flagged = [
        p
        for p in valid_clean
        if p not in spracks_normalized_pypi_set and p not in spracks_false_positive_csv
    ]
    full_stdlib_flagged = [
        p
        for p in valid_clean
        if p not in pure_pypi_snapshot and p not in stdlib_normalized
    ]

    phr_pure_pypi_pct = round(100.0 * len(pure_pypi_flagged) / len(valid_clean), 2)
    phr_spracks_csv_pct = round(100.0 * len(spracks_flagged) / len(valid_clean), 2)
    phr_with_stdlib_pct = round(100.0 * len(full_stdlib_flagged) / len(valid_clean), 2)
    pure_pypi_stdlib_inflation_pp = round(phr_pure_pypi_pct - phr_with_stdlib_pct, 2)
    spracks_false_positive_stdlib = sorted(
        set(spracks_flagged) - set(full_stdlib_flagged)
    )
    pypi_backports_not_flagged = [
        b for b in ("dataclasses", "pathlib") if b not in pure_pypi_flagged
    ]

    # [illustrative analytical model] (`Basis: derived`) anchored to:
    # - Churilov (2026) §6: 127 5-model universal hallucinations (109 PyPI, 18 npm),
    #   of which 53 (41 PyPI, 12 npm) remain attacker-registrable after registry defenses;
    #   frontier per-prompt hallucination band [4.62%, 6.10%].
    # - Spracklen et al. (USENIX Security 2025) §5.3-5.4: 43% of hallucination-inducing
    #   prompts regenerate the identical hallucinated name in 10/10 runs; 81% of 2024
    #   unique hallucinated names were single-model, whereas Churilov's 53 registrable
    #   universal names occur across 5/5 frontier models (`Claude Haiku 4.5`,
    #   `Claude Sonnet 4.6`, `Gemini 2.5 Pro`, `DeepSeek V3.2`, `GPT-5.4-mini`).
    universal_total = 127
    universal_registrable = 53  # 41 PyPI + 12 npm
    blocked_by_registry_rules = universal_total - universal_registrable  # 74 blocked

    compromised_unguarded = universal_registrable
    compromised_5of5_consensus = universal_registrable
    compromised_snapshot_lock_gate = 0
    attractor_share = 0.43

    return {
        "parser_caller_list_mutated": caller_mutated_in_place,
        "parser_leaked_local_and_cli_as_hallucinations": false_hallucinations,
        "parser_erased_valid_2char_packages": erased_valid_short_pkgs,
        "phr_pure_pypi_without_stdlib_pct": phr_pure_pypi_pct,
        "phr_spracks_appended_csv_pct": phr_spracks_csv_pct,
        "phr_with_stdlib_pct": phr_with_stdlib_pct,
        "pure_pypi_stdlib_inflation_pp_on_fixture": pure_pypi_stdlib_inflation_pp,
        "pypi_backports_not_flagged": pypi_backports_not_flagged,
        "spracks_false_positive_stdlib_modules": spracks_false_positive_stdlib,
        "spracks_missing_public_stdlib_gt2_count": len(
            SPRACKS_MISSING_22_PUBLIC_STDLIB_GT2
        ),
        "model_label": "[illustrative analytical model] (Basis: derived)",
        "churilov_universal_5model_total": universal_total,
        "churilov_registry_blocked": blocked_by_registry_rules,
        "churilov_universal_registrable": universal_registrable,
        "compromised_unguarded": f"{compromised_unguarded}/{universal_registrable}",
        "compromised_5of5_consensus": f"{compromised_5of5_consensus}/{universal_registrable}",
        "compromised_snapshot_lockfile_gate": f"{compromised_snapshot_lock_gate}/{universal_registrable}",
        "spracklen_10of10_attractor_share": attractor_share,
    }


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        p1 = run_probe_1_govulncheck_vta_and_openvex()
        p2 = run_probe_2_osv_scanner_rust_dwarf_and_osv_ranges(tmp_dir)
        p3 = run_probe_3_syft_trivy_python_sbom_and_edges(tmp_dir)
        p4 = run_probe_4_vex_alias_revocation_and_orphan_impossibility()
        p5 = run_probe_5_package_hallucination_parser_and_slopsquatting()

    assert p1["cha_flagged"] == ["GO-TAR", "GO-XML", "GO-YAML"]
    assert p1["vta_pass1_flagged"] == ["GO-TAR", "GO-YAML"]
    assert p1["vta_pass2_flagged"] == ["GO-TAR"]
    assert p1["vta_unpassed_closure_pruned_pass1"] is True
    assert p1["vta_missed_reflection"] == ["GO-REFL"]
    assert p1["generic_lib_entries_count"] == 0 and p1["generic_lib_flagged"] == []
    assert len(p1["binary_stripped_flagged"]) == 6
    assert p1["antisymmetry_violations"] == [
        "(required,imported):-1_vs_-1",
        "(imported,required):-1_vs_-1",
    ]
    assert p1["openvex_req_then_imp"] == "vulnerable_code_not_in_execute_path"
    assert p1["openvex_imp_then_req_buggy"] == "vulnerable_code_not_present"
    assert p1["openvex_imp_then_req_fixed"] == "vulnerable_code_not_in_execute_path"
    assert p1["scalibr_unimported_mod_signal"] == "vulnerable_code_not_in_execute_path"

    assert p2["rust_regex_upstream_recall"] == "2/6"
    assert p2["rust_regex_balanced_recall"] == "6/6"
    assert p2["dwarf_inlined_detected"] is False
    assert p2["dwarf_dead_export_flagged"] is True
    assert p2["cargo_depfile_multi_rule_err"] is True
    assert p2["osv_git_limit_false_negatives"] == ["D", "E", "F"]
    assert p2["go_v1_false_imports_inheritance"] is True

    assert p3["syft_default_count"] == 3 and p3["trivy_default_count"] == 3
    assert p3["syft_guess_werkzeug"] == "2.2.2" and p3["trivy_min_werkzeug"] == "2.0.0"
    assert (
        p3["syft_guess_pyjwt_splitafter_bug"] is None
        and p3["trivy_default_pyjwt"] == "2.8.0"
    )
    assert (
        p3["syft_default_certifi_triple_eq"] == "2024.2.2"
        and p3["trivy_default_certifi_triple_eq"] is None
    )
    assert p3["trivy_pep621_extras_leaked"] == ["mypy", "pytest", "sphinx"]
    assert p3["trivy_poetry_deps_retained_when_optional_set"] == []
    assert p3["syft_cdx_relationships_kept"] == "1/4"
    assert p3["syft_spdx_relationships_kept"] == "4/4"

    assert p4["govex_effective_stmt_status"] == "affected"
    assert p4["trivy_openvex_falsely_suppresses_revoked_cve"] is True
    assert p4["prefixes_sorting_after_cve"] == "6/6"
    assert p4["connected_openvex_suppressed"] == "100/100"
    assert p4["degen_97pct_orphan_openvex_suppressed"] == "3/100"
    assert p4["degen_97pct_orphan_csaf_suppressed"] == "3/100"
    assert p4["degen_97pct_orphan_cdx_root_suppressed"] == "3/100"
    assert p4["degen_97pct_orphan_cdx_leaf_suppressed"] == "100/100"
    assert p4["wild_sbom_parseable_total"] == 77092
    assert p4["wild_sbom_non_connected_pct"] == 61.68

    assert p5["parser_caller_list_mutated"] is True
    assert p5["parser_leaked_local_and_cli_as_hallucinations"] == [
        "--legacy-peer-flag",
        "./config",
    ]
    assert p5["parser_erased_valid_2char_packages"] == ["ws", "pg"]
    assert p5["phr_pure_pypi_without_stdlib_pct"] == 64.71
    assert p5["phr_spracks_appended_csv_pct"] == 41.18
    assert p5["phr_with_stdlib_pct"] == 11.76
    assert p5["pure_pypi_stdlib_inflation_pp_on_fixture"] == 52.95
    assert p5["pypi_backports_not_flagged"] == ["dataclasses", "pathlib"]
    assert p5["spracks_false_positive_stdlib_modules"] == [
        "atexit",
        "concurrent",
        "mmap",
        "stringprep",
        "xml",
    ]
    assert p5["spracks_missing_public_stdlib_gt2_count"] == 22
    assert p5["compromised_5of5_consensus"] == "53/53"
    assert p5["compromised_snapshot_lockfile_gate"] == "0/53"

    report = {
        "probe_1_govulncheck_vta_and_openvex": p1,
        "probe_2_osv_scanner_rust_dwarf_and_osv_ranges": p2,
        "probe_3_syft_trivy_python_sbom_and_edges": p3,
        "probe_4_vex_alias_revocation_and_orphan_impossibility": p4,
        "probe_5_package_hallucination_parser_and_slopsquatting": p5,
    }
    sys.stdout.write(json.dumps(report, indent=2, sort_keys=False) + "\n")


if __name__ == "__main__":
    main()
