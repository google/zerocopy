#!/usr/bin/env python3
"""Standalone pure-stdlib verification suite for typed synthesis, typestate, and edit planning.

Run cleanly from the repository root with isolated interpreter flags:
    python3 -I -B reports/agent-typed-hole-contextualization-typestate-and-edit-planning/support/verify_typed_synthesis_typestate_codeplan_probes.py

This module uses only the Python 3.10+ standard library, performs zero disk writes
and zero network requests, and deterministically verifies four mechanisms:

1. Probe 1 [Basis: normative + derived + execution] — CodePlan Change May-Impact (CMG)
   AST diff classification and incremental dependency-graph propagation (D -> D',
   extracting edges directly from ASTs; Bairi et al., PACMSE/FSE 2024, DOI 10.1145/3643757)
   with AST-driven spatial-context helper synthesis vs. k-hop lexical grep and both
   single-pass and iterative multi-round static Build-Repair AST type/override checking.
2. Probe 2 [Basis: source + derived + execution] — Exact Aider@5dc9490bb35f9729ef2c95d00a19ccd30c26339c
   call-only Python RepoMap (`python-tags.scm:1-14` + `repomap.py:279-706` `if "ref" in saw: return`
   Pygments skip) vs. a counterfactual PEP-484 type-annotation + ImportFrom extension
   (`import_scoped=False` vs. `import_scoped=True`, bridging Blinn et al., OOPSLA 2024,
   DOI 10.1145/3689728) vs. matched-file 6x150-char BM25 chunk retrieval on the exact
   same unfilled typed hole (`...`) with zero oracle completion leakage.
3. Probe 3 [Basis: documentation + derived + execution] — Algebraic sum-type vs.
   boolean/nullable product illegal-state cardinality explosion (closed form cross-checked
   by exhaustive Cartesian enumeration) and Strom & Yemini (IEEE TSE 1986,
   DOI 10.1109/TSE.1986.6312929) lower-semilattice meet typestate dataflow analysis with
   sound intra-block pre-operation downward coercions and per-throw-site exception coercions.
4. Probe 4 [Basis: documentation + derived + execution] — Primary-source rational accounting
   of RustAssistant (Deligiannis et al., ICSE 2025, DOI 10.1109/ICSE55347.2025.00022, Table V
   9/134 = 6.72% non-stub runtime corruption) and CRUST-Bench (Khatry et al., COLM 2025,
   arXiv:2504.15254v3, Table 4 build-regression under test repair), paired with an explicitly
   parameterized absorbing Markov model N = (I - Q)^(-1), B = N * R (`Basis: derived`) and a
   comment/string-stripping Rust syntactic anti-bypass gate tested against non-stub `{ Ok(()) }`
   semantic deletion.
"""

from __future__ import annotations

import ast
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import io
import itertools
import json
import keyword
import math
from pathlib import PurePosixPath
import random
import re
import sys
import tokenize
from typing import Iterable, Sequence


# ============================================================================
# Probe 1: CodePlan CMG Incremental Dependency-Graph Propagation vs. Baselines
# ============================================================================


@dataclass(frozen=True)
class CodeBlock:
    block_id: str
    module: str
    kind: str  # "class" | "init" | "method" | "function"
    owner_class: str | None
    symbol: str
    source: str


@dataclass(frozen=True)
class DepEdge:
    src: str
    dst: str
    rel: str
    # Relations (Bairi et al., FSE 2024, §2.2.1):
    # "Calls" (src calls dst), "Instantiates" (src instantiates class dst),
    # "ConstructedBy" (class src constructed by init dst),
    # "Overrides" (derived method src overrides base method dst),
    # "BaseClassOf" (base class src of derived class dst),
    # "Uses" (block src accesses field `ClassName.field_name`).


@dataclass(frozen=True)
class ClassifiedDiff:
    block_id: str
    cmg_label: str  # CodePlan Table 1 labels: MMB, MMS, AF, MF, DF, MCC, AM, DM, AI, DI, ...
    escaping_mutation: bool = False
    signature_breaking: bool = False
    added_field: str | None = None
    modified_field: str | None = None


def _extract_func_def(source: str) -> ast.FunctionDef:
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            return node
    raise ValueError(f"No top-level FunctionDef in block source: {source!r}")


def _extract_class_def(source: str) -> ast.ClassDef:
    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            return node
    raise ValueError(f"No top-level ClassDef in block source: {source!r}")


def _extract_class_fields(source: str) -> dict[str, str]:
    cls_node = _extract_class_def(source)
    fields: dict[str, str] = {}
    for stmt in cls_node.body:
        if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            fields[stmt.target.id] = ast.unparse(stmt.annotation)
    return fields


def _extract_class_bases(source: str) -> list[str]:
    cls_node = _extract_class_def(source)
    bases: list[str] = []
    for base in cls_node.bases:
        if isinstance(base, ast.Name):
            bases.append(base.id)
    return bases


def extract_graph_edges_from_blocks(blocks: dict[str, CodeBlock]) -> set[DepEdge]:
    """Derives DependencyGraph edges D = (N, E) directly from parsed block ASTs."""
    edges: set[DepEdge] = set()
    class_bases: dict[str, list[str]] = {}
    own_fields: dict[str, dict[str, str]] = {}
    methods_by_class: dict[str, dict[str, str]] = defaultdict(dict)
    functions_by_name: dict[str, str] = {}

    for bid, blk in sorted(blocks.items()):
        if blk.kind == "class":
            bases = _extract_class_bases(blk.source)
            class_bases[blk.symbol] = bases
            own_fields[blk.symbol] = _extract_class_fields(blk.source)
            for bname in bases:
                if f"cls:{bname}" in blocks:
                    edges.add(DepEdge(f"cls:{bname}", bid, "BaseClassOf"))
            init_id = f"init:{blk.symbol}.__init__"
            if init_id in blocks:
                edges.add(DepEdge(bid, init_id, "ConstructedBy"))
        elif blk.kind == "method" and blk.owner_class is not None:
            methods_by_class[blk.owner_class][blk.symbol] = bid
        elif blk.kind == "function":
            functions_by_name[blk.symbol] = bid

    def ancestor_classes(cname: str) -> list[str]:
        out: list[str] = []
        queue: deque[str] = deque(class_bases.get(cname, []))
        seen: set[str] = set()
        while queue:
            cur = queue.popleft()
            if cur not in seen:
                seen.add(cur)
                out.append(cur)
                queue.extend(class_bases.get(cur, []))
        return out

    def resolve_field_owner_and_type(cname: str, attr: str) -> tuple[str, str] | None:
        for candidate in (cname, *ancestor_classes(cname)):
            fmap = own_fields.get(candidate, {})
            if attr in fmap:
                return candidate, fmap[attr]
        return None

    def resolve_method_target(cname: str, mname: str) -> str | None:
        for candidate in (cname, *ancestor_classes(cname)):
            if mname in methods_by_class.get(candidate, {}):
                return methods_by_class[candidate][mname]
        return None

    # Override edges across class hierarchy.
    for cname, mmap in sorted(methods_by_class.items()):
        for anc in ancestor_classes(cname):
            anc_methods = methods_by_class.get(anc, {})
            for mname, derived_bid in sorted(mmap.items()):
                if mname in anc_methods:
                    edges.add(DepEdge(derived_bid, anc_methods[mname], "Overrides"))

    # Intra-procedural receiver/parameter static type resolution for Calls, Instantiates, and Uses.
    for bid, blk in sorted(blocks.items()):
        if blk.kind not in {"init", "method", "function"}:
            continue
        fn = _extract_func_def(blk.source)
        local_types: dict[str, str] = {}
        if blk.owner_class is not None and fn.args.args:
            local_types[fn.args.args[0].arg] = blk.owner_class
        for arg in fn.args.args:
            if arg.annotation is not None:
                ann = ast.unparse(arg.annotation)
                if f"cls:{ann}" in blocks:
                    local_types[arg.arg] = ann

        # Simple local constructor assignments `x = ClassName(...)`.
        for node in ast.walk(fn):
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
                    cname = node.value.func.id
                    if f"cls:{cname}" in blocks:
                        local_types[node.targets[0].id] = cname

        def expr_class_type(expr: ast.AST) -> str | None:
            if isinstance(expr, ast.Name):
                return local_types.get(expr.id)
            if isinstance(expr, ast.Attribute):
                owner_cls = expr_class_type(expr.value)
                if owner_cls is not None:
                    resolved = resolve_field_owner_and_type(owner_cls, expr.attr)
                    if resolved is not None and f"cls:{resolved[1]}" in blocks:
                        return resolved[1]
            return None

        call_func_nodes: set[int] = set()
        for node in ast.walk(fn):
            if isinstance(node, ast.Call):
                call_func_nodes.add(id(node.func))
                if isinstance(node.func, ast.Name):
                    callee = node.func.id
                    if f"cls:{callee}" in blocks:
                        edges.add(DepEdge(bid, f"cls:{callee}", "Instantiates"))
                    elif callee in functions_by_name:
                        edges.add(DepEdge(bid, functions_by_name[callee], "Calls"))
                elif isinstance(node.func, ast.Attribute):
                    recv_cls = expr_class_type(node.func.value)
                    if recv_cls is not None:
                        mtarget = resolve_method_target(recv_cls, node.func.attr)
                        if mtarget is not None:
                            edges.add(DepEdge(bid, mtarget, "Calls"))

        for node in ast.walk(fn):
            if isinstance(node, ast.Attribute) and id(node) not in call_func_nodes:
                recv_cls = expr_class_type(node.value)
                if recv_cls is not None:
                    resolved = resolve_field_owner_and_type(recv_cls, node.attr)
                    if resolved is not None:
                        edges.add(DepEdge(bid, f"{resolved[0]}.{node.attr}", "Uses"))

    return edges


class DependencyGraph:
    """Incremental AST-derived dependency graph D = (N, E) supporting D -> D' updates."""

    def __init__(self, blocks: dict[str, CodeBlock], edges: Iterable[DepEdge] | None = None) -> None:
        self.blocks: dict[str, CodeBlock] = dict(blocks)
        self.edges: set[DepEdge] = (
            set(edges) if edges is not None else extract_graph_edges_from_blocks(self.blocks)
        )

    @classmethod
    def from_blocks(cls, blocks: dict[str, CodeBlock]) -> DependencyGraph:
        return cls(blocks, extract_graph_edges_from_blocks(blocks))

    def update_block(self, updated: CodeBlock) -> DependencyGraph:
        """Recomputes AST dependency edges incrementally after replacing or adding `updated`."""
        new_blocks = dict(self.blocks)
        new_blocks[updated.block_id] = updated
        return DependencyGraph.from_blocks(new_blocks)

    def rel(self, node: str, relation: str) -> list[str]:
        out: set[str] = set()
        for e in self.edges:
            if relation == "CalledBy" and e.rel == "Calls" and e.dst == node:
                out.add(e.src)
            elif relation == "Calls" and e.rel == "Calls" and e.src == node:
                out.add(e.dst)
            elif relation == "Overrides" and e.rel == "Overrides" and e.src == node:
                out.add(e.dst)
            elif relation == "OverriddenBy" and e.rel == "Overrides" and e.dst == node:
                out.add(e.src)
            elif relation == "ConstructedBy" and e.rel == "ConstructedBy" and e.src == node:
                out.add(e.dst)
            elif relation == "InstantiatedBy" and e.rel == "Instantiates" and e.dst == node:
                out.add(e.src)
            elif relation == "BaseClassOf" and e.rel == "BaseClassOf" and e.src == node:
                out.add(e.dst)
            elif relation == "DerivedClassOf" and e.rel == "BaseClassOf" and e.dst == node:
                out.add(e.src)
            elif relation == "UsedBy" and e.rel == "Uses" and e.dst == node:
                out.add(e.src)
        return sorted(out)


def _type_subsumes(wider: str, narrower: str) -> bool:
    """Checks simple contravariant parameter widening such as `int` -> `int | float`."""
    if wider == "Any" or wider == narrower:
        return True
    wider_parts = {p.strip() for p in wider.split("|")}
    narrower_parts = {p.strip() for p in narrower.split("|")}
    return narrower_parts.issubset(wider_parts)


def _mutates_escaping_state(fn: ast.FunctionDef) -> set[str]:
    """Detects mutations to receiver attributes (`self.<attr>`) or parameter attributes."""
    param_names = {arg.arg for arg in fn.args.args}
    mutated: set[str] = set()
    for node in ast.walk(fn):
        if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for tgt in targets:
                if isinstance(tgt, ast.Attribute) and isinstance(tgt.value, ast.Name):
                    if tgt.value.id in param_names:
                        mutated.add(f"{tgt.value.id}.{tgt.attr}")
    return mutated


def classify_ast_diff(old_block: CodeBlock, new_block: CodeBlock) -> list[ClassifiedDiff]:
    """Classifies AST edits into CodePlan Table 1 CMG labels with variance awareness."""
    if old_block.kind == "class":
        old_fields = _extract_class_fields(old_block.source)
        new_fields = _extract_class_fields(new_block.source)
        diffs: list[ClassifiedDiff] = []
        for fname in sorted(set(new_fields) - set(old_fields)):
            diffs.append(
                ClassifiedDiff(
                    block_id=new_block.block_id,
                    cmg_label="AF",
                    added_field=f"{new_block.symbol}.{fname}",
                )
            )
        for fname in sorted(set(old_fields) - set(new_fields)):
            diffs.append(
                ClassifiedDiff(
                    block_id=new_block.block_id,
                    cmg_label="DF",
                    modified_field=f"{new_block.symbol}.{fname}",
                )
            )
        for fname in sorted(set(old_fields) & set(new_fields)):
            if old_fields[fname] != new_fields[fname]:
                diffs.append(
                    ClassifiedDiff(
                        block_id=new_block.block_id,
                        cmg_label="MF",
                        modified_field=f"{new_block.symbol}.{fname}",
                    )
                )
        return diffs

    old_fn = _extract_func_def(old_block.source)
    new_fn = _extract_func_def(new_block.source)

    old_args = [(a.arg, ast.unparse(a.annotation) if a.annotation else "Any") for a in old_fn.args.args]
    new_args = [(a.arg, ast.unparse(a.annotation) if a.annotation else "Any") for a in new_fn.args.args]
    old_req = len(old_args) - len(old_fn.args.defaults)
    new_req = len(new_args) - len(new_fn.args.defaults)
    old_ret = ast.unparse(old_fn.returns) if old_fn.returns else "None"
    new_ret = ast.unparse(new_fn.returns) if new_fn.returns else "None"

    if (old_args != new_args) or (old_req != new_req) or (old_ret != new_ret):
        if old_block.kind == "init":
            return [ClassifiedDiff(block_id=new_block.block_id, cmg_label="MCC", signature_breaking=True)]
        compatible_arity = (new_req <= old_req) and (len(new_args) >= len(old_args))
        params_contravariant_safe = compatible_arity and all(
            old_args[i][0] == new_args[i][0] and _type_subsumes(new_args[i][1], old_args[i][1])
            for i in range(len(old_args))
        )
        ret_covariant_safe = _type_subsumes(old_ret, new_ret)
        breaking = not (params_contravariant_safe and ret_covariant_safe)
        return [ClassifiedDiff(block_id=new_block.block_id, cmg_label="MMS", signature_breaking=breaking)]

    escaping = _mutates_escaping_state(old_fn) != _mutates_escaping_state(new_fn)
    return [ClassifiedDiff(block_id=new_block.block_id, cmg_label="MMB", escaping_mutation=escaping)]


def cmg_affected_blocks(
    d_old: DependencyGraph,
    d_new: DependencyGraph,
    diff: ClassifiedDiff,
    *,
    variance_aware: bool = True,
) -> list[str]:
    """Implements GetAffectedBlocks from CodePlan Table 1 (Bairi et al., FSE 2024)."""
    b = diff.block_id
    blk = d_new.blocks[b]
    affected: set[str] = set()

    if diff.cmg_label == "MMB":
        if diff.escaping_mutation:
            affected.update(d_old.rel(b, "CalledBy"))
    elif diff.cmg_label == "MMS":
        affected.update(d_old.rel(b, "Overrides"))
        affected.update(d_old.rel(b, "OverriddenBy"))
        affected.update(d_new.rel(b, "Overrides"))
        affected.update(d_new.rel(b, "OverriddenBy"))
        if (not variance_aware) or diff.signature_breaking:
            affected.update(d_old.rel(b, "CalledBy"))
    elif diff.cmg_label == "AF":
        affected.update(d_old.rel(b, "ConstructedBy"))
        affected.update(d_old.rel(b, "BaseClassOf"))
        affected.update(d_old.rel(b, "DerivedClassOf"))
    elif diff.cmg_label in {"MF", "DF"}:
        assert diff.modified_field is not None
        affected.update(d_old.rel(diff.modified_field, "UsedBy"))
        affected.update(d_old.rel(b, "ConstructedBy"))
        affected.update(d_old.rel(b, "BaseClassOf"))
        affected.update(d_old.rel(b, "DerivedClassOf"))
    elif diff.cmg_label == "MCC":
        assert blk.owner_class is not None
        cls_node = f"cls:{blk.owner_class}"
        affected.update(d_old.rel(cls_node, "InstantiatedBy"))
        affected.update(d_old.rel(cls_node, "BaseClassOf"))
        affected.update(d_old.rel(cls_node, "DerivedClassOf"))
    elif diff.cmg_label in {"AI", "DI"}:
        if diff.cmg_label == "DI":
            affected.update(d_old.rel(b, "UsedBy"))
    else:
        raise ValueError(f"Unsupported CMG label: {diff.cmg_label}")

    affected.discard(b)
    return sorted(affected)


def gather_spatial_class_sketch(
    graph: DependencyGraph,
    owner_class: str | None,
    *,
    include_spatial_context: bool,
) -> dict[str, tuple[tuple[str, ...], str]]:
    """Extracts visible sibling zero-arg/typed method signatures on `owner_class` for GatherContext."""
    if not include_spatial_context or owner_class is None:
        return {}
    visible: dict[str, tuple[tuple[str, ...], str]] = {}
    for _bid, blk in sorted(graph.blocks.items()):
        if blk.kind == "method" and blk.owner_class == owner_class:
            fn = _extract_func_def(blk.source)
            param_types = tuple(
                ast.unparse(a.annotation) if a.annotation else "Any"
                for a in fn.args.args[1:]  # exclude `self`
            )
            ret_type = ast.unparse(fn.returns) if fn.returns else "None"
            visible[blk.symbol] = (param_types, ret_type)
    return visible


def synthesize_caller_adaptation_ast(
    caller_blk: CodeBlock,
    callee_blk: CodeBlock,
    visible_sibling_methods: dict[str, tuple[tuple[str, ...], str]],
    true_class_methods: dict[str, tuple[tuple[str, ...], str]],
) -> tuple[str, list[CodeBlock]]:
    """Synthesizes AST call-site repair for added required parameters, emitting a helper if out-of-scope."""
    caller_fn = _extract_func_def(caller_blk.source)
    callee_fn = _extract_func_def(callee_blk.source)

    callee_params = [
        (a.arg, ast.unparse(a.annotation) if a.annotation else "Any")
        for a in (callee_fn.args.args[1:] if callee_blk.owner_class else callee_fn.args.args)
    ]
    callee_req = len(callee_params) - len(callee_fn.args.defaults)
    caller_scope_vars = {
        a.arg: (ast.unparse(a.annotation) if a.annotation else "Any")
        for a in caller_fn.args.args
    }

    synthesized_helpers: list[CodeBlock] = []
    extra_bind_lines: list[str] = []
    call_rewrites: list[tuple[str, str]] = []

    for node in ast.walk(caller_fn):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            if node.func.attr == callee_blk.symbol and len(node.args) < callee_req:
                new_arg_exprs = [ast.unparse(a) for a in node.args]
                for idx in range(len(node.args), callee_req):
                    pname, ptype = callee_params[idx]
                    matching_local = [
                        v for v, vtype in sorted(caller_scope_vars.items())
                        if v == pname and vtype == ptype
                    ]
                    if matching_local:
                        new_arg_exprs.append(matching_local[0])
                        continue
                    # Search visible enclosing-class sketch for an existing `() -> ptype` provider.
                    matching_siblings = [
                        msym for msym, (mparams, mret) in sorted(visible_sibling_methods.items())
                        if msym != caller_blk.symbol and mparams == () and mret == ptype
                    ]
                    if matching_siblings:
                        var_name = f"resolved_{pname}"
                        extra_bind_lines.append(f"    {var_name} = self.{matching_siblings[0]}()")
                        new_arg_exprs.append(var_name)
                    else:
                        # Spatial Context lacked sibling member visibility -> synthesize new helper method!
                        helper_sym = f"_resolve_{pname}"
                        helper_id = f"meth:{caller_blk.owner_class}.{helper_sym}"
                        helper_src = (
                            f"def {helper_sym}(self) -> {ptype}:\n"
                            f"    return 'synthesized-default'\n"
                        )
                        # Check AST signatures of true existing class methods for duplicate capability.
                        existing_providers = [
                            msym for msym, (mparams, mret) in sorted(true_class_methods.items())
                            if msym != caller_blk.symbol and mparams == () and mret == ptype
                        ]
                        if existing_providers:
                            synthesized_helpers.append(
                                CodeBlock(
                                    helper_id,
                                    caller_blk.module,
                                    "method",
                                    caller_blk.owner_class,
                                    helper_sym,
                                    helper_src,
                                )
                            )
                        var_name = f"resolved_{pname}"
                        extra_bind_lines.append(f"    {var_name} = self.{helper_sym}()")
                        new_arg_exprs.append(var_name)
                old_call_src = ast.unparse(node)
                new_call_src = f"{ast.unparse(node.func)}({', '.join(new_arg_exprs)})"
                call_rewrites.append((old_call_src, new_call_src))

    header_line = caller_blk.source.splitlines()[0]
    body_lines = caller_blk.source.splitlines()[1:]
    updated_body: list[str] = list(extra_bind_lines)
    for line in body_lines:
        new_line = line
        for old_c, new_c in call_rewrites:
            new_line = new_line.replace(old_c, new_c)
        updated_body.append(new_line)
    return "\n".join([header_line, *updated_body]) + "\n", synthesized_helpers


def find_static_type_and_arity_errors(
    graph: DependencyGraph,
    *,
    check_override_signatures: bool,
) -> set[str]:
    """Static compiler/Pyright AST checker over `graph` (no hardcoded block IDs)."""
    flagged: set[str] = set()

    def fn_sig(blk: CodeBlock) -> tuple[list[tuple[str, str]], int, str]:
        fn = _extract_func_def(blk.source)
        params = [
            (a.arg, ast.unparse(a.annotation) if a.annotation else "Any")
            for a in (fn.args.args[1:] if blk.owner_class else fn.args.args)
        ]
        req = len(params) - len(fn.args.defaults)
        ret = ast.unparse(fn.returns) if fn.returns else "None"
        return params, req, ret

    # 1. Check direct call/instantiation arity and static argument types.
    for e in sorted(graph.edges, key=lambda item: (item.src, item.dst, item.rel)):
        if e.rel in {"Calls", "Instantiates"}:
            caller_blk = graph.blocks[e.src]
            if e.rel == "Instantiates":
                cls_name = graph.blocks[e.dst].symbol
                init_id = f"init:{cls_name}.__init__"
                if init_id not in graph.blocks:
                    continue
                callee_blk = graph.blocks[init_id]
                target_sym = cls_name
            else:
                callee_blk = graph.blocks[e.dst]
                target_sym = callee_blk.symbol

            params, req_count, _ret = fn_sig(callee_blk)
            caller_fn = _extract_func_def(caller_blk.source)
            local_types = {
                a.arg: (ast.unparse(a.annotation) if a.annotation else "Any")
                for a in caller_fn.args.args
            }
            for node in ast.walk(caller_fn):
                if not isinstance(node, ast.Call):
                    continue
                matched_name = (
                    node.func.id
                    if isinstance(node.func, ast.Name)
                    else (node.func.attr if isinstance(node.func, ast.Attribute) else None)
                )
                if matched_name != target_sym:
                    continue
                if len(node.args) < req_count or len(node.args) > len(params):
                    flagged.add(caller_blk.block_id)
                else:
                    for arg_node, (_pname, ptype) in zip(node.args, params):
                        if isinstance(arg_node, ast.Name) and arg_node.id in local_types:
                            if not _type_subsumes(ptype, local_types[arg_node.id]):
                                flagged.add(caller_blk.block_id)

        # 2. Check Liskov override compatibility (`Pyright` `reportIncompatibleMethodOverride`).
        elif e.rel == "Overrides" and check_override_signatures:
            derived_blk = graph.blocks[e.src]
            base_blk = graph.blocks[e.dst]
            d_params, d_req, d_ret = fn_sig(derived_blk)
            b_params, b_req, b_ret = fn_sig(base_blk)
            compatible = (
                d_req <= b_req
                and len(d_params) >= len(b_params)
                and all(_type_subsumes(d_params[i][1], b_params[i][1]) for i in range(len(b_params)))
                and _type_subsumes(b_ret, d_ret)
            )
            if not compatible:
                flagged.add(derived_blk.block_id)

    # 3. Check `self.<field> = <param>` assignment type consistency inside `__init__` / methods.
    for bid, blk in sorted(graph.blocks.items()):
        if blk.kind in {"init", "method"} and blk.owner_class is not None:
            cls_id = f"cls:{blk.owner_class}"
            if cls_id not in graph.blocks:
                continue
            field_types = _extract_class_fields(graph.blocks[cls_id].source)
            fn = _extract_func_def(blk.source)
            param_types = {
                a.arg: (ast.unparse(a.annotation) if a.annotation else "Any")
                for a in fn.args.args
            }
            for node in ast.walk(fn):
                if isinstance(node, ast.Assign) and isinstance(node.value, ast.Name):
                    rhs_type = param_types.get(node.value.id)
                    if rhs_type is None:
                        continue
                    for tgt in node.targets:
                        if (
                            isinstance(tgt, ast.Attribute)
                            and isinstance(tgt.value, ast.Name)
                            and tgt.value.id == "self"
                            and tgt.attr in field_types
                        ):
                            if not _type_subsumes(field_types[tgt.attr], rhs_type):
                                flagged.add(bid)

    return flagged


def run_probe_1_codeplan() -> dict[str, object]:
    """Executes Probe 1 on a 20-block multi-module workspace across 6 seed edits."""
    blocks: dict[str, CodeBlock] = {
        "cls:SessionToken": CodeBlock(
            "cls:SessionToken",
            "auth_models.py",
            "class",
            None,
            "SessionToken",
            "class SessionToken:\n    user_id: str\n    secret_digest: bytes\n    nonce_seq: int\n",
        ),
        "init:SessionToken.__init__": CodeBlock(
            "init:SessionToken.__init__",
            "auth_models.py",
            "init",
            "SessionToken",
            "__init__",
            "def __init__(self, user_id: str, secret_digest: bytes, nonce_seq: int = 0) -> None:\n    self.user_id = user_id\n    self.secret_digest = secret_digest\n    self.nonce_seq = nonce_seq\n",
        ),
        "meth:SessionToken.rotate_nonce": CodeBlock(
            "meth:SessionToken.rotate_nonce",
            "auth_models.py",
            "method",
            "SessionToken",
            "rotate_nonce",
            "def rotate_nonce(self) -> int:\n    next_seq = self.nonce_seq + 1\n    return next_seq\n",
        ),
        "fn:refresh_auth_header": CodeBlock(
            "fn:refresh_auth_header",
            "auth_check.py",
            "function",
            None,
            "refresh_auth_header",
            "def refresh_auth_header(tok: SessionToken) -> str:\n    seq = tok.rotate_nonce()\n    return f'v1:{seq}'\n",
        ),
        "fn:verify_session_digest": CodeBlock(
            "fn:verify_session_digest",
            "auth_check.py",
            "function",
            None,
            "verify_session_digest",
            "def verify_session_digest(tok: SessionToken) -> bool:\n    return len(tok.secret_digest) == 32\n",
        ),
        "cls:BaseGateway": CodeBlock(
            "cls:BaseGateway",
            "gateway_base.py",
            "class",
            None,
            "BaseGateway",
            "class BaseGateway:\n    endpoint: str\n",
        ),
        "meth:BaseGateway.charge": CodeBlock(
            "meth:BaseGateway.charge",
            "gateway_base.py",
            "method",
            "BaseGateway",
            "charge",
            "def charge(self, account_id: str, cents: int) -> bool:\n    return cents >= 0\n",
        ),
        "cls:StripeGateway": CodeBlock(
            "cls:StripeGateway",
            "gateway_stripe.py",
            "class",
            None,
            "StripeGateway",
            "class StripeGateway(BaseGateway):\n    region: str\n",
        ),
        "meth:StripeGateway.charge": CodeBlock(
            "meth:StripeGateway.charge",
            "gateway_stripe.py",
            "method",
            "StripeGateway",
            "charge",
            "def charge(self, account_id: str, cents: int) -> bool:\n    return cents > 0\n",
        ),
        "cls:ServiceBase": CodeBlock(
            "cls:ServiceBase",
            "service_base.py",
            "class",
            None,
            "ServiceBase",
            "class ServiceBase:\n    service_name: str\n",
        ),
        "cls:BillingService": CodeBlock(
            "cls:BillingService",
            "billing_service.py",
            "class",
            None,
            "BillingService",
            "class BillingService(ServiceBase):\n    gateway: BaseGateway\n",
        ),
        "init:BillingService.__init__": CodeBlock(
            "init:BillingService.__init__",
            "billing_service.py",
            "init",
            "BillingService",
            "__init__",
            "def __init__(self, gateway: BaseGateway) -> None:\n    self.gateway = gateway\n",
        ),
        "meth:BillingService.current_tenant_id": CodeBlock(
            "meth:BillingService.current_tenant_id",
            "billing_service.py",
            "method",
            "BillingService",
            "current_tenant_id",
            "def current_tenant_id(self) -> str:\n    return 'tenant-default'\n",
        ),
        "meth:BillingService.settle_invoice": CodeBlock(
            "meth:BillingService.settle_invoice",
            "billing_service.py",
            "method",
            "BillingService",
            "settle_invoice",
            "def settle_invoice(self, account_id: str, cents: int) -> bool:\n    return self.gateway.charge(account_id, cents)\n",
        ),
        "fn:build_checkout_pipeline": CodeBlock(
            "fn:build_checkout_pipeline",
            "checkout_wire.py",
            "function",
            None,
            "build_checkout_pipeline",
            "def build_checkout_pipeline(gw: BaseGateway) -> BillingService:\n    return BillingService(gw)\n",
        ),
        "fn:compute_tax_basis": CodeBlock(
            "fn:compute_tax_basis",
            "tax_math.py",
            "function",
            None,
            "compute_tax_basis",
            "def compute_tax_basis(cents: int) -> int:\n    step = cents * 7\n    return step // 100\n",
        ),
        "fn:render_invoice_line": CodeBlock(
            "fn:render_invoice_line",
            "invoice_fmt.py",
            "function",
            None,
            "render_invoice_line",
            "def render_invoice_line(cents: int) -> str:\n    tax = compute_tax_basis(cents)\n    return f'{cents}+{tax}'\n",
        ),
        "fn:format_currency_units": CodeBlock(
            "fn:format_currency_units",
            "currency_fmt.py",
            "function",
            None,
            "format_currency_units",
            "def format_currency_units(amount: int) -> str:\n    return f'{amount}c'\n",
        ),
        "fn:export_summary_row": CodeBlock(
            "fn:export_summary_row",
            "report_export.py",
            "function",
            None,
            "export_summary_row",
            "def export_summary_row(total_cents: int) -> str:\n    return format_currency_units(total_cents)\n",
        ),
        "fn:archive_charge_notes": CodeBlock(
            "fn:archive_charge_notes",
            "legacy_notes.py",
            "function",
            None,
            "archive_charge_notes",
            "def archive_charge_notes(charge: str) -> str:\n    return charge.strip()\n",
        ),
    }

    graph = DependencyGraph.from_blocks(blocks)
    assert find_static_type_and_arity_errors(graph, check_override_signatures=True) == set()

    seed_updates: dict[str, str] = {
        "fn:compute_tax_basis": (
            "def compute_tax_basis(cents: int) -> int:\n"
            "    return (cents * 7) // 100\n"
        ),
        "meth:SessionToken.rotate_nonce": (
            "def rotate_nonce(self) -> int:\n"
            "    self.nonce_seq += 1\n"
            "    return self.nonce_seq\n"
        ),
        "fn:format_currency_units": (
            "def format_currency_units(amount: int | float) -> str:\n"
            "    return f'{amount}c'\n"
        ),
        "meth:BaseGateway.charge": (
            "def charge(self, account_id: str, cents: int, trace_id: str) -> bool:\n"
            "    return cents >= 0 and bool(trace_id)\n"
        ),
        "cls:ServiceBase": (
            "class ServiceBase:\n"
            "    service_name: str\n"
            "    audit_sink: AuditSink\n"
        ),
        "cls:SessionToken": (
            "class SessionToken:\n"
            "    user_id: str\n"
            "    secret_digest: str\n"
            "    nonce_seq: int\n"
        ),
    }

    downstream_patches: dict[str, str] = {
        "fn:refresh_auth_header": (
            "def refresh_auth_header(tok: SessionToken) -> str:\n"
            "    seq = tok.rotate_nonce()\n"
            "    return f'v2-mutated:{seq}'\n"
        ),
        "meth:StripeGateway.charge": (
            "def charge(self, account_id: str, cents: int, trace_id: str) -> bool:\n"
            "    return cents > 0 and bool(trace_id)\n"
        ),
        "meth:BillingService.settle_invoice": (
            "def settle_invoice(self, account_id: str, cents: int) -> bool:\n"
            "    resolved_trace_id = self.current_tenant_id()\n"
            "    return self.gateway.charge(account_id, cents, resolved_trace_id)\n"
        ),
        "cls:BillingService": (
            "class BillingService(ServiceBase):\n"
            "    gateway: BaseGateway\n"
            "    audit_sink: AuditSink\n"
        ),
        "init:BillingService.__init__": (
            "def __init__(self, gateway: BaseGateway, audit_sink: AuditSink) -> None:\n"
            "    self.gateway = gateway\n"
            "    self.audit_sink = audit_sink\n"
        ),
        "fn:build_checkout_pipeline": (
            "def build_checkout_pipeline(gw: BaseGateway, sink: AuditSink) -> BillingService:\n"
            "    return BillingService(gw, sink)\n"
        ),
        "init:SessionToken.__init__": (
            "def __init__(self, user_id: str, secret_digest: str, nonce_seq: int = 0) -> None:\n"
            "    self.user_id = user_id\n"
            "    self.secret_digest = secret_digest\n"
            "    self.nonce_seq = nonce_seq\n"
        ),
        "fn:verify_session_digest": (
            "def verify_session_digest(tok: SessionToken) -> bool:\n"
            "    return len(tok.secret_digest) == 64\n"
        ),
    }
    ground_truth_derived: set[str] = set(downstream_patches.keys())

    def apply_seeds(base_graph: DependencyGraph) -> DependencyGraph:
        g = base_graph
        for bid, new_src in sorted(seed_updates.items()):
            old_blk = g.blocks[bid]
            g = g.update_block(
                CodeBlock(bid, old_blk.module, old_blk.kind, old_blk.owner_class, old_blk.symbol, new_src)
            )
        return g

    def run_cmg_worklist(*, variance_aware: bool, include_spatial_context: bool) -> tuple[set[str], int, DependencyGraph]:
        cur_graph = graph
        queue: deque[str] = deque()
        scheduled_derived: set[str] = set()
        duplicate_helpers: list[CodeBlock] = []

        for bid, new_src in sorted(seed_updates.items()):
            old_blk = cur_graph.blocks[bid]
            new_blk = CodeBlock(bid, old_blk.module, old_blk.kind, old_blk.owner_class, old_blk.symbol, new_src)
            d_next = cur_graph.update_block(new_blk)
            for cdiff in classify_ast_diff(old_blk, new_blk):
                for dep in cmg_affected_blocks(cur_graph, d_next, cdiff, variance_aware=variance_aware):
                    if dep not in seed_updates and dep not in scheduled_derived:
                        scheduled_derived.add(dep)
                        queue.append(dep)
            cur_graph = d_next

        while queue:
            target = queue.popleft()
            old_blk = cur_graph.blocks[target]
            # Check if target has an unresolved caller arity adaptation obligation against any callee in `cur_graph`.
            synthesized_src: str | None = None
            for callee_id in cur_graph.rel(target, "Calls"):
                callee_blk = cur_graph.blocks[callee_id]
                visible_sketch = gather_spatial_class_sketch(
                    cur_graph, old_blk.owner_class, include_spatial_context=include_spatial_context
                )
                true_sketch = gather_spatial_class_sketch(
                    cur_graph, old_blk.owner_class, include_spatial_context=True
                )
                cand_src, extra_helpers = synthesize_caller_adaptation_ast(
                    old_blk, callee_blk, visible_sketch, true_sketch
                )
                if cand_src != old_blk.source.rstrip("\n") + "\n":
                    synthesized_src = cand_src
                    for hblk in extra_helpers:
                        duplicate_helpers.append(hblk)
                        cur_graph = cur_graph.update_block(hblk)

            if synthesized_src is None:
                if target not in downstream_patches:
                    continue
                synthesized_src = downstream_patches[target]

            new_blk = CodeBlock(
                target, old_blk.module, old_blk.kind, old_blk.owner_class, old_blk.symbol, synthesized_src
            )
            d_next = cur_graph.update_block(new_blk)
            for cdiff in classify_ast_diff(old_blk, new_blk):
                for dep in cmg_affected_blocks(cur_graph, d_next, cdiff, variance_aware=variance_aware):
                    if dep not in seed_updates and dep not in scheduled_derived:
                        scheduled_derived.add(dep)
                        queue.append(dep)
            cur_graph = d_next

        return scheduled_derived, len(duplicate_helpers), cur_graph

    # Baseline A: Genuine single-pass static compiler check (direct caller arity + field assignment types).
    seeded_graph = apply_seeds(graph)
    build_repair_1pass = (
        find_static_type_and_arity_errors(seeded_graph, check_override_signatures=False) - set(seed_updates)
    )

    # Baseline B: Iterative multi-round strict static checker (including Liskov override signatures)
    # run to zero-static-error fixed point, modeling Pyright-Strict-Repair / Build-Repair.
    iter_graph = seeded_graph
    build_repair_iter: set[str] = set()
    while True:
        errs = find_static_type_and_arity_errors(iter_graph, check_override_signatures=True) - set(seed_updates)
        new_errs = sorted(errs - build_repair_iter)
        if not new_errs:
            break
        for bid in new_errs:
            build_repair_iter.add(bid)
            if bid in downstream_patches:
                oblk = iter_graph.blocks[bid]
                iter_graph = iter_graph.update_block(
                    CodeBlock(bid, oblk.module, oblk.kind, oblk.owner_class, oblk.symbol, downstream_patches[bid])
                )

    # Baseline C: Lexical k-hop grep over symbol identifiers of edited seed blocks.
    ident_re = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")

    def run_lexical_grep(hops: int) -> set[str]:
        frontier_syms = {blocks[b].symbol for b in seed_updates}
        matched: set[str] = set()
        for _ in range(hops):
            next_syms: set[str] = set()
            for bid, blk in sorted(blocks.items()):
                if bid in seed_updates or bid in matched:
                    continue
                tokens = set(ident_re.findall(blk.source))
                if tokens & frontier_syms:
                    matched.add(bid)
                    next_syms.add(blk.symbol)
            frontier_syms = next_syms
        return matched

    cmg_var_pred, cmg_var_spurious, final_cmg_graph = run_cmg_worklist(
        variance_aware=True, include_spatial_context=True
    )
    cmg_strict_pred, _, _ = run_cmg_worklist(variance_aware=False, include_spatial_context=True)
    cmg_nosc_pred, cmg_nosc_spurious, final_nosc_graph = run_cmg_worklist(
        variance_aware=True, include_spatial_context=False
    )
    grep_1_pred = run_lexical_grep(1)
    grep_2_pred = run_lexical_grep(2)

    def score(pred: set[str]) -> tuple[int, int, int, float, float]:
        tp = len(pred & ground_truth_derived)
        fp = len(pred - ground_truth_derived)
        fn = len(ground_truth_derived - pred)
        prec = tp / (tp + fp) if (tp + fp) else 1.0
        rec = tp / (tp + fn) if (tp + fn) else 1.0
        return tp, fp, fn, prec, rec

    s_cmg_var = score(cmg_var_pred)
    s_cmg_strict = score(cmg_strict_pred)
    s_build_1pass = score(build_repair_1pass)
    s_build_iter = score(build_repair_iter)
    s_grep1 = score(grep_1_pred)
    s_grep2 = score(grep_2_pred)

    # Verify live D -> D' incremental edge addition from AST updates!
    added_tenant_edge = DepEdge(
        "meth:BillingService.settle_invoice", "meth:BillingService.current_tenant_id", "Calls"
    )
    added_spurious_edge = DepEdge(
        "meth:BillingService.settle_invoice", "meth:BillingService._resolve_trace_id", "Calls"
    )
    assert added_tenant_edge not in graph.edges
    assert added_tenant_edge in final_cmg_graph.edges
    assert added_spurious_edge in final_nosc_graph.edges
    assert find_static_type_and_arity_errors(final_cmg_graph, check_override_signatures=True) == set()
    assert find_static_type_and_arity_errors(iter_graph, check_override_signatures=True) == set()

    assert s_cmg_var[:3] == (8, 0, 0), f"Expected exact (8, 0, 0), got {s_cmg_var}"
    assert cmg_var_spurious == 0
    assert cmg_nosc_pred == ground_truth_derived and cmg_nosc_spurious == 1
    assert s_cmg_strict[:3] == (8, 1, 0), f"Expected strict MMS to flag widened caller only: {s_cmg_strict}"
    assert build_repair_1pass == {"meth:BillingService.settle_invoice", "init:SessionToken.__init__"}
    assert s_build_1pass[:3] == (2, 0, 6)
    assert build_repair_iter == {
        "meth:BillingService.settle_invoice",
        "init:SessionToken.__init__",
        "meth:StripeGateway.charge",
    }
    assert s_build_iter[:3] == (3, 0, 5)
    assert "init:BillingService.__init__" not in grep_1_pred
    assert "fn:build_checkout_pipeline" not in grep_1_pred
    assert "fn:archive_charge_notes" in grep_1_pred
    assert "fn:render_invoice_line" in grep_1_pred

    return {
        "cmg_variance_aware": (*s_cmg_var, cmg_var_spurious),
        "cmg_table1_strict": (*s_cmg_strict, 0),
        "cmg_no_spatial_ctx": (*score(cmg_nosc_pred), cmg_nosc_spurious),
        "build_repair_1pass": (*s_build_1pass, 0),
        "build_repair_iter_strict": (*s_build_iter, 0),
        "lexical_grep_1hop": (*s_grep1, 0),
        "lexical_grep_2hop": (*s_grep2, 0),
        "dynamic_edges_initial_to_final": (len(graph.edges), len(final_cmg_graph.edges)),
    }


# ============================================================================
# Probe 2: Exact Aider@5dc9490b Call-Only RepoMap vs. PEP-484 Extension & BM25
# ============================================================================


@dataclass(frozen=True, order=True)
class SymbolTag:
    rel_fname: str
    fname: str
    line: int
    name: str
    kind: str  # "def" | "ref"


SPECIAL_ROOT_FILENAMES = frozenset(
    {"README.md", "pyproject.toml", "setup.py", "Cargo.toml", "package.json", "Makefile"}
)


def filter_important_files(rel_fnames: Iterable[str]) -> list[str]:
    """Matches `aider.special.filter_important_files` root metadata check."""
    return [fn for fn in rel_fnames if fn in SPECIAL_ROOT_FILENAMES]


def extract_aider_upstream_python_tags(rel_fname: str, source: str) -> list[SymbolTag]:
    """Exact port of `Aider-AI/aider@5dc9490b` `python-tags.scm:1-14` + `repomap.py:317-363`.

    In upstream `python-tags.scm`, the ONLY `@name.reference.*` pattern is `(call ...)`:
    neither `ImportFrom` bindings nor PEP-484 type annotations emit `"ref"` tags. And in
    `repomap.py:338-341`, `if "ref" in saw: return` skips the Pygments `Token.Name` fallback
    whenever the file contains even a single call expression!
    """
    tree = ast.parse(source)
    tags: list[SymbolTag] = []
    saw: set[str] = set()

    # `python-tags.scm:1`: `(module (expression_statement (assignment left: (identifier) @name.definition.constant)))`
    for stmt in tree.body:
        if isinstance(stmt, ast.Assign):
            for tgt in stmt.targets:
                if isinstance(tgt, ast.Name):
                    saw.add("def")
                    tags.append(SymbolTag(rel_fname, rel_fname, stmt.lineno, tgt.id, "def"))

    # `python-tags.scm:3-14`: `class_definition`, `function_definition`, and `call` ONLY.
    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            saw.add("def")
            tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.name, "def"))
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                saw.add("ref")
                tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.func.id, "ref"))
            elif isinstance(node.func, ast.Attribute):
                saw.add("ref")
                tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.func.attr, "ref"))

    # `repomap.py:338-341`: early return skips Pygments backfill whenever `"ref" in saw`!
    if ("ref" in saw) or ("def" not in saw):
        return sorted(tags)

    # `repomap.py:347-363`: Pygments `Token.Name` backfill for pure def-only files with zero calls.
    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type == tokenize.NAME and not keyword.iskeyword(tok.string):
            tags.append(SymbolTag(rel_fname, rel_fname, -1, tok.string, "ref"))
    return tags


def extract_pep484_and_import_python_tags(rel_fname: str, source: str) -> list[SymbolTag]:
    """Counterfactual extension (`Basis: derived`): adds PEP-484 annotations + `ImportFrom` refs."""
    tree = ast.parse(source)
    tags: list[SymbolTag] = []

    for stmt in tree.body:
        if isinstance(stmt, ast.Assign):
            for tgt in stmt.targets:
                if isinstance(tgt, ast.Name):
                    tags.append(SymbolTag(rel_fname, rel_fname, stmt.lineno, tgt.id, "def"))

    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.name, "def"))
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.id, "ref"))
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load):
            tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, node.attr, "ref"))
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                tags.append(SymbolTag(rel_fname, rel_fname, node.lineno, alias.name, "ref"))

    return sorted(tags)


def pagerank_multidigraph(
    nodes: Sequence[str],
    edges: Sequence[tuple[str, str, float, str]],
    personalization: dict[str, float] | None,
    alpha: float = 0.85,
    max_iter: int = 200,
    tol: float = 1.0e-11,
) -> dict[str, float]:
    """Exact pure-stdlib match to `networkx.pagerank(G, weight='weight', personalization=p, dangling=p)`."""
    nodelist = sorted(set(nodes))
    n_nodes = len(nodelist)
    if n_nodes == 0:
        return {}

    if personalization:
        p_vec = {n: float(personalization.get(n, 0.0)) for n in nodelist}
        p_sum = sum(p_vec.values())
        if p_sum == 0.0:
            raise ZeroDivisionError("Personalization sum is zero on graph nodes")
        p_vec = {n: v / p_sum for n, v in p_vec.items()}
        dangling_weights = dict(p_vec)
    else:
        p_vec = {n: 1.0 / n_nodes for n in nodelist}
        dangling_weights = dict(p_vec)

    out_adj: dict[str, list[tuple[str, float]]] = {n: [] for n in nodelist}
    out_sum: dict[str, float] = {n: 0.0 for n in nodelist}
    for src, dst, w, _ident in edges:
        out_adj[src].append((dst, w))
        out_sum[src] += w

    dangling_nodes = [n for n in nodelist if out_sum[n] == 0.0]
    x = dict(p_vec)

    for _ in range(max_iter):
        x_prev = x
        danglesum = alpha * sum(x_prev[n] for n in dangling_nodes)
        x = {
            n: danglesum * dangling_weights[n] + (1.0 - alpha) * p_vec[n]
            for n in nodelist
        }
        for src in nodelist:
            tot = out_sum[src]
            if tot > 0.0:
                scale = alpha * x_prev[src] / tot
                for dst, w in out_adj[src]:
                    x[dst] += scale * w
        err = sum(abs(x[n] - x_prev[n]) for n in nodelist)
        if err < n_nodes * tol:
            return x
    raise RuntimeError("PageRank failed to converge")


def render_signature_skeleton(rel_fname: str, source: str, target_lines: set[int]) -> str:
    """Renders syntactically valid elided class/function signature skeletons (`TreeContext` analogue)."""
    rendered: list[str] = [f"# {rel_fname}:"]
    if not target_lines:
        body = "\n".join(rendered) + "\n"
        ast.parse(body)
        return body

    tree = ast.parse(source)
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.lineno in target_lines:
            bases = f"({', '.join(ast.unparse(b) for b in node.bases)})" if node.bases else ""
            rendered.append(f"class {node.name}{bases}:")
            field_lines: list[str] = []
            for stmt in node.body:
                if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    field_lines.append(f"    {stmt.target.id}: {ast.unparse(stmt.annotation)}")
                elif isinstance(stmt, ast.FunctionDef) and stmt.lineno in target_lines:
                    sig = ast.unparse(stmt.args)
                    ret = f" -> {ast.unparse(stmt.returns)}" if stmt.returns else ""
                    field_lines.append(f"    def {stmt.name}({sig}){ret}: ...")
            if not field_lines:
                field_lines.append("    ...")
            rendered.extend(field_lines)
        elif isinstance(node, ast.FunctionDef) and node.lineno in target_lines:
            sig = ast.unparse(node.args)
            ret = f" -> {ast.unparse(node.returns)}" if node.returns else ""
            rendered.append(f"def {node.name}({sig}){ret}: ...")
    body = "\n".join(rendered) + "\n"
    ast.parse(body)  # Guarantee every rendered skeleton fragment is valid Python syntax!
    return body


def _extract_explicit_imports(source: str) -> set[tuple[str, str]]:
    """Returns `(module_py_filename, imported_symbol)` pairs for import-scoped edge filtering."""
    tree = ast.parse(source)
    out: set[tuple[str, str]] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            target_file = f"{node.module.replace('.', '/')}.py"
            for alias in node.names:
                out.add((target_file, alias.name))
    return out


def repomap_rank_and_pack(
    repo_files: dict[str, str],
    chat_fnames: set[str],
    mentioned_fnames: set[str],
    mentioned_idents: set[str],
    max_map_tokens: int,
    *,
    tag_mode: str,  # "aider_upstream" | "pep484_extension"
    import_scoped: bool = False,
) -> tuple[list[tuple[tuple[str, str], float]], str, int]:
    """Executes `aider/repomap.py:365-706` ranking + packing under `tag_mode`."""
    defines: dict[str, set[str]] = defaultdict(set)
    references: dict[str, list[str]] = defaultdict(list)
    definitions: dict[tuple[str, str], set[SymbolTag]] = defaultdict(set)
    explicit_imports: dict[str, set[tuple[str, str]]] = {}
    personalization: dict[str, float] = {}

    fnames = sorted(repo_files.keys())
    other_fnames = sorted(set(fnames) - set(chat_fnames))
    chat_rel_fnames: set[str] = set()
    personalize = 100.0 / len(fnames)

    extractor = (
        extract_aider_upstream_python_tags
        if tag_mode == "aider_upstream"
        else extract_pep484_and_import_python_tags
    )

    for rel_fname in fnames:
        explicit_imports[rel_fname] = _extract_explicit_imports(repo_files[rel_fname])
        current_pers = 0.0
        if rel_fname in chat_fnames:
            current_pers += personalize
            chat_rel_fnames.add(rel_fname)
        if rel_fname in mentioned_fnames:
            current_pers = max(current_pers, personalize)

        path_obj = PurePosixPath(rel_fname)
        components_to_check = set(path_obj.parts) | {path_obj.name, path_obj.stem}
        if components_to_check & mentioned_idents:
            current_pers += personalize
        if current_pers > 0.0:
            personalization[rel_fname] = current_pers

        for tag in extractor(rel_fname, repo_files[rel_fname]):
            if tag.kind == "def":
                defines[tag.name].add(rel_fname)
                definitions[(rel_fname, tag.name)].add(tag)
            elif tag.kind == "ref":
                references[tag.name].append(rel_fname)

    if not references:
        references = {k: sorted(v) for k, v in defines.items()}

    idents = sorted(set(defines.keys()) & set(references.keys()))
    graph_nodes: set[str] = set()
    graph_edges: list[tuple[str, str, float, str]] = []

    # L475-479: 0.1 self-edge for definitions with zero references.
    for ident in sorted(defines.keys()):
        if ident in references:
            continue
        for definer in sorted(defines[ident]):
            graph_nodes.add(definer)
            graph_edges.append((definer, definer, 0.1, ident))

    # L481-515: Specificity-weighted MultiDiGraph edges.
    for ident in idents:
        definers = sorted(defines[ident])
        mul = 1.0
        is_snake = ("_" in ident) and any(c.isalpha() for c in ident)
        is_kebab = ("-" in ident) and any(c.isalpha() for c in ident)
        is_camel = any(c.isupper() for c in ident) and any(c.islower() for c in ident)
        if ident in mentioned_idents:
            mul *= 10.0
        if (is_snake or is_kebab or is_camel) and len(ident) >= 8:
            mul *= 10.0
        if ident.startswith("_"):
            mul *= 0.1
        if len(definers) > 5:
            mul *= 0.1

        for referencer, num_refs in sorted(Counter(references[ident]).items()):
            for definer in definers:
                if import_scoped and referencer != definer:
                    if (definer, ident) not in explicit_imports[referencer]:
                        continue
                use_mul = mul * 50.0 if referencer in chat_rel_fnames else mul
                weight = use_mul * math.sqrt(num_refs)
                graph_nodes.add(referencer)
                graph_nodes.add(definer)
                graph_edges.append((referencer, definer, weight, ident))

    try:
        ranked = pagerank_multidigraph(
            sorted(graph_nodes), graph_edges, personalization if personalization else None
        )
    except ZeroDivisionError:
        ranked = pagerank_multidigraph(sorted(graph_nodes), graph_edges, None)

    # L534-559: Redistribute source node PageRank across outgoing symbol edges.
    out_by_src: dict[str, list[tuple[str, float, str]]] = defaultdict(list)
    for src, dst, w, ident in graph_edges:
        out_by_src[src].append((dst, w, ident))

    ranked_definitions_acc: dict[tuple[str, str], float] = defaultdict(float)
    for src in sorted(graph_nodes):
        src_rank = ranked[src]
        total_weight = sum(w for _dst, w, _ident in out_by_src[src])
        if total_weight > 0.0:
            for dst, w, ident in out_by_src[src]:
                ranked_definitions_acc[(dst, ident)] += src_rank * w / total_weight

    ranked_definitions = sorted(
        ranked_definitions_acc.items(),
        reverse=True,
        key=lambda item: (round(item[1], 12), item[0]),
    )

    ranked_tags: list[SymbolTag | tuple[str]] = []
    for (fname, ident), _rank in ranked_definitions:
        if fname in chat_rel_fnames:
            continue
        ranked_tags.extend(sorted(definitions.get((fname, ident), set())))

    # L560-573: Append `(fname,)` fallback entries for `other_fnames` without included definitions.
    rel_other_fnames_without_tags = set(other_fnames)
    fnames_already_included = {rt[0] if isinstance(rt, tuple) else rt.rel_fname for rt in ranked_tags}
    top_rank = sorted(((rank, node) for node, rank in ranked.items()), reverse=True)
    for _rank, fname in top_rank:
        if fname in rel_other_fnames_without_tags:
            rel_other_fnames_without_tags.remove(fname)
        if fname not in fnames_already_included:
            ranked_tags.append((fname,))
    for fname in sorted(rel_other_fnames_without_tags):
        ranked_tags.append((fname,))

    # L656-662: Prepend `filter_important_files(other_rel_fnames)` before binary search.
    ranked_tags_fnames = {rt[0] if isinstance(rt, tuple) else rt.rel_fname for rt in ranked_tags}
    special_entries: list[SymbolTag | tuple[str]] = [
        (fn,) for fn in filter_important_files(other_fnames) if fn not in ranked_tags_fnames
    ]
    ranked_tags = special_entries + ranked_tags

    # L666-706 & L748-784: Binary search over prefix `middle` with `ok_err = 0.15`.
    def tags_to_tree(prefix: Sequence[SymbolTag | tuple[str]]) -> str:
        by_file_lines: dict[str, set[int]] = {}
        for item in prefix:
            fn = item[0] if isinstance(item, tuple) else item.rel_fname
            if fn in chat_rel_fnames:
                continue
            by_file_lines.setdefault(fn, set())
            if isinstance(item, SymbolTag):
                by_file_lines[fn].add(item.line)
        return "\n".join(
            render_signature_skeleton(fn, repo_files[fn], lines)
            for fn, lines in sorted(by_file_lines.items())
        )

    def token_count(text: str) -> int:
        return max(1, (len(text) + 3) // 4) if text else 0

    num_tags = len(ranked_tags)
    lower_bound = 0
    upper_bound = num_tags
    best_tree = ""
    best_tree_tokens = 0
    middle = min(int(max_map_tokens // 25), num_tags)
    ok_err = 0.15

    while lower_bound <= upper_bound:
        tree = tags_to_tree(ranked_tags[:middle])
        num_tokens = token_count(tree)
        pct_err = abs(num_tokens - max_map_tokens) / max_map_tokens
        if (num_tokens <= max_map_tokens and num_tokens > best_tree_tokens) or pct_err < ok_err:
            best_tree = tree
            best_tree_tokens = num_tokens
            if pct_err < ok_err:
                break
        if num_tokens < max_map_tokens:
            lower_bound = middle + 1
        else:
            upper_bound = middle - 1
        middle = int((lower_bound + upper_bound) // 2)

    return ranked_definitions, best_tree, best_tree_tokens


def bm25_chunk_retrieve(
    repo_files: dict[str, str],
    exclude_files: set[str],
    query_text: str,
    chunk_chars: int = 150,
    top_k: int = 6,
    k1: float = 1.5,
    b: float = 0.75,
) -> list[tuple[str, str, float]]:
    """Fixed-width 150-char chunk BM25 retriever replicating Blinn et al. (OOPSLA 2024, §2.8.5)."""
    tok_re = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
    chunks: list[tuple[str, str, list[str]]] = []
    for fname in sorted(repo_files.keys()):
        if fname in exclude_files:
            continue
        text = repo_files[fname]
        for idx in range(0, len(text), chunk_chars):
            piece = text[idx : idx + chunk_chars]
            toks = [t.lower() for t in tok_re.findall(piece)]
            if toks:
                chunks.append((fname, piece, toks))

    n_docs = len(chunks)
    avgdl = sum(len(toks) for _, _, toks in chunks) / n_docs
    df: Counter[str] = Counter()
    for _, _, toks in chunks:
        for term in set(toks):
            df[term] += 1

    q_terms = [t.lower() for t in tok_re.findall(query_text)]
    scored: list[tuple[str, str, float]] = []
    for fname, piece, toks in chunks:
        tf = Counter(toks)
        dl = len(toks)
        score = 0.0
        for qt in q_terms:
            if tf[qt] == 0:
                continue
            idf = math.log(1.0 + (n_docs - df[qt] + 0.5) / (df[qt] + 0.5))
            denom = tf[qt] + k1 * (1.0 - b + b * dl / avgdl)
            score += idf * (tf[qt] * (k1 + 1.0)) / denom
        scored.append((fname, piece, score))

    scored.sort(key=lambda item: (-round(item[2], 12), item[0], item[1]))
    return scored[:top_k]


def run_probe_2_repomap() -> dict[str, object]:
    """Evaluates upstream Aider@5dc9490b RepoMap, PEP-484+ImportFrom PPR, and BM25 on an unfilled hole."""
    # Exact same incomplete typed hole (`...` inside `update`) given symmetrically to ALL methods!
    repo_files: dict[str, str] = {
        "emoji_app.py": (
            "from canvas_types import CanvasGrid\n"
            "from canvas_ops import apply_brush_stroke, clear_canvas_grid\n"
            "from util_a import get\n\n"
            "class Action:\n"
            "    kind: str\n"
            "    row: int\n"
            "    col: int\n\n"
            "class Model:\n"
            "    grid: CanvasGrid\n"
            "    active_brush: str\n\n"
            "def init_model(grid: CanvasGrid) -> Model:\n"
            "    _ = get(grid)\n"
            "    return Model()\n\n"
            "def update(model: Model, action: Action) -> Model:\n"
            "    ...\n"
        ),
        "canvas_types.py": (
            "from cell_stamp import CellStamp\n\n"
            "class CanvasGrid:\n"
            "    width: int\n"
            "    height: int\n"
            "    cells: list[CellStamp]\n"
        ),
        "cell_stamp.py": (
            "from palette_color import PaletteColor\n\n"
            "class CellStamp:\n"
            "    glyph: str\n"
            "    tint: PaletteColor\n"
        ),
        "palette_color.py": (
            "class PaletteColor:\n"
            "    hue_deg: int\n"
            "    alpha_pct: int\n"
        ),
        "canvas_ops.py": (
            "from canvas_types import CanvasGrid\n\n"
            "def _normalize_coord(coord: int) -> int:\n"
            "    return max(0, coord)\n\n"
            "def apply_brush_stroke(state: object, grid: CanvasGrid, row: int) -> object:\n"
            "    _ = _normalize_coord(row)\n"
            "    return state\n\n"
            "def clear_canvas_grid(grid: CanvasGrid) -> CanvasGrid:\n"
            "    return grid\n"
        ),
        "todo_app.py": (
            "class Action:\n"
            "    kind: str\n"
            "    row: int\n"
            "    col: int\n\n"
            "class Model:\n"
            "    tasks: list[str]\n\n"
            "def init_model() -> Model:\n"
            "    return Model()\n\n"
            "def update(model: Model, action: Action) -> Model:\n"
            "    # Model and Action update handler for Todo Model state\n"
            "    return model\n"
        ),
        "booking_app.py": (
            "class Action:\n"
            "    kind: str\n"
            "    row: int\n"
            "    col: int\n\n"
            "class Model:\n"
            "    bookings: list[int]\n\n"
            "def init_model() -> Model:\n"
            "    return Model()\n\n"
            "def update(model: Model, action: Action) -> Model:\n"
            "    # Booking Model and Action transition update\n"
            "    return model\n"
        ),
        "util_a.py": "def get(x: object) -> object:\n    return x\n",
        "util_b.py": "def get(x: object) -> object:\n    return x\n",
        "util_c.py": "def get(x: object) -> object:\n    return x\n",
        "util_d.py": "def get(x: object) -> object:\n    return x\n",
        "util_e.py": "def get(x: object) -> object:\n    return x\n",
        "util_f.py": "def get(x: object) -> object:\n    return x\n",
    }

    type_targets = ("CanvasGrid", "CellStamp", "PaletteColor")
    all_targets = ("CanvasGrid", "CellStamp", "PaletteColor", "apply_brush_stroke", "clear_canvas_grid")
    required_pairs = {
        ("canvas_types.py", "CanvasGrid"),
        ("cell_stamp.py", "CellStamp"),
        ("palette_color.py", "PaletteColor"),
        ("canvas_ops.py", "apply_brush_stroke"),
        ("canvas_ops.py", "clear_canvas_grid"),
    }

    # 1. Exact upstream Aider@5dc9490b call-only Python RepoMap (`python-tags.scm` + `L338` early return).
    up_defs, up_skeleton, up_tokens = repomap_rank_and_pack(
        repo_files=repo_files,
        chat_fnames={"emoji_app.py"},
        mentioned_fnames=set(),
        mentioned_idents=set(),
        max_map_tokens=95,
        tag_mode="aider_upstream",
        import_scoped=False,
    )
    up_non_chat = [item for item in up_defs if item[0][0] != "emoji_app.py"]
    up_rank_dict = dict(up_non_chat)
    up_types_recovered = {
        sym for sym in type_targets if f"class {sym}" in up_skeleton and up_rank_dict.get(
            next(pair for pair in required_pairs if pair[1] == sym), 0.0
        ) > 0.0
    }
    up_all_recovered = {
        sym for sym in all_targets if (f"class {sym}" in up_skeleton or f"def {sym}" in up_skeleton)
    }
    up_skeleton_confounders = sum(
        1 for fn in ("todo_app.py", "booking_app.py") if f"# {fn}:" in up_skeleton
    )
    up_confounder_mass = sum(
        sc for (fn, _sym), sc in up_non_chat if fn in {"todo_app.py", "booking_app.py"}
    )

    # 2. Counterfactual extension (`Basis: derived`): PEP-484 annotations + `ImportFrom` refs
    # (`import_scoped=False` vs. `import_scoped=True`).
    ext_defs, ext_skeleton, ext_tokens = repomap_rank_and_pack(
        repo_files=repo_files,
        chat_fnames={"emoji_app.py"},
        mentioned_fnames=set(),
        mentioned_idents=set(),
        max_map_tokens=95,
        tag_mode="pep484_extension",
        import_scoped=False,
    )
    scoped_defs, scoped_skeleton, scoped_tokens = repomap_rank_and_pack(
        repo_files=repo_files,
        chat_fnames={"emoji_app.py"},
        mentioned_fnames=set(),
        mentioned_idents=set(),
        max_map_tokens=95,
        tag_mode="pep484_extension",
        import_scoped=True,
    )

    ext_non_chat = [item for item in ext_defs if item[0][0] != "emoji_app.py"]
    scoped_non_chat = [item for item in scoped_defs if item[0][0] != "emoji_app.py"]
    ext_rank_dict = dict(ext_non_chat)
    scoped_top5 = {item[0] for item in scoped_non_chat[:5]}

    ext_recovered = {
        sym for sym in all_targets if f"class {sym}" in ext_skeleton or f"def {sym}" in ext_skeleton
    }
    scoped_recovered = {
        sym for sym in all_targets if f"class {sym}" in scoped_skeleton or f"def {sym}" in scoped_skeleton
    }
    ext_skeleton_confounders = sum(
        1 for fn in ("todo_app.py", "booking_app.py") if f"# {fn}:" in ext_skeleton
    )
    scoped_skeleton_confounders = sum(
        1 for fn in ("todo_app.py", "booking_app.py") if f"# {fn}:" in scoped_skeleton
    )
    ext_unscoped_mass = sum(
        sc for (fn, _sym), sc in ext_non_chat if fn in {"todo_app.py", "booking_app.py"}
    )
    scoped_mass = sum(
        sc for (fn, _sym), sc in scoped_non_chat if fn in {"todo_app.py", "booking_app.py"}
    )

    # 3. Matched-query 6x150-char BM25 given the EXACT SAME complete unfilled `emoji_app.py` file!
    bm25_top6 = bm25_chunk_retrieve(
        repo_files=repo_files,
        exclude_files={"emoji_app.py"},
        query_text=repo_files["emoji_app.py"],
        chunk_chars=150,
        top_k=6,
    )
    bm25_concat = "\n".join(piece for _fn, piece, _sc in bm25_top6)
    bm25_types_recovered = {sym for sym in type_targets if f"class {sym}" in bm25_concat}
    bm25_all_recovered = {
        sym for sym in all_targets if f"class {sym}" in bm25_concat or f"def {sym}" in bm25_concat
    }
    bm25_confounder_chunks = sum(
        1 for fn, _p, _s in bm25_top6 if fn in {"todo_app.py", "booking_app.py"}
    )
    bm25_broken_syntax = 0
    for _fn, piece, _sc in bm25_top6:
        try:
            ast.parse(piece)
        except SyntaxError:
            bm25_broken_syntax += 1

    get_hub_score = ext_rank_dict.get(("util_a.py", "get"), 0.0)
    private_score = ext_rank_dict.get(("canvas_ops.py", "_normalize_coord"), 0.0)
    canvas_grid_score = ext_rank_dict[("canvas_types.py", "CanvasGrid")]

    # Assertions verifying the upstream call-only blind spot AND the counterfactual extension.
    assert "apply_brush_stroke(" not in repo_files["emoji_app.py"], "Zero oracle call leakage allowed!"
    assert up_rank_dict.get(("canvas_types.py", "CanvasGrid"), 0.0) == 0.0
    assert up_rank_dict.get(("cell_stamp.py", "CellStamp"), 0.0) == 0.0
    assert up_rank_dict.get(("palette_color.py", "PaletteColor"), 0.0) == 0.0
    assert len(up_types_recovered) == 0 and len(up_all_recovered) == 0
    assert up_skeleton_confounders == 2 and up_confounder_mass > 0.40

    assert {item[0] for item in ext_non_chat[:5]} == required_pairs
    assert scoped_top5 == required_pairs
    assert len(ext_recovered) == 5 and len(scoped_recovered) == 5
    assert ext_skeleton_confounders == 0 and scoped_skeleton_confounders == 0
    assert ext_unscoped_mass > 0.0 and scoped_mass == 0.0
    assert canvas_grid_score / get_hub_score > 100.0
    assert canvas_grid_score / private_score > 20.0

    assert len(bm25_types_recovered) == 0
    assert bm25_confounder_chunks == 4
    assert bm25_top6[0][0] in {"todo_app.py", "booking_app.py"}
    assert bm25_broken_syntax == 6

    return {
        "upstream_aider_type_recall": f"{len(up_types_recovered)}/3",
        "upstream_aider_total_recall": f"{len(up_all_recovered)}/5",
        "upstream_aider_tokens": up_tokens,
        "upstream_aider_skeleton_confounders": up_skeleton_confounders,
        "upstream_aider_confounder_mass": round(up_confounder_mass, 6),
        "pep484_ext_top5": [(fn, sym, round(sc, 6)) for (fn, sym), sc in scoped_non_chat[:5]],
        "pep484_ext_recall": f"{len(scoped_recovered)}/5",
        "pep484_ext_tokens": scoped_tokens,
        "pep484_unscoped_confounder_mass": round(ext_unscoped_mass, 6),
        "pep484_import_scoped_mass": round(scoped_mass, 6),
        "hub_suppression_ratio": round(canvas_grid_score / get_hub_score, 2),
        "private_suppression_ratio": round(canvas_grid_score / private_score, 2),
        "bm25_type_recall": f"{len(bm25_types_recovered)}/3",
        "bm25_total_recall": f"{len(bm25_all_recovered)}/5",
        "bm25_confounder_chunks": f"{bm25_confounder_chunks}/6",
        "bm25_broken_syntax_chunks": f"{bm25_broken_syntax}/6",
    }


# ============================================================================
# Probe 3: Sum-vs-Product Illegal-State Cardinality & Strom-Yemini Semilattice
# ============================================================================


@dataclass(frozen=True)
class ProtocolSpec:
    name: str
    num_bool_flags: int
    nullable_field_cardinalities: tuple[int, ...]
    variants: tuple[tuple[str, tuple[int, ...], tuple[bool, ...]], ...]


def verify_cardinality_explosion(spec: ProtocolSpec) -> tuple[int, int, int, float]:
    """Verifies `2^b * prod(|D_i| + 1) - sum_s prod(|D_f|)` algebraically and by enumeration."""
    b = spec.num_bool_flags
    d_sizes = spec.nullable_field_cardinalities

    prod_formula = (1 << b) * math.prod(sz + 1 for sz in d_sizes)
    sum_formula = sum(
        math.prod(d_sizes[idx] for idx in active_fields)
        for _vname, active_fields, _flags in spec.variants
    )
    illegal_formula = prod_formula - sum_formula

    bool_domain = list(itertools.product([False, True], repeat=b))
    field_domains = [[None, *range(sz)] for sz in d_sizes]
    all_product_states = list(itertools.product(bool_domain, *field_domains))
    assert len(all_product_states) == prod_formula

    valid_predicate_matches = 0
    for state in all_product_states:
        flags = state[0]
        fields = state[1:]
        matched_variants = 0
        for _vname, active_idxs, expected_flags in spec.variants:
            if flags != expected_flags:
                continue
            active_set = set(active_idxs)
            if all(
                (fields[i] is not None) if (i in active_set) else (fields[i] is None)
                for i in range(len(d_sizes))
            ):
                matched_variants += 1
        assert matched_variants <= 1, "Disjoint sum variants cannot overlap"
        if matched_variants == 1:
            valid_predicate_matches += 1

    assert valid_predicate_matches == sum_formula
    assert len(all_product_states) - valid_predicate_matches == illegal_formula
    return prod_formula, sum_formula, illegal_formula, illegal_formula / prod_formula


@dataclass(frozen=True)
class TypestateOp:
    name: str
    required_state: str
    normal_post: str
    exc_post: str | None = None


@dataclass(frozen=True)
class BasicBlock:
    block_id: str
    ops: tuple[TypestateOp, ...]
    normal_succs: tuple[str, ...]
    exc_succ: str | None = None


class StromYeminiLattice:
    """Finite partial-order lower semilattice `(S, <=, meet, bottom)` with downward coercions."""

    def __init__(
        self,
        states: Sequence[str],
        bottom: str,
        direct_lower_coercions: dict[tuple[str, str], str],
    ) -> None:
        self.states = tuple(states)
        assert len(set(self.states)) == len(self.states), "Duplicate typestate names"
        assert bottom in self.states, f"Unknown bottom state {bottom}"
        self.bottom = bottom
        self.direct_coercions = dict(direct_lower_coercions)
        self.leq_map: dict[str, set[str]] = {s: {s} for s in self.states}

        changed = True
        while changed:
            changed = False
            for hi, lo in self.direct_coercions:
                assert hi in self.leq_map and lo in self.leq_map
                before = len(self.leq_map[hi])
                self.leq_map[hi] |= self.leq_map[lo]
                if len(self.leq_map[hi]) != before:
                    changed = True

        # Verify partial-order antisymmetry, global bottom, and unique GLB (`meet`) over `S x S`.
        for a in self.states:
            assert bottom in self.leq_map[a], f"{bottom} is not <= {a}"
            for b in self.states:
                if a != b:
                    assert not (self.leq(a, b) and self.leq(b, a)), f"Cycle between {a} and {b}"
                _ = self.meet(a, b)

    def leq(self, a: str, b: str) -> bool:
        """Returns True iff `a <= b` (`b` can be coerced downward to `a`)."""
        return a in self.leq_map[b]

    def meet(self, a: str, b: str) -> str:
        """Unique greatest lower bound `a sqcap b` in `(S, <=)`."""
        common_lowers = self.leq_map[a] & self.leq_map[b]
        maximal = [
            c for c in common_lowers
            if all(not (c != d and self.leq(c, d)) for d in common_lowers)
        ]
        assert len(maximal) == 1, f"Non-unique GLB for ({a}, {b}): {maximal}"
        return maximal[0]

    def coercion_chain(self, src_hi: str, dst_lo: str) -> tuple[str, ...]:
        """Shortest deterministic downward cleanup coercion path from `src_hi` down to `dst_lo`."""
        assert self.leq(dst_lo, src_hi), f"Cannot coerce upward from {src_hi} to {dst_lo}"
        if src_hi == dst_lo:
            return ()
        queue: deque[tuple[str, tuple[str, ...]]] = deque([(src_hi, ())])
        visited = {src_hi}
        while queue:
            cur, path = queue.popleft()
            next_steps = sorted(
                (lo, op_name) for (hi, lo), op_name in self.direct_coercions.items() if hi == cur
            )
            for lo, op_name in next_steps:
                new_path = (*path, op_name)
                if lo == dst_lo:
                    return new_path
                if lo not in visited and self.leq(dst_lo, lo):
                    visited.add(lo)
                    queue.append((lo, new_path))
        raise RuntimeError(f"Missing coercion path from {src_hi} to {dst_lo}")


def analyze_cfg_typestate(
    lattice: StromYeminiLattice,
    blocks: dict[str, BasicBlock],
    entry_id: str,
    entry_state: str,
) -> tuple[dict[str, str], dict[str, tuple[str, ...]], list[str]]:
    """Forward Strom-Yemini dataflow analyzer with intra-block, normal-edge, and per-throw coercions."""
    in_state: dict[str, str] = {entry_id: entry_state}
    # Keys describe exact coercion insertion sites:
    #   - `"<entry>->B"` (entry edge if a loop back-edge lowers `in_state[entry_id]`)
    #   - `"B[i]:op(pre)"` (intra-block pre-operation downward coercion when `op.required_state < cur`)
    #   - `"B->S(normal)"` (inter-block normal control-flow edge)
    #   - `"B[i]:op->E(exc)"` (per-instruction exception edge from `op.exc_post` to `in_state[E]`)
    normal_edge_out: dict[tuple[str, str], str] = {}
    exc_site_out: dict[tuple[str, int, str, str], str] = {}

    worklist: deque[str] = deque([entry_id])
    while worklist:
        bid = worklist.popleft()
        blk = blocks[bid]
        cur = in_state[bid]

        for idx, op in enumerate(blk.ops):
            if op.exc_post is not None and blk.exc_succ is not None:
                exc_site_out[(bid, idx, op.name, blk.exc_succ)] = op.exc_post
                prev_e = in_state.get(blk.exc_succ)
                merged_e = op.exc_post if prev_e is None else lattice.meet(prev_e, op.exc_post)
                if merged_e != prev_e:
                    in_state[blk.exc_succ] = merged_e
                    worklist.append(blk.exc_succ)
            cur = op.normal_post

        for succ in blk.normal_succs:
            normal_edge_out[(bid, succ)] = cur
            prev = in_state.get(succ)
            merged = cur if prev is None else lattice.meet(prev, cur)
            if merged != prev:
                in_state[succ] = merged
                worklist.append(succ)

    # Second pass at converged fixed-point `in_state`: verify preconditions & synthesize all coercions.
    errors: list[str] = []
    coercions: dict[str, tuple[str, ...]] = {}

    entry_chain = lattice.coercion_chain(entry_state, in_state[entry_id])
    if entry_chain:
        coercions[f"<entry>->{entry_id}"] = entry_chain

    for bid, blk in sorted(blocks.items()):
        if bid not in in_state:
            continue
        cur = in_state[bid]
        for idx, op in enumerate(blk.ops):
            if not lattice.leq(op.required_state, cur):
                errors.append(f"{bid}[{idx}]:{op.name} requires {op.required_state}, actual={cur}")
            elif cur != op.required_state:
                chain = lattice.coercion_chain(cur, op.required_state)
                if chain:
                    coercions[f"{bid}[{idx}]:{op.name}(pre)"] = chain
            cur = op.normal_post

    for (src, dst), src_out in sorted(normal_edge_out.items()):
        chain = lattice.coercion_chain(src_out, in_state[dst])
        if chain:
            coercions[f"{src}->{dst}(normal)"] = chain

    for (src, idx, op_name, exc_dst), exc_out in sorted(exc_site_out.items()):
        chain = lattice.coercion_chain(exc_out, in_state[exc_dst])
        if chain:
            coercions[f"{src}[{idx}]:{op_name}->{exc_dst}(exc)"] = chain

    return in_state, coercions, errors


def run_probe_3_typestate() -> dict[str, object]:
    """Verifies sum-vs-product illegal-state explosion and Strom-Yemini intra-block/per-throw meets."""
    conn_spec = ProtocolSpec(
        name="TransactionalConnection",
        num_bool_flags=3,
        nullable_field_cardinalities=(4, 4, 4),
        variants=(
            ("Disconnected", (), (False, False, False)),
            ("ConnectedUnauth", (0,), (True, False, False)),
            ("AuthenticatedIdle", (0, 1), (True, True, False)),
            ("InTransaction", (0, 1, 2), (True, True, True)),
        ),
    )
    cursor_spec = ProtocolSpec(
        name="ResultSetCursor",
        num_bool_flags=4,
        nullable_field_cardinalities=(3, 3),
        variants=(
            ("Closed", (), (False, False, False, False)),
            ("BeforeFirstOrAfterLast", (), (True, False, False, False)),
            ("PositionedRead", (0,), (True, True, False, False)),
            ("PositionedUpdatable", (0,), (True, True, False, True)),
            ("InsertRowStaging", (0, 1), (True, False, True, True)),
        ),
    )

    c_prod, c_sum, c_ill, c_frac = verify_cardinality_explosion(conn_spec)
    r_prod, r_sum, r_ill, r_frac = verify_cardinality_explosion(cursor_spec)
    assert (c_prod, c_sum, c_ill) == (1000, 85, 915)
    assert (r_prod, r_sum, r_ill) == (256, 17, 239)

    # Non-linear tree lower semilattice (Strom & Yemini 1986):
    #                 PreparedCommit
    #                       |
    #       ReadSnapshot  WriteStaged
    #            \          /
    #              OpenConn
    #                 |
    #               Closed (bottom)
    lattice = StromYeminiLattice(
        states=("Closed", "OpenConn", "ReadSnapshot", "WriteStaged", "PreparedCommit"),
        bottom="Closed",
        direct_lower_coercions={
            ("PreparedCommit", "WriteStaged"): "unprepare_tx",
            ("WriteStaged", "OpenConn"): "rollback_staged_write",
            ("ReadSnapshot", "OpenConn"): "release_snapshot_pin",
            ("OpenConn", "Closed"): "close_socket",
        },
    )
    assert lattice.meet("ReadSnapshot", "WriteStaged") == "OpenConn"
    assert lattice.meet("PreparedCommit", "Closed") == "Closed"

    op_open = TypestateOp("connect", "Closed", "OpenConn", exc_post="Closed")
    op_read_begin = TypestateOp("begin_read_snapshot", "OpenConn", "ReadSnapshot")
    # BOTH operations in `B_write` can throw from distinct typestates (`OpenConn` vs `WriteStaged`)!
    op_write_begin = TypestateOp("begin_write_tx", "OpenConn", "WriteStaged", exc_post="OpenConn")
    op_prepare = TypestateOp("prepare_commit", "WriteStaged", "PreparedCommit", exc_post="WriteStaged")
    op_ping = TypestateOp("ping_keepalive", "OpenConn", "OpenConn")
    op_close = TypestateOp("explicit_close", "OpenConn", "Closed")
    op_illegal_commit = TypestateOp("finalize_commit", "PreparedCommit", "OpenConn")

    valid_cfg = {
        "B_entry": BasicBlock("B_entry", (op_open,), ("B_read", "B_write", "B_abort_inline"), exc_succ="B_exit"),
        "B_read": BasicBlock("B_read", (op_read_begin,), ("B_join",)),
        "B_write": BasicBlock("B_write", (op_write_begin, op_prepare), ("B_join",), exc_succ="B_join"),
        # `B_abort_inline` closes directly after `prepare_commit`, exercising intra-block pre-op coercion!
        "B_abort_inline": BasicBlock("B_abort_inline", (op_write_begin, op_prepare, op_close), ("B_exit",)),
        "B_join": BasicBlock("B_join", (op_ping, op_close), ("B_exit",)),
        "B_exit": BasicBlock("B_exit", (), ()),
    }
    in_valid, coercions_valid, errs_valid = analyze_cfg_typestate(lattice, valid_cfg, "B_entry", "Closed")
    assert not errs_valid, f"Valid CFG should typecheck cleanly: {errs_valid}"
    assert in_valid["B_join"] == "OpenConn"
    assert in_valid["B_exit"] == "Closed"
    assert coercions_valid["B_read->B_join(normal)"] == ("release_snapshot_pin",)
    assert coercions_valid["B_write->B_join(normal)"] == ("unprepare_tx", "rollback_staged_write")
    # Per-throw-site exception coercion: `prepare_commit` throws in `WriteStaged` and MUST roll back,
    # even though `begin_write_tx` in the same block throws in `OpenConn`!
    assert coercions_valid["B_write[1]:prepare_commit->B_join(exc)"] == ("rollback_staged_write",)
    assert "B_write[0]:begin_write_tx->B_join(exc)" not in coercions_valid
    # Intra-block pre-operation downward coercion before `explicit_close` in `B_abort_inline`!
    assert coercions_valid["B_abort_inline[2]:explicit_close(pre)"] == (
        "unprepare_tx",
        "rollback_staged_write",
    )

    # Verify loop back-edge lowering `<entry>->L_head` coercion synthesis.
    loop_cfg = {
        "L_head": BasicBlock("L_head", (op_ping,), ("L_head", "L_done")),
        "L_done": BasicBlock("L_done", (op_close,), ()),
    }
    in_loop, coercions_loop, errs_loop = analyze_cfg_typestate(lattice, loop_cfg, "L_head", "ReadSnapshot")
    assert not errs_loop and in_loop["L_head"] == "OpenConn"
    assert coercions_loop["<entry>->L_head"] == ("release_snapshot_pin",)

    # Buggy CFG attempting `finalize_commit` after merging `ReadSnapshot` and `PreparedCommit`.
    buggy_cfg = dict(valid_cfg)
    buggy_cfg["B_join"] = BasicBlock("B_join", (op_illegal_commit, op_close), ("B_exit",))
    _in_bug, _coerc_bug, errs_bug = analyze_cfg_typestate(lattice, buggy_cfg, "B_entry", "Closed")
    assert errs_bug == ["B_join[0]:finalize_commit requires PreparedCommit, actual=OpenConn"]

    return {
        "conn_cardinality": (c_prod, c_sum, c_ill, round(c_frac * 100.0, 2)),
        "cursor_cardinality": (r_prod, r_sum, r_ill, round(r_frac * 100.0, 2)),
        "join_meet_state": in_valid["B_join"],
        "synthesized_coercions": {k: list(v) for k, v in coercions_valid.items()},
        "loop_entry_coercion": list(coercions_loop["<entry>->L_head"]),
        "caught_protocol_error": errs_bug[0],
    }


# ============================================================================
# Probe 4: Empirical Repair Accounting, Derived Markov Model & Anti-Bypass Gate
# ============================================================================


def invert_rational_matrix(mat: Sequence[Sequence[Fraction]]) -> list[list[Fraction]]:
    """Exact Gauss-Jordan matrix inversion over Q (`fractions.Fraction`)."""
    n = len(mat)
    aug = [
        [Fraction(mat[r][c]) for c in range(n)] + [Fraction(1 if r == c else 0) for c in range(n)]
        for r in range(n)
    ]
    for col in range(n):
        pivot = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if pivot is None:
            raise ValueError("Singular matrix in (I - Q) inversion")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        piv_val = aug[col][col]
        aug[col] = [val / piv_val for val in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                factor = aug[r][col]
                aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def solve_absorbing_markov_chain(
    q_mat: Sequence[Sequence[Fraction]],
    r_mat: Sequence[Sequence[Fraction]],
) -> tuple[list[list[Fraction]], list[list[Fraction]], list[Fraction]]:
    """Computes fundamental matrix N = (I - Q)^(-1), absorption matrix B = N*R, and E[steps] = N*1."""
    t_count = len(q_mat)
    a_count = len(r_mat[0])
    for i in range(t_count):
        row_sum = sum(q_mat[i]) + sum(r_mat[i])
        assert row_sum == Fraction(1, 1), f"Row {i} is not stochastic: {row_sum}"

    i_minus_q = [
        [Fraction(1 if r == c else 0) - q_mat[r][c] for c in range(t_count)]
        for r in range(t_count)
    ]
    n_mat = invert_rational_matrix(i_minus_q)

    for r in range(t_count):
        for c in range(t_count):
            entry = sum(i_minus_q[r][k] * n_mat[k][c] for k in range(t_count))
            assert entry == (Fraction(1, 1) if r == c else Fraction(0, 1))

    b_mat = [
        [sum(n_mat[i][k] * r_mat[k][j] for k in range(t_count)) for j in range(a_count)]
        for i in range(t_count)
    ]
    for i in range(t_count):
        assert sum(b_mat[i]) == Fraction(1, 1)

    expected_steps = [sum(n_mat[i]) for i in range(t_count)]
    return n_mat, b_mat, expected_steps


def mat_mul_rational(
    a: Sequence[Sequence[Fraction]], b: Sequence[Sequence[Fraction]]
) -> list[list[Fraction]]:
    rows, inner, cols = len(a), len(b), len(b[0])
    return [
        [sum(a[r][k] * b[k][c] for k in range(inner)) for c in range(cols)]
        for r in range(rows)
    ]


def strip_rust_comments_and_strings(src: str) -> str:
    """Replaces Rust line/block comments and string/raw-string literals with spaces."""
    out: list[str] = []
    i = 0
    n = len(src)
    while i < n:
        # Line comment `// ...`
        if src[i : i + 2] == "//":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        # Nested block comment `/* ... */`
        if src[i : i + 2] == "/*":
            depth = 1
            out.extend((" ", " "))
            i += 2
            while i < n and depth > 0:
                if src[i : i + 2] == "/*":
                    depth += 1
                    out.extend((" ", " "))
                    i += 2
                elif src[i : i + 2] == "*/":
                    depth -= 1
                    out.extend((" ", " "))
                    i += 2
                else:
                    out.append("\n" if src[i] == "\n" else " ")
                    i += 1
            continue
        # Raw string literal `r#*"..."#*`
        if src[i] == "r" and i + 1 < n and src[i + 1] in {"#", '"'}:
            j = i + 1
            hashes = 0
            while j < n and src[j] == "#":
                hashes += 1
                j += 1
            if j < n and src[j] == '"':
                closing = '"' + ("#" * hashes)
                end_idx = src.find(closing, j + 1)
                stop = n if end_idx == -1 else end_idx + len(closing)
                while i < stop:
                    out.append("\n" if src[i] == "\n" else " ")
                    i += 1
                continue
        # Standard string literal `"..."`
        if src[i] == '"':
            out.append(" ")
            i += 1
            while i < n:
                if src[i] == "\\" and i + 1 < n:
                    out.extend((" ", " "))
                    i += 2
                    continue
                ch = src[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
                if ch == '"':
                    break
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def check_rust_patch_anti_bypass_gate(locked_fn_sig: str, candidate_rust_src: str) -> tuple[bool, list[str]]:
    """Syntactic signature-lock + anti-bypass gate rejecting `todo!`, `unimplemented!`, `panic!`, and `unsafe`."""
    stripped = strip_rust_comments_and_strings(candidate_rust_src)
    violations: list[str] = []
    normalized_src = " ".join(stripped.split())
    normalized_sig = " ".join(locked_fn_sig.split())
    if normalized_sig not in normalized_src:
        violations.append("signature_mutated")
    if re.search(r"\b(?:todo|unimplemented|panic)\s*!", stripped):
        violations.append("diverging_stub_macro")
    if re.search(r"\bunsafe\b", stripped):
        violations.append("forbidden_unsafe_block")
    return (len(violations) == 0), violations


def run_probe_4_markov_repair() -> dict[str, object]:
    """Verifies primary-source RustAssistant/CRUST-Bench ratios and derived 4-absorbing-state Markov gating."""
    # 1. Primary-source rational accounting (`Basis: documentation`):
    # RustAssistant (Deligiannis et al., ICSE 2025, Table V, 182 top-100 crate commits):
    #   Cat 1 (55 unambiguous) + Cat 2 (41 developer-matching) + Cat 3 (29 behavior-preserving `const`/`pub`/trait)
    #   = 125/182 semantic-preserving compiles; Cat 4 = 9/182 runtime-corrupting compiles; 48/182 build failures.
    ra_sem_ok = Fraction(55 + 41 + 29, 182)
    ra_silent_corrupt = Fraction(9, 182)
    ra_build_fail = Fraction(48, 182)
    assert ra_sem_ok + ra_silent_corrupt + ra_build_fail == Fraction(1, 1)
    ra_compile_total = ra_sem_ok + ra_silent_corrupt
    ra_cond_corrupt = ra_silent_corrupt / ra_compile_total
    assert ra_compile_total == Fraction(134, 182)
    assert ra_cond_corrupt == Fraction(9, 134)  # Exact 6.7164%

    # CRUST-Bench (Khatry et al., COLM 2025, Table 4 — Claude Opus 4 empirical state proportions):
    # States: [BuildFail, BuildsFailsTests, BuildsPassesTests]
    pi_0 = [[Fraction(57, 100), Fraction(21, 100), Fraction(22, 100)]]
    p_comp_3 = [
        [Fraction(22, 57), Fraction(28, 57), Fraction(7, 57)],
        [Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    ]
    pi_after_comp = mat_mul_rational(pi_0, p_comp_3)[0]
    comp_build = pi_after_comp[1] + pi_after_comp[2]
    comp_test = pi_after_comp[2]
    assert (comp_build, comp_test) == (Fraction(78, 100), Fraction(29, 100))

    p_test_3 = [
        [Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
        [Fraction(13, 49), Fraction(25, 49), Fraction(11, 49)],
        [Fraction(0, 1), Fraction(0, 1), Fraction(1, 1)],
    ]
    pi_after_test = mat_mul_rational([pi_after_comp], p_test_3)[0]
    test_build = pi_after_test[1] + pi_after_test[2]
    test_pass = pi_after_test[2]
    assert (test_build, test_pass) == (Fraction(65, 100), Fraction(40, 100))
    assert test_build - comp_build == Fraction(-13, 100)

    # 2. Parameterized Absorbing Markov Chain (`Basis: derived` — analytical illustration):
    # Transient states: T0 = TypeMismatch, T1 = BorrowOrTraitError.
    # Absorbing states:
    #   A0 = VerifiedCorrect
    #   A1 = SyntacticBypassStub (`todo!`/`unimplemented!`/`unsafe`/mutated signature)
    #   A2 = NonStubSemanticCorruption (`{ Ok(()) }` / deleted statements / wrong match arms; passes AST gate!)
    #   A3 = BudgetExhausted
    # Note: In both states, `r_ok : r_nonstub_corrupt` is parameterized at `125 : 9` so that whenever
    # syntactic stubs (`A1`) are blocked, conditional non-stub corruption given compilation equals
    # `9 / (125 + 9) = 9/134 = 6.72%`, matching RustAssistant Table V!
    q_unguarded = [
        [Fraction(15, 100), Fraction(25, 100)],
        [Fraction(10, 100), Fraction(25, 100)],
    ]
    r_unguarded = [
        [Fraction(125, 400), Fraction(73, 400), Fraction(9, 400), Fraction(33, 400)],
        [Fraction(125, 800), Fraction(287, 800), Fraction(9, 800), Fraction(99, 800)],
    ]
    _n_u, b_u, steps_u = solve_absorbing_markov_chain(q_unguarded, r_unguarded)

    # Regime B (Syntactic Anti-Bypass Gate ONLY, without behavioral test oracle):
    # Derived directly by intercepting `A1 (SyntacticBypassStub)` transitions (`r[i][1] -> 0`) and
    # returning `4/5` of rejected stub attempts to transient retry `q[i][i]` (`1/5` to `BudgetExhausted`).
    # Crucially, `A2 (NonStubSemanticCorruption)` is NOT intercepted by syntactic AST checks!
    q_syn_gate: list[list[Fraction]] = []
    r_syn_gate: list[list[Fraction]] = []
    for i in range(2):
        blocked_stub = r_unguarded[i][1]
        q_row = list(q_unguarded[i])
        q_row[i] += Fraction(4, 5) * blocked_stub
        r_row = [
            r_unguarded[i][0],
            Fraction(0, 1),
            r_unguarded[i][2],
            r_unguarded[i][3] + Fraction(1, 5) * blocked_stub,
        ]
        q_syn_gate.append(q_row)
        r_syn_gate.append(r_row)
    _n_sg, b_sg, steps_sg = solve_absorbing_markov_chain(q_syn_gate, r_syn_gate)

    sg_compile_from_borrow = b_sg[1][0] + b_sg[1][2]
    sg_cond_silent_corrupt = b_sg[1][2] / sg_compile_from_borrow
    assert b_sg[1][1] == Fraction(0, 1), "Syntactic gate blocks `todo!`/`unsafe` stubs"
    assert b_sg[1][2] > Fraction(0, 1), "Syntactic gate CANNOT block non-stub semantic corruption!"
    assert sg_cond_silent_corrupt == Fraction(9, 134), "Exact 9/134 (6.72%) residual silent corruption!"

    # Regime C (Syntactic Gate + Held-Out Behavioral Contract Gate):
    # Intercepts BOTH `A1` and `A2`, returning `4/5` of rejected `A2` attempts to transient retry.
    q_full_gate: list[list[Fraction]] = []
    r_full_gate: list[list[Fraction]] = []
    for i in range(2):
        blocked_silent = r_syn_gate[i][2]
        q_row = list(q_syn_gate[i])
        q_row[i] += Fraction(4, 5) * blocked_silent
        r_row = [
            r_syn_gate[i][0],
            Fraction(0, 1),
            Fraction(0, 1),
            r_syn_gate[i][3] + Fraction(1, 5) * blocked_silent,
        ]
        q_full_gate.append(q_row)
        r_full_gate.append(r_row)
    _n_fg, b_fg, steps_fg = solve_absorbing_markov_chain(q_full_gate, r_full_gate)

    # Monte Carlo cross-check of `b_sg[1]` (`BorrowOrTraitError` under Syntactic Gate).
    rng = random.Random(20261122)
    mc_trials = 25000
    mc_counts = [0, 0, 0, 0]
    for _ in range(mc_trials):
        state = 1
        while True:
            u = rng.random()
            q0, q1 = float(q_syn_gate[state][0]), float(q_syn_gate[state][1])
            if u < q0:
                state = 0
            elif u < q0 + q1:
                state = 1
            else:
                u_abs = u - (q0 + q1)
                acc = 0.0
                for j in range(4):
                    acc += float(r_syn_gate[state][j])
                    if u_abs <= acc or j == 3:
                        mc_counts[j] += 1
                        break
                break
    mc_sg_ok = mc_counts[0] / mc_trials
    assert abs(mc_sg_ok - float(b_sg[1][0])) < 0.01

    # 3. Concrete verification of comment/string stripping & `{ Ok(()) }` non-stub limitation (`Basis: execution`).
    locked_sig = "pub fn push_checked(buf: &mut Vec<u8>, byte: u8, cap: usize) -> Result<(), CapacityErr>"
    ok_stub, v_stub = check_rust_patch_anti_bypass_gate(locked_sig, f"{locked_sig} {{ todo!() }}")
    ok_unsafe, v_unsafe = check_rust_patch_anti_bypass_gate(
        locked_sig, f"{locked_sig} {{ unsafe {{ buf.set_len(0); }} Ok(()) }}"
    )
    ok_sigmut, v_sigmut = check_rust_patch_anti_bypass_gate(
        locked_sig,
        "pub fn push_checked(buf: Vec<u8>, byte: u8, cap: usize) -> Result<(), CapacityErr> { Ok(()) }",
    )
    ok_comments_strings, v_comments_strings = check_rust_patch_anti_bypass_gate(
        locked_sig,
        (
            f"{locked_sig} {{\n"
            '    // unsafe todo!() in comment must not trigger false positive\n'
            '    /* nested /* panic!("ignored") */ comment */\n'
            '    let _msg = "unsafe { todo!() }";\n'
            '    let _raw = r#"unimplemented!("raw")"#;\n'
            "    if buf.len() >= cap { return Err(CapacityErr); }\n"
            "    buf.push(byte);\n"
            "    Ok(())\n"
            "}"
        ),
    )
    # Critical non-stub semantic corruption case: trivial `{ Ok(()) }` body deletion!
    trivial_noop_patch = f"{locked_sig} {{ Ok(()) }}"
    ok_trivial_ast, v_trivial_ast = check_rust_patch_anti_bypass_gate(locked_sig, trivial_noop_patch)

    assert not ok_stub and v_stub == ["diverging_stub_macro"]
    assert not ok_unsafe and v_unsafe == ["forbidden_unsafe_block"]
    assert not ok_sigmut and v_sigmut == ["signature_mutated"]
    assert ok_comments_strings and v_comments_strings == []
    # Proves syntactic gate passes `{ Ok(()) }` (`ok_trivial_ast == True`), requiring behavioral contract check!
    assert ok_trivial_ast and v_trivial_ast == []

    return {
        "rustassistant_compile_rate": round(float(ra_compile_total) * 100.0, 2),
        "rustassistant_silent_corrupt_cond_pct": round(float(ra_cond_corrupt) * 100.0, 2),
        "crust_opus4_comp_repair": (int(comp_build * 100), int(comp_test * 100)),
        "crust_opus4_test_repair": (int(test_build * 100), int(test_pass * 100)),
        "derived_unguarded_borrow": tuple(round(float(x) * 100.0, 2) for x in b_u[1]),
        "derived_syntactic_gate_borrow": tuple(round(float(x) * 100.0, 2) for x in b_sg[1]),
        "derived_syntactic_gate_cond_corrupt_pct": round(float(sg_cond_silent_corrupt) * 100.0, 2),
        "derived_full_contract_gate_borrow": tuple(round(float(x) * 100.0, 2) for x in b_fg[1]),
        "derived_expected_steps": (
            round(float(steps_u[1]), 3),
            round(float(steps_sg[1]), 3),
            round(float(steps_fg[1]), 3),
        ),
        "mc_syn_gate_ok_pct": round(mc_sg_ok * 100.0, 2),
        "trivial_ok_passes_syntactic_gate": ok_trivial_ast,
    }


# ============================================================================
# Deterministic Entrypoint & Structured Report Output
# ============================================================================


def main() -> int:
    r1 = run_probe_1_codeplan()
    r2 = run_probe_2_repomap()
    r3 = run_probe_3_typestate()
    r4 = run_probe_4_markov_repair()

    payload = {"probe_1": r1, "probe_2": r2, "probe_3": r3, "probe_4": r4}
    payload_bytes = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    payload_sha256 = hashlib.sha256(payload_bytes).hexdigest()

    lines: list[str] = [
        "=== [PROBE 1] codeplan_cmg_ast_worklist_vs_grep_and_build_repair | [Basis: normative + derived + execution] ===",
        f"  dynamic_ast_edges          : initial={r1['dynamic_edges_initial_to_final'][0]} -> final={r1['dynamic_edges_initial_to_final'][1]}",  # type: ignore[index]
    ]
    for label in (
        "cmg_variance_aware",
        "cmg_table1_strict",
        "cmg_no_spatial_ctx",
        "build_repair_1pass",
        "build_repair_iter_strict",
        "lexical_grep_1hop",
        "lexical_grep_2hop",
    ):
        tp, fp, fn, prec, rec, spur = r1[label]  # type: ignore[misc]
        lines.append(
            f"  {label:<24s} TP={tp} FP={fp} FN={fn} "
            f"Precision={prec:.4f} Recall={rec:.4f} SpuriousHelpers={spur}"
        )

    lines.append("")
    lines.append(
        "=== [PROBE 2] aider_upstream_call_only_vs_pep484_extension_and_bm25 | [Basis: source + derived + execution] ==="
    )
    lines.append(
        f"  Upstream Aider@5dc9490b    : type_recall={r2['upstream_aider_type_recall']} "
        f"total_recall={r2['upstream_aider_total_recall']} tokens={r2['upstream_aider_tokens']} "
        f"skeleton_confounders={r2['upstream_aider_skeleton_confounders']} "
        f"confounder_mass={r2['upstream_aider_confounder_mass']:.6f}"
    )
    lines.append(f"  PEP484+ImportFrom top-5    : {r2['pep484_ext_top5']}")
    lines.append(
        f"  PEP484+ImportFrom [derived]: total_recall={r2['pep484_ext_recall']} tokens={r2['pep484_ext_tokens']} "
        f"unscoped_confounder_mass={r2['pep484_unscoped_confounder_mass']:.6f} "
        f"import_scoped_mass={r2['pep484_import_scoped_mass']:.6f} "
        f"hub_damping={r2['hub_suppression_ratio']:.2f}x "
        f"private_damping={r2['private_suppression_ratio']:.2f}x"
    )
    lines.append(
        f"  BM25 full-file (6x150c)    : type_recall={r2['bm25_type_recall']} "
        f"total_recall={r2['bm25_total_recall']} "
        f"confounder_chunks={r2['bm25_confounder_chunks']} "
        f"broken_syntax_chunks={r2['bm25_broken_syntax_chunks']}"
    )

    lines.append("")
    lines.append(
        "=== [PROBE 3] sum_vs_product_cardinality_and_strom_yemini_coercions | [Basis: documentation + derived + execution] ==="
    )
    c_prod, c_sum, c_ill, c_pct = r3["conn_cardinality"]  # type: ignore[misc]
    r_prod, r_sum, r_ill, r_pct = r3["cursor_cardinality"]  # type: ignore[misc]
    lines.append(
        f"  TransactionalConnection    : product={c_prod} sum={c_sum} illegal={c_ill} ({c_pct:.2f}%)"
    )
    lines.append(
        f"  ResultSetCursor            : product={r_prod} sum={r_sum} illegal={r_ill} ({r_pct:.2f}%)"
    )
    lines.append(f"  Join meet state (B_join)   : {r3['join_meet_state']}")
    lines.append(f"  Synthesized coercions      : {r3['synthesized_coercions']}")
    lines.append(f"  Loop back-edge coercion    : {r3['loop_entry_coercion']}")
    lines.append(f"  Static typestate rejection : {r3['caught_protocol_error']}")

    lines.append("")
    lines.append(
        "=== [PROBE 4] repair_ratios_derived_markov_and_ast_gate | [Basis: documentation + derived + execution] ==="
    )
    lines.append(
        f"  RustAssistant [doc]        : compile={r4['rustassistant_compile_rate']:.2f}% "
        f"conditional_nonstub_corruption={r4['rustassistant_silent_corrupt_cond_pct']:.2f}%"
    )
    lines.append(
        f"  CRUST-Bench Opus-4 [doc]   : compiler_repair(build={r4['crust_opus4_comp_repair'][0]}%, "  # type: ignore[index]
        f"test={r4['crust_opus4_comp_repair'][1]}%) -> test_repair(build={r4['crust_opus4_test_repair'][0]}%, "  # type: ignore[index]
        f"test={r4['crust_opus4_test_repair'][1]}%)"  # type: ignore[index]
    )
    u_ok, u_stub, u_sil, u_ex = r4["derived_unguarded_borrow"]  # type: ignore[misc]
    s_ok, s_stub, s_sil, s_ex = r4["derived_syntactic_gate_borrow"]  # type: ignore[misc]
    f_ok, f_stub, f_sil, f_ex = r4["derived_full_contract_gate_borrow"]  # type: ignore[misc]
    st_u, st_s, st_f = r4["derived_expected_steps"]  # type: ignore[misc]
    lines.append(
        f"  Markov unguarded [derived] : ok={u_ok:.2f}% stub_bypass={u_stub:.2f}% "
        f"nonstub_corrupt={u_sil:.2f}% exhausted={u_ex:.2f}% E[steps]={st_u:.3f}"
    )
    lines.append(
        f"  Markov syn-gate [derived]  : ok={s_ok:.2f}% stub_bypass={s_stub:.2f}% "
        f"nonstub_corrupt={s_sil:.2f}% (cond={r4['derived_syntactic_gate_cond_corrupt_pct']:.2f}%) "
        f"exhausted={s_ex:.2f}% E[steps]={st_s:.3f} (MC_ok={r4['mc_syn_gate_ok_pct']:.2f}%)"
    )
    lines.append(
        f"  Markov syn+test [derived]  : ok={f_ok:.2f}% stub_bypass={f_stub:.2f}% "
        f"nonstub_corrupt={f_sil:.2f}% exhausted={f_ex:.2f}% E[steps]={st_f:.3f} "
        f"trivial_ok_passes_syn_gate={r4['trivial_ok_passes_syntactic_gate']}"
    )
    lines.append("")
    lines.append(
        f"=== ALL 4 VERIFICATION PROBES PASSED DETERMINISTICALLY (payload_sha256={payload_sha256}) ==="
    )
    sys.stdout.write("\n".join(lines) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
