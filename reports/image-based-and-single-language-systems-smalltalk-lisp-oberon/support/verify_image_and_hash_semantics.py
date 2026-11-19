#!/usr/bin/env python3
"""Standalone verification probe for image-based, modular, and content-addressed systems.

Demonstrates and verifies three core semantic mechanisms contrasted against
conventional file-and-linker toolchains:

  (A) Unison-style alpha-invariant canonical AST hashing (SHA3-512, Base32Hex,
      de Bruijn variable elimination, SCC cycle canonicalization, and diamond
      coexistence without symbol collision), plus the symmetric-cycle ordering
      edge case (IncompleteElementOrderingError).
  (B) Smalltalk/Spur-style live object memory with partial-read-barrier
      forwarding (`become:`), live class schema migration (`allInstances` +
      `elementsForwardIdentityTo:`), and a constructive image-drift witness
      showing snapshotted heap states unreachable from declarative source.
  (C) Separate-compilation interface identity regimes: Mesa/Cedar 48-bit
      version stamps, Project Oberon 2013 whole-module `.smb` checksums (with
      hidden-pointer GC metadata), Crelier (1994) per-export structural
      fingerprints (PB/PV), and untyped C/ELF symbol matching.

Requires Python 3.10+ standard library only. Exits 0 iff all assertions pass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
from dataclasses import dataclass, field
from typing import Any


# =============================================================================
# PART A: Unison-Style Alpha-Invariant Canonical ABT Hashing (SHA3-512)
# =============================================================================

BASE32HEX_ALPHABET = "0123456789abcdefghijklmnopqrstuv"
HASHING_VERSION_TAG = 2  # Mirrors Unison.Hashing.V2.Tokenizable.hashingVersion


def encode_base32hex(raw: bytes) -> str:
    """RFC 4648 section 7 lowercase unpadded Base32Hex (matches Unison.Hash)."""
    bits = 0
    bit_count = 0
    out: list[str] = []
    for byte in raw:
        bits = (bits << 8) | byte
        bit_count += 8
        while bit_count >= 5:
            bit_count -= 5
            out.append(BASE32HEX_ALPHABET[(bits >> bit_count) & 0x1F])
    if bit_count > 0:
        out.append(BASE32HEX_ALPHABET[(bits << (5 - bit_count)) & 0x1F])
    return "".join(out)


def accumulate_tokens(tokens: list[tuple[str, Any]]) -> bytes:
    """SHA3-512 over version-tagged length-prefixed tokens (Tokenizable.hs)."""
    h = hashlib.sha3_512()
    h.update(struct.pack("!B", HASHING_VERSION_TAG))
    for kind, val in tokens:
        if kind == "tag":
            h.update(struct.pack("!B", val))
        elif kind == "nat":
            h.update(struct.pack("!Q", val))
        elif kind == "int":
            h.update(struct.pack("!q", val))
        elif kind == "text":
            enc = val.encode("utf-8")
            h.update(struct.pack("!Q", len(enc)))
            h.update(enc)
        elif kind == "bytes":
            h.update(struct.pack("!Q", len(val)))
            h.update(val)
        elif kind == "hashed":
            assert isinstance(val, bytes) and len(val) == 64
            h.update(val)
        else:
            raise ValueError(f"Unknown token kind: {kind}")
    return h.digest()


class Expr:
    """Minimal Abstract Binding Tree (ABT) with optional source annotations."""


@dataclass(frozen=True)
class Var(Expr):
    name: str
    span: tuple[int, int] = (0, 0)


@dataclass(frozen=True)
class LitInt(Expr):
    value: int
    span: tuple[int, int] = (0, 0)


@dataclass(frozen=True)
class Builtin(Expr):
    symbol: str


@dataclass(frozen=True)
class Ref(Expr):
    digest: bytes
    pos: int = 0  # Component index inside mutually recursive SCC

    @property
    def short_id(self) -> str:
        b32 = encode_base32hex(self.digest)[:10]
        return f"#{b32}" if self.pos == 0 else f"#{b32}.{self.pos}"


@dataclass(frozen=True)
class Abs(Expr):
    param: str
    body: Expr
    span: tuple[int, int] = (0, 0)


@dataclass(frozen=True)
class App(Expr):
    fn: Expr
    arg: Expr
    span: tuple[int, int] = (0, 0)


@dataclass(frozen=True)
class BinOp(Expr):
    op: str
    left: Expr
    right: Expr
    span: tuple[int, int] = (0, 0)


@dataclass(frozen=True)
class IfZero(Expr):
    cond: Expr
    then_br: Expr
    else_br: Expr


def free_vars(expr: Expr, bound: frozenset[str] = frozenset()) -> set[str]:
    if isinstance(expr, Var):
        return set() if expr.name in bound else {expr.name}
    if isinstance(expr, (LitInt, Builtin, Ref)):
        return set()
    if isinstance(expr, Abs):
        return free_vars(expr.body, bound | {expr.param})
    if isinstance(expr, App):
        return free_vars(expr.fn, bound) | free_vars(expr.arg, bound)
    if isinstance(expr, BinOp):
        return free_vars(expr.left, bound) | free_vars(expr.right, bound)
    if isinstance(expr, IfZero):
        return (
            free_vars(expr.cond, bound)
            | free_vars(expr.then_br, bound)
            | free_vars(expr.else_br, bound)
        )
    raise TypeError(f"Unsupported Expr: {type(expr)}")


def subst_expr(expr: Expr, mapping: dict[str, Expr]) -> Expr:
    if isinstance(expr, Var):
        return mapping.get(expr.name, expr)
    if isinstance(expr, (LitInt, Builtin, Ref)):
        return expr
    if isinstance(expr, Abs):
        sub_map = {k: v for k, v in mapping.items() if k != expr.param}
        return Abs(expr.param, subst_expr(expr.body, sub_map), expr.span)
    if isinstance(expr, App):
        return App(subst_expr(expr.fn, mapping), subst_expr(expr.arg, mapping), expr.span)
    if isinstance(expr, BinOp):
        return BinOp(expr.op, subst_expr(expr.left, mapping), subst_expr(expr.right, mapping), expr.span)
    if isinstance(expr, IfZero):
        return IfZero(
            subst_expr(expr.cond, mapping),
            subst_expr(expr.then_br, mapping),
            subst_expr(expr.else_br, mapping),
        )
    raise TypeError(f"Unsupported Expr: {type(expr)}")


def hash_abt(expr: Expr, env: list[tuple[str, Any]]) -> bytes:
    """Hash an ABT under de Bruijn environment `env`, ignoring names and spans.

    Each entry in `env` is either ("single", var_name) or ("cycle", set_of_names),
    mirroring `[Either [v] v]` in Unison.Hashing.V2.ABT.hash'.
    """
    if isinstance(expr, Var):
        for idx, (kind, entry) in enumerate(env):
            if (kind == "single" and entry == expr.name) or (
                kind == "cycle" and expr.name in entry
            ):
                return accumulate_tokens([("nat", idx)])
        raise KeyError(f"Unbound variable {expr.name!r} in env {env!r}")

    if isinstance(expr, Ref):
        if expr.pos == 0:
            # Transparent reference property (Unison.Hashing.V2.Term line 147)
            return expr.digest
        return accumulate_tokens([("tag", 1), ("hashed", expr.digest), ("nat", expr.pos)])

    if isinstance(expr, Builtin):
        return accumulate_tokens([("tag", 1), ("tag", 2), ("text", expr.symbol)])

    if isinstance(expr, LitInt):
        return accumulate_tokens([("tag", 1), ("tag", 3), ("int", expr.value)])

    if isinstance(expr, Abs):
        # Bound variable name and source span are completely erased.
        body_hash = hash_abt(expr.body, [("single", expr.param)] + env)
        return accumulate_tokens([("tag", 1), ("tag", 4), ("hashed", body_hash)])

    if isinstance(expr, App):
        return accumulate_tokens(
            [
                ("tag", 1),
                ("tag", 5),
                ("hashed", hash_abt(expr.fn, env)),
                ("hashed", hash_abt(expr.arg, env)),
            ]
        )

    if isinstance(expr, BinOp):
        return accumulate_tokens(
            [
                ("tag", 1),
                ("tag", 6),
                ("text", expr.op),
                ("hashed", hash_abt(expr.left, env)),
                ("hashed", hash_abt(expr.right, env)),
            ]
        )

    if isinstance(expr, IfZero):
        return accumulate_tokens(
            [
                ("tag", 1),
                ("tag", 7),
                ("hashed", hash_abt(expr.cond, env)),
                ("hashed", hash_abt(expr.then_br, env)),
                ("hashed", hash_abt(expr.else_br, env)),
            ]
        )

    raise TypeError(f"Unsupported Expr: {type(expr)}")


def tarjan_sccs(nodes: list[str], deps: dict[str, set[str]]) -> list[list[str]]:
    """Return strongly connected components in reverse topological order (deps first)."""
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    sccs: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in sorted(deps.get(v, set())):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for n in sorted(nodes):
        if n not in indices:
            strongconnect(n)
    return sccs


class IncompleteElementOrderingError(Exception):
    """Raised when structurally symmetric cycle elements cannot be canonically ordered."""

    def __init__(self, equiv_groups: list[list[str]]) -> None:
        self.equiv_groups = equiv_groups
        super().__init__(f"Structurally symmetric cycle elements: {equiv_groups}")


def hash_component(defs: dict[str, Expr]) -> tuple[bytes, list[tuple[str, Expr]], list[list[str]]]:
    """Canonicalize and hash an SCC of mutually recursive definitions (ABT.hs:doHashCycle)."""
    names = sorted(defs.keys())
    if len(names) == 1 and names[0] not in free_vars(defs[names[0]]):
        # Non-recursive single definition: direct hash
        n = names[0]
        return hash_abt(defs[n], []), [(n, defs[n])], []

    # Step 1: Collapse all intra-cycle references to de Bruijn index 0
    perm_env: list[tuple[str, Any]] = [("cycle", set(names))]
    named_perm_hashes = [(n, hash_abt(defs[n], perm_env)) for n in names]

    # Detect structurally symmetric cycle elements (IncompleteElementOrderingError)
    buckets: dict[bytes, list[str]] = {}
    for n, digest in named_perm_hashes:
        buckets.setdefault(digest, []).append(n)
    warnings = [sorted(grp) for grp in buckets.values() if len(grp) > 1]

    # Step 2: Canonical permutation sorted by permutation hash
    permuted = sorted(named_perm_hashes, key=lambda pair: (pair[1], pair[0]))
    permuted_names = [n for n, _ in permuted]
    new_env: list[tuple[str, Any]] = [("single", n) for n in permuted_names]

    # Step 3: Re-hash each member in ordered cycle environment and derive overall SCC hash
    cycle_hashes = [hash_abt(defs[n], new_env) for n in permuted_names]
    common_tokens: list[tuple[str, Any]] = [("tag", 1)] + [("hashed", h) for h in cycle_hashes]
    member_hashes = [
        (accumulate_tokens(common_tokens + [("hashed", hash_abt(Var(n), new_env))]), n)
        for n in permuted_names
    ]
    member_hashes.sort(key=lambda pair: pair[0])
    overall_hash = accumulate_tokens([("hashed", h) for h, _ in member_hashes])
    ordered_defs = [(n, defs[n]) for _, n in member_hashes]
    return overall_hash, ordered_defs, warnings


class UnisonCodebase:
    """Content-addressed code store separating AST storage from human namespaces."""

    def __init__(self) -> None:
        self.terms: dict[tuple[bytes, int], Expr] = {}
        self.eval_cache: dict[tuple[bytes, int, int], int] = {}
        self.namespaces: dict[str, dict[str, Ref]] = {"main": {}}
        self.compile_count: int = 0

    def add_definitions(
        self,
        namespace: str,
        raw_defs: dict[str, Expr],
        *,
        strict_cycle_order: bool = True,
    ) -> dict[str, Ref]:
        """Resolve names in `namespace`, hash SCCs, and store only unseen hashes."""
        ns = self.namespaces.setdefault(namespace, {})
        # Resolve free variables referring to existing namespace bindings into Ref nodes
        resolved: dict[str, Expr] = {}
        local_names = set(raw_defs.keys())
        for name, body in raw_defs.items():
            ext_map = {k: ref for k, ref in ns.items() if k not in local_names}
            resolved[name] = subst_expr(body, ext_map)

        deps = {name: free_vars(body) & local_names for name, body in resolved.items()}
        sccs = tarjan_sccs(list(resolved.keys()), deps)

        assigned: dict[str, Ref] = {}
        for comp in sccs:
            sub_map = {k: v for k, v in assigned.items()}
            comp_defs = {n: subst_expr(resolved[n], sub_map) for n in comp}
            overall_hash, ordered_defs, warnings = hash_component(comp_defs)
            if warnings and strict_cycle_order:
                raise IncompleteElementOrderingError(warnings)

            local_refs = {n: Ref(overall_hash, pos) for pos, (n, _) in enumerate(ordered_defs)}
            for pos, (n, expr) in enumerate(ordered_defs):
                closed = subst_expr(expr, local_refs)
                key = (overall_hash, pos)
                if key not in self.terms:
                    self.terms[key] = closed
                    self.compile_count += 1
                assigned[n] = local_refs[n]
                ns[n] = local_refs[n]
        return assigned

    def rename_in_namespace(self, namespace: str, old_name: str, new_name: str) -> None:
        """Pure metadata operation: mutates namespace table only, zero AST/hash change."""
        ns = self.namespaces[namespace]
        ns[new_name] = ns.pop(old_name)

    def eval_expr(self, expr: Expr, env: dict[str, Any] | None = None) -> Any:
        env = {} if env is None else env
        if isinstance(expr, LitInt):
            return expr.value
        if isinstance(expr, Var):
            return env[expr.name]
        if isinstance(expr, Ref):
            return self.eval_expr(self.terms[(expr.digest, expr.pos)], {})
        if isinstance(expr, Abs):
            captured = dict(env)
            return lambda arg: self.eval_expr(expr.body, {**captured, expr.param: arg})
        if isinstance(expr, App):
            fn = self.eval_expr(expr.fn, env)
            arg = self.eval_expr(expr.arg, env)
            return fn(arg)
        if isinstance(expr, BinOp):
            l = self.eval_expr(expr.left, env)
            r = self.eval_expr(expr.right, env)
            if expr.op == "+":
                return l + r
            if expr.op == "-":
                return l - r
            if expr.op == "*":
                return l * r
            raise ValueError(f"Unsupported op {expr.op}")
        if isinstance(expr, IfZero):
            c = self.eval_expr(expr.cond, env)
            return self.eval_expr(expr.then_br if c == 0 else expr.else_br, env)
        raise TypeError(f"Cannot evaluate {type(expr)}")


def run_probe_a_unison() -> dict[str, Any]:
    cb = UnisonCodebase()

    # 1. Alpha-invariance & 0 rebuilds on rename
    defs_v1 = {
        "scale": Abs("x", BinOp("*", Var("x", (1, 2)), LitInt(3, (5, 6)), (1, 6)), (0, 6)),
        "pipeline": Abs("n", BinOp("+", App(Var("scale"), Var("n")), LitInt(1)), (10, 25)),
    }
    refs_v1 = cb.add_definitions("main", defs_v1)
    compiles_after_v1 = cb.compile_count

    # Rename parameters, source spans, AND top-level namespace names
    cb.rename_in_namespace("main", "scale", "rescale")
    cb.rename_in_namespace("main", "pipeline", "run_pipeline")

    # Re-add alpha-renamed equivalents with different spans & identifier names
    defs_renamed = {
        "rescale_copy": Abs("amount", BinOp("*", Var("amount", (99, 105)), LitInt(3, (108, 109)), (99, 109)), (90, 110)),
        "run_pipeline_copy": Abs("input_val", BinOp("+", App(Var("rescale_copy"), Var("input_val")), LitInt(1)), (120, 160)),
    }
    refs_renamed = cb.add_definitions("main", defs_renamed)
    rebuilds_on_rename = cb.compile_count - compiles_after_v1
    assert refs_renamed["rescale_copy"] == refs_v1["scale"], "Alpha-renaming broke scale hash!"
    assert refs_renamed["run_pipeline_copy"] == refs_v1["pipeline"], "Alpha-renaming broke dependent hash!"
    assert rebuilds_on_rename == 0, f"Alpha-renaming triggered {rebuilds_on_rename} spurious rebuilds!"

    # 2. Diamond dependency coexistence without SemVer/symbol collision
    math_v1_refs = cb.add_definitions("lib.math_v1", {"norm": Abs("x", BinOp("+", Var("x"), LitInt(1)))})
    math_v2_refs = cb.add_definitions("lib.math_v2", {"norm": Abs("x", BinOp("*", Var("x"), LitInt(2)))})
    assert math_v1_refs["norm"] != math_v2_refs["norm"]

    # service_a links to lib.math_v1.norm; service_b links to lib.math_v2.norm
    cb.namespaces["svc_a"] = {"norm": math_v1_refs["norm"]}
    svc_a_refs = cb.add_definitions("svc_a", {"compute": Abs("v", App(Var("norm"), Var("v")))})
    cb.namespaces["svc_b"] = {"norm": math_v2_refs["norm"]}
    svc_b_refs = cb.add_definitions("svc_b", {"compute": Abs("v", App(Var("norm"), Var("v")))})

    # Combine both services in one root program without symbol collision
    cb.namespaces["app"] = {
        "svc_a_compute": svc_a_refs["compute"],
        "svc_b_compute": svc_b_refs["compute"],
    }
    app_refs = cb.add_definitions(
        "app",
        {
            "combined": Abs(
                "x",
                BinOp("+", App(Var("svc_a_compute"), Var("x")), App(Var("svc_b_compute"), Var("x"))),
            )
        },
    )
    combined_fn = cb.eval_expr(app_refs["combined"])
    # For x = 5: svc_a gives 5+1=6, svc_b gives 5*2=10, combined gives 16
    combined_result = combined_fn(5)
    assert combined_result == 16, f"Expected 16, got {combined_result}"

    # 3. Symmetric mutual recursion triggers IncompleteElementOrderingError
    sym_cycle = {
        "ping": Abs("n", IfZero(Var("n"), LitInt(0), App(Var("pong"), BinOp("-", Var("n"), LitInt(1))))),
        "pong": Abs("m", IfZero(Var("m"), LitInt(0), App(Var("ping"), BinOp("-", Var("m"), LitInt(1))))),
    }
    caught_symmetry = False
    symmetry_groups: list[list[str]] = []
    try:
        cb.add_definitions("sym", sym_cycle, strict_cycle_order=True)
    except IncompleteElementOrderingError as exc:
        caught_symmetry = True
        symmetry_groups = exc.equiv_groups
    assert caught_symmetry and symmetry_groups == [["ping", "pong"]]

    # Asymmetric mutual recursion (even/odd return different base cases 1 vs 0) hashes cleanly
    asym_cycle = {
        "is_even": Abs("n", IfZero(Var("n"), LitInt(1), App(Var("is_odd"), BinOp("-", Var("n"), LitInt(1))))),
        "is_odd": Abs("m", IfZero(Var("m"), LitInt(0), App(Var("is_even"), BinOp("-", Var("m"), LitInt(1))))),
    }
    eo_refs = cb.add_definitions("eo", asym_cycle, strict_cycle_order=True)
    assert eo_refs["is_even"].digest == eo_refs["is_odd"].digest
    assert {eo_refs["is_even"].pos, eo_refs["is_odd"].pos} == {0, 1}
    assert cb.eval_expr(eo_refs["is_even"])(6) == 1
    assert cb.eval_expr(eo_refs["is_odd"])(6) == 0

    return {
        "scale_hash_short": refs_v1["scale"].short_id,
        "pipeline_hash_short": refs_v1["pipeline"].short_id,
        "rebuilds_on_rename": rebuilds_on_rename,
        "rename_zero_rebuilds": rebuilds_on_rename == 0,
        "diamond_math_v1_hash": math_v1_refs["norm"].short_id,
        "diamond_math_v2_hash": math_v2_refs["norm"].short_id,
        "diamond_eval_5": combined_result,
        "symmetric_cycle_detected": symmetry_groups,
        "asymmetric_cycle_refs": {k: v.short_id for k, v in eo_refs.items()},
    }


# =============================================================================
# PART B: Smalltalk/Spur Partial-Read-Barrier Forwarding & Image-Drift Witness
# =============================================================================

# Exact Spur64 constants verified from OpenSmalltalk/opensmalltalk-vm cointerp.c
SPUR_CLASS_INDEX_MASK = 0x3FFFFF
SPUR_FORMAT_SHIFT = 24
SPUR_FORMAT_MASK = 0x1F
SPUR_IDENTITY_HASH_SHIFT = 32
SPUR_IDENTITY_HASH_MASK = 0x3FFFFF
SPUR_NUM_SLOTS_SHIFT = 56
SPUR_IMMUTABLE_BIT = 1 << 23
SPUR_FORWARDED_CLASS_INDEX_PUN = 8
SPUR_FORWARDED_FORMAT = 7
SPUR_NORMAL_OBJECT_FORMAT = 1
SPUR_CLASS_METACLASS_FORMAT = 1


def pack_spur_header(
    class_index: int,
    fmt: int,
    identity_hash: int,
    num_slots: int,
    immutable: bool = False,
) -> int:
    hdr = (class_index & SPUR_CLASS_INDEX_MASK)
    hdr |= (fmt & SPUR_FORMAT_MASK) << SPUR_FORMAT_SHIFT
    hdr |= (identity_hash & SPUR_IDENTITY_HASH_MASK) << SPUR_IDENTITY_HASH_SHIFT
    hdr |= (min(num_slots, 255) & 0xFF) << SPUR_NUM_SLOTS_SHIFT
    if immutable:
        hdr |= SPUR_IMMUTABLE_BIT
    return hdr


def header_class_index(hdr: int) -> int:
    return hdr & SPUR_CLASS_INDEX_MASK


def header_identity_hash(hdr: int) -> int:
    return (hdr >> SPUR_IDENTITY_HASH_SHIFT) & SPUR_IDENTITY_HASH_MASK


def header_is_forwarded(hdr: int) -> bool:
    # Mirrors Spur's single-mask check: class_index == 8 (and format == 7)
    return (hdr & SPUR_CLASS_INDEX_MASK) == SPUR_FORWARDED_CLASS_INDEX_PUN


@dataclass
class HeapObject:
    addr: int
    header: int
    slots: list[Any]


class SpurHeap:
    """Miniature Spur64 object memory modeling become:, schema migration, and snapshotting."""

    def __init__(self) -> None:
        self.next_addr = 0x1000
        self.next_hash = 100
        self.next_class_idx = 32  # Indices 0..31 reserved for Spur puns
        self.objects: dict[int, HeapObject] = {}
        self.class_table: dict[int, int] = {}  # class_index -> class object addr
        self.globals: dict[str, int] = {}
        self.forwarding_misses = 0

    def alloc_class(self, name: str, slot_names: tuple[str, ...]) -> int:
        cidx = self.next_class_idx
        self.next_class_idx += 1
        addr = self.next_addr
        self.next_addr += 8 * (1 + 2)
        # In Spur, a class's identity hash IS its index in the Class Table
        hdr = pack_spur_header(
            class_index=1,  # Meta-index placeholder
            fmt=SPUR_CLASS_METACLASS_FORMAT,
            identity_hash=cidx,
            num_slots=2,
        )
        self.objects[addr] = HeapObject(addr=addr, header=hdr, slots=[name, list(slot_names)])
        self.class_table[cidx] = addr
        self.globals[name] = addr
        return addr

    def alloc_instance(self, class_addr: int, values: list[Any], immutable: bool = False) -> int:
        class_addr = self.follow(class_addr)
        cidx = header_identity_hash(self.objects[class_addr].header)
        slot_names = self.objects[class_addr].slots[1]
        assert len(values) == len(slot_names)
        addr = self.next_addr
        self.next_addr += 8 * (1 + max(1, len(values)))
        ihash = self.next_hash
        self.next_hash += 1
        hdr = pack_spur_header(
            class_index=cidx,
            fmt=SPUR_NORMAL_OBJECT_FORMAT,
            identity_hash=ihash,
            num_slots=len(values),
            immutable=immutable,
        )
        self.objects[addr] = HeapObject(addr=addr, header=hdr, slots=list(values))
        return addr

    def follow(self, oop: int) -> int:
        """Spur partial read barrier slow path: follow classIndex==8 forwarding chain."""
        cur = oop
        while header_is_forwarded(self.objects[cur].header):
            self.forwarding_misses += 1
            cur = self.objects[cur].slots[0]
        return cur

    def get_slot(self, oop: int, idx: int) -> Any:
        real = self.follow(oop)
        return self.objects[real].slots[idx]

    def set_slot(self, oop: int, idx: int, val: Any) -> None:
        real = self.follow(oop)
        if self.objects[real].header & SPUR_IMMUTABLE_BIT:
            raise PermissionError("Cannot mutate immutable object")
        self.objects[real].slots[idx] = val

    def identity_hash_of(self, oop: int) -> int:
        return header_identity_hash(self.objects[self.follow(oop)].header)

    def class_of(self, oop: int) -> int:
        real = self.follow(oop)
        cidx = header_class_index(self.objects[real].header)
        return self.follow(self.class_table[cidx])

    def all_instances_of(self, class_addr: int) -> list[int]:
        class_addr = self.follow(class_addr)
        cidx = header_identity_hash(self.objects[class_addr].header)
        res = []
        for addr, obj in self.objects.items():
            if not header_is_forwarded(obj.header) and header_class_index(obj.header) == cidx:
                res.append(addr)
        return res

    def become_two_way(self, oop1: int, oop2: int, copy_hash: bool = False) -> str:
        """Mirrors SpurMemoryManager>>#become:with:twoWay:copyHash: (cointerp.c:47374-47408).

        Equal-slot non-class instances swap in place with 0 forwarders; unequal-slot
        or class objects clone and overwrite both old headers with classIndex=8 forwarders.
        """
        a1 = self.follow(oop1)
        a2 = self.follow(oop2)
        if a1 == a2:
            return "noop"
        o1 = self.objects[a1]
        o2 = self.objects[a2]
        is_cls1 = header_identity_hash(o1.header) in self.class_table and self.class_table[header_identity_hash(o1.header)] == a1
        is_cls2 = header_identity_hash(o2.header) in self.class_table and self.class_table[header_identity_hash(o2.header)] == a2

        if len(o1.slots) == len(o2.slots) and not is_cls1 and not is_cls2:
            # inPlaceBecomeandcopyHashFlag: swap headers and slots in place, 0 forwarders
            h1, h2 = o1.header, o2.header
            if not copy_hash:
                # Unswap 22-bit identity hashes (cointerp.c:52820-52826)
                mask = SPUR_IDENTITY_HASH_MASK << SPUR_IDENTITY_HASH_SHIFT
                diff = (h1 ^ h2) & mask
                h1 ^= diff
                h2 ^= diff
            o1.header, o2.header = h2, h1
            o1.slots, o2.slots = o2.slots, o1.slots
            return "in_place"

        # outOfPlaceBecomeandcopyHashFlag: clone both, then forward a1->clone2 and a2->clone1
        c1_addr = self.next_addr
        self.next_addr += 8 * (1 + max(1, len(o1.slots)))
        c2_addr = self.next_addr
        self.next_addr += 8 * (1 + max(1, len(o2.slots)))
        c1_hdr, c2_hdr = o1.header, o2.header
        if not copy_hash:
            mask = SPUR_IDENTITY_HASH_MASK << SPUR_IDENTITY_HASH_SHIFT
            diff = (c1_hdr ^ c2_hdr) & mask
            c1_hdr ^= diff
            c2_hdr ^= diff
        self.objects[c1_addr] = HeapObject(c1_addr, c1_hdr, list(o1.slots))
        self.objects[c2_addr] = HeapObject(c2_addr, c2_hdr, list(o2.slots))
        o1.header = pack_spur_header(SPUR_FORWARDED_CLASS_INDEX_PUN, SPUR_FORWARDED_FORMAT, 0, max(1, len(o1.slots)))
        o1.slots = [c2_addr]
        o2.header = pack_spur_header(SPUR_FORWARDED_CLASS_INDEX_PUN, SPUR_FORWARDED_FORMAT, 0, max(1, len(o2.slots)))
        o2.slots = [c1_addr]
        return "out_of_place"

    def become_one_way(self, old_oops: list[int], new_oops: list[int], copy_hash: bool = True) -> None:
        """Mirrors elementsForwardIdentityTo:copyHash: using Spur forwarding objects."""
        assert len(old_oops) == len(new_oops)
        for old_a, new_a in zip(old_oops, new_oops):
            old_a = self.follow(old_a)
            new_a = self.follow(new_a)
            old_obj = self.objects[old_a]
            new_obj = self.objects[new_a]
            old_hash = header_identity_hash(old_obj.header)
            if copy_hash:
                # Preserve old object's identity hash (and Class Table slot if class)
                new_obj.header = pack_spur_header(
                    class_index=header_class_index(new_obj.header),
                    fmt=SPUR_NORMAL_OBJECT_FORMAT,
                    identity_hash=old_hash,
                    num_slots=len(new_obj.slots),
                    immutable=bool(new_obj.header & SPUR_IMMUTABLE_BIT),
                )
                if old_hash in self.class_table and self.class_table[old_hash] == old_a:
                    self.class_table[old_hash] = new_a
            # Overwrite old header with forwarded pun (classIndex=8, format=7) and clear immutable bit
            old_obj.header = pack_spur_header(
                class_index=SPUR_FORWARDED_CLASS_INDEX_PUN,
                fmt=SPUR_FORWARDED_FORMAT,
                identity_hash=0,
                num_slots=max(1, len(old_obj.slots)),
                immutable=False,
            )
            old_obj.slots = [new_a]

    def migrate_class_schema(self, class_name: str, new_slot_names: tuple[str, ...]) -> int:
        """Mirrors Pharo ShiftClassInstaller>>migrateClassTo: & migrateInstancesTo:."""
        old_cls = self.follow(self.globals[class_name])
        old_slot_names: list[str] = list(self.objects[old_cls].slots[1])
        old_instances = self.all_instances_of(old_cls)

        # Create replacement class object
        new_cls = self.alloc_class(class_name + "__new", new_slot_names)
        self.objects[new_cls].slots[0] = class_name
        del self.globals[class_name + "__new"]

        # Allocate migrated instances, copying matching slots by name (new slots -> None)
        new_instances: list[int] = []
        saved_immutable: list[bool] = []
        for old_inst in old_instances:
            obj = self.objects[old_inst]
            was_imm = bool(obj.header & SPUR_IMMUTABLE_BIT)
            saved_immutable.append(was_imm)
            # Clear immutable flag on old object prior to become (ShiftClassInstaller.st:111)
            obj.header &= ~SPUR_IMMUTABLE_BIT
            old_map = dict(zip(old_slot_names, obj.slots))
            new_vals = [old_map.get(sn, None) for sn in new_slot_names]
            new_instances.append(self.alloc_instance(new_cls, new_vals, immutable=False))

        # Atomically forward instances, then class object
        if old_instances:
            self.become_one_way(old_instances, new_instances, copy_hash=True)
        self.become_one_way([old_cls], [new_cls], copy_hash=True)
        self.globals[class_name] = new_cls

        # Fix migrated instances' class_index to point to preserved class hash
        preserved_cidx = header_identity_hash(self.objects[new_cls].header)
        for new_inst, was_imm in zip(new_instances, saved_immutable):
            o = self.objects[new_inst]
            o.header = pack_spur_header(
                class_index=preserved_cidx,
                fmt=SPUR_NORMAL_OBJECT_FORMAT,
                identity_hash=header_identity_hash(o.header),
                num_slots=len(o.slots),
                immutable=was_imm,
            )
        return new_cls

    def gc_resolve_and_compact_forwarders(self, roots: dict[str, int]) -> int:
        """Rewrite all pointers past forwarding objects and reclaim forwarder stubs."""
        for k, v in list(roots.items()):
            roots[k] = self.follow(v)
        for k, v in list(self.globals.items()):
            self.globals[k] = self.follow(v)
        for addr, obj in self.objects.items():
            if not header_is_forwarded(obj.header):
                obj.slots = [
                    self.follow(s) if isinstance(s, int) and s in self.objects else s
                    for s in obj.slots
                ]
        dead = [a for a, o in self.objects.items() if header_is_forwarded(o.header)]
        for a in dead:
            del self.objects[a]
        return len(dead)

    def snapshot_json(self, roots: dict[str, int]) -> str:
        """Serialize live object heap (image snapshot)."""
        return json.dumps(
            {
                "next_addr": self.next_addr,
                "next_hash": self.next_hash,
                "next_class_idx": self.next_class_idx,
                "globals": self.globals,
                "class_table": {str(k): v for k, v in self.class_table.items()},
                "roots": roots,
                "objects": {
                    str(a): {"header": o.header, "slots": o.slots}
                    for a, o in self.objects.items()
                },
            },
            sort_keys=True,
        )

    @classmethod
    def load_snapshot(cls, data: str) -> tuple["SpurHeap", dict[str, int]]:
        raw = json.loads(data)
        h = cls()
        h.next_addr = raw["next_addr"]
        h.next_hash = raw["next_hash"]
        h.next_class_idx = raw["next_class_idx"]
        h.globals = raw["globals"]
        h.class_table = {int(k): v for k, v in raw["class_table"].items()}
        h.objects = {
            int(a): HeapObject(addr=int(a), header=v["header"], slots=v["slots"])
            for a, v in raw["objects"].items()
        }
        return h, raw["roots"]


def run_probe_b_smalltalk_spur() -> dict[str, Any]:
    heap = SpurHeap()
    pt_cls = heap.alloc_class("Point", ("x", "y"))
    pair_cls = heap.alloc_class("Pair", ("a", "b"))
    p1 = heap.alloc_instance(pt_cls, [10, 20])
    p2 = heap.alloc_instance(pair_cls, [77, 88])
    h_p1_before = heap.identity_hash_of(p1)
    h_p2_before = heap.identity_hash_of(p2)

    # Two-way equal-slot become: uses Spur in-place path with 0 forwarding objects!
    two_way_eq_path = heap.become_two_way(p1, p2, copy_hash=False)
    assert two_way_eq_path == "in_place"
    assert not header_is_forwarded(heap.objects[p1].header)
    assert heap.get_slot(p1, 0) == 77 and heap.get_slot(p2, 0) == 10
    assert heap.identity_hash_of(p1) == h_p1_before and heap.identity_hash_of(p2) == h_p2_before

    # Two-way unequal-slot become: uses Spur out-of-place cloning + classIndex=8 forwarders
    box_cls = heap.alloc_class("Box", ("v",))
    b1 = heap.alloc_instance(box_cls, [555])
    two_way_neq_path = heap.become_two_way(p2, b1, copy_hash=False)
    assert two_way_neq_path == "out_of_place"
    assert header_is_forwarded(heap.objects[p2].header) and header_is_forwarded(heap.objects[b1].header)
    assert heap.get_slot(p2, 0) == 555 and heap.get_slot(b1, 0) == 10

    # Fresh Point instance for live schema migration test
    p_oop = heap.alloc_instance(pt_cls, [3, 4])
    orig_hash = heap.identity_hash_of(p_oop)

    # Two distinct roots alias the same live object
    roots = {"alias_a": p_oop, "alias_b": p_oop}

    # Live schema migration: Point(x, y) -> Point(x, y, z)
    heap.migrate_class_schema("Point", ("x", "y", "z"))

    # Before GC, old oop is a Spur forwarder (classIndex=8)
    assert header_is_forwarded(heap.objects[p_oop].header)
    assert heap.get_slot(roots["alias_a"], 0) == 3
    assert heap.get_slot(roots["alias_a"], 1) == 4
    assert heap.get_slot(roots["alias_a"], 2) is None
    assert heap.identity_hash_of(roots["alias_a"]) == orig_hash

    # Mutate through alias_a and observe via alias_b (identity preserved!)
    heap.set_slot(roots["alias_a"], 2, 99)
    assert heap.get_slot(roots["alias_b"], 2) == 99
    misses_before_gc = heap.forwarding_misses
    assert misses_before_gc > 0

    # GC compacts away forwarding stubs
    reclaimed = heap.gc_resolve_and_compact_forwarders(roots)
    assert reclaimed >= 2  # forwarded Point instance + forwarded Point class
    misses_after_gc_base = heap.forwarding_misses
    assert heap.get_slot(roots["alias_a"], 2) == 99
    assert heap.forwarding_misses == misses_after_gc_base, "Zero barrier misses after GC!"

    # --- Constructive Image-Drift Witness ---
    # Declarative source S_final defines Counter(count, origin, next_ref):
    #   Counter class >> new  => Counter(count=0, origin="source", next_ref=None)
    #   Counter >> inc        => count := count + 1   (only non-negative, acyclic, origin=="source")
    # Invariant of EVERY state constructible from S_final starting at fresh root:
    #   I(obj) := (count >= 0) and (origin == "source") and (next_ref is None)
    counter_cls = heap.alloc_class("Counter", ("count", "origin", "next_ref"))
    c_oop = heap.alloc_instance(counter_cls, [0, "source", None])
    roots["singleton_counter"] = c_oop

    # Developer performs live workspace/debugger mutations + becomes + deletes temporary script:
    mutated = heap.alloc_instance(counter_cls, [-42, "workspace-hotfix-v0", None])
    heap.set_slot(mutated, 2, mutated)  # Self-referential pointer cycle!
    heap.become_one_way([c_oop], [mutated], copy_hash=True)
    heap.gc_resolve_and_compact_forwarders(roots)

    # Snapshot image and reload it cold
    snap_bytes = heap.snapshot_json(roots)
    reloaded_heap, reloaded_roots = SpurHeap.load_snapshot(snap_bytes)
    live_counter = reloaded_heap.objects[reloaded_roots["singleton_counter"]]
    snap_state = (
        live_counter.slots[0],
        live_counter.slots[1],
        live_counter.slots[2] == live_counter.addr,
    )
    assert snap_state == (-42, "workspace-hotfix-v0", True)

    # Exhaustive bounded replay from declarative source S_final (fresh root, up to 100 steps)
    reachable_from_source: set[tuple[int, str, bool]] = set()
    state = (0, "source", False)  # Counter class >> new
    for _ in range(100):
        reachable_from_source.add(state)
        state = (state[0] + 1, state[1], state[2])  # Counter >> inc

    # Formal image-drift witness: snap_state violates declarative reachability invariant
    assert snap_state not in reachable_from_source
    for count_val, origin_val, is_cyclic in reachable_from_source:
        assert count_val >= 0 and origin_val == "source" and not is_cyclic

    return {
        "two_way_equal_slot_path": two_way_eq_path,
        "two_way_unequal_slot_path": two_way_neq_path,
        "migrated_point_slots": reloaded_heap.objects[reloaded_roots["alias_a"]].slots,
        "identity_hash_preserved": reloaded_heap.identity_hash_of(reloaded_roots["alias_a"]) == orig_hash,
        "forwarding_misses_before_gc": misses_before_gc,
        "forwarders_reclaimed_by_gc": reclaimed,
        "image_drift_snap_state": list(snap_state),
        "image_drift_witness_unreachable_from_source": True,
        "snapshot_size_bytes": len(snap_bytes),
    }


# =============================================================================
# PART C: Oberon `.smb` Whole-Module Keys vs. Crelier Per-Export Fingerprints
# =============================================================================

@dataclass(frozen=True)
class FieldSpec:
    name: str
    typ: str
    offset: int
    exported: bool
    is_pointer: bool = False


@dataclass(frozen=True)
class RecordExport:
    name: str
    base: str | None
    ext_level: int
    byte_size: int
    fields: tuple[FieldSpec, ...]


@dataclass(frozen=True)
class ProcExport:
    name: str
    params: tuple[tuple[str, bool], ...]  # (type_name, is_var_param)
    ret_type: str


@dataclass(frozen=True)
class ConstExport:
    name: str
    typ: str
    value: int


@dataclass(frozen=True)
class ModuleVersion:
    name: str
    timestamp_48bit: tuple[int, int, int]  # (net, host, compile_time) for Mesa/Cedar .bcd
    body_revision: int
    records: tuple[RecordExport, ...]
    procs: tuple[ProcExport, ...]
    consts: tuple[ConstExport, ...]


def serialize_oberon_smb(mod: ModuleVersion) -> bytes:
    """Serialize exported interface + hidden-pointer offsets (mirrors ORB.Export/FindHiddenPointers)."""
    parts: list[str] = [f"MOD:{mod.name}"]
    for r in mod.records:
        # Visible fields + hidden pointer offsets (ORB.Mod:259-288)
        vis = [(f.name, f.typ, f.offset) for f in r.fields if f.exported]
        hid_ptrs = [f.offset for f in r.fields if not f.exported and f.is_pointer]
        parts.append(f"REC:{r.name}|base={r.base}|lvl={r.ext_level}|sz={r.byte_size}|vis={vis}|hptr={hid_ptrs}")
    for p in mod.procs:
        parts.append(f"PROC:{p.name}|params={list(p.params)}|ret={p.ret_type}")
    for c in mod.consts:
        parts.append(f"CONST:{c.name}|typ={c.typ}|val={c.value}")
    raw = "\n".join(parts).encode("utf-8")
    pad = (-len(raw)) % 4
    return raw + b"\x00" * pad


def oberon_2013_module_key(mod: ModuleVersion) -> int:
    """32-bit additive word checksum of .smb file (exact algorithm of ORB.Mod:343-344)."""
    smb = serialize_oberon_smb(mod)
    total = 0
    for (word,) in struct.iter_unpack("<I", smb):
        total = (total + word) & 0xFFFFFFFF
    return total


def crelier_fp32(payload: str) -> int:
    """Deterministic 32-bit structural fingerprint for per-export compatibility checking."""
    digest = hashlib.sha256(payload.encode("utf-8")).digest()
    return struct.unpack("<I", digest[:4])[0]


def crelier_export_fingerprints(mod: ModuleVersion) -> dict[str, dict[str, int]]:
    """Crelier (1994) per-export PB (public) and PV (private/layout/GC) fingerprints."""
    fps: dict[str, dict[str, int]] = {}
    for r in mod.records:
        vis = [(f.name, f.typ, f.offset) for f in r.fields if f.exported]
        hid_ptrs = [f.offset for f in r.fields if not f.exported and f.is_pointer]
        # PB covers public field types/offsets; PV additionally covers total byte_size + hidden GC ptrs
        pb = crelier_fp32(f"REC_PB:{mod.name}.{r.name}|base={r.base}|lvl={r.ext_level}|vis={vis}")
        pv = crelier_fp32(f"REC_PV:{pb}|sz={r.byte_size}|hptr={hid_ptrs}")
        fps[r.name] = {"pb": pb, "pv": pv}
    for p in mod.procs:
        pb = crelier_fp32(f"PROC_PB:{mod.name}.{p.name}|params={list(p.params)}|ret={p.ret_type}")
        fps[p.name] = {"pb": pb, "pv": pb}
    for c in mod.consts:
        pb = crelier_fp32(f"CONST_PB:{mod.name}.{c.name}|typ={c.typ}|val={c.value}")
        fps[c.name] = {"pb": pb, "pv": pb}
    return fps


@dataclass(frozen=True)
class ClientBinary:
    name: str
    imported_module: str
    # Recorded at compile time of the client:
    expected_bcd_stamp: tuple[int, int, int]
    expected_oberon_key: int
    # Per-export requirements: item_name -> need_pv (True for record extension/value allocation)
    crelier_imports: dict[str, tuple[str, int]]  # item_name -> ("pb"|"pv", expected_fp)
    unix_symbols: tuple[str, ...]


def compile_client(name: str, provider: ModuleVersion, uses: dict[str, str]) -> ClientBinary:
    fps = crelier_export_fingerprints(provider)
    crelier_req = {item: (mode, fps[item][mode]) for item, mode in uses.items()}
    return ClientBinary(
        name=name,
        imported_module=provider.name,
        expected_bcd_stamp=provider.timestamp_48bit,
        expected_oberon_key=oberon_2013_module_key(provider),
        crelier_imports=crelier_req,
        unix_symbols=tuple(sorted(uses.keys())),
    )


def check_link_compatibility(client: ClientBinary, loaded: ModuleVersion) -> dict[str, str]:
    """Return link result ('OK' or 'REJECT') under each of the four linking regimes."""
    # 1. Mesa/Cedar .bcd 48-bit version stamp
    mesa_ok = client.expected_bcd_stamp == loaded.timestamp_48bit

    # 2. Project Oberon 2013 Modules.Load key check (Modules.Mod:73)
    oberon_ok = client.expected_oberon_key == oberon_2013_module_key(loaded)

    # 3. Crelier (1994) per-export PB/PV structural fingerprint check
    loaded_fps = crelier_export_fingerprints(loaded)
    crelier_ok = all(
        item in loaded_fps and loaded_fps[item][mode] == expected_fp
        for item, (mode, expected_fp) in client.crelier_imports.items()
    )

    # 4. Untyped Unix/ELF C linker: checks only exported symbol-name existence
    exported_names = (
        {r.name for r in loaded.records}
        | {p.name for p in loaded.procs}
        | {c.name for c in loaded.consts}
    )
    unix_ok = all(sym in exported_names for sym in client.unix_symbols)

    return {
        "mesa_bcd_stamp": "OK" if mesa_ok else "REJECT",
        "oberon2013_smb_key": "OK" if oberon_ok else "REJECT",
        "crelier_export_fp": "OK" if crelier_ok else "REJECT",
        "untyped_elf_symbols": "OK" if unix_ok else "REJECT",
    }


def run_probe_c_oberon_fingerprints() -> dict[str, Any]:
    # Baseline Display module v0
    base_frame = RecordExport(
        name="Frame",
        base=None,
        ext_level=0,
        byte_size=12,
        fields=(
            FieldSpec("x", "INTEGER", 0, exported=True),
            FieldSpec("y", "INTEGER", 4, exported=True),
            FieldSpec("priv_flags", "INTEGER", 8, exported=False, is_pointer=False),
        ),
    )
    draw_proc = ProcExport("Draw", (("INTEGER", False), ("INTEGER", False)), "VOID")
    v0 = ModuleVersion(
        name="Display",
        timestamp_48bit=(1, 42, 1000),
        body_revision=1,
        records=(base_frame,),
        procs=(draw_proc,),
        consts=(),
    )

    # Two distinct clients compiled against v0:
    # - ClientDrawOnly imports ONLY Display.Draw (does not depend on Frame layout)
    # - ClientExtFrame extends Display.Frame (depends on Frame PV size + hidden GC pointers!)
    client_draw = compile_client("ClientDrawOnly", v0, {"Draw": "pb"})
    client_ext = compile_client("ClientExtFrame", v0, {"Draw": "pb", "Frame": "pv"})

    # Evolution scenarios:
    evolutions: list[tuple[str, ModuleVersion]] = [
        (
            "E1_body_only_edit",
            ModuleVersion(
                name="Display",
                # Assume DEFINITIONS file untouched in Mesa -> same stamp, body changed
                timestamp_48bit=(1, 42, 1000),
                body_revision=2,
                records=(base_frame,),
                procs=(draw_proc,),
                consts=(),
            ),
        ),
        (
            "E2_add_unrelated_export",
            ModuleVersion(
                name="Display",
                timestamp_48bit=(1, 42, 1001),
                body_revision=3,
                records=(base_frame,),
                procs=(draw_proc,),
                consts=(ConstExport("LogLevel", "INTEGER", 2),),
            ),
        ),
        (
            "E3_hidden_field_size_drift",
            ModuleVersion(
                name="Display",
                timestamp_48bit=(1, 42, 1002),
                body_revision=4,
                records=(
                    RecordExport(
                        name="Frame",
                        base=None,
                        ext_level=0,
                        byte_size=16,  # Grew by 4 bytes! Breaks subclass field offsets!
                        fields=(
                            FieldSpec("x", "INTEGER", 0, exported=True),
                            FieldSpec("y", "INTEGER", 4, exported=True),
                            FieldSpec("priv_flags", "INTEGER", 8, exported=False, is_pointer=False),
                            FieldSpec("priv_cache", "INTEGER", 12, exported=False, is_pointer=False),
                        ),
                    ),
                ),
                procs=(draw_proc,),
                consts=(),
            ),
        ),
        (
            "E4_hidden_gc_pointer_drift_same_size",
            ModuleVersion(
                name="Display",
                timestamp_48bit=(1, 42, 1003),
                body_revision=5,
                records=(
                    RecordExport(
                        name="Frame",
                        base=None,
                        ext_level=0,
                        byte_size=12,  # IDENTICAL byte size, but offset 8 became a traced POINTER!
                        fields=(
                            FieldSpec("x", "INTEGER", 0, exported=True),
                            FieldSpec("y", "INTEGER", 4, exported=True),
                            FieldSpec("priv_buf", "POINTER", 8, exported=False, is_pointer=True),
                        ),
                    ),
                ),
                procs=(draw_proc,),
                consts=(),
            ),
        ),
        (
            "E5_draw_signature_abi_change",
            ModuleVersion(
                name="Display",
                timestamp_48bit=(1, 42, 1004),
                body_revision=6,
                records=(base_frame,),
                procs=(ProcExport("Draw", (("REAL", False), ("REAL", False)), "VOID"),),
                consts=(),
            ),
        ),
    ]

    matrix: dict[str, dict[str, dict[str, str]]] = {}
    for label, mod_v in evolutions:
        matrix[label] = {
            client_draw.name: check_link_compatibility(client_draw, mod_v),
            client_ext.name: check_link_compatibility(client_ext, mod_v),
        }

    # Verify exact discriminating properties:
    # E1: All four accept body-only edit
    assert all(v == "OK" for v in matrix["E1_body_only_edit"]["ClientDrawOnly"].values())
    assert all(v == "OK" for v in matrix["E1_body_only_edit"]["ClientExtFrame"].values())

    # E2: Adding unrelated export invalidates Oberon-2013 whole-module key & Mesa stamp,
    #     but Crelier per-export fingerprints allow BOTH existing clients without recompilation!
    assert matrix["E2_add_unrelated_export"]["ClientDrawOnly"]["oberon2013_smb_key"] == "REJECT"
    assert matrix["E2_add_unrelated_export"]["ClientDrawOnly"]["crelier_export_fp"] == "OK"
    assert matrix["E2_add_unrelated_export"]["ClientExtFrame"]["crelier_export_fp"] == "OK"

    # E3: Hidden field size change breaks ClientExtFrame in Mesa, Oberon-2013, and Crelier,
    #     while Crelier still permits non-consumer ClientDrawOnly; untyped ELF SILENTLY ACCEPTS BOTH!
    assert matrix["E3_hidden_field_size_drift"]["ClientExtFrame"]["oberon2013_smb_key"] == "REJECT"
    assert matrix["E3_hidden_field_size_drift"]["ClientExtFrame"]["crelier_export_fp"] == "REJECT"
    assert matrix["E3_hidden_field_size_drift"]["ClientDrawOnly"]["crelier_export_fp"] == "OK"
    assert matrix["E3_hidden_field_size_drift"]["ClientExtFrame"]["untyped_elf_symbols"] == "OK"

    # E4: Hidden GC-pointer offset change at constant byte size is caught by Oberon-2013 & Crelier PV
    #     (thanks to FindHiddenPointers metadata), while Crelier still permits ClientDrawOnly!
    assert matrix["E4_hidden_gc_pointer_drift_same_size"]["ClientExtFrame"]["oberon2013_smb_key"] == "REJECT"
    assert matrix["E4_hidden_gc_pointer_drift_same_size"]["ClientExtFrame"]["crelier_export_fp"] == "REJECT"
    assert matrix["E4_hidden_gc_pointer_drift_same_size"]["ClientDrawOnly"]["crelier_export_fp"] == "OK"
    assert matrix["E4_hidden_gc_pointer_drift_same_size"]["ClientExtFrame"]["untyped_elf_symbols"] == "OK"

    # E5: Procedure signature change rejected by Mesa, Oberon-2013, and Crelier, silently accepted by ELF!
    assert matrix["E5_draw_signature_abi_change"]["ClientDrawOnly"]["oberon2013_smb_key"] == "REJECT"
    assert matrix["E5_draw_signature_abi_change"]["ClientDrawOnly"]["crelier_export_fp"] == "REJECT"
    assert matrix["E5_draw_signature_abi_change"]["ClientDrawOnly"]["untyped_elf_symbols"] == "OK"

    return {
        "v0_oberon2013_key_hex": f"0x{oberon_2013_module_key(v0):08x}",
        "v0_crelier_fps": {
            k: {m: f"0x{val:08x}" for m, val in v.items()}
            for k, v in crelier_export_fingerprints(v0).items()
        },
        "evolution_matrix": matrix,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit structured JSON summary")
    args = ap.parse_args()

    res_a = run_probe_a_unison()
    res_b = run_probe_b_smalltalk_spur()
    res_c = run_probe_c_oberon_fingerprints()

    summary = {
        "probe_a_unison_content_addressing": res_a,
        "probe_b_smalltalk_spur_image_drift": res_b,
        "probe_c_oberon_crelier_fingerprints": res_c,
        "all_assertions_passed": True,
    }

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("[PASS] Probe A (Unison SHA3-512 ABT hashing & diamond coexistence):")
        print(f"       scale={res_a['scale_hash_short']} pipeline={res_a['pipeline_hash_short']} (0 rebuilds on alpha/namespace rename)")
        print(f"       diamond norm v1={res_a['diamond_math_v1_hash']} vs v2={res_a['diamond_math_v2_hash']} -> combined(5)={res_a['diamond_eval_5']}")
        print(f"       symmetric cycle ambiguity detected: {res_a['symmetric_cycle_detected']}; asymmetric even/odd: {res_a['asymmetric_cycle_refs']}")
        print("[PASS] Probe B (Smalltalk/Spur become: forwarding & image-drift witness):")
        print(f"       migrated Point slots={res_b['migrated_point_slots']} identity_hash_preserved={res_b['identity_hash_preserved']} misses_before_gc={res_b['forwarding_misses_before_gc']} reclaimed={res_b['forwarders_reclaimed_by_gc']}")
        print(f"       image-drift witness state={res_b['image_drift_snap_state']} unreachable_from_source={res_b['image_drift_witness_unreachable_from_source']} (snapshot={res_b['snapshot_size_bytes']}B)")
        print("[PASS] Probe C (Mesa .bcd / Oberon-2013 .smb / Crelier PB+PV / Untyped ELF):")
        print(f"       Display v0 Oberon-2013 key={res_c['v0_oberon2013_key_hex']} Crelier FPs={res_c['v0_crelier_fps']}")
        for evo, clients in res_c["evolution_matrix"].items():
            d = clients["ClientDrawOnly"]
            e = clients["ClientExtFrame"]
            print(
                f"       {evo:38s} | DrawOnly[M={d['mesa_bcd_stamp']}, O={d['oberon2013_smb_key']}, C={d['crelier_export_fp']}, ELF={d['untyped_elf_symbols']}]"
                f" | ExtFrame[M={e['mesa_bcd_stamp']}, O={e['oberon2013_smb_key']}, C={e['crelier_export_fp']}, ELF={e['untyped_elf_symbols']}]"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
