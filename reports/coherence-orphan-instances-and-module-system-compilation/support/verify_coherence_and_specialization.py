#!/usr/bin/env python3
"""Standalone executable models for coherence, orphan rules, specialization soundness,
and ML functor / recursive-module type identity.

Requires Python 3.10+ (standard library only). Exits 0 iff all invariant checks
and counterexample witnesses succeed.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
import json
from typing import Callable, Generic, TypeVar


# =============================================================================
# PART A: Global Coherence & BTreeSet Invariant Corruption vs. Branded Types
# =============================================================================

K = TypeVar("K")


@dataclass
class BstNode(Generic[K]):
    key: K
    left: BstNode[K] | None = None
    right: BstNode[K] | None = None


def bst_insert(root: BstNode[K] | None, key: K, cmp: Callable[[K, K], int]) -> BstNode[K]:
    if root is None:
        return BstNode(key)
    c = cmp(key, root.key)
    if c < 0:
        return BstNode(root.key, bst_insert(root.left, key, cmp), root.right)
    if c > 0:
        return BstNode(root.key, root.left, bst_insert(root.right, key, cmp))
    return root


def bst_contains(root: BstNode[K] | None, key: K, cmp: Callable[[K, K], int]) -> bool:
    cur = root
    while cur is not None:
        c = cmp(key, cur.key)
        if c == 0:
            return True
        cur = cur.left if c < 0 else cur.right
    return False


def bst_inorder(root: BstNode[K] | None) -> list[K]:
    if root is None:
        return []
    return bst_inorder(root.left) + [root.key] + bst_inorder(root.right)


def is_valid_bst(root: BstNode[K] | None, cmp: Callable[[K, K], int]) -> bool:
    elems = bst_inorder(root)
    return all(cmp(elems[i], elems[i + 1]) < 0 for i in range(len(elems) - 1))


@dataclass(frozen=True)
class OrdInstance(Generic[K]):
    brand: str
    cmp: Callable[[K, K], int]


class BrandMismatchError(TypeError):
    """Static type error: two collections carry incompatible Ord instance brands."""


@dataclass(frozen=True)
class BrandedSet(Generic[K]):
    """Set whose type identity is indexed by the Ord instance brand (phantom/module tag)."""

    ord_brand: str
    root: BstNode[K] | None = None

    def insert(self, key: K, inst: OrdInstance[K]) -> BrandedSet[K]:
        if inst.brand != self.ord_brand:
            raise BrandMismatchError(
                f"cannot insert with Ord brand {inst.brand!r} into Set branded {self.ord_brand!r}"
            )
        return BrandedSet(self.ord_brand, bst_insert(self.root, key, inst.cmp))

    def contains(self, key: K, inst: OrdInstance[K]) -> bool:
        if inst.brand != self.ord_brand:
            raise BrandMismatchError(
                f"cannot query with Ord brand {inst.brand!r} on Set branded {self.ord_brand!r}"
            )
        return bst_contains(self.root, key, inst.cmp)

    def union(self, other: BrandedSet[K], inst: OrdInstance[K]) -> BrandedSet[K]:
        if self.ord_brand != other.ord_brand or inst.brand != self.ord_brand:
            raise BrandMismatchError(
                f"cannot union Set[{self.ord_brand}] and Set[{other.ord_brand}] under {inst.brand}"
            )
        merged = self.root
        for k in bst_inorder(other.root):
            merged = bst_insert(merged, k, inst.cmp)
        return BrandedSet(self.ord_brand, merged)


def probe_a_btreeset_coherence() -> dict[str, object]:
    asc_cmp = lambda a, b: (a > b) - (a < b)
    desc_cmp = lambda a, b: (b > a) - (b < a)

    # Unbranded (incoherent local instances): Set<int> does not record Ord identity.
    s_mod1: BstNode[int] | None = None
    for k in (30, 10, 50, 20, 40):
        s_mod1 = bst_insert(s_mod1, k, asc_cmp)

    assert is_valid_bst(s_mod1, asc_cmp)
    assert bst_contains(s_mod1, 10, asc_cmp) is True

    # Module 2 uses local descending Ord on the same Set<int> value.
    # 10 < 30 under asc, so 10 lives in left subtree; under desc, desc_cmp(10, 30) > 0,
    # so Module 2 searches the right subtree and misses an element present in the tree.
    lookup_under_desc = bst_contains(s_mod1, 10, desc_cmp)
    assert lookup_under_desc is False, "expected silent lookup miss under mismatched local Ord"
    assert 10 in bst_inorder(s_mod1), "10 is physically stored in the tree"

    # Module 2 inserts 25 under descending Ord (desc_cmp(25, 30) > 0 -> goes right -> right of 50).
    corrupted = bst_insert(s_mod1, 25, desc_cmp)
    corrupted_order = bst_inorder(corrupted)
    valid_under_asc = is_valid_bst(corrupted, asc_cmp)
    valid_under_desc = is_valid_bst(corrupted, desc_cmp)
    assert not valid_under_asc, "corrupted tree must violate ascending BST invariant"
    assert not valid_under_desc, "corrupted tree must violate descending BST invariant"

    # Branded / functor-indexed sets statically forbid cross-dictionary mixing.
    ord_asc = OrdInstance("IntOrdAsc", asc_cmp)
    ord_desc = OrdInstance("IntOrdDesc", desc_cmp)
    bs1: BrandedSet[int] = BrandedSet(ord_asc.brand)
    for k in (30, 10, 50):
        bs1 = bs1.insert(k, ord_asc)
    bs2: BrandedSet[int] = BrandedSet(ord_desc.brand).insert(25, ord_desc)

    mismatch_blocked = False
    try:
        bs1.union(bs2, ord_desc)
    except BrandMismatchError:
        mismatch_blocked = True
    assert mismatch_blocked

    # Same-brand union succeeds and preserves BST invariant.
    bs3 = BrandedSet(ord_asc.brand).insert(25, ord_asc)
    merged = bs1.union(bs3, ord_asc)
    assert is_valid_bst(merged.root, asc_cmp)
    assert bst_inorder(merged.root) == [10, 25, 30, 50]

    return {
        "unbranded_inorder_before": bst_inorder(s_mod1),
        "silent_lookup_miss_for_10": not lookup_under_desc,
        "corrupted_inorder_after_desc_insert_25": corrupted_order,
        "corrupted_valid_under_asc": valid_under_asc,
        "corrupted_valid_under_desc": valid_under_desc,
        "branded_cross_union_rejected": mismatch_blocked,
        "branded_same_ord_union": bst_inorder(merged.root),
    }


# =============================================================================
# PART B: Rust RFC 1023 / RFC 2451 Orphan Check & Knowability Checker
# =============================================================================


class InCrate(Enum):
    LOCAL_PROPER = auto()
    LOCAL_COMPAT = auto()
    REMOTE = auto()


class OrphanOutcome(Enum):
    OK = "ok"
    UNCOVERED_TY_PARAM = "uncovered_ty_param"
    NON_LOCAL_INPUT_TYPE = "non_local_input_type"


class Knowability(Enum):
    KNOWABLE = "knowable"
    CONFLICT_DOWNSTREAM = "conflict_downstream"
    CONFLICT_UPSTREAM = "conflict_upstream"


@dataclass(frozen=True)
class Ty:
    pass


@dataclass(frozen=True)
class PrimitiveTy(Ty):
    name: str


@dataclass(frozen=True)
class AdtTy(Ty):
    name: str
    crate: str
    args: tuple[Ty, ...] = ()
    fundamental: bool = False


@dataclass(frozen=True)
class RefTy(Ty):
    inner: Ty
    mutable: bool = False


@dataclass(frozen=True)
class DynTraitTy(Ty):
    principal_name: str
    principal_crate: str


@dataclass(frozen=True)
class OpaqueTy(Ty):
    name: str
    crate: str  # Always treated as non-local per rustc_next_trait_solver/src/coherence.rs:390-406


@dataclass(frozen=True)
class ParamTy(Ty):
    name: str


@dataclass(frozen=True)
class ProjectionTy(Ty):
    self_ty: Ty
    trait_name: str
    assoc_name: str


@dataclass(frozen=True)
class TraitDef:
    name: str
    crate: str
    fundamental: bool = False


@dataclass(frozen=True)
class TraitRef:
    trait: TraitDef
    self_ty: Ty
    args: tuple[Ty, ...] = ()

    @property
    def input_tys(self) -> tuple[Ty, ...]:
        return (self.self_ty, *self.args)


def has_param(ty: Ty) -> bool:
    match ty:
        case ParamTy():
            return True
        case AdtTy(args=args):
            return any(has_param(a) for a in args)
        case RefTy(inner=inner):
            return has_param(inner)
        case ProjectionTy(self_ty=s):
            return has_param(s)
        case _:
            return False


def orphan_check_trait_ref(
    trait_ref: TraitRef,
    current_crate: str,
    mode: InCrate,
    *,
    allow_local_trait_shortcut: bool = True,
) -> tuple[OrphanOutcome, str]:
    """Model of rustc_next_trait_solver::coherence::orphan_check_trait_ref (RFC 2451)."""
    if allow_local_trait_shortcut and mode != InCrate.REMOTE and trait_ref.trait.crate == current_crate:
        return (OrphanOutcome.OK, "local_trait")

    def is_local_crate(crate: str) -> bool:
        return mode != InCrate.REMOTE and crate == current_crate

    def visit(ty: Ty) -> tuple[OrphanOutcome, str] | None:
        """Returns Some(early_exit) on LocalTy or UncoveredTyParam, None to continue."""
        match ty:
            case PrimitiveTy():
                return None
            case ParamTy(name=n):
                if mode == InCrate.REMOTE:
                    return (OrphanOutcome.OK, f"remote_may_instantiate_local({n})")
                return (OrphanOutcome.UNCOVERED_TY_PARAM, f"uncovered_param({n})")
            case ProjectionTy() as proj:
                if has_param(proj):
                    if mode == InCrate.REMOTE:
                        return (OrphanOutcome.OK, "remote_projection_with_param")
                    if mode == InCrate.LOCAL_COMPAT:
                        # Unsound backward-compatibility mode (rustc #124559 / #99554)
                        return None
                    return (OrphanOutcome.UNCOVERED_TY_PARAM, f"uncovered_param_in_projection({proj.assoc_name})")
                return None
            case OpaqueTy():
                # Opaque types are non-local even in defining crate (coherence.rs:390-406)
                return None
            case RefTy(inner=inner):
                # References are fundamental: look inside without covering
                return visit(inner)
            case AdtTy(name=name, crate=crate, args=args, fundamental=is_fund):
                if is_local_crate(crate):
                    return (OrphanOutcome.OK, f"local_adt({name})")
                if is_fund:
                    # Box<T, A> only inspects T (args[0]); general fundamental inspects all args
                    inspect_args = args[:1] if name == "Box" and args else args
                    for a in inspect_args:
                        res = visit(a)
                        if res is not None:
                            return res
                    return None
                return None
            case DynTraitTy(principal_name=pname, principal_crate=pcrate):
                if is_local_crate(pcrate):
                    return (OrphanOutcome.OK, f"local_dyn_trait({pname})")
                return None
            case _:
                return None

    for t in trait_ref.input_tys:
        res = visit(t)
        if res is not None:
            return res
    return (OrphanOutcome.NON_LOCAL_INPUT_TYPE, "no_local_input_type")


def trait_ref_is_knowable(trait_ref: TraitRef, current_crate: str) -> Knowability:
    """Model of rustc_next_trait_solver::coherence::trait_ref_is_knowable (coherence.rs:48-94)."""
    remote_res, _ = orphan_check_trait_ref(
        trait_ref, current_crate, InCrate.REMOTE, allow_local_trait_shortcut=False
    )
    if remote_res == OrphanOutcome.OK:
        return Knowability.CONFLICT_DOWNSTREAM

    if trait_ref.trait.crate == current_crate or trait_ref.trait.fundamental:
        return Knowability.KNOWABLE

    local_res, _ = orphan_check_trait_ref(
        trait_ref, current_crate, InCrate.LOCAL_PROPER, allow_local_trait_shortcut=False
    )
    if local_res == OrphanOutcome.OK:
        return Knowability.KNOWABLE
    return Knowability.CONFLICT_UPSTREAM


def probe_b_rust_orphan_and_knowability() -> dict[str, object]:
    T = ParamTy("T")
    str_ref = RefTy(PrimitiveTy("str"))
    local_ty = AdtTy("MyLocal", "crate_a")
    sibling_ty = AdtTy("SiblingTy", "crate_b")
    foreign_ty = AdtTy("Foreign", "upstream")
    vec_t = AdtTy("Vec", "alloc", (T,), fundamental=False)
    vec_local = AdtTy("Vec", "alloc", (local_ty,), fundamental=False)
    box_local = AdtTy("Box", "alloc", (local_ty, AdtTy("Global", "alloc")), fundamental=True)
    box_t = AdtTy("Box", "alloc", (T, AdtTy("Global", "alloc")), fundamental=True)
    pin_box_local = RefTy(AdtTy("Pin", "core", (box_local,), fundamental=True), mutable=True)
    local_opaque = OpaqueTy("LocalOpaque", "crate_a")
    local_dyn = DynTraitTy("LocalErr", "crate_a")

    f_trait = TraitDef("ForeignTrait", "upstream", fundamental=False)
    l_trait = TraitDef("LocalTrait", "crate_a", fundamental=False)
    fn_mut = TraitDef("FnMut", "core", fundamental=True)

    cases: list[tuple[str, TraitRef, InCrate, OrphanOutcome]] = [
        ("local_trait_for_param", TraitRef(l_trait, T), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("foreign_trait_for_local", TraitRef(f_trait, local_ty), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("foreign_trait_for_box_local", TraitRef(f_trait, box_local), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("foreign_trait_for_mut_pin_box_local", TraitRef(f_trait, pin_box_local), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("foreign_trait_for_box_dyn_local", TraitRef(f_trait, AdtTy("Box", "alloc", (local_dyn,), fundamental=True)), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("foreign_trait_for_vec_local", TraitRef(f_trait, vec_local), InCrate.LOCAL_PROPER, OrphanOutcome.NON_LOCAL_INPUT_TYPE),
        ("rfc2451_vec_t_covered_before_local", TraitRef(f_trait, vec_t, (local_ty,)), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("rfc2451_box_t_uncovered_before_local", TraitRef(f_trait, box_t, (local_ty,)), InCrate.LOCAL_PROPER, OrphanOutcome.UNCOVERED_TY_PARAM),
        ("foreign_trait_for_uncovered_t_with_local_arg", TraitRef(f_trait, T, (local_ty,)), InCrate.LOCAL_PROPER, OrphanOutcome.UNCOVERED_TY_PARAM),
        ("ordered_local_before_t", TraitRef(f_trait, foreign_ty, (local_ty, T)), InCrate.LOCAL_PROPER, OrphanOutcome.OK),
        ("ordered_t_before_local", TraitRef(f_trait, foreign_ty, (T, local_ty)), InCrate.LOCAL_PROPER, OrphanOutcome.UNCOVERED_TY_PARAM),
        ("opaque_type_treated_nonlocal", TraitRef(f_trait, local_opaque), InCrate.LOCAL_PROPER, OrphanOutcome.NON_LOCAL_INPUT_TYPE),
        (
            "projection_proper_rejects_uncovered_param",
            TraitRef(f_trait, ProjectionTy(T, "Id", "Assoc"), (local_ty,)),
            InCrate.LOCAL_PROPER,
            OrphanOutcome.UNCOVERED_TY_PARAM,
        ),
        (
            "projection_compat_unsoundly_accepts",
            TraitRef(f_trait, ProjectionTy(T, "Id", "Assoc"), (local_ty,)),
            InCrate.LOCAL_COMPAT,
            OrphanOutcome.OK,
        ),
    ]

    results = {}
    for label, tref, mode, expected in cases:
        actual, detail = orphan_check_trait_ref(tref, "crate_a", mode)
        assert actual == expected, f"{label}: expected {expected}, got {actual} ({detail})"
        results[label] = f"{actual.value} ({detail})"

    # Knowability checks (RFC 1023 negative reasoning):
    k_str_fnmut = trait_ref_is_knowable(TraitRef(fn_mut, str_ref), "regex")
    assert k_str_fnmut == Knowability.KNOWABLE
    k_str_foreign = trait_ref_is_knowable(TraitRef(f_trait, str_ref), "regex")
    assert k_str_foreign == Knowability.CONFLICT_UPSTREAM
    k_local_foreign = trait_ref_is_knowable(TraitRef(f_trait, local_ty), "crate_a")
    assert k_local_foreign == Knowability.KNOWABLE
    k_param_foreign = trait_ref_is_knowable(TraitRef(f_trait, T), "crate_a")
    assert k_param_foreign == Knowability.CONFLICT_DOWNSTREAM

    # Link-safety invariant (RFC 2451): for two mutually-unknowing sibling crates
    # crate_a and crate_b (neither can name the other's local ADTs), no pair of
    # proper-orphan-passing impls (impl_a in crate_a, impl_b in crate_b) can unify.
    def unify_tys(t1: Ty, t2: Ty, sub: dict[str, Ty]) -> bool:
        def resolve(t: Ty) -> Ty:
            while isinstance(t, ParamTy) and t.name in sub:
                t = sub[t.name]
            return t

        def occurs(var: str, t: Ty) -> bool:
            t = resolve(t)
            if isinstance(t, ParamTy):
                return t.name == var
            if isinstance(t, RefTy):
                return occurs(var, t.inner)
            if isinstance(t, AdtTy):
                return any(occurs(var, a) for a in t.args)
            return False

        t1, t2 = resolve(t1), resolve(t2)
        if t1 == t2:
            return True
        if isinstance(t1, ParamTy):
            if occurs(t1.name, t2):
                return False
            sub[t1.name] = t2
            return True
        if isinstance(t2, ParamTy):
            if occurs(t2.name, t1):
                return False
            sub[t2.name] = t1
            return True
        if isinstance(t1, RefTy) and isinstance(t2, RefTy) and t1.mutable == t2.mutable:
            return unify_tys(t1.inner, t2.inner, sub)
        if (
            isinstance(t1, AdtTy)
            and isinstance(t2, AdtTy)
            and t1.name == t2.name
            and t1.crate == t2.crate
            and len(t1.args) == len(t2.args)
        ):
            return all(unify_tys(a, b, sub) for a, b in zip(t1.args, t2.args))
        return False

    def impls_unify(tr1: TraitRef, tr2: TraitRef) -> bool:
        if tr1.trait != tr2.trait or len(tr1.input_tys) != len(tr2.input_tys):
            return False
        sub: dict[str, Ty] = {}
        return all(unify_tys(a, b, sub) for a, b in zip(tr1.input_tys, tr2.input_tys))

    def build_crate_pool(crate: str, local_name: str, param_prefix: str) -> list[Ty]:
        loc = AdtTy(local_name, crate)
        p = ParamTy(f"{param_prefix}0")
        return [
            PrimitiveTy("i32"),
            foreign_ty,
            p,
            loc,
            RefTy(loc),
            RefTy(p),
            AdtTy("Box", "alloc", (loc,), fundamental=True),
            AdtTy("Box", "alloc", (p,), fundamental=True),
            AdtTy("Vec", "alloc", (loc,), fundamental=False),
            AdtTy("Vec", "alloc", (p,), fundamental=False),
        ]

    pool_a = build_crate_pool("crate_a", "MyLocal", "A")
    pool_b = build_crate_pool("crate_b", "SiblingTy", "B")
    valid_a = [
        TraitRef(f_trait, s, (a,))
        for s in pool_a
        for a in pool_a
        if orphan_check_trait_ref(TraitRef(f_trait, s, (a,)), "crate_a", InCrate.LOCAL_PROPER)[0]
        == OrphanOutcome.OK
    ]
    valid_b = [
        TraitRef(f_trait, s, (a,))
        for s in pool_b
        for a in pool_b
        if orphan_check_trait_ref(TraitRef(f_trait, s, (a,)), "crate_b", InCrate.LOCAL_PROPER)[0]
        == OrphanOutcome.OK
    ]
    checked_pairs = 0
    for tra in valid_a:
        for trb in valid_b:
            checked_pairs += 1
            assert not impls_unify(tra, trb), f"Link-safety violated: {tra} unifies with {trb}"

    # Counterfactual check: bypassing ordering with `impl<B0> ForeignTrait<SiblingTy> for B0`
    # collides with crate_a's valid `impl<A0> ForeignTrait<A0> for MyLocal`.
    illegal_b = TraitRef(f_trait, ParamTy("B0"), (sibling_ty,))
    legal_a = TraitRef(f_trait, local_ty, (ParamTy("A0"),))
    assert orphan_check_trait_ref(illegal_b, "crate_b", InCrate.LOCAL_PROPER)[0] == OrphanOutcome.UNCOVERED_TY_PARAM
    assert orphan_check_trait_ref(legal_a, "crate_a", InCrate.LOCAL_PROPER)[0] == OrphanOutcome.OK
    assert impls_unify(legal_a, illegal_b) is True

    return {
        "orphan_matrix_passed": len(cases),
        "projection_compat_vs_proper_diverged": True,
        "knowability_str_fnmut": k_str_fnmut.value,
        "knowability_str_foreign": k_str_foreign.value,
        "knowability_local_foreign": k_local_foreign.value,
        "knowability_param_foreign": k_param_foreign.value,
        "valid_sibling_impls_per_crate": (len(valid_a), len(valid_b)),
        "link_safety_sibling_pairs_verified": checked_pairs,
        "ordering_bypass_collision_witnessed": True,
    }


# =============================================================================
# PART C: Specialization Lifetime-Erasure Unsoundness & min_specialization Gate
# =============================================================================


@dataclass(frozen=True)
class Region:
    name: str  # "'static", "'local", "'a", "'erased"


@dataclass(frozen=True)
class SpecTy:
    pass


@dataclass(frozen=True)
class SParam(SpecTy):
    name: str


@dataclass(frozen=True)
class SPrim(SpecTy):
    name: str


@dataclass(frozen=True)
class SRef(SpecTy):
    region: Region
    inner: SpecTy


@dataclass(frozen=True)
class STuple(SpecTy):
    elems: tuple[SpecTy, ...]


@dataclass(frozen=True)
class SAdt(SpecTy):
    name: str
    args: tuple[SpecTy | Region, ...] = ()


@dataclass(frozen=True)
class Predicate:
    kind: str  # "outlives_static" | "trait" | "projection" | "global"
    subject: str
    target: str
    always_applicable_trait: bool = False


@dataclass(frozen=True)
class SpecImpl:
    name: str
    trait: str
    generics: tuple[str, ...]
    self_ty: SpecTy
    trait_args: tuple[SpecTy | Region, ...] = ()
    predicates: tuple[Predicate, ...] = ()
    is_default: bool = False


def erase_regions(ty: SpecTy) -> SpecTy:
    erased = Region("'erased")
    match ty:
        case SRef(_, inner):
            return SRef(erased, erase_regions(inner))
        case STuple(elems):
            return STuple(tuple(erase_regions(e) for e in elems))
        case SAdt(name, args):
            return SAdt(name, tuple(erased if isinstance(a, Region) else erase_regions(a) for a in args))
        case _:
            return ty


def match_spec_pattern(
    pattern: SpecTy | Region,
    concrete: SpecTy | Region,
    subst: dict[str, SpecTy | Region],
) -> bool:
    if isinstance(pattern, Region):
        if not isinstance(concrete, Region):
            return False
        if pattern.name == "'static":
            return concrete.name in ("'static", "'erased")
        if pattern.name in subst:
            return subst[pattern.name] == concrete
        subst[pattern.name] = concrete
        return True

    if isinstance(concrete, Region):
        return False

    match pattern:
        case SParam(name):
            if name in subst:
                return subst[name] == concrete
            subst[name] = concrete
            return True
        case SPrim(name):
            return isinstance(concrete, SPrim) and concrete.name == name
        case SRef(pr, pinner):
            return (
                isinstance(concrete, SRef)
                and match_spec_pattern(pr, concrete.region, subst)
                and match_spec_pattern(pinner, concrete.inner, subst)
            )
        case STuple(pelems):
            return (
                isinstance(concrete, STuple)
                and len(pelems) == len(concrete.elems)
                and all(match_spec_pattern(p, c, subst) for p, c in zip(pelems, concrete.elems))
            )
        case SAdt(pname, pargs):
            return (
                isinstance(concrete, SAdt)
                and pname == concrete.name
                and len(pargs) == len(concrete.args)
                and all(match_spec_pattern(p, c, subst) for p, c in zip(pargs, concrete.args))
            )
        case _:
            return False


def satisfies_outlives_static(ty: SpecTy | Region) -> bool:
    if isinstance(ty, Region):
        return ty.name in ("'static", "'erased")
    match ty:
        case SPrim():
            return True
        case SRef(r, inner):
            return satisfies_outlives_static(r) and satisfies_outlives_static(inner)
        case STuple(elems):
            return all(satisfies_outlives_static(e) for e in elems)
        case SAdt(_, args):
            return all(satisfies_outlives_static(a) for a in args)
        case _:
            return False


def check_min_specialization(child: SpecImpl, parent: SpecImpl) -> tuple[bool, list[str]]:
    """Model of rustc_hir_analysis::impl_wf_check::min_specialization::check_always_applicable."""
    errors: list[str] = []

    subst: dict[str, SpecTy | Region] = {}
    ok = match_spec_pattern(parent.self_ty, child.self_ty, subst)
    for pa, ca in zip(parent.trait_args, child.trait_args):
        ok = ok and match_spec_pattern(pa, ca, subst)
    if not ok:
        return (False, ["child does not structurally specialize parent"])

    constrained_parent_params = {
        p.target for p in parent.predicates if p.kind == "projection"
    }
    unconstrained_parent_args = [
        v for k, v in subst.items() if k not in constrained_parent_params
    ]

    seen_params: list[str] = []
    has_static = False

    def walk(node: SpecTy | Region) -> None:
        nonlocal has_static
        if isinstance(node, Region):
            if node.name == "'static":
                has_static = True
            elif node.name in child.generics:
                seen_params.append(node.name)
            return
        match node:
            case SParam(n):
                if n in child.generics:
                    seen_params.append(n)
            case SRef(r, inner):
                walk(r)
                walk(inner)
            case STuple(elems):
                for e in elems:
                    walk(e)
            case SAdt(_, args):
                for a in args:
                    walk(a)

    for arg in unconstrained_parent_args:
        walk(arg)

    if has_static:
        errors.append("StaticSpecialize: cannot specialize on `'static` lifetime")

    dups = sorted({p for p in seen_params if seen_params.count(p) > 1})
    for d in dups:
        errors.append(f"DuplicateParam: specializing impl repeats parameter `{d}`")

    parent_preds_inst = set()
    for p in parent.predicates:
        subj = subst.get(p.subject, p.subject)
        subj_str = subj.name if isinstance(subj, (SParam, Region)) else str(subj)
        parent_preds_inst.add((p.kind, subj_str, p.target))

    for p in child.predicates:
        if p.kind == "global":
            continue
        if (p.kind, p.subject, p.target) in parent_preds_inst:
            continue
        if p.kind == "trait" and p.always_applicable_trait:
            continue
        errors.append(f"DisallowedPredicate: cannot specialize on {p.kind}({p.subject}: {p.target})")

    return (len(errors) == 0, errors)


def probe_c_specialization_lifetime_erasure() -> dict[str, object]:
    # Witness C1: 'static specialization soundness hole
    base_promote = SpecImpl("promote_default", "Promote", ("T",), SParam("T"), is_default=True)
    spec_promote = SpecImpl(
        "promote_static",
        "Promote",
        ("T",),
        SParam("T"),
        predicates=(Predicate("outlives_static", "T", "'static"),),
    )

    local_str_ty = SRef(Region("'local"), SPrim("str"))
    erased_str_ty = erase_regions(local_str_ty)

    pre_subst: dict[str, SpecTy | Region] = {}
    assert match_spec_pattern(spec_promote.self_ty, local_str_ty, pre_subst)
    c1_pre_applies = satisfies_outlives_static(pre_subst["T"])
    assert c1_pre_applies is False

    post_subst: dict[str, SpecTy | Region] = {}
    assert match_spec_pattern(spec_promote.self_ty, erased_str_ty, post_subst)
    c1_post_applies = satisfies_outlives_static(post_subst["T"])
    assert c1_post_applies is True

    # Witness C2: rust-lang/rust#40582 (make_static via repeated lifetime 'a)
    base_from_ref = SpecImpl(
        "from_ref_default",
        "FromRef",
        ("'a", "T", "R"),
        self_ty=SParam("R"),
        trait_args=(Region("'a"), SParam("T")),
        is_default=True,
    )
    spec_from_ref = SpecImpl(
        "from_ref_same_lifetime",
        "FromRef",
        ("'a", "T"),
        self_ty=SRef(Region("'a"), SParam("T")),
        trait_args=(Region("'a"), SParam("T")),
    )

    c2_pre_subst: dict[str, SpecTy | Region] = {}
    c2_pre_matches = (
        match_spec_pattern(spec_from_ref.self_ty, SRef(Region("'static"), SPrim("str")), c2_pre_subst)
        and match_spec_pattern(spec_from_ref.trait_args[0], Region("'local"), c2_pre_subst)
        and match_spec_pattern(spec_from_ref.trait_args[1], SPrim("str"), c2_pre_subst)
    )
    assert c2_pre_matches is False

    c2_post_subst: dict[str, SpecTy | Region] = {}
    c2_post_matches = (
        match_spec_pattern(spec_from_ref.self_ty, SRef(Region("'erased"), SPrim("str")), c2_post_subst)
        and match_spec_pattern(spec_from_ref.trait_args[0], Region("'erased"), c2_post_subst)
        and match_spec_pattern(spec_from_ref.trait_args[1], SPrim("str"), c2_post_subst)
    )
    assert c2_post_matches is True

    # Witness C3: Repeated type parameter (T, T) specializing T
    base_any = SpecImpl("x_default", "X", ("T",), SParam("T"), is_default=True)
    spec_pair_eq = SpecImpl("x_pair_eq", "X", ("T",), STuple((SParam("T"), SParam("T"))))
    pair_diff_lt = STuple((SRef(Region("'a"), SPrim("u8")), SRef(Region("'b"), SPrim("u8"))))
    c3_pre_matches = match_spec_pattern(spec_pair_eq.self_ty, pair_diff_lt, {})
    c3_post_matches = match_spec_pattern(spec_pair_eq.self_ty, erase_regions(pair_diff_lt), {})
    assert c3_pre_matches is False and c3_post_matches is True

    # Witness C4: Indirect non-always-applicable trait (Ord on Evil<'a, 'a>)
    spec_ord = SpecImpl(
        "slice_cmp_ord",
        "SliceCmp",
        ("T",),
        SParam("T"),
        predicates=(Predicate("trait", "T", "Ord", always_applicable_trait=False),),
    )

    # Positive Sound Case: SpecExtend<T> for VecIntoIter<T> specializing I: Iterator<Item = T>
    base_extend = SpecImpl(
        "spec_extend_default",
        "SpecExtend",
        ("T", "I"),
        self_ty=SParam("I"),
        trait_args=(SParam("T"),),
        predicates=(Predicate("projection", "I", "T"),),
        is_default=True,
    )
    spec_extend_vec = SpecImpl(
        "spec_extend_vec",
        "SpecExtend",
        ("T",),
        self_ty=SAdt("VecIntoIter", (SParam("T"),)),
        trait_args=(SParam("T"),),
    )

    ok_c1, err_c1 = check_min_specialization(spec_promote, base_promote)
    ok_c2, err_c2 = check_min_specialization(spec_from_ref, base_from_ref)
    ok_c3, err_c3 = check_min_specialization(spec_pair_eq, base_any)
    ok_c4, err_c4 = check_min_specialization(spec_ord, base_any)
    ok_static_ref, err_static_ref = check_min_specialization(
        SpecImpl("x_static_ref", "X", (), SRef(Region("'static"), SPrim("u8"))),
        base_any,
    )
    ok_sound, err_sound = check_min_specialization(spec_extend_vec, base_extend)

    assert not ok_c1 and any("outlives_static" in e for e in err_c1)
    assert not ok_c2 and any("repeats parameter" in e for e in err_c2)
    assert not ok_c3 and any("repeats parameter `T`" in e for e in err_c3)
    assert not ok_c4 and any("Ord" in e for e in err_c4)
    assert not ok_static_ref and any("StaticSpecialize" in e for e in err_static_ref)
    assert ok_sound and not err_sound

    return {
        "witness_c1_static_pre_vs_post": (c1_pre_applies, c1_post_applies),
        "witness_c2_issue_40582_pre_vs_post": (c2_pre_matches, c2_post_matches),
        "witness_c3_repeated_ty_param_pre_vs_post": (c3_pre_matches, c3_post_matches),
        "min_spec_rejects_c1_static_bound": err_c1,
        "min_spec_rejects_c2_issue_40582": err_c2,
        "min_spec_rejects_c3_pair_t_t": err_c3,
        "min_spec_rejects_c4_non_aa_ord": err_c4,
        "min_spec_rejects_static_ref": err_static_ref,
        "min_spec_accepts_vec_into_iter_projection": ok_sound,
    }


# =============================================================================
# PART D: Applicative vs. Generative Functors & Recursive Module Double Vision
# =============================================================================


@dataclass(frozen=True)
class ModTypeId:
    origin: str


class FunctorEngine:
    """Models OCaml-style applicative (path-indexed) vs. generative (stamped) functors."""

    def __init__(self) -> None:
        self._stamp = 0

    def apply_applicative(self, functor: str, arg_path: str | None, body_has_generative: bool) -> ModTypeId:
        if body_has_generative:
            raise ValueError("Not_allowed_in_functor_body: generative functor inside applicative functor")
        if arg_path is None:
            raise ValueError("Cannot_eliminate_dependency: anonymous module arg has no static path")
        return ModTypeId(f"{functor}({arg_path}).t")

    def apply_generative(self, functor: str) -> ModTypeId:
        self._stamp += 1
        return ModTypeId(f"{functor}()#stamp{self._stamp}.t")


def probe_d_modules_and_double_vision() -> dict[str, object]:
    eng = FunctorEngine()

    t_a = eng.apply_applicative("SetMake", "IntOrd", body_has_generative=False)
    t_b = eng.apply_applicative("SetMake", "IntOrd", body_has_generative=False)
    assert t_a == t_b

    g1 = eng.apply_generative("FreshKeyStore")
    g2 = eng.apply_generative("FreshKeyStore")
    assert g1 != g2

    gen_in_app_rejected = False
    try:
        eng.apply_applicative("BadApp", "IntOrd", body_has_generative=True)
    except ValueError as e:
        gen_in_app_rejected = "Not_allowed_in_functor_body" in str(e)
    assert gen_in_app_rejected

    anon_dep_rejected = False
    try:
        eng.apply_applicative("SetMake", None, body_has_generative=False)
    except ValueError as e:
        anon_dep_rejected = "Cannot_eliminate_dependency" in str(e)
    assert anon_dep_rejected

    naive_internal_type = "int"
    naive_external_forward_type = "Abstract(A.t)"
    naive_double_vision_error = naive_internal_type != naive_external_forward_type
    assert naive_double_vision_error

    dest_env_inside_A = {"dest_A_t": "int"}
    dest_env_outside_A: dict[str, str] = {}
    resolved_inside = dest_env_inside_A.get("dest_A_t", "dest_A_t")
    resolved_outside = dest_env_outside_A.get("dest_A_t", "dest_A_t")
    assert resolved_inside == "int"
    assert resolved_outside == "dest_A_t" and resolved_outside != "int"

    return {
        "applicative_diamond_equal": t_a == t_b,
        "generative_calls_distinct": g1 != g2,
        "generative_inside_applicative_rejected": gen_in_app_rejected,
        "anonymous_arg_dependency_rejected": anon_dep_rejected,
        "naive_recmodule_double_vision_conflict": naive_double_vision_error,
        "rtg_destination_passing_internal_transparent": resolved_inside == "int",
        "rtg_destination_passing_external_opaque": resolved_outside == "dest_A_t",
    }


def main() -> int:
    summary = {
        "part_a_btreeset_coherence": probe_a_btreeset_coherence(),
        "part_b_rust_orphan_and_knowability": probe_b_rust_orphan_and_knowability(),
        "part_c_specialization_lifetime_erasure": probe_c_specialization_lifetime_erasure(),
        "part_d_modules_and_double_vision": probe_d_modules_and_double_vision(),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
