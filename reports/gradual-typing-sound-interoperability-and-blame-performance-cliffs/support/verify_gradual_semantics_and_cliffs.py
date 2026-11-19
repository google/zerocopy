#!/usr/bin/env python3
"""Executable verification probe for gradual typing semantics, blame polarity,
space-efficient coercion collapse, complete monitoring, and 2^k lattice cliffs.

Models five runtime enforcement strategies over higher-order callbacks and
mutable arrays using only the Python 3.10+ standard library:
  1. Erasure (unsound, zero runtime overhead)
  2. Natural-Uncollapsed (deep higher-order proxies, unbounded wrapper chains)
  3. Natural-Collapsed (Herman-Tomb-Flanagan normalized coercions, O(1) depth)
  4. Transient (Vitousek et al. shallow tag checks, no proxies, no CM)
  5. Concrete (Muehlboeck-Tate / Static Python nominal tags on allocation)

Exits 0 iff all formal and scaling assertions hold.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


# ---------------------------------------------------------------------------
# 1. Type algebra, consistency (~), subtyping (<:, <:+ , <:-, <:n)
# ---------------------------------------------------------------------------

class Type:
    def height(self) -> int:
        raise NotImplementedError


@dataclass(frozen=True)
class Dyn(Type):
    def height(self) -> int:
        return 1

    def __str__(self) -> str:
        return "Dyn"


@dataclass(frozen=True)
class Base(Type):
    name: str  # "Int", "Bool", "Str"

    def height(self) -> int:
        return 1

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Fn(Type):
    dom: Type
    cod: Type

    def height(self) -> int:
        return 1 + max(self.dom.height(), self.cod.height())

    def __str__(self) -> str:
        return f"({self.dom} -> {self.cod})"


@dataclass(frozen=True)
class Ref(Type):
    elem: Type

    def height(self) -> int:
        return 1 + self.elem.height()

    def __str__(self) -> str:
        return f"Ref[{self.elem}]"


DYN = Dyn()
INT = Base("Int")
BOOL = Base("Bool")
STR = Base("Str")


def consistent(s: Type, t: Type) -> bool:
    """Siek & Taha (2006) type consistency (~): reflexive, symmetric, non-transitive."""
    if isinstance(s, Dyn) or isinstance(t, Dyn):
        return True
    if isinstance(s, Base) and isinstance(t, Base):
        return s.name == t.name
    if isinstance(s, Fn) and isinstance(t, Fn):
        return consistent(s.dom, t.dom) and consistent(s.cod, t.cod)
    if isinstance(s, Ref) and isinstance(t, Ref):
        return consistent(s.elem, t.elem)
    return False


def subtype(s: Type, t: Type) -> bool:
    """Wadler & Findler (2009) ordinary subtyping (<:) over base/Dyn/Fn/Ref."""
    if s == t:
        return True
    if isinstance(s, Fn) and isinstance(t, Fn):
        return subtype(t.dom, s.dom) and subtype(s.cod, t.cod)
    if isinstance(s, Ref) and isinstance(t, Ref):
        return subtype(s.elem, t.elem) and subtype(t.elem, s.elem)
    return False


def subtype_pos(s: Type, t: Type) -> bool:
    """Wadler & Findler (2009) positive subtyping (<:+): cast S => T cannot fail positively."""
    if isinstance(t, Dyn):
        return True
    if isinstance(s, Dyn):
        return False
    if isinstance(s, Base) and isinstance(t, Base):
        return s.name == t.name
    if isinstance(s, Fn) and isinstance(t, Fn):
        return subtype_neg(t.dom, s.dom) and subtype_pos(s.cod, t.cod)
    if isinstance(s, Ref) and isinstance(t, Ref):
        return subtype_pos(s.elem, t.elem) and subtype_neg(t.elem, s.elem)
    return False


def subtype_neg(s: Type, t: Type) -> bool:
    """Wadler & Findler (2009) negative subtyping (<:-): cast S => T cannot fail negatively."""
    if isinstance(s, Dyn):
        return True
    if isinstance(t, Dyn):
        return False
    if isinstance(s, Base) and isinstance(t, Base):
        return s.name == t.name
    if isinstance(s, Fn) and isinstance(t, Fn):
        return subtype_pos(t.dom, s.dom) and subtype_neg(s.cod, t.cod)
    if isinstance(s, Ref) and isinstance(t, Ref):
        return subtype_neg(s.elem, t.elem) and subtype_pos(t.elem, s.elem)
    return False


def subtype_naive(s: Type, t: Type) -> bool:
    """Wadler & Findler (2009) naive subtyping (<:n): S is more precise than T (covariant in all args)."""
    if isinstance(t, Dyn):
        return True
    if isinstance(s, Dyn):
        return False
    if isinstance(s, Base) and isinstance(t, Base):
        return s.name == t.name
    if isinstance(s, Fn) and isinstance(t, Fn):
        return subtype_naive(s.dom, t.dom) and subtype_naive(s.cod, t.cod)
    if isinstance(s, Ref) and isinstance(t, Ref):
        return subtype_naive(s.elem, t.elem)
    return False


def verify_type_relations() -> dict[str, Any]:
    # Generate all types up to depth 2 over {Dyn, Int, Bool}
    atoms: list[Type] = [DYN, INT, BOOL]
    depth1: list[Type] = list(atoms)
    for a in atoms:
        depth1.append(Ref(a))
        for b in atoms:
            depth1.append(Fn(a, b))
    # Add sample depth-2 types (higher-order & nested refs)
    universe: list[Type] = list(depth1)
    for a in [DYN, INT, Fn(INT, BOOL), Fn(DYN, INT), Ref(INT), Ref(DYN)]:
        universe.append(Fn(a, INT))
        universe.append(Fn(INT, a))
        universe.append(Ref(a))
    universe = list(dict.fromkeys(universe))

    # Siek & Taha Proposition 1: reflexivity, symmetry, non-transitivity
    for t in universe:
        assert consistent(t, t), f"Consistency not reflexive on {t}"
    for s in universe:
        for t in universe:
            assert consistent(s, t) == consistent(t, s), f"Consistency not symmetric on {s}, {t}"
    assert consistent(INT, DYN) and consistent(DYN, BOOL) and not consistent(INT, BOOL)

    # Wadler & Findler Propositions 8 & 9:
    #   S <: T  <=>  S <:+ T  and  S <:- T
    #   S <:n T <=>  S <:+ T  and  T <:- S
    checked_pairs = 0
    for s in universe:
        for t in universe:
            checked_pairs += 1
            assert subtype(s, t) == (subtype_pos(s, t) and subtype_neg(s, t)), (
                f"Prop 8 failed for {s}, {t}"
            )
            assert subtype_naive(s, t) == (subtype_pos(s, t) and subtype_neg(t, s)), (
                f"Prop 9 failed for {s}, {t}"
            )

    return {"universe_size": len(universe), "pairs_verified": checked_pairs}


# ---------------------------------------------------------------------------
# 2. Blame exception & Wadler-Findler higher-order + mutable-ref casts
# ---------------------------------------------------------------------------

class BlameError(Exception):
    def __init__(self, blamed: str, polarity: str, detail: str):
        super().__init__(f"BLAME[{polarity}:{blamed}]: {detail}")
        self.blamed = blamed
        self.polarity = polarity
        self.detail = detail


class RuntimeTagError(Exception):
    """Unblamed check error (e.g. blame-free Transient or Concrete check failure)."""


def is_base_value(v: Any, ty: Base) -> bool:
    if ty.name == "Int":
        # Note: in Python bool subclasses int; exclude bool from Int!
        return type(v) is int
    if ty.name == "Bool":
        return type(v) is bool
    if ty.name == "Str":
        return type(v) is str
    return False


@dataclass
class Metrics:
    boundary_casts: int = 0
    proxy_allocs: int = 0
    proxy_hops: int = 0
    tag_checks: int = 0
    coercion_compositions: int = 0
    max_proxy_depth: int = 0
    max_coercion_size: int = 0

    def note_depth(self, d: int) -> None:
        if d > self.max_proxy_depth:
            self.max_proxy_depth = d

    def note_csize(self, s: int) -> None:
        if s > self.max_coercion_size:
            self.max_coercion_size = s


class RawArray:
    """Mutable array cell (simulating Racket mutable vector / Python list)."""

    def __init__(self, items: list[Any]):
        self.items = list(items)

    def get(self, idx: int) -> Any:
        return self.items[idx]

    def set(self, idx: int, val: Any) -> None:
        self.items[idx] = val

    def __len__(self) -> int:
        return len(self.items)


class NaturalFnProxy:
    """Uncollapsed Natural higher-order function chaperone wrapper."""

    def __init__(
        self,
        target: Any,
        src: Fn,
        trg: Fn,
        pos: str,
        neg: str,
        metrics: Metrics,
    ):
        self.target = target
        self.src = src
        self.trg = trg
        self.pos = pos
        self.neg = neg
        self.metrics = metrics
        self.depth = (target.depth + 1) if isinstance(target, NaturalFnProxy) else 1
        metrics.proxy_allocs += 1
        metrics.note_depth(self.depth)

    def __call__(self, arg: Any) -> Any:
        # Unwind nested proxy chain iteratively (exposing the O(depth) stack frames
        # that naive recursive wrappers consume on the native call stack).
        chain: list[NaturalFnProxy] = []
        cur: Any = self
        while isinstance(cur, NaturalFnProxy):
            chain.append(cur)
            cur = cur.target
        cur_arg = arg
        for p in chain:
            p.metrics.proxy_hops += 1
            cur_arg = natural_cast(cur_arg, p.trg.dom, p.src.dom, p.neg, p.pos, p.metrics)
        res = cur(cur_arg)
        for p in reversed(chain):
            res = natural_cast(res, p.src.cod, p.trg.cod, p.pos, p.neg, p.metrics)
        return res


class NaturalArrayProxy:
    """Uncollapsed Natural mutable array chaperone wrapper (Strickland et al. 2012)."""

    def __init__(
        self,
        target: Any,
        src: Ref,
        trg: Ref,
        pos: str,
        neg: str,
        metrics: Metrics,
    ):
        self.target = target
        self.src = src
        self.trg = trg
        self.pos = pos
        self.neg = neg
        self.metrics = metrics
        self.depth = (target.depth + 1) if isinstance(target, NaturalArrayProxy) else 1
        metrics.proxy_allocs += 1
        metrics.note_depth(self.depth)

    def _unwind(self) -> tuple[list[NaturalArrayProxy], RawArray]:
        chain: list[NaturalArrayProxy] = []
        cur: Any = self
        while isinstance(cur, NaturalArrayProxy):
            chain.append(cur)
            cur = cur.target
        assert isinstance(cur, RawArray)
        return chain, cur

    def get(self, idx: int) -> Any:
        chain, base = self._unwind()
        val = base.get(idx)
        for p in reversed(chain):
            p.metrics.proxy_hops += 1
            val = natural_cast(val, p.src.elem, p.trg.elem, p.pos, p.neg, p.metrics)
        return val

    def set(self, idx: int, val: Any) -> None:
        chain, base = self._unwind()
        cur_val = val
        for p in chain:
            p.metrics.proxy_hops += 1
            # Mutation reverses value flow => blame polarity flips!
            cur_val = natural_cast(cur_val, p.trg.elem, p.src.elem, p.neg, p.pos, p.metrics)
        base.set(idx, cur_val)

    def __len__(self) -> int:
        _, base = self._unwind()
        return len(base)


def natural_cast(
    val: Any,
    src: Type,
    trg: Type,
    pos: str,
    neg: str,
    metrics: Metrics,
) -> Any:
    """Uncollapsed Wadler-Findler / Natural cast semantics."""
    metrics.boundary_casts += 1
    if src == trg:
        return val
    # Upcast to Dyn (ground injection)
    if isinstance(trg, Dyn):
        if isinstance(src, Base):
            return val
        if isinstance(src, Fn):
            return NaturalFnProxy(val, src, Fn(DYN, DYN), pos, neg, metrics)
        if isinstance(src, Ref):
            return NaturalArrayProxy(val, src, Ref(DYN), pos, neg, metrics)
        return val
    # Downcast from Dyn (ground projection + structural wrapping)
    if isinstance(src, Dyn):
        metrics.tag_checks += 1
        if isinstance(trg, Base):
            if not is_base_value(val, trg):
                raise BlameError(pos, "positive", f"expected {trg}, got {val!r}")
            return val
        if isinstance(trg, Fn):
            if not callable(val):
                raise BlameError(pos, "positive", f"expected callable for {trg}, got {val!r}")
            return NaturalFnProxy(val, Fn(DYN, DYN), trg, pos, neg, metrics)
        if isinstance(trg, Ref):
            if not isinstance(val, (RawArray, NaturalArrayProxy)):
                raise BlameError(pos, "positive", f"expected array for {trg}, got {val!r}")
            return NaturalArrayProxy(val, Ref(DYN), trg, pos, neg, metrics)
    # Direct higher-order casts
    if isinstance(src, Fn) and isinstance(trg, Fn):
        return NaturalFnProxy(val, src, trg, pos, neg, metrics)
    if isinstance(src, Ref) and isinstance(trg, Ref):
        return NaturalArrayProxy(val, src, trg, pos, neg, metrics)
    if isinstance(src, Base) and isinstance(trg, Base):
        metrics.tag_checks += 1
        if src != trg or not is_base_value(val, trg):
            raise BlameError(pos, "positive", f"incompatible base cast {src} => {trg}")
        return val
    raise BlameError(pos, "positive", f"inconsistent cast {src} => {trg}")


def verify_wadler_findler_blame() -> dict[str, str]:
    m = Metrics()

    # Case A: First-order positive blame (untyped provider returns bad value to typed client)
    try:
        natural_cast("oops", DYN, INT, pos="untyped_provider", neg="typed_client", metrics=m)
        raise AssertionError("Case A should have raised BlameError")
    except BlameError as e:
        assert e.blamed == "untyped_provider" and e.polarity == "positive"
        case_a = f"{e.polarity}:{e.blamed}"

    # Case B: Contravariant negative blame (untyped caller passes Str to typed Int->Int)
    typed_inc = lambda x: x + 1
    exported_inc = natural_cast(typed_inc, Fn(INT, INT), DYN, pos="typed_server", neg="untyped_caller", metrics=m)
    try:
        exported_inc("bad_arg")
        raise AssertionError("Case B should have raised BlameError")
    except BlameError as e:
        # Notice: typed_server was exported at Fn(INT, INT) <:n DYN; Blame Theorem forbids blaming typed_server!
        assert e.blamed == "untyped_caller"
        case_b = f"blamed={e.blamed}"

    # Case C: Double-contravariant 2nd-order callback blame
    # Typed HO function `apply_to_5 : (Int -> Int) -> Int` exported to untyped caller passing bad callback
    typed_ho = lambda f: f(5)
    exported_ho = natural_cast(
        typed_ho,
        Fn(Fn(INT, INT), INT),
        Fn(Fn(DYN, DYN), DYN),
        pos="typed_ho",
        neg="untyped_caller",
        metrics=m,
    )
    try:
        exported_ho(lambda x: "not_an_int")
        raise AssertionError("Case C should have raised BlameError")
    except BlameError as e:
        # Bad callback supplied by untyped_caller violates (Int -> Int) codomain => blames untyped_caller!
        assert e.blamed == "untyped_caller"
        case_c = f"blamed={e.blamed}"

    # Case D1 & D2: Mutable array polarity reversal (Strickland et al. 2012)
    typed_arr = RawArray([1, 2, 3])
    exported_arr = natural_cast(typed_arr, Ref(INT), Ref(DYN), pos="typed_owner", neg="untyped_mutator", metrics=m)
    try:
        exported_arr.set(0, "corrupt")
        raise AssertionError("Case D1 should have raised BlameError")
    except BlameError as e:
        assert e.blamed == "untyped_mutator"
        case_d1 = f"write_blamed={e.blamed}"

    untyped_arr = RawArray(["corrupt"])
    imported_arr = natural_cast(untyped_arr, Ref(DYN), Ref(INT), pos="untyped_owner", neg="typed_reader", metrics=m)
    try:
        imported_arr.get(0)
        raise AssertionError("Case D2 should have raised BlameError")
    except BlameError as e:
        assert e.blamed == "untyped_owner"
        case_d2 = f"read_blamed={e.blamed}"

    return {
        "first_order_pos": case_a,
        "ho_contravariant_neg": case_b,
        "ho_2nd_order_callback": case_c,
        "ref_write_polarity": case_d1,
        "ref_read_polarity": case_d2,
    }


# ---------------------------------------------------------------------------
# 3. Herman-Tomb-Flanagan (2010) Space-Efficient Coercion Algebra
# ---------------------------------------------------------------------------

class Coercion:
    def height(self) -> int:
        raise NotImplementedError

    def size(self) -> int:
        raise NotImplementedError


@dataclass(frozen=True)
class CId(Coercion):
    def height(self) -> int:
        return 1

    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class CFail(Coercion):
    label: str

    def height(self) -> int:
        return 1

    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class CInj(Coercion):
    """Ground injection G! : G => Dyn (ground tag is 'Int', 'Bool', 'Str', 'Fn', 'Ref')."""
    ground: str

    def height(self) -> int:
        return 1

    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class CProj(Coercion):
    """Ground projection G?^l : Dyn => G."""
    ground: str
    label: str

    def height(self) -> int:
        return 1

    def size(self) -> int:
        return 1


@dataclass(frozen=True)
class CFn(Coercion):
    """Function coercion Fun(dom_c, cod_c) where dom_c is contravariant."""
    dom: Coercion
    cod: Coercion

    def height(self) -> int:
        return 1 + max(self.dom.height(), self.cod.height())

    def size(self) -> int:
        return 1 + self.dom.size() + self.cod.size()


@dataclass(frozen=True)
class CRef(Coercion):
    """Mutable reference coercion Ref(read_c, write_c)."""
    read: Coercion
    write: Coercion

    def height(self) -> int:
        return 1 + max(self.read.height(), self.write.height())

    def size(self) -> int:
        return 1 + self.read.size() + self.write.size()


@dataclass(frozen=True)
class CSeq(Coercion):
    """Normalized coercion sequence [proj? ; med? ; inj?] (at most 3 atomic stages)."""
    first: Coercion
    second: Coercion

    def height(self) -> int:
        return max(self.first.height(), self.second.height())

    def size(self) -> int:
        return 1 + self.first.size() + self.second.size()


CID = CId()


def make_coercion(src: Type, trg: Type, pos: str, neg: str) -> Coercion:
    """Compile cast (src => trg)^{pos, neg} into a normalized HTF coercion."""
    if src == trg:
        return CID
    if isinstance(trg, Dyn):
        if isinstance(src, Base):
            return CInj(src.name)
        if isinstance(src, Fn):
            med = make_coercion(src, Fn(DYN, DYN), pos, neg)
            return compose_coercion(med, CInj("Fn"))
        if isinstance(src, Ref):
            med = make_coercion(src, Ref(DYN), pos, neg)
            return compose_coercion(med, CInj("Ref"))
    if isinstance(src, Dyn):
        if isinstance(trg, Base):
            return CProj(trg.name, pos)
        if isinstance(trg, Fn):
            med = make_coercion(Fn(DYN, DYN), trg, pos, neg)
            return compose_coercion(CProj("Fn", pos), med)
        if isinstance(trg, Ref):
            med = make_coercion(Ref(DYN), trg, pos, neg)
            return compose_coercion(CProj("Ref", pos), med)
    if isinstance(src, Fn) and isinstance(trg, Fn):
        dc = make_coercion(trg.dom, src.dom, neg, pos)
        cc = make_coercion(src.cod, trg.cod, pos, neg)
        return CID if (dc == CID and cc == CID) else CFn(dc, cc)
    if isinstance(src, Ref) and isinstance(trg, Ref):
        rc = make_coercion(src.elem, trg.elem, pos, neg)
        wc = make_coercion(trg.elem, src.elem, neg, pos)
        return CID if (rc == CID and wc == CID) else CRef(rc, wc)
    return CFail(pos)


def _split_seq(c: Coercion) -> tuple[CProj | None, Coercion | None, CInj | None]:
    """Decompose a normalized coercion into (optional CProj, optional medial, optional CInj)."""
    parts: list[Coercion] = []

    def flatten(x: Coercion) -> None:
        if isinstance(x, CSeq):
            flatten(x.first)
            flatten(x.second)
        elif not isinstance(x, CId):
            parts.append(x)

    flatten(c)
    proj: CProj | None = None
    inj: CInj | None = None
    med: Coercion | None = None
    idx = 0
    if idx < len(parts) and isinstance(parts[idx], CProj):
        proj = parts[idx]
        idx += 1
    if idx < len(parts) and isinstance(parts[-1], CInj):
        inj = parts[-1]
        end = len(parts) - 1
    else:
        end = len(parts)
    if idx < end:
        med = parts[idx]
        assert idx + 1 == end, f"Unnormalized medial sequence: {parts}"
    return proj, med, inj


def _rebuild(proj: CProj | None, med: Coercion | None, inj: CInj | None) -> Coercion:
    if isinstance(med, CFail):
        return med
    if isinstance(med, CId):
        med = None
    seq = [x for x in (proj, med, inj) if x is not None]
    if not seq:
        return CID
    res = seq[0]
    for nxt in seq[1:]:
        res = CSeq(res, nxt)
    return res


def compose_coercion(c1: Coercion, c2: Coercion, metrics: Metrics | None = None) -> Coercion:
    """Herman, Tomb & Flanagan (2010) normalized coercion composition c1 ; c2."""
    if metrics is not None:
        metrics.coercion_compositions += 1
    if isinstance(c1, CId):
        return c2
    if isinstance(c2, CId):
        return c1
    if isinstance(c1, CFail):
        return c1
    if isinstance(c2, CFail):
        return c2

    p1, m1, i1 = _split_seq(c1)
    p2, m2, i2 = _split_seq(c2)

    # Collapse injection followed by projection: G1! ; G2?^l
    if i1 is not None and p2 is not None:
        if i1.ground != p2.ground:
            return CFail(p2.label)  # Early error detection!
        # i1 and p2 cancel to identity!
        i1 = None
        p2 = None

    # Now compose medial coercions m1 and m2
    if m1 is None:
        med = m2
    elif m2 is None:
        med = m1
    elif isinstance(m1, CFn) and isinstance(m2, CFn):
        # Contravariant domain composition: (d2 ; d1), covariant codomain: (c1 ; c2)
        nd = compose_coercion(m2.dom, m1.dom, metrics)
        nc = compose_coercion(m1.cod, m2.cod, metrics)
        med = CID if (nd == CID and nc == CID) else CFn(nd, nc)
    elif isinstance(m1, CRef) and isinstance(m2, CRef):
        nr = compose_coercion(m1.read, m2.read, metrics)
        nw = compose_coercion(m2.write, m1.write, metrics)
        med = CID if (nr == CID and nw == CID) else CRef(nr, nw)
    else:
        raise AssertionError(f"Ill-typed medial composition: {m1} ; {m2}")

    # Notice: after cancellation, at most one outer proj (p1 or p2) and one outer inj (i2 or i1) remain
    proj = p1 if p1 is not None else p2
    inj = i2 if i2 is not None else i1
    res = _rebuild(proj, med, inj)
    # Check Herman et al. (2010) Lemma 2 space bound: size(c) <= 5 * (2^height(c) - 1)
    h = res.height()
    sz = res.size()
    assert sz <= 5 * ((1 << h) - 1), f"HTF Lemma 2 violated: size={sz}, height={h}, c={res}"
    if metrics is not None:
        metrics.note_csize(sz)
    return res


class CollapsedFnProxy:
    """Space-efficient HTF function proxy: depth is ALWAYS 1."""

    def __init__(self, target: Any, coercion: CFn, metrics: Metrics):
        assert not isinstance(target, CollapsedFnProxy), "Must collapse instead of nesting!"
        self.target = target
        self.coercion = coercion
        self.metrics = metrics
        self.depth = 1
        metrics.proxy_allocs += 1
        metrics.note_depth(1)

    def __call__(self, arg: Any) -> Any:
        self.metrics.proxy_hops += 1
        carg = apply_coercion(arg, self.coercion.dom, self.metrics)
        res = self.target(carg)
        return apply_coercion(res, self.coercion.cod, self.metrics)


class CollapsedArrayProxy:
    """Space-efficient HTF mutable array proxy: depth is ALWAYS 1."""

    def __init__(self, target: RawArray, coercion: CRef, metrics: Metrics):
        assert isinstance(target, RawArray), "Must collapse instead of nesting!"
        self.target = target
        self.coercion = coercion
        self.metrics = metrics
        self.depth = 1
        metrics.proxy_allocs += 1
        metrics.note_depth(1)

    def get(self, idx: int) -> Any:
        self.metrics.proxy_hops += 1
        val = self.target.get(idx)
        return apply_coercion(val, self.coercion.read, self.metrics)

    def set(self, idx: int, val: Any) -> None:
        self.metrics.proxy_hops += 1
        checked = apply_coercion(val, self.coercion.write, self.metrics)
        self.target.set(idx, checked)

    def __len__(self) -> int:
        return len(self.target)


def _check_ground(val: Any, ground: str, label: str, metrics: Metrics) -> None:
    metrics.tag_checks += 1
    if ground == "Int":
        ok = type(val) is int
    elif ground == "Bool":
        ok = type(val) is bool
    elif ground == "Str":
        ok = type(val) is str
    elif ground == "Fn":
        ok = callable(val)
    elif ground == "Ref":
        ok = isinstance(val, (RawArray, CollapsedArrayProxy))
    else:
        ok = False
    if not ok:
        raise BlameError(label, "positive", f"ground projection {ground}? failed on {val!r}")


def apply_coercion(val: Any, c: Coercion, metrics: Metrics) -> Any:
    """Apply a normalized HTF coercion with eager wrapper collapse."""
    if isinstance(c, CId):
        return val
    if isinstance(c, CFail):
        raise BlameError(c.label, "positive", "coercion Fail reached")
    if isinstance(c, CSeq):
        val = apply_coercion(val, c.first, metrics)
        return apply_coercion(val, c.second, metrics)
    if isinstance(c, CInj):
        return val
    if isinstance(c, CProj):
        _check_ground(val, c.ground, c.label, metrics)
        return val
    if isinstance(c, CFn):
        if isinstance(val, CollapsedFnProxy):
            merged = compose_coercion(val.coercion, c, metrics)
            if isinstance(merged, CId):
                return val.target
            if isinstance(merged, CFail):
                raise BlameError(merged.label, "positive", "collapsed fn coercion Fail")
            assert isinstance(merged, CFn)
            # Early error check: if domain or codomain collapsed to CFail, raise immediately
            # (or preserve lazy/eager behavior; note Herman et al. §7 detects domain mismatch at cast!)
            return CollapsedFnProxy(val.target, merged, metrics)
        return CollapsedFnProxy(val, c, metrics)
    if isinstance(c, CRef):
        if isinstance(val, CollapsedArrayProxy):
            merged = compose_coercion(val.coercion, c, metrics)
            if isinstance(merged, CId):
                return val.target
            if isinstance(merged, CFail):
                raise BlameError(merged.label, "positive", "collapsed ref coercion Fail")
            assert isinstance(merged, CRef)
            return CollapsedArrayProxy(val.target, merged, metrics)
        assert isinstance(val, RawArray)
        return CollapsedArrayProxy(val, c, metrics)
    raise AssertionError(f"Unhandled coercion {c}")


def collapsed_cast(
    val: Any,
    src: Type,
    trg: Type,
    pos: str,
    neg: str,
    metrics: Metrics,
) -> Any:
    metrics.boundary_casts += 1
    c = make_coercion(src, trg, pos, neg)
    return apply_coercion(val, c, metrics)


def verify_htf_space_efficiency() -> list[dict[str, int]]:
    rows: list[dict[str, int]] = []
    # 1. Verify early error detection (Herman et al. 2010 §7):
    #    f : Int -> Int  ==>  g : Dyn  ==>  h : Bool -> Int
    c_up = make_coercion(Fn(INT, INT), DYN, "up_pos", "up_neg")
    c_dn = make_coercion(DYN, Fn(BOOL, INT), "dn_pos", "dn_neg")
    c_comp = compose_coercion(c_up, c_dn)
    assert isinstance(c_comp, CFn) and isinstance(c_comp.dom, CFail), (
        f"Expected early domain CFail in {c_comp}"
    )

    # 2. Scaling test A (round-trip Int->Int <=> Dyn & Ref[Int] <=> Dyn) +
    #    Scaling test B (non-identity persistent wrapper: Int->Int => Dyn => Dyn->Int => Dyn => ...)
    for n in (10, 50, 200, 1000):
        m_nat = Metrics()
        m_htf = Metrics()
        fn_nat: Any = lambda x: x + 1
        fn_htf: Any = lambda x: x + 1
        arr_nat: Any = RawArray([0])
        arr_htf: Any = RawArray([0])

        # Persistent non-identity callback (cannot simplify to Id because domain stays Int?!)
        pfn_htf: Any = lambda x: x + 1
        pfn_htf = collapsed_cast(pfn_htf, Fn(INT, INT), Fn(DYN, INT), "P", "Q", m_htf)

        for _ in range(n):
            # Bounce across Int->Int <=> Dyn and Ref[Int] <=> Dyn
            fn_nat = natural_cast(fn_nat, Fn(INT, INT), DYN, "A", "B", m_nat)
            fn_nat = natural_cast(fn_nat, DYN, Fn(INT, INT), "B", "A", m_nat)
            arr_nat = natural_cast(arr_nat, Ref(INT), DYN, "A", "B", m_nat)
            arr_nat = natural_cast(arr_nat, DYN, Ref(INT), "B", "A", m_nat)

            fn_htf = collapsed_cast(fn_htf, Fn(INT, INT), DYN, "A", "B", m_htf)
            fn_htf = collapsed_cast(fn_htf, DYN, Fn(INT, INT), "B", "A", m_htf)
            arr_htf = collapsed_cast(arr_htf, Ref(INT), DYN, "A", "B", m_htf)
            arr_htf = collapsed_cast(arr_htf, DYN, Ref(INT), "B", "A", m_htf)

            # Non-identity bounce: Fn(Dyn, Int) => Dyn => Fn(Dyn, Int)
            pfn_htf = collapsed_cast(pfn_htf, Fn(DYN, INT), DYN, "P", "Q", m_htf)
            pfn_htf = collapsed_cast(pfn_htf, DYN, Fn(DYN, INT), "Q", "P", m_htf)

        # Single invocation & array read/write after N boundary round-trips
        hops_before_nat = m_nat.proxy_hops
        hops_before_htf = m_htf.proxy_hops
        assert fn_nat(1) == 2 and fn_htf(1) == 2
        assert pfn_htf(1) == 2
        arr_nat.set(0, arr_nat.get(0) + 1)
        arr_htf.set(0, arr_htf.get(0) + 1)
        assert arr_nat.get(0) == 1 and arr_htf.get(0) == 1

        nat_access_hops = m_nat.proxy_hops - hops_before_nat
        htf_access_hops = m_htf.proxy_hops - hops_before_htf

        assert m_nat.max_proxy_depth == 2 * n, f"Expected depth {2*n}, got {m_nat.max_proxy_depth}"
        assert m_htf.max_proxy_depth == 1, f"HTF depth expected 1, got {m_htf.max_proxy_depth}"
        assert nat_access_hops == 8 * n, f"Expected 8*n hops, got {nat_access_hops}"
        # fn_htf & arr_htf collapsed to Id (0 hops); pfn_htf stayed a single depth-1 wrapper (1 hop)!
        assert htf_access_hops == 1, f"Expected 1 hop (persistent wrapper only), got {htf_access_hops}"

        rows.append({
            "N": n,
            "nat_depth": m_nat.max_proxy_depth,
            "htf_depth": m_htf.max_proxy_depth,
            "nat_access_hops": nat_access_hops,
            "htf_access_hops": htf_access_hops,
            "htf_max_csize": m_htf.max_coercion_size,
        })
    return rows


# ---------------------------------------------------------------------------
# 4. Transient (shallow checks) & Concrete (nominal tags) runtimes
# ---------------------------------------------------------------------------

def transient_check(val: Any, expected: Type, metrics: Metrics) -> Any:
    """Vitousek et al. (2017) shallow O(1) top-level tag check (no wrapping)."""
    metrics.tag_checks += 1
    if isinstance(expected, Dyn):
        return val
    if isinstance(expected, Base):
        if not is_base_value(val, expected):
            raise RuntimeTagError(f"Transient check failed: expected {expected}, got {val!r}")
        return val
    if isinstance(expected, Fn):
        if not callable(val):
            raise RuntimeTagError(f"Transient check failed: expected callable, got {val!r}")
        return val
    if isinstance(expected, Ref):
        if not isinstance(val, RawArray):
            raise RuntimeTagError(f"Transient check failed: expected array, got {val!r}")
        return val
    return val


class ConcreteArray:
    """Muehlboeck & Tate (2017) / Static Python nominal checked container.

    Carries an immutable runtime element type tag from allocation.
    Typed reads need zero element checks; untyped writes check against the tag;
    raw untyped RawArray cannot cross into Concrete[Int] without conversion.
    """

    def __init__(self, elem_ty: Base, items: list[Any], metrics: Metrics):
        self.elem_ty = elem_ty
        self.metrics = metrics
        for v in items:
            metrics.tag_checks += 1
            if not is_base_value(v, elem_ty):
                raise RuntimeTagError(f"ConcreteArray[{elem_ty}] init rejected {v!r}")
        self.items = list(items)

    def get_typed(self, idx: int) -> Any:
        # Zero element tag check because runtime tag guarantees all elements satisfy elem_ty!
        return self.items[idx]

    def set_typed(self, idx: int, val: Any) -> None:
        # Statically checked caller -> unchecked fast path (cf. CinderX chklist_append)
        self.items[idx] = val

    def set_dynamic(self, idx: int, val: Any) -> None:
        # Untyped caller -> checked wrapper (cf. CinderX chklist_append_wrapper)
        self.metrics.tag_checks += 1
        if not is_base_value(val, self.elem_ty):
            raise RuntimeTagError(f"ConcreteArray[{self.elem_ty}] dynamic write rejected {val!r}")
        self.items[idx] = val

    def __len__(self) -> int:
        return len(self.items)


def concrete_check_ref(val: Any, expected_elem: Base, metrics: Metrics) -> ConcreteArray:
    metrics.tag_checks += 1
    if not isinstance(val, ConcreteArray) or val.elem_ty != expected_elem:
        raise RuntimeTagError(
            f"Concrete nominal check failed: expected ConcreteArray[{expected_elem}], got {type(val).__name__}"
        )
    return val


# ---------------------------------------------------------------------------
# 5. Complete Monitoring counterexample (Greenman, Felleisen & Dimoulas 2019)
# ---------------------------------------------------------------------------

def verify_complete_monitoring_distinction() -> dict[str, str]:
    """Clickable-Plot style counterexample:
      untyped_client defines callback h expecting Int
      typed_api declares register(cb: Int -> Int) -> (Dyn -> Any) that forwards cb to untyped_lib
      untyped_lib invokes cb("MouseEvt") directly.
    Natural (deep) catches the violation across the typed API channel;
    Transient (shallow) allows untyped_lib -> untyped_client to communicate unchecked!
    """
    m_nat = Metrics()
    m_tr = Metrics()

    def untyped_client_cb(x: Any) -> Any:
        # Untyped callback performs an operation that only fails late or silently coerces
        return f"received:{type(x).__name__}"

    # Under Natural: cb crosses untyped_client -> typed_api (Dyn => Int -> Int)
    # and then typed_api -> untyped_lib (Int -> Int => Dyn).
    cb_in_typed = natural_cast(untyped_client_cb, DYN, Fn(INT, INT), "untyped_client", "typed_api", m_nat)
    cb_in_lib = natural_cast(cb_in_typed, Fn(INT, INT), DYN, "typed_api", "untyped_lib", m_nat)
    try:
        cb_in_lib("MouseEvt")
        raise AssertionError("Natural MUST catch untyped_lib sending Str over Int->Int channel")
    except BlameError as e:
        assert e.blamed == "untyped_lib"
        nat_outcome = f"CAUGHT({e.blamed})"

    # Under Transient: typed_api only checks `callable(cb)` when receiving cb and passes
    # the unproxied function to untyped_lib; untyped_lib calls untyped_client_cb("MouseEvt")
    # directly with NO check triggered!
    cb_tr = transient_check(untyped_client_cb, Fn(INT, INT), m_tr)
    tr_res = cb_tr("MouseEvt")
    assert tr_res == "received:str"
    tr_outcome = f"UNCHECKED_CHANNEL({tr_res})"

    # Under Concrete: verify structural-flexibility restriction — raw untyped array rejected
    m_conc = Metrics()
    raw = RawArray([1, 2, 3])
    try:
        concrete_check_ref(raw, INT, m_conc)
        raise AssertionError("Concrete MUST reject raw untyped RawArray at Ref[Int] boundary")
    except RuntimeTagError:
        conc_outcome = "REJECTED_RAW_UNTYPED_LIST"

    return {
        "natural_cm": nat_outcome,
        "transient_no_cm": tr_outcome,
        "concrete_nominal_restriction": conc_outcome,
    }


# ---------------------------------------------------------------------------
# 6. Full 2^4 = 16 mixed-typed lattice across all 5 semantics
# ---------------------------------------------------------------------------

def run_lattice_config(
    mode: str,
    cfg: tuple[int, int, int, int],  # (M0_prod, M1_step, M2_mut, M3_drv): 0=untyped, 1=typed
    rounds: int = 24,
    arr_len: int = 8,
    inject_bad_untyped: bool = False,
) -> tuple[Any, Metrics]:
    """Execute a 4-module higher-order + mutable-array pipeline across config `cfg`.

    Data flow per round r in 0..rounds-1:
      M3 (driver) calls M1 (stepper) passing (arr, cb, r)
      M1 calls M2 (mutator) passing (arr, cb, idx)
      M2 reads arr[idx], invokes cb(val), writes result back into arr[idx], returns arr
      M1 returns (arr, cb) back to M3 for the next round.
    """
    m0, m1, m2, m3 = cfg
    metrics = Metrics()

    def boundary(val: Any, from_t: int, to_t: int, ty: Type, pos: str, neg: str) -> Any:
        if from_t == to_t:
            return val
        if mode == "Erasure":
            return val
        if mode == "Natural-Uncollapsed":
            return natural_cast(val, ty if from_t else DYN, ty if to_t else DYN, pos, neg, metrics)
        if mode == "Natural-Collapsed":
            return collapsed_cast(val, ty if from_t else DYN, ty if to_t else DYN, pos, neg, metrics)
        if mode == "Transient":
            return transient_check(val, ty, metrics) if to_t else val
        if mode == "Concrete":
            if to_t:
                if isinstance(ty, Ref) and isinstance(ty.elem, Base):
                    return concrete_check_ref(val, ty.elem, metrics)
                if isinstance(ty, Fn):
                    metrics.tag_checks += 1
                    if not callable(val):
                        raise RuntimeTagError("Concrete callable check failed")
                if isinstance(ty, Base):
                    metrics.tag_checks += 1
                    if not is_base_value(val, ty):
                        raise RuntimeTagError(f"Concrete base check failed for {ty}")
            return val
        raise ValueError(mode)

    # M0: producer creates array & callback
    init_vals: list[Any] = [i for i in range(arr_len)]
    if inject_bad_untyped and m0 == 0:
        init_vals[0] = "BAD"
    if mode == "Concrete":
        # Concrete requires nominal ConcreteArray allocation even when producer is untyped
        # if it will flow to typed consumers (otherwise Concrete rejects it!).
        arr: Any = ConcreteArray(INT, [0 if x == "BAD" else x for x in init_vals], metrics)
    else:
        arr = RawArray(init_vals)

    def cb_impl(x: Any) -> Any:
        if m0 == 1 and mode == "Transient":
            x = transient_check(x, INT, metrics)
        return x + 1 if type(x) is int else x

    cb: Any = cb_impl

    # M0 -> M3 handoff
    arr = boundary(arr, m0, m3, Ref(INT), "M0", "M3")
    cb = boundary(cb, m0, m3, Fn(INT, INT), "M0", "M3")

    # M3 driver loop
    for r in range(rounds):
        # M3 -> M1
        arr_1 = boundary(arr, m3, m1, Ref(INT), "M3", "M1")
        cb_1 = boundary(cb, m3, m1, Fn(INT, INT), "M3", "M1")
        if m1 == 1 and mode == "Transient":
            arr_1 = transient_check(arr_1, Ref(INT), metrics)
            cb_1 = transient_check(cb_1, Fn(INT, INT), metrics)

        # M1 -> M2
        arr_2 = boundary(arr_1, m1, m2, Ref(INT), "M1", "M2")
        cb_2 = boundary(cb_1, m1, m2, Fn(INT, INT), "M1", "M2")
        if m2 == 1 and mode == "Transient":
            arr_2 = transient_check(arr_2, Ref(INT), metrics)
            cb_2 = transient_check(cb_2, Fn(INT, INT), metrics)

        # M2 mutator: read, invoke callback, write back
        idx = r % arr_len
        if mode == "Concrete":
            v = arr_2.get_typed(idx) if m2 == 1 else arr_2.get_typed(idx)
            if m2 == 0:
                # Untyped dynamic dispatch cost modeled as 1 tag check
                metrics.tag_checks += 1
            nv = cb_2(v)
            if m2 == 1:
                arr_2.set_typed(idx, nv)
            else:
                arr_2.set_dynamic(idx, nv)
        else:
            v = arr_2.get(idx)
            if m2 == 1 and mode == "Transient":
                v = transient_check(v, INT, metrics)
            nv = cb_2(v)
            if m2 == 1 and mode == "Transient":
                nv = transient_check(nv, INT, metrics)
            arr_2.set(idx, nv)

        # M2 -> M1 -> M3 return path (returns mutated array + callback)
        arr_1b = boundary(arr_2, m2, m1, Ref(INT), "M2", "M1")
        cb_1b = boundary(cb_2, m2, m1, Fn(INT, INT), "M2", "M1")
        arr = boundary(arr_1b, m1, m3, Ref(INT), "M1", "M3")
        cb = boundary(cb_1b, m1, m3, Fn(INT, INT), "M1", "M3")

    # M3 sums final array
    total = 0
    for i in range(arr_len):
        val = arr.get_typed(i) if mode == "Concrete" else arr.get(i)
        if m3 == 1 and mode == "Transient":
            val = transient_check(val, INT, metrics)
        if type(val) is int:
            total += val
        else:
            return f"UNSOUND_CORRUPTED({val!r})", metrics
    return total, metrics


def verify_2k_lattice() -> tuple[dict[str, dict[str, int]], dict[str, list[tuple[str, Metrics]]]]:
    modes = [
        "Erasure",
        "Natural-Uncollapsed",
        "Natural-Collapsed",
        "Transient",
        "Concrete",
    ]
    expected_sum = sum(range(8)) + 24  # 28 + 24 = 52
    summary: dict[str, dict[str, int]] = {}
    per_mode_work: dict[str, list[tuple[str, Metrics]]] = {}

    for mode in modes:
        records: list[tuple[str, Metrics]] = []
        for mask in range(16):
            cfg = ((mask >> 3) & 1, (mask >> 2) & 1, (mask >> 1) & 1, mask & 1)
            res, met = run_lattice_config(mode, cfg, rounds=24, arr_len=8)
            assert res == expected_sum, f"{mode} cfg={cfg} returned {res}, expected {expected_sum}"
            records.append((f"{mask:04b}", met))
        per_mode_work[mode] = records

        work = [m.proxy_hops + m.tag_checks + m.boundary_casts for _, m in records]
        depths = [m.max_proxy_depth for _, m in records]
        summary[mode] = {
            "untyped_0000_ops": work[0],
            "typed_1111_ops": work[15],
            "max_mixed_ops": max(work),
            "max_proxy_depth": max(depths),
        }

    # Verify soundness failure of Erasure when untyped M0 injects "BAD" into typed M1/M2/M3
    erasure_res, _ = run_lattice_config("Erasure", (0, 1, 1, 1), inject_bad_untyped=True)
    assert str(erasure_res).startswith("UNSOUND_CORRUPTED"), f"Expected Erasure corruption, got {erasure_res}"

    # Verify Natural-Uncollapsed, Natural-Collapsed, and Transient catch the injected bad element
    for sound_mode in ("Natural-Uncollapsed", "Natural-Collapsed", "Transient"):
        caught = False
        try:
            run_lattice_config(sound_mode, (0, 1, 1, 1), inject_bad_untyped=True)
        except (BlameError, RuntimeTagError):
            caught = True
        assert caught, f"{sound_mode} failed to catch untyped injection"

    # Verify core architectural distinctions across the 2^4 lattice:
    # 1. Erasure: 0 ops everywhere
    assert summary["Erasure"]["max_mixed_ops"] == 0
    # 2. Natural-Uncollapsed: 0 ops at 0000 & 1111, massive quadratic mixed cliff + linear proxy depth
    assert summary["Natural-Uncollapsed"]["untyped_0000_ops"] == 0
    assert summary["Natural-Uncollapsed"]["typed_1111_ops"] == 0
    assert summary["Natural-Uncollapsed"]["max_proxy_depth"] >= 48
    assert summary["Natural-Uncollapsed"]["max_mixed_ops"] > 5 * summary["Natural-Collapsed"]["max_mixed_ops"]
    # 3. Natural-Collapsed: 0 ops at 0000 & 1111, O(1) proxy depth <= 1
    assert summary["Natural-Collapsed"]["untyped_0000_ops"] == 0
    assert summary["Natural-Collapsed"]["typed_1111_ops"] == 0
    assert summary["Natural-Collapsed"]["max_proxy_depth"] == 1
    # 4. Transient: 0 proxies, NO cliff, but non-zero linear tax even in fully-typed 1111!
    assert summary["Transient"]["max_proxy_depth"] == 0
    assert summary["Transient"]["typed_1111_ops"] > 0
    assert summary["Transient"]["max_mixed_ops"] < summary["Natural-Uncollapsed"]["max_mixed_ops"]
    # 5. Concrete: 0 proxies, typed 1111 has fewer runtime checks than untyped 0000 (monotonic improvement!)
    assert summary["Concrete"]["max_proxy_depth"] == 0
    assert summary["Concrete"]["typed_1111_ops"] < summary["Concrete"]["untyped_0000_ops"]

    return summary, per_mode_work


def main(argv: list[str] | None = None) -> int:
    import sys

    verbose = "--verbose" in (argv if argv is not None else sys.argv[1:])
    rel = verify_type_relations()
    blame = verify_wadler_findler_blame()
    htf_rows = verify_htf_space_efficiency()
    cm = verify_complete_monitoring_distinction()
    lat, per_mode = verify_2k_lattice()

    print("=== 1. Type Consistency & Wadler-Findler Subtyping Factorizations ===")
    print(f"  universe_size={rel['universe_size']} pairs_verified={rel['pairs_verified']} (Prop 1, Prop 8, Prop 9 PASS)")

    print("\n=== 2. Wadler-Findler Blame Polarity (Higher-Order & Mutable Refs) ===")
    for k, v in blame.items():
        print(f"  {k:24s}: {v}")

    print("\n=== 3. Herman-Tomb-Flanagan O(1) Coercion Collapse vs Uncollapsed Natural ===")
    print(f"  {'N':>5s} | {'nat_depth':>9s} | {'htf_depth':>9s} | {'nat_hops':>9s} | {'htf_hops':>9s} | {'max_csize':>9s}")
    for r in htf_rows:
        print(
            f"  {r['N']:5d} | {r['nat_depth']:9d} | {r['htf_depth']:9d} | "
            f"{r['nat_access_hops']:9d} | {r['htf_access_hops']:9d} | {r['htf_max_csize']:9d}"
        )

    print("\n=== 4. Complete Monitoring & Structural-Flexibility Distinctions ===")
    for k, v in cm.items():
        print(f"  {k:30s}: {v}")

    print("\n=== 5. Full 2^4 (16-Config) Mixed-Typed Lattice Overhead (rounds=24, len=8) ===")
    print(f"  {'Semantics':20s} | {'0000 ops':>9s} | {'1111 ops':>9s} | {'max mixed':>9s} | {'max depth':>9s}")
    for mode, stats in lat.items():
        print(
            f"  {mode:20s} | {stats['untyped_0000_ops']:9d} | {stats['typed_1111_ops']:9d} | "
            f"{stats['max_mixed_ops']:9d} | {stats['max_proxy_depth']:9d}"
        )

    if verbose:
        print("\n=== 6. Per-Configuration Ops (cfg = M0 M1 M2 M3) ===")
        header = "  cfg  | " + " | ".join(f"{m[:12]:>12s}" for m in lat)
        print(header)
        for i in range(16):
            cfg_str = per_mode["Erasure"][i][0]
            vals = []
            for m in lat:
                met = per_mode[m][i][1]
                ops = met.proxy_hops + met.tag_checks + met.boundary_casts
                vals.append(f"{ops:9d}(d{met.max_proxy_depth})")
            print(f"  {cfg_str} | " + " | ".join(f"{v:>12s}" for v in vals))

    print("\nALL ASSERTIONS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
