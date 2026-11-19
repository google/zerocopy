#!/usr/bin/env python3
"""Standalone mathematical verifier for CuTe layout algebra, F2 XOR-swizzle SMEM banking,
and Exo-style affine read/write footprint & schedule equivalence.

Requires Python 3.10+ and uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence, Union

IntTuple = Union[int, tuple["IntTuple", ...]]


# =============================================================================
# Part 1: Hierarchical CuTe (Shape, Stride) Layout Algebra & Tractability
# =============================================================================


def is_tuple(x: IntTuple) -> bool:
    return isinstance(x, tuple)


def flatten(x: IntTuple) -> tuple[int, ...]:
    if isinstance(x, int):
        return (x,)
    out: list[int] = []
    for item in x:
        out.extend(flatten(item))
    return tuple(out)


def congruent(a: IntTuple, b: IntTuple) -> bool:
    if isinstance(a, int) and isinstance(b, int):
        return True
    if isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b):
        return all(congruent(x, y) for x, y in zip(a, b))
    return False


def product(x: IntTuple) -> int:
    res = 1
    for v in flatten(x):
        res *= v
    return res


def prefix_product(shape: IntTuple, init: int = 1) -> IntTuple:
    """Compute compact LayoutLeft (generalized column-major) strides."""
    flat = flatten(shape)
    strides: list[int] = []
    acc = init
    for s in flat:
        strides.append(acc)
        acc *= s
    it = iter(strides)

    def rebuild(node: IntTuple) -> IntTuple:
        if isinstance(node, int):
            return next(it)
        return tuple(rebuild(ch) for ch in node)

    return rebuild(shape)


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def idx2crd(idx: int, shape: IntTuple) -> IntTuple:
    """Hierarchical colexicographic (column-major) decomposition of 1-D idx into shape."""
    if isinstance(shape, int):
        return idx
    coords: list[IntTuple] = []
    rem = idx
    for mode in shape:
        m_size = product(mode)
        coords.append(idx2crd(rem % m_size, mode))
        rem //= m_size
    return tuple(coords)


def crd2idx(coord: IntTuple, shape: IntTuple, stride: IntTuple) -> int:
    """Evaluate inner product <coord, stride> supporting 1-D, hierarchical, and partial coords."""
    if isinstance(shape, int):
        assert isinstance(stride, int)
        assert isinstance(coord, int)
        return coord * stride
    assert isinstance(stride, tuple) and len(shape) == len(stride)
    if isinstance(coord, int):
        # Colexicographic decomposition into sub-modes
        return crd2idx(idx2crd(coord, shape), shape, stride)
    assert isinstance(coord, tuple) and len(coord) == len(shape)
    return sum(crd2idx(c, s, d) for c, s, d in zip(coord, shape, stride))


@dataclass(frozen=True)
class Layout:
    shape: IntTuple
    stride: IntTuple

    def __post_init__(self) -> None:
        if not congruent(self.shape, self.stride):
            raise ValueError(f"Non-congruent shape {self.shape} and stride {self.stride}")
        if any(s <= 0 for s in flatten(self.shape)):
            raise ValueError(f"Shape entries must be positive: {self.shape}")

    @staticmethod
    def make(shape: IntTuple, stride: IntTuple | None = None) -> "Layout":
        return Layout(shape, prefix_product(shape) if stride is None else stride)

    @property
    def size(self) -> int:
        return product(self.shape)

    @property
    def rank(self) -> int:
        return len(self.shape) if isinstance(self.shape, tuple) else 1

    def mode(self, i: int) -> "Layout":
        if isinstance(self.shape, int):
            assert i == 0
            return self
        assert isinstance(self.stride, tuple)
        return Layout(self.shape[i], self.stride[i])

    def __call__(self, coord: IntTuple) -> int:
        return crd2idx(coord, self.shape, self.stride)

    @property
    def cosize(self) -> int:
        return self(self.size - 1) + 1

    def __str__(self) -> str:
        return f"{self.shape}:{self.stride}"


def make_layout(*layouts: Layout) -> Layout:
    return Layout(tuple(l.shape for l in layouts), tuple(l.stride for l in layouts))


def coalesce(layout: Layout, profile: IntTuple | None = None) -> Layout:
    """CuTe 4-rule flat or by-mode coalesce preserving the 1-D integer function."""
    if isinstance(profile, tuple):
        assert layout.rank >= len(profile)
        parts = [coalesce(layout.mode(i), profile[i]) for i in range(len(profile))]
        parts.extend(layout.mode(i) for i in range(len(profile), layout.rank))
        return make_layout(*parts)

    res_s = [1]
    res_d = [0]
    for s, d in zip(flatten(layout.shape), flatten(layout.stride)):
        if s == 1:
            continue
        elif res_s[-1] == 1:
            res_s[-1] = s
            res_d[-1] = d
        elif res_s[-1] * res_d[-1] == d:
            res_s[-1] *= s
        else:
            res_s.append(s)
            res_d.append(d)

    if len(res_s) == 1:
        return Layout(res_s[0], res_d[0])
    return Layout(tuple(res_s), tuple(res_d))


def filter_layout(layout: Layout) -> Layout:
    """Remove shape-1 and stride-0 modes, then coalesce."""
    fs: list[int] = []
    fd: list[int] = []
    for s, d in zip(flatten(layout.shape), flatten(layout.stride)):
        if s != 1 and d != 0:
            fs.append(s)
            fd.append(d)
    if not fs:
        return Layout(1, 0)
    return coalesce(Layout(tuple(fs), tuple(fd)))


def is_tractable(layout: Layout) -> bool:
    """Exact tractability condition (Carlisle, Shah, Stern & VanKoughnett, arXiv:2601.05972):
    After flattening and sorting by (stride, shape), every nonzero consecutive pair
    satisfies (s_i * d_i) | d_{i+1}.
    """
    pairs = sorted(zip(flatten(layout.shape), flatten(layout.stride)), key=lambda x: (x[1], x[0]))
    for i in range(len(pairs) - 1):
        s_i, d_i = pairs[i]
        _, d_next = pairs[i + 1]
        if d_i < 0 or d_next < 0:
            return False
        if d_i != 0:
            if d_next % (s_i * d_i) != 0:
                return False
    return True


@dataclass(frozen=True)
class TupleMorphism:
    """Morphism in the category Tuple over E_0 (finite pointed sets with injective nonzero map)."""

    domain: tuple[int, ...]
    codomain: tuple[int, ...]
    alpha: tuple[int, ...]  # 1-indexed into codomain, 0 denotes basepoint * (broadcast)

    def __post_init__(self) -> None:
        assert len(self.alpha) == len(self.domain)
        nonzero = [a for a in self.alpha if a != 0]
        assert len(nonzero) == len(set(nonzero)), "alpha must be injective on nonzero entries"
        for i, a in enumerate(self.alpha):
            if a != 0:
                assert 1 <= a <= len(self.codomain)
                assert self.domain[i] == self.codomain[a - 1]

    def to_flat_layout(self) -> Layout:
        strides: list[int] = []
        for a in self.alpha:
            if a == 0:
                strides.append(0)
            else:
                st = 1
                for j in range(a - 1):
                    st *= self.codomain[j]
                strides.append(st)
        return Layout(self.domain, tuple(strides))


def flat_layout_to_tuple_morphism(layout: Layout) -> TupleMorphism:
    """Canonical functorial realization from tractable flat layout to Tuple morphism."""
    if not is_tractable(layout):
        raise ValueError(f"Layout {layout} is NOT tractable; no Tuple morphism exists.")
    flat_s = flatten(layout.shape)
    flat_d = flatten(layout.stride)
    m = len(flat_s)
    indexed = sorted(enumerate(zip(flat_s, flat_d)), key=lambda x: (x[1][1], x[1][0]))
    perm = [idx + 1 for idx, _ in indexed]
    s_sorted = [sd[0] for _, sd in indexed]
    d_sorted = [sd[1] for _, sd in indexed]

    k = 0
    while k < m and d_sorted[k] == 0:
        k += 1

    cod: list[int] = []
    if k < m:
        cod.extend([d_sorted[k], s_sorted[k]])
        for j in range(k + 1, m):
            denom = s_sorted[j - 1] * d_sorted[j - 1]
            cod.append(d_sorted[j] // denom)
            cod.append(s_sorted[j])

    alpha_prime = [0] * m
    for j in range(k, m):
        alpha_prime[j] = 2 * (j - k + 1)

    inv_perm = [0] * m
    for i in range(m):
        inv_perm[perm[i] - 1] = i + 1
    alpha = [alpha_prime[inv_perm[i] - 1] for i in range(m)]

    # Factorize out redundant 1s from codomain that are not in the image of alpha
    keep = [idx for idx, val in enumerate(cod, start=1) if val != 1 or idx in alpha]
    new_cod = tuple(cod[idx - 1] for idx in keep)
    new_alpha = tuple(0 if a == 0 else keep.index(a) + 1 for a in alpha)
    return TupleMorphism(flat_s, new_cod, new_alpha)


def complement(layout: Layout, cotarget: int, strict_tractable: bool = True) -> Layout:
    """CuTe complement over integer cotarget bound M."""
    filt = filter_layout(layout)
    if filt.stride == 0:
        return Layout(cotarget, 1)

    pairs = sorted(zip(flatten(filt.stride), flatten(filt.shape)))
    res_s: list[int] = []
    res_d: list[int] = []
    curr = 1
    for d, s in pairs:
        if strict_tractable and d % curr != 0:
            raise ValueError(
                f"Non-tractable stride {d} not divisible by current prefix {curr} in {layout}"
            )
        gap = d // curr
        if gap == 0:
            raise ValueError(f"Non-injective layout detected in complement: {layout}")
        res_s.append(gap)
        res_d.append(curr)
        curr = s * d

    res_s.append(ceil_div(cotarget, curr))
    res_d.append(curr)
    return coalesce(Layout(tuple(res_s), tuple(res_d)))


def check_exact_integral_admissibility(lhs: Layout, rhs_s: int, rhs_d: int) -> tuple[bool, str]:
    """Exact necessary-and-sufficient admissibility check for A o (s:d) on coalesced A."""
    flat_a = coalesce(lhs)
    shapes = flatten(flat_a.shape)
    if rhs_s == 1 or rhs_d == 0:
        return True, "trivial"
    rest_s = rhs_s
    rest_d = rhs_d
    for c in shapes[:-1]:
        if rest_s == 1:
            return True, "absorbed"
        if rest_d >= c:
            if rest_d % c != 0:
                return False, f"stride {rest_d} >= mode shape {c} but {c} does not divide {rest_d}"
            rest_d //= c
        else:
            # rest_d < c: check whether the remaining points stay strictly within mode c
            if (rest_s - 1) * rest_d < c:
                return True, "no-wrap"
            # Wraps into outer modes: must reset cleanly to 0 mod c and align shape
            if c % rest_d != 0:
                return False, (
                    f"wrapping stride {rest_d} < mode shape {c} with rest_shape={rest_s} "
                    f"fails exact divisibility {c} % {rest_d} != 0"
                )
            next_s = c // rest_d
            if rest_s % next_s != 0:
                return False, (
                    f"shape divisibility failed: rest_shape={rest_s} not divisible by {next_s}"
                )
            rest_s //= next_s
            rest_d = 1
    return True, "admissible"


def composition(
    lhs: Layout,
    rhs: Layout,
    mode: str = "exact",
) -> Layout:
    """CuTe functional composition lhs o rhs.

    mode:
      - 'exact': enforce exact necessary-and-sufficient admissibility + tractability of multi-mode rhs.
      - 'cutlass_cpp': mirror CUTLASS include/cute/layout.hpp:1076-1111 weak static_assert checks.
      - 'unchecked': run CuTe fold without admissibility assertions (to synthesize counterexamples).
    """
    if isinstance(rhs.shape, tuple):
        if mode == "exact" and not is_tractable(rhs):
            raise ValueError(f"Multi-mode RHS {rhs} is untractable; left-distributivity may fail")
        return make_layout(*(composition(lhs, rhs.mode(i), mode=mode) for i in range(rhs.rank)))

    assert isinstance(rhs.shape, int) and isinstance(rhs.stride, int)
    if rhs.stride == 0:
        return Layout(rhs.shape, 0)

    flat_a = coalesce(lhs)
    if isinstance(flat_a.shape, int):
        assert isinstance(flat_a.stride, int)
        return Layout(rhs.shape, rhs.stride * flat_a.stride)

    if mode == "exact":
        ok, reason = check_exact_integral_admissibility(flat_a, rhs.shape, rhs.stride)
        if not ok:
            raise ValueError(f"Inadmissible composition {lhs} o {rhs}: {reason}")

    shapes = flatten(flat_a.shape)
    strides = flatten(flat_a.stride)
    res_s: list[int] = []
    res_d: list[int] = []
    rest_s = rhs.shape
    rest_d = rhs.stride

    for c_s, c_d in zip(shapes[:-1], strides[:-1]):
        if mode == "cutlass_cpp":
            if not ((rest_d % c_s == 0) or (rest_d < c_s)):
                raise ValueError(
                    f"CUTLASS Stride Divisibility Condition failed: rest_d={rest_d}, c_s={c_s}"
                )
        next_s = ceil_div(c_s, abs(rest_d))
        next_d = ceil_div(abs(rest_d), c_s) * (1 if rest_d >= 0 else -1)
        if next_s != 1 and rest_s != 1:
            new_s = min(next_s, rest_s)
            if mode == "cutlass_cpp":
                if rest_s % new_s != 0:
                    raise ValueError(
                        f"CUTLASS Shape Divisibility Condition failed: rest_s={rest_s}, new_s={new_s}"
                    )
            res_s.append(new_s)
            res_d.append(rest_d * c_d)
            rest_s //= new_s
        rest_d = next_d

    if not res_s:
        return Layout(rest_s, rest_d * strides[-1])
    if rest_s == 1:
        return Layout(res_s[0], res_d[0]) if len(res_s) == 1 else Layout(tuple(res_s), tuple(res_d))
    res_s.append(rest_s)
    res_d.append(rest_d * strides[-1])
    return Layout(tuple(res_s), tuple(res_d))


def logical_divide(lhs: Layout, tiler: Layout) -> Layout:
    return composition(lhs, make_layout(tiler, complement(tiler, lhs.size)))


def logical_product(block: Layout, tiler: Layout) -> Layout:
    return make_layout(block, composition(complement(block, block.size * tiler.cosize), tiler))


def right_inverse(layout: Layout) -> Layout:
    cl = coalesce(layout)
    fs = flatten(cl.shape)
    fd = flatten(cl.stride)
    pre = flatten(prefix_product(fs))
    res_s: list[int] = [1]
    res_d: list[int] = [0]
    curr = 1
    for d, s, r_d in sorted(zip(fd, fs, pre)):
        if s == 1:
            continue
        if d == curr:
            res_s.append(s)
            res_d.append(r_d)
            curr = s * d
    return coalesce(Layout(tuple(res_s), tuple(res_d)))


def left_inverse(layout: Layout) -> Layout:
    return right_inverse(make_layout(layout, complement(layout, layout.cosize)))


def max_common_vector(a: Layout, b: Layout) -> int:
    common = coalesce(composition(a, right_inverse(b)))
    s0 = flatten(common.shape)[0]
    d0 = flatten(common.stride)[0]
    return s0 if d0 == 1 else 1


def verify_cute_algebra() -> dict[str, object]:
    # 1. Coalesce exactness
    l_hier = Layout((2, (1, 6)), (1, (6, 2)))
    l_coal = coalesce(l_hier)
    assert l_coal == Layout(12, 1)
    assert all(l_hier(i) == l_coal(i) for i in range(l_hier.size))

    # 2. Classic CuTe composition example: (6,2):(8,2) o (4,3):(3,1) = ((2,2),3):((24,2),8)
    a = Layout((6, 2), (8, 2))
    b = Layout((4, 3), (3, 1))
    r = composition(a, b, mode="exact")
    assert r == Layout(((2, 2), 3), ((24, 2), 8))
    assert all(r(i) == a(b(i)) for i in range(b.size))

    # 3. Complement & logical_divide & logical_product & inverses
    tiler = Layout(4, 2)
    comp = complement(tiler, 24)
    assert comp == Layout((2, 3), (1, 8))
    # Verify complement postconditions: strictly increasing, disjoint from tiler, covers 24
    tiler_img = {tiler(i) for i in range(tiler.size)}
    comp_vals = [comp(i) for i in range(comp.size)]
    assert all(comp_vals[i - 1] < comp_vals[i] for i in range(1, len(comp_vals)))
    assert set(comp_vals[1:]).isdisjoint(tiler_img)
    combined_tc = make_layout(tiler, comp)
    assert len({combined_tc(i) for i in range(combined_tc.size)}) == combined_tc.size == 24
    assert combined_tc.cosize == 24

    a_div = Layout((4, 2, 3), (2, 1, 8))
    ld = logical_divide(a_div, tiler)
    assert ld == Layout(((2, 2), (2, 3)), ((4, 1), (2, 8)))
    # Bijectivity of logical_divide (permutation of codomain of a_div)
    assert sorted(ld(i) for i in range(ld.size)) == sorted(a_div(i) for i in range(a_div.size))

    a_prod = Layout((2, 2), (4, 1))
    lp = logical_product(a_prod, Layout(6, 1))
    assert lp == Layout(((2, 2), (2, 3)), ((4, 1), (2, 8)))

    # Right & left inverse + max_common_vector
    perm = Layout((4, 8), (8, 1))
    rinv = right_inverse(perm)
    linv = left_inverse(perm)
    assert all(perm(rinv(i)) == i for i in range(rinv.size))
    assert all(linv(perm(i)) == i for i in range(perm.size))
    assert max_common_vector(Layout((8, 4), (1, 8)), Layout((4, 8), (1, 4))) == 32
    assert max_common_vector(Layout((4, 8), (1, 16)), Layout((4, 8), (1, 4))) == 4
    assert max_common_vector(Layout((4, 8), (8, 1)), Layout((4, 8), (1, 4))) == 1

    # 4. Categorical Tuple morphism round-trip on tractable layout
    assert is_tractable(a)
    morph = flat_layout_to_tuple_morphism(a)
    assert morph.to_flat_layout() == a

    # 5. Counterexample A: Untractable injective layout breaks complement exactness
    untractable = Layout((2, 3), (1, 3))
    assert len({untractable(i) for i in range(untractable.size)}) == untractable.size  # injective
    assert not is_tractable(untractable)
    # Unchecked CuTe complement drops holes 2 and 5 because 3 // 2 == 1
    comp_bad = complement(untractable, 12, strict_tractable=False)
    combined_bad = make_layout(untractable, comp_bad)
    covered_bad = {combined_bad(i) for i in range(combined_bad.size)}
    missing_holes = sorted(set(range(untractable.cosize)) - covered_bad)
    assert missing_holes == [2, 5], f"Expected missing holes [2, 5], got {missing_holes}"

    # 6. Counterexample B: CUTLASS C++ static_assert gap on wrapping non-divisible stride
    # A = (4,4):(1,8), B = 4:3 passes CUTLASS layout.hpp:1077 & 1101 checks, yet breaks R(i) == A(B(i))
    a_ce = Layout((4, 4), (1, 8))
    b_ce = Layout(4, 3)
    r_cpp = composition(a_ce, b_ce, mode="cutlass_cpp")
    assert r_cpp == Layout((2, 2), (3, 8))
    mismatches_b = [(i, r_cpp(i), a_ce(b_ce(i))) for i in range(b_ce.size) if r_cpp(i) != a_ce(b_ce(i))]
    assert mismatches_b == [(2, 8, 10), (3, 11, 17)]
    # Exact mode rejects it cleanly
    ok_ce, reason_ce = check_exact_integral_admissibility(a_ce, b_ce.shape, b_ce.stride)
    assert not ok_ce

    # 7. Counterexample C: Injective yet untractable multi-mode RHS breaks left-distributivity!
    # A = (4,4):(1,8), B = (2,2):(1,3) is strictly injective ({0,1,3,4}), each 1-D mode is exact,
    # yet cross-mode carry B(1,1) = 1 + 3 = 4 crosses mode-0 boundary c_0 = 4!
    b_carry = Layout((2, 2), (1, 3))
    assert len({b_carry(i) for i in range(b_carry.size)}) == b_carry.size  # strictly injective!
    assert not is_tractable(b_carry)
    r_carry = composition(a_ce, b_carry, mode="cutlass_cpp")
    assert r_carry == Layout((2, 2), (1, 3))
    assert r_carry((1, 1)) == 4 and a_ce(b_carry((1, 1))) == 8  # homomorphism violation!

    return {
        "coalesce_example": str(l_coal),
        "composition_example": str(r),
        "complement_example": str(comp),
        "logical_divide_example": str(ld),
        "tuple_morphism_codomain": morph.codomain,
        "tuple_morphism_alpha": morph.alpha,
        "counterexample_untractable_missing_holes": missing_holes,
        "counterexample_cutlass_cpp_wrap_mismatches": mismatches_b,
        "counterexample_exact_rejection_reason": reason_ce,
        "counterexample_injective_carry_violation": (r_carry((1, 1)), a_ce(b_carry((1, 1)))),
    }


# =============================================================================
# Part 2: F_2 XOR-Swizzle Morphisms & Exact 32-Bank GPU SMEM Conflict Verifier
# =============================================================================


@dataclass(frozen=True)
class Swizzle:
    """CuTe Swizzle<B, M, S>: offset ^ shiftr(offset & yyy_msk, S)."""

    bits: int
    base: int
    shift: int

    def __post_init__(self) -> None:
        if self.bits < 0 or self.base < 0 or abs(self.shift) < self.bits:
            raise ValueError(
                f"Invalid Swizzle<{self.bits},{self.base},{self.shift}>: require B>=0, M>=0, |S|>=B"
            )

    @property
    def yyy_mask(self) -> int:
        return ((1 << self.bits) - 1) << (self.base + max(0, self.shift))

    @property
    def zzz_mask(self) -> int:
        return ((1 << self.bits) - 1) << (self.base - min(0, self.shift))

    def __call__(self, offset: int) -> int:
        masked = offset & self.yyy_mask
        shifted = (masked >> self.shift) if self.shift >= 0 else (masked << (-self.shift))
        return offset ^ shifted

    def domain_bits(self) -> int:
        return self.bits + self.base + abs(self.shift)

    def f2_matrix(self, n_bits: int) -> list[list[int]]:
        """Return n_bits x n_bits matrix M over GF(2) such that swizzle(x) = M * x (mod 2)."""
        mat = [[1 if i == j else 0 for j in range(n_bits)] for i in range(n_bits)]
        for k in range(self.bits):
            y_bit = self.base + max(0, self.shift) + k
            z_bit = self.base - min(0, self.shift) + k
            if y_bit < n_bits and z_bit < n_bits:
                mat[z_bit][y_bit] ^= 1
        return mat


def f2_matmul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    n = len(a)
    m = len(b[0])
    k_dim = len(b)
    return [
        [sum(a[i][k] * b[k][j] for k in range(k_dim)) % 2 for j in range(m)]
        for i in range(n)
    ]


def f2_rank(matrix: Sequence[Sequence[int]]) -> int:
    """Exact Gaussian elimination rank over GF(2)."""
    rows = [list(r) for r in matrix]
    if not rows:
        return 0
    num_rows, num_cols = len(rows), len(rows[0])
    rank = 0
    for col in range(num_cols):
        pivot = None
        for r in range(rank, num_rows):
            if rows[r][col] == 1:
                pivot = r
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(num_rows):
            if r != rank and rows[r][col] == 1:
                rows[r] = [x ^ y for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def smem_bank_conflict_ways(byte_addrs: Sequence[int]) -> int:
    """Exact 32-bank (4-byte word) GPU SMEM conflict serialization factor for a warp.

    Distinct 4-byte word addresses hitting the same bank serialize; identical word addresses
    broadcast without conflict. Return value 1 = conflict-free; 32 = worst-case 32-way stall.
    """
    bank_to_words: dict[int, set[int]] = {}
    for addr in byte_addrs:
        word = addr >> 2
        bank = word & 0x1F
        bank_to_words.setdefault(bank, set()).add(word)
    return max((len(words) for words in bank_to_words.values()), default=0)


def verify_swizzle_and_banks() -> dict[str, object]:
    # 1. 32x32 f32 tile (4 bytes/elem, 128 bytes/row = 4096 bytes total = 12 address bits)
    # Row-major byte offset: byte_addr(r, c) = (32*r + c) * 4 = (r << 7) | (c << 2)
    # Swizzle<5, 2, 5> in bytes: XORs bits [6:2] (col) with bits [11:7] (row).
    sw_f32 = Swizzle(5, 2, 5)
    assert (sw_f32.yyy_mask & sw_f32.zzz_mask) == 0

    # Algebraic involution proof in GL_12(F_2): M^2 = I_12 and rank = 12
    m_f32 = sw_f32.f2_matrix(12)
    m_f32_sq = f2_matmul(m_f32, m_f32)
    ident_12 = [[1 if i == j else 0 for j in range(12)] for i in range(12)]
    assert m_f32_sq == ident_12 and f2_rank(m_f32) == 12

    # Exhaustive involution & bijectivity check across all 4096 byte addresses
    imgs_f32 = {sw_f32(x) for x in range(4096)}
    assert len(imgs_f32) == 4096
    assert all(sw_f32(sw_f32(x)) == x for x in range(4096))

    # Bank conflict measurement: unswizzled vs Swizzle<5,2,5> on 32x32 f32
    f32_row_unswiz = max(smem_bank_conflict_ways([(32 * r + t) * 4 for t in range(32)]) for r in range(32))
    f32_col_unswiz = max(smem_bank_conflict_ways([(32 * t + c) * 4 for t in range(32)]) for c in range(32))
    f32_row_swiz = max(smem_bank_conflict_ways([sw_f32((32 * r + t) * 4) for t in range(32)]) for r in range(32))
    f32_col_swiz = max(smem_bank_conflict_ways([sw_f32((32 * t + c) * 4) for t in range(32)]) for c in range(32))
    assert (f32_row_unswiz, f32_col_unswiz) == (1, 32)
    assert (f32_row_swiz, f32_col_swiz) == (1, 1)

    # F_2 rank certification for 5-bit lane t -> 5-bit bank b = addr[6:2]
    # For column warp: addr = (t << 7) | (c << 2), swizzled bank bits [6:2] = M[2..6, 7..11] * t XOR c
    a_f32_col_unswiz = [[0] * 5 for _ in range(5)]
    a_f32_col_swiz = [[m_f32[2 + row][7 + col] for col in range(5)] for row in range(5)]
    assert 2 ** (5 - f2_rank(a_f32_col_unswiz)) == 32
    assert 2 ** (5 - f2_rank(a_f32_col_swiz)) == 1

    # 2. 32x32 f16 tile (2 bytes/elem, 64 bytes/row = 2048 bytes total = 11 address bits)
    # Row-major byte offset: byte_addr(r, c) = (32*r + c) * 2 = (r << 6) | (c << 1)
    # Bank bits are byte_addr[6:2]: bit 6 = r[0], bits [5:2] = c[4:1].
    # Swizzle<4, 2, 5> in bytes (equiv. Swizzle<4, 1, 5> in f16 elems): XORs bits [5:2] with bits [10:7] (r[4:1]).
    sw_f16 = Swizzle(4, 2, 5)
    m_f16 = sw_f16.f2_matrix(11)
    ident_11 = [[1 if i == j else 0 for j in range(11)] for i in range(11)]
    assert f2_matmul(m_f16, m_f16) == ident_11 and f2_rank(m_f16) == 11
    assert len({sw_f16(x) for x in range(2048)}) == 2048
    assert all(sw_f16(sw_f16(x)) == x for x in range(2048))

    f16_row_unswiz = max(smem_bank_conflict_ways([(32 * r + t) * 2 for t in range(32)]) for r in range(32))
    f16_col_unswiz = max(smem_bank_conflict_ways([(32 * t + c) * 2 for t in range(32)]) for c in range(32))
    f16_row_swiz = max(smem_bank_conflict_ways([sw_f16((32 * r + t) * 2) for t in range(32)]) for r in range(32))
    f16_col_swiz = max(smem_bank_conflict_ways([sw_f16((32 * t + c) * 2) for t in range(32)]) for c in range(32))
    assert (f16_row_unswiz, f16_col_unswiz) == (1, 16)
    assert (f16_row_swiz, f16_col_swiz) == (1, 1)

    # F_2 bank-map submatrix for 32x32 f16 column warp: lane t is placed at bits [10:6]
    a_f16_col_unswiz = [[1 if (2 + row) == (6 + col) else 0 for col in range(5)] for row in range(5)]
    a_f16_col_swiz = [[m_f16[2 + row][6 + col] for col in range(5)] for row in range(5)]
    assert 2 ** (5 - f2_rank(a_f16_col_unswiz)) == 16
    assert 2 ** (5 - f2_rank(a_f16_col_swiz)) == 1

    # 3. Hopper TMA / wgmma SW128 Atom: Swizzle<3, 4, 3> in bytes on 8x64 f16 (128 bytes/row)
    # 8 threads loading 16-byte (4-bank) ldmatrix/core-matrix chunks from column chunk g in 0..7 across rows 0..7:
    # Unswizzled: all 8 rows hit the same 4 banks -> 8-way conflict!
    # Swizzle<3, 4, 3>: bits [6:4] XOR bits [9:7] (row 0..7) -> 8 distinct 16B bank-groups = 32 banks -> 1-way!
    sw_hopper_128b = Swizzle(3, 4, 3)
    m_hop = sw_hopper_128b.f2_matrix(10)
    ident_10 = [[1 if i == j else 0 for j in range(10)] for i in range(10)]
    assert f2_matmul(m_hop, m_hop) == ident_10 and f2_rank(m_hop) == 10

    def ldmatrix_col_chunk_addrs(chunk_g: int, sw: Swizzle | None) -> list[int]:
        # 8 rows x 4 words (16B) = 32 4-byte bank accesses in one 128B ldmatrix phase
        addrs: list[int] = []
        for row in range(8):
            base_byte = row * 128 + chunk_g * 16
            phys_base = sw(base_byte) if sw is not None else base_byte
            for w in range(4):
                addrs.append(phys_base + 4 * w)
        return addrs

    hop_unswiz = max(smem_bank_conflict_ways(ldmatrix_col_chunk_addrs(g, None)) for g in range(8))
    hop_swiz = max(smem_bank_conflict_ways(ldmatrix_col_chunk_addrs(g, sw_hopper_128b)) for g in range(8))
    assert (hop_unswiz, hop_swiz) == (8, 1)

    # 4. Equivalence check: Triton SwizzledSharedEncodingAttr(vec=8, perPhase=1, maxPhase=8) on 8x64 f16
    # matches CuTe Hopper SW128 (Swizzle<3, 4, 3> in bytes = Swizzle<3, 3, 3> in f16 elements) element-for-element!
    sw_cute_f16 = Swizzle(3, 3, 3)  # M=3 -> 2^3=8 f16 elems (16B), B=3 -> 8 phases, S=3 -> 64 elems/row
    vec, per_phase, max_phase, cols = 8, 1, 8, 64
    for r in range(8):
        for c in range(cols):
            triton_c_swiz = ((c // vec) ^ ((r // per_phase) % max_phase)) * vec + (c % vec)
            triton_idx = r * cols + triton_c_swiz
            cute_idx = sw_cute_f16(r * cols + c)
            assert triton_idx == cute_idx, f"Mismatch at ({r},{c}): {triton_idx} != {cute_idx}"

    return {
        "f32_32x32_unswizzled_row_col_ways": (f32_row_unswiz, f32_col_unswiz),
        "f32_32x32_Swizzle_5_2_5_row_col_ways": (f32_row_swiz, f32_col_swiz),
        "f16_32x32_unswizzled_row_col_ways": (f16_row_unswiz, f16_col_unswiz),
        "f16_32x32_Swizzle_4_2_5_row_col_ways": (f16_row_swiz, f16_col_swiz),
        "hopper_sw128_ldmatrix_unswiz_vs_Swizzle_3_4_3_ways": (hop_unswiz, hop_swiz),
        "triton_swizzled_shared_matches_cute_sw128_f16_exact": True,
        "f2_ranks_col_unswiz_vs_swiz": {
            "f32": (f2_rank(a_f32_col_unswiz), f2_rank(a_f32_col_swiz)),
            "f16": (f2_rank(a_f16_col_unswiz), f2_rank(a_f16_col_swiz)),
        },
    }


# =============================================================================
# Part 3: Exo-Style Affine Effect Analysis, Loop Tiling & Scratchpad Staging
# =============================================================================

Loc = tuple[str, tuple[int, ...]]


@dataclass(frozen=True)
class EffectSet:
    reads: frozenset[Loc]
    writes: frozenset[Loc]
    reduces: frozenset[Loc]

    @property
    def all_locs(self) -> frozenset[Loc]:
        return self.reads | self.writes | self.reduces

    def commutes(self, other: "EffectSet") -> bool:
        """Exact Exo Commutes(a1, a2) predicate (src/exo/rewrite/new_eff.py:1452-1463):
        W1 ∩ All2 = ∅, W2 ∩ All1 = ∅, Red1 ∩ R2 = ∅, Red2 ∩ R1 = ∅.
        Note: Red1 ∩ Red2 is permitted (assumes algebraic associativity/commutativity).
        """
        return (
            self.writes.isdisjoint(other.all_locs)
            and other.writes.isdisjoint(self.all_locs)
            and self.reduces.isdisjoint(other.reads)
            and other.reduces.isdisjoint(self.reads)
        )

    def disjoint_memory(self, other: "EffectSet") -> bool:
        """Exact Exo Disjoint_Memory(a1, a2) predicate (src/exo/rewrite/new_eff.py:1438-1449):
        Used by Check_ParallelizeLoop; forbids concurrent REDUCE to the same location.
        """
        return (
            self.writes.isdisjoint(other.all_locs)
            and other.writes.isdisjoint(self.all_locs)
            and self.reduces.isdisjoint(other.all_locs)
            and other.reduces.isdisjoint(self.all_locs)
        )


def check_reorder_loops(
    x_bound: int,
    y_bound: int,
    body_eff,
) -> tuple[bool, tuple[int, int, int, int] | None]:
    """Check Exo's Check_ReorderLoops condition (new_eff.py:1658-1674):
    forall x < x2, y2 < y: Commutes(body(x, y), body(x2, y2)).
    """
    for x in range(x_bound):
        for x2 in range(x + 1, x_bound):
            for y2 in range(y_bound):
                for y in range(y2 + 1, y_bound):
                    if not body_eff(x, y).commutes(body_eff(x2, y2)):
                        return False, (x, y, x2, y2)
    return True, None


def check_parallelize_loop(bound: int, iter_eff) -> tuple[bool, tuple[int, int] | None]:
    """Check Exo's Check_ParallelizeLoop condition (new_eff.py:1720-1726):
    forall i < i2: Disjoint_Memory(body(i), body(i2)).
    """
    for i in range(bound):
        for i2 in range(i + 1, bound):
            if not iter_eff(i).disjoint_memory(iter_eff(i2)):
                return False, (i, i2)
    return True, None


def verify_stage_mem_window(
    tile_reads: set[Loc],
    tile_writes: set[Loc],
    tile_reduces: set[Loc],
    buf_name: str,
    window_bounds: tuple[tuple[int, int], tuple[int, int]],
    outer_shape: tuple[int, int],
    accum: bool,
) -> tuple[bool, str]:
    """Verify Exo stage_mem window soundness:
    1. Window is strictly in-bounds of outer_shape.
    2. All accesses to buf_name inside the block fall within window_bounds.
    3. If accum=True, block may ONLY reduce into buf_name (no reads or overwriting writes).
    """
    (r0, r1), (c0, c1) = window_bounds
    rows, cols = outer_shape
    if not (0 <= r0 <= r1 <= rows and 0 <= c0 <= c1 <= cols):
        return False, f"Window {window_bounds} out of bounds for {buf_name}{outer_shape}"
    win_locs = {(buf_name, (r, c)) for r in range(r0, r1) for c in range(c0, c1)}

    buf_reads = {loc for loc in tile_reads if loc[0] == buf_name}
    buf_writes = {loc for loc in tile_writes if loc[0] == buf_name}
    buf_reduces = {loc for loc in tile_reduces if loc[0] == buf_name}
    all_buf = buf_reads | buf_writes | buf_reduces

    if not all_buf.issubset(win_locs):
        outside = sorted(all_buf - win_locs)
        return False, f"Accesses {outside[:3]} fall outside staged window {window_bounds}"
    if accum and (buf_reads or buf_writes):
        return False, f"accum=True staging requires reduce-only accesses; found reads/writes on {buf_name}"
    return True, "verified"


def verify_exo_schedule_and_staging() -> dict[str, object]:
    M, N, K = 8, 8, 8
    TM, TN, TK = 4, 4, 4

    # 1. Loop reorder check: GEMM (j, k) interchange succeeds via REDUCE/REDUCE commutativity
    def gemm_jk_eff(j: int, k: int) -> EffectSet:
        return EffectSet(
            reads=frozenset({("A", (0, k)), ("B", (k, j))}),
            writes=frozenset(),
            reduces=frozenset({("C", (0, j))}),
        )

    ok_gemm_reorder, wit_gemm = check_reorder_loops(N, K, gemm_jk_eff)
    assert ok_gemm_reorder and wit_gemm is None

    # 2. Loop reorder counterexample: wavefront X[i, j] = X[i-1, j+1] + 1 has distance (1, -1)
    def wavefront_eff(i: int, j: int) -> EffectSet:
        return EffectSet(
            reads=frozenset({("X", (i - 1, j + 1))}) if (i > 0 and j + 1 < 4) else frozenset(),
            writes=frozenset({("X", (i, j))}),
            reduces=frozenset(),
        )

    ok_wave_reorder, wit_wave = check_reorder_loops(4, 4, wavefront_eff)
    assert not ok_wave_reorder and wit_wave == (0, 1, 1, 0)

    # 3. Parallelize check: outer GEMM i-loop is safe; inner GEMM k-reduction is rejected
    def gemm_outer_i_eff(i: int) -> EffectSet:
        return EffectSet(
            reads=frozenset({("A", (i, k)) for k in range(K)} | {("B", (k, j)) for k in range(K) for j in range(N)}),
            writes=frozenset(),
            reduces=frozenset({("C", (i, j)) for j in range(N)}),
        )

    def gemm_inner_k_eff(k: int) -> EffectSet:
        return EffectSet(
            reads=frozenset({("A", (0, k)), ("B", (k, 0))}),
            writes=frozenset(),
            reduces=frozenset({("C", (0, 0))}),
        )

    ok_par_i, _ = check_parallelize_loop(M, gemm_outer_i_eff)
    ok_par_k, wit_par_k = check_parallelize_loop(K, gemm_inner_k_eff)
    assert ok_par_i and (not ok_par_k) and wit_par_k == (0, 1)

    # 4. Full GEMM tiling + scratchpad staging (stage_mem with accum=True on C_tile)
    A = [[(i * 7 + k * 3 + 1) % 11 for k in range(K)] for i in range(M)]
    B = [[(k * 5 + j * 2 + 3) % 13 for j in range(N)] for k in range(K)]
    C_init = [[(i + j) % 5 for j in range(N)] for i in range(M)]

    # Reference untiled GEMM
    C_ref = [row[:] for row in C_init]
    for i in range(M):
        for j in range(N):
            for k in range(K):
                C_ref[i][j] += A[i][k] * B[k][j]

    # Tiled + scratchpad-staged GEMM with footprint verification at every tile
    C_staged = [row[:] for row in C_init]
    tiles_verified = 0
    for io in range(0, M, TM):
        for jo in range(0, N, TN):
            # stage_mem C[io:io+TM, jo:jo+TN] into C_tile (accum=True -> zero-init + accumulate back)
            C_tile = [[0] * TN for _ in range(TM)]
            tile_reads: set[Loc] = set()
            tile_writes: set[Loc] = set()
            tile_reduces: set[Loc] = set()
            for ko in range(0, K, TK):
                # stage_mem A[io:io+TM, ko:ko+TK] -> A_tile (read-only)
                # stage_mem B[ko:ko+TK, jo:jo+TN] -> B_tile (read-only)
                A_tile = [[A[io + ii][ko + kk] for kk in range(TK)] for ii in range(TM)]
                B_tile = [[B[ko + kk][jo + jj] for jj in range(TN)] for kk in range(TK)]
                k_reads: set[Loc] = set()
                for ii in range(TM):
                    for jj in range(TN):
                        for kk in range(TK):
                            k_reads.add(("A", (io + ii, ko + kk)))
                            k_reads.add(("B", (ko + kk, jo + jj)))
                            tile_reduces.add(("C", (io + ii, jo + jj)))
                            C_tile[ii][jj] += A_tile[ii][kk] * B_tile[kk][jj]
                ok_a, _ = verify_stage_mem_window(k_reads, set(), set(), "A", ((io, io + TM), (ko, ko + TK)), (M, K), False)
                ok_b, _ = verify_stage_mem_window(k_reads, set(), set(), "B", ((ko, ko + TK), (jo, jo + TN)), (K, N), False)
                assert ok_a and ok_b
                tile_reads |= k_reads
            ok_c, _ = verify_stage_mem_window(tile_reads, tile_writes, tile_reduces, "C", ((io, io + TM), (jo, jo + TN)), (M, N), True)
            assert ok_c
            # Accumulate-back C_tile into C_staged
            for ii in range(TM):
                for jj in range(TN):
                    C_staged[io + ii][jo + jj] += C_tile[ii][jj]
            tiles_verified += 1

    assert C_staged == C_ref

    # Negative staging test: undersized window (missing last row) is rejected
    ok_bad_win, bad_win_msg = verify_stage_mem_window(
        {("A", (r, c)) for r in range(4) for c in range(4)},
        set(),
        set(),
        "A",
        ((0, 3), (0, 4)),
        (M, K),
        False,
    )
    assert not ok_bad_win

    return {
        "gemm_jk_reorder_safe": ok_gemm_reorder,
        "wavefront_reorder_counterexample": wit_wave,
        "gemm_outer_i_parallel_safe": ok_par_i,
        "gemm_inner_k_parallel_counterexample": wit_par_k,
        "tiled_staged_gemm_tiles_verified": tiles_verified,
        "tiled_staged_gemm_exact_match": C_staged == C_ref,
        "undersized_window_rejected": (not ok_bad_win, bad_win_msg),
    }


def main() -> int:
    cute_res = verify_cute_algebra()
    swiz_res = verify_swizzle_and_banks()
    exo_res = verify_exo_schedule_and_staging()

    print("=== [1] CuTe Hierarchical Layout Algebra & Tractability ===")
    for k, v in cute_res.items():
        print(f"  {k}: {v}")

    print("=== [2] F_2 XOR-Swizzle Involution & 32-Bank SMEM Conflict Verification ===")
    for k, v in swiz_res.items():
        print(f"  {k}: {v}")

    print("=== [3] Exo-Style Affine Effect Analysis & Scratchpad Staging Equivalence ===")
    for k, v in exo_res.items():
        print(f"  {k}: {v}")

    print("ALL VERIFICATION CHECKS PASSED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
