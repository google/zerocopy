#!/usr/bin/env python3
"""Bit-exact standalone verification probe for:
  1. FP8 (OCP E4M3FN / E5M2) and IEEE P3109 v4.1 (Binary8p4sf / Binary8p4se /
     Binary4p2sf) codecs and IEEE-754 compiler rewrite unsoundness.
  2. OCP Microscaling v1.0 MXFP4 (E2M1 + 32-element shared E8M0 scale) codec,
     scale-NaN poisoning, and single-element mutation sibling quantization drift.
  3. Posit Standard (2022) exact Posit16/Quire16 (256-bit) order-invariant dot
     product vs IEEE-754 binary16 catastrophic cancellation, Hardware Stochastic
     Rounding (SR Mode 1 / P3109 StochasticA) exact unbiasedness vs illegal CSE
     variance doubling & nonlinear bias, and DSP Q1.15 saturation semantics.
  4. P4_16 / Petr4 header-validity typestate, header_union invalid-member write
     havoc, copy-in/copy-out aliasing, and Domino/Chipmunk single-cycle SALU
     Tarjan-SCC pipeline schedulability checks.

Requires Python 3.10+ standard library only. Exits 0 iff all checks pass.
"""

from __future__ import annotations

import bisect
import itertools
import math
import random
import struct
from collections import defaultdict
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


# =============================================================================
# PART 1: FP8 (OCP E4M3FN / E5M2) & IEEE P3109 v4.1 Codecs + Rewrite Soundness
# =============================================================================

@dataclass(frozen=True)
class ExtReal:
    """Closed extended real value (Fraction, +inf, -inf, or NaN)."""
    kind: str  # "finite", "+inf", "-inf", "nan"
    val: Fraction = Fraction(0)

    @staticmethod
    def finite(v: Fraction | int | float) -> "ExtReal":
        if isinstance(v, float):
            if math.isnan(v):
                return ExtReal("nan")
            if math.isinf(v):
                return ExtReal("+inf" if v > 0 else "-inf")
            return ExtReal("finite", Fraction(v))
        return ExtReal("finite", Fraction(v))

    @staticmethod
    def pos_inf() -> "ExtReal":
        return ExtReal("+inf")

    @staticmethod
    def neg_inf() -> "ExtReal":
        return ExtReal("-inf")

    @staticmethod
    def nan() -> "ExtReal":
        return ExtReal("nan")

    def is_finite(self) -> bool:
        return self.kind == "finite"

    def is_nan(self) -> bool:
        return self.kind == "nan"

    def is_inf(self) -> bool:
        return self.kind in ("+inf", "-inf")


def decode_ocp_e4m3fn(byte: int) -> ExtReal:
    """Decode OCP/Micikevicius FP8 E4M3FN (S.EEEE.MMM, bias=7, no Inf, 0x7F/0xFF=NaN)."""
    assert 0 <= byte <= 0xFF
    s = (byte >> 7) & 1
    e = (byte >> 3) & 0xF
    m = byte & 0x7
    if e == 0xF and m == 0x7:
        return ExtReal.nan()
    sign = -1 if s else 1
    if e == 0:
        return ExtReal.finite(sign * Fraction(m, 8) * Fraction(1, 1 << 6))
    return ExtReal.finite(sign * (1 + Fraction(m, 8)) * (Fraction(1 << (e - 7)) if e >= 7 else Fraction(1, 1 << (7 - e))))


def decode_ocp_e5m2(byte: int) -> ExtReal:
    """Decode OCP/Micikevicius FP8 E5M2 (S.EEEEE.MM, bias=15, IEEE Inf/NaN)."""
    assert 0 <= byte <= 0xFF
    s = (byte >> 7) & 1
    e = (byte >> 2) & 0x1F
    m = byte & 0x3
    if e == 0x1F:
        if m == 0:
            return ExtReal.neg_inf() if s else ExtReal.pos_inf()
        return ExtReal.nan()
    sign = -1 if s else 1
    if e == 0:
        return ExtReal.finite(sign * Fraction(m, 4) * Fraction(1, 1 << 14))
    return ExtReal.finite(sign * (1 + Fraction(m, 4)) * (Fraction(1 << (e - 15)) if e >= 15 else Fraction(1, 1 << (15 - e))))


def decode_p3109(byte: int, k: int, p: int, signed: bool, extended: bool) -> ExtReal:
    """Decode IEEE P3109 v4.1 Binary{K, P, Sigma, Delta} per Sec. 3.1, 4.7.2, 4.7.6, Annex B."""
    assert k > 2
    assert 0 < byte < (1 << k) or byte == 0
    if signed:
        assert 0 < p < k
        bias = 1 << (k - p - 1)
        if byte == 0:
            return ExtReal.finite(0)
        if byte == (1 << (k - 1)):
            return ExtReal.nan()
        if extended:
            if byte == (1 << (k - 1)) - 1:
                return ExtReal.pos_inf()
            if byte == (1 << k) - 1:
                return ExtReal.neg_inf()
        neg = (byte >> (k - 1)) & 1
        mag = byte & ((1 << (k - 1)) - 1)
    else:
        assert 0 < p <= k
        bias = 1 << (k - p)
        if byte == 0:
            return ExtReal.finite(0)
        if byte == (1 << k) - 1:
            return ExtReal.nan()
        if extended and byte == (1 << k) - 2:
            return ExtReal.pos_inf()
        neg = 0
        mag = byte

    t_bits = p - 1
    t = mag & ((1 << t_bits) - 1)
    eb = mag >> t_bits
    if eb == 0:
        # Subnormal: S = T, E = 1 - B
        sig = t
        exp = 1 - bias
    else:
        # Normal: S = 2^(P-1) + T, E = eb - B
        sig = (1 << t_bits) + t
        exp = eb - bias
    # Value = (-1)^neg * S * 2^(1 - P + E)
    shift = 1 - p + exp
    val = Fraction(sig << shift) if shift >= 0 else Fraction(sig, 1 << (-shift))
    return ExtReal.finite(-val if neg else val)


def round_to_nearest_even_code(x: Fraction, finite_table: List[Tuple[Fraction, int]], max_mag: Fraction) -> Tuple[Optional[int], bool]:
    """Round finite Fraction x to nearest-even code in finite_table.

    Returns (code, overflowed). Follows IEEE-754/P3109 rule: values strictly below
    max_mag + 0.5 * ulp(max_mag) round to max_mag; >= that threshold overflow.
    """
    if x == 0:
        return 0x00, False
    neg = x < 0
    ax = abs(x)
    # Build sorted unique non-negative magnitudes from finite_table
    pos_entries = sorted((v, c) for v, c in finite_table if v >= 0)
    # Determine top two positive magnitudes to compute exact overflow threshold
    top_v = pos_entries[-1][0]
    prev_v = pos_entries[-2][0]
    top_ulp = top_v - prev_v
    if ax >= top_v + Fraction(1, 2) * top_ulp:
        return None, True

    # Find bracketing entries
    best_code = pos_entries[0][1]
    best_dist = abs(ax - pos_entries[0][0])
    for v, c in pos_entries[1:]:
        d = abs(ax - v)
        if d < best_dist:
            best_dist = d
            best_code = c
        elif d == best_dist:
            # Tie to even LSB of code point
            if (c & 1) == 0:
                best_code = c

    if best_code == 0:
        return (0x00, False)
    if neg:
        # Find negative counterpart in finite_table
        pos_val = dict((c, v) for v, c in pos_entries)[best_code]
        for v, c in finite_table:
            if v == -pos_val:
                return c, False
    return best_code, False


_E4M3FN_FINITE_TABLE: List[Tuple[Fraction, int]] = [
    (d.val, b)
    for b in range(256)
    if b != 0x80 and (d := decode_ocp_e4m3fn(b)).is_finite()
]

_P3109_8P4SF_FINITE_TABLE: List[Tuple[Fraction, int]] = [
    (d.val, b)
    for b in range(256)
    if (d := decode_p3109(b, k=8, p=4, signed=True, extended=False)).is_finite()
]


def encode_ocp_e4m3fn(x: ExtReal, mode: str) -> int:
    """Encode ExtReal into OCP E4M3FN with mode in {'SAT', 'OVF'} per OCP MX v1.0 Table 3."""
    assert mode in ("SAT", "OVF")
    if x.is_nan():
        return 0x7F
    if x.is_inf():
        if mode == "SAT":
            return 0x7E if x.kind == "+inf" else 0xFE
        return 0x7F  # OVF maps +/-Inf to NaN in E4M3!
    code, ovf = round_to_nearest_even_code(x.val, _E4M3FN_FINITE_TABLE, Fraction(448))
    if ovf:
        if mode == "SAT":
            return 0x7E if x.val > 0 else 0xFE
        return 0x7F  # OVF maps overflow to NaN in E4M3!
    assert code is not None
    return code


def encode_p3109_binary8p4sf(x: ExtReal, sat_mode: str) -> int:
    """Encode ExtReal into IEEE P3109 v4.1 Binary8p4sf (K=8, P=4, Signed, Finite).

    sat_mode in {'SatFinite', 'SatPropagate', 'SatNone'} with NearestTiesToEven.
    """
    assert sat_mode in ("SatFinite", "SatPropagate", "SatNone")
    if x.is_nan():
        return 0x80  # Single NaN at 2^(K-1)
    if x.is_inf():
        if sat_mode in ("SatFinite", "SatPropagate"):
            return 0x7F if x.kind == "+inf" else 0xFF
        return 0x80  # SatNone on Finite domain -> NaN per P3109 Sec 4.7.5!
    code, ovf = round_to_nearest_even_code(x.val, _P3109_8P4SF_FINITE_TABLE, Fraction(240))
    if ovf:
        if sat_mode in ("SatFinite", "SatPropagate"):
            return 0x7F if x.val > 0 else 0xFF
        return 0x80  # SatNone on Finite domain -> NaN per P3109 Sec 4.7.5!
    assert code is not None
    return code


def verify_part1_fp8_and_p3109() -> None:
    print("=== PART 1: FP8 (OCP E4M3FN / E5M2) & IEEE P3109 v4.1 Verification ===")

    # 1a. Exhaustive table sanity across all 256 code points
    e4m3_vals = [decode_ocp_e4m3fn(b) for b in range(256)]
    e5m2_vals = [decode_ocp_e5m2(b) for b in range(256)]
    p3109_sf_vals = [decode_p3109(b, 8, 4, True, False) for b in range(256)]
    p3109_se_vals = [decode_p3109(b, 8, 4, True, True) for b in range(256)]

    # OCP E4M3FN: 0 Infs, 2 NaNs (0x7F, 0xFF), 2 zeros (0x00, 0x80), max finite 448, min subnorm 2^-9
    assert sum(v.is_inf() for v in e4m3_vals) == 0
    assert [b for b, v in enumerate(e4m3_vals) if v.is_nan()] == [0x7F, 0xFF]
    assert max(v.val for v in e4m3_vals if v.is_finite()) == Fraction(448)
    assert min(v.val for v in e4m3_vals if v.is_finite() and v.val > 0) == Fraction(1, 512)
    assert decode_ocp_e4m3fn(0x80) == ExtReal.finite(0)  # -0.0

    # OCP E5M2: 2 Infs (0x7C, 0xFC), 6 NaNs, max finite 57344, min subnorm 2^-16
    assert [b for b, v in enumerate(e5m2_vals) if v.is_inf()] == [0x7C, 0xFC]
    assert sum(v.is_nan() for v in e5m2_vals) == 6
    assert max(v.val for v in e5m2_vals if v.is_finite()) == Fraction(57344)
    assert min(v.val for v in e5m2_vals if v.is_finite() and v.val > 0) == Fraction(1, 65536)

    # IEEE P3109 Binary8p4sf (v4.1): bias=8, 0 Infs, 1 NaN at 0x80, 1 zero at 0x00, max finite 240
    assert sum(v.is_inf() for v in p3109_sf_vals) == 0
    assert [b for b, v in enumerate(p3109_sf_vals) if v.is_nan()] == [0x80]
    assert [b for b, v in enumerate(p3109_sf_vals) if v.is_finite() and v.val == 0] == [0x00]
    assert max(v.val for v in p3109_sf_vals if v.is_finite()) == Fraction(240)
    # IEEE P3109 Binary8p4se (v4.1): 2 Infs at 0x7F/0xFF, 1 NaN at 0x80, max finite 224
    assert [b for b, v in enumerate(p3109_se_vals) if v.is_inf()] == [0x7F, 0xFF]
    assert [b for b, v in enumerate(p3109_se_vals) if v.is_nan()] == [0x80]
    assert max(v.val for v in p3109_se_vals if v.is_finite()) == Fraction(224)
    # Verify Annex B Table 5 (Binary4p2sf): bias = 2^(4-2-1) = 2, max finite = 3.0, 0x8 = NaN
    b4p2sf = [decode_p3109(b, 4, 2, True, False) for b in range(16)]
    assert b4p2sf[7] == ExtReal.finite(3)
    assert b4p2sf[8].is_nan()
    assert b4p2sf[15] == ExtReal.finite(-3)

    # 1b. Concrete IEEE-754 Rewrite Unsoundness Counterexamples
    # Counterexample A: Overflow-to-NaN breaks `isinf` and `x - x == 0` under E4M3FN OVF & P3109 SatNone
    x_ovf_e4m3 = encode_ocp_e4m3fn(ExtReal.finite(256 + 256), mode="OVF")
    d_ovf_e4m3 = decode_ocp_e4m3fn(x_ovf_e4m3)
    assert d_ovf_e4m3.is_nan() and not d_ovf_e4m3.is_inf()
    x_ovf_p3109 = encode_p3109_binary8p4sf(ExtReal.finite(160 + 160), sat_mode="SatNone")
    assert decode_p3109(x_ovf_p3109, 8, 4, True, False).is_nan()

    # Counterexample B: Saturation breaks algebraic inverse `(2.0 * x) * 0.5 == x` without producing Inf
    x_val = Fraction(256)  # Exact in E4M3FN (0x78)
    assert decode_ocp_e4m3fn(encode_ocp_e4m3fn(ExtReal.finite(x_val), "SAT")).val == x_val
    step1_sat = decode_ocp_e4m3fn(encode_ocp_e4m3fn(ExtReal.finite(2 * x_val), "SAT")).val
    step2_sat = decode_ocp_e4m3fn(encode_ocp_e4m3fn(ExtReal.finite(step1_sat * Fraction(1, 2)), "SAT")).val
    assert step1_sat == Fraction(448)
    assert step2_sat == Fraction(224) and step2_sat != x_val  # Silent 32.0 loss with no Inf/NaN!

    # Counterexample C: Bitwise sign-flip `x ^ 0x80` on +0.0 yields -0.0 in OCP E4M3FN but NaN in P3109!
    zero_byte = 0x00
    flipped = zero_byte ^ 0x80
    assert decode_ocp_e4m3fn(flipped) == ExtReal.finite(0)
    assert decode_p3109(flipped, 8, 4, True, False).is_nan()

    print(f"  [OK] OCP E4M3FN: 0 Infs, 2 NaNs (0x7F/0xFF), max=448, min_subnorm=2^-9")
    print(f"  [OK] IEEE P3109 v4.1 Binary8p4sf: bias=8, 0 Infs, 1 NaN (0x80), max=240; Binary8p4se max=224")
    print(f"  [OK] Unsoundness A (OVF/SatNone): E4M3FN(256+256)=NaN (not +Inf); P3109_8p4sf(160+160)=NaN")
    print(f"  [OK] Unsoundness B (SAT inverse): E4M3FN_SAT(256*2)*0.5 = {float(step2_sat)} != 256.0 (silent clamp)")
    print(f"  [OK] Unsoundness C (xor-0x80 neg): 0x00^0x80 -> -0.0 in E4M3FN, but NaN in P3109 Binary8p4sf")


# =============================================================================
# PART 2: OCP Microscaling v1.0 MXFP4 (E2M1 + 32-Element Shared E8M0 Scale)
# =============================================================================

# OCP MX v1.0 Table 5: FP4 E2M1 (bias=1, no Inf, no NaN, largest power-of-2 = 4 = 2^2)
E2M1_TABLE: Tuple[Fraction, ...] = (
    Fraction(0), Fraction(1, 2), Fraction(1), Fraction(3, 2),
    Fraction(2), Fraction(3), Fraction(4), Fraction(6),
    Fraction(0), Fraction(-1, 2), Fraction(-1), Fraction(-3, 2),
    Fraction(-2), Fraction(-3), Fraction(-4), Fraction(-6),
)


def decode_e2m1(nibble: int) -> Fraction:
    assert 0 <= nibble <= 0xF
    return E2M1_TABLE[nibble]


def encode_e2m1_rtne_sat(x: Fraction) -> int:
    """Quantize finite Fraction x to OCP FP4 E2M1 using RTNE + clamp to +/-6.0."""
    if x == 0:
        return 0
    neg = x < 0
    ax = abs(x)
    if ax >= Fraction(6):
        code = 7
    else:
        pos_vals = E2M1_TABLE[:8]
        best_code = 0
        best_dist = abs(ax - pos_vals[0])
        for c in range(1, 8):
            d = abs(ax - pos_vals[c])
            if d < best_dist or (d == best_dist and (c & 1) == 0):
                best_dist = d
                best_code = c
        code = best_code
    return (8 | code) if (neg and code != 0) else code


def decode_e8m0(scale_byte: int) -> ExtReal:
    """OCP MX v1.0 Table 7: E8M0 (bias=127, 0x00..0xFE => 2^(e-127), 0xFF => NaN)."""
    assert 0 <= scale_byte <= 0xFF
    if scale_byte == 0xFF:
        return ExtReal.nan()
    exp = scale_byte - 127
    return ExtReal.finite(Fraction(1 << exp) if exp >= 0 else Fraction(1, 1 << (-exp)))


def compute_mxfp4_scale_byte(values: Sequence[Fraction]) -> int:
    """OCP MX v1.0 Sec 6.3: X = largest pow2 <= max(|V_i|) / largest_pow2_in_E2M1 (4)."""
    assert len(values) == 32
    max_abs = max(abs(v) for v in values)
    if max_abs == 0:
        return 0  # smallest finite scale 2^-127
    # floor(log2(max_abs))
    # Compute exact floor(log2(p/q)) using bit_length
    p, q = max_abs.numerator, max_abs.denominator
    e = p.bit_length() - q.bit_length()
    if (p << max(0, -e)) < (q << max(0, e)):
        e -= 1
    shared_exp = e - 2  # largest power of 2 in E2M1 is 2^2 = 4
    if shared_exp > 127:
        return 0xFF  # NaN overflow
    if shared_exp < -127:
        return 0
    return shared_exp + 127


@dataclass
class MxFp4Block:
    """32-element OCP MXFP4 block: 1 shared E8M0 byte + 32 x 4-bit E2M1 codes (17 bytes total)."""
    scale_byte: int
    nibbles: List[int]

    @classmethod
    def quantize(cls, values: Sequence[Fraction]) -> "MxFp4Block":
        assert len(values) == 32
        sb = compute_mxfp4_scale_byte(values)
        scale = decode_e8m0(sb)
        if scale.is_nan():
            return cls(sb, [0] * 32)
        nibbles = [encode_e2m1_rtne_sat(v / scale.val) for v in values]
        return cls(sb, nibbles)

    def dequantize(self) -> List[ExtReal]:
        scale = decode_e8m0(self.scale_byte)
        if scale.is_nan():
            # OCP MX v1.0 Sec 5.1: X = NaN => all k elements are NaN regardless of P_i
            return [ExtReal.nan() for _ in range(32)]
        return [ExtReal.finite(scale.val * decode_e2m1(n)) for n in self.nibbles]


def verify_part2_ocp_mxfp4() -> None:
    print("=== PART 2: OCP Microscaling v1.0 MXFP4 Block-Coupling Verification ===")

    # Verify E2M1 exact codebook and E8M0 NaN broadcast
    assert len(set(E2M1_TABLE)) == 15  # {0, +/-0.5, +/-1, +/-1.5, +/-2, +/-3, +/-4, +/-6}
    nan_block = MxFp4Block(scale_byte=0xFF, nibbles=[2] * 32)
    assert all(v.is_nan() for v in nan_block.dequantize())

    # Build a 32-element vector where v[0..30] are exact under initial scale X = 2^-2 = 0.25
    # Values in {0.25, 0.5, 0.75, 1.0, 1.5} -> max = 1.5 -> floor(log2(1.5))=0 -> exp = 0-2 = -2 (0x7D)
    orig_vec = [Fraction(1, 2) if i % 2 == 0 else Fraction(3, 4) for i in range(31)] + [Fraction(1)]
    orig_vec[30] = Fraction(3, 2)  # 1.5
    blk = MxFp4Block.quantize(orig_vec)
    assert blk.scale_byte == 125  # 0x7D => 2^-2 = 0.25
    deq_before = [x.val for x in blk.dequantize()]
    assert deq_before == orig_vec, f"Expected exact quantization before mutation, got {deq_before}"

    # Mutate ONLY index 31 from 1.0 to 128.0 (simulating &mut elem[31] = 128.0)
    mutated_vec = list(deq_before)
    mutated_vec[31] = Fraction(128)

    # Strategy 1: Re-quantize block to preserve mutated element 31 -> catastrophic sibling drift!
    blk_requant = MxFp4Block.quantize(mutated_vec)
    assert blk_requant.scale_byte == 132  # 0x84 => 2^(7-2) = 2^5 = 32.0
    deq_requant = [x.val for x in blk_requant.dequantize()]
    assert deq_requant[31] == Fraction(128)  # 32 * 4.0 = 128 exact
    flushed_siblings = sum(1 for i in range(31) if deq_requant[i] == 0)
    assert flushed_siblings == 31  # ALL 31 untouched siblings silently flushed to 0.0!

    # Strategy 2: Hold shared scale fixed to avoid sibling aliasing -> mutated element clamps to 1.5!
    fixed_nibbles = list(blk.nibbles)
    fixed_nibbles[31] = encode_e2m1_rtne_sat(Fraction(128) / decode_e8m0(blk.scale_byte).val)
    blk_fixed = MxFp4Block(blk.scale_byte, fixed_nibbles)
    deq_fixed = [x.val for x in blk_fixed.dequantize()]
    assert deq_fixed[:31] == orig_vec[:31]
    assert deq_fixed[31] == Fraction(3, 2)  # 98.83% error on the written element!

    print(f"  [OK] MXFP4 initial block: scale=0x{blk.scale_byte:02x} (2^-2=0.25), 32/32 elements exact")
    print(f"  [OK] Mutate elem[31]=128.0 (re-scale): scale->0x{blk_requant.scale_byte:02x} (32.0), "
          f"{flushed_siblings}/31 untouched siblings silently flushed to 0.0")
    print(f"  [OK] Mutate elem[31]=128.0 (fixed-scale): elem[31] clamps to {float(deq_fixed[31])} (error 98.83%)")
    print(f"  [OK] E8M0=0xFF NaN poisoning: 32/32 elements evaluate to NaN")


# =============================================================================
# PART 3: Posit16/Quire16 Exact Associativity, Stochastic Rounding & DSP Q1.15
# =============================================================================

def decode_posit16(bits: int) -> Optional[Fraction]:
    """Decode Posit Standard (2022) posit16 (n=16, es=2) to exact Fraction or None (NaR)."""
    assert 0 <= bits < (1 << 16)
    if bits == 0:
        return Fraction(0)
    if bits == 0x8000:
        return None  # NaR
    s = (bits >> 15) & 1
    r0 = (bits >> 14) & 1
    # Count regime run length k starting at bit 14 downward
    k = 0
    idx = 14
    while idx >= 0 and ((bits >> idx) & 1) == r0:
        k += 1
        idx -= 1
    # Skip terminating bit (if present)
    idx -= 1
    r = (k - 1) if r0 == 1 else -k
    # Extract up to 2 exponent bits (truncated bits treated as 0)
    e = 0
    for shift in (1, 0):
        if idx >= 0:
            e |= ((bits >> idx) & 1) << shift
            idx -= 1
    # Extract remaining m fraction bits (0 <= m <= 11)
    m = max(0, idx + 1)
    f_int = bits & ((1 << m) - 1) if m > 0 else 0
    f = Fraction(f_int, 1 << m)
    # Posit Standard 2022 Sec 3.3 formula: p = ((1 - 3s) + f) * 2^((1 - 2s)*(4r + e + s))
    exp = (1 - 2 * s) * (4 * r + e + s)
    scale = Fraction(1 << exp) if exp >= 0 else Fraction(1, 1 << (-exp))
    return ((1 - 3 * s) + f) * scale


class Quire16:
    """Exact 256-bit 2's-complement Quire for posit16 per Posit Standard (2022) Sec 3.4.

    Layout: 1 sign bit + 31 carry bits + 112 integer bits + 112 fraction bits = 256 bits.
    Represents q = acc * 2^(-112), with NaR sentinel = -2^255.
    """
    WIDTH = 256
    FRAC_BITS = 112  # 8*16 - 16
    NAR = -(1 << 255)
    MIN_VAL = -(1 << 255) + 1
    MAX_VAL = (1 << 255) - 1

    def __init__(self) -> None:
        self.acc: int = 0  # exact signed 256-bit integer (in units of 2^-112)

    def is_nar(self) -> bool:
        return self.acc == self.NAR

    def q_mul_add(self, p1: Optional[Fraction], p2: Optional[Fraction]) -> None:
        if self.is_nar() or p1 is None or p2 is None:
            self.acc = self.NAR
            return
        prod = p1 * p2
        scaled = prod * (1 << self.FRAC_BITS)
        assert scaled.denominator == 1, f"Product {prod} not exact in Quire16!"
        nxt = self.acc + scaled.numerator
        if nxt < self.MIN_VAL or nxt > self.MAX_VAL:
            self.acc = self.NAR
        else:
            self.acc = nxt

    def exact_value(self) -> Optional[Fraction]:
        if self.is_nar():
            return None
        return Fraction(self.acc, 1 << self.FRAC_BITS)


def fp16_round(x: float) -> float:
    """Round Python float to IEEE-754 binary16 via struct ('e' format, RTNE)."""
    return struct.unpack("<e", struct.pack("<e", x))[0]


def p3109_stochastic_a(x: Fraction, x1: Fraction, x2: Fraction, n_bits: int, r: int) -> Fraction:
    """IEEE P3109 v4.1 Sec 4.7.4 StochasticA_{N,R} rounding between adjacent grid points x1 <= x <= x2."""
    assert x1 <= x <= x2 and x2 > x1
    assert 0 <= r < (1 << n_bits)
    nu = (x - x1) / (x2 - x1)  # in [0, 1]
    threshold = math.floor(nu * (1 << n_bits)) + r
    return x2 if threshold >= (1 << n_bits) else x1


def q15_mul_sat(a: int, b: int) -> int:
    """ARM SQDMULH-equivalent Q1.15 signed saturating fractional multiply."""
    assert -32768 <= a <= 32767 and -32768 <= b <= 32767
    if a == -32768 and b == -32768:
        return 32767  # Saturate +1.0 -> +0.99996948 instead of wrapping to -32768 (-1.0)
    return (a * b) >> 15


def q15_mul_wrap(a: int, b: int) -> int:
    """Wrapping 16-bit two's-complement Q1.15 multiply (demonstrating -1 * -1 = -1 wrap bug)."""
    raw = (a * b) >> 15
    raw16 = raw & 0xFFFF
    return raw16 - 0x10000 if raw16 >= 0x8000 else raw16


def q15_add_sat(a: int, b: int) -> int:
    """LLVM llvm.sadd.sat.i16 / ARM VQADD.S16 signed 16-bit saturating add."""
    s = a + b
    if s > 32767:
        return 32767
    if s < -32768:
        return -32768
    return s


def verify_part3_quire_sr_and_dsp() -> None:
    print("=== PART 3: Posit16/Quire16, Stochastic Rounding CSE & DSP Q1.15 Verification ===")

    # 3a. Verify Posit16 boundary encodings against Posit Standard 2022 Table 1
    assert decode_posit16(0x0000) == Fraction(0)
    assert decode_posit16(0x8000) is None  # NaR
    assert decode_posit16(0x0001) == Fraction(1, 1 << 56)  # minPos = 2^-56
    assert decode_posit16(0x7FFF) == Fraction(1 << 56)     # maxPos = 2^56
    assert decode_posit16(0x4000) == Fraction(1)           # 1.0
    assert decode_posit16(0xC000) == Fraction(-1)          # -1.0
    assert decode_posit16(0xFFFF) == Fraction(-1, 1 << 56) # -minPos

    # 3b. Quire16 exact order-invariance vs IEEE binary16 catastrophic cancellation
    # Direct exact posit16 codes verified via decode_posit16:
    #   +1024 = 0b0_1110_10_000000000 = 0x7400 (r=2, e=2 => 2^(4*2+2)=2^10)
    #   -1024 = 0x10000 - 0x7400 = 0x8C00
    #   +32   = 0b0_110_01_0000000000 = 0x6400 (r=1, e=1 => 2^(4*1+1)=2^5)
    #   +1    = 0x4000
    #   2^-10 = 0b0_0001_10_000000000 = 0x0C00 (r=-3, e=2 => 2^(4*-3+2)=2^-10)
    val_to_p16: Dict[Fraction, int] = {
        Fraction(1024): 0x7400,
        Fraction(-1024): 0x8C00,
        Fraction(32): 0x6400,
        Fraction(1): 0x4000,
        Fraction(1, 1024): 0x0C00,
    }
    for expected_val, code in val_to_p16.items():
        assert decode_posit16(code) == expected_val, f"0x{code:04x} decoded to {decode_posit16(code)}"

    pairs = [
        (Fraction(1024), Fraction(32)),   # +32768.0
        (Fraction(-1024), Fraction(32)),  # -32768.0
        (Fraction(1), Fraction(1, 1024)), # +2^-10
        (Fraction(1), Fraction(1, 1024)), # +2^-10
    ]
    exact_dot = Fraction(1, 512)  # 2^-9

    quire_results = set()
    fp16_results = set()
    for perm in itertools.permutations(pairs):
        # Exact Quire16 accumulation
        q = Quire16()
        for a, b in perm:
            q.q_mul_add(decode_posit16(val_to_p16[a]), decode_posit16(val_to_p16[b]))
        quire_results.add(q.exact_value())

        # IEEE-754 binary16 left-to-right sequential dot product
        acc16 = 0.0
        for a, b in perm:
            prod16 = fp16_round(fp16_round(float(a)) * fp16_round(float(b)))
            acc16 = fp16_round(acc16 + prod16)
        fp16_results.add(acc16)

    assert quire_results == {exact_dot}, f"Quire16 lost order-invariance: {quire_results}"
    assert len(fp16_results) > 1 and 0.0 in fp16_results, f"Expected FP16 cancellation, got {fp16_results}"

    # 3c. Exact Analytic Stochastic Rounding (Mode 1 / P3109 StochasticA) vs Illegal CSE
    # Exhaustively enumerate all 2^N PRNG states (N=4 => 16 states, exact Fraction math!)
    x1, x2 = Fraction(1), Fraction(2)
    x = Fraction(11, 8)  # 1.375 -> exact binary fraction nu = 3/8 = 6/16
    n_bits = 4
    n_states = 1 << n_bits
    outcomes = [p3109_stochastic_a(x, x1, x2, n_bits, r) for r in range(n_states)]
    mean_sr = sum(outcomes) / n_states
    var_sr = sum((y - mean_sr) ** 2 for y in outcomes) / n_states
    analytic_var = (x - x1) * (x2 - x)
    assert mean_sr == x, f"SR unbiasedness failed: {mean_sr} != {x}"
    assert var_sr == analytic_var == Fraction(15, 64)

    # Compare independent sum SR(x;R1) + SR(x;R2) vs CSE `let y = SR(x;R1); y + y`
    indep_sums = [y1 + y2 for y1 in outcomes for y2 in outcomes]
    cse_sums = [y + y for y in outcomes]
    mean_indep = sum(indep_sums) / len(indep_sums)
    mean_cse = sum(cse_sums) / len(cse_sums)
    var_indep = sum((z - mean_indep) ** 2 for z in indep_sums) / len(indep_sums)
    var_cse = sum((z - mean_cse) ** 2 for z in cse_sums) / len(cse_sums)
    assert mean_indep == mean_cse == 2 * x
    assert var_indep == 2 * analytic_var == Fraction(15, 32)
    assert var_cse == 4 * analytic_var == Fraction(15, 16)
    assert var_cse == 2 * var_indep  # Exact 2x variance inflation!
    assert Fraction(3) in indep_sums and Fraction(3) not in cse_sums  # Support corruption!

    # Compare nonlinear product SR(x;R1)*SR(x;R2) vs CSE `let y = SR(x;R1); y * y` -> BIAS!
    mean_prod_indep = sum(y1 * y2 for y1 in outcomes for y2 in outcomes) / (n_states * n_states)
    mean_prod_cse = sum(y * y for y in outcomes) / n_states
    assert mean_prod_indep == x * x  # Unbiased!
    assert mean_prod_cse == x * x + analytic_var  # Strictly biased by +Var(SR(x)) = +15/64!

    # 3d. RN Stagnation vs SR Convergence in FP8 E4M3FN (deterministic seeded PRNG)
    # Add delta = 2^-10 ten thousand times to w0 = 1.0 (ulp(1.0) in E4M3FN is 0.125 = 2^-3)
    # Sorted E4M3FN non-negative grid (0 .. 448) for O(log N) bisect lookup
    e4m3_grid = sorted({decode_ocp_e4m3fn(b).val for b in range(127)})
    e4m3_grid_f = [float(v) for v in e4m3_grid]

    w_rn = Fraction(1)
    delta = Fraction(1, 1024)
    steps = 10000
    # Verify single step stagnates (exact RTNE) and thus by induction all 10000 steps stagnate
    w_rn_one_step = decode_ocp_e4m3fn(encode_ocp_e4m3fn(ExtReal.finite(w_rn + delta), "SAT")).val
    assert w_rn_one_step == Fraction(1), "Expected RN stagnation on w0 + 2^-10!"
    w_rn = w_rn_one_step

    rng = random.Random(20261119)
    w_sr = Fraction(1)
    for _ in range(steps):
        target = w_sr + delta
        idx = bisect.bisect_right(e4m3_grid_f, float(target)) - 1
        lo = e4m3_grid[idx]
        if target == lo:
            w_sr = lo
        else:
            hi = e4m3_grid[idx + 1]
            r16 = rng.randrange(1 << 16)
            w_sr = p3109_stochastic_a(target, lo, hi, 16, r16)
    exact_final = Fraction(1) + steps * delta  # 10.765625
    assert abs(w_sr - exact_final) < Fraction(1, 2), f"SR drifted unexpectedly: {float(w_sr)} vs {float(exact_final)}"

    # 3e. DSP Q1.15 saturation corner cases
    assert q15_mul_wrap(-32768, -32768) == -32768  # Classic -1.0 * -1.0 = -1.0 wrap fault
    assert q15_mul_sat(-32768, -32768) == 32767    # ARM SQDMULH saturates to +0.99996948
    lhs_sat = q15_add_sat(q15_add_sat(20000, 20000), -10000)
    rhs_sat = q15_add_sat(20000, q15_add_sat(20000, -10000))
    assert lhs_sat == 22767 and rhs_sat == 30000 and lhs_sat != rhs_sat  # Non-associativity

    print(f"  [OK] Quire16 (256-bit): all 24 permutations yield exact {exact_dot} ({float(exact_dot)}); "
          f"IEEE binary16 produced {sorted(fp16_results)}")
    print(f"  [OK] SR Mode 1 (exhaustive N=4): E[SR(11/8)]={mean_sr}, Var={var_sr}; "
          f"CSE Var={var_cse} (2x indep Var={var_indep}); CSE E[y*y]-x^2=+{mean_prod_cse - x*x}")
    print(f"  [OK] E4M3FN 10000x(+2^-10) from 1.0 (exact={float(exact_final):.6f}): "
          f"RN stagnated at {float(w_rn):.6f}; SR converged to {float(w_sr):.6f}")
    print(f"  [OK] DSP Q1.15: wrap(-1*-1)={q15_mul_wrap(-32768,-32768)}, sat(-1*-1)={q15_mul_sat(-32768,-32768)}; "
          f"sat_add non-associative ({lhs_sat} != {rhs_sat})")


# =============================================================================
# PART 4: P4_16 / Petr4 Header Validity, Copy-In/Copy-Out & Domino SALU SCCs
# =============================================================================

@dataclass
class P4Header:
    """Petr4-style symbolic header with validity bit and optional (unspecified=None) fields."""
    valid: Optional[bool]
    fields: Dict[str, Optional[int]]


@dataclass
class P4HeaderUnion:
    """P4_16 header_union enforcing at most one valid member + invalid-write sibling havoc."""
    members: Dict[str, P4Header]

    def write_field(self, member_name: str, field_name: str, val: int) -> None:
        """P4_16 Sec 8.16 & Petr4 Semantics.v L889-L913 havoc_header rule."""
        target = self.members[member_name]
        if target.valid is True:
            target.fields[field_name] = val
        else:
            # Writing to a field of an invalid union member may corrupt ALL fields of
            # any currently valid sibling without changing any member's validity bit!
            for m in self.members.values():
                for k in list(m.fields.keys()):
                    m.fields[k] = None


def verify_p4_copy_in_copy_out() -> Tuple[int, int]:
    """Compare P4_16 copy-in/copy-out (Sec 6.7 L1550-1592) vs call-by-reference on f(a, g(a)).

    extern void f(inout bit<8> x, in bit<8> y) { x = x + y; }
    extern bit<8> g(inout bit<8> z) { z = z + 10; return z; }
    Starting from a = 5:
      - P4_16 copy-in/copy-out: tmp1=5, tmp2=g(a)=15 (a becomes 15), f(tmp1,tmp2) => tmp1=20, a=tmp1=20
      - Call-by-reference:      g(a) mutates a to 15 first, then f(&a, 15) => a = 15 + 15 = 30!
    """
    # P4_16 copy-in/copy-out
    a_cico = 5
    tmp1 = a_cico          # Step 1 & 4: evaluate left-to-right, snapshot first arg
    a_cico = a_cico + 10   # Step 1: evaluate g(a) (mutates a)
    tmp2 = a_cico
    tmp1 = tmp1 + tmp2     # Step 5: execute f(tmp1, tmp2) on non-aliased temporaries
    a_cico = tmp1          # Step 6: copy out left-to-right

    # Naive call-by-reference
    a_ref = 5
    a_ref = a_ref + 10     # g(a) mutates shared reference
    y_ref = a_ref
    a_ref = a_ref + y_ref  # f(&a, y) reads mutated a!
    return a_cico, a_ref


def check_header_validity_typestate(
    parser_paths: Dict[str, Set[str]],
    accesses: Sequence[Tuple[str, Optional[str], str]],
) -> List[str]:
    """Static path-sensitive typestate check over parser exit states.

    parser_paths: path_name -> set of valid headers guaranteed upon parser accept.
    accesses: list of (header_name, guard_header_or_None, field_name).
    Returns list of unguarded invalid-header dereference diagnostics.
    """
    violations: List[str] = []
    for path_name, valid_set in sorted(parser_paths.items()):
        for hdr, guard, fld in accesses:
            if guard == hdr:
                continue  # Guarded by `if (hdr.isValid())`
            if hdr not in valid_set:
                violations.append(f"path={path_name}: unguarded read/write {hdr}.{fld} (invalid header)")
    return violations


@dataclass(frozen=True)
class Stmt:
    """Single SSA-flattened Domino packet transaction statement."""
    sid: int
    lhs: str
    rhs_vars: Tuple[str, ...]
    op: str  # "read_state", "write_state", "add", "mux", "mul", "cmp"
    state_var: Optional[str] = None  # Non-None iff statement accesses persistent switch register


def tarjan_scc(nodes: Sequence[int], edges: Dict[int, Set[int]]) -> List[List[int]]:
    """Deterministic Tarjan strongly connected components algorithm."""
    index = 0
    indices: Dict[int, int] = {}
    lowlink: Dict[int, int] = {}
    stack: List[int] = []
    on_stack: Set[int] = set()
    sccs: List[List[int]] = []

    def strongconnect(v: int) -> None:
        nonlocal index
        indices[v] = lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in sorted(edges.get(v, ())):
            if w not in indices:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            comp: List[int] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            sccs.append(sorted(comp))

    for n in sorted(nodes):
        if n not in indices:
            strongconnect(n)
    return sccs


def domino_salu_schedule(
    stmts: Sequence[Stmt],
    atom_max_state_vars: int = 1,
    allow_mul_in_salu: bool = False,
    max_stages: int = 12,
) -> Tuple[bool, str, Dict[int, List[int]]]:
    """Domino partitioning.cc (L19-L193) SCC condensation + critical-path stage scheduler.

    - Adds bidirectional edges between the read and write of each persistent state variable
      (forcing every state-variable feedback loop into one indivisible single-cycle SCC).
    - Adds forward RAW edges between packet-variable producers and consumers.
    - Rejects any SCC whose state-variable count exceeds `atom_max_state_vars` (e.g., 1 for
      RAW/PRAW, 2 for Pair) or contains unsupported single-cycle ops (e.g., `mul`), or if
      the condensed DAG depth exceeds `max_stages`.
    """
    by_id = {s.sid: s for s in stmts}
    edges: Dict[int, Set[int]] = defaultdict(set)
    producer: Dict[str, int] = {}
    state_read: Dict[str, int] = {}
    state_write: Dict[str, int] = {}

    for s in stmts:
        # Packet RAW edges
        for rv in s.rhs_vars:
            if rv in producer:
                edges[producer[rv]].add(s.sid)
        # Bidirectional state-variable feedback cycle (Domino handle_state_vars L42-43)
        if s.op == "read_state":
            assert s.state_var is not None
            state_read[s.state_var] = s.sid
            producer[s.lhs] = s.sid
        elif s.op == "write_state":
            assert s.state_var is not None
            state_write[s.state_var] = s.sid
            edges[state_read[s.state_var]].add(s.sid)
            edges[s.sid].add(state_read[s.state_var])
        else:
            producer[s.lhs] = s.sid

    sccs = tarjan_scc([s.sid for s in stmts], edges)
    node_to_scc: Dict[int, int] = {}
    for cid, comp in enumerate(sccs):
        for sid in comp:
            node_to_scc[sid] = cid

    # Validate each SCC against single-cycle SALU atom capability
    for cid, comp in enumerate(sccs):
        svars = {by_id[sid].state_var for sid in comp if by_id[sid].state_var is not None}
        ops = {by_id[sid].op for sid in comp}
        if len(svars) > atom_max_state_vars:
            return (
                False,
                f"REJECT: SCC {comp} couples {len(svars)} state variables {sorted(svars)} "
                f"(exceeds single-cycle SALU limit {atom_max_state_vars})",
                {},
            )
        if svars and ("mul" in ops) and not allow_mul_in_salu:
            return (
                False,
                f"REJECT: SCC {comp} requires non-single-cycle 'mul' inside stateful loop {sorted(svars)}",
                {},
            )

    # Critical-path scheduling on condensed DAG
    dag_preds: Dict[int, Set[int]] = {cid: set() for cid in range(len(sccs))}
    for u, nbrs in edges.items():
        cu = node_to_scc[u]
        for v in nbrs:
            cv = node_to_scc[v]
            if cu != cv:
                dag_preds[cv].add(cu)

    stage_of: Dict[int, int] = {}
    while len(stage_of) < len(sccs):
        progressed = False
        for cid in range(len(sccs)):
            if cid in stage_of:
                continue
            if all(p in stage_of for p in dag_preds[cid]):
                stage_of[cid] = 0 if not dag_preds[cid] else 1 + max(stage_of[p] for p in dag_preds[cid])
                progressed = True
        assert progressed, "Condensed graph must be a DAG!"

    total_stages = (max(stage_of.values()) + 1) if stage_of else 0
    if total_stages > max_stages:
        return False, f"REJECT: requires {total_stages} stages > hardware limit {max_stages}", {}

    schedule: Dict[int, List[int]] = defaultdict(list)
    for cid, stg in sorted(stage_of.items(), key=lambda kv: (kv[1], kv[0])):
        schedule[stg].extend(sccs[cid])
    return True, f"ACCEPT: scheduled in {total_stages} stage(s)", dict(schedule)


def verify_part4_p4_and_salu() -> None:
    print("=== PART 4: P4_16 Semantics & Domino/Chipmunk Single-Cycle SALU Verification ===")

    # 4a. P4_16 header_union invalid-member write havoc (Petr4 Semantics.v L889)
    union = P4HeaderUnion(
        members={
            "ipv4": P4Header(valid=True, fields={"ttl": 64, "dst": 0x0A000001}),
            "ipv6": P4Header(valid=False, fields={"hop_limit": None}),
        }
    )
    union.write_field("ipv6", "hop_limit", 128)  # Write to INVALID union member!
    assert union.members["ipv4"].valid is True
    assert union.members["ipv6"].valid is False
    assert union.members["ipv4"].fields["ttl"] is None  # Valid sibling field havoced!
    assert union.members["ipv4"].fields["dst"] is None

    # 4b. P4_16 copy-in/copy-out aliasing vs call-by-reference
    a_cico, a_ref = verify_p4_copy_in_copy_out()
    assert a_cico == 20 and a_ref == 30

    # 4c. Header-validity typestate check across parser paths
    parser_paths = {
        "ipv4_tcp": {"eth", "ipv4", "tcp"},
        "arp_only": {"eth", "arp"},
    }
    unguarded_errs = check_header_validity_typestate(parser_paths, [("ipv4", None, "ttl")])
    guarded_errs = check_header_validity_typestate(parser_paths, [("ipv4", "ipv4", "ttl")])
    assert len(unguarded_errs) == 1 and "arp_only" in unguarded_errs[0]
    assert guarded_errs == []

    # 4d. Domino/Chipmunk SALU scheduling:
    # Case 1 (Schedulable): Flowlet-like single-state update + downstream stateless stage
    flowlet_prog = [
        Stmt(1, "t_old", (), "read_state", state_var="last_time"),
        Stmt(2, "gap", ("pkt_ts", "t_old"), "add"),
        Stmt(3, "is_new", ("gap",), "cmp"),
        Stmt(4, "last_time", ("pkt_ts",), "write_state", state_var="last_time"),
        Stmt(5, "id_old", (), "read_state", state_var="flowlet_id"),
        Stmt(6, "id_nxt", ("id_old", "is_new"), "mux"),
        Stmt(7, "flowlet_id", ("id_nxt",), "write_state", state_var="flowlet_id"),
    ]
    ok1, msg1, sched1 = domino_salu_schedule(flowlet_prog, atom_max_state_vars=1)
    # Stage 0: SCC {1,4} (last_time read+write); Stage 1: {2} (gap); Stage 2: {3} (cmp);
    # Stage 3: SCC {5,6,7} (flowlet_id PredRAW read-mux-write atom).
    assert ok1 and len(sched1) == 4 and sched1[0] == [1, 4] and sched1[3] == [5, 6, 7], (
        f"Unexpected flowlet schedule: {ok1}, {msg1}, {sched1}"
    )

    # Case 2 (Unschedulable on 1-state RAW/PRAW atom, schedulable ONLY on 2-state Pair atom):
    # Cross-dependent state pair: A_next = A + B; B_next = B + A (mutual cycle!)
    coupled_prog = [
        Stmt(1, "a_old", (), "read_state", state_var="A"),
        Stmt(2, "b_old", (), "read_state", state_var="B"),
        Stmt(3, "a_new", ("a_old", "b_old"), "add"),
        Stmt(4, "b_new", ("a_old", "b_old"), "add"),
        Stmt(5, "A", ("a_new",), "write_state", state_var="A"),
        Stmt(6, "B", ("b_new",), "write_state", state_var="B"),
    ]
    ok_raw, msg_raw, _ = domino_salu_schedule(coupled_prog, atom_max_state_vars=1)
    ok_pair, msg_pair, sched_pair = domino_salu_schedule(coupled_prog, atom_max_state_vars=2)
    assert not ok_raw and "couples 2 state variables" in msg_raw
    assert ok_pair and len(sched_pair) == 1

    # Case 3 (Unschedulable even on Pair atom): stateful multiply inside feedback cycle
    mul_loop_prog = [
        Stmt(1, "s_old", (), "read_state", state_var="ewma"),
        Stmt(2, "s_mul", ("s_old", "pkt_len"), "mul"),
        Stmt(3, "ewma", ("s_mul",), "write_state", state_var="ewma"),
    ]
    ok_mul, msg_mul, _ = domino_salu_schedule(mul_loop_prog, atom_max_state_vars=2, allow_mul_in_salu=False)
    assert not ok_mul and "mul" in msg_mul

    print(f"  [OK] P4_16 header_union invalid write: ipv4.valid={union.members['ipv4'].valid}, "
          f"ipv4.ttl={union.members['ipv4'].fields['ttl']} (havoced)")
    print(f"  [OK] P4_16 copy-in/copy-out f(a, g(a)): a={a_cico} (vs call-by-ref a={a_ref})")
    print(f"  [OK] Header typestate: caught unguarded access ({unguarded_errs[0]}); guarded=0 errors")
    print(f"  [OK] Domino SALU Flowlet (1-var RAW): {msg1} -> stages={sched1}")
    print(f"  [OK] Domino SALU Coupled (A<->B): RAW->{msg_raw}; Pair->{msg_pair}")
    print(f"  [OK] Domino SALU Stateful mul loop: {msg_mul}")


def main() -> int:
    verify_part1_fp8_and_p3109()
    verify_part2_ocp_mxfp4()
    verify_part3_quire_sr_and_dsp()
    verify_part4_p4_and_salu()
    print("ALL_PROBES_PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
