#!/usr/bin/env python3
"""Executable model of CHERI capability algebra, bounds compression, and tagged memory.

Self-contained (Python 3.10+, standard library only, deterministic, no I/O besides
stdout).  Exit status 0 means every check passed; any failed check raises.

What is modelled, and from which public artifact each piece was transcribed:

* ``CCFormat`` -- CHERI Concentrate bounds compression (``setCapBounds``,
  ``getCapBoundsBits``, ``fastRepCheck``, ``getRepresentableAlignmentMask``,
  ``getRepresentableLength``) transcribed from ``src/cheri_cap_common.sail`` of
  CTSRD-CHERI/sail-cheri-riscv at cf36cfd4fca0bd10a5906651bf48b9674ccd0a2b.  The
  128-bit format uses a 64-bit address and mantissa width 14; the 64-bit format
  uses a 32-bit address and mantissa width 8 (``src/cheri_prelude_{128,64}.sail``).
* ``CheriotFormat`` -- the CHERIoT 64-bit encoding (9-bit B and T, 4-bit E,
  no internal exponent) transcribed from ``src/cheri_cap_common.sail`` of
  CHERIoT-Platform/cheriot-sail at 518813ec3e595f79930d9129eaded2521831cbe2.
* ``Cpu`` -- guarded-manipulation instructions (CSetBounds, CSetBoundsExact,
  CAndPerm, CIncOffset, CSetAddr, CSeal, CUnseal, CSealEntry, CBuildCap)
  transcribed from ``src/cheri_insts.sail`` of sail-cheri-riscv at the same
  revision.  Every failure path clears the tag instead of trapping.
* ``TaggedMemory`` -- one tag bit per capability-sized, capability-aligned
  granule; any data store clears the tag of each granule it touches
  (``__WriteRAM_Meta`` in ``src/cheri_mem_metadata.sail``).
* ``memcpy_capaware`` -- the word-copy strategy of ``lib/libc/string/bcopy.c``
  of CTSRD-CHERI/cheribsd at 88f39900c32928d807dba245fba138808c666f34, where the
  copy word is a capability when source and destination are mutually aligned.
* ``epoch_clears`` -- ``cheri_revoke_epoch_clears`` from ``sys/cheri/revoke.h``
  of cheribsd at the same revision.
* ``sweep_model`` -- a deliberately tiny abstract model of sweeping revocation
  written for this probe.  It is not a transcription of any kernel; it exists
  to discriminate three designs (no barrier, stop-the-world re-scan, load
  barrier) on an exhaustively explored state space.

``GOLDEN_SETBOUNDS_128`` rows are copied from
``test/contrib/setbounds_inputs_128.cpp`` of CTSRD-CHERI/cheri-compressed-cap at
5b3dfd25ae49a62594477ba25be1371d29774cf9, whose expected values were generated
by the upstream Sail model; ``REGRESSIONS_128`` are from
``test/setbounds_test_128.cpp`` of the same revision.
"""

from __future__ import annotations

import itertools
import random
import sys
from dataclasses import dataclass, replace

CHECKS: list[tuple[str, int]] = []


def record(name: str, count: int) -> None:
    CHECKS.append((name, count))
    print(f"[ok] {name}: {count} cases")


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def mask(n: int) -> int:
    return (1 << n) - 1


# --------------------------------------------------------------------------
# CHERI Concentrate (sail-cheri-riscv)
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Bounds:
    """Bounds fields of a partially decompressed capability (Sail `Capability`)."""

    E: int
    B: int
    T: int
    ie: bool


class CCFormat:
    """CHERI Concentrate with a 3-bit-per-field internal exponent."""

    TAKE = 3  # internal_E_take_bits

    def __init__(self, name: str, addr_width: int, mantissa_width: int) -> None:
        self.name = name
        self.AW = addr_width
        self.MW = mantissa_width
        self.LW = addr_width + 1  # cap_len_width
        self.max_E = self.LW - self.MW + 1  # cap_max_E
        self.cap_bytes = 2 * addr_width // 8
        self.reset = Bounds(E=self.max_E, B=0, T=1 << (self.MW - 2), ie=True)

    # -- setCapBounds ------------------------------------------------------
    def set_bounds(self, base: int, top: int) -> tuple[bool, Bounds]:
        AW, MW, LW = self.AW, self.MW, self.LW
        length = (top - base) & mask(LW)
        # e = cap_max_E - count_leading_zeros(length[AW .. MW-1])
        e = (length >> (MW - 1)).bit_length()
        ie = (e != 0) or bool((length >> (MW - 2)) & 1)
        Bbits = base & mask(MW)
        Tbits = top & mask(MW)
        lost_base = lost_top = False
        inc_e = False
        if ie:
            w = MW - 3
            B_ie = (base >> (e + 3)) & mask(w)
            T_ie = (top >> (e + 3)) & mask(w)
            mask_lo = mask(e + 3)
            lost_base = (base & mask_lo) != 0
            lost_top = (top & mask_lo) != 0
            if lost_top:
                T_ie = (T_ie + 1) & mask(w)
            len_ie = (T_ie - B_ie) & mask(w)
            if (len_ie >> (MW - 4)) & 1:
                inc_e = True
                lost_base = lost_base or bool(B_ie & 1)
                lost_top = lost_top or bool(T_ie & 1)
                B_ie = (base >> (e + 4)) & mask(w)
                T_ie = ((top >> (e + 4)) + (1 if lost_top else 0)) & mask(w)
            Bbits = B_ie << 3
            Tbits = T_ie << 3
        exact = not (lost_base or lost_top)
        return exact, Bounds(E=e + 1 if inc_e else e, B=Bbits, T=Tbits, ie=ie)

    # -- capToEncCap / encCapabilityToCapability (bounds bits only) ---------
    def encode(self, b: Bounds) -> int:
        """Pack to the stored 1 + (MW-2) + MW bounds bits."""
        MW = self.MW
        t = b.T & mask(MW - 2)
        bb = b.B
        if b.ie:
            t = (t & ~mask(3)) | ((b.E >> 3) & mask(3))
            bb = (bb & ~mask(3)) | (b.E & mask(3))
        return (int(b.ie) << (2 * MW - 2)) | (t << MW) | bb

    def decode(self, bits: int) -> Bounds:
        MW = self.MW
        ie = bool((bits >> (2 * MW - 2)) & 1)
        t = (bits >> MW) & mask(MW - 2)
        bb = bits & mask(MW)
        if ie:
            E = ((t & mask(3)) << 3) | (bb & mask(3))
            len_msbs = 1
            t &= ~mask(3)
            bb &= ~mask(3)
        else:
            E = 0
            len_msbs = 0
        carry = 1 if t < (bb & mask(MW - 2)) else 0
        t_top2 = ((bb >> (MW - 2)) + len_msbs + carry) & 3
        return Bounds(E=E, B=bb, T=(t_top2 << (MW - 2)) | t, ie=ie)

    # -- getCapBoundsBits --------------------------------------------------
    def get_bounds(self, b: Bounds, addr: int) -> tuple[int, int]:
        AW, MW, LW = self.AW, self.MW, self.LW
        E = min(self.max_E, b.E)
        a3 = (addr >> (E + MW - 3)) & 7
        B3 = (b.B >> (MW - 3)) & 7
        T3 = (b.T >> (MW - 3)) & 7
        R3 = (B3 - 1) & 7
        a_hi = 1 if a3 < R3 else 0
        b_hi = 1 if B3 < R3 else 0
        t_hi = 1 if T3 < R3 else 0
        a_top = addr >> (E + MW)
        base = (((a_top + b_hi - a_hi) << (MW + E)) | (b.B << E)) & mask(LW)
        top = (((a_top + t_hi - a_hi) << (MW + E)) | (b.T << E)) & mask(LW)
        base2 = (base >> (AW - 1)) & 1
        top2 = (top >> (AW - 1)) & 3
        if E < self.max_E - 1 and ((top2 - base2) & 3) > 1:
            top ^= 1 << AW
        return base & mask(AW), top

    # -- fastRepCheck ------------------------------------------------------
    def fast_rep_check(self, b: Bounds, addr: int, inc: int) -> bool:
        AW, MW = self.AW, self.MW
        E = b.E
        if E >= self.max_E - 2:
            return True
        inc &= mask(AW)
        signed_inc = inc - (1 << AW) if inc >> (AW - 1) else inc
        i_top = signed_inc >> (E + MW)
        i_mid = (inc >> E) & mask(MW)
        a_mid = (addr >> E) & mask(MW)
        R = (((b.B >> (MW - 3)) - 1) & 7) << (MW - 3)
        diff = (R - a_mid) & mask(MW)
        diff1 = (diff - 1) & mask(MW)
        if i_top == 0:
            return i_mid < diff1
        if i_top == -1:
            return i_mid >= diff and R != a_mid
        return False

    def exact_rep_check(self, b: Bounds, addr: int, new_addr: int) -> bool:
        return self.get_bounds(b, addr) == self.get_bounds(b, new_addr)

    # -- CRAM / CRRL -------------------------------------------------------
    def cram(self, length: int) -> int:
        _, c = self.set_bounds(0, length)
        e = min(c.E, self.max_E)
        e2 = e + self.TAKE if c.ie else 0
        return mask(self.AW) & ~mask(e2)

    def crrl(self, length: int) -> int:
        m = self.cram(length)
        return (length + (~m & mask(self.AW))) & m & mask(self.AW)

    def round(self, base: int, top: int) -> tuple[int, int, bool]:
        """Decoded bounds produced by setCapBounds with address = base."""
        exact, b = self.set_bounds(base, top)
        lo, hi = self.get_bounds(b, base)
        return lo, hi, exact


CC128 = CCFormat("CC-128 (RV64, MW=14)", 64, 14)
CC64 = CCFormat("CC-64 (RV32, MW=8)", 32, 8)
TOY = CCFormat("toy CC (AW=7, MW=6)", 7, 6)


# --------------------------------------------------------------------------
# CHERIoT encoding (cheriot-sail)
# --------------------------------------------------------------------------


class CheriotFormat:
    AW, MW, MAX_E = 32, 9, 24

    def set_bounds(self, base: int, length: int) -> tuple[bool, tuple[int, int, int]]:
        """Returns (exact, (effective exponent, B, T)); the encoded E field stores 15 for 24."""
        top = base + length
        e = max(0, (length >> 9).bit_length())  # 23 - clz(length[31..9])
        e_sat = self.MAX_E if e > 14 else e
        B = (base >> e_sat) & mask(10)
        T = (top >> e_sat) & mask(10)
        lost_top = (top & mask(e_sat)) != 0
        if lost_top:
            T = (T + 1) & mask(10)
        if ((T - B) & mask(10)) > 0x1FF:
            e_sat = e_sat + 1 if e_sat < 14 else self.MAX_E
            B = (base >> e_sat) & mask(10)
            T = (top >> e_sat) & mask(10)
            lost_top = (top & mask(e_sat)) != 0
            if lost_top:
                T = (T + 1) & mask(10)
        lost_base = (base & mask(e_sat)) != 0
        return not (lost_base or lost_top), (e_sat, B & 0x1FF, T & 0x1FF)

    def get_bounds(self, enc: tuple[int, int, int], addr: int) -> tuple[int, int]:
        E, B, T = enc
        a_mid = (addr >> E) & 0x1FF
        a_hi = 1 if a_mid < B else 0
        t_hi = 1 if T < B else 0
        a_top = addr >> (E + 9)
        base = (((a_top - a_hi) << (E + 9)) | (B << E)) & mask(32)
        top = (((a_top + t_hi - a_hi) << (E + 9)) | (T << E)) & mask(33)
        return base, top


CHERIOT = CheriotFormat()


# --------------------------------------------------------------------------
# Capabilities and guarded manipulation (sail-cheri-riscv cheri_insts.sail)
# --------------------------------------------------------------------------

P_GLOBAL, P_EXEC, P_LOAD, P_STORE, P_LOAD_CAP, P_STORE_CAP = 1, 2, 4, 8, 16, 32
P_STORE_LOCAL, P_SEAL, P_CINVOKE, P_UNSEAL, P_ASR, P_SETCID = 64, 128, 256, 512, 1024, 2048
ALL_PERMS = 0xFFF
OTYPE_UNSEALED, OTYPE_SENTRY = -1, -2


@dataclass(frozen=True)
class Cap:
    tag: bool
    perms: int
    otype: int
    bounds: Bounds
    addr: int

    @property
    def sealed(self) -> bool:
        return self.otype != OTYPE_UNSEALED


class Cpu:
    def __init__(self, fmt: CCFormat, otype_width: int) -> None:
        self.f = fmt
        self.max_otype = mask(otype_width) - 4  # cap_max_otype (4 reserved otypes)
        self.root = Cap(True, ALL_PERMS, OTYPE_UNSEALED, fmt.reset, 0)
        self.null = Cap(False, 0, OTYPE_UNSEALED, fmt.reset, 0)

    def bounds(self, c: Cap) -> tuple[int, int]:
        return self.f.get_bounds(c.bounds, c.addr)

    def in_bounds(self, c: Cap, addr: int, size: int) -> bool:
        base, top = self.bounds(c)
        return addr >= base and addr + size <= top

    @staticmethod
    def _untag_if(c: Cap, cond: bool) -> Cap:
        return replace(c, tag=c.tag and not cond)

    def csetbounds(self, c: Cap, length: int, exact_required: bool = False) -> Cap:
        f = self.f
        length &= mask(f.AW)
        ok = self.in_bounds(c, c.addr, length)
        exact, nb = f.set_bounds(c.addr, c.addr + length)
        out = replace(self._untag_if(c, c.sealed), bounds=nb)
        return self._untag_if(out, not ok or (exact_required and not exact))

    def candperm(self, c: Cap, m: int) -> Cap:
        return replace(self._untag_if(c, c.sealed), perms=c.perms & m & ALL_PERMS)

    def cincoffset(self, c: Cap, delta: int) -> Cap:
        f = self.f
        new_addr = (c.addr + delta) & mask(f.AW)
        ok = f.fast_rep_check(c.bounds, c.addr, delta)
        return self._untag_if(replace(self._untag_if(c, c.sealed), addr=new_addr), not ok)

    def csetaddr(self, c: Cap, addr: int) -> Cap:
        f = self.f
        addr &= mask(f.AW)
        ok = f.exact_rep_check(c.bounds, c.addr, addr)
        return self._untag_if(replace(self._untag_if(c, c.sealed), addr=addr), not ok)

    def cseal(self, c: Cap, auth: Cap) -> Cap:
        base, top = self.bounds(auth)
        permitted = (
            auth.tag
            and not auth.sealed
            and bool(auth.perms & P_SEAL)
            and base <= auth.addr < top
            and auth.addr <= self.max_otype
        )
        out = replace(self._untag_if(c, c.sealed), otype=auth.addr)
        return self._untag_if(out, not permitted)

    def cunseal(self, c: Cap, auth: Cap) -> Cap:
        base, top = self.bounds(auth)
        permitted = (
            auth.tag
            and c.sealed
            and not auth.sealed
            and 0 <= c.otype <= self.max_otype
            and auth.addr == c.otype
            and bool(auth.perms & P_UNSEAL)
            and base <= auth.addr < top
        )
        perms = c.perms if auth.perms & P_GLOBAL else c.perms & ~P_GLOBAL
        return self._untag_if(replace(c, otype=OTYPE_UNSEALED, perms=perms), not permitted)

    def csealentry(self, c: Cap) -> Cap:
        return replace(self._untag_if(c, c.sealed), otype=OTYPE_SENTRY)

    def cbuildcap(self, auth: Cap, bits: Cap) -> Cap:
        """Re-derive a tagged capability from untagged bits under an authority."""
        f = self.f
        want_sentry = bits.otype == OTYPE_SENTRY
        req = replace(bits, tag=True, otype=OTYPE_SENTRY if want_sentry else OTYPE_UNSEALED)
        a_base, a_top = self.bounds(auth)
        r_base, r_top = self.bounds(req)
        subset = (
            r_base >= a_base
            and r_top <= a_top
            and r_base <= r_top
            and (req.perms & auth.perms) == req.perms
        )
        _, nb = f.set_bounds(r_base, r_top & mask(f.LW))
        cd = replace(self._untag_if(auth, auth.sealed), bounds=nb, addr=req.addr, perms=req.perms)
        if want_sentry:
            cd = replace(cd, otype=OTYPE_SENTRY)
        derivable = cd == req
        return cd if (subset and derivable) else replace(req, tag=False)


def dominated(cpu: Cpu, child: Cap, parent: Cap) -> bool:
    """`child` conveys no more memory authority than `parent` (bounds and perms)."""
    if not child.tag:
        return True
    if not parent.tag:
        return False
    cb, ct = cpu.bounds(child)
    pb, pt = cpu.bounds(parent)
    return pb <= cb and ct <= pt and (child.perms & ~parent.perms) == 0


# --------------------------------------------------------------------------
# Tagged memory and memcpy strategies
# --------------------------------------------------------------------------


class TaggedMemory:
    def __init__(self, size: int, cap_bytes: int) -> None:
        require(size % cap_bytes == 0, "memory size must be a granule multiple")
        self.cap_bytes = cap_bytes
        self.data = bytearray(size)
        self.tags = [False] * (size // cap_bytes)
        self.tag_sets = 0

    def store_bytes(self, addr: int, payload: bytes) -> None:
        self.data[addr : addr + len(payload)] = payload
        if payload:
            first = addr // self.cap_bytes
            last = (addr + len(payload) - 1) // self.cap_bytes
            for g in range(first, last + 1):
                self.tags[g] = False

    def load_bytes(self, addr: int, n: int) -> bytes:
        return bytes(self.data[addr : addr + n])

    def store_cap(self, addr: int, payload: bytes, tag: bool) -> None:
        require(addr % self.cap_bytes == 0, "unaligned capability store traps")
        require(len(payload) == self.cap_bytes, "capability width")
        self.data[addr : addr + self.cap_bytes] = payload
        self.tags[addr // self.cap_bytes] = tag
        self.tag_sets += int(tag)

    def load_cap(self, addr: int) -> tuple[bytes, bool]:
        require(addr % self.cap_bytes == 0, "unaligned capability load traps")
        return bytes(self.data[addr : addr + self.cap_bytes]), self.tags[addr // self.cap_bytes]


def memcpy_bytewise(mem: TaggedMemory, dst: int, src: int, n: int) -> None:
    for i in range(n):
        mem.store_bytes(dst + i, mem.load_bytes(src + i, 1))


def memcpy_capaware(mem: TaggedMemory, dst: int, src: int, n: int) -> None:
    """Forward copy of cheribsd bcopy.c with `word` = capability."""
    w = mem.cap_bytes
    wmask = w - 1
    if n == 0 or dst == src:
        return
    if (src | dst) & wmask:
        t = n if ((src ^ dst) & wmask or n < w) else w - (src & wmask)
        n -= t
        for _ in range(t):
            mem.store_bytes(dst, mem.load_bytes(src, 1))
            src, dst = src + 1, dst + 1
    for _ in range(n // w):
        payload, tag = mem.load_cap(src)
        mem.store_cap(dst, payload, tag)
        src, dst = src + w, dst + w
    for _ in range(n & wmask):
        mem.store_bytes(dst, mem.load_bytes(src, 1))
        src, dst = src + 1, dst + 1


# --------------------------------------------------------------------------
# Golden vectors
# --------------------------------------------------------------------------

# (base1, top1, base2, top2, ccBase1, ccTop1, ccBase2, ccTop2)
GOLDEN_SETBOUNDS_128 = [
    (0x000000000000004B, 0x0000000007CF18F9B, 0x000000000006D6A8, 0x0000000000086D6A0,
     0x0000000000000000, 0x0000000007D000000, 0x000000000006C000, 0x00000000000870000),
    (0x0000000000000007, 0x000000712B609C5B0, 0x00000000032DC20F, 0x000000008032D1C77,
     0x0000000000000000, 0x00000071400000000, 0x0000000000000000, 0x00000000804000000),
    (0x00000000000049FE, 0x00B87DF010D7254BB, 0x000000000900A7CA, 0x000000800085F0270,
     0x0000000000000000, 0x00B88000000000000, 0x0000000000000000, 0x00000080400000000),
    (0x000001991A6FD045, 0x00080018A6ACD2D6C, 0x0000BEDAF8F73C0F, 0x0004D37033A19B295,
     0x0000000000000000, 0x00080400000000000, 0x0000A00000000000, 0x0004D400000000000),
    (0x0000000000003D0E, 0x0000000902DCEEE9C, 0x0000000000032796, 0x00000003FFFF8EDC8,
     0x0000000000000000, 0x00000009040000000, 0x0000000000000000, 0x00000004000000000),
    (0x000000000006CDF7, 0x01FFFFF5B88378EC7, 0x0000000000086940, 0x00000000000214459,
     0x0000000000000000, 0x02000000000000000, 0x0000000000086800, 0x00000000000214800),
]

# (address, requested length, expected base, expected length, expected exact)
REGRESSIONS_128 = [
    (0xFFFFFFFFFF000000, 0x0000000000FFFFFF, 0xFFFFFFFFFF000000, 0x1000000, False),
    (0x0000000000000007, 0x0000000010000000, 0x0000000000000000, 0x10080000, False),
    (0x0000000160600000, 0x0000000000300000, 0x0000000160600000, 0x300000, True),
]


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------


def check_golden() -> None:
    n = 0
    for b1, t1, b2, t2, cb1, ct1, cb2, ct2 in GOLDEN_SETBOUNDS_128:
        lo, hi, _ = CC128.round(b1, t1)
        require((lo, hi) == (cb1, ct1), f"golden row outer {b1:#x},{t1:#x} -> {lo:#x},{hi:#x}")
        lo, hi, _ = CC128.round(b2, t2)
        require((lo, hi) == (cb2, ct2), f"golden row inner {b2:#x},{t2:#x} -> {lo:#x},{hi:#x}")
        n += 2
    for addr, length, ebase, elen, eexact in REGRESSIONS_128:
        lo, hi, exact = CC128.round(addr, addr + length)
        require((lo, hi - lo, exact) == (ebase, elen, eexact), f"regression {addr:#x}+{length:#x}")
        n += 1
    record("CC-128 set-bounds matches upstream Sail-generated vectors", n)


def check_alignment_table() -> None:
    """Closed-form alignment rule: exact iff base and length are 2^(E+3)-aligned."""
    rows = []
    for fmt in (CC128, CC64):
        MW = fmt.MW
        thresh = 1 << (MW - 2)
        # Byte precision strictly below 2^(MW-2); 8-byte granule begins there.
        for length in (1, thresh - 1):
            for base in (1, 0x1235, (1 << (fmt.AW - 1)) + 3):
                lo, hi, exact = fmt.round(base, base + length)
                require(exact and (lo, hi) == (base, base + length), f"{fmt.name} small exact")
        lo, hi, exact = fmt.round(1, 1 + thresh)
        require(not exact and lo == 0 and hi == thresh + 8, f"{fmt.name} first rounding step")
        require(fmt.cram(thresh - 1) == mask(fmt.AW), f"{fmt.name} CRAM below threshold")
        require(fmt.cram(thresh) == mask(fmt.AW) & ~7, f"{fmt.name} CRAM at threshold")
        for k in range(MW - 2, fmt.AW - 1):
            length = 1 << k
            e = k - (MW - 2)
            align = 1 << (e + 3)
            require(fmt.cram(length) == mask(fmt.AW) & ~(align - 1), f"{fmt.name} CRAM 2^{k}")
            require(fmt.crrl(length) == length, f"{fmt.name} CRRL power of two")
            require(fmt.crrl(length + 1) == length + align, f"{fmt.name} CRRL round-up 2^{k}+1")
            rows.append((fmt.name, k, align))
    record("alignment rule: byte-exact below 2^(MW-2), then 2^(E+3)", len(rows))
    print("     CC-128: byte-exact for length < 4096; 8-byte granule from 4 KiB; "
          f"1 MiB object needs {1 << ((20 - 12) + 3)}-byte alignment; "
          f"1 GiB object needs {1 << ((30 - 12) + 3)}-byte alignment")
    print("     CC-64 : byte-exact for length < 64; "
          f"1 MiB object needs {1 << ((20 - 6) + 3)}-byte alignment")


def check_toy_exhaustive() -> None:
    f = TOY
    N = 1 << f.AW
    table: dict[tuple[int, int], tuple[int, int, bool]] = {}
    for base in range(N):
        for top in range(base, N + 1):
            lo, hi, exact = f.round(base, top)
            require(lo <= base and top <= hi, f"toy containment {base},{top} -> {lo},{hi}")
            require(exact == ((lo, hi) == (base, top)), f"toy exact flag {base},{top}")
            table[(base, top)] = (lo, hi, exact)
    record("toy CC exhaustive: rounded bounds contain request; exact flag is precise", len(table))

    n = 0
    for (base, top), (lo, hi, _) in table.items():
        if hi <= N:
            lo2, hi2, exact2 = table[(lo, hi)]
            require(exact2 and (lo2, hi2) == (lo, hi), f"toy idempotence {base},{top}")
            n += 1
    record("toy CC exhaustive: rounding is idempotent (results are fixed points)", n)

    n = 0
    parents = [(b, t) for (b, t), (_, _, exact) in table.items() if exact]
    for pb, pt in parents:
        for a in range(pb, min(pt, N - 1) + 1):
            for t in range(a, pt + 1):
                lo, hi, _ = table[(a, t)]
                require(pb <= lo and hi <= pt, f"toy nesting parent {pb},{pt} child {a},{t} -> {lo},{hi}")
                n += 1
    record("toy CC exhaustive: CSetBounds inside a representable parent never escapes it", n)

    n = 0
    for pb, pt in parents:
        _, b = f.set_bounds(pb, pt)
        require(f.decode(f.encode(b)) == b, f"toy encode/decode {pb},{pt}")
        for a in range(pb, pt + 1 if pt < N else pt):
            require(f.exact_rep_check(b, pb, a), f"toy in-bounds address unrepresentable {pb},{pt}@{a}")
            n += 1
    record("toy CC exhaustive: every address in [base, top] keeps the bounds (one-past-the-end is safe)", n)

    n = 0
    for length in range(N + 1):
        m, L = f.cram(length), f.crrl(length)
        if L < length:  # wrapped at the top of the toy address space
            continue
        for base in range(0, N, 1):
            if base & ~m & mask(f.AW) or base + L > N:
                continue
            lo, hi, exact = table[(base, base + L)]
            require(exact, f"toy CRRL/CRAM not exact len={length} base={base}")
            n += 1
    record("toy CC exhaustive: CRAM-aligned base + CRRL length is always exact", n)


def check_representability() -> None:
    """Representable region: guaranteed slack and soundness of the fast check."""
    rng = random.Random(0x2E9)
    for fmt, samples in ((CC128, 20000), (CC64, 20000), (CCFormat("toy CC (AW=9, MW=6)", 9, 6), 20000)):
        AW, MW = fmt.AW, fmt.MW
        n = fast_true = exact_true = slack = 0
        while n < samples:
            base = rng.getrandbits(AW)
            length = min(rng.getrandbits(rng.randrange(1, AW + 1)), (1 << AW) - base)
            _, b = fmt.set_bounds(base, base + length)
            lo, hi = fmt.get_bounds(b, base)
            if hi > 1 << AW:
                continue
            s = 1 << (b.E + MW)  # size of the representable space
            # Start from a random in-bounds address and move by a stressed increment.
            a = lo + rng.randrange(hi - lo + 1) if hi > lo else lo
            if a >> AW:
                a = lo
            kind = rng.randrange(4)
            if kind == 0:
                delta = rng.randrange(-2 * s, 2 * s + 1)
            elif kind == 1:
                delta = (lo - s // 8) - a + rng.randrange(-2, 3)
            elif kind == 2:
                delta = (hi + s // 4) - a + rng.randrange(-2, 3)
            else:
                delta = rng.getrandbits(AW) - a
            new = (a + delta) & mask(AW)
            fast = fmt.fast_rep_check(b, a, delta)
            exact = fmt.exact_rep_check(b, a, new)
            require(not fast or exact, f"{fmt.name}: fast check unsound base={base:#x} len={length:#x} {a:#x}{delta:+#x}")
            fast_true += fast
            exact_true += exact
            # Documented slack: s/8 below base and s/4 above top stay representable.
            if b.E < fmt.max_E - 2:
                below, above = lo - s // 8, hi + s // 4 - 1
                if below >= 0:
                    require(fmt.exact_rep_check(b, lo, below), f"{fmt.name}: less than s/8 slack below base")
                    slack += 1
                if above < 1 << AW:
                    require(fmt.exact_rep_check(b, lo, above), f"{fmt.name}: less than s/4 slack above top")
                    slack += 1
            n += 1
        record(f"{fmt.name}: fast representability check implies the exact check", n)
        print(f"     fast check accepted {fast_true} of {exact_true} exactly representable moves; "
              f"{slack} slack probes (s/8 below base, s/4 above top) all representable")


def random_cap_chain(cpu: Cpu, rng: random.Random, steps: int) -> tuple[list[tuple[Cap, Cap]], int]:
    """Random guarded-manipulation chain; returns (parent, child) pairs."""
    f = cpu.f
    c = cpu.root
    pairs: list[tuple[Cap, Cap]] = []
    for _ in range(steps):
        base, top = cpu.bounds(c)
        span = max(top - base, 1)
        op = rng.randrange(6)
        if op == 0:  # in-bounds narrowing
            off = rng.randrange(span)
            c2 = cpu.csetaddr(c, base + off)
            pairs.append((c, c2))
            length = rng.randrange(span - off + 1)
            if rng.random() < 0.5 and length:
                length = min(length, 1 << rng.randrange(1, f.AW))
            c3 = cpu.csetbounds(c2, length)
            pairs.append((c2, c3))
            c = c3 if c3.tag else c
        elif op == 1:  # attempt to widen
            c2 = cpu.csetbounds(c, min(span + rng.randrange(1, 1 << 12), mask(f.AW)))
            pairs.append((c, c2))
        elif op == 2:
            c2 = cpu.candperm(c, rng.getrandbits(12) | rng.getrandbits(12))
            pairs.append((c, c2))
            c = c2
        elif op == 3:  # arbitrary pointer arithmetic, possibly far out of bounds
            delta = rng.choice([rng.randrange(-span, 2 * span + 1), rng.getrandbits(f.AW), -rng.getrandbits(f.AW)])
            c2 = cpu.cincoffset(c, delta)
            pairs.append((c, c2))
            c = c2 if c2.tag else c
        elif op == 4:
            c2 = cpu.csetaddr(c, rng.getrandbits(f.AW))
            pairs.append((c, c2))
            c = c2 if c2.tag else c
        else:
            c2 = cpu.csetbounds(c, rng.randrange(0, 1 << 14), exact_required=True)
            pairs.append((c, c2))
            c = c2 if c2.tag else c
    return pairs, steps


def check_monotonic_random() -> None:
    rng = random.Random(0xC4E21)
    for fmt, otw, chains in ((CC128, 18, 1500), (CC64, 4, 1500)):
        cpu = Cpu(fmt, otw)
        n = untagged = 0
        for _ in range(chains):
            pairs, _ = random_cap_chain(cpu, rng, 12)
            for parent, child in pairs:
                require(dominated(cpu, child, parent), f"{fmt.name}: {parent} -> {child} gained rights")
                require(dominated(cpu, child, cpu.root), f"{fmt.name}: escaped root")
                if child.tag:
                    b = child.bounds
                    require(fmt.decode(fmt.encode(b)) == b, f"{fmt.name}: encode/decode not stable")
                    cb, ct = cpu.bounds(child)
                    require(cb <= ct, f"{fmt.name}: tagged capability with top < base")
                else:
                    untagged += 1
                n += 1
        record(f"{fmt.name}: random derivation chains are monotone (bounds and perms)", n)
        print(f"     {untagged} of {n} results had the tag cleared rather than gaining rights")


def check_sealing() -> None:
    cpu = Cpu(CC128, 18)
    root = cpu.root
    data = cpu.candperm(cpu.csetbounds(cpu.csetaddr(root, 0x10000), 0x100), P_LOAD | P_STORE | P_GLOBAL)
    sealer = cpu.candperm(cpu.csetbounds(cpu.csetaddr(root, 42), 1), P_SEAL | P_UNSEAL | P_GLOBAL)
    other = cpu.candperm(cpu.csetbounds(cpu.csetaddr(root, 43), 1), P_SEAL | P_UNSEAL | P_GLOBAL)
    sealed = cpu.cseal(data, sealer)
    require(sealed.tag and sealed.sealed and sealed.otype == 42, "CSeal")
    n = 1
    # A sealed capability is immutable: every mutator clears the tag.
    for out in (
        cpu.csetbounds(sealed, 8),
        cpu.candperm(sealed, P_LOAD),
        cpu.cincoffset(sealed, 1),
        cpu.csetaddr(sealed, 0x10008),
        cpu.cseal(sealed, other),
        cpu.csealentry(sealed),
    ):
        require(not out.tag, "sealed capability was modified with tag intact")
        n += 1
    # Unsealing needs the matching otype, the permission, and an in-bounds cursor.
    for auth, expect in (
        (sealer, True),
        (other, False),
        (cpu.candperm(sealer, P_SEAL | P_GLOBAL), False),
        (cpu.cincoffset(sealer, 1), False),
        (replace(sealer, tag=False), False),
        (cpu.cseal(sealer, other), False),
        (data, False),
    ):
        out = cpu.cunseal(sealed, auth)
        require(out.tag == expect, f"CUnseal authority check {auth}")
        if out.tag:
            require(cpu.bounds(out) == cpu.bounds(data) and out.perms == data.perms, "unseal restores exactly")
        n += 1
    local_auth = cpu.candperm(sealer, P_SEAL | P_UNSEAL)
    out = cpu.cunseal(sealed, local_auth)
    require(out.tag and not out.perms & P_GLOBAL, "unsealing via non-global authority strips Global")
    sentry = cpu.csealentry(cpu.candperm(cpu.csetbounds(cpu.csetaddr(root, 0x4000), 0x40), P_EXEC | P_LOAD | P_GLOBAL))
    require(sentry.tag and not cpu.cunseal(sentry, sealer).tag, "sentries use a reserved otype and cannot be CUnsealed")
    require(not cpu.cseal(data, cpu.csetaddr(cpu.candperm(root, P_SEAL), cpu.max_otype + 1)).tag, "reserved otype range")
    n += 3
    record("sealing: immutability, authority matching, Global stripping, sentries", n)


def check_buildcap_and_forgery() -> None:
    rng = random.Random(0xF026E)
    cpu = Cpu(CC128, 18)
    n = rejected = accepted = 0
    for _ in range(4000):
        pairs, _ = random_cap_chain(cpu, rng, 4)
        auth = next((c for _, c in reversed(pairs) if c.tag), cpu.root)
        # An attacker-chosen bit pattern: sometimes a subset of `auth`, usually not.
        if rng.random() < 0.5:
            base, top = cpu.bounds(auth)
            span = max(top - base, 1)
            off = rng.randrange(span)
            bits = cpu.candperm(cpu.csetbounds(cpu.csetaddr(auth, base + off), rng.randrange(span - off + 1)),
                                rng.getrandbits(12))
        else:
            _, nb = CC128.set_bounds(a := rng.getrandbits(64), min(a + rng.getrandbits(rng.randrange(1, 64)), 1 << 64))
            bits = Cap(False, rng.getrandbits(12), OTYPE_UNSEALED, nb, a)
        bits = replace(bits, tag=False)
        out = cpu.cbuildcap(auth, bits)
        require(dominated(cpu, out, auth), "CBuildCap exceeded its authority")
        accepted += out.tag
        rejected += not out.tag
        n += 1
    require(accepted > 100 and rejected > 100, "CBuildCap test did not exercise both outcomes")
    record("CBuildCap: untagged bits regain a tag only as a subset of a held authority", n)
    print(f"     {accepted} re-derivations accepted, {rejected} rejected")

    # Tag conservation: with only untagged capability operands, nothing is tagged.
    n = 0
    sealer = cpu.candperm(cpu.csetbounds(cpu.csetaddr(cpu.root, 7), 1), P_SEAL | P_UNSEAL | P_GLOBAL)
    for _ in range(3000):
        a = rng.getrandbits(64)
        _, nb = CC128.set_bounds(a, min(a + rng.getrandbits(rng.randrange(1, 64)), 1 << 64))
        raw = Cap(False, rng.getrandbits(12), rng.choice([OTYPE_UNSEALED, OTYPE_SENTRY, 7, rng.getrandbits(17)]), nb,
                  rng.getrandbits(64))
        outs = (
            cpu.csetbounds(raw, rng.getrandbits(20)),
            cpu.csetbounds(raw, rng.getrandbits(20), exact_required=True),
            cpu.candperm(raw, rng.getrandbits(12)),
            cpu.cincoffset(raw, rng.getrandbits(16)),
            cpu.csetaddr(raw, rng.getrandbits(64)),
            cpu.csealentry(raw),
            cpu.cseal(raw, sealer),       # tagged sealing authority, untagged subject
            cpu.cunseal(raw, sealer),     # tagged unsealing authority, untagged subject
            cpu.cseal(sealer, raw),       # untagged authority
            cpu.cunseal(cpu.cseal(cpu.root, sealer), raw),
            cpu.cbuildcap(raw, raw),      # untagged authority
        )
        for i, out in enumerate(outs):
            # cseal(sealer, raw) keeps `sealer`'s lineage but must lose the tag as well.
            require(not out.tag, f"instruction #{i} produced a tagged capability without tagged authority")
            n += 1
    record("tag conservation: no instruction yields a tag from untagged operands or authorities", n)


def cap_bytes_of(cap: Cap, fmt: CCFormat) -> bytes:
    """Deterministic byte image (layout is illustrative; only the width matters)."""
    meta = (cap.perms << 44) | ((cap.otype & mask(18)) << 26) | fmt.encode(cap.bounds)
    return (cap.addr | (meta << 64)).to_bytes(16, "little")


def check_tagged_memory() -> None:
    rng = random.Random(0x7A65)
    W = 16
    cpu = Cpu(CC128, 18)
    cap = cpu.csetbounds(cpu.csetaddr(cpu.root, 0x2000), 0x80)
    image = cap_bytes_of(cap, CC128)

    # (1) Every partial overwrite clears the tag; straddling writes clear two tags.
    n = 0
    for width in (1, 2, 4, 8):
        for off in range(-width + 1, 2 * W):
            mem = TaggedMemory(4 * W, W)
            mem.store_cap(W, image, True)
            mem.store_cap(2 * W, image, True)
            mem.store_bytes(W + off, mem.load_bytes(W + off, width))  # rewrite identical bytes
            touched = {g for g in range(4) if g * W < W + off + width and W + off < (g + 1) * W}
            for g in (1, 2):
                require(mem.tags[g] == (g not in touched), f"tag state after {width}-byte store at +{off}")
            require(mem.load_bytes(W, W) == image, "data changed")
            n += 1
    record("tagged memory: any data store into a granule clears its tag (even identical bytes)", n)

    # (2) No sequence of data stores forges a tag; only tagged capability stores set tags.
    n = 0
    for _ in range(400):
        mem = TaggedMemory(16 * W, W)
        legit: dict[int, bytes] = {}
        for _ in range(60):
            op = rng.randrange(5)
            if op == 0:
                g = rng.randrange(16)
                mem.store_cap(g * W, image, True)
                legit[g] = image
            elif op == 1:  # write the exact image of a valid capability as plain data
                a = rng.randrange(16 * W - W + 1)
                mem.store_bytes(a, image)
            elif op == 2:
                a = rng.randrange(16 * W - 8)
                mem.store_bytes(a, rng.randbytes(rng.choice([1, 2, 4, 8])))
            elif op == 3:
                d, s = rng.randrange(8 * W), 8 * W + rng.randrange(7 * W)
                memcpy_bytewise(mem, d, s, rng.randrange(W + 1))
            else:
                g = rng.randrange(16)
                mem.store_cap(g * W, rng.randbytes(W), False)
            for g in list(legit):
                if not mem.tags[g]:
                    del legit[g]
            for g in range(16):
                if mem.tags[g]:
                    require(legit.get(g) == mem.load_bytes(g * W, W), "tag set on bytes not stored as a capability")
            n += 1
    record("tagged memory: byte images of valid capabilities never become tagged", n)

    # (3) memcpy strategies.
    n = kept = dropped = 0
    for trial in range(1500):
        mem = TaggedMemory(64 * W, W)
        for g in range(0, 24):
            if rng.random() < 0.6:
                mem.store_cap(g * W, image, True)
            else:
                mem.store_bytes(g * W, rng.randbytes(W))
        src = rng.randrange(0, 8 * W)
        length = rng.randrange(0, 12 * W)
        dst = 32 * W + rng.randrange(0, 4 * W)
        if trial % 3 == 0:
            dst = (dst & ~(W - 1)) | (src & (W - 1))  # force mutual alignment
        before = list(mem.tags)
        ref = mem.load_bytes(src, length)
        byte_mem = TaggedMemory(64 * W, W)
        byte_mem.data[:] = mem.data
        byte_mem.tags[:] = mem.tags
        memcpy_bytewise(byte_mem, dst, src, length)
        memcpy_capaware(mem, dst, src, length)
        require(mem.load_bytes(dst, length) == ref == byte_mem.load_bytes(dst, length), "copy payload mismatch")
        mutual = ((src ^ dst) & (W - 1)) == 0
        for g in range(32, 64):
            lo, hi = g * W, (g + 1) * W
            whole = dst <= lo and hi <= dst + length
            src_g = (lo - dst + src) // W
            expect = mutual and whole and before[src_g]
            if lo < dst + length and dst < hi:
                require(mem.tags[g] == expect, f"cap-aware memcpy tag at granule {g}")
                require(not byte_mem.tags[g], "byte-wise memcpy preserved a tag")
                kept += mem.tags[g]
                dropped += before[src_g] and not mem.tags[g] if whole else 0
            n += 1
    require(kept > 500 and dropped > 500, "memcpy test did not exercise both outcomes")
    record("memcpy: byte loop drops every tag; capability-word copy keeps tags only when "
           "source and destination are mutually aligned and the granule is wholly copied", n)
    print(f"     capability-word copy preserved {kept} tags; {dropped} wholly overwritten granules lost a "
          "source tag because the operands were mutually misaligned")


def check_cheriot() -> None:
    rng = random.Random(0xC4E210)
    f = CHERIOT
    n = 0
    for length in range(0, 512):
        for base in (0, 1, 0x1FF, 0x20000003, 0xFFFFFE00):
            if base + length > 1 << 32:
                continue
            exact, enc = f.set_bounds(base, length)
            lo, hi = f.get_bounds(enc, base)
            require(exact and (lo, hi) == (base, base + length), f"CHERIoT byte-exact {base:#x}+{length}")
            n += 1
    exact, enc = f.set_bounds(1, 512)
    require(not exact and f.get_bounds(enc, 1) == (0, 514), "CHERIoT first rounding step")
    for e in range(0, 15):
        max_len = 511 << e
        exact, enc = f.set_bounds(0, max_len)
        require(exact and enc[0] == e and f.get_bounds(enc, 0) == (0, max_len), f"CHERIoT max length e={e}")
        n += 1
    exact, enc = f.set_bounds(0, mask(32))
    require(enc[0] == 24, "CHERIoT saturating exponent")
    for _ in range(20000):
        base = rng.getrandbits(32)
        length = min(rng.getrandbits(rng.randrange(1, 33)), (1 << 32) - base)
        exact, enc = f.set_bounds(base, length)
        lo, hi = f.get_bounds(enc, base)
        require(lo <= base and base + length <= hi, f"CHERIoT containment {base:#x}+{length:#x}")
        require(exact == ((lo, hi) == (base, base + length)), "CHERIoT exact flag")
        e = enc[0]
        if e != 24:
            # Representable range is [base, base + 2^(e+9)): nothing below base.
            for a in (lo, hi - 1 if hi > lo else lo, hi):
                if a < 1 << 32:
                    require(f.get_bounds(enc, a) == (lo, hi), "CHERIoT in-bounds address representable")
            if lo > 0:
                require(f.get_bounds(enc, lo - 1) != (lo, hi), "CHERIoT address below base stayed representable")
        n += 1
    record("CHERIoT encoding: byte-exact to 511 bytes, 2^e alignment, no representable space below base", n)
    # Same capability width (64 bits, 32-bit address), very different precision.
    mib = 1 << 20
    _, enc = f.set_bounds(0, mib)
    cheriot_align = 1 << enc[0]
    cc64_align = (~CC64.cram(mib) & mask(32)) + 1
    require(cheriot_align == 4096 and cc64_align == 131072, "1 MiB alignment comparison")
    require(f.set_bounds(cheriot_align, mib)[0] and not f.set_bounds(cheriot_align // 2, mib)[0], "CHERIoT 1 MiB")
    require(CC64.round(cc64_align, cc64_align + mib)[2] and not CC64.round(cc64_align // 2, cc64_align // 2 + mib)[2],
            "CC-64 1 MiB")
    record("64-bit formats compared: a 1 MiB object needs 4 KiB alignment (CHERIoT) vs 128 KiB (CC-64)", 4)

    # Alignment granule required for a requested length, per format.
    table = {  # length: (CC-128, CC-64, CHERIoT)
        63: (1, 1, 1),
        511: (1, 64, 1),
        4095: (1, 512, 16),
        4096: (8, 512, 16),
        1 << 20: (2048, 131072, 4096),
        1 << 30: (1 << 21, 1 << 27, 1 << 24),
    }
    for length, (a128, a64, aiot) in table.items():
        require((~CC128.cram(length) & mask(64)) + 1 == a128, f"CC-128 alignment for {length}")
        require((~CC64.cram(length) & mask(32)) + 1 == a64, f"CC-64 alignment for {length}")
        require(1 << f.set_bounds(0, length)[1][0] == aiot, f"CHERIoT alignment for {length}")
    # Padding when one byte is added to a 1 MiB request.
    require(CC128.crrl(mib + 1) == mib + 2048, "CC-128 padded length")
    require(CC64.crrl(mib + 1) == mib + 131072, "CC-64 padded length")
    lo, hi = f.get_bounds(f.set_bounds(0, mib + 1)[1], 0)
    require(hi - lo == mib + 4096, "CHERIoT padded length")
    record("alignment table: granule per request length for CC-128, CC-64, and CHERIoT", 3 * len(table) + 3)


def epoch_clears(now: int, then: int) -> bool:
    """cheri_revoke_epoch_clears: now >= then + (then & 1) + 2."""
    return now >= then + (then & 1) + 2


def check_epochs() -> None:
    n = 0
    for then in range(0, 40):
        # The counter is even when idle and odd while a pass is running.
        # Memory painted at `then` is safe once a pass that *started* after
        # painting has *finished*.
        first_start_after = then + 1 if then % 2 == 0 else then + 2
        first_safe = first_start_after + 1
        for now in range(then, then + 8):
            require(epoch_clears(now, then) == (now >= first_safe), f"epoch arithmetic {then}->{now}")
            n += 1
    record("revocation epochs: quarantine is released only after one full later sweep", n)


def sweep_model(design: str, pages: int = 3) -> tuple[bool, int]:
    """Exhaustively explore mutator/sweeper interleavings for one revocation epoch.

    State: one register and `pages` single-slot pages.  Each holds 0 (nothing),
    1 (a live capability), or 2 (a stale capability to quarantined memory).
    The sweeper visits pages in order, erasing stale capabilities.  Between
    sweeper steps the mutator may load a slot into the register or store the
    register into a slot.  Returns (sound, states explored); sound means no
    stale capability survives anywhere at the end of the epoch.

    design = "none"      registers scanned at start, concurrent sweep only
             "store-stw" as above, plus stores mark the page dirty and dirty
                         pages are re-swept with the mutator stopped
             "load"      registers scanned at start; loading from an unswept
                         page sweeps that page first (load barrier)
    """
    seen: set[tuple] = set()
    sound = True
    for init in itertools.product((0, 1, 2), repeat=pages + 1):
        reg = 1 if init[0] == 2 else init[0]  # epoch start: register scan
        stack = [(reg, tuple(init[1:]), 0, frozenset())]
        while stack:
            state = stack.pop()
            if state in seen:
                continue
            seen.add(state)
            reg, mem, swept, dirty = state
            if swept == pages:
                final = list(mem)
                if design == "store-stw":
                    for p in dirty:
                        if final[p] == 2:
                            final[p] = 0
                    if reg == 2:
                        reg = 0
                if reg == 2 or 2 in final:
                    sound = False
                continue
            # sweeper step
            m = list(mem)
            if m[swept] == 2:
                m[swept] = 0
            stack.append((reg, tuple(m), swept + 1, dirty - {swept}))
            # mutator steps
            for p in range(pages):
                if design == "load" and p >= swept:
                    val = 0 if mem[p] == 2 else mem[p]  # barrier cleans before the load completes
                else:
                    val = mem[p]
                stack.append((val, mem, swept, dirty))
                m = list(mem)
                m[p] = reg
                stack.append((reg, tuple(m), swept, dirty | {p} if p < swept else dirty))
    return sound, len(seen)


def check_sweep_designs() -> None:
    results = {d: sweep_model(d) for d in ("none", "store-stw", "load")}
    require(not results["none"][0], "barrier-free concurrent sweep was unexpectedly sound")
    require(results["store-stw"][0], "store-tracking + stop-the-world re-scan should be sound")
    require(results["load"][0], "load barrier should be sound")
    record("sweeping revocation: concurrent sweep needs a store-tracked stop-the-world pass "
           "or a load barrier", sum(r[1] for r in results.values()))
    for d, (ok, states) in results.items():
        print(f"     design={d:9s} sound={ok!s:5s} states={states}")


def check_upstream_file(path: str) -> None:
    """Optional: compare against every row of an upstream setbounds_inputs_128.cpp."""
    import re

    text = open(path, encoding="utf-8").read()
    rows = re.findall(r"\{\s*" + ",".join(["(0x[0-9a-fA-F]+)"] * 8) + r"\}", text)
    require(len(rows) > 0, "no vector rows found")
    for row in rows:
        b1, t1, b2, t2, cb1, ct1, cb2, ct2 = (int(x, 16) for x in row)
        require(CC128.round(b1, t1)[:2] == (cb1, ct1), f"upstream row {row}")
        require(CC128.round(b2, t2)[:2] == (cb2, ct2), f"upstream row {row}")
    record(f"CC-128 set-bounds matches every row of {path}", 2 * len(rows))


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "--upstream-vectors":
        check_upstream_file(sys.argv[2])
    check_golden()
    check_alignment_table()
    check_toy_exhaustive()
    check_representability()
    check_monotonic_random()
    check_sealing()
    check_buildcap_and_forgery()
    check_tagged_memory()
    check_cheriot()
    check_epochs()
    check_sweep_designs()
    total = sum(c for _, c in CHECKS)
    print(f"PASS: {len(CHECKS)} check groups, {total} cases")
    return 0


if __name__ == "__main__":
    sys.exit(main())
