#!/usr/bin/env python3
"""Standalone model and optional compiler cross-check for C ABI contingencies.

The script has two layers.

1. A pure-Python model (standard library only, Python 3.10+) of
   * natural C aggregate layout and two bit-field allocation rules,
   * System V AMD64 psABI eightbyte classification and register assignment,
   * the Microsoft x64 ("Win64") positional convention,
   * the AAPCS64 stage B/C marshalling algorithm (plus the two documented
     Darwin deviations at this level),
   * the System V AMD64 and AAPCS64 `va_list` state machines,
   * C integer promotions and the usual arithmetic conversions under the
     LP64 and LLP64 data models and both `char` signedness choices.
   Every model result is compared with an expectation transcribed by hand
   from the cited normative text (worked examples where the text has them).

2. An optional cross-check that compiles small C programs with a local C
   compiler on an x86-64 System V host and observes, at run time, which
   register or stack slot each argument byte arrived in, where return values
   are produced, how `va_list` fields evolve, what the integer expressions
   evaluate to, and how specimen structures are laid out. The Win64 rules are
   exercised through the compiler's `ms_abi` function attribute, so that part
   observes one compiler's emulation of the convention, not MSVC.
   AAPCS64 is model-only.

Exit status: 0 when every model check passes and every attempted compiler
check passes; 1 otherwise. `--no-cc` restricts the run to layer 1.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass

# --------------------------------------------------------------------------
# Type model
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Prim:
    c: str  # C spelling, key into PRIMS[abi]


@dataclass(frozen=True)
class Struct:
    name: str
    fields: tuple  # tuple[(field name, type)]
    packed: bool = False


@dataclass(frozen=True)
class Array:
    elem: object
    n: int


def _prims(long_size, long_double):
    return {
        "char": (1, 1, "int"),
        "short": (2, 2, "int"),
        "int": (4, 4, "int"),
        "long": (long_size, long_size, "int"),
        "long long": (8, 8, "int"),
        "void *": (8, 8, "int"),
        "float": (4, 4, "f32"),
        "double": (8, 8, "f64"),
        "long double": long_double,
        "__int128": (16, 16, "i128"),
        "__float128": (16, 16, "f128"),
        "__m256": (32, 32, "vec"),
        "__m512": (64, 64, "vec"),
    }


# (size, alignment, kind). `long double` is the 80-bit x87 format on System V
# AMD64, IEEE binary128 on AAPCS64, and identical to `double` for MSVC.
PRIMS = {
    "sysv": _prims(8, (16, 16, "x87")),
    "win64": _prims(4, (8, 8, "f64")),
    "aapcs64": _prims(8, (16, 16, "f128")),
}

CHAR, SHORT, INT, LONG, LLONG = (Prim(n) for n in ("char", "short", "int", "long", "long long"))
PTR, FLOAT, DOUBLE, LDOUBLE = Prim("void *"), Prim("float"), Prim("double"), Prim("long double")
I128, F128, M256, M512 = Prim("__int128"), Prim("__float128"), Prim("__m256"), Prim("__m512")


def align_up(x, a):
    return (x + a - 1) // a * a


@dataclass(frozen=True)
class Layout:
    size: int
    align: int
    leaves: tuple  # tuple[(offset, Prim)]


def layout(abi, t):
    """Natural C layout: members in declaration order, each at the lowest
    offset with its alignment; size rounded up to the aggregate alignment."""
    if isinstance(t, Prim):
        size, align, _ = PRIMS[abi][t.c]
        return Layout(size, align, ((0, t),))
    if isinstance(t, Array):
        e = layout(abi, t.elem)
        leaves = tuple((i * e.size + o, p) for i in range(t.n) for o, p in e.leaves)
        return Layout(e.size * t.n, e.align, leaves)
    off, align, leaves = 0, 1, []
    for _, ft in t.fields:
        f = layout(abi, ft)
        fa = 1 if t.packed else f.align
        off = align_up(off, fa)
        leaves += [(off + o, p) for o, p in f.leaves]
        off += f.size
        align = max(align, fa)
    return Layout(align_up(off, align), align, tuple(leaves))


def kind(abi, p):
    return PRIMS[abi][p.c][2]


# --------------------------------------------------------------------------
# System V AMD64 psABI: classification (section "Parameter Passing")
# --------------------------------------------------------------------------

MEM = ("MEMORY",)
SYSV_INT = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]


def _merge(a, b):
    if a == b:
        return a
    if a == "NO_CLASS":
        return b
    if b == "NO_CLASS":
        return a
    if "MEMORY" in (a, b):
        return "MEMORY"
    if "INTEGER" in (a, b):
        return "INTEGER"
    if {a, b} & {"X87", "X87UP", "COMPLEX_X87"}:
        return "MEMORY"
    return "SSE"


def sysv_classify(t):
    """Return a tuple with one class per eightbyte, () for an empty object,
    or MEM."""
    lay = layout("sysv", t)
    if lay.size == 0:
        return ()
    if lay.size > 64:  # larger than eight eightbytes
        return MEM
    n = (lay.size + 7) // 8
    cls = ["NO_CLASS"] * n
    for off, p in lay.leaves:
        size, align, k = PRIMS["sysv"][p.c]
        if off % align:  # unaligned field
            return MEM
        parts = {
            "int": ["INTEGER"],
            "f32": ["SSE"],
            "f64": ["SSE"],
            "i128": ["INTEGER", "INTEGER"],
            "f128": ["SSE", "SSEUP"],
            "x87": ["X87", "X87UP"],
            "vec": ["SSE"] + ["SSEUP"] * (size // 8 - 1),
        }[k]
        for i, c in enumerate(parts):
            cls[off // 8 + i] = _merge(cls[off // 8 + i], c)
    # Post-merger cleanup.
    if "MEMORY" in cls:
        return MEM
    for i, c in enumerate(cls):
        if c == "X87UP" and (i == 0 or cls[i - 1] != "X87"):
            return MEM
    if n > 2 and (cls[0] != "SSE" or any(c != "SSEUP" for c in cls[1:])):
        return MEM
    for i, c in enumerate(cls):
        if c == "SSEUP" and (i == 0 or cls[i - 1] not in ("SSE", "SSEUP")):
            cls[i] = "SSE"
    return tuple(cls)


def sysv_ret_detail(t):
    if t is None:
        return {"kind": "void"}
    cls = sysv_classify(t)
    if cls == ():
        return {"kind": "ignored"}
    if cls == MEM:
        return {"kind": "sret"}
    ints, sses, eb = ["rax", "rdx"], ["xmm0", "xmm1"], []
    for c in cls:
        if c == "INTEGER":
            eb.append(ints.pop(0))
        elif c == "SSE":
            eb.append(sses.pop(0))
        elif c == "X87":
            eb.append("st0")
        else:  # SSEUP, X87UP, NO_CLASS travel with / are padding of the previous
            eb.append(None)
    return {"kind": "reg", "eb": eb}


def sysv_args_detail(args, ret=None):
    """Assign locations. Each argument is all-or-nothing: if any eightbyte
    lacks a register, the whole argument goes to the stack and registers
    already tentatively taken are released."""
    ni = 1 if sysv_ret_detail(ret)["kind"] == "sret" else 0  # hidden pointer in rdi
    ns, stack, out = 0, 0, []
    for t in args:
        lay, cls = layout("sysv", t), sysv_classify(t)
        if cls == ():
            out.append({"kind": "ignored"})
            continue
        need_i, need_s = cls.count("INTEGER"), cls.count("SSE")
        if cls == MEM or "X87" in cls or ni + need_i > 6 or ns + need_s > 8:
            stack = align_up(stack, max(8, lay.align))
            out.append({"kind": "stack", "off": stack})
            stack += align_up(lay.size, 8)
            continue
        eb = []
        for c in cls:
            if c == "INTEGER":
                eb.append(("I", ni))
                ni += 1
            elif c == "SSE":
                eb.append(("X", ns))
                ns += 1
            elif c == "SSEUP":
                eb.append(("XUP", ns - 1))
            else:
                eb.append(None)
        out.append({"kind": "reg", "eb": eb})
    return out, {"int_used": ni, "sse_used": ns, "stack": stack}


def _sysv_fmt(d, wide=None):
    if d["kind"] in ("ignored", "void"):
        return d["kind"]
    if d["kind"] == "stack":
        return f"stack@{d['off']}"
    if d["kind"] == "sret":
        return "sret(rdi)->rax"
    names = []
    for e in d["eb"]:
        if isinstance(e, tuple) and e[0] == "I":
            names.append(SYSV_INT[e[1]])
        elif isinstance(e, tuple) and e[0] == "X":
            names.append(f"xmm{e[1]}")
        elif isinstance(e, str):
            names.append(e)
    return "+".join(names)


def sysv_args(args, ret=None):
    return [_sysv_fmt(d) for d in sysv_args_detail(args, ret)[0]]


def sysv_ret(t):
    return _sysv_fmt(sysv_ret_detail(t))


# --------------------------------------------------------------------------
# Microsoft x64 convention
# --------------------------------------------------------------------------

WIN_GPR = ["rcx", "rdx", "r8", "r9"]


def win64_mode(t):
    """'int' (by value, integer slot), 'xmm' (by value, vector slot) or
    'ref' (pointer to a caller-allocated copy)."""
    lay = layout("win64", t)
    if isinstance(t, Prim):
        k = kind("win64", t)
        if k == "int":
            return "int"
        if k in ("f32", "f64"):
            return "xmm"
        return "ref"  # 16-byte scalars never travel by immediate value
    return "int" if lay.size in (1, 2, 4, 8) else "ref"


def win64_ret(t):
    if t is None:
        return "void"
    if isinstance(t, Prim):
        k = kind("win64", t)
        if k == "int":
            return "rax"
        if k in ("f32", "f64"):
            return "xmm0"
        if k == "i128":
            return "xmm0"  # GNU-family compilers; the type does not exist in MSVC
        raise NotImplementedError(t)
    return "rax" if layout("win64", t).size in (1, 2, 4, 8) else "sret(rcx)->rax"


def win64_args(args, ret=None, n_named=None):
    """One slot per argument, by position. Offsets are relative to RSP at the
    call instruction; offsets 0..31 are the register home ("shadow") area."""
    slot = 1 if win64_ret(ret).startswith("sret") else 0
    out = []
    for idx, t in enumerate(args):
        mode = win64_mode(t)
        if slot < 4:
            loc = f"xmm{slot}" if mode == "xmm" else WIN_GPR[slot]
            if mode == "xmm" and n_named is not None and idx >= n_named:
                loc += "=" + WIN_GPR[slot]  # variadic: duplicated in the integer register
        else:
            loc = f"stack@{8 * slot}"
        out.append("&" + loc if mode == "ref" else loc)
        slot += 1
    return out


# --------------------------------------------------------------------------
# AAPCS64 (stage B and stage C rules), with the two Darwin deviations
# --------------------------------------------------------------------------


def a64_hfa(t):
    """Homogeneous Floating-point Aggregate: a composite whose fundamental
    members all have the same floating-point type, at most four of them."""
    if isinstance(t, Prim):
        return None
    lay = layout("aapcs64", t)
    kinds = {kind("aapcs64", p) for _, p in lay.leaves}
    if len(kinds) == 1 and kinds <= {"f32", "f64", "f128"} and 1 <= len(lay.leaves) <= 4:
        return len(lay.leaves)
    return None


def a64_args(args, variant="aapcs64", n_named=None):
    darwin = variant == "darwin"
    ngrn = nsrn = nsaa = 0
    out = []
    for idx, t in enumerate(args):
        lay = layout("aapcs64", t)
        if lay.size == 0:
            out.append("ignored")
            continue
        composite = not isinstance(t, Prim)
        k = None if composite else kind("aapcs64", t)
        hfa = a64_hfa(t)
        size, align, ref = lay.size, lay.align, ""
        if composite and not hfa and size > 16:  # B.4: replaced by a pointer to a copy
            composite, k, size, align, ref = False, "int", 8, 8, "&"
        elif composite:  # B.5
            size = align_up(size, 8)
        fp = (not composite) and k in ("f32", "f64", "f128")
        if darwin and n_named is not None and idx >= n_named:  # variadic: all on the stack
            nsaa = align_up(nsaa, max(8, align))
            out.append(f"{ref}stack@{nsaa}")
            nsaa += align_up(size, 8)
            continue
        if fp and nsrn < 8:  # C.1
            out.append(f"v{nsrn}")
            nsrn += 1
        elif hfa and nsrn + hfa <= 8:  # C.2
            out.append("+".join(f"v{nsrn + i}" for i in range(hfa)))
            nsrn += hfa
        elif hfa or fp:
            if hfa:  # C.3
                nsrn = 8
            if hfa or k == "f128":  # C.4
                nsaa = align_up(nsaa, 8 if align <= 8 else 16)
            if fp and k == "f32" and not darwin:  # C.5
                size = 8
            if fp and darwin:
                nsaa = align_up(nsaa, align)
            out.append(f"stack@{nsaa}")  # C.6
            nsaa += size
        elif not composite and size <= 8 and ngrn < 8:  # C.9
            out.append(f"{ref}x{ngrn}")
            ngrn += 1
        else:
            if align == 16 and not darwin:  # C.10
                ngrn = align_up(ngrn, 2)
            if not composite and size == 16 and ngrn < 7:  # C.11
                out.append(f"x{ngrn}+x{ngrn + 1}")
                ngrn += 2
            elif composite and size // 8 <= 8 - ngrn:  # C.12
                out.append("+".join(f"x{ngrn + i}" for i in range(size // 8)))
                ngrn += size // 8
            else:
                ngrn = 8  # C.13
                if darwin and not composite:
                    nsaa = align_up(nsaa, align)  # slots sized as needed
                else:
                    nsaa = align_up(nsaa, max(8, align))  # C.14
                    if not composite and size < 8:  # C.16
                        size = 8
                out.append(f"{ref}stack@{nsaa}")  # C.15 / C.17
                nsaa += size
    return out


def a64_ret(t):
    if t is None:
        return "void"
    loc = a64_args([t])[0]
    return "indirect(x8)" if loc.startswith(("&", "stack")) else loc


# --------------------------------------------------------------------------
# va_list state machines
# --------------------------------------------------------------------------


def default_argument_promotion(t):
    """Types narrower than int become int and float becomes double."""
    if isinstance(t, Prim) and t.c in ("char", "short"):
        return INT
    return DOUBLE if t == FLOAT else t


def sysv_va_sim(named, fetched):
    """Simulate `va_start` then a sequence of `va_arg` fetches. Returns a list
    of (gp_offset, fp_offset, overflow_arg_area offset, source)."""
    _, used = sysv_args_detail(named)
    gp, fp, ovf = 8 * used["int_used"], 48 + 16 * used["sse_used"], used["stack"]
    states = [(gp, fp, ovf, "va_start")]
    for t in fetched:
        t = default_argument_promotion(t)
        lay, cls = layout("sysv", t), sysv_classify(t)
        num_gp, num_fp = cls.count("INTEGER"), cls.count("SSE")
        in_reg_class = cls not in ((), MEM) and "X87" not in cls
        if in_reg_class and gp <= 48 - num_gp * 8 and fp <= 176 - num_fp * 16:
            gp, fp, src = gp + 8 * num_gp, fp + 16 * num_fp, "reg_save_area"
        else:
            if lay.align > 8:
                ovf = align_up(ovf, 16)
            ovf = align_up(ovf + lay.size, 8)
            src = "overflow_arg_area"
        states.append((gp, fp, ovf, src))
    return states


def a64_va_sim(named_gr, named_vr, fetched):
    """AAPCS64 appendix pseudo-code. Returns (__gr_offs, __vr_offs, __stack
    offset, source) after va_start and after each fetch."""
    gr, vr, stack = -((8 - named_gr) * 8), -((8 - named_vr) * 16), 0
    states = [(gr, vr, stack, "va_start")]
    for t in fetched:
        t = default_argument_promotion(t)
        lay, hfa = layout("aapcs64", t), a64_hfa(t)
        size, align = lay.size, lay.align
        composite = not isinstance(t, Prim)
        fp = (not composite) and kind("aapcs64", t) in ("f32", "f64", "f128")
        if composite and not hfa and size > 16:
            size, align = 8, 8  # a pointer to the copy is fetched
        src = "stack"
        if hfa or fp:
            nreg = hfa if hfa else (size + 15) // 16
            if vr < 0:
                offs = vr
                vr = offs + nreg * 16
                if vr <= 0:
                    src = "vr_save_area"
        else:
            if gr < 0:
                offs = gr
                if align > 8:
                    offs = (offs + 15) & -16
                gr = offs + (size + 7) // 8 * 8
                if gr <= 0:
                    src = "gr_save_area"
        if src == "stack":
            if align > 8:
                stack = (stack + 15) & -16
            stack = (stack + size + 7) & -8
        states.append((gr, vr, stack, src))
    return states


# --------------------------------------------------------------------------
# C integer promotions and usual arithmetic conversions
# --------------------------------------------------------------------------

RANK = {"char": 1, "short": 2, "int": 3, "long": 4, "long long": 5}
DATA_MODELS = {
    "LP64 signed-char (System V AMD64)": {"long": 64, "char_signed": True},
    "LLP64 signed-char (Microsoft x64)": {"long": 32, "char_signed": True},
    "LP64 unsigned-char (AAPCS64)": {"long": 64, "char_signed": False},
}


def itype(dm, name):
    """(bits, signed, rank) of a standard integer type name."""
    unsigned = name.startswith("unsigned ")
    base = name.removeprefix("unsigned ").removeprefix("signed ")
    bits = {"char": 8, "short": 16, "int": 32, "long": dm["long"], "long long": 64}[base]
    signed = dm["char_signed"] if name == "char" else not unsigned
    return bits, signed, RANK[base]


def promote(dm, name):
    bits, signed, rank = itype(dm, name)
    if rank >= RANK["int"]:
        return name
    return "int" if bits < 32 or signed else "unsigned int"


def usual(dm, a, b):
    a, b = promote(dm, a), promote(dm, b)
    if a == b:
        return a
    (ba, sa, ra), (bb, sb, rb) = itype(dm, a), itype(dm, b)
    if sa == sb:
        return a if ra > rb else b
    (u, bu, ru), (s, bs, rs) = ((a, ba, ra), (b, bb, rb)) if not sa else ((b, bb, rb), (a, ba, ra))
    if ru >= rs:
        return u
    if bs > bu:  # the signed type represents every value of the unsigned type
        return s
    return "unsigned " + s


def convert(dm, v, name):
    bits, signed, _ = itype(dm, name)
    v &= (1 << bits) - 1
    return v - (1 << bits) if signed and v >> (bits - 1) else v


def binop(dm, op, a, b):
    """a and b are (value, type). Returns (value, type) or ('UB', type) when a
    signed result is not representable."""
    (va, ta), (vb, tb) = a, b
    ct = usual(dm, ta, tb)
    x, y = convert(dm, va, ct), convert(dm, vb, ct)
    if op in ("<", "=="):
        return (int(x < y) if op == "<" else int(x == y)), "int"
    r = {"+": x + y, "-": x - y, "*": x * y}[op]
    bits, signed, _ = itype(dm, ct)
    if signed and not -(1 << (bits - 1)) <= r < (1 << (bits - 1)):
        return "UB", ct
    return convert(dm, r, ct), ct


def bitnot(dm, a):
    v, t = a
    pt = promote(dm, t)
    return convert(dm, ~convert(dm, v, pt), pt), pt


def cast(dm, a, t):
    return convert(dm, a[0], t), t


def hazards(dm):
    """(C expression, model value). Values are ints or 'UB'."""
    c = lambda v, t: (convert(dm, v, t), t)
    i0 = (0, "int")
    return [
        ("~(unsigned char)0xFF", bitnot(dm, c(0xFF, "unsigned char"))[0]),
        ("(unsigned char)~(unsigned char)0xFF", cast(dm, bitnot(dm, c(0xFF, "unsigned char")), "unsigned char")[0]),
        ("-1 < 1u", binop(dm, "<", (-1, "int"), (1, "unsigned int"))[0]),
        ("-1L < 1u", binop(dm, "<", (-1, "long"), (1, "unsigned int"))[0]),
        ("-1LL < 1u", binop(dm, "<", (-1, "long long"), (1, "unsigned int"))[0]),
        ("((unsigned short)1 - (unsigned short)2) < 0",
         binop(dm, "<", binop(dm, "-", c(1, "unsigned short"), c(2, "unsigned short")), i0)[0]),
        ("(1u - 2u) < 0", binop(dm, "<", binop(dm, "-", (1, "unsigned int"), (2, "unsigned int")), i0)[0]),
        ("(unsigned short)0xFFFF + 1", binop(dm, "+", c(0xFFFF, "unsigned short"), (1, "int"))[0]),
        ("0xFFFFFFFFu + 1", binop(dm, "+", (0xFFFFFFFF, "unsigned int"), (1, "int"))[0]),
        ("(char)0xFF == 0xFF", binop(dm, "==", c(0xFF, "char"), (0xFF, "int"))[0]),
        ("(char)0xFF < 0", binop(dm, "<", c(0xFF, "char"), i0)[0]),
        ("(unsigned short)0xFFFF * (unsigned short)0xFFFF",
         binop(dm, "*", c(0xFFFF, "unsigned short"), c(0xFFFF, "unsigned short"))[0]),
        ("0xFFFFu * 0xFFFFu", binop(dm, "*", (0xFFFF, "unsigned int"), (0xFFFF, "unsigned int"))[0]),
    ]


# --------------------------------------------------------------------------
# Bit-field allocation: System V rule versus Microsoft rule
# --------------------------------------------------------------------------


def bitfield_layout(rule, members):
    """members: list of (type size in bytes, width in bits or None for an
    ordinary member). Returns (sizeof, alignof).

    'sysv': a bit-field goes at the next free bit unless it would cross a
            boundary of a storage unit of its declared type; it shares units
            with neighbouring members of any type.
    'ms':   adjacent bit-fields share an allocation unit only if their
            declared types have the same size and the next field fits; every
            unit occupies the full size of its declared type."""
    align, bit = 1, 0  # sysv state: next free bit
    end, unit = 0, None  # ms state: byte end, (start byte, type size, bits used)
    for size, width in members:
        align = max(align, size)
        if rule == "sysv":
            if width is None:
                bit = align_up(align_up(bit, 8), 8 * size) + 8 * size
            else:
                if bit // (8 * size) != (bit + width - 1) // (8 * size):
                    bit = align_up(bit, 8 * size)
                bit += width
        else:
            if width is None:
                end, unit = align_up(end, size) + size, None
            else:
                if unit is None or unit[1] != size or unit[2] + width > 8 * size:
                    start = align_up(end, size)
                    end, unit = start + size, (start, size, 0)
                unit = (unit[0], unit[1], unit[2] + width)
    raw = (bit + 7) // 8 if rule == "sysv" else end
    return align_up(raw, align), align


BITFIELD_SPECIMENS = [
    # name, C body, members, expected sysv (size, align), expected ms (size, align)
    ("BF1", "unsigned char a:4; unsigned int b:4;", [(1, 4), (4, 4)], (4, 4), (8, 4)),
    ("BF2", "unsigned int a:4; unsigned char b;", [(4, 4), (1, None)], (4, 4), (8, 4)),
    ("BF3", "unsigned int a:20; unsigned int b:20;", [(4, 20), (4, 20)], (8, 4), (8, 4)),
    ("BF4", "unsigned long long a:33; unsigned int b:10;", [(8, 33), (4, 10)], (8, 8), (16, 8)),
]

# --------------------------------------------------------------------------
# Specimen types and expectations transcribed from the specifications
# --------------------------------------------------------------------------

S_DL = Struct("S_DL", (("a", DOUBLE), ("b", LLONG)))  # { double; long long }
S_F4 = Struct("S_F4", (("a", FLOAT), ("b", FLOAT), ("c", FLOAT), ("d", FLOAT)))
S_D4 = Struct("S_D4", (("a", DOUBLE), ("b", DOUBLE), ("c", DOUBLE), ("d", DOUBLE)))
S_L3 = Struct("S_L3", (("a", LLONG), ("b", LLONG), ("c", LLONG)))
S_IF = Struct("S_IF", (("a", INT), ("b", FLOAT)))
S_LD = Struct("S_LD", (("x", LDOUBLE),))
S_PK = Struct("S_PK", (("c", CHAR), ("x", LLONG)), packed=True)
S_E = Struct("S_E", ())
S_CI = Struct("S_CI", (("c", CHAR), ("x", I128)))
S_I1 = Struct("S_I1", (("x", I128),))
S_PARM = Struct("structparm", (("a", INT), ("b", INT), ("d", DOUBLE)))
S_C3 = Struct("S_C3", (("a", CHAR), ("b", CHAR), ("c", CHAR)))
S_D2 = Struct("S_D2", (("a", DOUBLE), ("b", DOUBLE)))

MODEL_CHECKS = []  # (label, got, expected)


def expect(label, got, expected):
    MODEL_CHECKS.append((label, got, expected))


def build_model_checks():
    # ---- layout ----------------------------------------------------------
    for abi in ("sysv", "win64", "aapcs64"):
        lay = lambda t: (layout(abi, t).size, layout(abi, t).align)
        expect(f"layout[{abi}] {{double; long long}}", lay(S_DL), (16, 8))
        expect(f"layout[{abi}] {{char; __int128}}", lay(S_CI), (32, 16))
        expect(f"layout[{abi}] packed {{char; long long}}", lay(S_PK), (9, 1))
        expect(f"layout[{abi}] {{char; char; char}}", lay(S_C3), (3, 1))
    expect("layout[sysv] long / long double", [PRIMS["sysv"][n][:2] for n in ("long", "long double")], [(8, 8), (16, 16)])
    expect("layout[win64] long / long double", [PRIMS["win64"][n][:2] for n in ("long", "long double")], [(4, 4), (8, 8)])
    expect("layout[aapcs64] long / long double", [PRIMS["aapcs64"][n][:2] for n in ("long", "long double")], [(8, 8), (16, 16)])
    for name, _, members, sysv_exp, ms_exp in BITFIELD_SPECIMENS:
        expect(f"bitfield[sysv] {name}", bitfield_layout("sysv", members), sysv_exp)
        expect(f"bitfield[ms] {name}", bitfield_layout("ms", members), ms_exp)

    # ---- System V AMD64 --------------------------------------------------
    expect("sysv classify {double; long long}", sysv_classify(S_DL), ("SSE", "INTEGER"))
    expect("sysv classify {float x4}", sysv_classify(S_F4), ("SSE", "SSE"))
    expect("sysv classify {double x4}", sysv_classify(S_D4), MEM)
    expect("sysv classify {long long x3}", sysv_classify(S_L3), MEM)
    expect("sysv classify {int; float}", sysv_classify(S_IF), ("INTEGER",))
    expect("sysv classify __int128", sysv_classify(I128), ("INTEGER", "INTEGER"))
    expect("sysv classify __float128", sysv_classify(F128), ("SSE", "SSEUP"))
    expect("sysv classify long double", sysv_classify(LDOUBLE), ("X87", "X87UP"))
    expect("sysv classify {long double}", sysv_classify(S_LD), ("X87", "X87UP"))
    expect("sysv classify packed {char; long long}", sysv_classify(S_PK), MEM)
    expect("sysv classify {char; __int128}", sysv_classify(S_CI), MEM)
    expect("sysv classify empty struct", sysv_classify(S_E), ())
    expect("sysv classify __m256", sysv_classify(M256), ("SSE", "SSEUP", "SSEUP", "SSEUP"))
    # The psABI's own worked example (figures "Parameter Passing Example" and
    # "Register Allocation Example"):
    #   func(int e, int f, structparm s, int g, int h, long double ld,
    #        double m, __m256 y, __m512 z, double n, int i, int j, int k)
    psabi_example = [INT, INT, S_PARM, INT, INT, LDOUBLE, DOUBLE, M256, M512, DOUBLE, INT, INT, INT]
    expect("sysv psABI worked example", sysv_args(psabi_example),
           ["rdi", "rsi", "rdx+xmm0", "rcx", "r8", "stack@0", "xmm1", "xmm2", "xmm3", "xmm4", "r9",
            "stack@16", "stack@24"])
    # All-or-nothing rule: the third __int128 needs two registers, only r9 is
    # free, so it goes to the stack whole; r9 stays available for `d`.
    expect("sysv (char, i128, i128, i128, long long)", sysv_args([CHAR, I128, I128, I128, LLONG]),
           ["rdi", "rsi+rdx", "rcx+r8", "stack@0", "r9"])
    expect("sysv (double x8, {double; long long}, long long)", sysv_args([DOUBLE] * 8 + [S_DL, LLONG]),
           [f"xmm{i}" for i in range(8)] + ["stack@0", "rdi"])
    expect("sysv (long double) / ({long double})", sysv_args([LDOUBLE]) + sysv_args([S_LD]), ["stack@0", "stack@0"])
    expect("sysv (empty, int)", sysv_args([S_E, INT]), ["ignored", "rdi"])
    expect("sysv (int x7, i128): stack alignment", sysv_args([INT] * 7 + [I128]),
           SYSV_INT + ["stack@0", "stack@16"])
    expect("sysv returns",
           [sysv_ret(t) for t in (S_DL, S_F4, S_L3, I128, LDOUBLE, S_LD, S_I1, S_D2, DOUBLE)],
           ["xmm0+rax", "xmm0+xmm1", "sret(rdi)->rax", "rax+rdx", "st0", "st0", "rax+rdx", "xmm0+xmm1", "xmm0"])
    expect("sysv sret consumes rdi", sysv_args([INT], ret=S_L3), ["rsi"])

    # ---- Microsoft x64 ----------------------------------------------------
    # Examples 1-3 of the Microsoft "x64 calling convention" page.
    expect("win64 doc example 1", win64_args([INT] * 6), ["rcx", "rdx", "r8", "r9", "stack@32", "stack@40"])
    expect("win64 doc example 2", win64_args([FLOAT, DOUBLE, FLOAT, DOUBLE, FLOAT, FLOAT]),
           ["xmm0", "xmm1", "xmm2", "xmm3", "stack@32", "stack@40"])
    expect("win64 doc example 3", win64_args([INT, DOUBLE, INT, FLOAT, INT, FLOAT]),
           ["rcx", "xmm1", "r8", "xmm3", "stack@32", "stack@40"])
    expect("win64 ({double; long long}, double, {ll x3}, int, i128, {int; float})",
           win64_args([S_DL, DOUBLE, S_L3, INT, I128, S_IF]),
           ["&rcx", "xmm1", "&r8", "r9", "&stack@32", "stack@40"])
    expect("win64 {char x3} is not 1, 2, 4 or 8 bytes", win64_args([S_C3]), ["&rcx"])
    expect("win64 variadic double is duplicated", win64_args([INT, DOUBLE], n_named=1), ["rcx", "xmm1=rdx"])
    expect("win64 returns", [win64_ret(t) for t in (S_DL, S_IF, S_L3, I128, DOUBLE, LLONG)],
           ["sret(rcx)->rax", "rax", "sret(rcx)->rax", "xmm0", "xmm0", "rax"])
    expect("win64 sret shifts arguments", win64_args([INT, DOUBLE], ret=S_L3), ["rdx", "xmm2"])

    # ---- AAPCS64 ------------------------------------------------------------
    expect("aapcs64 HFA detection", [a64_hfa(t) for t in (S_F4, S_D4, S_D2, S_IF, S_DL, S_LD)], [4, 4, 2, None, None, 1])
    expect("aapcs64 ({float x4}) / ({double x4})", a64_args([S_F4]) + a64_args([S_D4]), ["v0+v1+v2+v3"] * 2)
    expect("aapcs64 ({double; long long}) / ({int; float})", a64_args([S_DL]) + a64_args([S_IF]), ["x0+x1", "x0"])
    expect("aapcs64 ({long long x3}) by reference", a64_args([S_L3]), ["&x0"])
    expect("aapcs64 (int, __int128): even register rule", a64_args([INT, I128]), ["x0", "x2+x3"])
    expect("darwin  (int, __int128): no even register rule", a64_args([INT, I128], "darwin"), ["x0", "x1+x2"])
    expect("aapcs64 (int, {__int128})", a64_args([INT, S_I1]), ["x0", "x2+x3"])
    expect("aapcs64 (int x7, __int128, int)", a64_args([INT] * 7 + [I128, INT]),
           [f"x{i}" for i in range(7)] + ["stack@0", "stack@16"])
    expect("aapcs64 (double x6, {double x4}, double)", a64_args([DOUBLE] * 6 + [S_D4, DOUBLE]),
           [f"v{i}" for i in range(6)] + ["stack@0", "stack@32"])
    expect("aapcs64 (long double) is binary128 in v0", a64_args([LDOUBLE]), ["v0"])
    expect("aapcs64 (int x8, int, int): 8-byte stack slots", a64_args([INT] * 10)[8:], ["stack@0", "stack@8"])
    expect("darwin  (int x8, int, int): natural-size slots", a64_args([INT] * 10, "darwin")[8:], ["stack@0", "stack@4"])
    expect("darwin  variadic arguments all on the stack", a64_args([INT, INT, DOUBLE], "darwin", n_named=1),
           ["x0", "stack@0", "stack@8"])
    expect("aapcs64 returns", [a64_ret(t) for t in (S_DL, S_F4, S_L3, I128, S_D4, LDOUBLE)],
           ["x0+x1", "v0+v1+v2+v3", "indirect(x8)", "x0+x1", "v0+v1+v2+v3", "v0"])

    # ---- va_list ----------------------------------------------------------
    seq = [INT, DOUBLE, LLONG, LDOUBLE, S_DL, I128, INT] + [DOUBLE] * 7
    expect("sysv va_list transitions", [s[:3] for s in sysv_va_sim([INT], seq)],
           [(8, 48, 0), (16, 48, 0), (16, 64, 0), (24, 64, 0), (24, 64, 16), (32, 80, 16), (48, 80, 16),
            (48, 80, 24), (48, 96, 24), (48, 112, 24), (48, 128, 24), (48, 144, 24), (48, 160, 24),
            (48, 176, 24), (48, 176, 32)])
    expect("sysv va_list: struct needs both classes or neither",
           [s[:3] for s in sysv_va_sim([INT] * 6, [S_DL, DOUBLE])], [(48, 48, 0), (48, 48, 16), (48, 64, 16)])
    expect("sysv default argument promotions", [default_argument_promotion(t).c for t in (CHAR, SHORT, FLOAT, INT)],
           ["int", "int", "double", "int"])
    # One named general-register argument (x0). x1 and x2 take the two ints;
    # the __int128 has 16-byte alignment, so __gr_offs is rounded from -40 up
    # to -32 (x3 is skipped) and x4:x5 are consumed; the 24-byte struct is
    # fetched as a pointer (x6); the next int takes x7; the last one is on
    # the stack.
    expect("aapcs64 va_list transitions",
           [s[:3] for s in a64_va_sim(1, 0, [INT, DOUBLE, INT, I128, S_F4, S_L3, INT, INT])],
           [(-56, -128, 0), (-48, -128, 0), (-48, -112, 0), (-40, -112, 0), (-16, -112, 0), (-16, -48, 0),
            (-8, -48, 0), (0, -48, 0), (0, -48, 8)])

    # ---- integer conversions ------------------------------------------------
    lp64, llp64, a64 = (dict(hazards(dm)) for dm in DATA_MODELS.values())
    expect("promotion: ~(unsigned char)0xFF", lp64["~(unsigned char)0xFF"], -256)
    expect("promotion: -1 < 1u", [m["-1 < 1u"] for m in (lp64, llp64, a64)], [0, 0, 0])
    expect("promotion: -1L < 1u flips with the data model", [m["-1L < 1u"] for m in (lp64, llp64, a64)], [1, 0, 1])
    expect("promotion: unsigned short difference is negative", lp64["((unsigned short)1 - (unsigned short)2) < 0"], 1)
    expect("promotion: unsigned int difference is not", lp64["(1u - 2u) < 0"], 0)
    expect("promotion: (unsigned short)0xFFFF + 1", lp64["(unsigned short)0xFFFF + 1"], 65536)
    expect("promotion: 0xFFFFFFFFu + 1", lp64["0xFFFFFFFFu + 1"], 0)
    expect("promotion: (char)0xFF == 0xFF flips with char signedness",
           [m["(char)0xFF == 0xFF"] for m in (lp64, llp64, a64)], [0, 0, 1])
    expect("promotion: unsigned short product overflows int",
           lp64["(unsigned short)0xFFFF * (unsigned short)0xFFFF"], "UB")
    expect("promotion: unsigned int product wraps", lp64["0xFFFFu * 0xFFFFu"], 0xFFFE0001)


def divergence_matrix():
    rows = [
        ("{double; long long}", S_DL), ("{float x4}", S_F4), ("{double x4}", S_D4), ("{long long x3}", S_L3),
        ("{int; float}", S_IF), ("__int128", I128), ("long double", LDOUBLE), ("{char; char; char}", S_C3),
    ]
    out = []
    for label, t in rows:
        out.append({
            "type": label,
            "sysv_arg": sysv_args([t])[0], "sysv_ret": sysv_ret(t),
            "win64_arg": win64_args([t])[0], "win64_ret": win64_ret(t),
            "aapcs64_arg": a64_args([t])[0], "aapcs64_ret": a64_ret(t),
        })
    return out


# --------------------------------------------------------------------------
# Optional compiler cross-check (x86-64 System V hosts only)
# --------------------------------------------------------------------------

C_PRELUDE = r"""
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
"""


def c_typedefs(types):
    seen, out = set(), []

    def emit(t):
        if isinstance(t, Struct) and t.name not in seen:
            for _, ft in t.fields:
                emit(ft)
            seen.add(t.name)
            body = " ".join(f"{c_name(ft)} {fn};" for fn, ft in t.fields)
            attr = " __attribute__((packed))" if t.packed else ""
            out.append(f"typedef struct{attr} {{ {body} }} {t.name};")

    for t in types:
        emit(t)
    return "\n".join(out)


def c_name(t):
    return t.c if isinstance(t, Prim) else t.name


SYSV_ARG_SIGS = [
    ("a_dl", [S_DL]), ("a_f4", [S_F4]), ("a_d4", [S_D4]), ("a_l3", [S_L3]), ("a_if", [S_IF]),
    ("a_i128x3", [CHAR, I128, I128, I128, LLONG]), ("a_sse_full", [DOUBLE] * 8 + [S_DL, LLONG]),
    ("a_ld", [LDOUBLE, INT]), ("a_sld", [S_LD, INT]), ("a_pk", [S_PK, INT]), ("a_ci", [S_CI, INT]),
    ("a_empty", [S_E, INT]), ("a_i7_i128", [INT] * 7 + [I128]), ("a_i1", [INT, S_I1]),
    ("a_parm", [INT, INT, S_PARM, INT, INT, LDOUBLE, DOUBLE, DOUBLE, INT, INT, INT]),
    ("a_f128", [F128, FLOAT, INT]),
]
SYSV_RET_SIGS = [("r_dl", S_DL), ("r_f4", S_F4), ("r_l3", S_L3), ("r_i128", I128), ("r_ld", LDOUBLE),
                 ("r_sld", S_LD), ("r_i1", S_I1), ("r_d2", S_D2), ("r_if", S_IF), ("r_d4", S_D4)]
MS_ARG_SIGS = [
    ("m_mix", [S_DL, DOUBLE, S_L3, INT, I128, S_IF]), ("m_ints", [INT] * 6),
    ("m_flts", [FLOAT, DOUBLE, FLOAT, DOUBLE, FLOAT, FLOAT]), ("m_c3", [S_C3, S_IF, S_F4, S_D2]),
]
MS_RET_SIGS = [("mr_dl", S_DL), ("mr_if", S_IF), ("mr_l3", S_L3), ("mr_i128", I128), ("mr_d", DOUBLE),
               ("mr_ll", LLONG)]
ALL_TYPES = [S_DL, S_F4, S_D4, S_L3, S_IF, S_LD, S_PK, S_E, S_CI, S_I1, S_PARM, S_C3, S_D2]


def gen_callee_c():
    lines = [C_PRELUDE, c_typedefs(ALL_TYPES),
             "unsigned char abi_out[2048]; unsigned long abi_outn; unsigned char abi_pat[64];",
             "static void rec(const void *p, unsigned long n) { memcpy(abi_out + abi_outn, p, n); abi_outn += n; }"]
    for prefix, sigs in (("", SYSV_ARG_SIGS), ("__attribute__((ms_abi)) ", MS_ARG_SIGS)):
        for name, args in sigs:
            params = ", ".join(f"{c_name(t)} a{i}" for i, t in enumerate(args))
            body = " ".join(f"rec(&a{i}, sizeof a{i});" for i in range(len(args)))
            lines.append(f"{prefix}void {name}({params}) {{ {body} }}")
    for prefix, sigs in (("", SYSV_RET_SIGS), ("__attribute__((ms_abi)) ", MS_RET_SIGS)):
        for name, t in sigs:
            lines.append(f"{prefix}{c_name(t)} {name}(void) {{ {c_name(t)} v; memcpy(&v, abi_pat, sizeof v); return v; }}")
    return "\n".join(lines) + "\n"


TRAMPOLINES = r"""
/* Call fn with poisoned return registers and a candidate hidden-result buffer,
   then record rax, rdx, xmm0, xmm1 and the number of values left on the x87
   stack. Entered with the System V convention: fn, buffer, out. */
__asm__(
"    .text\n"
"    .globl abi_observe_ret\n"
"abi_observe_ret:\n"
"    pushq %rbx\n"
"    movq %rdx, %rbx\n"
"    movq %rdi, %r11\n"
"    movq %rsi, %rdi\n"
"    movabsq $0x5a5a5a5a5a5a5a5a, %rax\n"
"    movq %rax, %rdx\n"
"    movq %rax, %xmm0\n"
"    movq %rax, %xmm1\n"
"    fninit\n"
"    call *%r11\n"
"    movq %rax, 0(%rbx)\n"
"    movq %rdx, 8(%rbx)\n"
"    movq %xmm0, 16(%rbx)\n"
"    movq %xmm1, 24(%rbx)\n"
"    xorl %eax, %eax\n"
"    fnstsw %ax\n"
"    movq %rax, 32(%rbx)\n"
"    fninit\n"
"    popq %rbx\n"
"    ret\n"
"    .globl abi_observe_ret_ms\n"
"abi_observe_ret_ms:\n"
"    pushq %rbx\n"
"    subq $48, %rsp\n"
"    movq %rdx, %rbx\n"
"    movq %rdi, %r11\n"
"    movq %rsi, %rcx\n"
"    movabsq $0x5a5a5a5a5a5a5a5a, %rax\n"
"    movq %rax, %rdx\n"
"    movq %rax, %xmm0\n"
"    movq %rax, %xmm1\n"
"    fninit\n"
"    call *%r11\n"
"    movq %rax, 0(%rbx)\n"
"    movq %rdx, 8(%rbx)\n"
"    movq %xmm0, 16(%rbx)\n"
"    movq %xmm1, 24(%rbx)\n"
"    xorl %eax, %eax\n"
"    fnstsw %ax\n"
"    movq %rax, 32(%rbx)\n"
"    fninit\n"
"    addq $48, %rsp\n"
"    popq %rbx\n"
"    ret\n"
);
extern void abi_observe_ret(void *fn, void *buf, uint64_t *out);
extern void abi_observe_ret_ms(void *fn, void *buf, uint64_t *out);
"""


def gen_main_c(with_ms_args):
    L = [C_PRELUDE, TRAMPOLINES,
         "extern unsigned char abi_out[2048]; extern unsigned long abi_outn; extern unsigned char abi_pat[64];",
         "typedef void (*sysv_fn)(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,"
         "double,double,double,double,double,double,double,double,"
         "uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t,uint64_t);",
         "static uint64_t sent(unsigned base, unsigned k) { uint64_t v = 0; "
         "for (unsigned j = 0; j < 8; j++) v |= (uint64_t)(base + 8 * k + j) << (8 * j); return v; }",
         "static double dbl(uint64_t x) { double d; memcpy(&d, &x, 8); return d; }",
         "static void dump(const char *tag, const char *name) { printf(\"%s %s \", tag, name); "
         "for (unsigned long i = 0; i < abi_outn; i++) printf(\"%02x\", abi_out[i]); printf(\"\\n\"); abi_outn = 0; }",
         "static void hex(const unsigned char *p, unsigned n) { for (unsigned i = 0; i < n; i++) printf(\"%02x\", p[i]); }",
         "static unsigned char bufs[7][32];"]
    if with_ms_args:
        L.append("typedef void (__attribute__((ms_abi)) *ms_fn)(...);")
    names = [n for n, _ in SYSV_ARG_SIGS + MS_ARG_SIGS + SYSV_RET_SIGS + MS_RET_SIGS]
    L.append("extern void " + ", ".join(f"{n}(void)" for n in names) + ";")
    L.append("int main(void) {")
    L.append("  void *volatile vp; uint64_t o[5]; unsigned char sret[64];")
    L.append("  for (unsigned i = 0; i < 64; i++) abi_pat[i] = 0xA0 + i;")
    L.append("  for (unsigned k = 0; k < 7; k++) for (unsigned i = 0; i < 32; i++) bufs[k][i] = ((k + 1) << 5) | i;")
    for name, _ in SYSV_ARG_SIGS:
        ints = ", ".join(f"sent(0x10, {k})" for k in range(6))
        dbls = ", ".join(f"dbl(sent(0x40, {k}))" for k in range(8))
        stk = ", ".join(f"sent(0x80, {k})" for k in range(12))
        L.append(f"  vp = (void *){name}; abi_outn = 0; ((sysv_fn)vp)({ints}, {dbls}, {stk}); dump(\"ARGS\", \"{name}\");")
    for name, _ in SYSV_RET_SIGS:
        L.append(f"  memset(sret, 0, 64); abi_observe_ret((void *){name}, sret, o); "
                 f"printf(\"RET {name} %016llx %016llx %016llx %016llx %u %d \", (unsigned long long)o[0], "
                 "(unsigned long long)o[1], (unsigned long long)o[2], (unsigned long long)o[3], "
                 "(unsigned)((8 - ((o[4] >> 11) & 7)) & 7), o[0] == (uint64_t)(uintptr_t)sret); hex(sret, 64); printf(\"\\n\");")
    if with_ms_args:
        for name, _ in MS_ARG_SIGS:
            args = ", ".join(f"dbl((uint64_t)(uintptr_t)bufs[{k}])" for k in range(7))
            L.append(f"  vp = (void *){name}; abi_outn = 0; ((ms_fn)vp)({args}); "
                     "printf(\"MSADDR\"); for (unsigned k = 0; k < 7; k++) "
                     "printf(\" %016llx\", (unsigned long long)(uintptr_t)bufs[k]); printf(\"\\n\"); "
                     f"dump(\"MSARGS\", \"{name}\");")
    for name, _ in MS_RET_SIGS:
        L.append(f"  memset(sret, 0, 64); abi_observe_ret_ms((void *){name}, sret, o); "
                 f"printf(\"MSRET {name} %016llx %016llx %016llx %016llx %u %d \", (unsigned long long)o[0], "
                 "(unsigned long long)o[1], (unsigned long long)o[2], (unsigned long long)o[3], "
                 "(unsigned)((8 - ((o[4] >> 11) & 7)) & 7), o[0] == (uint64_t)(uintptr_t)sret); hex(sret, 64); printf(\"\\n\");")
    L.append("  return 0;\n}")
    return "\n".join(L) + "\n"


VA_SEQ = [INT, DOUBLE, LLONG, LDOUBLE, S_DL, I128, INT] + [DOUBLE] * 7
VA_ARGS = ["1", "2.0", "3LL", "(long double)4", "(S_DL){5.0, 6}", "(__int128)7", "8"] + ["9.0"] * 7


def gen_misc_c():
    hz = hazards(DATA_MODELS["LP64 signed-char (System V AMD64)"])
    L = [C_PRELUDE, "#include <stdarg.h>", c_typedefs(ALL_TYPES)]
    L.append("static void st(va_list ap, char *base) { printf(\" %u,%u,%ld\", ap[0].gp_offset, ap[0].fp_offset, "
             "(long)((char *)ap[0].overflow_arg_area - base)); }")
    L.append("static void vprobe(int n, ...) { va_list ap; va_start(ap, n); char *base = ap[0].overflow_arg_area; "
             "printf(\"VA\"); st(ap, base);")
    for t in VA_SEQ:
        L.append(f"  (void)va_arg(ap, {c_name(t)}); st(ap, base);")
    L.append("  va_end(ap); printf(\"\\n\"); }")
    L.append("static void vprobe6(int a, int b, int c, int d, int e, int f, ...) { va_list ap; va_start(ap, f); "
             "char *base = ap[0].overflow_arg_area; printf(\"VA6\"); st(ap, base); (void)va_arg(ap, S_DL); st(ap, base); "
             "(void)va_arg(ap, double); st(ap, base); va_end(ap); printf(\"\\n\"); }")
    L.append("static void __attribute__((ms_abi)) msv(int n, ...) { __builtin_ms_va_list ap; __builtin_ms_va_start(ap, n); "
             "char *base = (char *)ap; printf(\"MSVA %ld\", (long)((char *)ap - base));")
    for t in (INT, DOUBLE, S_IF, LLONG):
        L.append(f"  (void)__builtin_va_arg(ap, {c_name(t)}); printf(\" %ld\", (long)((char *)ap - base));")
    L.append("  __builtin_ms_va_end(ap); printf(\"\\n\"); }")
    # A 16-byte aggregate is passed by reference under this convention, so a
    # conforming va_arg consumes one 8-byte slot and yields the original value.
    L.append("static void __attribute__((ms_abi)) msv16(int n, ...) { __builtin_ms_va_list ap; "
             "__builtin_ms_va_start(ap, n); char *base = (char *)ap; S_DL s = __builtin_va_arg(ap, S_DL); "
             "printf(\"MSVA16 %ld %d\\n\", (long)((char *)ap - base), s.a == 3.0 && s.b == 4); "
             "__builtin_ms_va_end(ap); }")
    for name, body, _, _, _ in BITFIELD_SPECIMENS:
        L.append(f"struct {name} {{ {body} }}; struct __attribute__((ms_struct)) {name}_ms {{ {body} }};")
    L.append("struct PlainBF { int f : 3; };")
    L.append("int main(void) {")
    L.append(f"  vprobe(0, {', '.join(VA_ARGS)});")
    L.append("  vprobe6(1, 2, 3, 4, 5, 6, (S_DL){1.0, 2}, 3.0);")
    L.append("  msv(0, 1, 2.0, (S_IF){3, 4.0f}, 6LL);")
    L.append("  msv16(0, (S_DL){3.0, 4});")
    for i, (expr, _) in enumerate(hz):
        if _ == "UB":
            continue  # never evaluate an expression the model flags as undefined
        L.append(f"  printf(\"HZ {i} %lld\\n\", (long long)({expr}));")
    for t in ALL_TYPES + [I128, LDOUBLE, LONG]:
        L.append(f"  printf(\"LAYOUT {c_name(t)}|%zu|%zu\\n\", sizeof({c_name(t)}), _Alignof({c_name(t)}));")
    for name, _, _, _, _ in BITFIELD_SPECIMENS:
        L.append(f"  printf(\"BF {name} %zu %zu %zu %zu\\n\", sizeof(struct {name}), _Alignof(struct {name}), "
                 f"sizeof(struct {name}_ms), _Alignof(struct {name}_ms));")
    L.append("  { struct PlainBF s; s.f = 3; s.f += 4; printf(\"PLAINBF %d\\n\", s.f); }")
    L.append("  printf(\"CHARSIGN %d\\n\", (char)0xFF < 0);")
    L.append("  return 0;\n}")
    return "\n".join(L) + "\n"


class CrossCheck:
    def __init__(self, cc, keep):
        self.cc, self.keep = cc, keep
        self.results = []  # (label, ok, detail)
        self.notes = []

    def ok(self, label, cond, detail=""):
        self.results.append((label, bool(cond), detail))

    def run(self, cmd, cwd):
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=120)

    def build(self, tmp, name, sources, flags):
        objs = []
        for src, extra in sources:
            obj = src[:-2] + ".o"
            r = self.run([self.cc, "-w", "-c", src, "-o", obj] + flags + extra, tmp)
            if r.returncode:
                return None, r.stderr.strip().splitlines()[:3]
            objs.append(obj)
        r = self.run([self.cc] + objs + ["-o", name], tmp)
        if r.returncode:
            return None, r.stderr.strip().splitlines()[:3]
        r = self.run([os.path.join(tmp, name)], tmp)
        if r.returncode:
            return None, [f"exit status {r.returncode}"]
        return r.stdout.splitlines(), None

    def execute(self):
        tmp = tempfile.mkdtemp(prefix="c_abi_probe_")
        try:
            self._execute(tmp)
        finally:
            if self.keep:
                self.notes.append(f"kept build directory {tmp}")
            else:
                shutil.rmtree(tmp, ignore_errors=True)

    def _write(self, tmp, name, text):
        with open(os.path.join(tmp, name), "w", encoding="utf-8") as f:
            f.write(text)

    def _execute(self, tmp):
        self._write(tmp, "callee.c", gen_callee_c())
        with_ms = True
        self._write(tmp, "main.c", gen_main_c(True))
        srcs = [("callee.c", ["-O2", "-fno-inline"]), ("main.c", ["-O0", "-std=gnu2x"])]
        lines, err = self.build(tmp, "abi", srcs, [])
        if lines is None:
            with_ms = False
            self.notes.append("variadic-prototype ms_abi call unavailable; Win64 argument check skipped: " + "; ".join(err))
            self._write(tmp, "main.c", gen_main_c(False))
            lines, err = self.build(tmp, "abi", [srcs[0], ("main.c", ["-O0"])], [])
        if lines is None:
            self.ok("build calling-convention harness", False, "; ".join(err))
        else:
            self.check_calls(lines, with_ms)
        self._write(tmp, "misc.c", gen_misc_c())
        lines, err = self.build(tmp, "misc", [("misc.c", ["-O0"])], [])
        if lines is None:
            self.ok("build va_list/promotion/layout harness", False, "; ".join(err))
        else:
            self.check_misc(lines)
        self.check_variants(tmp)

    # ---- argument and return observation ---------------------------------
    @staticmethod
    def _src(b):
        if 0x10 <= b < 0x40:
            return ("I", (b - 0x10) // 8, (b - 0x10) % 8)
        if 0x40 <= b < 0x80:
            return ("X", (b - 0x40) // 8, (b - 0x40) % 8)
        if 0x80 <= b < 0xE0:
            return ("S", b - 0x80)
        return ("?", b)

    @staticmethod
    def _sig_bytes(abi, lay):
        """Offsets of bytes that carry data (x87 values use 10 of 16 bytes)."""
        out = []
        for off, p in lay.leaves:
            size, _, k = PRIMS[abi][p.c]
            out += range(off, off + (10 if k == "x87" else size))
        return out

    def check_calls(self, lines, with_ms):
        rows = {}
        msaddr = None
        for ln in lines:
            parts = ln.split()
            if parts[0] == "MSADDR":
                msaddr = [int(x, 16) for x in parts[1:]]
            elif parts[0] == "MSARGS":
                rows[("MSARGS", parts[1])] = (msaddr, bytes.fromhex(parts[2]) if len(parts) > 2 else b"")
            elif parts[0] == "ARGS":
                rows[("ARGS", parts[1])] = bytes.fromhex(parts[2]) if len(parts) > 2 else b""
            else:
                rows[(parts[0], parts[1])] = parts[2:]
        for name, args in SYSV_ARG_SIGS:
            data, pos, bad = rows[("ARGS", name)], 0, []
            detail, _ = sysv_args_detail(args)
            for i, (t, d) in enumerate(zip(args, detail)):
                lay = layout("sysv", t)
                chunk = data[pos:pos + lay.size]
                pos += lay.size
                if d["kind"] == "ignored":
                    continue
                for o in self._sig_bytes("sysv", lay):
                    got = self._src(chunk[o])
                    if d["kind"] == "stack":
                        want = ("S", d["off"] + o)
                    else:
                        e = d["eb"][o // 8]
                        if e is None or e[0] == "XUP":
                            continue  # upper half of a vector register: not observable here
                        want = (e[0], e[1], o % 8)
                    if got != want:
                        bad.append(f"arg{i}+{o}: observed {got}, model {want}")
            self.ok(f"sysv args {name}: {' '.join(sysv_args(args))}", not bad, "; ".join(bad[:3]))
        for name, t in SYSV_RET_SIGS:
            self.ok(f"sysv return {name}: {sysv_ret(t)}", *self._check_ret(rows[("RET", name)], "sysv", t))
        if with_ms:
            for name, args in MS_ARG_SIGS:
                addr, data = rows[("MSARGS", name)]
                pos, bad, model = 0, [], win64_args(args)
                for i, (t, loc) in enumerate(zip(args, model)):
                    lay = layout("sysv", t)  # the host compiler's own type sizes
                    chunk = data[pos:pos + lay.size]
                    pos += lay.size
                    slot = i  # no hidden result pointer in these signatures
                    if loc.startswith("&"):
                        want = bytes(((slot + 1) << 5) | o for o in range(lay.size))
                        sig = self._sig_bytes("sysv", lay)
                    else:
                        want = addr[slot].to_bytes(8, "little")[:lay.size]
                        sig = range(lay.size)
                    if any(chunk[o] != want[o] for o in sig):
                        bad.append(f"arg{i} model {loc}: observed {chunk.hex()}")
                self.ok(f"ms_abi args {name}: {' '.join(model)}", not bad, "; ".join(bad[:3]))
        for name, t in MS_RET_SIGS:
            self.ok(f"ms_abi return {name}: {win64_ret(t)}", *self._check_ret(rows[("MSRET", name)], "win64", t))

    def _check_ret(self, row, abi, t):
        rax, rdx, x0, x1 = (int(v, 16).to_bytes(8, "little") for v in row[:4])
        depth, sret_is_rax, buf = int(row[4]), int(row[5]), bytes.fromhex(row[6])
        lay = layout("sysv", t)
        regs = {"rax": rax, "rdx": rdx, "xmm0": x0, "xmm1": x1}
        pat = bytes(0xA0 + i for i in range(64))
        sig = self._sig_bytes("sysv", lay)
        if abi == "sysv":
            d = sysv_ret_detail(t)
            want_sret = d["kind"] == "sret"
            eb = [] if want_sret else d["eb"]
        else:
            loc = win64_ret(t)
            want_sret = loc.startswith("sret")
            eb = [] if want_sret else [loc, None]
        bad = []
        if want_sret:
            if not sret_is_rax or any(buf[o] != pat[o] for o in sig):
                bad.append("hidden result buffer not written or its address not returned in rax")
        else:
            if any(buf):
                bad.append("hidden result buffer unexpectedly written")
            for o in sig:
                e = eb[o // 8] if o // 8 < len(eb) else None
                if e in regs and regs[e][o % 8] != pat[o]:
                    bad.append(f"byte {o}: {e} holds {regs[e].hex()}")
                    break
        want_depth = 1 if (not want_sret and "st0" in eb) else 0
        if depth != want_depth:
            bad.append(f"x87 stack depth {depth}, model {want_depth}")
        return not bad, "; ".join(bad)

    # ---- va_list, promotions, layout ----------------------------------------
    def check_misc(self, lines):
        tag = {}
        for ln in lines:
            k, _, rest = ln.partition(" ")
            tag.setdefault(k, []).append(rest)
        got = [tuple(int(x) for x in s.split(",")) for s in tag["VA"][0].split()]
        want = [s[:3] for s in sysv_va_sim([INT], VA_SEQ)]
        self.ok("sysv va_list gp_offset/fp_offset/overflow transitions (16 states)", got == want, f"observed {got}")
        got = [tuple(int(x) for x in s.split(",")) for s in tag["VA6"][0].split()]
        want = [s[:3] for s in sysv_va_sim([INT] * 6, [S_DL, DOUBLE])]
        self.ok("sysv va_list mixed-class struct falls to overflow area when gp is exhausted", got == want, f"observed {got}")
        got = [int(x) for x in tag["MSVA"][0].split()]
        self.ok("ms_abi va_list is a pointer advancing 8 bytes per argument (types of at most 8 bytes)",
                got == [0, 8, 16, 24, 32], f"observed {got}")
        adv, intact = (int(x) for x in tag["MSVA16"][0].split())
        verdict = "consistent with by-reference passing" if (adv, intact) == (8, 1) else \
            "INCONSISTENT with this compiler's own by-reference call sequence"
        self.notes.append(f"ms_abi va_arg of a 16-byte struct advanced {adv} bytes and "
                          f"{'returned' if intact else 'did not return'} the passed value: {verdict}")
        dm = DATA_MODELS["LP64 signed-char (System V AMD64)"]
        hz, bad = hazards(dm), []
        for row in tag["HZ"]:
            i, v = row.split()
            if hz[int(i)][1] != int(v):
                bad.append(f"{hz[int(i)][0]} = {v}, model {hz[int(i)][1]}")
        self.ok(f"integer conversion expressions ({len(tag['HZ'])} evaluated, LP64, signed char)", not bad, "; ".join(bad))
        bad = []
        types = {c_name(t): t for t in ALL_TYPES + [I128, LDOUBLE, LONG]}
        for row in tag["LAYOUT"]:
            name, size, align = row.split("|")
            lay = layout("sysv", types[name])
            if (lay.size, lay.align) != (int(size), int(align)):
                bad.append(f"{name}: compiler {size}/{align}, model {lay.size}/{lay.align}")
        self.ok(f"sizeof/_Alignof of {len(tag['LAYOUT'])} specimen types", not bad, "; ".join(bad))
        bad = []
        for row in tag["BF"]:
            name, s, a, ms, ma = row.split()
            spec = next(x for x in BITFIELD_SPECIMENS if x[0] == name)
            if (int(s), int(a)) != bitfield_layout("sysv", spec[2]):
                bad.append(f"{name} native {s}/{a}")
            if (int(ms), int(ma)) != bitfield_layout("ms", spec[2]):
                bad.append(f"{name} ms_struct {ms}/{ma}")
        self.ok("bit-field specimens: native rule and ms_struct rule", not bad, "; ".join(bad))
        plain = int(tag["PLAINBF"][0])
        self.notes.append(f"plain `int f:3` holding bit pattern 0b111 reads back as {plain} "
                          f"({'signed' if plain < 0 else 'unsigned'} interpretation by this compiler)")
        self.ok("host char is signed (psABI: char is a signed byte)", tag["CHARSIGN"][0] == "1")

    def check_variants(self, tmp):
        # AAPCS64-style unsigned char, emulated with -funsigned-char.
        self._write(tmp, "uc.c", "_Static_assert(((char)0xFF == 0xFF) == 1, \"\"); _Static_assert(((char)0xFF < 0) == 0, \"\");\n")
        r = self.run([self.cc, "-w", "-fsyntax-only", "-funsigned-char", "uc.c"], tmp)
        if r.returncode == 0:
            self.ok("-funsigned-char: (char)0xFF == 0xFF holds, as modelled for AAPCS64", True)
        else:
            self.notes.append("-funsigned-char variant not checked")
        # 32-bit long, emulated with -m32 (same conversion ranks as LLP64 for this expression).
        self._write(tmp, "l32.c", "_Static_assert(sizeof(long) == 4, \"\"); _Static_assert((-1L < 1u) == 0, \"\");\n")
        r = self.run([self.cc, "-w", "-fsyntax-only", "-m32", "l32.c"], tmp)
        if r.returncode == 0:
            self.ok("-m32 (32-bit long): -1L < 1u is false, as modelled for LLP64", True)
        else:
            self.notes.append("-m32 variant not checked (compiler lacks 32-bit support)")


def host_supports_cross_check(cc):
    if not sys.platform.startswith("linux") or platform.machine() not in ("x86_64", "AMD64"):
        return f"host is {sys.platform}/{platform.machine()}, not x86-64 Linux"
    probe = "#if !defined(__x86_64__) || !defined(__LP64__) || defined(_WIN32)\n#error unsupported\n#endif\n"
    r = subprocess.run([cc, "-fsyntax-only", "-x", "c", "-"], input=probe, capture_output=True, text=True)
    return None if r.returncode == 0 else "compiler does not target x86-64 LP64 System V"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--no-cc", action="store_true", help="skip the compiler cross-check")
    ap.add_argument("--cc", default=None, help="C compiler to use (default: cc, gcc or clang from PATH)")
    ap.add_argument("--keep", action="store_true", help="keep generated C sources and binaries")
    ap.add_argument("--json", default=None, help="write machine-readable results to this file")
    ns = ap.parse_args(argv)

    build_model_checks()
    failed = 0
    print("== model checks (expectations transcribed from the specifications) ==")
    for label, got, expected in MODEL_CHECKS:
        ok = got == expected
        failed += not ok
        print(f"{'PASS' if ok else 'FAIL'} {label}" + ("" if ok else f"\n     got      {got}\n     expected {expected}"))
    print(f"model: {len(MODEL_CHECKS) - failed}/{len(MODEL_CHECKS)} checks passed")

    print("\n== divergence matrix: one argument / return value of each type ==")
    matrix = divergence_matrix()
    print(f"{'type':22} {'SysV AMD64 arg':16} {'ret':16} {'Win64 arg':10} {'ret':16} {'AAPCS64 arg':13} ret")
    for r in matrix:
        print(f"{r['type']:22} {r['sysv_arg']:16} {r['sysv_ret']:16} {r['win64_arg']:10} {r['win64_ret']:16} "
              f"{r['aapcs64_arg']:13} {r['aapcs64_ret']}")

    print("\n== integer conversion hazards by data model ==")
    names = list(DATA_MODELS)
    table = [hazards(DATA_MODELS[n]) for n in names]
    print(f"{'expression':52} " + " ".join(f"{n.split(' (')[0]:>20}" for n in names))
    for i, (expr, _) in enumerate(table[0]):
        print(f"{expr:52} " + " ".join(f"{str(t[i][1]):>20}" for t in table))

    cc_report = {"attempted": False, "reason": None, "compiler": None, "results": [], "notes": []}
    cc_failed = 0
    if ns.no_cc:
        cc_report["reason"] = "disabled with --no-cc"
    else:
        cc = ns.cc or next((c for c in ("cc", "gcc", "clang") if shutil.which(c)), None)
        reason = "no C compiler found" if cc is None else host_supports_cross_check(cc)
        if reason:
            cc_report["reason"] = reason
        else:
            version = subprocess.run([cc, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
            chk = CrossCheck(cc, ns.keep)
            chk.execute()
            cc_report.update(attempted=True, compiler=version, results=chk.results, notes=chk.notes)
            cc_failed = sum(1 for _, ok, _ in chk.results if not ok)
    print("\n== compiler cross-check ==")
    if not cc_report["attempted"]:
        print(f"skipped: {cc_report['reason']}")
    else:
        print(f"compiler: {cc_report['compiler']}")
        for label, ok, detail in cc_report["results"]:
            print(f"{'PASS' if ok else 'FAIL'} {label}" + (f"\n     {detail}" if detail and not ok else ""))
        for note in cc_report["notes"]:
            print(f"NOTE {note}")
        n = len(cc_report["results"])
        print(f"compiler: {n - cc_failed}/{n} checks passed")

    if ns.json:
        with open(ns.json, "w", encoding="utf-8") as f:
            json.dump({
                "model_checks": [{"label": l, "ok": g == e} for l, g, e in MODEL_CHECKS],
                "divergence_matrix": matrix,
                "hazards": {n: [[e, v] for e, v in hazards(DATA_MODELS[n])] for n in names},
                "compiler_cross_check": cc_report,
            }, f, indent=2, sort_keys=True)
            f.write("\n")
    status = 1 if failed or cc_failed else 0
    print(f"\nRESULT: {'OK' if status == 0 else 'FAILED'}")
    return status


if __name__ == "__main__":
    sys.exit(main())
