#!/usr/bin/env python3
"""Minimal reader for R .rda/.RData files (serialization versions 2 and 3, XDR).

Standard library only. Supports the subset of SEXP types needed to read the
data frames shipped in the data/ directories of the R packages examined in this
report: NULL, symbols, pairlists, CHARSXP, logical/integer/double/character
vectors, generic vectors (lists / data.frames), reference objects, and the
compact_intseq / wrap_* ALTREP classes that R >= 3.5 writes for row names.

Usage as a library:
    from rda_reader import read_rda, as_columns
    objs = read_rda("omopReferenceSet.rda")       # {name: RObj}
    cols = as_columns(objs["omopReferenceSet"])   # {colname: list}

This is an independent re-implementation of the documented R serialization
format, not R itself.
"""
import bz2
import gzip
import lzma
import struct
import sys

NA_INTEGER = -2147483648


class RObj:
    def __init__(self, sexptype, value, attrs=None):
        self.sexptype = sexptype
        self.value = value
        self.attrs = attrs or {}

    def __repr__(self):
        return f"RObj(type={self.sexptype}, attrs={list(self.attrs)})"


def _decompress(raw):
    if raw[:2] == b"\x1f\x8b":
        return gzip.decompress(raw)
    if raw[:3] == b"BZh":
        return bz2.decompress(raw)
    if raw[:6] == b"\xfd7zXZ\x00":
        return lzma.decompress(raw)
    return raw


class _Reader:
    def __init__(self, buf):
        self.buf = buf
        self.pos = 0
        self.refs = []

    def take(self, n):
        b = self.buf[self.pos:self.pos + n]
        self.pos += n
        return b

    def int(self):
        return struct.unpack(">i", self.take(4))[0]

    def double(self):
        return struct.unpack(">d", self.take(8))[0]

    def string(self, n):
        return self.take(n).decode("utf-8", errors="replace")

    def item(self):
        flags = self.int()
        sexptype = flags & 0xFF
        has_attr = bool(flags & (1 << 9))
        has_tag = bool(flags & (1 << 10))
        if sexptype == 254:  # NILVALUE_SXP
            return None
        if sexptype in (242, 251, 252, 253):  # empty env, unbound, missing, base env
            return RObj(sexptype, None)
        if sexptype == 255:  # REFSXP
            idx = flags >> 8
            if idx == 0:
                idx = self.int()
            return self.refs[idx - 1]
        if sexptype == 1:  # SYMSXP
            name = self.item()
            obj = RObj(1, name)
            self.refs.append(obj)
            return obj
        if sexptype == 9:  # CHARSXP
            n = self.int()
            return None if n == -1 else self.string(n)
        if sexptype in (2, 6):  # LISTSXP / LANGSXP (pairlist)
            out = []
            attrs = self.item() if has_attr else None
            tag = self.item() if has_tag else None
            car = self.item()
            cdr = self.item()
            name = tag.value if isinstance(tag, RObj) and tag.sexptype == 1 else None
            out.append((name, car))
            if isinstance(cdr, RObj) and cdr.sexptype in (2, 6):
                out.extend(cdr.value)
            return RObj(sexptype, out, _attrs(attrs))
        if sexptype == 238:  # ALTREP_SXP
            info = self.item()
            state = self.item()
            attr = self.item()
            cls = info.value[0][1].value if info is not None else "?"
            if cls == "compact_intseq":
                n, start, step = state.value
                return RObj(13, [int(start + i * step) for i in range(int(n))], _attrs(attr))
            if cls == "compact_realseq":
                n, start, step = state.value
                return RObj(14, [start + i * step for i in range(int(n))], _attrs(attr))
            if cls.startswith("wrap_"):
                inner = state.value[0][1]
                return inner
            if cls == "deferred_string":
                return state.value[0][1]
            raise NotImplementedError(f"ALTREP class {cls}")
        if sexptype == 10 or sexptype == 13:  # LGLSXP / INTSXP
            n = self.int()
            vals = list(struct.unpack(f">{n}i", self.take(4 * n)))
            vals = [None if v == NA_INTEGER else v for v in vals]
            if sexptype == 10:
                vals = [None if v is None else bool(v) for v in vals]
            attrs = self.item() if has_attr else None
            return RObj(sexptype, vals, _attrs(attrs))
        if sexptype == 14:  # REALSXP
            n = self.int()
            vals = list(struct.unpack(f">{n}d", self.take(8 * n)))
            attrs = self.item() if has_attr else None
            return RObj(14, vals, _attrs(attrs))
        if sexptype == 16:  # STRSXP
            n = self.int()
            vals = [self.item() for _ in range(n)]
            attrs = self.item() if has_attr else None
            return RObj(16, vals, _attrs(attrs))
        if sexptype in (19, 20):  # VECSXP / EXPRSXP
            n = self.int()
            vals = [self.item() for _ in range(n)]
            attrs = self.item() if has_attr else None
            return RObj(19, vals, _attrs(attrs))
        raise NotImplementedError(f"SEXP type {sexptype} at offset {self.pos}")


def _attrs(pl):
    if pl is None:
        return {}
    return {k: v for k, v in pl.value}


def read_rda(path):
    raw = _decompress(open(path, "rb").read())
    if raw[:5] not in (b"RDX2\n", b"RDX3\n"):
        raise ValueError("not an RDX2/RDX3 file")
    r = _Reader(raw[5:])
    if r.take(2) != b"X\n":
        raise ValueError("only XDR format supported")
    version = r.int()
    r.int()  # writer R version
    r.int()  # min reader version
    if version == 3:
        n = r.int()
        r.string(n)  # native encoding
    top = r.item()
    return {name: obj for name, obj in top.value}


def as_columns(obj):
    """Return {column name: python list} for a data.frame RObj; factors decoded."""
    names = obj.attrs["names"].value
    out = {}
    for name, col in zip(names, obj.value):
        vals = col.value
        levels = col.attrs.get("levels")
        if levels is not None and col.sexptype == 13:
            lv = levels.value
            vals = [None if v is None else lv[v - 1] for v in vals]
        out[name] = vals
    return out


if __name__ == "__main__":
    for p in sys.argv[1:]:
        for name, obj in read_rda(p).items():
            cls = obj.attrs.get("class")
            print(p, name, cls.value if cls else None)
            if cls is not None and "data.frame" in cls.value:
                cols = as_columns(obj)
                n = len(next(iter(cols.values())))
                print("  rows:", n, "cols:", list(cols))
