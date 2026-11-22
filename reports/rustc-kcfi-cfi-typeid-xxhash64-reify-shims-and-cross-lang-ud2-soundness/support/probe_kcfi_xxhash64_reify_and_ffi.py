#!/usr/bin/env python3
"""Real-toolchain probe for rustc/Clang KCFI type identifiers on x86-64 Linux.

Everything this script reports is either computed here in pure Python
(XXH64, the two Itanium type-id encoder models, the collision search) or
observed by running the real tools (rustc, clang, llvm-objdump, and the
binaries they produce).  No expected value is copied into the output: where
a model prediction is compared with a tool observation, both sides and the
comparison result are recorded.

Parts
  A  XXH64(seed 0) known-answer vectors and type-id string hashes.
  B  rustc <-> clang cross-language KCFI: execution (SIGILL or success),
     `!kcfi_type` / `"kcfi"` operand-bundle values from LLVM IR, and the
     machine code of the 16-byte `__cfi_` prefix and the call-site guard.
  C  The reify shim: which functions exist with and without KCFI, their
     KCFI ids, the type-id *strings* (read from `-Zsanitizer=cfi` IR) whose
     hashes those ids are, and execution of both the supported paths and
     the two cross-wired paths.
  D  Differential test of the pure-Python encoder models against
     rustc- and clang-emitted ids over generated signatures.
  E  A pair of distinct function types with equal 32-bit KCFI ids
     (birthday search), confirmed against rustc and executed.
  F  rustc target-modifier gating for mixed sanitizer flags.
  G  LLVM MergeFunctions folding two type-correct functions whose KCFI ids
     differ, and what that does to a type-correct indirect call.

Tools (override with environment variables):
  RUSTC         default "rustc" (a nightly; -Z flags are required)
  CLANG         default "clang-19"
  LLVM_OBJDUMP  default: "llvm-objdump" on PATH, else the copy shipped in
                the rustc sysroot (rustup component llvm-tools)

Usage:
  python3 probe_kcfi_xxhash64_reify_and_ffi.py [--out results.json] [--keep DIR]
Exit status is 0 iff every check listed under "checks" in the output holds.
"""
import argparse
import itertools
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

# --------------------------------------------------------------------------
# XXH64 (seed 0), written from the published algorithm description.
# --------------------------------------------------------------------------
M64 = (1 << 64) - 1
P1 = 0x9E3779B185EBCA87
P2 = 0xC2B2AE3D27D4EB4F
P3 = 0x165667B19E3779F9
P4 = 0x85EBCA77C2B2AE63
P5 = 0x27D4EB2F165667C5


def _rotl(x, r):
    return ((x << r) | (x >> (64 - r))) & M64


def _round(acc, inp):
    return (_rotl((acc + inp * P2) & M64, 31) * P1) & M64


def _merge(h, v):
    return (((h ^ _round(0, v)) * P1) + P4) & M64


def xxh64(data, seed=0):
    n = len(data)
    i = 0
    if n >= 32:
        v1 = (seed + P1 + P2) & M64
        v2 = (seed + P2) & M64
        v3 = seed
        v4 = (seed - P1) & M64
        while i + 32 <= n:
            v1 = _round(v1, int.from_bytes(data[i:i + 8], "little"))
            v2 = _round(v2, int.from_bytes(data[i + 8:i + 16], "little"))
            v3 = _round(v3, int.from_bytes(data[i + 16:i + 24], "little"))
            v4 = _round(v4, int.from_bytes(data[i + 24:i + 32], "little"))
            i += 32
        h = (_rotl(v1, 1) + _rotl(v2, 7) + _rotl(v3, 12) + _rotl(v4, 18)) & M64
        for v in (v1, v2, v3, v4):
            h = _merge(h, v)
    else:
        h = (seed + P5) & M64
    h = (h + n) & M64
    while i + 8 <= n:
        h ^= _round(0, int.from_bytes(data[i:i + 8], "little"))
        h = (_rotl(h, 27) * P1 + P4) & M64
        i += 8
    if i + 4 <= n:
        h ^= (int.from_bytes(data[i:i + 4], "little") * P1) & M64
        h = (_rotl(h, 23) * P2 + P3) & M64
        i += 4
    while i < n:
        h ^= (data[i] * P5) & M64
        h = (_rotl(h, 11) * P1) & M64
        i += 1
    h ^= h >> 33
    h = (h * P2) & M64
    h ^= h >> 29
    h = (h * P3) & M64
    h ^= h >> 32
    return h


def kcfi_id(typeid):
    """Low 32 bits of XXH64(seed 0) of the type-id string."""
    return xxh64(typeid.encode("ascii")) & 0xFFFFFFFF


def mask_kcfi_type(v):
    """LLVM X86AsmPrinter::MaskKCFIType: avoid ENDBR64/ENDBR32 byte patterns."""
    for n in (0xFA1E0FF3, 0xFB1E0FF3):
        if v == n or v == ((-n) & 0xFFFFFFFF):
            return (v + 1) & 0xFFFFFFFF
    return v


def u32(x):
    return x & 0xFFFFFFFF


# --------------------------------------------------------------------------
# Encoder model 1: rustc (rustc_sanitizers::cfi::typeid::itanium_cxx_abi)
# for the first-order fragment: bool, char, integers, f32/f64, unit,
# raw pointers, #[repr(transparent)] single-field wrappers, zero-sized
# arguments.  Types are tuples:
#   ("bool",) ("char",) ("int", "i32") ("f32",) ("f64",) ("unit",)
#   ("ptr", is_mut, pointee) ("transparent", name, inner) ("zst", name)
#   ("cvoid",)
# --------------------------------------------------------------------------
RUST_INT_VENDOR = {
    "i8": "u2i8", "i16": "u3i16", "i32": "u3i32", "i64": "u3i64",
    "i128": "u4i128", "isize": "u5isize",
    "u8": "u2u8", "u16": "u3u16", "u32": "u3u32", "u64": "u3u64",
    "u128": "u4u128", "usize": "u5usize",
}
BASE36 = "0123456789abcdefghijklmnopqrstuvwxyz"


def seq_id(num):
    """Itanium <seq-id>: S_ for 0, S0_ for 1, ... base 36 upper case."""
    if num == 0:
        return ""
    num -= 1
    digits = ""
    while True:
        digits = BASE36[num % 36] + digits
        num //= 36
        if num == 0:
            break
    return digits.upper()


def _compress(dic, key, comp):
    if key in dic:
        return "S%s_" % seq_id(dic[key])
    dic[key] = len(dic)
    return comp


def rust_transform(ty, normalize):
    """TransformTy::fold_ty for the modelled fragment (64-bit target)."""
    k = ty[0]
    if k == "bool":
        return ("int", "u8") if normalize else ty
    if k == "char":
        return ("int", "u32") if normalize else ty
    if k == "int":
        if normalize and ty[1] == "isize":
            return ("int", "i64")
        if normalize and ty[1] == "usize":
            return ("int", "u64")
        return ty
    if k == "cvoid":
        return ("unit",)
    if k == "transparent":
        return rust_transform(ty[2], normalize)
    if k == "ptr":
        return ("ptr", ty[1], rust_transform(ty[2], normalize))
    return ty


def rust_encode_ty(ty, dic):
    k = ty[0]
    if k == "bool":
        return "b"
    if k == "int":
        return _compress(dic, ty, RUST_INT_VENDOR[ty[1]])
    if k == "f32":
        return "f"
    if k == "f64":
        return "d"
    if k == "char":
        return _compress(dic, ty, "u4char")
    if k == "unit":
        return "v"
    if k == "ptr":
        s = rust_encode_ty(ty[2], dic)
        if not ty[1]:
            s = _compress(dic, ("constq", ty[2]), "K" + s)
        return _compress(dic, ty, "P" + s)
    raise ValueError(ty)


def rust_typeid(ret, args, normalize):
    """typeid_for_fnabi: `_ZTSF<ret><args>E[.normalized]`."""
    dic = {}
    out = "_ZTSF" + rust_encode_ty(rust_transform(ret, normalize), dic)
    pushed = False
    for a in args:
        if a[0] == "zst":      # PassMode::Ignore
            continue
        pushed = True
        out += rust_encode_ty(rust_transform(a, normalize), dic)
    if not pushed:
        out += "v"
    out += "E"
    if normalize:
        out += ".normalized"
    return out


# --------------------------------------------------------------------------
# Encoder model 2: clang (ItaniumMangle.cpp, mangleCanonicalTypeName) for
# C function types on x86-64 SysV (LP64).  Types are tuples:
#   ("b", name)  builtin with Itanium code      ("ptr", is_const_pointee, T)
# --------------------------------------------------------------------------
C_BUILTINS = {
    # name: (code, c_spelling, is_integer, signed, bits)
    "void": ("v", "void", False, False, 0),
    "bool": ("b", "_Bool", True, False, 8),
    "char": ("c", "char", True, True, 8),
    "schar": ("a", "signed char", True, True, 8),
    "uchar": ("h", "unsigned char", True, False, 8),
    "short": ("s", "short", True, True, 16),
    "ushort": ("t", "unsigned short", True, False, 16),
    "int": ("i", "int", True, True, 32),
    "uint": ("j", "unsigned int", True, False, 32),
    "long": ("l", "long", True, True, 64),
    "ulong": ("m", "unsigned long", True, False, 64),
    "llong": ("x", "long long", True, True, 64),
    "ullong": ("y", "unsigned long long", True, False, 64),
    "float": ("f", "float", False, True, 32),
    "double": ("d", "double", False, True, 64),
}


def c_encode_ty(ty, dic, normalize):
    if ty[0] == "b":
        code, _sp, is_int, signed, bits = C_BUILTINS[ty[1]]
        if normalize and is_int:
            # One substitution representative per (signedness, width).
            vend = "%s%d" % ("i" if signed else "u", bits)
            return _compress(dic, ("normint", signed, bits), "u%d%s" % (len(vend), vend))
        return code                      # builtins are not substitution candidates
    if ty[0] == "ptr":
        # Compound types are substitution candidates keyed by the C type
        # itself: `long *` and `long long *` stay distinct even when their
        # pointees share one normalised representative.
        s = c_encode_ty(ty[2], dic, normalize)
        if ty[1]:
            s = _compress(dic, ("constq", ty[2]), "K" + s)
        return _compress(dic, ty, "P" + s)
    raise ValueError(ty)


def c_norm_key(ty):
    """The C type with every integer builtin replaced by (signedness, width)."""
    if ty[0] == "b":
        _code, _sp, is_int, signed, bits = C_BUILTINS[ty[1]]
        return ("normint", signed, bits) if is_int else ty
    return ("ptr", ty[1], c_norm_key(ty[2]))


def c_compound_types(ty, acc):
    if ty[0] == "ptr":
        acc.add(ty)
        if ty[1]:
            acc.add(("constq", ty[2]))
        c_compound_types(ty[2], acc)
    return acc


def c_mixes_same_width_integer_spellings(ret, args):
    """True iff two distinct compound C types in the signature become equal
    once integer builtins are identified by (signedness, width)."""
    comp = set()
    for t in [ret] + list(args):
        c_compound_types(t, comp)
    keys = {}
    for t in comp:
        k = ("constq", c_norm_key(t[1])) if t[0] == "constq" else c_norm_key(t)
        keys.setdefault(k, set()).add(t)
    return any(len(v) > 1 for v in keys.values())


def c_typeid(ret, args, normalize):
    dic = {}
    out = "_ZTSF" + c_encode_ty(ret, dic, normalize)
    if not args:
        out += "v"
    for a in args:
        out += c_encode_ty(a, dic, normalize)
    out += "E"
    if normalize:
        out += ".normalized"
    return out


# --------------------------------------------------------------------------
# Helpers for running tools and reading their output.
# --------------------------------------------------------------------------
class Tools:
    def __init__(self):
        self.rustc = os.environ.get("RUSTC", "rustc")
        self.clang = os.environ.get("CLANG", "clang-19")
        objdump = os.environ.get("LLVM_OBJDUMP")
        if not objdump:
            objdump = shutil.which("llvm-objdump")
        if not objdump:
            sysroot = subprocess.run([self.rustc, "--print", "sysroot"], capture_output=True, text=True).stdout.strip()
            host = ""
            for line in subprocess.run([self.rustc, "-vV"], capture_output=True, text=True).stdout.splitlines():
                if line.startswith("host: "):
                    host = line[6:].strip()
            cand = os.path.join(sysroot, "lib", "rustlib", host, "bin", "llvm-objdump")
            objdump = cand if os.path.exists(cand) else "llvm-objdump"
        self.objdump = objdump


def run(cmd, cwd, timeout=300):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout, p.stderr


def must(cmd, cwd):
    rc, out, err = run(cmd, cwd)
    if rc != 0:
        raise RuntimeError("command failed (%d): %s\n%s\n%s" % (rc, " ".join(cmd), out[-2000:], err[-4000:]))
    return out


def execute(binary, args, cwd):
    p = subprocess.run([os.path.join(".", binary)] + args, cwd=cwd, capture_output=True, text=True, timeout=60)
    return {"rc": p.returncode, "stdout": p.stdout.strip()}


RE_MD_I32 = re.compile(r"^!(\d+) = !\{i32 (-?\d+)\}", re.M)
RE_DEFINE = re.compile(r"^define [^@\n]*@\"?([A-Za-z0-9_.$]+)\"?\(.*?\)[^\n{]*\{", re.M)
RE_KCFI_ATTACH = re.compile(r"!kcfi_type !(\d+)")
RE_TYPE_ATTACH = re.compile(r"!type !(\d+)")
RE_MD_TYPE = re.compile(r"^!(\d+) = !\{i64 0, !\"([^\"]+)\"\}", re.M)
RE_ALIAS = re.compile(r"^@\"?([A-Za-z0-9_.$]+)\"? = [^\n]*\balias\b[^\n]*, ptr @\"?([A-Za-z0-9_.$]+)\"?\s*$", re.M)
RE_BUNDLE = re.compile(r"\[ \"kcfi\"\(i32 (-?\d+)\) \]")


def ir_functions(ir):
    """name -> {'kcfi_type': u32|None, 'type_strings': [...], 'bundles': [u32...]}"""
    md_i32 = {m.group(1): u32(int(m.group(2))) for m in RE_MD_I32.finditer(ir)}
    md_ty = {m.group(1): m.group(2) for m in RE_MD_TYPE.finditer(ir)}
    out = {}
    for m in RE_DEFINE.finditer(ir):
        name = m.group(1)
        header = m.group(0)
        end = ir.find("\n}\n", m.end())
        body = ir[m.end():end if end != -1 else len(ir)]
        k = RE_KCFI_ATTACH.search(header)
        out[name] = {
            "kcfi_type": md_i32.get(k.group(1)) if k else None,
            "type_strings": [md_ty[t] for t in RE_TYPE_ATTACH.findall(header) if t in md_ty],
            "kcfi_bundles": [u32(int(b)) for b in RE_BUNDLE.findall(body)],
        }
    # Functions folded by LLVM's MergeFunctions pass appear as aliases of the
    # surviving definition and share its prefix word.
    for m in RE_ALIAS.finditer(ir):
        if m.group(2) in out and m.group(1) not in out:
            out[m.group(1)] = dict(out[m.group(2)], alias_of=m.group(2))
    return out


RE_SYM = re.compile(r"^([0-9a-f]+) <([^>]+)>:$")
RE_INSN = re.compile(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)$")


def disassemble(tools, binary, cwd, symbols):
    """Return {symbol: {'addr': int, 'insns': [(addr, bytes, text)]}} for the
    requested symbols (substring match on the demangled-or-not name)."""
    text = must([tools.objdump, "-d", "--no-print-imm-hex", binary], cwd)
    res = {}
    cur = None
    for line in text.splitlines():
        m = RE_SYM.match(line)
        if m:
            name = m.group(2)
            cur = name if any(s in name for s in symbols) else None
            if cur:
                res[cur] = {"addr": int(m.group(1), 16), "insns": []}
            continue
        if cur:
            mi = RE_INSN.match(line)
            if mi:
                res[cur]["insns"].append((int(mi.group(1), 16), bytes.fromhex(mi.group(2).replace(" ", "")), mi.group(3).replace("\t", " ").strip()))
    return res


def render(sym):
    return ["%x: %-21s %s" % (a, b.hex(" "), t) for a, b, t in sym["insns"]]


def parse_prefix(sym):
    """Decode a `__cfi_<fn>` prefix: N one-byte nops then `b8 imm32`."""
    raw = b"".join(b for _a, b, _t in sym["insns"])
    nops = 0
    while nops < len(raw) and raw[nops] == 0x90:
        nops += 1
    ok = len(raw) >= nops + 5 and raw[nops] == 0xB8
    imm = int.from_bytes(raw[nops + 1:nops + 5], "little") if ok else None
    return {"size_bytes": len(raw), "leading_0x90_nops": nops, "opcode_after_nops": "0x%02x" % raw[nops] if nops < len(raw) else None,
            "mov_eax_imm32": imm, "raw_hex": raw.hex(" ")}


def parse_guard(sym):
    """Find `mov $imm,%r10d|%r11d ; add -4(%reg),%r1Xd ; je ; ud2 ; jmp|call *%reg`."""
    ins = sym["insns"]
    for i in range(len(ins) - 4):
        b0, b1, b2, b3, b4 = (ins[i + j][1] for j in range(5))
        if len(b0) == 6 and b0[0] == 0x41 and b0[1] in (0xBA, 0xBB) and b2[:1] == b"\x74" and b3 == b"\x0f\x0b":
            return {
                "neg_imm32": int.from_bytes(b0[2:6], "little"),
                "add_disp8": int.from_bytes(b1[-1:], "little", signed=True),
                "je_rel8": b2[1],
                "insns": ["%s    | %s" % (ins[i + j][1].hex(" "), ins[i + j][2]) for j in range(5)],
                "transfer": ins[i + 4][2],
            }
    return None


# --------------------------------------------------------------------------
# Part B sources
# --------------------------------------------------------------------------
FFI_C = r"""
#include <stdint.h>
typedef uint64_t (*cb_u64_i32_t)(int32_t);
typedef uint32_t (*cb_u32_u32_t)(uint32_t);
uint64_t call_u64_i32(cb_u64_i32_t f, int32_t x) { return f(x); }
uint32_t call_u32_u32(cb_u32_u32_t f, uint32_t x) { return f(x); }
/* `long` and `long long` are both 64-bit signed on LP64. */
typedef void (*cb_ptrs_same_t)(long *, long *);
typedef void (*cb_ptrs_mixed_t)(long *, long long *);
void call_ptrs_same(cb_ptrs_same_t f, long *a, long *b) { f(a, b); }
void call_ptrs_mixed(cb_ptrs_mixed_t f, long *a, long long *b) { f(a, b); }
"""

FFI_RS = r"""
#[repr(transparent)]
pub struct TransU32(pub u32);

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_cb_u64_i32(x: i32) -> u64 { 1000u64.wrapping_add(x as u64) }

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_cb_u32_trans(x: TransU32) -> u32 { x.0.wrapping_add(58) }

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_cb_wrong_sig(x: i64) -> u64 { 2000u64.wrapping_add(x as u64) }

#[no_mangle]
#[inline(never)]
pub extern "C" fn rust_cb_two_i64_ptrs(a: *mut i64, b: *mut i64) { unsafe { *a = 7; *b = 9; } }

extern "C" {
    fn call_u64_i32(f: extern "C" fn(i32) -> u64, x: i32) -> u64;
    fn call_u32_u32(f: extern "C" fn(TransU32) -> u32, x: u32) -> u32;
    fn call_ptrs_same(f: extern "C" fn(*mut i64, *mut i64), a: *mut i64, b: *mut i64);
    fn call_ptrs_mixed(f: extern "C" fn(*mut i64, *mut i64), a: *mut i64, b: *mut i64);
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "u64" => {
            let r = unsafe { call_u64_i32(rust_cb_u64_i32, 42) };
            println!("U64_OK={r}");
        }
        "trans" => {
            let r = unsafe { call_u32_u32(rust_cb_u32_trans, 42) };
            println!("TRANS_OK={r}");
        }
        "wrong" => {
            let f: extern "C" fn(i32) -> u64 =
                unsafe { std::mem::transmute(rust_cb_wrong_sig as extern "C" fn(i64) -> u64) };
            let r = unsafe { call_u64_i32(f, 42) };
            println!("WRONG_SIG_NOT_TRAPPED={r}");
        }
        "ptrs_same" => {
            let (mut a, mut b) = (0i64, 0i64);
            unsafe { call_ptrs_same(rust_cb_two_i64_ptrs, &mut a, &mut b) };
            println!("PTRS_SAME_OK={}", a + b);
        }
        "ptrs_mixed" => {
            let (mut a, mut b) = (0i64, 0i64);
            unsafe { call_ptrs_mixed(rust_cb_two_i64_ptrs, &mut a, &mut b) };
            println!("PTRS_MIXED_OK={}", a + b);
        }
        _ => std::process::exit(2),
    }
}
"""

RUST_BASE = ["--edition", "2021", "-Copt-level=2", "-Ccodegen-units=1", "-Cpanic=abort",
             "-Csymbol-mangling-version=v0"]
# The precompiled standard library shipped with the toolchain is built
# without these flags, so the mismatch must be allowed explicitly.  The
# allow-list has to be one comma-separated value: a second
# `-Cunsafe-allow-abi-mismatch=` replaces the first (see part F).
RUST_KCFI = ["-Zsanitizer=kcfi", "-Cunsafe-allow-abi-mismatch=sanitizer"]
RUST_KCFI_NORM = ["-Zsanitizer=kcfi", "-Zsanitizer-cfi-normalize-integers",
                  "-Cunsafe-allow-abi-mismatch=sanitizer,sanitizer-cfi-normalize-integers"]
CLANG_KCFI = ["-fsanitize=kcfi"]
CLANG_NORM = ["-fsanitize-cfi-icall-experimental-normalize-integers"]


def part_b(tools, wd, checks):
    d = os.path.join(wd, "ffi")
    os.makedirs(d)
    open(os.path.join(d, "ffi_harness.c"), "w").write(FFI_C)
    open(os.path.join(d, "ffi_main.rs"), "w").write(FFI_RS)
    res = {"sources": {"ffi_harness.c": FFI_C, "ffi_main.rs": FFI_RS}, "configs": {}}
    configs = {
        "no_sanitizer": ([], []),
        "kcfi_default": (CLANG_KCFI, RUST_KCFI),
        "kcfi_normalized": (CLANG_KCFI + CLANG_NORM, RUST_KCFI_NORM),
        "kcfi_rust_normalized_c_default": (CLANG_KCFI, RUST_KCFI_NORM),
    }
    for name, (cflags, rflags) in configs.items():
        obj, ll_c, ll_rs, exe = "ffi_%s.o" % name, "ffi_%s.c.ll" % name, "ffi_%s.rs.ll" % name, "ffi_%s.bin" % name
        must([tools.clang, "-O2", "-c"] + cflags + ["ffi_harness.c", "-o", obj], d)
        must([tools.clang, "-O2", "-S", "-emit-llvm"] + cflags + ["ffi_harness.c", "-o", ll_c], d)
        must([tools.rustc] + RUST_BASE + rflags + ["--emit=llvm-ir", "-o", ll_rs, "ffi_main.rs"], d)
        must([tools.rustc] + RUST_BASE + rflags + ["-Clink-arg=" + obj, "-o", exe, "ffi_main.rs"], d)
        c_ir = ir_functions(open(os.path.join(d, ll_c)).read())
        r_ir = ir_functions(open(os.path.join(d, ll_rs)).read())
        entry = {
            "clang_flags": ["-O2"] + cflags,
            "rustc_flags": RUST_BASE + rflags,
            "clang_ir": {k: {"kcfi_type": v["kcfi_type"], "call_site_kcfi_bundles": v["kcfi_bundles"]} for k, v in c_ir.items()},
            "rustc_ir_kcfi_type": {k: v["kcfi_type"] for k, v in r_ir.items() if k.startswith("rust_cb_")},
            "exec": {m: execute(exe, [m], d) for m in ("u64", "trans", "wrong", "ptrs_same", "ptrs_mixed")},
        }
        if name != "no_sanitizer":
            dis = disassemble(tools, exe, d, ["call_u64_i32", "call_u32_u32", "rust_cb_u64_i32", "rust_cb_u32_trans", "rust_cb_wrong_sig"])
            dis = {k: v for k, v in dis.items() if not k.startswith("rust_cb_two") and not k.startswith("__cfi_rust_cb_two")}
            mc = {}
            for cb in ("rust_cb_u64_i32", "rust_cb_u32_trans", "rust_cb_wrong_sig"):
                pre, fn = dis.get("__cfi_" + cb), dis.get(cb)
                if pre and fn:
                    info = parse_prefix(pre)
                    info["entry_minus_prefix_symbol"] = fn["addr"] - pre["addr"]
                    info["disassembly"] = render(pre)
                    mc["__cfi_" + cb] = info
            for cs in ("call_u64_i32", "call_u32_u32"):
                if cs in dis:
                    g = parse_guard(dis[cs])
                    mc[cs] = {"guard": g, "disassembly": render(dis[cs])}
            entry["machine_code"] = mc
        res["configs"][name] = entry

    # ---- checks -----------------------------------------------------------
    ns, df, nm, mx = (res["configs"][k] for k in ("no_sanitizer", "kcfi_default", "kcfi_normalized", "kcfi_rust_normalized_c_default"))
    checks["B_control_without_sanitizer_all_three_calls_return"] = (
        ns["exec"]["u64"] == {"rc": 0, "stdout": "U64_OK=1042"}
        and ns["exec"]["trans"] == {"rc": 0, "stdout": "TRANS_OK=100"}
        and ns["exec"]["wrong"] == {"rc": 0, "stdout": "WRONG_SIG_NOT_TRAPPED=2042"}
        and ns["exec"]["ptrs_same"] == {"rc": 0, "stdout": "PTRS_SAME_OK=16"}
        and ns["exec"]["ptrs_mixed"] == {"rc": 0, "stdout": "PTRS_MIXED_OK=16"})
    checks["B_default_u64_i32_callback_dies_with_SIGILL"] = df["exec"]["u64"] == {"rc": -4, "stdout": ""}
    checks["B_default_transparent_u32_callback_dies_with_SIGILL"] = df["exec"]["trans"] == {"rc": -4, "stdout": ""}
    checks["B_normalized_u64_i32_callback_returns_1042"] = nm["exec"]["u64"] == {"rc": 0, "stdout": "U64_OK=1042"}
    checks["B_normalized_transparent_u32_callback_returns_100"] = nm["exec"]["trans"] == {"rc": 0, "stdout": "TRANS_OK=100"}
    checks["B_normalized_wrong_signature_dies_with_SIGILL"] = nm["exec"]["wrong"] == {"rc": -4, "stdout": ""}
    checks["B_normalized_pointer_pair_with_one_c_spelling_returns_16"] = nm["exec"]["ptrs_same"] == {"rc": 0, "stdout": "PTRS_SAME_OK=16"}
    checks["B_normalized_pointer_pair_mixing_long_and_long_long_dies_with_SIGILL"] = nm["exec"]["ptrs_mixed"] == {"rc": -4, "stdout": ""}
    checks["B_one_sided_normalization_dies_with_SIGILL"] = (mx["exec"]["u64"]["rc"] == -4 and mx["exec"]["trans"]["rc"] == -4)

    # ids: model vs rustc vs clang
    r_u64 = (("int", "u64"), [("int", "i32")])
    r_tr = (("int", "u32"), [("transparent", "TransU32", ("int", "u32"))])
    r_wr = (("int", "u64"), [("int", "i64")])
    c_u64 = (("b", "ulong"), [("b", "int")])
    c_u32 = (("b", "uint"), [("b", "uint")])
    r_pp = (("unit",), [("ptr", True, ("int", "i64")), ("ptr", True, ("int", "i64"))])
    c_pp_same = (("b", "void"), [("ptr", False, ("b", "long")), ("ptr", False, ("b", "long"))])
    c_pp_mixed = (("b", "void"), [("ptr", False, ("b", "long")), ("ptr", False, ("b", "llong"))])
    ids = {}
    for label, norm, cfg in (("default", False, df), ("normalized", True, nm)):
        ids[label] = {
            "rust_cb_u64_i32": {"model_typeid": rust_typeid(*r_u64, norm), "rustc": cfg["rustc_ir_kcfi_type"]["rust_cb_u64_i32"]},
            "rust_cb_u32_trans": {"model_typeid": rust_typeid(*r_tr, norm), "rustc": cfg["rustc_ir_kcfi_type"]["rust_cb_u32_trans"]},
            "rust_cb_wrong_sig": {"model_typeid": rust_typeid(*r_wr, norm), "rustc": cfg["rustc_ir_kcfi_type"]["rust_cb_wrong_sig"]},
            "call_u64_i32": {"model_typeid": c_typeid(*c_u64, norm), "clang_bundle": cfg["clang_ir"]["call_u64_i32"]["call_site_kcfi_bundles"]},
            "call_u32_u32": {"model_typeid": c_typeid(*c_u32, norm), "clang_bundle": cfg["clang_ir"]["call_u32_u32"]["call_site_kcfi_bundles"]},
            "rust_cb_two_i64_ptrs": {"model_typeid": rust_typeid(*r_pp, norm), "rustc": cfg["rustc_ir_kcfi_type"]["rust_cb_two_i64_ptrs"]},
            "call_ptrs_same": {"model_typeid": c_typeid(*c_pp_same, norm), "clang_bundle": cfg["clang_ir"]["call_ptrs_same"]["call_site_kcfi_bundles"]},
            "call_ptrs_mixed": {"model_typeid": c_typeid(*c_pp_mixed, norm), "clang_bundle": cfg["clang_ir"]["call_ptrs_mixed"]["call_site_kcfi_bundles"]},
        }
        for v in ids[label].values():
            v["model_id"] = kcfi_id(v["model_typeid"])
    res["type_ids"] = ids
    checks["B_model_ids_equal_rustc_and_clang_emitted_ids"] = all(
        (v.get("rustc") == v["model_id"]) if "rustc" in v else (v["clang_bundle"] == [v["model_id"]])
        for lab in ids.values() for v in lab.values())
    checks["B_default_ids_differ_across_languages"] = (
        ids["default"]["rust_cb_u64_i32"]["rustc"] != ids["default"]["call_u64_i32"]["clang_bundle"][0]
        and ids["default"]["rust_cb_u32_trans"]["rustc"] != ids["default"]["call_u32_u32"]["clang_bundle"][0])
    checks["B_normalized_pointer_ids_agree_only_for_the_single_spelling_prototype"] = (
        ids["normalized"]["rust_cb_two_i64_ptrs"]["rustc"] == ids["normalized"]["call_ptrs_same"]["clang_bundle"][0]
        and ids["normalized"]["rust_cb_two_i64_ptrs"]["rustc"] != ids["normalized"]["call_ptrs_mixed"]["clang_bundle"][0])
    checks["B_normalized_ids_agree_across_languages"] = (
        ids["normalized"]["rust_cb_u64_i32"]["rustc"] == ids["normalized"]["call_u64_i32"]["clang_bundle"][0]
        and ids["normalized"]["rust_cb_u32_trans"]["rustc"] == ids["normalized"]["call_u32_u32"]["clang_bundle"][0])

    # machine code: prefix layout and guard arithmetic, read from the binary
    mc = nm["machine_code"]
    pre = mc["__cfi_rust_cb_u64_i32"]
    g = mc["call_u64_i32"]["guard"]
    res["normalized_machine_code_summary"] = {
        "prefix_imm32": pre["mov_eax_imm32"], "prefix_imm32_hex": "0x%08x" % pre["mov_eax_imm32"],
        "guard_neg_imm32": g["neg_imm32"], "guard_neg_imm32_hex": "0x%08x" % g["neg_imm32"],
        "sum_mod_2_32": u32(pre["mov_eax_imm32"] + g["neg_imm32"]),
    }
    checks["B_prefix_is_11_nops_then_mov_eax_imm32_and_16_bytes"] = all(
        m["leading_0x90_nops"] == 11 and m["size_bytes"] == 16 and m["entry_minus_prefix_symbol"] == 16 and m["mov_eax_imm32"] is not None
        for k, m in mc.items() if k.startswith("__cfi_"))
    checks["B_prefix_imm32_equals_emitted_kcfi_type"] = all(
        mc["__cfi_" + cb]["mov_eax_imm32"] == mask_kcfi_type(nm["rustc_ir_kcfi_type"][cb])
        for cb in ("rust_cb_u64_i32", "rust_cb_u32_trans", "rust_cb_wrong_sig"))
    checks["B_guard_reads_disp_minus_4_and_neg_imm_plus_prefix_is_zero_mod_2_32"] = (
        g["add_disp8"] == -4 and u32(pre["mov_eax_imm32"] + g["neg_imm32"]) == 0 and g["je_rel8"] == 2)
    gd = df["machine_code"]["call_u64_i32"]["guard"]
    pd = df["machine_code"]["__cfi_rust_cb_u64_i32"]
    res["default_machine_code_summary"] = {
        "prefix_imm32_hex": "0x%08x" % pd["mov_eax_imm32"], "guard_neg_imm32_hex": "0x%08x" % gd["neg_imm32"],
        "sum_mod_2_32_hex": "0x%08x" % u32(pd["mov_eax_imm32"] + gd["neg_imm32"]),
    }
    checks["B_default_guard_sum_is_nonzero"] = u32(pd["mov_eax_imm32"] + gd["neg_imm32"]) != 0
    return res


# --------------------------------------------------------------------------
# Part C: the reify shim
# --------------------------------------------------------------------------
REIFY_RS = r"""
use std::hint::black_box;

pub trait Step { fn step(&self, x: u32) -> u32; }
pub struct Counter(pub u32);
impl Step for Counter {
    #[inline(never)]
    fn step(&self, x: u32) -> u32 { self.0.wrapping_add(x) }
}

#[inline(never)]
pub fn invoke_dyn(s: &dyn Step, x: u32) -> u32 { s.step(x) }

#[inline(never)]
pub fn invoke_fnptr(f: fn(&Counter, u32) -> u32, c: &Counter, x: u32) -> u32 { f(c, x) }

#[inline(never)]
pub fn reify_step_as_fnptr() -> fn(&Counter, u32) -> u32 { <Counter as Step>::step }

/// Address stored in the vtable slot of `Step::step` for `Counter`
/// (slots 0..2 are drop_in_place, size, align in this toolchain; the
/// no-sanitizer control run of mode `slot_as_fnptr` checks that reading).
fn vtable_parts(d: &dyn Step) -> (*const (), *const usize) {
    unsafe { std::mem::transmute::<&dyn Step, (*const (), *const usize)>(d) }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let c = Counter(40);
    match mode.as_str() {
        "dyn" => println!("DYN_OK={}", invoke_dyn(black_box(&c), 2)),
        "fnptr" => println!("FNPTR_OK={}", invoke_fnptr(black_box(reify_step_as_fnptr()), &c, 2)),
        "addrs" => {
            let (_data, vt) = vtable_parts(&c);
            let slot = unsafe { *vt.add(3) };
            println!("FNPTR_EQ_VTABLE_SLOT={}", slot == reify_step_as_fnptr() as usize);
        }
        // Cross-wire 1: the vtable entry used as a plain fn pointer.
        "slot_as_fnptr" => {
            let (_data, vt) = vtable_parts(&c);
            let slot = unsafe { *vt.add(3) };
            let f: fn(&Counter, u32) -> u32 = unsafe { std::mem::transmute(slot) };
            println!("SLOT_AS_FNPTR={}", invoke_fnptr(black_box(f), &c, 2));
        }
        // Cross-wire 2: the fn-pointer value placed in a vtable slot.
        "fnptr_in_vtable" => {
            let (data, vt) = vtable_parts(&c);
            let forged: &'static [usize; 4] = Box::leak(Box::new(unsafe {
                [*vt, *vt.add(1), *vt.add(2), reify_step_as_fnptr() as usize]
            }));
            let fake: &dyn Step = unsafe {
                std::mem::transmute::<(*const (), *const usize), &dyn Step>((data, forged.as_ptr()))
            };
            println!("FNPTR_IN_VTABLE={}", invoke_dyn(black_box(fake), 2));
        }
        _ => std::process::exit(2),
    }
}
"""


def part_c(tools, wd, checks):
    d = os.path.join(wd, "reify")
    os.makedirs(d)
    open(os.path.join(d, "reify_kcfi.rs"), "w").write(REIFY_RS)
    base = RUST_BASE + ["--crate-name", "reify_kcfi"]
    res = {"sources": {"reify_kcfi.rs": REIFY_RS}, "builds": {}}
    builds = {
        "no_sanitizer": [],
        "kcfi": RUST_KCFI,
        "cfi": ["-Zsanitizer=cfi", "-Clinker-plugin-lto", "-Cunsafe-allow-abi-mismatch=sanitizer"],
    }
    irs = {}
    for name, flags in builds.items():
        ll = "reify_%s.ll" % name
        must([tools.rustc] + base + flags + ["--emit=llvm-ir", "-o", ll, "reify_kcfi.rs"], d)
        fns = ir_functions(open(os.path.join(d, ll)).read())
        irs[name] = fns
        res["builds"][name] = {
            "rustc_flags": base + flags,
            "defined_functions": {k: {kk: vv for kk, vv in v.items() if vv not in (None, [])} for k, v in sorted(fns.items()) if "reify_kcfi" in k},
        }

    def find(fns, *needles):
        hits = [k for k in fns if all(n in k for n in needles)]
        return hits[0] if len(hits) == 1 else None

    k, c, p = irs["kcfi"], irs["cfi"], irs["no_sanitizer"]
    shim = find(k, "10reify_kcfi", "4Step4step", "reify_fnptr")
    step_k = find({x: 0 for x in k if "reify_fnptr" not in x}, "10reify_kcfi", "4Step4step")
    step_c = find(c, "10reify_kcfi", "4Step4step")
    inv_dyn_k, inv_fp_k = find(k, "10invoke_dyn"), find(k, "12invoke_fnptr")
    summary = {
        "shim_symbol_with_kcfi": shim,
        "all_reify_shims_with_kcfi": sorted(x for x in k if x.endswith(("reify_fnptr", "reify_vtable"))),
        "all_reify_shims_without_sanitizer": sorted(x for x in p if x.endswith(("reify_fnptr", "reify_vtable"))),
        "all_reify_shims_with_cfi": sorted(x for x in c if x.endswith(("reify_fnptr", "reify_vtable"))),
        "method_symbol": step_k,
        "method_kcfi_type": k[step_k]["kcfi_type"] if step_k else None,
        "shim_kcfi_type": k[shim]["kcfi_type"] if shim else None,
        "dyn_call_site_expected_id": k[inv_dyn_k]["kcfi_bundles"],
        "fnptr_call_site_expected_id": k[inv_fp_k]["kcfi_bundles"],
        "cfi_type_strings_attached_to_method": c[step_c]["type_strings"] if step_c else [],
    }
    # Which CFI strings hash to the two KCFI ids?
    strings = summary["cfi_type_strings_attached_to_method"]
    summary["method_kcfi_type_is_hash_of"] = [s for s in strings if kcfi_id(s) == summary["method_kcfi_type"]]
    summary["shim_kcfi_type_is_hash_of"] = [s for s in strings if kcfi_id(s) == summary["shim_kcfi_type"]]
    summary["cfi_string_hashes"] = {s: kcfi_id(s) for s in strings}
    res["summary"] = summary

    checks["C_reify_fnptr_shim_defined_only_with_kcfi"] = (
        shim is not None and not summary["all_reify_shims_without_sanitizer"] and not summary["all_reify_shims_with_cfi"])
    checks["C_cfi_attaches_more_than_one_type_id_to_the_method_and_kcfi_exactly_one"] = (
        len(strings) >= 2 and summary["method_kcfi_type"] is not None)
    checks["C_method_id_is_hash_of_self_erased_string_and_shim_id_of_concrete_self_string"] = (
        len(summary["method_kcfi_type_is_hash_of"]) == 1 and "u3dynI" in summary["method_kcfi_type_is_hash_of"][0]
        and len(summary["shim_kcfi_type_is_hash_of"]) == 1 and "u3dynI" not in summary["shim_kcfi_type_is_hash_of"][0]
        and "7Counter" in summary["shim_kcfi_type_is_hash_of"][0])
    checks["C_call_sites_expect_method_id_for_dyn_and_shim_id_for_fnptr"] = (
        summary["dyn_call_site_expected_id"] == [summary["method_kcfi_type"]]
        and summary["fnptr_call_site_expected_id"] == [summary["shim_kcfi_type"]]
        and summary["method_kcfi_type"] != summary["shim_kcfi_type"])

    # executables
    res["exec"] = {}
    for name in ("no_sanitizer", "kcfi"):
        exe = "reify_%s.bin" % name
        must([tools.rustc] + base + builds[name] + ["-o", exe, "reify_kcfi.rs"], d)
        res["exec"][name] = {m: execute(exe, [m], d) for m in ("dyn", "fnptr", "addrs", "slot_as_fnptr", "fnptr_in_vtable")}
    ek, en = res["exec"]["kcfi"], res["exec"]["no_sanitizer"]
    checks["C_control_without_sanitizer_all_paths_return_42_and_fnptr_is_vtable_slot"] = (
        en["dyn"]["stdout"] == "DYN_OK=42" and en["fnptr"]["stdout"] == "FNPTR_OK=42"
        and en["slot_as_fnptr"]["stdout"] == "SLOT_AS_FNPTR=42" and en["fnptr_in_vtable"]["stdout"] == "FNPTR_IN_VTABLE=42"
        and en["addrs"]["stdout"] == "FNPTR_EQ_VTABLE_SLOT=true")
    checks["C_kcfi_dyn_and_fnptr_paths_return_42"] = (
        ek["dyn"] == {"rc": 0, "stdout": "DYN_OK=42"} and ek["fnptr"] == {"rc": 0, "stdout": "FNPTR_OK=42"})
    checks["C_kcfi_fnptr_value_differs_from_vtable_slot"] = ek["addrs"] == {"rc": 0, "stdout": "FNPTR_EQ_VTABLE_SLOT=false"}
    checks["C_kcfi_cross_wired_paths_die_with_SIGILL"] = (
        ek["slot_as_fnptr"] == {"rc": -4, "stdout": ""} and ek["fnptr_in_vtable"] == {"rc": -4, "stdout": ""})

    # machine code of shim and method
    dis = disassemble(tools, "reify_kcfi.bin", d, ["7CounterNtB2_4Step4step", "7CounterNtB4_4Step4step"])
    mc = {}
    for sym, v in dis.items():
        e = {"disassembly": render(v)}
        if sym.startswith("__cfi_"):
            e.update(parse_prefix(v))
            e.pop("raw_hex", None)
        mc[sym] = e
    res["machine_code"] = mc
    pre_shim = [v for s, v in mc.items() if s.startswith("__cfi_") and s.endswith("reify_fnptr")]
    pre_meth = [v for s, v in mc.items() if s.startswith("__cfi_") and not s.endswith("reify_fnptr")]
    checks["C_binary_prefixes_carry_the_two_distinct_ids"] = (
        len(pre_shim) == 1 and len(pre_meth) == 1
        and pre_shim[0]["mov_eax_imm32"] == summary["shim_kcfi_type"]
        and pre_meth[0]["mov_eax_imm32"] == summary["method_kcfi_type"])
    shim_body = [v for s, v in dis.items() if not s.startswith("__cfi_") and s.endswith("reify_fnptr")]
    res["shim_body_is_single_direct_jmp_to_method"] = bool(
        shim_body and len(shim_body[0]["insns"]) >= 1 and shim_body[0]["insns"][0][2].startswith("jmp") and "*" not in shim_body[0]["insns"][0][2])
    checks["C_shim_forwards_with_a_direct_unchecked_jump"] = res["shim_body_is_single_direct_jmp_to_method"]
    return res


# --------------------------------------------------------------------------
# Part D: differential test of the encoder models
# --------------------------------------------------------------------------
RUST_SPELL = {"bool": "bool", "char": "char", "f32": "f32", "f64": "f64", "unit": "()", "cvoid": "core::ffi::c_void"}
RUST_SCALARS = [("bool",), ("char",), ("f32",), ("f64",)] + [("int", n) for n in RUST_INT_VENDOR]
# Rust scalar -> LP64 C builtins with the same size, signedness and call ABI.
RUST_TO_C = {
    ("bool",): ["bool"], ("f32",): ["float"], ("f64",): ["double"],
    ("int", "i8"): ["schar", "char"], ("int", "u8"): ["uchar"],
    ("int", "i16"): ["short"], ("int", "u16"): ["ushort"],
    ("int", "i32"): ["int"], ("int", "u32"): ["uint"],
    ("int", "i64"): ["long", "llong"], ("int", "u64"): ["ulong", "ullong"],
    ("int", "isize"): ["long"], ("int", "usize"): ["ulong"],
}


def rust_spelling(ty):
    k = ty[0]
    if k == "int":
        return ty[1]
    if k == "ptr":
        return ("*mut " if ty[1] else "*const ") + rust_spelling(ty[2])
    if k == "transparent":
        return ty[1]
    if k == "zst":
        return ty[1]
    return RUST_SPELL[k]


def c_decl(ty):
    """C spelling; pointer-to-const is written `T const *`."""
    if ty[0] == "b":
        return C_BUILTINS[ty[1]][1]
    return c_decl(ty[2]) + (" const *" if ty[1] else " *")


def gen_signatures(rng, n):
    """Random (ret, args) pairs over the modelled Rust fragment, each with an
    ABI-compatible C counterpart when one exists."""
    sigs = []

    def rnd_ty(depth=0):
        r = rng.random()
        if r < 0.62 or depth >= 2:
            return rng.choice(RUST_SCALARS)
        if r < 0.86:
            inner = rng.choice([("cvoid",)] + RUST_SCALARS) if depth == 0 and rng.random() < 0.3 else rnd_ty(depth + 1)
            return ("ptr", rng.random() < 0.5, inner)
        if r < 0.95 or depth > 0:
            return ("transparent", None, rnd_ty(depth + 1))
        return ("zst", None)             # zero-sized values only as whole arguments

    for _ in range(n):
        nargs = rng.randint(0, 5)
        ret = rng.choice([("unit",)] * 2 + [rnd_ty(1) for _ in range(4)])
        while ret[0] == "zst":
            ret = rnd_ty(1)
        args = [rnd_ty() for _ in range(nargs)]
        sigs.append((ret, args))
    return sigs


def to_c(ty, rng):
    """ABI-compatible C type for a Rust type, or None."""
    k = ty[0]
    if k == "transparent":
        return to_c(ty[2], rng)
    if k == "ptr":
        if ty[2][0] == "cvoid":
            return ("ptr", not ty[1], ("b", "void"))
        inner = to_c(ty[2], rng)
        return None if inner is None else ("ptr", not ty[1], inner)
    if k == "unit":
        return ("b", "void")
    opts = RUST_TO_C.get(ty)
    return ("b", rng.choice(opts)) if opts else None


def part_d(tools, wd, checks, seed, count):
    d = os.path.join(wd, "diff")
    os.makedirs(d)
    rng = random.Random(seed)
    I = lambda n: ("int", n)                      # noqa: E731
    PM = lambda t: ("ptr", True, t)               # noqa: E731  *mut T
    PC = lambda t: ("ptr", False, t)              # noqa: E731  *const T
    CB = lambda n: ("b", n)                       # noqa: E731
    CP = lambda t: ("ptr", False, t)              # noqa: E731  T *
    CPK = lambda t: ("ptr", True, t)              # noqa: E731  T const *
    T = lambda t: ("transparent", None, t)        # noqa: E731
    Z = ("zst", None)
    U = ("unit",)
    # (rust_ret, rust_args, explicit C counterpart or None).  With None an
    # ABI-compatible C prototype is derived (random choice among LP64
    # spellings); signatures with zero-sized arguments get no C counterpart.
    fixed = [
        (I("u32"), [I("u32"), I("u32"), I("u32")], None),                       # S_ S_ S_
        (U, [I("i8"), I("u8"), I("i8"), I("u8")], None),                        # S_ and S0_
        (U, [PC(I("i32")), PC(I("i32")), I("i32")], None),
        (U, [PM(I("i32")), PC(I("i32"))], None),
        (U, [Z, Z], None),                                                      # every argument ignored -> v
        (U, [Z, I("u16")], None),
        (("bool",), [("bool",), ("char",), I("usize"), I("isize")], None),
        (I("u64"), [I("usize"), I("u64")], None),                               # distinct unless normalised
        (U, [PM(("cvoid",)), PC(("cvoid",))], None),
        (PC(PC(I("u8"))), [PC(I("u8"))], None),
        (U, [I(n) for n in ("i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "i8", "u64")], None),
        (I("u32"), [T(T(I("u32")))], None),
        (U, [("f32",), ("f64",), ("bool",), PM(("cvoid",))], None),             # integer-free
        # explicit C spellings: same-width integer aliases
        (U, [I("i64"), I("i64")], (CB("void"), [CB("long"), CB("llong")])),
        (U, [PM(I("i64")), PM(I("i64"))], (CB("void"), [CP(CB("long")), CP(CB("long"))])),
        (U, [PM(I("i64")), PM(I("i64"))], (CB("void"), [CP(CB("long")), CP(CB("llong"))])),
        (U, [PC(I("i8")), PC(I("i8"))], (CB("void"), [CPK(CB("char")), CPK(CB("schar"))])),
        (U, [PC(I("u64")), PC(I("u64")), I("u64")], (CB("void"), [CPK(CB("ulong")), CPK(CB("ullong")), CB("ullong")])),
        (PM(PM(I("i64"))), [PM(I("i64"))], (CP(CP(CB("long"))), [CP(CB("llong"))])),
    ]
    sigs = fixed + [(r, a, None) for r, a in gen_signatures(rng, count)]

    wrappers = []

    def spell(ty):
        if ty[0] == "transparent":
            inner = spell(ty[2])
            name = "W%d" % len(wrappers)
            wrappers.append("#[repr(transparent)] pub struct %s(pub %s);" % (name, inner))
            return name
        if ty[0] == "zst":
            return "Z0"
        if ty[0] == "ptr":
            return ("*mut " if ty[1] else "*const ") + spell(ty[2])
        return rust_spelling(ty)

    rs = ["#![allow(improper_ctypes_definitions, unused_variables, private_interfaces)]",
          "#![crate_type = \"lib\"]", "pub struct Z0;"]
    body, c_src, c_types = [], [], {}
    for i, (ret, args, explicit) in enumerate(sigs):
        params = ", ".join("a%d: %s" % (j, spell(a)) for j, a in enumerate(args))
        rsp = spell(ret)
        body.append("#[no_mangle] pub extern \"C\" fn sig_c_%d(%s) -> %s { loop {} }" % (i, params, rsp))
        body.append("#[no_mangle] pub fn sig_rust_%d(%s) -> %s { loop {} }" % (i, params, rsp))
        if explicit is not None:
            cret, cargs = explicit
        elif any(a[0] == "zst" for a in args):
            continue
        else:
            cret = to_c(ret, rng)
            cargs = [to_c(a, rng) for a in args]
            if cret is None or any(a is None for a in cargs):
                continue
        c_types[i] = (cret, cargs)
        cparams = ", ".join("%s a%d" % (c_decl(a), j) for j, a in enumerate(cargs)) or "void"
        c_src.append("%s csig_%d(%s) { __builtin_trap(); }" % (c_decl(cret), i, cparams))
    open(os.path.join(d, "sigs.rs"), "w").write("\n".join(rs + wrappers + body) + "\n")
    open(os.path.join(d, "sigs.c"), "w").write("\n".join(c_src) + "\n")

    def mentions_int(ty):
        if ty[0] in ("int", "char"):
            return True
        if ty[0] in ("ptr", "transparent"):
            return mentions_int(ty[2])
        return False

    res = {"prng_seed": seed, "signature_count": len(sigs), "c_counterparts": len(c_types), "modes": {}}
    mism = []
    cross_pred_fail = []
    cross = {}
    class_ok = {"default": True, "normalized": True}
    for label, norm in (("default", False), ("normalized", True)):
        rflags = RUST_KCFI_NORM if norm else RUST_KCFI
        cflags = CLANG_KCFI + (CLANG_NORM if norm else [])
        # All generated bodies are identical (`loop {}`), so LLVM's
        # MergeFunctions pass must be off here; its effect is measured below.
        must([tools.rustc] + RUST_BASE + rflags + ["-Zmerge-functions=disabled", "--emit=llvm-ir", "-o", "sigs_%s.ll" % label, "sigs.rs"], d)
        must([tools.clang, "-O1", "-S", "-emit-llvm", "-Wno-everything"] + cflags + ["sigs.c", "-o", "sigs_c_%s.ll" % label], d)
        r_ir = ir_functions(open(os.path.join(d, "sigs_%s.ll" % label)).read())
        c_ir = ir_functions(open(os.path.join(d, "sigs_c_%s.ll" % label)).read())
        n_r = n_c = 0
        cr = {"agree": 0, "differ": 0, "agree_examples": [], "differ_examples": []}
        for i, (ret, args, _e) in enumerate(sigs):
            tid = rust_typeid(ret, args, norm)
            for fn in ("sig_c_%d" % i, "sig_rust_%d" % i):
                n_r += 1
                got = r_ir.get(fn, {}).get("kcfi_type")
                if got != kcfi_id(tid):
                    mism.append({"tool": "rustc", "mode": label, "fn": fn, "model_typeid": tid, "model_id": kcfi_id(tid), "tool_id": got})
            if i not in c_types:
                continue
            cret, cargs = c_types[i]
            ctid = c_typeid(cret, cargs, norm)
            n_c += 1
            cgot = c_ir.get("csig_%d" % i, {}).get("kcfi_type")
            if cgot != kcfi_id(ctid):
                mism.append({"tool": "clang", "mode": label, "fn": "csig_%d" % i, "model_typeid": ctid, "model_id": kcfi_id(ctid), "tool_id": cgot})
            rgot = r_ir.get("sig_c_%d" % i, {}).get("kcfi_type")
            same = rgot == cgot
            if same != (tid == ctid):
                cross_pred_fail.append({"mode": label, "rust_typeid": tid, "c_typeid": ctid, "rustc_id": rgot, "clang_id": cgot})
            bucket = "agree" if same else "differ"
            cr[bucket] += 1
            if len(cr[bucket + "_examples"]) < 8:
                cr[bucket + "_examples"].append({"rust_typeid": tid, "c_typeid": ctid, "c_prototype": "%s (*)(%s)" % (c_decl(cret), ", ".join(c_decl(a) for a in cargs) or "void")})
            if norm:
                if same == c_mixes_same_width_integer_spellings(cret, cargs):
                    class_ok[label] = False
            else:
                has_int = mentions_int(ret) or any(mentions_int(a) for a in args)
                if same == has_int:
                    class_ok[label] = False
        cross[label] = cr
        res["modes"][label] = {"rustc_functions_compared": n_r, "clang_functions_compared": n_c}
    res["model_vs_tool_mismatches"] = mism
    res["cross_language_prediction_failures"] = cross_pred_fail
    res["cross_language"] = cross
    # Same source with rustc's default MergeFunctions setting at -Copt-level=2:
    # which exported symbols end up in front of a prefix word that is not the
    # id of their own signature?
    must([tools.rustc] + RUST_BASE + RUST_KCFI + ["--emit=llvm-ir", "-o", "sigs_merged.ll", "sigs.rs"], d)
    m_ir = ir_functions(open(os.path.join(d, "sigs_merged.ll")).read())
    wrong, aliases = [], 0
    for i, (ret, args, _e) in enumerate(sigs):
        own = kcfi_id(rust_typeid(ret, args, False))
        for fn in ("sig_c_%d" % i, "sig_rust_%d" % i):
            ent = m_ir.get(fn)
            if ent is None:
                continue
            if "alias_of" in ent:
                aliases += 1
                if ent["kcfi_type"] != own:
                    wrong.append({"symbol": fn, "own_typeid": rust_typeid(ret, args, False), "own_id": own,
                                  "alias_of": ent["alias_of"], "id_in_front_of_shared_entry": ent["kcfi_type"]})
    res["merge_functions_default_at_opt_level_2"] = {
        "symbols_emitted_as_aliases": aliases,
        "aliases_whose_shared_prefix_id_is_not_their_own": len(wrong),
        "examples": wrong[:6],
    }
    checks["D_rustc_model_matches_every_rustc_emitted_id"] = not [m for m in mism if m["tool"] == "rustc"]
    checks["D_clang_model_matches_every_clang_emitted_id"] = not [m for m in mism if m["tool"] == "clang"]
    checks["D_cross_language_equality_is_exactly_type_id_string_equality"] = not cross_pred_fail
    checks["D_default_ids_agree_iff_signature_has_no_integer_or_char"] = (
        class_ok["default"] and cross["default"]["agree"] > 0 and cross["default"]["differ"] > 0)
    checks["D_normalized_ids_differ_iff_c_prototype_mixes_same_width_integer_spellings_under_pointers"] = (
        class_ok["normalized"] and cross["normalized"]["agree"] > 0 and cross["normalized"]["differ"] > 0)
    return res


# --------------------------------------------------------------------------
# Part E: two distinct function types with one 32-bit id
# --------------------------------------------------------------------------
COLLISION_TYPES = ["i8", "i16", "i32", "i64", "isize", "u8", "u16", "u32", "u64", "usize", "f32", "f64", "bool", "char"]


def _ctype(name):
    return {"f32": ("f32",), "f64": ("f64",), "bool": ("bool",), "char": ("char",)}.get(name, ("int", name))


def find_collision(max_len=5):
    """First pair (in a fixed enumeration order) of Rust-ABI signatures
    `fn(distinct scalar params...)` whose type-id strings differ and whose
    32-bit ids are equal.  Parameters are pairwise distinct types, so the
    strings contain no substitutions."""
    seen = {}
    tested = 0
    for n in range(1, max_len + 1):
        for perm in itertools.permutations(COLLISION_TYPES, n):
            tid = rust_typeid(("unit",), [_ctype(t) for t in perm], False)
            h = xxh64(tid.encode())
            tested += 1
            k = h & 0xFFFFFFFF
            if k in seen and seen[k][0] != tid:
                return {"a": {"params": list(seen[k][1]), "typeid": seen[k][0], "xxh64": "0x%016x" % seen[k][2]},
                        "b": {"params": list(perm), "typeid": tid, "xxh64": "0x%016x" % h},
                        "shared_low32": k, "candidates_hashed_before_hit": tested}
            seen.setdefault(k, (tid, perm, h))
    return None


def part_e(tools, wd, checks):
    d = os.path.join(wd, "collision")
    os.makedirs(d)
    col = find_collision()
    res = {"search_space": "Rust-ABI fn(p1..pn) with n<=5 pairwise-distinct parameter types from %s, return ()" % COLLISION_TYPES,
           "collision": col}
    if not col:
        checks["E_collision_found"] = False
        return res
    a, b = col["a"]["params"], col["b"]["params"]
    # a third signature that does not collide, for the negative control
    cparams = ["u64", "u8"]
    lit = {"f32": "1.0", "f64": "1.0", "bool": "true", "char": "'x'"}

    def plist(ps):
        return ", ".join("_p%d: %s" % (i, t) for i, t in enumerate(ps))

    def tlist(ps):
        return ", ".join(ps)

    def alist(ps):
        return ", ".join(lit.get(t, "1") for t in ps)

    src = """
use std::hint::black_box;
use std::sync::atomic::{AtomicU32, Ordering};
static HIT: AtomicU32 = AtomicU32::new(0);
#[inline(never)] pub fn col_a(%s) { HIT.store(0xA, Ordering::SeqCst); }
#[inline(never)] pub fn col_b(%s) { HIT.store(0xB, Ordering::SeqCst); }
#[inline(never)] pub fn col_c(%s) { HIT.store(0xC, Ordering::SeqCst); }
#[inline(never)] fn call_as_b(f: fn(%s)) { f(%s) }
fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let f: fn(%s) = match mode.as_str() {
        "b" => col_b,
        "a_as_b" => unsafe { std::mem::transmute(col_a as fn(%s)) },
        "c_as_b" => unsafe { std::mem::transmute(col_c as fn(%s)) },
        _ => std::process::exit(2),
    };
    call_as_b(black_box(f));
    println!("CALLEE_RAN={:X}", HIT.load(Ordering::SeqCst));
}
""" % (plist(a), plist(b), plist(cparams), tlist(b), alist(b), tlist(b), tlist(a), tlist(cparams))
    open(os.path.join(d, "collision.rs"), "w").write(src)
    res["source"] = src
    flags = RUST_BASE + RUST_KCFI
    must([tools.rustc] + flags + ["--emit=llvm-ir", "-o", "collision.ll", "collision.rs"], d)
    must([tools.rustc] + flags + ["-o", "collision.bin", "collision.rs"], d)
    fns = ir_functions(open(os.path.join(d, "collision.ll")).read())
    ids = {}
    for nm in ("col_a", "col_b", "col_c", "call_as_b"):
        hit = [k for k in fns if ("5" + nm) in k or ("9" + nm) in k]
        ids[nm] = fns[hit[0]] if len(hit) == 1 else None
    res["rustc_kcfi_type"] = {nm: (v["kcfi_type"] if v else None) for nm, v in ids.items() if nm != "call_as_b"}
    res["rustc_call_site_expected_id"] = ids["call_as_b"]["kcfi_bundles"] if ids["call_as_b"] else None
    res["exec"] = {m: execute("collision.bin", [m], d) for m in ("b", "a_as_b", "c_as_b")}
    checks["E_collision_found_with_distinct_strings_and_distinct_64_bit_hashes"] = (
        col["a"]["typeid"] != col["b"]["typeid"] and col["a"]["xxh64"] != col["b"]["xxh64"])
    checks["E_rustc_emits_the_same_id_for_both_signatures"] = (
        res["rustc_kcfi_type"]["col_a"] == res["rustc_kcfi_type"]["col_b"] == col["shared_low32"]
        and res["rustc_kcfi_type"]["col_c"] != col["shared_low32"])
    checks["E_wrong_signature_call_through_colliding_id_is_not_trapped"] = (
        res["exec"]["a_as_b"] == {"rc": 0, "stdout": "CALLEE_RAN=A"} and res["exec"]["b"] == {"rc": 0, "stdout": "CALLEE_RAN=B"})
    checks["E_wrong_signature_call_without_collision_dies_with_SIGILL"] = res["exec"]["c_as_b"] == {"rc": -4, "stdout": ""}
    return res


# --------------------------------------------------------------------------
# Part F: target-modifier gating
# --------------------------------------------------------------------------
def part_f(tools, wd, checks):
    d = os.path.join(wd, "gate")
    os.makedirs(d)
    open(os.path.join(d, "m.rs"), "w").write("fn main() {}\n")
    cases = {
        "kcfi_without_panic_abort": ["-Zsanitizer=kcfi"],
        "kcfi_no_allow": ["-Cpanic=abort", "-Zsanitizer=kcfi"],
        "kcfi_allow_sanitizer": ["-Cpanic=abort", "-Zsanitizer=kcfi", "-Cunsafe-allow-abi-mismatch=sanitizer"],
        "kcfi_normalize_allow_sanitizer_only": ["-Cpanic=abort", "-Zsanitizer=kcfi", "-Zsanitizer-cfi-normalize-integers",
                                                "-Cunsafe-allow-abi-mismatch=sanitizer"],
        "kcfi_normalize_allow_both": ["-Cpanic=abort", "-Zsanitizer=kcfi", "-Zsanitizer-cfi-normalize-integers",
                                      "-Cunsafe-allow-abi-mismatch=sanitizer,sanitizer-cfi-normalize-integers"],
        "kcfi_normalize_allow_as_two_separate_flags": ["-Cpanic=abort", "-Zsanitizer=kcfi", "-Zsanitizer-cfi-normalize-integers",
                                                       "-Cunsafe-allow-abi-mismatch=sanitizer",
                                                       "-Cunsafe-allow-abi-mismatch=sanitizer-cfi-normalize-integers"],
        "normalize_without_cfi_or_kcfi": ["-Cpanic=abort", "-Zsanitizer-cfi-normalize-integers"],
    }
    res = {}
    for name, flags in cases.items():
        rc, _out, err = run([tools.rustc, "--edition", "2021"] + flags + ["-o", "m_%s.bin" % name, "m.rs"], d)
        first = [l for l in err.splitlines() if l.startswith("error")]
        notes = [l.strip() for l in err.splitlines() if l.strip().startswith("= note:")]
        res[name] = {"flags": flags, "rustc_exit_code": rc, "first_error": first[0] if first else None,
                     "distinct_error_lines": sorted(set(first)), "note_count": len(notes), "first_note": notes[0] if notes else None}
    checks["F_kcfi_requires_panic_abort"] = res["kcfi_without_panic_abort"]["rustc_exit_code"] != 0
    checks["F_mixing_sanitizer_is_rejected_without_allow"] = (
        res["kcfi_no_allow"]["rustc_exit_code"] != 0 and "ABI mismatch" in (res["kcfi_no_allow"]["first_error"] or ""))
    checks["F_allow_sanitizer_accepts_kcfi"] = res["kcfi_allow_sanitizer"]["rustc_exit_code"] == 0
    checks["F_normalize_integers_is_a_separate_target_modifier_under_kcfi"] = (
        res["kcfi_normalize_allow_sanitizer_only"]["rustc_exit_code"] != 0
        and "sanitizer-cfi-normalize-integers" in (res["kcfi_normalize_allow_sanitizer_only"]["first_error"] or "")
        and res["kcfi_normalize_allow_both"]["rustc_exit_code"] == 0)
    checks["F_repeating_the_allow_flag_does_not_accumulate"] = (
        res["kcfi_normalize_allow_as_two_separate_flags"]["rustc_exit_code"] != 0
        and "`-Zsanitizer`" in (res["kcfi_normalize_allow_as_two_separate_flags"]["first_error"] or ""))
    checks["F_normalize_integers_requires_cfi_or_kcfi"] = res["normalize_without_cfi_or_kcfi"]["rustc_exit_code"] != 0
    return res


# --------------------------------------------------------------------------
# Part G: LLVM MergeFunctions folds functions whose KCFI ids differ
# --------------------------------------------------------------------------
MERGE_RS = r"""
use std::hint::black_box;

// Two safe functions with different Rust types, the same LLVM type
// `i32 (ptr, ptr)`, and the same body.
#[inline(never)]
pub fn f_i32(a: *mut i32, b: *const i32) -> u32 { let _ = (a, b); 7 }
#[inline(never)]
pub fn f_u8(a: *mut u8, b: *const u8) -> u32 { let _ = (a, b); 7 }

#[inline(never)]
fn call_i32(f: fn(*mut i32, *const i32) -> u32) -> u32 { f(std::ptr::null_mut(), std::ptr::null()) }
#[inline(never)]
fn call_u8(f: fn(*mut u8, *const u8) -> u32) -> u32 { f(std::ptr::null_mut(), std::ptr::null()) }

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "i32" => println!("I32_OK={}", call_i32(black_box(f_i32))),
        "u8" => println!("U8_OK={}", call_u8(black_box(f_u8))),
        _ => std::process::exit(2),
    }
}
"""


def part_g(tools, wd, checks):
    d = os.path.join(wd, "merge")
    os.makedirs(d)
    open(os.path.join(d, "merge.rs"), "w").write(MERGE_RS)
    base = [f for f in RUST_BASE if not f.startswith("-Copt-level")]
    configs = {
        "no_sanitizer_O2": ["-Copt-level=2"],
        "kcfi_O1": ["-Copt-level=1"] + RUST_KCFI,
        "kcfi_O2": ["-Copt-level=2"] + RUST_KCFI,
        "kcfi_O2_merge_functions_trampolines": ["-Copt-level=2", "-Zmerge-functions=trampolines"] + RUST_KCFI,
        "kcfi_O2_merge_functions_disabled": ["-Copt-level=2", "-Zmerge-functions=disabled"] + RUST_KCFI,
    }
    res = {"source": MERGE_RS, "configs": {}}
    tid_i32 = rust_typeid(("int", "u32"), [("ptr", True, ("int", "i32")), ("ptr", False, ("int", "i32"))], False)
    tid_u8 = rust_typeid(("int", "u32"), [("ptr", True, ("int", "u8")), ("ptr", False, ("int", "u8"))], False)
    res["model"] = {"f_i32": {"typeid": tid_i32, "id": kcfi_id(tid_i32)}, "f_u8": {"typeid": tid_u8, "id": kcfi_id(tid_u8)}}
    for name, flags in configs.items():
        exe, ll = "merge_%s.bin" % name, "merge_%s.ll" % name
        must([tools.rustc] + base + flags + ["--emit=llvm-ir", "-o", ll, "merge.rs"], d)
        must([tools.rustc] + base + flags + ["-o", exe, "merge.rs"], d)
        fns = ir_functions(open(os.path.join(d, ll)).read())
        defs = {}
        for short in ("f_i32", "f_u8", "call_i32", "call_u8"):
            hit = [k for k in fns if k.endswith("5merge%d%s" % (len(short), short))]
            defs[short] = ({"kcfi_type": fns[hit[0]]["kcfi_type"], "kcfi_bundles": fns[hit[0]]["kcfi_bundles"],
                            "alias_of": fns[hit[0]].get("alias_of")} if hit else None)
        res["configs"][name] = {"rustc_flags": base + flags, "ir": defs,
                                "exec": {m: execute(exe, [m], d) for m in ("i32", "u8")}}
    c = res["configs"]
    ok = lambda e: e["exec"]["i32"] == {"rc": 0, "stdout": "I32_OK=7"} and e["exec"]["u8"] == {"rc": 0, "stdout": "U8_OK=7"}  # noqa: E731
    checks["G_type_correct_calls_return_without_sanitizer_and_with_merging_off_or_O1"] = (
        ok(c["no_sanitizer_O2"]) and ok(c["kcfi_O1"]) and ok(c["kcfi_O2_merge_functions_disabled"]))
    trapped = lambda e: sorted([e["exec"]["i32"]["rc"], e["exec"]["u8"]["rc"]]) == [-4, 0]  # noqa: E731
    checks["G_kcfi_O2_default_merging_makes_one_type_correct_call_die_with_SIGILL"] = trapped(c["kcfi_O2"])
    checks["G_kcfi_O2_trampolines_mode_also_dies_with_SIGILL"] = trapped(c["kcfi_O2_merge_functions_trampolines"])
    gone = [k for k in ("f_i32", "f_u8") if c["kcfi_O2"]["ir"][k] is None or c["kcfi_O2"]["ir"][k].get("alias_of")]
    res["kcfi_O2_function_without_own_definition"] = gone
    checks["G_kcfi_O2_one_of_the_two_definitions_is_folded_into_the_other"] = len(gone) == 1
    checks["G_both_definitions_and_both_ids_survive_with_merging_disabled"] = (
        c["kcfi_O2_merge_functions_disabled"]["ir"]["f_i32"] is not None
        and c["kcfi_O2_merge_functions_disabled"]["ir"]["f_u8"] is not None
        and c["kcfi_O2_merge_functions_disabled"]["ir"]["f_i32"]["kcfi_type"] == res["model"]["f_i32"]["id"]
        and c["kcfi_O2_merge_functions_disabled"]["ir"]["f_u8"]["kcfi_type"] == res["model"]["f_u8"]["id"])
    return res


# --------------------------------------------------------------------------
# Part A and main
# --------------------------------------------------------------------------
def part_a(checks):
    vectors = {
        "": 0xEF46DB3751D8E999,
        "a": 0xD24EC4F1A98C6E5B,
        "abc": 0x44BC2CF5AD770999,
        "Nobody inspects the spammish repetition": 0xFBCEA83C8A378BF1,
    }
    got = {k: xxh64(k.encode()) for k in vectors}
    checks["A_xxh64_reference_vectors"] = got == vectors
    strings = [
        "_ZTSFmiE", "_ZTSFyiE", "_ZTSFu3u64u3i32E", "_ZTSFu3u64u3i32E.normalized",
        "_ZTSFjjE", "_ZTSFu3u32S_E", "_ZTSFu3u32S_E.normalized",
        "_ZTSFu3u64u3i64E", "_ZTSFu3u64u3i64E.normalized",
    ]
    table = {}
    for s in strings:
        h = xxh64(s.encode())
        k = h & 0xFFFFFFFF
        table[s] = {"xxh64": "0x%016x" % h, "kcfi_id": k, "kcfi_id_hex": "0x%08x" % k,
                    "negated_mod_2_32_hex": "0x%08x" % u32(-mask_kcfi_type(k))}
    return {"reference_vectors": {repr(k): "0x%016x" % v for k, v in got.items()}, "type_id_strings": table}


def cpu_model():
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None, help="write JSON here (default: stdout)")
    ap.add_argument("--keep", default=None, help="build in this directory and keep it")
    ap.add_argument("--seed", type=int, default=20261122)
    ap.add_argument("--count", type=int, default=160)
    args = ap.parse_args()
    tools = Tools()
    checks = {}
    out = {"schema": "kcfi-probe/1"}

    def ver(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, text=True).stdout.strip().splitlines()
        except OSError as e:
            return ["<unavailable: %s>" % e.__class__.__name__]

    rv = ver([tools.rustc, "-vV"])
    out["toolchain"] = {
        "rustc": [l for l in rv if not l.startswith("binary:")],
        "clang": ver([tools.clang, "--version"])[:2],
        "llvm_objdump": [l.strip() for l in ver([tools.objdump, "--version"]) if "version" in l][:1],
        "uname_machine": os.uname().machine, "uname_sysname": os.uname().sysname,
        "cpu_model": cpu_model(),
    }
    out["A_xxh64"] = part_a(checks)

    def body(wd):
        out["B_cross_language_ffi"] = part_b(tools, wd, checks)
        out["C_reify_shim"] = part_c(tools, wd, checks)
        out["D_encoder_model_differential"] = part_d(tools, wd, checks, args.seed, args.count)
        out["E_truncation_collision"] = part_e(tools, wd, checks)
        out["F_target_modifier_gating"] = part_f(tools, wd, checks)
        out["G_merge_functions"] = part_g(tools, wd, checks)

    if args.keep:
        os.makedirs(args.keep, exist_ok=True)
        body(args.keep)
    else:
        with tempfile.TemporaryDirectory(prefix="kcfi_probe_") as wd:
            body(wd)
    out["checks"] = checks
    out["all_checks_hold"] = all(checks.values())
    text = json.dumps(out, indent=2, sort_keys=False) + "\n"
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)
    failed = [k for k, v in checks.items() if not v]
    sys.stderr.write("checks: %d held, %d failed%s\n" % (len(checks) - len(failed), len(failed), (": " + ", ".join(failed)) if failed else ""))
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
