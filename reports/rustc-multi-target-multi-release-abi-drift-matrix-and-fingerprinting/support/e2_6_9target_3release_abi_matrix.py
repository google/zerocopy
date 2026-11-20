#!/usr/bin/env python3
"""9-Target x 3-Release Real `rustc` Procedural ABI Differential Matrix.

Compiles a self-contained `#![no_core]` suite of 100+ Rust ABI signatures across:
- 3 real `rustc` releases: `1.99.1` (`58cf8f9c3`), `1.100.0` (`0ef1bc386`), `1.102.0-nightly` (`3ef0c22cd`)
- 9 targets: all 8 Tier-1/platform targets (`x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`,
  `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-unknown-linux-gnu`,
  `aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `i686-unknown-linux-gnu`, `i686-pc-windows-msvc`)
using `-C opt-level=0 --emit=llvm-ir` (so `MergeFunctions` never aliases distinct `define` headers),
and extracts exact normalized LLVM IR parameter/return ABI lowering + symbol mangling (`@@N` on Windows/vectorcall).

"""
import argparse
import json
import os
import re
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

DEFAULT_OUT_JSON = Path(__file__).resolve().parent / "e2_6_9target_3release_abi_matrix.json"

TOOLCHAINS = [
    ("1.99.1", "+1.99.1"),
    ("1.100.0", "+1.100.0"),
    ("1.102.0-nightly", "+nightly"),
]

TARGETS = [
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "aarch64-pc-windows-msvc",
    "i686-unknown-linux-gnu",
    "i686-pc-windows-msvc",
]

RUST_HEADER = r"""#![crate_type = "lib"]
#![allow(internal_features, improper_ctypes_definitions, non_camel_case_types, unused_variables)]
#![feature(no_core, lang_items, repr_simd, auto_traits, abi_vectorcall)]
#![no_core]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}

pub struct ZstStruct;

#[repr(transparent)]
pub struct TransU64(pub u64);

#[repr(transparent)]
pub struct TransWithZst(pub ZstStruct, pub f32);

#[repr(C)]
pub struct PairU64(pub u64, pub u64);

#[repr(C)]
pub struct TripleU64(pub u64, pub u64, pub u64);

#[repr(C)]
pub struct Sub8Bytes(pub u8, pub u16, pub u8);

#[repr(C, packed)]
pub struct PackedU16U64(pub u16, pub u64);

#[repr(C, align(16))]
pub struct Align16U64(pub u64);

#[repr(C)]
pub struct HfaF32x2(pub f32, pub f32);

#[repr(C)]
pub struct HfaF32x3(pub f32, pub f32, pub f32);

#[repr(C)]
pub struct HfaF32x4(pub f32, pub f32, pub f32, pub f32);

#[repr(C)]
pub struct HfaF32x5(pub f32, pub f32, pub f32, pub f32, pub f32);

#[repr(C)]
pub struct HfaF64x2(pub f64, pub f64);

#[repr(C)]
pub struct MixedIntFloat(pub u32, pub f32);

#[repr(C)]
pub struct MixedFloatInt(pub f32, pub u32);

#[repr(C)]
pub struct MixedU64F64(pub u64, pub f64);

pub struct RustPair(pub u32, pub u64);

pub enum ZstSingleEnum { Only }

#[repr(u8)]
pub enum TagU8Enum { A = 0, B = 1, C = 255 }

pub enum NicheRefEnum<'a> { None, Some(&'a u64) }

pub enum NicheResultU64 { Ok(u64), Err(u32) }

#[repr(simd)]
pub struct SimdF32x2([f32; 2]);

#[repr(simd)]
pub struct SimdF32x4([f32; 4]);

#[repr(simd)]
pub struct SimdI32x4([i32; 4]);

#[repr(simd)]
pub struct SimdU8x16([u8; 16]);

#[repr(simd)]
pub struct SimdF64x2([f64; 2]);

#[repr(simd)]
pub struct SimdF32x8([f32; 8]);

#[repr(simd)]
pub struct SimdI64x4([i64; 4]);

#[repr(simd)]
pub struct SimdF32x16([f32; 16]);
"""

BASE_TYPES = [
    ("unit", "()"),
    ("bool", "bool"),
    ("u8", "u8"),
    ("i16", "i16"),
    ("u32", "u32"),
    ("i64", "i64"),
    ("usize", "usize"),
    ("u128", "u128"),
    ("i128", "i128"),
    ("f32", "f32"),
    ("f64", "f64"),
    ("zst_struct", "ZstStruct"),
    ("trans_u64", "TransU64"),
    ("trans_zst_f32", "TransWithZst"),
    ("pair_u64", "PairU64"),
    ("triple_u64", "TripleU64"),
    ("sub8_bytes", "Sub8Bytes"),
    ("packed_u16_u64", "PackedU16U64"),
    ("align16_u64", "Align16U64"),
    ("hfa_f32x2", "HfaF32x2"),
    ("hfa_f32x3", "HfaF32x3"),
    ("hfa_f32x4", "HfaF32x4"),
    ("hfa_f32x5", "HfaF32x5"),
    ("hfa_f64x2", "HfaF64x2"),
    ("mixed_int_float", "MixedIntFloat"),
    ("mixed_float_int", "MixedFloatInt"),
    ("mixed_u64_f64", "MixedU64F64"),
    ("rust_pair", "RustPair"),
    ("zst_enum", "ZstSingleEnum"),
    ("tag_u8_enum", "TagU8Enum"),
    ("niche_ref_enum", "NicheRefEnum<'static>"),
    ("niche_res_u64", "NicheResultU64"),
    ("fat_slice_ptr", "*const [u8]"),
    ("simd_f32x2", "SimdF32x2"),
    ("simd_f32x4", "SimdF32x4"),
    ("simd_i32x4", "SimdI32x4"),
    ("simd_u8x16", "SimdU8x16"),
    ("simd_f64x2", "SimdF64x2"),
    ("simd_f32x8", "SimdF32x8"),
    ("simd_i64x4", "SimdI64x4"),
    ("simd_f32x16", "SimdF32x16"),
]


def build_rust_suite() -> tuple[str, list[str]]:
    lines = [RUST_HEADER]
    fn_names = []
    # 1. All 41 types in extern "Rust"; 38 base types in extern "C" (256/512-bit C-ABI SIMD requires target_feature on x86/aarch64)
    wide_simd = {"simd_f32x8", "simd_i64x4", "simd_f32x16"}
    for slug, ty in BASE_TYPES:
        r_name = f"abi_rust_{slug}"
        lines.append(f'#[no_mangle] pub fn {r_name}(x: {ty}) -> {ty} {{ x }}')
        fn_names.append(r_name)
        if slug not in wide_simd:
            c_name = f"abi_c_{slug}"
            lines.append(f'#[no_mangle] pub extern "C" fn {c_name}(x: {ty}) -> {ty} {{ x }}')
            fn_names.append(c_name)
    # Also test wide SIMD under extern "C" on x86_64 with explicit avx / avx512f
    lines.append('#[cfg(target_arch = "x86_64")] #[target_feature(enable = "avx")] #[no_mangle] pub unsafe extern "C" fn abi_c_avx_simd_f32x8(x: SimdF32x8) -> SimdF32x8 { x }')
    lines.append('#[cfg(target_arch = "x86_64")] #[target_feature(enable = "avx")] #[no_mangle] pub unsafe extern "C" fn abi_c_avx_simd_i64x4(x: SimdI64x4) -> SimdI64x4 { x }')
    lines.append('#[cfg(target_arch = "x86_64")] #[target_feature(enable = "avx512f")] #[no_mangle] pub unsafe extern "C" fn abi_c_avx512_simd_f32x16(x: SimdF32x16) -> SimdF32x16 { x }')
    fn_names.extend(["abi_c_avx_simd_f32x8", "abi_c_avx_simd_i64x4", "abi_c_avx512_simd_f32x16"])

    # 2. Multi-arg register exhaustion / split-stack probes (8 fns)
    multi = [
        ("abi_rust_many_gpr8", 'pub fn abi_rust_many_gpr8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 { a }'),
        ("abi_c_many_gpr8", 'pub extern "C" fn abi_c_many_gpr8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) -> u64 { h }'),
        ("abi_c_many_fp9", 'pub extern "C" fn abi_c_many_fp9(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, g: f64, h: f64, i: f64) -> f64 { i }'),
        ("abi_c_odd_i128_align", 'pub extern "C" fn abi_c_odd_i128_align(pad: u32, big: u128, tail: u32) -> u128 { big }'),
        ("abi_rust_odd_i128_align", 'pub fn abi_rust_odd_i128_align(pad: u32, big: u128, tail: u32) -> u128 { big }'),
        ("abi_c_unwind_pair", 'pub extern "C-unwind" fn abi_c_unwind_pair(x: PairU64) -> PairU64 { x }'),
        ("abi_system_u64_f32", 'pub extern "system" fn abi_system_u64_f32(a: u64, b: f32) -> f32 { b }'),
        ("abi_efiapi_pair", 'pub extern "efiapi" fn abi_efiapi_pair(a: u64, b: PairU64, c: f64) -> PairU64 { b }'),
    ]
    for nm, decl in multi:
        lines.append(f"#[no_mangle] {decl}")
        fn_names.append(nm)

    # 3. x86 / x86_64 calling-convention probes (vectorcall, sysv64, win64, fastcall, stdcall, thiscall)
    x86_cc = [
        ("abi_vec_f32x4", '#[cfg(any(target_arch = "x86", target_arch = "x86_64"))] #[no_mangle] pub extern "vectorcall" fn abi_vec_f32x4(a: SimdF32x4, b: SimdF32x4) -> SimdF32x4 { a }'),
        ("abi_vec_hfa4", '#[cfg(any(target_arch = "x86", target_arch = "x86_64"))] #[no_mangle] pub extern "vectorcall" fn abi_vec_hfa4(a: HfaF32x4, b: f32) -> HfaF32x4 { a }'),
        ("abi_vec_f32x8", '#[cfg(any(target_arch = "x86", target_arch = "x86_64"))] #[target_feature(enable = "avx")] #[no_mangle] pub unsafe extern "vectorcall" fn abi_vec_f32x8(a: SimdF32x8) -> SimdF32x8 { a }'),
        ("abi_vec_many6_simd", '#[cfg(any(target_arch = "x86", target_arch = "x86_64"))] #[no_mangle] pub extern "vectorcall" fn abi_vec_many6_simd(a: SimdF32x4, b: SimdF32x4, c: SimdF32x4, d: SimdF32x4, e: SimdF32x4, f: SimdF32x4, g: SimdF32x4) -> SimdF32x4 { g }'),
        ("abi_sysv64_hfa2", '#[cfg(target_arch = "x86_64")] #[no_mangle] pub extern "sysv64" fn abi_sysv64_hfa2(a: HfaF64x2, b: u128) -> HfaF64x2 { a }'),
        ("abi_win64_hfa2", '#[cfg(target_arch = "x86_64")] #[no_mangle] pub extern "win64" fn abi_win64_hfa2(a: HfaF64x2, b: u128) -> HfaF64x2 { a }'),
        ("abi_fastcall_i686", '#[cfg(target_arch = "x86")] #[no_mangle] pub extern "fastcall" fn abi_fastcall_i686(a: u32, b: u32, c: f32, d: u64) -> f32 { c }'),
        ("abi_stdcall_i686", '#[cfg(target_arch = "x86")] #[no_mangle] pub extern "stdcall" fn abi_stdcall_i686(a: u32, b: PairU64) -> u32 { a }'),
        ("abi_thiscall_i686", '#[cfg(target_arch = "x86")] #[no_mangle] pub extern "thiscall" fn abi_thiscall_i686(this: *const u8, a: u32, b: f32) -> f32 { b }'),
    ]
    for nm, decl in x86_cc:
        lines.append(decl)
        fn_names.append(nm)

    return "\n".join(lines) + "\n", fn_names


def normalize_llvm_def_header(line: str) -> tuple[str, str, str]:
    """Extract (base_fn_name, raw_symbol, normalized_signature_without_var_names_or_attr_groups)."""
    # Example: define void @"_ZN..."(ptr sret([16 x i8]) align 16 %_0, ...) unnamed_addr #0 !guid !1 {
    s = re.sub(r"\s+unnamed_addr.*$", "", line.strip())
    s = re.sub(r"\s+#\d+.*$", "", s)
    s = re.sub(r"\s*\{$", "", s)
    # Extract symbol @foo or @"\01_abi_vec_f32x4@@32"
    m = re.search(r'@("([^"]+)"|([A-Za-z0-9_.$@]+))\s*\(', s)
    if not m:
        return ("", "", s)
    raw_sym = m.group(2) if m.group(2) is not None else m.group(3)
    # Strip leading \01 or _ or ? and trailing @@N to map back to base name
    clean_sym = raw_sym.replace("\\01", "")
    base = re.sub(r"^[_@?]+", "", clean_sym)
    base = re.sub(r"@@?\d+$", "", base)
    # Normalize parameter names (%_0, %x, %a, etc.) and volatile captures(none)/nocapture differences?
    # Wait: keep TWO normalizations:
    # 1. `abi_shape`: calling conv + return type/sret + parameter types/sret/byval/inreg/align (stripping non-ABI optimization attrs like nofree/nosync/captures/nocapture/noundef/dead_on_unwind/dead_on_return/initializes/writable/writeonly/readonly/returned)
    # 2. `full_header`: full header with only SSA %var names normalized
    before_sym = s[: m.start()].replace("define ", "").strip()
    params_str = s[m.end() - 1 :]  # includes (...)
    full_norm = f"{before_sym} @{raw_sym}{re.sub(r'%[A-Za-z0-9_.]+', '%_', params_str)}"

    # Extract pure ABI-relevant shape (calling convention, return type, sret, byval, inreg, swift*, parameter LLVM types, symbol @@N suffix!)
    def strip_opt_attrs(tok: str) -> str:
        # Remove attributes that change LLVM optimization metadata without changing machine register/stack calling convention
        for pat in (
            r"\bnoundef\b",
            r"\bnofree\b",
            r"\bnosync\b",
            r"\bnoalias\b",
            r"\bnonnull\b",
            r"\breadonly\b",
            r"\bwriteonly\b",
            r"\bwritable\b",
            r"\breturned\b",
            r"\bdead_on_unwind\b",
            r"\bdead_on_return\b",
            r"\bcaptures\([^)]*\)",
            r"\bnocapture\b",
            r"\binitializes\([^)]*\)",
            r"\bdereferenceable(?:_or_null)?\(\d+\)",
            r"\brange\([^)]*\)",
        ):
            tok = re.sub(pat, "", tok)
        tok = re.sub(r"%[A-Za-z0-9_.]+", "", tok)
        return " ".join(tok.split())

    ret_abi = strip_opt_attrs(before_sym)
    inner_params = params_str.strip()
    if inner_params.startswith("(") and inner_params.endswith(")"):
        inner_params = inner_params[1:-1]
    # Split top-level commas (respecting parens/brackets)
    parts, cur, depth = [], [], 0
    for ch in inner_params:
        if ch in "([<":
            depth += 1
        elif ch in ")]>":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(strip_opt_attrs("".join(cur)))
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        parts.append(strip_opt_attrs("".join(cur)))
    mangle_suffix = ""
    ms = re.search(r"(@@?\d+)$", clean_sym)
    if ms:
        mangle_suffix = ms.group(1)
    abi_shape = f"{ret_abi} ({', '.join(parts)}){mangle_suffix}"
    return (base, raw_sym, abi_shape + " || RAW: " + full_norm)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run 9-target x 3-release rustc ABI differential matrix.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_JSON, help="Output JSON path")
    args = parser.parse_args()
    out_json = args.out
    suite_src, expected_fns = build_rust_suite()
    with tempfile.TemporaryDirectory(prefix="rustc_abi_matrix_") as tmp_str:
        tmp = Path(tmp_str)
        rs_path = tmp / "abi_matrix.rs"
        rs_path.write_text(suite_src, encoding="utf-8")

        tc_meta = {}
        matrix = {}  # matrix[tc_label][target][fn_name] = {"sym": ..., "abi_shape": ..., "raw": ...}
        compile_status = {}

        for tc_label, tc_arg in TOOLCHAINS:
            vv = subprocess.run(
                ["rustc", tc_arg, "-vV"], cwd=str(tmp), text=True, capture_output=True, check=True
            ).stdout.strip()
            tc_meta[tc_label] = vv
            matrix[tc_label] = {}
            compile_status[tc_label] = {}
            for tgt in TARGETS:
                ll_out = tmp / f"out_{tc_label}_{tgt}.ll"
                env = os.environ.copy()
                env["RUSTC_BOOTSTRAP"] = "1"
                env["RUSTC_ICE"] = "0"
                r = subprocess.run(
                    [
                        "rustc",
                        tc_arg,
                        "--target",
                        tgt,
                        "-C",
                        "opt-level=0",
                        "-C",
                        "debuginfo=0",
                        "--emit=llvm-ir",
                        str(rs_path),
                        "-o",
                        str(ll_out),
                    ],
                    cwd=str(tmp),
                    env=env,
                    text=True,
                    capture_output=True,
                    timeout=60,
                )
                if r.returncode != 0:
                    compile_status[tc_label][tgt] = {"ok": False, "stderr": r.stderr[:500]}
                    continue
                defs = {}
                for ln in ll_out.read_text(encoding="utf-8", errors="replace").splitlines():
                    if ln.startswith("define "):
                        base, raw_sym, combined = normalize_llvm_def_header(ln)
                        if base:
                            abi_sh, raw_h = combined.split(" || RAW: ", 1)
                            defs[base] = {"sym": raw_sym, "abi_shape": abi_sh, "full_header": raw_h}
                matrix[tc_label][tgt] = defs
                compile_status[tc_label][tgt] = {"ok": True, "emitted_fns": len(defs)}

        # Compute exact cross-release ABI drift across all 9 targets!
        drift_199_to_1100 = []
        drift_1100_to_nightly = []
        drift_199_to_nightly = []
        attr_only_churn_199_to_1100 = Counter()
        attr_only_churn_1100_to_nightly = Counter()

        total_pairs_199_1100 = 0
        total_pairs_1100_nightly = 0

        for tgt in TARGETS:
            m99 = matrix["1.99.1"].get(tgt, {})
            m100 = matrix["1.100.0"].get(tgt, {})
            mnight = matrix["1.102.0-nightly"].get(tgt, {})
            for fn in sorted(set(m99) & set(m100)):
                total_pairs_199_1100 += 1
                if m99[fn]["abi_shape"] != m100[fn]["abi_shape"]:
                    drift_199_to_1100.append(
                        {
                            "target": tgt,
                            "fn": fn,
                            "abi_1_99_1": m99[fn]["abi_shape"],
                            "abi_1_100_0": m100[fn]["abi_shape"],
                            "sym_1_99_1": m99[fn]["sym"],
                            "sym_1_100_0": m100[fn]["sym"],
                        }
                    )
                elif m99[fn]["full_header"] != m100[fn]["full_header"]:
                    attr_only_churn_199_to_1100[tgt] += 1

            for fn in sorted(set(m100) & set(mnight)):
                total_pairs_1100_nightly += 1
                if m100[fn]["abi_shape"] != mnight[fn]["abi_shape"]:
                    drift_1100_to_nightly.append(
                        {
                            "target": tgt,
                            "fn": fn,
                            "abi_1_100_0": m100[fn]["abi_shape"],
                            "abi_nightly": mnight[fn]["abi_shape"],
                            "sym_1_100_0": m100[fn]["sym"],
                            "sym_nightly": mnight[fn]["sym"],
                        }
                    )
                elif m100[fn]["full_header"] != mnight[fn]["full_header"]:
                    attr_only_churn_1100_to_nightly[tgt] += 1

            for fn in sorted(set(m99) & set(mnight)):
                if m99[fn]["abi_shape"] != mnight[fn]["abi_shape"]:
                    drift_199_to_nightly.append(
                        {
                            "target": tgt,
                            "fn": fn,
                            "abi_1_99_1": m99[fn]["abi_shape"],
                            "abi_nightly": mnight[fn]["abi_shape"],
                        }
                    )

        # Also extract key cross-target ABI highlights on 1.99.1 (e.g. i686 f32/f64 Rust vs C, u128/i128, HfaF32x4)
        spotlights = {}
        for key_fn in (
            "abi_rust_f32",
            "abi_c_f32",
            "abi_rust_f64",
            "abi_c_f64",
            "abi_rust_u128",
            "abi_c_u128",
            "abi_rust_hfa_f32x4",
            "abi_c_hfa_f32x4",
            "abi_rust_simd_f32x4",
            "abi_c_simd_f32x4",
            "abi_rust_simd_f32x8",
            "abi_vec_f32x4",
            "abi_vec_hfa4",
        ):
            spotlights[key_fn] = {
                tgt: {
                    tc: matrix[tc].get(tgt, {}).get(key_fn, {}).get("abi_shape")
                    for tc, _ in TOOLCHAINS
                }
                for tgt in TARGETS
                if key_fn in matrix["1.99.1"].get(tgt, {})
            }

        out = {
            "toolchains": tc_meta,
            "targets": TARGETS,
            "compile_status": compile_status,
            "total_compiled_fn_instances": sum(
                len(matrix[tc].get(tgt, {})) for tc, _ in TOOLCHAINS for tgt in TARGETS
            ),
            "total_compared_pairs_1_99_1_to_1_100_0": total_pairs_199_1100,
            "total_compared_pairs_1_100_0_to_nightly": total_pairs_1100_nightly,
            "true_abi_drift_1_99_1_to_1_100_0_count": len(drift_199_to_1100),
            "true_abi_drift_1_99_1_to_1_100_0_by_target": dict(
                Counter(x["target"] for x in drift_199_to_1100)
            ),
            "true_abi_drift_1_100_0_to_nightly_count": len(drift_1100_to_nightly),
            "true_abi_drift_1_100_0_to_nightly_by_target": dict(
                Counter(x["target"] for x in drift_1100_to_nightly)
            ),
            "true_abi_drift_1_99_1_to_nightly_count": len(drift_199_to_nightly),
            "true_abi_drift_1_99_1_to_nightly_by_target": dict(
                Counter(x["target"] for x in drift_199_to_nightly)
            ),
            "opt_attr_only_churn_1_99_1_to_1_100_0": dict(attr_only_churn_199_to_1100),
            "opt_attr_only_churn_1_100_0_to_nightly": dict(attr_only_churn_1100_to_nightly),
            "drift_1_99_1_to_1_100_0": drift_199_to_1100,
            "drift_1_100_0_to_nightly": drift_1100_to_nightly,
            "spotlights": spotlights,
        }
        out_json.parent.mkdir(parents=True, exist_ok=True)
        out_json.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({k: v for k, v in out.items() if k not in ("drift_1_99_1_to_1_100_0", "drift_1_100_0_to_nightly", "spotlights")}, indent=2))
        print("=== SAMPLE 1.99.1 -> 1.100.0 DRIFTS ===")
        for x in drift_199_to_1100[:15]:
            print(" ", x["target"], x["fn"], ":", x["abi_1_99_1"], "-->", x["abi_1_100_0"])
        print("=== SAMPLE 1.100.0 -> NIGHTLY DRIFTS ===")
        for x in drift_1100_to_nightly[:20]:
            print(" ", x["target"], x["fn"], ":", x["abi_1_100_0"], "-->", x["abi_nightly"])


if __name__ == "__main__":
    main()
