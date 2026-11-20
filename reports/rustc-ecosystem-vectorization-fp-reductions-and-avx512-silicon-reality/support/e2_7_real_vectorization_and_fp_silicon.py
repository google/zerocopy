#!/usr/bin/env python3
"""E2-7: Real rustc 1.99.1 / LLVM 23.1.1 Ecosystem Vectorization Census
+ Real Native Silicon Execution of Scalar, Bit-Exact Ordered-SIMD, and
Fast-Math/Tree-Reassociated FP Reductions & Integer Kernels Across
SSE2 (x86-64) / AVX2 (x86-64-v3) / AVX-512 (x86-64-v4 & x86-64-v4-zmm512).

Measures real LLVM 23.1.1 ecosystem vectorization idioms, width distributions, and native x86-64 AVX-512 silicon behavior.

Hard guarantees:
- Zero Lean/Lake invocations; zero writes inside workspace repos.
- All scratch builds and execution live strictly inside /tmp/vrustc_e2_7.
- Zero fabricated numbers: every IR count, remark count, disassembly count,
  timing measurement, and numerical ULP/bit error comes from real rustc +1.99.1
  (LLVM 23.1.1) execution on this host.
- Non-host microarchitectures (Zen 4, Zen 5, Neoverse-V1, Apple Silicon) are
  explicitly marked `not measured on silicon` (optional AArch64 NEON/+sve
  comparison is strictly static disassembly only).
"""

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

SCRATCH_ROOT = Path("/tmp/vrustc_e2_7")
OUT_JSON = Path(__file__).resolve().parent / "e2_7_real_vectorization_and_fp_silicon.json"
CARGO_HOME_DIR = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
CARGO_SRC_INDEX = next((CARGO_HOME_DIR / "registry/src").glob("index.crates.io-*"), CARGO_HOME_DIR / "registry/src/index.crates.io-1949cf8c6b5b557f")

TOOLCHAIN = "+1.99.1"

# 7 real multi-module offline crates covering pure-Rust auto-vec (compression,
# JSON parsing, regex automata, JPEG DSP w/ FP) and explicit std::arch SIMD
# (memchr, crc32fast, base64).
PART_A_CRATES = [
    ("miniz_oxide", "0.9.1", "miniz_oxide", "pure-Rust DEFLATE compression/decompression"),
    ("memchr", "2.8.3", "memchr", "explicit std::arch SSE2/AVX2 byte/substring search + scalar"),
    ("crc32fast", "1.5.5", "crc32fast", "explicit std::arch PCLMULQDQ + slice-by-8 scalar checksum"),
    ("base64", "0.23.1", "base64", "hybrid explicit AVX2 std::arch + scalar base64 codec"),
    ("serde_json", "1.0.154", "serde_json", "branchy JSON parser/serializer/Value AST"),
    ("regex-automata", "0.4.19", "regex_automata", "multi-module NFA/DFA/hybrid regex automata engine"),
    ("jpeg-decoder", "0.1.22", "jpeg_decoder", "pure-Rust JPEG IDCT, upsampling, and FP YCbCr/CMYK color conversion"),
]

# CPU tiers:
# Notice LLVM 23.1.1 defaults generic `x86-64-v4` to `prefer-256-bit` for many
# auto-vectorized loops to avoid legacy Intel AVX-512 downclocking, while still
# using EVEX opmasks (`%k0-%k7`), 512-bit gathers/widening, and 512-bit SLP.
# We measure BOTH default `x86-64-v4` AND `x86-64-v4-zmm512` (`-prefer-256-bit`)
# to expose the exact effect of LLVM's vector-width policy on real silicon!
CPU_TIERS = [
    ("x86-64", "x86-64", None, "Baseline SSE2 (128-bit xmm)"),
    ("x86-64-v3", "x86-64-v3", None, "AVX2 + FMA + BMI1/2 (256-bit ymm)"),
    ("x86-64-v4", "x86-64-v4", None, "AVX-512F/BW/DQ/VL/CD (LLVM default prefer-256-bit policy)"),
    ("x86-64-v4-zmm512", "x86-64-v4", "-prefer-256-bit", "AVX-512F/BW/DQ/VL/CD with -C target-feature=-prefer-256-bit (full 512-bit zmm)"),
]

VEC_TYPE_RE = re.compile(r"<(\d+)\s+x\s+(i(\d+)|half|bfloat|float|double|fp128|ptr)>")
STDARCH_FILE_MARKERS = (
    "core_arch",
    "stdarch",
    "arch/x86",
    "pclmulqdq",
    "engine/simd",
)


def run_cmd(cmd, cwd=None, env=None, check=True):
    e = os.environ.copy()
    e["RUSTC_ICE"] = "0"
    if env:
        e.update(env)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=e,
        text=True,
        capture_output=True,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"Command failed (rc={proc.returncode}): {' '.join(cmd)}\n"
            f"STDOUT:\n{proc.stdout[-2000:]}\nSTDERR:\n{proc.stderr[-2000:]}"
        )
    return proc


def gather_host_metadata():
    rustc_vv = run_cmd(["rustc", TOOLCHAIN, "-vV"]).stdout.strip()
    cargo_v = run_cmd(["cargo", TOOLCHAIN, "-V"]).stdout.strip()
    sysroot = Path(run_cmd(["rustc", TOOLCHAIN, "--print", "sysroot"]).stdout.strip())
    llvm_objdump = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump"
    objdump_ver = run_cmd([str(llvm_objdump), "--version"]).stdout.strip().splitlines()[0]

    lscpu_out = run_cmd(["lscpu"]).stdout
    lscpu_kv = {}
    for line in lscpu_out.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            lscpu_kv[k.strip()] = v.strip()

    cpuinfo = Path("/proc/cpuinfo").read_text()
    first_block = cpuinfo.split("\n\n", 1)[0]
    ci = {}
    for line in first_block.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            ci[k.strip()] = v.strip()

    all_flags = set(ci.get("flags", "").split())
    simd_flags = sorted(
        f for f in all_flags
        if any(f.startswith(p) for p in ("sse", "avx", "fma", "bmi", "f16c", "pclmul", "gfni", "vaes", "vpclmul", "popcnt", "aes", "sha"))
    )

    return {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "rustc_version_verbose": rustc_vv,
        "cargo_version": cargo_v,
        "llvm_objdump_path": "<rustup-sysroot>/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump",
        "llvm_objdump_version": objdump_ver,
        "host_triple": "x86_64-unknown-linux-gnu",
        "cpu": {
            "vendor_id": ci.get("vendor_id", ""),
            "model_name": ci.get("model name", lscpu_kv.get("Model name", "")),
            "cpu_family": int(ci["cpu family"]) if ci.get("cpu family", "").isdigit() else ci.get("cpu family"),
            "model": int(ci["model"]) if ci.get("model", "").isdigit() else ci.get("model"),
            "stepping": int(ci["stepping"]) if ci.get("stepping", "").isdigit() else ci.get("stepping"),
            "cpu_mhz": ci.get("cpu MHz", ""),
            "logical_cpus": lscpu_kv.get("CPU(s)", ""),
            "l1d_cache": lscpu_kv.get("L1d cache", ""),
            "l1i_cache": lscpu_kv.get("L1i cache", ""),
            "l2_cache": lscpu_kv.get("L2 cache", ""),
            "l3_cache": lscpu_kv.get("L3 cache", ""),
            "simd_and_bit_flags": simd_flags,
        },
        "non_host_microarchitectures": {
            "AMD Zen 4": "not measured on silicon",
            "AMD Zen 5": "not measured on silicon",
            "ARM Neoverse-V1": "not measured on silicon",
            "Apple Silicon (M-series)": "not measured on silicon",
            "aarch64-unknown-linux-gnu (NEON / +sve)": "static_disassembly_only; runtime not measured on silicon",
        },
    }


def elem_bits(t):
    if t.startswith("i"):
        return int(t[1:])
    return {
        "half": 16,
        "bfloat": 16,
        "float": 32,
        "double": 64,
        "fp128": 128,
        "ptr": 64,
    }[t]


def instr_vec_width_bits(line):
    s = line.split(";", 1)[0]
    if "shufflevector " in s:
        ms = VEC_TYPE_RE.findall(s)
        if len(ms) >= 3:
            n1, t1, _ = ms[0]
            eb = elem_bits(t1)
            n_mask = int(ms[-1][0])
            return max(int(n1) * eb, n_mask * eb)
    widths = [int(n) * elem_bits(t) for n, t, _ in VEC_TYPE_RE.findall(s)]
    return max(widths) if widths else 0


def classify_vec_instr(line):
    s = line.strip()
    rhs = s.split("=", 1)[1].strip() if "=" in s else s
    toks = rhs.split()
    if not toks:
        return "other"
    op = toks[0]
    if op in ("tail", "musttail", "notail") and len(toks) > 1:
        op = toks[1]
    if op in ("call", "invoke"):
        m = re.search(r'@([a-zA-Z0-9_.$"]+)', rhs)
        callee = m.group(1) if m else ""
        if callee.startswith("llvm.vector.reduce."):
            return "vector_reduce"
        if callee.startswith("llvm.masked."):
            return "masked_load_store_gather_scatter"
        if callee.startswith("llvm.x86."):
            return "x86_target_intrinsic"
        if any(
            callee.startswith(p)
            for p in (
                "llvm.fma",
                "llvm.fmuladd",
                "llvm.sqrt",
                "llvm.fabs",
                "llvm.minnum",
                "llvm.maxnum",
                "llvm.minimum",
                "llvm.maximum",
                "llvm.fptosi",
                "llvm.fptoui",
                "llvm.floor",
                "llvm.ceil",
                "llvm.round",
                "llvm.copysign",
            )
        ):
            return "fp_arith"
        if any(
            callee.startswith(p)
            for p in (
                "llvm.umax",
                "llvm.umin",
                "llvm.smax",
                "llvm.smin",
                "llvm.usub",
                "llvm.uadd",
                "llvm.ssub",
                "llvm.sadd",
                "llvm.abs",
                "llvm.fshl",
                "llvm.fshr",
                "llvm.bswap",
                "llvm.bitreverse",
                "llvm.ctpop",
                "llvm.ctlz",
                "llvm.cttz",
            )
        ):
            return "int_arith_bitwise"
        return "other_call"
    if op in ("load", "store"):
        return "load_store"
    if op in ("shufflevector", "extractelement", "insertelement"):
        return "shuffle_extract_insert"
    if op in (
        "add", "sub", "mul", "udiv", "sdiv", "urem", "srem",
        "and", "or", "xor", "shl", "lshr", "ashr",
        "zext", "sext", "trunc", "bitcast", "inttoptr", "ptrtoint", "getelementptr",
    ):
        return "int_arith_bitwise"
    if op in (
        "fadd", "fsub", "fmul", "fdiv", "frem", "fneg",
        "fpext", "fptrunc", "sitofp", "uitofp", "fptosi", "fptoui",
    ):
        return "fp_arith"
    if op in ("icmp", "fcmp", "select"):
        return "icmp_fcmp_select"
    if op in ("phi", "freeze", "extractvalue", "insertvalue", "ret"):
        return "ssa_phi_freeze"
    return f"other:{op}"


def parse_llvm_ir_file(ll_path: Path):
    txt = ll_path.read_text(errors="replace")
    # Build DWARF debug metadata maps to attribute std::arch / core_arch accurately
    files = {
        m.group(1): m.group(2)
        for m in re.finditer(r'^!(\d+)\s*=\s*!DIFile\(filename:\s*"([^"]+)"', txt, re.M)
    }
    scopes = {
        m.group(1): files.get(m.group(2), "")
        for m in re.finditer(
            r'^!(\d+)\s*=\s*(?:distinct\s+)?!DI(?:Subprogram|LexicalBlock|LexicalBlockFile)\([^)]*file:\s*!(\d+)',
            txt,
            re.M,
        )
    }
    locs = {
        m.group(1): (m.group(2), m.group(3))
        for m in re.finditer(
            r'^!(\d+)\s*=\s*!DILocation\([^)]*scope:\s*!(\d+)(?:[^)]*inlinedAt:\s*!(\d+))?',
            txt,
            re.M,
        )
    }

    def loc_files(lid):
        out, seen = [], set()
        while lid and lid not in seen and lid in locs:
            seen.add(lid)
            sc, inl = locs[lid]
            if sc in scopes:
                out.append(scopes[sc])
            lid = inl
        return out

    total_functions = 0
    functions_with_vec = 0
    fn_origin_counts = Counter()
    instr_origin_counts = Counter()
    width_counts = Counter()
    width_sub_counts = Counter()
    family_counts = Counter()
    x86_intrinsics = Counter()
    reduce_intrinsics = Counter()
    masked_intrinsics = Counter()
    vec_types_top = Counter()
    top_vec_functions = []

    for chunk in re.split(r"\n(?=define )", txt):
        if not chunk.startswith("define "):
            continue
        total_functions += 1
        lines = chunk.splitlines()
        hdr = lines[0]
        m_name = re.search(r"@([^\s(]+)\(", hdr)
        fn_name = m_name.group(1) if m_name else "<anon>"
        dm_fn = re.search(r"!dbg\s*!(\d+)", hdr)
        fn_file = scopes.get(dm_fn.group(1), "") if dm_fn else ""

        vec_lines = []
        for l in lines[1:]:
            if l == "}":
                break
            if "#dbg_" in l or "@llvm.dbg." in l:
                continue
            if VEC_TYPE_RE.search(l):
                vec_lines.append(l)

        if not vec_lines:
            continue

        functions_with_vec += 1
        fn_has_stdarch = any(p in fn_file for p in STDARCH_FILE_MARKERS)
        if not fn_has_stdarch:
            for l in vec_lines:
                if "@llvm.x86." in l:
                    fn_has_stdarch = True
                    break
                dm = re.search(r"!dbg\s*!(\d+)", l)
                if dm and any(any(p in f for p in STDARCH_FILE_MARKERS) for f in loc_files(dm.group(1))):
                    fn_has_stdarch = True
                    break

        origin = "handwritten_std_arch" if fn_has_stdarch else "compiler_autovec_slp"
        fn_origin_counts[origin] += 1
        instr_origin_counts[origin] += len(vec_lines)

        fn_families = Counter()
        fn_max_w = 0
        for l in vec_lines:
            w = instr_vec_width_bits(l)
            fn_max_w = max(fn_max_w, w)
            if w <= 128:
                width_counts["le_128_bit"] += 1
                width_sub_counts["lt_128_bit" if w < 128 else "eq_128_bit"] += 1
            elif w <= 256:
                width_counts["w_256_bit"] += 1
            elif w <= 512:
                width_counts["w_512_bit"] += 1
            else:
                width_counts["gt_512_bit_pre_legalization"] += 1

            fam = classify_vec_instr(l)
            family_counts[fam] += 1
            fn_families[fam] += 1

            for n, t, _ in VEC_TYPE_RE.findall(l.split(";", 1)[0]):
                vec_types_top[f"<{n} x {t}>"] += 1
            for intr in re.findall(r"@llvm\.x86\.[a-zA-Z0-9_.]+", l):
                x86_intrinsics[intr] += 1
            for intr in re.findall(r"@llvm\.vector\.reduce\.[a-zA-Z0-9_.]+", l):
                reduce_intrinsics[intr] += 1
            for intr in re.findall(r"@llvm\.masked\.[a-zA-Z0-9_.]+", l):
                masked_intrinsics[intr] += 1

        top_vec_functions.append({
            "symbol": fn_name,
            "source_file": Path(fn_file).name if fn_file else "",
            "origin": origin,
            "vec_instrs": len(vec_lines),
            "max_width_bits": fn_max_w,
            "families": dict(fn_families),
        })

    top_vec_functions.sort(key=lambda x: -x["vec_instrs"])
    total_vec = sum(family_counts.values())
    total_vec_excl_phi = total_vec - family_counts.get("ssa_phi_freeze", 0)

    return {
        "ll_file_bytes": ll_path.stat().st_size,
        "total_functions": total_functions,
        "functions_with_vector_ir": functions_with_vec,
        "vector_function_pct": round(100.0 * functions_with_vec / total_functions, 2) if total_functions else 0.0,
        "total_vector_ir_instructions": total_vec,
        "total_vector_compute_mem_excl_phi": total_vec_excl_phi,
        "width_breakdown": {
            "le_128_bit": width_counts["le_128_bit"],
            "lt_128_bit_sub": width_sub_counts["lt_128_bit"],
            "eq_128_bit_sub": width_sub_counts["eq_128_bit"],
            "w_256_bit": width_counts["w_256_bit"],
            "w_512_bit": width_counts["w_512_bit"],
            "gt_512_bit_pre_legalization": width_counts["gt_512_bit_pre_legalization"],
        },
        "family_breakdown": {
            "load_store": family_counts["load_store"],
            "shuffle_extract_insert": family_counts["shuffle_extract_insert"],
            "int_arith_bitwise": family_counts["int_arith_bitwise"],
            "fp_arith": family_counts["fp_arith"],
            "icmp_fcmp_select": family_counts["icmp_fcmp_select"],
            "vector_reduce": family_counts["vector_reduce"],
            "masked_load_store_gather_scatter": family_counts["masked_load_store_gather_scatter"],
            "x86_target_intrinsic": family_counts["x86_target_intrinsic"],
            "ssa_phi_freeze": family_counts["ssa_phi_freeze"],
            "other": sum(v for k, v in family_counts.items() if k not in {
                "load_store", "shuffle_extract_insert", "int_arith_bitwise",
                "fp_arith", "icmp_fcmp_select", "vector_reduce",
                "masked_load_store_gather_scatter", "x86_target_intrinsic",
                "ssa_phi_freeze",
            }),
        },
        "origin_separation": {
            "handwritten_std_arch_functions": fn_origin_counts["handwritten_std_arch"],
            "compiler_autovec_slp_functions": fn_origin_counts["compiler_autovec_slp"],
            "handwritten_std_arch_vec_instrs": instr_origin_counts["handwritten_std_arch"],
            "compiler_autovec_slp_vec_instrs": instr_origin_counts["compiler_autovec_slp"],
        },
        "x86_intrinsics": dict(x86_intrinsics.most_common(20)),
        "vector_reduce_intrinsics": dict(reduce_intrinsics.most_common(20)),
        "masked_intrinsics": dict(masked_intrinsics.most_common(20)),
        "top_vector_types": dict(vec_types_top.most_common(12)),
        "top_vector_functions": top_vec_functions[:8],
    }


def parse_remarks(stderr_text: str):
    counts = Counter()
    lv_vf_ic = Counter()
    lv_analysis_reasons = Counter()
    slp_kinds = Counter()
    slp_tree_sizes = Counter()
    sample_success = []

    rem_re = re.compile(
        r"^note:\s+(.+?):(\d+):(\d+)\s+(loop-vectorize|slp-vectorizer)\s+\((success|missed|analysis)\):\s*(.+)$"
    )
    for line in stderr_text.splitlines():
        m = rem_re.match(line.strip())
        if not m:
            continue
        loc_file, ln, col, pass_name, kind, msg = m.groups()
        counts[f"{pass_name}:{kind}"] += 1
        if pass_name == "loop-vectorize" and kind == "success":
            m_w = re.search(r"vectorization width:\s*(\d+),\s*interleaved count:\s*(\d+)", msg)
            if m_w:
                lv_vf_ic[f"VF={m_w.group(1)},IC={m_w.group(2)}"] += 1
            else:
                lv_vf_ic[msg[:60]] += 1
            if len(sample_success) < 10:
                sample_success.append(f"{Path(loc_file).name}:{ln} [{pass_name}] {msg}")
        elif pass_name == "loop-vectorize" and kind == "analysis":
            # Normalize reason string
            reason = re.sub(r"^loop not vectorized:\s*", "", msg).strip()
            reason = re.sub(r"\s+", " ", reason)
            lv_analysis_reasons[reason[:100]] += 1
        elif pass_name == "slp-vectorizer" and kind == "success":
            m_t = re.search(r"tree size\s+(\d+)", msg)
            if m_t:
                slp_tree_sizes[int(m_t.group(1))] += 1
            if "Stores SLP vectorized" in msg:
                slp_kinds["stores_slp"] += 1
            elif "Vectorized horizontal reduction" in msg:
                slp_kinds["horizontal_reduction_slp"] += 1
            elif "SLP vectorized" in msg:
                slp_kinds["general_list_slp"] += 1
            else:
                slp_kinds["other_slp"] += 1
            if len(sample_success) < 15:
                sample_success.append(f"{Path(loc_file).name}:{ln} [{pass_name}] {msg}")

    return {
        "loop_vectorize_success": counts["loop-vectorize:success"],
        "loop_vectorize_missed": counts["loop-vectorize:missed"],
        "loop_vectorize_analysis": counts["loop-vectorize:analysis"],
        "slp_vectorizer_success": counts["slp-vectorizer:success"],
        "slp_vectorizer_missed": counts["slp-vectorizer:missed"],
        "slp_vectorizer_analysis": counts["slp-vectorizer:analysis"],
        "lv_vf_ic_distribution": dict(lv_vf_ic.most_common(15)),
        "lv_top_analysis_reasons": dict(lv_analysis_reasons.most_common(12)),
        "slp_success_kinds": dict(slp_kinds),
        "slp_tree_size_distribution": {str(k): v for k, v in sorted(slp_tree_sizes.items())},
        "sample_success_remarks": sample_success,
    }


def run_part_a():
    ws_dir = SCRATCH_ROOT / "part_a_ws"
    if ws_dir.exists():
        shutil.rmtree(ws_dir)
    (ws_dir / "src").mkdir(parents=True, exist_ok=True)
    (ws_dir / "src/lib.rs").write_text("pub fn harness_marker() {}\n")

    deps_toml = "\n".join(f'{pkg} = "={ver}"' for pkg, ver, _, _ in PART_A_CRATES)
    (ws_dir / "Cargo.toml").write_text(
        f'[package]\nname = "e2_7_census_ws"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\n{deps_toml}\n'
    )

    # Verify offline source-level std::arch audit
    crate_source_audit = {}
    for pkg, ver, lib_name, desc in PART_A_CRATES:
        src_dir = CARGO_SRC_INDEX / f"{pkg}-{ver}/src"
        arch_files, tf_files = [], []
        rs_count = 0
        if src_dir.exists():
            for rs in sorted(src_dir.rglob("*.rs")):
                rs_count += 1
                t = rs.read_text(errors="replace")
                if re.search(r"\b(core|std)::arch\b", t):
                    arch_files.append(str(rs.relative_to(src_dir)))
                if re.search(r"#\[target_feature\(", t):
                    tf_files.append(str(rs.relative_to(src_dir)))
        crate_source_audit[pkg] = {
            "version": ver,
            "description": desc,
            "rs_source_files": rs_count,
            "uses_std_arch_files": arch_files,
            "uses_target_feature_files": tf_files,
        }

    # Resolve offline lockfile once
    run_cmd(["cargo", TOOLCHAIN, "generate-lockfile", "--offline"], cwd=ws_dir)

    results_by_tier = {}
    for tier_id, cpu, extra_feat, tier_desc in CPU_TIERS:
        print(f"[Part A] Compiling 7 offline crates for tier={tier_id} ...", flush=True)
        target_dir = SCRATCH_ROOT / f"part_a_target_{tier_id}"
        if target_dir.exists():
            shutil.rmtree(target_dir)

        rf = f"-C target-cpu={cpu}"
        if extra_feat:
            rf += f" -C target-feature={extra_feat}"

        tier_crates = {}
        agg_totals = Counter()
        agg_widths = Counter()
        agg_families = Counter()
        agg_origins = Counter()
        agg_remarks = Counter()
        agg_reasons = Counter()
        agg_vf_ic = Counter()
        agg_slp_kinds = Counter()

        for pkg, ver, lib_name, _desc in PART_A_CRATES:
            t0 = time.perf_counter()
            cmd = [
                "cargo", TOOLCHAIN, "rustc", "--offline", "--release",
                "-p", pkg, "--lib",
                "--target-dir", str(target_dir),
                "--",
                "-C", "codegen-units=1",
                "-C", "debuginfo=line-tables-only",
                "-C", "remark=loop-vectorize slp-vectorizer",
                "--emit=llvm-ir",
            ]
            proc = run_cmd(cmd, cwd=ws_dir, env={"RUSTFLAGS": rf})
            elapsed = round(time.perf_counter() - t0, 3)

            deps_dir = target_dir / "release/deps"
            lls = sorted(deps_dir.glob(f"{lib_name}-*.ll"))
            if not lls:
                raise RuntimeError(f"No .ll found for {pkg} ({lib_name}) in {deps_dir}")
            # Pick the newest / largest .ll matching crate
            ll_path = max(lls, key=lambda p: p.stat().st_size)

            ir_stats = parse_llvm_ir_file(ll_path)
            rem_stats = parse_remarks(proc.stderr)
            tier_crates[pkg] = {
                "version": ver,
                "compile_wall_s": elapsed,
                "ir": ir_stats,
                "remarks": rem_stats,
            }

            agg_totals["total_functions"] += ir_stats["total_functions"]
            agg_totals["functions_with_vector_ir"] += ir_stats["functions_with_vector_ir"]
            agg_totals["total_vector_ir_instructions"] += ir_stats["total_vector_ir_instructions"]
            agg_totals["total_vector_compute_mem_excl_phi"] += ir_stats["total_vector_compute_mem_excl_phi"]
            for k, v in ir_stats["width_breakdown"].items():
                agg_widths[k] += v
            for k, v in ir_stats["family_breakdown"].items():
                agg_families[k] += v
            for k, v in ir_stats["origin_separation"].items():
                agg_origins[k] += v
            for k in (
                "loop_vectorize_success", "loop_vectorize_missed", "loop_vectorize_analysis",
                "slp_vectorizer_success", "slp_vectorizer_missed", "slp_vectorizer_analysis",
            ):
                agg_remarks[k] += rem_stats[k]
            for k, v in rem_stats["lv_top_analysis_reasons"].items():
                agg_reasons[k] += v
            for k, v in rem_stats["lv_vf_ic_distribution"].items():
                agg_vf_ic[k] += v
            for k, v in rem_stats["slp_success_kinds"].items():
                agg_slp_kinds[k] += v

            print(
                f"  {pkg:15s}: fns={ir_stats['total_functions']:4d} vec_fns={ir_stats['functions_with_vector_ir']:3d} "
                f"vec_ir={ir_stats['total_vector_ir_instructions']:4d} "
                f"(<=128:{ir_stats['width_breakdown']['le_128_bit']} 256:{ir_stats['width_breakdown']['w_256_bit']} "
                f"512:{ir_stats['width_breakdown']['w_512_bit']} >512:{ir_stats['width_breakdown']['gt_512_bit_pre_legalization']}) "
                f"LV_ok={rem_stats['loop_vectorize_success']} SLP_ok={rem_stats['slp_vectorizer_success']} "
                f"LV_miss={rem_stats['loop_vectorize_missed']} ({elapsed}s)",
                flush=True,
            )

        tot_fns = agg_totals["total_functions"]
        results_by_tier[tier_id] = {
            "target_cpu": cpu,
            "extra_target_feature": extra_feat,
            "description": tier_desc,
            "aggregate": {
                "total_functions": tot_fns,
                "functions_with_vector_ir": agg_totals["functions_with_vector_ir"],
                "vector_function_pct": round(100.0 * agg_totals["functions_with_vector_ir"] / tot_fns, 2) if tot_fns else 0.0,
                "total_vector_ir_instructions": agg_totals["total_vector_ir_instructions"],
                "total_vector_compute_mem_excl_phi": agg_totals["total_vector_compute_mem_excl_phi"],
                "width_breakdown": dict(agg_widths),
                "family_breakdown": dict(agg_families),
                "origin_separation": dict(agg_origins),
                "remarks_summary": dict(agg_remarks),
                "lv_vf_ic_distribution": dict(agg_vf_ic.most_common(15)),
                "slp_success_kinds": dict(agg_slp_kinds),
                "top_lv_missed_analysis_reasons": dict(agg_reasons.most_common(12)),
            },
            "crates": tier_crates,
        }

    # Build grounded taxonomy of observed real-world vectorization idioms
    v3_agg = results_by_tier["x86-64-v3"]["aggregate"]
    v4_agg = results_by_tier["x86-64-v4"]["aggregate"]
    v4_512_agg = results_by_tier["x86-64-v4-zmm512"]["aggregate"]
    v3_crates = results_by_tier["x86-64-v3"]["crates"]

    idiom_taxonomy = [
        {
            "idiom_id": "I1_slp_contiguous_stores_and_struct_init",
            "description": "Straight-line SLP vectorization of contiguous array/struct stores, lookup-table initialization, and DFA state-table updates",
            "observed_in_crates": ["regex-automata", "miniz_oxide", "jpeg-decoder", "serde_json"],
            "evidence_v3_slp_stores": v3_agg["slp_success_kinds"].get("stores_slp", 0),
            "evidence_v3_slp_total": v3_agg["remarks_summary"]["slp_vectorizer_success"],
            "dominant_ir_ops": ["load_store", "shuffle_extract_insert", "int_arith_bitwise"],
        },
        {
            "idiom_id": "I2_handwritten_std_arch_byte_search_and_crypto",
            "description": "Explicit std::arch SIMD kernels with runtime CPUID dispatch (memchr SSE2/AVX2 byte search, crc32fast PCLMULQDQ 128/256/512-bit folding, base64 AVX2 vpshufb/vpmaddubsw codec)",
            "observed_in_crates": ["memchr", "crc32fast", "base64", "regex-automata (inlined memchr prefilters)"],
            "evidence_v3_std_arch_vec_instrs": v3_agg["origin_separation"]["handwritten_std_arch_vec_instrs"],
            "evidence_v3_std_arch_functions": v3_agg["origin_separation"]["handwritten_std_arch_functions"],
            "share_of_total_vec_ir_v3_pct": round(
                100.0 * v3_agg["origin_separation"]["handwritten_std_arch_vec_instrs"]
                / max(1, v3_agg["total_vector_ir_instructions"]), 2
            ),
        },
        {
            "idiom_id": "I3_interleaved_wide_pre_legalization_loops",
            "description": "LLVM LoopVectorize emitting >512-bit pre-legalization IR vectors for interleaved/strided channel loops (e.g., <128 x i8> CMYK inversion and <32 x float> YCbCr->RGB in jpeg-decoder; <13 x i64> stride-4 deinterleaving in regex-automata; <16 x i64> window-index math in miniz_oxide)",
            "observed_in_crates": ["jpeg-decoder", "regex-automata", "miniz_oxide", "base64"],
            "evidence_v3_gt_512_ir_instrs": v3_agg["width_breakdown"]["gt_512_bit_pre_legalization"],
            "evidence_v4_gt_512_ir_instrs": v4_agg["width_breakdown"]["gt_512_bit_pre_legalization"],
            "evidence_v4_zmm512_gt_512_ir_instrs": v4_512_agg["width_breakdown"]["gt_512_bit_pre_legalization"],
        },
        {
            "idiom_id": "I4_associative_integer_and_minmax_reductions",
            "description": "Auto-vectorized integer associative reductions (add, or, umax, umin) lowered to @llvm.vector.reduce.{add,or,umax,umin}.*",
            "observed_in_crates": ["memchr", "regex-automata", "jpeg-decoder", "miniz_oxide"],
            "evidence_v3_vector_reduce_instrs": v3_agg["family_breakdown"]["vector_reduce"],
            "evidence_v4_vector_reduce_instrs": v4_agg["family_breakdown"]["vector_reduce"],
        },
        {
            "idiom_id": "I5_elementwise_fp_dsp_without_reassociation",
            "description": "Data-parallel elementwise FP color-space conversion (YCbCr/YCCK -> RGB, @llvm.fptosi.sat.v*i32.v*f32) requiring zero FP reassociation",
            "observed_in_crates": ["jpeg-decoder"],
            "evidence_v3_fp_arith_vec_instrs": v3_agg["family_breakdown"]["fp_arith"],
            "evidence_v4_fp_arith_vec_instrs": v4_agg["family_breakdown"]["fp_arith"],
        },
        {
            "idiom_id": "I6_branchy_and_unbounded_loop_barriers",
            "description": "Dominant missed loop-vectorization barriers in real Rust code (serde_json, regex-automata, miniz_oxide): non-countable exit conditions, early-exit/switch control flow, and loop-carried dependencies",
            "observed_in_crates": ["regex-automata", "miniz_oxide", "memchr", "serde_json", "jpeg-decoder"],
            "evidence_v3_lv_success_vs_missed": {
                "lv_success": v3_agg["remarks_summary"]["loop_vectorize_success"],
                "lv_missed": v3_agg["remarks_summary"]["loop_vectorize_missed"],
                "lv_success_rate_pct": round(
                    100.0 * v3_agg["remarks_summary"]["loop_vectorize_success"]
                    / max(1, v3_agg["remarks_summary"]["loop_vectorize_success"] + v3_agg["remarks_summary"]["loop_vectorize_missed"]),
                    2,
                ),
            },
            "top_reasons_v3": v3_agg["top_lv_missed_analysis_reasons"],
            "serde_json_vec_ir_v3": v3_crates["serde_json"]["ir"]["total_vector_ir_instructions"],
        },
    ]

    return {
        "crates_audited": crate_source_audit,
        "tiers": results_by_tier,
        "observed_idiom_taxonomy": idiom_taxonomy,
    }


# =============================================================================
# PART B: Real Native Silicon Benchmark & Disassembly Verification
# =============================================================================

BENCH_RS = r"""#![feature(core_intrinsics, repr_simd)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::{fadd_fast, fmul_fast};
use std::intrinsics::simd::simd_reduce_add_ordered;
use std::time::Instant;

#[repr(simd)]
#[derive(Copy, Clone)]
struct F64x4([f64; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct F64x8([f64; 8]);

// =========================================================================
// 15 Real Numeric / FP / Integer Kernels (all #[no_mangle] #[inline(never)])
// =========================================================================

#[no_mangle]
#[inline(never)]
pub extern "C" fn k01_f64_sum_ordered_scalar(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut acc = 0.0f64;
    for &x in s {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k02_f64_sum_ordered_simd_chunk4(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut acc = 0.0f64;
    let chunks = s.chunks_exact(4);
    let rem = chunks.remainder();
    for c in chunks {
        let v = F64x4([c[0], c[1], c[2], c[3]]);
        acc = unsafe { simd_reduce_add_ordered(v, acc) };
    }
    for &x in rem {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k03_f64_sum_ordered_simd_chunk8(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut acc = 0.0f64;
    let chunks = s.chunks_exact(8);
    let rem = chunks.remainder();
    for c in chunks {
        let v = F64x8([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
        acc = unsafe { simd_reduce_add_ordered(v, acc) };
    }
    for &x in rem {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k04_f64_sum_reassoc_fadd_fast(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut acc = 0.0f64;
    for &x in s {
        acc = unsafe { fadd_fast(acc, x) };
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k05_f64_sum_reassoc_tree4(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut lanes = [0.0f64; 4];
    let chunks = s.chunks_exact(4);
    let rem = chunks.remainder();
    for c in chunks {
        for k in 0..4 {
            lanes[k] += c[k];
        }
    }
    let mut acc = (lanes[0] + lanes[1]) + (lanes[2] + lanes[3]);
    for &x in rem {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k06_f64_sum_reassoc_tree8(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut lanes = [0.0f64; 8];
    let chunks = s.chunks_exact(8);
    let rem = chunks.remainder();
    for c in chunks {
        for k in 0..8 {
            lanes[k] += c[k];
        }
    }
    let mut acc = ((lanes[0] + lanes[1]) + (lanes[2] + lanes[3]))
        + ((lanes[4] + lanes[5]) + (lanes[6] + lanes[7]));
    for &x in rem {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k07_f64_sum_reassoc_tree16(ptr: *const f64, n: usize) -> f64 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut lanes = [0.0f64; 16];
    let chunks = s.chunks_exact(16);
    let rem = chunks.remainder();
    for c in chunks {
        for k in 0..16 {
            lanes[k] += c[k];
        }
    }
    let a = ((lanes[0] + lanes[1]) + (lanes[2] + lanes[3]))
        + ((lanes[4] + lanes[5]) + (lanes[6] + lanes[7]));
    let b = ((lanes[8] + lanes[9]) + (lanes[10] + lanes[11]))
        + ((lanes[12] + lanes[13]) + (lanes[14] + lanes[15]));
    let mut acc = a + b;
    for &x in rem {
        acc += x;
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k08_f32_dot_ordered(a: *const f32, b: *const f32, n: usize) -> f32 {
    let sa = unsafe { std::slice::from_raw_parts(a, n) };
    let sb = unsafe { std::slice::from_raw_parts(b, n) };
    let mut acc = 0.0f32;
    for i in 0..n {
        acc += sa[i] * sb[i];
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k09_f32_dot_reassoc_fma(a: *const f32, b: *const f32, n: usize) -> f32 {
    let sa = unsafe { std::slice::from_raw_parts(a, n) };
    let sb = unsafe { std::slice::from_raw_parts(b, n) };
    let mut acc = 0.0f32;
    for i in 0..n {
        acc = unsafe { fadd_fast(acc, fmul_fast(sa[i], sb[i])) };
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k10_f32_dot_tree16_fma(a: *const f32, b: *const f32, n: usize) -> f32 {
    let sa = unsafe { std::slice::from_raw_parts(a, n) };
    let sb = unsafe { std::slice::from_raw_parts(b, n) };
    let mut lanes = [0.0f32; 16];
    let ca = sa.chunks_exact(16);
    let cb = sb.chunks_exact(16);
    let ra = ca.remainder();
    let rb = cb.remainder();
    for (xa, xb) in ca.zip(cb) {
        for k in 0..16 {
            lanes[k] = xa[k].mul_add(xb[k], lanes[k]);
        }
    }
    let mut acc = 0.0f32;
    for v in lanes {
        acc += v;
    }
    for (&xa, &xb) in ra.iter().zip(rb.iter()) {
        acc = xa.mul_add(xb, acc);
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k11_f64_axpy_elementwise(a: f64, x: *const f64, y: *mut f64, n: usize) {
    let sx = unsafe { std::slice::from_raw_parts(x, n) };
    let sy = unsafe { std::slice::from_raw_parts_mut(y, n) };
    for i in 0..n {
        sy[i] = a * sx[i] + sy[i];
    }
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k12_u32_wrapping_sum_reduce(ptr: *const u32, n: usize) -> u32 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    s.iter().copied().fold(0u32, u32::wrapping_add)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k13_u8_byte_count(ptr: *const u8, n: usize, needle: u8) -> u32 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n) };
    let mut c = 0u32;
    for &b in s {
        c = c.wrapping_add((b == needle) as u32);
    }
    c
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k14_u32_strided4_sum(ptr: *const u32, n: usize) -> u32 {
    let s = unsafe { std::slice::from_raw_parts(ptr, n * 4) };
    let mut acc = 0u32;
    for i in 0..n {
        acc = acc.wrapping_add(unsafe { *s.get_unchecked(i * 4) });
    }
    acc
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn k15_u32_indexed_gather_sum(table: *const u32, idx: *const u32, n: usize) -> u32 {
    let mut acc = 0u32;
    for i in 0..n {
        let j = unsafe { *idx.add(i) } as usize;
        acc = acc.wrapping_add(unsafe { *table.add(j) });
    }
    acc
}

// =========================================================================
// Exact ULP helpers
// =========================================================================

fn f64_to_ordered_u64(x: f64) -> u64 {
    let b = x.to_bits();
    if (b >> 63) != 0 { !b } else { b | (1u64 << 63) }
}

fn ulp_diff_f64(a: f64, b: f64) -> u64 {
    if a.is_nan() || b.is_nan() {
        return u64::MAX;
    }
    if a == 0.0 && b == 0.0 {
        return 0;
    }
    let oa = f64_to_ordered_u64(a);
    let ob = f64_to_ordered_u64(b);
    let raw = oa.abs_diff(ob);
    if (a.to_bits() >> 63) != (b.to_bits() >> 63) {
        raw.saturating_sub(1)
    } else {
        raw
    }
}

fn f32_to_ordered_u32(x: f32) -> u32 {
    let b = x.to_bits();
    if (b >> 31) != 0 { !b } else { b | (1u32 << 31) }
}

fn ulp_diff_f32(a: f32, b: f32) -> u32 {
    if a.is_nan() || b.is_nan() {
        return u32::MAX;
    }
    if a == 0.0 && b == 0.0 {
        return 0;
    }
    let oa = f32_to_ordered_u32(a);
    let ob = f32_to_ordered_u32(b);
    let raw = oa.abs_diff(ob);
    if (a.to_bits() >> 31) != (b.to_bits() >> 31) {
        raw.saturating_sub(1)
    } else {
        raw
    }
}

fn iters_for_n(n: usize) -> usize {
    match n {
        8 => 160_000,
        32 => 80_000,
        128 => 40_000,
        1024 => 8_000,
        16384 => 600,
        262144 => 40,
        _ => 100,
    }
}

fn main() {
    let trip_counts: [usize; 6] = [8, 32, 128, 1024, 16384, 262144];
    let rounds: usize = 9;
    let max_n = *trip_counts.last().unwrap();

    // Well-conditioned f64 input
    let f64_well: Vec<f64> = (0..max_n)
        .map(|i| (((i.wrapping_mul(17).wrapping_add(3)) % 997) as f64) / 997.0 + 1e-7 * (i as f64))
        .collect();

    // Cancellation-heavy f64 input (period 4: [1e16, 1.0, -1e16, 1.0, ...])
    // Exact math sum = N / 2; strict left-to-right IEEE-754 sum = N / 4 (since ulp(1e16) = 2.0)
    let f64_cancel4: Vec<f64> = (0..max_n)
        .map(|i| match i & 3 {
            0 => 1.0e16f64,
            1 => 1.0f64,
            2 => -1.0e16f64,
            _ => 1.0f64,
        })
        .collect();

    // Cancellation-heavy f64 input (period 8: [1e16, 1.0, 1.0, 1.0, -1e16, 1.0, 1.0, 1.0, ...])
    // Exact math sum = 6*(N/8) = 0.75*N; strict left-to-right IEEE-754 sum = 3*(N/8) = 0.375*N
    let f64_cancel8: Vec<f64> = (0..max_n)
        .map(|i| match i & 7 {
            0 => 1.0e16f64,
            4 => -1.0e16f64,
            _ => 1.0f64,
        })
        .collect();

    // Well-conditioned f32 dot inputs
    let f32_a_well: Vec<f32> = (0..max_n)
        .map(|i| (((i.wrapping_mul(13).wrapping_add(5)) % 251) as f32) / 251.0 - 0.5f32)
        .collect();
    let f32_b_well: Vec<f32> = (0..max_n)
        .map(|i| (((i.wrapping_mul(29).wrapping_add(7)) % 257) as f32) / 257.0 + 0.125f32)
        .collect();

    // Cancellation-heavy f32 dot inputs (ulp(2e7f32) = 2.0, so 2e7 + 1.0 == 2e7)
    let f32_a_cancel4: Vec<f32> = (0..max_n)
        .map(|i| match i & 3 {
            0 => 2.0e7f32,
            1 => 1.0f32,
            2 => -2.0e7f32,
            _ => 1.0f32,
        })
        .collect();
    let f32_b_ones: Vec<f32> = vec![1.0f32; max_n];

    // AXPY inputs
    let axpy_a = 1.0e-6f64;
    let axpy_x: Vec<f64> = (0..max_n)
        .map(|i| (((i.wrapping_mul(31).wrapping_add(11)) % 1021) as f64) / 1021.0 - 0.5)
        .collect();
    let axpy_y_init: Vec<f64> = (0..max_n)
        .map(|i| 1.0 + (((i.wrapping_mul(7).wrapping_add(1)) % 509) as f64) / 509.0)
        .collect();

    // Integer inputs
    let u32_data: Vec<u32> = (0..max_n)
        .map(|i| (i as u32).wrapping_mul(2654435761).wrapping_add(17))
        .collect();
    let u8_data: Vec<u8> = (0..max_n)
        .map(|i| ((i.wrapping_mul(37).wrapping_add(13)) & 0xff) as u8)
        .collect();
    let u8_needle: u8 = 42;
    let u32_strided_data: Vec<u32> = (0..max_n * 4)
        .map(|i| (i as u32).wrapping_mul(1664525).wrapping_add(1013904223))
        .collect();

    // Gather table & deterministic pseudo-random indices per trip count
    let mut gather_tables: Vec<Vec<u32>> = Vec::new();
    let mut gather_indices: Vec<Vec<u32>> = Vec::new();
    for &n in &trip_counts {
        let tlen = n.max(1024);
        let tbl: Vec<u32> = (0..tlen)
            .map(|i| (i as u32).wrapping_mul(2246822519).wrapping_add(3266489917))
            .collect();
        let idx: Vec<u32> = (0..n)
            .map(|i| (((i as u64).wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407) >> 16) % (tlen as u64)) as u32)
            .collect();
        gather_tables.push(tbl);
        gather_indices.push(idx);
    }

    // -------------------------------------------------------------------------
    // Phase 1: Exact Numerical & Bit-Exactness Verification across all N
    // -------------------------------------------------------------------------
    let mut num_checks = Vec::new();
    for (ti, &n) in trip_counts.iter().enumerate() {
        // f64 well-conditioned
        let r_s_w = k01_f64_sum_ordered_scalar(f64_well.as_ptr(), n);
        let r_o4_w = k02_f64_sum_ordered_simd_chunk4(f64_well.as_ptr(), n);
        let r_o8_w = k03_f64_sum_ordered_simd_chunk8(f64_well.as_ptr(), n);
        let r_ff_w = k04_f64_sum_reassoc_fadd_fast(f64_well.as_ptr(), n);
        let r_t4_w = k05_f64_sum_reassoc_tree4(f64_well.as_ptr(), n);
        let r_t8_w = k06_f64_sum_reassoc_tree8(f64_well.as_ptr(), n);
        let r_t16_w = k07_f64_sum_reassoc_tree16(f64_well.as_ptr(), n);

        // f64 cancellation-heavy period 4
        let r_s_c4 = k01_f64_sum_ordered_scalar(f64_cancel4.as_ptr(), n);
        let r_o4_c4 = k02_f64_sum_ordered_simd_chunk4(f64_cancel4.as_ptr(), n);
        let r_o8_c4 = k03_f64_sum_ordered_simd_chunk8(f64_cancel4.as_ptr(), n);
        let r_ff_c4 = k04_f64_sum_reassoc_fadd_fast(f64_cancel4.as_ptr(), n);
        let r_t4_c4 = k05_f64_sum_reassoc_tree4(f64_cancel4.as_ptr(), n);
        let r_t8_c4 = k06_f64_sum_reassoc_tree8(f64_cancel4.as_ptr(), n);
        let r_t16_c4 = k07_f64_sum_reassoc_tree16(f64_cancel4.as_ptr(), n);

        // f64 cancellation-heavy period 8
        let r_s_c8 = k01_f64_sum_ordered_scalar(f64_cancel8.as_ptr(), n);
        let r_o4_c8 = k02_f64_sum_ordered_simd_chunk4(f64_cancel8.as_ptr(), n);
        let r_o8_c8 = k03_f64_sum_ordered_simd_chunk8(f64_cancel8.as_ptr(), n);
        let r_ff_c8 = k04_f64_sum_reassoc_fadd_fast(f64_cancel8.as_ptr(), n);
        let r_t4_c8 = k05_f64_sum_reassoc_tree4(f64_cancel8.as_ptr(), n);
        let r_t8_c8 = k06_f64_sum_reassoc_tree8(f64_cancel8.as_ptr(), n);
        let r_t16_c8 = k07_f64_sum_reassoc_tree16(f64_cancel8.as_ptr(), n);

        // f32 dot well & cancel4
        let d_o_w = k08_f32_dot_ordered(f32_a_well.as_ptr(), f32_b_well.as_ptr(), n);
        let d_ff_w = k09_f32_dot_reassoc_fma(f32_a_well.as_ptr(), f32_b_well.as_ptr(), n);
        let d_t16_w = k10_f32_dot_tree16_fma(f32_a_well.as_ptr(), f32_b_well.as_ptr(), n);

        let d_o_c4 = k08_f32_dot_ordered(f32_a_cancel4.as_ptr(), f32_b_ones.as_ptr(), n);
        let d_ff_c4 = k09_f32_dot_reassoc_fma(f32_a_cancel4.as_ptr(), f32_b_ones.as_ptr(), n);
        let d_t16_c4 = k10_f32_dot_tree16_fma(f32_a_cancel4.as_ptr(), f32_b_ones.as_ptr(), n);

        // f64 axpy bit-exact check against scalar loop with black_box preventing vectorization
        let mut y_simd = axpy_y_init[..n].to_vec();
        k11_f64_axpy_elementwise(axpy_a, axpy_x.as_ptr(), y_simd.as_mut_ptr(), n);
        let mut axpy_bit_diffs = 0usize;
        let mut axpy_max_abs = 0.0f64;
        for i in 0..n {
            let ref_y = black_box(axpy_a) * black_box(axpy_x[i]) + black_box(axpy_y_init[i]);
            if y_simd[i].to_bits() != ref_y.to_bits() {
                axpy_bit_diffs += 1;
            }
            let diff = (y_simd[i] - ref_y).abs();
            if diff > axpy_max_abs {
                axpy_max_abs = diff;
            }
        }

        // Integer bit-exact checks against black_box scalar
        let u32_sum = k12_u32_wrapping_sum_reduce(u32_data.as_ptr(), n);
        let mut u32_ref = 0u32;
        for i in 0..n { u32_ref = u32_ref.wrapping_add(black_box(u32_data[i])); }

        let u8_cnt = k13_u8_byte_count(u8_data.as_ptr(), n, u8_needle);
        let mut u8_ref = 0u32;
        for i in 0..n { u8_ref = u8_ref.wrapping_add((black_box(u8_data[i]) == u8_needle) as u32); }

        let s4_sum = k14_u32_strided4_sum(u32_strided_data.as_ptr(), n);
        let mut s4_ref = 0u32;
        for i in 0..n { s4_ref = s4_ref.wrapping_add(black_box(u32_strided_data[i * 4])); }

        let g_sum = k15_u32_indexed_gather_sum(gather_tables[ti].as_ptr(), gather_indices[ti].as_ptr(), n);
        let mut g_ref = 0u32;
        for i in 0..n { g_ref = g_ref.wrapping_add(black_box(gather_tables[ti][gather_indices[ti][i] as usize])); }

        fn fmt_f64_cmp(name: &str, v: f64, ref_v: f64, exact_math: Option<f64>) -> String {
            let exact_part = match exact_math {
                Some(em) => format!(",\"abs_err_vs_exact_math\":{:.17e}", (v - em).abs()),
                None => String::new(),
            };
            format!(
                "\"{}\":{{\"val\":{:.17e},\"bits\":\"0x{:016x}\",\"bit_exact_vs_ieee_ltr\":{},\"abs_err_vs_ieee_ltr\":{:.17e},\"ulp_diff_vs_ieee_ltr\":{}{}}}",
                name, v, v.to_bits(), v.to_bits() == ref_v.to_bits(), (v - ref_v).abs(), ulp_diff_f64(v, ref_v), exact_part
            )
        }
        fn fmt_f32_cmp(name: &str, v: f32, ref_v: f32, exact_math: Option<f64>) -> String {
            let exact_part = match exact_math {
                Some(em) => format!(",\"abs_err_vs_exact_math\":{:.9e}", ((v as f64) - em).abs()),
                None => String::new(),
            };
            format!(
                "\"{}\":{{\"val\":{:.9e},\"bits\":\"0x{:08x}\",\"bit_exact_vs_ieee_ltr\":{},\"abs_err_vs_ieee_ltr\":{:.9e},\"ulp_diff_vs_ieee_ltr\":{}{}}}",
                name, v, v.to_bits(), v.to_bits() == ref_v.to_bits(), (v - ref_v).abs(), ulp_diff_f32(v, ref_v), exact_part
            )
        }

        let exact_c4 = (n / 2) as f64;
        let exact_c8 = (6 * (n / 8)) as f64;
        let exact_f32_c4 = (n / 2) as f64;

        num_checks.push(format!(
            "{{\"n\":{},\"f64_well\":{{{},{},{},{},{},{},{}}},\"f64_cancel4\":{{\"exact_math_sum\":{:.17e},{},{},{},{},{},{},{}}},\"f64_cancel8\":{{\"exact_math_sum\":{:.17e},{},{},{},{},{},{},{}}},\"f32_dot_well\":{{{},{},{}}},\"f32_dot_cancel4\":{{\"exact_math_sum\":{:.9e},{},{},{}}},\"f64_axpy_bit_diffs\":{},\"f64_axpy_max_abs_err\":{:.17e},\"int_exact\":{{\"u32_wrapping_sum_eq\":{},\"u8_byte_count_eq\":{},\"u32_strided4_eq\":{},\"u32_gather_eq\":{}}}}}",
            n,
            fmt_f64_cmp("ordered_scalar", r_s_w, r_s_w, None),
            fmt_f64_cmp("ordered_simd_chunk4", r_o4_w, r_s_w, None),
            fmt_f64_cmp("ordered_simd_chunk8", r_o8_w, r_s_w, None),
            fmt_f64_cmp("reassoc_fadd_fast", r_ff_w, r_s_w, None),
            fmt_f64_cmp("reassoc_tree4", r_t4_w, r_s_w, None),
            fmt_f64_cmp("reassoc_tree8", r_t8_w, r_s_w, None),
            fmt_f64_cmp("reassoc_tree16", r_t16_w, r_s_w, None),
            exact_c4,
            fmt_f64_cmp("ordered_scalar", r_s_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("ordered_simd_chunk4", r_o4_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("ordered_simd_chunk8", r_o8_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("reassoc_fadd_fast", r_ff_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("reassoc_tree4", r_t4_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("reassoc_tree8", r_t8_c4, r_s_c4, Some(exact_c4)),
            fmt_f64_cmp("reassoc_tree16", r_t16_c4, r_s_c4, Some(exact_c4)),
            exact_c8,
            fmt_f64_cmp("ordered_scalar", r_s_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("ordered_simd_chunk4", r_o4_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("ordered_simd_chunk8", r_o8_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("reassoc_fadd_fast", r_ff_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("reassoc_tree4", r_t4_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("reassoc_tree8", r_t8_c8, r_s_c8, Some(exact_c8)),
            fmt_f64_cmp("reassoc_tree16", r_t16_c8, r_s_c8, Some(exact_c8)),
            fmt_f32_cmp("ordered", d_o_w, d_o_w, None),
            fmt_f32_cmp("reassoc_fma", d_ff_w, d_o_w, None),
            fmt_f32_cmp("tree16_fma", d_t16_w, d_o_w, None),
            exact_f32_c4,
            fmt_f32_cmp("ordered", d_o_c4, d_o_c4, Some(exact_f32_c4)),
            fmt_f32_cmp("reassoc_fma", d_ff_c4, d_o_c4, Some(exact_f32_c4)),
            fmt_f32_cmp("tree16_fma", d_t16_c4, d_o_c4, Some(exact_f32_c4)),
            axpy_bit_diffs,
            axpy_max_abs,
            u32_sum == u32_ref,
            u8_cnt == u8_ref,
            s4_sum == s4_ref,
            g_sum == g_ref,
        ));
    }

    // -------------------------------------------------------------------------
    // Phase 2: 9 Interleaved Timing Rounds across all 15 Kernels x 6 Trip Counts
    // -------------------------------------------------------------------------
    let kernel_names: [&str; 15] = [
        "k01_f64_sum_ordered_scalar",
        "k02_f64_sum_ordered_simd_chunk4",
        "k03_f64_sum_ordered_simd_chunk8",
        "k04_f64_sum_reassoc_fadd_fast",
        "k05_f64_sum_reassoc_tree4",
        "k06_f64_sum_reassoc_tree8",
        "k07_f64_sum_reassoc_tree16",
        "k08_f32_dot_ordered",
        "k09_f32_dot_reassoc_fma",
        "k10_f32_dot_tree16_fma",
        "k11_f64_axpy_elementwise",
        "k12_u32_wrapping_sum_reduce",
        "k13_u8_byte_count",
        "k14_u32_strided4_sum",
        "k15_u32_indexed_gather_sum",
    ];
    let bytes_per_elem: [f64; 15] = [
        8.0, 8.0, 8.0, 8.0, 8.0, 8.0, 8.0,
        8.0, 8.0, 8.0,
        24.0, // axpy: read x (8) + read y (8) + write y (8)
        4.0,
        1.0,
        4.0,  // useful elements loaded (stride-4 footprint = 16 B/elem)
        8.0,  // 4B index + 4B gathered value
    ];

    let mut axpy_y_buf = axpy_y_init.clone();
    // samples[ki][ti] = Vec<f64> of ns_per_elem over 9 rounds
    let mut samples: Vec<Vec<Vec<f64>>> = vec![vec![Vec::with_capacity(rounds); trip_counts.len()]; kernel_names.len()];

    // Warmup round + 9 measured rounds (interleaved across all kernels & trip counts)
    for round in 0..(rounds + 1) {
        let record = round > 0;
        for (ti, &n) in trip_counts.iter().enumerate() {
            let iters = iters_for_n(n);
            let denom = (iters as f64) * (n as f64);

            // Reset axpy buffer once per (round, n) so y stays well-conditioned near 1.0
            axpy_y_buf[..n].copy_from_slice(&axpy_y_init[..n]);

            for ki in 0..kernel_names.len() {
                let t0 = Instant::now();
                match ki {
                    0 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k01_f64_sum_ordered_scalar(p, black_box(n)); }
                        black_box(sink);
                    }
                    1 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k02_f64_sum_ordered_simd_chunk4(p, black_box(n)); }
                        black_box(sink);
                    }
                    2 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k03_f64_sum_ordered_simd_chunk8(p, black_box(n)); }
                        black_box(sink);
                    }
                    3 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k04_f64_sum_reassoc_fadd_fast(p, black_box(n)); }
                        black_box(sink);
                    }
                    4 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k05_f64_sum_reassoc_tree4(p, black_box(n)); }
                        black_box(sink);
                    }
                    5 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k06_f64_sum_reassoc_tree8(p, black_box(n)); }
                        black_box(sink);
                    }
                    6 => {
                        let p = black_box(f64_well.as_ptr());
                        let mut sink = 0.0f64;
                        for _ in 0..iters { sink += k07_f64_sum_reassoc_tree16(p, black_box(n)); }
                        black_box(sink);
                    }
                    7 => {
                        let pa = black_box(f32_a_well.as_ptr());
                        let pb = black_box(f32_b_well.as_ptr());
                        let mut sink = 0.0f32;
                        for _ in 0..iters { sink += k08_f32_dot_ordered(pa, pb, black_box(n)); }
                        black_box(sink);
                    }
                    8 => {
                        let pa = black_box(f32_a_well.as_ptr());
                        let pb = black_box(f32_b_well.as_ptr());
                        let mut sink = 0.0f32;
                        for _ in 0..iters { sink += k09_f32_dot_reassoc_fma(pa, pb, black_box(n)); }
                        black_box(sink);
                    }
                    9 => {
                        let pa = black_box(f32_a_well.as_ptr());
                        let pb = black_box(f32_b_well.as_ptr());
                        let mut sink = 0.0f32;
                        for _ in 0..iters { sink += k10_f32_dot_tree16_fma(pa, pb, black_box(n)); }
                        black_box(sink);
                    }
                    10 => {
                        let px = black_box(axpy_x.as_ptr());
                        let py = black_box(axpy_y_buf.as_mut_ptr());
                        let a = black_box(axpy_a);
                        for _ in 0..iters { k11_f64_axpy_elementwise(a, px, py, black_box(n)); }
                        black_box(axpy_y_buf[0]);
                    }
                    11 => {
                        let p = black_box(u32_data.as_ptr());
                        let mut sink = 0u32;
                        for _ in 0..iters { sink = sink.wrapping_add(k12_u32_wrapping_sum_reduce(p, black_box(n))); }
                        black_box(sink);
                    }
                    12 => {
                        let p = black_box(u8_data.as_ptr());
                        let ndl = black_box(u8_needle);
                        let mut sink = 0u32;
                        for _ in 0..iters { sink = sink.wrapping_add(k13_u8_byte_count(p, black_box(n), ndl)); }
                        black_box(sink);
                    }
                    13 => {
                        let p = black_box(u32_strided_data.as_ptr());
                        let mut sink = 0u32;
                        for _ in 0..iters { sink = sink.wrapping_add(k14_u32_strided4_sum(p, black_box(n))); }
                        black_box(sink);
                    }
                    14 => {
                        let pt = black_box(gather_tables[ti].as_ptr());
                        let pi = black_box(gather_indices[ti].as_ptr());
                        let mut sink = 0u32;
                        for _ in 0..iters { sink = sink.wrapping_add(k15_u32_indexed_gather_sum(pt, pi, black_box(n))); }
                        black_box(sink);
                    }
                    _ => unreachable!(),
                }
                let elapsed_ns = t0.elapsed().as_nanos() as f64;
                if record {
                    samples[ki][ti].push(elapsed_ns / denom);
                }
            }
        }
    }

    // Emit JSON to stdout
    let mut timing_entries = Vec::new();
    for (ki, kname) in kernel_names.iter().enumerate() {
        let mut by_n = Vec::new();
        for (ti, &n) in trip_counts.iter().enumerate() {
            let mut v = samples[ki][ti].clone();
            v.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let med = v[v.len() / 2];
            let min_v = v[0];
            let max_v = v[v.len() - 1];
            let q1 = v[v.len() / 4];
            let q3 = v[(3 * v.len()) / 4];
            let gb_s = bytes_per_elem[ki] / med; // (bytes/elem) / (ns/elem) == GB/s (10^9 B/s)
            let raw_str = samples[ki][ti]
                .iter()
                .map(|x| format!("{:.6}", x))
                .collect::<Vec<_>>()
                .join(",");
            by_n.push(format!(
                "\"{}\":{{\"iters\":{},\"median_ns_per_elem\":{:.6},\"min_ns_per_elem\":{:.6},\"max_ns_per_elem\":{:.6},\"iqr_ns_per_elem\":{:.6},\"median_gb_per_s\":{:.4},\"rounds_ns_per_elem\":[{}]}}",
                n, iters_for_n(n), med, min_v, max_v, q3 - q1, gb_s, raw_str
            ));
        }
        timing_entries.push(format!(
            "\"{}\":{{\"bytes_per_elem\":{},\"by_n\":{{{}}}}}",
            kname, bytes_per_elem[ki], by_n.join(",")
        ));
    }

    println!(
        "{{\"rounds\":{},\"trip_counts\":[8,32,128,1024,16384,262144],\"numerical_verification\":[{}],\"timings\":{{{}}}}}",
        rounds,
        num_checks.join(","),
        timing_entries.join(",")
    );
}
"""

KERNEL_SYMBOLS = [
    "k01_f64_sum_ordered_scalar",
    "k02_f64_sum_ordered_simd_chunk4",
    "k03_f64_sum_ordered_simd_chunk8",
    "k04_f64_sum_reassoc_fadd_fast",
    "k05_f64_sum_reassoc_tree4",
    "k06_f64_sum_reassoc_tree8",
    "k07_f64_sum_reassoc_tree16",
    "k08_f32_dot_ordered",
    "k09_f32_dot_reassoc_fma",
    "k10_f32_dot_tree16_fma",
    "k11_f64_axpy_elementwise",
    "k12_u32_wrapping_sum_reduce",
    "k13_u8_byte_count",
    "k14_u32_strided4_sum",
    "k15_u32_indexed_gather_sum",
]


def analyze_x86_objdump(llvm_objdump: Path, bin_path: Path):
    """Disassemble actual linked binary via llvm-objdump -d and count real machine registers/mnemonics."""
    out = {}
    for sym in KERNEL_SYMBOLS:
        proc = run_cmd([str(llvm_objdump), "-d", f"--disassemble-symbols={sym}", str(bin_path)])
        lines = [l for l in proc.stdout.splitlines() if re.match(r"^\s*[0-9a-f]+:\s", l)]
        body = "\n".join(lines)
        xmm_insns = sum(1 for l in lines if re.search(r"%xmm\d+", l))
        ymm_insns = sum(1 for l in lines if re.search(r"%ymm\d+", l))
        zmm_insns = sum(1 for l in lines if re.search(r"%zmm\d+", l))
        k_insns = sum(1 for l in lines if re.search(r"%k[0-7]\b", l))
        fma_insns = sum(1 for l in lines if re.search(r"\bv?fmadd\w+", l))
        gather_insns = sum(1 for l in lines if re.search(r"\bv?p?gather\w+", l))
        # Distinguish vector packed FP ops vs scalar FP ops
        packed_fp_insns = sum(1 for l in lines if re.search(r"\bv?(add|mul|sub|fmadd\d*)(pd|ps)\b", l))
        scalar_fp_insns = sum(1 for l in lines if re.search(r"\bv?(add|mul|sub|fmadd\d*)(sd|ss)\b", l))
        packed_int_insns = sum(1 for l in lines if re.search(r"\bv?(padd|psub|pcmpeq|pmov|psad|punpck|pshuf|palign|pxor|por|pand)\w*\b", l))
        panic_calls = sum(1 for l in lines if "panic" in l or "slice_index" in l)

        if zmm_insns > 0:
            max_w = 512
        elif ymm_insns > 0:
            max_w = 256
        elif packed_fp_insns > 0 or packed_int_insns > 0:
            max_w = 128
        elif xmm_insns > 0:
            max_w = 64  # scalar FP in xmm
        else:
            max_w = 0

        # Capture exact representative vector mnemonics
        mnem_counts = Counter()
        for l in lines:
            # llvm-objdump format: "  addr: bytes... \tmnemonic\toperands"
            parts = l.split("\t")
            if len(parts) >= 2:
                mnem = parts[-1].strip().split()[0] if parts[-1].strip() else ""
                if mnem and (re.search(r"%[xyz]mm\d+|%k[0-7]", l) or "gather" in mnem):
                    mnem_counts[mnem] += 1

        out[sym] = {
            "total_insns": len(lines),
            "xmm_insns": xmm_insns,
            "ymm_insns": ymm_insns,
            "zmm_insns": zmm_insns,
            "k_mask_insns": k_insns,
            "packed_fp_insns": packed_fp_insns,
            "scalar_fp_insns": scalar_fp_insns,
            "packed_int_insns": packed_int_insns,
            "fma_insns": fma_insns,
            "gather_insns": gather_insns,
            "panic_calls": panic_calls,
            "max_active_vector_width_bits": max_w,
            "top_vector_mnemonics": dict(mnem_counts.most_common(10)),
        }
    return out


def compile_static_aarch64_disasm(bench_lib_src: Path):
    """Static-only cross-compilation for aarch64-unknown-linux-gnu (NEON and +sve).
    STRICTLY static disassembly — runtime is NOT measured on silicon.
    """
    out = {}
    for label, feat in [("aarch64_neon", None), ("aarch64_sve", "+sve")]:
        asm_path = SCRATCH_ROOT / f"part_b_{label}.s"
        cmd = [
            "rustc", TOOLCHAIN,
            "--target=aarch64-unknown-linux-gnu",
            "--crate-type=lib",
            "-C", "codegen-units=1",
            "-C", "opt-level=3",
            "--emit=asm",
            "-o", str(asm_path),
            str(bench_lib_src),
        ]
        if feat:
            cmd.extend(["-C", f"target-feature={feat}"])
        run_cmd(cmd, env={"RUSTC_BOOTSTRAP": "1"})
        s = asm_path.read_text()
        per_sym = {}
        for sym in KERNEL_SYMBOLS:
            m = re.search(rf"^{sym}:(.*?)^\.Lfunc_end", s, re.M | re.S)
            body = m.group(1) if m else ""
            insns = [l.strip() for l in body.splitlines() if l.strip() and not l.strip().startswith((".", "//"))]
            fadda = sum(1 for l in insns if re.match(r"fadda\b", l))
            fmla = sum(1 for l in insns if re.match(r"fmla\b", l))
            sve_z = sum(1 for l in insns if re.search(r"\bz\d+\.[bhsd]\b", l))
            neon_v = sum(1 for l in insns if re.search(r"\bv\d+\.\d+[bhsd]\b", l))
            gather = sum(1 for l in insns if re.match(r"ld1w\b.*z\d+\.", l))
            per_sym[sym] = {
                "total_asm_insns": len(insns),
                "sve_z_insns": sve_z,
                "neon_v_insns": neon_v,
                "fadda_ordered_reduce_insns": fadda,
                "fmla_insns": fmla,
                "sve_gather_ld1w_insns": gather,
            }
        out[label] = {
            "measurement_type": "static_disassembly_only",
            "runtime_timing": "not measured on silicon",
            "target": "aarch64-unknown-linux-gnu",
            "target_feature": feat or "default (NEON)",
            "kernels": per_sym,
        }
    return out


def run_part_b(llvm_objdump: Path):
    b_dir = SCRATCH_ROOT / "part_b"
    if b_dir.exists():
        shutil.rmtree(b_dir)
    b_dir.mkdir(parents=True, exist_ok=True)
    src_path = b_dir / "bench.rs"
    src_path.write_text(BENCH_RS)

    # Also write a library-only copy (no main) for static AArch64 cross-compile without aarch64 linker
    lib_src = b_dir / "bench_lib.rs"
    lib_src.write_text(BENCH_RS.split("fn main()", 1)[0])

    has_taskset = shutil.which("taskset") is not None
    pin_core = 12 if (os.cpu_count() or 1) > 12 else 0

    tiers_out = {}
    for tier_id, cpu, extra_feat, tier_desc in CPU_TIERS:
        print(f"[Part B] Building & executing native silicon benchmark for tier={tier_id} ...", flush=True)
        bin_path = b_dir / f"bench_{tier_id}"
        cmd = [
            "rustc", TOOLCHAIN,
            "-C", "opt-level=3",
            "-C", "codegen-units=1",
            "-C", f"target-cpu={cpu}",
            "-o", str(bin_path),
            str(src_path),
        ]
        if extra_feat:
            cmd.extend(["-C", f"target-feature={extra_feat}"])
        run_cmd(cmd, env={"RUSTC_BOOTSTRAP": "1"})

        disasm = analyze_x86_objdump(llvm_objdump, bin_path)

        exec_cmd = (["taskset", "-c", str(pin_core), str(bin_path)] if has_taskset else [str(bin_path)])
        t0 = time.perf_counter()
        proc = run_cmd(exec_cmd, cwd=b_dir)
        exec_wall_s = round(time.perf_counter() - t0, 3)
        bench_data = json.loads(proc.stdout)

        # Print crisp summary line for key kernels at N=262144 and N=32
        tm = bench_data["timings"]
        print(
            f"  [{tier_id}] wall={exec_wall_s}s | N=262144 ns/el: "
            f"ord_sc={tm['k01_f64_sum_ordered_scalar']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"ord_s8={tm['k03_f64_sum_ordered_simd_chunk8']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"fast={tm['k04_f64_sum_reassoc_fadd_fast']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"tree16={tm['k07_f64_sum_reassoc_tree16']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"axpy={tm['k11_f64_axpy_elementwise']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"u32sum={tm['k12_u32_wrapping_sum_reduce']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"u8cnt={tm['k13_u8_byte_count']['by_n']['262144']['median_ns_per_elem']:.3f} "
            f"gath={tm['k15_u32_indexed_gather_sum']['by_n']['262144']['median_ns_per_elem']:.3f}",
            flush=True,
        )

        tiers_out[tier_id] = {
            "target_cpu": cpu,
            "extra_target_feature": extra_feat,
            "description": tier_desc,
            "pinned_cpu_core": f"{pin_core} (taskset -c {pin_core})" if has_taskset else "unpinned",
            "exec_wall_s": exec_wall_s,
            "disassembly_objdump": disasm,
            "benchmark": bench_data,
        }

    # Build cross-tier speedup comparisons and numerical divergence summary
    speedups = {}
    for n_str in ["8", "32", "128", "1024", "16384", "262144"]:
        row = {}
        base_f64_ord = tiers_out["x86-64"]["benchmark"]["timings"]["k01_f64_sum_ordered_scalar"]["by_n"][n_str]["median_ns_per_elem"]
        base_f32_ord = tiers_out["x86-64"]["benchmark"]["timings"]["k08_f32_dot_ordered"]["by_n"][n_str]["median_ns_per_elem"]
        for tier_id, _, _, _ in CPU_TIERS:
            tm = tiers_out[tier_id]["benchmark"]["timings"]
            t_ord = tm["k01_f64_sum_ordered_scalar"]["by_n"][n_str]["median_ns_per_elem"]
            t_os8 = tm["k03_f64_sum_ordered_simd_chunk8"]["by_n"][n_str]["median_ns_per_elem"]
            t_ff = tm["k04_f64_sum_reassoc_fadd_fast"]["by_n"][n_str]["median_ns_per_elem"]
            t_t16 = tm["k07_f64_sum_reassoc_tree16"]["by_n"][n_str]["median_ns_per_elem"]
            t_d_ord = tm["k08_f32_dot_ordered"]["by_n"][n_str]["median_ns_per_elem"]
            t_d_ff = tm["k09_f32_dot_reassoc_fma"]["by_n"][n_str]["median_ns_per_elem"]
            t_d_t16 = tm["k10_f32_dot_tree16_fma"]["by_n"][n_str]["median_ns_per_elem"]
            row[tier_id] = {
                "f64_ordered_simd8_vs_scalar": round(t_ord / t_os8, 3),
                "f64_fadd_fast_vs_ordered_scalar": round(t_ord / t_ff, 3),
                "f64_tree16_vs_ordered_scalar": round(t_ord / t_t16, 3),
                "f64_fadd_fast_vs_x86_64_ordered_scalar": round(base_f64_ord / t_ff, 3),
                "f32_dot_reassoc_fma_vs_ordered": round(t_d_ord / t_d_ff, 3),
                "f32_dot_tree16_fma_vs_ordered": round(t_d_ord / t_d_t16, 3),
                "f32_dot_tree16_fma_vs_x86_64_ordered": round(base_f32_ord / t_d_t16, 3),
                "axpy_vs_x86_64": round(
                    tiers_out["x86-64"]["benchmark"]["timings"]["k11_f64_axpy_elementwise"]["by_n"][n_str]["median_ns_per_elem"]
                    / tm["k11_f64_axpy_elementwise"]["by_n"][n_str]["median_ns_per_elem"], 3
                ),
                "u32_sum_vs_x86_64": round(
                    tiers_out["x86-64"]["benchmark"]["timings"]["k12_u32_wrapping_sum_reduce"]["by_n"][n_str]["median_ns_per_elem"]
                    / tm["k12_u32_wrapping_sum_reduce"]["by_n"][n_str]["median_ns_per_elem"], 3
                ),
                "u8_count_vs_x86_64": round(
                    tiers_out["x86-64"]["benchmark"]["timings"]["k13_u8_byte_count"]["by_n"][n_str]["median_ns_per_elem"]
                    / tm["k13_u8_byte_count"]["by_n"][n_str]["median_ns_per_elem"], 3
                ),
                "u32_strided4_vs_x86_64": round(
                    tiers_out["x86-64"]["benchmark"]["timings"]["k14_u32_strided4_sum"]["by_n"][n_str]["median_ns_per_elem"]
                    / tm["k14_u32_strided4_sum"]["by_n"][n_str]["median_ns_per_elem"], 3
                ),
                "u32_gather_vs_x86_64": round(
                    tiers_out["x86-64"]["benchmark"]["timings"]["k15_u32_indexed_gather_sum"]["by_n"][n_str]["median_ns_per_elem"]
                    / tm["k15_u32_indexed_gather_sum"]["by_n"][n_str]["median_ns_per_elem"], 3
                ),
            }
        speedups[n_str] = row

    # Static-only AArch64 disassembly comparison
    print("[Part B] Cross-compiling static-only AArch64 NEON / +sve disassembly ...", flush=True)
    aarch64_static = compile_static_aarch64_disasm(lib_src)

    return {
        "host_tiers": tiers_out,
        "speedup_summary": speedups,
        "static_cross_arch_disassembly": aarch64_static,
    }


def main():
    parser = argparse.ArgumentParser(description="E2-7 real vectorization census + native silicon FP/int probe")
    parser.add_argument("--keep-tmp", action="store_true", help="Keep /tmp/vrustc_e2_7 after execution")
    parser.add_argument("--out", type=Path, default=OUT_JSON, help="Output JSON path")
    args = parser.parse_args()

    SCRATCH_ROOT.mkdir(parents=True, exist_ok=True)
    try:
        meta = gather_host_metadata()
        part_a = run_part_a()
        sysroot = Path(run_cmd(["rustc", TOOLCHAIN, "--print", "sysroot"]).stdout.strip())
        part_b = run_part_b(sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump")

        # Verify critical invariants before writing JSON
        all_ordered_bit_exact = True
        all_axpy_bit_exact = True
        all_int_exact = True
        for tier_id in ("x86-64", "x86-64-v3", "x86-64-v4", "x86-64-v4-zmm512"):
            for entry in part_b["host_tiers"][tier_id]["benchmark"]["numerical_verification"]:
                for ds in ("f64_well", "f64_cancel4", "f64_cancel8"):
                    if not entry[ds]["ordered_simd_chunk4"]["bit_exact_vs_ieee_ltr"]:
                        all_ordered_bit_exact = False
                    if not entry[ds]["ordered_simd_chunk8"]["bit_exact_vs_ieee_ltr"]:
                        all_ordered_bit_exact = False
                if entry["f64_axpy_bit_diffs"] != 0:
                    all_axpy_bit_exact = False
                if not all(entry["int_exact"].values()):
                    all_int_exact = False

        payload = {
            "probe_id": "E2-7",
            "title": "Real rustc 1.99.1 / LLVM 23.1.1 Ecosystem Vectorization Census + Native Xeon AVX-512 Execution of Scalar, Ordered-SIMD, and Reassociated FP/Int Kernels",
            "measurement_label": "[real measurement]",
            "metadata": meta,
            "invariant_checks": {
                "all_ordered_simd_bit_exact_with_scalar_across_all_tiers_and_N": all_ordered_bit_exact,
                "all_f64_axpy_bit_exact_with_scalar_across_all_tiers_and_N": all_axpy_bit_exact,
                "all_integer_kernels_exact_across_all_tiers_and_N": all_int_exact,
                "all_part_b_kernels_zero_panic_calls_in_disasm": all(
                    k["panic_calls"] == 0
                    for t in part_b["host_tiers"].values()
                    for k in t["disassembly_objdump"].values()
                ),
            },
            "part_a_ecosystem_census": part_a,
            "part_b_silicon_execution": part_b,
        }

        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(payload, indent=2) + "\n")
        print(f"[E2-7] Wrote {args.out} ({args.out.stat().st_size} bytes)", flush=True)
        print("[E2-7] Invariant checks:", json.dumps(payload["invariant_checks"]), flush=True)
    finally:
        if not args.keep_tmp and SCRATCH_ROOT.exists():
            shutil.rmtree(SCRATCH_ROOT)
            print(f"[E2-7] Cleaned up {SCRATCH_ROOT}", flush=True)


if __name__ == "__main__":
    main()
