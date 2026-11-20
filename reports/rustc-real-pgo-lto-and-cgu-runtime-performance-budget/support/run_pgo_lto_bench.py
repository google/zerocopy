#!/usr/bin/env python3
"""E2-3 (T09 Real Un-Rigged PGO + 4-Mode LTO + -O2/-O3 Runtime Benchmark):
Replaces Stage 0c Refutations O5_ (rigged --cfg feature="anneal_specialized") and O8_ (hardcoded ThinLTO).

Compiles the EXACT SAME Rust benchmark crate (ZERO --cfg flags, 100% offline against cached crates:
miniz_oxide 0.9.1, serde_json 1.0.154, memchr 2.8.3, base64 0.23.1, crc32fast 1.5.5, toml 1.2.0) under 7 real
rustc 1.99.1 profiles:
  1. O2_cgu16     : -C opt-level=2, lto=off, cgu=16
  2. O3_cgu16     : -C opt-level=3, lto=off, cgu=16 (default Cargo --release baseline)
  3. O3_cgu1      : -C opt-level=3, lto=off, cgu=1
  4. O3_thin      : -C opt-level=3, lto=thin
  5. O3_fat       : -C opt-level=3, lto=fat
  6. O3_cgu16_pgo : -C opt-level=3, lto=off, cgu=16 + REAL -C profile-generate / llvm-profdata / -C profile-use
  7. O3_thin_pgo  : -C opt-level=3, lto=thin        + REAL -C profile-generate / llvm-profdata / -C profile-use

Trains PGO on a DISJOINT training corpus (`--mode train`) and benchmarks all 7 binaries on a HELD-OUT test
corpus (`--mode eval`) across 9 interleaved rounds, asserting 100% bit-identical checksums across all 7 binaries!
"""
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import time

OUT_JSON = Path(os.environ.get("OUT_JSON", "e2_3_real_pgo_and_lto_runtime.json"))
WORK = Path("/tmp/vrustc_e2_3")
CRATE_DIR = WORK / "bench_crate"

CARGO_TOML = """[package]
name = "e2_3_pgo_lto_bench"
version = "0.1.0"
edition = "2021"

[dependencies]
miniz_oxide = "=0.9.1"
serde_json = "=1.0.154"
memchr = "=2.8.3"
base64 = "=0.23.1"
crc32fast = "=1.5.5"
toml = "=1.2.0+spec-1.1.0"
"""

MAIN_RS = r"""use std::env;
use std::hint::black_box;
use std::time::Instant;
use base64::Engine as _;

fn gen_text_payload(seed: u64, n_records: usize) -> String {
    let mut s = String::with_capacity(n_records * 120);
    let mut x = seed ^ 0x9e37_79b9_7f4a_7c15;
    s.push_str("{\"records\":[");
    for i in 0..n_records {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        if i > 0 {
            s.push(',');
        }
        let kind = match (x >> 4) & 3 {
            0 => "alpha_MirStmt_assign",
            1 => "beta_TreeBorrows_cell",
            2 => "gamma_MiniSsa_phi_node",
            _ => "delta_Unwind_landingpad",
        };
        let v1 = (x >> 16) & 0xffff;
        let v2 = (x >> 32) & 0xffff;
        let flag = (x & 1) == 0;
        let line = format!(
            "{{\"id\":{},\"kind\":\"{}\",\"vals\":[{},{},{}],\"ok\":{},\"meta\":{{\"tag\":\"t{}\",\"score\":{:.3}}}}}",
            i, kind, v1, v2, v1.wrapping_add(v2), flag, x & 0xff, (v1 as f64) / 13.0
        );
        s.push_str(&line);
    }
    s.push_str("]}");
    s
}

fn gen_toml_payload(seed: u64, n_sections: usize) -> String {
    let mut s = String::with_capacity(n_sections * 140);
    let mut x = seed ^ 0xbf58_476d_1ce4_e5b9;
    for i in 0..n_sections {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1);
        s.push_str(&format!(
            "[crate.mod_{}]\nversion = \"1.{}.{}\"\nedition = \"2021\"\nopt_level = {}\nflags = [\"nuw\", \"noundef\", \"noalias\", \"f{}\"]\nenabled = {}\n\n",
            i,
            (x >> 8) & 15,
            (x >> 16) & 31,
            (x >> 24) & 3,
            x & 63,
            (x & 1) == 0
        ));
    }
    s
}

fn gen_binary_payload(seed: u64, len: usize) -> Vec<u8> {
    let mut out = vec![0u8; len];
    let mut x = seed ^ 0x94d0_49bb_1331_11eb;
    let mut i = 0;
    while i < len {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        // Mix compressible runs with pseudo-random bytes (realistic DEFLATE input)
        if (x & 7) < 5 {
            let pat = (x >> 8) as u8;
            let run = (((x >> 16) & 31) as usize + 4).min(len - i);
            for j in 0..run {
                out[i + j] = pat.wrapping_add((j as u8) & 3);
            }
            i += run;
        } else {
            out[i] = (x >> 24) as u8;
            i += 1;
        }
    }
    out
}

fn run_suite(seed: u64, scale: usize) {
    let json_doc = gen_text_payload(seed, 320 * scale);
    let toml_doc = gen_toml_payload(seed.wrapping_add(17), 220 * scale);
    let bin_buf = gen_binary_payload(seed.wrapping_add(31), 256 * 1024 * scale);

    // 1. miniz_oxide DEFLATE compress + inflate roundtrip
    let t0 = Instant::now();
    let mut deflate_chk: u64 = 0;
    for lvl in [4u8, 6u8] {
        let comp = miniz_oxide::deflate::compress_to_vec(black_box(&bin_buf), lvl);
        let decomp = miniz_oxide::inflate::decompress_to_vec(black_box(&comp)).unwrap();
        assert_eq!(decomp.len(), bin_buf.len());
        deflate_chk = deflate_chk.wrapping_mul(31).wrapping_add(comp.len() as u64).wrapping_add(decomp[seed as usize % decomp.len()] as u64);
    }
    let deflate_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // 2. serde_json parse + serialize
    let t1 = Instant::now();
    let mut json_chk: u64 = 0;
    for _ in 0..6 {
        let val: serde_json::Value = serde_json::from_str(black_box(&json_doc)).unwrap();
        let ser = serde_json::to_vec(black_box(&val)).unwrap();
        json_chk = json_chk.wrapping_add(ser.len() as u64).wrapping_add(ser[7] as u64);
    }
    let json_ms = t1.elapsed().as_secs_f64() * 1000.0;

    // 3. toml parse + serialize
    let t2 = Instant::now();
    let mut toml_chk: u64 = 0;
    for _ in 0..4 {
        let val: toml::Value = toml::from_str(black_box(&toml_doc)).unwrap();
        let ser = toml::to_string(black_box(&val)).unwrap();
        toml_chk = toml_chk.wrapping_add(ser.len() as u64);
    }
    let toml_ms = t2.elapsed().as_secs_f64() * 1000.0;

    // 4. memchr / memmem multi-pattern scan
    let mut scan_buf = Vec::with_capacity(json_doc.len() * 8);
    for _ in 0..8 {
        scan_buf.extend_from_slice(json_doc.as_bytes());
    }
    let t3 = Instant::now();
    let finder1 = memchr::memmem::Finder::new(b"TreeBorrows_cell");
    let finder2 = memchr::memmem::Finder::new(b"Unwind_landingpad");
    let mut memchr_chk: u64 = 0;
    for _ in 0..12 {
        memchr_chk = memchr_chk.wrapping_add(finder1.find_iter(black_box(&scan_buf)).count() as u64);
        memchr_chk = memchr_chk.wrapping_add(finder2.find_iter(black_box(&scan_buf)).count() as u64);
        memchr_chk = memchr_chk.wrapping_add(memchr::memchr3_iter(b'{', b'}', b':', black_box(&scan_buf)).count() as u64);
    }
    let memchr_ms = t3.elapsed().as_secs_f64() * 1000.0;

    // 5. base64 encode + decode roundtrip
    let t4 = Instant::now();
    let mut b64_chk: u64 = 0;
    let eng = base64::engine::general_purpose::STANDARD;
    for _ in 0..8 {
        let enc = eng.encode(black_box(&bin_buf));
        let dec = eng.decode(black_box(&enc)).unwrap();
        assert_eq!(dec.len(), bin_buf.len());
        b64_chk = b64_chk.wrapping_add(enc.len() as u64).wrapping_add(dec[0] as u64);
    }
    let b64_ms = t4.elapsed().as_secs_f64() * 1000.0;

    // 6. crc32fast streaming hash
    let t5 = Instant::now();
    let mut crc_chk: u64 = 0;
    for _ in 0..48 {
        let mut h = crc32fast::Hasher::new();
        h.update(black_box(&bin_buf));
        h.update(black_box(json_doc.as_bytes()));
        crc_chk = crc_chk.wrapping_add(h.finalize() as u64);
    }
    let crc_ms = t5.elapsed().as_secs_f64() * 1000.0;

    // 7. Skewed dyn-Trait indirect dispatch (85% hot impl, 15% cold impls — classic PGO ICP workload)
    trait ByteFilter {
        fn step(&self, acc: u64, b: u8) -> u64;
    }
    struct HotMulXor(u64);
    struct ColdAddRot(u32);
    struct ColdMix(u64);
    impl ByteFilter for HotMulXor {
        fn step(&self, acc: u64, b: u8) -> u64 {
            acc.wrapping_mul(self.0) ^ (b as u64).wrapping_add(0x9e37)
        }
    }
    impl ByteFilter for ColdAddRot {
        fn step(&self, acc: u64, b: u8) -> u64 {
            acc.rotate_left(self.0).wrapping_add(b as u64)
        }
    }
    impl ByteFilter for ColdMix {
        fn step(&self, acc: u64, b: u8) -> u64 {
            (acc ^ self.0).wrapping_add((b as u64) << 7)
        }
    }
    let f_hot = HotMulXor(6364136223846793005);
    let f_c1 = ColdAddRot(7);
    let f_c2 = ColdMix(0xbf58476d1ce4e5b9);
    let mut filters: Vec<&dyn ByteFilter> = Vec::with_capacity(1024);
    let mut sx = seed ^ 0x1234_5678_9abc_def0;
    for _ in 0..1024 {
        sx = sx.wrapping_mul(6364136223846793005).wrapping_add(1);
        let r = (sx >> 32) % 100;
        if r < 85 {
            filters.push(&f_hot);
        } else if r < 93 {
            filters.push(&f_c1);
        } else {
            filters.push(&f_c2);
        }
    }
    let t6 = Instant::now();
    let mut dyn_chk: u64 = seed;
    let slice = &bin_buf[..65536];
    for rep in 0..24usize {
        for (i, &b) in slice.iter().enumerate() {
            let f = black_box(filters[(i + rep * 17) & 1023]);
            dyn_chk = f.step(dyn_chk, b);
        }
    }
    let dyn_ms = t6.elapsed().as_secs_f64() * 1000.0;

    let total_ms = deflate_ms + json_ms + toml_ms + memchr_ms + b64_ms + crc_ms + dyn_ms;
    println!(
        "{{\"deflate_ms\":{:.3},\"json_ms\":{:.3},\"toml_ms\":{:.3},\"memchr_ms\":{:.3},\"base64_ms\":{:.3},\"crc32_ms\":{:.3},\"dyn_icp_ms\":{:.3},\"total_ms\":{:.3},\"chk\":[{},{},{},{},{},{},{}]}}",
        deflate_ms, json_ms, toml_ms, memchr_ms, b64_ms, crc_ms, dyn_ms, total_ms,
        deflate_chk, json_chk, toml_chk, memchr_chk, b64_chk, crc_chk, dyn_chk
    );
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("eval");
    match mode {
        "train" => {
            // Disjoint training seeds & scale
            for s in [101u64, 202, 303] {
                run_suite(s, 2);
            }
        }
        _ => {
            // Held-out evaluation seed
            run_suite(9_999_991u64, 2);
        }
    }
}
"""


def elf_text_bytes(bin_path: Path) -> int:
    out = subprocess.check_output(["size", str(bin_path)], text=True).splitlines()
    return int(out[1].split()[0]) if len(out) >= 2 else 0


def build_profile(name: str, cenv: dict[str, str], rustflags: str = "") -> tuple[Path, float, int]:
    tdir = WORK / f"target_{name}"
    if tdir.exists():
        shutil.rmtree(tdir)
    env = os.environ.copy()
    env.pop("RUSTFLAGS", None)
    for k in list(env.keys()):
        if k.startswith("CARGO_PROFILE_RELEASE_"):
            env.pop(k, None)
    env.update(cenv)
    if rustflags:
        env["RUSTFLAGS"] = rustflags
    env["RUSTC_ICE"] = "0"
    t0 = time.monotonic()
    r = subprocess.run(
        ["cargo", "+1.99.1", "build", "--release", "--offline", "--target-dir", str(tdir)],
        cwd=str(CRATE_DIR), env=env, capture_output=True, text=True, timeout=600,
    )
    if r.returncode != 0:
        raise RuntimeError(f"Build {name} failed (rc={r.returncode}):\n{r.stderr[-1000:]}")
    dt = round(time.monotonic() - t0, 2)
    bin_p = tdir / "release/e2_3_pgo_lto_bench"
    txt = elf_text_bytes(bin_p)
    print(f"  Built {name:16s}: build={dt:5.2f}s | .text={txt/1024:6.1f}KB", flush=True)
    return bin_p, dt, txt


def main() -> None:
    if WORK.exists():
        shutil.rmtree(WORK)
    (CRATE_DIR / "src").mkdir(parents=True)
    (CRATE_DIR / "Cargo.toml").write_text(CARGO_TOML, encoding="utf-8")
    (CRATE_DIR / "src/main.rs").write_text(MAIN_RS, encoding="utf-8")

    # Find llvm-profdata matching rustc 1.99.1 if available, else /usr/bin/llvm-profdata
    profdata_bin = "/usr/bin/llvm-profdata"
    rustup_pd = list(Path.home() / ".rustup/toolchains".glob("1.99.1*/lib/rustlib/*/bin/llvm-profdata"))
    if rustup_pd:
        profdata_bin = str(rustup_pd[0])
    print(f"Using llvm-profdata: {profdata_bin}", flush=True)

    print("\n=== Step 1: Building 5 non-PGO profiles (rustc 1.99.1, offline, zero --cfg cheats) ===", flush=True)
    profiles = {}
    specs = [
        ("O2_cgu16", {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "2", "CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16"}),
        ("O3_cgu16", {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16"}),
        ("O3_cgu1",  {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "1"}),
        ("O3_thin",  {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "thin"}),
        ("O3_fat",   {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "fat"}),
    ]
    for name, cenv in specs:
        bp, dt, txt = build_profile(name, cenv)
        profiles[name] = {"bin": bp, "build_sec": dt, "text_bytes": txt}

    print("\n=== Step 2: Real PGO (matched LTO profile-generate -> train on disjoint corpus -> llvm-profdata merge -> profile-use) ===", flush=True)
    pgo_meta = {}
    for pgo_name, cenv in [
        ("O3_cgu16_pgo", {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "off", "CARGO_PROFILE_RELEASE_CODEGEN_UNITS": "16"}),
        ("O3_thin_pgo",  {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "thin"}),
        ("O3_fat_pgo",   {"CARGO_PROFILE_RELEASE_OPT_LEVEL": "3", "CARGO_PROFILE_RELEASE_LTO": "fat"}),
    ]:
        pgo_dir = WORK / f"pgo_data_{pgo_name}"
        pgo_dir.mkdir(parents=True)
        gen_bin, gen_dt, _ = build_profile(f"pgo_gen_{pgo_name}", cenv, rustflags=f"-Cprofile-generate={pgo_dir}")
        t_train0 = time.monotonic()
        subprocess.run([str(gen_bin), "train"], capture_output=True, text=True, check=True, timeout=180)
        tr_s = round(time.monotonic() - t_train0, 2)
        profraws = sorted(pgo_dir.glob("*.profraw"))
        merged = WORK / f"merged_{pgo_name}.profdata"
        subprocess.run([profdata_bin, "merge", "-o", str(merged), *[str(p) for p in profraws]], check=True, capture_output=True, text=True)
        print(f"  PGO {pgo_name} trained ({tr_s}s): {len(profraws)} profraw -> {merged.stat().st_size:,} B", flush=True)
        pgo_meta[pgo_name] = {"gen_build_sec": gen_dt, "train_sec": tr_s, "profraw_count": len(profraws), "merged_bytes": merged.stat().st_size}
        bp, dt, txt = build_profile(pgo_name, cenv, rustflags=f"-Cprofile-use={merged}")
        profiles[pgo_name] = {"bin": bp, "build_sec": dt, "text_bytes": txt}
    train_s = sum(v["train_sec"] for v in pgo_meta.values())

    print("\n=== Step 3: Interleaved Held-Out Evaluation (9 rounds, exact checksum lock) ===", flush=True)
    names = list(profiles.keys())
    samples: dict[str, list[dict]] = {n: [] for n in names}
    expected_chk = None
    # Warmup 1 round
    for n in names:
        out = subprocess.check_output([str(profiles[n]["bin"]), "eval"], text=True, timeout=120).strip()
        row = json.loads(out)
        if expected_chk is None:
            expected_chk = row["chk"]
        else:
            assert row["chk"] == expected_chk, f"Checksum mismatch on {n}: {row['chk']} != {expected_chk}"

    for rnd in range(9):
        order = names if rnd % 2 == 0 else list(reversed(names))
        for n in order:
            out = subprocess.check_output([str(profiles[n]["bin"]), "eval"], text=True, timeout=120).strip()
            row = json.loads(out)
            assert row["chk"] == expected_chk
            samples[n].append(row)

    metrics = ["deflate_ms", "json_ms", "toml_ms", "memchr_ms", "base64_ms", "crc32_ms", "dyn_icp_ms", "total_ms"]
    summary = {}
    base_meds = {m: statistics.median([r[m] for r in samples["O3_cgu16"]]) for m in metrics}
    for n in names:
        meds = {m: round(statistics.median([r[m] for r in samples[n]]), 3) for m in metrics}
        iqrs = {m: round(statistics.quantiles([r[m] for r in samples[n]], n=4)[2] - statistics.quantiles([r[m] for r in samples[n]], n=4)[0], 3) for m in metrics}
        speedups = {m: round(base_meds[m] / meds[m], 4) for m in metrics}
        summary[n] = {
            "build_sec": profiles[n]["build_sec"],
            "text_bytes": profiles[n]["text_bytes"],
            "median_ms": meds,
            "iqr_ms": iqrs,
            "speedup_vs_O3_cgu16": speedups,
        }
        print(
            f"  {n:14s}: total={meds['total_ms']:6.2f}ms ({speedups['total_ms']:.3f}x) | "
            f"deflate={meds['deflate_ms']:5.2f} ({speedups['deflate_ms']:.3f}x) | "
            f"json={meds['json_ms']:5.2f} ({speedups['json_ms']:.3f}x) | "
            f"toml={meds['toml_ms']:5.2f} ({speedups['toml_ms']:.3f}x) | "
            f"memchr={meds['memchr_ms']:5.2f} ({speedups['memchr_ms']:.3f}x) | "
            f"b64={meds['base64_ms']:5.2f} ({speedups['base64_ms']:.3f}x) | "
            f"crc={meds['crc32_ms']:5.2f} ({speedups['crc32_ms']:.3f}x) | "
            f"dyn={meds['dyn_icp_ms']:5.2f} ({speedups['dyn_icp_ms']:.3f}x)",
            flush=True,
        )

    doc = {
        "benchmark": "E2-3_T09_real_unrigged_pgo_and_lto_runtime",
        "rustc_version": subprocess.check_output(["rustc", "+1.99.1", "-Vv"], text=True).strip(),
        "llvm_profdata": profdata_bin,
        "pgo_train_sec": round(train_s, 2),
        "pgo_meta": pgo_meta,
        "eval_rounds": 9,
        "checksum_verified_identical": expected_chk,
        "profiles": summary,
    }
    OUT_JSON.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(f"\nSaved -> {OUT_JSON}", flush=True)


if __name__ == "__main__":
    main()
