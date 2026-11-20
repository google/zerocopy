#!/usr/bin/env python3
"""Real `rustc` Surgical-Edit Invalidation Blast Radius & Canonical MIR Early-Cutoff Probe.

Collects ground-truth invalidation and early-cutoff measurements on real `rustc`
(`rustc +1.102.0-nightly` for `-Z dump-mir` and `rustc +1.99.1` for `-O3` LLVM IR and
real `-C incremental` rebuilds) across two production multi-module crates from Cargo's
local registry (`miniz_oxide-0.9.1` and `serde_json-1.0.154`), evaluating baseline `E0`
and five surgical source edits (`E1..E5`) inside `/tmp/vrustc_e2_4`:

  - E1_top_comment_shift    : Insert 6 comment lines near top of file (pure span shift).
  - E2_private_noninline_leaf: Modify a constant inside one private non-generic non-inlined leaf fn.
  - E3_widely_inlined_helper : Modify an expression inside a widely called `#[inline]` helper fn.
  - E4_internal_const        : Change literal value of an internal `const` used by a small subset of fns.
  - E5_append_new_pub_fn     : Append `pub fn __vrustc_probe_added(x: u64) -> u64` at EOF (0 line shifts).

Measures across all 4 compiler stages:
  1. Pre-optimization MIR (`3-2-000.runtime-post-cleanup.after.mir`, i.e. `Runtime(PostCleanup)`):
     raw `.mir` (with `-Z mir-include-spans=true`) vs. span-stripped canonical MIR vs.
     span-stripped + transitive `Const::Unevaluated` dependency cone.
  2. Post-optimization MIR (`3-3-000.runtime-optimized.after.mir`, i.e. `Runtime(Optimized)` / `PreCodegen`
     after `Inline`, `GVN`, `SROA`, `InstSimplify`): raw vs. span-stripped MIR blast radius.
  3. Post-`-O3` LLVM IR (`rustc +1.99.1 --emit=llvm-ir -C opt-level=3 -C debuginfo=0` at `cgu=16` and `cgu=1`):
     function-level invalidation (`llvm_o3_fn_changed`, plus `@alloc_*` panic-Location-erased count).
  4. Real `rustc +1.99.1` `-O3` incremental rebuild wall-clock (`ms`, median of 3 resetting `E0` cache
     before each trial) vs. clean cold `-O3` compile wall-clock (`ms`, median of 3), plus exact CGU
     `.o` and `.pre-lto.bc` reuse vs. re-emission counts inside `-C incremental`.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import time

SCRATCH_ROOT = Path("/tmp/vrustc_e2_4")
CARGO_REGISTRY = Path(
    os.environ.get(
        "CARGO_REGISTRY_SRC",
        str(Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "registry/src/index.crates.io-1949cf8c6b5b557f"),
    )
)
OUT_JSON = Path(os.environ.get("VRUSTC_OUT_JSON", str(Path(__file__).resolve().parent / "e2_4_real_incremental_mir_cutoff.json")))
CXXFILT = Path("/usr/bin/llvm-cxxfilt")

NIGHTLY_TC = "+nightly"  # rustc 1.102.0-nightly
STABLE_TC = "+1.99.1"    # rustc 1.99.1

# Regexes for canonical MIR span-stripping (preserving every bb, local type, statement, rvalue, terminator)
MIR_TRAILING_SPAN_COMMENT_RE = re.compile(
    r"\s*//\s*(?:(?:return place )?in scope \d+|scope \d+|at |mir::|ty::|\+ ).*$"
)
MIR_EMBEDDED_SPAN_LOC_RE = re.compile(r"(@|impl at )([^\s:>}]+):\d+:\d+:\s*\d+:\d+")
MIR_CONST_REF_RE = re.compile(r"\bconst\s+([a-zA-Z_][a-zA-Z0-9_]*(?:::[a-zA-Z0-9_]+)+)\b")

# Regexes for LLVM IR parsing and normalization
LLVM_ATTR_DEF_RE = re.compile(r"^attributes #(\d+) = \{ (.*) \}$")
LLVM_DEFINE_SYM_RE = re.compile(r'@("[^"]+"|[A-Za-z0-9_.$]+)\(')
LLVM_META_TAG_RE = re.compile(r"(?:,\s*)?![a-zA-Z0-9_.]+\s+!\d+")
LLVM_ATTR_REF_RE = re.compile(r"(?<=\s)#(\d+)\b")
LLVM_ALLOC_HASH_RE = re.compile(r"@(alloc_[0-9a-f]{32}|anon\.[0-9a-f]{32}\.\d+)\b")
LLVM_THINLTO_SYM_SUFFIX_RE = re.compile(r"\.llvm\.\d+\b")


def run_cmd(cmd, cwd=SCRATCH_ROOT):
    env = os.environ.copy()
    env["RUSTC_ICE"] = "0"
    res = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(
            f"Command failed (exit {res.returncode}): {' '.join(cmd)}\n"
            f"STDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}"
        )
    return res


def get_rustc_vv(toolchain: str) -> dict:
    raw = run_cmd(["rustc", toolchain, "-vV"]).stdout.strip()
    meta = {"raw": raw}
    for line in raw.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip()] = v.strip()
    return meta


def demangle_symbols(syms: list[str]) -> list[str]:
    if not syms:
        return []
    cleaned = [s.strip('"') for s in syms]
    if not CXXFILT.exists():
        return cleaned
    res = subprocess.run(
        [str(CXXFILT)],
        input="\n".join(cleaned) + "\n",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=True,
    )
    return [ln.strip() for ln in res.stdout.splitlines()]


def strip_mir_spans(text: str) -> str:
    """Strip source-span and scope-location noise while preserving all MIR semantics."""
    out_lines = []
    for line in text.splitlines():
        if line.lstrip().startswith("//"):
            continue
        line = MIR_TRAILING_SPAN_COMMENT_RE.sub("", line)
        line = MIR_EMBEDDED_SPAN_LOC_RE.sub(r"\1\2", line)
        line = line.rstrip()
        if line:
            out_lines.append(line)
    return "\n".join(out_lines)


def mir_item_key(filename: str, suffix: str) -> str:
    """Extract crate-local item key from `<crate>.<item>.<pass_suffix>`."""
    assert filename.endswith("." + suffix), filename
    stem = filename[: -(len(suffix) + 1)]
    # Strip `<crate>.` prefix
    return stem.split(".", 1)[1] if "." in stem else stem


def mir_header_def_path(text: str) -> str | None:
    r"""Extract header item path from `// MIR for \`<path>\` ...` on line 1."""
    first = text.splitlines()[0] if text else ""
    m = re.match(r"^// MIR for `([^`]+)`", first)
    return m.group(1) if m else None


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def parse_mir_phase(mir_dir: Path, suffix: str) -> dict:
    """Return per-item raw hash, canonical span-stripped hash, header path, and const refs."""
    items = {}
    for p in sorted(mir_dir.glob(f"*.{suffix}")):
        key = mir_item_key(p.name, suffix)
        raw_txt = p.read_text(encoding="utf-8")
        canon_txt = strip_mir_spans(raw_txt)
        hdr = mir_header_def_path(raw_txt) or key
        const_refs = sorted(set(MIR_CONST_REF_RE.findall(canon_txt)))
        items[key] = {
            "def_path": hdr,
            "raw_sha256": sha256_str(raw_txt),
            "canon_sha256": sha256_str(canon_txt),
            "const_refs": const_refs,
        }
    return items


def diff_mir_phase(base: dict, curr: dict, compute_const_cone: bool = False) -> dict:
    base_keys = set(base.keys())
    curr_keys = set(curr.keys())
    common = sorted(base_keys & curr_keys)
    added = sorted(curr_keys - base_keys)
    removed = sorted(base_keys - curr_keys)

    raw_changed = [k for k in common if base[k]["raw_sha256"] != curr[k]["raw_sha256"]]
    canon_changed = [k for k in common if base[k]["canon_sha256"] != curr[k]["canon_sha256"]]

    out = {
        "n_baseline": len(base_keys),
        "n_current": len(curr_keys),
        "added_count": len(added),
        "removed_count": len(removed),
        "raw_changed_count": len(raw_changed),
        "span_stripped_changed_count": len(canon_changed),
        "added_items": [curr[k]["def_path"] for k in added[:20]],
        "removed_items": [base[k]["def_path"] for k in removed[:20]],
        "span_stripped_changed_items": [curr[k]["def_path"] for k in canon_changed[:25]],
    }

    if compute_const_cone:
        # Map `def_path` -> item_key in `curr` to propagate `Const::Unevaluated` edits
        changed_set = set(canon_changed)
        def_to_key = {v["def_path"]: k for k, v in curr.items()}
        changed = True
        while changed:
            changed = False
            changed_def_paths = {curr[k]["def_path"] for k in changed_set}
            for k in common:
                if k in changed_set:
                    continue
                if any(cref in changed_def_paths for cref in curr[k]["const_refs"]):
                    changed_set.add(k)
                    changed = True
        cone_sorted = sorted(changed_set)
        out["span_stripped_plus_const_cone_changed_count"] = len(cone_sorted)
        out["span_stripped_plus_const_cone_changed_items"] = [
            curr[k]["def_path"] for k in cone_sorted[:25]
        ]

    return out


def parse_llvm_dir(
    out_dir: Path,
) -> tuple[dict[str, list[str]], dict[str, list[str]], dict[str, list[str]]]:
    """Parse all `.ll` files in `out_dir`, returning exact, alloc-erased, and cgu-hash-erased maps."""
    fns_exact: dict[str, list[str]] = {}
    fns_alloc_erased: dict[str, list[str]] = {}
    fns_cgu_erased: dict[str, list[str]] = {}

    for ll_file in sorted(out_dir.glob("*.ll")):
        lines = ll_file.read_text(encoding="utf-8").splitlines()
        attrs = {}
        for line in lines:
            m = LLVM_ATTR_DEF_RE.match(line)
            if m:
                attrs[m.group(1)] = m.group(2)

        in_fn = False
        cur_sym = None
        cur_lines = []
        for line in lines:
            if not in_fn:
                if line.startswith("define "):
                    m = LLVM_DEFINE_SYM_RE.search(line)
                    if not m:
                        raise RuntimeError(f"Could not parse LLVM define line: {line}")
                    cur_sym = m.group(1)
                    in_fn = True
                    cur_lines = [line]
            else:
                cur_lines.append(line)
                if line == "}":
                    in_fn = False
                    norm = []
                    for ln in cur_lines:
                        ln2 = LLVM_META_TAG_RE.sub("", ln)
                        ln2 = LLVM_ATTR_REF_RE.sub(
                            lambda am: f"attr({attrs.get(am.group(1), am.group(1))})", ln2
                        )
                        norm.append(ln2.rstrip())
                    joined = "\n".join(norm)
                    body_exact = sha256_str(joined)
                    erased_txt = LLVM_ALLOC_HASH_RE.sub("@ALLOC_CONST", joined)
                    body_erased = sha256_str(erased_txt)
                    cgu_erased_txt = LLVM_THINLTO_SYM_SUFFIX_RE.sub(".llvm.HASH", erased_txt)
                    assert cur_sym is not None
                    norm_sym = LLVM_THINLTO_SYM_SUFFIX_RE.sub(".llvm.HASH", cur_sym)
                    fns_exact.setdefault(cur_sym, []).append(body_exact)
                    fns_alloc_erased.setdefault(cur_sym, []).append(body_erased)
                    fns_cgu_erased.setdefault(norm_sym, []).append(sha256_str(cgu_erased_txt))

    for d in (fns_exact, fns_alloc_erased, fns_cgu_erased):
        for k in d:
            d[k].sort()
    return fns_exact, fns_alloc_erased, fns_cgu_erased


def diff_llvm(
    base_tuple: tuple[dict[str, list[str]], dict[str, list[str]], dict[str, list[str]]],
    curr_tuple: tuple[dict[str, list[str]], dict[str, list[str]], dict[str, list[str]]],
) -> dict:
    base_ex, base_er, base_cgu = base_tuple
    curr_ex, curr_er, curr_cgu = curr_tuple
    b_syms = set(base_ex.keys())
    c_syms = set(curr_ex.keys())
    common = sorted(b_syms & c_syms)
    added = sorted(c_syms - b_syms)
    removed = sorted(b_syms - c_syms)

    changed_ex = [s for s in common if base_ex[s] != curr_ex[s]]
    changed_er = [s for s in common if base_er[s] != curr_er[s]]

    common_cgu = sorted(set(base_cgu.keys()) & set(curr_cgu.keys()))
    changed_cgu = [s for s in common_cgu if base_cgu[s] != curr_cgu[s]]
    added_cgu = sorted(set(curr_cgu.keys()) - set(base_cgu.keys()))
    removed_cgu = sorted(set(base_cgu.keys()) - set(curr_cgu.keys()))

    return {
        "n_unique_fns_baseline": len(b_syms),
        "n_unique_fns_current": len(c_syms),
        "n_total_defs_baseline": sum(len(v) for v in base_ex.values()),
        "n_total_defs_current": sum(len(v) for v in curr_ex.values()),
        "llvm_o3_fn_changed": len(changed_ex),
        "llvm_o3_alloc_location_erased_changed": len(changed_er),
        "llvm_o3_alloc_and_cgu_hash_erased_changed": len(changed_cgu),
        "llvm_o3_fn_added": len(added),
        "llvm_o3_fn_removed": len(removed),
        "llvm_o3_cgu_hash_erased_added": len(added_cgu),
        "llvm_o3_cgu_hash_erased_removed": len(removed_cgu),
        "changed_demangled": demangle_symbols(changed_ex[:25]),
        "alloc_erased_changed_demangled": demangle_symbols(changed_er[:25]),
        "added_demangled": demangle_symbols(added[:20]),
        "removed_demangled": demangle_symbols(removed[:20]),
    }


def build_leaf_dependencies(deps_dir: Path, toolchain: str):
    """Precompile leaf `.rlib` dependencies offline into `deps_dir`."""
    deps_dir.mkdir(parents=True, exist_ok=True)
    sc_out = SCRATCH_ROOT / "serde_core_out"
    sc_out.mkdir(parents=True, exist_ok=True)
    (sc_out / "private.rs").write_text(
        "#[doc(hidden)]\n"
        "pub mod __private229 {\n"
        "    #[doc(hidden)]\n"
        "    pub use crate::private::*;\n"
        "}\n",
        encoding="utf-8",
    )

    # 1. adler2-2.0.1 (for miniz_oxide)
    run_cmd([
        "rustc", toolchain, "--edition=2021", "--crate-name", "adler2", "--crate-type=lib",
        "-C", "opt-level=3", "--cap-lints", "allow",
        str(CARGO_REGISTRY / "adler2-2.0.1/src/lib.rs"),
        "-o", str(deps_dir / "libadler2.rlib"),
    ])

    # 2. itoa-1.0.18, memchr-2.8.3, zmij-1.0.23, serde_core-1.0.229 (for serde_json)
    run_cmd([
        "rustc", toolchain, "--edition=2021", "--crate-name", "itoa", "--crate-type=lib",
        "-C", "opt-level=3", "--cap-lints", "allow",
        str(CARGO_REGISTRY / "itoa-1.0.18/src/lib.rs"),
        "-o", str(deps_dir / "libitoa.rlib"),
    ])
    run_cmd([
        "rustc", toolchain, "--edition=2021", "--crate-name", "memchr", "--crate-type=lib",
        "-C", "opt-level=3", "--cfg", 'feature="alloc"', "--cfg", 'feature="std"',
        "--cap-lints", "allow",
        str(CARGO_REGISTRY / "memchr-2.8.3/src/lib.rs"),
        "-o", str(deps_dir / "libmemchr.rlib"),
    ])
    run_cmd([
        "rustc", toolchain, "--edition=2021", "--crate-name", "zmij", "--crate-type=lib",
        "-C", "opt-level=3", "--cap-lints", "allow",
        str(CARGO_REGISTRY / "zmij-1.0.23/src/lib.rs"),
        "-o", str(deps_dir / "libzmij.rlib"),
    ])

    env = os.environ.copy()
    env["RUSTC_ICE"] = "0"
    env["OUT_DIR"] = str(sc_out)
    res = subprocess.run(
        [
            "rustc", toolchain, "--edition=2021", "--crate-name", "serde_core",
            "--crate-type=lib", "-C", "opt-level=3", "--cfg", 'feature="std"',
            "--cap-lints", "allow",
            str(CARGO_REGISTRY / "serde_core-1.0.229/src/lib.rs"),
            "-o", str(deps_dir / "libserde_core.rlib"),
        ],
        cwd=str(SCRATCH_ROOT),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(f"Failed building serde_core: {res.stderr}")


def replace_exact_once(text: str, old: str, new: str) -> str:
    cnt = text.count(old)
    if cnt != 1:
        raise RuntimeError(f"Expected exact single match (got {cnt}) for:\n{old}")
    return text.replace(old, new, 1)


def setup_crates(deps_nightly: Path, deps_stable: Path) -> list[dict]:
    """Copy both crates into `/tmp/vrustc_e2_4/crates/` and define exact E1..E5 transforms."""
    crates_root = SCRATCH_ROOT / "crates"
    if crates_root.exists():
        shutil.rmtree(crates_root)
    crates_root.mkdir(parents=True)

    # 1. miniz_oxide-0.9.1
    mz_dir = crates_root / "miniz_oxide"
    shutil.copytree(CARGO_REGISTRY / "miniz_oxide-0.9.1", mz_dir)
    # Include a small fixed concrete exerciser in E0..E5 so all entrypoints stay live
    mz_lib = mz_dir / "src/lib.rs"
    mz_lib.write_text(
        mz_lib.read_text(encoding="utf-8")
        + "\n#[doc(hidden)]\n"
        "pub mod __vrustc_exerciser {\n"
        "    use alloc::vec::Vec;\n"
        "    pub fn roundtrip_zlib(data: &[u8]) -> Result<Vec<u8>, crate::inflate::DecompressError> {\n"
        "        let compressed = crate::deflate::compress_to_vec_zlib(data, 6);\n"
        "        crate::inflate::decompress_to_vec_zlib(&compressed)\n"
        "    }\n"
        "}\n",
        encoding="utf-8",
    )
    mz_target = mz_dir / "src/inflate/core.rs"
    mz_orig = mz_target.read_text(encoding="utf-8")

    mz_comments = (
        "\n".join(f"// vrustc E1 span-shift probe comment line {i}" for i in range(1, 7)) + "\n"
    )
    mz_edits = {
        "E0_baseline": lambda s: s,
        "E1_top_comment_shift": lambda s: replace_exact_once(
            s,
            "pub const TINFL_LZ_DICT_SIZE: usize = 32_768;",
            mz_comments + "pub const TINFL_LZ_DICT_SIZE: usize = 32_768;",
        ),
        "E2_private_noninline_leaf": lambda s: replace_exact_once(
            s,
            "        if bt != HUFFLEN_TABLE {\n            table.tree.fill(0);\n        }",
            "        if bt != HUFFLEN_TABLE {\n            table.tree.fill(1);\n        }",
        ),
        "E3_widely_inlined_helper": lambda s: replace_exact_once(
            s,
            "    const fn fast_lookup(&self, bit_buf: BitBuffer) -> i16 {\n"
            "        self.look_up[(bit_buf & (FAST_LOOKUP_SIZE - 1) as BitBuffer) as usize]\n"
            "    }",
            "    const fn fast_lookup(&self, bit_buf: BitBuffer) -> i16 {\n"
            "        self.look_up[((bit_buf ^ 1) & (FAST_LOOKUP_SIZE - 1) as BitBuffer) as usize]\n"
            "    }",
        ),
        "E4_internal_const": lambda s: replace_exact_once(
            s,
            "const BASE_EXTRA_MASK: usize = 32 - 1;",
            "const BASE_EXTRA_MASK: usize = 16 - 1;",
        ),
        "E5_append_new_pub_fn": lambda s: (
            s
            + "\npub fn __vrustc_probe_added(x: u64) -> u64 {\n"
            "    x.wrapping_add(1)\n"
            "}\n"
        ),
    }

    # 2. serde_json-1.0.154
    sj_dir = crates_root / "serde_json"
    shutil.copytree(CARGO_REGISTRY / "serde_json-1.0.154", sj_dir)
    sj_lib = sj_dir / "src/lib.rs"
    sj_lib.write_text(
        sj_lib.read_text(encoding="utf-8")
        + "\n#[doc(hidden)]\n"
        "pub mod __vrustc_exerciser {\n"
        "    use alloc::vec::Vec;\n"
        "    use crate::Value;\n"
        "    pub fn exercise_all(input: &str, bytes: &[u8]) -> Result<Vec<u8>, crate::Error> {\n"
        "        let mut v: Value = crate::from_str(input)?;     \n"
        "        let v2: Value = crate::from_slice(bytes)?;      \n"
        "        if let Value::Object(ref mut m) = v {\n"
        "            m.insert(\"other\".into(), v2);\n"
        "        }\n"
        "        let mut out = crate::to_vec(&v)?;\n"
        "        let pretty = crate::to_vec_pretty(&v)?;\n"
        "        out.extend_from_slice(&pretty);\n"
        "        Ok(out)\n"
        "    }\n"
        "}\n",
        encoding="utf-8",
    )
    sj_target = sj_dir / "src/ser.rs"
    sj_orig = sj_target.read_text(encoding="utf-8")

    sj_comments = (
        "\n".join(f"// vrustc E1 span-shift probe comment line {i}" for i in range(1, 7)) + "\n"
    )
    sj_edits = {
        "E0_baseline": lambda s: s,
        "E1_top_comment_shift": lambda s: replace_exact_once(
            s,
            "/// A structure for serializing Rust values into JSON.",
            sj_comments + "/// A structure for serializing Rust values into JSON.",
        ),
        "E2_private_noninline_leaf": lambda s: replace_exact_once(
            s,
            "fn key_must_be_a_string() -> Error {\n"
            "    Error::syntax(ErrorCode::KeyMustBeAString, 0, 0)\n"
            "}",
            "fn key_must_be_a_string() -> Error {\n"
            "    Error::syntax(ErrorCode::KeyMustBeAString, 0, 1)\n"
            "}",
        ),
        "E3_widely_inlined_helper": lambda s: replace_exact_once(
            s,
            "    #[inline]\n"
            "    fn serialize_str(self, value: &str) -> Result<()> {\n"
            "        format_escaped_str(&mut self.writer, &mut self.formatter, value).map_err(Error::io)\n"
            "    }",
            "    #[inline]\n"
            "    fn serialize_str(self, value: &str) -> Result<()> {\n"
            "        format_escaped_str(\n"
            "            &mut self.writer,\n"
            "            &mut self.formatter,\n"
            "            if value.len() == 0x7fff_ffff { \"\" } else { value },\n"
            "        )\n"
            "        .map_err(Error::io)\n"
            "    }",
        ),
        "E4_internal_const": lambda s: replace_exact_once(
            s,
            "const BB: u8 = b'b'; // \\x08",
            "const BB: u8 = b'x'; // \\x08",
        ),
        "E5_append_new_pub_fn": lambda s: (
            s
            + "\npub fn __vrustc_probe_added(x: u64) -> u64 {\n"
            "    x.wrapping_add(1)\n"
            "}\n"
        ),
    }

    return [
        {
            "name": "miniz_oxide",
            "version": "0.9.1",
            "registry_dir": str(CARGO_REGISTRY / "miniz_oxide-0.9.1"),
            "edited_file_rel": "src/inflate/core.rs",
            "edit_descriptions": {
                "E1_top_comment_shift": "Insert 6 comment lines above `pub const TINFL_LZ_DICT_SIZE` at top of `src/inflate/core.rs`.",
                "E2_private_noninline_leaf": "Change `table.tree.fill(0)` -> `table.tree.fill(1)` in private non-generic non-inlined `inflate::core::init_tree`.",
                "E3_widely_inlined_helper": "Change `bit_buf & ...` -> `(bit_buf ^ 1) & ...` in `#[inline] const fn HuffmanTable::fast_lookup`.",
                "E4_internal_const": "Change `const BASE_EXTRA_MASK: usize = 32 - 1` -> `16 - 1` (referenced as `Const::Unevaluated` in `decompress_fast` and `decompress_with_limit`).",
                "E5_append_new_pub_fn": "Append `pub fn __vrustc_probe_added(x: u64) -> u64 { x.wrapping_add(1) }` at EOF of `src/inflate/core.rs`.",
            },
            "crate_dir": mz_dir,
            "entry_rs": mz_dir / "src/lib.rs",
            "target_file": mz_target,
            "orig_text": mz_orig,
            "edits": mz_edits,
            "flags_for": lambda deps: [
                "--edition=2021",
                "--crate-name", "miniz_oxide",
                "--crate-type=lib",
                "--cfg", 'feature="with-alloc"',
                "--cap-lints", "allow",
                "-L", f"dependency={deps}",
                "--extern", f"adler2={deps / 'libadler2.rlib'}",
            ],
        },
        {
            "name": "serde_json",
            "version": "1.0.154",
            "registry_dir": str(CARGO_REGISTRY / "serde_json-1.0.154"),
            "edited_file_rel": "src/ser.rs",
            "edit_descriptions": {
                "E1_top_comment_shift": "Insert 6 comment lines above `pub struct Serializer` at line 15 of `src/ser.rs` (199 fns below it).",
                "E2_private_noninline_leaf": "Change `(0, 0)` -> `(0, 1)` in private non-generic non-inlined `ser::key_must_be_a_string`.",
                "E3_widely_inlined_helper": "Modify slice expression in `#[inline] <&mut Serializer<W, F> as serde::Serializer>::serialize_str`.",
                "E4_internal_const": "Change `const BB: u8 = b'b'` -> `b'x'` in `src/ser.rs` (referenced in `static ESCAPE` and `SwitchInt` pattern in `format_escaped_str_contents`).",
                "E5_append_new_pub_fn": "Append `pub fn __vrustc_probe_added(x: u64) -> u64 { x.wrapping_add(1) }` at EOF of `src/ser.rs`.",
            },
            "crate_dir": sj_dir,
            "entry_rs": sj_dir / "src/lib.rs",
            "target_file": sj_target,
            "orig_text": sj_orig,
            "edits": sj_edits,
            "flags_for": lambda deps: [
                "--edition=2021",
                "--crate-name", "serde_json",
                "--crate-type=lib",
                "--cfg", 'feature="default"',
                "--cfg", 'feature="std"',
                "--cfg", 'fast_arithmetic="64"',
                "--cap-lints", "allow",
                "-L", f"dependency={deps}",
                "--extern", f"itoa={deps / 'libitoa.rlib'}",
                "--extern", f"memchr={deps / 'libmemchr.rlib'}",
                "--extern", f"serde_core={deps / 'libserde_core.rlib'}",
                "--extern", f"zmij={deps / 'libzmij.rlib'}",
            ],
        },
    ]


def newest_session_dir(incr_dir: Path) -> Path:
    """Return the newest `s-*` session directory inside an incremental cache directory."""
    sessions = [p for p in incr_dir.glob("*/*") if p.is_dir() and p.name.startswith("s-")]
    if not sessions:
        raise RuntimeError(f"No incremental session dir found under {incr_dir}")
    # `s-<base36_unix_micros>-<random>-<hash>`: the base36 timestamp segment is strictly monotonic!
    return max(sessions, key=lambda p: p.name.split("-")[1])


def snapshot_session_hashes(session_dir: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Return `({o_name: sha256}, {bc_name: sha256})` for a single session dir."""
    o_hashes = {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(session_dir.glob("*.o"))
    }
    bc_hashes = {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(session_dir.glob("*.pre-lto.bc"))
    }
    return o_hashes, bc_hashes


def pin_prev_o_inodes(incr_live: Path, pin_dir: Path) -> dict[str, tuple[int, str]]:
    """Hardlink `E0`'s `.o` files in `incr_live` into `pin_dir` before running `rustc`.

    Pinning each `.o` inode in `pin_dir` prevents `tmpfs` from recycling inode numbers if
    `rustc`'s background session GC deletes `s_prev` at the end of the incremental build,
    and avoids relying on `st_nlink >= 2` (which drops back to `1` once `s_prev` is GC'd).
    We also assert after `rustc` exits that every pinned `.o` retained its exact SHA-256.
    """
    if pin_dir.exists():
        shutil.rmtree(pin_dir)
    pin_dir.mkdir(parents=True)
    s_prev = newest_session_dir(incr_live)
    pinned = {}
    for p in sorted(s_prev.glob("*.o")):
        os.link(p, pin_dir / p.name)
        pinned[p.name] = (p.stat().st_ino, hashlib.sha256(p.read_bytes()).hexdigest())
    return pinned


def inspect_post_rebuild_session(
    incr_live: Path,
    pin_dir: Path,
    pinned_prev_o: dict[str, tuple[int, str]],
    base_o_hashes: dict[str, str],
    base_bc_hashes: dict[str, str],
) -> dict:
    """Inspect the newly created session in `incr_live` after an `E0 -> Ei` rebuild."""
    for name, (_, h0) in pinned_prev_o.items():
        h_now = hashlib.sha256((pin_dir / name).read_bytes()).hexdigest()
        if h_now != h0:
            raise RuntimeError(f"Pinned .o file {name} was unexpectedly mutated in place!")

    s_new = newest_session_dir(incr_live)
    o_files = sorted(s_new.glob("*.o"))
    bc_files = sorted(s_new.glob("*.pre-lto.bc"))

    o_reused = sum(
        1
        for p in o_files
        if p.name in pinned_prev_o and p.stat().st_ino == pinned_prev_o[p.name][0]
    )
    o_reemitted = len(o_files) - o_reused
    o_bytes_changed = sum(
        1
        for p in o_files
        if base_o_hashes.get(p.name) != hashlib.sha256(p.read_bytes()).hexdigest()
    )
    bc_bytes_changed = sum(
        1
        for p in bc_files
        if base_bc_hashes.get(p.name) != hashlib.sha256(p.read_bytes()).hexdigest()
    )
    return {
        "rcgu_o_total": len(o_files),
        "rcgu_o_reused": o_reused,
        "rcgu_o_reemitted": o_reemitted,
        "rcgu_o_bytes_changed": o_bytes_changed,
        "pre_lto_bc_total": len(bc_files),
        "pre_lto_bc_unchanged_bytes": len(bc_files) - bc_bytes_changed,
        "pre_lto_bc_changed_bytes": bc_bytes_changed,
    }


def measure_clean_and_incremental(spec: dict, deps_stable: Path) -> dict:
    """Measure clean -O3 wall-clock (median of 3) and E0->Ei incremental rebuilds + CGU reuse."""
    base_flags = spec["flags_for"](deps_stable)
    entry_rs = str(spec["entry_rs"])
    target_file: Path = spec["target_file"]
    orig_text: str = spec["orig_text"]

    out_clean = SCRATCH_ROOT / "out_clean"
    out_incr = SCRATCH_ROOT / "out_incr"
    incr_live = SCRATCH_ROOT / "incr_cache"
    incr_snap = SCRATCH_ROOT / "incr_e0_snapshot"
    pin_dir = SCRATCH_ROOT / "incr_pin_inodes"

    # 1. Measure clean -O3 compile on E0 (3 trials after 1 warm-up)
    target_file.write_text(orig_text, encoding="utf-8")
    e0_clean_samples = []
    for trial in range(4):
        if out_clean.exists():
            shutil.rmtree(out_clean)
        out_clean.mkdir(parents=True)
        t0 = time.perf_counter()
        run_cmd([
            "rustc", STABLE_TC, *base_flags,
            "-C", "opt-level=3", "-C", "codegen-units=16", "-C", "debuginfo=0",
            entry_rs, f"--out-dir={out_clean}",
        ])
        dt_ms = (time.perf_counter() - t0) * 1000.0
        if trial > 0:
            e0_clean_samples.append(round(dt_ms, 2))

    # 2. Populate baseline E0 incremental cache in `incr_live`, then copy (non-hardlinked!) to `incr_snap`
    for d in (incr_live, incr_snap, out_incr):
        if d.exists():
            shutil.rmtree(d)
    incr_live.mkdir(parents=True)
    out_incr.mkdir(parents=True)

    t0 = time.perf_counter()
    run_cmd([
        "rustc", STABLE_TC, *base_flags,
        "-C", "opt-level=3", "-C", "codegen-units=16", "-C", "debuginfo=0",
        "-C", f"incremental={incr_live}",
        entry_rs, f"--out-dir={out_incr}",
    ])
    e0_incr_seed_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    shutil.copytree(incr_live, incr_snap)
    base_o_hashes, base_bc_hashes = snapshot_session_hashes(newest_session_dir(incr_snap))

    per_edit_timing = {
        "E0_baseline": {
            "clean_o3_samples_ms": e0_clean_samples,
            "clean_o3_median_ms": round(statistics.median(e0_clean_samples), 2),
            "incr_seed_build_ms": e0_incr_seed_ms,
            "rcgu_o_total": len(base_o_hashes),
            "pre_lto_bc_total": len(base_bc_hashes),
        }
    }

    # 3. For each edit E1..E5, measure 3 clean trials AND 3 fresh E0->Ei incremental trials
    for edit_name, transform in spec["edits"].items():
        if edit_name == "E0_baseline":
            continue
        edited_text = transform(orig_text)
        target_file.write_text(edited_text, encoding="utf-8")

        clean_samples = []
        for _ in range(3):
            if out_clean.exists():
                shutil.rmtree(out_clean)
            out_clean.mkdir(parents=True)
            t0 = time.perf_counter()
            run_cmd([
                "rustc", STABLE_TC, *base_flags,
                "-C", "opt-level=3", "-C", "codegen-units=16", "-C", "debuginfo=0",
                entry_rs, f"--out-dir={out_clean}",
            ])
            clean_samples.append(round((time.perf_counter() - t0) * 1000.0, 2))

        incr_samples = []
        reuse_stats = {}
        for _ in range(3):
            # Reset `incr_live` cleanly via full independent copy from `incr_snap` (`E0`)
            if incr_live.exists():
                shutil.rmtree(incr_live)
            shutil.copytree(incr_snap, incr_live)
            pinned_prev_o = pin_prev_o_inodes(incr_live, pin_dir)
            if out_incr.exists():
                shutil.rmtree(out_incr)
            out_incr.mkdir(parents=True)

            t0 = time.perf_counter()
            run_cmd([
                "rustc", STABLE_TC, *base_flags,
                "-C", "opt-level=3", "-C", "codegen-units=16", "-C", "debuginfo=0",
                "-C", f"incremental={incr_live}",
                entry_rs, f"--out-dir={out_incr}",
            ])
            incr_samples.append(round((time.perf_counter() - t0) * 1000.0, 2))
            reuse_stats = inspect_post_rebuild_session(
                incr_live, pin_dir, pinned_prev_o, base_o_hashes, base_bc_hashes
            )

        clean_med = round(statistics.median(clean_samples), 2)
        incr_med = round(statistics.median(incr_samples), 2)
        per_edit_timing[edit_name] = {
            "clean_o3_samples_ms": clean_samples,
            "clean_o3_median_ms": clean_med,
            "incr_o3_samples_ms": incr_samples,
            "incr_o3_median_ms": incr_med,
            "incr_speedup_vs_clean": round(clean_med / incr_med, 3) if incr_med > 0 else None,
            "incr_fraction_of_clean": round(incr_med / clean_med, 4) if clean_med > 0 else None,
            **reuse_stats,
        }

    # Restore original source file
    target_file.write_text(orig_text, encoding="utf-8")
    for p in (out_clean, out_incr, incr_live, incr_snap, pin_dir):
        if p.exists():
            shutil.rmtree(p)
    return per_edit_timing


def run_crate_probe(spec: dict, deps_nightly: Path, deps_stable: Path) -> dict:
    name = spec["name"]
    print(f"\n=== Running surgical-edit probe on {name}-{spec['version']} ({spec['edited_file_rel']}) ===", flush=True)
    nightly_flags = spec["flags_for"](deps_nightly)
    stable_flags = spec["flags_for"](deps_stable)
    entry_rs = str(spec["entry_rs"])
    target_file: Path = spec["target_file"]
    orig_text: str = spec["orig_text"]

    POSTCLEANUP_SUFFIX = "3-2-000.runtime-post-cleanup.after.mir"
    PRECODEGEN_SUFFIX = "3-3-000.runtime-optimized.after.mir"

    mir_tmp = SCRATCH_ROOT / "mir_dump_tmp"
    out_tmp = SCRATCH_ROOT / "out_tmp"
    ll_cgu1_tmp = SCRATCH_ROOT / "ll_cgu1_tmp"
    ll_cgu16_tmp = SCRATCH_ROOT / "ll_cgu16_tmp"

    base_postcleanup = None
    base_precodegen = None
    base_ll_cgu1 = None
    base_ll_cgu16 = None

    edits_report = {}

    for edit_name, transform in spec["edits"].items():
        print(f"  -> Dumping MIR & -O3 LLVM IR for {edit_name}...", flush=True)
        target_file.write_text(transform(orig_text), encoding="utf-8")

        for d in (mir_tmp, out_tmp, ll_cgu1_tmp, ll_cgu16_tmp):
            if d.exists():
                shutil.rmtree(d)
            d.mkdir(parents=True)

        # 1 & 2. Dump Runtime(PostCleanup) and Runtime(Optimized)/PreCodegen MIR with full spans
        run_cmd([
            "rustc", NIGHTLY_TC, *nightly_flags,
            "-C", "opt-level=3",
            "-Z", "mir-include-spans=true",
            "-Z", "dump-mir=runtime-post-cleanup | runtime-optimized",
            "-Z", f"dump-mir-dir={mir_tmp}",
            entry_rs, f"--out-dir={out_tmp}",
        ])
        pc_map = parse_mir_phase(mir_tmp, POSTCLEANUP_SUFFIX)
        opt_map = parse_mir_phase(mir_tmp, PRECODEGEN_SUFFIX)

        # 3a. Emit -O3 LLVM IR with codegen-units=1
        run_cmd([
            "rustc", STABLE_TC, *stable_flags,
            "-C", "opt-level=3", "-C", "codegen-units=1", "-C", "debuginfo=0",
            "--emit=llvm-ir",
            entry_rs, f"--out-dir={ll_cgu1_tmp}",
        ])
        ll1_tuple = parse_llvm_dir(ll_cgu1_tmp)

        # 3b. Emit -O3 LLVM IR with codegen-units=16
        run_cmd([
            "rustc", STABLE_TC, *stable_flags,
            "-C", "opt-level=3", "-C", "codegen-units=16", "-C", "debuginfo=0",
            "--emit=llvm-ir",
            entry_rs, f"--out-dir={ll_cgu16_tmp}",
        ])
        ll16_tuple = parse_llvm_dir(ll_cgu16_tmp)

        if edit_name == "E0_baseline":
            base_postcleanup = pc_map
            base_precodegen = opt_map
            base_ll_cgu1 = ll1_tuple
            base_ll_cgu16 = ll16_tuple
            edits_report[edit_name] = {
                "n_postcleanup": len(pc_map),
                "n_precodegen": len(opt_map),
                "n_llvm_o3_cgu1_unique_fns": len(ll1_tuple[0]),
                "n_llvm_o3_cgu1_total_defs": sum(len(v) for v in ll1_tuple[0].values()),
                "n_llvm_o3_cgu16_unique_fns": len(ll16_tuple[0]),
                "n_llvm_o3_cgu16_total_defs": sum(len(v) for v in ll16_tuple[0].values()),
            }
        else:
            assert base_postcleanup is not None
            assert base_precodegen is not None
            assert base_ll_cgu1 is not None
            assert base_ll_cgu16 is not None
            edits_report[edit_name] = {
                "description": spec["edit_descriptions"][edit_name],
                "postcleanup_mir": diff_mir_phase(
                    base_postcleanup, pc_map, compute_const_cone=True
                ),
                "precodegen_mir": diff_mir_phase(
                    base_precodegen, opt_map, compute_const_cone=False
                ),
                "llvm_o3_cgu1": diff_llvm(base_ll_cgu1, ll1_tuple),
                "llvm_o3_cgu16": diff_llvm(base_ll_cgu16, ll16_tuple),
            }

    # Cleanup dump dirs before timing runs
    target_file.write_text(orig_text, encoding="utf-8")
    for d in (mir_tmp, out_tmp, ll_cgu1_tmp, ll_cgu16_tmp):
        if d.exists():
            shutil.rmtree(d)

    # 4. Clean vs Incremental -O3 timing & .rcgu.o reuse
    print(f"  -> Measuring clean vs incremental -O3 rebuild timings & CGU reuse on {name}...", flush=True)
    timings = measure_clean_and_incremental(spec, deps_stable)
    for edit_name, t_info in timings.items():
        edits_report[edit_name]["rustc_1_99_1_incremental_o3"] = t_info

    return {
        "crate": name,
        "version": spec["version"],
        "registry_source": spec["registry_dir"],
        "central_edited_file": spec["edited_file_rel"],
        "edited_file_baseline_lines": len(orig_text.splitlines()),
        "mir_pass_names": {
            "pre_optimization": POSTCLEANUP_SUFFIX,
            "post_optimization": PRECODEGEN_SUFFIX,
        },
        "edits": edits_report,
    }


def main():
    if SCRATCH_ROOT.exists():
        shutil.rmtree(SCRATCH_ROOT)
    SCRATCH_ROOT.mkdir(parents=True, exist_ok=True)

    stable_vv = get_rustc_vv(STABLE_TC)
    nightly_vv = get_rustc_vv(NIGHTLY_TC)
    print(f"Stable : {stable_vv.get('release')} ({stable_vv.get('commit-hash')})", flush=True)
    print(f"Nightly: {nightly_vv.get('release')} ({nightly_vv.get('commit-hash')})", flush=True)

    deps_nightly = SCRATCH_ROOT / "deps_nightly"
    deps_stable = SCRATCH_ROOT / "deps_stable"
    print("Building leaf dependencies offline...", flush=True)
    build_leaf_dependencies(deps_nightly, NIGHTLY_TC)
    build_leaf_dependencies(deps_stable, STABLE_TC)

    specs = setup_crates(deps_nightly, deps_stable)
    crate_results = {}
    for spec in specs:
        crate_results[spec["name"]] = run_crate_probe(spec, deps_nightly, deps_stable)

    result = {
        "title": "Real rustc Surgical-Edit Invalidation Blast Radius & Canonical MIR Early-Cutoff Measurement",
        "toolchains": {
            "rustc_stable_1_99_1": stable_vv,
            "rustc_nightly_1_102_0": nightly_vv,
        },
        "methodology": {
            "scratch_dir": str(SCRATCH_ROOT),
            "mir_dump_flags": [
                "-C opt-level=3",
                "-Z mir-include-spans=true",
                "-Z dump-mir=runtime-post-cleanup | runtime-optimized",
            ],
            "mir_canonicalization": (
                "Strips full-line `//` comments, trailing `// [return place ]in scope ...`, "
                "`// scope ... at ...`, `// mir::...`, `// + ...` comments, and embedded "
                "`{closure@file:l1:c1: l2:c2}` / `<impl at file:l1:c1: l2:c2>` span coordinates "
                "while preserving 100% of basic blocks, local types, statements, rvalues, constants, "
                "and terminators. Also computes transitive `Const::Unevaluated` dependency cone on PostCleanup MIR."
            ),
            "llvm_ir_flags": [
                "-C opt-level=3",
                "-C debuginfo=0",
                "--emit=llvm-ir",
                "tested at both -C codegen-units=1 and -C codegen-units=16",
            ],
            "incremental_timing_protocol": (
                "Median of 3 clean cold `-O3 -C codegen-units=16` builds vs. median of 3 incremental "
                "`E0 -> Ei` rebuilds (`-C incremental=...`), resetting the incremental cache via a full "
                "independent directory copy (`shutil.copytree`) of `E0` before every single trial, "
                "pinning `E0`'s `.o` inodes in a side directory (`os.link`, verified immutable by SHA-256) "
                "so `rustc` session GC / `tmpfs` inode reuse never distort `.o` hardlink-reuse counts, "
                "and comparing both `.o` and `.pre-lto.bc` SHA-256 digests against `E0`."
            ),
        },
        "crates": crate_results,
    }

    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"\nWrote structured JSON to {OUT_JSON}", flush=True)


if __name__ == "__main__":
    main()
