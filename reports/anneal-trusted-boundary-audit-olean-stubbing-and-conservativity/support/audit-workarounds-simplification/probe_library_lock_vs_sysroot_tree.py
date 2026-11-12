#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical probe for Topic 9 Question 3:
Analyze the 5,342-line `trusted/audit/library-lock.json` (`186,931` bytes)
against recursive sysroot tree authentication (`lean/lib/lean/{Init,Std}/**`
and `lean/src/lean/{Init,Std}/**`) + `.olean` `ModuleData.imports` header
discovery in Lean 4.34.1."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HOME = Path.home()
TOOLCHAIN_DIR = HOME / ".elan/toolchains/leanprover--lean4---v4.34.1"
LEAN = str(TOOLCHAIN_DIR / "bin/lean")
SCRATCH_DIR = (
    HOME
    / "<scratch-root>"
    / "scratch/ref-pass-9-audit-simplification"
)
LIB_LOCK_PATH = SCRATCH_DIR / "inspected/mvp_library-lock.json"

PARTS = ["olean", "olean.server", "olean.private", "ilean", "ir"]


def sha256_file(path: Path) -> str:
  h = hashlib.sha256()
  with path.open("rb") as f:
    while chunk := f.read(65536):
      h.update(chunk)
  return h.hexdigest()


def stage_tree_digest(root: Path) -> tuple[str, int, int]:
  """Exact Python equivalent of `stage_tree_digest` in `setup.rs`."""
  entries = []
  total_bytes = 0
  for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
    dirnames.sort()
    filenames.sort()
    for fn in filenames:
      full = Path(dirpath) / fn
      rel = full.relative_to(root).as_posix()
      st = full.lstat()
      total_bytes += st.st_size
      entries.append((rel, full))
  entries.sort(key=lambda x: x[0])
  outer = hashlib.sha256()
  for rel, full in entries:
    file_digest = hashlib.sha256(full.read_bytes()).digest()
    outer.update(rel.encode("utf-8"))
    outer.update(b"\x00")
    outer.update(file_digest)
  return outer.hexdigest(), len(entries), total_bytes


def stat_tree_fingerprints(root: Path) -> int:
  """Simulate warm `FileFingerprint` `(dev, ino, mode, len, mtime, mtime_nsec)`
  verification across all files in `root`."""
  count = 0
  for dirpath, _, filenames in os.walk(root, followlinks=False):
    for fn in filenames:
      st = (Path(dirpath) / fn).lstat()
      _ = (st.st_dev, st.st_ino, st.st_mode, st.st_size, st.st_mtime_ns)
      count += 1
  return count


def main():
  raw_text = LIB_LOCK_PATH.read_text()
  line_count = len(raw_text.splitlines())
  byte_count = len(raw_text.encode("utf-8"))
  lib_lock = json.loads(raw_text)

  modules = lib_lock["modules"]
  graph = lib_lock["graph"]

  num_modules = len(modules)
  num_sha256_entries = sum(1 + len(m["parts"]) for m in modules.values())
  num_graph_edges = sum(len(edges) for edges in graph.values())

  # Verify that 100% of the SHA-256 hashes in library-lock.json match the
  # files inside the Lean 4.34.1 sysroot
  t0 = time.perf_counter()
  matched_hashes = 0
  for mod_name, m in modules.items():
    rel = Path(*mod_name.split("."))
    src_path = TOOLCHAIN_DIR / "src/lean" / rel.with_suffix(".lean")
    assert sha256_file(src_path) == m["sourceSha256"], f"Mismatch on {src_path}"
    matched_hashes += 1
    for part, expected_sha in m["parts"].items():
      part_path = TOOLCHAIN_DIR / "lib/lean" / rel.with_suffix(f".{part}")
      assert sha256_file(part_path) == expected_sha, f"Mismatch on {part_path}"
      matched_hashes += 1
  per_module_hash_ms = (time.perf_counter() - t0) * 1000.0

  # Verify that the 3,100+ lines of `"graph"` in `library-lock.json` are 100%
  # identical to the `ModuleData.imports` arrays already stored inside the
  # `.olean` headers on disk!
  stage_dir = SCRATCH_DIR / "lib_lock_probe_stage"
  stage_dir.mkdir(parents=True, exist_ok=True)
  mod_names_json = stage_dir / "mod_names.json"
  olean_graph_json = stage_dir / "olean_graph.json"
  mod_names_json.write_text(json.dumps(list(modules.keys())))

  lean_probe = stage_dir / "VerifyOleanGraph.lean"
  lean_probe.write_text("""import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let [sysrootStr, modNamesPath, outGraphPath] := args
    | return 1
  Lean.initSearchPath (System.FilePath.mk sysrootStr)
  let modNames ← IO.ofExcept <|
    (Json.parse (← IO.FS.readFile modNamesPath) >>= fromJson? (α := Array String))
  let mut pairs : Array (String × Json) := #[]
  for mStr in modNames do
    let mName := mStr.toName
    let oleanPath ← findOLean mName
    let (modData, _) ← readModuleData oleanPath
    pairs := pairs.push (mStr, toJson modData.imports)
  IO.FS.writeFile outGraphPath (Json.mkObj pairs.toList).pretty
  return 0
""")

  t_olean0 = time.perf_counter()
  cmd = [
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "5",
      "--",
      LEAN,
      "--run",
      str(lean_probe),
      str(TOOLCHAIN_DIR),
      str(mod_names_json),
      str(olean_graph_json),
  ]
  p = subprocess.run(cmd, cwd=stage_dir, capture_output=True, text=True, check=False)
  assert p.returncode == 0, f"VerifyOleanGraph failed:\n{p.stdout}\n{p.stderr}"
  read_olean_headers_ms = (time.perf_counter() - t_olean0) * 1000.0

  olean_graph = json.loads(olean_graph_json.read_text())
  assert olean_graph == graph, "Mismatch between library-lock.json graph and .olean ModuleData.imports!"

  # Measure recursive sysroot tree digest (`stage_tree_digest`) and warm
  # `FileFingerprint` stat check over `Init` + `Std` in `lib/lean` and `src/lean`
  t_tree0 = time.perf_counter()
  lib_init_sha, lib_init_files, lib_init_bytes = stage_tree_digest(
      TOOLCHAIN_DIR / "lib/lean/Init"
  )
  lib_std_sha, lib_std_files, lib_std_bytes = stage_tree_digest(
      TOOLCHAIN_DIR / "lib/lean/Std"
  )
  src_init_sha, src_init_files, src_init_bytes = stage_tree_digest(
      TOOLCHAIN_DIR / "src/lean/Init"
  )
  src_std_sha, src_std_files, src_std_bytes = stage_tree_digest(
      TOOLCHAIN_DIR / "src/lean/Std"
  )
  cold_tree_hash_ms = (time.perf_counter() - t_tree0) * 1000.0

  t_stat0 = time.perf_counter()
  stat_files = (
      stat_tree_fingerprints(TOOLCHAIN_DIR / "lib/lean/Init")
      + stat_tree_fingerprints(TOOLCHAIN_DIR / "lib/lean/Std")
      + stat_tree_fingerprints(TOOLCHAIN_DIR / "src/lean/Init")
      + stat_tree_fingerprints(TOOLCHAIN_DIR / "src/lean/Std")
  )
  warm_fingerprint_stat_ms = (time.perf_counter() - t_stat0) * 1000.0

  lock_lines_replacement = [
      f"{lib_init_sha}  lean/lib/lean/Init/**",
      f"{lib_std_sha}  lean/lib/lean/Std/**",
      f"{src_init_sha}  lean/src/lean/Init/**",
      f"{src_std_sha}  lean/src/lean/Std/**",
  ]
  replacement_bytes = len(("\n".join(lock_lines_replacement) + "\n").encode("utf-8"))

  result = {
      "lean_version": "4.34.1",
      "library_lock_json": {
          "lines": line_count,
          "bytes": byte_count,
          "locked_modules": num_modules,
          "hardcoded_sha256_digests": num_sha256_entries,
          "hardcoded_import_edges": num_graph_edges,
          "all_732_hashes_match_v4_34_1_sysroot": matched_hashes == num_sha256_entries,
          "graph_100pct_identical_to_olean_headers": olean_graph == graph,
          "per_module_732_sha256_verify_ms": round(per_module_hash_ms, 2),
      },
      "sysroot_tree_digest_replacement": {
          "toolchain_lock_lines_added": len(lock_lines_replacement),
          "toolchain_lock_bytes_added": replacement_bytes,
          "lines_reduction_pct": round(
              (1.0 - len(lock_lines_replacement) / line_count) * 100.0, 2
          ),
          "bytes_reduction_pct": round(
              (1.0 - replacement_bytes / byte_count) * 100.0, 2
          ),
          "tree_entries": lock_lines_replacement,
          "total_files_covered": (
              lib_init_files + lib_std_files + src_init_files + src_std_files
          ),
          "total_bytes_covered": (
              lib_init_bytes + lib_std_bytes + src_init_bytes + src_std_bytes
          ),
          "cold_tree_sha256_ms": round(cold_tree_hash_ms, 2),
          "warm_stat_fingerprint_ms": round(warm_fingerprint_stat_ms, 2),
          "olean_header_graph_read_122_modules_ms": round(read_olean_headers_ms, 2),
      },
  }
  out_path = SCRATCH_DIR / "library_lock_vs_sysroot_tree.json"
  out_path.write_text(json.dumps(result, indent=2) + "\n")
  print(json.dumps(result, indent=2))


if __name__ == "__main__":
  main()
