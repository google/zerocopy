#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic FIFO-synchronized probes for rustc concurrent source edits.

Tests:
1. Exp 1: Intra-crate temporal skew across `mod first; mod gate; mod second;`.
2. Exp 2: Single-file split-brain via non-canonical path aliasing (`./shared.rs`
   vs `./sub/../shared.rs` and symlink aliasing).
3. Exp 3: Same-path caching vs re-reading across `include!`, `include_str!`,
   `include_bytes!`, `mod`, file deletion, phase ordering (`collect_invocations`
   vs `expand_invoc`), and `-Zchecksum-hash-algorithm` dep-info emission
   (`write_out_deps`).
4. Exp 4: Cross-crate `ensure_source_file_source_present` / `add_external_src`
   hash validation (`src_hash.matches`) vs intra-crate in-memory `SourceFile.src`
   during diagnostic rendering.
"""

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import threading
from pathlib import Path


def run_cmd(cmd, cwd=None):
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    return {
        "cmd": [str(c) for c in cmd],
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def experiment_1_intra_crate_temporal_skew(base_dir: Path) -> dict:
    """Exp 1: `main.rs` -> `mod first; mod gate; mod second;` with FIFO gate."""
    work = base_dir / "exp1_temporal_skew"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    main_rs = work / "main.rs"
    first_rs = work / "first.rs"
    gate_rs = work / "gate.rs"
    second_rs = work / "second.rs"
    out_bin = work / "exp1_bin"

    main_rs.write_text(
        "mod first;\n"
        "mod gate;\n"
        "mod second;\n"
        "fn main() {\n"
        "    println!(\"first={}, second={}, gate={}\", first::V, second::V, gate::G);\n"
        "}\n",
        encoding="utf-8",
    )
    first_rs.write_text("pub const V: u32 = 10;\n", encoding="utf-8")
    second_rs.write_text("pub const V: u32 = 10;\n", encoding="utf-8")
    os.mkfifo(gate_rs)

    def writer_thread():
        # Kernel-level rendezvous: blocks until rustc opens gate.rs for reading
        # after parsing main.rs and first.rs, before parsing second.rs.
        fd = os.open(gate_rs, os.O_WRONLY)
        try:
            first_rs.write_text("pub const V: u32 = 20;\n", encoding="utf-8")
            second_rs.write_text("pub const V: u32 = 20;\n", encoding="utf-8")
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_thread, daemon=True)
    t.start()
    compile_res = run_cmd(["rustc", "--edition=2021", "main.rs", "-o", str(out_bin)], cwd=work)
    t.join(timeout=5.0)

    run_res = run_cmd([str(out_bin)], cwd=work) if compile_res["returncode"] == 0 else None
    return {
        "compile": compile_res,
        "run": run_res,
        "final_first_rs": first_rs.read_text(encoding="utf-8"),
        "final_second_rs": second_rs.read_text(encoding="utf-8"),
    }


def experiment_2_non_canonical_path_aliasing(base_dir: Path) -> dict:
    """Exp 2: Single physical file read twice at different times via `#[path]`."""
    work = base_dir / "exp2_path_aliasing"
    if work.exists():
        shutil.rmtree(work)
    (work / "sub").mkdir(parents=True)

    main_rs = work / "main.rs"
    shared_rs = work / "shared.rs"
    symlink_rs = work / "sym_shared.rs"
    gate_rs = work / "gate.rs"

    os.symlink("shared.rs", symlink_rs)
    os.mkfifo(gate_rs)

    main_rs.write_text(
        "#[path = \"./shared.rs\"]\n"
        "mod a;\n"
        "mod gate;\n"
        "#[path = \"./sub/../shared.rs\"]\n"
        "mod b;\n"
        "#[path = \"./sym_shared.rs\"]\n"
        "mod c;\n"
        "fn main() {\n"
        "    println!(\"a={}, b={}, c={}, a_file={}, b_file={}, c_file={}\",\n"
        "        a::V, b::V, c::V, a::FILE, b::FILE, c::FILE);\n"
        "}\n",
        encoding="utf-8",
    )
    shared_rs.write_text(
        "pub const V: u32 = 1;\npub const FILE: &str = file!();\n",
        encoding="utf-8",
    )

    inode_before = shared_rs.stat().st_ino

    def writer_thread():
        fd = os.open(gate_rs, os.O_WRONLY)
        try:
            # Mutate shared.rs in place (preserving inode) while rustc is blocked on gate.rs
            with open(shared_rs, "r+", encoding="utf-8") as f:
                f.seek(0)
                f.write("pub const V: u32 = 2;\npub const FILE: &str = file!();\n")
                f.truncate()
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_thread, daemon=True)
    t.start()
    compile_res = run_cmd(
        [
            "rustc",
            "--edition=2021",
            "-Z",
            "checksum-hash-algorithm=sha256",
            "--emit=link,dep-info",
            "main.rs",
        ],
        cwd=work,
    )
    t.join(timeout=5.0)

    inode_after = shared_rs.stat().st_ino
    run_res = run_cmd([str(work / "main")], cwd=work) if compile_res["returncode"] == 0 else None
    dep_info = (work / "main.d").read_text(encoding="utf-8") if (work / "main.d").exists() else None
    return {
        "compile": compile_res,
        "run": run_res,
        "same_inode": inode_before == inode_after,
        "inode": inode_before,
        "dep_info": dep_info,
    }


def experiment_3_same_path_reuse_and_depinfo(base_dir: Path) -> dict:
    """Exp 3: Same-path caching vs re-reading across include!, include_str!, include_bytes!."""
    results = {}

    v1_text = "pub const V: u32 = 1;\n"
    v2_text = "pub const V: u32 = 2;\n"

    # --- Sub-experiment 3a: include! vs include_str! vs include_bytes! on identical path ---
    # We use `mod gate_mod { include!("./gate.rs"); }` as the macro-phase FIFO gate
    # so the barrier executes in exact macro-expansion order between BEFORE and AFTER,
    # and calls `SourceMap::load_file` (not `load_binary_file`).
    work3a = base_dir / "exp3a_include_macros"
    if work3a.exists():
        shutil.rmtree(work3a)
    work3a.mkdir(parents=True)

    shared_rs = work3a / "shared.rs"
    gate_rs = work3a / "gate.rs"
    main_rs = work3a / "main.rs"

    shared_rs.write_text(v1_text, encoding="utf-8")
    os.mkfifo(gate_rs)

    main_rs.write_text(
        "mod before_inc {\n"
        "    include!(\"./shared.rs\");\n"
        "}\n"
        "const STR_BEFORE: &str = include_str!(\"./shared.rs\");\n"
        "const BYTES_BEFORE: &[u8] = include_bytes!(\"./shared.rs\");\n"
        "mod gate_mod {\n"
        "    include!(\"./gate.rs\");\n"
        "}\n"
        "mod after_inc {\n"
        "    include!(\"./shared.rs\");\n"
        "}\n"
        "const STR_AFTER: &str = include_str!(\"./shared.rs\");\n"
        "const BYTES_AFTER: &[u8] = include_bytes!(\"./shared.rs\");\n"
        "fn main() {\n"
        "    println!(\n"
        "        \"before_inc::V={}, after_inc::V={}, STR_BEFORE={:?}, STR_AFTER={:?}, BYTES_BEFORE={:?}, BYTES_AFTER={:?}\",\n"
        "        before_inc::V,\n"
        "        after_inc::V,\n"
        "        STR_BEFORE.trim(),\n"
        "        STR_AFTER.trim(),\n"
        "        std::str::from_utf8(BYTES_BEFORE).unwrap().trim(),\n"
        "        std::str::from_utf8(BYTES_AFTER).unwrap().trim(),\n"
        "    );\n"
        "}\n",
        encoding="utf-8",
    )

    def writer_3a():
        fd = os.open(gate_rs, os.O_WRONLY)
        try:
            shared_rs.write_text(v2_text, encoding="utf-8")
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_3a, daemon=True)
    t.start()
    comp_3a = run_cmd(["rustc", "--edition=2021", "main.rs", "-o", "bin3a"], cwd=work3a)
    t.join(timeout=5.0)
    run_3a = run_cmd([str(work3a / "bin3a")], cwd=work3a) if comp_3a["returncode"] == 0 else None
    results["sub_3a_same_path_include_vs_str_vs_bytes"] = {
        "compile": comp_3a,
        "run": run_3a,
    }

    # --- Sub-experiment 3b: include_bytes! before gate populates SourceMap cache,
    # poisoning a subsequent `include!("./shared.rs")` (or macro-expanded `mod shared;`)
    # after the gate! ---
    work3b = base_dir / "exp3b_binary_poisons_include"
    if work3b.exists():
        shutil.rmtree(work3b)
    work3b.mkdir(parents=True)

    shared_b = work3b / "shared.rs"
    gate_b = work3b / "gate.rs"
    main_b = work3b / "main.rs"
    shared_b.write_text(v1_text, encoding="utf-8")
    os.mkfifo(gate_b)

    main_b.write_text(
        "macro_rules! declare_shared_mods {\n"
        "    () => {\n"
        "        #[path = \"./shared.rs\"]\n"
        "        mod shared_same_path;\n"
        "        mod shared;\n"
        "    };\n"
        "}\n"
        "const BYTES_EARLY: &[u8] = include_bytes!(\"./shared.rs\");\n"
        "mod gate_mod { include!(\"./gate.rs\"); }\n"
        "declare_shared_mods!();\n"
        "const BYTES_LATE: &[u8] = include_bytes!(\"./shared.rs\");\n"
        "fn main() {\n"
        "    println!(\n"
        "        \"BYTES_EARLY={:?}, shared_same_path::V={} (cached by early include_bytes!), shared::V={} ('shared.rs' != './shared.rs'), BYTES_LATE={:?}\",\n"
        "        std::str::from_utf8(BYTES_EARLY).unwrap().trim(),\n"
        "        shared_same_path::V,\n"
        "        shared::V,\n"
        "        std::str::from_utf8(BYTES_LATE).unwrap().trim(),\n"
        "    );\n"
        "}\n",
        encoding="utf-8",
    )

    def writer_3b():
        fd = os.open(gate_b, os.O_WRONLY)
        try:
            shared_b.write_text(v2_text, encoding="utf-8")
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_3b, daemon=True)
    t.start()
    comp_3b = run_cmd(["rustc", "--edition=2021", "main.rs", "-o", "bin3b"], cwd=work3b)
    t.join(timeout=5.0)
    run_3b = run_cmd([str(work3b / "bin3b")], cwd=work3b) if comp_3b["returncode"] == 0 else None
    results["sub_3b_include_bytes_populates_sourcemap_for_later_mod"] = {
        "compile": comp_3b,
        "run": run_3b,
    }

    # --- Sub-experiment 3c: Deleting an already-cached SourceFile before a second include!
    # fails in SourceMap::load_file because `file_loader.read_file` runs BEFORE the
    # `stable_id_to_source_file` cache lookup in `try_new_source_file`! ---
    work3c = base_dir / "exp3c_delete_cached_file"
    if work3c.exists():
        shutil.rmtree(work3c)
    work3c.mkdir(parents=True)

    shared_c = work3c / "shared.rs"
    gate_c = work3c / "gate.rs"
    main_c = work3c / "main.rs"
    shared_c.write_text(v1_text, encoding="utf-8")
    os.mkfifo(gate_c)

    main_c.write_text(
        "mod first_inc { include!(\"./shared.rs\"); }\n"
        "mod gate_mod { include!(\"./gate.rs\"); }\n"
        "mod second_inc { include!(\"./shared.rs\"); }\n"
        "fn main() {}\n",
        encoding="utf-8",
    )

    def writer_3c():
        fd = os.open(gate_c, os.O_WRONLY)
        try:
            os.unlink(shared_c)
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_3c, daemon=True)
    t.start()
    comp_3c = run_cmd(["rustc", "--edition=2021", "main.rs", "-o", "bin3c"], cwd=work3c)
    t.join(timeout=5.0)
    results["sub_3c_deleted_cached_file_still_calls_read_file"] = {
        "compile": comp_3c,
    }

    # --- Sub-experiment 3d: write_out_deps re-reads file_depinfo (include_str!) at end of expansion ---
    work3d = base_dir / "exp3d_depinfo_checksum_mismatch"
    if work3d.exists():
        shutil.rmtree(work3d)
    work3d.mkdir(parents=True)

    first_d = work3d / "first.rs"
    data_d = work3d / "data.txt"
    gate_d = work3d / "gate.rs"
    main_d = work3d / "main.rs"

    first_t0 = b"pub const V: u32 = 10;\n"
    first_t1 = b"pub const V: u32 = 20;\n"
    data_t0 = b"OLD_PAYLOAD_T0\n"
    data_t1 = b"NEW_PAYLOAD_T1\n"

    first_d.write_bytes(first_t0)
    data_d.write_bytes(data_t0)
    os.mkfifo(gate_d)

    main_d.write_text(
        "mod first;\n"
        "const PAYLOAD: &str = include_str!(\"./data.txt\");\n"
        "mod gate_mod { include!(\"./gate.rs\"); }\n"
        "fn main() {\n"
        "    println!(\"first::V={}, PAYLOAD={:?}\", first::V, PAYLOAD.trim());\n"
        "}\n",
        encoding="utf-8",
    )

    def writer_3d():
        fd = os.open(gate_d, os.O_WRONLY)
        try:
            # Both first.rs (loaded via `mod` during collect_invocations) and
            # data.txt (loaded via `include_str!` before `include!("./gate.rs")`)
            # have ALREADY been read by rustc!
            # Now we overwrite both on disk before macro expansion completes and write_dep_info runs!
            first_d.write_bytes(first_t1)
            data_d.write_bytes(data_t1)
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_3d, daemon=True)
    t.start()
    comp_3d = run_cmd(
        [
            "rustc",
            "--edition=2021",
            "-Z",
            "checksum-hash-algorithm=sha256",
            "--emit=link,dep-info",
            "main.rs",
        ],
        cwd=work3d,
    )
    t.join(timeout=5.0)
    run_3d = run_cmd([str(work3d / "main")], cwd=work3d) if comp_3d["returncode"] == 0 else None
    dep_3d = (work3d / "main.d").read_text(encoding="utf-8") if (work3d / "main.d").exists() else None
    results["sub_3d_depinfo_rehashes_file_depinfo_at_t_end"] = {
        "compile": comp_3d,
        "run": run_3d,
        "expected_hashes": {
            "first_rs_t0_sha256": sha256_hex(first_t0),
            "first_rs_t1_sha256": sha256_hex(first_t1),
            "data_txt_t0_sha256": sha256_hex(data_t0),
            "data_txt_t1_sha256": sha256_hex(data_t1),
        },
        "dep_info": dep_3d,
    }

    # --- Sub-experiment 3e: Out-of-line `mod` items are loaded during `collect_invocations`
    # BEFORE any macro (`include_str!`) in the same fragment, even if `include_str!` is lexically earlier! ---
    work3e = base_dir / "exp3e_mod_before_macro_ordering"
    if work3e.exists():
        shutil.rmtree(work3e)
    work3e.mkdir(parents=True)

    data_e = work3e / "data.txt"
    gate_e = work3e / "gate.rs"
    main_e = work3e / "main.rs"
    data_e.write_text("T0_BEFORE_MOD_GATE\n", encoding="utf-8")
    os.mkfifo(gate_e)

    main_e.write_text(
        "// Even though `include_str!` is on line 3 and `mod gate;` is on line 4,\n"
        "// `collect_invocations` loads `mod gate;` BEFORE expanding `include_str!`!\n"
        "const PAYLOAD: &str = include_str!(\"./data.txt\");\n"
        "mod gate;\n"
        "fn main() {\n"
        "    println!(\"PAYLOAD={:?}, gate={}\", PAYLOAD.trim(), gate::G);\n"
        "}\n",
        encoding="utf-8",
    )

    def writer_3e():
        fd = os.open(gate_e, os.O_WRONLY)
        try:
            data_e.write_text("T1_DURING_MOD_GATE\n", encoding="utf-8")
            os.write(fd, b"pub const G: u32 = 1;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_3e, daemon=True)
    t.start()
    comp_3e = run_cmd(["rustc", "--edition=2021", "main.rs", "-o", "bin3e"], cwd=work3e)
    t.join(timeout=5.0)
    run_3e = run_cmd([str(work3e / "bin3e")], cwd=work3e) if comp_3e["returncode"] == 0 else None
    results["sub_3e_out_of_line_mod_loaded_before_lexically_earlier_macro"] = {
        "compile": comp_3e,
        "run": run_3e,
    }

    return results


def experiment_4_cross_crate_external_src_validation(base_dir: Path) -> dict:
    """Exp 4: Cross-crate `ensure_source_file_source_present` & `add_external_src` validation."""
    work = base_dir / "exp4_cross_crate"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    dep_rs = work / "dep.rs"
    user_rs = work / "user.rs"

    dep_orig = (
        "pub fn expect_u32(_x: u32) {}\n"
        "// Padding comment: AAAAAAAAAA\n"
    )
    dep_same_len = (
        "pub fn expect_u32(_x: u32) {}\n"
        "// Padding comment: BBBBBBBBBB\n"
    )
    assert len(dep_orig.encode("utf-8")) == len(dep_same_len.encode("utf-8"))
    dep_diff_len = "// Shorter modified file\n"

    dep_rs.write_text(dep_orig, encoding="utf-8")
    user_rs.write_text(
        "extern crate dep;\n"
        "fn main() {\n"
        "    dep::expect_u32(\"not_a_u32\");\n"
        "}\n",
        encoding="utf-8",
    )

    compile_dep = run_cmd(
        ["rustc", "--edition=2021", "--crate-type=rlib", "dep.rs", "-o", "libdep.rlib"],
        cwd=work,
    )

    # 4a: Unmodified dep.rs
    diag_unmodified = run_cmd(
        ["rustc", "--edition=2021", "user.rs", "--extern", "dep=libdep.rlib"],
        cwd=work,
    )

    # 4b: Modified dep.rs with exact same byte length
    dep_rs.write_text(dep_same_len, encoding="utf-8")
    diag_same_len_modified = run_cmd(
        ["rustc", "--edition=2021", "user.rs", "--extern", "dep=libdep.rlib"],
        cwd=work,
    )

    # 4c: Modified dep.rs with different (shorter) byte length
    dep_rs.write_text(dep_diff_len, encoding="utf-8")
    diag_diff_len_modified = run_cmd(
        ["rustc", "--edition=2021", "user.rs", "--extern", "dep=libdep.rlib"],
        cwd=work,
    )

    # 4d: Contrast with intra-crate local module modified after parse but before typeck diagnostic
    work_local = work / "local_diag"
    work_local.mkdir(parents=True)
    local_main = work_local / "main.rs"
    local_first = work_local / "first.rs"
    local_gate = work_local / "gate.rs"

    local_first.write_text(
        "pub fn bad() -> u32 {\n"
        "    \"ORIGINAL_IN_MEMORY_TEXT\"\n"
        "}\n",
        encoding="utf-8",
    )
    os.mkfifo(local_gate)
    local_main.write_text(
        "mod first;\n"
        "mod gate;\n"
        "fn main() { let _ = first::bad(); }\n",
        encoding="utf-8",
    )

    def writer_4d():
        fd = os.open(local_gate, os.O_WRONLY)
        try:
            local_first.write_text(
                "pub fn bad() -> u32 {\n"
                "    \"MODIFIED_ON_DISK_TEXT\"\n"
                "}\n",
                encoding="utf-8",
            )
            os.write(fd, b"pub const G: u32 = 0;\n")
        finally:
            os.close(fd)

    t = threading.Thread(target=writer_4d, daemon=True)
    t.start()
    diag_local_modified = run_cmd(["rustc", "--edition=2021", "main.rs"], cwd=work_local)
    t.join(timeout=5.0)

    return {
        "compile_dep": compile_dep,
        "case_4a_unmodified_dep": diag_unmodified,
        "case_4b_same_len_modified_dep": diag_same_len_modified,
        "case_4c_diff_len_modified_dep": diag_diff_len_modified,
        "case_4d_local_crate_modified_before_typeck_diag": diag_local_modified,
    }


def main():
    tmp_ctx = tempfile.TemporaryDirectory(prefix="rustc_source_probes_")
    base_dir = Path(tmp_ctx.name)

    rustc_vv = run_cmd(["rustc", "-vV"])
    exp1 = experiment_1_intra_crate_temporal_skew(base_dir)
    exp2 = experiment_2_non_canonical_path_aliasing(base_dir)
    exp3 = experiment_3_same_path_reuse_and_depinfo(base_dir)
    exp4 = experiment_4_cross_crate_external_src_validation(base_dir)

    summary = {
        "rustc_version": rustc_vv["stdout"],
        "experiment_1_intra_crate_temporal_skew": exp1,
        "experiment_2_non_canonical_path_aliasing": exp2,
        "experiment_3_same_path_reuse_and_depinfo": exp3,
        "experiment_4_cross_crate_external_src_validation": exp4,
    }

    out_json = Path(__file__).resolve().parent / "rustc_probe_results.json"
    out_json.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote results to {out_json}")
    print("--- EXP 1 RUN STDOUT ---")
    print(exp1["run"]["stdout"] if exp1["run"] else exp1["compile"]["stderr"])
    print("--- EXP 2 RUN STDOUT ---")
    print(exp2["run"]["stdout"] if exp2["run"] else exp2["compile"]["stderr"])
    print("--- EXP 3a RUN STDOUT ---")
    print(exp3["sub_3a_same_path_include_vs_str_vs_bytes"]["run"]["stdout"])
    print("--- EXP 3b RUN STDOUT ---")
    print(exp3["sub_3b_include_bytes_populates_sourcemap_for_later_mod"]["run"]["stdout"])
    print("--- EXP 3c STDERR ---")
    print(exp3["sub_3c_deleted_cached_file_still_calls_read_file"]["compile"]["stderr"])
    print("--- EXP 3d RUN STDOUT & DEP INFO ---")
    print(exp3["sub_3d_depinfo_rehashes_file_depinfo_at_t_end"]["run"]["stdout"])
    print(exp3["sub_3d_depinfo_rehashes_file_depinfo_at_t_end"]["expected_hashes"])
    print(exp3["sub_3d_depinfo_rehashes_file_depinfo_at_t_end"]["dep_info"])
    print("--- EXP 3e RUN STDOUT ---")
    print(exp3["sub_3e_out_of_line_mod_loaded_before_lexically_earlier_macro"]["run"]["stdout"])
    print("--- EXP 4a vs 4b vs 4c STDERR ---")
    print("4a (unmodified):\n" + exp4["case_4a_unmodified_dep"]["stderr"])
    print("4b (same-len modified):\n" + exp4["case_4b_same_len_modified_dep"]["stderr"])
    print("4c (diff-len modified):\n" + exp4["case_4c_diff_len_modified_dep"]["stderr"])
    print("4d (local modified):\n" + exp4["case_4d_local_crate_modified_before_typeck_diag"]["stderr"])


if __name__ == "__main__":
    main()
