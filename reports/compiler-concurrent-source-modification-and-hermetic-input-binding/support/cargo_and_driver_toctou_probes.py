#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Track 3 Empirical Probes: Build Orchestrator Mtime/Checksum Races & Hermetic rustc_driver Patterns.

Tests:
1. Cargo default mtime freshness:
   - Probe 1A: How Cargo's `invoked.timestamp` rewind (`set_invocation_time` at t0 +
     `set_file_time_no_err(dep_info_loc, t0)` at t3) handles mid-build edits when t2 > t0.
   - Probe 1B: How Cargo's `path_mtime <= reference_mtime` check (`cargo#5918`) causes
     permanent stale-binary cache poisoning when a mid-build edit lands in the same
     filesystem timestamp tick (t2 == t0) or when `dep-lib` retains its post-rustc mtime (t3).
2. Cargo `-Z checksum-freshness` (`-Z checksum-hash-algorithm=blake3`):
   - Probe 2A: Single-read `SourceMap` in-memory hashing at t1 detects a mid-build edit at t2.
   - Probe 2B: `proc_macro::tracked_path::path` post-expansion re-read (`hash_iter_files` in
     `compiler/rustc_interface/src/passes.rs:614-649`) hashes the file on disk AFTER macro
     expansion (t_depinfo > t2) and overwrites the `SourceMap` entry, poisoning `-Z checksum-freshness`
     into permanently caching the stale Version 1 binary!
   - Probe 2C: Non-canonical path aliasing (`src/main.rs` at t1 vs `include_str!("./main.rs")` at t2
     after a mid-build edit) emits two `# checksum:` lines in `.d` that Cargo canonicalizes to the
     same key in `parse_dep_info`, overwriting Version 1's hash with Version 2's hash and
     permanently caching the stale/mixed binary under `-Z checksum-freshness`!
3. GNU Make (`mtime(input) <= mtime(output)`):
   - Probe 3: Classic mid-build edit poisoning (t_read < t_edit < t_output) permanently caches
     a stale Version 1 binary.
4. `rustc_driver` Source-Binding Verification Patterns (Patterns 1..5):
   - Pattern 1: External pre-hash only (vulnerable to t_pre < t_edit < t_read).
   - Pattern 2: External post-hash only (vulnerable to t_read < t_edit < t_post).
   - Pattern 3: External pre_hash == post_hash without FileLoader (vulnerable to ABA race A -> B -> A
     and undeclared `#[path]` / `include!` files).
   - Pattern 4: In-process `FileLoader` recording + canonical-path & `(st_dev, st_ino)` single-hash
     invariant + post-compile `source_map` / `file_depinfo` / `env_depinfo` audit (catches pre/mid/post
     edits, ABA races, non-canonical path aliasing, and hardlink aliasing; demonstrates residual gap for
     untracked `std::fs::read` inside an un-sandboxed procedural macro).
   - Pattern 5: Preloaded in-memory `VirtualFileLoader` (immune to all concurrent filesystem edits
     for `SourceMap` reads).
"""

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import threading
import time
from pathlib import Path

OUT_DIR = Path(__file__).resolve().parent


def run_cmd(cmd, cwd=None, env=None, check=True):
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        env=merged_env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"Command {cmd} failed (rc={proc.returncode}):\n"
            f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )
    return proc


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


# ==============================================================================
# Probe 1: Cargo Default Mtime Freshness (invoked.timestamp rewind vs <= bug)
# ==============================================================================
def probe_1_cargo_mtime(tmp_root: Path) -> dict:
    results = {}

    # --- Sub-probe 1A: Mid-build edit across distinct clock tick (t2 > t0) ---
    pkg_a = tmp_root / "cargo_mtime_distinct_tick"
    (pkg_a / "src").mkdir(parents=True)
    (pkg_a / "Cargo.toml").write_text(
        '[package]\nname = "foo_mtime"\nversion = "0.1.0"\nedition = "2021"\n'
    )
    v1_code = (
        'mod gate;\n'
        'fn main() {\n'
        '    println!("VERSION_1");\n'
        '}\n'
    )
    v2_code = (
        'mod gate;\n'
        'fn main() {\n'
        '    println!("VERSION_2");\n'
        '}\n'
    )
    main_rs_a = pkg_a / "src" / "main.rs"
    gate_rs_a = pkg_a / "src" / "gate.rs"
    main_rs_a.write_text(v1_code)
    os.mkfifo(gate_rs_a)

    def writer_1a():
        with open(gate_rs_a, "w") as fifo:
            # At this point rustc has already parsed src/main.rs (Version 1) and opened src/gate.rs.
            # Sleep 50ms so the OS clock advances well past invoked.timestamp (t0).
            time.sleep(0.05)
            main_rs_a.write_text(v2_code)
            fifo.write("pub const GATE: u32 = 1;\n")
            fifo.flush()
        # Replace FIFO with regular file so subsequent cargo builds don't block on FIFO
        gate_rs_a.unlink()
        gate_rs_a.write_text("pub const GATE: u32 = 1;\n")
        # Set gate.rs mtime older than main.rs so main.rs is the deciding input
        st = main_rs_a.stat()
        os.utime(gate_rs_a, ns=(st.st_atime_ns, st.st_mtime_ns))

    t = threading.Thread(target=writer_1a)
    t.start()
    build1 = run_cmd(["cargo", "build"], cwd=pkg_a)
    t.join()

    bin_a = pkg_a / "target" / "debug" / "foo_mtime"
    out1 = run_cmd([str(bin_a)]).stdout.strip()

    # Inspect invoked.timestamp and dep-bin-foo_mtime mtime vs src/main.rs mtime
    fp_dir_a = next((pkg_a / "target").rglob("invoked.timestamp")).parent
    invoked_ts_ns = (fp_dir_a / "invoked.timestamp").stat().st_mtime_ns
    dep_bin_ns = (fp_dir_a / "dep-bin-foo_mtime").stat().st_mtime_ns
    main_rs_ns = main_rs_a.stat().st_mtime_ns

    build2 = run_cmd(["cargo", "build", "-v"], cwd=pkg_a)
    out2 = run_cmd([str(bin_a)]).stdout.strip()

    results["1a_distinct_tick_mid_build_edit"] = {
        "binary_after_build1": out1,
        "on_disk_after_build1": "VERSION_2" if "VERSION_2" in main_rs_a.read_text() else "VERSION_1",
        "invoked_timestamp_mtime_ns": invoked_ts_ns,
        "dep_bin_mtime_ns": dep_bin_ns,
        "dep_bin_rewound_to_invoked_timestamp": dep_bin_ns == invoked_ts_ns,
        "main_rs_edit_mtime_ns": main_rs_ns,
        "main_rs_StrictlyNewerThan_dep_bin": main_rs_ns > dep_bin_ns,
        "build2_rebuilt": "Compiling foo_mtime" in build2.stderr,
        "binary_after_build2": out2,
    }

    # --- Sub-probe 1B: Same-tick / coarse-clock mtime poisoning (t2 == t0, cargo#5918) ---
    pkg_b = tmp_root / "cargo_mtime_same_tick_poison"
    (pkg_b / "src").mkdir(parents=True)
    (pkg_b / "Cargo.toml").write_text(
        '[package]\nname = "foo_poison"\nversion = "0.1.0"\nedition = "2021"\n'
    )
    main_rs_b = pkg_b / "src" / "main.rs"
    gate_rs_b = pkg_b / "src" / "gate.rs"
    main_rs_b.write_text(v1_code)
    os.mkfifo(gate_rs_b)

    def writer_1b():
        with open(gate_rs_b, "w") as fifo:
            # Locate the invoked.timestamp that Cargo just wrote before spawning rustc
            invoked_file = next((pkg_b / "target").rglob("invoked.timestamp"))
            t0_ns = invoked_file.stat().st_mtime_ns
            # Edit main.rs while rustc is mid-compile, landing in the exact same timestamp tick t0_ns
            # (simulating coarse filesystem granularity / same kernel jiffy tick / Docker layer mtime)
            main_rs_b.write_text(v2_code)
            os.utime(main_rs_b, ns=(t0_ns, t0_ns))
            fifo.write("pub const GATE: u32 = 1;\n")
            fifo.flush()
            t0_saved = t0_ns
        gate_rs_b.unlink()
        gate_rs_b.write_text("pub const GATE: u32 = 1;\n")
        os.utime(gate_rs_b, ns=(t0_saved, t0_saved))

    t = threading.Thread(target=writer_1b)
    t.start()
    run_cmd(["cargo", "build"], cwd=pkg_b)
    t.join()

    bin_b = pkg_b / "target" / "debug" / "foo_poison"
    out1_b = run_cmd([str(bin_b)]).stdout.strip()
    fp_dir_b = next((pkg_b / "target").rglob("invoked.timestamp")).parent
    dep_bin_b_ns = (fp_dir_b / "dep-bin-foo_poison").stat().st_mtime_ns
    main_rs_b_ns = main_rs_b.stat().st_mtime_ns

    # Now run cargo build again at t4 >> t3!
    time.sleep(0.05)
    build2_b = run_cmd(["cargo", "build", "-v"], cwd=pkg_b)
    out2_b = run_cmd([str(bin_b)]).stdout.strip()

    results["1b_same_tick_or_coarse_mtime_poisoning"] = {
        "binary_after_build1": out1_b,
        "on_disk_after_build1": "VERSION_2" if "VERSION_2" in main_rs_b.read_text() else "VERSION_1",
        "dep_bin_mtime_ns": dep_bin_b_ns,
        "main_rs_mtime_ns": main_rs_b_ns,
        "path_mtime_le_reference_mtime": main_rs_b_ns <= dep_bin_b_ns,
        "build2_rebuilt": "Compiling foo_poison" in build2_b.stderr,
        "binary_after_build2": out2_b,
        "stale_binary_permanently_cached": (out2_b == "VERSION_1" and "VERSION_2" in main_rs_b.read_text()),
    }
    return results


# ==============================================================================
# Probe 2: Cargo `-Z checksum-freshness` (In-Memory SourceMap vs 2 Poisoning Bugs)
# ==============================================================================
def probe_2_cargo_checksum_freshness(tmp_root: Path) -> dict:
    results = {}

    # --- Sub-probe 2A: Single SourceMap read (in-memory blake3 at t1 catches mid-build edit) ---
    pkg_2a = tmp_root / "cargo_cksum_single_read"
    (pkg_2a / "src").mkdir(parents=True)
    (pkg_2a / "Cargo.toml").write_text(
        '[package]\nname = "cksum_single"\nversion = "0.1.0"\nedition = "2021"\n'
    )
    main_2a = pkg_2a / "src" / "main.rs"
    gate_2a = pkg_2a / "src" / "gate.rs"
    v1_2a = 'mod gate;\nfn main() { println!("VERSION_1"); }\n'
    v2_2a = 'mod gate;\nfn main() { println!("VERSION_2_LONGER"); }\n'
    main_2a.write_text(v1_2a)
    os.mkfifo(gate_2a)

    def writer_2a():
        with open(gate_2a, "w") as fifo:
            # Modify main.rs while rustc is blocked on gate.rs
            main_2a.write_text(v2_2a)
            fifo.write("pub const G: u32 = 1;\n")
            fifo.flush()
        # Keep gate.rs identical content so only main.rs differs
        gate_2a.unlink()
        gate_2a.write_text("pub const G: u32 = 1;\n")

    t = threading.Thread(target=writer_2a)
    t.start()
    run_cmd(
        ["cargo", "build", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"'],
        cwd=pkg_2a,
    )
    t.join()

    bin_2a = pkg_2a / "target" / "debug" / "cksum_single"
    out1_2a = run_cmd([str(bin_2a)]).stdout.strip()
    d_file_2a = next((pkg_2a / "target" / "debug" / "build").rglob("cksum_single*.d"))
    d_text_2a = d_file_2a.read_text()

    build2_2a = run_cmd(
        ["cargo", "build", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"', "-v"],
        cwd=pkg_2a,
    )
    out2_2a = run_cmd([str(bin_2a)]).stdout.strip()

    results["2a_single_sourcemap_read"] = {
        "binary_after_build1": out1_2a,
        "dep_info_checksum_lines": [
            line for line in d_text_2a.splitlines() if line.startswith("# checksum:")
        ],
        "build2_rebuilt": "Compiling cksum_single" in build2_2a.stderr,
        "binary_after_build2": out2_2a,
    }

    # --- Sub-probe 2B: Checksum Poisoning Bug #1 (`proc_macro::tracked_path::path`) ---
    # In `compiler/rustc_interface/src/passes.rs:614-649`, `write_out_deps` hashes all
    # `sess.file_depinfo` entries (`extra_tracked_files`) by opening them from disk AFTER
    # macro expansion (`hash_iter_files`) and calling `files.extend(extra_tracked_files)`,
    # which ALSO overwrites any in-memory `SourceMap` checksum for that path!
    ws_2b = tmp_root / "cargo_cksum_tracked_path_poison"
    (ws_2b / "pm" / "src").mkdir(parents=True)
    (ws_2b / "app" / "src").mkdir(parents=True)
    (ws_2b / "Cargo.toml").write_text(
        '[workspace]\nmembers = ["pm", "app"]\nresolver = "2"\n'
    )
    (ws_2b / "pm" / "Cargo.toml").write_text(
        '[package]\nname = "pm"\nversion = "0.1.0"\nedition = "2021"\n'
        '[lib]\nproc-macro = true\n'
    )
    # The proc macro reads `app/data.txt` (Version 1), then waits until an external editor
    # updates `app/data.txt` (and even `app/src/main.rs`!) to Version 2 while macro expansion
    # is still in flight, and registers both via `proc_macro::tracked_path::path`.
    (ws_2b / "pm" / "src" / "lib.rs").write_text(
        '#![feature(proc_macro_tracked_path)]\n'
        'extern crate proc_macro;\n'
        'use proc_macro::TokenStream;\n'
        '\n'
        '#[proc_macro]\n'
        'pub fn embed_tracked(_input: TokenStream) -> TokenStream {\n'
        '    proc_macro::tracked::path("app/src/data.txt");\n'
        '    proc_macro::tracked::path("app/src/main.rs");\n'
        '    let val = std::fs::read_to_string("app/src/data.txt").unwrap();\n'
        '    // Signal the external editor via FIFO that Version 1 has been read\n'
        '    let _ = std::fs::read_to_string("app/src/gate.fifo");\n'
        '    format!("pub const EMBEDDED: &str = {:?};", val.trim()).parse().unwrap()\n'
        '}\n'
    )
    (ws_2b / "app" / "Cargo.toml").write_text(
        '[package]\nname = "app"\nversion = "0.1.0"\nedition = "2021"\n'
        '[dependencies]\npm = { path = "../pm" }\n'
    )
    app_main_2b = ws_2b / "app" / "src" / "main.rs"
    app_data_2b = ws_2b / "app" / "src" / "data.txt"
    app_fifo_2b = ws_2b / "app" / "src" / "gate.fifo"

    app_main_v1 = (
        'pm::embed_tracked!();\n'
        'fn main() {\n'
        '    println!("MAIN_V1:{}", EMBEDDED);\n'
        '}\n'
    )
    app_main_v2 = (
        'pm::embed_tracked!();\n'
        'fn main() {\n'
        '    println!("MAIN_V2:{}", EMBEDDED);\n'
        '}\n'
    )
    app_main_2b.write_text(app_main_v1)
    app_data_2b.write_text("DATA_V1\n")
    os.mkfifo(app_fifo_2b)

    # Pre-compile the proc-macro crate so only `app` compiles during the timed probe
    run_cmd(
        ["cargo", "build", "-p", "pm", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"'],
        cwd=ws_2b,
    )

    def writer_2b():
        with open(app_fifo_2b, "w") as fifo:
            # At this moment:
            # 1. rustc has already loaded `src/main.rs` (MAIN_V1) into SourceMap.
            # 2. `pm::embed_tracked!()` has already read `src/data.txt` (DATA_V1).
            # Now the user edits BOTH `src/data.txt` -> DATA_V2 and `src/main.rs` -> MAIN_V2!
            app_data_2b.write_text("DATA_V2_MODIFIED\n")
            app_main_2b.write_text(app_main_v2)
            fifo.write("go\n")
            fifo.flush()
        app_fifo_2b.unlink()

    t = threading.Thread(target=writer_2b)
    t.start()
    run_cmd(
        ["cargo", "build", "-p", "app", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"'],
        cwd=ws_2b,
    )
    t.join()

    bin_2b = ws_2b / "target" / "debug" / "app"
    out1_2b = run_cmd([str(bin_2b)]).stdout.strip()
    d_file_2b = next((ws_2b / "target" / "debug" / "build").rglob("app*.d"))
    d_text_2b = d_file_2b.read_text()

    # Now run `cargo build -p app -Z checksum-freshness` again at t4!
    # Both `src/main.rs` and `src/data.txt` on disk are Version 2, while the compiled binary
    # has MAIN_V1:DATA_V1! Because `write_out_deps` hashed `sess.file_depinfo` from disk at t3
    # (and overwrote `src/main.rs`'s SourceMap hash via `files.extend(extra_tracked_files)`),
    # `.d` recorded `blake3(Version 2)` for both files!
    build2_2b = run_cmd(
        ["cargo", "build", "-p", "app", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"', "-v"],
        cwd=ws_2b,
    )
    out2_2b = run_cmd([str(bin_2b)]).stdout.strip()

    results["2b_tracked_path_post_expansion_hash_poisoning"] = {
        "binary_after_build1": out1_2b,
        "on_disk_main_after_build1": "MAIN_V2" if "MAIN_V2" in app_main_2b.read_text() else "MAIN_V1",
        "on_disk_data_after_build1": app_data_2b.read_text().strip(),
        "dep_info_checksum_lines": [
            line for line in d_text_2b.splitlines() if line.startswith("# checksum:")
        ],
        "build2_rebuilt": "Compiling app" in build2_2b.stderr,
        "binary_after_build2": out2_2b,
        "stale_binary_permanently_cached": (
            out2_2b == "MAIN_V1:DATA_V1"
            and "MAIN_V2" in app_main_2b.read_text()
            and app_data_2b.read_text().strip() == "DATA_V2_MODIFIED"
        ),
    }

    # --- Sub-probe 2C: Checksum Poisoning Bug #2 (Non-Canonical Path Aliasing in SourceMap + Cargo Overwrite) ---
    # 1. `rustc` loads `src/main.rs` (Version 1) into `SourceMap` under `FileName::Real("src/main.rs")`.
    # 2. `rustc` blocks on `mod gate;` (`src/gate.rs` FIFO).
    # 3. Editor modifies `src/main.rs` on disk to Version 2 and releases `src/gate.rs`.
    # 4. `src/gate.rs` contains `include_str!("./main.rs")`, which resolves to `"src/./main.rs"`.
    # 5. Because `SourceMap::try_new_source_file` keys `files_map` by `StableSourceFileId`
    #    computed from the un-canonicalized path `"src/./main.rs" != "src/main.rs"`, `SourceMap`
    #    re-reads `src/./main.rs` from disk (getting Version 2!) and writes TWO `# checksum:` lines
    #    into `.d`: first `src/main.rs` (hash of V1), second `src/./main.rs` (hash of V2).
    # 6. Cargo's `translate_dep_info` (`dep_info.rs:360`) canonicalizes both via `try_canonicalize`
    #    to `"src/main.rs"`, and `parse_dep_info` (`dep_info.rs:498`) inserts them into `HashMap`,
    #    so the second entry (`hash(V2)`) overwrites the first entry (`hash(V1)`)!
    pkg_2c = tmp_root / "cargo_cksum_alias_poison"
    (pkg_2c / "src").mkdir(parents=True)
    (pkg_2c / "Cargo.toml").write_text(
        '[package]\nname = "cksum_alias"\nversion = "0.1.0"\nedition = "2021"\n'
    )
    main_2c = pkg_2c / "src" / "main.rs"
    gate_2c = pkg_2c / "src" / "gate.rs"
    v1_2c = 'mod gate;\nfn main() { println!("CODE_V1"); }\n'
    v2_2c = 'mod gate;\nfn main() { println!("CODE_V2_UPDATED"); }\n'
    main_2c.write_text(v1_2c)
    os.mkfifo(gate_2c)

    gate_content = 'pub const SELF_TEXT: &str = include_str!("./main.rs");\n'

    def writer_2c():
        with open(gate_2c, "w") as fifo:
            # rustc has parsed `src/main.rs` (CODE_V1) and is now reading `src/gate.rs`.
            # Update `src/main.rs` on disk to CODE_V2_UPDATED before `include_str!("./main.rs")` executes!
            main_2c.write_text(v2_2c)
            fifo.write(gate_content)
            fifo.flush()
        gate_2c.unlink()
        gate_2c.write_text(gate_content)

    t = threading.Thread(target=writer_2c)
    t.start()
    run_cmd(
        ["cargo", "build", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"'],
        cwd=pkg_2c,
    )
    t.join()

    bin_2c = pkg_2c / "target" / "debug" / "cksum_alias"
    out1_2c = run_cmd([str(bin_2c)]).stdout.strip()
    d_file_2c = next((pkg_2c / "target" / "debug" / "build").rglob("cksum_alias*.d"))
    d_text_2c = d_file_2c.read_text()

    # Run second build with `-Z checksum-freshness`
    build2_2c = run_cmd(
        ["cargo", "build", "-Z", "checksum-freshness", "--config", 'build.fingerprint="content"', "-v"],
        cwd=pkg_2c,
    )
    out2_2c = run_cmd([str(bin_2c)]).stdout.strip()

    results["2c_non_canonical_path_aliasing_poisoning"] = {
        "binary_after_build1": out1_2c,
        "on_disk_main_after_build1": "CODE_V2_UPDATED" if "CODE_V2_UPDATED" in main_2c.read_text() else "CODE_V1",
        "dep_info_checksum_lines": [
            line for line in d_text_2c.splitlines() if line.startswith("# checksum:")
        ],
        "build2_rebuilt": "Compiling cksum_alias" in build2_2c.stderr,
        "binary_after_build2": out2_2c,
        "stale_binary_permanently_cached": (
            out2_2c == "CODE_V1" and "CODE_V2_UPDATED" in main_2c.read_text()
        ),
    }
    return results


# ==============================================================================
# Probe 3: GNU Make Classic Mid-Build Mtime Poisoning (t_read < t_edit < t_output)
# ==============================================================================
def probe_3_make_mid_build_poisoning(tmp_root: Path) -> dict:
    make_dir = tmp_root / "make_probe"
    make_dir.mkdir(parents=True)
    main_rs = make_dir / "main.rs"
    gate_rs = make_dir / "gate.rs"
    makefile = make_dir / "Makefile"

    main_rs.write_text('mod gate;\nfn main() { println!("MAKE_V1"); }\n')
    os.mkfifo(gate_rs)
    makefile.write_text(
        "app: main.rs gate.rs\n"
        "\trustc main.rs -o app\n"
    )

    def writer_make():
        with open(gate_rs, "w") as fifo:
            time.sleep(0.05)
            main_rs.write_text('mod gate;\nfn main() { println!("MAKE_V2"); }\n')
            fifo.write("pub const G: u32 = 1;\n")
            fifo.flush()
        st = main_rs.stat()
        gate_rs.unlink()
        gate_rs.write_text("pub const G: u32 = 1;\n")
        os.utime(gate_rs, ns=(st.st_atime_ns, st.st_mtime_ns))

    t = threading.Thread(target=writer_make)
    t.start()
    make1 = run_cmd(["make"], cwd=make_dir)
    t.join()

    app_bin = make_dir / "app"
    out1 = run_cmd([str(app_bin)]).stdout.strip()
    main_mtime_ns = main_rs.stat().st_mtime_ns
    app_mtime_ns = app_bin.stat().st_mtime_ns

    make2 = run_cmd(["make"], cwd=make_dir)
    out2 = run_cmd([str(app_bin)]).stdout.strip()

    return {
        "make_version": run_cmd(["make", "--version"]).stdout.splitlines()[0],
        "binary_after_make1": out1,
        "on_disk_after_make1": "MAKE_V2" if "MAKE_V2" in main_rs.read_text() else "MAKE_V1",
        "main_rs_mtime_ns": main_mtime_ns,
        "app_output_mtime_ns": app_mtime_ns,
        "input_older_than_output": main_mtime_ns < app_mtime_ns,
        "make2_stdout": make2.stdout.strip(),
        "binary_after_make2": out2,
        "stale_binary_permanently_cached": (
            "is up to date" in make2.stdout and out2 == "MAKE_V1"
        ),
    }


# ==============================================================================
# Probe 4: `rustc_driver` Source-Binding Verification Patterns (Patterns 1..5)
# ==============================================================================
DRIVER_PROBE_RS = r"""// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Config, Compiler};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::{FileLoader, RealFileLoader};
use rustc_span::FileName;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// Simple FNV-1a 64-bit hash (for standalone zero-dependency probing in rustc_private).
fn hash_bytes(bytes: &[u8]) -> String {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("{:016x}:{:x}", h, bytes.len())
}

fn hash_file_disk(path: &Path) -> io::Result<String> {
    let bytes = fs::read(path)?;
    Ok(hash_bytes(&bytes))
}

/// Pattern 4: In-process RecordingFileLoader enforcing:
/// 1. Explicit allowlist of canonical paths (or staging root).
/// 2. Canonical-path single-hash invariant (rejects if two reads of the same canonical path
///    return different bytes, e.g. via non-canonical `./lib.rs` vs `lib.rs` aliases).
/// 3. `(st_dev, st_ino)` inode single-hash invariant (rejects if two hardlinks to the same
///    underlying inode return different bytes across reads!).
#[derive(Default, Debug)]
struct LoaderState {
    by_canon_path: BTreeMap<PathBuf, String>,
    by_inode: BTreeMap<(u64, u64), (PathBuf, String)>,
    violations: Vec<String>,
}

struct RecordingFileLoader {
    allowlist: BTreeSet<PathBuf>,
    state: Arc<Mutex<LoaderState>>,
    on_first_lib_read: Option<Box<dyn Fn() + Send + Sync>>,
}

impl RecordingFileLoader {
    fn record_and_verify(&self, path: &Path, bytes: &[u8]) -> io::Result<()> {
        let canon = fs::canonicalize(path)?;
        let meta = fs::metadata(path)?;
        let inode_key = (meta.dev(), meta.ino());
        let digest = hash_bytes(bytes);

        let mut st = self.state.lock().unwrap();
        if !self.allowlist.is_empty() && !self.allowlist.contains(&canon) {
            st.violations.push(format!("Unallowed path read: {}", canon.display()));
        }
        if let Some(prev) = st.by_canon_path.get(&canon).cloned() {
            if prev != digest {
                st.violations.push(format!(
                    "Canonical-path hash mismatch on {}: first={}, second={}",
                    canon.display(),
                    prev,
                    digest
                ));
            }
        } else {
            st.by_canon_path.insert(canon.clone(), digest.clone());
        }

        if let Some((prev_path, prev_digest)) = st.by_inode.get(&inode_key).cloned() {
            if prev_digest != digest {
                st.violations.push(format!(
                    "Hardlink/inode ({:?}) hash mismatch between {} ({}) and {} ({})",
                    inode_key,
                    prev_path.display(),
                    prev_digest,
                    canon.display(),
                    digest
                ));
            }
        } else {
            st.by_inode.insert(inode_key, (canon, digest));
        }
        Ok(())
    }
}

impl FileLoader for RecordingFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        RealFileLoader.file_exists(path)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        // Read via a single file descriptor and fstat that exact descriptor
        use std::io::Read;
        let mut f = fs::File::open(path)?;
        let mut buf = String::new();
        f.read_to_string(&mut buf)?;
        self.record_and_verify(path, buf.as_bytes())?;
        if path.file_name().and_then(|s| s.to_str()) == Some("lib.rs") {
            if let Some(cb) = &self.on_first_lib_read {
                cb();
            }
        }
        Ok(buf)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        let bytes = RealFileLoader.read_binary_file(path)?;
        self.record_and_verify(path, &bytes)?;
        Ok(bytes)
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

/// Pattern 5: Pure In-Memory Preloaded VirtualFileLoader.
/// Reads all declared files into memory once before `compiler_entrypoint` and never touches the disk
/// during compilation.
struct PreloadedFileLoader {
    files: BTreeMap<PathBuf, Arc<[u8]>>,
    on_first_lib_read: Option<Box<dyn Fn() + Send + Sync>>,
}

impl PreloadedFileLoader {
    fn lookup(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        let canon = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        self.files
            .get(&canon)
            .cloned()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, format!("Not in VFS: {}", path.display())))
    }
}

impl FileLoader for PreloadedFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        self.lookup(path).is_ok()
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        let bytes = self.lookup(path)?;
        let s = std::str::from_utf8(&bytes)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
            .to_owned();
        if path.file_name().and_then(|s| s.to_str()) == Some("lib.rs") {
            if let Some(cb) = &self.on_first_lib_read {
                cb();
            }
        }
        Ok(s)
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        self.lookup(path)
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        RealFileLoader.current_directory()
    }
}

struct ExtractConstCallbacks {
    extracted_val: Arc<Mutex<Option<String>>>,
    audit_violations: Arc<Mutex<Vec<String>>>,
    loader_state: Option<Arc<Mutex<LoaderState>>>,
}

impl Callbacks for ExtractConstCallbacks {
    fn config(&mut self, _config: &mut Config) {}

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // Inspect the compiled crate's top-level const `VERSION_ID: u32` via HIR/ConstEval
        for id in tcx.hir_free_items() {
            let def_id = id.owner_id.def_id.to_def_id();
            if tcx.opt_item_name(def_id).is_some_and(|s| s.as_str() == "VERSION_ID") {
                if let Ok(val) = tcx.const_eval_poly(def_id) {
                    if let Some(scalar) = val.try_to_scalar_int() {
                        *self.extracted_val.lock().unwrap() = Some(format!("{}", scalar));
                    }
                }
            }
        }

        // Pattern 4 post-analysis session audit:
        if let Some(state_arc) = &self.loader_state {
            let st = state_arc.lock().unwrap();
            let mut violations = self.audit_violations.lock().unwrap();
            violations.extend(st.violations.clone());

            // 1. Every local file in SourceMap must appear in `by_canon_path`
            let sm = tcx.sess.source_map();
            for sf in sm.files().iter() {
                if sf.cnum != rustc_span::def_id::LOCAL_CRATE {
                    continue;
                }
                if let FileName::Real(real_name) = &sf.name {
                    if let Some(local_path) = real_name.local_path() {
                        match fs::canonicalize(local_path) {
                            Ok(canon) => {
                                let sm_hash = sf.src.as_ref().map(|s| hash_bytes(s.as_bytes()));
                                match (st.by_canon_path.get(&canon), sm_hash) {
                                    (Some(recorded), Some(in_sm)) if recorded != &in_sm => {
                                        violations.push(format!(
                                            "SourceMap content hash mismatch for {}: loader={}, sm={}",
                                            canon.display(),
                                            recorded,
                                            in_sm
                                        ));
                                    }
                                    (None, _) => {
                                        violations.push(format!(
                                            "SourceMap file missing from FileLoader table: {}",
                                            canon.display()
                                        ));
                                    }
                                    _ => {}
                                }
                            }
                            Err(e) => violations.push(format!("Cannot canonicalize {}: {}", local_path.display(), e)),
                        }
                    }
                }
            }

            // 2. Every path in `tcx.sess.file_depinfo` (`proc_macro::tracked::path`)
            //    must be in `by_canon_path`!
            for sym in tcx.sess.file_depinfo.borrow().iter() {
                let p = PathBuf::from(sym.as_str());
                match fs::canonicalize(&p) {
                    Ok(canon) => {
                        if !st.by_canon_path.contains_key(&canon) {
                            violations.push(format!(
                                "file_depinfo tracked_path bypassed FileLoader: {}",
                                canon.display()
                            ));
                        }
                    }
                    Err(e) => {
                        violations.push(format!("file_depinfo path unreadable {}: {}", p.display(), e));
                    }
                }
            }

            // 3. `env_depinfo` must be empty
            if !tcx.sess.env_depinfo.borrow().is_empty() {
                violations.push("Non-empty env_depinfo detected".to_string());
            }
        }

        Compilation::Stop
    }
}

fn sysroot() -> String {
    let out = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("all");
    let work_dir = PathBuf::from(args.get(2).expect("work_dir required"));
    fs::create_dir_all(&work_dir).unwrap();
    let sr = sysroot();

    match mode {
        "pattern1_pre_hash" => {
            // Pattern 1: External Pre-Hash Only (vulnerable to edit between t_pre and t_read)
            let lib_rs = work_dir.join("lib.rs");
            fs::write(&lib_rs, "pub const VERSION_ID: u32 = 101;\n").unwrap();
            let _pre_hash = hash_file_disk(&lib_rs).unwrap();

            // Concurrent edit happens AFTER pre_hash (t_pre) but BEFORE rustc reads lib.rs (t_read)
            fs::write(&lib_rs, "pub const VERSION_ID: u32 = 202;\n").unwrap();

            let extracted = Arc::new(Mutex::new(None));
            let mut cb = ExtractConstCallbacks {
                extracted_val: extracted.clone(),
                audit_violations: Arc::new(Mutex::new(Vec::new())),
                loader_state: None,
            };
            let rustc_args = vec![
                "rustc".to_string(),
                "--crate-type=lib".to_string(),
                format!("--sysroot={}", sr),
                lib_rs.to_string_lossy().to_string(),
            ];
            let _ = rustc_driver::catch_fatal_errors(|| {
                rustc_driver::compiler_entrypoint(&rustc_args, &mut cb);
            });
            let compiled_val = extracted.lock().unwrap().clone().unwrap_or_default();
            println!(
                "{{\"pattern\":\"1_pre_hash_only\",\"pre_hash_version\":\"101\",\"compiled_version\":\"{}\",\"soundness_broken\":{}}}",
                compiled_val,
                compiled_val == "202"
            );
        }
        "pattern2_post_hash" => {
            // Pattern 2: External Post-Hash Only (vulnerable to edit between t_read and t_post)
            let lib_rs = work_dir.join("lib.rs");
            fs::write(&lib_rs, "pub const VERSION_ID: u32 = 101;\n").unwrap();

            let lib_rs_clone = lib_rs.clone();
            let loader = RecordingFileLoader {
                allowlist: BTreeSet::new(),
                state: Arc::new(Mutex::new(LoaderState::default())),
                on_first_lib_read: Some(Box::new(move || {
                    // Modify lib.rs immediately AFTER rustc reads Version 101, BEFORE post_hash!
                    fs::write(&lib_rs_clone, "pub const VERSION_ID: u32 = 202;\n").unwrap();
                })),
            };

            let extracted = Arc::new(Mutex::new(None));
            struct PostHashCallbacks {
                extracted: Arc<Mutex<Option<String>>>,
                loader: Option<RecordingFileLoader>,
            }
            impl Callbacks for PostHashCallbacks {
                fn config(&mut self, config: &mut Config) {
                    config.file_loader = Some(Box::new(self.loader.take().unwrap()));
                }
                fn after_analysis<'tcx>(&mut self, _c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
                    for id in tcx.hir_free_items() {
                        let def_id = id.owner_id.def_id.to_def_id();
                        if tcx.opt_item_name(def_id).is_some_and(|s| s.as_str() == "VERSION_ID") {
                            if let Ok(val) = tcx.const_eval_poly(def_id) {
                                if let Some(s) = val.try_to_scalar_int() {
                                    *self.extracted.lock().unwrap() = Some(format!("{}", s));
                                }
                            }
                        }
                    }
                    Compilation::Stop
                }
            }
            let mut cb = PostHashCallbacks {
                extracted: extracted.clone(),
                loader: Some(loader),
            };
            let rustc_args = vec![
                "rustc".to_string(),
                "--crate-type=lib".to_string(),
                format!("--sysroot={}", sr),
                lib_rs.to_string_lossy().to_string(),
            ];
            let _ = rustc_driver::catch_fatal_errors(|| {
                rustc_driver::compiler_entrypoint(&rustc_args, &mut cb);
            });
            let post_hash = hash_file_disk(&lib_rs).unwrap();
            let v202_hash = hash_bytes(b"pub const VERSION_ID: u32 = 202;\n");
            let compiled_val = extracted.lock().unwrap().clone().unwrap_or_default();
            println!(
                "{{\"pattern\":\"2_post_hash_only\",\"post_hash_matches_202\":{},\"compiled_version\":\"{}\",\"soundness_broken\":{}}}",
                post_hash == v202_hash,
                compiled_val,
                compiled_val == "101" && post_hash == v202_hash
            );
        }
        "pattern3_aba" => {
            // Pattern 3: External Pre-Hash == Post-Hash WITHOUT In-Process FileLoader
            // Vulnerable to ABA race: disk starts at A (101) -> switches to B (202) before t_read
            // -> switches back to A (101) before t_post!
            let lib_rs = work_dir.join("lib.rs");
            let v101 = "pub const VERSION_ID: u32 = 101;\n";
            let v202 = "pub const VERSION_ID: u32 = 202;\n";
            fs::write(&lib_rs, v101).unwrap();
            let pre_hash = hash_file_disk(&lib_rs).unwrap();

            // Mutate to B (202) before rustc reads lib.rs
            fs::write(&lib_rs, v202).unwrap();

            let lib_rs_clone = lib_rs.clone();
            let loader = RecordingFileLoader {
                allowlist: BTreeSet::new(),
                state: Arc::new(Mutex::new(LoaderState::default())),
                on_first_lib_read: Some(Box::new(move || {
                    // Revert disk back to A (101) right after rustc reads B (202)!
                    fs::write(&lib_rs_clone, v101).unwrap();
                })),
            };
            let extracted = Arc::new(Mutex::new(None));
            struct AbaCallbacks {
                extracted: Arc<Mutex<Option<String>>>,
                loader: Option<RecordingFileLoader>,
            }
            impl Callbacks for AbaCallbacks {
                fn config(&mut self, config: &mut Config) {
                    config.file_loader = Some(Box::new(self.loader.take().unwrap()));
                }
                fn after_analysis<'tcx>(&mut self, _c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
                    for id in tcx.hir_free_items() {
                        let def_id = id.owner_id.def_id.to_def_id();
                        if tcx.opt_item_name(def_id).is_some_and(|s| s.as_str() == "VERSION_ID") {
                            if let Ok(val) = tcx.const_eval_poly(def_id) {
                                if let Some(s) = val.try_to_scalar_int() {
                                    *self.extracted.lock().unwrap() = Some(format!("{}", s));
                                }
                            }
                        }
                    }
                    Compilation::Stop
                }
            }
            let mut cb = AbaCallbacks {
                extracted: extracted.clone(),
                loader: Some(loader),
            };
            let rustc_args = vec![
                "rustc".to_string(),
                "--crate-type=lib".to_string(),
                format!("--sysroot={}", sr),
                lib_rs.to_string_lossy().to_string(),
            ];
            let _ = rustc_driver::catch_fatal_errors(|| {
                rustc_driver::compiler_entrypoint(&rustc_args, &mut cb);
            });
            let post_hash = hash_file_disk(&lib_rs).unwrap();
            let compiled_val = extracted.lock().unwrap().clone().unwrap_or_default();
            println!(
                "{{\"pattern\":\"3_pre_eq_post_without_fileloader\",\"pre_eq_post\":{},\"verified_hash_version\":\"101\",\"compiled_version\":\"{}\",\"aba_bypass_succeeded\":{}}}",
                pre_hash == post_hash,
                compiled_val,
                (pre_hash == post_hash) && compiled_val == "202"
            );
        }
        "pattern4_aba_caught" | "pattern4_alias_caught" | "pattern4_hardlink_caught" => {
            // Pattern 4: In-process RecordingFileLoader + canonical-path & (st_dev, st_ino)
            // single-hash invariant + post-analysis SourceMap/depinfo audit + disk hash check.
            let lib_rs = work_dir.join("lib.rs");
            let v101_alias = "pub const VERSION_ID: u32 = 101;\npub const SELF_STR: &str = include_str!(\"./lib.rs\");\n";
            let v202_alias = "pub const VERSION_ID: u32 = 202;\npub const SELF_STR: &str = include_str!(\"./lib.rs\");\n";

            let hardlink_rs = work_dir.join("hardlink_lib.rs");
            let _ = fs::remove_file(&hardlink_rs);
            let v101_hl = "pub const VERSION_ID: u32 = 101;\npub const HL_STR: &str = include_str!(\"hardlink_lib.rs\");\n";
            let v202_hl = "pub const VERSION_ID: u32 = 202;\npub const HL_STR: &str = include_str!(\"hardlink_lib.rs\");\n";

            if mode == "pattern4_aba_caught" {
                fs::write(&lib_rs, v101_alias).unwrap();
            } else if mode == "pattern4_alias_caught" {
                fs::write(&lib_rs, v101_alias).unwrap();
            } else {
                fs::write(&lib_rs, v101_hl).unwrap();
                fs::hard_link(&lib_rs, &hardlink_rs).unwrap();
            }

            let canon_lib = fs::canonicalize(&lib_rs).unwrap();
            let mut allowlist = BTreeSet::new();
            allowlist.insert(canon_lib.clone());
            if mode == "pattern4_hardlink_caught" {
                allowlist.insert(fs::canonicalize(&hardlink_rs).unwrap());
            }

            let pre_hash = hash_file_disk(&lib_rs).unwrap();
            if mode == "pattern4_aba_caught" {
                // ABA: mutate to v202 before rustc reads
                fs::write(&lib_rs, v202_alias).unwrap();
            }

            let lib_rs_clone = lib_rs.clone();
            let mode_str = mode.to_string();
            let state = Arc::new(Mutex::new(LoaderState::default()));
            let state_clone = state.clone();

            let loader = RecordingFileLoader {
                allowlist,
                state: state.clone(),
                on_first_lib_read: Some(Box::new(move || {
                    if mode_str == "pattern4_aba_caught" {
                        // Revert back to v101 after first read
                        fs::write(&lib_rs_clone, v101_alias).unwrap();
                    } else if mode_str == "pattern4_alias_caught" {
                        // Mutate lib.rs before `include_str!("./lib.rs")` executes!
                        fs::write(&lib_rs_clone, v202_alias).unwrap();
                    } else if mode_str == "pattern4_hardlink_caught" {
                        // Modify the shared inode in-place before `include_str!("hardlink_lib.rs")` executes!
                        // Note: canonicalize(lib.rs) != canonicalize(hardlink_lib.rs), so ONLY the
                        // (st_dev, st_ino) check catches this mid-compile mutation!
                        fs::write(&lib_rs_clone, v202_hl).unwrap();
                    }
                })),
            };

            let extracted = Arc::new(Mutex::new(None));
            let violations = Arc::new(Mutex::new(Vec::new()));
            struct P4Callbacks {
                inner: ExtractConstCallbacks,
                loader: Option<RecordingFileLoader>,
            }
            impl Callbacks for P4Callbacks {
                fn config(&mut self, config: &mut Config) {
                    config.file_loader = Some(Box::new(self.loader.take().unwrap()));
                }
                fn after_analysis<'tcx>(&mut self, c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
                    self.inner.after_analysis(c, tcx)
                }
            }
            let mut cb = P4Callbacks {
                inner: ExtractConstCallbacks {
                    extracted_val: extracted.clone(),
                    audit_violations: violations.clone(),
                    loader_state: Some(state_clone),
                },
                loader: Some(loader),
            };
            let rustc_args = vec![
                "rustc".to_string(),
                "--crate-type=lib".to_string(),
                format!("--sysroot={}", sr),
                lib_rs.to_string_lossy().to_string(),
            ];
            let _ = rustc_driver::catch_fatal_errors(|| {
                rustc_driver::compiler_entrypoint(&rustc_args, &mut cb);
            });

            // Also verify pre_hash == in_memory_hash == post_hash
            let post_hash = hash_file_disk(&lib_rs).unwrap();
            let st = state.lock().unwrap();
            let mut all_violations = violations.lock().unwrap().clone();
            if let Some(mem_hash) = st.by_canon_path.get(&canon_lib) {
                if mem_hash != &pre_hash {
                    all_violations.push(format!(
                        "Pre-hash != in-memory FileLoader hash: pre={}, mem={}",
                        pre_hash, mem_hash
                    ));
                }
                if mem_hash != &post_hash {
                    all_violations.push(format!(
                        "Post-hash != in-memory FileLoader hash: post={}, mem={}",
                        post_hash, mem_hash
                    ));
                }
            }

            println!(
                "{{\"mode\":\"{}\",\"rejected\":{},\"violations\":{:?}}}",
                mode,
                !all_violations.is_empty(),
                all_violations
            );
        }
        "pattern5_vfs_immune" => {
            // Pattern 5: Preloaded in-memory VirtualFileLoader
            let lib_rs = work_dir.join("lib.rs");
            let v101 = "pub const VERSION_ID: u32 = 101;\npub const SELF_STR: &str = include_str!(\"./lib.rs\");\n";
            let v202 = "pub const VERSION_ID: u32 = 202;\npub const SELF_STR: &str = include_str!(\"./lib.rs\");\n";
            fs::write(&lib_rs, v101).unwrap();
            let canon_lib = fs::canonicalize(&lib_rs).unwrap();

            // Snapshot into memory BEFORE compilation
            let mut vfs_map = BTreeMap::new();
            let raw_bytes: Arc<[u8]> = Arc::from(fs::read(&canon_lib).unwrap().into_boxed_slice());
            let vfs_digest = hash_bytes(&raw_bytes);
            vfs_map.insert(canon_lib.clone(), raw_bytes);

            // Now mutate disk BEFORE and DURING compilation!
            fs::write(&lib_rs, v202).unwrap();
            let lib_rs_clone = lib_rs.clone();
            let loader = PreloadedFileLoader {
                files: vfs_map,
                on_first_lib_read: Some(Box::new(move || {
                    fs::write(&lib_rs_clone, "pub const VERSION_ID: u32 = 303;\n").unwrap();
                })),
            };

            let extracted = Arc::new(Mutex::new(None));
            struct P5Callbacks {
                extracted: Arc<Mutex<Option<String>>>,
                loader: Option<PreloadedFileLoader>,
                sm_hashes: Arc<Mutex<Vec<String>>>,
            }
            impl Callbacks for P5Callbacks {
                fn config(&mut self, config: &mut Config) {
                    config.file_loader = Some(Box::new(self.loader.take().unwrap()));
                }
                fn after_analysis<'tcx>(&mut self, _c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
                    for id in tcx.hir_free_items() {
                        let def_id = id.owner_id.def_id.to_def_id();
                        if tcx.opt_item_name(def_id).is_some_and(|s| s.as_str() == "VERSION_ID") {
                            if let Ok(val) = tcx.const_eval_poly(def_id) {
                                if let Some(s) = val.try_to_scalar_int() {
                                    *self.extracted.lock().unwrap() = Some(format!("{}", s));
                                }
                            }
                        }
                    }
                    for sf in tcx.sess.source_map().files().iter() {
                        if sf.cnum == rustc_span::def_id::LOCAL_CRATE {
                            if let Some(src) = &sf.src {
                                self.sm_hashes.lock().unwrap().push(hash_bytes(src.as_bytes()));
                            }
                        }
                    }
                    Compilation::Stop
                }
            }
            let sm_hashes = Arc::new(Mutex::new(Vec::new()));
            let mut cb = P5Callbacks {
                extracted: extracted.clone(),
                loader: Some(loader),
                sm_hashes: sm_hashes.clone(),
            };
            let rustc_args = vec![
                "rustc".to_string(),
                "--crate-type=lib".to_string(),
                format!("--sysroot={}", sr),
                lib_rs.to_string_lossy().to_string(),
            ];
            let _ = rustc_driver::catch_fatal_errors(|| {
                rustc_driver::compiler_entrypoint(&rustc_args, &mut cb);
            });
            let compiled_val = extracted.lock().unwrap().clone().unwrap_or_default();
            let hashes = sm_hashes.lock().unwrap().clone();
            let all_match_vfs = hashes.iter().all(|h| h == &vfs_digest);
            println!(
                "{{\"mode\":\"pattern5_vfs_immune\",\"compiled_version\":\"{}\",\"source_map_files_count\":{},\"all_sourcemap_entries_match_vfs_snapshot\":{}}}",
                compiled_val,
                hashes.len(),
                all_match_vfs && compiled_val == "101"
            );
        }
        _ => panic!("Unknown mode: {}", mode),
    }
}
"""


def probe_4_rustc_driver_patterns(tmp_root: Path) -> dict:
    drv_dir = tmp_root / "driver_probe"
    drv_dir.mkdir(parents=True)
    src_file = drv_dir / "driver_probe.rs"
    bin_file = drv_dir / "driver_probe"
    src_file.write_text(DRIVER_PROBE_RS)

    sysroot = run_cmd(["rustc", "--print", "sysroot"]).stdout.strip()
    lib_dir = f"{sysroot}/lib"

    # Compile custom rustc_driver wrapper binary
    run_cmd(
        [
            "rustc",
            "--edition=2021",
            "-C",
            f"link-args=-Wl,-rpath,{lib_dir}",
            str(src_file),
            "-o",
            str(bin_file),
        ],
        env={"RUSTC_BOOTSTRAP": "1"},
    )

    modes = [
        "pattern1_pre_hash",
        "pattern2_post_hash",
        "pattern3_aba",
        "pattern4_aba_caught",
        "pattern4_alias_caught",
        "pattern4_hardlink_caught",
        "pattern5_vfs_immune",
    ]
    results = {}
    for m in modes:
        sub_work = drv_dir / m
        out = run_cmd([str(bin_file), m, str(sub_work)]).stdout.strip()
        results[m] = json.loads(out)

    # Also test the untracked proc-macro `std::fs::read` gap:
    # A proc-macro that calls `std::fs::read("untracked_secret.txt")` WITHOUT calling
    # `proc_macro::tracked_path::path` leaves NO entry in `SourceMap` and NO entry in
    # `tcx.sess.psess.file_depinfo`.
    pm_dir = drv_dir / "untracked_pm_gap"
    pm_dir.mkdir(parents=True)
    pm_src = pm_dir / "pm.rs"
    pm_src.write_text(
        'extern crate proc_macro;\n'
        'use proc_macro::TokenStream;\n'
        '#[proc_macro]\n'
        'pub fn read_untracked(input: TokenStream) -> TokenStream {\n'
        '    let path = input.to_string().trim_matches(\'"\').to_string();\n'
        '    let secret = std::fs::read_to_string(&path).unwrap();\n'
        '    format!("pub const VERSION_ID: u32 = {};", secret.trim()).parse().unwrap()\n'
        '}\n'
    )
    run_cmd(
        [
            "rustc",
            "--crate-type=proc-macro",
            "--edition=2021",
            str(pm_src),
            "-o",
            str(pm_dir / "libpm.so"),
        ]
    )
    secret_file = pm_dir / "untracked_secret.txt"
    secret_file.write_text("999\n")
    app_rs = pm_dir / "lib.rs"
    app_rs.write_text(
        f'extern crate pm;\npm::read_untracked!("{secret_file}");\n'
    )
    # Run rustc with `--emit=dep-info` and inspect whether `untracked_secret.txt` appears in `.d`
    dep_out = pm_dir / "lib.d"
    run_cmd(
        [
            "rustc",
            "--crate-type=lib",
            "--edition=2021",
            "--extern",
            f"pm={pm_dir / 'libpm.so'}",
            "--emit=dep-info",
            str(app_rs),
            "-o",
            str(dep_out),
        ]
    )
    dep_contents = dep_out.read_text()
    results["pattern4_untracked_proc_macro_gap"] = {
        "secret_file_in_rustc_dep_info": "untracked_secret.txt" in dep_contents,
        "dep_info_contents": dep_contents.strip(),
        "explanation": (
            "A proc-macro runs in-process (or via proc_macro_srv) with full ambient host "
            "filesystem access and calls std::fs::read directly without calling "
            "proc_macro::tracked_path::path, bypassing both Config::file_loader (SourceMap) "
            "and Session::file_depinfo."
        ),
    }

    return results


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="track3_probes_") as tmp:
        tmp_root = Path(tmp)
        print("[1/4] Running Probe 1: Cargo Default Mtime Freshness...")
        p1 = probe_1_cargo_mtime(tmp_root)
        print("[2/4] Running Probe 2: Cargo -Z checksum-freshness...")
        p2 = probe_2_cargo_checksum_freshness(tmp_root)
        print("[3/4] Running Probe 3: GNU Make Mid-Build Mtime Poisoning...")
        p3 = probe_3_make_mid_build_poisoning(tmp_root)
        print("[4/4] Running Probe 4: rustc_driver Source-Binding Verification Patterns...")
        p4 = probe_4_rustc_driver_patterns(tmp_root)

    summary = {
        "environment": {
            "rustc_version": run_cmd(["rustc", "--version", "--verbose"]).stdout.strip(),
            "cargo_version": run_cmd(["cargo", "--version", "--verbose"]).stdout.strip(),
            "local_rust_checkout_head": "49d734536222bf28bb6d07d885b3a81d145981da",
            "local_rust_cargo_submodule_commit": "3c0b534756e166d12eb9fd2e1abfe5b42ac6101e",
        },
        "probe_1_cargo_mtime": p1,
        "probe_2_cargo_checksum_freshness": p2,
        "probe_3_make_mid_build_poisoning": p3,
        "probe_4_rustc_driver_verification_patterns": p4,
    }

    out_json = OUT_DIR / "cargo_and_driver_probe_results.json"
    out_json.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"\nSaved probe results to {out_json}")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
