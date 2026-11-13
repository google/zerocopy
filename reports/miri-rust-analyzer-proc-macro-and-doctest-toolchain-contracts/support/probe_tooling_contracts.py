#!/usr/bin/env python3
"""
Extract and empirically probe C7: Miri, rust-analyzer, proc-macro, and doctest integration at Rust 1.99.1.
1. Miri (`src/tools/miri` in s1991):
   - Parse `extern crate rustc_*` in `src/tools/miri/src/lib.rs` and `cargo-miri/src/setup.rs`.
   - Extract Miri CLI flags (`-Zmiri-*`), aliasing models (Stacked Borrows vs Tree Borrows), data-race / weak-memory / GenMC support.
   - Count Miri test suite files (`src/tools/miri/tests/{pass,fail,panic,pass-dep,fail-dep,genmc}`).
2. rust-analyzer (`src/tools/rust-analyzer` in s1991):
   - Inspect `crates/project-model/src/{sysroot.rs, workspace.rs, build_dependencies.rs}` and `crates/proc-macro-srv` / `crates/proc-macro-api`.
   - Extract the proc-macro server protocol version (`CURRENT_API_VERSION` in `crates/proc-macro-api/src/version.rs` or `legacy_protocol`).
3. Proc macros (`compiler/rustc_expand/src/proc_macro_server.rs`, `library/proc_macro/src/bridge/`):
   - Extract `proc_macro::bridge` ABI structures, `__rustc_proc_macro_decls_*` symbol generation, version check, and Cranelift/GCC proc-macro support.
4. Doctests (`src/librustdoc/doctest.rs`):
   - Inspect `--test-builder`, `--test-args`, and how `rustdoc --test` invokes `rustc` (and empirically run `rustdoc +1.99.1 --test -Zunstable-options --test-builder ...`).
"""
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

RUST_S1991 = Path("./rust-1.99.1")
OUT_DIR = Path("/tmp/reval")
OUT_DIR.mkdir(parents=True, exist_ok=True)
TMP_DIR = Path("/tmp/reval")
os.environ["TMPDIR"] = str(TMP_DIR)

def inspect_miri():
    miri_dir = RUST_S1991 / "src/tools/miri"
    rustc_crates = set()
    zmiri_flags = set()
    for root, _, files in os.walk(miri_dir):
        for fn in files:
            if not fn.endswith(".rs"):
                continue
            p = Path(root) / fn
            t = p.read_text(errors="ignore")
            for m in re.finditer(r'extern\s+crate\s+(rustc_[a-z0-9_]+)', t):
                rustc_crates.add(m.group(1))
            for m in re.finditer(r'"(-Zmiri-[a-z0-9_-]+)"', t):
                zmiri_flags.add(m.group(1))

    # Count test files per subdir
    test_counts = {}
    tdir = miri_dir / "tests"
    if tdir.exists():
        for sub in sorted(tdir.iterdir()):
            if sub.is_dir():
                rs_files = list(sub.rglob("*.rs"))
                test_counts[sub.name] = len(rs_files)

    # Check cargo-miri setup.rs for flags passed when building sysroot
    setup_files = list((miri_dir / "cargo-miri").rglob("*.rs"))
    setup_snippets = {}
    for sf in setup_files:
        t = sf.read_text(errors="ignore")
        if "always-encode-mir" in t or "miri" in t:
            setup_snippets[str(sf.relative_to(RUST_S1991))] = [
                f"L{i+1}: {line.strip()}"
                for i, line in enumerate(t.splitlines())
                if any(k in line for k in ["always-encode-mir", "RUSTFLAGS", "--cfg", "Xargo", "sysroot"])
            ]

    return {
        "rustc_private_crates": sorted(rustc_crates),
        "zmiri_flags": sorted(zmiri_flags),
        "test_suite_counts": test_counts,
        "total_test_files": sum(test_counts.values()),
        "cargo_miri_setup_lines": setup_snippets,
    }

def inspect_rust_analyzer():
    ra_dir = RUST_S1991 / "src/tools/rust-analyzer"
    info = {}
    for rel in [
        "crates/project-model/src/sysroot.rs",
        "crates/project-model/src/workspace.rs",
        "crates/project-model/src/rustc_cfg.rs",
        "crates/proc-macro-api/src/version.rs",
        "crates/proc-macro-api/src/lib.rs",
        "crates/proc-macro-srv/src/lib.rs",
        "crates/proc-macro-srv-cli/src/main.rs",
    ]:
        p = ra_dir / rel
        if p.exists():
            t = p.read_text(errors="ignore")
            info[rel] = {
                "lines": len(t.splitlines()),
                "head": "\n".join(t.splitlines()[:80]),
            }
    return info

def inspect_proc_macro_and_doctest():
    res = {}
    for rel in [
        "library/proc_macro/src/bridge/mod.rs",
        "library/proc_macro/src/bridge/client.rs",
        "library/proc_macro/src/bridge/server.rs",
        "compiler/rustc_expand/src/proc_macro_server.rs",
        "compiler/rustc_metadata/src/DynamicLibrary.rs",
        "compiler/rustc_metadata/src/creader.rs",
        "src/librustdoc/doctest.rs",
        "src/librustdoc/config.rs",
    ]:
        p = RUST_S1991 / rel
        if p.exists():
            t = p.read_text(errors="ignore")
            res[rel] = {
                "lines": len(t.splitlines()),
                "matches": [
                    f"L{i+1}: {line.strip()}"
                    for i, line in enumerate(t.splitlines())
                    if any(k in line for k in ["proc_macro_decls", "test_builder", "test-builder", "BridgeConfig", "run_client", "API_VERSION"])
                ][:50]
            }

    # Empirical probe of rustdoc --test --test-builder with a wrapper
    with tempfile.TemporaryDirectory(dir=TMP_DIR) as wd:
        wd_p = Path(wd)
        src = wd_p / "lib.rs"
        src.write_text('/// ```\n/// assert_eq!(1 + 1, 2);\n/// ```\npub fn demo() {}\n')
        log_f = wd_p / "doctest_builder.json"
        wrapper = wd_p / "fake_builder.py"
        wrapper.write_text(f"""#!/usr/bin/env python3
import json, os, sys
with open({repr(str(log_f))}, "a") as f:
    f.write(json.dumps({{"args": sys.argv[1:]}}) + "\\n")
os.execvp("rustc", ["rustc", "+1.99.1"] + sys.argv[1:])
""")
        wrapper.chmod(0o755)
        p = subprocess.run(
            ["rustdoc", "+1.99.1", "-Zunstable-options", "--test", f"--test-builder={wrapper}", str(src)],
            cwd=wd, env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, capture_output=True, text=True
        )
        res["doctest_probe"] = {
            "rc": p.returncode,
            "stdout": p.stdout.strip(),
            "stderr": p.stderr.strip(),
            "captured_invocations": [
                json.loads(l) for l in log_f.read_text().splitlines()
            ] if log_f.exists() else []
        }

    return res

if __name__ == "__main__":
    out = {
        "miri": inspect_miri(),
        "rust_analyzer": inspect_rust_analyzer(),
        "proc_macro_and_doctest": inspect_proc_macro_and_doctest(),
    }
    (OUT_DIR / "c7_extracted.json").write_text(json.dumps(out, indent=2))
    print("C7 extraction complete: miri crates=", len(out["miri"]["rustc_private_crates"]), "miri tests=", out["miri"]["total_test_files"])
