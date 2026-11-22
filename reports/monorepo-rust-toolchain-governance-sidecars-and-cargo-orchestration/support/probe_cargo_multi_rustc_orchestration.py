#!/usr/bin/env python3
"""Empirical probe for multi-version Cargo workspace orchestration.

Tests three experimental axes across installed Rustup toolchains without network
access or global toolchain mutation:
  1. `cargo` orchestrator vs. `RUSTC` compiler decoupling on `Cargo.lock` v4
     workspaces containing `edition = "2024"` sibling crates, MSRV validation
     against `RUSTC -vV`, and the `rustc 1.80.0` `--check-cfg` CLI flag floor.
  2. `RUSTC` vs. `RUSTC_WRAPPER` vs. `RUSTC_WORKSPACE_WRAPPER` invocation matrix
     across probes, primary crates, workspace path deps, external deps, and host
     `proc-macro` / `build.rs` units (with and without `--target` and
     `-Z target-applies-to-host`), plus ABI failure modes when wrappers alter or
     halt host codegen.
  3. Concurrent multi-compiler (`subprocess.Popen`) verification against a
     single `chmod -R a-w` read-only workspace source tree, plus unit
     fingerprint cache-skip traps (`RUSTC_WRAPPER` post-hoc attachment, wrapper
     mtime edits, unhashed `MY_VERIFIER_ARGS`) and deterministic cache-busting
     remedies.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import textwrap
import time
from typing import Any


HOST_TRIPLE = "x86_64-unknown-linux-gnu"

CANDIDATE_TOOLCHAINS = [
    f"1.61.0-{HOST_TRIPLE}",
    f"1.78.0-{HOST_TRIPLE}",
    f"1.79.0-{HOST_TRIPLE}",
    f"1.80-{HOST_TRIPLE}",
    f"1.83.0-{HOST_TRIPLE}",
    f"1.84.0-{HOST_TRIPLE}",
    f"1.93.1-{HOST_TRIPLE}",
    f"1.100.0-{HOST_TRIPLE}",
    f"nightly-2026-11-20-{HOST_TRIPLE}",
]


def scrubbed_env(extra: dict[str, str | None] | None = None) -> dict[str, str]:
    """Return an environment scrubbed of ambient rustup/cargo overrides."""
    env = dict(os.environ)
    for k in list(env.keys()):
        if (
            k.startswith("RUSTUP_")
            or k.startswith("CARGO_")
            or k in {
                "RUSTC",
                "RUSTDOC",
                "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER",
                "RUSTFLAGS",
                "RUSTDOCFLAGS",
                "LD_LIBRARY_PATH",
                "DYLD_LIBRARY_PATH",
            }
        ):
            env.pop(k, None)
    if extra:
        for k, v in extra.items():
            if v is None:
                env.pop(k, None)
            else:
                env[k] = v
    return env


def parse_vv(vv_text: str) -> dict[str, str]:
    info: dict[str, str] = {}
    lines = [ln.strip() for ln in vv_text.strip().splitlines() if ln.strip()]
    if lines:
        info["headline"] = lines[0]
    for ln in lines[1:]:
        if ": " in ln:
            k, v = ln.split(": ", 1)
            info[k] = v
    return info


def discover_toolchains() -> dict[str, dict[str, Any]]:
    toolchains_root = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup")) / "toolchains"
    found: dict[str, dict[str, Any]] = {}
    for tc in CANDIDATE_TOOLCHAINS:
        tc_dir = toolchains_root / tc
        rustc_bin = tc_dir / "bin" / "rustc"
        cargo_bin = tc_dir / "bin" / "cargo"
        if rustc_bin.is_file() and cargo_bin.is_file():
            r_vv = subprocess.run(
                [str(rustc_bin), "-vV"],
                env=scrubbed_env(),
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            c_vv = subprocess.run(
                [str(cargo_bin), "-vV"],
                env=scrubbed_env(),
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            found[tc] = {
                "dir": str(tc_dir),
                "rustc": str(rustc_bin),
                "cargo": str(cargo_bin),
                "rustc_vv": parse_vv(r_vv),
                "cargo_vv": parse_vv(c_vv),
            }
    return found


def write_text(path: Path, content: str, executable: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(content).lstrip(), encoding="utf-8")
    if executable:
        path.chmod(0o755)


def create_multi_crate_fixture(
    base_dir: Path, cargo_1_100: str, rustc_1_100: str, include_2024_sibling: bool = True
) -> dict[str, Path]:
    """Create an offline multi-crate workspace with Cargo.lock version = 4."""
    ext_dir = base_dir / "external" / "ext_dep"
    write_text(
        ext_dir / "Cargo.toml",
        """
        [package]
        name = "ext_dep"
        version = "0.1.0"
        edition = "2021"
        rust-version = "1.60"
        build = "build.rs"
        """,
    )
    write_text(
        ext_dir / "build.rs",
        """
        fn main() {
            println!("cargo:rerun-if-changed=build.rs");
            if let Ok(out) = std::env::var("PROBE_BUILD_ENV_LOG") {
                let line = format!(
                    "pkg=ext_dep|RUSTC={}|RUSTC_WRAPPER={}|RUSTC_WORKSPACE_WRAPPER={}|RUSTFLAGS={}|CARGO_ENCODED_RUSTFLAGS={}\\n",
                    std::env::var("RUSTC").unwrap_or_default(),
                    std::env::var("RUSTC_WRAPPER").unwrap_or_default(),
                    std::env::var("RUSTC_WORKSPACE_WRAPPER").unwrap_or_default(),
                    std::env::var("RUSTFLAGS").unwrap_or_default(),
                    std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default(),
                );
                let _ = std::fs::OpenOptions::new().create(true).append(true).open(out)
                    .and_then(|mut f| std::io::Write::write_all(&mut f, line.as_bytes()));
            }
        }
        """,
    )
    write_text(
        ext_dir / "src" / "lib.rs",
        """
        pub fn ext_val() -> i32 {
            10
        }
        """,
    )

    ws_dir = base_dir / ("ws" if include_2024_sibling else "ws_no_2024")
    members = [
        '"crate_msrv"',
        '"my_proc_macro"',
        '"ws_lib_dep"',
        '"dep_with_build_rs"',
    ]
    if include_2024_sibling:
        members.insert(1, '"crate_2024_sibling"')

    write_text(
        ws_dir / "Cargo.toml",
        f"""
        [workspace]
        resolver = "2"
        members = [{", ".join(members)}]
        """,
    )

    write_text(
        ws_dir / "my_proc_macro" / "Cargo.toml",
        """
        [package]
        name = "my_proc_macro"
        version = "0.1.0"
        edition = "2021"
        rust-version = "1.78"

        [lib]
        proc-macro = true
        """,
    )
    write_text(
        ws_dir / "my_proc_macro" / "src" / "lib.rs",
        """
        use proc_macro::TokenStream;

        #[proc_macro]
        pub fn answer_macro(_input: TokenStream) -> TokenStream {
            "27".parse().unwrap()
        }
        """,
    )

    write_text(
        ws_dir / "ws_lib_dep" / "Cargo.toml",
        """
        [package]
        name = "ws_lib_dep"
        version = "0.1.0"
        edition = "2021"
        rust-version = "1.78"
        """,
    )
    write_text(
        ws_dir / "ws_lib_dep" / "src" / "lib.rs",
        """
        pub fn ws_val() -> i32 {
            5
        }
        """,
    )

    write_text(
        ws_dir / "dep_with_build_rs" / "Cargo.toml",
        """
        [package]
        name = "dep_with_build_rs"
        version = "0.1.0"
        edition = "2021"
        rust-version = "1.78"
        build = "build.rs"
        """,
    )
    write_text(
        ws_dir / "dep_with_build_rs" / "build.rs",
        """
        fn main() {
            println!("cargo:rerun-if-changed=build.rs");
            println!("cargo:rustc-cfg=from_ws_build_rs");
            if let Ok(out) = std::env::var("PROBE_BUILD_ENV_LOG") {
                let line = format!(
                    "pkg=dep_with_build_rs|RUSTC={}|RUSTC_WRAPPER={}|RUSTC_WORKSPACE_WRAPPER={}|RUSTFLAGS={}|CARGO_ENCODED_RUSTFLAGS={}\\n",
                    std::env::var("RUSTC").unwrap_or_default(),
                    std::env::var("RUSTC_WRAPPER").unwrap_or_default(),
                    std::env::var("RUSTC_WORKSPACE_WRAPPER").unwrap_or_default(),
                    std::env::var("RUSTFLAGS").unwrap_or_default(),
                    std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default(),
                );
                let _ = std::fs::OpenOptions::new().create(true).append(true).open(out)
                    .and_then(|mut f| std::io::Write::write_all(&mut f, line.as_bytes()));
            }
        }
        """,
    )
    write_text(
        ws_dir / "dep_with_build_rs" / "src" / "lib.rs",
        """
        #[cfg(from_ws_build_rs)]
        pub fn build_val() -> i32 {
            100
        }
        """,
    )

    write_text(
        ws_dir / "crate_msrv" / "Cargo.toml",
        """
        [package]
        name = "crate_msrv"
        version = "0.1.0"
        edition = "2021"
        rust-version = "1.78"

        [dependencies]
        my_proc_macro = { path = "../my_proc_macro" }
        ws_lib_dep = { path = "../ws_lib_dep" }
        dep_with_build_rs = { path = "../dep_with_build_rs" }
        ext_dep = { path = "../../external/ext_dep" }
        """,
    )
    write_text(
        ws_dir / "crate_msrv" / "src" / "lib.rs",
        """
        pub fn total() -> i32 {
            my_proc_macro::answer_macro!()
                + ws_lib_dep::ws_val()
                + dep_with_build_rs::build_val()
                + ext_dep::ext_val()
        }
        """,
    )

    if include_2024_sibling:
        write_text(
            ws_dir / "crate_2024_sibling" / "Cargo.toml",
            """
            [package]
            name = "crate_2024_sibling"
            version = "0.1.0"
            edition = "2024"
            rust-version = "1.85"
            """,
        )
        write_text(
            ws_dir / "crate_2024_sibling" / "src" / "lib.rs",
            """
            pub fn sibling_2024() -> usize {
                42
            }
            """,
        )

    # Generate Cargo.lock with cargo 1.100.0 and verify version = 4.
    # Note: ResolveVersion::with_rust_version uses ws.lowest_rust_version()
    # (1.78 -> V3 by default unless Cargo.lock is already V4 or no rust-version
    # < 1.83). Force version = 4 explicitly if needed so we test true V4 lockfiles!
    subprocess.run(
        [cargo_1_100, "generate-lockfile", "--offline"],
        cwd=ws_dir,
        env=scrubbed_env({"RUSTC": rustc_1_100}),
        capture_output=True,
        text=True,
        check=True,
    )
    lock_path = ws_dir / "Cargo.lock"
    lock_text = lock_path.read_text(encoding="utf-8")
    natural_lock_header = [
        ln for ln in lock_text.splitlines() if ln.startswith("version =")
    ]
    # Upgrade header to version = 4 if ws.lowest_rust_version() selected version = 3!
    if "version = 3\n" in lock_text:
        lock_text = lock_text.replace("version = 3\n", "version = 4\n", 1)
        lock_path.write_text(lock_text, encoding="utf-8")

    assert "version = 4" in lock_path.read_text(encoding="utf-8")
    return {
        "ws_dir": ws_dir,
        "ext_dir": ext_dir,
        "natural_lock_header": natural_lock_header[0] if natural_lock_header else "",
    }


WRAPPER_SCRIPT = r"""#!/usr/bin/env python3
import hashlib
import json
import os
import subprocess
import sys

def main() -> int:
    role = os.environ.get("PROBE_WRAPPER_ROLE", "wrapper")
    log_path = os.environ.get("PROBE_WRAPPER_LOG", "")
    mode = os.environ.get("PROBE_WRAPPER_MODE", "passthrough")
    strip_check_cfg = os.environ.get("PROBE_STRIP_CHECK_CFG", "0") == "1"
    strip_1_79_json_unused = os.environ.get("PROBE_STRIP_1_79_JSON_UNUSED", "0") == "1"
    append_vv_nonce = os.environ.get("PROBE_APPEND_VV_NONCE", "0") == "1"
    verifier_args = os.environ.get("MY_VERIFIER_ARGS", "")

    # Identify real rustc vs chained inner wrapper:
    # argv[1] is either inner_wrapper or rustc; remaining args follow.
    sub_prog = sys.argv[1]
    raw_args = sys.argv[2:]

    is_vv = "-vV" in raw_args or ("--version" in raw_args and "--verbose" in raw_args)
    prints = [a.split("=", 1)[1] for a in raw_args if a.startswith("--print=")]
    for i, a in enumerate(raw_args[:-1]):
        if a == "--print":
            prints.append(raw_args[i + 1])
    is_print = len(prints) > 0

    crate_name = None
    crate_types = []
    target_flag = None
    has_ambient_cfg = False
    for i, a in enumerate(raw_args):
        if a == "--crate-name" and i + 1 < len(raw_args):
            crate_name = raw_args[i + 1]
        elif a.startswith("--crate-name="):
            crate_name = a.split("=", 1)[1]
        elif a == "--crate-type" and i + 1 < len(raw_args):
            crate_types.append(raw_args[i + 1])
        elif a.startswith("--crate-type="):
            crate_types.append(a.split("=", 1)[1])
        elif a == "--target" and i + 1 < len(raw_args):
            target_flag = raw_args[i + 1]
        elif a.startswith("--target="):
            target_flag = a.split("=", 1)[1]
        elif a == "--cfg=from_ambient_rustflags" or (
            a == "from_ambient_rustflags" and i > 0 and raw_args[i - 1] == "--cfg"
        ):
            has_ambient_cfg = True

    is_host_unit = ("proc-macro" in crate_types) or (crate_name == "build_script_build")
    has_primary = os.environ.get("CARGO_PRIMARY_PACKAGE") == "1"

    record = {
        "role": role,
        "sub_prog": os.path.basename(sub_prog),
        "is_probe_vV": is_vv,
        "is_probe_print": is_print,
        "prints": prints,
        "crate_name": crate_name,
        "crate_types": crate_types,
        "has_primary_pkg": has_primary,
        "has_target_flag": target_flag is not None,
        "target_flag": target_flag,
        "has_ambient_rustflag": has_ambient_cfg,
        "cargo_pkg_name": os.environ.get("CARGO_PKG_NAME"),
        "verifier_args": verifier_args,
        "pid": os.getpid(),
    }
    if log_path:
        with open(log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record) + "\n")

    forward_args = list(raw_args)
    if strip_check_cfg:
        cleaned = []
        skip_next = False
        for a in forward_args:
            if skip_next:
                skip_next = False
                continue
            if a == "--check-cfg":
                skip_next = True
                continue
            if a.startswith("--check-cfg="):
                continue
            cleaned.append(a)
        forward_args = cleaned

    if strip_1_79_json_unused:
        cleaned2 = []
        for a in forward_args:
            if a.startswith("--json="):
                parts = [p for p in a.split("=", 1)[1].split(",") if not p.startswith("unused-externs")]
                cleaned2.append("--json=" + ",".join(parts))
            elif a == "--force-warn=unused_crate_dependencies":
                continue
            else:
                cleaned2.append(a)
        forward_args = cleaned2

    if is_vv:
        res = subprocess.run([sub_prog, *forward_args], capture_output=True, text=True)
        sys.stderr.write(res.stderr)
        out = res.stdout
        if append_vv_nonce:
            digest = hashlib.sha256(verifier_args.encode("utf-8")).hexdigest()[:16]
            out = out.rstrip("\n") + f"\nverifier-args-digest: {digest}\n"
        sys.stdout.write(out)
        return res.returncode

    if is_print:
        res = subprocess.run([sub_prog, *forward_args], close_fds=False)
        return res.returncode

    def replace_emit(args_list: list[str], new_emit: str) -> list[str]:
        out = []
        skip = False
        for item in args_list:
            if skip:
                skip = False
                continue
            if item == "--emit":
                skip = True
                continue
            if item.startswith("--emit="):
                continue
            out.append(item)
        out.append(f"--emit={new_emit}")
        return out

    # Non-probe crate compilation modes for Experiment 2b:
    if mode == "force_emit_metadata_all":
        forward_args = replace_emit(forward_args, "dep-info,metadata")
    elif mode == "force_emit_metadata_skip_build_rs":
        if crate_name != "build_script_build":
            forward_args = replace_emit(forward_args, "dep-info,metadata")
    elif mode == "inject_unstable_z_flag_all":
        forward_args.append("-Zmir-preserve-ub")
    elif mode == "inject_unstable_z_flag_target_only":
        if not is_host_unit:
            forward_args.append("-Zmir-preserve-ub")
    elif mode == "stop_on_proc_macro":
        if "proc-macro" in crate_types:
            return 0
    elif mode == "stop_on_build_rs":
        if crate_name == "build_script_build":
            return 0
    elif mode == "stop_on_ws_lib_dep":
        if crate_name == "ws_lib_dep":
            return 0
    elif mode == "stop_on_primary_only":
        if has_primary and not is_host_unit:
            return 0
    elif mode == "host_passthrough_target_continue":
        if not is_host_unit:
            receipt_dir = os.environ.get("PROBE_MIR_RECEIPT_DIR", "")
            if receipt_dir:
                os.makedirs(receipt_dir, exist_ok=True)
                with open(os.path.join(receipt_dir, f"{crate_name}.mir.json"), "w", encoding="utf-8") as rf:
                    json.dump(
                        {
                            "crate_name": crate_name,
                            "primary": has_primary,
                            "verifier_args": verifier_args,
                        },
                        rf,
                    )

    res = subprocess.run([sub_prog, *forward_args], close_fds=False)
    return res.returncode

if __name__ == "__main__":
    sys.exit(main())
"""


def sanitize_paths(text: str, tmp: Path | None = None) -> str:
    rustup_home = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup"))
    if tmp is not None:
        text = text.replace(str(tmp), "<TMPDIR>")
    text = text.replace(str(rustup_home), "<RUSTUP_HOME>")
    text = text.replace(str(Path.home()), "<HOME>")
    return text


def first_error_lines(stderr: str, max_lines: int = 6, tmp: Path | None = None) -> str:
    cleaned = [
        sanitize_paths(ln.strip(), tmp)
        for ln in stderr.strip().splitlines()
        if ln.strip()
        and not ln.lstrip().startswith(("Compiling ", "Checking ", "Building ", "Locking "))
    ]
    err_focused = [
        ln
        for ln in cleaned
        if ln.startswith(("error", "Caused by:", "could not ", "No such file", "lock file", "feature "))
        or "can't find crate" in ln
        or "proc-macro" in ln
        or "Unrecognized" in ln
        or "unstable-options" in ln
    ]
    chosen = err_focused if err_focused else cleaned
    return " | ".join(chosen[:max_lines])


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    return [
        json.loads(ln)
        for ln in path.read_text(encoding="utf-8").splitlines()
        if ln.strip()
    ]


def set_tree_readonly(root: Path, readonly: bool) -> None:
    if readonly:
        for dirpath, dirnames, filenames in os.walk(root, topdown=False):
            for fn in filenames:
                p = Path(dirpath) / fn
                p.chmod(stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
            Path(dirpath).chmod(
                stat.S_IRUSR | stat.S_IXUSR | stat.S_IRGRP | stat.S_IXGRP | stat.S_IROTH | stat.S_IXOTH
            )
    else:
        for dirpath, dirnames, filenames in os.walk(root, topdown=True):
            Path(dirpath).chmod(0o755)
            for fn in filenames:
                (Path(dirpath) / fn).chmod(0o644)


def run_experiment_1(
    tmp: Path, toolchains: dict[str, dict[str, Any]], fixture_2024: dict[str, Path], fixture_no_2024: dict[str, Path]
) -> dict[str, Any]:
    cargo_1_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["cargo"]
    wrapper_bin = tmp / "wrappers" / "strip_wrapper.py"
    write_text(wrapper_bin, WRAPPER_SCRIPT, executable=True)

    exp1a_ws_2024: dict[str, Any] = {}
    exp1a_ws_v4_only: dict[str, Any] = {}
    for tc, info in toolchains.items():
        tdir1 = tmp / "exp1a_2024" / tc
        r1 = subprocess.run(
            [info["cargo"], "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir1)],
            cwd=fixture_2024["ws_dir"],
            env=scrubbed_env({"RUSTC": info["rustc"]}),
            capture_output=True,
            text=True,
        )
        exp1a_ws_2024[tc] = {
            "returncode": r1.returncode,
            "summary": "ok" if r1.returncode == 0 else first_error_lines(r1.stderr),
        }

        tdir2 = tmp / "exp1a_v4_only" / tc
        r2 = subprocess.run(
            [info["cargo"], "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir2)],
            cwd=fixture_no_2024["ws_dir"],
            env=scrubbed_env({"RUSTC": info["rustc"]}),
            capture_output=True,
            text=True,
        )
        exp1a_ws_v4_only[tc] = {
            "returncode": r2.returncode,
            "summary": "ok" if r2.returncode == 0 else first_error_lines(r2.stderr),
        }

    # 1b: Modern cargo 1.100.0 driving older RUSTC binaries on ws (Cargo.lock v4 + edition = "2024" sibling)
    exp1b_decoupled_direct: dict[str, Any] = {}
    exp1c_decoupled_strip_check_cfg: dict[str, Any] = {}
    for tc, info in toolchains.items():
        log_file = tmp / "exp1b_logs" / f"{tc}.jsonl"
        log_file.parent.mkdir(parents=True, exist_ok=True)
        tdir = tmp / "exp1b_direct" / tc
        r = subprocess.run(
            [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir)],
            cwd=fixture_2024["ws_dir"],
            env=scrubbed_env(
                {
                    "RUSTC": info["rustc"],
                    "RUSTC_WRAPPER": str(wrapper_bin),
                    "PROBE_WRAPPER_LOG": str(log_file),
                }
            ),
            capture_output=True,
            text=True,
        )
        recs = read_jsonl(log_file)
        compiled_crates = [x["crate_name"] for x in recs if not x["is_probe_vV"] and not x["is_probe_print"]]
        exp1b_decoupled_direct[tc] = {
            "rustc_release": info["rustc_vv"].get("release"),
            "returncode": r.returncode,
            "compiled_crates": compiled_crates,
            "summary": "ok" if r.returncode == 0 else first_error_lines(r.stderr),
        }

        if r.returncode != 0:
            log_strip = tmp / "exp1c_logs" / f"{tc}.jsonl"
            log_strip.parent.mkdir(parents=True, exist_ok=True)
            tdir_s = tmp / "exp1c_strip" / tc
            rs = subprocess.run(
                [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir_s)],
                cwd=fixture_2024["ws_dir"],
                env=scrubbed_env(
                    {
                        "RUSTC": info["rustc"],
                        "RUSTC_WRAPPER": str(wrapper_bin),
                        "PROBE_WRAPPER_LOG": str(log_strip),
                        "PROBE_STRIP_CHECK_CFG": "1",
                    }
                ),
                capture_output=True,
                text=True,
            )
            recs_s = read_jsonl(log_strip)
            exp1c_decoupled_strip_check_cfg[tc] = {
                "rustc_release": info["rustc_vv"].get("release"),
                "returncode": rs.returncode,
                "compiled_crates": [
                    x["crate_name"] for x in recs_s if not x["is_probe_vV"] and not x["is_probe_print"]
                ],
                "summary": "ok" if rs.returncode == 0 else first_error_lines(rs.stderr, tmp=tmp),
            }
            if tc.startswith("1.78."):
                log_s2 = tmp / "exp1c_logs" / f"{tc}_full_shim.jsonl"
                tdir_s2 = tmp / "exp1c_strip_full" / tc
                rs2 = subprocess.run(
                    [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir_s2)],
                    cwd=fixture_2024["ws_dir"],
                    env=scrubbed_env(
                        {
                            "RUSTC": info["rustc"],
                            "RUSTC_WRAPPER": str(wrapper_bin),
                            "PROBE_WRAPPER_LOG": str(log_s2),
                            "PROBE_STRIP_CHECK_CFG": "1",
                            "PROBE_STRIP_1_79_JSON_UNUSED": "1",
                        }
                    ),
                    capture_output=True,
                    text=True,
                )
                recs_s2 = read_jsonl(log_s2)
                exp1c_decoupled_strip_check_cfg[f"{tc}_plus_strip_json_unused_externs"] = {
                    "rustc_release": info["rustc_vv"].get("release"),
                    "returncode": rs2.returncode,
                    "compiled_crates": [
                        x["crate_name"] for x in recs_s2 if not x["is_probe_vV"] and not x["is_probe_print"]
                    ],
                    "summary": "ok" if rs2.returncode == 0 else first_error_lines(rs2.stderr, tmp=tmp),
                }

    # 1d: MSRV validation source of truth: cargo 1.100.0 with RUSTC=1.80.1 checking crate_msrv (1.78)
    # vs crate_2024_sibling (rust-version = 1.85), plus a 2021-edition crate with rust-version = 1.85
    rustc_1_80 = toolchains[f"1.80-{HOST_TRIPLE}"]["rustc"]
    msrv_fail_run = subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_2024_sibling",
            "--frozen",
            "--target-dir",
            str(tmp / "exp1d_msrv_fail"),
        ],
        cwd=fixture_2024["ws_dir"],
        env=scrubbed_env({"RUSTC": rustc_1_80}),
        capture_output=True,
        text=True,
    )
    # Also test --ignore-rust-version with RUSTC=1.84.0 on crate_2024_sibling (hits edition 2024 rustc gate)
    rustc_1_84 = toolchains[f"1.84.0-{HOST_TRIPLE}"]["rustc"]
    msrv_ignore_run = subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_2024_sibling",
            "--frozen",
            "--ignore-rust-version",
            "--target-dir",
            str(tmp / "exp1d_msrv_ignore"),
        ],
        cwd=fixture_2024["ws_dir"],
        env=scrubbed_env({"RUSTC": rustc_1_84}),
        capture_output=True,
        text=True,
    )

    return {
        "natural_lockfile_version_with_msrv_1_78": fixture_2024["natural_lock_header"],
        "exp1a_native_cargo_on_v4_plus_2024_sibling": exp1a_ws_2024,
        "exp1a_native_cargo_on_v4_without_2024_sibling": exp1a_ws_v4_only,
        "exp1b_cargo_1_100_driving_older_rustc_direct": exp1b_decoupled_direct,
        "exp1c_cargo_1_100_driving_pre_1_80_rustc_with_check_cfg_stripped": exp1c_decoupled_strip_check_cfg,
        "exp1d_msrv_validation_against_rustc_vv": {
            "cargo_1_100_with_rustc_1_80_on_pkg_msrv_1_85": {
                "returncode": msrv_fail_run.returncode,
                "summary": first_error_lines(msrv_fail_run.stderr),
            },
            "cargo_1_100_with_rustc_1_84_and_ignore_rust_version_on_2024_crate": {
                "returncode": msrv_ignore_run.returncode,
                "summary": first_error_lines(msrv_ignore_run.stderr),
            },
        },
    }


def run_experiment_2(
    tmp: Path, toolchains: dict[str, dict[str, Any]], fixture_2024: dict[str, Path]
) -> dict[str, Any]:
    cargo_1_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["cargo"]
    rustc_1_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["rustc"]
    cargo_nightly = toolchains[f"nightly-2026-11-20-{HOST_TRIPLE}"]["cargo"]
    rustc_nightly = toolchains[f"nightly-2026-11-20-{HOST_TRIPLE}"]["rustc"]

    outer_wrapper = tmp / "wrappers" / "outer_rustc_wrapper.py"
    inner_ws_wrapper = tmp / "wrappers" / "inner_ws_wrapper.py"
    write_text(outer_wrapper, WRAPPER_SCRIPT, executable=True)
    write_text(inner_ws_wrapper, WRAPPER_SCRIPT, executable=True)

    ws_dir = fixture_2024["ws_dir"]

    matrix_cases = [
        ("rustc_wrapper_no_target", cargo_1_100, rustc_1_100, [], {"RUSTC_WRAPPER": str(outer_wrapper), "PROBE_WRAPPER_ROLE": "RUSTC_WRAPPER"}),
        ("ws_wrapper_no_target", cargo_1_100, rustc_1_100, [], {"RUSTC_WORKSPACE_WRAPPER": str(inner_ws_wrapper), "PROBE_WRAPPER_ROLE": "RUSTC_WORKSPACE_WRAPPER"}),
        ("ws_wrapper_with_target", cargo_1_100, rustc_1_100, ["--target", HOST_TRIPLE], {"RUSTC_WORKSPACE_WRAPPER": str(inner_ws_wrapper), "PROBE_WRAPPER_ROLE": "RUSTC_WORKSPACE_WRAPPER"}),
        (
            "both_wrappers_with_target",
            cargo_1_100,
            rustc_1_100,
            ["--target", HOST_TRIPLE],
            {
                "RUSTC_WRAPPER": str(outer_wrapper),
                "RUSTC_WORKSPACE_WRAPPER": str(inner_ws_wrapper),
            },
        ),
        (
            "ambient_rustflags_no_target_default_applies_to_host",
            cargo_1_100,
            rustc_1_100,
            [],
            {
                "RUSTC_WRAPPER": str(outer_wrapper),
                "CARGO_ENCODED_RUSTFLAGS": "--cfg=from_ambient_rustflags",
            },
        ),
        (
            "ambient_rustflags_with_explicit_target",
            cargo_1_100,
            rustc_1_100,
            ["--target", HOST_TRIPLE],
            {
                "RUSTC_WRAPPER": str(outer_wrapper),
                "CARGO_ENCODED_RUSTFLAGS": "--cfg=from_ambient_rustflags",
            },
        ),
        (
            "nightly_target_applies_to_host_false_no_target",
            cargo_nightly,
            rustc_nightly,
            ["-Z", "target-applies-to-host", "--config", "target-applies-to-host=false"],
            {
                "RUSTC_WRAPPER": str(outer_wrapper),
                "CARGO_ENCODED_RUSTFLAGS": "--cfg=from_ambient_rustflags",
            },
        ),
    ]

    invocation_matrix: dict[str, Any] = {}
    for name, c_bin, r_bin, extra_cli, env_overrides in matrix_cases:
        log_path = tmp / "exp2a_logs" / f"{name}.jsonl"
        build_env_log = tmp / "exp2a_logs" / f"{name}.build_env.txt"
        log_path.parent.mkdir(parents=True, exist_ok=True)
        tdir = tmp / "exp2a_targets" / name
        env = scrubbed_env(
            {
                "RUSTC": r_bin,
                "PROBE_WRAPPER_LOG": str(log_path),
                "PROBE_BUILD_ENV_LOG": str(build_env_log),
                **env_overrides,
            }
        )
        res = subprocess.run(
            [c_bin, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir), *extra_cli],
            cwd=ws_dir,
            env=env,
            capture_output=True,
            text=True,
        )
        recs = read_jsonl(log_path)
        build_env_lines = (
            [sanitize_paths(ln, tmp) for ln in build_env_log.read_text(encoding="utf-8").strip().splitlines()]
            if build_env_log.exists()
            else []
        )
        invocation_matrix[name] = {
            "returncode": res.returncode,
            "invocations": [
                {
                    "sub_prog": r["sub_prog"],
                    "is_probe_vV": r["is_probe_vV"],
                    "is_probe_print": r["is_probe_print"],
                    "crate_name": r["crate_name"],
                    "crate_types": r["crate_types"],
                    "has_primary_pkg": r["has_primary_pkg"],
                    "has_target_flag": r["has_target_flag"],
                    "target_flag": r["target_flag"],
                    "has_ambient_rustflag": r["has_ambient_rustflag"],
                }
                for r in recs
            ],
            "build_script_runtime_env": build_env_lines,
        }

    # Experiment 2b: Proc-macro & build.rs ABI survival modes under RUSTC_WORKSPACE_WRAPPER
    abi_modes = [
        ("force_emit_metadata_all", cargo_1_100, rustc_1_100),
        ("force_emit_metadata_skip_build_rs", cargo_1_100, rustc_1_100),
        ("inject_unstable_z_flag_all_stable", cargo_1_100, rustc_1_100),
        ("inject_unstable_z_flag_target_only_nightly", cargo_nightly, rustc_nightly),
        ("stop_on_build_rs", cargo_1_100, rustc_1_100),
        ("stop_on_proc_macro", cargo_1_100, rustc_1_100),
        ("stop_on_ws_lib_dep", cargo_1_100, rustc_1_100),
        ("stop_on_primary_only", cargo_1_100, rustc_1_100),
        ("host_passthrough_target_continue", cargo_1_100, rustc_1_100),
    ]
    abi_results: dict[str, Any] = {}
    for label, c_bin, r_bin in abi_modes:
        mode_val = (
            "inject_unstable_z_flag_all"
            if label == "inject_unstable_z_flag_all_stable"
            else (
                "inject_unstable_z_flag_target_only"
                if label == "inject_unstable_z_flag_target_only_nightly"
                else label
            )
        )
        tdir = tmp / "exp2b_targets" / label
        receipt_dir = tmp / "exp2b_receipts" / label
        res = subprocess.run(
            [c_bin, "check", "-p", "crate_msrv", "--frozen", "--target", HOST_TRIPLE, "--target-dir", str(tdir)],
            cwd=ws_dir,
            env=scrubbed_env(
                {
                    "RUSTC": r_bin,
                    "RUSTC_WORKSPACE_WRAPPER": str(inner_ws_wrapper),
                    "PROBE_WRAPPER_MODE": mode_val,
                    "PROBE_MIR_RECEIPT_DIR": str(receipt_dir),
                }
            ),
            capture_output=True,
            text=True,
        )
        receipts = sorted(p.name for p in receipt_dir.glob("*.mir.json")) if receipt_dir.exists() else []
        second_run_crates = None
        if label == "stop_on_primary_only" and res.returncode == 0:
            recheck_log = tmp / "exp2b_logs" / "stop_primary_recheck.jsonl"
            recheck_log.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [c_bin, "check", "-p", "crate_msrv", "--frozen", "--target", HOST_TRIPLE, "--target-dir", str(tdir)],
                cwd=ws_dir,
                env=scrubbed_env(
                    {
                        "RUSTC": r_bin,
                        "RUSTC_WORKSPACE_WRAPPER": str(inner_ws_wrapper),
                        "PROBE_WRAPPER_MODE": mode_val,
                        "PROBE_WRAPPER_LOG": str(recheck_log),
                    }
                ),
                capture_output=True,
                text=True,
            )
            second_run_crates = [
                r["crate_name"]
                for r in read_jsonl(recheck_log)
                if not r["is_probe_vV"] and not r["is_probe_print"]
            ]
        abi_results[label] = {
            "returncode": res.returncode,
            "mir_receipts": receipts,
            "second_incremental_run_compiled_crates": second_run_crates,
            "summary": "ok" if res.returncode == 0 else first_error_lines(res.stderr, max_lines=6, tmp=tmp),
        }

    return {
        "exp2a_invocation_matrix": invocation_matrix,
        "exp2b_proc_macro_and_build_rs_abi_survival": abi_results,
    }


def run_experiment_3(
    tmp: Path, toolchains: dict[str, dict[str, Any]], fixture_2024: dict[str, Path]
) -> dict[str, Any]:
    cargo_1_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["cargo"]
    ws_dir = fixture_2024["ws_dir"]
    ext_dir = fixture_2024["ext_dir"].parent

    ws_wrapper = tmp / "wrappers" / "exp3_ws_wrapper.py"
    rustc_wrapper = tmp / "wrappers" / "exp3_rustc_wrapper.py"
    write_text(ws_wrapper, WRAPPER_SCRIPT, executable=True)
    write_text(rustc_wrapper, WRAPPER_SCRIPT, executable=True)

    concurrent_tcs = [
        f"1.84.0-{HOST_TRIPLE}",
        f"1.93.1-{HOST_TRIPLE}",
        f"1.100.0-{HOST_TRIPLE}",
        f"nightly-2026-11-20-{HOST_TRIPLE}",
    ]

    concurrent_outcomes: dict[str, Any] = {}
    set_tree_readonly(ws_dir, True)
    set_tree_readonly(ext_dir, True)
    try:
        procs: list[tuple[str, subprocess.Popen[str], Path, Path]] = []
        t0 = time.monotonic()
        for tc in concurrent_tcs:
            r_bin = toolchains[tc]["rustc"]
            tdir = tmp / "exp3a_concurrent" / tc
            rdir = tmp / "exp3a_receipts" / tc
            logf = tmp / "exp3a_logs" / f"{tc}.jsonl"
            logf.parent.mkdir(parents=True, exist_ok=True)
            p = subprocess.Popen(
                [
                    cargo_1_100,
                    "check",
                    "-p",
                    "crate_msrv",
                    "--frozen",
                    "--target",
                    HOST_TRIPLE,
                    "--target-dir",
                    str(tdir),
                ],
                cwd=ws_dir,
                env=scrubbed_env(
                    {
                        "RUSTC": r_bin,
                        "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                        "PROBE_WRAPPER_MODE": "host_passthrough_target_continue",
                        "PROBE_MIR_RECEIPT_DIR": str(rdir),
                        "PROBE_WRAPPER_LOG": str(logf),
                        "MY_VERIFIER_ARGS": f"compiler={tc}",
                    }
                ),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            procs.append((tc, p, rdir, tdir))

        for tc, p, rdir, tdir in procs:
            out, err = p.communicate(timeout=60)
            rustc_info_exists = (tdir / ".rustc_info.json").is_file()
            receipts = sorted(x.name for x in rdir.glob("*.mir.json")) if rdir.exists() else []
            concurrent_outcomes[tc] = {
                "returncode": p.returncode,
                "rustc_info_cached": rustc_info_exists,
                "mir_receipts": receipts,
                "stderr_summary": "ok" if p.returncode == 0 else first_error_lines(err),
            }
        wall_sec = round(time.monotonic() - t0, 3)
    finally:
        set_tree_readonly(ws_dir, False)
        set_tree_readonly(ext_dir, False)

    # Experiment 3b: Fingerprint cache-skip traps and cache-busting remedies
    rustc_1_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["rustc"]

    # Trap 1: Plain cargo check -> attach RUSTC_WRAPPER on warm target-dir
    tdir_trap1 = tmp / "exp3b_trap_rustc_wrapper"
    subprocess.run(
        [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir_trap1)],
        cwd=ws_dir,
        env=scrubbed_env({"RUSTC": rustc_1_100}),
        capture_output=True,
        text=True,
        check=True,
    )
    trap1_log = tmp / "exp3b_logs" / "trap1_rustc_wrapper.jsonl"
    trap1_log.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir_trap1)],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WRAPPER": str(rustc_wrapper),
                "PROBE_WRAPPER_LOG": str(trap1_log),
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )
    trap1_recs = read_jsonl(trap1_log)

    # Contrast: attach RUSTC_WORKSPACE_WRAPPER onto the SAME warm target-dir!
    trap1_ws_log = tmp / "exp3b_logs" / "trap1_ws_wrapper.jsonl"
    subprocess.run(
        [cargo_1_100, "check", "-p", "crate_msrv", "--frozen", "--target-dir", str(tdir_trap1)],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(trap1_ws_log),
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )
    trap1_ws_recs = read_jsonl(trap1_ws_log)

    # Trap 2: Unhashed MY_VERIFIER_ARGS change AND wrapper mtime bump on warm target-dir
    tdir_trap2 = tmp / "exp3b_trap_env_and_mtime"
    log_v1 = tmp / "exp3b_logs" / "v1.jsonl"
    subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_msrv",
            "--frozen",
            "--target",
            HOST_TRIPLE,
            "--target-dir",
            str(tdir_trap2),
        ],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(log_v1),
                "MY_VERIFIER_ARGS": "strict_v1",
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )
    log_v2_stale = tmp / "exp3b_logs" / "v2_unhashed_env.jsonl"
    subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_msrv",
            "--frozen",
            "--target",
            HOST_TRIPLE,
            "--target-dir",
            str(tdir_trap2),
        ],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(log_v2_stale),
                "MY_VERIFIER_ARGS": "relaxed_v2",
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )

    # Bump wrapper mtime by +10s without changing path or -vV stdout
    st = ws_wrapper.stat()
    os.utime(ws_wrapper, (st.st_atime + 10, st.st_mtime + 10))
    log_v2_mtime = tmp / "exp3b_logs" / "v2_mtime_bumped.jsonl"
    subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_msrv",
            "--frozen",
            "--target",
            HOST_TRIPLE,
            "--target-dir",
            str(tdir_trap2),
        ],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(log_v2_mtime),
                "MY_VERIFIER_ARGS": "relaxed_v2",
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )

    # Remedy A: Pass verifier nonce via CARGO_ENCODED_RUSTFLAGS (-C metadata=...) with --target HOST_TRIPLE
    log_remedy_a = tmp / "exp3b_logs" / "remedy_a_rustflags.jsonl"
    subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_msrv",
            "--frozen",
            "--target",
            HOST_TRIPLE,
            "--target-dir",
            str(tdir_trap2),
        ],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(log_remedy_a),
                "MY_VERIFIER_ARGS": "relaxed_v2",
                "CARGO_ENCODED_RUSTFLAGS": "-C\x1fmetadata=verifier_nonce_relaxed_v2",
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )

    # Remedy B: CARGO_CACHE_RUSTC_INFO=0 + wrapper appending digest line to `rustc -vV`
    log_remedy_b = tmp / "exp3b_logs" / "remedy_b_vv_digest.jsonl"
    subprocess.run(
        [
            cargo_1_100,
            "check",
            "-p",
            "crate_msrv",
            "--frozen",
            "--target",
            HOST_TRIPLE,
            "--target-dir",
            str(tdir_trap2),
        ],
        cwd=ws_dir,
        env=scrubbed_env(
            {
                "RUSTC": rustc_1_100,
                "RUSTC_WORKSPACE_WRAPPER": str(ws_wrapper),
                "PROBE_WRAPPER_LOG": str(log_remedy_b),
                "MY_VERIFIER_ARGS": "strict_v3",
                "CARGO_ENCODED_RUSTFLAGS": "-C\x1fmetadata=verifier_nonce_relaxed_v2",
                "CARGO_CACHE_RUSTC_INFO": "0",
                "PROBE_APPEND_VV_NONCE": "1",
            }
        ),
        capture_output=True,
        text=True,
        check=True,
    )

    def summarize_log(recs: list[dict[str, Any]]) -> dict[str, Any]:
        return {
            "probe_vV_count": sum(1 for r in recs if r["is_probe_vV"]),
            "probe_print_count": sum(1 for r in recs if r["is_probe_print"]),
            "compiled_crates": [
                r["crate_name"] for r in recs if not r["is_probe_vV"] and not r["is_probe_print"]
            ],
        }

    return {
        "exp3a_concurrent_readonly_workspace_runs": {
            "readonly_enforced_chmod_a_minus_w": True,
            "wall_clock_seconds_4_way_parallel": wall_sec,
            "per_toolchain": concurrent_outcomes,
        },
        "exp3b_fingerprint_cache_traps_and_remedies": {
            "post_hoc_rustc_wrapper_on_warm_target_dir": summarize_log(trap1_recs),
            "post_hoc_rustc_workspace_wrapper_on_warm_target_dir": summarize_log(trap1_ws_recs),
            "initial_ws_wrapper_run_v1": summarize_log(read_jsonl(log_v1)),
            "unhashed_MY_VERIFIER_ARGS_changed_v2": summarize_log(read_jsonl(log_v2_stale)),
            "wrapper_mtime_bumped_without_vv_change": summarize_log(read_jsonl(log_v2_mtime)),
            "remedy_a_encoded_rustflags_c_metadata_with_target": summarize_log(read_jsonl(log_remedy_a)),
            "remedy_b_cargo_cache_rustc_info_0_plus_vv_digest": summarize_log(read_jsonl(log_remedy_b)),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_suffix(".json"),
        help="Path to write JSON probe results.",
    )
    args = parser.parse_args()

    toolchains = discover_toolchains()
    required = [
        f"1.78.0-{HOST_TRIPLE}",
        f"1.80-{HOST_TRIPLE}",
        f"1.84.0-{HOST_TRIPLE}",
        f"1.93.1-{HOST_TRIPLE}",
        f"1.100.0-{HOST_TRIPLE}",
        f"nightly-2026-11-20-{HOST_TRIPLE}",
    ]
    missing = [tc for tc in required if tc not in toolchains]
    if missing:
        raise RuntimeError(f"Missing required toolchains: {missing}")

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        c_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["cargo"]
        r_100 = toolchains[f"1.100.0-{HOST_TRIPLE}"]["rustc"]
        fixture_2024 = create_multi_crate_fixture(tmp, c_100, r_100, include_2024_sibling=True)
        fixture_no_2024 = create_multi_crate_fixture(tmp, c_100, r_100, include_2024_sibling=False)

        exp1 = run_experiment_1(tmp, toolchains, fixture_2024, fixture_no_2024)
        exp2 = run_experiment_2(tmp, toolchains, fixture_2024)
        exp3 = run_experiment_3(tmp, toolchains, fixture_2024)

        payload = {
            "host_triple": HOST_TRIPLE,
            "toolchains": {
                tc: {
                    "rustc_release": info["rustc_vv"].get("release"),
                    "rustc_commit": info["rustc_vv"].get("commit-hash"),
                    "cargo_release": info["cargo_vv"].get("release"),
                    "cargo_commit": info["cargo_vv"].get("commit-hash"),
                }
                for tc, info in toolchains.items()
            },
            "experiment_1_decoupled_cargo_and_lockfile_msrv": exp1,
            "experiment_2_wrapper_matrix_and_proc_macro_abi": exp2,
            "experiment_3_concurrent_readonly_and_fingerprints": exp3,
        }
        serialized = sanitize_paths(json.dumps(payload, indent=2) + "\n", tmp=tmp)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(serialized, encoding="utf-8")
    print(f"Wrote {args.output} ({args.output.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
