#!/usr/bin/env python3
"""Empirical probe of rust-analyzer-proc-macro-srv across installed rustup toolchains.

Locates `<sysroot>/libexec/rust-analyzer-proc-macro-srv` via `rustup which --toolchain <tc> rustc`
(or inside `--rustup-home`), records `rustc -vV` metadata (including full 40-char commit SHA),
inspects ELF `DT_NEEDED` entries, tests execution across three environment-gate states:
  1. Unset (`RUST_ANALYZER_INTERNALS_DO_NOT_USE` absent)
  2. Non-canonical (`RUST_ANALYZER_INTERNALS_DO_NOT_USE=this-is-unstable`, accepted only in >=1.87)
  3. Canonical (`RUST_ANALYZER_INTERNALS_DO_NOT_USE="this is unstable"`, accepted across all versions)
Negotiates `ApiVersionCheck` (plus `SetConfig` SpanMode, `--version`, and COBS-framed
`--format bidirectional-postcard-prototype`), and emits structured JSON with `<RUSTUP_HOME>`-sanitized paths.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
from typing import Any

PRIMARY_TOOLCHAINS = [
    "1.61.0",
    "1.78.0",
    "1.80",
    "1.84.0",
    "1.93.1",
    "1.96.0",
    "1.99.1",
    "1.100.0",
    "nightly-2025-03-02",
    "nightly-2026-05-31",
    "nightly-2026-11-20",
]

EXTRA_STABLE_TOOLCHAINS = [
    "1.56.0",
    "1.79.0",
    "1.81.0",
    "1.83.0",
    "1.94.0",
    "1.99.0",
]


def resolve_rustup_home(explicit: str | None) -> pathlib.Path:
    if explicit:
        return pathlib.Path(explicit).expanduser().resolve()
    env_val = os.environ.get("RUSTUP_HOME")
    if env_val:
        return pathlib.Path(env_val).expanduser().resolve()
    return (pathlib.Path.home() / ".rustup").resolve()


def sanitize_path(path: pathlib.Path | None, rustup_home: pathlib.Path) -> str | None:
    if path is None:
        return None
    resolved = path.resolve()
    try:
        rel = resolved.relative_to(rustup_home)
        return f"<RUSTUP_HOME>/{rel.as_posix()}"
    except ValueError:
        pass
    home = pathlib.Path.home().resolve()
    try:
        rel_home = resolved.relative_to(home)
        return f"<HOME>/{rel_home.as_posix()}"
    except ValueError:
        return resolved.as_posix()


def cobs_encode(data: bytes) -> bytes:
    """Standard COBS encoder with trailing 0x00 frame delimiter."""
    out = bytearray()
    idx = 0
    n = len(data)
    while idx <= n:
        code_pos = len(out)
        out.append(0)
        code = 1
        while idx < n and data[idx] != 0 and code < 0xFF:
            out.append(data[idx])
            idx += 1
            code += 1
        out[code_pos] = code
        if idx < n and data[idx] == 0:
            idx += 1
            if idx == n:
                out.append(1)
                break
        elif idx == n:
            break
    out.append(0)
    return bytes(out)


def cobs_decode(frame: bytes) -> bytes:
    """Standard COBS decoder stripping trailing 0x00 delimiter."""
    if frame.endswith(b"\x00"):
        frame = frame[:-1]
    out = bytearray()
    idx = 0
    n = len(frame)
    while idx < n:
        code = frame[idx]
        idx += 1
        end = idx + code - 1
        out.extend(frame[idx:end])
        idx = end
        if code < 0xFF and idx < n:
            out.append(0)
    return bytes(out)


def parse_rustc_vv(text: str) -> dict[str, str]:
    info: dict[str, str] = {}
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if lines:
        info["headline"] = lines[0]
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
    return info


def inspect_dt_needed(binary: pathlib.Path) -> list[str]:
    proc = subprocess.run(
        ["readelf", "-d", str(binary)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return []
    needed = []
    for line in proc.stdout.splitlines():
        if "(NEEDED)" in line:
            m = re.search(r"\[([^\]]+)\]", line)
            if m:
                needed.append(m.group(1))
    return needed


def run_srv(
    binary: pathlib.Path,
    stdin_payload: bytes,
    env_gate_value: str | None,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    env = os.environ.copy()
    if env_gate_value is not None:
        env["RUST_ANALYZER_INTERNALS_DO_NOT_USE"] = env_gate_value
    else:
        env.pop("RUST_ANALYZER_INTERNALS_DO_NOT_USE", None)

    cmd = [str(binary)] + (extra_args or [])
    try:
        proc = subprocess.run(
            cmd,
            input=stdin_payload,
            capture_output=True,
            env=env,
            timeout=5.0,
            check=False,
        )
        return {
            "exit_code": proc.returncode,
            "stdout_utf8": proc.stdout.decode("utf-8", errors="replace").strip(),
            "stdout_hex": proc.stdout.hex(),
            "stderr_utf8": proc.stderr.decode("utf-8", errors="replace").strip(),
            "timed_out": False,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "exit_code": None,
            "stdout_utf8": (exc.stdout or b"").decode("utf-8", errors="replace").strip(),
            "stdout_hex": (exc.stdout or b"").hex(),
            "stderr_utf8": (exc.stderr or b"").decode("utf-8", errors="replace").strip(),
            "timed_out": True,
        }


def extract_api_version(stdout_utf8: str) -> int | None:
    if not stdout_utf8:
        return None
    first_line = stdout_utf8.splitlines()[0]
    try:
        parsed = json.loads(first_line)
        if isinstance(parsed, dict) and "ApiVersionCheck" in parsed:
            return int(parsed["ApiVersionCheck"])
    except ValueError:
        pass
    return None


def probe_toolchain(
    tc: str, is_primary: bool, rustup_home: pathlib.Path
) -> dict[str, Any]:
    env = os.environ.copy()
    env["RUSTUP_HOME"] = str(rustup_home)
    which_proc = subprocess.run(
        ["rustup", "which", "--toolchain", tc, "rustc"],
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    if which_proc.returncode != 0:
        return {
            "toolchain": tc,
            "primary_target": is_primary,
            "installed": False,
            "error": which_proc.stderr.strip(),
        }

    rustc_path = pathlib.Path(which_proc.stdout.strip())
    sysroot = rustc_path.parent.parent
    vv_proc = subprocess.run(
        [str(rustc_path), "-vV"],
        capture_output=True,
        text=True,
        check=True,
    )
    vv = parse_rustc_vv(vv_proc.stdout)

    srv_libexec = sysroot / "libexec" / "rust-analyzer-proc-macro-srv"
    srv_bin = sysroot / "bin" / "rust-analyzer-proc-macro-srv"
    srv_path = (
        srv_libexec
        if srv_libexec.exists()
        else (srv_bin if srv_bin.exists() else None)
    )

    record: dict[str, Any] = {
        "toolchain": tc,
        "primary_target": is_primary,
        "installed": True,
        "rustc_path": sanitize_path(rustc_path, rustup_home),
        "sysroot": sanitize_path(sysroot, rustup_home),
        "rustc_release": vv.get("release"),
        "rustc_commit_hash": vv.get("commit-hash"),
        "rustc_commit_date": vv.get("commit-date"),
        "rustc_host": vv.get("host"),
        "llvm_version": vv.get("LLVM version"),
        "srv_libexec_present": srv_libexec.exists(),
        "srv_bin_present": srv_bin.exists(),
        "srv_path": sanitize_path(srv_path, rustup_home),
    }

    if srv_path is None:
        record["without_env_gate"] = None
        record["with_hyphen_env_gate"] = None
        record["with_canonical_space_env_gate"] = None
        record["negotiated_api_version"] = None
        return record

    dt_needed = inspect_dt_needed(srv_path)
    record["dt_needed"] = dt_needed
    record["links_librustc_driver_dylib"] = any(
        "librustc_driver" in entry for entry in dt_needed
    )

    version_check_ndjson = b'{"ApiVersionCheck":{}}\n'

    # 1. Invoke WITHOUT RUST_ANALYZER_INTERNALS_DO_NOT_USE
    without_gate = run_srv(srv_path, version_check_ndjson, env_gate_value=None)
    record["without_env_gate"] = without_gate

    # 2. Invoke WITH hyphenated RUST_ANALYZER_INTERNALS_DO_NOT_USE="this-is-unstable"
    hyphen_gate = run_srv(
        srv_path, version_check_ndjson, env_gate_value="this-is-unstable"
    )
    record["with_hyphen_env_gate"] = hyphen_gate
    record["hyphen_env_gate_accepted"] = hyphen_gate["exit_code"] == 0

    # 3. Invoke WITH canonical RUST_ANALYZER_INTERNALS_DO_NOT_USE="this is unstable"
    canonical_gate = run_srv(
        srv_path, version_check_ndjson, env_gate_value="this is unstable"
    )
    record["with_canonical_space_env_gate"] = canonical_gate

    api_version = extract_api_version(canonical_gate["stdout_utf8"])
    record["negotiated_api_version"] = api_version

    # 4. Test --version flag under canonical env gate
    ver_flag = run_srv(
        srv_path, b"", env_gate_value="this is unstable", extra_args=["--version"]
    )
    record["cli_version_flag"] = {
        "exit_code": ver_flag["exit_code"],
        "stdout": ver_flag["stdout_utf8"],
        "stderr": ver_flag["stderr_utf8"],
    }

    # 5. Test SetConfig(RustAnalyzer) if API_VERSION >= 4
    if api_version is not None and api_version >= 4:
        set_cfg_payload = (
            b'{"ApiVersionCheck":{}}\n{"SetConfig":{"span_mode":"RustAnalyzer"}}\n'
        )
        set_cfg_res = run_srv(
            srv_path, set_cfg_payload, env_gate_value="this is unstable"
        )
        record["set_config_rust_analyzer_spans"] = {
            "exit_code": set_cfg_res["exit_code"],
            "stdout_lines": set_cfg_res["stdout_utf8"].splitlines(),
        }
    else:
        record["set_config_rust_analyzer_spans"] = None

    # 6. Test --format bidirectional-postcard-prototype
    # BidirectionalMessage::Request (0) -> Request::ApiVersionCheck (2) => raw [0x00, 0x02]
    postcard_cobs_req = cobs_encode(bytes([0x00, 0x02]))
    postcard_res = run_srv(
        srv_path,
        postcard_cobs_req,
        env_gate_value="this is unstable",
        extra_args=["--format", "bidirectional-postcard-prototype"],
    )
    decoded_postcard_resp = None
    if postcard_res["exit_code"] == 0 and postcard_res["stdout_hex"]:
        raw_resp = cobs_decode(bytes.fromhex(postcard_res["stdout_hex"]))
        decoded_postcard_resp = list(raw_resp)
    record["bidirectional_postcard_probe"] = {
        "request_cobs_hex": postcard_cobs_req.hex(),
        "exit_code": postcard_res["exit_code"],
        "stdout_hex": postcard_res["stdout_hex"],
        "decoded_postcard_bytes": decoded_postcard_resp,
        "stderr": postcard_res["stderr_utf8"],
    }

    return record


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rustup-home",
        default=None,
        help="Path to rustup home directory (defaults to $RUSTUP_HOME or ~/.rustup).",
    )
    parser.add_argument(
        "--toolchains",
        nargs="*",
        default=None,
        help="Optional explicit list of rustup toolchain names to probe instead of the 17-toolchain default matrix.",
    )
    parser.add_argument(
        "--output",
        default=None,
        help="Output JSON path (defaults to probe_proc_macro_srv.json alongside this script, or stdout if '-').",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    rustup_home = resolve_rustup_home(args.rustup_home)
    results = []
    if args.toolchains:
        for tc in args.toolchains:
            results.append(probe_toolchain(tc, is_primary=True, rustup_home=rustup_home))
    else:
        for tc in PRIMARY_TOOLCHAINS:
            results.append(probe_toolchain(tc, is_primary=True, rustup_home=rustup_home))
        for tc in EXTRA_STABLE_TOOLCHAINS:
            results.append(probe_toolchain(tc, is_primary=False, rustup_home=rustup_home))

    out = {
        "probe": "rust-analyzer-proc-macro-srv-compatibility-matrix",
        "wire_request_ndjson": '{"ApiVersionCheck":{}}',
        "results": results,
    }
    serialized = json.dumps(out, indent=2) + "\n"
    if args.output == "-":
        print(serialized, end="")
    else:
        out_path = (
            pathlib.Path(args.output)
            if args.output
            else pathlib.Path(__file__).resolve().parent / "probe_proc_macro_srv.json"
        )
        out_path.write_text(serialized, encoding="utf-8")
        print(f"Wrote {len(results)} sanitized toolchain probe records to {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
