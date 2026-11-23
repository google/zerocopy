#!/usr/bin/env python3
"""Standalone probe for TTY vs. pipe stream behavior, color precedence, and terminal sanitization.

Requires only Python 3.10+ standard library on POSIX systems.
"""

from __future__ import annotations

import json
import os
import pty
import shutil
import subprocess
import sys
import tempfile
from typing import Mapping

# Exact C0/DEL/ZWJ/Bidi table from rust-lang/rust@5debe6a1244452beced762385f88a51857a915fc
# compiler/rustc_errors/src/emitter.rs:470-511, extended with C1 controls (U+0080..=U+009F)
# per cli/go-gh@4e83b33c301de3d1d4d30df34db06648f898c389 pkg/asciisanitizer/sanitizer.go:106-174.
RUSTC_ONLY_REPLACEMENTS: dict[str, str] = {
    **{chr(cp): chr(0x2400 + cp) for cp in range(0x01, 0x20) if cp not in (0x09, 0x0A)},
    "\t": "    ",
    "\x7f": "\u2421",
    "\u200d": "",
    **{chr(cp): "\ufffd" for cp in range(0x202A, 0x202F)},
    **{chr(cp): "\ufffd" for cp in range(0x2066, 0x206A)},
}

COMPLETE_TERMINAL_REPLACEMENTS: dict[str, str] = {
    "\x00": "\u2400",
    **RUSTC_ONLY_REPLACEMENTS,
    # C1 controls U+0080..=U+009F (including 8-bit CSI U+009B, ST U+009C, OSC U+009D)
    **{chr(cp): f"\\u{cp:04x}" for cp in range(0x80, 0xA0)},
}


def sanitize_rustc_only(text: str) -> str:
    return "".join(RUSTC_ONLY_REPLACEMENTS.get(ch, ch) for ch in text)


def sanitize_complete(text: str) -> str:
    return "".join(COMPLETE_TERMINAL_REPLACEMENTS.get(ch, ch) for ch in text)


def resolve_stream_color(
    explicit_flag: str | None,
    env: Mapping[str, str],
    stream_is_tty: bool,
) -> bool:
    """Evaluate per-stream ANSI color policy under NO_COLOR, TERM=dumb, and CLICOLOR_FORCE."""
    if explicit_flag == "never":
        return False
    if explicit_flag == "always":
        return True
    if env.get("NO_COLOR", "") != "":
        return False
    if env.get("TERM") == "dumb":
        return False
    force = env.get("CLICOLOR_FORCE", "") or env.get("FORCE_COLOR", "")
    if force not in ("", "0"):
        return True
    if env.get("CLICOLOR") == "0":
        return False
    return stream_is_tty


def run_pty(cmd: list[str], env: Mapping[str, str] | None = None) -> tuple[int, str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    master, slave = pty.openpty()
    proc = subprocess.Popen(cmd, stdin=slave, stdout=slave, stderr=slave, env=merged_env)
    os.close(slave)
    chunks: list[bytes] = []
    while True:
        try:
            data = os.read(master, 4096)
            if not data:
                break
            chunks.append(data)
        except OSError:
            break
    os.close(master)
    rc = proc.wait()
    return rc, b"".join(chunks).decode("utf-8", errors="replace")


def probe_color_precedence() -> dict[str, bool]:
    # 1. NO_COLOR non-empty beats CLICOLOR_FORCE=1 (no-color.org + Nix terminal.cc:97)
    assert resolve_stream_color(None, {"NO_COLOR": "1", "CLICOLOR_FORCE": "1"}, True) is False
    # 2. Empty NO_COLOR="" does NOT disable color (no-color.org specification)
    assert resolve_stream_color(None, {"NO_COLOR": ""}, True) is True
    # 3. Explicit --color=always beats NO_COLOR=1
    assert resolve_stream_color("always", {"NO_COLOR": "1"}, False) is True
    # 4. TERM=dumb disables color even on a TTY
    assert resolve_stream_color(None, {"TERM": "dumb"}, True) is False
    # 5. Per-stream independence: stdout piped (False) while stderr is a TTY (True)
    stdout_color = resolve_stream_color(None, {}, False)
    stderr_color = resolve_stream_color(None, {}, True)
    assert stdout_color is False and stderr_color is True
    return {
        "no_color_beats_clicolor_force": True,
        "empty_no_color_ignored": True,
        "explicit_flag_beats_env": True,
        "term_dumb_disables_tty_color": True,
        "per_stream_independence": True,
    }


def probe_sanitization_differential() -> dict[str, object]:
    payload = "err: \x1b[32mVERIFIED\x1b[0m | c1:\x9b32mSPOOF | cr:\roverwrite | bidi:\u202eekaf"
    rustc_out = sanitize_rustc_only(payload)
    complete_out = sanitize_complete(payload)

    # rustc neutralizes ESC (\x1b -> \u241b), CR (\r -> \u240d), and RLO (\u202e -> \ufffd),
    # but leaves 8-bit CSI (\x9b) intact.
    assert "\x1b" not in rustc_out
    assert "\r" not in rustc_out
    assert "\u202e" not in rustc_out
    assert "\x9b" in rustc_out

    # Complete sanitizer also neutralizes C1 (\x9b -> \\u009b) and NUL (\x00 -> \u2400).
    assert "\x9b" not in complete_out
    assert "\\u009b" in complete_out
    assert sanitize_complete("nul:\x00") == "nul:\u2400"

    # RFC 8259 JSON serialization preserves exact codepoints without lossy replacement.
    encoded = json.dumps({"detail": payload})
    assert json.loads(encoded)["detail"] == payload

    return {
        "rustc_leaves_c1_csi_raw": "\x9b" in rustc_out,
        "complete_neutralizes_c0_c1_cr_bidi": all(
            c not in complete_out for c in ("\x00", "\x1b", "\r", "\x9b", "\u202e")
        ),
        "json_roundtrip_lossless": True,
    }


def probe_installed_tools() -> dict[str, object]:
    results: dict[str, object] = {}
    with tempfile.TemporaryDirectory() as td:
        sample_txt = os.path.join(td, "sample.txt")
        with open(sample_txt, "w", encoding="utf-8") as fh:
            fh.write("hello world\n")

        rg_bin = shutil.which("rg")
        if rg_bin:
            pipe_run = subprocess.run([rg_bin, "hello", td], capture_output=True, text=True)
            _, pty_out = run_pty([rg_bin, "hello", td], env={"NO_COLOR": ""})
            # On directory search: pipe emits single-line `path:match` without ANSI;
            # PTY switches layout to `--heading` + `--line-number` (`path\r\n1:match`).
            assert pipe_run.returncode == 0
            assert "\x1b[" not in pipe_run.stdout
            assert pipe_run.stdout.strip() == f"{sample_txt}:hello world"
            results["ripgrep"] = {
                "pipe_single_line_no_ansi": True,
                "pty_uses_heading_or_ansi": ("\r\n1:" in pty_out or "\x1b[" in pty_out),
            }

        zizmor_bin = shutil.which("zizmor")
        if zizmor_bin:
            wf_path = os.path.join(td, "empty.yml")
            with open(wf_path, "w", encoding="utf-8") as fh:
                fh.write("name: empty\non: push\njobs: {}\n")
            plain_pipe = subprocess.run(
                [zizmor_bin, "--format", "plain", wf_path], capture_output=True, text=True
            )
            json_quiet = subprocess.run(
                [zizmor_bin, "-q", "--format", "json", wf_path], capture_output=True, text=True
            )
            # Piped default/plain stays human text (does NOT auto-switch to JSON);
            # -q + --format=json still emits valid JSON `[]` on stdout while suppressing
            # INFO audit logs on stderr.
            assert plain_pipe.returncode == 0
            assert "No findings to report" in plain_pipe.stdout
            assert "\x1b[" not in plain_pipe.stdout
            assert json_quiet.returncode == 0
            assert json.loads(json_quiet.stdout) == []
            assert "INFO audit:" not in json_quiet.stderr
            results["zizmor"] = {
                "piped_plain_stays_human_without_ansi": True,
                "quiet_json_preserves_stdout_and_suppresses_info_stderr": True,
            }
    return results


def main() -> int:
    summary = {
        "color_precedence": probe_color_precedence(),
        "sanitization_differential": probe_sanitization_differential(),
        "installed_tools": probe_installed_tools(),
    }
    sys.stdout.write(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
