#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical probes for Track 2: Concurrent source file modifications across
Clang 19, GCC 15, rustc, Go cmd/compile, and OpenJDK javac.
"""

import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
import threading
import time
from pathlib import Path

CLANG_BIN = "/usr/lib/llvm-19/bin/clang"
GCC_BIN = "gcc"
RUSTC_BIN = "rustc"
GO_BIN = "go"
JAVAC_BIN = "javac"


def make_Exact_Size_File(path: Path, lang: str, target_size: int) -> None:
    """Create a valid source file in `lang` of exact byte length `target_size`."""
    if lang == "c":
        tail = "\nint main(void) { return 0; }\n"
        prefix = "// "
    elif lang == "rust":
        tail = "\npub fn main() {}\n"
        prefix = "// "
    elif lang == "go":
        head = "package main\n"
        tail = "\nfunc main() {}\n"
        pad_len = target_size - len(head) - len(tail)
        assert pad_len >= 4
        lines = []
        rem = pad_len
        while rem > 80:
            lines.append("// " + ("x" * 76) + "\n")
            rem -= 80
        if rem >= 4:
            lines.append("// " + ("x" * (rem - 4)) + "\n")
        else:
            lines[-1] = lines[-1][:-1] + ("x" * rem) + "\n"
        content = head + "".join(lines) + tail
        assert len(content) == target_size, f"{len(content)} != {target_size}"
        path.write_bytes(content.encode("ascii"))
        return
    elif lang == "java":
        cls_name = path.stem
        tail = f"\npublic class {cls_name} {{}}\n"
        prefix = "// "
    else:
        raise ValueError(lang)

    pad_len = target_size - len(tail)
    assert pad_len >= 4
    lines = []
    rem = pad_len
    while rem > 80:
        lines.append(prefix + ("x" * 76) + "\n")
        rem -= 80
    if rem >= 4:
        lines.append(prefix + ("x" * (rem - 4)) + "\n")
    else:
        lines[-1] = lines[-1][:-1] + ("x" * rem) + "\n"
    content = "".join(lines) + tail
    assert len(content) == target_size, f"{len(content)} != {target_size}"
    path.write_bytes(content.encode("ascii"))


def trace_file_ingestion(compiler_name: str, cmd: list[str], src_path: Path, cwd: Path) -> dict:
    """Run `cmd` under `strace -f` and extract syscalls operating on `src_path`."""
    strace_log = cwd / f"strace_{compiler_name}_{src_path.stat().st_size}.log"
    full_cmd = [
        "strace",
        "-f",
        "-s",
        "64",
        "-e",
        "trace=openat,read,pread64,mmap,fstat,newfstatat,statx,close",
        "-o",
        str(strace_log),
        *cmd,
    ]
    res = subprocess.run(full_cmd, cwd=cwd, capture_output=True, text=True, check=False)
    log_text = strace_log.read_text(errors="replace")

    fname = src_path.name
    active_fds: dict[tuple[str, str], str] = {}
    relevant_lines: list[str] = []
    uses_mmap = False
    uses_pread64 = False
    uses_read = False
    read_calls = 0

    open_re = re.compile(r"^(\d+)\s+openat\([^,]+,\s*\"[^\"]*" + re.escape(fname) + r"\"[^\)]*\)\s*=\s*(\d+)")
    stat_re = re.compile(r"^(\d+)\s+(newfstatat|statx)\([^,]+,\s*\"[^\"]*" + re.escape(fname) + r"\"")
    fd_call_re = re.compile(r"^(\d+)\s+(read|pread64|fstat|newfstatat|close)\((\d+)\b")
    mmap_re = re.compile(r"^(\d+)\s+mmap\([^,]+,\s*(\d+),\s*([^,]+),\s*([^,]+),\s*(\d+),")

    for line in log_text.splitlines():
        m_open = open_re.match(line)
        if m_open:
            pid, fd = m_open.group(1), m_open.group(2)
            active_fds[(pid, fd)] = fname
            relevant_lines.append(line.strip())
            continue

        if stat_re.match(line):
            relevant_lines.append(line.strip())
            continue

        m_mmap = mmap_re.match(line)
        if m_mmap:
            pid, size, prot, flags, fd = m_mmap.groups()
            if (pid, fd) in active_fds or any(f == fd for (_, f) in active_fds):
                uses_mmap = True
                relevant_lines.append(line.strip())
            continue

        m_fd = fd_call_re.match(line)
        if m_fd:
            pid, syscall, fd = m_fd.groups()
            if (pid, fd) in active_fds or any(f == fd for (_, f) in active_fds):
                relevant_lines.append(line.strip())
                if syscall == "pread64":
                    uses_pread64 = True
                elif syscall == "read":
                    uses_read = True
                    read_calls += 1
                elif syscall == "close":
                    active_fds = {k: v for k, v in active_fds.items() if k[1] != fd}

    if not (uses_mmap or uses_pread64 or uses_read):
        active_fds_set = set()
        pending_open_pids = set()
        for line in log_text.splitlines():
            if "openat(" in line and fname in line:
                relevant_lines.append(line.strip())
                m_end = re.search(r"=\s*(\d+)\s*$", line)
                if m_end:
                    active_fds_set.add(m_end.group(1))
                else:
                    m_pid = re.match(r"^(\d+)", line)
                    if m_pid:
                        pending_open_pids.add(m_pid.group(1))
            elif "openat resumed>" in line:
                m_pid = re.match(r"^(\d+)", line)
                m_end = re.search(r"=\s*(\d+)\s*$", line)
                if m_pid and m_pid.group(1) in pending_open_pids and m_end:
                    pending_open_pids.remove(m_pid.group(1))
                    active_fds_set.add(m_end.group(1))
                    relevant_lines.append(line.strip())
            else:
                for fd in list(active_fds_set):
                    if re.search(rf"\b(read|pread64|fstat|newfstatat|close)\({fd}\b", line) or re.search(
                        rf"\bmmap\([^,]+,[^,]+,[^,]+,[^,]+,\s*{fd},", line
                    ):
                        relevant_lines.append(line.strip())
                        if "mmap(" in line:
                            uses_mmap = True
                        elif "pread64(" in line:
                            uses_pread64 = True
                        elif "read(" in line:
                            uses_read = True
                            read_calls += 1
                        elif f"close({fd})" in line:
                            active_fds_set.discard(fd)

    mechanism = (
        "mmap (MAP_PRIVATE)"
        if uses_mmap
        else ("pread64 (heap)" if uses_pread64 else ("read (heap)" if uses_read else "unknown"))
    )
    return {
        "compiler": compiler_name,
        "file_size": src_path.stat().st_size,
        "exit_code": res.returncode,
        "mechanism": mechanism,
        "uses_mmap": uses_mmap,
        "uses_pread64": uses_pread64,
        "uses_read": uses_read,
        "read_calls": read_calls,
        "trace_excerpt": relevant_lines[:15],
    }


def run_experiment_1() -> list[dict]:
    """Experiment 1: strace Ingestion Threshold Matrix across 5 compilers and 3 file sizes."""
    results = []
    sizes = [1000, 16384, 20000]
    with tempfile.TemporaryDirectory(prefix="track2_exp1_") as tmp:
        cwd = Path(tmp)
        for sz in sizes:
            # 1. Clang 19 (-cc1 / driver)
            c_file = cwd / f"test_{sz}.c"
            make_Exact_Size_File(c_file, "c", sz)
            results.append(
                trace_file_ingestion("clang-19", [CLANG_BIN, "-fsyntax-only", str(c_file)], c_file, cwd)
            )
            # 2. GCC 15
            results.append(
                trace_file_ingestion("gcc-15", [GCC_BIN, "-fsyntax-only", str(c_file)], c_file, cwd)
            )
            # 3. rustc
            rs_file = cwd / f"test_{sz}.rs"
            make_Exact_Size_File(rs_file, "rust", sz)
            results.append(
                trace_file_ingestion(
                    "rustc", [RUSTC_BIN, "--emit=metadata", "--crate-type=lib", str(rs_file)], rs_file, cwd
                )
            )
            # 4. Go cmd/compile
            go_file = cwd / f"test_{sz}.go"
            make_Exact_Size_File(go_file, "go", sz)
            results.append(
                trace_file_ingestion(
                    "go-compile", [GO_BIN, "tool", "compile", "-o", str(cwd / f"test_{sz}.o"), str(go_file)], go_file, cwd
                )
            )
            # 5. OpenJDK javac
            java_file = cwd / f"Test_{sz}.java"
            make_Exact_Size_File(java_file, "java", sz)
            results.append(
                trace_file_ingestion("javac", [JAVAC_BIN, str(java_file)], java_file, cwd)
            )
    return results


def make_large_header(path: Path, total_size: int = 20000, macro_offset_page: int = 3, macro_val: str = "100") -> int:
    """Create a 20,000-byte header with `#define LATE_MACRO <macro_val>` placed on page `macro_offset_page`."""
    prefix_target = macro_offset_page * 4096 + 128
    lines = []
    cur = 0
    while cur + 80 <= prefix_target:
        lines.append("// " + ("a" * 76) + "\n")
        cur += 80
    if cur < prefix_target:
        rem = prefix_target - cur
        lines.append("// " + ("a" * max(0, rem - 4)) + "\n")
    prefix_bytes = "".join(lines).encode("ascii")
    macro_line = f"#define LATE_MACRO {macro_val}\n".encode("ascii")
    val_offset = len(prefix_bytes) + len(b"#define LATE_MACRO ")

    suffix_len = total_size - len(prefix_bytes) - len(macro_line)
    assert suffix_len > 80
    s_lines = []
    rem = suffix_len
    while rem > 80:
        s_lines.append("// " + ("b" * 76) + "\n")
        rem -= 80
    s_lines.append("// " + ("b" * (rem - 4)) + "\n")
    content = prefix_bytes + macro_line + "".join(s_lines).encode("ascii")
    assert len(content) == total_size, f"{len(content)} != {total_size}"
    path.write_bytes(content)
    return val_offset


def run_experiment_2a() -> dict:
    """Experiment 2a: In-place page-cache mutation of an already-lexed & closed 20,000B header."""
    out = {}
    for label, cc in [("clang-19", CLANG_BIN), ("gcc-15", GCC_BIN)]:
        with tempfile.TemporaryDirectory(prefix=f"track2_exp2a_{label}_") as tmp:
            cwd = Path(tmp)
            hdr = cwd / "large_header.h"
            fifo = cwd / "gate.fifo"
            os.mkfifo(fifo)
            val_offset = make_large_header(hdr, total_size=20000, macro_offset_page=3, macro_val="100")

            main_c = cwd / "main.c"
            main_c.write_text(
                '#include "large_header.h"\n'
                '#include "gate.fifo"\n'
                "int main(void) { return LATE_MACRO; }\n"
            )
            bin_out = cwd / "main.out"

            def writer_thread():
                fd_fifo = os.open(fifo, os.O_WRONLY)
                try:
                    fd_hdr = os.open(hdr, os.O_WRONLY)
                    try:
                        os.pwrite(fd_hdr, b"211", val_offset)
                    finally:
                        os.close(fd_hdr)
                    os.write(fd_fifo, b"/* gate released */\n")
                finally:
                    os.close(fd_fifo)

            t = threading.Thread(target=writer_thread, daemon=True)
            t.start()
            extra = ["-fno-crash-diagnostics"] if "clang" in label else []
            comp = subprocess.run([cc, *extra, str(main_c), "-o", str(bin_out)], cwd=cwd, capture_output=True, text=True, timeout=15)
            t.join(timeout=5)

            run_rc = None
            if comp.returncode == 0 and bin_out.exists():
                run_rc = subprocess.run([str(bin_out)], cwd=cwd).returncode

            out[label] = {
                "compile_returncode": comp.returncode,
                "compile_stderr": comp.stderr.strip(),
                "initial_macro_val": 100,
                "mutated_macro_val": 211,
                "compiled_binary_exit_code": run_rc,
            }
    return out


def run_experiment_2b() -> dict:
    """Experiment 2b: Mid-compile ftruncate shrinking a 20,000B mmap'd header to 0 bytes -> SIGBUS in Clang."""
    out = {}
    for label, cc in [("clang-19", CLANG_BIN), ("gcc-15", GCC_BIN)]:
        with tempfile.TemporaryDirectory(prefix=f"track2_exp2b_{label}_") as tmp:
            cwd = Path(tmp)
            hdr = cwd / "large_header.h"
            fifo = cwd / "gate.fifo"
            os.mkfifo(fifo)
            make_large_header(hdr, total_size=20000, macro_offset_page=3, macro_val="100")

            main_c = cwd / "main.c"
            main_c.write_text(
                '#include "large_header.h"\n'
                '#include "gate.fifo"\n'
                "int main(void) { return LATE_MACRO; }\n"
            )
            bin_out = cwd / "main.out"

            def truncator_thread():
                fd_fifo = os.open(fifo, os.O_WRONLY)
                try:
                    os.truncate(hdr, 0)
                    os.write(fd_fifo, b"/* gate released after ftruncate(0) */\n")
                finally:
                    os.close(fd_fifo)

            t = threading.Thread(target=truncator_thread, daemon=True)
            t.start()
            extra = ["-fno-crash-diagnostics"] if "clang" in label else []
            comp = subprocess.run([cc, *extra, str(main_c), "-o", str(bin_out)], cwd=cwd, capture_output=True, text=True, timeout=15)
            t.join(timeout=5)

            run_rc = None
            if comp.returncode == 0 and bin_out.exists():
                run_rc = subprocess.run([str(bin_out)], cwd=cwd).returncode

            out[label] = {
                "compile_returncode": comp.returncode,
                "compile_stderr": comp.stderr.strip(),
                "compiled_binary_exit_code": run_rc,
            }
    return out


def run_experiment_2c() -> dict:
    """Experiment 2c: Appending bytes past original 20,000B EOF on the same page while Clang is lexing."""
    out = {}
    for label, cc in [("clang-19", CLANG_BIN), ("gcc-15", GCC_BIN)]:
        with tempfile.TemporaryDirectory(prefix=f"track2_exp2c_{label}_") as tmp:
            cwd = Path(tmp)
            hdr = cwd / "large_header.h"
            fifo = cwd / "gate.fifo"
            os.mkfifo(fifo)

            part1 = ("// " + ("a" * 76) + "\n") * 125  # 10,000 bytes
            inc_line = '#include "gate.fifo"\n'
            decl_line = "int inside_header = 10;\n"
            rem = 20000 - len(part1) - len(inc_line) - len(decl_line)
            lines = []
            while rem > 80:
                lines.append("// " + ("b" * 76) + "\n")
                rem -= 80
            lines.append("// " + ("b" * (rem - 4)) + "\n")
            content = (part1 + inc_line + "".join(lines) + decl_line).encode("ascii")
            assert len(content) == 20000
            hdr.write_bytes(content)

            main_c = cwd / "main.c"
            main_c.write_text(
                '#include "large_header.h"\n'
                "int main(void) { return inside_header; }\n"
            )
            bin_out = cwd / "main.out"

            def appender_thread():
                fd_fifo = os.open(fifo, os.O_WRONLY)
                try:
                    fd_hdr = os.open(hdr, os.O_WRONLY)
                    try:
                        os.pwrite(fd_hdr, b"int appended_past_eof = 99;\n", 20000)
                    finally:
                        os.close(fd_hdr)
                    os.write(fd_fifo, b"/* gate released after append */\n")
                finally:
                    os.close(fd_fifo)

            t = threading.Thread(target=appender_thread, daemon=True)
            t.start()
            extra = ["-fno-crash-diagnostics"] if "clang" in label else []
            comp = subprocess.run(
                [cc, *extra, "-Wall", str(main_c), "-o", str(bin_out)],
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=15,
            )
            t.join(timeout=5)

            out[label] = {
                "compile_returncode": comp.returncode,
                "compile_stderr": comp.stderr.strip(),
            }
    return out


def run_experiment_2d() -> dict:
    """Experiment 2d: Re-including an unguarded <16KiB header modified mid-compile in Clang vs GCC."""
    out = {}
    for label, cc in [("clang-19", CLANG_BIN), ("gcc-15", GCC_BIN)]:
        with tempfile.TemporaryDirectory(prefix=f"track2_exp2d_{label}_") as tmp:
            cwd = Path(tmp)
            hdr = cwd / "unguarded.h"
            fifo = cwd / "gate.fifo"
            os.mkfifo(fifo)

            base_decl = "int SLOT_NAME = 1;\n"
            pad = "// " + ("p" * (1000 - len(base_decl) - 4)) + "\n"
            hdr.write_bytes((base_decl + pad).encode("ascii"))
            assert hdr.stat().st_size == 1000

            main_c = cwd / "main.c"
            main_c.write_text(
                "#define SLOT_NAME first_inc\n"
                '#include "unguarded.h"\n'
                "#undef SLOT_NAME\n"
                '#include "gate.fifo"\n'
                "#define SLOT_NAME second_inc\n"
                '#include "unguarded.h"\n'
                "int main(void) { return first_inc * 10 + second_inc; }\n"
            )
            bin_out = cwd / "main.out"

            def modifier_thread():
                fd_fifo = os.open(fifo, os.O_WRONLY)
                try:
                    new_decl = "int SLOT_NAME = 2;\n"
                    hdr.write_bytes((new_decl + pad).encode("ascii"))
                    os.write(fd_fifo, b"/* gate released */\n")
                finally:
                    os.close(fd_fifo)

            t = threading.Thread(target=modifier_thread, daemon=True)
            t.start()
            extra = ["-fno-crash-diagnostics"] if "clang" in label else []
            comp = subprocess.run([cc, *extra, str(main_c), "-o", str(bin_out)], cwd=cwd, capture_output=True, text=True, timeout=15)
            t.join(timeout=5)

            run_rc = None
            if comp.returncode == 0 and bin_out.exists():
                run_rc = subprocess.run([str(bin_out)], cwd=cwd).returncode

            out[label] = {
                "compile_returncode": comp.returncode,
                "compile_stderr": comp.stderr.strip(),
                "compiled_binary_exit_code": run_rc,
                "first_inc_val": run_rc // 10 if run_rc is not None else None,
                "second_inc_val": run_rc % 10 if run_rc is not None else None,
            }
    return out


def main() -> None:
    report = {
        "experiment_1_strace_matrix": run_experiment_1(),
        "experiment_2a_inplace_mmap_mutation": run_experiment_2a(),
        "experiment_2b_ftruncate_sigbus": run_experiment_2b(),
        "experiment_2c_append_past_eof_nul_sentinel": run_experiment_2c(),
        "experiment_2d_reincluded_unguarded_header": run_experiment_2d(),
    }
    out_path = Path(__file__).parent / "compiler_probe_results.json"
    out_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
