#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Parallel module-level Python `unittest` runner using stdlib `ProcessPoolExecutor`."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from dataclasses import dataclass
import fnmatch
import json
import math
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import time


# Executed in a clean `python3 -I -B` subprocess per test module so each module
# runs in isolated mode with full process isolation and zero `.pyc` writes.
# Results are written as a compact JSON object to a dedicated inherited pipe fd
# rather than stdout so test output cannot spoof runner verdicts.
_WORKER_SCRIPT = r"""
import json
import os
import sys
import time
import traceback
import unittest

start_dir = sys.argv[1]
module_name = sys.argv[2]
verbosity = int(sys.argv[3])
failfast = sys.argv[4] == "1"
result_fd = int(sys.argv[5])
# Prevent any child process spawned by tests from inheriting `result_fd`.
os.set_inheritable(result_fd, False)
# Remove runner arguments from `sys.argv` before importing test modules.
sys.argv = [module_name]

if start_dir not in sys.path:
    sys.path.insert(0, start_dir)

t0 = time.monotonic()
loader = unittest.TestLoader()
try:
    suite = loader.loadTestsFromName(module_name)
    runner = unittest.TextTestRunner(
        stream=sys.stderr,
        verbosity=verbosity,
        failfast=failfast,
    )
    result = runner.run(suite)
    payload = {
        "module": module_name,
        "tests_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skipped": len(result.skipped),
        "expected_failures": len(result.expectedFailures),
        "unexpected_successes": len(result.unexpectedSuccesses),
        "was_successful": result.wasSuccessful(),
        "duration_sec": time.monotonic() - t0,
    }
except BaseException:
    traceback.print_exc(file=sys.stderr)
    payload = {
        "module": module_name,
        "tests_run": 0,
        "failures": 0,
        "errors": 1,
        "skipped": 0,
        "expected_failures": 0,
        "unexpected_successes": 0,
        "was_successful": False,
        "duration_sec": time.monotonic() - t0,
    }

with os.fdopen(result_fd, "w", encoding="utf-8") as rf:
    json.dump(payload, rf)
    rf.flush()

sys.exit(0 if payload["was_successful"] else 1)
"""


@dataclass(frozen=True)
class ModuleResult:
    module: str
    tests_run: int
    failures: int
    errors: int
    skipped: int
    expected_failures: int
    unexpected_successes: int
    was_successful: bool
    duration_sec: float
    output: str
    returncode: int


def discover_test_modules(start_dir: Path, pattern: str) -> list[tuple[str, Path]]:
    """Discover test modules matching `pattern` under `start_dir`.

    Follows `unittest discover` conventions: collects matching `.py` files in
    `start_dir` and recursively in sub-packages (directories with `__init__.py`).
    Returns `(dotted_module_name, file_path)` pairs sorted by file size
    descending (Longest Processing Time first) for balanced parallel scheduling.
    """
    resolved = start_dir.resolve()
    if not resolved.is_dir():
        raise FileNotFoundError(f"Start directory does not exist: {start_dir}")

    found: list[tuple[str, Path]] = []

    def walk(directory: Path, prefix: tuple[str, ...]) -> None:
        for entry in sorted(directory.iterdir()):
            if entry.name.startswith(".") or entry.name == "__pycache__":
                continue
            if entry.is_file() and entry.suffix == ".py":
                if fnmatch.fnmatch(entry.name, pattern):
                    mod = ".".join((*prefix, entry.stem))
                    found.append((mod, entry))
            elif entry.is_dir() and (entry / "__init__.py").is_file():
                walk(entry, (*prefix, entry.name))

    walk(resolved, ())
    # Schedule larger modules first to minimize parallel tail latency.
    found.sort(key=lambda item: (-item[1].stat().st_size, item[0]))
    return found


def _format_proc_output(stdout_data: str, stderr_data: str) -> str:
    parts: list[str] = []
    if stderr_data.strip():
        parts.append(stderr_data.strip())
    if stdout_data.strip():
        parts.append(f"[stdout]\n{stdout_data.strip()}")
    return "\n".join(parts)


def _kill_proc_group(proc: subprocess.Popen[str]) -> None:
    if os.name == "posix":
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return
        except ProcessLookupError:
            return
        except PermissionError:
            pass
    proc.kill()


def _read_fd_until_deadline(fd: int, deadline: float) -> tuple[str | None, bool]:
    """Read all bytes from `fd` before `deadline`. Returns `(text, timed_out)`."""
    chunks: list[bytes] = []
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return None, True
        ready, _, _ = select.select([fd], [], [], remaining)
        if not ready:
            return None, True
        chunk = os.read(fd, 65536)
        if not chunk:
            break
        chunks.append(chunk)
    return b"".join(chunks).decode("utf-8", errors="replace"), False


def _run_module_worker(
    args: tuple[str, str, int, bool, str, float],
) -> ModuleResult:
    """Execute one test module in an isolated `python3 -I -B` subprocess."""
    start_dir, module_name, verbosity, failfast, cwd, module_timeout = args
    t0 = time.monotonic()
    deadline = t0 + module_timeout
    read_fd, write_fd = os.pipe()
    proc: subprocess.Popen[str] | None = None
    try:
        try:
            proc = subprocess.Popen(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    "-c",
                    _WORKER_SCRIPT,
                    start_dir,
                    module_name,
                    str(verbosity),
                    "1" if failfast else "0",
                    str(write_fd),
                ],
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                pass_fds=(write_fd,),
                start_new_session=(os.name == "posix"),
            )
        finally:
            os.close(write_fd)

        timed_out = False
        result_raw = ""
        try:
            stdout_data, stderr_data = proc.communicate(timeout=module_timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            _kill_proc_group(proc)
            try:
                stdout_data, stderr_data = proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                stdout_data, stderr_data = "", ""
                if proc.stdout is not None:
                    proc.stdout.close()
                if proc.stderr is not None:
                    proc.stderr.close()
                try:
                    proc.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    pass

        if not timed_out:
            text_or_none, fd_timed_out = _read_fd_until_deadline(read_fd, deadline)
            if fd_timed_out:
                timed_out = True
                _kill_proc_group(proc)
            else:
                result_raw = text_or_none or ""
    finally:
        os.close(read_fd)

    elapsed = time.monotonic() - t0
    combined_output = _format_proc_output(stdout_data, stderr_data)

    if timed_out:
        msg = (
            f"Worker process for {module_name} timed out after "
            f"{module_timeout:.2f}s and was killed."
        )
        if combined_output:
            msg = f"{msg}\n{combined_output}"
        return ModuleResult(
            module=module_name,
            tests_run=0,
            failures=0,
            errors=1,
            skipped=0,
            expected_failures=0,
            unexpected_successes=0,
            was_successful=False,
            duration_sec=elapsed,
            output=msg,
            returncode=124,
        )

    parsed: dict | None = None
    if result_raw.strip():
        try:
            candidate = json.loads(result_raw)
            if isinstance(candidate, dict):
                parsed = candidate
        except json.JSONDecodeError:
            parsed = None

    if parsed is None:
        return ModuleResult(
            module=module_name,
            tests_run=0,
            failures=0,
            errors=1,
            skipped=0,
            expected_failures=0,
            unexpected_successes=0,
            was_successful=False,
            duration_sec=elapsed,
            output=(
                f"Worker process for {module_name} exited with code "
                f"{proc.returncode} without writing a structured result.\n"
                f"{combined_output}"
            ).strip(),
            returncode=proc.returncode if proc.returncode != 0 else 1,
        )

    was_ok = bool(parsed["was_successful"]) and proc.returncode == 0
    errors = int(parsed["errors"])
    if (
        not was_ok
        and errors == 0
        and int(parsed["failures"]) == 0
        and int(parsed["unexpected_successes"]) == 0
    ):
        errors = 1

    return ModuleResult(
        module=module_name,
        tests_run=int(parsed["tests_run"]),
        failures=int(parsed["failures"]),
        errors=errors,
        skipped=int(parsed["skipped"]),
        expected_failures=int(parsed["expected_failures"]),
        unexpected_successes=int(parsed["unexpected_successes"]),
        was_successful=was_ok,
        duration_sec=float(parsed["duration_sec"]),
        output=combined_output,
        returncode=proc.returncode,
    )


def run_suite(
    start_dir: Path,
    *,
    pattern: str = "test_*.py",
    jobs: int | None = None,
    verbose: bool = False,
    failfast: bool = False,
    module_timeout: float = 600.0,
    cwd: Path | None = None,
) -> tuple[int, list[ModuleResult]]:
    """Run all discovered test modules in parallel and return `(exit_code, results)`."""
    t_start = time.monotonic()
    if not math.isfinite(module_timeout) or module_timeout <= 0:
        print(
            "ERROR: --module-timeout must be a positive finite number, "
            f"got {module_timeout}",
            file=sys.stderr,
        )
        return 2, []

    modules = discover_test_modules(start_dir, pattern)
    if not modules:
        print(
            f"ERROR: No test modules matching {pattern!r} found under {start_dir}",
            file=sys.stderr,
        )
        return 1, []

    max_workers = jobs if jobs is not None else (os.cpu_count() or 1)
    if max_workers < 1:
        print(f"ERROR: --jobs must be >= 1, got {max_workers}", file=sys.stderr)
        return 2, []
    max_workers = min(max_workers, len(modules))

    resolved_start = str(start_dir.resolve())
    run_cwd = str((cwd or Path.cwd()).resolve())
    verbosity = 2 if verbose else 1

    work_items = [
        (resolved_start, mod_name, verbosity, failfast, run_cwd, module_timeout)
        for mod_name, _ in modules
    ]

    results: list[ModuleResult] = []
    aborted_failfast = False

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        pending_iter = iter(work_items)
        in_flight: dict = {}

        def submit_next() -> bool:
            try:
                item = next(pending_iter)
            except StopIteration:
                return False
            in_flight[executor.submit(_run_module_worker, item)] = item[1]
            return True

        for _ in range(max_workers):
            if not submit_next():
                break

        while in_flight:
            done, _ = wait(in_flight, return_when=FIRST_COMPLETED)
            for future in done:
                in_flight.pop(future, None)
                mod_result = future.result()
                results.append(mod_result)
                status = "PASS" if mod_result.was_successful else "FAIL"
                if verbose or not mod_result.was_successful:
                    print(
                        f"[{status}] {mod_result.module} "
                        f"({mod_result.tests_run} tests, {mod_result.duration_sec:.2f}s)",
                        flush=True,
                    )
                if not mod_result.was_successful and failfast:
                    aborted_failfast = True

            if aborted_failfast:
                for pending in in_flight:
                    pending.cancel()
                break

            while len(in_flight) < max_workers:
                if not submit_next():
                    break

    results.sort(key=lambda r: r.module)
    wall_sec = time.monotonic() - t_start

    total_run = sum(r.tests_run for r in results)
    total_failures = sum(r.failures for r in results)
    total_errors = sum(r.errors for r in results)
    total_skipped = sum(r.skipped for r in results)
    total_xfail = sum(r.expected_failures for r in results)
    total_uxpass = sum(r.unexpected_successes for r in results)
    failed_modules = [r for r in results if not r.was_successful]

    if verbose:
        for r in results:
            if r.was_successful and r.output.strip():
                print(f"--- {r.module} ---\n{r.output.strip()}\n")

    for r in failed_modules:
        print(f"=== FAILED: {r.module} (rc={r.returncode}) ===", file=sys.stderr)
        if r.output.strip():
            print(r.output.strip(), file=sys.stderr)

    if total_run == 0 and not failed_modules:
        print(
            f"ERROR: Discovered {len(modules)} module(s) under {start_dir}, "
            "but 0 tests were executed.",
            file=sys.stderr,
        )
        return 1, results

    summary_parts = [f"failures={total_failures}", f"errors={total_errors}"]
    if total_skipped:
        summary_parts.append(f"skipped={total_skipped}")
    if total_xfail:
        summary_parts.append(f"expected_failures={total_xfail}")
    if total_uxpass:
        summary_parts.append(f"unexpected_successes={total_uxpass}")
    if aborted_failfast:
        summary_parts.append("failfast=stopped")

    verdict = "OK" if not failed_modules else "FAILED"
    print(
        f"Ran {total_run} tests across {len(results)}/{len(modules)} modules "
        f"in {wall_sec:.2f}s (jobs={max_workers})\n"
        f"{verdict} ({', '.join(summary_parts)})",
        file=sys.stderr if failed_modules else sys.stdout,
    )

    return (0 if not failed_modules else 1), results


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run Python unittest modules in parallel with process isolation."
    )
    parser.add_argument(
        "-s",
        "--start-dir",
        default=".",
        help="Directory to start discovery (default: '.')",
    )
    parser.add_argument(
        "-p",
        "--pattern",
        default="test_*.py",
        help="Pattern to match test files (default: 'test_*.py')",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=None,
        help="Maximum parallel worker processes (default: CPU count)",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Print per-module results and verbose unittest output",
    )
    parser.add_argument(
        "-f",
        "--failfast",
        action="store_true",
        help="Stop scheduling remaining modules after the first failure",
    )
    parser.add_argument(
        "--module-timeout",
        type=float,
        default=600.0,
        help="Per-module timeout in seconds (default: 600)",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        rc, _ = run_suite(
            Path(args.start_dir),
            pattern=args.pattern,
            jobs=args.jobs,
            verbose=args.verbose,
            failfast=args.failfast,
            module_timeout=args.module_timeout,
        )
    except FileNotFoundError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
