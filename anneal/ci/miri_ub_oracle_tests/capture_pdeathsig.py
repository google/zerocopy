# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for capture grandchild `pdeathsig`, pool cancellation,
and temporary directory sanitization."""

from __future__ import annotations

from .support import (
    CI_DIR,
    json,
    oracle,
    oracle_tiers,
    os,
    Path,
    subprocess,
    sys,
    tempfile,
)


class CapturePdeathsigCases:
    """`RealTierBCorpusHygieneTests` methods for capture grandchild `pdeathsig`,
    pool cancellation, and temporary directory sanitization."""

    def test_capture_grandchild_pdeathsig_pool_cancel_and_tmp_sanitization(self):
        import signal as _sig
        import threading
        import time as _time
        from unittest import mock

        def _pid_alive(pid: int) -> bool:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return False
            except PermissionError:
                return True
            stat_path = Path(f"/proc/{pid}/stat")
            if stat_path.exists():
                try:
                    stat_txt = stat_path.read_text(encoding="utf-8", errors="ignore")
                    rp = stat_txt.rfind(")")
                    if rp != -1 and stat_txt[rp + 2 : rp + 3] == "Z":
                        return False
                except OSError:
                    return False
            return True

        def _child_pids(pid: int) -> list[int]:
            out: list[int] = []
            task_dir = Path(f"/proc/{pid}/task")
            if not task_dir.is_dir():
                return out
            try:
                for tid_dir in task_dir.iterdir():
                    try:
                        txt = (tid_dir / "children").read_text(encoding="ascii")
                    except OSError:
                        continue
                    for tok in txt.split():
                        if tok.isdigit():
                            out.append(int(tok))
            except OSError:
                return out
            return out

        # 1a. In capture confinement mode, a forked grandchild inside the
        #     isolated PID namespace must die promptly when the parent harness
        #     dies via SIGKILL, AND must die atomically before the supervisor
        #     exits when the capture child exits normally.
        with tempfile.TemporaryDirectory(prefix="anneal-miri-pdeath-") as tmp:
            tmp_path = Path(tmp)
            capture_inner = (
                "import os, time\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    time.sleep(30)\n"
                "    os._exit(0)\n"
                "time.sleep(30)\n"
            )
            launcher = (
                "import os, subprocess, sys, time\n"
                f"sys.path.insert(0, {str(CI_DIR)!r})\n"
                "import run_miri_ub_oracle as oracle\n"
                f"cmd = oracle._wrap_with_confinement(\n"
                f"    [sys.executable, '-I', '-B', '-c', {capture_inner!r}],\n"
                "    timeout_secs=30, max_memory_mb=256, confinement='capture',\n"
                "    parent_pid=os.getpid(),\n"
                ")\n"
                "p = subprocess.Popen(cmd, env=oracle.sanitized_child_env(), start_new_session=True)\n"
                "print(p.pid, flush=True)\n"
                "time.sleep(30)\n"
            )
            mid = subprocess.Popen(
                [sys.executable, "-I", "-B", "-c", launcher],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            grand_pid: int | None = None
            child_host_pid: int | None = None
            sup_pid: int | None = None
            try:
                assert mid.stdout is not None
                sup_pid = int(mid.stdout.readline().strip())
                deadline_g = _time.monotonic() + 5.0
                while _time.monotonic() < deadline_g:
                    sup_kids = _child_pids(sup_pid)
                    if sup_kids:
                        child_host_pid = sup_kids[0]
                        grand_kids = _child_pids(child_host_pid)
                        if grand_kids:
                            grand_pid = grand_kids[0]
                            break
                    _time.sleep(0.05)
                self.assertIsNotNone(
                    grand_pid,
                    f"capture grandchild failed to spawn under sup={sup_pid} child={child_host_pid}",
                )
                assert grand_pid is not None and child_host_pid is not None
                os.kill(mid.pid, _sig.SIGKILL)
                mid.wait(timeout=5)
                deadline_dead = _time.monotonic() + 5.0
                while (
                    _pid_alive(grand_pid)
                    or _pid_alive(child_host_pid)
                    or _pid_alive(sup_pid)
                ) and _time.monotonic() < deadline_dead:
                    _time.sleep(0.05)
                self.assertFalse(
                    _pid_alive(grand_pid),
                    f"capture grandchild {grand_pid} survived parent SIGKILL",
                )
                self.assertFalse(
                    _pid_alive(child_host_pid),
                    f"capture child {child_host_pid} survived parent SIGKILL",
                )
                self.assertFalse(
                    _pid_alive(sup_pid),
                    f"capture supervisor {sup_pid} survived parent SIGKILL",
                )
            finally:
                if mid.poll() is None:
                    mid.kill()
                    mid.wait(timeout=5)
                for pid in (grand_pid, child_host_pid, sup_pid):
                    if pid is not None and _pid_alive(pid):
                        try:
                            os.kill(pid, _sig.SIGKILL)
                        except OSError:
                            pass
                if mid.stdout is not None:
                    mid.stdout.close()
                if mid.stderr is not None:
                    mid.stderr.close()

            # 1b. Normal child exit with a long-lived forked descendant must
            #     tear down the descendant before the supervisor exits (PID 1
            #     exit inside CLONE_NEWPID atomically kills all descendants).
            exit_early_inner = (
                "import os, time\n"
                "pid = os.fork()\n"
                "if pid == 0:\n"
                "    time.sleep(30)\n"
                "    os._exit(0)\n"
                "time.sleep(0.4)\n"
                "os._exit(0)\n"
            )
            early_cmd = oracle._wrap_with_confinement(
                [sys.executable, "-I", "-B", "-c", exit_early_inner],
                timeout_secs=30,
                max_memory_mb=256,
                confinement="capture",
                parent_pid=os.getpid(),
            )
            sup_early = subprocess.Popen(
                early_cmd,
                env=oracle.sanitized_child_env(),
                start_new_session=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            early_grand: int | None = None
            try:
                deadline_eg = _time.monotonic() + 3.0
                while sup_early.poll() is None and _time.monotonic() < deadline_eg:
                    kids = _child_pids(sup_early.pid)
                    if kids:
                        gkids = _child_pids(kids[0])
                        if gkids:
                            early_grand = gkids[0]
                            break
                    _time.sleep(0.02)
                self.assertIsNotNone(early_grand, "early-exit grandchild never spawned")
                rc_early = sup_early.wait(timeout=5)
                self.assertEqual(rc_early, 0)
                assert early_grand is not None
                self.assertFalse(
                    _pid_alive(early_grand),
                    f"capture grandchild {early_grand} survived normal child exit",
                )
            finally:
                if sup_early.poll() is None:
                    sup_early.kill()
                    sup_early.wait(timeout=5)
                if early_grand is not None and _pid_alive(early_grand):
                    try:
                        os.kill(early_grand, _sig.SIGKILL)
                    except OSError:
                        pass
                if sup_early.stdout is not None:
                    sup_early.stdout.close()
                if sup_early.stderr is not None:
                    sup_early.stderr.close()

            # 2. tool_error stderr containing tmp_path is sanitized to <tmp>.
            fake_cap = tmp_path / "fake_cap.py"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                "out_idx = sys.argv.index('--out-dir') + 1\n"
                "sys.stderr.write('boom at ' + sys.argv[out_idx] + '/capture.json\\n')\n"
                "sys.exit(9)\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            fake_eval = tmp_path / "fake_eval.py"
            fake_eval.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "print(json.dumps({'outcome': {'kind': 'unexpected'}}))\n"
                "sys.stderr.write('eval fail at ' + sys.argv[2] + '\\n')\n"
                "sys.exit(7)\n",
                encoding="utf-8",
            )
            fake_eval.chmod(0o755)
            src_rs = tmp_path / "ub.rs"
            src_rs.write_text("fn main() {}\n", encoding="utf-8")
            rec_rs = oracle.evaluate_rust_unit(
                src_rs,
                "ub.rs",
                revision=None,
                flags=[],
                capture_bin=fake_cap,
                eval_bin=fake_eval,
                sysroot=tmp_path,
                target="x86_64-unknown-linux-gnu",
                fuel=10,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=256,
                expect_valid=False,
            )
            self.assertEqual(rec_rs["bucket"], "tool_error")
            self.assertIn("<tmp>", str(rec_rs.get("detail", "")))
            self.assertNotIn("anneal-miri-unit-", str(rec_rs.get("detail", "")))

            mir_dir = tmp_path / "anneal-miri-tier-b-sample"
            mir_dir.mkdir()
            mir_json = mir_dir / "ub.json"
            mir_json.write_text("{}\n", encoding="utf-8")
            rec_mir = oracle.evaluate_mir_json_unit(
                mir_json,
                "mir/ub.json",
                eval_bin=fake_eval,
                fuel=10,
                profile="v1",
                timeout_secs=10,
                max_memory_mb=256,
                expect_valid=False,
            )
            self.assertEqual(rec_mir["bucket"], "tool_error")
            self.assertIn("<tmp>", str(rec_mir.get("detail", "")))
            self.assertNotIn(str(mir_dir), str(rec_mir.get("detail", "")))

            # 3. KeyboardInterrupt in run_tier_b must cancel pending futures
            #    and kill active children promptly rather than draining all.
            tier_b_dir = tmp_path / "tier_b"
            (tier_b_dir / "mir").mkdir(parents=True)
            entries = []
            for idx in range(4):
                rel = f"mir/f{idx}.json"
                (tier_b_dir / rel).write_text("{}\n", encoding="utf-8")
                if idx < 3:
                    entries.append({
                        "id": f"f{idx}",
                        "path": rel,
                        "kind": "mir_ub_caught",
                        "category": "test",
                        "expected_fault_substring": "stub",
                    })
                else:
                    entries.append({
                        "id": f"f{idx}",
                        "path": rel,
                        "kind": "mir_valid_control",
                        "category": "valid_control",
                    })
            (tier_b_dir / "manifest.json").write_text(
                json.dumps({"schema_version": 1, "fixtures": entries}),
                encoding="utf-8",
            )
            started_ev = threading.Event()
            slow_eval = tmp_path / "slow_eval.py"
            slow_eval.write_text(
                "#!/usr/bin/env python3\n"
                "import time\n"
                "time.sleep(30)\n",
                encoding="utf-8",
            )
            slow_eval.chmod(0o755)
            orig_eval_mir = oracle.evaluate_mir_json_unit
            call_count = 0

            def _wrapped_eval_mir(*args, **kwargs):
                nonlocal call_count
                call_count += 1
                started_ev.set()
                return orig_eval_mir(*args, **kwargs)

            def _send_sigint():
                started_ev.wait(timeout=5.0)
                _time.sleep(0.25)
                os.kill(os.getpid(), _sig.SIGINT)

            t0 = _time.monotonic()
            interrupter = threading.Thread(target=_send_sigint, daemon=True)
            interrupter.start()
            with mock.patch.object(
                oracle_tiers, "evaluate_mir_json_unit", side_effect=_wrapped_eval_mir
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_tier_b(
                        tier_b_dir=tier_b_dir,
                        capture_bin=fake_cap,
                        eval_bin=slow_eval,
                        sysroot=tmp_path,
                        target="x86_64-unknown-linux-gnu",
                        profile="v1",
                        workers=1,
                        timeout_secs=30,
                        max_memory_mb=256,
                        fuel=10,
                        pin=None,
                    )
            elapsed_int = _time.monotonic() - t0
            interrupter.join(timeout=2.0)
            self.assertLess(elapsed_int, 5.0)
            self.assertEqual(call_count, 1)

            # 4. Atomic cancellation race: if cancellation triggers between
            #    Popen() and killer registration, run_bounded must kill the
            #    newly spawned child PGID immediately and raise
            #    KeyboardInterrupt without waiting for timeout_secs.
            race_token = oracle._CancelToken()
            orig_popen = oracle.subprocess.Popen
            spawned_pids: list[int] = []

            def _racy_popen(*p_args, **p_kwargs):
                proc = orig_popen(*p_args, **p_kwargs)
                spawned_pids.append(proc.pid)
                race_token.cancel_and_kill_all()
                return proc

            t_race = _time.monotonic()
            with mock.patch.object(
                oracle.subprocess, "Popen", side_effect=_racy_popen
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "import time; time.sleep(30)"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=30,
                        max_memory_mb=256,
                        cancel_token=race_token,
                    )
            self.assertLess(_time.monotonic() - t_race, 5.0)
            self.assertEqual(len(spawned_pids), 1)
            self.assertFalse(_pid_alive(spawned_pids[0]))

            # Already-cancelled token must abort before calling Popen.
            with mock.patch.object(
                oracle.subprocess,
                "Popen",
                side_effect=AssertionError("Popen must not be called"),
            ):
                with self.assertRaises(KeyboardInterrupt):
                    oracle.run_bounded(
                        [sys.executable, "-I", "-B", "-c", "pass"],
                        env=oracle.sanitized_child_env(),
                        timeout_secs=10,
                        max_memory_mb=256,
                        cancel_token=race_token,
                    )
