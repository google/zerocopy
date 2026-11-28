# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Warm Lean 4 LSP workspace pool and interactive query operations."""

from __future__ import annotations

from collections import OrderedDict
import contextlib
import os
from pathlib import Path
import queue
import subprocess
import threading
import time
from typing import Any, Callable, Iterator
import weakref

from .client import (
    LspProcess, LspRpcError, build_sandbox_cmd, caller_homes, path_to_uri, py_col_to_utf16,
)
from .discovery import WorkspaceContext, discover_workspace, is_elan_shim
# The Lean source helpers moved to `lean_source.py` are re-exported here so
# that every `anneal_lsp.workspace` name stays importable. `LspProcess` must
# stay a global of this module: `WorkspaceWorker._start` looks it up here, and
# tests patch `anneal_lsp.workspace.LspProcess`.
from .lean_source import (  # noqa: F401
    _ATTR_RE, _BULLET_RE, _DECL_HEAD_RE, _KINDS, _MOD_WORD_RE, _OPEN_SET_RE, _SCOPE_BOUND_RE,
    _SEVS, _SKIP_DIRS, _SORRY_RE, _SORRY_WARN_RE, _WS_RE, _cdiag, _col, _find_in_tok,
    _flatten_syms, _fmt_cand, _logical_lines, _match_decl, _read_regular_text, _req_lean,
    _safe_read_lines, _scan_decls, _walk_lean,
)
from .pool_queries import _PoolQueries


_ALLOW_ENV = frozenset({
    "PATH", "HOME", "USER", "LOGNAME", "LANG", "LC_ALL", "LC_CTYPE",
    "TERM", "TZ", "TMPDIR", "TEMP", "TMP",
})


def _hidden_def_roots(
    worker: WorkspaceWorker, allowed_roots: tuple[Path, ...],
) -> tuple[Path, ...]:
    homes = caller_homes()
    rehide_cands: list[Path] = [
        *homes, *(h / ".local" for h in homes),
        Path("/tmp"), Path("/var/tmp"), Path("/run"), Path("/var/run"),
    ]
    forbid_cands: list[Path] = [*worker.hidden_paths]
    if worker.caller_home is not None:
        rehide_cands.extend([worker.caller_home, worker.caller_home / ".local"])
    if raw_xdg := os.environ.get("XDG_RUNTIME_DIR", "").strip():
        rehide_cands.append(Path(raw_xdg).expanduser())
    if hasattr(os, "getuid"):
        rehide_cands.append(Path(f"/run/user/{os.getuid()}"))
    if env_sock := os.environ.get("ANNEAL_LSP_SOCKET", "").strip():
        forbid_cands.append(Path(os.path.abspath(str(Path(env_sock).expanduser()))).parent)
    out: list[Path] = []
    for c in rehide_cands:
        with contextlib.suppress(OSError):
            res = c.resolve()
            if any(res == ar or res.is_relative_to(ar) for ar in allowed_roots):
                if res not in out:
                    out.append(res)
    for c in forbid_cands:
        with contextlib.suppress(OSError):
            res = c.resolve()
            if any(
                res == ar or res.is_relative_to(ar) or ar.is_relative_to(res)
                for ar in allowed_roots
            ):
                if res not in out:
                    out.append(res)
    return tuple(out)


def _ro_tc(bin_path: Path | None, extra: tuple[Path, ...] = ()) -> list[Path]:
    if bin_path is None:
        return []
    hid: set[Path] = set()
    bases = (
        Path("/"), Path("/usr"), Path("/usr/local"), Path("/bin"), Path("/sbin"),
        Path("/lib"), Path("/lib32"), Path("/lib64"), Path("/etc"),
        Path("/tmp"), Path("/var"), Path("/var/tmp"), Path("/run"), Path("/var/run"),
        Path("/home"), Path("/Users"), Path("/mnt"), Path("/srv"), Path("/opt"),
        *caller_homes(), *extra,
    )
    for base in bases:
        hid.add(base)
        with contextlib.suppress(OSError):
            hid.add(base.expanduser().resolve())
    for hc in (*caller_homes(), *extra):
        for anc in (hc, hc.expanduser()):
            with contextlib.suppress(OSError):
                res = anc.resolve()
                hid.update((res, res / ".local", *res.parents))
    out: list[Path] = []
    for c in (bin_path, bin_path.resolve()):
        par = c.parent
        b = par.parent
        is_tc_root = (
            par.name == "bin"
            and b not in hid
            and ((b / "lib/lean").is_dir() or str(b).startswith("/nix/store/"))
        )
        if is_tc_root:
            out.append(b)
        elif par.name == "bin":
            subs = [par, b / "lib/lean", b / "src/lean", b / "libexec/lean"]
            if b not in hid and is_elan_shim(c):
                subs.extend((b / "toolchains", b / "settings.toml", b / "env"))
            out.extend(s for s in subs if s != b and s not in hid and s.exists())
        elif par not in hid and par.exists():
            out.append(par)
        elif c.exists():
            out.append(c)
    return out


def _has_fatal(proc: list[Any]) -> bool:
    return any(isinstance(x, dict) and x.get("kind") == 2 for x in proc)


def _stat_sig(path: Path) -> tuple[int, int, int] | None:
    try:
        st = path.stat()
        return (st.st_ino, st.st_mtime_ns, st.st_size)
    except OSError:
        return None


def _close_all(workers: list[WorkspaceWorker]) -> None:
    for w in workers:
        w.close()


class _ProcSpawner:
    """Keep `bwrap --die-with-parent` tied to pool, not ephemeral threads."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._q: queue.Queue[Any] | None = None
        self._thread: threading.Thread | None = None

    @staticmethod
    def _run(q: queue.Queue[Any]) -> None:
        while (item := q.get()) is not None:
            cmd, cwd, env, rq = item
            try:
                proc = subprocess.Popen(
                    cmd, cwd=str(cwd), env=env, stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    start_new_session=True,
                )
                rq.put((proc, None))
            except BaseException as exc:
                rq.put((None, exc))

    def spawn(self, cmd: list[str], cwd: Path, env: dict[str, str]) -> subprocess.Popen[bytes]:
        with self._lock:
            if self._q is None or self._thread is None or not self._thread.is_alive():
                q: queue.Queue[Any] = queue.Queue()
                th = threading.Thread(target=self._run, args=(q,), daemon=True)
                th.start()
                self._q, self._thread = q, th
            q = self._q
        rq: queue.Queue[tuple[Any, BaseException | None]] = queue.Queue(maxsize=1)
        q.put((cmd, cwd, env, rq))
        proc, exc = rq.get()
        if exc is not None:
            raise exc
        assert proc is not None
        return proc

    def close(self) -> None:
        with self._lock:
            q, th = self._q, self._thread
            self._q, self._thread = None, None
        if q is not None:
            q.put(None)
        if th is not None:
            th.join(timeout=2.0)


class WorkspaceWorker:
    """Single warm `lean --server` or `lake serve --` child process."""

    def __init__(
        self, ctx: WorkspaceContext, *, sandbox: bool = True,
        memory_mb: int | None = None, caller_home: Path | None = None,
        hidden_paths: list[Path] | tuple[Path, ...] = (),
        spawn_fn: Callable[[list[str], Path, dict[str, str]], subprocess.Popen[bytes]]
        | None = None,
    ) -> None:
        if ctx.lean_bin is None:
            raise FileNotFoundError("Lean binary unavailable for workspace worker.")
        if ctx.mode == "lake" and ctx.lake_bin is None:
            raise FileNotFoundError(
                f"Lake workspace `{ctx.root}` requires a matching `lake` binary "
                f"beside `{ctx.lean_bin}`."
            )
        self.ctx, self.sandbox, self.memory_mb = ctx, sandbox, memory_mb
        self.caller_home = caller_home.expanduser().resolve() if caller_home else None
        self.hidden_paths, self._spawn_fn = tuple(hidden_paths), spawn_fn
        self.fingerprint = (*ctx.fingerprint(), sandbox, memory_mb, str(self.caller_home or ""))
        self.last_used, self.lock = time.monotonic(), threading.RLock()
        self._cond = threading.Condition()
        self._in_flight, self._retired, self._closed, self._seq = 0, False, False, 0
        self._docs: OrderedDict[str, tuple[int, str]] = OrderedDict()
        self._diags: dict[str, tuple[int | None, int, list[dict[str, Any]]]] = {}
        self._prog: dict[str, tuple[int, list[Any]]] = {}
        self._sync_ok: dict[str, int] = {}
        self._worker_errors: dict[str, tuple[int, str]] = {}
        self._source_sigs: dict[Path, tuple[int, int, int] | None] = {
            sp: _stat_sig(sp) for sp in ctx.source_paths
        }
        self.sandboxed = False
        self.lsp = self._start()

    def deps_stale(self, target: Path, source_paths: tuple[Path, ...]) -> bool:
        t_res = target.resolve()
        for sp, old_sig in self._source_sigs.items():
            if sp != t_res and _stat_sig(sp) != old_sig:
                return True
        return any(sp != t_res and sp not in self._source_sigs for sp in source_paths)

    def _on_notify(self, method: str, params: Any) -> None:
        if not isinstance(params, dict):
            return
        with self._cond:
            if method == "textDocument/publishDiagnostics":
                if not isinstance(u := params.get("uri"), str):
                    return
                rv = params.get("version")
                doc = self._docs.get(u)
                if isinstance(rv, int) and doc is not None and rv < doc[0]:
                    return
                self._seq += 1
                self._diags[u] = (
                    rv if isinstance(rv, int) else None, self._seq,
                    list(params.get("diagnostics") or []),
                )
            elif method == "$/lean/fileProgress":
                doc_p = params.get("textDocument") or {}
                if not isinstance(u := doc_p.get("uri"), str):
                    return
                ver = doc_p.get("version")
                cur = self._docs.get(u)
                if isinstance(ver, int) and cur is not None and ver < cur[0]:
                    return
                self._seq += 1
                prev = self._prog.get(u, (0, []))[0]
                proc = list(params.get("processing") or [])
                eff_ver = ver if isinstance(ver, int) else (cur[0] if cur is not None else prev)
                self._prog[u] = (eff_ver, proc)
            else:
                return
            self._cond.notify_all()

    def _on_rpc_response(self) -> None:
        with self._cond:
            self._cond.notify_all()

    def _start(self) -> LspProcess:
        assert self.ctx.lean_bin is not None
        env = {k: v for k, v in os.environ.items() if k in _ALLOW_ENV}
        if self.caller_home is not None:
            env["HOME"] = str(self.caller_home)
        for k, v in (("LEAN_PATH", self.ctx.lean_path), ("LEAN_SRC_PATH", self.ctx.lean_src_path)):
            if v:
                env[k] = os.pathsep.join(str(p) for p in v)
        path_parts = [seg for seg in env.get("PATH", "").split(os.pathsep) if seg]
        env["PATH"] = os.pathsep.join([str(self.ctx.lean_bin.parent), *path_parts])
        eh = (self.caller_home,) if self.caller_home is not None else ()
        mem = self.memory_mb if self.memory_mb is not None else 4096
        ro = [self.ctx.root, *_ro_tc(self.ctx.lean_bin, eh),
              *self.ctx.lean_path, *self.ctx.lean_src_path]
        if self.ctx.artifacts_dir is not None:
            ro.append(self.ctx.artifacts_dir)
        wr: list[Path] = []
        if self.ctx.mode == "lake":
            if self.ctx.lake_bin is None:
                raise FileNotFoundError(
                    f"Lake workspace `{self.ctx.root}` requires a matching `lake` binary."
                )
            cmd = [str(self.ctx.lake_bin), "serve", "--", "-M", str(mem)]
            ro.extend(_ro_tc(self.ctx.lake_bin, eh))
            if (dl := self.ctx.root / ".lake").is_dir() and not dl.is_symlink():
                wr.append(dl)
        else:
            cmd = [str(self.ctx.lean_bin), "--server", "-M", str(mem)]
        caps = {"textDocument": {"hover": {"contentFormat": ["markdown", "plaintext"]},
                                 "completion": {"completionItem": {"snippetSupport": False}},
                                 "documentSymbol": {"hierarchicalDocumentSymbolSupport": True}}}
        raw_ld = os.environ.get("LD_LIBRARY_PATH", "")
        safe_ld = os.pathsep.join(
            seg for seg in raw_ld.split(os.pathsep) if seg and os.path.isabs(seg)
        )
        inner_env = {"LD_LIBRARY_PATH": safe_ld} if safe_ld else None
        wrapped, self.sandboxed = build_sandbox_cmd(
            cmd, ro_binds=ro, writable_dirs=wr, hidden_homes=list(eh),
            hidden_paths=list(self.hidden_paths), inner_env=inner_env,
            work_dir=self.ctx.root, sandbox=self.sandbox,
        )
        if self.sandboxed:
            for k in ("TMPDIR", "TEMP", "TMP"):
                env.pop(k, None)
        if safe_ld and not self.sandboxed:
            env["LD_LIBRARY_PATH"] = safe_ld
        proc_cwd = Path("/") if self.sandboxed else self.ctx.root
        proc = LspProcess(
            wrapped, cwd=proc_cwd, env=env, on_notification=self._on_notify,
            on_response=self._on_rpc_response, spawn_fn=self._spawn_fn,
        )
        try:
            init_p = {"processId": os.getpid(), "rootUri": path_to_uri(self.ctx.root),
                      "capabilities": caps}
            proc.request("initialize", init_p, 30.0)
            proc.notify("initialized", {})
            return proc
        except Exception as exc:
            proc.close()
            if self.sandboxed:
                raise RuntimeError(
                    f"bwrap sandbox failed (`--no-sandbox` / `ANNEAL_LSP_NO_SANDBOX=1`): {exc}"
                ) from exc
            raise

    def close(self) -> None:
        with self.lock:
            if not self._closed:
                self._closed = True
                self.lsp.close()

    def worker_error(self, uri: str) -> str | None:
        if (err := self._worker_errors.get(uri)) is None:
            return None
        doc = self._docs.get(uri)
        return err[1] if doc is None or err[0] >= doc[0] else None

    def _set_worker_error(self, uri: str, ver: int, msg: str) -> None:
        with self._cond:
            self._worker_errors[uri] = (ver, msg)

    def _handle_wfd_rpc_error(self, uri: str, ver: int, exc: RuntimeError) -> bool:
        """Record non--32601 worker crashes; return True only for fallback."""
        if hasattr(self.lsp, "is_alive") and not self.lsp.is_alive():
            self._set_worker_error(uri, ver, f"Lean LSP process exited unexpectedly: {exc}")
            return False
        if isinstance(exc, LspRpcError) and exc.code != -32601:
            self._set_worker_error(uri, ver, str(exc))
            return False
        return True

    def _wait_ready(self, uri: str, ver: int, start_seq: int, timeout_s: float) -> bool:
        deadline = time.monotonic() + timeout_s
        if not hasattr(self.lsp, "start_request"):
            try:
                self.lsp.request(
                    "textDocument/waitForDiagnostics", {"uri": uri, "version": ver}, timeout_s
                )
                return True
            except TimeoutError:
                return False
            except RuntimeError as exc:
                if not self._handle_wfd_rpc_error(uri, ver, exc):
                    return False
        else:
            try:
                rid, q = self.lsp.start_request(
                    "textDocument/waitForDiagnostics", {"uri": uri, "version": ver}
                )
            except RuntimeError as exc:
                self._set_worker_error(uri, ver, f"Lean LSP process exited unexpectedly: {exc}")
                return False
            fatal_at: float | None = None
            fallback = False
            try:
                with self._cond:
                    while True:
                        with contextlib.suppress(queue.Empty):
                            msg = q.get_nowait()
                            self.lsp.unpack_reply("textDocument/waitForDiagnostics", msg)
                            return True
                        if not self.lsp.is_alive():
                            self._worker_errors[uri] = (
                                ver, "Lean LSP process exited unexpectedly.",
                            )
                            return False
                        prog = self._prog.get(uri)
                        if prog is not None and prog[0] >= ver and _has_fatal(prog[1]):
                            if fatal_at is None:
                                fatal_at = time.monotonic()
                        else:
                            fatal_at = None
                        w_end = deadline if fatal_at is None else min(deadline, fatal_at + 1.0)
                        rem = w_end - time.monotonic()
                        if rem <= 0:
                            with contextlib.suppress(queue.Empty):
                                msg = q.get_nowait()
                                self.lsp.unpack_reply("textDocument/waitForDiagnostics", msg)
                                return True
                            if fatal_at is not None:
                                self._worker_errors[uri] = (
                                    ver,
                                    "Lean file worker crashed (`fatalError` without "
                                    "`waitForDiagnostics` response).",
                                )
                            return False
                        self._cond.wait(timeout=min(0.25, rem))
            except RuntimeError as exc:
                if not self._handle_wfd_rpc_error(uri, ver, exc):
                    return False
                fallback = True
            finally:
                self.lsp.finish_request(rid)
            if not fallback:
                return False
        with self._cond:
            while True:
                prog = self._prog.get(uri)
                if prog is not None and prog[0] >= ver and (not prog[1] or _has_fatal(prog[1])):
                    break
                if not self.lsp.is_alive() or (rem := deadline - time.monotonic()) <= 0:
                    return False
                self._cond.wait(timeout=min(0.25, rem))
            if prog is not None and prog[0] >= ver and _has_fatal(prog[1]):
                return True
            d_end = time.monotonic() + min(0.25, max(0.0, deadline - time.monotonic()))
            while True:
                de = self._diags.get(uri)
                if de and de[1] > start_seq and (de[0] is None or de[0] >= ver):
                    return True
                if not self.lsp.is_alive():
                    return False
                if (rem := d_end - time.monotonic()) <= 0:
                    return True
                self._cond.wait(timeout=min(0.05, rem))

    def sync_text(self, path: Path, text: str, *, wait_s: float = 45.0) -> tuple[str, float, bool]:
        t0, uri = time.monotonic(), path_to_uri(path)
        with self.lock:
            self._source_sigs.setdefault(path.resolve(), _stat_sig(path))
            self.last_used = t0
            prev = self._docs.get(uri)
            if prev is None or prev[1] != text:
                evict_u: str | None = None
                reopen = prev is not None and uri in self._worker_errors
                ver = 1 if prev is None else prev[0] + 1
                is_new = prev is None or reopen
                with self._cond:
                    if prev is None and len(self._docs) >= 8:
                        evict_u, _ = self._docs.popitem(last=False)
                        self._diags.pop(evict_u, None)
                        self._prog.pop(evict_u, None)
                        self._sync_ok.pop(evict_u, None)
                        self._worker_errors.pop(evict_u, None)
                    self._worker_errors.pop(uri, None)
                    self._diags.pop(uri, None)
                    self._sync_ok.pop(uri, None)
                    self._docs[uri] = (ver, text)
                    self._docs.move_to_end(uri)
                    self._prog[uri] = (ver, [{"pending": True}])
                    start_seq = self._seq
                td = {"uri": uri, "version": ver}
                msg = ({"textDocument": {**td, "languageId": "lean4", "text": text}} if is_new
                       else {"textDocument": td, "contentChanges": [{"text": text}]})
                try:
                    if hasattr(self.lsp, "is_alive") and not self.lsp.is_alive():
                        raise RuntimeError("LSP process is not running")
                    if evict_u is not None:
                        self.lsp.notify(
                            "textDocument/didClose", {"textDocument": {"uri": evict_u}}
                        )
                    if reopen:
                        self.lsp.notify(
                            "textDocument/didClose", {"textDocument": {"uri": uri}}
                        )
                    self.lsp.notify(
                        "textDocument/didOpen" if is_new else "textDocument/didChange", msg
                    )
                except RuntimeError as exc:
                    self._set_worker_error(uri, ver, f"Lean LSP process exited unexpectedly: {exc}")
                    return uri, round((time.monotonic() - t0) * 1000.0, 1), False
                ok = self._wait_ready(uri, ver, start_seq, wait_s)
                if ok:
                    self._sync_ok[uri] = ver
            else:
                self._docs.move_to_end(uri)
                if self.worker_error(uri) is not None:
                    ok = False
                else:
                    with self._cond:
                        start_seq = self._seq
                        prog = self._prog.get(uri)
                    pend = bool(prog and prog[0] >= prev[0] and prog[1] and not _has_fatal(prog[1]))
                    confirmed = self._sync_ok.get(uri, -1) >= prev[0]
                    if pend or not confirmed:
                        ok = self._wait_ready(uri, prev[0], start_seq, wait_s)
                        if ok:
                            self._sync_ok[uri] = prev[0]
                    else:
                        ok = True
            return uri, round((time.monotonic() - t0) * 1000.0, 1), ok

    def diags(self, uri: str) -> list[dict[str, Any]]:
        with self._cond:
            de = self._diags.get(uri)
            if de is None:
                return []
            doc = self._docs.get(uri)
            if doc is not None and de[0] is not None and de[0] != doc[0]:
                return []
            return list(de[2])

    def has_fatal_progress(self, uri: str) -> bool:
        with self._cond:
            prog = self._prog.get(uri)
            if prog is None:
                return False
            doc = self._docs.get(uri)
            if doc is not None and prog[0] != doc[0]:
                return False
            return _has_fatal(prog[1])



class WorkspacePool(_PoolQueries):
    """Thread-safe LRU pool of warm Lean 4 LSP workers."""

    def __init__(
        self, *, max_workers: int = 4, idle_ttl_s: float = 900.0,
        sandbox: bool = True, use_env: bool = True, default_memory_mb: int | None = None,
        default_artifacts_dir: Path | None = None,
        default_extra_lean_path: list[Path] | tuple[Path, ...] = (),
        hidden_paths: list[Path] | tuple[Path, ...] = (),
    ) -> None:
        self.max_workers, self.idle_ttl_s = max(1, max_workers), idle_ttl_s
        self.sandbox, self.use_env, self.default_memory_mb = sandbox, use_env, default_memory_mb
        self.default_artifacts_dir = default_artifacts_dir
        self.default_extra_lean_path = tuple(default_extra_lean_path)
        self.hidden_paths = tuple(hidden_paths)
        self._lock = threading.Lock()
        self._pool_cond = threading.Condition(self._lock)
        self._workers: OrderedDict[tuple[str, str, bool], WorkspaceWorker] = OrderedDict()
        self._retired_workers: set[WorkspaceWorker] = set()
        self._starting = 0
        self._last_activity = time.monotonic()
        self._spawner = _ProcSpawner()
        self._spawner_fin = weakref.finalize(self, self._spawner.close)

    def _retire_unlocked(self, w: WorkspaceWorker, sink: list[WorkspaceWorker]) -> None:
        w._retired = True
        self._retired_workers.add(w)
        if w._in_flight == 0:
            sink.append(w)

    def _retire_dead_worker(self, worker: WorkspaceWorker) -> None:
        with self._pool_cond:
            for k, w in list(self._workers.items()):
                if w is worker:
                    self._workers.pop(k)
            worker._retired = True
            self._retired_workers.add(worker)
            self._pool_cond.notify_all()

    def _live_count_unlocked(self) -> int:
        return len(self._workers) + len(self._retired_workers) + self._starting

    def _close_retired(self, workers: list[WorkspaceWorker]) -> None:
        if not workers:
            return
        try:
            _close_all(workers)
        finally:
            with self._pool_cond:
                for w in workers:
                    self._retired_workers.discard(w)
                self._pool_cond.notify_all()

    def _reuse_unlocked(
        self, key: tuple[str, str, bool], fp: tuple[Any, ...], sink: list[WorkspaceWorker],
        target: Path, source_paths: tuple[Path, ...],
    ) -> WorkspaceWorker | None:
        if (ex := self._workers.get(key)) is not None:
            fresh = not ex.deps_stale(target, source_paths)
            if ex.fingerprint == fp and fresh and ex.lsp.is_alive() and not ex._retired:
                self._workers.move_to_end(key)
                ex.last_used, ex._in_flight = time.monotonic(), ex._in_flight + 1
                return ex
            self._retire_unlocked(self._workers.pop(key), sink)
        return None

    def evict_idle(self) -> int:
        evicted, now = [], time.monotonic()
        with self._pool_cond:
            for k in [k for k, w in self._workers.items() if w._in_flight == 0
                      and ((now - w.last_used) > self.idle_ttl_s or not w.lsp.is_alive())]:
                self._retire_unlocked(self._workers.pop(k), evicted)
            cnt = len(self._workers)
        self._close_retired(evicted)
        return cnt

    def is_idle_expired(self) -> bool:
        with self._pool_cond:
            idle_empty = not self._workers and not self._retired_workers and self._starting == 0
            return idle_empty and (time.monotonic() - self._last_activity) > self.idle_ttl_s

    def _acquire(self, file_path: str | Path, **kw: Any) -> WorkspaceWorker:
        sbx = self.sandbox if kw.get("sandbox") is None else (self.sandbox or bool(kw["sandbox"]))
        eff_mem = self.default_memory_mb if kw.get("memory_mb") is None else kw["memory_mb"]
        ch_lex = (
            Path(os.path.abspath(str(kw["caller_home"].expanduser())))
            if kw.get("caller_home") is not None else None
        )
        ch = ch_lex.resolve() if ch_lex is not None else None
        eff_art = (
            kw.get("artifacts_dir")
            if kw.get("artifacts_dir") is not None else self.default_artifacts_dir
        )
        eff_lp = [*self.default_extra_lean_path, *(kw.get("extra_lean_path") or ())] or None
        ctx = discover_workspace(
            file_path,
            artifacts_dir=eff_art,
            extra_lean_path=eff_lp,
            extra_lean_src_path=kw.get("extra_lean_src_path"),
            explicit_lean=kw.get("explicit_lean"),
            explicit_lake=kw.get("explicit_lake"),
            cargo_target_dir=kw.get("cargo_target_dir"),
            test_install_root=kw.get("test_install_root"),
            require_lean=True,
            use_env=self.use_env,
            home=ch_lex,
        )
        key, fp = (ctx.mode, str(ctx.root), sbx), (*ctx.fingerprint(), sbx, eff_mem, str(ch or ""))
        self.evict_idle()
        deadline = time.monotonic() + float(kw.get("acquire_timeout_s") or 120.0)
        t_path = Path(file_path).resolve()
        while True:
            evicted: list[WorkspaceWorker] = []
            hit: WorkspaceWorker | None = None
            start_slot = False
            with self._pool_cond:
                self._last_activity = time.monotonic()
                if (hit := self._reuse_unlocked(
                    key, fp, evicted, t_path, ctx.source_paths
                )) is None:
                    for k in [k for k, w in self._workers.items() if w._in_flight == 0]:
                        if self._live_count_unlocked() - len(evicted) < self.max_workers:
                            break
                        self._retire_unlocked(self._workers.pop(k), evicted)
                    if not evicted and self._live_count_unlocked() < self.max_workers:
                        self._starting += 1
                        start_slot = True
            self._close_retired(evicted)
            if hit is not None:
                return hit
            if start_slot:
                break
            if not evicted:
                ev2: list[WorkspaceWorker] = []
                with self._pool_cond:
                    if (hit := self._reuse_unlocked(
                        key, fp, ev2, t_path, ctx.source_paths
                    )) is None:
                        if self._live_count_unlocked() >= self.max_workers:
                            if (rem := deadline - time.monotonic()) <= 0:
                                raise TimeoutError("Timed out waiting for Lean LSP worker slot.")
                            self._pool_cond.wait(timeout=min(0.25, rem))
                self._close_retired(ev2)
                if hit is not None:
                    return hit
        try:
            worker = WorkspaceWorker(
                ctx, sandbox=sbx, memory_mb=eff_mem, caller_home=ch,
                hidden_paths=self.hidden_paths, spawn_fn=self._spawner.spawn,
            )
        except Exception:
            with self._pool_cond:
                self._starting = max(0, self._starting - 1)
                self._pool_cond.notify_all()
            raise
        evicted = []
        dup_worker = False
        with self._pool_cond:
            self._starting = max(0, self._starting - 1)
            if hit := self._reuse_unlocked(key, fp, evicted, t_path, ctx.source_paths):
                dup_worker = True
                out = hit
            else:
                worker._in_flight, self._workers[key] = 1, worker
                out = worker
            self._pool_cond.notify_all()
        if dup_worker:
            worker.close()
        self._close_retired(evicted)
        return out

    @contextlib.contextmanager
    def _checkout(self, file_path: str | Path, **wkw: Any) -> Iterator[WorkspaceWorker]:
        worker = self._acquire(file_path, **wkw)
        try:
            yield worker
        finally:
            close_now = False
            with self._pool_cond:
                worker._in_flight = max(0, worker._in_flight - 1)
                if worker._retired and worker._in_flight == 0:
                    self._retired_workers.add(worker)
                    close_now = True
                else:
                    self._pool_cond.notify_all()
            if close_now:
                self._close_retired([worker])

    def restart(self, root: str | None = None) -> dict[str, Any]:
        restarted, to_close = [], []
        with self._pool_cond:
            tgt = str(Path(root).expanduser().resolve()) if root and root != "all" else None
            for k in [k for k in self._workers if tgt is None or k[1] == tgt]:
                restarted.append(k[1])
                self._retire_unlocked(self._workers.pop(k), to_close)
            self._pool_cond.notify_all()
        self._close_retired(to_close)
        return {"restarted": restarted, "text": f"Restarted {len(restarted)} worker(s)."}

    def shutdown(self) -> None:
        try:
            self.restart("all")
        finally:
            self._spawner.close()

    @staticmethod
    def _req_err(worker: WorkspaceWorker, exc: RuntimeError) -> str:
        alive = not hasattr(worker.lsp, "is_alive") or worker.lsp.is_alive()
        prefix = "Lean LSP request failed" if alive else "Lean LSP process exited unexpectedly"
        return f"{prefix}: {exc}"

    def _pos_req(
        self, method: str, file: str, line: int, *, symbol: str | None = None,
        column: int | None = None, eol_default: bool = False, wkw: dict[str, Any] | None = None,
    ) -> tuple[Path, int, int, Any, tuple[Path, ...], tuple[Path, ...], bool, str | None]:
        p = _req_lean(file, home=(wkw or {}).get("caller_home"))
        with self._checkout(p, **(wkw or {})) as worker, worker.lock:
            text = p.read_text("utf-8", errors="replace")
            uri, _, ok = worker.sync_text(p, text)
            lines = _logical_lines(text)
            if not (1 <= line <= len(lines)):
                raise ValueError(f"line {line} out of range 1..{len(lines)}")
            raw = lines[line - 1]
            eol = symbol is None and column is None and eol_default
            col = len(raw.rstrip()) if eol else _col(raw, symbol, column)
            pos = {"line": line - 1, "character": py_col_to_utf16(raw, col)}
            req = {"textDocument": {"uri": uri}, "position": pos}
            ctx = worker.ctx
            eh = (worker.caller_home,) if worker.caller_home else ()
            roots = tuple(
                r.resolve()
                for r in (ctx.root, *ctx.lean_src_path, *_ro_tc(ctx.lean_bin, eh))
                if r.exists()
            )
            excluded = _hidden_def_roots(worker, roots)
            w_err = worker.worker_error(uri)
            res, timed_out = None, (not ok) and not w_err
            if ok:
                try:
                    res = worker.lsp.request(method, req, 10.0)
                except TimeoutError:
                    timed_out = True
                except RuntimeError as exc:
                    w_err = w_err or self._req_err(worker, exc)
            return p, line, col + 1, res, roots, excluded, timed_out, w_err

    def _goal_at(
        self, w: WorkspaceWorker, uri: str, line0: int, raw: str, col: int, tm: float = 10.0
    ) -> list[Any]:
        pos = {"line": line0, "character": py_col_to_utf16(raw, col)}
        res = w.lsp.request("$/lean/plainGoal", {"textDocument": {"uri": uri}, "position": pos}, tm)
        return list((res or {}).get("goals") or []) if isinstance(res, dict) else []
