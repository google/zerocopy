# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Warm Lean 4 LSP workspace pool and interactive query operations."""

from __future__ import annotations

from collections import Counter, OrderedDict
import contextlib
import os
from pathlib import Path
import queue
import re
import stat
import subprocess
import threading
import time
from typing import Any, Callable, Iterator
import weakref

from .client import (
    LspProcess, LspRpcError, build_sandbox_cmd, caller_homes, mask_lean_comments,
    middle_clip, path_to_uri, py_col_to_utf16, uri_to_path, utf16_to_py_col,
)
from .discovery import (
    WorkspaceContext, discover_workspace, is_elan_shim, validate_no_symlink_target,
)

_WS_RE = re.compile(r"[ \t]+")
_ATTR_RE = re.compile(r"@\[[^\]\n]*\]")
_MOD_WORD_RE = re.compile(
    r"(?:private|protected|public|noncomputable|partial|unsafe|nonrec|local|scoped|meta)(?=[ \t])"
)
_OPEN_SET_RE = re.compile(r"(?:set_option|open)(?=[ \t])")
_DECL_HEAD_RE = re.compile(
    r"(inductive|structure|class|def|abbrev|theorem|lemma|instance|opaque|axiom|example)\b"
    r"(?:\s+((?:_root_\.)?(?:«[^»]+»|[^\s:({[]+?))(?:\.\{[^}]*\})?"
    r"(?=\s|:|\(|\{|\[|$))?"
)
_SCOPE_BOUND_RE = re.compile(r"^\s*(?:end|namespace|section|mutual|#)\b")
_SORRY_RE = re.compile(
    r"(?<![\w'.«`])((?:(?:_root_|«_root_»)\.)?"
    r"(?:sorry|admit|sorryAx|«sorryAx»))(?![\w'»?])"
)
_SORRY_WARN_RE = re.compile(
    r"\bdeclaration uses [`'«]?(?:sorry|sorryAx|admit)[`'»]?", re.IGNORECASE
)
_BULLET_RE = re.compile(r"^(\s*(?:[·•|]\s*)?)")
_SKIP_DIRS = frozenset({".git", ".lake", "target", "vendor", "__pycache__"})
_SEVS = {1: "error", 2: "warning", 3: "info", 4: "hint"}
_KINDS = {5: "class", 6: "method", 12: "def", 13: "var", 23: "struct", 26: "param"}
_ALLOW_ENV = frozenset({
    "PATH", "HOME", "USER", "LOGNAME", "LANG", "LC_ALL", "LC_CTYPE",
    "TERM", "TZ", "TMPDIR", "TEMP", "TMP",
})


def _find_in_tok(line: str, pos: int) -> int | None:
    n, idx = len(line), pos
    while (idx := line.find("in", idx)) >= 0:
        if idx > pos and line[idx - 1] in " \t" and (idx + 2 == n or line[idx + 2] in " \t"):
            return idx + 2
        idx += 1
    return None


def _match_decl(line: str) -> re.Match[str] | None:
    pos, n = 0, len(line)
    while pos < n:
        if m := _WS_RE.match(line, pos):
            pos = m.end()
        elif m := _ATTR_RE.match(line, pos):
            pos = m.end()
        elif m := _MOD_WORD_RE.match(line, pos):
            pos = m.end()
        elif m := _OPEN_SET_RE.match(line, pos):
            if (nxt := _find_in_tok(line, m.end())) is None:
                break
            pos = nxt
        else:
            break
    return _DECL_HEAD_RE.match(line, pos)


def _logical_lines(text: str) -> list[str]:
    return text.replace("\r\n", "\n").replace("\r", "\n").split("\n")


def _read_regular_text(path: Path, *, max_bytes: int = 16 * 1024 * 1024) -> str | None:
    """Read UTF-8 text from a regular non-symlink file without blocking on FIFOs."""
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, flags)
    except OSError:
        return None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode) or st.st_size > max_bytes:
            return None
        with os.fdopen(fd, "r", encoding="utf-8", errors="replace") as fh:
            fd = -1
            return fh.read()
    except OSError:
        return None
    finally:
        if fd >= 0:
            with contextlib.suppress(OSError):
                os.close(fd)


def _safe_read_lines(
    raw_path: str, allowed_roots: tuple[Path, ...], excluded_roots: tuple[Path, ...] = (),
) -> list[str] | None:
    """Read regular non-symlink `.lean` source lines inside approved unhidden roots."""
    cand = Path(os.path.abspath(raw_path))
    try:
        if cand.is_symlink():
            return None
        res = cand.resolve()
        if res.suffix != ".lean" or not any(res.is_relative_to(r) for r in allowed_roots):
            return None
        if any(res == ex or res.is_relative_to(ex) for ex in excluded_roots):
            return None
    except OSError:
        return None
    raw = _read_regular_text(res)
    return _logical_lines(raw) if raw is not None else None


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


def _req_lean(file: str, *, home: Path | None = None) -> Path:
    p = validate_no_symlink_target(file, home=home, kind="Lean file")
    if not p.is_file():
        raise FileNotFoundError(f"Lean file not found: {p}")
    if p.suffix != ".lean":
        raise ValueError(f"Expected a `.lean` source file: {p}")
    return p


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


def _col(raw: str, sym: str | None = None, col: int | None = None) -> int:
    if isinstance(sym, str) and sym:
        if (i := raw.find(sym)) >= 0 or (i := raw.lower().find(sym.lower())) >= 0:
            return i
    return max(0, col - 1) if isinstance(col, int) else (len(raw) - len(raw.lstrip()))


def _cdiag(d: dict[str, Any], lines: list[str] | None = None) -> dict[str, Any]:
    s = d.get("range", {}).get("start", {})
    ln0, u16 = int(s.get("line", 0)), int(s.get("character", 0))
    col0 = utf16_to_py_col(lines[ln0], u16) if lines and 0 <= ln0 < len(lines) else u16
    return {"severity": _SEVS.get(int(d.get("severity", 1)), "error"),
            "line": ln0 + 1, "column": col0 + 1, "message": str(d.get("message", "")).strip()}


def _scan_decls(path: Path) -> list[dict[str, Any]]:
    if (raw := _read_regular_text(path)) is None:
        return []
    orig = _logical_lines(raw)
    clean = _logical_lines(mask_lean_comments(raw)) + [""] * len(orig)
    out: list[dict[str, Any]] = []
    for i, (ln, cln) in enumerate(zip(orig, clean), 1):
        if m := _match_decl(cln):
            name = ln[m.start(2) : m.end(2)] if m.group(2) is not None else "<anonymous>"
            out.append({"kind": m.group(1), "name": name, "line": i, "signature": ln.strip()})
    return out


def _walk_lean(root: Path) -> Iterator[Path]:
    for cur, dirs, files in os.walk(root):
        dirs[:] = [
            d for d in sorted(dirs)
            if d not in _SKIP_DIRS and not (Path(cur) / d).is_symlink()
        ]
        for fn in sorted(files):
            if fn.endswith(".lean"):
                fp = Path(cur) / fn
                with contextlib.suppress(OSError):
                    if stat.S_ISREG(fp.lstat().st_mode):
                        yield fp


def _fmt_cand(raw: str, sorry_m: re.Match[str] | None, cand: str) -> tuple[str, int]:
    cls = cand.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    if sorry_m:
        lead, tail = raw[: sorry_m.start(1)], raw[sorry_m.end(1) :]
    else:
        bm = _BULLET_RE.match(raw)
        ok_b = bm and not cand.lstrip().startswith(("·", "•", "|"))
        lead, tail = (bm.group(1) if ok_b else raw[: len(raw) - len(raw.lstrip())]), ""
    cont = lead if not lead.strip() else re.sub(r"[^\t ]", " ", lead)
    body = "\n".join((cont + s if s else "") if i else s for i, s in enumerate(cls))
    ec = len(lead) + len(cls[0]) if len(cls) == 1 else (len(cont) + len(cls[-1]) if cls[-1] else 0)
    return lead + body + tail, ec


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


def _flatten_syms(nodes: list[Any], out: list[dict[str, Any]], depth: int = 0) -> None:
    for n in nodes:
        if isinstance(n, dict):
            rng = n.get("selectionRange") or n.get("range") or {}
            out.append({
                "name": str(n.get("name", "")), "kind": _KINDS.get(int(n.get("kind") or 0), "decl"),
                "detail": str(n.get("detail") or ""),
                "line": int(rng.get("start", {}).get("line", 0)) + 1, "depth": depth,
            })
            if isinstance(n.get("children"), list):
                _flatten_syms(n["children"], out, depth + 1)


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


class WorkspacePool:
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

    def diagnostics(self, file: str, *, severity: str = "all", **wkw: Any) -> dict[str, Any]:
        if severity not in ("all", "warning", "error"):
            raise ValueError(
                f"Invalid `severity`: {severity!r}; expected 'all', 'warning', or 'error'."
            )
        p = _req_lean(file, home=wkw.get("caller_home"))
        with self._checkout(p, **wkw) as worker, worker.lock:
            text = p.read_text("utf-8", errors="replace")
            uri, ms, ok = worker.sync_text(p, text)
            raw_diags, fatal = worker.diags(uri), worker.has_fatal_progress(uri)
            w_err = worker.worker_error(uri)
            ctx, pid, sbx = worker.ctx, worker.lsp.proc.pid, worker.sandboxed
            lines = _logical_lines(text)
            clean = _logical_lines(mask_lean_comments(text)) + [""] * len(lines)
            sorrys = [
                (i, r.strip(), m.start(1))
                for i, (r, c) in enumerate(zip(lines, clean), 1)
                for m in _SORRY_RE.finditer(c)
            ]
            sgoals: list[dict[str, Any]] = []
            goal_timed_out = False
            if ok:
                for ln, _, col in sorrys[:8]:
                    gs, g_to = [], False
                    try:
                        gs = self._goal_at(worker, uri, ln - 1, lines[ln - 1], col, 4.0)
                    except TimeoutError:
                        g_to = goal_timed_out = True
                    except RuntimeError as exc:
                        w_err = w_err or self._req_err(worker, exc)
                        break
                    sgoals.append({"line": ln, "column": col + 1, "goals": gs, "timed_out": g_to})
        all_diags = [_cdiag(d, lines) for d in raw_diags]
        errs = [d for d in all_diags if d["severity"] == "error"]
        warns = [d for d in all_diags if d["severity"] == "warning"]
        diags = (
            all_diags
            if severity == "all"
            else [d for d in all_diags if d["severity"] == severity]
        )
        if w_err and not errs:
            synth = {"severity": "error", "line": 1, "column": 1, "message": w_err}
            if severity in ("all", "error"):
                diags.append(synth)
            errs.append(synth)
        body = [f"File: {p} ({ctx.mode} root={ctx.root}; {ms} ms; pid={pid}; sandbox={sbx})"]
        if w_err:
            body.append(f"Lean file worker error ({len(diags)} partial): {w_err}")
        elif not ok:
            body.append(f"Timed out waiting for Lean diagnostics ({len(diags)} partial).")
        if goal_timed_out:
            body.append("Timed out querying Lean goals for one or more sorry targets.")
        if fatal and not w_err:
            body.append("Fatal import/header failure reported by Lean server.")
        if hint := ctx.missing_artifacts_hint():
            body.append(hint)
        body.append(f"Errors: {len(errs)} | Warnings: {len(warns)} | sorry targets: {len(sorrys)}")
        body.extend(
            f"  L{d['line']}:{d['column']} [{d['severity']}] {d['message']}" for d in diags[:40]
        )
        sg_map = {(g["line"], g["column"]): g for g in sgoals}
        for ln, txt, col in sorrys[:20]:
            body.append(f"  sorry @ L{ln}:{col + 1}: {txt}")
            if (sg := sg_map.get((ln, col + 1))) is not None:
                if sg["timed_out"]:
                    body.append("    goal: timed out")
                elif sg["goals"]:
                    for gi, g in enumerate(sg["goals"][:2], 1):
                        if len(sg["goals"]) > 1:
                            body.append(f"    -- goal {gi}/{len(sg['goals'])} --")
                        body.extend(f"    {gl}" for gl in str(g).splitlines()[:6])
        return {
            "file": str(p), "mode": ctx.mode, "root": str(ctx.root), "sandboxed": sbx,
            "server_pid": pid, "elapsed_ms": ms,
            "completed": ok and not goal_timed_out and not w_err,
            "timed_out": ((not ok) and not w_err) or goal_timed_out, "fatal": fatal,
            "error_count": len(errs), "warning_count": len(warns), "sorry_count": len(sorrys),
            "sorry_lines": [ln for ln, _, _ in sorrys], "sorry_goals": sgoals,
            "diagnostics": diags, "text": middle_clip("\n".join(body)),
        }

    def goal(
        self, file: str, line: int, *, column: int | None = None,
        snippet: str | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p = _req_lean(file, home=wkw.get("caller_home"))
        with self._checkout(p, **wkw) as worker, worker.lock:
            text = p.read_text("utf-8", errors="replace")
            uri, ms, ok = worker.sync_text(p, text)
            w_err = worker.worker_error(uri)
            fatal = worker.has_fatal_progress(uri)
            has_errs = any(int(d.get("severity", 1)) == 1 for d in worker.diags(uri))
            lines = _logical_lines(text)
            if not (1 <= line <= len(lines)):
                raise ValueError(f"line {line} out of range 1..{len(lines)}")
            raw = lines[line - 1]
            sc, ec, fc = len(raw) - len(raw.lstrip()), len(raw.rstrip()), _col(raw, snippet, column)
            cache: dict[int, list[Any]] = {}
            tg: Any = None
            timed_out = (not ok) and not w_err
            if ok:
                try:
                    for c in (sc, fc, ec):
                        if c not in cache:
                            cache[c] = self._goal_at(worker, uri, line - 1, raw, c)
                    pos = {"line": line - 1, "character": py_col_to_utf16(raw, fc)}
                    req = {"textDocument": {"uri": uri}, "position": pos}
                    tg = worker.lsp.request("$/lean/plainTermGoal", req, 10.0)
                except TimeoutError:
                    timed_out, tg = True, None
                except RuntimeError as exc:
                    w_err = w_err or self._req_err(worker, exc)
                    tg = None
        before, focus, after = cache.get(sc, []), cache.get(fc, []), cache.get(ec, [])
        term = tg.get("goal") if isinstance(tg, dict) else None
        if w_err:
            empty_t = f"worker error (goal unknown): {w_err}"
            empty_a = empty_t
        elif timed_out:
            empty_t = empty_a = "timed out (goal unknown)"
        elif fatal:
            empty_t = "no tactic goals (fatal header/import error)"
            empty_a = "no goals (fatal header/import error)"
        elif has_errs:
            empty_t = "no tactic goals (file has errors)"
            empty_a = "no goals (file has errors)"
        else:
            empty_t = "no tactic goals"
            empty_a = "no goals"
        out = [f"File: {p}:{line} ({ms} ms)"]
        if w_err:
            out.append(f"Lean file worker error (goal unknown): {w_err}")
        elif timed_out:
            out.append("Timed out waiting for Lean goal state (partial/stale result).")
        out.append(f"Line {line}: `{raw}`")
        if column is not None or snippet:
            out.extend([f"\n--- Goal at col {fc + 1} ---", "\n\n".join(focus) or empty_t])
        out.extend([
            f"\n--- Goal BEFORE L{line} (col {sc + 1}) ---",
            "\n\n".join(before) or empty_t,
            f"\n--- Goal AFTER L{line} (col {ec + 1}) ---",
            "\n\n".join(after) or empty_a,
        ])
        if term:
            out.append(f"\n--- Term Goal ---\n{term}")
        return {
            "file": str(p), "line": line, "elapsed_ms": ms,
            "completed": ok and not timed_out and not w_err,
            "timed_out": timed_out, "goals_before": before, "goals_focus": focus,
            "goals_after": after, "term_goal": term, "text": middle_clip("\n".join(out)),
        }

    def multi_attempt(
        self, file: str, line: int, tactics: list[str], *,
        candidate_budget_s: float = 190.0, **wkw: Any,
    ) -> dict[str, Any]:
        """Try tactics in memory via `didChange` (advisory; verify via `cargo anneal`)."""
        cleaned = [str(t).strip() for t in tactics if str(t).strip()]
        if not cleaned or len(cleaned) > 12:
            raise ValueError("Provide 1..12 non-empty candidate tactics.")
        p, results = _req_lean(file, home=wkw.get("caller_home")), []
        with self._checkout(p, **wkw) as worker, worker.lock:
            orig = p.read_text("utf-8", errors="replace")
            uri, _, base_ok = worker.sync_text(p, orig)
            orig_lines = _logical_lines(orig)
            if not (1 <= line <= len(orig_lines)):
                raise ValueError(f"line {line} out of range 1..{len(orig_lines)}")
            clean = _logical_lines(mask_lean_comments(orig)) + [""] * len(orig_lines)
            raw, c_tgt = orig_lines[line - 1], clean[line - 1]
            sorry_m = _SORRY_RE.search(c_tgt)
            pcol = sorry_m.start(1) if sorry_m else (len(c_tgt.rstrip()) - len(c_tgt.strip()))
            d0 = 0
            for idx in range(line - 1, -1, -1):
                if (m := _match_decl(cln := clean[idx])) and (idx < line - 1 or m.start(1) < pcol):
                    d0 = idx
                    break
                if idx < line - 1 and _SCOPE_BOUND_RE.match(cln):
                    d0 = idx + 1
                    break
            d1 = len(orig_lines)
            for idx in range(line, len(orig_lines)):
                if _match_decl(cln := clean[idx]) or _SCOPE_BOUND_RE.match(cln):
                    d1 = idx
                    break
            bdiags = worker.diags(uri)
            dl = lambda d: int(d.get("range", {}).get("start", {}).get("line", -9))
            uns = lambda s: s == "unsolved goals" or s.startswith("unsolved goals\n")
            lsp_alive = lambda: not hasattr(worker.lsp, "is_alive") or worker.lsp.is_alive()
            w_err = worker.worker_error(uri) or (
                None if lsp_alive() else "Lean LSP process exited unexpectedly."
            )
            fatal = worker.has_fatal_progress(uri) or not base_ok
            prior = [_cdiag(d, orig_lines) for d in bdiags
                     if d.get("severity") == 1 and not uns(str(d.get("message", "")).strip())
                     and (d0 <= dl(d) < line - 1 or (fatal and 0 <= dl(d) < d0))]
            if not prior and w_err:
                prior = [{"severity": "error", "line": 1, "column": 1, "message": w_err}]
            if prior:
                if not lsp_alive():
                    self._retire_dead_worker(worker)
                results = [{"tactic": c, "evaluated": False, "closes_goal": False, "ok_step": False,
                            "uses_sorry": False, "remaining_goals": [], "errors": prior[:3],
                            "elapsed_ms": 0.0, "timed_out": False} for c in cleaned]
            else:
                berr = Counter((dl(d), str(d.get("message", "")).strip())
                               for d in bdiags if d.get("severity") == 1 and dl(d) != line - 1)
                try:
                    cand_dl = time.monotonic() + max(0.0, float(candidate_budget_s))
                    for cand_idx, cand in enumerate(cleaned):
                        rem = cand_dl - time.monotonic()
                        if rem <= 0:
                            results.append({
                                "tactic": cand, "evaluated": True, "closes_goal": False,
                                "ok_step": False, "uses_sorry": False, "remaining_goals": [],
                                "errors": [], "timed_out": True, "elapsed_ms": 0.0,
                            })
                            continue
                        t0 = time.monotonic()
                        rep, ec = _fmt_cand(raw, sorry_m, cand)
                        rls = rep.split("\n")
                        delta, mod = len(rls) - 1, list(orig_lines)
                        mod[line - 1 : line] = rls
                        body = "\n".join(mod)
                        _, _, ok = worker.sync_text(p, body, wait_s=min(15.0, rem))
                        cand_w_err = worker.worker_error(uri)
                        li, ga = (line - 1) + delta, []
                        if not lsp_alive():
                            ok = False
                            cand_w_err = cand_w_err or "Lean LSP process exited unexpectedly."
                        if ok:
                            rem_g = cand_dl - time.monotonic()
                            if rem_g <= 0:
                                ok = False
                            else:
                                try:
                                    ga = self._goal_at(
                                        worker, uri, li, mod[li], ec, min(5.0, rem_g)
                                    )
                                except TimeoutError:
                                    ok = False
                                except RuntimeError as exc:
                                    ok = False
                                    cand_w_err = cand_w_err or self._req_err(worker, exc)
                            if not lsp_alive():
                                ok = False
                                cand_w_err = cand_w_err or "Lean LSP process exited unexpectedly."
                        errs, unsv, seen, warn_sorry = [], [], Counter(), False
                        for d in worker.diags(uri):
                            ln0, msg = dl(d), str(d.get("message", "")).strip()
                            if d.get("severity") == 2:
                                if d0 <= ln0 < d1 + delta and _SORRY_WARN_RE.search(msg):
                                    warn_sorry = True
                                continue
                            if d.get("severity") != 1:
                                continue
                            tgt = (line - 1) <= ln0 <= li
                            if not tgt:
                                seen[(ln0, msg)] += 1
                                orig_ln = ln0 - (delta if ln0 > li else 0)
                                tgt = seen[(ln0, msg)] > berr.get((orig_ln, msg), 0)
                            if tgt:
                                item = msg if uns(msg) else _cdiag(d, mod)
                                (unsv if uns(msg) else errs).append(item)
                        if cand_w_err and not errs:
                            errs.append(
                                {"severity": "error", "line": 1, "column": 1, "message": cand_w_err}
                            )
                        if not errs and unsv and not ga:
                            pts = unsv[0].split("\n", 1)[1].strip() if "\n" in unsv[0] else ""
                            ga = [pts or "unsolved goals"]
                        decl_mask = mask_lean_comments("\n".join(mod[d0 : d1 + delta]))
                        cand_mask = mask_lean_comments(cand)
                        usor = bool(
                            _SORRY_RE.search(cand_mask)
                            or _SORRY_RE.search(decl_mask)
                            or warn_sorry
                        )
                        ok_step = ok and not errs and not usor and not cand_w_err
                        ms = round((time.monotonic() - t0) * 1000.0, 1)
                        results.append({
                            "tactic": cand, "evaluated": True, "closes_goal": ok_step and not ga,
                            "ok_step": ok_step, "uses_sorry": usor, "remaining_goals": ga,
                            "errors": errs, "timed_out": (not ok) and not cand_w_err,
                            "elapsed_ms": ms,
                        })
                        if not lsp_alive():
                            blk = cand_w_err or "Lean LSP process exited unexpectedly."
                            blk_err = [{
                                "severity": "error", "line": 1, "column": 1, "message": blk,
                            }]
                            for rem_cand in cleaned[cand_idx + 1 :]:
                                results.append({
                                    "tactic": rem_cand, "evaluated": False, "closes_goal": False,
                                    "ok_step": False, "uses_sorry": False, "remaining_goals": [],
                                    "errors": blk_err, "elapsed_ms": 0.0, "timed_out": False,
                                })
                            break
                finally:
                    if lsp_alive():
                        worker.sync_text(p, orig, wait_s=15.0)
                    if not lsp_alive():
                        self._retire_dead_worker(worker)
        out = [f"In-Memory Multi-Attempt (advisory; verify via `cargo anneal`) on {p}:{line}"]
        for idx, r in enumerate(results, 1):
            tag = (
                f"BLOCKED (prior error at L{r['errors'][0]['line']})" if not r["evaluated"]
                else "TIMEOUT" if r["timed_out"]
                else "INCOMPLETE (uses sorry)" if r["uses_sorry"] and not r["errors"]
                else "CLOSED (0 goals, 0 errors; advisory)" if r["closes_goal"]
                else f"STEP ({len(r['remaining_goals'])} remaining)" if r["ok_step"]
                else f"ERROR ({len(r['errors'])})"
            )
            out.append(f"[{idx}] `{r['tactic']}` -> {tag} ({r['elapsed_ms']} ms)")
            if r["errors"]:
                out.append(f"    {r['errors'][0]['message'][:220]}")
            elif r["remaining_goals"]:
                out.append("    " + "\n    ".join(r["remaining_goals"][0].splitlines()[:6]))
        return {"attempts": results, "text": middle_clip("\n".join(out))}

    def hover(
        self, file: str, line: int, *, symbol: str | None = None,
        column: int | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p, ln, col, res, _, _, timed_out, w_err = self._pos_req(
            "textDocument/hover", file, line, symbol=symbol, column=column, wkw=wkw
        )
        c = res.get("contents") if isinstance(res, dict) else None
        if isinstance(c, str):
            md = c.strip()
        elif isinstance(c, dict):
            md = str(c.get("value", "")).strip()
        elif isinstance(c, list):
            md = "\n".join(str(x.get("value", x) if isinstance(x, dict) else x).strip() for x in c)
        else:
            md = ""
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            txt = middle_clip(f"{prefix}\n{md}" if md else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean hover info at {p}:{ln}:{col}."
            txt = middle_clip(f"{prefix}\n{md}" if md else prefix)
        else:
            txt = middle_clip(md or f"No hover info at {p}:{ln}:{col}.")
        return {
            "hover": md, "line": ln, "column": col,
            "completed": (not timed_out) and not w_err, "timed_out": timed_out, "text": txt,
        }

    def definition(
        self, file: str, line: int, *, symbol: str | None = None,
        column: int | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p, ln, col, res, allowed_roots, excluded_roots, timed_out, w_err = self._pos_req(
            "textDocument/definition", file, line, symbol=symbol, column=column, wkw=wkw
        )
        locs: list[dict[str, Any]] = []
        for item in (res if isinstance(res, list) else ([res] if isinstance(res, dict) else [])):
            if not isinstance(item, dict):
                continue
            tu = item.get("targetUri") or item.get("uri")
            rng = item.get("targetSelectionRange") or item.get("targetRange") or item.get("range")
            if isinstance(tu, str) and isinstance(rng, dict):
                st = rng.get("start", {})
                tp, tl = uri_to_path(tu), int(st.get("line", 0)) + 1
                tu16 = int(st.get("character", 0))
                is_file = tu.lower().startswith("file://")
                lines = _safe_read_lines(tp, allowed_roots, excluded_roots) if is_file else None
                if lines is not None:
                    tcol = (
                        utf16_to_py_col(lines[tl - 1], tu16) + 1
                        if 1 <= tl <= len(lines) else tu16 + 1
                    )
                    lo, hi = max(1, tl - 2), min(len(lines), tl + 2)
                    snip = "\n".join(
                        f"{'>' if i == tl else ' '} {i:4d}: {lines[i - 1]}"
                        for i in range(lo, hi + 1)
                    )
                else:
                    tcol, snip = tu16 + 1, ""
                locs.append({"file": tp, "line": tl, "column": tcol, "snippet": snip})
        out = [f"{loc['file']}:{loc['line']}:{loc['column']}\n{loc['snippet']}" for loc in locs[:5]]
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            body = "\n\n".join(out)
            txt = middle_clip(f"{prefix}\n\n{body}" if body else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean definition at {p}:{ln}:{col}."
            body = "\n\n".join(out)
            txt = middle_clip(f"{prefix}\n\n{body}" if body else prefix)
        else:
            txt = middle_clip("\n\n".join(out) or f"No definition at {p}:{ln}:{col}.")
        return {
            "locations": locs, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": txt,
        }

    def completions(
        self, file: str, line: int, *, column: int | None = None, **wkw: Any
    ) -> dict[str, Any]:
        p, ln, col, res, _, _, timed_out, w_err = self._pos_req(
            "textDocument/completion", file, line, column=column, eol_default=True, wkw=wkw
        )
        if isinstance(res, dict):
            raw = res.get("items", [])
        else:
            raw = res if isinstance(res, list) else []
        items = [
            {"label": str(it.get("label", "")), "detail": str(it.get("detail") or ""),
             "kind": _KINDS.get(int(it.get("kind") or 0), "")}
            for it in raw[:30] if isinstance(it, dict)
        ]
        lines = [
            f"- {it['label']}" + (f" : {it['detail']}" if it["detail"] else "") for it in items
        ]
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            txt = middle_clip(f"{prefix}\n" + "\n".join(lines) if lines else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean completions at {p}:{ln}:{col}."
            txt = middle_clip(f"{prefix}\n" + "\n".join(lines) if lines else prefix)
        else:
            txt = middle_clip("\n".join(lines) or "No completions.")
        return {
            "items": items, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": txt,
        }

    def outline(self, file: str, **wkw: Any) -> dict[str, Any]:
        ch = wkw.get("caller_home")
        p = validate_no_symlink_target(file, home=ch, kind="Lean target")
        if p.is_dir():
            syms = [{**d, "file": str(fp)} for fp in _walk_lean(p) for d in _scan_decls(fp)]
            txt = "\n".join(f"{e['file']}:{e['line']}: {e['signature']}" for e in syms[:80])
            return {
                "symbols": syms, "completed": True, "timed_out": False,
                "text": middle_clip(txt or "No Lean declarations."),
            }
        p, syms = _req_lean(str(p), home=ch), []
        with self._checkout(p, **wkw) as worker, worker.lock:
            uri, _, ok = worker.sync_text(p, p.read_text("utf-8", errors="replace"))
            w_err = worker.worker_error(uri)
            req = {"textDocument": {"uri": uri}}
            res, timed_out = None, (not ok) and not w_err
            if ok:
                try:
                    res = worker.lsp.request("textDocument/documentSymbol", req, 10.0)
                except TimeoutError:
                    timed_out = True
                except RuntimeError as exc:
                    w_err = w_err or self._req_err(worker, exc)
        if isinstance(res, list):
            _flatten_syms(res, syms)
        syms = syms or _scan_decls(p)
        lines = [
            f"{'  ' * int(s.get('depth', 0))}L{s['line']}: {s.get('kind', '')} {s['name']}".strip()
            + (f" — {s['detail']}" if s.get("detail") else "")
            for s in syms[:100]
        ]
        head = (
            [f"Lean file worker error ({w_err}); fallback regex outline."] if w_err
            else ["Timed out waiting for Lean symbols (fallback regex outline)."] if timed_out
            else []
        )
        txt = "\n".join([*head, *lines])
        return {
            "symbols": syms, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": middle_clip(txt or "No symbols found."),
        }

    def local_search(
        self, query: str, *, workspace: str | None = None, max_results: int = 30, **wkw: Any
    ) -> dict[str, Any]:
        eff_art = (
            wkw.get("artifacts_dir")
            if wkw.get("artifacts_dir") is not None else self.default_artifacts_dir
        )
        eff_lp = [*self.default_extra_lean_path, *(wkw.get("extra_lean_path") or ())] or None
        ch_raw = wkw.get("caller_home")
        ch_lex = Path(os.path.abspath(str(ch_raw.expanduser()))) if ch_raw is not None else None
        ctx = discover_workspace(
            workspace or ".",
            artifacts_dir=eff_art,
            extra_lean_path=eff_lp,
            extra_lean_src_path=wkw.get("extra_lean_src_path"),
            cargo_target_dir=wkw.get("cargo_target_dir"),
            test_install_root=wkw.get("test_install_root"),
            require_lean=False,
            use_env=self.use_env,
            home=ch_lex,
        )
        roots = [
            ctx.root,
            *(e for e in ctx.lean_src_path if e.is_dir() and not e.is_relative_to(ctx.root)),
        ]
        try:
            rx = re.compile(query[6:], re.IGNORECASE) if query.startswith("regex:") else None
        except re.error as exc:
            raise ValueError(f"Invalid regex `{query[6:]}`: {exc}") from exc
        pat, hits = query.lower(), []
        for sr in dict.fromkeys(roots):
            for fp in _walk_lean(sr):
                rel = str(fp.relative_to(sr))
                for d in _scan_decls(fp):
                    hit = (bool(rx.search(d["name"]) or rx.search(rel)) if rx
                           else (pat in d["name"].lower() or pat in fp.stem.lower()))
                    if hit:
                        hits.append({**d, "file": str(fp)})
                        if len(hits) >= max_results:
                            txt = "\n".join(
                                f"{h['file']}:{h['line']}: {h['signature']}" for h in hits
                            )
                            return {"matches": hits, "text": middle_clip(txt)}
        txt = "\n".join(f"{h['file']}:{h['line']}: {h['signature']}" for h in hits)
        return {"matches": hits, "text": middle_clip(txt or f"No matches for `{query}`.")}
