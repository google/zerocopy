# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""CLI, optional Unix warm daemon, and stdio MCP server for `anneal-lsp`."""

from __future__ import annotations

import argparse
import contextlib
from dataclasses import asdict
try:
    import fcntl
except ImportError:  # Non-POSIX hosts run `--direct` or `mcp` without Unix daemons.
    fcntl = None  # type: ignore[assignment]
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import socketserver
import stat
import subprocess
import sys
import threading
import time
from typing import Any

from .client import caller_homes
from .discovery import discover_workspace, find_lean_binary, validate_no_symlink_target
from .workspace import WorkspacePool

SERVER_NAME, SERVER_VERSION = "anneal-lsp", "0.1.0"
MCP_PROTOCOLS = ("2024-11-05", "2025-03-26", "2025-06-18")


def _build_id() -> str:
    h = hashlib.sha256()
    for fp in sorted(Path(__file__).resolve().parent.glob("*.py")):
        h.update(fp.name.encode("utf-8") + fp.read_bytes())
    return h.hexdigest()[:16]


SERVER_BUILD_ID = _build_id()
_S, _I = {"type": "string"}, {"type": "integer"}
_FP = {"file": _S, "line": _I, "artifacts_dir": _S}
_SEV = {"type": "string", "enum": ["all", "warning", "error"]}
_SPECS = (
    ("lean_diagnostics", "Check errors, warnings, and open sorry goals.", ("file",),
     {"file": _S, "severity": _SEV, "artifacts_dir": _S}),
    ("lean_goal", "Inspect tactic goals before/after `line` plus term goal.",
     ("file", "line"), {**_FP, "column": _I, "snippet": _S}),
    ("lean_multi_attempt", "Try tactics in memory (advisory; verify via cargo anneal).",
     ("file", "line", "tactics"), {**_FP, "tactics": {"type": "array", "items": _S}}),
    ("lean_hover", "Get Lean 4 type and docstring hover info.",
     ("file", "line"), {**_FP, "symbol": _S, "column": _I}),
    ("lean_definition", "Jump to Lean 4 symbol definition.",
     ("file", "line"), {**_FP, "symbol": _S, "column": _I}),
    ("lean_completions", "List Lean 4 identifier and dot completions.",
     ("file", "line"), {**_FP, "column": _I}),
    ("lean_outline", "Outline Lean 4 declarations in a file or dir.",
     ("file",), {"file": _S, "artifacts_dir": _S}),
    ("lean_local_search", "Search Lean 4 declarations across workspace.",
     ("query",), {"query": _S, "workspace": _S, "max_results": _I}),
    ("lean_restart_workspace", "Restart warm Lean LSP worker(s).", (), {"root": _S}),
)
_MCP_TOOL_KEYS = {n: frozenset(p) for n, _, _, p in _SPECS}
_MCP_REQ = {n: r for n, _, r, _ in _SPECS}
MCP_TOOLS = [
    {"name": n, "description": d,
     "inputSchema": {"type": "object", "properties": p, "required": list(r)}}
    for n, d, r, p in _SPECS
]
_CMD_MAP = {
    "diag": "lean_diagnostics", "diagnostics": "lean_diagnostics", "check": "lean_diagnostics",
    "goal": "lean_goal", "multi-attempt": "lean_multi_attempt", "try": "lean_multi_attempt",
    "hover": "lean_hover", "def": "lean_definition", "definition": "lean_definition",
    "completions": "lean_completions", "outline": "lean_outline",
    "search": "lean_local_search", "restart": "lean_restart_workspace",
}
_CLEAR_ENV = (
    "ANNEAL_LEAN", "ANNEAL_TEST_INSTALL_ROOT", "XDG_CACHE_HOME", "ANNEAL_LSP_ARTIFACTS",
    "ANNEAL_LSP_LEAN_PATH", "ANNEAL_LSP_NO_SANDBOX", "ANNEAL_LSP_MEMORY_MB",
    "ANNEAL_LSP_SOCKET", "LEAN_PATH", "LEAN_SRC_PATH", "CARGO_TARGET_DIR",
)


def _safe_sock(raw: str, *, ensure_dir: bool = False, unlink: bool = False) -> Path:
    if not _HAS_UNIX_DAEMON:
        raise OSError("Unix domain sockets require POSIX (`fcntl` and `AF_UNIX`).")
    abs_p = Path(os.path.abspath(str(Path(raw).expanduser())))
    if abs_p.is_symlink() or abs_p.parent.is_symlink():
        raise PermissionError(f"Socket path/dir must not be a symlink: {abs_p}")
    sp = abs_p.parent.resolve() / abs_p.name
    pd, uid = sp.parent, os.getuid()
    is_default_dir = pd.name in ("anneal-lsp", f"anneal-lsp-{uid}")
    if ensure_dir and not pd.exists():
        for anc in (pd.parent, *pd.parent.parents):
            if anc.exists():
                ast = anc.lstat()
                bad_world = (ast.st_mode & 0o002) != 0 and not (ast.st_mode & stat.S_ISVTX)
                bad_grp = (ast.st_mode & 0o020) != 0 and ast.st_uid not in (0, uid)
                if bad_world or bad_grp or ast.st_uid not in (0, uid):
                    raise PermissionError(f"Unsafe socket parent ancestor: {anc}")
                break
        pd.mkdir(mode=0o700, parents=True, exist_ok=True)
    if pd.exists() or pd.is_symlink():
        pst = pd.lstat()
        if stat.S_ISLNK(pst.st_mode) or not stat.S_ISDIR(pst.st_mode) or pst.st_uid != uid:
            raise PermissionError(f"Unsafe socket directory owner/type: {pd}")
        if (pst.st_mode & 0o077) != 0:
            if ensure_dir and is_default_dir:
                os.chmod(pd, 0o700)
            else:
                raise PermissionError(f"Socket directory must have private (0700) mode: {pd}")
    with contextlib.suppress(FileNotFoundError):
        st = sp.lstat()
        if (
            stat.S_ISLNK(st.st_mode)
            or not stat.S_ISSOCK(st.st_mode)
            or st.st_uid != uid
            or (st.st_mode & 0o077) != 0
        ):
            raise PermissionError(f"Unsafe or non-socket path: {sp}")
        if unlink:
            sp.unlink()
    return sp


def default_socket_path() -> str:
    if not _HAS_UNIX_DAEMON:
        raise OSError("Unix domain sockets require POSIX (`fcntl` and `AF_UNIX`).")
    if env_sock := os.environ.get("ANNEAL_LSP_SOCKET", "").strip():
        return str(_safe_sock(env_sock))
    rt = os.environ.get("XDG_RUNTIME_DIR", "").strip()
    root = Path(rt) if (rt and Path(rt).is_dir()) else Path(f"/tmp/anneal-lsp-{os.getuid()}")
    sub = root if root.name.startswith("anneal-lsp-") else root / "anneal-lsp"
    return str(_safe_sock(str(sub / "lsp.sock"), ensure_dir=True))


def _worker_kw(args: dict[str, Any], *, allow_trust_overrides: bool) -> dict[str, Any]:
    kw: dict[str, Any] = {"artifacts_dir": Path(ad)} if (ad := args.get("artifacts_dir")) else {}
    if not allow_trust_overrides:
        return kw
    if nl := args.get("no_lean"):
        raise FileNotFoundError(
            nl if isinstance(nl, str) else "Unable to locate `lean`; set `ANNEAL_LEAN`."
        )
    for ak in ("explicit_lean", "explicit_lake", "cargo_target_dir",
               "test_install_root", "caller_home"):
        if args.get(ak):
            kw[ak] = Path(args[ak])
    for ak, kk in (("lean_path", "extra_lean_path"), ("lean_src_path", "extra_lean_src_path")):
        if args.get(ak):
            kw[kk] = [Path(p) for p in args[ak]]
    if args.get("memory_mb") is not None:
        kw["memory_mb"] = int(args["memory_mb"])
    return kw


def dispatch_action(
    pool: WorkspacePool, action: str, args: dict[str, Any], *,
    allow_trust_overrides: bool = True, allow_ping: bool = True,
) -> dict[str, Any]:
    def nstr(k: str) -> str:
        if not isinstance(v := args.get(k), str) or not v:
            raise ValueError(f"Missing required string argument `{k}`.")
        return v

    def nint(k: str) -> int:
        v = args.get(k)
        if isinstance(v, bool) or not isinstance(v, (int, str)):
            raise ValueError(f"Missing or invalid integer argument `{k}`.")
        return int(v)

    if action == "ping" and allow_ping:
        return {"ok": True, "pid": os.getpid(), "sandbox": pool.sandbox,
                "version": SERVER_VERSION, "build_id": SERVER_BUILD_ID}
    if action == "lean_restart_workspace":
        return pool.restart(args.get("root"))
    if action == "lean_outline":
        fp = nstr("file")
        dwkw = _worker_kw({k: v for k, v in args.items() if k != "no_lean"},
                          allow_trust_overrides=allow_trust_overrides)
        tp = validate_no_symlink_target(
            fp, home=dwkw.get("caller_home"), kind="Lean target"
        )
        if tp.is_dir():
            return pool.outline(fp, **dwkw)
    if action == "lean_local_search":
        wkw = _worker_kw({k: v for k, v in args.items() if k != "no_lean"},
                         allow_trust_overrides=allow_trust_overrides)
        mr = 30 if args.get("max_results") is None else nint("max_results")
        if mr < 1:
            raise ValueError("`max_results` must be >= 1.")
        return pool.local_search(nstr("query"), workspace=args.get("workspace"),
                                 max_results=mr, **wkw)
    wkw = _worker_kw(args, allow_trust_overrides=allow_trust_overrides)
    if action == "lean_diagnostics":
        sev = "all" if args.get("severity") is None else args["severity"]
        if not isinstance(sev, str) or sev not in ("all", "warning", "error"):
            raise ValueError(
                f"Invalid `severity`: {sev!r}; expected 'all', 'warning', or 'error'."
            )
        return pool.diagnostics(nstr("file"), severity=sev, **wkw)
    if action == "lean_outline":
        return pool.outline(nstr("file"), **wkw)
    if action == "lean_multi_attempt":
        rt = args.get("tactics")
        if not isinstance(rt, list) or not all(isinstance(t, str) for t in rt):
            raise ValueError("`tactics` must be a list of strings.")
        return pool.multi_attempt(nstr("file"), nint("line"), rt, **wkw)
    pos_fn = {"lean_goal": pool.goal, "lean_hover": pool.hover,
              "lean_definition": pool.definition, "lean_completions": pool.completions}.get(action)
    if pos_fn is None:
        raise ValueError(f"Unknown action: {action}")
    ex = {k: args[k] for k in ("symbol", "snippet") if args.get(k) is not None}
    if args.get("column") is not None:
        if (col := nint("column")) < 1:
            raise ValueError("`column` must be >= 1.")
        ex["column"] = col
    return pos_fn(nstr("file"), nint("line"), **ex, **wkw)


def _rpc_err(rid: Any, code: int, message: str) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": rid, "error": {"code": code, "message": message}}


def handle_mcp_request(pool: WorkspacePool, msg: Any, *, _in_batch: bool = False) -> Any:
    if isinstance(msg, list):
        if _in_batch or not msg:
            return _rpc_err(None, -32600, "Invalid Request")
        rs = [r for it in msg if (r := handle_mcp_request(pool, it, _in_batch=True)) is not None]
        return rs or None
    if not isinstance(msg, dict):
        return _rpc_err(None, -32600, "Invalid Request")
    method, raw_p, rid = msg.get("method"), msg.get("params"), msg.get("id")
    if "id" not in msg or method == "notifications/initialized":
        return None
    if not isinstance(method, str) or not method:
        return _rpc_err(rid, -32600, "Invalid Request")
    params = {} if raw_p is None else (raw_p if isinstance(raw_p, dict) else None)
    if params is None:
        return _rpc_err(rid, -32602, "Invalid params")
    try:
        if method == "initialize":
            rv = params.get("protocolVersion")
            pv = rv if isinstance(rv, str) and rv in MCP_PROTOCOLS else MCP_PROTOCOLS[-1]
            res: Any = {"protocolVersion": pv, "capabilities": {"tools": {"listChanged": False}},
                        "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION}}
        elif method in ("ping", "shutdown"):
            if method == "shutdown":
                pool.shutdown()
            res = {}
        elif method == "tools/list":
            res = {"tools": MCP_TOOLS}
        elif method == "tools/call":
            tn, raw_args = params.get("name"), params.get("arguments")
            ra = {} if raw_args is None else raw_args
            if not isinstance(tn, str) or tn not in _MCP_REQ or not isinstance(ra, dict):
                raise ValueError(f"Invalid MCP tool call: {tn}")
            safe = {k: v for k, v in ra.items() if k in _MCP_TOOL_KEYS[tn]}
            for rk in _MCP_REQ[tn]:
                if safe.get(rk) is None:
                    raise ValueError(f"Missing required argument `{rk}`.")
            out = dispatch_action(pool, tn, safe, allow_trust_overrides=False, allow_ping=False)
            res = {"content": [{"type": "text", "text": out.get("text", "")}]}
        else:
            return _rpc_err(rid, -32601, f"Unknown method: {method}")
        return {"jsonrpc": "2.0", "id": rid, "result": res}
    except Exception as exc:
        if method == "tools/call":
            err = {"content": [{"type": "text", "text": f"Error: {exc}"}], "isError": True}
            return {"jsonrpc": "2.0", "id": rid, "result": err}
        return _rpc_err(rid, -32000, str(exc))


def serve_mcp(pool: WorkspacePool, stdin: Any = None, stdout: Any = None) -> int:
    inp, out = stdin or sys.stdin, stdout or sys.stdout
    try:
        for line in inp:
            if not (s := line.strip()):
                continue
            try:
                msg = json.loads(s)
                resp = handle_mcp_request(pool, msg)
            except (json.JSONDecodeError, ValueError, RecursionError) as exc:
                msg, resp = None, _rpc_err(None, -32700, str(exc))
            if resp is not None:
                try:
                    enc = json.dumps(resp)
                except (ValueError, RecursionError) as exc:
                    enc = json.dumps(_rpc_err(None, -32600, str(exc)))
                out.write(enc + "\n")
                out.flush()
            if isinstance(msg, dict) and msg.get("method") == "shutdown":
                break
    finally:
        pool.shutdown()
    return 0


if hasattr(socketserver, "UnixStreamServer"):
    class _UnixRpcServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
        daemon_threads = False
        block_on_close = True
else:
    _UnixRpcServer = None  # type: ignore[assignment,misc]

_HAS_UNIX_DAEMON = (
    fcntl is not None
    and hasattr(socket, "AF_UNIX")
    and _UnixRpcServer is not None
    and hasattr(os, "getuid")
)


def _unlock_close(fd: int) -> None:
    if fcntl is not None:
        with contextlib.suppress(OSError):
            fcntl.flock(fd, fcntl.LOCK_UN)
    with contextlib.suppress(OSError):
        os.close(fd)


def serve_daemon(sock_path: str, *, sandbox: bool = True, idle_ttl_s: float = 900.0) -> int:
    if not _HAS_UNIX_DAEMON:
        print("Warm Unix daemon requires POSIX; use `--direct` or `mcp`.", file=sys.stderr)
        return 1
    assert fcntl is not None and _UnixRpcServer is not None
    try:
        sp = _safe_sock(sock_path, ensure_dir=True)
        srv_fd = os.open(f"{sp}.srv.lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    except OSError as exc:
        print(f"Cannot prepare anneal-lsp socket {sock_path}: {exc}", file=sys.stderr)
        return 1
    dl = time.monotonic() + 5.0
    while True:
        try:
            fcntl.flock(srv_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if _check_daemon_ping(str(sp), 0.3) is not None:
                os.close(srv_fd)
                return 0
            if time.monotonic() >= dl:
                print(f"Daemon lock busy on {sp} while unpingable.", file=sys.stderr)
                os.close(srv_fd)
                return 1
            time.sleep(0.05)

    for v in list(os.environ):
        if v in _CLEAR_ENV or v.startswith(("LD_", "DYLD_", "PYTHON")):
            os.environ.pop(v, None)
    pool = WorkspacePool(
        idle_ttl_s=idle_ttl_s, sandbox=sandbox, use_env=False, hidden_paths=(sp.parent,)
    )
    stop_ev = threading.Event()
    _safe_sock(str(sp), unlink=True)

    class Handler(socketserver.StreamRequestHandler):
        def handle(self) -> None:
            if not (raw := self.rfile.readline()):
                return
            try:
                req = json.loads(raw.decode("utf-8"))
                act, rargs = str(req["action"]), dict(req.get("args") or {})
                if act == "shutdown":
                    resp: dict[str, Any] = {"ok": True, "result": {"stopped": True}}
                    stop_ev.set()
                else:
                    resp = {"ok": True, "result": dispatch_action(pool, act, rargs)}
            except Exception as exc:
                resp = {"ok": False, "error": str(exc)}
            self.wfile.write((json.dumps(resp) + "\n").encode("utf-8"))

    old_umask = os.umask(0o077)
    try:
        srv = _UnixRpcServer(str(sp), Handler)
    except OSError as exc:
        print(f"Failed to bind anneal-lsp socket {sp}: {exc}", file=sys.stderr)
        _unlock_close(srv_fd)
        return 1
    finally:
        os.umask(old_umask)
    try:
        os.chmod(sp, 0o600)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        with contextlib.suppress(OSError):
            dn = os.open(os.devnull, os.O_WRONLY)
            os.dup2(dn, 2)
            os.close(dn)

        def _reap() -> None:
            while not stop_ev.wait(15.0):
                pool.evict_idle()
                if pool.is_idle_expired():
                    stop_ev.set()
                    break

        threading.Thread(target=_reap, daemon=True).start()
        with contextlib.suppress(KeyboardInterrupt):
            stop_ev.wait()
        srv.shutdown()
        srv.server_close()
    finally:
        with contextlib.suppress(OSError):
            _safe_sock(str(sp), unlink=True)
        pool.shutdown()
        _unlock_close(srv_fd)
    return 0


def _unix_call(
    sock_path: str, action: str, args: dict[str, Any], timeout_s: float = 270.0
) -> dict[str, Any]:
    if not _HAS_UNIX_DAEMON:
        raise OSError("Unix domain sockets require POSIX (`fcntl` and `AF_UNIX`).")
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as s:
        s.settimeout(timeout_s)
        s.connect(sock_path)
        s.sendall((json.dumps({"action": action, "args": args}) + "\n").encode("utf-8"))
        chunks: list[bytes] = []
        while data := s.recv(65536):
            chunks.append(data)
            if b"\n" in data:
                break
    return json.loads(b"".join(chunks).decode("utf-8"))


def _check_daemon_ping(sock_path: str, timeout_s: float = 1.0) -> dict[str, Any] | None:
    with contextlib.suppress(OSError, json.JSONDecodeError, UnicodeDecodeError):
        resp = _unix_call(sock_path, "ping", {}, timeout_s)
        return (resp.get("result") or {}) if resp.get("ok") else None
    return None


def _srv_lock_free(sp: Path) -> bool:
    if fcntl is None:
        return True
    lp = Path(f"{sp}.srv.lock")
    if not lp.exists() or lp.is_symlink():
        return True
    try:
        fd = os.open(str(lp), os.O_RDWR | getattr(os, "O_NOFOLLOW", 0))
    except OSError:
        return True
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(fd, fcntl.LOCK_UN)
            return True
        except BlockingIOError:
            return False
    finally:
        os.close(fd)


def stop_daemon(sock_path: str, timeout_s: float = 5.0) -> int:
    if not _HAS_UNIX_DAEMON:
        raise RuntimeError("Warm Unix daemon requires POSIX; use `--direct` or `mcp`.")
    assert fcntl is not None
    sp = _safe_sock(sock_path)
    if not sp.parent.exists():
        return 0
    lock_fd = os.open(f"{sp}.lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        sent, dl = False, time.monotonic() + timeout_s
        while True:
            if not sent:
                with contextlib.suppress(OSError, json.JSONDecodeError, UnicodeDecodeError):
                    resp = _unix_call(str(sp), "shutdown", {}, 2.0)
                    sent = bool(resp.get("ok"))
            if _srv_lock_free(sp):
                return 0
            if time.monotonic() >= dl:
                raise TimeoutError(f"Timed out stopping anneal-lsp daemon on {sp}.")
            time.sleep(0.05)
    finally:
        _unlock_close(lock_fd)


def _check_sbx(info: dict[str, Any], *, sandbox: bool) -> None:
    if info.get("version") != SERVER_VERSION or info.get("build_id") != SERVER_BUILD_ID:
        raise RuntimeError(
            "Running anneal-lsp daemon version/build mismatch; run `stop-daemon` first."
        )
    dsbx = bool(info.get("sandbox", True))
    if dsbx != sandbox:
        msg = ("enforces bwrap sandbox; pass `--direct --no-sandbox`"
               if dsbx else "has sandbox disabled; pass `--direct`")
        raise RuntimeError(f"Running anneal-lsp daemon {msg} or run `stop-daemon` first.")


def _stop_timed_out_proc(proc: subprocess.Popen[Any]) -> None:
    if hasattr(os, "killpg") and hasattr(signal, "SIGKILL"):
        for sig, tm in ((signal.SIGTERM, 1.5), (signal.SIGKILL, 1.0)):
            with contextlib.suppress(Exception):
                os.killpg(os.getpgid(proc.pid), sig)
                proc.wait(timeout=tm)
                return
    with contextlib.suppress(Exception):
        proc.terminate()
        proc.wait(timeout=1.5)
    if proc.poll() is None:
        with contextlib.suppress(Exception):
            proc.kill()
            proc.wait(timeout=1.0)


def _ensure_daemon(sock_path: str, *, sandbox: bool) -> None:
    if not _HAS_UNIX_DAEMON:
        raise RuntimeError("Warm Unix daemon requires POSIX; pass `--direct` or use `mcp`.")
    assert fcntl is not None
    sp = _safe_sock(sock_path, ensure_dir=True)
    if (info := _check_daemon_ping(str(sp), 1.0)) is not None:
        return _check_sbx(info, sandbox=sandbox)
    lock_fd = os.open(f"{sp}.lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        if (info := _check_daemon_ping(str(sp), 1.0)) is not None:
            return _check_sbx(info, sandbox=sandbox)
        entry, err_p = Path(__file__).resolve().parent.parent / "anneal-lsp", Path(f"{sp}.err")
        err_fd = os.open(str(err_p), os.O_CREAT | os.O_WRONLY | os.O_TRUNC | os.O_NOFOLLOW, 0o600)
        try:
            cmd = [
                sys.executable, "-I", "-B", str(entry),
                *([] if sandbox else ["--no-sandbox"]), "daemon", "--socket", str(sp),
            ]
            d_env = {
                k: v for k, v in os.environ.items()
                if k != "ANNEAL_LSP_SOCKET" and not k.startswith(("LD_", "DYLD_", "PYTHON"))
            }
            proc = subprocess.Popen(
                cmd, cwd="/", env=d_env, stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=err_fd, start_new_session=True,
            )
        finally:
            os.close(err_fd)
        dl = time.monotonic() + 10.0
        while time.monotonic() < dl:
            if (info := _check_daemon_ping(str(sp), 0.5)) is not None:
                return _check_sbx(info, sandbox=sandbox)
            if proc.poll() is not None:
                break
            time.sleep(0.05)
        if proc.poll() is None:
            _stop_timed_out_proc(proc)
        det = err_p.read_text("utf-8", errors="replace").strip()[-300:] if err_p.is_file() else ""
        raise RuntimeError(
            f"Failed to start anneal-lsp daemon on {sp}" + (f": {det}" if det else "")
        )
    finally:
        _unlock_close(lock_fd)


def _abs(raw: str) -> str:
    return str(Path(raw).expanduser().resolve())


def _abs_lex(raw: str) -> str:
    return os.path.abspath(str(Path(raw).expanduser()))


def _abs_args(args: dict[str, Any]) -> dict[str, Any]:
    out = dict(args)
    homes = caller_homes()
    ch_lex = Path(os.path.abspath(str(homes[0].expanduser()))) if homes else None
    for k in ("file", "workspace"):
        if isinstance(v := out.get(k), str) and v:
            out[k] = str(validate_no_symlink_target(v, home=ch_lex, kind=k))
    if isinstance(v := out.get("artifacts_dir"), str) and v:
        out["artifacts_dir"] = _abs_lex(v)
    if isinstance(r := out.get("root"), str) and r and r != "all":
        out["root"] = _abs(r)
    lp = [_abs(x) for x in (out.get("lean_path") or []) if x]
    for var in ("ANNEAL_LSP_LEAN_PATH", "LEAN_PATH"):
        if raw := os.environ.get(var, "").strip():
            lp.extend(_abs(x.strip()) for x in raw.split(os.pathsep) if x.strip())
    if lp:
        out["lean_path"] = list(dict.fromkeys(lp))
    if rs := os.environ.get("LEAN_SRC_PATH", "").strip():
        out["lean_src_path"] = [_abs(x.strip()) for x in rs.split(os.pathsep) if x.strip()]
    if not out.get("artifacts_dir") and (ev := os.environ.get("ANNEAL_LSP_ARTIFACTS", "").strip()):
        out["artifacts_dir"] = _abs_lex(ev)
    if not out.get("cargo_target_dir") and (ct := os.environ.get("CARGO_TARGET_DIR", "").strip()):
        out["cargo_target_dir"] = _abs_lex(ct)
    if (
        not out.get("test_install_root")
        and (ir := os.environ.get("ANNEAL_TEST_INSTALL_ROOT", "").strip())
    ):
        out["test_install_root"] = _abs_lex(ir)
    if (rm := os.environ.get("ANNEAL_LSP_MEMORY_MB", "").strip()).isascii() and rm.isdigit():
        out["memory_mb"] = max(256, int(rm))
    if ch_lex is not None:
        out["caller_home"] = str(ch_lex)
    hint = out.get("file") or out.get("workspace")
    try:
        hp = Path(hint) if isinstance(hint, str) else None
        lean_bin, lake_bin = find_lean_binary(start=hp, use_env=True, home=ch_lex)
        out["explicit_lean"] = str(lean_bin)
        if lake_bin is not None:
            out["explicit_lake"] = str(lake_bin)
    except FileNotFoundError as exc:
        out["no_lean"] = str(exc)
    return out


def build_parser() -> argparse.ArgumentParser:
    common = argparse.ArgumentParser(add_help=False)
    p = argparse.ArgumentParser(
        prog="anneal-lsp", description="Warm Lean 4 LSP CLI and MCP server."
    )
    for tgt, sup in ((common, True), (p, False)):
        df, dn, dl = (argparse.SUPPRESS,) * 3 if sup else (False, None, [])
        for fl in ("--json", "--direct", "--no-sandbox"):
            tgt.add_argument(fl, action="store_true", default=df)
        tgt.add_argument("--artifacts", default=dn)
        tgt.add_argument("--lean-path", action="append", default=dl)
    sub = p.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("diag", aliases=["diagnostics", "check"], parents=[common])
    d.add_argument("file")
    d.add_argument("--severity", choices=("all", "warning", "error"), default="all")
    pos_cmds = (("goal", ()), ("hover", ()), ("def", ("definition",)), ("completions", ()))
    for cmd, aliases in pos_cmds:
        sp = sub.add_parser(cmd, aliases=aliases, parents=[common])
        sp.add_argument("file")
        sp.add_argument("line", type=int)
        if cmd in ("hover", "def"):
            sp.add_argument("symbol", nargs="?", default=None)
        sp.add_argument("--column", type=int, default=None)
        if cmd == "goal":
            sp.add_argument("--snippet", default=None)
    m = sub.add_parser("multi-attempt", aliases=["try"], parents=[common])
    m.add_argument("file")
    m.add_argument("line", type=int)
    m.add_argument("tactics", nargs="+")
    sub.add_parser("outline", parents=[common]).add_argument("file")
    sr = sub.add_parser("search", parents=[common])
    sr.add_argument("query")
    sr.add_argument("--workspace", default=".")
    sr.add_argument("--max-results", type=int, default=30)
    sub.add_parser("discover", parents=[common]).add_argument("file")
    sub.add_parser("restart", parents=[common]).add_argument("root", nargs="?", default="all")
    sub.add_parser("mcp", parents=[common])
    sub.add_parser("daemon", parents=[common]).add_argument("--socket", default=None)
    sub.add_parser("stop-daemon", parents=[common]).add_argument("--socket", default=None)
    return p


def main(argv: list[str] | None = None) -> int:
    ns = build_parser().parse_args(argv)
    sandbox = not ns.no_sandbox and os.environ.get("ANNEAL_LSP_NO_SANDBOX") != "1"
    try:
        if ns.cmd == "mcp":
            rm = os.environ.get("ANNEAL_LSP_MEMORY_MB", "").strip()
            mem = max(256, int(rm)) if rm.isascii() and rm.isdigit() else None
            def_art = Path(ns.artifacts).expanduser() if ns.artifacts else None
            def_lp = [Path(p).expanduser() for p in ns.lean_path]
            pool = WorkspacePool(
                sandbox=sandbox,
                default_memory_mb=mem,
                default_artifacts_dir=def_art,
                default_extra_lean_path=def_lp,
            )
            return serve_mcp(pool)
        if ns.cmd == "daemon":
            return serve_daemon(ns.socket or default_socket_path(), sandbox=sandbox)
        if ns.cmd == "stop-daemon":
            return stop_daemon(ns.socket or default_socket_path())
        if ns.cmd == "discover":
            ctx = discover_workspace(
                ns.file, artifacts_dir=Path(ns.artifacts) if ns.artifacts else None,
                extra_lean_path=[Path(p) for p in ns.lean_path], require_lean=False,
            )
            ser = {
                k: ([str(x) for x in v] if isinstance(v, tuple)
                    else (str(v) if isinstance(v, Path) else v))
                for k, v in asdict(ctx).items()
            }
            print(json.dumps(ser, indent=2))
            return 0
        raw = {k: v for k, v in vars(ns).items()
               if k not in ("cmd", "json", "direct", "no_sandbox", "artifacts") and v is not None}
        if ns.artifacts:
            raw["artifacts_dir"] = ns.artifacts
        args = _abs_args(raw)
        if ns.direct or not _HAS_UNIX_DAEMON:
            pool = WorkspacePool(sandbox=sandbox, use_env=True)
            try:
                res = dispatch_action(pool, _CMD_MAP[ns.cmd], args)
            finally:
                pool.shutdown()
        else:
            sock = default_socket_path()
            _ensure_daemon(sock, sandbox=sandbox)
            act = _CMD_MAP[ns.cmd]
            # Bound: acquire(120)+init(30)+sync(45)+work(190/40)+restore(15).
            call_tm = 450.0 if act == "lean_multi_attempt" else 270.0
            resp = _unix_call(sock, act, args, timeout_s=call_tm)
            if not resp.get("ok"):
                raise RuntimeError(resp.get("error", "daemon error"))
            res = resp["result"]
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(json.dumps(res, indent=2) if ns.json else res.get("text", ""))
    return 0
