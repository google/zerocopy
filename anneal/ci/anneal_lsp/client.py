# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""JSON-RPC 2.0 `Content-Length` client and Unicode/sandbox utilities."""

from __future__ import annotations

import contextlib
import json
import os
from pathlib import Path
import queue
import re
import select
import shutil
import signal
import stat
import subprocess
import sys
import threading
from typing import Any, Callable
from urllib.parse import unquote, urlparse

_MAX_FRAME_BYTES = 64 * 1024 * 1024
_SYS_BWRAP_PATH = os.pathsep.join((
    "/usr/bin", "/bin", "/usr/local/bin",
    "/run/current-system/sw/bin", "/nix/var/nix/profiles/default/bin",
))
_TRUSTED_BWRAP_PREFIXES = (
    "/usr/", "/bin/", "/nix/store/", "/run/current-system/",
    "/nix/var/nix/profiles/",
)
_SYS_RO_LINKS = ("/bin", "/sbin", "/lib", "/lib32", "/lib64")
_SYS_RO_DIRS = ("/nix/store", "/nix/var/nix/profiles", "/opt/anneal-nix")
_ETC_RO_PATHS = (
    "/etc/ld.so.cache", "/etc/ld.so.conf", "/etc/ld.so.conf.d",
    "/etc/alternatives", "/etc/passwd", "/etc/group",
    "/etc/hosts", "/etc/nsswitch.conf", "/etc/localtime",
    "/etc/ssl/certs", "/etc/ssl/openssl.cnf", "/etc/ca-certificates",
)
_RAW_RE = re.compile(r'r(#*)"')
_CHAR_RE = re.compile(r"'(?:[^'\\\r\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[^\r\n]))'")


def py_col_to_utf16(line: str, py_col: int) -> int:
    """Convert a 0-based Python index into a UTF-16 code-unit offset."""
    return len(line[: max(0, min(py_col, len(line)))].encode("utf-16-le")) // 2


def utf16_to_py_col(line: str, utf16_col: int) -> int:
    """Convert a 0-based UTF-16 code-unit offset into a Python index."""
    acc = 0
    for idx, ch in enumerate(line):
        step = 2 if ord(ch) > 0xFFFF else 1
        if acc + step > utf16_col:
            return idx
        acc += step
    return len(line)


def mask_lean_comments(text: str) -> str:
    """Mask comments and string literals while keeping `{...}` interpolations."""
    out: list[str] = []
    i, n, depth, raw_h = 0, len(text), 0, -1
    stack: list[str | list[int]] = []
    while i < n:
        ch, nxt = text[i], (text[i + 1] if i + 1 < n else "")
        top = stack[-1] if stack else None
        in_str = top == "str" or (isinstance(top, list) and top[0] == 0)
        if depth > 0 and ch in "/-" and nxt in "-/" and ch != nxt:
            depth, i = depth + (1 if ch == "/" else -1), i + 2
            out.append("  ")
        elif raw_h >= 0 and ch == '"' and text.startswith("#" * raw_h, i + 1):
            out.append('"' + " " * raw_h)
            i, raw_h = i + 1 + raw_h, -1
        elif depth > 0 or raw_h >= 0:
            out.append("\n" if ch == "\n" else " ")
            i += 1
        elif in_str:
            if ch == "\\" and i + 1 < n and nxt not in ("\n", "\r"):
                out.append("  ")
                i += 2
            elif ch == '"':
                stack.pop()
                out.append('"')
                i += 1
            elif isinstance(top, list) and ch == "{":
                top[0] = 1
                out.append("{")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif isinstance(top, list) and top[0] > 0 and ch in "{}":
            top[0] += 1 if ch == "{" else -1
            out.append(ch)
            i += 1
        elif ch == "«":
            end_g = text.find("»", i + 1)
            stop = end_g + 1 if end_g >= 0 else n
            inner = text[i + 1 : end_g] if end_g >= 0 else text[i + 1 :]
            if inner in ("sorryAx", "_root_"):
                out.append(text[i:stop])
            else:
                masked = "".join(c if c in "\r\n" else " " for c in inner)
                out.append("«" + masked + ("»" if end_g >= 0 else ""))
            i = stop
        elif (
            ch == "'"
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'»"))
            and (cm := _CHAR_RE.match(text, i))
        ):
            out.append("'" + " " * (cm.end() - i - 2) + "'")
            i = cm.end()
        elif (
            ch == "r"
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'»."))
            and (mr := _RAW_RE.match(text, i))
        ):
            raw_h, i = len(mr.group(1)), mr.end()
            out.append(" " * raw_h + ' "')
        elif ch == '"':
            is_interp = (
                i >= 2
                and text[i - 1] == "!"
                and (text[i - 2].isalnum() or text[i - 2] in "_'»")
            )
            stack.append([0] if is_interp else "str")
            out.append('"')
            i += 1
        elif ch == "-" and nxt == "-":
            end_i = n if (e := text.find("\n", i)) < 0 else e
            out.append(" " * (end_i - i))
            i = end_i
        elif ch == "/" and nxt == "-":
            depth, i = 1, i + 2
            out.append("  ")
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def path_to_uri(path: str | Path) -> str:
    return Path(path).expanduser().resolve().as_uri()


def uri_to_path(uri: str) -> str:
    parsed = urlparse(uri)
    if parsed.scheme.lower() != "file":
        return uri
    netloc = "" if parsed.netloc.lower() == "localhost" else parsed.netloc
    if os.name == "nt":
        import nturl2path

        tail = re.sub(r"%3[aA]", ":", f"//{netloc}{parsed.path}")
        return nturl2path.url2pathname(tail)
    return f"//{netloc}{unquote(parsed.path)}" if netloc else unquote(parsed.path)


def middle_clip(text: str, max_chars: int = 3600) -> str:
    """Compact oversized output preserving head and tail context."""
    if len(text) <= max_chars:
        return text
    head = (max_chars * 3) // 5
    tail = max(0, max_chars - head - 64)
    return f"{text[:head]}\n\n... [{len(text) - head - tail} chars omitted] ...\n\n{text[-tail:]}"


def _reject_hardlinks(root: Path) -> None:
    stack = [root]
    while stack:
        cur = stack.pop()
        with os.scandir(cur) as it:
            for entry in it:
                st = entry.stat(follow_symlinks=False)
                if stat.S_ISDIR(st.st_mode):
                    stack.append(Path(entry.path))
                elif stat.S_ISREG(st.st_mode) and st.st_nlink > 1:
                    raise PermissionError(
                        f"Refusing writable sandbox dir with hardlinked file "
                        f"(nlink={st.st_nlink}): {entry.path}"
                    )


def _trusted_bwrap_uids() -> frozenset[int]:
    uids = {0}
    with contextlib.suppress(OSError, ValueError):
        lines = Path("/proc/self/uid_map").read_text(encoding="utf-8").splitlines()
        mapped = [int(p[2]) for ln in lines if len(p := ln.split()) == 3]
        if mapped and sum(mapped) < 4294967295:
            ov = Path("/proc/sys/kernel/overflowuid")
            uids.add(int(ov.read_text(encoding="utf-8").strip()) if ov.is_file() else 65534)
            uids.add(os.getuid())
    return frozenset(uids)


def _is_trusted_bwrap_path(raw: str) -> bool:
    p = Path(raw)
    if not p.is_absolute() or not p.exists():
        return False
    try:
        res = p.resolve()
    except OSError:
        return False
    if not any(str(res).startswith(pfx) for pfx in _TRUSTED_BWRAP_PREFIXES):
        return False
    trusted_uids = _trusted_bwrap_uids()
    for check in (p, res):
        cur = check
        while True:
            try:
                st = cur.lstat()
            except OSError:
                return False
            # Allow Nix `/nix/store` sticky mode 01775 while keeping store
            # entries beneath it strict against group/world writes.
            allow_nix_store = (
                cur == Path("/nix/store")
                and stat.S_ISDIR(st.st_mode)
                and (st.st_mode & 0o002) == 0
                and (st.st_mode & stat.S_ISVTX) != 0
            )
            bad_mode = (
                not stat.S_ISLNK(st.st_mode)
                and (st.st_mode & 0o022) != 0
                and not allow_nix_store
            )
            if st.st_uid not in trusted_uids or bad_mode:
                return False
            if cur == cur.parent:
                break
            cur = cur.parent
    return res.is_file()


def _find_trusted_bwrap() -> str | None:
    for cand in (shutil.which("bwrap", path=_SYS_BWRAP_PATH), shutil.which("bwrap")):
        if cand is None:
            continue
        if _is_trusted_bwrap_path(cand):
            return cand
        raise PermissionError(f"Refusing untrusted `bwrap` executable: {cand}")
    return None


def caller_homes() -> tuple[Path, ...]:
    """Return deduplicated caller homes from `$HOME` and `/etc/passwd`."""
    out: list[Path] = []
    with contextlib.suppress(RuntimeError, OSError):
        out.append(Path.home())
    if hasattr(os, "getuid"):
        with contextlib.suppress(ImportError, KeyError, OSError):
            import pwd

            if pw_dir := pwd.getpwuid(os.getuid()).pw_dir:
                out.append(Path(pw_dir))
    dedup: list[Path] = []
    for p in out:
        if p not in dedup:
            dedup.append(p)
    return tuple(dedup)


def build_sandbox_cmd(
    cmd: list[str], *, ro_binds: list[Path] | None = None, writable_dirs: list[Path] | None = None,
    hidden_homes: list[Path] | None = None, hidden_paths: list[Path] | None = None,
    inner_env: dict[str, str] | None = None, work_dir: Path | None = None,
    sandbox: bool = True,
) -> tuple[list[str], bool]:
    """Wrap `cmd` in deny-by-default `bwrap` with isolated IPC/PID/net."""
    if not sandbox:
        return cmd, False
    if not (bwrap := _find_trusted_bwrap()):
        if sys.platform.startswith("linux"):
            raise RuntimeError(
                "`bwrap` missing on system PATH (`--no-sandbox` / `ANNEAL_LSP_NO_SANDBOX=1`)."
            )
        return cmd, False
    wrapped = [bwrap, "--tmpfs", "/", "--dev", "/dev", "--proc", "/proc",
               "--unshare-ipc", "--unshare-pid", "--unshare-net", "--die-with-parent",
               "--cap-drop", "ALL", "--new-session"]
    sys_bound: list[Path] = []
    usr_p = Path("/usr")
    if usr_p.is_dir() and not usr_p.is_symlink():
        wrapped.extend(["--ro-bind", "/usr", "/usr"])
        sys_bound.append(usr_p)
    for sp_str in _SYS_RO_LINKS:
        sp_p = Path(sp_str)
        if sp_p.is_symlink():
            tgt = os.readlink(sp_p)
            abs_t = Path(tgt if tgt.startswith("/") else os.path.normpath(f"/{tgt}"))
            if abs_t == usr_p or abs_t.is_relative_to(usr_p) or any(
                abs_t.is_relative_to(Path(d)) for d in _SYS_RO_DIRS
            ):
                wrapped.extend(["--symlink", tgt, sp_str])
            elif sp_p.is_dir():
                wrapped.extend(["--ro-bind", sp_str, sp_str])
                sys_bound.append(sp_p)
        elif sp_p.is_dir():
            wrapped.extend(["--ro-bind", sp_str, sp_str])
            sys_bound.append(sp_p)
    for d_str in _SYS_RO_DIRS:
        dp = Path(d_str)
        if dp.is_dir() and not dp.is_symlink():
            wrapped.extend(["--ro-bind", d_str, d_str])
            sys_bound.append(dp)
    for e_str in _ETC_RO_PATHS:
        ep = Path(e_str)
        with contextlib.suppress(OSError):
            if ep.exists() and not stat.S_ISSOCK(ep.stat().st_mode):
                wrapped.extend(["--ro-bind", e_str, e_str])
                sys_bound.append(ep)
    hidden, forbidden, rehide = [], {Path("/")}, []

    def hide(cand: Path | None) -> Path | None:
        with contextlib.suppress(OSError):
            if cand and cand.exists() and (res := cand.resolve()).is_dir() and res != Path("/"):
                if not any(res == h or res.is_relative_to(h) for h in hidden):
                    wrapped.extend(["--tmpfs", str(res)])
                    hidden.append(res)
                return res
        return None

    for sys_tmp in (Path("/tmp"), Path("/var/tmp"), Path("/run"), Path("/var/run")):
        if r := hide(sys_tmp):
            if r not in rehide:
                rehide.append(r)
    nix_sw = Path("/run/current-system/sw")
    raw_xdg = os.environ.get("XDG_RUNTIME_DIR", "").strip()
    rt = (Path(raw_xdg).expanduser() if raw_xdg else None, Path(f"/run/user/{os.getuid()}"))
    for is_home, cand in (*((True, p) for p in (*caller_homes(), *(hidden_homes or []))),
                          *((False, p) for p in rt)):
        if r := hide(cand):
            forbidden.update({r, r / ".local"} if is_home else {r})
            if r not in rehide:
                rehide.append(r)
    wd_res = work_dir.resolve() if work_dir is not None else None
    if wd_res is not None and (wd_res in hidden or wd_res in forbidden):
        raise PermissionError(
            f"Refusing hidden workspace root `{wd_res}` in sandbox; "
            f"move `.lean` files into a subdirectory (e.g. `{wd_res}/ws/`)."
        )
    sock_cands = list(hidden_paths or [])
    if env_sock := os.environ.get("ANNEAL_LSP_SOCKET", "").strip():
        sock_cands.append(Path(os.path.abspath(str(Path(env_sock).expanduser()))).parent)
    post_hide: list[Path] = []
    for hp in sock_cands:
        if hp.is_symlink():
            raise PermissionError(f"Refusing symlinked socket directory: {hp}")
        if hp.exists():
            hres = hp.resolve()
            if not hres.is_dir() or hres == Path("/"):
                raise PermissionError(f"Unsafe hidden socket directory: {hp}")
            forbidden.add(hres)
            if wd_res is not None and (wd_res == hres or wd_res.is_relative_to(hres)):
                raise PermissionError(
                    f"Workspace root `{wd_res}` overlaps hidden socket directory `{hres}`."
                )
            if hres not in post_hide:
                post_hide.append(hres)
    if nix_sw.is_dir() and nix_sw not in forbidden and not any(
        nix_sw == ph or nix_sw.is_relative_to(ph) for ph in post_hide
    ):
        wrapped.extend(["--ro-bind", str(nix_sw), str(nix_sw)])
        sys_bound.append(nix_sw)
    sys_set = set(sys_bound)
    ro_res = sorted({
        r for d in (ro_binds or []) if d.exists() and (r := d.resolve()) not in forbidden
        and r not in hidden and r not in sys_set
        and not any(r == ph or r.is_relative_to(ph) for ph in post_hide)
    }, key=lambda p: len(p.parts))
    wr_res = sorted({
        w_res for w in (writable_dirs or [])
        if w.is_dir() and not w.is_symlink() and (w_res := w.resolve()) not in forbidden
        and not any(w_res == ph or w_res.is_relative_to(ph) for ph in post_hide)
    }, key=lambda p: len(p.parts))
    for w_res in wr_res:
        _reject_hardlinks(w_res)
    mount_ops: list[tuple[int, int, str, Path]] = [
        (len(d.parts), 0, "--ro-bind", d) for d in ro_res
    ]
    mount_ops.extend((len(d.parts), 0, "--bind", d) for d in wr_res)
    for hd in sorted(rehide, key=lambda p: len(p.parts)):
        if any(hd == m or hd.is_relative_to(m) for m in (*ro_res, *wr_res)):
            mount_ops.append((len(hd.parts), 1, "--tmpfs", hd))
    for _, _, flag, d in sorted(mount_ops, key=lambda it: (it[0], it[1], str(it[3]))):
        if flag == "--tmpfs":
            wrapped.extend([flag, str(d)])
        else:
            wrapped.extend([flag, str(d), str(d)])
    exposed = (*sys_bound, *ro_res, *wr_res)
    for ph in sorted(post_hide, key=lambda p: len(p.parts)):
        in_hidden = any(ph == h or ph.is_relative_to(h) for h in hidden)
        in_exposed = any(ph == m or ph.is_relative_to(m) for m in exposed)
        if not in_hidden or in_exposed:
            wrapped.extend(["--tmpfs", str(ph)])
    if wd_res is not None:
        wrapped.extend(["--chdir", str(wd_res)])
    wrapped.extend(["--unsetenv", "LD_LIBRARY_PATH"])
    for k, v in sorted((inner_env or {}).items()):
        wrapped.extend(["--setenv", k, v])
    return [*wrapped, "--", *cmd], True


class LspRpcError(RuntimeError):
    """JSON-RPC error returned by a Lean LSP server."""

    def __init__(self, method: str, code: Any, detail: Any) -> None:
        self.method, self.code, self.detail = method, code, detail
        super().__init__(f"LSP `{method}` error: {detail}")


class LspProcess:
    """Framed stdio JSON-RPC 2.0 client managing a Lean LSP child."""

    def __init__(
        self, cmd: list[str], *, cwd: Path, env: dict[str, str],
        on_notification: Callable[[str, Any], None] | None = None,
        on_response: Callable[[], None] | None = None,
        spawn_fn: Callable[[list[str], Path, dict[str, str]], subprocess.Popen[bytes]]
        | None = None,
    ) -> None:
        self._on_notify, self._on_resp, self._next_id = on_notification, on_response, 1
        self._closed, self._closing, self._broken_stdin = False, False, False
        self._id_lock, self._write_lock = threading.Lock(), threading.Lock()
        self._cleanup_lock = threading.Lock()
        self._pending: dict[int, queue.Queue[dict[str, Any]]] = {}
        self._wake_r: int | None = None
        self._wake_w: int | None = None
        if spawn_fn is not None:
            self.proc = spawn_fn(cmd, cwd, env)
        else:
            self.proc = subprocess.Popen(
                cmd, cwd=str(cwd), env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL, start_new_session=True,
            )
        if self._raw_stdout_fd() is not None:
            self._wake_r, self._wake_w = os.pipe()
        self._read_thread = threading.Thread(target=self._read_loop, daemon=True)
        self._read_thread.start()

    def is_alive(self) -> bool:
        return not self._closed and not self._broken_stdin and self.proc.poll() is None

    def _raw_stdout_fd(self) -> int | None:
        out = self.proc.stdout
        if out is None or os.name != "posix":
            return None
        try:
            fd = out.fileno()
        except (OSError, ValueError, AttributeError):
            return None
        return fd if isinstance(fd, int) and not isinstance(fd, bool) and fd >= 0 else None

    def _wake_reader(self) -> None:
        with self._id_lock:
            wfd = self._wake_w
        if wfd is not None:
            with contextlib.suppress(OSError):
                os.write(wfd, b"\x00")

    def _terminate_child(self) -> None:
        if self.proc.poll() is not None:
            return
        killpg = getattr(os, "killpg", None)
        sigkill = getattr(signal, "SIGKILL", None)
        if killpg is not None and sigkill is not None:
            for sig, tm in ((signal.SIGTERM, 2.0), (sigkill, 1.0)):
                with contextlib.suppress(Exception):
                    killpg(os.getpgid(self.proc.pid), sig)
                    self.proc.wait(timeout=tm)
                    return
        with contextlib.suppress(Exception):
            self.proc.terminate()
            self.proc.wait(timeout=2.0)
        if self.proc.poll() is None:
            with contextlib.suppress(Exception):
                self.proc.kill()
                self.proc.wait(timeout=1.0)

    def _dispatch_frame(self, body: bytes) -> None:
        msg = json.loads(body.decode("utf-8", "replace"))
        if "id" in msg and ("result" in msg or "error" in msg):
            with self._id_lock:
                q = self._pending.pop(msg["id"], None)
            if q is not None:
                q.put(msg)
                if self._on_resp is not None:
                    self._on_resp()
        elif self._on_notify is not None and "method" in msg:
            self._on_notify(msg["method"], msg.get("params"))

    def _read_loop_fd(self, fd: int, wake_r: int) -> None:
        buf = bytearray()
        poller = select.poll() if hasattr(select, "poll") else None
        if poller is not None:
            ev = select.POLLIN | select.POLLHUP | select.POLLERR
            poller.register(fd, ev)
            poller.register(wake_r, ev)

        def fill() -> bool:
            while not self._closed:
                if poller is not None:
                    ready = {pfd for pfd, _ in poller.poll()}
                else:
                    ready = set(select.select([fd, wake_r], [], [])[0])
                if self._closed or wake_r in ready:
                    return False
                if fd in ready:
                    chunk = os.read(fd, 65536)
                    if not chunk:
                        return False
                    buf.extend(chunk)
                    return True
            return False

        def read_line() -> bytes:
            while (idx := buf.find(b"\n")) < 0:
                if not fill():
                    if not self._closed and buf:
                        tail = bytes(buf)
                        buf.clear()
                        return tail
                    return b""
            line = bytes(buf[: idx + 1])
            del buf[: idx + 1]
            return line

        while not self._closed:
            hdrs: dict[str, str] = {}
            while (raw := read_line()) not in (b"", b"\r\n", b"\n"):
                if b":" in raw:
                    k, v = raw.decode("ascii", "replace").split(":", 1)
                    hdrs[k.strip().lower()] = v.strip()
            n = int(hdrs.get("content-length") or 0)
            if not (bool(hdrs or raw) and 0 < n <= _MAX_FRAME_BYTES):
                break
            while len(buf) < n:
                if not fill():
                    return
            body = bytes(buf[:n])
            del buf[:n]
            self._dispatch_frame(body)

    def _read_loop_stream(self, out: Any) -> None:
        while not self._closed:
            hdrs: dict[str, str] = {}
            while (raw := out.readline()) not in (b"", b"\r\n", b"\n"):
                if b":" in raw:
                    k, v = raw.decode("ascii", "replace").split(":", 1)
                    hdrs[k.strip().lower()] = v.strip()
            n = int(hdrs.get("content-length") or 0)
            ok = bool(hdrs or raw) and 0 < n <= _MAX_FRAME_BYTES
            if not ok or len(body := out.read(n)) < n:
                break
            self._dispatch_frame(body)

    def _read_loop(self) -> None:
        try:
            fd = self._raw_stdout_fd()
            if fd is not None and self._wake_r is not None:
                self._read_loop_fd(fd, self._wake_r)
            else:
                out = self.proc.stdout
                assert out is not None
                self._read_loop_stream(out)
        except Exception:
            pass
        finally:
            with self._cleanup_lock:
                unexpected = not self._closed and not self._closing
                self._closed = True
                self._fail_pending()
                if unexpected:
                    if self.proc.poll() is None:
                        self._terminate_child()
                    self._close_streams()

    @staticmethod
    def _close_one_stream(strm: Any) -> None:
        if strm is not None:
            with contextlib.suppress(OSError, RuntimeError, ValueError):
                strm.close()

    def _close_streams(self, *, wait_reader: threading.Thread | None = None) -> None:
        with self._id_lock:
            stdin, stdout = self.proc.stdin, self.proc.stdout
            wr, ww = self._wake_r, self._wake_w
            self.proc.stdin, self.proc.stdout = None, None
            self._wake_r, self._wake_w = None, None
        self._close_one_stream(stdin)
        for pfd in (wr, ww):
            if pfd is not None:
                with contextlib.suppress(OSError):
                    os.close(pfd)
        if stdout is None:
            return
        if (
            wait_reader is not None
            and wait_reader is not threading.current_thread()
            and wait_reader.is_alive()
        ):
            def _reap_stdout() -> None:
                wait_reader.join()
                self._close_one_stream(stdout)

            threading.Thread(target=_reap_stdout, daemon=True).start()
        else:
            self._close_one_stream(stdout)

    def _fail_pending(self) -> None:
        with self._id_lock:
            pending, self._pending = list(self._pending.values()), {}
        for q in pending:
            q.put({"error": {"code": -32000, "message": "LSP process exited"}})
        if pending and self._on_resp is not None:
            self._on_resp()

    def _send(self, obj: dict[str, Any]) -> None:
        raw = json.dumps(obj).encode("utf-8")
        frame = f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii") + raw
        with self._write_lock:
            with self._id_lock:
                stdin = self.proc.stdin
            if not self.is_alive() or stdin is None:
                raise RuntimeError("LSP process is not running")
            try:
                stdin.write(frame)
                stdin.flush()
            except (OSError, ValueError) as exc:
                with self._id_lock:
                    self._broken_stdin = True
                self._fail_pending()
                raise RuntimeError(f"LSP process stdin closed: {exc}") from exc

    def notify(self, method: str, params: Any) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def start_request(
        self, method: str, params: Any,
    ) -> tuple[int, queue.Queue[dict[str, Any]]]:
        q: queue.Queue[dict[str, Any]] = queue.Queue(maxsize=1)
        with self._id_lock:
            rid, self._next_id = self._next_id, self._next_id + 1
            self._pending[rid] = q
        try:
            self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        except BaseException:
            self.finish_request(rid)
            raise
        return rid, q

    def finish_request(self, rid: int) -> None:
        with self._id_lock:
            self._pending.pop(rid, None)

    @staticmethod
    def unpack_reply(method: str, msg: dict[str, Any]) -> Any:
        if (err := msg.get("error")) is not None:
            code = err.get("code") if isinstance(err, dict) else None
            detail = err.get("message", err) if isinstance(err, dict) else err
            raise LspRpcError(method, code, detail)
        return msg.get("result")

    def request(self, method: str, params: Any, timeout_s: float = 30.0) -> Any:
        rid, q = self.start_request(method, params)
        try:
            msg = q.get(timeout=timeout_s)
        except queue.Empty as exc:
            raise TimeoutError(f"LSP `{method}` timed out after {timeout_s:.1f}s") from exc
        finally:
            self.finish_request(rid)
        return self.unpack_reply(method, msg)

    def close(self) -> None:
        do_shutdown = False
        with self._id_lock:
            if not self._closing:
                self._closing = True
                do_shutdown = not self._closed
        if do_shutdown and self.proc.poll() is None:
            with contextlib.suppress(Exception):
                self.request("shutdown", None, timeout_s=1.5)
                self.notify("exit", None)
                self.proc.wait(timeout=0.2)
        with self._cleanup_lock:
            self._closed = True
            self._fail_pending()
            with self._id_lock:
                stdin = self.proc.stdin
                self.proc.stdin = None
            self._close_one_stream(stdin)
            self._terminate_child()
            self._wake_reader()
            th = self._read_thread
        if th is not None and th is not threading.current_thread():
            th.join(timeout=1.0 if os.name == "posix" else 0.25)
        with self._cleanup_lock:
            self._close_streams(wait_reader=th)
