#!/usr/bin/env python3
"""Revalidation probe for sandboxed interactive Lean 4 / verification playgrounds.

Measures locally (without hardcoded user paths):
1. bubblewrap spawn overhead (`--unshare-all` noop).
2. Cold `lean --stdin` vs warm persistent `lean --server` LSP inside `bwrap` (`prelude` and `import Init`),
   including `textDocument/completion` payload size on `#check Nat.`.
3. Lean elaborator containment inside `bwrap` (`/etc/passwd` read blocked, `IO.Process.output` allowed
   when seccomp is omitted) and Linux `ulimit -m` no-op vs `prlimit --as`.

Requires `bwrap` and a Lean 4 toolchain (`LEAN_BIN` or `lean` on PATH / `~/.elan`).
"""

import json
import os
import pathlib
import selectors
import shutil
import statistics
import subprocess
import sys
import tempfile
import time


def find_lean_toolchain() -> pathlib.Path | None:
    env_bin = os.environ.get("LEAN_BIN")
    if env_bin:
        p = pathlib.Path(env_bin).resolve()
        if p.exists():
            return p.parent.parent
    elan_root = pathlib.Path.home() / ".elan" / "toolchains"
    if elan_root.exists():
        for name in sorted(elan_root.iterdir()):
            if (name / "bin" / "lean").exists() and "v4.34" in name.name:
                return name
        for name in sorted(elan_root.iterdir()):
            if (name / "bin" / "lean").exists():
                return name
    which_lean = shutil.which("lean")
    if which_lean:
        return pathlib.Path(which_lean).resolve().parent.parent
    return None


def build_bwrap_cmd(toolchain_dir: pathlib.Path, work_dir: pathlib.Path, inner_cmd: list[str]) -> list[str]:
    cmd = [
        "bwrap",
        "--ro-bind", str(toolchain_dir), "/lean",
        "--ro-bind", "/usr", "/usr",
        "--ro-bind", str(work_dir), "/work",
        "--dev", "/dev",
        "--proc", "/proc",
        "--tmpfs", "/tmp",
        "--clearenv",
        "--setenv", "PATH", "/lean/bin:/usr/bin:/bin",
        "--setenv", "LEAN_PATH", "/lean/lib/lean:/work",
        "--setenv", "HOME", "/tmp",
        "--unshare-all",
        "--die-with-parent",
        "--chdir", "/work",
    ]
    if pathlib.Path("/etc/localtime").exists():
        cmd += ["--ro-bind", "/etc/localtime", "/etc/localtime"]
    for d in ("lib", "lib64", "bin", "sbin"):
        p = pathlib.Path("/") / d
        if p.is_symlink():
            cmd += ["--symlink", os.readlink(p), f"/{d}"]
        elif p.exists():
            cmd += ["--ro-bind", str(p), f"/{d}"]
    return cmd + ["--"] + inner_cmd


class LspReader:
    def __init__(self, proc: subprocess.Popen[bytes]) -> None:
        assert proc.stdout is not None
        self.proc = proc
        self.fd = proc.stdout.fileno()
        self.sel = selectors.DefaultSelector()
        self.sel.register(self.fd, selectors.EVENT_READ)
        self.buf = bytearray()

    def recv(self, deadline: float) -> dict:
        while True:
            idx = self.buf.find(b"\r\n\r\n")
            if idx != -1:
                hdr_raw = bytes(self.buf[:idx]).decode("ascii")
                headers = {}
                for line in hdr_raw.split("\r\n"):
                    k, v = line.split(":", 1)
                    headers[k.strip().lower()] = v.strip()
                length = int(headers["content-length"])
                total = idx + 4 + length
                if len(self.buf) >= total:
                    payload = bytes(self.buf[idx + 4 : total])
                    del self.buf[:total]
                    return json.loads(payload.decode("utf-8"))
            rem = deadline - time.perf_counter()
            if rem <= 0 or not self.sel.select(timeout=rem):
                raise TimeoutError("LSP recv timeout")
            chunk = os.read(self.fd, 65536)
            if not chunk:
                err = self.proc.stderr.read().decode("utf-8", "replace") if self.proc.stderr else ""
                raise EOFError(f"LSP EOF (rc={self.proc.poll()}, stderr={err[:300]})")
            self.buf.extend(chunk)


def lsp_send(proc: subprocess.Popen[bytes], msg: dict) -> None:
    assert proc.stdin is not None
    body = json.dumps(msg).encode("utf-8")
    proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
    proc.stdin.flush()


def main() -> int:
    report: dict = {}

    bwrap = shutil.which("bwrap")
    if not bwrap:
        print("SKIP: bwrap not installed on PATH", file=sys.stderr)
        return 0

    toolchain = find_lean_toolchain()
    if not toolchain:
        print("SKIP: lean toolchain not found", file=sys.stderr)
        return 0

    report["toolchain"] = toolchain.name

    with tempfile.TemporaryDirectory(prefix="pg_probe_") as td:
        td_path = pathlib.Path(td)

        # 1. bwrap noop overhead
        noop_ms = []
        for _ in range(5):
            t0 = time.perf_counter()
            r = subprocess.run(build_bwrap_cmd(toolchain, td_path, ["/bin/true"]), capture_output=True)
            noop_ms.append((time.perf_counter() - t0) * 1000.0)
            assert r.returncode == 0
        report["bwrap_noop_ms"] = {
            "n": len(noop_ms),
            "min": round(min(noop_ms), 2),
            "median": round(statistics.median(noop_ms), 2),
            "max": round(max(noop_ms), 2),
        }

        # 2. Cold lean --stdin vs warm LSP
        cold_init_ms = []
        for _ in range(3):
            t0 = time.perf_counter()
            r = subprocess.run(
                build_bwrap_cmd(toolchain, td_path, ["lean", "--stdin"]),
                input=b"import Init\ntheorem t1 : 1 + 1 = 2 := rfl\n",
                capture_output=True,
                timeout=30,
            )
            cold_init_ms.append((time.perf_counter() - t0) * 1000.0)
            assert r.returncode == 0
        report["cold_lean_init_ms"] = {
            "n": len(cold_init_ms),
            "median": round(statistics.median(cold_init_ms), 2),
        }

        proc = subprocess.Popen(
            build_bwrap_cmd(toolchain, td_path, ["lean", "--server"]),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        rdr = LspReader(proc)
        try:
            t0 = time.perf_counter()
            lsp_send(proc, {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"processId": None, "rootUri": "file:///work", "capabilities": {}}})
            while rdr.recv(t0 + 15).get("id") != 1:
                pass
            t_init = (time.perf_counter() - t0) * 1000.0
            lsp_send(proc, {"jsonrpc": "2.0", "method": "initialized", "params": {}})

            uri = "file:///work/Probe.lean"
            t_open0 = time.perf_counter()
            lsp_send(proc, {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {"textDocument": {"uri": uri, "languageId": "lean4", "version": 1, "text": "import Init\ntheorem t1 : 1 + 1 = 2 := rfl\n#check Nat."}},
            })
            while True:
                m = rdr.recv(t_open0 + 25)
                if m.get("method") == "$/lean/fileProgress" and m["params"].get("processing") == []:
                    break
            t_open = (time.perf_counter() - t_open0) * 1000.0

            lsp_send(proc, {
                "jsonrpc": "2.0",
                "id": 2,
                "method": "textDocument/completion",
                "params": {"textDocument": {"uri": uri}, "position": {"line": 2, "character": 11}},
            })
            t_c0 = time.perf_counter()
            while True:
                m = rdr.recv(t_c0 + 15)
                if m.get("id") == 2:
                    res = m.get("result")
                    items = res.get("items", []) if isinstance(res, dict) else (res or [])
                    report["lsp_init"] = {
                        "initialize_ms": round(t_init, 2),
                        "didOpen_ms": round(t_open, 2),
                        "completion_items": len(items),
                        "completion_bytes": len(json.dumps(res).encode("utf-8")),
                    }
                    break
        finally:
            proc.kill()
            proc.wait()

        # 3. Containment checks
        r_passwd = subprocess.run(
            build_bwrap_cmd(toolchain, td_path, ["lean", "--stdin"]),
            input=b'#eval IO.FS.readFile "/etc/passwd"\n',
            capture_output=True,
        )
        r_sh = subprocess.run(
            build_bwrap_cmd(toolchain, td_path, ["lean", "--stdin"]),
            input=b'import Lean\n#eval IO.Process.output { cmd := "sh", args := #["-c", "echo sandbox_exec_ok"] }\n',
            capture_output=True,
        )
        assert r_passwd.returncode != 0
        assert r_sh.returncode == 0
        report["containment"] = {
            "bwrap_read_passwd_rc": r_passwd.returncode,
            "bwrap_sh_without_seccomp_rc": r_sh.returncode,
        }

    # 4. Linux ulimit -m vs prlimit --as
    r_ulim_m = subprocess.run(
        ["bash", "-c", "ulimit -m 65536 && python3 -c 'b = bytearray(128*1024*1024); b[0]=1; print(len(b))'"],
        capture_output=True,
        text=True,
    )
    r_prlim_as = subprocess.run(
        ["prlimit", f"--as={64*1024*1024}", "python3", "-c", "b = bytearray(128*1024*1024); print('ok')"],
        capture_output=True,
        text=True,
    )
    assert r_ulim_m.returncode == 0
    assert r_prlim_as.returncode != 0
    report["linux_limits"] = {
        "ulimit_m_64MiB_alloc_128MiB_rc": r_ulim_m.returncode,
        "prlimit_as_64MiB_alloc_128MiB_rc": r_prlim_as.returncode,
    }

    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
