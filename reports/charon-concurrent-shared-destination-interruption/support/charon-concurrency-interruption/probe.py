#!/usr/bin/env python3
"""Bounded concurrent and interrupted pinned Charon/Cargo experiments."""
import argparse
import hashlib
import json
import os
import select
import shutil
import signal
import subprocess
import time
from pathlib import Path

TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST_BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
RUST_LIB = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib"
CHARON = TOOLS / "bin/charon"
CARGO = RUST_BIN / "cargo"
RUSTC = RUST_BIN / "rustc"
OUT = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def env():
    e = dict(os.environ)
    e.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
             CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_BUILD_JOBS="1", CARGO_INCREMENTAL="0",
             RAYON_NUM_THREADS="1", PATH=os.pathsep.join((str(RUST_BIN), str(TOOLS / "bin"), e.get("PATH", ""))),
             DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST_LIB), str(RUST_LIB / "rustlib/aarch64-apple-darwin/lib"), e.get("DYLD_LIBRARY_PATH", ""))))
    return e


def cmd(argv, cwd, e, timeout=25):
    t = time.monotonic()
    p = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=e,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        stdout, stderr = p.communicate(timeout=5)
    return {"argv": [str(x) for x in argv], "cwd": str(cwd), "rc": p.returncode,
            "stdout": stdout.decode(errors="replace"), "stderr": stderr.decode(errors="replace"),
            "elapsed_ms": round((time.monotonic()-t)*1000, 1), "pid": p.pid}


def pair(argv1, cwd1, e1, argv2, cwd2, e2, timeout=30):
    t = time.monotonic()
    procs = [subprocess.Popen([str(x) for x in argv], cwd=cwd, env=e,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
             for argv, cwd, e in ((argv1, cwd1, e1), (argv2, cwd2, e2))]
    rows = []
    try:
        for index, (p, argv, cwd) in enumerate(((procs[0], argv1, cwd1), (procs[1], argv2, cwd2))):
            remain = max(1, timeout-(time.monotonic()-t))
            stdout, stderr = p.communicate(timeout=remain)
            rows.append({"argv": [str(x) for x in argv], "cwd": str(cwd), "pid": p.pid,
                         "rc": p.returncode, "stdout": stdout.decode(errors="replace"),
                         "stderr": stderr.decode(errors="replace"),
                         "elapsed_ms_from_pair_start": round((time.monotonic()-t)*1000, 1),
                         "index": index})
    except Exception:
        for p in procs:
            if p.poll() is None: os.killpg(p.pid, signal.SIGKILL)
            p.communicate(timeout=5)
        raise
    return rows


def rs(name, extra=False, order=0):
    funcs = [f"pub fn marker_{name}(x: u32) -> u32 {{ x.wrapping_add({1 if name=='alpha' else 2}) }}",
             "pub fn common(x: u32) -> u32 { x.wrapping_mul(3) }"]
    if order: funcs.reverse()
    if extra: funcs.append("#[cfg(selected)] pub fn flagged(x: u32) -> u32 { x + 99 }")
    return "\n".join(funcs)+"\n"


def make_cargo(path, name):
    (path / "src").mkdir(parents=True)
    (path / "Cargo.toml").write_text(f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n')
    (path / "src/lib.rs").write_text(rs(name))


def direct(src, dest, crate, flags=()):
    return [CHARON, "rustc", "--preset", "aeneas", "--dest-file", dest,
            "--", src, "--crate-type", "lib", "--crate-name", crate, *flags]


def direct_all(src, base, crate):
    return [CHARON, "rustc", "--preset", "aeneas", "--format", "all", "--dest-file", base,
            "--", src, "--crate-type", "lib", "--crate-name", crate]


def cargo(path, dest):
    return [CHARON, "cargo", "--preset", "aeneas", "--dest-file", dest,
            "--", "--manifest-path", path / "Cargo.toml", "--lib", "--offline", "--locked"]


def item_name(parts):
    return "::".join(p["Ident"][0] if "Ident" in p else "<"+next(iter(p))+">" for p in parts)


def inspect(path):
    if not path.exists(): return {"exists": False}
    blob = path.read_bytes()
    row = {"exists": True, "bytes": len(blob), "sha256": sha(blob)}
    try:
        j = json.loads(blob)
        trans = j["translated"]
        names = []
        bodies = {}
        for f in trans.get("fun_decls", []):
            if f and f.get("item_meta", {}).get("is_local"):
                name = item_name(f["item_meta"].get("name", []))
                names.append(name)
                body = f.get("body")
                bodies[name] = sha(json.dumps(body, sort_keys=True, separators=(",", ":"))) if body is not None else None
        row.update(parseable=True, has_errors=j.get("has_errors"), crate=trans.get("crate_name"),
                   local_names=names, local_body_sha256=bodies,
                   file_count=len(trans.get("files", [])))
    except (json.JSONDecodeError, KeyError, TypeError) as ex:
        row.update(parseable=False, parse_error=repr(ex))
    return row


def file_set(directory):
    return {str(p.relative_to(directory)): inspect(p) if p.suffix == ".llbc" else
            {"bytes": p.stat().st_size, "sha256": sha(p.read_bytes())}
            for p in sorted(directory.rglob("*")) if p.is_file() and not p.is_fifo()}


def kill_blocked_fifo(argv, cwd, e, fifo, delay=.9):
    os.mkfifo(fifo)
    p = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=e,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    time.sleep(delay)
    alive = p.poll() is None
    if alive: os.killpg(p.pid, signal.SIGKILL)
    stdout, stderr = p.communicate(timeout=5)
    return {"pid": p.pid, "alive_before_kill": alive, "rc": p.returncode,
            "fifo_is_regular": fifo.is_file(), "fifo_is_fifo": fifo.is_fifo(),
            "stdout": stdout.decode(errors="replace"), "stderr": stderr.decode(errors="replace")}


def kill_partial_fifo(argv, cwd, e, fifo, prefix_path):
    os.mkfifo(fifo)
    fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
    p = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=e,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    start = time.monotonic()
    prefix = b""
    try:
        while time.monotonic()-start < 8 and not prefix:
            readable, _, _ = select.select([fd], [], [], .05)
            if readable:
                try: prefix = os.read(fd, 512)
                except BlockingIOError: pass
        alive = p.poll() is None
        if alive: os.killpg(p.pid, signal.SIGKILL)
        stdout, stderr = p.communicate(timeout=5)
        # Drain only bytes already queued after termination; this is a stream prefix, not a regular output file.
        while True:
            try: chunk = os.read(fd, 65536)
            except BlockingIOError: break
            if not chunk: break
            prefix += chunk
        prefix_path.write_bytes(prefix)
        return {"pid": p.pid, "alive_at_first_bytes": alive, "rc": p.returncode,
                "captured_prefix_bytes": len(prefix), "captured_prefix_sha256": sha(prefix),
                "prefix_json_parseable": inspect(prefix_path).get("parseable"),
                "fifo_is_fifo": fifo.is_fifo(),
                "stdout": stdout.decode(errors="replace"), "stderr": stderr.decode(errors="replace")}
    finally:
        os.close(fd)
        if p.poll() is None:
            os.killpg(p.pid, signal.SIGKILL)
            p.communicate(timeout=5)


def kill_between_formats(argv, cwd, e, base):
    json_path = Path(str(base)+".llbc")
    postcard = Path(str(base)+".llbc.postcard")
    os.mkfifo(postcard)
    p = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=e,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    start = time.monotonic()
    while time.monotonic()-start < 8 and not (json_path.exists() and inspect(json_path).get("parseable")):
        if p.poll() is not None: break
        time.sleep(.01)
    before = inspect(json_path)
    alive = p.poll() is None
    if alive: os.killpg(p.pid, signal.SIGKILL)
    stdout, stderr = p.communicate(timeout=5)
    return {"pid": p.pid, "alive_with_complete_json": alive and before.get("parseable") is True,
            "rc": p.returncode, "json_before_kill": before, "json_after_kill": inspect(json_path),
            "postcard_is_fifo": postcard.is_fifo(), "postcard_is_regular": postcard.is_file(),
            "stdout": stdout.decode(errors="replace"), "stderr": stderr.decode(errors="replace")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", type=Path, required=True)
    a = ap.parse_args()
    work = a.work.resolve()
    if work.exists(): raise SystemExit("--work must not exist")
    if shutil.disk_usage(work.parent).free < 10*(1 << 30): raise SystemExit("under 10 GiB free disk")
    work.mkdir(parents=True)
    artifacts = OUT / "artifacts"
    artifacts.mkdir(exist_ok=True)
    e = env()
    results = {"work": str(work), "tools": {"charon_sha256": sha(CHARON.read_bytes()),
               "cargo_sha256": sha(CARGO.read_bytes()), "rustc_sha256": sha(RUSTC.read_bytes()),
               "charon_version": cmd([CHARON, "version"], work, e),
               "cargo_version": cmd([CARGO, "--version"], work, e),
               "rustc_version": cmd([RUSTC, "--version"], work, e)}}
    try:
        srcdir = work / "sources"; srcdir.mkdir()
        srcs = {}
        for name in ("alpha", "beta"):
            srcs[name] = srcdir / f"{name}.rs"
            srcs[name].write_text(rs(name))
        results["source_hashes"] = {n: sha(p.read_bytes()) for n, p in srcs.items()}
        distinct = work / "distinct"; distinct.mkdir()
        pair_rows = pair(direct(srcs["alpha"], distinct/"alpha.llbc", "alpha"), work, e,
                         direct(srcs["beta"], distinct/"beta.llbc", "beta"), work, e)
        results["direct_distinct"] = {"processes": pair_rows, "files": file_set(distinct)}
        assert [x["rc"] for x in pair_rows] == [0, 0]
        assert {x["crate"] for x in results["direct_distinct"]["files"].values()} == {"alpha", "beta"}
        for p in distinct.glob("*.llbc"): shutil.copy2(p, artifacts / ("direct-distinct-"+p.name))

        # Repeated fresh process: same source/cfg/path, separate destination paths.
        restart = work / "restart"; restart.mkdir()
        results["restart"] = []
        for i in range(2):
            dst = restart / f"alpha-{i}.llbc"
            run = cmd(direct(srcs["alpha"], dst, "alpha"), work, e)
            results["restart"].append({"command": run, "llbc": inspect(dst)})
            shutil.copy2(dst, artifacts / ("restart-"+dst.name))
        assert all(x["command"]["rc"] == 0 for x in results["restart"])

        # Reordering and one cfg option distinguish raw format versus local semantic projection.
        variants = work / "variants"; variants.mkdir()
        order_source = srcdir / "alpha-reordered.rs"; order_source.write_text(rs("alpha", order=1))
        flag_source = srcdir / "alpha-flag.rs"; flag_source.write_text(rs("alpha", extra=True))
        results["variants"] = []
        for name, source, flags in (("reordered", order_source, ()), ("flag-off", flag_source, ()),
                                    ("flag-on", flag_source, ("--cfg", "selected"))):
            dst = variants / (name+".llbc")
            run = cmd(direct(source, dst, "alpha", flags), work, e)
            results["variants"].append({"case": name, "source_sha256": sha(source.read_bytes()),
                                         "flags": list(flags), "command": run, "llbc": inspect(dst)})
            assert run["rc"] == 0 and inspect(dst).get("parseable")
            shutil.copy2(dst, artifacts / ("variant-"+dst.name))

        # Direct CLI contention on one regular path; preserve each round's observed winner.
        collision = work / "collision"; collision.mkdir()
        results["direct_collisions"] = []
        for round_no in range(6):
            dst = collision / "shared.llbc"
            dst.unlink(missing_ok=True)
            rows = pair(direct(srcs["alpha"], dst, "alpha"), work, e,
                        direct(srcs["beta"], dst, "beta"), work, e)
            observed = inspect(dst)
            results["direct_collisions"].append({"round": round_no, "processes": rows, "file": observed})
            shutil.copy2(dst, artifacts / f"direct-collision-{round_no}.llbc")

        # Two independent Cargo packages, private target dirs, first distinct then one shared destination.
        packages = work / "cargo"; packages.mkdir()
        for name in ("alpha", "beta"):
            make_cargo(packages/name, name)
            lock = cmd([CARGO, "generate-lockfile", "--offline", "--manifest-path", packages/name/"Cargo.toml"], work, e)
            assert lock["rc"] == 0
        c_out = work / "cargo-distinct"; c_out.mkdir()
        c_env = {n: dict(e, CARGO_TARGET_DIR=str(work / ("target-"+n))) for n in ("alpha", "beta")}
        rows = pair(cargo(packages/"alpha", c_out/"alpha.llbc"), work, c_env["alpha"],
                    cargo(packages/"beta", c_out/"beta.llbc"), work, c_env["beta"])
        results["cargo_distinct"] = {"processes": rows, "files": file_set(c_out)}
        assert [x["rc"] for x in rows] == [0, 0]
        assert {x["crate"] for x in results["cargo_distinct"]["files"].values()} == {"alpha", "beta"}
        for p in c_out.glob("*.llbc"): shutil.copy2(p, artifacts / ("cargo-distinct-"+p.name))
        c_collision = work / "cargo-collision"; c_collision.mkdir()
        results["cargo_collisions"] = []
        for round_no in range(3):
            # Fresh targets force each Charon-producing wrapper invocation.
            c_env2 = {n: dict(e, CARGO_TARGET_DIR=str(work / f"collision-target-{round_no}-{n}"))
                      for n in ("alpha", "beta")}
            dst = c_collision / "shared.llbc"
            dst.unlink(missing_ok=True)
            rows = pair(cargo(packages/"alpha", dst), work, c_env2["alpha"],
                        cargo(packages/"beta", dst), work, c_env2["beta"])
            observed = inspect(dst)
            results["cargo_collisions"].append({"round": round_no, "processes": rows, "file": observed})
            shutil.copy2(dst, artifacts / f"cargo-collision-{round_no}.llbc")

        # Warm Cargo target: same process invocation command, but Cargo may skip Charon's wrapper.
        warm = work / "warm"; warm.mkdir()
        warm_env = dict(e, CARGO_TARGET_DIR=str(work / "target-warm"))
        results["warm"] = []
        dest = warm / "same.llbc"
        for stage in ("first", "unchanged", "source-touched"):
            if stage == "unchanged": dest.unlink()
            if stage == "source-touched":
                p = packages/"alpha/src/lib.rs"; p.write_text(p.read_text()+"\n// force Cargo rerun\n")
            run = cmd(cargo(packages/"alpha", dest), work, warm_env)
            results["warm"].append({"stage": stage, "command": run, "output": inspect(dest)})

        # Seed a valid old LLBC then fail extraction from malformed input at the same path.
        stale = work / "stale"; stale.mkdir()
        dst = stale / "shared.llbc"
        seed = cmd(direct(srcs["alpha"], dst, "alpha"), work, e)
        before = inspect(dst)
        bad = srcdir / "broken.rs"; bad.write_text("pub fn broken( -> u32 {\n")
        failed = cmd(direct(bad, dst, "beta"), work, e)
        results["failed_over_stale"] = {"seed": seed, "before": before, "failed": failed,
                                         "after": inspect(dst)}
        shutil.copy2(dst, artifacts / "stale-after-failed.llbc")

        # With --format all, output is a two-file family. A FIFO at the second
        # name creates a causal stop after the first JSON file is complete.
        multi = work / "multi"; multi.mkdir()
        base = multi / "seed"
        seed_multi = cmd(direct_all(srcs["alpha"], base, "alpha"), work, e)
        results["multi_seed"] = {"command": seed_multi, "files": file_set(multi)}
        assert seed_multi["rc"] == 0
        assert inspect(Path(str(base)+".llbc"))["crate"] == "alpha"
        results["multi_collisions"] = []
        for round_no in range(5):
            base = multi / f"shared-{round_no}"
            rows = pair(direct_all(srcs["alpha"], base, "alpha"), work, e,
                        direct_all(srcs["beta"], base, "beta"), work, e)
            js = Path(str(base)+".llbc")
            pc = Path(str(base)+".llbc.postcard")
            pretty = cmd([CHARON, "pretty-print", "--format", "postcard", pc], work, e)
            pretty_subject = ("alpha" if "alpha::marker_alpha" in pretty["stdout"] else
                              "beta" if "beta::marker_beta" in pretty["stdout"] else None)
            results["multi_collisions"].append({"round": round_no, "processes": rows,
                                                 "json": inspect(js), "postcard":
                                                 {"exists": pc.exists(), "bytes": pc.stat().st_size,
                                                  "sha256": sha(pc.read_bytes()),
                                                  "pretty_print_rc": pretty["rc"],
                                                  "pretty_subject": pretty_subject,
                                                  "pretty_stderr": pretty["stderr"]}})
            shutil.copy2(js, artifacts / f"multi-collision-{round_no}.llbc")
            shutil.copy2(pc, artifacts / f"multi-collision-{round_no}.llbc.postcard")

        staged_base = multi / "staged-interrupt"
        results["kill_between_formats"] = kill_between_formats(
            direct_all(srcs["alpha"], staged_base, "alpha"), work, e, staged_base)
        if Path(str(staged_base)+".llbc").is_file():
            shutil.copy2(Path(str(staged_base)+".llbc"), artifacts / "interrupted-first-complete.llbc")
        Path(str(staged_base)+".llbc.postcard").unlink()
        after_retry = cmd(direct_all(srcs["alpha"], staged_base, "alpha"), work, e)
        postcard_after = Path(str(staged_base)+".llbc.postcard")
        pretty_after = cmd([CHARON, "pretty-print", "--format", "postcard", postcard_after], work, e)
        results["retry_multi_after_kill"] = {"command": after_retry,
            "json": inspect(Path(str(staged_base)+".llbc")),
            "postcard": {"exists": postcard_after.is_file(), "bytes": postcard_after.stat().st_size,
                         "sha256": sha(postcard_after.read_bytes()),
                         "pretty_print_rc": pretty_after["rc"],
                         "marker_alpha": "alpha::marker_alpha" in pretty_after["stdout"]}}
        shutil.copy2(Path(str(staged_base)+".llbc"), artifacts / "interrupted-retry.llbc")
        shutil.copy2(postcard_after, artifacts / "interrupted-retry.llbc.postcard")

        # A named-pipe destination creates causal barriers at open and mid-stream write.
        fifo = work / "fifo"; fifo.mkdir()
        blocked = fifo / "no-reader.llbc"
        results["kill_before_reader"] = kill_blocked_fifo(direct(srcs["alpha"], blocked, "alpha"), work, e, blocked)
        large = srcdir / "large.rs"
        large.write_text("\n".join(f"pub fn f{i:04}(x: u32) -> u32 {{ x.wrapping_add({i}) }}" for i in range(320))+"\n")
        partial = fifo / "stream.llbc"
        prefix = artifacts / "fifo-interrupted-prefix.bin"
        results["kill_after_first_bytes"] = kill_partial_fifo(direct(large, partial, "large"), work, e, partial, prefix)
        retry = fifo / "retry.llbc"
        results["retry_after_kill"] = {"command": cmd(direct(large, retry, "large"), work, e, 35),
                                       "output": inspect(retry)}
        shutil.copy2(retry, artifacts / "retry-complete.llbc")
        results["final_file_sets"] = {"distinct": file_set(distinct), "collision": file_set(collision),
                                      "cargo_distinct": file_set(c_out), "cargo_collision": file_set(c_collision),
                                      "warm": file_set(warm), "stale": file_set(stale), "fifo": file_set(fifo),
                                      "multi": file_set(multi)}
    finally:
        blob = json.dumps(results, indent=2, sort_keys=True)+"\n"
        blob = blob.replace(str(work), "$WORK").replace(str(TOOLS), "$LOCAL_TOOLS")
        (OUT / "results.json").write_text(blob)
    print(json.dumps({"direct_collisions": len(results.get("direct_collisions", [])),
                      "cargo_collisions": len(results.get("cargo_collisions", [])),
                      "multi_collisions": len(results.get("multi_collisions", [])),
                      "warm": [(x["stage"], x["command"]["rc"], x["output"].get("exists")) for x in results.get("warm", [])],
                      "kill": {k: results[k].get("rc") for k in ("kill_before_reader", "kill_after_first_bytes", "kill_between_formats") if k in results}}, indent=2))


if __name__ == "__main__":
    main()
