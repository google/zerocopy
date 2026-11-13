#!/usr/bin/env python3
import os
import re
import json
import time
import subprocess

S1991 = "/tmp/rust-s1991"
OUT_DIR = "/tmp/run-probe"
COMPILETEST = "/usr/local/google/home/joshlf/workspace/rust/build/x86_64-unknown-linux-gnu/stage1-tools-bin/compiletest"
SYSROOT_1991 = "/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"
SYSROOT_N1112 = "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-11-12-x86_64-unknown-linux-gnu"
FILECHECK = "/usr/local/google/home/joshlf/workspace/rust/build/x86_64-unknown-linux-gnu/ci-llvm/bin/FileCheck"

rustc_1991 = os.path.join(SYSROOT_1991, "bin/rustc")
rustc_n1112 = os.path.join(SYSROOT_N1112, "bin/rustc")
helpers_x64 = os.path.join(OUT_DIR, "helpers_x86_64")
helpers_i686 = os.path.join(OUT_DIR, "helpers_i686")
rtc_bin = os.path.join(OUT_DIR, "remote-test-client")
rts_bin = os.path.join(OUT_DIR, "remote-test-server")

def run_ct(name, src_root, rustc_path, sysroot, target, suite, mode, filters, extra_args=None, env_extra=None):
    build_root = os.path.join(OUT_DIR, "ct_build3", name)
    suite_build = os.path.join(build_root, "test", suite)
    os.makedirs(suite_build, exist_ok=True)
    helpers_dir = helpers_i686 if "i686" in target else helpers_x64
    cmd = [
        COMPILETEST,
        "--compile-lib-path", os.path.join(sysroot, "lib"),
        "--run-lib-path", os.path.join(sysroot, "lib", "rustlib", target, "lib"),
        "--rustc-path", rustc_path,
        "--python", "python3",
        "--src-root", src_root,
        "--src-test-suite-root", os.path.join(src_root, "tests", suite),
        "--build-root", build_root,
        "--build-test-suite-root", suite_build,
        "--sysroot-base", sysroot,
        "--stage", "1",
        "--stage-id", f"stage1-{target}",
        "--mode", mode,
        "--suite", suite,
        "--cc", "cc",
        "--cxx", "c++",
        "--cflags", "",
        "--cxxflags", "",
        "--llvm-components", "x86 aarch64 arm",
        "--llvm-version", "23.1.1",
        "--llvm-filecheck", FILECHECK,
        "--channel", "nightly",
        "--nightly-branch", "master",
        "--git-merge-commit-email", "bors@rust-lang.org",
        "--minicore-path", os.path.join(src_root, "tests/auxiliary/minicore.rs"),
        "--jobs", "8",
        "--host", "x86_64-unknown-linux-gnu",
        "--target", target,
        "--edition", "2021",
        "--default-codegen-backend", "llvm",
        "--host-rustcflags", f"-Lnative={helpers_x64}",
        "--target-rustcflags", f"-Lnative={helpers_dir}",
        "--force-rerun",
    ]
    if extra_args:
        if "--default-codegen-backend" in extra_args:
            idx = cmd.index("--default-codegen-backend")
            cmd.pop(idx)
            cmd.pop(idx)
        cmd.extend(extra_args)
    cmd.extend(filters)
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env["RUSTC_FORCE_RUSTC_VERSION"] = "compiletest"
    env["TMPDIR"] = os.path.join(OUT_DIR, "tmp")
    if env_extra:
        env.update(env_extra)
    t0 = time.time()
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env, timeout=180)
    dt = time.time() - t0
    suite_evt = {}
    failed_tests = []
    for line in p.stdout.splitlines():
        if line.startswith("{"):
            try:
                obj = json.loads(line)
                if obj.get("type") == "suite" and "passed" in obj:
                    suite_evt = obj
                elif obj.get("type") == "test" and obj.get("event") == "failed":
                    failed_tests.append((obj.get("name"), (obj.get("stdout") or "")[-400:]))
            except Exception:
                pass
    print(f"[{name}] rc={p.returncode} time={dt:.2f}s passed={suite_evt.get('passed')} failed={suite_evt.get('failed')} ignored={suite_evt.get('ignored')} exec_time={suite_evt.get('exec_time')}")
    for fn, out in failed_tests[:5]:
        print(f"  FAILED: {fn}\n    {out[:200]}")
    return {
        "name": name,
        "returncode": p.returncode,
        "wall_sec": round(dt, 3),
        "suite_event": suite_evt,
        "failed_tests": [fn for fn, _ in failed_tests],
    }

results = []

# Test remote-test-server + remote-test-client over TCP loopback
rts_work = os.path.join(OUT_DIR, "tmp/rts_work2")
os.makedirs(rts_work, exist_ok=True)
rts_env = os.environ.copy()
rts_env["TMPDIR"] = rts_work
rts_proc = subprocess.Popen(
    [rts_bin, "--bind", "127.0.0.1:28766"],
    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=rts_env
)
time.sleep(0.5)
try:
    results.append(run_ct(
        "ui_arith_x86_64_remote_test_server", S1991, rustc_1991, SYSROOT_1991,
        "x86_64-unknown-linux-gnu", "ui", "ui", ["numbers-arithmetic/"],
        extra_args=["--remote-test-client", rtc_bin],
        env_extra={"TEST_DEVICE_ADDR": "127.0.0.1:28766"}
    ))
finally:
    rts_proc.terminate()
    rts_proc.wait(timeout=5)

# Test Cranelift on S1991 numbers-arithmetic (skipping the 2 UI diagnostic tests whose error text changed in 1.102)
results.append(run_ct(
    "ui_arith_x86_64_cranelift", S1991, rustc_n1112, SYSROOT_N1112,
    "x86_64-unknown-linux-gnu", "ui", "ui", ["numbers-arithmetic/"],
    extra_args=[
        "--override-codegen-backend", "cranelift",
        "--default-codegen-backend", "cranelift",
        "--skip", "suggest-float-literal",
    ]
))

# Also test codegen-units and incremental suites on S1991 with rustc 1.99.1!
results.append(run_ct(
    "codegen_units_all", S1991, rustc_1991, SYSROOT_1991,
    "x86_64-unknown-linux-gnu", "codegen-units", "codegen-units", []
))

with open(os.path.join(OUT_DIR, "compiletest_part3_results.json"), "w") as f:
    json.dump(results, f, indent=2)
