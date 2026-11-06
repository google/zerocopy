#!/usr/bin/env python3
"""Study P1 (R7): Cargo workspace and build-graph capture with per-invocation binding and .amir v3 wire artifacts."""

import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import time

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
WS_DIR = os.path.join(BASE_DIR, "workspace")
ART_DIR = os.path.join(BASE_DIR, "artifacts")
TC_DIR = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61"
RUSTC = os.path.join(TC_DIR, "rust/bin/rustc")
CARGO = "/usr/local/google/home/joshlf/.cargo/bin/cargo"
CHARON = os.path.join(TC_DIR, "aeneas/bin/charon")
LIB_DIR = os.path.join(TC_DIR, "rust/lib")
HOST_LIB_DIR = os.path.join(TC_DIR, "rust/lib/rustlib/x86_64-unknown-linux-gnu/lib")
DRIVER_SRC = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/direct_mir_driver_v4.rs"
DRIVER_BIN = "/tmp/direct_mir_driver_v4_bin"


def sha256_file(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def fnv1a_16_bytes(data: bytes) -> list[int]:
    acc = 0x811C9DC5
    for b in data:
        acc = ((acc ^ b) * 0x01000193) % 65536
    return [acc & 0xFF, (acc >> 8) & 0xFF]


def parse_amir_v3_summary(path: str) -> dict:
    with open(path, "rb") as f:
        data = f.read()
    magic = data[:4].decode("ascii", errors="replace")
    version = data[4] if len(data) > 4 else -1
    rustc_hi = data[5] if len(data) > 5 else -1
    rustc_lo = data[6] if len(data) > 6 else -1
    fp16 = [data[7], data[8]] if len(data) > 8 else [-1, -1]
    payload_fp16 = fnv1a_16_bytes(data[9:]) if len(data) > 9 else [-1, -1]
    body_count = data[9] if len(data) > 9 else -1
    return {
        "magic": magic,
        "version": version,
        "rustc_hi": rustc_hi,
        "rustc_lo": rustc_lo,
        "fp16": fp16,
        "payload_fp16": payload_fp16,
        "fp16_matches_payload": fp16 == payload_fp16,
        "body_count": body_count,
        "size_bytes": len(data),
        "sha256": sha256_file(path),
    }


def run_timed(run_id: str, cmd: list, cwd: str, extra_env: dict, out_paths: list, allow_nonzero: bool = False):
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = f"{LIB_DIR}:{HOST_LIB_DIR}:" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = f"{TC_DIR}/rust/bin:{TC_DIR}/aeneas/bin:" + env.get("PATH", "")
    env["RUSTC"] = RUSTC
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"
    env.update(extra_env)

    rusage_before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    t0 = time.monotonic()
    proc = subprocess.run(
        ["/usr/bin/time", "-v"] + cmd,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
    )
    t1 = time.monotonic()
    rusage_after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss

    m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", proc.stderr)
    time_rss_bytes = int(m.group(1)) * 1024 if m else 0
    rusage_children_max_bytes = int(rusage_after) * 1024
    rss_bytes = time_rss_bytes if time_rss_bytes > 0 else rusage_children_max_bytes

    outputs = []
    for p in out_paths:
        full_p = p if os.path.isabs(p) else os.path.join(BASE_DIR, p)
        if os.path.exists(full_p):
            entry = {
                "path": os.path.relpath(full_p, BASE_DIR),
                "sha256": sha256_file(full_p),
                "size_bytes": os.path.getsize(full_p),
            }
            if full_p.endswith(".amir"):
                entry["amir_v3_header"] = parse_amir_v3_summary(full_p)
            outputs.append(entry)

    rec = {
        "run_id": run_id,
        "cmd": cmd,
        "exit_code": proc.returncode,
        "elapsed_ms": int(round((t1 - t0) * 1000)),
        "max_rss_bytes": rss_bytes,
        "rusage_children_ru_maxrss_bytes": rusage_children_max_bytes,
        "rusage_before_kb": int(rusage_before),
        "rusage_after_kb": int(rusage_after),
        "outputs": outputs,
    }
    print(f"{run_id}: exit={rec['exit_code']}, elapsed={rec['elapsed_ms']}ms, rss={rec['max_rss_bytes']}, outputs={len(outputs)}")
    if proc.returncode != 0 and not allow_nonzero:
        print("STDERR:", proc.stderr[:800])
    return rec


def main():
    os.makedirs(ART_DIR, exist_ok=True)
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = f"{LIB_DIR}:{HOST_LIB_DIR}:" + env.get("LD_LIBRARY_PATH", "")
    subprocess.run([RUSTC, "--edition=2021", "-O", DRIVER_SRC, "-o", DRIVER_BIN], env=env, check=True)

    # Clean temporary target dirs so cold builds are genuinely cold
    for d in (
        "/tmp/anneal_ws_target_default_v3",
        "/tmp/anneal_ws_target_always_encode_v3",
        "/tmp/anneal_ws_target_strict_v3",
        "/tmp/anneal_ws_target_check_v3",
        "/tmp/anneal_ws_target_charon_v3",
        "/tmp/anneal_ws_target_stateful_v3",
        "/tmp/anneal_ws_target_stateful_default_v3",
        "/tmp/anneal_ws_post_mono_probes",
    ):
        if os.path.exists(d):
            shutil.rmtree(d)

    wrapper_log = "/tmp/anneal_cargo_wrapper_invocations.jsonl"
    if os.path.exists(wrapper_log):
        os.remove(wrapper_log)

    wrapper_path = "/tmp/anneal_cargo_rustc_wrapper_v4.py"
    with open(wrapper_path, "w") as f:
        f.write(f"""#!/usr/bin/env python3
import hashlib, json, os, sys, subprocess

args = sys.argv[1:]
rustc_bin = args[0]
rest = args[1:]

crate_name = None
crate_types = []
cfg_flags = []
emit_kinds = []
extern_specs = []
edition = None
for i, a in enumerate(rest):
    if a == "--crate-name" and i + 1 < len(rest):
        crate_name = rest[i + 1]
    elif a == "--crate-type" and i + 1 < len(rest):
        crate_types.append(rest[i + 1])
    elif a == "--cfg" and i + 1 < len(rest):
        cfg_flags.append(rest[i + 1])
    elif a.startswith("--emit="):
        emit_kinds.extend(a.split("=", 1)[1].split(","))
    elif a == "--emit" and i + 1 < len(rest):
        emit_kinds.extend(rest[i + 1].split(","))
    elif a == "--extern" and i + 1 < len(rest):
        extern_specs.append(rest[i + 1])
    elif a.startswith("--edition="):
        edition = a.split("=", 1)[1]
    elif a == "--edition" and i + 1 < len(rest):
        edition = rest[i + 1]

is_build_script = (crate_name == "build_script_build")
role = "host_build_script" if is_build_script else "target_crate"
mode = os.environ.get("ANNEAL_WRAPPER_MODE", "full")
tag = os.environ.get("ANNEAL_WRAPPER_TAG", "default")
out_dir_env = os.environ.get("OUT_DIR", "")
cargo_features = sorted(
    k[len("CARGO_FEATURE_"):].lower()
    for k in os.environ
    if k.startswith("CARGO_FEATURE_")
)
generated_out_files = []
if out_dir_env and os.path.isdir(out_dir_env):
    for fn in sorted(os.listdir(out_dir_env)):
        fp = os.path.join(out_dir_env, fn)
        if os.path.isfile(fp):
            h = hashlib.sha256(open(fp, "rb").read()).hexdigest()
            generated_out_files.append({{"file": fn, "size_bytes": os.path.getsize(fp), "sha256": h}})

art_dir = "{ART_DIR}"
log_path = "{wrapper_log}"

inv_record = {{
    "tag": tag,
    "mode": mode,
    "crate_name": crate_name,
    "role": role,
    "is_build_script": is_build_script,
    "edition": edition,
    "crate_types": crate_types,
    "cfg_flags": cfg_flags,
    "cargo_features": cargo_features,
    "emit_kinds": emit_kinds,
    "extern_specs": extern_specs,
    "out_dir": out_dir_env,
    "generated_out_dir_files": generated_out_files,
}}

if not is_build_script and crate_name in (
    "dep_layout_core",
    "app_verifier_subject",
    "stateful_generic_lib",
    "client_contract_user",
    "client_direct_mir_inspector",
):
    out_json = os.path.join(art_dir, f"out_{{crate_name}}_{{tag}}.json")
    out_amir = os.path.join(art_dir, f"{{crate_name}}_{{tag}}.amir")
    driver_flags = [
        "--sysroot", "{TC_DIR}/rust",
        "-Z", "mir-preserve-ub",
        "--driver-include-const-owners",
        "--driver-out-json", out_json,
        "--driver-emit-amir-v3", out_amir,
    ]
    if crate_name == "stateful_generic_lib":
        out_bodies = os.path.join(art_dir, f"bodies_{{crate_name}}_{{tag}}.json")
        driver_flags.extend(["--driver-dump-bodies", out_bodies])
    if mode == "full":
        driver_flags.append("--driver-run-mono-collector")
    elif mode == "always_encode":
        driver_flags.extend(["-Z", "always-encode-mir=yes", "--driver-run-mono-collector"])
    inv_record["driver_flags_injected"] = driver_flags
    inv_record["out_json"] = os.path.basename(out_json)
    inv_record["out_amir"] = os.path.basename(out_amir)
    with open(log_path, "a") as lf:
        lf.write(json.dumps(inv_record) + "\\n")
    cmd = ["{DRIVER_BIN}"] + rest + driver_flags
    sys.exit(subprocess.call(cmd))
else:
    with open(log_path, "a") as lf:
        lf.write(json.dumps(inv_record) + "\\n")
    sys.exit(subprocess.call([rustc_bin] + rest))
""")
    os.chmod(wrapper_path, 0o755)

    def read_wrapper_events(tag: str) -> list:
        if not os.path.exists(wrapper_log):
            return []
        events = []
        with open(wrapper_log) as lf:
            for line in lf:
                obj = json.loads(line)
                if obj.get("tag") == tag:
                    events.append(obj)
        return events

    records = []

    # Run 1: Cold build of dep_layout_core and app_verifier_subject (default features)
    rec_cold = run_timed(
        "cargo_workspace_default_mir_encoding",
        [CARGO, "build", "--target-dir", "/tmp/anneal_ws_target_default_v3"],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "full", "ANNEAL_WRAPPER_TAG": "default"},
        [
            "artifacts/out_dep_layout_core_default.json",
            "artifacts/dep_layout_core_default.amir",
            "artifacts/out_app_verifier_subject_default.json",
            "artifacts/app_verifier_subject_default.amir",
        ],
    )
    rec_cold["driver_invocations"] = read_wrapper_events("default")
    records.append(rec_cold)

    # Copy short-named aliases dep_default.amir and app_default.amir
    shutil.copyfile(os.path.join(ART_DIR, "dep_layout_core_default.amir"), os.path.join(ART_DIR, "dep_default.amir"))
    shutil.copyfile(os.path.join(ART_DIR, "app_verifier_subject_default.amir"), os.path.join(ART_DIR, "app_default.amir"))

    # Run 2: Warm no-op rebuild against the exact same target-dir and mode/flags
    rec_warm = run_timed(
        "cargo_workspace_warm_noop_rebuild",
        [CARGO, "build", "--target-dir", "/tmp/anneal_ws_target_default_v3"],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "full", "ANNEAL_WRAPPER_TAG": "warm_noop"},
        [
            "artifacts/dep_layout_core_default.amir",
            "artifacts/app_verifier_subject_default.amir",
        ],
    )
    rec_warm["driver_invocations"] = read_wrapper_events("warm_noop")
    rec_warm["cached_crate_reuse_observed"] = len(rec_warm["driver_invocations"]) == 0
    records.append(rec_warm)

    # Run 3: Full build with -Z always-encode-mir=yes
    rec_always = run_timed(
        "cargo_workspace_always_encode_mir",
        [CARGO, "build", "--target-dir", "/tmp/anneal_ws_target_always_encode_v3"],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "always_encode", "ANNEAL_WRAPPER_TAG": "always_encode"},
        [
            "artifacts/out_dep_layout_core_always_encode.json",
            "artifacts/dep_layout_core_always_encode.amir",
            "artifacts/out_app_verifier_subject_always_encode.json",
            "artifacts/app_verifier_subject_always_encode.amir",
        ],
    )
    rec_always["driver_invocations"] = read_wrapper_events("always_encode")
    records.append(rec_always)

    # Run 4: Feature-toggled build (--features strict_align) with -Z always-encode-mir=yes
    rec_strict = run_timed(
        "cargo_workspace_strict_align_feature",
        [CARGO, "build", "--features", "strict_align", "--target-dir", "/tmp/anneal_ws_target_strict_v3"],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "always_encode", "ANNEAL_WRAPPER_TAG": "strict_align"},
        [
            "artifacts/out_dep_layout_core_strict_align.json",
            "artifacts/dep_layout_core_strict_align.amir",
            "artifacts/out_app_verifier_subject_strict_align.json",
            "artifacts/app_verifier_subject_strict_align.amir",
        ],
    )
    rec_strict["driver_invocations"] = read_wrapper_events("strict_align")
    records.append(rec_strict)

    # Copy short-named aliases dep_strict.amir and app_strict.amir
    shutil.copyfile(os.path.join(ART_DIR, "dep_layout_core_strict_align.amir"), os.path.join(ART_DIR, "dep_strict.amir"))
    shutil.copyfile(os.path.join(ART_DIR, "app_verifier_subject_strict_align.amir"), os.path.join(ART_DIR, "app_strict.amir"))

    # Run 5: Fast cargo check mode (--emit=dep-info,metadata, no mono collector)
    rec_check = run_timed(
        "cargo_workspace_check_fast_mode",
        [CARGO, "check", "--target-dir", "/tmp/anneal_ws_target_check_v3"],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "check", "ANNEAL_WRAPPER_TAG": "check_fast"},
        [
            "artifacts/out_dep_layout_core_check_fast.json",
            "artifacts/out_app_verifier_subject_check_fast.json",
        ],
        allow_nonzero=True,
    )
    rec_check["driver_invocations"] = read_wrapper_events("check_fast")
    with open(os.path.join(ART_DIR, "out_dep_layout_core_check_fast.json")) as jf:
        check_json = json.load(jf)
    rec_check["mono_collection_completed"] = check_json.get("mono_collection_completed")
    rec_check["has_errors_at_after_analysis"] = check_json.get("has_errors_at_after_analysis")
    rec_check["compilation_completeness_status"] = (
        "accepted_complete"
        if check_json.get("mono_collection_completed") and not check_json.get("has_errors_at_after_analysis")
        else "rejected_incomplete_compilation"
    )
    records.append(rec_check)

    # Run 6: Post-monomorphization const evaluation probes (including a genuine unreferenced failing mention alpha::<()>!)
    os.makedirs("/tmp/anneal_ws_post_mono_probes", exist_ok=True)
    probe_reachable_src = "/tmp/anneal_ws_post_mono_probes/post_mono_reachable_fail.rs"
    with open(probe_reachable_src, "w") as pf:
        pf.write("""#![allow(dead_code)]
pub struct ZstProbe<T>(core::marker::PhantomData<T>);
impl<T> ZstProbe<T> {
    pub const VALID: usize = { assert!(core::mem::size_of::<T>() > 0, "post-mono ZST guard"); 1 };
}
pub fn alpha<T>(x: usize) -> usize {
    const { assert!(core::mem::size_of::<T>() > 0, "post-mono ZST guard"); }
    x.wrapping_add(8)
}
pub fn beta(x: usize) -> usize {
    alpha::<()>(x)
}
""")
    probe_unreachable_src = "/tmp/anneal_ws_post_mono_probes/post_mono_unreachable_unused.rs"
    with open(probe_unreachable_src, "w") as pf:
        pf.write("""#![allow(dead_code)]
pub struct ZstProbe<T>(core::marker::PhantomData<T>);
impl<T> ZstProbe<T> {
    pub fn unused_failing_assoc(x: usize) -> usize {
        alpha::<()>(x)
    }
}
pub type UnusedFailingZstMention = ZstProbe<()>;
pub fn alpha<T>(x: usize) -> usize {
    const { assert!(core::mem::size_of::<T>() > 0, "post-mono ZST guard"); }
    x.wrapping_add(8)
}
pub fn beta(x: usize) -> usize {
    alpha::<u64>(x)
}
""")

    # 6a: Reachable post-mono const failure without mono collector (check-only provisional mode) -> rejected_incomplete_compilation (exit 2)
    rec_post_mono_provisional = run_timed(
        "post_mono_reachable_const_without_mono_collector",
        [
            DRIVER_BIN,
            "--crate-name", "post_mono_reachable_fail",
            "--edition=2021",
            "--crate-type", "lib",
            "--emit=metadata",
            "--out-dir", "/tmp/anneal_ws_post_mono_probes",
            "--sysroot", f"{TC_DIR}/rust",
            "-Z", "mir-preserve-ub",
            "--driver-out-json", os.path.join(ART_DIR, "out_post_mono_reachable_provisional.json"),
            "--driver-emit-amir-v3", os.path.join(ART_DIR, "post_mono_reachable_provisional.amir"),
            probe_reachable_src,
        ],
        WS_DIR,
        {},
        [
            "artifacts/out_post_mono_reachable_provisional.json",
        ],
        allow_nonzero=True,
    )
    with open(os.path.join(ART_DIR, "out_post_mono_reachable_provisional.json")) as jf:
        pm_prov_json = json.load(jf)
    rec_post_mono_provisional["amir_v3_status"] = pm_prov_json.get("amir_v3_status")
    rec_post_mono_provisional["mono_collection_completed"] = pm_prov_json.get("mono_collection_completed")
    rec_post_mono_provisional["has_errors_at_after_analysis"] = pm_prov_json.get("has_errors_at_after_analysis")
    rec_post_mono_provisional["compilation_completeness_status"] = pm_prov_json.get("amir_v3_status")
    records.append(rec_post_mono_provisional)

    # 6b: Reachable post-mono const failure WITH mono collector -> rustc const-eval error (nonzero exit)
    rec_post_mono_fail = run_timed(
        "post_mono_reachable_const_with_mono_collector_fails",
        [
            DRIVER_BIN,
            "--crate-name", "post_mono_reachable_fail",
            "--edition=2021",
            "--crate-type", "lib",
            "--out-dir", "/tmp/anneal_ws_post_mono_probes",
            "--sysroot", f"{TC_DIR}/rust",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json", os.path.join(ART_DIR, "out_post_mono_reachable_full.json"),
            "--driver-emit-amir-v3", os.path.join(ART_DIR, "post_mono_reachable_full.amir"),
            probe_reachable_src,
        ],
        WS_DIR,
        {},
        [],
        allow_nonzero=True,
    )
    rec_post_mono_fail["compilation_completeness_status"] = "rejected_post_mono_const_error"
    records.append(rec_post_mono_fail)

    # 6c: Unreferenced private failing mention `alpha::<()>(x)` alongside reachable `alpha::<u64>(x)` WITH mono collector -> accepted_complete
    rec_post_mono_unused = run_timed(
        "post_mono_unused_const_with_mono_collector_accepted",
        [
            DRIVER_BIN,
            "--crate-name", "post_mono_unreachable_unused",
            "--edition=2021",
            "--crate-type", "lib",
            "--out-dir", "/tmp/anneal_ws_post_mono_probes",
            "--sysroot", f"{TC_DIR}/rust",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json", os.path.join(ART_DIR, "out_post_mono_unused_accepted.json"),
            "--driver-emit-amir-v3", os.path.join(ART_DIR, "post_mono_unused_accepted.amir"),
            probe_unreachable_src,
        ],
        WS_DIR,
        {},
        [
            "artifacts/out_post_mono_unused_accepted.json",
            "artifacts/post_mono_unused_accepted.amir",
        ],
    )
    with open(os.path.join(ART_DIR, "out_post_mono_unused_accepted.json")) as jf:
        pm_unused_json = json.load(jf)
    rec_post_mono_unused["amir_v3_status"] = pm_unused_json.get("amir_v3_status")
    rec_post_mono_unused["mono_collection_completed"] = pm_unused_json.get("mono_collection_completed")
    rec_post_mono_unused["has_errors_at_after_analysis"] = pm_unused_json.get("has_errors_at_after_analysis")
    rec_post_mono_unused["compilation_completeness_status"] = pm_unused_json.get("amir_v3_status")
    rec_post_mono_unused["contains_unreferenced_failing_zst_mention"] = True
    rec_post_mono_unused["collected_mono_items"] = pm_unused_json.get("collected_mono_items", [])
    records.append(rec_post_mono_unused)

    # Run 7: Charon cargo extraction on app_verifier_subject
    records.append(
        run_timed(
            "charon_cargo_app_verifier_subject",
            [
                CHARON,
                "cargo",
                "--ullbc",
                "--mir",
                "elaborated",
                "--dest-file",
                os.path.join(ART_DIR, "app_verifier_subject.ullbc"),
                "--",
                "--package",
                "app_verifier_subject",
                "--target-dir",
                "/tmp/anneal_ws_target_charon_v3",
            ],
            WS_DIR,
            {},
            ["artifacts/app_verifier_subject.ullbc"],
        )
    )

    # Run 8: H3 3-crate stateful generic library workspace (stateful_generic_lib, client_contract_user, client_direct_mir_inspector)
    rec_stateful = run_timed(
        "cargo_workspace_stateful_lib_always_encode",
        [
            CARGO,
            "build",
            "-p",
            "stateful_generic_lib",
            "-p",
            "client_contract_user",
            "-p",
            "client_direct_mir_inspector",
            "--target-dir",
            "/tmp/anneal_ws_target_stateful_v3",
        ],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "always_encode", "ANNEAL_WRAPPER_TAG": "always_encode"},
        [
            "artifacts/out_stateful_generic_lib_always_encode.json",
            "artifacts/bodies_stateful_generic_lib_always_encode.json",
            "artifacts/stateful_generic_lib_always_encode.amir",
            "artifacts/out_client_contract_user_always_encode.json",
            "artifacts/client_contract_user_always_encode.amir",
            "artifacts/out_client_direct_mir_inspector_always_encode.json",
            "artifacts/client_direct_mir_inspector_always_encode.amir",
        ],
    )
    rec_stateful["driver_invocations"] = [
        ev
        for ev in read_wrapper_events("always_encode")
        if ev.get("crate_name") in ("stateful_generic_lib", "client_contract_user", "client_direct_mir_inspector")
    ]
    records.append(rec_stateful)

    # Run 8b: H3 3-crate stateful generic library workspace in default metadata mode (without -Z always-encode-mir=yes)
    rec_stateful_default = run_timed(
        "cargo_workspace_stateful_lib_default_encoding",
        [
            CARGO,
            "build",
            "-p",
            "stateful_generic_lib",
            "-p",
            "client_contract_user",
            "-p",
            "client_direct_mir_inspector",
            "--target-dir",
            "/tmp/anneal_ws_target_stateful_default_v3",
        ],
        WS_DIR,
        {"RUSTC_WRAPPER": wrapper_path, "ANNEAL_WRAPPER_MODE": "full", "ANNEAL_WRAPPER_TAG": "stateful_default"},
        [
            "artifacts/out_stateful_generic_lib_stateful_default.json",
            "artifacts/stateful_generic_lib_stateful_default.amir",
            "artifacts/out_client_contract_user_stateful_default.json",
            "artifacts/client_contract_user_stateful_default.amir",
            "artifacts/out_client_direct_mir_inspector_stateful_default.json",
            "artifacts/client_direct_mir_inspector_stateful_default.amir",
        ],
    )
    rec_stateful_default["driver_invocations"] = read_wrapper_events("stateful_default")
    records.append(rec_stateful_default)

    # Run 9: Charon cargo extraction on client_direct_mir_inspector (with --rustc-arg=-Zmir-preserve-ub and --ullbc --mir elaborated)
    records.append(
        run_timed(
            "charon_cargo_stateful_generic_lib_ullbc",
            [
                CHARON,
                "cargo",
                "--ullbc",
                "--mir",
                "elaborated",
                "--rustc-arg=-Zmir-preserve-ub",
                "--dest-file",
                os.path.join(ART_DIR, "stateful_generic_lib.ullbc"),
                "--",
                "--package",
                "stateful_generic_lib",
                "--target-dir",
                "/tmp/anneal_ws_target_charon_v3",
            ],
            WS_DIR,
            {},
            ["artifacts/stateful_generic_lib.ullbc"],
        )
    )
    records.append(
        run_timed(
            "charon_cargo_client_direct_mir_inspector_ullbc",
            [
                CHARON,
                "cargo",
                "--ullbc",
                "--mir",
                "elaborated",
                "--rustc-arg=-Zmir-preserve-ub",
                "--dest-file",
                os.path.join(ART_DIR, "client_direct_mir_inspector.ullbc"),
                "--",
                "--package",
                "client_direct_mir_inspector",
                "--target-dir",
                "/tmp/anneal_ws_target_charon_v3",
            ],
            WS_DIR,
            {},
            ["artifacts/client_direct_mir_inspector.ullbc"],
        )
    )

    dep_def_hdr = parse_amir_v3_summary(os.path.join(ART_DIR, "dep_default.amir"))
    dep_str_hdr = parse_amir_v3_summary(os.path.join(ART_DIR, "dep_strict.amir"))
    app_def_hdr = parse_amir_v3_summary(os.path.join(ART_DIR, "app_default.amir"))
    app_str_hdr = parse_amir_v3_summary(os.path.join(ART_DIR, "app_strict.amir"))

    feature_toggle_diff = {
        "dep_default": dep_def_hdr,
        "dep_strict": dep_str_hdr,
        "app_default": app_def_hdr,
        "app_strict": app_str_hdr,
        "dep_bytes_distinct": dep_def_hdr["sha256"] != dep_str_hdr["sha256"],
        "app_bytes_distinct": app_def_hdr["sha256"] != app_str_hdr["sha256"],
        "dep_fp16_distinct": dep_def_hdr["fp16"] != dep_str_hdr["fp16"],
        "app_fp16_distinct": app_def_hdr["fp16"] != app_str_hdr["fp16"],
    }

    ledger = {
        "wire_format": "AMIR_v3",
        "driver_binary": DRIVER_BIN,
        "driver_source": DRIVER_SRC,
        "driver_source_sha256": sha256_file(DRIVER_SRC),
        "pinned_rustc_sha256": sha256_file(RUSTC),
        "pinned_cargo_sha256": sha256_file(CARGO),
        "pinned_charon_sha256": sha256_file(CHARON),
        "feature_toggle_amir_v3_comparison": feature_toggle_diff,
        "runs": records,
    }

    out_ledger = os.path.join(BASE_DIR, "workspace-capture-ledger.json")
    with open(out_ledger, "w") as f:
        json.dump(ledger, f, indent=2)
        f.write("\n")
    print("Wrote", out_ledger, "sha256:", sha256_file(out_ledger))


if __name__ == "__main__":
    main()
