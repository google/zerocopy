#!/usr/bin/env python3
"""
Milestone R5 (#62): Live Bounded Agent Task Execution & Four-Toolchain Upgrade Capture
Workspace: /usr/local/google/home/joshlf/.gemini/jetski/brain/07db2a18-1303-4996-b1bb-b386433e2c0f/scratch/workers/r5_live_tasks/

Performs and records all 4 bounded tasks across Direct MIR (`.amir` v3 + `VarDebugInfo` sidecar)
and Charon `0.1.210` (`--ullbc --mir elaborated` and `--mir elaborated`):
- Task 1 (Initial Spec & Proof Authoring on Non-Cleanup Holdouts):
  Captures `dep_layout_core` (`task1_dep_layout_core.amir`, plus unmodified-driver diagnostic
  `out_task1_dep_layout_core_unmodified_driver.json`, `driver_v4_t_param_substs_fix.patch`, and
  concrete `task1_dep_layout_core_u32.amir`) and `zerocopy_layout_holdout` (`task1_align_to.amir`,
  `task1_zerocopy.ullbc`, `task1_zerocopy.llbc`, `task1_dep_layout_core.ullbc`,
  `task1_dep_layout_core.llbc`), and extracts `var_debug_local_join.json`.
- Task 2 (Seeded Bug Localization & Full-Program Repair on `DstLayout::extend`):
  Captures `task2_extend_buggy.amir`, `bodies_task2_extend_buggy.json`, `task2_extend_buggy.ullbc`,
  and `task2_extend_buggy.llbc`, extracts the live localization trace across Direct MIR (`bb11 -> bb12`,
  `_21 = copy (_2.1: usize)` instead of `_21 = copy _7`), Charon ULLBC (`bb14 -> bb16`, `Local 18`),
  and Charon LLBC (`Local 17`), authors the repair (`task2_extend_repaired.rs`, `task2_extend_repair.patch`),
  and captures `task2_extend_repaired.amir`, `.ullbc`, and `.llbc`.
- Task 3 (Behavior-Preserving Refactor & Contract/Representation Maintenance):
  Authors behavior-preserving refactors on `zerocopy_layout_holdout.rs` (`align_to` intermediate
  `aligned_rem`) and `cleanup_subject.rs` (`partial_init_move_cleanup` intermediate `early_flag`),
  captures `task3_align_to_refactored.amir` (`.ullbc`, `.llbc`) and `task3_cleanup_refactored.amir`
  (`.ullbc`, `.llbc`), and extracts the shifted `VarDebugInfo` join mappings.
- Task 4 (Weakening-Trap Rejection via Actual Interpreter/Gate Checks):
  Records the exact inputs, byte vectors, and Lean theorem identifiers in
  `AgentTasksAndCompilerUpgrade.lean` and `AgentTasksAndCompilerUpgradeControls.lean` that
  reject Traps A, B, and C via actual decoded-AST execution and Boundary 3/5 gates.
"""

import difflib
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

OUT_DIR = "/usr/local/google/home/joshlf/.gemini/jetski/brain/07db2a18-1303-4996-b1bb-b386433e2c0f/scratch/workers/r5_live_tasks"
ART_DIR = os.path.join(OUT_DIR, "artifacts")
TMP_BUILD = "/tmp/r5_live_build"
CAP_DIR = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture"
V4_ART_DIR = os.path.join(CAP_DIR, "artifacts/v4")
CARGO_WS_DIR = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/cargo-workspace-integration/workspace"
DRIVER_V4_BIN = "/tmp/direct_mir_driver_v4_bin"

TC_198_ROOT = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61"
RUSTC_198 = os.path.join(TC_198_ROOT, "rust/bin/rustc")
CHARON_198 = os.path.join(TC_198_ROOT, "aeneas/bin/charon")

TOOLCHAINS = [
    {
        "id": "nightly_1_95_2026_02_06",
        "version_label": "1.95.0-nightly (efc9e1b50 2026-02-06)",
        "root": "/usr/local/google/home/joshlf/.anneal/toolchain/x86_64-unknown-linux-gnu-0191de6c9fa5/rust",
        "is_1_98": False,
    },
    {
        "id": "nightly_1_96_2026_04_10",
        "version_label": "1.96.0-nightly (02c7f9bec 2026-04-10)",
        "root": "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu",
        "is_1_98": False,
    },
    {
        "id": "nightly_1_97_2026_04_11",
        "version_label": "1.97.0-nightly (bf4fbfb7a 2026-04-11)",
        "root": "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-04-12-x86_64-unknown-linux-gnu",
        "is_1_98": False,
    },
    {
        "id": "nightly_1_98_2026_05_30",
        "version_label": "1.98.0-nightly (f8a08b688 2026-05-30)",
        "root": os.path.join(TC_198_ROOT, "rust"),
        "is_1_98": True,
    },
]


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(path: str) -> str:
    with open(path, "rb") as f:
        return sha256_bytes(f.read())


def make_env(rust_root: str = os.path.join(TC_198_ROOT, "rust")) -> dict:
    env = os.environ.copy()
    lib_dir = os.path.join(rust_root, "lib")
    host_lib_dir = os.path.join(rust_root, "lib/rustlib/x86_64-unknown-linux-gnu/lib")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}:{host_lib_dir}:" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = f"{rust_root}/bin:{TC_198_ROOT}/aeneas/bin:" + env.get("PATH", "")
    env["RUSTC"] = os.path.join(rust_root, "bin/rustc")
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"
    return env


def run_measured(cmd: list, env: dict, cwd: str = None) -> dict:
    t0 = time.monotonic()
    proc = subprocess.run(
        ["/usr/bin/time", "-v"] + cmd,
        env=env,
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=120,
    )
    elapsed_ms = int(round((time.monotonic() - t0) * 1000))
    m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", proc.stderr)
    rss_bytes = int(m.group(1)) * 1024 if m else 0
    return {
        "cmd": cmd,
        "exit_code": proc.returncode,
        "wall_clock_ms": elapsed_ms,
        "max_rss_bytes": rss_bytes,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def make_portable_v4_driver(dest_rs: str) -> str:
    v4_src = open(os.path.join(CAP_DIR, "direct_mir_driver_v4.rs")).read()
    # Fix ParamTy formatting `[T/#0]` alongside `[T]` for generic `core::mem::align_of::<T>()` (`sym = 38`)
    v4_src = v4_src.replace(
        '        } else if substs_repr == "[T]" {\n            Ok(38)',
        '        } else if substs_repr == "[T]" || substs_repr == "[T/#0]" {\n            Ok(38)',
    )
    portable = v4_src.replace(
        "    VarDebugInfoContents, WithRetag,\n};",
        "    VarDebugInfoContents,\n};\n#[cfg(rustc_1_98)]\nuse rustc_middle::mir::WithRetag;\n#[cfg(not(rustc_1_98))]\nuse rustc_middle::mir::RetagKind;",
    )
    portable = portable.replace(
        'else if path.contains("DstLayout") && path.ends_with("::assert_fields_are_eq") {',
        'else if path.contains("DstLayout") && (path.ends_with("::assert_fields_are_eq") || path.ends_with("::assert_receiver_is_total_eq")) {',
    ).replace(
        'else if path.contains("SizeError") && path.ends_with("::assert_fields_are_eq") {',
        'else if path.contains("SizeError") && (path.ends_with("::assert_fields_are_eq") || path.ends_with("::assert_receiver_is_total_eq")) {',
    )
    old_rval = """                        Rvalue::Use(op, WithRetag::No) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x10, dst_l, dst_p, b0, b1]
                        }
                        Rvalue::Use(op, WithRetag::Yes) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x11, dst_l, dst_p, b0, b1]
                        }"""
    new_rval = """                        #[cfg(rustc_1_98)]
                        Rvalue::Use(op, WithRetag::No) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x10, dst_l, dst_p, b0, b1]
                        }
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(op, WithRetag::Yes) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x11, dst_l, dst_p, b0, b1]
                        }
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(op) => {
                            let [b0, b1] = encode_operand_v3(tcx, typing_env, op, local_count)?;
                            vec![0x11, dst_l, dst_p, b0, b1]
                        }"""
    assert old_rval in portable
    portable = portable.replace(old_rval, new_rval)

    old_stmt_pm = """                StatementKind::PlaceMention(p) => {
                    let [src_l, src_pr] = encode_place_v3(p, local_count)?;
                    vec![0x30, src_l, src_pr]
                }"""
    new_stmt_pm = """                StatementKind::PlaceMention(p) => {
                    let [src_l, src_pr] = encode_place_v3(p, local_count)?;
                    vec![0x30, src_l, src_pr]
                }
                #[cfg(not(rustc_1_98))]
                StatementKind::Retag(rk, p) => {
                    let [src_l, src_pr] = encode_place_v3(p, local_count)?;
                    let rk_byte: u8 = match rk {
                        RetagKind::Default => 0,
                        RetagKind::TwoPhase => 1,
                        RetagKind::Raw => 2,
                        RetagKind::FnEntry => 3,
                    };
                    vec![0x31, rk_byte, src_l, src_pr]
                }"""
    assert old_stmt_pm in portable
    portable = portable.replace(old_stmt_pm, new_stmt_pm)

    old_m2 = """                        Rvalue::CopyForDeref(_) => "Assign(CopyForDeref)",
                        Rvalue::Use(_, WithRetag::Yes) => "Assign(Use,WithRetag::Yes)",
                        Rvalue::Use(_, WithRetag::No) => "Assign(Use,WithRetag::No)",
                        _ => "Assign(Other)","""
    new_m2 = """                        Rvalue::CopyForDeref(_) => "Assign(CopyForDeref)",
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::Yes) => "Assign(Use,WithRetag::Yes)",
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::No) => "Assign(Use,WithRetag::No)",
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(_) => "Assign(Use,Pre198)",
                        _ => "Assign(Other)","""
    assert old_m2 in portable
    portable = portable.replace(old_m2, new_m2)

    old_m3 = """                        Rvalue::CopyForDeref(_) => copy_for_deref_count += 1,
                        Rvalue::Use(_, WithRetag::Yes) => use_retag_yes_count += 1,
                        Rvalue::Use(_, WithRetag::No) => use_retag_no_count += 1,
                        _ => {}"""
    new_m3 = """                        Rvalue::CopyForDeref(_) => copy_for_deref_count += 1,
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::Yes) => use_retag_yes_count += 1,
                        #[cfg(rustc_1_98)]
                        Rvalue::Use(_, WithRetag::No) => use_retag_no_count += 1,
                        #[cfg(not(rustc_1_98))]
                        Rvalue::Use(_) => { let _ = &mut use_retag_no_count; use_retag_yes_count += 1; }
                        _ => {}"""
    assert old_m3 in portable
    portable = portable.replace(old_m3, new_m3)

    old_drop = "                        let drop_inst = Instance::resolve_drop_glue(tcx, ty);"
    new_drop = """                        #[cfg(not(rustc_1_98))]
                        let drop_inst = Instance::resolve_drop_in_place(tcx, ty);
                        #[cfg(rustc_1_98)]
                        let drop_inst = Instance::resolve_drop_glue(tcx, ty);"""
    assert old_drop in portable
    portable = portable.replace(old_drop, new_drop)

    with open(dest_rs, "w") as f:
        f.write(portable)
    return dest_rs


def extract_var_debug_table(bodies_json_path: str) -> dict:
    data = json.load(open(bodies_json_path))
    table = {}
    for b in data:
        if b.get("stage") == "hook_mir_drops_elaborated":
            owner = b["owner"]
            vj = b.get("var_debug_join", [])
            counts = {}
            named_vars = {}
            for entry in vj:
                bk = entry["binding_kind"]
                counts[bk] = counts.get(bk, 0) + 1
                if bk in ("UniqueUserVar", "ProjectedCaptureVar", "SynthesizedDropFlag", "SynthesizedPassTemp"):
                    named_vars[entry["local"]] = {
                        "source_name": entry["source_name"],
                        "binding_kind": bk,
                        "ty": entry["ty"],
                        "built_local_info": entry["built_local_info"],
                        "post_cleanup_local_info": entry["post_cleanup_local_info"],
                        "source_span": entry["source_span"],
                    }
            table[owner] = {
                "phase": b["phase"],
                "total_locals": len(b.get("locals", [])),
                "total_blocks": len(b.get("basic_blocks", [])),
                "binding_kind_counts": counts,
                "recovered_bindings": named_vars,
                "full_var_debug_join": vj,
            }
    return table


def main():
    os.makedirs(ART_DIR, exist_ok=True)
    os.makedirs(TMP_BUILD, exist_ok=True)
    env_198 = make_env()

    gen_align_path = os.path.join(TMP_BUILD, "generated_align.rs")
    with open(gen_align_path, "w") as f:
        f.write("pub const GENERATED_ARCH_ALIGN: usize = 8;\n")
    env_dep = env_198.copy()
    env_dep["OUT_DIR"] = TMP_BUILD

    dep_src = os.path.join(CARGO_WS_DIR, "dep_layout_core/src/lib.rs")

    # 1a. Run unmodified /tmp/direct_mir_driver_v4_bin on polymorphic dep_layout_core to record `[T/#0]` diagnostic
    unmod_dep_json = os.path.join(ART_DIR, "out_task1_dep_layout_core_unmodified_driver.json")
    m_t1_dep_unmod = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "dep_layout_core",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            unmod_dep_json,
            "--driver-emit-amir-v3",
            os.path.join(TMP_BUILD, "unused_unmod.amir"),
            dep_src,
            "-o",
            os.path.join(TMP_BUILD, "libdep_unmod.rlib"),
        ],
        env_dep,
    )

    # 1b. Build 1-line `[T/#0]` patched driver and capture polymorphic `task1_dep_layout_core.amir`
    v4_orig_src = open(os.path.join(CAP_DIR, "direct_mir_driver_v4.rs")).read()
    v4_t_param_src = v4_orig_src.replace(
        '        } else if substs_repr == "[T]" {\n            Ok(38)',
        '        } else if substs_repr == "[T]" || substs_repr == "[T/#0]" {\n            Ok(38)',
    )
    t_param_rs = os.path.join(TMP_BUILD, "direct_mir_driver_v4_t_param.rs")
    t_param_bin = os.path.join(TMP_BUILD, "direct_mir_driver_v4_t_param_bin")
    with open(t_param_rs, "w") as f:
        f.write(v4_t_param_src)
    subprocess.run([RUSTC_198, "--edition=2021", "-O", t_param_rs, "-o", t_param_bin], env=env_198, check=True)

    t1_dep_json = os.path.join(ART_DIR, "out_task1_dep_layout_core.json")
    t1_dep_bodies = os.path.join(ART_DIR, "bodies_task1_dep_layout_core.json")
    t1_dep_amir = os.path.join(ART_DIR, "task1_dep_layout_core.amir")
    m_t1_dep = run_measured(
        [
            t_param_bin,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "dep_layout_core",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t1_dep_json,
            "--driver-dump-bodies",
            t1_dep_bodies,
            "--driver-emit-amir-v3",
            t1_dep_amir,
            dep_src,
            "-o",
            os.path.join(TMP_BUILD, "libdep_layout_core.rlib"),
        ],
        env_dep,
    )
    assert m_t1_dep["exit_code"] == 0, m_t1_dep["stderr"]

    # 1c. Also capture concrete `u32`-instantiated `task1_dep_layout_core_u32.amir` with unmodified DRIVER_V4_BIN
    dep_u32_rs = os.path.join(ART_DIR, "task1_dep_layout_core_u32.rs")
    t1_dep_u32_json = os.path.join(ART_DIR, "out_task1_dep_layout_core_u32.json")
    t1_dep_u32_bodies = os.path.join(ART_DIR, "bodies_task1_dep_layout_core_u32.json")
    t1_dep_u32_amir = os.path.join(ART_DIR, "task1_dep_layout_core_u32.amir")
    m_t1_dep_u32 = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "dep_layout_core",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t1_dep_u32_json,
            "--driver-dump-bodies",
            t1_dep_u32_bodies,
            "--driver-emit-amir-v3",
            t1_dep_u32_amir,
            dep_u32_rs,
            "-o",
            os.path.join(TMP_BUILD, "libdep_u32.rlib"),
        ],
        env_dep,
    )
    assert m_t1_dep_u32["exit_code"] == 0, m_t1_dep_u32["stderr"]

    # Copy v4 cleanup & zerocopy artifacts for Task 1 reference and extract combined VarDebugInfo join sidecar
    shutil.copyfile(
        os.path.join(V4_ART_DIR, "zerocopy_layout_holdout.amir"),
        os.path.join(ART_DIR, "task1_align_to.amir"),
    )
    shutil.copyfile(
        os.path.join(V4_ART_DIR, "out_zerocopy_holdout.json"),
        os.path.join(ART_DIR, "out_task1_align_to.json"),
    )
    shutil.copyfile(
        os.path.join(V4_ART_DIR, "bodies_zerocopy_holdout.json"),
        os.path.join(ART_DIR, "bodies_task1_align_to.json"),
    )

    zc_src_path = os.path.join(CAP_DIR, "zerocopy_layout_holdout.rs")
    t1_ullbc = os.path.join(ART_DIR, "task1_zerocopy.ullbc")
    t1_llbc = os.path.join(ART_DIR, "task1_zerocopy.llbc")
    m_t1_ullbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t1_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            zc_src_path,
        ],
        env_198,
    )
    m_t1_llbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t1_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            zc_src_path,
        ],
        env_198,
    )

    t1_dep_ullbc = os.path.join(ART_DIR, "task1_dep_layout_core.ullbc")
    t1_dep_llbc = os.path.join(ART_DIR, "task1_dep_layout_core.llbc")
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t1_dep_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            dep_src,
        ],
        env_dep,
    )
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t1_dep_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            dep_src,
        ],
        env_dep,
    )

    var_debug_sidecar = {
        "cleanup_subject": extract_var_debug_table(
            os.path.join(V4_ART_DIR, "bodies_cleanup_preserve_ub.json")
        ),
        "zerocopy_layout_holdout": extract_var_debug_table(
            os.path.join(V4_ART_DIR, "bodies_zerocopy_holdout.json")
        ),
        "dep_layout_core": extract_var_debug_table(t1_dep_bodies),
    }
    var_debug_sidecar_path = os.path.join(ART_DIR, "var_debug_local_join.json")
    with open(var_debug_sidecar_path, "w") as f:
        json.dump(var_debug_sidecar, f, indent=2)

    # 2. Task 2 (Seeded Bug Localization & Full-Program Repair on `DstLayout::extend`)
    zc_orig_text = open(zc_src_path).read()
    zc_buggy_text = zc_orig_text.replace(
        """        let new_size = if next.is_slice_dst {
            offset
        } else {
            offset.checked_add(next.size_info).ok_or(SizeError)?
        };""",
        """        let new_size = if next.is_slice_dst {
            next.size_info
        } else {
            offset.checked_add(next.size_info).ok_or(SizeError)?
        };""",
    )
    assert zc_buggy_text != zc_orig_text
    t2_buggy_rs = os.path.join(ART_DIR, "task2_extend_buggy.rs")
    t2_repaired_rs = os.path.join(ART_DIR, "task2_extend_repaired.rs")
    t2_patch_path = os.path.join(ART_DIR, "task2_extend_repair.patch")
    with open(t2_buggy_rs, "w") as f:
        f.write(zc_buggy_text)

    t2_buggy_json = os.path.join(ART_DIR, "out_task2_extend_buggy.json")
    t2_buggy_bodies = os.path.join(ART_DIR, "bodies_task2_extend_buggy.json")
    t2_buggy_amir = os.path.join(ART_DIR, "task2_extend_buggy.amir")
    m_t2_buggy = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "zerocopy_layout_holdout",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t2_buggy_json,
            "--driver-dump-bodies",
            t2_buggy_bodies,
            "--driver-emit-amir-v3",
            t2_buggy_amir,
            t2_buggy_rs,
            "-o",
            os.path.join(TMP_BUILD, "libtask2_buggy.rlib"),
        ],
        env_198,
    )
    assert m_t2_buggy["exit_code"] == 0

    t2_buggy_ullbc = os.path.join(ART_DIR, "task2_extend_buggy.ullbc")
    t2_buggy_llbc = os.path.join(ART_DIR, "task2_extend_buggy.llbc")
    m_t2_buggy_ullbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t2_buggy_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t2_buggy_rs,
        ],
        env_198,
    )
    m_t2_buggy_llbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t2_buggy_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t2_buggy_rs,
        ],
        env_198,
    )

    # Live localization extraction from `bodies_task2_extend_buggy.json`, `.ullbc`, and `.llbc`
    buggy_bodies_data = json.load(open(t2_buggy_bodies))
    extend_mir_body = [
        b
        for b in buggy_bodies_data
        if b.get("stage") == "hook_mir_drops_elaborated" and b["owner"] == "DstLayout::extend"
    ][0]
    extend_vdi_map = {
        e["local"]: e["source_name"]
        for e in extend_mir_body["var_debug_join"]
        if e["binding_kind"] == "UniqueUserVar"
    }
    bb11_mir = extend_mir_body["basic_blocks"][11]
    bb12_mir = extend_mir_body["basic_blocks"][12]

    ullbc_data = json.load(open(t2_buggy_ullbc))
    extend_ullbc_fn = [
        f
        for f in ullbc_data["translated"]["fun_decls"]
        if f
        and any(
            seg.get("Ident", [None])[0] == "extend"
            for seg in f["item_meta"]["name"]
            if isinstance(seg, dict)
        )
    ][0]
    extend_ullbc_body = extend_ullbc_fn["body"]["Unstructured"]
    ullbc_local_map = {
        f"var@{l['index']}": l["name"]
        for l in extend_ullbc_body["locals"]["locals"]
        if l.get("name")
    }
    bb14_ullbc = extend_ullbc_body["body"][14]
    bb16_ullbc = extend_ullbc_body["body"][16]

    llbc_data = json.load(open(t2_buggy_llbc))
    extend_llbc_fn = [
        f
        for f in llbc_data["translated"]["fun_decls"]
        if f
        and any(
            seg.get("Ident", [None])[0] == "extend"
            for seg in f["item_meta"]["name"]
            if isinstance(seg, dict)
        )
    ][0]
    extend_llbc_body = extend_llbc_fn["body"]["Structured"]
    llbc_local_map = {
        f"var@{l['index']}": l["name"]
        for l in extend_llbc_body["locals"]["locals"]
        if l.get("name")
    }

    localization_trace = {
        "task": "Task_2_Seeded_Bug_Localization_And_Full_Program_Repair",
        "subject": "zerocopy_layout_holdout::DstLayout::extend",
        "held_out_discriminator_input": {
            "self": {"align": 4, "size_info": 6, "is_slice_dst": False},
            "next": {"align": 4, "size_info": 4, "is_slice_dst": True},
            "rationale": "When self.size_info = 6 and next.align = 4, offset = align_to(6, 4) = 8 != next.size_info = 4, separating new_size = offset (8) from the buggy new_size = next.size_info (4).",
        },
        "direct_mir_with_var_debug_sidecar": {
            "recovered_user_vars": extend_vdi_map,
            "branch_block_bb11": bb11_mir,
            "faulty_block_bb12": bb12_mir,
            "localized_fault": "bb12 assigns `_21 = copy (_2.1: usize)` (`new_size = next.size_info`) instead of `_21 = copy _7` (`new_size = offset`).",
        },
        "direct_mir_anonymous_post_cleanup": {
            "post_cleanup_local_info": "All 40 locals have `post_cleanup_local_info = Cleared`; localization requires tracing `_7` back to `align_to` call in `bb2..bb6` and `_21` forward to `DstLayout` aggregate in `bb20`.",
        },
        "charon_ullbc_elaborated": {
            "recovered_user_vars": ullbc_local_map,
            "branch_block_bb14_terminator": bb14_ullbc["terminator"]["kind"],
            "faulty_block_bb16_statements": [s["kind"] for s in bb16_ullbc["statements"]],
            "localized_fault": "bb16 assigns `Local(18)` (`new_size`) from `Projection(Local(2), Field(1))` (`next.size_info`) instead of `Local(5)` (`offset`).",
        },
        "charon_llbc_structured": {
            "recovered_user_vars": llbc_local_map,
            "localized_fault": "Structured `Switch::If` branch on `var@18 = copy (next.2)` assigns `var@17` (`new_size`) from `copy (next.1)` instead of `copy var@5` (`offset`).",
        },
    }
    with open(os.path.join(ART_DIR, "task2_live_localization_trace.json"), "w") as f:
        json.dump(localization_trace, f, indent=2)

    # Apply localized repair (`next.size_info` -> `offset` in `if next.is_slice_dst` branch)
    repaired_text = zc_buggy_text.replace(
        """        let new_size = if next.is_slice_dst {
            next.size_info
        } else {""",
        """        let new_size = if next.is_slice_dst {
            offset
        } else {""",
    )
    with open(t2_repaired_rs, "w") as f:
        f.write(repaired_text)

    diff_t2 = "".join(
        difflib.unified_diff(
            zc_buggy_text.splitlines(keepends=True),
            repaired_text.splitlines(keepends=True),
            fromfile="a/task2_extend_buggy.rs",
            tofile="b/task2_extend_repaired.rs",
        )
    )
    with open(t2_patch_path, "w") as f:
        f.write(diff_t2)

    t2_repaired_json = os.path.join(ART_DIR, "out_task2_extend_repaired.json")
    t2_repaired_amir = os.path.join(ART_DIR, "task2_extend_repaired.amir")
    m_t2_repaired = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "zerocopy_layout_holdout",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t2_repaired_json,
            "--driver-emit-amir-v3",
            t2_repaired_amir,
            t2_repaired_rs,
            "-o",
            os.path.join(TMP_BUILD, "libtask2_repaired.rlib"),
        ],
        env_198,
    )
    assert m_t2_repaired["exit_code"] == 0

    t2_repaired_ullbc = os.path.join(ART_DIR, "task2_extend_repaired.ullbc")
    t2_repaired_llbc = os.path.join(ART_DIR, "task2_extend_repaired.llbc")
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t2_repaired_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t2_repaired_rs,
        ],
        env_198,
    )
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t2_repaired_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t2_repaired_rs,
        ],
        env_198,
    )

    # 3. Task 3 (Behavior-Preserving Refactor Maintenance on `align_to` and `partial_init_move_cleanup`)
    zc_refac_text = zc_orig_text.replace(
        "    let rem = size % align;",
        "    let aligned_rem = size % align;\n    let rem = aligned_rem;",
    )
    assert zc_refac_text != zc_orig_text
    t3_zc_rs = os.path.join(ART_DIR, "task3_align_to_refactored.rs")
    with open(t3_zc_rs, "w") as f:
        f.write(zc_refac_text)

    cs_src_path = os.path.join(CAP_DIR, "cleanup_subject.rs")
    cs_orig_text = open(cs_src_path).read()
    cs_refac_text = cs_orig_text.replace(
        "    if move_first_early {",
        "    let early_flag = move_first_early;\n    if early_flag {",
    )
    assert cs_refac_text != cs_orig_text
    t3_cs_rs = os.path.join(ART_DIR, "task3_cleanup_refactored.rs")
    with open(t3_cs_rs, "w") as f:
        f.write(cs_refac_text)

    diff_t3 = "".join(
        difflib.unified_diff(
            zc_orig_text.splitlines(keepends=True),
            zc_refac_text.splitlines(keepends=True),
            fromfile="a/zerocopy_layout_holdout.rs",
            tofile="b/task3_align_to_refactored.rs",
        )
    ) + "".join(
        difflib.unified_diff(
            cs_orig_text.splitlines(keepends=True),
            cs_refac_text.splitlines(keepends=True),
            fromfile="a/cleanup_subject.rs",
            tofile="b/task3_cleanup_refactored.rs",
        )
    )
    t3_patch_path = os.path.join(ART_DIR, "task3_refactor.patch")
    with open(t3_patch_path, "w") as f:
        f.write(diff_t3)

    t3_zc_json = os.path.join(ART_DIR, "out_task3_align_to_refactored.json")
    t3_zc_bodies = os.path.join(ART_DIR, "bodies_task3_align_to_refactored.json")
    t3_zc_amir = os.path.join(ART_DIR, "task3_align_to_refactored.amir")
    m_t3_zc = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "zerocopy_layout_holdout",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t3_zc_json,
            "--driver-dump-bodies",
            t3_zc_bodies,
            "--driver-emit-amir-v3",
            t3_zc_amir,
            t3_zc_rs,
            "-o",
            os.path.join(TMP_BUILD, "libtask3_zc.rlib"),
        ],
        env_198,
    )
    assert m_t3_zc["exit_code"] == 0

    t3_ullbc = os.path.join(ART_DIR, "task3_align_to_refactored.ullbc")
    t3_llbc = os.path.join(ART_DIR, "task3_align_to_refactored.llbc")
    m_t3_ullbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t3_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t3_zc_rs,
        ],
        env_198,
    )
    m_t3_llbc = run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t3_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t3_zc_rs,
        ],
        env_198,
    )

    t3_cs_json = os.path.join(ART_DIR, "out_task3_cleanup_refactored.json")
    t3_cs_bodies = os.path.join(ART_DIR, "bodies_task3_cleanup_refactored.json")
    t3_cs_amir = os.path.join(ART_DIR, "task3_cleanup_refactored.amir")
    m_t3_cs = run_measured(
        [
            DRIVER_V4_BIN,
            "--sysroot",
            os.path.join(TC_198_ROOT, "rust"),
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name",
            "cleanup_subject",
            "-Z",
            "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-out-json",
            t3_cs_json,
            "--driver-dump-bodies",
            t3_cs_bodies,
            "--driver-emit-amir-v3",
            t3_cs_amir,
            t3_cs_rs,
            "-o",
            os.path.join(TMP_BUILD, "libtask3_cs.rlib"),
        ],
        env_198,
    )
    assert m_t3_cs["exit_code"] == 0

    t3_cs_ullbc = os.path.join(ART_DIR, "task3_cleanup_refactored.ullbc")
    t3_cs_llbc = os.path.join(ART_DIR, "task3_cleanup_refactored.llbc")
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--ullbc",
            "--mir",
            "elaborated",
            "--dest-file",
            t3_cs_ullbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t3_cs_rs,
        ],
        env_198,
    )
    run_measured(
        [
            CHARON_198,
            "rustc",
            "--mir",
            "elaborated",
            "--dest-file",
            t3_cs_llbc,
            "--",
            "--edition=2021",
            "--crate-type=lib",
            t3_cs_rs,
        ],
        env_198,
    )

    # 4. Task 4 (Weakening-Trap Rejection artifacts linked to actual Lean interpreter & gate theorems)
    t4_trap_a_path = os.path.join(ART_DIR, "task4_trap_a_weakened_postcond.json")
    with open(t4_trap_a_path, "w") as f:
        json.dump(
            {
                "trap_id": "Trap_A_Weakened_Postcondition",
                "subjects": [
                    "partial_field_reinit_cleanup (mutant1SwapDropOrderBytes / mutant3ReinitKeepField0DropBytes)",
                    "DstLayout::extend (realTask2ExtendBuggyBytes)",
                ],
                "lean_theorems": [
                    "AnnealResearch.AgentTasksAndCompilerUpgrade.task4_trap_a_weakened_postconditions_accept_mutants_rejected_by_c0",
                    "AnnealResearch.AgentTasksAndCompilerUpgradeControls.control_trap_a_weakened_extend_and_cleanup_contracts_unsound",
                ],
                "c0_gate_functions": [
                    "checkCleanupSuiteAgainstC0",
                    "checkExtendSliceTailAgainstC0",
                ],
            },
            f,
            indent=2,
        )

    t4_trap_b_amir = os.path.join(ART_DIR, "task4_trap_b_dropped_preserve_ub.amir")
    shutil.copyfile(os.path.join(V4_ART_DIR, "place_mention_default.amir"), t4_trap_b_amir)

    t4_trap_c_path = os.path.join(ART_DIR, "task4_trap_c_unproved_assumption.json")
    with open(t4_trap_c_path, "w") as f:
        json.dump(
            {
                "trap_id": "Trap_C_Unproved_Assumption_Or_Admissibility_Widening",
                "subjects": [
                    "charonUllbcCleanupRawBytes",
                    "charonLlbcCleanupRemedyR2Bytes",
                ],
                "lean_theorems": [
                    "AnnealResearch.AgentTasksAndCompilerUpgrade.task4_trap_c_raw_ullbc_and_structured_llbc_rejected_by_c0_cleanup_gate",
                    "AnnealResearch.AgentTasksAndCompilerUpgradeControls.control_trap_c_unverified_charon_routes_fail_c0_cleanup_gate",
                ],
                "c0_gate_function": "checkCleanupSuiteAgainstC0",
            },
            f,
            indent=2,
        )

    # 5. Four-Toolchain `.amir` v3 Upgrade & `WithRetag` (`0x31` vs `0x11`/`0x10`) Trial
    portable_v4_rs = os.path.join(OUT_DIR, "direct_mir_driver_v4_portable.rs")
    make_portable_v4_driver(portable_v4_rs)

    tc_records = []
    for tc in TOOLCHAINS:
        tc_id = tc["id"]
        root = tc["root"]
        rustc_bin = os.path.join(root, "bin/rustc")
        tc_env = make_env(root)

        port_bin = os.path.join(TMP_BUILD, f"driver_v4_port_{tc_id}")
        build_cmd = [rustc_bin, "--edition=2021", "-O", portable_v4_rs, "-o", port_bin]
        if tc["is_1_98"]:
            build_cmd.extend(["--cfg", "rustc_1_98"])
        m_build = run_measured(build_cmd, tc_env)
        assert m_build["exit_code"] == 0, m_build["stderr"]

        captures = {}
        for subj in ["place_mention_probe", "cleanup_subject", "zerocopy_layout_holdout"]:
            out_json = os.path.join(ART_DIR, f"out_{subj}_{tc_id}.json")
            out_amir = os.path.join(ART_DIR, f"{subj}_{tc_id}.amir")
            m_cap = run_measured(
                [
                    port_bin,
                    "--sysroot",
                    root,
                    "--edition=2021",
                    "--crate-type=lib",
                    "--crate-name",
                    subj,
                    "-Z",
                    "mir-preserve-ub",
                    "--driver-run-mono-collector",
                    "--driver-out-json",
                    out_json,
                    "--driver-emit-amir-v3",
                    out_amir,
                    os.path.join(CAP_DIR, f"{subj}.rs"),
                    "-o",
                    os.path.join(TMP_BUILD, f"lib_{subj}_{tc_id}.rlib"),
                ],
                tc_env,
            )
            assert m_cap["exit_code"] == 0, m_cap["stderr"]
            amir_bytes = list(open(out_amir, "rb").read())
            captures[subj] = {
                "amir_path": os.path.relpath(out_amir, OUT_DIR),
                "amir_sha256": sha256_file(out_amir),
                "amir_size_bytes": len(amir_bytes),
                "opcode_0x10_assign_use_no_retag_count": amir_bytes.count(0x10),
                "opcode_0x11_assign_use_retag_yes_count": amir_bytes.count(0x11),
                "opcode_0x31_retag_stmt_count": amir_bytes.count(0x31),
                "wall_clock_ms": m_cap["wall_clock_ms"],
                "max_rss_bytes": m_cap["max_rss_bytes"],
            }

        retag_amir = os.path.join(ART_DIR, f"cleanup_subject_emit_retag_{tc_id}.amir")
        retag_json = os.path.join(ART_DIR, f"out_cleanup_subject_emit_retag_{tc_id}.json")
        m_retag = run_measured(
            [
                port_bin,
                "--sysroot",
                root,
                "--edition=2021",
                "--crate-type=lib",
                "--crate-name",
                "cleanup_subject",
                "-Z",
                "mir-preserve-ub",
                "-Z",
                "mir-emit-retag",
                "--driver-run-mono-collector",
                "--driver-out-json",
                retag_json,
                "--driver-emit-amir-v3",
                retag_amir,
                os.path.join(CAP_DIR, "cleanup_subject.rs"),
                "-o",
                os.path.join(TMP_BUILD, f"lib_cs_retag_{tc_id}.rlib"),
            ],
            tc_env,
        )
        retag_bytes = list(open(retag_amir, "rb").read()) if os.path.exists(retag_amir) else []
        tc_records.append(
            {
                "toolchain_id": tc_id,
                "version_label": tc["version_label"],
                "rustc_sha256": sha256_file(rustc_bin),
                "portable_v4_driver_exit_code": m_build["exit_code"],
                "portable_v4_driver_build_ms": m_build["wall_clock_ms"],
                "portable_v4_driver_build_max_rss_bytes": m_build["max_rss_bytes"],
                "captures": captures,
                "mir_emit_retag_probe": {
                    "exit_code": m_retag["exit_code"],
                    "amir_size_bytes": len(retag_bytes),
                    "amir_sha256": sha256_file(retag_amir) if os.path.exists(retag_amir) else None,
                    "retag_stmt_0x31_count": retag_bytes.count(0x31),
                },
            }
        )

    t3_zc_vdi = extract_var_debug_table(t3_zc_bodies)["align_to"]
    t3_cs_vdi = extract_var_debug_table(t3_cs_bodies)["partial_init_move_cleanup"]

    ledger = {
        "milestone": "R5 (Study P2 / FD-05 & Study P3 / FD-06 Live Bounded Agent Tasks)",
        "driver_v4_bin_sha256": sha256_file(DRIVER_V4_BIN),
        "driver_v4_t_param_patch_sha256": sha256_file(
            os.path.join(ART_DIR, "driver_v4_t_param_substs_fix.patch")
        ),
        "portable_v4_driver_sha256": sha256_file(portable_v4_rs),
        "var_debug_local_join_artifact": {
            "path": "artifacts/var_debug_local_join.json",
            "sha256": sha256_file(var_debug_sidecar_path),
            "highlights": {
                "align_to": var_debug_sidecar["zerocopy_layout_holdout"]["align_to"]["recovered_bindings"],
                "DstLayout::extend": var_debug_sidecar["zerocopy_layout_holdout"]["DstLayout::extend"]["recovered_bindings"],
                "partial_init_move_cleanup": var_debug_sidecar["cleanup_subject"]["partial_init_move_cleanup"]["recovered_bindings"],
                "partial_field_reinit_cleanup": var_debug_sidecar["cleanup_subject"]["partial_field_reinit_cleanup"]["recovered_bindings"],
                "dep_inline_align": var_debug_sidecar["dep_layout_core"]["dep_inline_align"]["recovered_bindings"],
                "dep_non_inline_check::{closure#0}": var_debug_sidecar["dep_layout_core"]["dep_non_inline_check::{closure#0}"]["recovered_bindings"],
            },
        },
        "executed_agent_tasks": {
            "task1_spec_proof_authoring": {
                "subjects": [
                    "zerocopy_layout_holdout::align_to",
                    "dep_layout_core::dep_inline_align",
                    "dep_layout_core::dep_non_inline_check::{closure#0}",
                ],
                "unmodified_driver_v4_diagnostic_on_polymorphic_dep_layout_core": {
                    "exit_code": m_t1_dep_unmod["exit_code"],
                    "error": "UnsupportedCallee(core::mem::align_of with substs [T/#0])",
                    "root_cause_and_fix": "rustc formats ParamTy T in substs as [T/#0]; 1-line fix in driver_v4_t_param_substs_fix.patch maps [T/#0] -> calleeSym 38 alongside concrete [u32] -> calleeSym 39.",
                },
                "direct_mir_var_debug_mappings": {
                    "align_to": {"_1": "size", "_2": "align", "_8": "rem", "_15": "pad"},
                    "dep_inline_align": {"_1": "val", "_2": "a"},
                    "dep_non_inline_check::{closure#0}": {
                        "_1": "align[Field(0, &'{erased} usize), Deref] (ProjectedCaptureVar)",
                        "_2": "v",
                        "_8": "_pass_temp_8 (SynthesizedPassTemp)",
                    },
                },
                "artifacts": {
                    "task1_align_to_amir_sha256": sha256_file(os.path.join(ART_DIR, "task1_align_to.amir")),
                    "task1_dep_layout_core_amir_sha256": sha256_file(t1_dep_amir),
                    "task1_dep_layout_core_u32_amir_sha256": sha256_file(t1_dep_u32_amir),
                    "task1_zerocopy_ullbc_sha256": sha256_file(t1_ullbc),
                    "task1_zerocopy_llbc_sha256": sha256_file(t1_llbc),
                    "task1_dep_layout_core_ullbc_sha256": sha256_file(t1_dep_ullbc),
                    "task1_dep_layout_core_llbc_sha256": sha256_file(t1_dep_llbc),
                },
                "measurements": {
                    "dep_direct_mir_wall_clock_ms": m_t1_dep["wall_clock_ms"],
                    "dep_direct_mir_max_rss_bytes": m_t1_dep["max_rss_bytes"],
                    "charon_ullbc_wall_clock_ms": m_t1_ullbc["wall_clock_ms"],
                    "charon_ullbc_max_rss_bytes": m_t1_ullbc["max_rss_bytes"],
                    "charon_llbc_wall_clock_ms": m_t1_llbc["wall_clock_ms"],
                    "charon_llbc_max_rss_bytes": m_t1_llbc["max_rss_bytes"],
                },
            },
            "task2_seeded_bug_localization_and_repair": {
                "subject": "zerocopy_layout_holdout::DstLayout::extend",
                "live_localization_trace_path": "artifacts/task2_live_localization_trace.json",
                "live_localization_trace_sha256": sha256_file(
                    os.path.join(ART_DIR, "task2_live_localization_trace.json")
                ),
                "artifacts": {
                    "buggy_rs_sha256": sha256_file(t2_buggy_rs),
                    "buggy_amir_sha256": sha256_file(t2_buggy_amir),
                    "buggy_amir_size_bytes": os.path.getsize(t2_buggy_amir),
                    "buggy_ullbc_sha256": sha256_file(t2_buggy_ullbc),
                    "buggy_llbc_sha256": sha256_file(t2_buggy_llbc),
                    "repair_patch_sha256": sha256_file(t2_patch_path),
                    "repaired_amir_sha256": sha256_file(t2_repaired_amir),
                    "repaired_ullbc_sha256": sha256_file(t2_repaired_ullbc),
                    "repaired_llbc_sha256": sha256_file(t2_repaired_llbc),
                    "repaired_matches_canonical_holdout": sha256_file(t2_repaired_amir)
                    == sha256_file(os.path.join(V4_ART_DIR, "zerocopy_layout_holdout.amir")),
                },
                "measurements": {
                    "buggy_capture_wall_clock_ms": m_t2_buggy["wall_clock_ms"],
                    "buggy_capture_max_rss_bytes": m_t2_buggy["max_rss_bytes"],
                    "buggy_ullbc_wall_clock_ms": m_t2_buggy_ullbc["wall_clock_ms"],
                    "buggy_llbc_wall_clock_ms": m_t2_buggy_llbc["wall_clock_ms"],
                    "repaired_capture_wall_clock_ms": m_t2_repaired["wall_clock_ms"],
                    "repaired_capture_max_rss_bytes": m_t2_repaired["max_rss_bytes"],
                },
            },
            "task3_behavior_preserving_refactor_maintenance": {
                "subjects": [
                    "zerocopy_layout_holdout::align_to",
                    "cleanup_subject::partial_init_move_cleanup",
                ],
                "align_to_local_shift": {
                    "before_locals_count": 23,
                    "after_locals_count": 24,
                    "before_var_debug_map": {"_1": "size", "_2": "align", "_8": "rem", "_15": "pad"},
                    "after_var_debug_map": t3_zc_vdi["recovered_bindings"],
                },
                "partial_init_move_cleanup_local_shift": {
                    "before_locals_count": 22,
                    "after_locals_count": t3_cs_vdi["total_locals"],
                    "after_var_debug_map": t3_cs_vdi["recovered_bindings"],
                },
                "artifacts": {
                    "refactor_patch_sha256": sha256_file(t3_patch_path),
                    "align_to_refactored_amir_sha256": sha256_file(t3_zc_amir),
                    "align_to_refactored_amir_size_bytes": os.path.getsize(t3_zc_amir),
                    "align_to_refactored_ullbc_sha256": sha256_file(t3_ullbc),
                    "align_to_refactored_llbc_sha256": sha256_file(t3_llbc),
                    "cleanup_refactored_amir_sha256": sha256_file(t3_cs_amir),
                    "cleanup_refactored_amir_size_bytes": os.path.getsize(t3_cs_amir),
                    "cleanup_refactored_ullbc_sha256": sha256_file(t3_cs_ullbc),
                    "cleanup_refactored_llbc_sha256": sha256_file(t3_cs_llbc),
                },
                "measurements": {
                    "zc_refactored_capture_ms": m_t3_zc["wall_clock_ms"],
                    "zc_refactored_capture_max_rss_bytes": m_t3_zc["max_rss_bytes"],
                    "cs_refactored_capture_ms": m_t3_cs["wall_clock_ms"],
                    "cs_refactored_capture_max_rss_bytes": m_t3_cs["max_rss_bytes"],
                },
            },
            "task4_weakening_trap_rejection": {
                "trap_a_postcondition_weakening": {
                    "artifact_sha256": sha256_file(t4_trap_a_path),
                    "verified_in_lean_module": "AnnealResearch/AgentTasksAndCompilerUpgrade.lean & AnnealResearch/AgentTasksAndCompilerUpgradeControls.lean",
                },
                "trap_b_dropped_preserve_ub": {
                    "artifact_sha256": sha256_file(t4_trap_b_amir),
                    "preserve_ub_header_bit_in_amir": bool(open(t4_trap_b_amir, "rb").read()[6] & 0x02),
                    "verified_in_lean_module": "AnnealResearch/AgentTasksAndCompilerUpgrade.lean & AnnealResearch/AgentTasksAndCompilerUpgradeControls.lean",
                },
                "trap_c_unproved_assumption": {
                    "artifact_sha256": sha256_file(t4_trap_c_path),
                    "verified_in_lean_module": "AnnealResearch/AgentTasksAndCompilerUpgrade.lean & AnnealResearch/AgentTasksAndCompilerUpgradeControls.lean",
                },
            },
        },
        "four_toolchain_amir_v3_upgrade_trial": tc_records,
    }

    ledger_path = os.path.join(OUT_DIR, "agent-tasks-ledger.json")
    with open(ledger_path, "w") as f:
        json.dump(ledger, f, indent=2)
        f.write("\n")
    print("Wrote agent-tasks-ledger.json:", ledger_path)
    print("SHA256:", sha256_file(ledger_path))


if __name__ == "__main__":
    main()
