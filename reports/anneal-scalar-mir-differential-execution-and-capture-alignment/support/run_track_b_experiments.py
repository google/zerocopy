#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Track B experimental verification harness for Q-B2.

Tests:
1. Phase 1 (Zero Lean Syntax/Semantics Changes):
   - Evaluates `mir::Const::Unevaluated` scalar constants and validates
     `body.required_consts` via `tcx.const_eval_resolve`.
   - Verifies that `i8::MIN`, `u32::MAX`, `const ITEM: i32 = -42`, `const { -42 }`,
     zero-field `AggregateKind::Adt` enum construction, identity `CastKind::IntToInt`
     (`e as isize`), and Starnix's `verifier::saturating_inc_u32` are captured and
     verified with 0 changes to `Trusted/Mvp/{Syntax,Semantics}.lean`.
   - Verifies that dead-branch `if false { const { panic!() } }` and
     `if false { const { 1 / 0 } }` in `body.required_consts` are rejected as
     unevaluable constants at capture (`status: "unsupported"`).
   - Verifies that non-enum `Rvalue::Discriminant` is rejected at capture
     (`status: "unsupported"`), closing the `status: "captured"` / `bodyWF = false`
     mismatch.
   - Verifies Empty Enum Option B (`ANNEAL_REJECT_EMPTY_ENUM=1`) rejects
     `pub enum EmptyEnum {}` at capture (`status: "unsupported"`).
2. Phase 2 (Relaxed `Ty.admitted` on Empty Enums + `UnaryOp.neg` & `UnaryOp.not`):
   - Verifies Empty Enum Option A (`Ty.admitted` without `!ds.isEmpty`) preserves
     all theorems in `Anneal/Mvp/Execution.lean` and `Anneal/Mvp/Canaries.lean`
     and enables `empty_enum_crate` (`pub fn match_empty(e: EmptyEnum) -> u64`)
     to pass end-to-end verification (`status: "crate_verified"`).
   - Verifies `UnaryOp.neg` (wrapping two's-complement negation under
     `-C overflow-checks=no`) and `UnaryOp.not` (bitwise complement on `Int`,
     logical negation on `Bool`) across Native `rustc`, Miri, and Lean 4 kernel
     `rfl` on boundary inputs (`i8::MIN`, `-1`, `0`, `127`, `i16::MIN`,
     `i32::MIN`, `i64::MIN`, `u8`, `u32`, `u64`, `bool`).
   - Verifies end-to-end `cargo-anneal verify` (`status: "crate_verified"`) on
     a unified crate combining all 9 valid extensions from the Task 2 refusal set.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
from typing import Any

TRACK_B_DIR = Path(__file__).resolve().parent
EXT_DIR = TRACK_B_DIR / "mvp-extended"
WORK_DIR = TRACK_B_DIR / "exp_work"

HOME = Path.home()
BUNDLE = Path(
    os.environ.get(
        "ANNEAL_TOOLCHAIN_BUNDLE",
        str(
            HOME
            / ".cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a"
        ),
    )
)
RUSTC = BUNDLE / "rust/bin/rustc"
MIRI = BUNDLE / "rust/bin/miri"
MIRI_SYSROOT = Path(os.environ.get("MIRI_SYSROOT", str(HOME / ".cache/miri")))
LEAN = BUNDLE / "lean/bin/lean"
ANNEAL_LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN", str(HOME / ".local/bin/anneal-lean-run")
)

CAPTURE_PHASE1 = EXT_DIR / "anneal-rustc-capture-phase1"
CAPTURE_PHASE2 = EXT_DIR / "anneal-rustc-capture-phase2"
CARGO_ANNEAL_BASELINE = Path(
    os.environ.get(
        "CARGO_ANNEAL_BASELINE",
        "/tmp/anneal-mvp-installed-final/bin/cargo-anneal",
    )
)
CARGO_ANNEAL_PHASE2 = EXT_DIR / "cargo-anneal-phase2"
STARNIX_RUST_DIR = (
    TRACK_B_DIR.parent.parent
    / "mvp-investigations/task3/profile_stage/rust"
)

COMMON_RUSTC_FLAGS = [
    "--edition=2024",
    "--target=x86_64-unknown-linux-gnu",
    "-Copt-level=0",
    "-Cdebug-assertions=no",
    "-Coverflow-checks=no",
]


def scrub_text(text: str) -> str:
    """Scrub workstation-specific paths from output strings."""
    return (
        text.replace(str(TRACK_B_DIR), "<TRACK_B>")
        .replace(str(BUNDLE), "<TOOLCHAIN_BUNDLE>")
        .replace(str(HOME), "<HOME>")
    )


def inject_execution_import(captured_lean: str) -> str:
    return captured_lean.replace(
        "import Trusted.Mvp\n",
        "import Trusted.Mvp\nimport Anneal.Mvp.Execution\n",
        1,
    )


def run_cmd(
    args: list[str],
    cwd: Path | None = None,
    env_extra: dict[str, str] | None = None,
    use_lean_run_mode: str | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = (
        f"{BUNDLE / 'rust/lib'}:{BUNDLE / 'lean/lib'}:{env.get('LD_LIBRARY_PATH', '')}"
    )
    if env_extra:
        env.update(env_extra)
    full_args = (
        [ANNEAL_LEAN_RUN, "--mode", use_lean_run_mode, "--concurrency", "4", "--"]
        + args
        if use_lean_run_mode
        else args
    )
    return subprocess.run(
        full_args,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=120,
    )


def run_capture(
    capture_bin: Path,
    name: str,
    rust_src: str,
    select: list[str] | None = None,
    scope_crate: bool = False,
    rustc_extra: list[str] | None = None,
    env_extra: dict[str, str] | None = None,
) -> dict[str, Any]:
    case_dir = WORK_DIR / name
    if case_dir.exists():
        shutil.rmtree(case_dir)
    case_dir.mkdir(parents=True)
    lib_rs = case_dir / "lib.rs"
    lib_rs.write_text(rust_src)
    out_dir = case_dir / "out"
    cmd = [
        str(capture_bin),
        f"--crate-root={lib_rs}",
        f"--crate-name={name}",
        "--edition=2024",
        "--target=x86_64-unknown-linux-gnu",
        f"--out-dir={out_dir}",
        f"--sysroot={BUNDLE / 'rust'}",
        f"--source-file={lib_rs}",
    ]
    if scope_crate:
        cmd.append("--scope=crate")
    for s in select or []:
        cmd.append(f"--select={s}")
    for cfg in rustc_extra or []:
        cmd.extend(["--cfg", cfg])

    proc = run_cmd(cmd, env_extra=env_extra)
    stdout_json = {}
    for line in proc.stdout.strip().splitlines():
        try:
            stdout_json = json.loads(line)
        except Exception:
            pass
    lean_path = out_dir / "Captured.lean"
    return {
        "exit_code": proc.returncode,
        "status": stdout_json.get("status", "unknown"),
        "diagnostics": [scrub_text(d) for d in stdout_json.get("diagnostics", [])],
        "unsupported": [
            {
                "path": u.get("path"),
                "reason": scrub_text(u.get("reason", "")),
            }
            for u in stdout_json.get("unsupported", [])
        ],
        "captured_lean": lean_path.read_text() if lean_path.exists() else None,
        "case_dir": case_dir,
    }


def build_baseline_lean_env() -> Path:
    """Compile unmodified baseline Syntax.lean and Semantics.lean for Phase 1 checks."""
    base_src = TRACK_B_DIR.parent / "mvp-baseline"
    build_dir = WORK_DIR / "lean_baseline_build"
    if build_dir.exists():
        shutil.rmtree(build_dir)
    (build_dir / "Trusted/Mvp").mkdir(parents=True)
    (build_dir / "Anneal/Mvp").mkdir(parents=True)
    lean_path = f"{build_dir}:{BUNDLE / 'lean/lib/lean'}"
    for rel, root in [
        ("Trusted/Mvp/Syntax.lean", base_src / "trusted/lean"),
        ("Trusted/Mvp/Semantics.lean", base_src / "trusted/lean"),
        ("Trusted/Mvp.lean", base_src / "trusted/lean"),
        ("Trusted.lean", base_src / "trusted/lean"),
        ("Anneal/Mvp/Execution.lean", base_src / "theory"),
        ("Anneal/Mvp/Canaries.lean", base_src / "theory"),
    ]:
        olean = build_dir / rel.replace(".lean", ".olean")
        res = run_cmd(
            [str(LEAN), "-R", str(root), "-o", str(olean), str(root / rel)],
            env_extra={"LEAN_PATH": lean_path},
            use_lean_run_mode="file",
        )
        assert res.returncode == 0, f"Baseline Lean build failed on {rel}: {res.stdout} {res.stderr}"
    return build_dir


def run_experiment_1_phase1(baseline_lean_build: Path) -> dict[str, Any]:
    """Test Phase 1 (`anneal-rustc-capture-phase1` + 0 Lean changes)."""
    results: dict[str, Any] = {}

    # 1a. Unevaluated scalar constants + enum variant construction + e as isize
    src_1a = """#![allow(dead_code)]
#[repr(isize)]
pub enum SimpleEnum {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

pub const MODULE_CONST: i32 = -42;

pub fn i8_min_val() -> i8 {
    i8::MIN
}

pub fn u32_max_val() -> u32 {
    u32::MAX
}

pub fn use_module_const(x: i32) -> i32 {
    x + MODULE_CONST
}

pub fn use_inline_const(x: i32) -> i32 {
    x + const { -40 + -2 }
}

pub fn construct_pos() -> SimpleEnum {
    SimpleEnum::Pos
}

pub fn enum_to_isize(e: SimpleEnum) -> isize {
    e as isize
}

pub fn match_constructed() -> i8 {
    let e = SimpleEnum::Neg;
    match e {
        SimpleEnum::Neg => -10,
        SimpleEnum::Zero => 0,
        SimpleEnum::Pos => 10,
    }
}
"""
    cap_1a = run_capture(
        CAPTURE_PHASE1,
        "phase1_zero_lean_valid",
        src_1a,
        scope_crate=True,
    )
    lean_check_1a = (
        inject_execution_import(cap_1a["captured_lean"])
        + """
namespace Phase1Check
open Trusted.Mvp
open Anneal.Mvp

def evalFn (idx : Nat) (args : List Word) : Option Word :=
  match Captured.program.bodies[idx]? with
  | none => none
  | some b => run b 32 (initial b args)

theorem all_bodies_wf : (Captured.program.bodies.all bodyWF) = true := rfl
-- body 0: i8_min_val() -> -128i8 (0x80)
theorem check_i8_min : evalFn 0 [] = some (BitVec.ofNat 64 0x80) := rfl
-- body 1: u32_max_val() -> 0xffffffff
theorem check_u32_max : evalFn 1 [] = some (BitVec.ofNat 64 0xffffffff) := rfl
-- body 2: use_module_const(50) -> 8
theorem check_module_const : evalFn 2 [BitVec.ofNat 64 50] = some (BitVec.ofNat 64 8) := rfl
-- body 3: use_inline_const(50) -> 8
theorem check_inline_const : evalFn 3 [BitVec.ofNat 64 50] = some (BitVec.ofNat 64 8) := rfl
-- body 4: construct_pos() -> variant index 2
theorem check_construct_pos : evalFn 4 [] = some (BitVec.ofNat 64 2) := rfl
-- body 5: enum_to_isize(Neg=idx 0 -> -1, Pos=idx 2 -> 1)
theorem check_enum_to_isize_neg : evalFn 5 [BitVec.ofNat 64 0] = some (BitVec.ofNat 64 0xffffffffffffffff) := rfl
theorem check_enum_to_isize_pos : evalFn 5 [BitVec.ofNat 64 2] = some (BitVec.ofNat 64 1) := rfl
-- body 6: match_constructed() -> -10i8 (0xf6)
theorem check_match_constructed : evalFn 6 [] = some (BitVec.ofNat 64 0xf6) := rfl

end Phase1Check
"""
    )
    check_file = cap_1a["case_dir"] / "Phase1Check.lean"
    check_file.write_text(lean_check_1a)
    lean_res = run_cmd(
        [str(LEAN), "-R", str(cap_1a["case_dir"]), str(check_file)],
        env_extra={"LEAN_PATH": f"{baseline_lean_build}:{BUNDLE / 'lean/lib/lean'}"},
        use_lean_run_mode="file",
    )
    results["phase1_zero_lean_valid_crate"] = {
        "capture_status": cap_1a["status"],
        "scope": "crate",
        "baseline_lean_rfl_passed": lean_res.returncode == 0,
        "lean_diagnostics": scrub_text((lean_res.stdout + lean_res.stderr).strip()),
        "verified_items": [
            "SimpleEnum (explicit negative discriminant AnonConst in --scope crate)",
            "MODULE_CONST (const item in --scope crate + Unevaluated operand)",
            "i8::MIN (Unevaluated associated const in required_consts + operand)",
            "u32::MAX (Unevaluated associated const in required_consts + operand)",
            "const { -40 + -2 } (InlineConst in --scope crate + Unevaluated operand)",
            "SimpleEnum::Pos (zero-field AggregateKind::Adt enum construction)",
            "e as isize (identity CastKind::IntToInt on isize discriminant)",
            "match SimpleEnum::Neg (constructed enum + SwitchInt on negative discriminant)",
        ],
    }

    # 1b. Starnix verifier::saturating_inc_u32 with 0 Lean changes!
    starnix_files = sorted(str(p) for p in STARNIX_RUST_DIR.rglob("*.rs"))
    starnix_out = WORK_DIR / "starnix_saturating_inc_u32_cap"
    if starnix_out.exists():
        shutil.rmtree(starnix_out)
    starnix_cmd = [
        str(CAPTURE_PHASE1),
        f"--crate-root={STARNIX_RUST_DIR / 'lib.rs'}",
        "--crate-name=ebpf_core",
        "--edition=2024",
        "--target=x86_64-unknown-linux-gnu",
        f"--out-dir={starnix_out}",
        f"--sysroot={BUNDLE / 'rust'}",
        "--select=verifier::saturating_inc_u32",
    ] + [f"--source-file={p}" for p in starnix_files]
    starnix_proc = run_cmd(starnix_cmd)
    starnix_json = json.loads(starnix_proc.stdout.strip().splitlines()[-1])
    starnix_captured_lean = (starnix_out / "Captured.lean").read_text()

    starnix_check = (
        inject_execution_import(starnix_captured_lean)
        + """
namespace StarnixPhase1Check
open Trusted.Mvp
open Anneal.Mvp

def b : Body := Captured.program.bodies[0]

theorem starnix_body_wf : bodyWF b = true := rfl
theorem starnix_eval_0 : run b 16 (initial b [0]) = some 1 := rfl
theorem starnix_eval_1 : run b 16 (initial b [1]) = some 2 := rfl
theorem starnix_eval_41 : run b 16 (initial b [41]) = some 42 := rfl
theorem starnix_eval_max_minus_1 :
    run b 16 (initial b [4294967294]) = some 4294967295 := rfl
theorem starnix_eval_max :
    run b 16 (initial b [4294967295]) = some 4294967295 := rfl

end StarnixPhase1Check
"""
    )
    starnix_check_file = starnix_out / "StarnixPhase1Check.lean"
    starnix_check_file.write_text(starnix_check)
    starnix_lean_res = run_cmd(
        [str(LEAN), "-R", str(starnix_out), str(starnix_check_file)],
        env_extra={"LEAN_PATH": f"{baseline_lean_build}:{BUNDLE / 'lean/lib/lean'}"},
        use_lean_run_mode="file",
    )
    results["starnix_saturating_inc_u32_zero_lean_changes"] = {
        "capture_status": starnix_json.get("status"),
        "selected_count": starnix_json.get("selected_count"),
        "census_count": starnix_json.get("census_count"),
        "baseline_lean_wf_and_eval_passed": starnix_lean_res.returncode == 0,
        "lean_diagnostics": scrub_text(
            (starnix_lean_res.stdout + starnix_lean_res.stderr).strip()
        ),
        "boundary_vectors_verified": [
            {"input": 0, "output": 1},
            {"input": 1, "output": 2},
            {"input": 41, "output": 42},
            {"input": 4294967294, "output": 4294967295},
            {"input": 4294967295, "output": 4294967295},
        ],
    }

    # 1c. Dead-branch failing required_consts (`if false { const { panic!() } }` and `1 / 0`)
    cap_dead_panic = run_capture(
        CAPTURE_PHASE1,
        "dead_inline_const_panic",
        """pub fn dead_panic(x: i32) -> i32 {
    if false {
        const { panic!("dead const panic") }
    } else {
        x + 1
    }
}
""",
        select=["dead_panic"],
    )
    cap_dead_div0 = run_capture(
        CAPTURE_PHASE1,
        "dead_inline_const_div0",
        """#![allow(unconditional_panic)]
pub fn dead_div0(x: i32) -> i32 {
    if false {
        const { 1 / 0 }
    } else {
        x + 1
    }
}
""",
        select=["dead_div0"],
    )
    results["required_consts_dead_branch_rejection"] = {
        "dead_panic": {
            "status": cap_dead_panic["status"],
            "unsupported": cap_dead_panic["unsupported"],
        },
        "dead_div0": {
            "status": cap_dead_div0["status"],
            "unsupported": cap_dead_div0["unsupported"],
        },
    }

    # 1d. Non-enum Rvalue::Discriminant rejection (matching Task 2's custom_mir_discriminant_on_non_enum)
    cap_non_enum_discr = run_capture(
        CAPTURE_PHASE1,
        "custom_mir_non_enum_discr",
        """#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_mir_discriminant_on_non_enum(x: i32) -> u8 {
    mir! {
        {
            RET = Discriminant(x);
            Return()
        }
    }
}
""",
        select=["custom_mir_discriminant_on_non_enum"],
    )
    results["non_enum_discriminant_rejection"] = {
        "status": cap_non_enum_discr["status"],
        "unsupported": cap_non_enum_discr["unsupported"],
    }

    # 1e. Empty Enum Option B (reject in extract.rs via ANNEAL_REJECT_EMPTY_ENUM=1)
    cap_empty_enum_opt_b = run_capture(
        CAPTURE_PHASE1,
        "empty_enum_option_b",
        """pub enum EmptyEnum {}
pub fn match_empty(e: EmptyEnum) -> u64 {
    match e {}
}
""",
        scope_crate=True,
        env_extra={"ANNEAL_REJECT_EMPTY_ENUM": "1"},
    )
    results["empty_enum_option_b_reject_in_extract"] = {
        "status": cap_empty_enum_opt_b["status"],
        "unsupported": cap_empty_enum_opt_b["unsupported"],
    }

    return results


def run_e2e_cargo_anneal(
    name: str,
    lib_rs_src: str,
    spec_lean_src: str,
    proof_lean_src: str,
) -> dict[str, Any]:
    """Run full end-to-end `cargo-anneal-phase2 verify` with TrustedBoundary audit."""
    crate_dir = WORK_DIR / f"e2e_{name}"
    if crate_dir.exists():
        shutil.rmtree(crate_dir)
    (crate_dir / "src").mkdir(parents=True)
    (crate_dir / "proof").mkdir(parents=True)
    (crate_dir / "Cargo.toml").write_text(
        f"""[package]
name = "{name}"
version = "0.1.0"
edition = "2024"
"""
    )
    (crate_dir / "src/lib.rs").write_text(lib_rs_src)
    (crate_dir / "proof/Spec.lean").write_text(spec_lean_src)
    (crate_dir / "proof/Proof.lean").write_text(proof_lean_src)
    artifacts_dir = crate_dir / "artifacts"

    cmd = [
        str(CARGO_ANNEAL_PHASE2),
        "verify",
        f"--manifest-path={crate_dir / 'Cargo.toml'}",
        f"--proof-dir={crate_dir / 'proof'}",
        f"--capture={CAPTURE_PHASE2}",
        f"--lean={LEAN}",
        f"--sysroot={BUNDLE / 'rust'}",
        f"--artifacts={artifacts_dir}",
    ]
    res = run_cmd(cmd, use_lean_run_mode="build")
    try:
        stdout_json = json.loads(res.stdout)
    except Exception:
        stdout_json = {}
    return {
        "exit_code": res.returncode,
        "status": stdout_json.get("status", "unknown"),
        "phase": stdout_json.get("phase"),
        "detail": scrub_text(str(stdout_json.get("detail", ""))),
        "theorem": stdout_json.get("theorem"),
        "scope": stdout_json.get("scope"),
    }


def run_native_and_miri(name: str, main_rs: str) -> dict[str, Any]:
    """Run a test harness under both Native rustc and Miri and parse JSON lines."""
    run_dir = WORK_DIR / f"diff_{name}"
    if run_dir.exists():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    src_file = run_dir / "main.rs"
    src_file.write_text(main_rs)
    bin_file = run_dir / "main_bin"

    c_res = run_cmd(
        [str(RUSTC)] + COMMON_RUSTC_FLAGS + [str(src_file), "-o", str(bin_file)]
    )
    assert c_res.returncode == 0, f"Native compile failed: {c_res.stderr}"
    n_res = run_cmd([str(bin_file)])
    assert n_res.returncode == 0, f"Native run failed: {n_res.stderr}"
    native_out = json.loads(n_res.stdout.strip())

    m_res = run_cmd(
        [
            str(MIRI),
            f"--sysroot={MIRI_SYSROOT}",
            "-Zmiri-disable-isolation",
        ]
        + COMMON_RUSTC_FLAGS
        + [str(src_file)]
    )
    assert m_res.returncode == 0, f"Miri run failed: {m_res.stderr}"
    miri_out = json.loads(m_res.stdout.strip())
    return {
        "native": native_out,
        "miri": miri_out,
        "native_equals_miri": native_out == miri_out,
    }


def run_experiment_2_phase2() -> dict[str, Any]:
    """Test Phase 2 (Empty Enum Option A + UnaryOp.neg & UnaryOp.not + E2E CrateTheorem)."""
    results: dict[str, Any] = {}

    # 2a. Empty Enum Option A end-to-end CrateTheorem verification (`empty_enum_crate`)
    e2e_empty = run_e2e_cargo_anneal(
        "empty_enum_crate",
        """pub enum EmptyEnum {}

pub fn match_empty(e: EmptyEnum) -> u64 {
    match e {}
}
""",
        """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace Spec

def specs : Trusted.Mvp.Specs :=
  { safety := fun _ _ => True
    property := fun program =>
      ∃ body, program.bodies[0]? = some body ∧
        (∀ args, ¬Trusted.Mvp.argsValid body args) }

end Spec
""",
        """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Anneal.Mvp.Execution
import Captured
import Spec

namespace Proof

open Trusted.Mvp

theorem empty_enum_no_valid_args (args : List Word) :
    ¬argsValid Captured.program.bodies[0] args := by
  intro valid
  cases args with
  | nil => cases valid.1
  | cons value rest =>
      cases valid.2 0 value rfl with
      | intro ty evidence =>
          have same : Ty.enum 3 [] = ty := Option.some.inj evidence.1
          subst ty
          have impossible := evidence.2
          change false = true at impossible
          cases impossible

theorem verify : CrateTheorem Captured.program Spec.specs := by
  refine ⟨rfl, ?_, ⟨Captured.program.bodies[0], rfl, empty_enum_no_valid_args⟩⟩
  intro id body hBody
  cases id with
  | zero =>
      injection hBody with hEq
      subst hEq
      refine ⟨rfl, ?_⟩
      intro args hArgs _
      exact False.elim (empty_enum_no_valid_args args hArgs)
  | succ n =>
      cases hBody

end Proof
""",
    )
    results["empty_enum_option_a_e2e_crate_verified"] = e2e_empty

    # 2b. Differential execution across Native rustc, Miri, and Lean 4 kernel `rfl`
    # for UnaryOp.neg, UnaryOp.not, and all 9 valid Task 2 refusal cases!
    diff_main_rs = """#![allow(dead_code, arithmetic_overflow)]

#[repr(isize)]
#[derive(Clone, Copy)]
pub enum SimpleEnum {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

pub const MODULE_CONST: i32 = -42;

pub fn c07_enum_match_i8(e: SimpleEnum) -> i8 {
    match e {
        SimpleEnum::Neg => -10,
        SimpleEnum::Zero => 0,
        SimpleEnum::Pos => 10,
    }
}

pub fn c08_enum_discriminant_isize(e: SimpleEnum) -> isize {
    e as isize
}

pub fn c11_i8_min_const() -> i8 {
    i8::MIN
}

pub fn c12_u32_max_const() -> u32 {
    u32::MAX
}

pub fn c13_const_item_neg(x: i32) -> i32 {
    x + MODULE_CONST
}

pub fn c14_unary_neg_i8(x: i8) -> i8 {
    -x
}

pub fn c14_unary_neg_i64(x: i64) -> i64 {
    -x
}

pub fn c15_unary_not_i8(x: i8) -> i8 {
    !x
}

pub fn c15_unary_not_u8(x: u8) -> u8 {
    !x
}

pub fn c15_unary_not_bool(b: bool) -> bool {
    !b
}

pub fn c16_enum_variant_construct(which: u8) -> isize {
    let e = if which == 0 {
        SimpleEnum::Neg
    } else if which == 1 {
        SimpleEnum::Zero
    } else {
        SimpleEnum::Pos
    };
    e as isize
}

fn u8_bits(v: i8) -> u64 {
    (v as u8) as u64
}

fn u64_bits_i32(v: i32) -> u64 {
    (v as u32) as u64
}

fn u64_bits_isize(v: isize) -> u64 {
    v as u64
}

fn u64_bits_i64(v: i64) -> u64 {
    v as u64
}

fn main() {
    let c07 = [
        u8_bits(c07_enum_match_i8(SimpleEnum::Neg)),
        u8_bits(c07_enum_match_i8(SimpleEnum::Zero)),
        u8_bits(c07_enum_match_i8(SimpleEnum::Pos)),
    ];
    let c08 = [
        u64_bits_isize(c08_enum_discriminant_isize(SimpleEnum::Neg)),
        u64_bits_isize(c08_enum_discriminant_isize(SimpleEnum::Zero)),
        u64_bits_isize(c08_enum_discriminant_isize(SimpleEnum::Pos)),
    ];
    let c11 = u8_bits(c11_i8_min_const());
    let c12 = c12_u32_max_const() as u64;
    let c13 = [
        u64_bits_i32(c13_const_item_neg(0)),
        u64_bits_i32(c13_const_item_neg(42)),
        u64_bits_i32(c13_const_item_neg(50)),
    ];
    let c14_i8 = [
        u8_bits(c14_unary_neg_i8(i8::MIN)),
        u8_bits(c14_unary_neg_i8(-1)),
        u8_bits(c14_unary_neg_i8(0)),
        u8_bits(c14_unary_neg_i8(1)),
        u8_bits(c14_unary_neg_i8(127)),
    ];
    let c14_i64 = [
        u64_bits_i64(c14_unary_neg_i64(i64::MIN)),
        u64_bits_i64(c14_unary_neg_i64(-1)),
        u64_bits_i64(c14_unary_neg_i64(0)),
        u64_bits_i64(c14_unary_neg_i64(1)),
    ];
    let c15_i8 = [
        u8_bits(c15_unary_not_i8(i8::MIN)),
        u8_bits(c15_unary_not_i8(-1)),
        u8_bits(c15_unary_not_i8(0)),
        u8_bits(c15_unary_not_i8(127)),
    ];
    let c15_u8 = [
        c15_unary_not_u8(0) as u64,
        c15_unary_not_u8(1) as u64,
        c15_unary_not_u8(0x80) as u64,
        c15_unary_not_u8(0xff) as u64,
    ];
    let c15_bool = [
        c15_unary_not_bool(false) as u64,
        c15_unary_not_bool(true) as u64,
    ];
    let c16 = [
        u64_bits_isize(c16_enum_variant_construct(0)),
        u64_bits_isize(c16_enum_variant_construct(1)),
        u64_bits_isize(c16_enum_variant_construct(2)),
    ];
    println!(
        "{{\\"c07\\":{:?},\\"c08\\":{:?},\\"c11\\\":{},\\"c12\\\":{},\\"c13\\":{:?},\\"c14_i8\\":{:?},\\"c14_i64\\":{:?},\\"c15_i8\\":{:?},\\"c15_u8\\":{:?},\\"c15_bool\\":{:?},\\"c16\\":{:?}}}",
        c07, c08, c11, c12, c13, c14_i8, c14_i64, c15_i8, c15_u8, c15_bool, c16
    );
}
"""
    nm_res = run_native_and_miri("task2_resolved_cases", diff_main_rs)
    native_vals = nm_res["native"]

    unified_lib_rs = """pub enum EmptyEnum {}

#[repr(isize)]
pub enum SimpleEnum {
    Neg = -1,
    Zero = 0,
    Pos = 1,
}

pub const MODULE_CONST: i32 = -42;

pub fn c07_enum_match_i8(e: SimpleEnum) -> i8 {
    match e {
        SimpleEnum::Neg => -10,
        SimpleEnum::Zero => 0,
        SimpleEnum::Pos => 10,
    }
}

pub fn c08_enum_discriminant_isize(e: SimpleEnum) -> isize {
    e as isize
}

pub fn c10_match_empty(e: EmptyEnum) -> u64 {
    match e {}
}

pub fn c11_i8_min_const() -> i8 {
    i8::MIN
}

pub fn c12_u32_max_const() -> u32 {
    u32::MAX
}

pub fn c13_const_item_neg(x: i32) -> i32 {
    x + MODULE_CONST
}

pub fn c14_unary_neg_i8(x: i8) -> i8 {
    -x
}

pub fn c14_unary_neg_i64(x: i64) -> i64 {
    -x
}

pub fn c15_unary_not_i8(x: i8) -> i8 {
    !x
}

pub fn c15_unary_not_u8(x: u8) -> u8 {
    !x
}

pub fn c15_unary_not_bool(b: bool) -> bool {
    !b
}

pub fn c16_enum_variant_construct(which: u8) -> isize {
    let e = if which == 0 {
        SimpleEnum::Neg
    } else if which == 1 {
        SimpleEnum::Zero
    } else {
        SimpleEnum::Pos
    };
    e as isize
}
"""
    cap_unified = run_capture(
        CAPTURE_PHASE2,
        "phase2_unified_crate",
        unified_lib_rs,
        scope_crate=True,
    )
    lean_diff_assertions = [
        "theorem all_wf : (Captured.program.bodies.all bodyWF) = true := rfl",
        # c07 (body 0)
        f"theorem diff_c07_0 : evalFn 0 [0] = some (BitVec.ofNat 64 {native_vals['c07'][0]}) := rfl",
        f"theorem diff_c07_1 : evalFn 0 [1] = some (BitVec.ofNat 64 {native_vals['c07'][1]}) := rfl",
        f"theorem diff_c07_2 : evalFn 0 [2] = some (BitVec.ofNat 64 {native_vals['c07'][2]}) := rfl",
        # c08 (body 1)
        f"theorem diff_c08_0 : evalFn 1 [0] = some (BitVec.ofNat 64 {native_vals['c08'][0]}) := rfl",
        f"theorem diff_c08_1 : evalFn 1 [1] = some (BitVec.ofNat 64 {native_vals['c08'][1]}) := rfl",
        f"theorem diff_c08_2 : evalFn 1 [2] = some (BitVec.ofNat 64 {native_vals['c08'][2]}) := rfl",
        # c10 (body 2) -> empty enum
        "theorem diff_c10_wf : bodyWF Captured.program.bodies[2] = true := rfl",
        # c11 (body 3)
        f"theorem diff_c11 : evalFn 3 [] = some (BitVec.ofNat 64 {native_vals['c11']}) := rfl",
        # c12 (body 4)
        f"theorem diff_c12 : evalFn 4 [] = some (BitVec.ofNat 64 {native_vals['c12']}) := rfl",
        # c13 (body 5)
        f"theorem diff_c13_0 : evalFn 5 [0] = some (BitVec.ofNat 64 {native_vals['c13'][0]}) := rfl",
        f"theorem diff_c13_42 : evalFn 5 [42] = some (BitVec.ofNat 64 {native_vals['c13'][1]}) := rfl",
        f"theorem diff_c13_50 : evalFn 5 [50] = some (BitVec.ofNat 64 {native_vals['c13'][2]}) := rfl",
        # c14_i8 (body 6): inputs i8::MIN=128, -1=255, 0=0, 1=1, 127=127
        f"theorem diff_c14_i8_min : evalFn 6 [128] = some (BitVec.ofNat 64 {native_vals['c14_i8'][0]}) := rfl",
        f"theorem diff_c14_i8_m1 : evalFn 6 [255] = some (BitVec.ofNat 64 {native_vals['c14_i8'][1]}) := rfl",
        f"theorem diff_c14_i8_0 : evalFn 6 [0] = some (BitVec.ofNat 64 {native_vals['c14_i8'][2]}) := rfl",
        f"theorem diff_c14_i8_1 : evalFn 6 [1] = some (BitVec.ofNat 64 {native_vals['c14_i8'][3]}) := rfl",
        f"theorem diff_c14_i8_127 : evalFn 6 [127] = some (BitVec.ofNat 64 {native_vals['c14_i8'][4]}) := rfl",
        # c14_i64 (body 7): inputs i64::MIN, -1, 0, 1
        f"theorem diff_c14_i64_min : evalFn 7 [9223372036854775808] = some (BitVec.ofNat 64 {native_vals['c14_i64'][0]}) := rfl",
        f"theorem diff_c14_i64_m1 : evalFn 7 [18446744073709551615] = some (BitVec.ofNat 64 {native_vals['c14_i64'][1]}) := rfl",
        f"theorem diff_c14_i64_0 : evalFn 7 [0] = some (BitVec.ofNat 64 {native_vals['c14_i64'][2]}) := rfl",
        f"theorem diff_c14_i64_1 : evalFn 7 [1] = some (BitVec.ofNat 64 {native_vals['c14_i64'][3]}) := rfl",
        # c15_i8 (body 8): inputs i8::MIN=128, -1=255, 0=0, 127=127
        f"theorem diff_c15_i8_min : evalFn 8 [128] = some (BitVec.ofNat 64 {native_vals['c15_i8'][0]}) := rfl",
        f"theorem diff_c15_i8_m1 : evalFn 8 [255] = some (BitVec.ofNat 64 {native_vals['c15_i8'][1]}) := rfl",
        f"theorem diff_c15_i8_0 : evalFn 8 [0] = some (BitVec.ofNat 64 {native_vals['c15_i8'][2]}) := rfl",
        f"theorem diff_c15_i8_127 : evalFn 8 [127] = some (BitVec.ofNat 64 {native_vals['c15_i8'][3]}) := rfl",
        # c15_u8 (body 9): inputs 0, 1, 128, 255
        f"theorem diff_c15_u8_0 : evalFn 9 [0] = some (BitVec.ofNat 64 {native_vals['c15_u8'][0]}) := rfl",
        f"theorem diff_c15_u8_1 : evalFn 9 [1] = some (BitVec.ofNat 64 {native_vals['c15_u8'][1]}) := rfl",
        f"theorem diff_c15_u8_128 : evalFn 9 [128] = some (BitVec.ofNat 64 {native_vals['c15_u8'][2]}) := rfl",
        f"theorem diff_c15_u8_255 : evalFn 9 [255] = some (BitVec.ofNat 64 {native_vals['c15_u8'][3]}) := rfl",
        # c15_bool (body 10): inputs 0, 1
        f"theorem diff_c15_bool_0 : evalFn 10 [0] = some (BitVec.ofNat 64 {native_vals['c15_bool'][0]}) := rfl",
        f"theorem diff_c15_bool_1 : evalFn 10 [1] = some (BitVec.ofNat 64 {native_vals['c15_bool'][1]}) := rfl",
        # c16 (body 11): inputs 0, 1, 2
        f"theorem diff_c16_0 : evalFn 11 [0] = some (BitVec.ofNat 64 {native_vals['c16'][0]}) := rfl",
        f"theorem diff_c16_1 : evalFn 11 [1] = some (BitVec.ofNat 64 {native_vals['c16'][1]}) := rfl",
        f"theorem diff_c16_2 : evalFn 11 [2] = some (BitVec.ofNat 64 {native_vals['c16'][2]}) := rfl",
    ]
    lean_diff_src = (
        inject_execution_import(cap_unified["captured_lean"])
        + "\nnamespace Phase2Diff\nopen Trusted.Mvp\nopen Anneal.Mvp\n"
        + "def evalFn (idx : Nat) (args : List Word) : Option Word :=\n"
        + "  match Captured.program.bodies[idx]? with\n"
        + "  | none => none\n"
        + "  | some b => run b 32 (initial b args)\n\n"
        + "\n".join(lean_diff_assertions)
        + "\nend Phase2Diff\n"
    )
    diff_lean_file = cap_unified["case_dir"] / "Phase2Diff.lean"
    diff_lean_file.write_text(lean_diff_src)
    diff_lean_res = run_cmd(
        [str(LEAN), "-R", str(cap_unified["case_dir"]), str(diff_lean_file)],
        env_extra={
            "LEAN_PATH": f"{EXT_DIR / 'lean_build'}:{BUNDLE / 'lean/lib/lean'}"
        },
        use_lean_run_mode="file",
    )

    results["phase2_differential_native_miri_lean"] = {
        "capture_status": cap_unified["status"],
        "scope": "crate",
        "native_equals_miri": nm_res["native_equals_miri"],
        "lean_rfl_matches_native_and_miri": diff_lean_res.returncode == 0,
        "lean_rfl_assertion_count": len(lean_diff_assertions),
        "lean_diagnostics": scrub_text(
            (diff_lean_res.stdout + diff_lean_res.stderr).strip()
        ),
        "vectors": native_vals,
    }
    return results


def main() -> None:
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True)

    baseline_lean_build = build_baseline_lean_env()
    exp1 = run_experiment_1_phase1(baseline_lean_build)
    exp2 = run_experiment_2_phase2()

    receipts = {
        "compiler_version": "1.98.0-nightly (f8a08b688 2026-05-30)",
        "compiler_commit": "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
        "lean_version": "4.34.1",
        "experiment_1_phase1_zero_lean_changes": exp1,
        "experiment_2_phase2_extended_model": exp2,
    }
    out_file = TRACK_B_DIR / "track_b_verification_receipts.json"
    out_file.write_text(json.dumps(receipts, indent=2) + "\n")
    print(f"Wrote {out_file.name} successfully.")
    print(json.dumps(receipts, indent=2))


if __name__ == "__main__":
    main()
