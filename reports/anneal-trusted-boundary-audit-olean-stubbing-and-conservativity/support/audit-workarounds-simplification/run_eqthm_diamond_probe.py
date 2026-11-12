#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical probe for Topic 9 Question 2:
1. `isAllowedEqThm` false positives (namespace spoofing via authored theorems in
   `namespace Trusted` such as `Trusted.someThm.eq_1` or `Trusted.step.match_99`
   or `Trusted.step._sunfold`).
2. `isAllowedEqThm` false negatives on legitimate `realizeConst` theorems
   (`_private.<Mod>.0.Trusted.step.match_1.splitter`, `Trusted.step.congr_simp`,
   `Trusted.step.fun_cases_unfolding`, `Trusted.recFn.induct_unfolding`).
3. Diamond `realizeConst` crash when two sibling non-foundation modules
   (`TheoryMod1` and `TheoryMod2`) both realize equational/splitter theorems for
   `Trusted.step` or `Trusted.recFn` under both `isAllowedEqThm` and
   foundation/library-only `alternateProofs`.
4. Clean resolution via universal duplicate `.thmInfo` header verification +
   `alternateProofs` kernel replay (`_anneal_checked_alternate`) +
   `Lean.isReservedName` / ancestor-constant origin check."""

import json
from pathlib import Path
import shutil
import subprocess

HOME = Path.home()
TOOLCHAIN_DIR = HOME / ".elan/toolchains/leanprover--lean4---v4.34.1"
LEAN = str(TOOLCHAIN_DIR / "bin/lean")
SCRATCH_DIR = (
    HOME
    / "<scratch-root>"
    / "scratch/ref-pass-9-audit-simplification"
)
STAGE_DIR = SCRATCH_DIR / "eqthm_diamond_stage"

TRUSTED_MOD_SRC = """
namespace Trusted

def step (x : Option Nat) : Nat :=
  match x with
  | none => 0
  | some n => n + 1

def recFn (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => recFn k + 2

theorem trustedProp : True := trivial

end Trusted
"""

# TheoryMod1 triggers realization of:
# - Trusted.step.eq_1, Trusted.step.eq_2, Trusted.step.eq_def
# - _private.TrustedMod.0.Trusted.step.match_1.splitter (via split / simp)
# - Trusted.step.congr_simp (via simp)
# - Trusted.recFn.induct_unfolding / Trusted.step.fun_cases_unfolding
THEORY_MOD1_SRC = """
import TrustedMod

namespace Anneal.Mod1

theorem step_none : Trusted.step none = 0 := by
  simp [Trusted.step]

theorem step_cases (x : Option Nat) : Trusted.step x = 0 ∨ Trusted.step x > 0 := by
  fun_cases Trusted.step x
  · left; rfl
  · right; simp [Trusted.step]

theorem recFn_pos (n : Nat) : Trusted.recFn n > 0 := by
  fun_induction Trusted.recFn n
  · decide
  · omega

end Anneal.Mod1
"""

# TheoryMod2 independently imports TrustedMod (not TheoryMod1) and realizes the
# exact same lazy theorems (`Trusted.step.eq_1`, `Trusted.step.eq_def`,
# `_private.TrustedMod.0.Trusted.step.match_1.splitter`, `Trusted.recFn.induct_unfolding`),
# creating a diamond realization when DiamondRoot imports both TheoryMod1 and TheoryMod2!
THEORY_MOD2_SRC = """
import TrustedMod

namespace Anneal.Mod2

theorem step_some (n : Nat) : Trusted.step (some n) = n + 1 := by
  simp [Trusted.step]

theorem step_split (x : Option Nat) : Trusted.step x ≥ 0 := by
  fun_cases Trusted.step x <;> omega

theorem recFn_ge_one (n : Nat) : Trusted.recFn n ≥ 1 := by
  fun_induction Trusted.recFn n <;> omega

end Anneal.Mod2
"""

# SpoofMod is an untrusted theory module that authors fake theorems directly inside
# `namespace Trusted` using suffixes accepted by `isAllowedEqThm`:
# 1. `Trusted.trustedProp.eq_1` (since `Trusted.trustedProp` is a theorem, not a
#    safe definition, `Lean.isReservedName` is false so the elaborator allows it,
#    yet `isAllowedEqThm` only checks `(env.checked.get.find? baseName).isSome`!)
# 2. `Trusted.step.match_99` and `Trusted.step._sunfold` (neither `match_99` nor
#    `_sunfold` is a reserved name in `Lean.isReservedName`, so the elaborator
#    allows an untrusted module to declare arbitrary theorems with those names
#    inside `namespace Trusted`, and `isAllowedEqThm` waves them through!)
SPOOF_MOD_SRC = """
import TrustedMod

namespace Trusted

theorem trustedProp.eq_1 : False → False := id
theorem step.match_99 : True := trivial
theorem step._sunfold : 2 + 2 = 4 := rfl

end Trusted
"""

DIAMOND_ROOT_SRC = """
import TheoryMod1
import TheoryMod2
import SpoofMod
"""

PROBE_LEAN_SRC = r"""
import Lean
import Lean.Replay

open Lean

inductive Role where
  | foundation
  | trusted
  | theory
  deriving BEq, Repr

instance : ToString Role where
  toString
    | .foundation => "foundation"
    | .trusted => "trusted"
    | .theory => "theory"

/-- Exact string-suffix matcher from the `isAllowedEqThm` workaround. -/
def isEqThmSuffix (s : String) : Bool :=
  s == "eq_def" || s == "eq_unfold" || s == "splitter" ||
  s == "_sunfold" || s == "_cstage1" || s == "_cstage2" ||
  (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit) ||
  (s.startsWith "_eq_" && !(s.drop 4).isEmpty && (s.drop 4).all Char.isDigit) ||
  (s.startsWith "match_" && !(s.drop 6).isEmpty && (s.drop 6).all Char.isDigit)

def originMod (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.modules[idx.toNat]!.module

/-- Exact `isAllowedEqThm` predicate from the suffix-whitelist workaround. -/
def isAllowedEqThm (env : Environment) (roles : Std.HashMap Name Role)
    (ci : ConstantInfo) : Bool := Id.run do
  unless ci matches .thmInfo _ do return false
  match privateToUserName ci.name with
  | .str baseName suffix =>
    unless isEqThmSuffix suffix do return false
    if (env.checked.get.find? baseName).isNone then return false
    let some origMod := originMod env baseName | return false
    let some baseRole := roles.get? origMod | return false
    return baseRole == .foundation || baseRole == .trusted
  | _ => return false

/-- Use `Lean.isReservedName` from `Lean.ResolveName` directly. -/
def kernelIsReservedName (env : Environment) (name : Name) : Bool :=
  Lean.isReservedName env name

/-- Check whether `n` (or its un-privatized form) is a reserved realization name
or has an ancestor constant defined in `Trusted`/`foundation`. -/
partial def hasTrustedOrFoundationAncestor (env : Environment)
    (roles : Std.HashMap Name Role) (n : Name) : Bool :=
  match n with
  | .anonymous => false
  | .str p _ | .num p _ =>
    let directHit :=
      match originMod env p >>= roles.get? with
      | some .trusted | some .foundation => true
      | _ => false
    directHit || hasTrustedOrFoundationAncestor env roles p

/-- Check whether two `ConstantInfo` entries represent the same theorem header
(allowing cross-module `realizeConst` duplicate emissions with identical or
different proof bodies to be queued into `alternateProofs`). -/
def sameThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    ta.name == tb.name && ta.type == tb.type &&
      ta.levelParams == tb.levelParams && ta.all == tb.all
  | _, _ => false

def main (args : List String) : IO UInt32 := do
  let [sysrootStr, stageDirStr, outJsonStr] := args
    | IO.eprintln "Usage: ProbeEqThmAndDiamondRealize <sysroot> <stageDir> <out.json>"
      return 1
  Lean.initSearchPath (System.FilePath.mk sysrootStr) [System.FilePath.mk stageDirStr]
  let env ← importModules #[{ module := `DiamondRoot }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false

  let mut roles : Std.HashMap Name Role := {}
  for m in env.header.modules do
    let r :=
      if m.module == `TrustedMod then Role.trusted
      else if m.module == `TheoryMod1 || m.module == `TheoryMod2 ||
              m.module == `SpoofMod || m.module == `DiamondRoot then Role.theory
      else Role.foundation
    roles := roles.insert m.module r

  -- 1. Collect all constants in TheoryMod1, TheoryMod2, and SpoofMod
  let mut mod1Consts : Array ConstantInfo := #[]
  let mut mod2Consts : Array ConstantInfo := #[]
  let mut spoofConsts : Array ConstantInfo := #[]
  for m in env.header.modules, data in env.header.moduleData do
    if m.module == `TheoryMod1 then mod1Consts := data.constants
    if m.module == `TheoryMod2 then mod2Consts := data.constants
    if m.module == `SpoofMod then spoofConsts := data.constants

  -- Check False Positives in SpoofMod: authored theorems inside `namespace Trusted`
  let mut spoofResults : Array Json := #[]
  for ci in spoofConsts do
    let inTrustedNs := (privateToUserName ci.name).getRoot == `Trusted
    let allowedByHeuristic := isAllowedEqThm env roles ci
    let isReserved :=
      kernelIsReservedName env ci.name ||
      kernelIsReservedName env (privateToUserName ci.name)
    spoofResults := spoofResults.push <| Json.mkObj [
      ("name", toJson ci.name.toString),
      ("inTrustedNamespace", toJson inTrustedNs),
      ("isAllowedEqThm", toJson allowedByHeuristic),
      ("leanIsReservedName", toJson isReserved)
    ]

  -- Check False Negatives in TheoryMod1: legitimate realized theorems in `Trusted.*`
  -- rejected by `isAllowedEqThm`
  let mut mod1TrustedRealized : Array Json := #[]
  for ci in mod1Consts do
    let userRoot := (privateToUserName ci.name).getRoot
    if userRoot == `Trusted then
      let allowedByHeuristic := isAllowedEqThm env roles ci
      let hasAnc :=
        hasTrustedOrFoundationAncestor env roles ci.name ||
        hasTrustedOrFoundationAncestor env roles (privateToUserName ci.name)
      let isReserved :=
        kernelIsReservedName env ci.name ||
        kernelIsReservedName env (privateToUserName ci.name)
      mod1TrustedRealized := mod1TrustedRealized.push <| Json.mkObj [
        ("name", toJson ci.name.toString),
        ("userName", toJson (privateToUserName ci.name).toString),
        ("isThmInfo", toJson (ci matches .thmInfo _)),
        ("isAllowedEqThm", toJson allowedByHeuristic),
        ("hasTrustedAncestor", toJson hasAnc),
        ("leanIsReservedName", toJson isReserved)
      ]

  -- Check Diamond Realization Collisions between TheoryMod1 and TheoryMod2
  let mut mod1Map : Std.HashMap Name ConstantInfo := {}
  for ci in mod1Consts do
    mod1Map := mod1Map.insert ci.name ci

  let mut diamondCollisions : Array Json := #[]
  let mut suffixHeuristicAuditErrors : Array String := #[]
  let mut mvpAuditErrors : Array String := #[]
  for ci2 in mod2Consts do
    if let some ci1 := mod1Map.get? ci2.name then
      let orig := originMod env ci2.name
      let stored := env.checked.get.find? ci2.name
      let sameType := ci1.type == ci2.type
      let sameVal := ci1.value? true == ci2.value? true
      let allowedEq := isAllowedEqThm env roles ci2
      diamondCollisions := diamondCollisions.push <| Json.mkObj [
        ("name", toJson ci2.name.toString),
        ("const2ModIdxOrigin", toJson (orig.map Name.toString)),
        ("sameType", toJson sameType),
        ("sameProofValue", toJson sameVal),
        ("isAllowedEqThm", toJson allowedEq)
      ]
      -- Simulate suffix-heuristic `verifyAndCollectLocals` on TheoryMod2:
      if !allowedEq then
        suffixHeuristicAuditErrors := suffixHeuristicAuditErrors.push
          s!"duplicate declaration {ci2.name} in TheoryMod2"
      if orig != some `TheoryMod2 && !allowedEq then
        suffixHeuristicAuditErrors := suffixHeuristicAuditErrors.push
          s!"inventory origin mismatch {ci2.name} (orig={repr orig}, mod=TheoryMod2)"
      if let some st := stored then
        if st.value? true != ci1.value? true then
          suffixHeuristicAuditErrors := suffixHeuristicAuditErrors.push
            s!"stored declaration differs from inventory {ci1.name} in TheoryMod1"
      -- Simulate foundation-only-alternateProofs's `verifyAndCollectLocals` / `targetAudit` on TheoryMod2:
      mvpAuditErrors := mvpAuditErrors.push
        s!"duplicate declaration {ci2.name} in TheoryMod2 (and inventory origin mismatch)"
      if !sameVal then
        mvpAuditErrors := mvpAuditErrors.push
          s!"stored declaration differs from inventory {ci1.name} (role=.theory not in .foundation|.library)"

  -- Verify the unified universal `sameThmHeader` + `alternateProofs` kernel replay
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut alternateProofs : Array ConstantInfo := #[]
  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | continue
    if role == .trusted || role == .theory then
      if m.module == `SpoofMod then continue
      for ci in data.constants do
        let some stored := env.checked.get.find? ci.name
          | throw <| IO.userError s!"missing stored {ci.name}"
        if let some prev := locals.get? ci.name then
          unless sameThmHeader prev ci do
            throw <| IO.userError s!"non-matching duplicate declaration {ci.name}"
          if prev.value? true != ci.value? true then
            alternateProofs := alternateProofs.push ci
        else
          if stored.value? true != ci.value? true then
            unless sameThmHeader stored ci do
              throw <| IO.userError s!"stored non-theorem differs {ci.name}"
            alternateProofs := (alternateProofs.push stored).push ci
          locals := locals.insert ci.name stored

  -- Replay all `locals` + `alternateProofs` onto `Init` foundation kernel env
  let foundationMods := env.header.modules.filterMap fun m =>
    if roles.get? m.module == some .foundation then some { module := m.module : Import } else none
  let base ← importModules foundationMods {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let replayed ← base.toKernelEnv.replay locals
  let checkedEnv := Environment.ofKernelEnv replayed
  let mut freshIndex := 0
  for ci in alternateProofs do
    let .thmInfo info := ci | throw <| IO.userError "expected thmInfo"
    let typeOfType ← IO.ofExcept <|
      (Kernel.check checkedEnv {} info.type).mapError (fun _ => IO.userError s!"check failed: {ci.name}")
    unless Kernel.isDefEqGuarded checkedEnv {} typeOfType (.sort .zero) do
      throw <| IO.userError s!"not a Prop: {ci.name}"
    let fresh := Name.num `_anneal_checked_alternate freshIndex
    freshIndex := freshIndex + 1
    match replayed.addDeclCore 0 0 (.thmDecl { info with name := fresh }) (cancelTk? := none) with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError s!"alternate proof rejected: {ci.name}"

  let out := Json.mkObj [
    ("leanVersion", toJson "4.34.1"),
    ("spoofModFalsePositives", .arr spoofResults),
    ("theoryMod1RealizedInTrustedNamespace", .arr mod1TrustedRealized),
    ("diamondCollisionsBetweenMod1AndMod2", .arr diamondCollisions),
    ("suffixHeuristicAuditErrorsOnDiamond", toJson suffixHeuristicAuditErrors),
    ("foundationOnlyAlternateProofsErrorsOnDiamond", toJson mvpAuditErrors),
    ("universalThmReplayLocalsCount", toJson locals.size),
    ("universalThmReplayAlternateProofsChecked", toJson alternateProofs.size),
    ("universalThmReplaySucceeded", toJson true)
  ]
  IO.FS.writeFile outJsonStr (out.pretty ++ "\n")
  IO.println (out.pretty)
  return 0
"""


def run_lean(args, cwd, extra_env=None):
  env = dict(subprocess.os.environ)
  if extra_env:
    env.update(extra_env)
  cmd = [
      "anneal-lean-run",
      "--mode",
      "file",
      "--concurrency",
      "5",
      "--",
      LEAN,
  ] + args
  p = subprocess.run(
      cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False
  )
  assert p.returncode == 0, (
      f"Command {cmd} failed (rc={p.returncode}):\n{p.stdout}\n{p.stderr}"
  )
  return p.stdout


def main():
  if STAGE_DIR.exists():
    shutil.rmtree(STAGE_DIR)
  STAGE_DIR.mkdir(parents=True)

  (STAGE_DIR / "TrustedMod.lean").write_text(TRUSTED_MOD_SRC.strip() + "\n")
  (STAGE_DIR / "TheoryMod1.lean").write_text(THEORY_MOD1_SRC.strip() + "\n")
  (STAGE_DIR / "TheoryMod2.lean").write_text(THEORY_MOD2_SRC.strip() + "\n")
  (STAGE_DIR / "SpoofMod.lean").write_text(SPOOF_MOD_SRC.strip() + "\n")
  (STAGE_DIR / "DiamondRoot.lean").write_text(DIAMOND_ROOT_SRC.strip() + "\n")
  (STAGE_DIR / "ProbeEqThmAndDiamondRealize.lean").write_text(
      PROBE_LEAN_SRC.strip() + "\n"
  )

  env_path = {"LEAN_PATH": str(STAGE_DIR)}
  for mod in ["TrustedMod", "TheoryMod1", "TheoryMod2", "SpoofMod", "DiamondRoot"]:
    print(f"Compiling {mod}.lean...", flush=True)
    run_lean(["-o", f"{mod}.olean", f"{mod}.lean"], cwd=STAGE_DIR, extra_env=env_path)

  out_json = SCRATCH_DIR / "eqthm_diamond_probe_results.json"
  print("Running ProbeEqThmAndDiamondRealize.lean...", flush=True)
  run_lean(
      [
          "--run",
          "ProbeEqThmAndDiamondRealize.lean",
          str(TOOLCHAIN_DIR),
          str(STAGE_DIR),
          str(out_json),
      ],
      cwd=STAGE_DIR,
      extra_env=env_path,
  )
  print(f"Wrote {out_json}", flush=True)


if __name__ == "__main__":
  main()
