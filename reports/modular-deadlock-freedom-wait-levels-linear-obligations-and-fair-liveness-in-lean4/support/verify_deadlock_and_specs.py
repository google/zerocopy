#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(os.environ["ANNEAL_ROOT"])
SCRATCH_ROOT = Path(__file__).resolve().parent
LEAN_PREFIX = Path(
    os.environ.get(
        "LEAN_PREFIX",
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"),
    )
)
LEAN_BIN = LEAN_PREFIX / "bin" / "lean"

OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]
ALL_PARTS = OLEAN_PARTS + IR_PARTS

CLEAN_ENV = {"PATH": "/usr/bin:/bin"}


def sha256_path(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def to_wire(avail: dict[str, str]) -> list[list[str]]:
    o = [avail[k] for k in OLEAN_PARTS if k in avail]
    i = [avail[k] for k in IR_PARTS if k in avail]
    return [o, i]


CHECK_ENV_CONSTANTS_LEAN = """\
import Lean.Environment
import Lean.Util.Sorry

open Lean

def constantHasSorry (ci : ConstantInfo) : Bool :=
  ci.type.hasSorry ||
    (ci.value? (allowOpaque := true)).any Expr.hasSorry ||
    match ci with
    | .recInfo v => v.rules.any (·.rhs.hasSorry)
    | _ => false

def main (args : List String) : IO UInt32 := do
  let [reqPath] := args
    | IO.eprintln "expected request json"; return 2
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile reqPath)
  let sysroot ← IO.ofExcept <| j.getObjValAs? String "sysroot"
  initSearchPath sysroot
  let entries ← IO.ofExcept <|
    j.getObjValAs? (Array (String × Array (Array String))) "artifacts"
  let arts : NameMap ImportArtifacts :=
    entries.foldl (init := {}) fun acc (n, parts) =>
      acc.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  let rootsRaw ← IO.ofExcept <| j.getObjValAs? (Array String) "roots"
  let repoModsRaw ← IO.ofExcept <| j.getObjValAs? (Array String) "repoModules"
  let repoModSet : NameSet := .ofList (repoModsRaw.toList.map String.toName)
  let env ← importModules (rootsRaw.map fun n => { module := n.toName }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false)
    (level := .private) (arts := arts)
  let mut totalConsts := 0
  let mut totalExtra := 0
  let mut nUnsafe := 0
  let mut nPartial := 0
  let mut nUnsafeRec := 0
  let mut nAxiom := 0
  let mut nOpaque := 0
  let mut nSorry := 0
  for m in env.header.modules, data in env.header.moduleData do
    if repoModSet.contains m.module then
      IO.println s!"MODULE {m.module}: constants={data.constants.size} extraConstNames={data.extraConstNames.size}"
      totalConsts := totalConsts + data.constants.size
      totalExtra := totalExtra + data.extraConstNames.size
      for ci in data.constants do
        if ci.isUnsafe then
          nUnsafe := nUnsafe + 1
          IO.eprintln s!"UNSAFE: {ci.name}"
        if ci.isPartial then
          nPartial := nPartial + 1
          IO.eprintln s!"PARTIAL: {ci.name}"
        if (ci.name.toString.splitOn "_unsafe_rec").length > 1 then
          nUnsafeRec := nUnsafeRec + 1
          IO.eprintln s!"UNSAFE_REC_CONST: {ci.name}"
        if ci.isAxiom then
          nAxiom := nAxiom + 1
          IO.eprintln s!"AXIOM: {ci.name}"
        if ci matches .opaqueInfo _ then
          nOpaque := nOpaque + 1
          IO.eprintln s!"OPAQUE: {ci.name}"
        if constantHasSorry ci then
          nSorry := nSorry + 1
          IO.eprintln s!"SORRY: {ci.name}"
      for en in data.extraConstNames do
        if (en.toString.splitOn "_unsafe_rec").length > 1 then
          nUnsafeRec := nUnsafeRec + 1
          IO.eprintln s!"UNSAFE_REC_EXTRA: {en}"
  IO.println s!"ENV_CHECK_SUMMARY: totalConstants={totalConsts} extraConstNames={totalExtra} isUnsafe={nUnsafe} isPartial={nPartial} unsafeRec={nUnsafeRec} isAxiom={nAxiom} isOpaque={nOpaque} hasSorry={nSorry}"
  if nUnsafe == 0 && nPartial == 0 && nUnsafeRec == 0 &&
     nAxiom == 0 && nOpaque == 0 && nSorry == 0 then
    return 0
  else
    return 1
"""

HEADLINE_THEOREMS = [
    # Trusted.Concurrency
    "Trusted.Concurrency.stepRequiresNotTerminated",
    "Trusted.Concurrency.progStepRequiresEnabled",
    "Trusted.Concurrency.osSpuriousWakeRequiresBlockedWait",
    "Trusted.Concurrency.noOsWakeRequiresBlockedWait",
    # Anneal.ConcurrencySeparation
    "Anneal.ConcurrencySeparation.noSpuriousWakes_implies_spuriousWakeNonRescuing",
    "Anneal.ConcurrencySeparation.subsystemDeadlockFree_implies_globalDeadlockFree",
    "Anneal.ConcurrencySeparation.subsystemDeadlockFreeWaitEpisode_implies_globalDeadlockFree",
    "Anneal.ConcurrencySeparation.strongFairTerminates_implies_globalDeadlockFree",
    "Anneal.ConcurrencySeparation.spinOnly_subsystemDeadlockFreeWaitEpisode",
    "Anneal.ConcurrencySeparation.wellFormedFutexProg_spuriousWakeNonRescuing",
    "Anneal.ConcurrencySeparation.spinOnce_subsystemDeadlockFreeWaitEpisode",
    "Anneal.ConcurrencySeparation.spinOnce_globalDeadlockFree",
    "Anneal.ConcurrencySeparation.spinOnce_spurious_globalDeadlockFree",
    "Anneal.ConcurrencySeparation.spinOnce_not_unconditionalTerminates",
    "Anneal.ConcurrencySeparation.contendedStarveRun_valid",
    "Anneal.ConcurrencySeparation.contendedStarveRun_strongFair_and_actionWeakFair_yet_starves",
    "Anneal.ConcurrencySeparation.spinContended_weakFair_and_actionStrongFair_no_starvation",
    "Anneal.ConcurrencySeparation.ticketContended_no_bargeIn_step",
    "Anneal.ConcurrencySeparation.ticketContended_weakFair_T0_starvation_free",
    "Anneal.ConcurrencySeparation.ticketContended_T1_never_terminates",
    "Anneal.ConcurrencySeparation.leakRun_hangs_under_strong_and_actionStrong_fairness",
    "Anneal.ConcurrencySeparation.multiPcSpuriousRetry_breaks_localState_progress",
    "Anneal.ConcurrencySeparation.multiPcSpuriousRetry_caught_by_waitEpisode",
    "Anneal.ConcurrencySeparation.healthyMultiPcWaiter_not_deadlockedWaitEpisode",
    "Anneal.ConcurrencySeparation.abBaMultiPc2_spurious_implication_instantiation",
    # Anneal.DeadlockLogic
    "Anneal.DeadlockLogic.creditChannel_slot_conservation",
    "Anneal.DeadlockLogic.strictDAG_has_maximal",
    "Anneal.DeadlockLogic.wellTypedWorld_no_closedBlockedSet",
    "Anneal.DeadlockLogic.wellTypedWorld_no_global_block",
    "Anneal.DeadlockLogic.condvarNotify_preserves_coupledInv",
    "Anneal.DeadlockLogic.worldStep_preserves_wellTypedWorld",
    "Anneal.DeadlockLogic.topology1a_dag_positive",
    "Anneal.DeadlockLogic.topology1a_forget_deadlock_witness",
    "Anneal.DeadlockLogic.topology1b_addr_sorted_lock_positive",
    "Anneal.DeadlockLogic.topology1b_same_addr_rejected",
    "Anneal.DeadlockLogic.topology2_rwlock_writerPref_rejects_recursive_read",
    "Anneal.DeadlockLogic.topology2_rwlock_readRecursive_admits_even_with_higher_lock",
    "Anneal.DeadlockLogic.topology2_rwlock_upgradable_clean_upgrade_positive",
    "Anneal.DeadlockLogic.topology2_rwlock_upgrade_while_holding_higher_lock_rejected",
    "Anneal.DeadlockLogic.topology3_condvar_standard_idiom_positive",
    "Anneal.DeadlockLogic.topology3_unheld_lock_condvar_notify_rejected",
    "Anneal.DeadlockLogic.topology3_unguarded_condvar_lost_wakeup_rejected",
    "Anneal.DeadlockLogic.topology3_condvar_outer_lock_deadlock_impossible",
    "Anneal.DeadlockLogic.topology4_once_hierarchical_positive",
    "Anneal.DeadlockLogic.topology4_once_reentrant_rejected",
    "Anneal.DeadlockLogic.topology4_once_containing_await_rejected",
    "Anneal.DeadlockLogic.topology4_once_containing_rayon_rejected",
    "Anneal.DeadlockLogic.topology5a_barrier_party_positive",
    "Anneal.DeadlockLogic.topology5a_barrier_double_ticket_same_thread_rejected",
    "Anneal.DeadlockLogic.topology5_bounded_chan_credit_send_under_higher_lock_positive",
    "Anneal.DeadlockLogic.topology5_mixed_mode_send_cannot_steal_credit_slot",
    "Anneal.DeadlockLogic.topology5_bounded_chan_overflow_while_holding_higher_lock_rejected",
    "Anneal.DeadlockLogic.topology5b_join_holding_lock_needed_by_child_impossible",
    "Anneal.DeadlockLogic.topology6_rayon_pure_nested_positive",
    "Anneal.DeadlockLogic.topology6_rayon_asymmetric_returned_guard_deadlock_rejected",
    "Anneal.DeadlockLogic.topology6_rayon_spoof_unlock_rejected",
    "Anneal.DeadlockLogic.topology6_rayon_os_recv_waiting_on_sibling_send_rejected",
    "Anneal.DeadlockLogic.topology6_rayon_holding_os_mutex_rejected",
    "Anneal.DeadlockLogic.topology7_async_mutex_across_await_and_scoped_sync_mutex_positive",
    "Anneal.DeadlockLogic.topology7_sync_mutex_across_await_single_worker_deadlock",
    # Anneal.ConcurrentSpecs
    "Anneal.ConcurrentSpecs.mutexStep_preserves_inv",
    "Anneal.ConcurrentSpecs.naive_ignore_poison_spec_refuted",
    "Anneal.ConcurrentSpecs.safe_rust_refutes_distinct_poisonInv",
    "Anneal.ConcurrentSpecs.safe_rust_refutes_distinct_poisonInv_concrete",
    "Anneal.ConcurrentSpecs.safe_forget_then_get_mut_breaks_unrestored_inv",
    "Anneal.ConcurrentSpecs.linear_mustRelease_and_unified_inv_sound_for_realStdMutex",
    "Anneal.ConcurrentSpecs.rwGhost_split_rejoin_half",
    "Anneal.ConcurrentSpecs.rwGhost_reader_agreement",
    "Anneal.ConcurrentSpecs.rwlock_downgrade_preserves_exact_value",
    "Anneal.ConcurrentSpecs.rwlock_unlock_then_read_loses_exact_value",
    "Anneal.ConcurrentSpecs.onceGhost_persistent_duplicable",
    "Anneal.ConcurrentSpecs.onceGhost_agreement",
    "Anneal.ConcurrentSpecs.genOnceGhost_scoped_soundness",
    "Anneal.ConcurrentSpecs.external_helper_linearizes_suspended_caller",
    "Anneal.ConcurrentSpecs.seqlock_odd_version_rejected",
    "Anneal.ConcurrentSpecs.seqlock_concurrent_write_retry_required",
    "Anneal.ConcurrentSpecs.seqlock_validated_read_linearizes_at_clean_snapshot",
    "Anneal.ConcurrentSpecs.ghost_erasure_invariant",
    "Anneal.ConcurrentSpecs.whole_program_future_lp_from_erased_physTrace",
    "Anneal.ConcurrentSpecs.chaseLev_valid_trace_linearizable",
    "Anneal.ConcurrentSpecs.chaseLev_buggy_no_cas_steal_refuted",
    "Anneal.ConcurrentSpecs.omo_refinement_implies_relLAT",
    "Anneal.ConcurrentSpecs.omo_refinement_implies_coupled_ghost_concurrent_relLAT",
    "Anneal.ConcurrentSpecs.non_relyStable_callerPost_fails_concurrent_relLAT",
    "Anneal.ConcurrentSpecs.cantor_no_unstratified_ghost_predicate_heap",
    "Anneal.ConcurrentSpecs.ratPrec_irrefl",
    "Anneal.ConcurrentSpecs.ratPrec_trans",
    "Anneal.ConcurrentSpecs.ratLevel_no_minimum",
    "Anneal.ConcurrentSpecs.ratLevel_no_maximum",
    "Anneal.ConcurrentSpecs.ratMediant_strictly_between",
    "Anneal.ConcurrentSpecs.downstream_interposes_below_between_and_above_upstream",
]


def main() -> int:
    lock_data = json.loads(
        (REPO_ROOT / "trusted/lean/foundation-lock.json").read_text()
    )
    inspector_orig = REPO_ROOT / "trusted/audit/TrustedBoundary.lean"

    lean_ver = subprocess.run(
        [str(LEAN_BIN), "--version"],
        env=CLEAN_ENV,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    lean_sha = sha256_path(LEAN_BIN)
    expected_lean_sha = lock_data["distributions"].get(lean_ver)
    assert expected_lean_sha == lean_sha, (
        f"Lean SHA mismatch: {lean_sha} vs {expected_lean_sha}"
    )
    print(f"TOOLCHAIN: {lean_ver}")
    print(f"LEAN_SHA256: {lean_sha}")

    mod_rel_paths = [
        ("Trusted.Concurrency", "Trusted/Concurrency.lean"),
        ("Anneal.ConcurrencySeparation", "Anneal/ConcurrencySeparation.lean"),
        ("Anneal.DeadlockLogic", "Anneal/DeadlockLogic.lean"),
        ("Anneal.ConcurrentSpecs", "Anneal/ConcurrentSpecs.lean"),
    ]

    for mod_name, rel in mod_rel_paths:
        p = SCRATCH_ROOT / rel
        txt = p.read_text()
        lines = len(txt.splitlines())
        sha = sha256_path(p)
        # Check zero sorry tokens outside comments:
        for idx, line in enumerate(txt.splitlines(), 1):
            code_part = line.split("--")[0]
            if "sorry" in code_part:
                print(f"FORBIDDEN sorry token in {rel}:{idx}: {line}", file=sys.stderr)
                return 1
        print(f"SOURCE {mod_name}: lines={lines} sha256={sha}")

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)
        inspector_staged = tmp / "TrustedBoundary.lean"
        shutil.copy2(inspector_orig, inspector_staged)

        staged_sources: list[tuple[str, str]] = []
        src_map: dict[str, Path] = {}
        for mod_name, rel in mod_rel_paths:
            dst = tmp / "src" / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SCRATCH_ROOT / rel, dst)
            staged_sources.append((mod_name, str(dst)))
            src_map[mod_name] = dst

        # Build foundation artifacts map
        artifacts: dict[str, list[list[str]]] = {}
        for fmod, rec in sorted(lock_data["modules"].items()):
            rel_mod = fmod.replace(".", "/")
            avail: dict[str, str] = {}
            for part in ALL_PARTS:
                expected = rec["parts"][part]
                installed = LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}"
                if expected is not None:
                    assert installed.exists() and sha256_path(installed) == expected, (
                        f"Missing or SHA-256 mismatch: {installed}"
                    )
                    avail[part] = str(installed)
            artifacts[fmod] = to_wire(avail)

        foundation_mods = sorted(lock_data["modules"].keys())
        graph = dict(lock_data["graph"])
        axioms = lock_data["axioms"]

        # -------------------------------------------------------------------
        # GATE 1: TrustedBoundary.lean "preflight"
        # -------------------------------------------------------------------
        pf_req = {
            "mode": "preflight",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
            "foundation": foundation_mods,
            "graph": graph,
            "axioms": axioms,
            "sources": staged_sources,
        }
        pf_req_path = tmp / "pf_req.json"
        pf_res_path = tmp / "pf_res.json"
        pf_req_path.write_text(json.dumps(pf_req))

        proc_pf = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "--run",
                str(inspector_staged),
                str(pf_req_path),
                str(pf_res_path),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
        )
        print(f"GATE 1 (PREFLIGHT) EXIT: {proc_pf.returncode}")
        if proc_pf.returncode != 0:
            print("PREFLIGHT STDERR:", proc_pf.stderr)
            if pf_res_path.exists():
                print("PREFLIGHT RES:", pf_res_path.read_text())
            return 1
        pf_env = json.loads(pf_res_path.read_text())
        print(f"PREFLIGHT OK: {pf_env['ok']}")
        assert pf_env["ok"] is True
        imports_by_mod: dict[str, list[dict]] = {}
        module_tiers: list[list[str]] = []
        for hdr in pf_env["result"]["headers"]:
            m = hdr["module"]
            t = hdr.get("trustTier")
            imps = hdr["imports"]
            imports_by_mod[m] = imps
            if m.startswith("Trusted."):
                assert t == "candidate:mir_semantics", f"Unexpected tier {t}"
                module_tiers.append([m, t])
            else:
                assert t is None, f"Unexpected tier {t} on theory module {m}"
            print(
                f"  HEADER: {json.dumps({'module': m, 'trustTier': t, 'importCount': len(imps)})}"
            )

        # -------------------------------------------------------------------
        # GATE 2: Strict --setup Kernel Compilation
        # -------------------------------------------------------------------
        out_lib = tmp / "lib"
        compile_failed = False
        for mod_name, _ in mod_rel_paths:
            setup_obj = {
                "name": mod_name,
                "isModule": False,
                "imports": imports_by_mod[mod_name],
                "importArts": artifacts,
                "dynlibs": [],
                "plugins": [],
                "options": {},
            }
            setup_path = tmp / f"{mod_name}.setup.json"
            setup_path.write_text(json.dumps(setup_obj))
            olean_out = out_lib / f"{mod_name.replace('.', '/')}.olean"
            olean_out.parent.mkdir(parents=True, exist_ok=True)
            proc_c = subprocess.run(
                [
                    str(LEAN_BIN),
                    "-j1",
                    "-M2048",
                    "-t0",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-DwarningAsError=true",
                    "--setup",
                    str(setup_path),
                    "-o",
                    str(olean_out),
                    str(src_map[mod_name]),
                ],
                cwd=tmp,
                env=CLEAN_ENV,
                capture_output=True,
                text=True,
            )
            print(
                f"GATE 2 COMPILE {mod_name}: exit={proc_c.returncode} stdout={proc_c.stdout!r} stderr={proc_c.stderr!r}"
            )
            if proc_c.returncode != 0 or proc_c.stdout != "" or proc_c.stderr != "":
                compile_failed = True
                continue
            avail_mod: dict[str, str] = {}
            stem = str(olean_out)[: -len("olean")]
            for part in ALL_PARTS:
                cand = Path(f"{stem}{part}")
                if cand.exists():
                    avail_mod[part] = str(cand)
            artifacts[mod_name] = to_wire(avail_mod)
            graph[mod_name] = imports_by_mod[mod_name]

        if compile_failed:
            return 1

        # -------------------------------------------------------------------
        # GATE 3: TrustedBoundary.lean "audit" (standalone requireMirWp: false)
        # -------------------------------------------------------------------
        audit_req = {
            "mode": "audit",
            "sysroot": str(LEAN_PREFIX),
            "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
            "foundation": foundation_mods,
            "graph": graph,
            "axioms": axioms,
            "trusted": ["Trusted.Concurrency"],
            "theory": [
                "Anneal.ConcurrencySeparation",
                "Anneal.DeadlockLogic",
                "Anneal.ConcurrentSpecs",
            ],
            "moduleTiers": module_tiers,
            "requireMirWp": False,
        }
        audit_req_path = tmp / "audit_req.json"
        audit_res_path = tmp / "audit_res.json"
        audit_req_path.write_text(json.dumps(audit_req))

        proc_aud = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "--run",
                str(inspector_staged),
                str(audit_req_path),
                str(audit_res_path),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
        )
        print(f"GATE 3 (AUDIT, requireMirWp=false) EXIT: {proc_aud.returncode}")
        if proc_aud.returncode != 0:
            print("AUDIT STDERR:", proc_aud.stderr)
            if audit_res_path.exists():
                print("AUDIT RES:", audit_res_path.read_text())
            return 1
        aud_env = json.loads(audit_res_path.read_text())
        assert aud_env["ok"] is True
        aud_res = aud_env["result"]
        assert aud_res["replay"] is True
        allowed_ax = {"propext", "Classical.choice", "Quot.sound"}
        assert set(aud_res["axioms"]).issubset(allowed_ax), aud_res["axioms"]
        summary_obj = {
            "ok": aud_env["ok"],
            "replay": aud_res["replay"],
            "requireMirWp": False,
            "kernelDeclarations": aud_res["kernelDeclarations"],
            "replayedDeclarations": aud_res["replayedDeclarations"],
            "checkedAlternateProofs": aud_res["checkedAlternateProofs"],
            "compilerOnlyNames": aud_res["compilerOnlyNames"],
            "reachableDeclarations": aud_res["reachableDeclarations"],
            "axioms": aud_res["axioms"],
        }
        print(f"AUDIT SUMMARY: {json.dumps(summary_obj)}")

        # -------------------------------------------------------------------
        # GATE 4: CheckEnvConstants.lean scan
        # -------------------------------------------------------------------
        chk_lean_path = tmp / "CheckEnvConstants.lean"
        chk_lean_path.write_text(CHECK_ENV_CONSTANTS_LEAN)
        chk_req_path = tmp / "chk_req.json"
        chk_req_path.write_text(
            json.dumps(
                {
                    "sysroot": str(LEAN_PREFIX),
                    "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
                    "roots": foundation_mods
                    + [m for m, _ in mod_rel_paths],
                    "repoModules": [m for m, _ in mod_rel_paths],
                }
            )
        )
        proc_chk = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "--run",
                str(chk_lean_path),
                str(chk_req_path),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
        )
        print(f"GATE 4 (ENV_INSPECT) EXIT: {proc_chk.returncode}")
        print(proc_chk.stdout.strip())
        if proc_chk.returncode != 0:
            print("ENV_INSPECT STDERR:", proc_chk.stderr)
            return 1

        # -------------------------------------------------------------------
        # GATE 5: #print axioms across every headline theorem
        # -------------------------------------------------------------------
        ax_src_lines = [
            "prelude",
            "import Trusted.Concurrency",
            "import Anneal.ConcurrencySeparation",
            "import Anneal.DeadlockLogic",
            "import Anneal.ConcurrentSpecs",
            "",
        ]
        for thm in HEADLINE_THEOREMS:
            ax_src_lines.append(f"#print axioms {thm}")
        ax_src = tmp / "AxiomAudit.lean"
        ax_src.write_text("\n".join(ax_src_lines) + "\n")
        ax_imports = [
            {
                "module": m,
                "importAll": False,
                "isExported": True,
                "isMeta": False,
            }
            for m, _ in mod_rel_paths
        ]
        ax_setup = tmp / "AxiomAudit.setup.json"
        ax_setup.write_text(
            json.dumps(
                {
                    "name": "AxiomAudit",
                    "isModule": False,
                    "imports": ax_imports,
                    "importArts": artifacts,
                    "dynlibs": [],
                    "plugins": [],
                    "options": {},
                }
            )
        )
        proc_ax = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "-t0",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "--setup",
                str(ax_setup),
                str(ax_src),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
        )
        print(
            f"GATE 5 (AXIOM AUDIT) EXIT: {proc_ax.returncode} (theorems={len(HEADLINE_THEOREMS)})"
        )
        if proc_ax.returncode != 0:
            print("AXIOM AUDIT STDERR:", proc_ax.stderr)
            print("AXIOM AUDIT STDOUT:", proc_ax.stdout)
            return 1
        ax_out = proc_ax.stdout.strip()
        for line in ax_out.splitlines():
            if "sorryAx" in line or "ofReduceBool" in line:
                print(f"FORBIDDEN AXIOM IN: {line}", file=sys.stderr)
                return 1
        print(ax_out)

    return 0


if __name__ == "__main__":
    sys.exit(main())
