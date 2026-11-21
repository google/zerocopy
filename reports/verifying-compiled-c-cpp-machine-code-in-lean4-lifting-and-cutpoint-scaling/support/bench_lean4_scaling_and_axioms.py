#!/usr/bin/env python3
"""
Real-kernel Lean 4.34.1 scaling, cutpoint-explosion, target-vs-theory tactic/axiom
budget, and Statement-Origin Separation benchmark suite.

Every measurement invokes the pinned Lean 4.34.1 binary synchronously
(`-DElab.async=false -Ddebug.skipKernelTC=false -j1 -M2048`) wrapped in
`~/.local/bin/anneal-lean-run` and `/usr/bin/time -v`, plus a standalone
`trustLevel := 0, loadExts := false` kernel replay pass (`base.toKernelEnv.replay`).
Uses `tempfile.TemporaryDirectory()` so zero temporary files leak into `/tmp`.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
RUN = Path.home() / ".local/bin/anneal-lean-run"


def run_timed_lean(args, env, timeout=120):
    """Run Lean wrapped in /usr/bin/time -v (inside the outer anneal-lean-run cgroup scope)."""
    cmd = ["/usr/bin/time", "-v", str(LEAN)] + args
    t0 = time.perf_counter()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=timeout)
        wall = time.perf_counter() - t0
        timed_out = False
        rc = r.returncode
        stdout = r.stdout
        stderr = r.stderr
    except subprocess.TimeoutExpired as e:
        wall = time.perf_counter() - t0
        timed_out = True
        rc = -1
        stdout = (e.stdout or b"").decode("utf-8", errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = (e.stderr or b"").decode("utf-8", errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")

    user_s = sys_s = None
    max_rss_kb = None
    for line in stderr.splitlines():
        if "User time (seconds):" in line:
            user_s = float(line.split(":")[-1].strip())
        elif "System time (seconds):" in line:
            sys_s = float(line.split(":")[-1].strip())
        elif "Maximum resident set size (kbytes):" in line:
            max_rss_kb = int(line.split(":")[-1].strip())
    return {
        "rc": rc,
        "timed_out": timed_out,
        "wall_s": round(wall, 4),
        "cpu_s": round((user_s or 0.0) + (sys_s or 0.0), 4) if user_s is not None else None,
        "rss_mb": round(max_rss_kb / 1024.0, 2) if max_rss_kb is not None else None,
        "stdout": stdout,
        "stderr_tail": "\n".join(stderr.splitlines()[-12:]),
    }


REPLAY_SCRIPT_TEMPLATE = """import Lean
import Lean.Replay

open Lean

def loadBase (baseStr : String) : IO (Environment × NameSet) := do
  let base ← importModules #[{ module := baseStr.toName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let base := base.setExporting false
  let mut mods : NameSet := {}
  for m in base.header.modules do
    mods := mods.insert m.module
  return (base, mods)

def auditOne (bases : Std.HashMap String (Environment × NameSet))
    (modStr thmStr baseStr : String) : IO Unit := do
  let some (base, baseMods) := bases.get? baseStr
    | throw <| IO.userError s!"unknown base {baseStr}"
  let modName := modStr.toName
  let thmName := thmStr.toName
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := modName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (m, md) in env.header.modules.zip env.header.moduleData do
    if !baseMods.contains m.module then
      for (n, ci) in md.constNames.zip md.constants do
        newConsts := newConsts.insert n ci
  let t1 ← IO.monoMsNow
  let replayed ← base.toKernelEnv.replay newConsts
  let t2 ← IO.monoMsNow
  if (replayed.find? thmName).isNone then
    throw <| IO.userError s!"theorem {thmName} absent after kernel replay"
  -- Collect transitive axioms across full private proof terms
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut stack : List Name := [thmName]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if !visited.contains c then
        visited := visited.insert c
        match env.find? c with
        | some (.axiomInfo _) => axioms := axioms.push c
        | some ci =>
          for d in ci.getUsedConstantsAsSet do
            if !visited.contains d then
              stack := d :: stack
        | none => pure ()
  -- Statement vs proof-body origin separation check (asserting real private proof body!)
  let mut typeHints : Array Name := #[]
  let mut valHints : Array Name := #[]
  let mut hasDummy : Bool := false
  match env.find? thmName with
  | some ci =>
    for d in ci.type.getUsedConstants do
      if d.toString.startsWith "UntrustedHints" then
        typeHints := typeHints.push d
    match ci.value? (allowOpaque := true) with
    | some v =>
      for d in v.getUsedConstants do
        if d.toString == "_inhabitedExprDummy" then
          hasDummy := true
        if d.toString.startsWith "UntrustedHints" then
          valHints := valHints.push d
    | none => throw <| IO.userError s!"theorem {thmName} missing proof body"
  | none => throw <| IO.userError s!"missing theorem {thmName}"
  if hasDummy then
    throw <| IO.userError s!"theorem {thmName} proof body collapsed to _inhabitedExprDummy"
  let axSorted := axioms.qsort (fun a b => a.toString < b.toString)
  IO.println s!"REPLAY_OK mod={modStr} import_ms={t1 - t0} replay_ms={t2 - t1} replayed_consts={newConsts.size} axioms={axSorted.toList} type_hints={typeHints.size} val_hints={valHints.size}"

def main (args : List String) : IO Unit := do
  let [jobsPath] := args | throw <| IO.userError "usage: ReplayAudit <jobs.txt>"
  let raw ← IO.FS.readFile jobsPath
  let lines := (raw.splitOn "\\n").filter (fun (s : String) => !s.isEmpty)
  let mut bases : Std.HashMap String (Environment × NameSet) := {}
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 3 then
      let b := parts[2]!
      if !bases.contains b then
        let pair ← loadBase b
        bases := bases.insert b pair
  for l in lines do
    let parts := l.splitOn " "
    if parts.length == 3 then
      try
        auditOne bases parts[0]! parts[1]! parts[2]!
      catch e =>
        IO.println s!"REPLAY_ERR mod={parts[0]!} err={e}"
"""


def gen_spill_code_items(n_insns):
    """Generate n_insns (multiple of 4) alternating register arithmetic + stack spills/reloads."""
    assert n_insns % 4 == 0
    items = []
    for k in range(n_insns // 4):
        slot = k % 4
        imm = (k % 17) + 1
        items.append(f".addImm .rax {imm}#64")
        items.append(f".spillStore {slot} .rax")
        items.append(f".xorReg .rdi .rax")
        items.append(f".spillLoad .rax {slot}")
    return items


def gen_spill_direct_sym(mod_name, n_insns):
    """Regime A: Direct symbolic stepping over MState.mem without chunking or SSA lifting."""
    items = gen_spill_code_items(n_insns)
    code_list = ",\n    ".join(items)
    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import MachineLiftBase",
        "",
        f"namespace {mod_name}",
        "open MachineLift",
        "",
        "def spillCode : List Instr := [",
        f"    {code_list}",
        "  ]",
        "def spillImg : ObjImage := { code := spillCode, rodata := [] }",
        "",
        f"theorem direct_sym_{n_insns} (s : MState)",
        "    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false)",
        "    (hdist : StackSlotsDistinct 4 (s.regs .rsp)) :",
        f"    let sf := run spillImg {n_insns} s",
        f"    sf.pc = {n_insns} ∧ sf.halted = false ∧ sf.fault = false ∧",
        "    sf.regs .rsp = s.regs .rsp ∧",
        "    (∀ addr, (∀ off, off < 4 → addr ≠ stackSlotAddr s off) → sf.mem addr = s.mem addr) := by",
        "  have h_all : ∀ (st : MState), st.pc = 0 → st.halted = false → st.fault = false →",
        "      StackSlotsDistinct 4 (st.regs .rsp) →",
        f"      (run spillImg {n_insns} st).pc = {n_insns} ∧ (run spillImg {n_insns} st).halted = false ∧",
        f"      (run spillImg {n_insns} st).fault = false ∧ (run spillImg {n_insns} st).regs .rsp = st.regs .rsp ∧",
        f"      (∀ addr, (∀ off, off < 4 → addr ≠ stackSlotAddr st off) → (run spillImg {n_insns} st).mem addr = st.mem addr) := by",
        "    intro st h0_pc h0_nh h0_nf h0_dist",
    ]
    # Emit explicit per-instruction stepping chain (mirroring s2n-bignum / LNSym direct stepping)
    # Using s_k concrete intermediate MState steps linked via step_* lemmas.
    prev = "st"
    for i in range(n_insns):
        nxt = f"s_{i+1}"
        kind = i % 4
        slot = (i // 4) % 4
        imm = ((i // 4) % 17) + 1
        pc_hyp = "h0_pc" if i == 0 else "rfl"
        if kind == 0:
            lines.append(f"    let {nxt} : MState := {{ {prev} with pc := {i+1}, regs := regUpd {prev}.regs .rax ({prev}.regs .rax + {imm}#64) }}")
            if i == 0:
                lines.append(f"    have hst_{i} : step spillImg {prev} = {nxt} := by")
                lines.append(f"      have t := step_addImm (img := spillImg) (s := {prev}) h0_nh h0_nf (by rw [h0_pc]; rfl)")
                lines.append(f"      rw [h0_pc] at t; exact t")
            else:
                lines.append(f"    have hst_{i} : step spillImg {prev} = {nxt} := step_addImm (img := spillImg) (s := {prev}) h0_nh h0_nf rfl")
        elif kind == 1:
            lines.append(f"    let {nxt} : MState := {{ {prev} with pc := {i+1}, mem := memUpd {prev}.mem (stackSlotAddr {prev} {slot}) ({prev}.regs .rax) }}")
            lines.append(f"    have hst_{i} : step spillImg {prev} = {nxt} := step_spillStore (img := spillImg) (s := {prev}) h0_nh h0_nf rfl")
        elif kind == 2:
            lines.append(f"    let {nxt} : MState := {{ {prev} with pc := {i+1}, regs := regUpd {prev}.regs .rdi ({prev}.regs .rdi ^^^ {prev}.regs .rax) }}")
            lines.append(f"    have hst_{i} : step spillImg {prev} = {nxt} := step_xorReg (img := spillImg) (s := {prev}) h0_nh h0_nf rfl")
        else:
            lines.append(f"    let {nxt} : MState := {{ {prev} with pc := {i+1}, regs := regUpd {prev}.regs .rax ({prev}.mem (stackSlotAddr {prev} {slot})) }}")
            lines.append(f"    have hst_{i} : step spillImg {prev} = {nxt} := step_spillLoad (img := spillImg) (s := {prev}) h0_nh h0_nf rfl")
        prev = nxt
    # Chain run_succ across all n_insns
    lines.append(f"    have hrun : run spillImg {n_insns} st = {prev} := by")
    # Chunk rewrites in groups of 20 inside the same theorem
    for start in range(0, n_insns, 20):
        end = min(start + 20, n_insns)
        rws = ", ".join(f"run_succ, hst_{j}" for j in range(start, end))
        lines.append(f"      rw [{rws}]")
    lines.append("      rfl")
    lines.append("    rw [hrun]")
    # Prove rsp preserved and heap untouched by peeling back each step
    lines.append("    have hr0 : st.regs .rsp = st.regs .rsp := rfl")
    for i in range(n_insns):
        kind = i % 4
        cur = "st" if i == 0 else f"s_{i}"
        nxt = f"s_{i+1}"
        if kind == 1:
            lines.append(f"    have hr{i+1} : {nxt}.regs .rsp = st.regs .rsp := hr{i}")
        elif i == 0:
            lines.append(f"    have hr{i+1} : {nxt}.regs .rsp = st.regs .rsp := by dsimp only [{nxt}]; exact regUpd_ne _ (by decide) _")
        else:
            lines.append(f"    have hr{i+1} : {nxt}.regs .rsp = st.regs .rsp := by dsimp only [{nxt}]; rw [regUpd_ne _ (by decide)]; exact hr{i}")
    lines.append(f"    refine ⟨rfl, h0_nh, h0_nf, hr{n_insns}, ?_⟩")
    lines.append("    intro addr haddr")
    lines.append("    have hm0 : st.mem addr = st.mem addr := rfl")
    for i in range(n_insns):
        kind = i % 4
        slot = (i // 4) % 4
        cur = "st" if i == 0 else f"s_{i}"
        nxt = f"s_{i+1}"
        if kind != 1:
            lines.append(f"    have hm{i+1} : {nxt}.mem addr = st.mem addr := hm{i}")
        else:
            lines.append(f"    have hm{i+1} : {nxt}.mem addr = st.mem addr := by")
            lines.append(f"      dsimp only [{nxt}]")
            lines.append(f"      have hslot : stackSlotAddr {cur} {slot} = stackSlotAddr st {slot} := stackSlotAddr_eq_of_rsp_eq hr{i} {slot}")
            if i == 1:
                lines.append(f"      rw [hslot]; exact memUpd_ne _ (haddr {slot} (by decide)) _")
            else:
                lines.append(f"      rw [hslot, memUpd_ne _ (haddr {slot} (by decide))]; exact hm{i}")
    lines.append(f"    exact hm{n_insns}")
    lines.append("  exact h_all s hpc hnh hnf hdist")
    lines.append(f"end {mod_name}")
    return "\n".join(lines) + "\n"


def gen_spill_cutpoint(mod_name, n_insns, chunk=20):
    """Regime B: Optimized Cutpoint symbolic execution (CutBox per 20-insn window +
    opaque existential spine per instruction so nested `let` zeta-blowup is eliminated)."""
    assert n_insns % chunk == 0
    items = gen_spill_code_items(n_insns)
    code_list = ",\n    ".join(items)
    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import MachineLiftBase",
        "",
        f"namespace {mod_name}",
        "open MachineLift",
        "",
        "def spillCode : List Instr := [",
        f"    {code_list}",
        "  ]",
        "def spillImg : ObjImage := { code := spillCode, rodata := [] }",
        "",
        "def CutInv (pc : Nat) (rsp0 : BitVec 64) (mem0 : BitVec 64 → BitVec 64) (s : MState) : Prop :=",
        "  CutBox pc (s.pc = pc ∧ s.halted = false ∧ s.fault = false ∧ s.regs .rsp = rsp0 ∧",
        "    (∀ addr, (∀ off, off < 4 → addr ≠ rsp0 + BitVec.ofNat 64 (off * 8)) → s.mem addr = mem0 addr))",
        "",
        "theorem cut_step_addImm {pc : Nat} {dst : Reg} {imm : BitVec 64} {rsp0 : BitVec 64}",
        "    {mem0 : BitVec 64 → BitVec 64} {st : MState}",
        "    (hc : listGet? spillImg.code pc = some (.addImm dst imm)) (hnr : dst ≠ .rsp)",
        "    (hin : CutInv pc rsp0 mem0 st) : CutInv (pc + 1) rsp0 mem0 (step spillImg st) := by",
        "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp, hmem⟩",
        "  rw [step_addImm hnh hnf (by rw [hpc]; exact hc), hpc]",
        "  refine CutBox.mk ⟨rfl, hnh, hnf, ?_, hmem⟩",
        "  dsimp only; rw [regUpd_ne _ (fun h => hnr h.symm), hrsp]",
        "",
        "theorem cut_step_xorReg {pc : Nat} {dst src : Reg} {rsp0 : BitVec 64}",
        "    {mem0 : BitVec 64 → BitVec 64} {st : MState}",
        "    (hc : listGet? spillImg.code pc = some (.xorReg dst src)) (hnr : dst ≠ .rsp)",
        "    (hin : CutInv pc rsp0 mem0 st) : CutInv (pc + 1) rsp0 mem0 (step spillImg st) := by",
        "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp, hmem⟩",
        "  rw [step_xorReg hnh hnf (by rw [hpc]; exact hc), hpc]",
        "  refine CutBox.mk ⟨rfl, hnh, hnf, ?_, hmem⟩",
        "  dsimp only; rw [regUpd_ne _ (fun h => hnr h.symm), hrsp]",
        "",
        "theorem cut_step_spillStore {pc off : Nat} {src : Reg} {rsp0 : BitVec 64}",
        "    {mem0 : BitVec 64 → BitVec 64} {st : MState}",
        "    (hc : listGet? spillImg.code pc = some (.spillStore off src)) (hoff : off < 4)",
        "    (hin : CutInv pc rsp0 mem0 st) : CutInv (pc + 1) rsp0 mem0 (step spillImg st) := by",
        "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp, hmem⟩",
        "  rw [step_spillStore hnh hnf (by rw [hpc]; exact hc), hpc]",
        "  refine CutBox.mk ⟨rfl, hnh, hnf, hrsp, ?_⟩",
        "  intro addr haddr; dsimp only [stackSlotAddr]; rw [hrsp, memUpd_ne _ (haddr off hoff)]; exact hmem addr haddr",
        "",
        "theorem cut_step_spillLoad {pc off : Nat} {dst : Reg} {rsp0 : BitVec 64}",
        "    {mem0 : BitVec 64 → BitVec 64} {st : MState}",
        "    (hc : listGet? spillImg.code pc = some (.spillLoad dst off)) (hnr : dst ≠ .rsp)",
        "    (hin : CutInv pc rsp0 mem0 st) : CutInv (pc + 1) rsp0 mem0 (step spillImg st) := by",
        "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp, hmem⟩",
        "  rw [step_spillLoad hnh hnf (by rw [hpc]; exact hc), hpc]",
        "  refine CutBox.mk ⟨rfl, hnh, hnf, ?_, hmem⟩",
        "  dsimp only; rw [regUpd_ne _ (fun h => hnr h.symm), hrsp]",
        "",
    ]
    n_chunks = n_insns // chunk
    for c in range(n_chunks):
        base_pc = c * chunk
        end_pc = base_pc + chunk
        lines.append(f"theorem cut_chunk_{c} (rsp0 : BitVec 64) (mem0 : BitVec 64 → BitVec 64) (st : MState)")
        lines.append(f"    (hin : CutInv {base_pc} rsp0 mem0 st) :")
        lines.append(f"    CutInv {end_pc} rsp0 mem0 (run spillImg {chunk} st) := by")
        lines.append(f"  have h0 : CutInv {base_pc} rsp0 mem0 st := hin")
        cur_expr = "st"
        for off_i in range(chunk):
            i = base_pc + off_i
            kind = i % 4
            if kind == 0:
                lines.append(f"  have h{off_i+1} := cut_step_addImm (pc := {i}) rfl (by decide) h{off_i}")
            elif kind == 1:
                lines.append(f"  have h{off_i+1} := cut_step_spillStore (pc := {i}) rfl (by decide) h{off_i}")
            elif kind == 2:
                lines.append(f"  have h{off_i+1} := cut_step_xorReg (pc := {i}) rfl (by decide) h{off_i}")
            else:
                lines.append(f"  have h{off_i+1} := cut_step_spillLoad (pc := {i}) rfl (by decide) h{off_i}")
        lines.append(f"  exact h{chunk}")
        lines.append("")

    # Top-level composition theorem
    lines.append(f"theorem cutpoint_{n_insns} (s : MState)")
    lines.append("    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false) :")
    lines.append(f"    let sf := run spillImg {n_insns} s")
    lines.append(f"    sf.pc = {n_insns} ∧ sf.halted = false ∧ sf.fault = false ∧")
    lines.append("    sf.regs .rsp = s.regs .rsp ∧")
    lines.append("    (∀ addr, (∀ off, off < 4 → addr ≠ stackSlotAddr s off) → sf.mem addr = s.mem addr) := by")
    lines.append("  have hc0 : CutInv 0 (s.regs .rsp) s.mem (run spillImg 0 s) :=")
    lines.append("    CutBox.mk ⟨hpc, hnh, hnf, rfl, fun _ _ => rfl⟩")
    for c in range(n_chunks):
        prev_n = c * chunk
        nxt_n = (c + 1) * chunk
        lines.append(f"  have hc{c+1} : CutInv {nxt_n} (s.regs .rsp) s.mem (run spillImg {nxt_n} s) := by")
        lines.append(f"    have hadd : run spillImg {nxt_n} s = run spillImg {chunk} (run spillImg {prev_n} s) := run_add spillImg {prev_n} {chunk} s")
        lines.append(f"    rw [hadd]; exact cut_chunk_{c} (s.regs .rsp) s.mem (run spillImg {prev_n} s) hc{c}")
    lines.append(f"  exact hc{n_chunks}.val")
    lines.append(f"end {mod_name}")
    return "\n".join(lines) + "\n"


def gen_spill_cert_lift(mod_name, n_insns):
    """Regime C: Certified O(N) lifting (`checkDropLift_sound`) to pure functional SSA IR."""
    items = gen_spill_code_items(n_insns)
    code_list = ",\n    ".join(items)
    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import MachineLiftBase",
        "",
        f"namespace {mod_name}",
        "open MachineLift",
        "",
        "def spillCode : List Instr := [",
        f"    {code_list}",
        "  ]",
        "def spillImg : ObjImage := { code := spillCode, rodata := [] }",
        "",
        "theorem check_lift_ok : checkDropLift 4 spillCode spillCode = true := rfl",
        f"theorem code_len_ok : spillCode.length = {n_insns} := rfl",
        "",
        f"theorem cert_lift_{n_insns} (s : MState)",
        "    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false)",
        "    (hdist : StackSlotsDistinct 4 (s.regs .rsp)) :",
        f"    let sf := run spillImg {n_insns} s",
        f"    sf.pc = {n_insns} ∧ sf.halted = false ∧ sf.fault = false ∧",
        "    sf.regs .rsp = s.regs .rsp ∧",
        "    (∀ addr, (∀ off, off < 4 → addr ≠ stackSlotAddr s off) → sf.mem addr = s.mem addr) := by",
        "  let l0 : LiftedState := { regs := s.regs, slots := fun off => s.mem (stackSlotAddr s off) }",
        "  have habs0 : AbstractsFrame 4 s l0 := ⟨hnh, hnf, fun _ => rfl, fun _ _ => rfl⟩",
        "  have hdrop : listDrop s.pc spillImg.code = spillCode := by rw [hpc]; rfl",
        "  have h := checkDropLift_sound (maxSlots := 4) (img := spillImg) spillCode spillCode s l0 hdrop check_lift_ok hdist habs0",
        "  rw [code_len_ok] at h",
        "  dsimp only",
        "  refine ⟨by rw [h.1, hpc, Nat.zero_add], h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1⟩",
        f"end {mod_name}",
    ]
    return "\n".join(lines) + "\n"


def build_balanced_tree_expr(leaves):
    """Build balanced CodeTree expression + per-leaf (TreePath expr, base_pc, length)."""
    # leaves: list of (idx, length)
    if len(leaves) == 1:
        idx, length = leaves[0]
        return f".leaf blk_{idx}", length, {idx: (".here", 0, length)}
    mid = len(leaves) // 2
    l_expr, l_size, l_paths = build_balanced_tree_expr(leaves[:mid])
    r_expr, r_size, r_paths = build_balanced_tree_expr(leaves[mid:])
    paths = {}
    for idx, (p, base, length) in l_paths.items():
        paths[idx] = (f".goLeft ({p})", base, length)
    for idx, (p, base, length) in r_paths.items():
        paths[idx] = (f".goRight ({p})", l_size + base, length)
    return f".node {l_size} ({l_expr}) ({r_expr})", l_size + r_size, paths


def gen_spill_sharded_tree_lift(mod_name, n_insns, leaf_size=64):
    """Regime D: Sharded balanced-CodeTree certified lifting (<=64-insn leaves, O(log B) lookup).
    Breaks the flat-List `maxRecDepth = 512` cliff and scales linearly to 5,000+ instructions
    with zero `set_option` overrides."""
    items = gen_spill_code_items(n_insns)
    chunks = [items[i:i + leaf_size] for i in range(0, len(items), leaf_size)]
    leaf_meta = [(k, len(ch)) for k, ch in enumerate(chunks)]
    tree_expr, total_sz, paths = build_balanced_tree_expr(leaf_meta)
    assert total_sz == n_insns

    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import MachineLiftBase",
        "",
        f"namespace {mod_name}",
        "open MachineLift",
        "",
    ]
    for k, ch in enumerate(chunks):
        body = ", ".join(ch)
        lines.append(f"def blk_{k} : List Instr := [{body}]")
    lines += [
        "",
        f"def treeCode : CodeTree := {tree_expr}",
        "def treeImg : TreeObjImage := { code := treeCode, rodata := [] }",
        "",
        "def CutTreeInv (pc : Nat) (rsp0 : BitVec 64) (mem0 : BitVec 64 → BitVec 64) (s : MState) : Prop :=",
        "  CutBox pc (s.pc = pc ∧ s.halted = false ∧ s.fault = false ∧ s.regs .rsp = rsp0 ∧",
        "    (∀ addr, (∀ slot, slot < 4 → addr ≠ rsp0 + BitVec.ofNat 64 (slot * 8)) → s.mem addr = mem0 addr))",
        "",
        "theorem cut_tree_leaf {p : TreePath} {base len : Nat} {blk : List Instr}",
        "    {rsp0 : BitVec 64} {mem0 : BitVec 64 → BitVec 64} {st : MState}",
        "    (hchk : checkLeafAt 4 treeImg.code p base blk = true)",
        "    (hlen : blk.length = len)",
        "    (hdist : StackSlotsDistinct 4 rsp0)",
        "    (hin : CutTreeInv base rsp0 mem0 st) :",
        "    CutTreeInv (base + len) rsp0 mem0 (runTree treeImg len st) := by",
        "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp, hmem⟩",
        "  have hdist' : StackSlotsDistinct 4 (st.regs .rsp) := by rw [hrsp]; exact hdist",
        "  have h := checkTreeLeaf_sound (maxSlots := 4) (img := treeImg) p base blk st hchk hpc hnh hnf hdist'",
        "  rw [hlen] at h",
        "  refine CutBox.mk ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩",
        "  · rw [h.2.2.2.1, hrsp]",
        "  · intro addr haddr",
        "    have haddr' : ∀ slot, slot < 4 → addr ≠ stackSlotAddr st slot := by",
        "      intro slot hslot; dsimp only [stackSlotAddr]; rw [hrsp]; exact haddr slot hslot",
        "    rw [h.2.2.2.2 addr haddr', hmem addr haddr]",
        "",
    ]
    for k, ch in enumerate(chunks):
        p_expr, base_pc, length = paths[k]
        lines.append(f"theorem chk_leaf_{k} : checkLeafAt 4 treeImg.code ({p_expr}) {base_pc} blk_{k} = true := rfl")
        lines.append(f"theorem len_leaf_{k} : blk_{k}.length = {length} := rfl")

    lines += [
        "",
        f"theorem sharded_tree_{n_insns} (s : MState)",
        "    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false)",
        "    (hdist : StackSlotsDistinct 4 (s.regs .rsp)) :",
        f"    let sf := runTree treeImg {n_insns} s",
        f"    sf.pc = {n_insns} ∧ sf.halted = false ∧ sf.fault = false ∧",
        "    sf.regs .rsp = s.regs .rsp ∧",
        "    (∀ addr, (∀ off, off < 4 → addr ≠ stackSlotAddr s off) → sf.mem addr = s.mem addr) := by",
        "  have hc0 : CutTreeInv 0 (s.regs .rsp) s.mem (runTree treeImg 0 s) :=",
        "    CutBox.mk ⟨hpc, hnh, hnf, rfl, fun _ _ => rfl⟩",
    ]
    for k, ch in enumerate(chunks):
        _, base_pc, length = paths[k]
        end_pc = base_pc + length
        lines.append(f"  have hc{k+1} : CutTreeInv {end_pc} (s.regs .rsp) s.mem (runTree treeImg {end_pc} s) := by")
        lines.append(f"    have hadd : runTree treeImg {end_pc} s = runTree treeImg {length} (runTree treeImg {base_pc} s) := runTree_add treeImg {base_pc} {length} s")
        lines.append(f"    rw [hadd]; exact cut_tree_leaf chk_leaf_{k} len_leaf_{k} hdist hc{k}")
    lines.append(f"  exact hc{len(chunks)}.val")
    lines.append(f"end {mod_name}")
    return "\n".join(lines) + "\n"


def gen_branch_diamonds(mod_name, b_count, use_cutpoints):
    """Experiment 2: B sequential branch diamonds (2^B paths without cutpoints vs O(B) with cutpoints)."""
    # Each diamond d in 0..B-1 occupies 4 PCs:
    # 4d+0: jzBit0 .rdi (4d+3)
    # 4d+1: addImm .rax 1#64
    # 4d+2: jmp (4d+4)
    # 4d+3: addImm .rax 2#64
    # Final PC 4B: ret
    # Notice each diamond takes either 3 steps (fall-through: jzBit0, addImm 1, jmp) or 2 steps (taken: jzBit0, addImm 2)!
    # Even simpler uniform step count (both arms 3 steps) so run fuel is exact 3*B:
    # 4d+0: jzBit0 .rdi (4d+2)   [fall->+1, taken->+2]
    # 4d+1: addImm .rax 1#64     -> jumps? Better: 5 PCs per diamond:
    # 5d+0: jzBit0 .rdi (5d+3)
    # 5d+1: addImm .rax 1#64
    # 5d+2: jmp (5d+5)
    # 5d+3: addImm .rax 2#64
    # 5d+4: jmp (5d+5)
    # Both arms take EXACTLY 3 steps to reach 5d+5!
    insns = []
    for d in range(b_count):
        base = 5 * d
        insns.append(f".jzBit0 .rdi {base + 3}")
        insns.append(f".addImm .rax 1#64")
        insns.append(f".jmp {base + 5}")
        insns.append(f".addImm .rax 2#64")
        insns.append(f".jmp {base + 5}")
    insns.append(".ret")
    code_list = ",\n    ".join(insns)
    total_steps = 3 * b_count
    lines = [
        "prelude",
        "import Init.Core",
        "import Init.Data.BitVec.Basic",
        "import Init.Data.BitVec.Lemmas",
        "import Init.Data.List.Basic",
        "import Init.Data.Nat.Basic",
        "import MachineLiftBase",
        "",
        f"namespace {mod_name}",
        "open MachineLift",
        "",
        "def diaCode : List Instr := [",
        f"    {code_list}",
        "  ]",
        "def diaImg : ObjImage := { code := diaCode, rodata := [] }",
        "",
    ]
    if not use_cutpoints:
        # Un-cutpointed symbolic execution: splits on every branch without merging -> 2^B leaf subgoals!
        lines += [
            f"theorem uncut_diamonds_{b_count} (s : MState)",
            "    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false) :",
            f"    let sf := run diaImg {total_steps} s",
            f"    sf.pc = {5 * b_count} ∧ sf.halted = false ∧ sf.fault = false ∧ sf.regs .rsp = s.regs .rsp := by",
            "  dsimp only",
        ]
        # Helper recursive tactic via explicit cases generating 2^B branches
        def emit_split(depth, state_var, indent):
            if depth == b_count:
                lines.append(f"{indent}exact ⟨rfl, hnh, hnf, rfl⟩")
                return
            base = 5 * depth
            pc_eq = "hpc" if depth == 0 else "rfl"
            rem = 3 * (b_count - depth)
            rem_next = rem - 3
            lines.append(f"{indent}cases hb_{depth} : (({state_var}.regs .rdi &&& 1#64) == 0#64) with")
            # Taken arm
            lines.append(f"{indent}| true =>")
            ind2 = indent + "  "
            lines.append(f"{ind2}have hs0 : step diaImg {state_var} = {{ {state_var} with pc := {base+3} }} := by")
            if depth == 0:
                lines.append(f"{ind2}  exact step_jzBit0_taken (img := diaImg) (s := {state_var}) hnh hnf (by rw [hpc]; rfl) hb_{depth}")
            else:
                lines.append(f"{ind2}  exact step_jzBit0_taken (img := diaImg) (s := {state_var}) hnh hnf rfl hb_{depth}")
            lines.append(f"{ind2}let t1_{depth} : MState := {{ {state_var} with pc := {base+3} }}")
            lines.append(f"{ind2}let t2_{depth} : MState := {{ t1_{depth} with pc := {base+4}, regs := regUpd t1_{depth}.regs .rax (t1_{depth}.regs .rax + 2#64) }}")
            lines.append(f"{ind2}have hs1 : step diaImg t1_{depth} = t2_{depth} := step_addImm (img := diaImg) (s := t1_{depth}) hnh hnf rfl")
            lines.append(f"{ind2}let t3_{depth} : MState := {{ t2_{depth} with pc := {base+5} }}")
            lines.append(f"{ind2}have hs2 : step diaImg t2_{depth} = t3_{depth} := step_jmp (img := diaImg) (s := t2_{depth}) hnh hnf rfl")
            lines.append(f"{ind2}have hr : run diaImg {rem} {state_var} = run diaImg {rem_next} t3_{depth} := by")
            lines.append(f"{ind2}  rw [run_succ, hs0]; change run diaImg {rem-1} t1_{depth} = _; rw [run_succ, hs1, run_succ, hs2]")
            lines.append(f"{ind2}rw [hr]")
            lines.append(f"{ind2}have hrsp_{depth} : t3_{depth}.regs .rsp = {state_var}.regs .rsp := by dsimp [t3_{depth}, t2_{depth}, t1_{depth}]; exact regUpd_ne _ (by decide) _")
            if depth == b_count - 1:
                lines.append(f"{ind2}rw [run_zero]")
                lines.append(f"{ind2}refine ⟨rfl, hnh, hnf, ?_⟩")
                rws = ", ".join(f"hrsp_{k}" for k in range(b_count - 1, -1, -1))
                lines.append(f"{ind2}rw [{rws}]")
            else:
                emit_split(depth + 1, f"t3_{depth}", ind2)
            # Fall-through arm
            lines.append(f"{indent}| false =>")
            lines.append(f"{ind2}have hs0 : step diaImg {state_var} = {{ {state_var} with pc := {base+1} }} := by")
            if depth == 0:
                lines.append(f"{ind2}  have t := step_jzBit0_fall (img := diaImg) (s := {state_var}) hnh hnf (by rw [hpc]; rfl) hb_{depth}")
                lines.append(f"{ind2}  rw [hpc] at t; exact t")
            else:
                lines.append(f"{ind2}  exact step_jzBit0_fall (img := diaImg) (s := {state_var}) hnh hnf rfl hb_{depth}")
            lines.append(f"{ind2}let f1_{depth} : MState := {{ {state_var} with pc := {base+1} }}")
            lines.append(f"{ind2}let f2_{depth} : MState := {{ f1_{depth} with pc := {base+2}, regs := regUpd f1_{depth}.regs .rax (f1_{depth}.regs .rax + 1#64) }}")
            lines.append(f"{ind2}have hs1 : step diaImg f1_{depth} = f2_{depth} := step_addImm (img := diaImg) (s := f1_{depth}) hnh hnf rfl")
            lines.append(f"{ind2}let f3_{depth} : MState := {{ f2_{depth} with pc := {base+5} }}")
            lines.append(f"{ind2}have hs2 : step diaImg f2_{depth} = f3_{depth} := step_jmp (img := diaImg) (s := f2_{depth}) hnh hnf rfl")
            lines.append(f"{ind2}have hr : run diaImg {rem} {state_var} = run diaImg {rem_next} f3_{depth} := by")
            lines.append(f"{ind2}  rw [run_succ, hs0]; change run diaImg {rem-1} f1_{depth} = _; rw [run_succ, hs1, run_succ, hs2]")
            lines.append(f"{ind2}rw [hr]")
            lines.append(f"{ind2}have hrsp_{depth} : f3_{depth}.regs .rsp = {state_var}.regs .rsp := by dsimp [f3_{depth}, f2_{depth}, f1_{depth}]; exact regUpd_ne _ (by decide) _")
            if depth == b_count - 1:
                lines.append(f"{ind2}rw [run_zero]")
                lines.append(f"{ind2}refine ⟨rfl, hnh, hnf, ?_⟩")
                rws = ", ".join(f"hrsp_{k}" for k in range(b_count - 1, -1, -1))
                lines.append(f"{ind2}rw [{rws}]")
            else:
                emit_split(depth + 1, f"f3_{depth}", ind2)
        emit_split(0, "s", "  ")
    else:
        # Cutpoint-merged O(B): one linear lemma per diamond joined by CutBox + run_add
        lines += [
            "def DiaCut (pc : Nat) (rsp0 : BitVec 64) (s : MState) : Prop :=",
            "  CutBox pc (s.pc = pc ∧ s.halted = false ∧ s.fault = false ∧ s.regs .rsp = rsp0)",
            "",
        ]
        for d in range(b_count):
            base = 5 * d
            lines += [
                f"theorem dia_cut_{d} (rsp0 : BitVec 64) (st : MState) (hin : DiaCut {base} rsp0 st) :",
                f"    DiaCut {base + 5} rsp0 (run diaImg 3 st) := by",
                "  rcases hin.val with ⟨hpc, hnh, hnf, hrsp⟩",
                "  cases hb : ((st.regs .rdi &&& 1#64) == 0#64) with",
                "  | true =>",
                f"    let s1 : MState := {{ st with pc := {base+3} }}",
                f"    have hs0 : step diaImg st = s1 := step_jzBit0_taken (img := diaImg) (s := st) hnh hnf (by rw [hpc]; rfl) hb",
                f"    let s2 : MState := {{ s1 with pc := {base+4}, regs := regUpd s1.regs .rax (s1.regs .rax + 2#64) }}",
                f"    have hs1 : step diaImg s1 = s2 := step_addImm (img := diaImg) (s := s1) hnh hnf rfl",
                f"    let s3 : MState := {{ s2 with pc := {base+5} }}",
                f"    have hs2 : step diaImg s2 = s3 := step_jmp (img := diaImg) (s := s2) hnh hnf rfl",
                "    rw [run_succ, hs0, run_succ, hs1, run_succ, hs2, run_zero]",
                "    refine CutBox.mk ⟨rfl, hnh, hnf, ?_⟩",
                "    dsimp [s3, s2, s1]; rw [regUpd_ne _ (by decide)]; exact hrsp",
                "  | false =>",
                f"    let s1 : MState := {{ st with pc := {base+1} }}",
                f"    have hs0 : step diaImg st = s1 := by",
                f"      have t := step_jzBit0_fall (img := diaImg) (s := st) hnh hnf (by rw [hpc]; rfl) hb",
                f"      rw [hpc] at t; exact t",
                f"    let s2 : MState := {{ s1 with pc := {base+2}, regs := regUpd s1.regs .rax (s1.regs .rax + 1#64) }}",
                f"    have hs1 : step diaImg s1 = s2 := step_addImm (img := diaImg) (s := s1) hnh hnf rfl",
                f"    let s3 : MState := {{ s2 with pc := {base+5} }}",
                f"    have hs2 : step diaImg s2 = s3 := step_jmp (img := diaImg) (s := s2) hnh hnf rfl",
                "    rw [run_succ, hs0, run_succ, hs1, run_succ, hs2, run_zero]",
                "    refine CutBox.mk ⟨rfl, hnh, hnf, ?_⟩",
                "    dsimp [s3, s2, s1]; rw [regUpd_ne _ (by decide)]; exact hrsp",
                "",
            ]
        lines += [
            f"theorem cut_diamonds_{b_count} (s : MState)",
            "    (hpc : s.pc = 0) (hnh : s.halted = false) (hnf : s.fault = false) :",
            f"    let sf := run diaImg {total_steps} s",
            f"    sf.pc = {5 * b_count} ∧ sf.halted = false ∧ sf.fault = false ∧ sf.regs .rsp = s.regs .rsp := by",
            "  have hc0 : DiaCut 0 (s.regs .rsp) (run diaImg 0 s) := CutBox.mk ⟨hpc, hnh, hnf, rfl⟩",
        ]
        for d in range(b_count):
            lines.append(f"  have hc{d+1} : DiaCut {5*(d+1)} (s.regs .rsp) (run diaImg {3*(d+1)} s) := by")
            lines.append(f"    rw [run_add diaImg {3*d} 3 s]; exact dia_cut_{d} (s.regs .rsp) (run diaImg {3*d} s) hc{d}")
        lines.append(f"  exact hc{b_count}.val")
    lines.append(f"end {mod_name}")
    return "\n".join(lines) + "\n"


def gen_tactic_budget_modules():
    """Experiment 3: 5 real tactic regimes on 4 compiled-code VCs."""
    # Common 4 VCs from real GCC 15.2.0 compiled code:
    # VC1: Stack-frame disjointness from heap buffer (64-bit Nat/BitVec range)
    # VC2: Jump-table 16-way bounds (`cmp edi, 15; ja default` -> op.toNat < 16)
    # VC3: GCC -O3 AVX2 runtime pointer-aliasing guard (`(dst - 4) - a > 24` -> dst ≠ a + 4*k for k in 0..7)
    # VC4: Stack pointer CFA round-trip `(rsp - 160) + 160 = rsp`
    mods = {}

    mods["Budget_Pass1_Explicit"] = """prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas

namespace Budget_Pass1_Explicit

theorem vc1_stack_heap_disjoint (rsp_lo rsp_hi buf_lo buf_hi addr : Nat)
    (h_sep : buf_hi ≤ rsp_lo) (h_in_buf : buf_lo ≤ addr ∧ addr < buf_hi)
    (h_in_stk : rsp_lo ≤ addr ∧ addr < rsp_hi) : False :=
  Nat.not_lt_of_ge (Nat.le_trans h_sep h_in_stk.1) h_in_buf.2

theorem vc2_jumptable_bound (op : BitVec 32) (h : ¬ (15#32 < op)) : op.toNat < 16 := by
  have hle : op ≤ 15#32 := BitVec.not_lt.mp h
  have hnat : op.toNat ≤ (15#32).toNat := BitVec.le_def.mp hle
  exact Nat.lt_succ_of_le hnat

theorem vc3_avx2_alias_lane (dst a : BitVec 64)
    (h_guard : (24#64 : BitVec 64) < (dst - 4#64) - a) :
    dst ≠ a + 4#64 := by
  intro heq
  rw [heq] at h_guard
  have h1 : a + 4#64 - 4#64 = a := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, BitVec.sub_self, BitVec.add_zero]
  rw [h1, BitVec.sub_self] at h_guard
  exact absurd h_guard (by decide)

theorem vc4_cfa_rsp_roundtrip (rsp : BitVec 64) : (rsp - 160#64) + 160#64 = rsp :=
  BitVec.sub_add_cancel rsp 160#64

theorem all_vcs (rsp_lo rsp_hi buf_lo buf_hi addr : Nat) (op : BitVec 32) (dst a rsp : BitVec 64) :
    (buf_hi ≤ rsp_lo → (buf_lo ≤ addr ∧ addr < buf_hi) → (rsp_lo ≤ addr ∧ addr < rsp_hi) → False) ∧
    (¬ (15#32 < op) → op.toNat < 16) ∧
    ((24#64 : BitVec 64) < (dst - 4#64) - a → dst ≠ a + 4#64) ∧
    ((rsp - 160#64) + 160#64 = rsp) :=
  ⟨vc1_stack_heap_disjoint rsp_lo rsp_hi buf_lo buf_hi addr,
   vc2_jumptable_bound op, vc3_avx2_alias_lane dst a, vc4_cfa_rsp_roundtrip rsp⟩

end Budget_Pass1_Explicit
"""

    mods["Budget_Target_Omega"] = """import Init

namespace Budget_Target_Omega

theorem vc1_stack_heap_disjoint (rsp_lo rsp_hi buf_lo buf_hi addr : Nat)
    (h_sep : buf_hi ≤ rsp_lo) (h_in_buf : buf_lo ≤ addr ∧ addr < buf_hi)
    (h_in_stk : rsp_lo ≤ addr ∧ addr < rsp_hi) : False := by
  omega

theorem vc2_jumptable_bound (op : BitVec 32) (h : ¬ (15#32 < op)) : op.toNat < 16 := by
  have hle : op ≤ 15#32 := BitVec.not_lt.mp h
  have hnat : op.toNat ≤ (15#32).toNat := BitVec.le_def.mp hle
  simp only [BitVec.toNat_ofNat] at hnat
  omega

theorem vc3_avx2_alias_lane (dst a : BitVec 64)
    (h_guard : (24#64 : BitVec 64) < (dst - 4#64) - a) :
    dst ≠ a + 4#64 := by
  intro heq
  subst heq
  simp only [BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h_guard
  omega

theorem vc4_cfa_rsp_roundtrip (rsp : BitVec 64) : (rsp - 160#64) + 160#64 = rsp := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem all_vcs (rsp_lo rsp_hi buf_lo buf_hi addr : Nat) (op : BitVec 32) (dst a rsp : BitVec 64) :
    (buf_hi ≤ rsp_lo → (buf_lo ≤ addr ∧ addr < buf_hi) → (rsp_lo ≤ addr ∧ addr < rsp_hi) → False) ∧
    (¬ (15#32 < op) → op.toNat < 16) ∧
    ((24#64 : BitVec 64) < (dst - 4#64) - a → dst ≠ a + 4#64) ∧
    ((rsp - 160#64) + 160#64 = rsp) :=
  ⟨vc1_stack_heap_disjoint rsp_lo rsp_hi buf_lo buf_hi addr,
   vc2_jumptable_bound op, vc3_avx2_alias_lane dst a, vc4_cfa_rsp_roundtrip rsp⟩

end Budget_Target_Omega
"""

    mods["Budget_Target_BvOmega"] = """import Init

namespace Budget_Target_BvOmega

theorem vc1_stack_heap_disjoint (rsp_lo rsp_hi buf_lo buf_hi addr : BitVec 64)
    (h_sep : buf_hi ≤ rsp_lo) (h_in_buf : buf_lo ≤ addr ∧ addr < buf_hi)
    (h_in_stk : rsp_lo ≤ addr ∧ addr < rsp_hi) : False := by
  bv_omega

theorem vc2_jumptable_bound (op : BitVec 32) (h : ¬ (15#32 < op)) : op.toNat < 16 := by
  bv_omega

theorem vc3_avx2_alias_lane (dst a : BitVec 64)
    (h_guard : (24#64 : BitVec 64) < (dst - 4#64) - a) :
    dst ≠ a + 4#64 := by
  bv_omega

theorem vc4_cfa_rsp_roundtrip (rsp : BitVec 64) : (rsp - 160#64) + 160#64 = rsp := by
  bv_omega

theorem all_vcs (rsp_lo rsp_hi buf_lo buf_hi addr : BitVec 64) (op : BitVec 32) (dst a rsp : BitVec 64) :
    (buf_hi ≤ rsp_lo → (buf_lo ≤ addr ∧ addr < buf_hi) → (rsp_lo ≤ addr ∧ addr < rsp_hi) → False) ∧
    (¬ (15#32 < op) → op.toNat < 16) ∧
    ((24#64 : BitVec 64) < (dst - 4#64) - a → dst ≠ a + 4#64) ∧
    ((rsp - 160#64) + 160#64 = rsp) :=
  ⟨vc1_stack_heap_disjoint rsp_lo rsp_hi buf_lo buf_hi addr,
   vc2_jumptable_bound op, vc3_avx2_alias_lane dst a, vc4_cfa_rsp_roundtrip rsp⟩

end Budget_Target_BvOmega
"""

    mods["Budget_Target_Grind"] = """import Init

namespace Budget_Target_Grind

theorem vc1_stack_heap_disjoint (rsp_lo rsp_hi buf_lo buf_hi addr : Nat)
    (h_sep : buf_hi ≤ rsp_lo) (h_in_buf : buf_lo ≤ addr ∧ addr < buf_hi)
    (h_in_stk : rsp_lo ≤ addr ∧ addr < rsp_hi) : False := by
  grind

theorem vc2_jumptable_bound (op : BitVec 32) (h : ¬ (15#32 < op)) : op.toNat < 16 := by
  have hle : op ≤ 15#32 := BitVec.not_lt.mp h
  have hnat : op.toNat ≤ (15#32).toNat := BitVec.le_def.mp hle
  grind

theorem vc3_avx2_alias_lane (dst a : BitVec 64)
    (h_guard : (24#64 : BitVec 64) < (dst - 4#64) - a) :
    dst ≠ a + 4#64 := by
  grind

theorem vc4_cfa_rsp_roundtrip (rsp : BitVec 64) : (rsp - 160#64) + 160#64 = rsp := by
  grind

theorem all_vcs (rsp_lo rsp_hi buf_lo buf_hi addr : Nat) (op : BitVec 32) (dst a rsp : BitVec 64) :
    (buf_hi ≤ rsp_lo → (buf_lo ≤ addr ∧ addr < buf_hi) → (rsp_lo ≤ addr ∧ addr < rsp_hi) → False) ∧
    (¬ (15#32 < op) → op.toNat < 16) ∧
    ((24#64 : BitVec 64) < (dst - 4#64) - a → dst ≠ a + 4#64) ∧
    ((rsp - 160#64) + 160#64 = rsp) :=
  ⟨vc1_stack_heap_disjoint rsp_lo rsp_hi buf_lo buf_hi addr,
   vc2_jumptable_bound op, vc3_avx2_alias_lane dst a, vc4_cfa_rsp_roundtrip rsp⟩

end Budget_Target_Grind
"""

    mods["Budget_Target_BvDecide"] = """import Std.Tactic.BVDecide

namespace Budget_Target_BvDecide

theorem vc1_stack_heap_disjoint (rsp_lo rsp_hi buf_lo buf_hi addr : BitVec 64)
    (h_sep : buf_hi ≤ rsp_lo) (h_in_buf : buf_lo ≤ addr ∧ addr < buf_hi)
    (h_in_stk : rsp_lo ≤ addr ∧ addr < rsp_hi) : False := by
  bv_decide

theorem vc2_jumptable_bound (op : BitVec 32) (h : ¬ (15#32 < op)) : op < 16#32 := by
  bv_decide

theorem vc3_avx2_alias_lane (dst a : BitVec 64)
    (h_guard : (24#64 : BitVec 64) < (dst - 4#64) - a) :
    dst ≠ a + 4#64 := by
  bv_decide

theorem vc4_cfa_rsp_roundtrip (rsp : BitVec 64) : (rsp - 160#64) + 160#64 = rsp := by
  bv_decide

theorem all_vcs (rsp_lo rsp_hi buf_lo buf_hi addr : BitVec 64) (op : BitVec 32) (dst a rsp : BitVec 64) :
    (buf_hi ≤ rsp_lo → (buf_lo ≤ addr ∧ addr < buf_hi) → (rsp_lo ≤ addr ∧ addr < rsp_hi) → False) ∧
    (¬ (15#32 < op) → op < 16#32) ∧
    ((24#64 : BitVec 64) < (dst - 4#64) - a → dst ≠ a + 4#64) ∧
    ((rsp - 160#64) + 160#64 = rsp) :=
  ⟨vc1_stack_heap_disjoint rsp_lo rsp_hi buf_lo buf_hi addr,
   vc2_jumptable_bound op, vc3_avx2_alias_lane dst a, vc4_cfa_rsp_roundtrip rsp⟩

end Budget_Target_BvDecide
"""
    return mods


def parse_batch_replay(stdout):
    out = {}
    for l in stdout.splitlines():
        if l.startswith("REPLAY_OK "):
            mm = re.search(r"mod=(\S+)", l)
            if not mm:
                continue
            mod = mm.group(1)
            row = {"replay_rc": 0}
            for key in ("import_ms", "replay_ms", "replayed_consts", "type_hints", "val_hints"):
                m = re.search(rf"{key}=(\d+)", l)
                if m:
                    row[key] = int(m.group(1))
            m = re.search(r"axioms=\[(.*?)\]", l)
            if m:
                raw = m.group(1).strip()
                row["axioms"] = [x.strip() for x in raw.split(",") if x.strip()] if raw else []
            out[mod] = row
        elif l.startswith("REPLAY_ERR "):
            mm = re.search(r"mod=(\S+)\s+err=(.*)", l)
            if mm:
                out[mm.group(1)] = {"replay_rc": 1, "replay_error": mm.group(2)}
    return out


def main():
    if "--inside-runner" not in sys.argv and RUN.exists():
        # Acquire ONE outer anneal-lean-run cgroup build slot for the entire sequential benchmark
        # so inner per-module wall timings are not contaminated by flock slot queuing.
        os.execv(str(RUN), [str(RUN), "--", sys.executable, str(Path(__file__).resolve()), "--inside-runner"])

    lean_ver = subprocess.run([str(LEAN), "--version"], capture_output=True, text=True, check=True).stdout.strip()
    results = {
        "lean_version": lean_ver,
        "flags": ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M2048"],
        "base_module": {},
        "exp1_spill_scaling": [],
        "exp2_branch_diamonds": [],
        "exp3_target_vs_theory_budget": [],
        "exp4_hint_separation": {},
    }

    with tempfile.TemporaryDirectory(prefix="lean4_mc_bench_") as td:
        tdp = Path(td)
        (tdp / "MachineLiftBase.lean").write_text((HERE / "MachineLiftBase.lean").read_text())
        (tdp / "HintSeparationProbe.lean").write_text((HERE / "HintSeparationProbe.lean").read_text())
        (tdp / "ReplayAudit.lean").write_text(REPLAY_SCRIPT_TEMPLATE)

        env = dict(os.environ, LEAN_PATH=str(tdp))
        base_flags = ["-R", str(tdp), "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-j1", "-M2048"]

        # Compile MachineLiftBase once
        base_olean = tdp / "MachineLiftBase.olean"
        r_base = run_timed_lean(base_flags + ["-o", str(base_olean), str(tdp / "MachineLiftBase.lean")], env)
        assert r_base["rc"] == 0, f"MachineLiftBase failed: {r_base['stdout']} {r_base['stderr_tail']}"
        results["base_module"] = {
            "wall_s": r_base["wall_s"],
            "cpu_s": r_base["cpu_s"],
            "rss_mb": r_base["rss_mb"],
            "olean_bytes": base_olean.stat().st_size,
        }
        print(f"[Base] MachineLiftBase: {results['base_module']}", flush=True)

        replay_jobs = []
        entry_by_mod = {}

        def compile_mod(mod_name, src_text, thm_name, replay_base="Init", timeout=90):
            src_path = tdp / f"{mod_name}.lean"
            olean_path = tdp / f"{mod_name}.olean"
            src_path.write_text(src_text)
            loc = len(src_text.splitlines())
            r = run_timed_lean(base_flags + ["-o", str(olean_path), str(src_path)], env, timeout=timeout)
            entry = {
                "module": mod_name,
                "loc": loc,
                "rc": r["rc"],
                "timed_out": r["timed_out"],
                "wall_s": r["wall_s"],
                "cpu_s": r["cpu_s"],
                "rss_mb": r["rss_mb"],
                "olean_bytes": olean_path.stat().st_size if olean_path.exists() else 0,
            }
            if r["rc"] == 0:
                replay_jobs.append((mod_name, thm_name, replay_base))
                entry_by_mod[mod_name] = entry
            else:
                entry["error_excerpt"] = (r["stdout"] + "\n" + r["stderr_tail"])[:400]
            return entry

        # --- Experiment 1A: Un-pruned DirectSym heartbeat cliff (N = 8..40) ---
        print("\n=== Experiment 1A: Un-Pruned DirectSym Cliff (N = 8..40) ===", flush=True)
        for n in [8, 16, 24, 32, 40]:
            mod = f"Spill_DirectSym_{n}"
            ent = compile_mod(mod, gen_spill_direct_sym(mod, n), f"{mod}.direct_sym_{n}", timeout=90)
            ent["regime"] = "DirectSym"
            ent["n_insns"] = n
            results["exp1_spill_scaling"].append(ent)
            print(
                f"  N={n:4d} DirectSym       rc={ent['rc']:2d} loc={ent['loc']:4d} "
                f"wall={ent['wall_s']:6.2f}s cpu={str(ent['cpu_s']):>6s}s rss={str(ent['rss_mb']):>6s}MB "
                f"olean={ent['olean_bytes']:8d}B",
                flush=True,
            )

        # --- Experiment 1B: Large-Scale Cutpoint20 vs FlatCertLift vs ShardedTreeLift (N = 40..5000) ---
        print("\n=== Experiment 1B: Cutpoint20 vs FlatCertLift vs ShardedTreeLift (N = 40..5000) ===", flush=True)
        failed_regimes = set()
        for n in [40, 100, 200, 400, 800, 1600, 3200, 5000]:
            for regime, gen_fn, thm_prefix in [
                ("Cutpoint20", gen_spill_cutpoint, "cutpoint"),
                ("FlatCertLift", gen_spill_cert_lift, "cert_lift"),
                ("ShardedTreeLift", gen_spill_sharded_tree_lift, "sharded_tree"),
            ]:
                if regime in failed_regimes:
                    continue
                mod = f"Spill_{regime}_{n}"
                ent = compile_mod(mod, gen_fn(mod, n), f"{mod}.{thm_prefix}_{n}", timeout=120)
                ent["regime"] = regime
                ent["n_insns"] = n
                results["exp1_spill_scaling"].append(ent)
                if ent["rc"] != 0:
                    failed_regimes.add(regime)
                print(
                    f"  N={n:4d} {regime:15s} rc={ent['rc']:2d} loc={ent['loc']:4d} "
                    f"wall={ent['wall_s']:6.2f}s cpu={str(ent['cpu_s']):>6s}s rss={str(ent['rss_mb']):>6s}MB "
                    f"olean={ent['olean_bytes']:8d}B",
                    flush=True,
                )

        # --- Experiment 2: Branch-Diamond Path Explosion vs Cutpoint Merging ---
        print("\n=== Experiment 2: Branch-Diamond Explosion (Uncut vs Cutpoint) ===", flush=True)
        for b in [4, 6, 8]:
            mod = f"Dia_Uncut_{b}"
            ent = compile_mod(mod, gen_branch_diamonds(mod, b, False), f"{mod}.uncut_diamonds_{b}", timeout=60)
            ent["regime"] = "Uncut"
            ent["diamonds"] = b
            ent["paths"] = 2 ** b
            results["exp2_branch_diamonds"].append(ent)
            print(
                f"  B={b:2d} (2^B={2**b:4d}) Uncut    rc={ent['rc']:2d} loc={ent['loc']:5d} "
                f"wall={ent['wall_s']:6.2f}s cpu={str(ent['cpu_s']):>6s}s rss={str(ent['rss_mb']):>6s}MB "
                f"olean={ent['olean_bytes']:8d}B",
                flush=True,
            )
        for b in [4, 6, 8, 16, 32]:
            mod = f"Dia_Cut_{b}"
            ent = compile_mod(mod, gen_branch_diamonds(mod, b, True), f"{mod}.cut_diamonds_{b}", timeout=60)
            ent["regime"] = "Cutpoint"
            ent["diamonds"] = b
            ent["paths"] = 2 ** b
            results["exp2_branch_diamonds"].append(ent)
            print(
                f"  B={b:2d} (2^B={2**b:10d}) Cutpoint rc={ent['rc']:2d} loc={ent['loc']:5d} "
                f"wall={ent['wall_s']:6.2f}s cpu={str(ent['cpu_s']):>6s}s rss={str(ent['rss_mb']):>6s}MB "
                f"olean={ent['olean_bytes']:8d}B",
                flush=True,
            )

        # --- Experiment 3: Target-Crate vs Pass-1 Theory Axiom & Tactic Budget ---
        print("\n=== Experiment 3: Target-Crate vs Pass-1 Theory Tactic & Axiom Audit ===", flush=True)
        allowed_3 = {"propext", "Classical.choice", "Quot.sound"}
        for mod, src in gen_tactic_budget_modules().items():
            replay_base = "Std.Tactic.BVDecide" if "import Std.Tactic.BVDecide" in src else "Init"
            ent = compile_mod(mod, src, f"{mod}.all_vcs", replay_base=replay_base, timeout=90)
            ent["replay_base"] = replay_base
            if ent["rc"] == 0:
                ax_script = tdp / f"Ax_{mod}.lean"
                ax_script.write_text(
                    f"import {mod}\n"
                    f"#print axioms {mod}.vc1_stack_heap_disjoint\n"
                    f"#print axioms {mod}.vc2_jumptable_bound\n"
                    f"#print axioms {mod}.vc3_avx2_alias_lane\n"
                    f"#print axioms {mod}.vc4_cfa_rsp_roundtrip\n"
                    f"#print axioms {mod}.all_vcs\n"
                )
                ra = run_timed_lean(base_flags + [str(ax_script)], env, timeout=60)
                per_vc = {}
                for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", ra["stdout"], re.S):
                    per_vc[m.group(1)] = [x.strip() for x in m.group(2).split(",") if x.strip()]
                for m in re.finditer(r"'([^']+)'\s+does not depend on any axioms", ra["stdout"]):
                    per_vc[m.group(1)] = []
                ax_list = per_vc.get(f"{mod}.all_vcs", [])
                ent["print_axioms"] = ax_list
                ent["per_vc_axioms"] = per_vc
                ent["within_3_axiom_ceiling"] = all(a in allowed_3 for a in ax_list)
            results["exp3_target_vs_theory_budget"].append(ent)
            print(
                f"  {mod:24s} rc={ent['rc']} wall={ent['wall_s']:5.2f}s cpu={str(ent['cpu_s']):>5s}s "
                f"rss={str(ent['rss_mb']):>6s}MB olean={ent['olean_bytes']:7d}B "
                f"3-ax={ent.get('within_3_axiom_ceiling')} print_ax={ent.get('print_axioms')}",
                flush=True,
            )

        # --- Experiment 4: Untrusted DWARF/CFA Hint Separation Audit ---
        print("\n=== Experiment 4: Statement-Origin Separation (HintSeparationProbe) ===", flush=True)
        hint_olean = tdp / "HintSeparationProbe.olean"
        rh = run_timed_lean(base_flags + ["-o", str(hint_olean), str(tdp / "HintSeparationProbe.lean")], env, timeout=60)
        assert rh["rc"] == 0, f"HintSeparationProbe failed: {rh['stdout']}"
        results["exp4_hint_separation"] = {
            "wall_s": rh["wall_s"],
            "cpu_s": rh["cpu_s"],
            "rss_mb": rh["rss_mb"],
            "olean_bytes": hint_olean.stat().st_size,
        }
        replay_jobs.append(("HintSeparationProbe", "LockedObligation.verify_compiled_dispatch_abi", "Init"))
        entry_by_mod["HintSeparationProbe"] = results["exp4_hint_separation"]

        # --- Batch Standalone Private-Level Kernel Replay (`trustLevel := 0, loadExts := false, level := .private`) ---
        print(f"\n=== Batch Standalone Kernel Replay ({len(replay_jobs)} compiled modules) ===", flush=True)
        jobs_file = tdp / "replay_jobs.txt"
        jobs_file.write_text("\n".join(f"{m} {t} {b}" for (m, t, b) in replay_jobs) + "\n")
        rr = run_timed_lean(["--run", str(tdp / "ReplayAudit.lean"), str(jobs_file)], env, timeout=180)
        print(f"  Batch ReplayAudit rc={rr['rc']} wall={rr['wall_s']}s cpu={rr['cpu_s']}s rss={rr['rss_mb']}MB", flush=True)
        if rr["rc"] != 0:
            print("  [REPLAY_FATAL_STDOUT]", rr["stdout"][:600], flush=True)
            print("  [REPLAY_FATAL_STDERR]", rr["stderr_tail"], flush=True)
        parsed = parse_batch_replay(rr["stdout"])
        for mod_name, thm_name, _ in replay_jobs:
            p_row = parsed.get(mod_name)
            if p_row:
                entry_by_mod[mod_name].update(p_row)
                print(
                    f"  REPLAY {mod_name:24s} rc={p_row.get('replay_rc')} "
                    f"import={p_row.get('import_ms')}ms replay={p_row.get('replay_ms')}ms "
                    f"consts={p_row.get('replayed_consts')} ty_h={p_row.get('type_hints')} val_h={p_row.get('val_hints')} "
                    f"ax={p_row.get('axioms')} err={p_row.get('replay_error')}",
                    flush=True,
                )
            else:
                entry_by_mod[mod_name]["replay_rc"] = -1
                print(f"  REPLAY {mod_name:24s} MISSING", flush=True)

    out_json = HERE / "lean4_scaling_and_axioms_results.json"
    out_json.write_text(json.dumps(results, indent=2) + "\n")
    print(f"\nWrote {out_json}", flush=True)


if __name__ == "__main__":
    main()
