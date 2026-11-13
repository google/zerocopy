-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import S16Chain.Link4X86Isa

namespace S16Chain

/-!
# Link 5: Top-Level End-to-End Machine-Code Correctness Theorem (`TopTheorem.lean`)

Composes Links 1–4 across all five definitional seams (`Seam 1`..`Seam 5`) into a
single closed theorem `end_to_end_x86_correct` over initial and final concrete
x86-64 machine states (`X86State`).
-/

/-- System V AMD64 ABI entry-state predicate (`Seam 4` Bridge Adapter):
`rip` points to `codeBase`, `rdi` holds `arg0`, `rsi` holds `arg1`, and the top
of the 64-bit stack (`readStack64 (m.regs .rsp)`) holds `retAddr`. -/
structure sysvEntryState (m : X86State) (codeBase retAddr arg0 arg1 : BitVec 64) : Prop where
  rip_eq : m.rip = codeBase
  rdi_eq : m.regs .rdi = arg0
  rsi_eq : m.regs .rsi = arg1
  ret_eq : m.readStack64 (m.regs .rsp) = retAddr

/-- System V AMD64 ABI callee-saved register preservation predicate. -/
def calleeSavedPreserved (m_init m_final : X86State) : Prop :=
  m_final.regs .rbx = m_init.regs .rbx ∧
  m_final.regs .rbp = m_init.regs .rbp ∧
  m_final.regs .r12 = m_init.regs .r12 ∧
  m_final.regs .r13 = m_init.regs .r13 ∧
  m_final.regs .r14 = m_init.regs .r14 ∧
  m_final.regs .r15 = m_init.regs .r15

/-- High-level precondition on the 64-bit machine words `arg0, arg1` (bridged
automatically via `wordRepresentsNat_toNat`). -/
def HighLevelPre (arg0 arg1 : BitVec 64) : Prop :=
  wordRepresentsNat arg0 arg0.toNat ∧ wordRepresentsNat arg1 arg1.toNat

/-- High-level postcondition relating the final x86-64 `rax` register both to
`HighLevelAddBoundedSpec` and to the Anneal `evalMirAddBounded` MIR semantics
(`Seam 1` + `Seam 5` Bridge). -/
def HighLevelPost (arg0 arg1 rax_final : BitVec 64) : Prop :=
  rax_final = BitVec.ofNat 64 (HighLevelAddBoundedSpec arg0.toNat arg1.toNat) ∧
  ∀ (st_mir : MirState),
    st_mir.locals 1 = some arg0.toNat →
    st_mir.locals 2 = some arg1.toNat →
    evalMirAddBounded st_mir = .returned rax_final.toNat

/-- Closed 5-Link End-to-End Machine-Code Theorem (`end_to_end_x86_correct`):
For any initial `X86State` where `fixtureMachineBytes` is loaded at `codeBase`
and the System V AMD64 entry contract holds, executing the x86-64 machine for
`k = 7` instructions halts at `retAddr`, increments `rsp` by 8, preserves all
6 callee-saved registers, and places the exact Anneal MIR-verified result into
`rax`. -/
theorem end_to_end_x86_correct
    (m_init : X86State) (codeBase retAddr arg0 arg1 : BitVec 64)
    (h_code : loadedAt m_init codeBase fixtureMachineBytes)
    (h_abi  : sysvEntryState m_init codeBase retAddr arg0 arg1)
    (_h_pre : HighLevelPre arg0 arg1) :
    ∃ (k : Nat) (m_final : X86State),
      runX86 k m_init = some m_final ∧
      m_final.rip = retAddr ∧
      m_final.regs .rsp = m_init.regs .rsp + 8#64 ∧
      HighLevelPost arg0 arg1 (m_final.regs .rax) ∧
      calleeSavedPreserved m_init m_final := by
  let a_body := runAddBoundedBodyAsm m_init.toAsm
  let a_final := a_body.setReg .rsp (m_init.regs .rsp + 8#64)
  let m_final := m_init.withAsmAndRip a_final (m_init.readStack64 (m_init.regs .rsp))
  refine ⟨7, m_final, ?_, ?_, ?_, ?_, ?_⟩
  · exact link4_x86_decode_and_run_7_steps m_init codeBase h_abi.rip_eq h_code
  · exact h_abi.ret_eq
  · simp [m_final, a_final, X86State.withAsmAndRip, AsmRegState.setReg]
  · -- Compose Link 3 -> Link 2 -> Seam 1 -> Link 1
    have h_l3 := (link3_abi_lowering_sound m_init.toAsm).1
    have h_rax_eq : m_final.regs .rax = (runAddBoundedBodyAsm m_init.toAsm).regs .rax := rfl
    rw [h_rax_eq]
    have h_rdi : m_init.toAsm.regs .rdi = arg0 := h_abi.rdi_eq
    have h_rsi : m_init.toAsm.regs .rsi = arg1 := h_abi.rsi_eq
    rw [h_rdi, h_rsi] at h_l3
    have h_l2 := link2_w6_opt_ssa_sound arg0 arg1
    let st_canonical : MirState := {
      locals := fun i => if i = 1 then some arg0.toNat else if i = 2 then some arg1.toNat else none
      allocs := fun _ => none
    }
    have h_seam1 := seam1_mir_to_ssa_pre_bridge st_canonical arg0 arg1 rfl rfl
    rw [h_l2, h_seam1] at h_l3
    injection h_l3 with h_val_eq
    constructor
    · exact h_val_eq.symm
    · intro st_mir hx1 hy2
      have h_l1 := link1_anneal_mir_add_bounded_verified st_mir arg0.toNat arg1.toNat hx1 hy2
      rw [h_l1, ← h_val_eq]
      congr 1
      unfold HighLevelAddBoundedSpec
      by_cases h1 : arg0.toNat ≤ 1000 <;> by_cases h2 : arg1.toNat ≤ 1000 <;>
        simp [h1, h2, BitVec.toNat_ofNat]
      omega
  · have h_l3 := link3_abi_lowering_sound m_init.toAsm
    rcases h_l3 with ⟨_, _, h_rbx, h_rbp, h_r12, h_r13, h_r14, h_r15⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simpa [m_final, a_final, a_body, X86State.withAsmAndRip, AsmRegState.setReg, X86State.toAsm]

#print axioms end_to_end_x86_correct

end S16Chain
