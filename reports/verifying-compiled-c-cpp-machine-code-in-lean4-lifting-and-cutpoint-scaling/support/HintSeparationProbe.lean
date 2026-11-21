prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import MachineLiftBase

/-!
Untrusted structural-hint consumption with Statement-Origin Separation:
- The locked theorem statement (`verify_compiled_dispatch_abi`) references ONLY
  raw compiled `ObjImage` (`code` + `.rodata` jump table), `MachineLift.run`,
  and System V AMD64 `FnAbi` registers (`rdi`, `rsi`, `rsp`, `rax`, `fs28`).
- The proof body consumes an untrusted `UntrustedHints.HintCert` (modeling
  offline DWARF / `.eh_frame` CFA / symbol-table extraction) to discover the
  stack-frame size (`32`), canary slot (`3`), jump-table metadata (`base=0`,
  `bound=16`), and per-case straight-line blocks, validating every hint
  against raw `dispatchImg` bytes inside the proof term.
-/

namespace CompiledDispatchSpec

open MachineLift

/-- Compiled 16-case switch + `-fstack-protector-strong` prologue/epilogue image:
    PC 0:  `subRsp 32`
    PC 1:  `loadCanary .r10`
    PC 2:  `spillStore 3 .r10`   (canary at `[rsp + 24]`)
    PC 3:  `jmpTable .rdi 16 0 36`
    PC 4..35: 16 two-instruction case handlers (`addImm .rsi (k+1); jmp 38`)
    PC 36..37: default handler (`movReg .rsi .rdi; jmp 38`) -- mirrors `.text.unlikely`
    PC 38: `movReg .rax .rsi`
    PC 39: `cmpCanary 3 42`      (checks `[rsp + 24] == fs:0x28`, else PC 42 trap)
    PC 40: `addRsp 32`
    PC 41: `ret`
    PC 42: `trap`                (`__stack_chk_fail`) -/
def dispatchCode : List Instr :=
  [ .subRsp 32,
    .loadCanary .r10,
    .spillStore 3 .r10,
    .jmpTable .rdi 16 0 36,
    .addImm .rsi 1#64,  .jmp 38,   -- case 0  (PC 4)
    .addImm .rsi 2#64,  .jmp 38,   -- case 1  (PC 6)
    .addImm .rsi 3#64,  .jmp 38,   -- case 2  (PC 8)
    .addImm .rsi 4#64,  .jmp 38,   -- case 3  (PC 10)
    .addImm .rsi 5#64,  .jmp 38,   -- case 4  (PC 12)
    .addImm .rsi 6#64,  .jmp 38,   -- case 5  (PC 14)
    .addImm .rsi 7#64,  .jmp 38,   -- case 6  (PC 16)
    .addImm .rsi 8#64,  .jmp 38,   -- case 7  (PC 18)
    .addImm .rsi 9#64,  .jmp 38,   -- case 8  (PC 20)
    .addImm .rsi 10#64, .jmp 38,   -- case 9  (PC 22)
    .addImm .rsi 11#64, .jmp 38,   -- case 10 (PC 24)
    .addImm .rsi 12#64, .jmp 38,   -- case 11 (PC 26)
    .addImm .rsi 13#64, .jmp 38,   -- case 12 (PC 28)
    .addImm .rsi 14#64, .jmp 38,   -- case 13 (PC 30)
    .addImm .rsi 15#64, .jmp 38,   -- case 14 (PC 32)
    .addImm .rsi 16#64, .jmp 38,   -- case 15 (PC 34)
    .movReg .rsi .rdi,  .jmp 38,   -- default (PC 36)
    .movReg .rax .rsi,             -- merge   (PC 38)
    .cmpCanary 3 42,               -- PC 39
    .addRsp 32,                    -- PC 40
    .ret,                          -- PC 41
    .trap                          -- PC 42
  ]

/-- Resolved `.rodata` jump-table entries (16 target PCs). -/
def dispatchRodata : List Nat :=
  [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34]

def dispatchImg : ObjImage :=
  { code := dispatchCode, rodata := dispatchRodata }

/-- Pure mathematical specification bound only to System V AMD64 `FnAbi` inputs
    (`rdi` = opcode, `rsi` = accumulator). Zero DWARF or hint terms! -/
def dispatchFunctionalSpec (op acc : BitVec 64) : BitVec 64 :=
  if op.toNat < 16 then acc + (op + 1#64) else op

end CompiledDispatchSpec

namespace UntrustedHints

open MachineLift

/-- Untrusted structural hint bundle extracted offline from `.eh_frame`, DWARF,
    `.rela.rodata`, and symbol tables. Never allowed in locked theorem statements! -/
structure HintCert where
  cfaFrameBytes : Nat
  canarySlot    : Nat
  tableBase     : Nat
  tableBound    : Nat
  defaultPc     : Nat
  mergePc       : Nat
  failPc        : Nat

def extractedHints : HintCert :=
  { cfaFrameBytes := 32,
    canarySlot    := 3,
    tableBase     := 0,
    tableBound    := 16,
    defaultPc     := 36,
    mergePc       := 38,
    failPc        := 42 }

/-- Check that every `.rodata` entry `k < bound` points to a valid two-instruction
    `addImm .rsi (k+1); jmp mergePc` case handler in `img.code`. -/
def checkJumpTableCase (img : ObjImage) (h : HintCert) (k : Nat) : Bool :=
  match listGet? img.rodata (h.tableBase + k) with
  | some tgt =>
    decide (listGet? img.code tgt = some (.addImm .rsi (BitVec.ofNat 64 (k + 1)))) &&
    decide (listGet? img.code (tgt + 1) = some (.jmp h.mergePc))
  | none => false

def checkAllCases (img : ObjImage) (h : HintCert) : Nat → Bool
  | 0 => true
  | k + 1 => checkJumpTableCase img h k && checkAllCases img h k

def checkHintCert (img : ObjImage) (h : HintCert) : Bool :=
  decide (listGet? img.code 0 = some (.subRsp h.cfaFrameBytes)) &&
  decide (listGet? img.code 1 = some (.loadCanary .r10)) &&
  decide (listGet? img.code 2 = some (.spillStore h.canarySlot .r10)) &&
  decide (listGet? img.code 3 = some (.jmpTable .rdi h.tableBound h.tableBase h.defaultPc)) &&
  decide (listGet? img.code h.defaultPc = some (.movReg .rsi .rdi)) &&
  decide (listGet? img.code (h.defaultPc + 1) = some (.jmp h.mergePc)) &&
  decide (listGet? img.code h.mergePc = some (.movReg .rax .rsi)) &&
  decide (listGet? img.code (h.mergePc + 1) = some (.cmpCanary h.canarySlot h.failPc)) &&
  decide (listGet? img.code (h.mergePc + 2) = some (.addRsp h.cfaFrameBytes)) &&
  decide (listGet? img.code (h.mergePc + 3) = some .ret) &&
  checkAllCases img h h.tableBound

theorem checkAllCases_lookup {img : ObjImage} {h : HintCert} :
    ∀ {n k : Nat}, checkAllCases img h n = true → k < n → checkJumpTableCase img h k = true
  | 0, _, _, hk => nomatch hk
  | n + 1, k, hchk, hk => by
    dsimp [checkAllCases] at hchk
    have hp := Bool.and_eq_true_iff.mp hchk
    cases hdec : decide (k = n) with
    | true =>
      have heq : k = n := of_decide_eq_true hdec
      rw [heq]
      exact hp.1
    | false =>
      have hne : k ≠ n := of_decide_eq_false hdec
      have hlt : k < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) hne
      exact checkAllCases_lookup hp.2 hlt

/-- Soundness of the untrusted hint certificate: checking `checkHintCert img h = true`
    discharges the full 10-step ABI, canary, stack-balance, heap-framing, and functional
    correctness theorem for ALL `op : BitVec 64` and `acc : BitVec 64`! -/
theorem checkHintCert_sound {img : ObjImage} {h : HintCert} (s : MState)
    (h_cert : checkHintCert img h = true)
    (h_pc : s.pc = 0)
    (h_nhalt : s.halted = false)
    (h_nfault : s.fault = false) :
    let sf := run img 10 s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.regs .rsp = s.regs .rsp ∧
    sf.regs .rax = (if (s.regs .rdi).toNat < h.tableBound
                    then s.regs .rsi + BitVec.ofNat 64 ((s.regs .rdi).toNat + 1)
                    else s.regs .rdi) ∧
    (∀ addr, addr ≠ (s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes) + BitVec.ofNat 64 (h.canarySlot * 8) →
      sf.mem addr = s.mem addr) := by
  dsimp [checkHintCert] at h_cert
  -- Unpack the 11 boolean checks
  have c10 := Bool.and_eq_true_iff.mp h_cert
  have h_cases := c10.2
  have c9 := Bool.and_eq_true_iff.mp c10.1
  have h_ret : listGet? img.code (h.mergePc + 3) = some .ret := of_decide_eq_true c9.2
  have c8 := Bool.and_eq_true_iff.mp c9.1
  have h_addrsp : listGet? img.code (h.mergePc + 2) = some (.addRsp h.cfaFrameBytes) := of_decide_eq_true c8.2
  have c7 := Bool.and_eq_true_iff.mp c8.1
  have h_cmpcan : listGet? img.code (h.mergePc + 1) = some (.cmpCanary h.canarySlot h.failPc) := of_decide_eq_true c7.2
  have c6 := Bool.and_eq_true_iff.mp c7.1
  have h_merge : listGet? img.code h.mergePc = some (.movReg .rax .rsi) := of_decide_eq_true c6.2
  have c5 := Bool.and_eq_true_iff.mp c6.1
  have h_def1 : listGet? img.code (h.defaultPc + 1) = some (.jmp h.mergePc) := of_decide_eq_true c5.2
  have c4 := Bool.and_eq_true_iff.mp c5.1
  have h_def0 : listGet? img.code h.defaultPc = some (.movReg .rsi .rdi) := of_decide_eq_true c4.2
  have c3 := Bool.and_eq_true_iff.mp c4.1
  have h_jtbl : listGet? img.code 3 = some (.jmpTable .rdi h.tableBound h.tableBase h.defaultPc) := of_decide_eq_true c3.2
  have c2 := Bool.and_eq_true_iff.mp c3.1
  have h_spill : listGet? img.code 2 = some (.spillStore h.canarySlot .r10) := of_decide_eq_true c2.2
  have c1 := Bool.and_eq_true_iff.mp c2.1
  have h_loadc : listGet? img.code 1 = some (.loadCanary .r10) := of_decide_eq_true c1.2
  have h_subrsp : listGet? img.code 0 = some (.subRsp h.cfaFrameBytes) := of_decide_eq_true c1.1
  -- Step 0..2: prologue (subRsp, loadCanary, spillStore)
  let s1 : MState := { s with pc := 1, regs := regUpd s.regs .rsp (s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes) }
  have hs0 : step img s = s1 := by
    have h0 := step_subRsp h_nhalt h_nfault (by rw [h_pc]; exact h_subrsp)
    rw [h_pc] at h0; exact h0
  let s2 : MState := { s1 with pc := 2, regs := regUpd s1.regs .r10 s1.fs28 }
  have hs1 : step img s1 = s2 :=
    step_loadCanary (s := s1) h_nhalt h_nfault h_loadc
  let s3 : MState := { s2 with pc := 3, mem := memUpd s2.mem (stackSlotAddr s2 h.canarySlot) (s2.regs .r10) }
  have hs2 : step img s2 = s3 :=
    step_spillStore (s := s2) h_nhalt h_nfault h_spill
  have h_run3 : run img 3 s = s3 := by
    rw [run_succ, hs0, run_succ, hs1, run_succ, hs2, run_zero]
  -- Facts at PC 3 (just before jmpTable):
  have hs3_rsp : s3.regs .rsp = s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes := by
    dsimp [s3, s2, s1]; rw [regUpd_ne _ (by decide), regUpd_eq]
  have hs3_rdi : s3.regs .rdi = s.regs .rdi := by
    dsimp [s3, s2, s1]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
  have hs3_rsi : s3.regs .rsi = s.regs .rsi := by
    dsimp [s3, s2, s1]; rw [regUpd_ne _ (by decide), regUpd_ne _ (by decide)]
  have hs3_can : s3.mem (stackSlotAddr s3 h.canarySlot) = s.fs28 := by
    dsimp [s3, stackSlotAddr]
    change memUpd s2.mem (stackSlotAddr s2 h.canarySlot) (s2.regs .r10) (stackSlotAddr s2 h.canarySlot) = s.fs28
    rw [memUpd_eq]
    dsimp [s2, s1]; rw [regUpd_eq]
  have hs3_mem_frame : ∀ addr,
      addr ≠ (s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes) + BitVec.ofNat 64 (h.canarySlot * 8) →
      s3.mem addr = s.mem addr := by
    intro addr hne
    dsimp [s3]
    have h_slot : stackSlotAddr s2 h.canarySlot =
        (s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes) + BitVec.ofNat 64 (h.canarySlot * 8) := by
      dsimp [stackSlotAddr, s2, s1]; rw [regUpd_ne _ (by decide), regUpd_eq]
    rw [h_slot, memUpd_ne _ hne]
  -- Helper finishing epilogue from PC = mergePc (4 steps: movReg, cmpCanary, addRsp, ret)
  have h_epilogue : ∀ (sm : MState),
      sm.pc = h.mergePc → sm.halted = false → sm.fault = false →
      sm.fs28 = s.fs28 →
      sm.regs .rsp = s.regs .rsp - BitVec.ofNat 64 h.cfaFrameBytes →
      sm.mem (stackSlotAddr sm h.canarySlot) = s.fs28 →
      let sf := run img 4 sm
      sf.halted = true ∧ sf.fault = false ∧ sf.regs .rsp = s.regs .rsp ∧
      sf.regs .rax = sm.regs .rsi ∧ sf.mem = sm.mem := by
    intro sm hmpc hmnh hmnf hmfs hmrsp hmcan
    let sm1 : MState := { sm with pc := h.mergePc + 1, regs := regUpd sm.regs .rax (sm.regs .rsi) }
    have e0 : step img sm = sm1 := by
      have t := step_movReg (s := sm) hmnh hmnf (by rw [hmpc]; exact h_merge)
      rw [hmpc] at t; exact t
    let sm2 : MState := { sm1 with pc := h.mergePc + 2 }
    have e1 : step img sm1 = sm2 := by
      have hcan1 : sm1.mem (stackSlotAddr sm1 h.canarySlot) = sm1.fs28 := by
        dsimp [sm1, stackSlotAddr]; rw [regUpd_ne _ (by decide), hmfs]; exact hmcan
      exact step_cmpCanary_ok (s := sm1) hmnh hmnf h_cmpcan hcan1
    let sm3 : MState := { sm2 with pc := h.mergePc + 3, regs := regUpd sm2.regs .rsp (sm2.regs .rsp + BitVec.ofNat 64 h.cfaFrameBytes) }
    have e2 : step img sm2 = sm3 :=
      step_addRsp (s := sm2) hmnh hmnf h_addrsp
    let sm4 : MState := { sm3 with halted := true }
    have e3 : step img sm3 = sm4 :=
      step_ret (s := sm3) hmnh hmnf h_ret
    have h_run4 : run img 4 sm = sm4 := by
      rw [run_succ, e0, run_succ, e1, run_succ, e2, run_succ, e3, run_zero]
    dsimp only
    rw [h_run4]
    refine ⟨rfl, hmnf, ?_, ?_, rfl⟩
    · dsimp [sm4, sm3, sm2, sm1]
      rw [regUpd_eq, regUpd_ne _ (by decide), hmrsp]
      exact BitVec.sub_add_cancel _ _
    · dsimp [sm4, sm3, sm2, sm1]
      rw [regUpd_ne _ (by decide), regUpd_eq]
  -- Split on `op.toNat < h.tableBound` at PC 3 (jmpTable) -> 3 steps to mergePc + 4 epilogue steps
  dsimp only
  have h_run10 : run img 10 s = run img 4 (run img 3 s3) := by
    have t1 : run img 10 s = run img 7 (run img 3 s) := run_add img 3 7 s
    rw [t1, h_run3]
    exact run_add img 3 4 s3
  rw [h_run10]
  cases hdec : decide ((s.regs .rdi).toNat < h.tableBound) with
  | true =>
    have hlt : (s.regs .rdi).toNat < h.tableBound := of_decide_eq_true hdec
    simp only [hlt, ite_true]
    have hcase := checkAllCases_lookup h_cases hlt
    dsimp [checkJumpTableCase] at hcase
    cases hro : listGet? img.rodata (h.tableBase + (s.regs .rdi).toNat) with
    | none => rw [hro] at hcase; nomatch hcase
    | some tgt =>
      rw [hro] at hcase
      dsimp only at hcase
      have hp := Bool.and_eq_true_iff.mp hcase
      have hc0 : listGet? img.code tgt = some (.addImm .rsi (BitVec.ofNat 64 ((s.regs .rdi).toNat + 1))) :=
        of_decide_eq_true hp.1
      have hc1 : listGet? img.code (tgt + 1) = some (.jmp h.mergePc) :=
        of_decide_eq_true hp.2
      have hlt3 : (s3.regs .rdi).toNat < h.tableBound := by rw [hs3_rdi]; exact hlt
      have hro3 : listGet? img.rodata (h.tableBase + (s3.regs .rdi).toNat) = some tgt := by
        rw [hs3_rdi]; exact hro
      let s4 : MState := { s3 with pc := tgt }
      have hs4 : step img s3 = s4 :=
        step_jmpTable_inbounds (s := s3) h_nhalt h_nfault h_jtbl hlt3 hro3
      let s5 : MState := { s4 with pc := tgt + 1, regs := regUpd s4.regs .rsi (s4.regs .rsi + BitVec.ofNat 64 ((s.regs .rdi).toNat + 1)) }
      have hs5 : step img s4 = s5 :=
        step_addImm (s := s4) h_nhalt h_nfault hc0
      let s6 : MState := { s5 with pc := h.mergePc }
      have hs6 : step img s5 = s6 :=
        step_jmp (s := s5) h_nhalt h_nfault hc1
      have h_run3_mid : run img 3 s3 = s6 := by
        rw [run_succ, hs4, run_succ, hs5, run_succ, hs6, run_zero]
      rw [h_run3_mid]
      have h_ep := h_epilogue s6 rfl h_nhalt h_nfault rfl
        (by dsimp [s6, s5, s4]; rw [regUpd_ne _ (by decide)]; exact hs3_rsp)
        (by dsimp [s6, s5, s4, stackSlotAddr]; rw [regUpd_ne _ (by decide)]; exact hs3_can)
      refine ⟨h_ep.1, h_ep.2.1, h_ep.2.2.1, ?_, ?_⟩
      · rw [h_ep.2.2.2.1]
        dsimp [s6, s5, s4]; rw [regUpd_eq, hs3_rsi]
      · intro addr hne
        rw [h_ep.2.2.2.2]
        exact hs3_mem_frame addr hne
  | false =>
    have hnlt : ¬ ((s.regs .rdi).toNat < h.tableBound) := of_decide_eq_false hdec
    simp only [hnlt, ite_false]
    let s4 : MState := { s3 with pc := h.defaultPc }
    have hs4 : step img s3 = s4 :=
      step_jmpTable_out (s := s3) h_nhalt h_nfault h_jtbl (by rw [hs3_rdi]; exact hnlt)
    let s5 : MState := { s4 with pc := h.defaultPc + 1, regs := regUpd s4.regs .rsi (s4.regs .rdi) }
    have hs5 : step img s4 = s5 :=
      step_movReg (s := s4) h_nhalt h_nfault h_def0
    let s6 : MState := { s5 with pc := h.mergePc }
    have hs6 : step img s5 = s6 :=
      step_jmp (s := s5) h_nhalt h_nfault h_def1
    have h_run3_mid : run img 3 s3 = s6 := by
      rw [run_succ, hs4, run_succ, hs5, run_succ, hs6, run_zero]
    rw [h_run3_mid]
    have h_ep := h_epilogue s6 rfl h_nhalt h_nfault rfl
      (by dsimp [s6, s5, s4]; rw [regUpd_ne _ (by decide)]; exact hs3_rsp)
      (by dsimp [s6, s5, s4, stackSlotAddr]; rw [regUpd_ne _ (by decide)]; exact hs3_can)
    refine ⟨h_ep.1, h_ep.2.1, h_ep.2.2.1, ?_, ?_⟩
    · rw [h_ep.2.2.2.1]
      dsimp [s6, s5, s4]; rw [regUpd_eq, hs3_rdi]
    · intro addr hne
      rw [h_ep.2.2.2.2]
      exact hs3_mem_frame addr hne

end UntrustedHints

namespace LockedObligation

open MachineLift CompiledDispatchSpec

/-- Locked theorem statement: references ONLY `CompiledDispatchSpec` (`dispatchImg`,
    `dispatchFunctionalSpec`), `MachineLift` (`run`, `MState`), and `Init.*`.
    Zero `UntrustedHints` constants appear anywhere in `ConstantInfo.type`! -/
theorem verify_compiled_dispatch_abi (s : MState)
    (h_pc : s.pc = 0)
    (h_nhalt : s.halted = false)
    (h_nfault : s.fault = false) :
    let sf := run dispatchImg 10 s
    sf.halted = true ∧
    sf.fault = false ∧
    sf.regs .rsp = s.regs .rsp ∧
    sf.regs .rax = dispatchFunctionalSpec (s.regs .rdi) (s.regs .rsi) ∧
    (∀ addr, addr ≠ (s.regs .rsp - 32#64) + 24#64 → sf.mem addr = s.mem addr) := by
  have h := UntrustedHints.checkHintCert_sound (img := dispatchImg)
    (h := UntrustedHints.extractedHints) s rfl h_pc h_nhalt h_nfault
  dsimp [UntrustedHints.extractedHints] at h
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  rw [h.2.2.2.1]
  dsimp [dispatchFunctionalSpec]
  cases hdec : decide ((s.regs .rdi).toNat < 16) with
  | true =>
    have hlt : (s.regs .rdi).toNat < 16 := of_decide_eq_true hdec
    simp only [hlt, ite_true]
    have hbv : BitVec.ofNat 64 ((s.regs .rdi).toNat + 1) = s.regs .rdi + 1#64 := by
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hbv]
  | false =>
    have hnlt : ¬ ((s.regs .rdi).toNat < 16) := of_decide_eq_false hdec
    simp only [hnlt, ite_false]

end LockedObligation
