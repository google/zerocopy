/- UNCOMPILED source-only candidate. No native grant for this file.
   It proposes a new, explicitly stronger positive domain. The accepted
   x1/x2-only-domain refutation remains unchanged in ByteDiagnostic5. -/
import LeanRV64D
import Proof
import ByteDiagnostic5

open Sail.ArchSem LeanRV64D

namespace AnnealSail.MachineDecode

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

theorem machine_lpe_reads_seccfg :
    Functions.get_xLPE Privilege.Machine =
    (show SailM Bool from do
      let csr ← readReg Register.mseccfg
      pure (Functions.bool_bit_backwards (Functions._get_Seccfg_MLPE csr))) := by
  rw [Functions.get_xLPE.eq_def]

theorem decoder_machine_effects :
    ∃ k : Privilege → SailM instruction,
      Functions.ext_decode (0x002081b3 : BitVec 32) =
        FreeM.impure
          (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch)
            Register.cur_privilege none))) k ∧
      k Privilege.Machine =
        (show SailM instruction from do
          let _ ← readReg Register.mseccfg
          pure (instruction.RTYPE
            (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD))) := by
  unfold Functions.ext_decode Functions.encdec_backwards
  rw [ByteDiagnostic.enabled_pause, ByteDiagnostic.enabled_cfilp]
  refine ⟨?_, ?_, ?_⟩
  case refine_2 => rfl
  case refine_3 =>
    dsimp only [Bind.bind, Pure.pure, FreeM.bind]
    rw [machine_lpe_reads_seccfg]
    dsimp only [Bind.bind, Pure.pure, FreeM.bind, readReg, PreSail.readReg]
    apply congrArg (fun cont : BitVec 64 → SailM instruction =>
      (show SailM instruction from FreeM.impure
        (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch)
          Register.mseccfg none))) cont))
    funext csr
    cases h : Functions.bool_bit_backwards (Functions._get_Seccfg_MLPE csr) <;> rfl

/-- Proposed positive domain: Machine privilege and arbitrary present mseccfg.
    This statement and proof script have NOT been elaborated or accepted. -/
theorem decode_add_machine
    (csr : BitVec 64) (s : SequentialState RegisterType)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hc : s.regs.get? Register.mseccfg = some csr) :
    (interpretSailEffects
      (Functions.ext_decode (0x002081b3 : BitVec 32))).run s =
    EStateM.Result.ok
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)) s := by
  obtain ⟨k, hk, hm⟩ := decoder_machine_effects
  rw [hk]
  simp [hm, PreSail.readReg, Functions.encdec_reg_backwards,
    Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.encdec_reg_backwards_matches,
    interpretSailEffects, FreeM.liftM, FreeM.bind, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, hp, hc]

/-- Same new domain, plus the original universal arithmetic operands.
    Full actual decode→execute and full-state equality are retained.
    This statement and proof script have NOT been elaborated or accepted. -/
theorem decode_execute_add_machine
    (a b csr : BitVec 64) (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b)
    (hp : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hc : s.regs.get? Register.mseccfg = some csr) :
    (interpretSailEffects
      (show SailM ExecutionResult from do
        let inst ← Functions.ext_decode (0x002081b3 : BitVec 32)
        Functions.execute inst)).run s =
    EStateM.Result.ok (ExecutionResult.Retire_Success ())
      {s with regs := s.regs.insert Register.x3 (a + b)} := by
  obtain ⟨k, hk, hm⟩ := decoder_machine_effects
  rw [hk]
  simp [hm, PreSail.readReg, Functions.encdec_reg_backwards,
    Functions.base_E_enabled, Functions.regidx_bit_width,
    Functions.encdec_reg_backwards_matches, AnnealSail.execute_add_effects,
    interpretSailEffects, FreeM.liftM, FreeM.bind, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, getThe, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify, hp, hc, h1, h2]


  exact AnnealSail.execute_add_full_state a b s h1 h2

#check decode_add_machine
#print axioms decode_add_machine
#check decode_execute_add_machine
#print axioms decode_execute_add_machine
#check decoder_machine_effects
#print axioms decoder_machine_effects
#check machine_lpe_reads_seccfg
#print axioms machine_lpe_reads_seccfg

end AnnealSail.MachineDecode
