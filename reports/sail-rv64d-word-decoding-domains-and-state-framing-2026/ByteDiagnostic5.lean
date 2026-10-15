/- Narrow diagnostic after the original state-free decoder candidate failed.
   These assertions retain the actual full encoder/decoder/executor and prove
   why x1/x2 presence alone is insufficient for a decoder-success theorem. -/
import LeanRV64D
import Proof
import Controls

open Sail.ArchSem LeanRV64D

namespace AnnealSail.ByteDiagnostic

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

/-- Layout only: low-address-first bytes b3 81 20 00 give this word. -/
theorem selected_little_endian_word :
    (((0x00 : BitVec 8).append (0x20 : BitVec 8)).append
      (0x81 : BitVec 8)).append (0xb3 : BitVec 8) =
    (0x002081b3 : BitVec 32) := by
  decide

/-- Actual generated ADD encoder remains an accepted positive target. -/
theorem encode_add :
    Functions.encdec_forwards
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)) =
    (FreeM.pure (0x002081b3 : BitVec 32) : SailM (BitVec 32)) := by
  rfl

theorem supports_zicsr : Functions.hartSupports extension.Ext_Zicsr = true := by
  rw [Functions.hartSupports.eq_def]

theorem supports_pause : Functions.hartSupports extension.Ext_Zihintpause = true := by
  rw [Functions.hartSupports.eq_def]

theorem supports_cfilp : Functions.hartSupports extension.Ext_Zicfilp = true := by
  rw [Functions.hartSupports.eq_def]

/-- Propositional equations for the actual well-founded generated predicate. -/
theorem enabled_zicsr : Functions.currentlyEnabled extension.Ext_Zicsr =
    (FreeM.pure true : SailM Bool) := by
  rw [Functions.currentlyEnabled.eq_def]
  change (FreeM.pure (Functions.hartSupports extension.Ext_Zicsr) : SailM Bool) = _
  rw [supports_zicsr]

theorem enabled_pause : Functions.currentlyEnabled extension.Ext_Zihintpause =
    (FreeM.pure true : SailM Bool) := by
  rw [Functions.currentlyEnabled.eq_def]
  change (FreeM.pure (Functions.hartSupports extension.Ext_Zihintpause) : SailM Bool) = _
  rw [supports_pause]

theorem enabled_cfilp : Functions.currentlyEnabled extension.Ext_Zicfilp =
    (show SailM Bool from do
      let priv ← readReg Register.cur_privilege
      let lpe ← Functions.get_xLPE priv
      pure (true && (true && lpe))) := by
  rw [Functions.currentlyEnabled.eq_def]
  change (show SailM Bool from do
    let csr ← Functions.currentlyEnabled extension.Ext_Zicsr
    let priv ← readReg Register.cur_privilege
    let lpe ← Functions.get_xLPE priv
    pure (csr && (Functions.hartSupports extension.Ext_Zicfilp && lpe))) = _
  rw [enabled_zicsr, supports_cfilp]
  rfl

/-- Actual decoder has a leading privilege-register effect, not pure ADD. -/
theorem decoder_starts_with_privilege_read :
    ∃ k : Privilege → SailM instruction,
      Functions.ext_decode (0x002081b3 : BitVec 32) =
      FreeM.impure
        (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch)
          Register.cur_privilege none))) k := by
  unfold Functions.ext_decode Functions.encdec_backwards
  rw [enabled_pause, enabled_cfilp]
  refine ⟨?_, ?_⟩
  case refine_2 => rfl

/-- Missing privilege fails before the actual decoder reaches ADD. -/
theorem decoder_missing_privilege
    (s : SequentialState RegisterType)
    (hp : s.regs.get? Register.cur_privilege = none) :
    (interpretSailEffects
      (Functions.ext_decode (0x002081b3 : BitVec 32))).run s =
    EStateM.Result.error (Sail.Error.Unreachable : Sail.Error exception) s := by
  obtain ⟨k, hk⟩ := decoder_starts_with_privilege_read
  rw [hk]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, hp]

/-- Composition with the actual executor retains that early decoder error. -/
theorem decoder_then_execute_missing_privilege
    (s : SequentialState RegisterType)
    (hp : s.regs.get? Register.cur_privilege = none) :
    (interpretSailEffects
      (show SailM ExecutionResult from do
        let inst ← Functions.ext_decode (0x002081b3 : BitVec 32)
        Functions.execute inst)).run s =
    EStateM.Result.error (Sail.Error.Unreachable : Sail.Error exception) s := by
  obtain ⟨k, hk⟩ := decoder_starts_with_privilege_read
  rw [hk]
  simp [interpretSailEffects, FreeM.liftM, FreeM.bind, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, hp]

/-- The existing accepted fixture satisfies the original operand premises. -/
theorem fixture_has_sources :
    Controls.fixture12.regs.get? Register.x1 = some (1 : BitVec 64) ∧
    Controls.fixture12.regs.get? Register.x2 = some (2 : BitVec 64) := by
  simp [Controls.fixture12, Controls.emptyState, Std.ExtDHashMap.get?_insert]

/-- That same real fixture does not initialize decoder privilege state. -/
theorem fixture_decoder_errors :
    (interpretSailEffects
      (Functions.ext_decode (0x002081b3 : BitVec 32))).run Controls.fixture12 =
    EStateM.Result.error (Sail.Error.Unreachable : Sail.Error exception)
      Controls.fixture12 := by
  apply decoder_missing_privilege
  simp [Controls.fixture12, Controls.emptyState, Std.ExtDHashMap.get?_insert]

/-- Concrete counterexample to extending AST success using only x1/x2. -/
theorem fixture_decode_execute_errors :
    (interpretSailEffects
      (show SailM ExecutionResult from do
        let inst ← Functions.ext_decode (0x002081b3 : BitVec 32)
        Functions.execute inst)).run Controls.fixture12 =
    EStateM.Result.error (Sail.Error.Unreachable : Sail.Error exception)
      Controls.fixture12 := by
  apply decoder_then_execute_missing_privilege
  simp [Controls.fixture12, Controls.emptyState, Std.ExtDHashMap.get?_insert]

/-- The original state-free decoder equality is semantically impossible. -/
theorem decoder_is_not_pure_selected_add :
    Functions.ext_decode (0x002081b3 : BitVec 32) ≠
    (FreeM.pure
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)) :
      SailM instruction) := by
  obtain ⟨k, hk⟩ := decoder_starts_with_privilege_read
  rw [hk]
  intro h
  cases h

/-- Refute the original universal decode-then-execute success domain,
    without replacing it by a stronger privilege/CSR-premise statement. -/
theorem x1x2_only_composition_success_is_false :
    ¬ (∀ (a b : BitVec 64) (s : SequentialState RegisterType),
      s.regs.get? Register.x1 = some a →
      s.regs.get? Register.x2 = some b →
      (interpretSailEffects
        (show SailM ExecutionResult from do
          let inst ← Functions.ext_decode (0x002081b3 : BitVec 32)
          Functions.execute inst)).run s =
      EStateM.Result.ok (ExecutionResult.Retire_Success ())
        {s with regs := s.regs.insert Register.x3 (a + b)}) := by
  intro alleged
  obtain ⟨h1, h2⟩ := fixture_has_sources
  have h := alleged 1 2 Controls.fixture12 h1 h2
  rw [fixture_decode_execute_errors] at h
  cases h

#check supports_zicsr
#print axioms supports_zicsr
#check supports_pause
#print axioms supports_pause
#check supports_cfilp
#print axioms supports_cfilp
#check enabled_zicsr
#print axioms enabled_zicsr
#check enabled_pause
#print axioms enabled_pause
#check enabled_cfilp
#print axioms enabled_cfilp
#check x1x2_only_composition_success_is_false
#print axioms x1x2_only_composition_success_is_false

#check selected_little_endian_word
#print axioms selected_little_endian_word
#check encode_add
#print axioms encode_add
#check decoder_starts_with_privilege_read
#print axioms decoder_starts_with_privilege_read
#check decoder_missing_privilege
#print axioms decoder_missing_privilege
#check decoder_then_execute_missing_privilege
#print axioms decoder_then_execute_missing_privilege
#check fixture_has_sources
#print axioms fixture_has_sources
#check fixture_decoder_errors
#print axioms fixture_decoder_errors
#check fixture_decode_execute_errors
#print axioms fixture_decode_execute_errors
#check decoder_is_not_pure_selected_add
#print axioms decoder_is_not_pure_selected_add

end AnnealSail.ByteDiagnostic
