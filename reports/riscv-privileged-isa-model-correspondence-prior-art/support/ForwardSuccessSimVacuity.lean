/-
Probe: the *shape* of Verified-zkEVM/riscv-zkvm@6810fc14
`RiscvZkvm.Rv64.SailEquiv.sailStep_run_sim` (StepRun.lean:327-334) is a
forward, success-only simulation:

    RunInv s t → step s = some s' → ∃ t', sailStep t = some t' ∧ RunInv s' t'

(the real theorem additionally has fetch/simulable/side-condition premises).
The hand model signals traps by `step s = none` (Execution.lean:341-371,
e.g. `step_sh_trap`).  This probe shows, abstractly and Init-only, that:

 1. a model that traps (gets stuck) EVERYWHERE satisfies the shape for every
    reference machine and every relation (vacuity);
 2. a model that agrees with a total reference machine on all successful
    steps but gets stuck where the reference takes a trap (jumps to a
    handler) also satisfies it, so trap entry semantics is unconstrained;
 3. adding a fault/trap clause ("model stuck ⇒ reference stuck", i.e. no
    silent trap collapse) rejects both.

Standalone; imports nothing beyond Init.  Not a statement about riscv-zkvm's
proof correctness: only about what its theorem shape can and cannot carry.
-/

namespace T2Probe

/-- The success-only forward simulation shape. -/
def FwdSuccessSim {S T : Type} (step : S → Option S) (tstep : T → Option T)
    (R : S → T → Prop) : Prop :=
  ∀ s t s', R s t → step s = some s' → ∃ t', tstep t = some t' ∧ R s' t'

/-- A fault clause: whenever the hand model is stuck, so is the reference. -/
def NoSilentTrap {S T : Type} (step : S → Option S) (tstep : T → Option T)
    (R : S → T → Prop) : Prop :=
  ∀ s t, R s t → step s = none → tstep t = none

/-- (1) A trap-everywhere hand model satisfies the shape for ANY reference/relation. -/
theorem trapEverywhere_fwd {S T : Type} (tstep : T → Option T) (R : S → T → Prop) :
    FwdSuccessSim (fun _ => none) tstep R := by
  intro s t s' _ h
  cases h

/-- A total reference machine over a pc: address 8 holds a trapping
instruction whose architectural effect is a jump to the handler at 0x100. -/
def refStep (pc : Nat) : Option Nat := some (if pc = 8 then 0x100 else pc + 4)

/-- A hand model that agrees on every non-trapping step and is stuck at the trap. -/
def handStep (pc : Nat) : Option Nat := if pc = 8 then none else some (pc + 4)

def Req (s t : Nat) : Prop := s = t

/-- (2) The hand model satisfies the success-only shape against `refStep`. -/
theorem hand_fwd : FwdSuccessSim handStep refStep Req := by
  intro s t s' hR h
  subst hR
  unfold handStep at h
  by_cases h8 : s = 8
  · simp [h8] at h
  · simp [h8] at h
    subst h
    exact ⟨s + 4, by simp [refStep, h8], rfl⟩

/-- ... yet hand and reference disagree on the trap. -/
theorem hand_ref_disagree_on_trap : handStep 8 = none ∧ refStep 8 = some 0x100 := by
  constructor <;> rfl

/-- (3) The fault clause rejects the trap-everywhere model ... -/
theorem trapEverywhere_not_noSilentTrap :
    ¬ NoSilentTrap (S := Nat) (T := Nat) (fun _ => none) refStep Req := by
  intro h
  have := h 0 0 rfl rfl
  simp [refStep] at this

/-- ... and the agree-except-trap model. -/
theorem hand_not_noSilentTrap : ¬ NoSilentTrap handStep refStep Req := by
  intro h
  have := h 8 8 rfl rfl
  simp [refStep] at this

end T2Probe

#print axioms T2Probe.trapEverywhere_fwd
#print axioms T2Probe.hand_fwd
#print axioms T2Probe.hand_ref_disagree_on_trap
#print axioms T2Probe.trapEverywhere_not_noSilentTrap
#print axioms T2Probe.hand_not_noSilentTrap
