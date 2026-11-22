import Toy.LawRewrite.Basic
import Toy.LawRewrite.CaptureBridge
import Toy.LawRewrite.Lemmas
import Toy.LawRewrite.Examples
import Toy.LawRewrite.Main

/-!
# Counterexamples and non-vacuity witnesses

Every theorem here is fully proved and does not depend on any unproved statement.
Each counterexample is stated in canonical form: a concrete instance satisfies the
other hypotheses of the statement it refutes, and the conclusion fails. Each
non-vacuity theorem exhibits a concrete instance satisfying all hypotheses of a main
statement.
-/

namespace Toy.LawRewrite

open CaptureBridge (Den DenIncl VerifierSound TransferSound)

/-! ## Direct capture -/

/-- **A non-trivial `Clone` breaks clone→copy.** In `envSafeLog` (safe trait; the impl
emits `9` and returns its argument; the contract is a copy), clone→copy substitutes the
contract (`ReplIsContract`), the law fails at the reached call of the probe, the direct
capture of the probe emits `9` then `5`, the rewritten program emits `5`, and neither
prefix-preserving nor whole-trace refinement holds. -/
theorem cex_nontrivial_clone_copy_rewrite :
    ReplIsContract envSafeLog cloneToCopy ∧
      ¬ LawOnReached envSafeLog cloneToCopy (probe 0 5) σ0 ∧
      capDirect envSafeLog .before (probe 0 5) σ0 = [.done [9, 5]] ∧
      compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0 = [.done [5]] ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .after (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) :=
  ⟨replIsContract_pos, lawOnReached_neg, by decide, by decide, by decide, by decide⟩

/-- **The law at the reached calls is not necessary for one program.** In
`envSafeSucc` (safe trait; the impl returns its argument plus one, with no effect),
`deadCall` from initial store `σ0` reaches the call of instance `0` at argument `5`,
where the copy law fails, yet clone→copy refines the direct capture of `deadCall` with
relies point `before`: the result is never used. -/
theorem cex_lawOnReached_not_necessary_for_one_program :
    ¬ LawOnReached envSafeSucc cloneToCopy deadCall σ0 ∧
      RefinesPP (capDirect envSafeSucc .before deadCall σ0)
        (compiled envSafeSucc (cloneToCopy.apply deadCall) σ0) := by
  refine ⟨?_, by decide⟩
  intro h
  have hr : Reaches envSafeSucc deadCall σ0 0 5 := by simp [Reaches, deadCall, Store.upd]
  have := h 0 5 rfl hr
  simp [LawAt, envSafeSucc, succClone, cloneToCopy, copyImpl] at this

/-- An effectful safe impl (`envSafeLog`) breaks clone→copy even on `deadCall` from `σ0`,
because the call's effect `9` is observable although its return value is unused. -/
theorem cex_deadCall_effectful_not_refined :
    ¬ RefinesPP (capDirect envSafeLog .before deadCall σ0)
      (compiled envSafeLog (cloneToCopy.apply deadCall) σ0) := by
  decide

/-- Tightness of `hsafe` in `lawAt_of_refinesPP_probe_of_safe_of_targets`: instance `0` of
`envUnsafeLog` is unsafe (not safe), targeted by clone→copy, and the rewrite refines
the direct capture of `probe 0 5` with the relies point before the impl, yet the law
fails at `5`. -/
theorem cex_probe_unsafe_before :
    envUnsafeLog.safety 0 ≠ .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envUnsafeLog cloneToCopy 0 5 :=
  ⟨by decide, rfl, by decide, by unfold LawAt; decide⟩

/-- Tightness of `ht` in `lawAt_of_refinesPP_probe_of_safe_of_targets`: instance `0` of
`envSafeLog` is safe and `cloneToCopy1` (whose targets are exactly instance `1`) refines the
direct capture of `probe 0 5`, yet the law of `cloneToCopy1` fails at instance `0`. -/
theorem cex_probe_untargeted :
    envSafeLog.safety 0 = .safeTrait ∧ cloneToCopy1.targets 0 = false ∧
      RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy1.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envSafeLog cloneToCopy1 0 5 :=
  ⟨rfl, rfl, by decide, by unfold LawAt; decide⟩

/-- Tightness of `href` in `lawAt_of_refinesPP_probe_of_safe_of_targets`: instance `0` of
`envSafeLog` is safe and targeted by clone→copy, the rewrite does not refine the direct
capture of `probe 0 5` from `σ0` with relies point `before`, and the law fails at `5`. -/
theorem cex_probe_no_refinement :
    envSafeLog.safety 0 = .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ LawAt envSafeLog cloneToCopy 0 5 :=
  ⟨rfl, rfl, by decide, lawAt_neg⟩

/-- Tightness of `hunsafe` in the unsafe-trait theorems: `envSafeLog` with clone→copy
satisfies `ReplIsContract`, its targeted instance is safe, and the rewrite refines the
direct capture of the probe neither with the relies point before the impl
(prefix-preserving) nor after it (whole-trace). -/
theorem cex_without_targetsUnsafe :
    ¬ TargetsUnsafe envSafeLog cloneToCopy ∧ ReplIsContract envSafeLog cloneToCopy ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envSafeLog .after (probe 0 5) σ0)
        (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0) :=
  ⟨targetsUnsafe_neg, replIsContract_pos, by decide, by decide, by decide⟩

/-- Tightness of `hrepl` in the unsafe-trait theorems: in `envUnsafeTriv` (unsafe trait,
the impl is a copy and satisfies the contract) every instance `succRewrite` targets is
unsafe, but it substitutes `succClone`, not the contract; the direct capture of
the probe emits `5`, the rewritten program emits `6`, and neither refinement holds,
for either relies position. -/
theorem cex_without_replIsContract :
    TargetsUnsafe envUnsafeTriv succRewrite ∧ ¬ ReplIsContract envUnsafeTriv succRewrite ∧
      ¬ RefinesPP (capDirect envUnsafeTriv .before (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envUnsafeTriv .before (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) ∧
      ¬ RefinesWT (capDirect envUnsafeTriv .after (probe 0 5) σ0)
        (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0) :=
  ⟨fun _ _ => rfl, replIsContract_neg, by decide, by decide, by decide⟩

/-- **Relies point after the impl's effects: an effectful unsafe contract violation can
break lawless prefix-preserving refinement.** In `envUnsafeLog` with clone→copy (every
hypothesis of the unsafe-trait theorems holds), from initial store `σ0` with the relies
point after the impl the direct capture of `probe 0 5` is UB after the event `9`, the
rewritten program terminates normally after emitting `5`, and prefix-preserving
refinement fails. Whole-trace refinement holds for this program with relies point `after`,
and prefix-preserving refinement holds with the relies point `before` the impl. -/
theorem cex_relies_after_effect_not_refined :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      capDirect envUnsafeLog .after (probe 0 5) σ0 = [.ub [9]] ∧
      compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0 = [.done [5]] ∧
      ¬ RefinesPP (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesWT (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) :=
  ⟨targetsUnsafe_pos, replIsContract_pos, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Verification of the direct capture of unsafe calls -/

/-- Tightness of `hunsafe` in
`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`:
with `envSafeLog` and clone→copy, `ReplIsContract` holds, the specification "terminates
after emitting `9`, `5`" is UB-free and verified of the direct capture of the probe, and
it fails for the rewritten program. -/
theorem cex_transfer_safe_target :
    ¬ TargetsUnsafe envSafeLog cloneToCopy ∧ ReplIsContract envSafeLog cloneToCopy ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      ¬ Sat (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [9, 5]) :=
  ⟨targetsUnsafe_neg, replIsContract_pos, (fun _ h => by cases h), by decide, by decide⟩

/-- Tightness of `hrepl` in
`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`:
with `envUnsafeTriv` and `succRewrite`, every targeted instance is unsafe, "terminates
after emitting `5`" is UB-free and verified of the direct capture of the probe, and it
fails for the rewritten program. -/
theorem cex_transfer_repl_not_contract :
    TargetsUnsafe envUnsafeTriv succRewrite ∧ ¬ ReplIsContract envUnsafeTriv succRewrite ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeTriv .before (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      ¬ Sat (compiled envUnsafeTriv (succRewrite.apply (probe 0 5)) σ0)
        (fun b => b = .done [5]) :=
  ⟨fun _ _ => rfl, replIsContract_neg, (fun _ h => by cases h), by decide, by decide⟩

/-- **UB-tolerant verification does not transfer.** With `envUnsafeLog` and clone→copy
(every targeted instance unsafe, `ReplIsContract`), the specification "UB before any
event, or termination after emitting `9`, `5`" is verified of the direct capture of
`probe 0 5` from `σ0` (relies point `before` the impl), is satisfied by a UB behaviour,
and fails for the rewritten program. -/
theorem cex_ub_tolerant_spec_no_transfer :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      ¬ UBFreeSpec (fun b => b = .ub [] ∨ b = .done [9, 5]) ∧
      Sat (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (fun b => b = .ub [] ∨ b = .done [9, 5]) ∧
      ¬ Sat (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .ub [] ∨ b = .done [9, 5]) :=
  ⟨targetsUnsafe_pos, replIsContract_pos, fun h => h [] (Or.inl rfl), by decide, by decide⟩

/-- Tightness of `hsat` in
`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`:
with `envUnsafeTriv` and clone→copy (every targeted instance unsafe, `ReplIsContract`),
the UB-free specification "terminates after emitting `7`" is not verified of the direct
capture of the probe, and fails for the rewritten program. -/
theorem cex_transfer_unverified :
    TargetsUnsafe envUnsafeTriv cloneToCopy ∧ ReplIsContract envUnsafeTriv cloneToCopy ∧
      UBFreeSpec (fun b => b = .done [7]) ∧
      ¬ Sat (capDirect envUnsafeTriv .before (probe 0 5) σ0) (fun b => b = .done [7]) ∧
      ¬ Sat (compiled envUnsafeTriv (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [7]) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, (fun _ h => by cases h), by decide, by decide⟩

/-- Tightness of `hunsafe` in `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`:
in `envSafeLog`, instance `0` is safe (not unsafe), `probe 0 5` from `σ0` reaches
`(0, 5)`, and "terminates after emitting `9`, `5`" is UB-free and holds of the direct
capture, yet the impl violates its contract at `(0, 5)`. -/
theorem cex_contract_discharge_safe_call :
    envSafeLog.safety 0 ≠ .unsafeTrait ∧
      Reaches envSafeLog (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      envSafeLog.impl 0 5 ≠ envSafeLog.contract 0 5 :=
  ⟨by decide, reaches_pos, (fun _ h => by cases h), by decide, by decide⟩

/-- Tightness of `hreach` in `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`:
in `envUnsafeSelective`, instance `0` is unsafe, `(0, 0)` is not reached by `probe 0 5`
from `σ0`, and "terminates after emitting `5`" is UB-free and holds of the direct
capture (relies point `after`), yet the impl violates its contract at the unreached
argument `0`. -/
theorem cex_contract_discharge_unreached_arg :
    envUnsafeSelective.safety 0 = .unsafeTrait ∧
      ¬ Reaches envUnsafeSelective (probe 0 5) σ0 0 0 ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeSelective .after (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      envUnsafeSelective.impl 0 0 ≠ envUnsafeSelective.contract 0 0 :=
  ⟨rfl, by simp [Reaches, probe, Store.upd], (fun _ h => by cases h), by decide, by decide⟩

/-- Tightness of `hub` in `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`:
instance `0` of `envUnsafeLog` is unsafe, `probe 0 5` from `σ0` reaches `(0, 5)`, the
trivial specification is not UB-free and holds of the direct capture, and the impl
violates the contract there. -/
theorem cex_contract_discharge_ub_tolerant :
    envUnsafeLog.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeLog (probe 0 5) σ0 0 5 ∧
      ¬ UBFreeSpec (fun _ => True) ∧
      Sat (capDirect envUnsafeLog .before (probe 0 5) σ0) (fun _ => True) ∧
      envUnsafeLog.impl 0 5 ≠ envUnsafeLog.contract 0 5 :=
  ⟨rfl, by simp [Reaches, probe, Store.upd], ubFreeSpec_neg, fun _ _ => trivial, by decide⟩

/-- Tightness of `hsat` in `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`:
instance `0` of `envUnsafeLog` is unsafe, `probe 0 5` from `σ0` reaches `(0, 5)`, the
UB-free specification "terminates after emitting `9`, `5`" is not verified of the
direct capture (which is UB), and the impl violates the contract there. -/
theorem cex_contract_discharge_unverified :
    envUnsafeLog.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeLog (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [9, 5]) ∧
      ¬ Sat (capDirect envUnsafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      envUnsafeLog.impl 0 5 ≠ envUnsafeLog.contract 0 5 :=
  ⟨rfl, by simp [Reaches, probe, Store.upd], (fun _ h => by cases h), by decide, by decide⟩

/-- Tightness of `hsat` in `sat_compiled_applyAt_of_sat_capRel` and
`sat_compiled_and_apply_of_sat_capRel`: "terminates after emitting `5`" is not verified
of the relational capture of `probe 0 5` from `σ0` in `envSafeLog` for clone→copy, and
fails for the compiled probe with no site rewritten (and hence for the conjunction of
unrewritten and fully rewritten compiled probes). -/
theorem cex_capRel_sound_unverified :
    ¬ Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      ¬ Sat (compiled envSafeLog (cloneToCopy.applyAt (fun _ => false) 0 (probe 0 5)) σ0)
        (fun b => b = .done [5]) ∧
      ¬ (Sat (compiled envSafeLog (probe 0 5) σ0) (fun b => b = .done [5]) ∧
          Sat (compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0)
            (fun b => b = .done [5])) := by
  decide

/-! ## Relational capture -/

/-- **Relational capture is not the weakest semantics for all-or-nothing rewriting.**
With `envSafeLog` and clone→copy on `twoCalls` (two calls of instance `0`) from `σ0`,
the specification "not terminate after emitting `[9]`" holds of the compiled program
without the rewrite and of the compiled program with the rewrite at every site, but not
of the relational capture, which also contains the mixed runs (one call rewritten, the
other not). -/
theorem cex_capRel_not_weakest_for_all_or_nothing :
    Sat (compiled envSafeLog twoCalls σ0) (fun b => b ≠ .done [9]) ∧
      Sat (compiled envSafeLog (cloneToCopy.apply twoCalls) σ0) (fun b => b ≠ .done [9]) ∧
      ¬ Sat (capRel envSafeLog [cloneToCopy] twoCalls σ0) (fun b => b ≠ .done [9]) := by
  decide

/-- **Relational capture loses effect-dependent properties.** With `envSafeLog` and
clone→copy from initial store `σ0` (relies point `before`), "terminates after emitting
`9`, `5`" (the clone's effect happens) holds of the direct capture of `probe 0 5` but
not of its relational capture. -/
theorem cex_capRel_loses_effect_property :
    Sat (capDirect envSafeLog .before (probe 0 5) σ0) (fun b => b = .done [9, 5]) ∧
      ¬ Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b = .done [9, 5]) := by
  decide

/-- Tightness of `hD` in `capRel_subset_of_sound_for_every_applyAt`: the empty
behaviour set fails the soundness hypothesis `hD` on `probe 0 5` from `σ0` in
`envSafeLog` with clone→copy, and does not contain the relational capture. -/
theorem cex_capRel_subset_without_soundness :
    ¬ (∀ spec : Beh → Prop, (∀ b, (fun _ => False : Beh → Prop) b → spec b) →
        ∀ S : Nat → Bool,
          Sat (compiled envSafeLog (cloneToCopy.applyAt S 0 (probe 0 5)) σ0) spec) ∧
      ¬ (∀ b ∈ capRel envSafeLog [cloneToCopy] (probe 0 5) σ0,
          (fun _ => False : Beh → Prop) b) := by
  refine ⟨?_, ?_⟩
  · intro hD
    exact hD (fun _ => False) (fun _ h => h) (fun _ => false) (.done [9, 5]) (by decide)
  · intro h
    exact h (.done [9, 5]) (by decide)

/-! ## Fail-closed rejection of rewritable calls -/

/-- The compiled probe of `envSafeLog` emits `9`, `5` from every store. -/
theorem compiled_envSafeLog_probe (σ : Store) :
    compiled envSafeLog (probe 0 5) σ = [.done [9, 5]] := rfl

/-- The compiled clone→copy probe of `envSafeLog` emits `5` from every store. -/
theorem compiled_envSafeLog_probe_rewritten (σ : Store) :
    compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ = [.done [5]] := rfl

/-- **Rejecting rewritable calls is incomplete.** `capRejectRewritable` for the targets
of clone→copy rejects the probe, although in `envSafeTriv` (the law holds) every
compiled run of the rewritten probe is a run of the probe itself, so capturing the
probe unchanged would over-approximate there. -/
theorem capRejectRewritable_incomplete :
    capRejectRewritable cloneToCopy.targets (probe 0 5) = .error () ∧
      DenIncl (compiledDen envSafeTriv (cloneToCopy.apply (probe 0 5)))
        (compiledDen envSafeTriv (probe 0 5)) := by
  refine ⟨rfl, ?_⟩
  intro r hr
  unfold compiledDen at hr ⊢
  rwa [compiled_apply_eq_of_repl_eq_impl envSafeTriv cloneToCopy (fun _ _ => rfl)] at hr

/-- Tightness of `hR` in `capRejectRewritable_compiledDen_transferSound`: with `R`
rejecting nothing, clone→copy targets an instance outside `R`; for the exact verifier of
`compiledDen envSafeLog` (which is sound), the probe is captured unchanged and verified
to emit `9`, `5`, while the rewritten compiled probe emits `5`. -/
theorem cex_capRejectRewritable_target_outside_R :
    ¬ (∀ i, cloneToCopy.targets i = true → (fun _ => false : Inst → Bool) i = true) ∧
      VerifierSound (compiledDen envSafeLog)
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) ∧
      ¬ TransferSound (fun p => compiledDen envSafeLog (cloneToCopy.apply p))
        (capRejectRewritable (fun _ => false))
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) := by
  refine ⟨(fun h => by cases h 0 rfl), fun _ _ h => h, ?_⟩
  intro h
  have hcap : capRejectRewritable (fun _ => false) (probe 0 5) = .ok (probe 0 5) := rfl
  have hver : CaptureBridge.Sat (compiledDen envSafeLog (probe 0 5))
      (fun r => r.2 = .done [9, 5]) := by
    intro r hr
    unfold compiledDen at hr
    rw [compiled_envSafeLog_probe] at hr
    simpa using hr
  have := h (probe 0 5) (probe 0 5) (fun r => r.2 = .done [9, 5]) hcap hver (σ0, .done [5])
    (show Beh.done [5] ∈ compiled envSafeLog (cloneToCopy.apply (probe 0 5)) σ0 by decide)
  simp at this

/-- Tightness of `hV` in `capRejectRewritable_compiledDen_transferSound`: the verifier
that accepts every specification is not sound, and verification does not transfer
through `capRejectRewritable` for the targets of clone→copy (the program `[]` is
accepted and "no run" is verified of it). -/
theorem cex_capRejectRewritable_unsound_verifier :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      ¬ VerifierSound (compiledDen envSafeTriv) (fun _ _ => True) ∧
      ¬ TransferSound (fun p => compiledDen envSafeTriv (cloneToCopy.apply p))
        (capRejectRewritable cloneToCopy.targets) (fun _ _ => True) := by
  refine ⟨fun _ h => h, ?_, ?_⟩
  · intro h
    exact h [] (fun _ => False) trivial (σ0, .done []) (by unfold compiledDen; decide)
  · intro h
    exact h [] [] (fun _ => False) rfl trivial (σ0, .done []) (by unfold compiledDen; decide)

/-- `compiledDen` admits the compiled behaviour of the probe from `σ0`. -/
theorem compiledDen_pos : compiledDen envSafeLog (probe 0 5) (σ0, .done [9, 5]) := by
  unfold compiledDen; decide

/-- `compiledDen` rejects a behaviour the compiled probe does not exhibit. -/
theorem compiledDen_neg : ¬ compiledDen envSafeLog (probe 0 5) (σ0, .done [5]) := by
  unfold compiledDen; decide

/-- `capDirectDen` admits the direct-capture UB behaviour of an unsafe contract-violating
call. -/
theorem capDirectDen_pos : capDirectDen envUnsafeLog .before (probe 1 5) (σ0, .ub []) := by
  unfold capDirectDen; decide

/-- `capDirectDen` rejects the normal compiled behaviour when the direct capture is UB. -/
theorem capDirectDen_neg : ¬ capDirectDen envUnsafeLog .before (probe 1 5) (σ0, .done [9, 5]) := by
  unfold capDirectDen; decide

/-- `capRejectRewritable` is not `TransferSound` for a verifier sound for `capDirectDen`
on UB-tolerant specifications: `probe 1 5` calls only untargeted unsafe instance `1`, so
`capRejectRewritable cloneToCopy.targets` accepts it unchanged; the UB-tolerant
specification `r.2 = .ub []` holds of `capDirectDen envUnsafeLog .before` and fails on
`compiledDen envUnsafeLog`. -/
theorem cex_capRejectRewritable_not_transferSound_for_capDirect :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      VerifierSound (capDirectDen envUnsafeLog .before)
        (fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec) ∧
      ¬ TransferSound (fun p => compiledDen envUnsafeLog (cloneToCopy.apply p))
        (capRejectRewritable cloneToCopy.targets)
        (fun q spec => CaptureBridge.Sat (capDirectDen envUnsafeLog .before q) spec) := by
  refine ⟨fun _ h => h, fun _ _ h => h, ?_⟩
  intro htr
  have hok : capRejectRewritable cloneToCopy.targets (probe 1 5) = .ok (probe 1 5) := rfl
  have hver : CaptureBridge.Sat
      (capDirectDen envUnsafeLog .before (probe 1 5)) (fun r => r.2 = .ub []) := by
    intro ⟨σ, b⟩ hb
    unfold capDirectDen at hb
    have hcap : capDirect envUnsafeLog .before (probe 1 5) σ = [.ub []] := rfl
    rw [hcap, List.mem_singleton] at hb
    exact hb
  have hbad := htr (probe 1 5) (probe 1 5) (fun r => r.2 = .ub []) hok hver (σ0, .done [9, 5])
    (show Beh.done [9, 5] ∈ compiled envUnsafeLog (cloneToCopy.apply (probe 1 5)) σ0 by decide)
  cases hbad

/-! ## Sequences of rewrites -/

/-- Tightness of `hlaw` in `refinesPP_capDirect_applySeq_of_lawOnReached`: the
one-element sequence `[cloneToCopy]` in `envSafeLog` does not satisfy the law at the
reached call of the probe, and does not refine. -/
theorem cex_applySeq_without_law :
    ¬ (∀ ρ ∈ [cloneToCopy], LawOnReached envSafeLog ρ (probe 0 5) σ0) ∧
      ¬ RefinesPP (capDirect envSafeLog .before (probe 0 5) σ0)
        (compiled envSafeLog (applySeq [cloneToCopy] (probe 0 5)) σ0) :=
  ⟨fun h => lawOnReached_neg (h cloneToCopy (List.mem_singleton.mpr rfl)), by decide⟩

/-- Environment for sequential non-composition of per-program refinement: safe trait,
instance `0` returns `10` without effects, instance `1` returns `0` without effects. -/
def envSeqChain : Env :=
  { impl := fun i _ => if i == 0 then ([], 10) else ([], 0)
    contract := fun _ => copyImpl
    safety := fun _ => .safeTrait }

/-- Rewrite on instance `1` that returns `0` at argument `10` (agreeing with
`envSeqChain`) and returns `99` at every other argument. -/
def guardTenRewrite : Rewrite :=
  { targets := fun i => i == 1
    repl := fun _ v => if v == 10 then ([], 0) else ([], 99) }

/-- Call instance `0` on `5` into variable `1`, then call instance `1` on variable `1`
into variable `2`, and emit variable `2`. -/
def seqChainProg : Prog :=
  [.set 0 5, .call 0 1 0, .call 1 2 1, .out 2]

/-- Per-program refinement is not closed under sequential composition without
`LawOnReached`: on `seqChainProg` from `σ0` in `envSeqChain`, `cloneToCopy` alone
refines `seqChainProg` (changing the intermediate value from `10` to `5` while `call 1`
still returns `0`), and `guardTenRewrite` alone satisfies `LawOnReached` and refines
`seqChainProg`, yet `applySeq [cloneToCopy, guardTenRewrite] seqChainProg` emits `[99]`
and fails to refine `seqChainProg` (`[0]`). -/
theorem cex_refining_rewrites_seq_not_refining :
    ¬ LawOnReached envSeqChain cloneToCopy seqChainProg σ0 ∧
      RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (cloneToCopy.apply seqChainProg) σ0) ∧
      LawOnReached envSeqChain guardTenRewrite seqChainProg σ0 ∧
      RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (guardTenRewrite.apply seqChainProg) σ0) ∧
      ¬ RefinesPP (capDirect envSeqChain .before seqChainProg σ0)
        (compiled envSeqChain (applySeq [cloneToCopy, guardTenRewrite] seqChainProg) σ0) := by
  refine ⟨?_, by decide, ?_, by decide, by decide⟩
  · intro h
    have hr : Reaches envSeqChain seqChainProg σ0 0 5 := by
      simp [Reaches, seqChainProg, Store.upd]
    have h0 := h 0 5 rfl hr
    simp [LawAt, envSeqChain, cloneToCopy, copyImpl] at h0
  · intro i v ht hr
    simp only [guardTenRewrite, beq_iff_eq] at ht
    subst ht
    simp [Reaches, seqChainProg, envSeqChain, Store.upd] at hr
    subst hr
    rfl

/-- **Overlapping rewrites: the conjunction of the laws is not necessary.** In
`envSafeTriv` (safe trait, the impl is a copy), the sequence clone→copy then
`succRewrite` (both target instance `0`) refines the direct capture on every program
and store with relies point `before`, because clone→copy satisfies `LawOnTargets` and
has already replaced every call `succRewrite` could match; yet `ContextSafeAt` fails for
the shadowed `succRewrite` at instance `0` and argument `0`. -/
theorem cex_overlapping_rewrites_conjunction_not_necessary :
    ¬ [cloneToCopy, succRewrite].Pairwise TargetsDisjoint ∧
      LawOnTargets envSafeTriv cloneToCopy ∧
      (∀ (p : Prog) (σ : Store),
        RefinesPP (capDirect envSafeTriv .before p σ)
          (compiled envSafeTriv (applySeq [cloneToCopy, succRewrite] p) σ)) ∧
      ¬ ContextSafeAt envSafeTriv .before succRewrite 0 0 ∧
      ¬ (∀ ρ ∈ [cloneToCopy, succRewrite], ∀ i, ρ.targets i = true → ∀ v,
          ContextSafeAt envSafeTriv .before ρ i v) := by
  have hnot0 : ¬ ContextSafeAt envSafeTriv .before succRewrite 0 0 := by
    rintro (h1 | ⟨h2, _, _⟩)
    · simp [LawAt, envSafeTriv, succRewrite, succClone, copyImpl] at h1
    · cases h2
  refine ⟨?_, lawOnTargets_pos, ?_, hnot0, ?_⟩
  · intro h
    have := List.rel_of_pairwise_cons h (List.mem_singleton.mpr rfl)
    exact targetsDisjoint_neg this
  · intro p σ
    rw [applySeq_pair, apply_apply_of_targets_le cloneToCopy succRewrite (fun _ h => h),
      compiled_apply_eq_of_repl_eq_impl envSafeTriv cloneToCopy (fun _ _ => rfl),
      capDirect_eq_compiled_of_allSafe envSafeTriv .before (fun _ => rfl)]
    exact refinesPP_refl _
  · intro h
    exact hnot0 (h succRewrite (by simp) 0 rfl 0)

/-- Tightness of `hcov` in `mem_capRel_of_mem_compiled_applySeq_of_coveredBy`:
clone→copy is not covered by the empty list, and the rewritten probe's behaviour
(emit `5`) is not a behaviour of the relational capture for no rewrite. -/
theorem cex_without_coveredBy :
    ¬ (∀ ρ ∈ [cloneToCopy], CoveredBy [] ρ) ∧
      ¬ (∀ b ∈ compiled envSafeLog (applySeq [cloneToCopy] (probe 0 5)) σ0,
          b ∈ capRel envSafeLog [] (probe 0 5) σ0) :=
  ⟨fun h => coveredBy_neg (h cloneToCopy (List.mem_singleton.mpr rfl)), by decide⟩

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity of `refinesPP_capDirect_apply_of_lawOnReached`: in `envSafeTriv` the law
holds at the reached call of the probe, and the conclusion holds. In `envSafeLog` the
law holds at every reached call of `[ub, call 0 1 0]` (the call is unreachable) and the
conclusion holds although the law fails at every argument. -/
theorem nonvacuity_lawOnReached :
    LawOnReached envSafeTriv cloneToCopy (probe 0 5) σ0 ∧
      RefinesPP (capDirect envSafeTriv .before (probe 0 5) σ0)
        (compiled envSafeTriv (cloneToCopy.apply (probe 0 5)) σ0) ∧
      LawOnReached envSafeLog cloneToCopy [.ub, .call 0 1 0] σ0 ∧
      RefinesPP (capDirect envSafeLog .before [.ub, .call 0 1 0] σ0)
        (compiled envSafeLog (cloneToCopy.apply [.ub, .call 0 1 0]) σ0) :=
  ⟨lawOnReached_pos, by decide, lawOnReached_unreached, by decide⟩

/-- Non-vacuity of `refinesPP_every_context_iff_contextSafeAt`: its right-hand side
holds across all three positive branches — for a lawful impl (`envSafeTriv`, relies
point `after`), for an unsafe contract violation with relies point `before`
(`envUnsafeLog`), and for an unsafe contract violation with relies point `after` whose
impl effects are a prefix of the replacement's (`envUnsafeSucc`) — and fails for a safe
law violation (`envSafeLog`), for an unsafe violation with relies point `after` an
effect the replacement lacks (`envUnsafeLog`), and for a non-contract replacement on a
lawful unsafe impl (`envUnsafeTriv`, `succRewrite`). -/
theorem nonvacuity_contextSafeAt :
    (∀ i, cloneToCopy.targets i = true → ∀ v, ContextSafeAt envSafeTriv .after cloneToCopy i v) ∧
      (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeLog .before cloneToCopy i v) ∧
      (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeSucc .after cloneToCopy i v) ∧
      ¬ (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envSafeLog .before cloneToCopy i v) ∧
      ¬ (∀ i, cloneToCopy.targets i = true → ∀ v,
        ContextSafeAt envUnsafeLog .after cloneToCopy i v) ∧
      ¬ (∀ i, succRewrite.targets i = true → ∀ v,
        ContextSafeAt envUnsafeTriv .before succRewrite i v) := by
  refine ⟨fun _ _ _ => Or.inl rfl, ?_, ?_, fun h => contextSafeAt_neg_safe (h 0 rfl 5),
    fun h => contextSafeAt_neg_after (h 0 rfl 5),
    fun h => contextSafeAt_neg_unsafe_lawful_noncontract.2 (h 0 rfl 5)⟩
  · intro i _ v
    refine Or.inr ⟨rfl, ?_, Or.inl rfl⟩
    simp [envUnsafeLog, loggingClone, copyImpl]
  · intro i _ v
    refine Or.inr ⟨rfl, ?_, Or.inr List.nil_prefix⟩
    simp [envUnsafeSucc, succClone, copyImpl]

/-- Non-vacuity of `lawAt_of_refinesPP_probe_of_safe_of_targets`: in `envSafeTriv`
instance `0` is safe and targeted, and the rewrite refines on the probe. -/
theorem nonvacuity_probe_safe :
    envSafeTriv.safety 0 = .safeTrait ∧ cloneToCopy.targets 0 = true ∧
      RefinesPP (capDirect envSafeTriv .before (probe 0 5) σ0)
        (compiled envSafeTriv (cloneToCopy.apply (probe 0 5)) σ0) :=
  ⟨rfl, rfl, by decide⟩

/-- Non-vacuity of the unsafe-trait theorems, in the case where the impl violates the
contract: `envUnsafeLog` with clone→copy satisfies both hypotheses, and both
conclusions hold on the probe (prefix-preserving with the relies point before the
impl; whole-trace with it after). -/
theorem nonvacuity_unsafe :
    TargetsUnsafe envUnsafeLog cloneToCopy ∧ ReplIsContract envUnsafeLog cloneToCopy ∧
      RefinesPP (capDirect envUnsafeLog .before (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) ∧
      RefinesWT (capDirect envUnsafeLog .after (probe 0 5) σ0)
        (compiled envUnsafeLog (cloneToCopy.apply (probe 0 5)) σ0) :=
  ⟨targetsUnsafe_pos, replIsContract_pos, by decide, by decide⟩

/-- Non-vacuity of
`sat_compiled_apply_of_targetsUnsafe_of_replIsContract_of_ubFreeSpec_of_sat_capDirect`
and `contract_at_reached_unsafe_of_sat_capDirect_of_ubFreeSpec`: in `envUnsafeSelective`
(whose impl agrees with `copyImpl` at `5` and violates it at every other argument, so
`LawOnTargets` fails globally), with clone→copy and relies point `after`, "terminates
after emitting `5`" is UB-free and verified of the direct capture of `probe 0 5` from
`σ0`; it holds of the rewritten program, the execution reaches the unsafe call `(0, 5)`,
and the impl agrees with the contract there. -/
theorem nonvacuity_ubFree_verification :
    ¬ LawOnTargets envUnsafeSelective cloneToCopy ∧
      TargetsUnsafe envUnsafeSelective cloneToCopy ∧
      ReplIsContract envUnsafeSelective cloneToCopy ∧
      envUnsafeSelective.safety 0 = .unsafeTrait ∧
      Reaches envUnsafeSelective (probe 0 5) σ0 0 5 ∧
      UBFreeSpec (fun b => b = .done [5]) ∧
      Sat (capDirect envUnsafeSelective .after (probe 0 5) σ0) (fun b => b = .done [5]) ∧
      Sat (compiled envUnsafeSelective (cloneToCopy.apply (probe 0 5)) σ0)
        (fun b => b = .done [5]) ∧
      envUnsafeSelective.impl 0 5 = envUnsafeSelective.contract 0 5 := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl, rfl, ?_, (fun _ h => by cases h),
    by decide, by decide, rfl⟩
  · intro h
    have h0 := h 0 rfl 0
    simp [LawAt, envUnsafeSelective, cloneToCopy, copyImpl] at h0
  · simp [Reaches, probe, Store.upd]

/-- Non-vacuity of `sat_compiled_applyAt_of_sat_capRel` and
`sat_compiled_and_apply_of_sat_capRel`: "the last emitted value is `5`" holds of the
relational capture of `probe 0 5` in `envSafeLog` for clone→copy. -/
theorem nonvacuity_capRel_sound :
    Sat (capRel envSafeLog [cloneToCopy] (probe 0 5) σ0) (fun b => b.trace.getLast? = some 5) := by
  decide

/-- Non-vacuity of `capRel_subset_of_sound_for_every_applyAt`: the two-element set
{emit `9`, `5`; emit `5`} satisfies `hD` for the probe in `envSafeLog` with clone→copy
(every site selection gives one of its two behaviours). -/
theorem nonvacuity_capRel_subset :
    ∀ spec : Beh → Prop,
      (∀ b, (b = .done [9, 5] ∨ b = .done [5]) → spec b) →
      ∀ S : Nat → Bool, Sat (compiled envSafeLog (cloneToCopy.applyAt S 0 (probe 0 5)) σ0) spec := by
  intro spec hspec S
  have h0 : ∀ (c : Bool) (s : Stmt), (if c = true then s else s) = s := fun c s => by cases c <;> rfl
  have happ : cloneToCopy.applyAt S 0 (probe 0 5) =
      [.set 0 5, if S 1 = true then .prim copyImpl 1 0 else .call 0 1 0, .out 1] := by
    simp only [probe, Rewrite.applyAt]
    congr 1
    · exact h0 _ _
    · congr 1
      exact congrArg (List.cons · []) (h0 _ _)
  rw [happ]
  cases S 1 with
  | true =>
    intro b hb
    have : compiled envSafeLog [.set 0 5, .prim copyImpl 1 0, .out 1] σ0 = [.done [5]] := by decide
    simp only [↓reduceIte, this, List.mem_singleton] at hb
    exact hspec b (Or.inr hb)
  | false =>
    intro b hb
    have : compiled envSafeLog [.set 0 5, .call 0 1 0, .out 1] σ0 = [.done [9, 5]] := by decide
    simp only [Bool.false_eq_true, ↓reduceIte, this, List.mem_singleton] at hb
    exact hspec b (Or.inl hb)

/-- Non-vacuity of `capRejectRewritable_compiledDen_transferSound`: the targets of
clone→copy satisfy `hR` for `R = cloneToCopy.targets`, the exact verifier is sound, and
a program whose every call is of instance `1` is accepted unchanged. -/
theorem nonvacuity_capRejectRewritable :
    (∀ i, cloneToCopy.targets i = true → cloneToCopy.targets i = true) ∧
      VerifierSound (compiledDen envSafeLog)
        (fun q spec => CaptureBridge.Sat (compiledDen envSafeLog q) spec) ∧
      capRejectRewritable cloneToCopy.targets [.call 1 1 0] = .ok [.call 1 1 0] :=
  ⟨fun _ h => h, fun _ _ h => h, rfl⟩

/-- Non-vacuity of `refinesPP_capDirect_applySeq_of_lawOnReached` and of
`refinesPP_every_context_applySeq_iff_of_pairwise_disjoint`: in `envSafeTriv`, the
sequence clone→copy on instance `0` then on instance `1` has disjoint targets, each
law holds at every reached call (and `ContextSafeAt` holds everywhere), and the
sequence refines on a program calling both instances. -/
theorem nonvacuity_applySeq :
    [cloneToCopy, cloneToCopy1].Pairwise TargetsDisjoint ∧
      (∀ ρ ∈ [cloneToCopy, cloneToCopy1],
        LawOnReached envSafeTriv ρ [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2] σ0) ∧
      (∀ ρ ∈ [cloneToCopy, cloneToCopy1], ∀ i, ρ.targets i = true → ∀ v,
        ContextSafeAt envSafeTriv .before ρ i v) ∧
      RefinesPP (capDirect envSafeTriv .before [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2] σ0)
        (compiled envSafeTriv
          (applySeq [cloneToCopy, cloneToCopy1] [.set 0 5, .call 0 1 0, .call 1 2 0, .out 1, .out 2])
          σ0) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons (fun _ h => by cases h) List.Pairwise.nil)
    intro ρ hρ
    rw [List.mem_singleton] at hρ
    subst hρ
    exact targetsDisjoint_pos
  · intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl <;> exact fun _ _ _ _ => rfl
  · intro ρ hρ i _ v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl <;> exact Or.inl rfl

/-- Non-vacuity of `mem_capRel_of_mem_compiled_applySeq_of_coveredBy`: `succRewrite` is
covered by `[cloneToCopy, succRewrite]`, and the behaviour of the probe rewritten by
`succRewrite` (emit `6`) is a behaviour of the relational capture for that list. -/
theorem nonvacuity_coveredBy :
    (∀ ρ ∈ [succRewrite], CoveredBy [cloneToCopy, succRewrite] ρ) ∧
      (∀ b ∈ compiled envSafeLog (applySeq [succRewrite] (probe 0 5)) σ0,
        b ∈ capRel envSafeLog [cloneToCopy, succRewrite] (probe 0 5) σ0) := by
  refine ⟨?_, by decide⟩
  intro ρ hρ
  rw [List.mem_singleton] at hρ
  subst hρ
  intro i hi
  exact ⟨succRewrite, by simp, hi, rfl⟩

end Toy.LawRewrite
