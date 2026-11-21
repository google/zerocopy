import SchedAdequacy.Examples
import SchedAdequacy.Lemmas

/-!
# Main results

Main theorems over arbitrary programs and generators, with their countermodels,
tightness witnesses, non-vacuity instances and positive controls. Tightness
witnesses are stated in canonical form: every other hypothesis holds and the
conclusion fails.
-/

namespace Toy.SchedAdequacy

open Act Prog

variable {α : Type}

/-! ## The per-step oracle is adequate -/

/-- **Per-step soundness.** For every program `p`, every run of the per-step
generator `runPerStep` is an interleaving of `p`. -/
theorem perStep_sound (p : Prog α) : Sound runPerStep p :=
  fun o => runPerStepAux_mem p.size p o rfl

/-- **Per-step completeness.** For every program `p`, every interleaving of `p` is
the run of `runPerStep` for some oracle. -/
theorem perStep_complete (p : Prog α) : Complete runPerStep p :=
  runPerStepAux_complete p.size p rfl

/-- Instance of `perStep_sound` and `perStep_complete` on `a ∥ (b ∥ c)`, fully proved by evaluation. -/
theorem perStep_adequate_parA_parBC :
    Sound runPerStep parA_parBC ∧ Complete runPerStep parA_parBC := by
  refine ⟨?_, complete_pos⟩
  intro o
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl

/-- Instance of `perStep_sound` and `perStep_complete` on `a ∥ ((b ∥ c) ; d)`,
fully proved by evaluation. -/
theorem perStep_adequate_parA_seqParBC_D :
    Sound runPerStep parA_seqParBC_D ∧ Complete runPerStep parA_seqParBC_D := by
  refine ⟨?_, complete_of_checkComplete (n := 4) (by decide)⟩
  intro o
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩⟩ <;>
    exact of_decide_eq_true rfl

/-- Adequacy is not equidistribution: the runs of `runPerStep` on `a ∥ (b ∥ c)`
for the eight oracles of length 3, in order. Two oracles each produce `a b c` and
`a c b`; one each produces the other four interleavings. -/
theorem perStep_runs_on_length3_oracles_parA_parBC :
    ([[false, false, false], [false, false, true], [false, true, false], [false, true, true],
      [true, false, false], [true, false, true], [true, true, false], [true, true, true]] :
        List Oracle).map (fun o => runPerStep o parA_parBC) =
      [[a, b, c], [a, b, c], [a, c, b], [a, c, b], [b, a, c], [b, c, a], [c, a, b], [c, b, a]] := by
  decide

/-! ## Shared-choice nesting is sound but incomplete -/

/-- **Shared-choice soundness.** For every program `p`, every run of the
shared-choice generator `runShared` is an interleaving of `p`. -/
theorem shared_sound (p : Prog α) : Sound runShared p :=
  fun o => runSharedAux_mem p.size p o rfl

/-- **Shared-choice incompleteness, nested `par`.** On `a ∥ (b ∥ c)` the shared-choice
generator produces exactly the 4 distinct runs listed, while the program has 6
distinct interleavings; the two that start with `b` are never generated. -/
theorem shared_incomplete_parA_parBC :
    (∀ t, (∃ o, runShared o parA_parBC = t) ↔ t ∈ [[a, b, c], [a, c, b], [c, a, b], [c, b, a]]) ∧
    [[a, b, c], [a, c, b], [c, a, b], [c, b, a]].Nodup ∧
    (Interleavings parA_parBC).Nodup ∧ (Interleavings parA_parBC).length = 6 ∧
    [b, a, c] ∈ Interleavings parA_parBC ∧ [b, c, a] ∈ Interleavings parA_parBC ∧
    ¬ Complete runShared parA_parBC := by
  refine ⟨fun t => ⟨?_, ?_⟩, by decide, by decide, by decide, by decide, by decide, complete_neg⟩
  · rintro ⟨o, rfl⟩
    rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨[], by decide⟩
    · exact ⟨[false, true], by decide⟩
    · exact ⟨[true], by decide⟩
    · exact ⟨[true, true], by decide⟩

/-- **Shared-choice incompleteness, nested `par` under `seq`.** On `a ∥ ((b ∥ c) ; d)`
the shared-choice generator produces exactly the 5 distinct runs listed, while
the program has 8 distinct interleavings. -/
theorem shared_incomplete_parA_seqParBC_D :
    (∀ t, (∃ o, runShared o parA_seqParBC_D = t) ↔
      t ∈ [[a, b, c, d], [c, a, b, d], [a, c, b, d], [c, b, a, d], [c, b, d, a]]) ∧
    [[a, b, c, d], [c, a, b, d], [a, c, b, d], [c, b, a, d], [c, b, d, a]].Nodup ∧
    (Interleavings parA_seqParBC_D).Nodup ∧ (Interleavings parA_seqParBC_D).length = 8 ∧
    [b, a, c, d] ∈ Interleavings parA_seqParBC_D ∧
    ¬ Complete runShared parA_seqParBC_D := by
  have hgen : ∀ o, runShared o parA_seqParBC_D ∈
      [[a, b, c, d], [c, a, b, d], [a, c, b, d], [c, b, a, d], [c, b, d, a]] := by
    intro o
    rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl
  refine ⟨fun t => ⟨?_, ?_⟩, by decide, by decide, by decide, by decide, ?_⟩
  · rintro ⟨o, rfl⟩; exact hgen o
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨[], by decide⟩
    · exact ⟨[true, false], by decide⟩
    · exact ⟨[false, true], by decide⟩
    · exact ⟨[true, true], by decide⟩
    · exact ⟨[true, true, true], by decide⟩
  · intro h
    obtain ⟨o, ho⟩ := h [b, a, c, d] (by decide)
    have := hgen o
    rw [ho] at this
    exact absurd this (by decide)

/-- **Shared-choice completeness without nesting.** For every program `p` with no
parallel composition nested inside another (`NoNestedPar p`), the shared-choice
generator `runShared` is complete on `p`. -/
theorem shared_complete_of_noNestedPar (p : Prog α) (h : NoNestedPar p) :
    Complete runShared p :=
  runSharedAux_complete_noNestedPar p.size p rfl h

/-- Non-vacuity of `shared_complete_of_noNestedPar`: `(a ; b) ∥ (c ; d)`
satisfies the hypothesis (and the conclusion, checked by evaluation). -/
theorem shared_complete_parSeqAB_seqCD :
    NoNestedPar parSeqAB_seqCD ∧ Complete runShared parSeqAB_seqCD :=
  ⟨by decide, complete_of_checkComplete (n := 3) (by decide)⟩

/-- Tightness of `NoNestedPar` in `shared_complete_of_noNestedPar`: on
`a ∥ (b ∥ c)` the hypothesis fails and so does the conclusion. -/
theorem shared_complete_of_noNestedPar_needs_hyp :
    ¬ NoNestedPar parA_parBC ∧ ¬ Complete runShared parA_parBC :=
  ⟨by decide, complete_neg⟩

/-- **Shared-choice completeness, characterization for distinct action labels.**
For every program `p` whose actions are pairwise distinct, the shared-choice
generator `runShared` is complete on `p` iff `p` has no nested parallel
composition. -/
theorem shared_complete_iff_noNestedPar_of_nodup (p : Prog α) (hd : p.actions.Nodup) :
    Complete runShared p ↔ NoNestedPar p :=
  ⟨fun hc => Decidable.byContradiction fun hn =>
      not_complete_of_not_noNestedPar p.size p (Nat.le_refl _) hd hn hc,
    shared_complete_of_noNestedPar p⟩

/-- Tightness of `p.actions.Nodup` in the characterization (canonical form): on
`a ∥ (a ∥ a)` (a 3-action nested program with one repeated label) the labels are
not distinct and the equivalence fails, because the shared-choice generator is
complete although the program has a nested `par`. -/
theorem shared_complete_iff_needs_nodup :
    ¬ parA_parAA.actions.Nodup ∧
    ¬ (Complete runShared parA_parAA ↔ NoNestedPar parA_parAA) ∧
    Complete runShared parA_parAA ∧ ¬ NoNestedPar parA_parAA := by
  have hc : Complete runShared parA_parAA := complete_of_checkComplete (n := 0) (by decide)
  have hn : ¬ NoNestedPar parA_parAA := by decide
  exact ⟨by decide, fun h => hn (h.mp hc), hc, hn⟩

/-- Non-vacuity of the characterization: both a distinct-label program on which
both sides hold and one on which both sides fail. -/
theorem shared_complete_iff_nonvacuous :
    parSeqAB_seqCD.actions.Nodup ∧ NoNestedPar parSeqAB_seqCD ∧ Complete runShared parSeqAB_seqCD ∧
    parA_parBC.actions.Nodup ∧ ¬ NoNestedPar parA_parBC ∧ ¬ Complete runShared parA_parBC :=
  ⟨by decide, shared_complete_parSeqAB_seqCD.1, shared_complete_parSeqAB_seqCD.2,
    by decide, by decide, complete_neg⟩

/-- The set of interleavings is the same for `a ∥ (b ∥ c)` and `(a ∥ c) ∥ b`, but
the shared-choice runs differ: `b a c` is a run of `runShared` on `(a ∥ c) ∥ b`
and on no oracle a run on `a ∥ (b ∥ c)`. -/
theorem shared_depends_on_parenthesization :
    (∀ t ∈ Interleavings parA_parBC, t ∈ Interleavings parAC_B) ∧
    (∀ t ∈ Interleavings parAC_B, t ∈ Interleavings parA_parBC) ∧
    runShared [true] parAC_B = [b, a, c] ∧
    (∀ o, runShared o parA_parBC ≠ [b, a, c]) := by
  refine ⟨by decide, by decide, by decide, fun o h => ?_⟩
  exact runShared_neg o (by rw [h]; rfl)

/-! ## The deterministic scheduler (reference point) -/

/-- The deterministic scheduler ignores its oracle (definitional). -/
theorem roundRobin_oracle_irrelevant (o o' : Oracle) (p : Prog α) :
    runRoundRobin o p = runRoundRobin o' p := rfl

/-- **Deterministic scheduler.** For every program `p`: the deterministic
scheduler `runRoundRobin` produces the same run for every oracle, that run is an
interleaving of `p`, and `runRoundRobin` is complete on `p` iff `p` has exactly
one distinct interleaving. -/
theorem roundRobin_sound_single_run_complete_iff_unique_interleaving (p : Prog α) :
    (∀ o, runRoundRobin o p = runRoundRobin [] p) ∧ Sound runRoundRobin p ∧
    (Complete runRoundRobin p ↔ ∀ t₁ ∈ Interleavings p, ∀ t₂ ∈ Interleavings p, t₁ = t₂) := by
  refine ⟨fun _ => rfl, fun _ => perStep_sound p _, fun hc t₁ h₁ t₂ h₂ => ?_,
    fun hu t ht => ⟨[], hu _ (perStep_sound p _) t ht⟩⟩
  obtain ⟨o₁, e₁⟩ := hc t₁ h₁
  obtain ⟨o₂, e₂⟩ := hc t₂ h₂
  rw [← e₁, ← e₂]; rfl

/-- Both sides of the equivalence in
`roundRobin_sound_single_run_complete_iff_unique_interleaving`: true on `a ; b`,
false on `a ∥ b`. -/
theorem roundRobin_examples :
    (Complete runRoundRobin seqAB ∧
      ∀ t₁ ∈ Interleavings seqAB, ∀ t₂ ∈ Interleavings seqAB, t₁ = t₂) ∧
    (¬ Complete runRoundRobin parAB ∧
      ¬ ∀ t₁ ∈ Interleavings parAB, ∀ t₂ ∈ Interleavings parAB, t₁ = t₂) := by
  refine ⟨⟨complete_of_checkComplete (n := 0) (by decide), by decide⟩, ?_, by decide⟩
  intro h
  obtain ⟨o, ho⟩ := h [b, a] (by decide)
  rw [roundRobin_oracle_irrelevant o []] at ho
  exact absurd ho (by decide)

/-- `runRoundRobin` alternates consumed oracle bits, not threads: on
`(a ∥ b) ∥ (c ∥ d)` it runs the whole left pair before the right pair. -/
theorem runRoundRobin_nested_runs_left_first :
    runRoundRobin [] parAB_parCD = [b, a, d, c] := by decide

/-! ## Universal transfer needs completeness -/

/-- **Universal transfer.** For every generator `gen` (any oracle type) and
program `p`: the implication "`P` holds on every run generated by `gen` ⇒ `P`
holds on every interleaving of `p`" holds for every trace property `P` iff `gen`
is complete on `p`. -/
theorem universal_transfer_iff_complete {O : Type} (gen : Gen O α) (p : Prog α) :
    (∀ P : List α → Prop, (∀ o, P (gen o p)) → ∀ t ∈ Interleavings p, P t) ↔ Complete gen p :=
  ⟨fun h t ht => h (fun r => ∃ o, gen o p = r) (fun o => ⟨o, rfl⟩) t ht,
   fun hc _ hP t ht => let ⟨o, ho⟩ := hc t ht; ho ▸ hP o⟩

/-- Both sides of `universal_transfer_iff_complete` on `a ∥ (b ∥ c)`: true for
`runPerStep`, false for `runShared`. -/
theorem universal_transfer_nonvacuous :
    ((∀ P : List Act → Prop, (∀ o, P (runPerStep o parA_parBC)) →
        ∀ t ∈ Interleavings parA_parBC, P t) ∧ Complete runPerStep parA_parBC) ∧
    (¬ (∀ P : List Act → Prop, (∀ o, P (runShared o parA_parBC)) →
        ∀ t ∈ Interleavings parA_parBC, P t) ∧ ¬ Complete runShared parA_parBC) :=
  ⟨⟨(universal_transfer_iff_complete _ _).mpr complete_pos, complete_pos⟩,
   ⟨fun h => complete_neg ((universal_transfer_iff_complete _ _).mp h), complete_neg⟩⟩

/-- Countermodel for `universal_transfer_iff_complete` (racy final value): on `a ∥ (b ∥ c)` with the racy
semantics `Act.eff`, every shared-choice run ends with `x ≠ 3`, but the
interleaving `b a c` ends with `x = 3`. -/
theorem shared_final_value_claim_does_not_transfer :
    (∀ o, finalX (runShared o parA_parBC) ≠ 3) ∧
    [b, a, c] ∈ Interleavings parA_parBC ∧ finalX [b, a, c] = 3 := by
  refine ⟨?_, by decide, by decide⟩
  intro o
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl

/-- Countermodel for `universal_transfer_iff_complete` (ordering constraint): every shared-choice run of
`a ∥ (b ∥ c)` avoids starting with `b`, but some interleaving starts with `b`. -/
theorem shared_ordering_claim_does_not_transfer :
    (∀ o, (runShared o parA_parBC).head? ≠ some b) ∧
    ∃ t ∈ Interleavings parA_parBC, t.head? = some b :=
  ⟨runShared_neg, ⟨[b, a, c], by decide, rfl⟩⟩

/-- Positive control for the two countermodels above: the complete per-step generator
does exhibit the run `b a c` with final value `3`. -/
theorem perStep_exhibits_final_value_three :
    runPerStep [true, false] parA_parBC = [b, a, c] ∧ finalX [b, a, c] = 3 := by decide

/-- A restricted class of properties can transfer from an incomplete generator:
on `a ∥ (b ∥ c)` the shared-choice generator is incomplete, yet every
postcondition on the final state of `Act.effPair` (from `(0, 0)`) that holds on
all its runs holds on all interleavings. -/
theorem postconditions_transfer_from_incomplete_shared :
    ¬ Complete runShared parA_parBC ∧
    ∀ Q : Nat × Nat → Prop,
      (∀ o, Q (finalState Act.effPair (0, 0) (runShared o parA_parBC))) →
      ∀ t ∈ Interleavings parA_parBC, Q (finalState Act.effPair (0, 0) t) := by
  refine ⟨complete_neg, fun Q hQ t ht => ?_⟩
  rw [interleavings_parA_parBC] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [] parA_parBC) =
      finalState Act.effPair (0, 0) [a, b, c]) ▸ hQ []
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [] parA_parBC) =
      finalState Act.effPair (0, 0) [b, a, c]) ▸ hQ []
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [] parA_parBC) =
      finalState Act.effPair (0, 0) [b, c, a]) ▸ hQ []
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [false, true] parA_parBC) =
      finalState Act.effPair (0, 0) [a, c, b]) ▸ hQ [false, true]
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [true] parA_parBC) =
      finalState Act.effPair (0, 0) [c, a, b]) ▸ hQ [true]
  · exact (by decide : finalState Act.effPair (0, 0) (runShared [true, true] parA_parBC) =
      finalState Act.effPair (0, 0) [c, b, a]) ▸ hQ [true, true]

/-! ## Existential transfer needs soundness -/

/-- **Existential transfer.** For every generator `gen` (any oracle type) and
program `p`: the implication "some run generated by `gen` satisfies `Bad` ⇒ some
interleaving of `p` satisfies `Bad`" holds for every trace property `Bad` iff
`gen` is sound on `p`. -/
theorem existential_transfer_iff_sound {O : Type} (gen : Gen O α) (p : Prog α) :
    (∀ Bad : List α → Prop, (∃ o, Bad (gen o p)) → ∃ t ∈ Interleavings p, Bad t) ↔
      Sound gen p :=
  ⟨fun h o => let ⟨_, ht, heq⟩ := h (· = gen o p) ⟨o, rfl⟩; heq ▸ ht,
   fun hs _ ⟨o, hb⟩ => ⟨gen o p, hs o, hb⟩⟩

/-- Countermodel for `existential_transfer_iff_sound` (false positive): the sequencing-ignoring generator is
complete on `a ; b`, yet it produces the run `b a`, which no interleaving of
`a ; b` matches; a "bug" witnessed by that run is a false positive. -/
theorem ignoringSeq_false_positive :
    Complete runIgnoringSeq seqAB ∧ runIgnoringSeq [true] seqAB = [b, a] ∧
    ∀ t ∈ Interleavings seqAB, t ≠ [b, a] :=
  ⟨complete_of_checkComplete (n := 0) (by decide), by decide, by decide⟩

/-- Both sides of `existential_transfer_iff_sound`: true for `runShared` on
`a ∥ (b ∥ c)`, false for `runIgnoringSeq` on `a ; b`. -/
theorem existential_transfer_nonvacuous :
    ((∀ Bad : List Act → Prop, (∃ o, Bad (runShared o parA_parBC)) →
        ∃ t ∈ Interleavings parA_parBC, Bad t) ∧ Sound runShared parA_parBC) ∧
    (¬ (∀ Bad : List Act → Prop, (∃ o, Bad (runIgnoringSeq o seqAB)) →
        ∃ t ∈ Interleavings seqAB, Bad t) ∧ ¬ Sound runIgnoringSeq seqAB) :=
  ⟨⟨(existential_transfer_iff_sound _ _).mpr sound_pos, sound_pos⟩,
   ⟨fun h => sound_neg ((existential_transfer_iff_sound _ _).mp h), sound_neg⟩⟩

/-! ## When a restricted domain is harmless (representatives) -/

/-- Directed generalization of `representative_transfer`: the transfer holds for
an arbitrary relation `I`, reading `TraceEquiv` as the directed swap closure. -/
theorem representative_transfer_directed {O : Type} (I : α → α → Prop) (gen : Gen O α)
    (p : Prog α) (P : List α → Prop) (hP : TraceInvariant I P) (hrep : MeetsEveryClass I gen p) :
    (∀ o, P (gen o p)) → ∀ t ∈ Interleavings p, P t :=
  fun hgen t ht => let ⟨o, heq⟩ := hrep t ht; hP (gen o p) t heq (hgen o)

/-- **Representative transfer.** For every symmetric relation `I` on actions,
generator `gen`, program `p` and trace property `P`: if `P` is invariant under
the trace equivalence generated by `I`, and the trace class of every
interleaving of `p` contains a run generated by `gen`, then `P` holding on every
run generated by `gen` implies `P` holding on every interleaving of `p`. -/
theorem representative_transfer {O : Type} (I : α → α → Prop) (hSym : Symmetric I)
    (gen : Gen O α) (p : Prog α) (P : List α → Prop) (hP : TraceInvariant I P)
    (hrep : MeetsEveryClass I gen p) :
    (∀ o, P (gen o p)) → ∀ t ∈ Interleavings p, P t :=
  have _ := hSym
  representative_transfer_directed I gen p P hP hrep

/-- Non-vacuity of `representative_transfer` (a partial-order-reduction style
use): `indepExceptBC` is symmetric; the final state of `Act.effPair` is
invariant; with only `b`–`c` conflicting, the shared-choice runs meet every class
of `a ∥ (b ∥ c)`; the property holds on every generated run, and indeed on all
six interleavings. -/
theorem representative_transfer_nonvacuous :
    Symmetric indepExceptBC ∧
    TraceInvariant indepExceptBC
      (fun t => finalState Act.effPair (0, 0) t = (6, 1) ∨ finalState Act.effPair (0, 0) t = (2, 1)) ∧
    MeetsEveryClass indepExceptBC runShared parA_parBC ∧
    (∀ o, finalState Act.effPair (0, 0) (runShared o parA_parBC) = (6, 1) ∨
      finalState Act.effPair (0, 0) (runShared o parA_parBC) = (2, 1)) ∧
    (∀ t ∈ Interleavings parA_parBC,
      finalState Act.effPair (0, 0) t = (6, 1) ∨ finalState Act.effPair (0, 0) t = (2, 1)) := by
  refine ⟨independence_pos.2.2.1, ?_, ?_, ?_, by decide⟩
  · intro s t h hs
    rw [← finalState_eq_of_traceEquiv commuting_effPair (0, 0) h]
    exact hs
  · intro t ht
    rw [interleavings_parA_parBC] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    have hab : indepExceptBC a b := by decide
    have hac : indepExceptBC a c := by decide
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨[], TraceEquiv.refl _⟩
    · exact ⟨[], TraceEquiv.swap1 [] [c] a b hab⟩
    · exact ⟨[], (TraceEquiv.swap1 [] [c] a b hab).trans (TraceEquiv.swap1 [b] [] a c hac)⟩
    · exact ⟨[false, true], TraceEquiv.refl _⟩
    · exact ⟨[true], TraceEquiv.refl _⟩
    · exact ⟨[true, true], TraceEquiv.refl _⟩
  · intro o
    rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl

/-- Tightness of `hP` in `representative_transfer` (canonical form; witness: the
symmetric relation `fullIndep`, `runShared` on the 3-action program
`a ∥ (b ∥ c)`, property "`b` is not first"): `fullIndep` is symmetric, the
shared-choice runs meet every class, the property is not invariant, and the
transfer fails (the property holds on every generated run and fails on an
interleaving). -/
theorem representative_transfer_needs_invariance :
    Symmetric fullIndep ∧
    MeetsEveryClass fullIndep runShared parA_parBC ∧
    ¬ TraceInvariant fullIndep (fun t => t.head? ≠ some b) ∧
    ¬ ((∀ o, (runShared o parA_parBC).head? ≠ some b) →
        ∀ t ∈ Interleavings parA_parBC, t.head? ≠ some b) ∧
    (∀ o, (runShared o parA_parBC).head? ≠ some b) ∧
    ¬ (∀ t ∈ Interleavings parA_parBC, t.head? ≠ some b) :=
  ⟨independence_pos.1.1, meetsEveryClass_pos, traceInvariant_neg,
    fun h => h runShared_neg [b, a, c] (by decide) rfl, runShared_neg,
    fun h => h [b, a, c] (by decide) rfl⟩

/-- Tightness of `hrep` in `representative_transfer` (canonical form; witness: the
symmetric relation `indepOnlyAC`, `runShared` on the 3-action program
`a ∥ (b ∥ c)`, property "`b` is not first"): `indepOnlyAC` is symmetric, the
property is invariant, the shared-choice runs miss a class, and the transfer
fails. -/
theorem representative_transfer_needs_meets_every_class :
    Symmetric indepOnlyAC ∧
    TraceInvariant indepOnlyAC (fun t => t.head? ≠ some b) ∧
    ¬ MeetsEveryClass indepOnlyAC runShared parA_parBC ∧
    ¬ ((∀ o, (runShared o parA_parBC).head? ≠ some b) →
        ∀ t ∈ Interleavings parA_parBC, t.head? ≠ some b) ∧
    (∀ o, (runShared o parA_parBC).head? ≠ some b) ∧
    ¬ (∀ t ∈ Interleavings parA_parBC, t.head? ≠ some b) := by
  refine ⟨independence_pos.2.1.1, ?_, meetsEveryClass_neg,
    fun h => h runShared_neg [b, a, c] (by decide) rfl, runShared_neg,
    fun h => h [b, a, c] (by decide) rfl⟩
  intro s t h hs ht
  exact hs ((head_eq_iff_of_traceEquiv_of_isolated indepOnlyAC_b_isolated h).mpr ht)

/-- A one-way relation: `a b` may be rewritten to `b a`, not back. -/
def oneWayAB : Act → Act → Prop := fun x y => x = .a ∧ y = .b

theorem oneWayAB_ba_stuck {s₀ u : List Act} (hs₀ : s₀ = [b, a]) (h : SwapStep oneWayAB s₀ u) :
    False := by
  cases h with
  | mk p s x y hxy =>
      rcases hxy with ⟨rfl, rfl⟩
      cases p with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hs₀
          exact Act.noConfusion hs₀.1
      | cons z p =>
          cases p with
          | nil =>
              have hlen := congrArg List.length hs₀
              simp at hlen
          | cons w p =>
              have hlen := congrArg List.length hs₀
              simp at hlen

theorem oneWayAB_ba_traceEquiv_eq {t : List Act} (h : TraceEquiv oneWayAB [b, a] t) :
    t = [b, a] := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact False.elim (oneWayAB_ba_stuck ih hs)

/-- Without symmetry the swap closure is not symmetric, and a property closed
under it can distinguish two traces related by one swap. -/
theorem swapClosure_not_symmetric_example :
    ¬ Symmetric oneWayAB ∧
    TraceEquiv oneWayAB [a, b] [b, a] ∧ ¬ TraceEquiv oneWayAB [b, a] [a, b] ∧
    TraceInvariant oneWayAB (· = [b, a]) ∧ ¬ ([a, b] = [b, a]) := by
  refine ⟨fun h => ?_, TraceEquiv.swap1 [] [] a b ⟨rfl, rfl⟩, fun h => ?_, fun s t h hs => ?_,
    by decide⟩
  · exact Act.noConfusion (h a b ⟨rfl, rfl⟩).1
  · exact absurd (oneWayAB_ba_traceEquiv_eq h) (by decide)
  · subst hs; exact oneWayAB_ba_traceEquiv_eq h

/-- A constant generator: every run is `b a`. -/
def constBA : Gen Oracle Act := fun _ _ => [b, a]

/-- Why `representative_transfer` assumes symmetry: reading the representative
condition in the other direction ("every interleaving reaches a generated run")
does not support the transfer for an asymmetric relation, even for a sound
generator. -/
theorem reversed_reading_fails_without_symmetry :
    Sound constBA parAB ∧
    TraceInvariant oneWayAB (· = [b, a]) ∧
    (∀ t ∈ Interleavings parAB, ∃ o, TraceEquiv oneWayAB t (constBA o parAB)) ∧
    (∀ o, constBA o parAB = [b, a]) ∧
    ¬ (∀ t ∈ Interleavings parAB, t = [b, a]) := by
  refine ⟨fun _ => of_decide_eq_true rfl, swapClosure_not_symmetric_example.2.2.2.1, ?_,
    fun _ => rfl, ?_⟩
  · intro t ht
    have ht' : t = [a, b] ∨ t = [b, a] := by
      have e : Interleavings parAB = [[a, b], [b, a]] := by decide
      rw [e] at ht
      simpa using ht
    rcases ht' with rfl | rfl
    · exact ⟨[], TraceEquiv.swap1 [] [] a b ⟨rfl, rfl⟩⟩
    · exact ⟨[], TraceEquiv.refl _⟩
  · intro h
    exact absurd (h [a, b] (by decide)) (by decide)

/-- Directed generalization of `invariant_transfer_iff_meets_every_class`. -/
theorem invariant_transfer_iff_meets_every_class_directed {O : Type} (I : α → α → Prop)
    (gen : Gen O α) (p : Prog α) :
    (∀ P : List α → Prop, TraceInvariant I P → (∀ o, P (gen o p)) → ∀ t ∈ Interleavings p, P t) ↔
      MeetsEveryClass I gen p := by
  refine ⟨fun h t ht => ?_, fun hrep P hP => representative_transfer_directed I gen p P hP hrep⟩
  exact h (fun u => ∃ o, TraceEquiv I (gen o p) u)
    (fun _ _ hst ⟨o, hso⟩ => ⟨o, hso.trans hst⟩)
    (fun o => ⟨o, .refl _⟩) t ht

/-- **Representative transfer, characterization.** For every symmetric relation
`I`, generator `gen` and program `p`: every property invariant under the trace
equivalence generated by `I` transfers from the runs generated by `gen` to all
interleavings of `p` iff the trace class of every interleaving of `p` contains a
run generated by `gen`. -/
theorem invariant_transfer_iff_meets_every_class {O : Type} (I : α → α → Prop)
    (hSym : Symmetric I) (gen : Gen O α) (p : Prog α) :
    (∀ P : List α → Prop, TraceInvariant I P → (∀ o, P (gen o p)) → ∀ t ∈ Interleavings p, P t) ↔
      MeetsEveryClass I gen p :=
  have _ := hSym
  invariant_transfer_iff_meets_every_class_directed I gen p

/-- Both sides of `invariant_transfer_iff_meets_every_class` for `runShared` on
`a ∥ (b ∥ c)`: true under the symmetric relations `fullIndep` and
`indepExceptBC`, false under the symmetric relation `indepOnlyAC`. -/
theorem invariant_transfer_nonvacuous :
    (Symmetric fullIndep ∧
      (∀ P, TraceInvariant fullIndep P → (∀ o, P (runShared o parA_parBC)) →
        ∀ t ∈ Interleavings parA_parBC, P t) ∧
      MeetsEveryClass fullIndep runShared parA_parBC) ∧
    (Symmetric indepExceptBC ∧
      (∀ P, TraceInvariant indepExceptBC P → (∀ o, P (runShared o parA_parBC)) →
        ∀ t ∈ Interleavings parA_parBC, P t) ∧
      MeetsEveryClass indepExceptBC runShared parA_parBC) ∧
    (Symmetric indepOnlyAC ∧
      ¬ (∀ P, TraceInvariant indepOnlyAC P → (∀ o, P (runShared o parA_parBC)) →
        ∀ t ∈ Interleavings parA_parBC, P t) ∧
      ¬ MeetsEveryClass indepOnlyAC runShared parA_parBC) := by
  have hm2 := representative_transfer_nonvacuous.2.2.1
  refine ⟨⟨independence_pos.1.1,
      (invariant_transfer_iff_meets_every_class _ independence_pos.1.1 _ _).mpr meetsEveryClass_pos,
      meetsEveryClass_pos⟩,
    ⟨independence_pos.2.2.1,
      (invariant_transfer_iff_meets_every_class _ independence_pos.2.2.1 _ _).mpr hm2, hm2⟩,
    ⟨independence_pos.2.1.1, fun h => meetsEveryClass_neg
      ((invariant_transfer_iff_meets_every_class _ independence_pos.2.1.1 _ _).mp h),
      meetsEveryClass_neg⟩⟩

/-- A property that is not invariant can still transfer: "the trace is not
`b a d`" is not invariant under `fullIndep`, yet it holds on every run of
`runShared` on `a ∥ (b ∥ c)` and on every interleaving. -/
theorem noninvariant_property_may_transfer :
    ¬ TraceInvariant fullIndep (· ≠ [b, a, d]) ∧
    (∀ o, runShared o parA_parBC ≠ [b, a, d]) ∧
    (∀ t ∈ Interleavings parA_parBC, t ≠ [b, a, d]) := by
  refine ⟨fun h => h [a, b, d] [b, a, d] (TraceEquiv.swap1 [] [d] a b (by decide)) (by decide) rfl,
    fun o => ?_, by decide⟩
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> exact of_decide_eq_true rfl

/-- `MeetsEveryClass` does not make the representatives interleavings: under
`fullIndep`, the constant generator `constBA` meets every class of `a ; b`,
although no run it generates is an interleaving of `a ; b`. -/
theorem meetsEveryClass_without_sound :
    MeetsEveryClass fullIndep constBA seqAB ∧ ∀ o, constBA o seqAB ∉ Interleavings seqAB := by
  have e : Interleavings seqAB = [[a, b]] := by decide
  refine ⟨fun t ht => ?_, fun _ => (by rw [e]; show [b, a] ∉ [[a, b]]; decide)⟩
  rw [e, List.mem_singleton] at ht
  subst ht
  exact ⟨[], TraceEquiv.swap1 [] [] b a (by decide)⟩

/-- **Representatives under full independence.** For every relation `I` under
which all distinct actions are related, every program `p`, and every generator
`gen` with an inhabited oracle type: if `gen` is sound on `p`, then every
interleaving of `p` is reachable by commuting adjacent `I`-related actions from
some run generated by `gen` (equivalently, as `I` is then symmetric, every
interleaving is `I`-trace-equivalent to some generated run). -/
theorem meets_every_class_of_sound_of_full_independence {O : Type} [Nonempty O]
    (I : α → α → Prop) (gen : Gen O α) (p : Prog α)
    (hI : ∀ x y, x ≠ y → I x y) (hs : Sound gen p) : MeetsEveryClass I gen p := by
  intro t ht
  obtain ⟨o⟩ := ‹Nonempty O›
  exact ⟨o, traceEquiv_of_perm hI
    ((perm_actions_of_mem_interleavings (hs o)).trans (perm_actions_of_mem_interleavings ht).symm)⟩

/-- Corollary for the shared-choice generator: under full independence the runs
of `runShared` meet every class of every program. -/
theorem shared_meets_every_class_of_full_independence (I : α → α → Prop)
    (hI : ∀ x y, x ≠ y → I x y) (p : Prog α) : MeetsEveryClass I runShared p :=
  meets_every_class_of_sound_of_full_independence I runShared p hI (shared_sound p)

/-- Non-vacuity of `meets_every_class_of_sound_of_full_independence`: all its
hypotheses hold for `fullIndep` and `runShared` on `a ∥ (b ∥ c)`. -/
theorem meets_every_class_full_independence_nonvacuous :
    Nonempty Oracle ∧ (∀ x y : Act, x ≠ y → fullIndep x y) ∧ Sound runShared parA_parBC ∧
    MeetsEveryClass fullIndep runShared parA_parBC :=
  ⟨⟨[]⟩, fun _ _ h => h, sound_pos, meetsEveryClass_pos⟩

/-- A generator over the empty oracle type. -/
def emptyGen : Gen Empty Act := fun o _ => nomatch o

/-- A generator whose every run is empty. -/
def dropAllGen : Gen Oracle Act := fun _ _ => []

/-- Tightness of `[Nonempty O]` (canonical form; witness: the uninhabited oracle
type `Empty` on the 2-action program `a ∥ b`): the generator is vacuously sound,
all distinct actions are related, and no class is met. -/
theorem meets_every_class_needs_nonempty_oracles :
    ¬ Nonempty Empty ∧ (∀ x y : Act, x ≠ y → fullIndep x y) ∧ Sound emptyGen parAB ∧
    ¬ MeetsEveryClass fullIndep emptyGen parAB := by
  refine ⟨(fun hne => by obtain ⟨x⟩ := hne; exact nomatch x), fun _ _ h => h,
    (fun o => nomatch o), fun h => ?_⟩
  obtain ⟨o, _⟩ := h [a, b] (by decide)
  exact nomatch o

/-- Tightness of `hI` (canonical form; witness: the symmetric relation
`indepOnlyAC`, which leaves `b` unrelated to `a` and `c`, and the sound generator
`runShared` on the 3-action program `a ∥ (b ∥ c)`): oracles exist, `runShared`
is sound, and a class is missed. -/
theorem meets_every_class_needs_full_independence :
    Nonempty Oracle ∧ ¬ (∀ x y : Act, x ≠ y → indepOnlyAC x y) ∧ Sound runShared parA_parBC ∧
    ¬ MeetsEveryClass indepOnlyAC runShared parA_parBC :=
  ⟨⟨[]⟩, fun h => absurd (h .a .b (by decide)) (by decide), sound_pos, meetsEveryClass_neg⟩

/-- Tightness of `hs` (canonical form; witness: the action-dropping generator
`dropAllGen`, whose runs are empty, on the 2-action program `a ∥ b` under
`fullIndep`): oracles exist, all distinct actions are related, the generator is
unsound, and no class is met. -/
theorem meets_every_class_needs_sound :
    Nonempty Oracle ∧ (∀ x y : Act, x ≠ y → fullIndep x y) ∧ ¬ Sound dropAllGen parAB ∧
    ¬ MeetsEveryClass fullIndep dropAllGen parAB := by
  refine ⟨⟨[]⟩, fun _ _ h => h, fun h => absurd (h []) (by decide), fun h => ?_⟩
  obtain ⟨o, ho⟩ := h [a, b] (by decide)
  exact Nat.noConfusion ho.length_eq

/-- Soundness is stronger than what full independence needs: the unsound
generator `runIgnoringSeq` still meets every class of `a ; b` under `fullIndep`
(it reorders actions but never drops them). -/
theorem meets_every_class_unsound_permuting :
    ¬ Sound runIgnoringSeq seqAB ∧ MeetsEveryClass fullIndep runIgnoringSeq seqAB := by
  have e : Interleavings seqAB = [[a, b]] := by decide
  refine ⟨sound_neg, fun t ht => ?_⟩
  rw [e, List.mem_singleton] at ht
  subst ht
  exact ⟨[], (by decide : runIgnoringSeq [] seqAB = [a, b]) ▸ TraceEquiv.refl _⟩

/-- **Conflicting nested actions (impossibility instance).** Under the relation
`indepOnlyAC`, which is symmetric and irreflexive and relates only `a` and `c`
(so `b` conflicts with both `a` and `c`), the sound shared-choice generator
`runShared` on `a ∥ (b ∥ c)` produces no run trace-equivalent to the
interleaving `b a c` (whose class also contains `b c a`), so it does not meet
every class. -/
theorem shared_misses_class_when_b_conflicts_with_a_and_c :
    Symmetric indepOnlyAC ∧ Irreflexive indepOnlyAC ∧ Sound runShared parA_parBC ∧
    [b, a, c] ∈ Interleavings parA_parBC ∧ TraceEquiv indepOnlyAC [b, a, c] [b, c, a] ∧
    (∀ o, ¬ TraceEquiv indepOnlyAC (runShared o parA_parBC) [b, a, c]) ∧
    (∀ o, ¬ TraceEquiv indepOnlyAC [b, a, c] (runShared o parA_parBC)) ∧
    ¬ MeetsEveryClass indepOnlyAC runShared parA_parBC := by
  refine ⟨independence_pos.2.1.1, independence_pos.2.1.2, sound_pos, by decide,
    TraceEquiv.swap1 [b] [] a c (Or.inl ⟨rfl, rfl⟩), fun o ho => ?_, fun o ho => ?_,
    meetsEveryClass_neg⟩
  · exact runShared_neg o ((head_eq_iff_of_traceEquiv_of_isolated indepOnlyAC_b_isolated ho).mpr rfl)
  · exact runShared_neg o ((head_eq_iff_of_traceEquiv_of_isolated indepOnlyAC_b_isolated ho).mp rfl)

/-- `indepOnlyAC` is an independence relation justified by a semantics:
symmetric, irreflexive, and `Act.effSwap` effects of related actions commute. -/
theorem indepOnlyAC_justified :
    Symmetric indepOnlyAC ∧ Irreflexive indepOnlyAC ∧ Commuting Act.effSwap indepOnlyAC :=
  ⟨independence_pos.2.1.1, independence_pos.2.1.2, commuting_effSwap⟩

/-- Positive control: if only the two nested actions `b` and `c` conflict
(`indepExceptBC`), the shared-choice generator does meet every class of
`a ∥ (b ∥ c)`. -/
theorem shared_meets_every_class_when_only_b_c_conflict :
    Symmetric indepExceptBC ∧ Irreflexive indepExceptBC ∧
    MeetsEveryClass indepExceptBC runShared parA_parBC :=
  ⟨independence_pos.2.2.1, independence_pos.2.2.2, representative_transfer_nonvacuous.2.2.1⟩

/-- Commuting effects make the final state invariant, not the intermediate
states: `Act.effInc` (`a` = `+1`, `b` = `-1` on integers) commutes for all
distinct actions, the final state agrees on `a b` and `b a`, but "every prefix
leaves the counter nonnegative" holds on `a b` and fails on the equivalent
`b a`. -/
theorem commuting_does_not_make_prefix_safety_invariant :
    Commuting Act.effInc fullIndep ∧ TraceEquiv fullIndep [a, b] [b, a] ∧
    finalState Act.effInc 0 [a, b] = finalState Act.effInc 0 [b, a] ∧
    (∀ k, 0 ≤ finalState Act.effInc 0 ([a, b].take k)) ∧
    ¬ (∀ k, 0 ≤ finalState Act.effInc 0 ([b, a].take k)) ∧
    ¬ TraceInvariant fullIndep (fun t => ∀ k, 0 ≤ finalState Act.effInc 0 (t.take k)) := by
  have hpos : ∀ k, 0 ≤ finalState Act.effInc 0 ([a, b].take k) := by
    intro k
    match k with
    | 0 => decide
    | 1 => decide
    | k + 2 => simp [finalState, Act.effInc]
  have hneg : ¬ (∀ k, 0 ≤ finalState Act.effInc 0 ([b, a].take k)) := fun h => by
    have := h 1
    revert this; decide
  refine ⟨?_, TraceEquiv.swap1 [] [] a b (by decide), by decide, hpos, hneg, fun h => ?_⟩
  · intro x y _ s
    cases x <;> cases y <;> simp [Act.effInc] <;> omega
  · exact hneg (h [a, b] [b, a] (TraceEquiv.swap1 [] [] a b (by decide)) hpos)

/-! ## Bounded adequacy check -/

/-- **Per-step oracle bound.** For every program `p`, the run of `runPerStep` on
`p` depends only on the first `schedPoints p` oracle bits. -/
theorem perStep_oracleBounded (p : Prog α) : OracleBounded runPerStep p (schedPoints p) :=
  fun o => runPerStepAux_take p.size p o (schedPoints p) rfl (Nat.le_refl _)

/-- **Shared-choice oracle bound.** For every program `p`, the run of `runShared`
on `p` depends only on the first `schedPoints p` oracle bits. -/
theorem shared_oracleBounded (p : Prog α) : OracleBounded runShared p (schedPoints p) :=
  fun o => runSharedAux_take p.size p o (schedPoints p) rfl (Nat.le_refl _)

/-- **Shared-choice oracle bound, linear form.** For every program `p`, the run of
`runShared` on `p` depends only on the first `size p - 1` oracle bits. -/
theorem shared_oracleBounded_size_pred (p : Prog α) : OracleBounded runShared p (p.size - 1) :=
  fun o => runSharedAux_take_size p.size p o (p.size - 1) rfl (Nat.le_refl _)

/-- Instances of the two oracle bounds on `a ∥ (b ∥ c)` (`schedPoints = 3`),
fully proved by case analysis on the first four oracle bits. -/
theorem oracleBounded_schedPoints_parA_parBC :
    OracleBounded runPerStep parA_parBC (schedPoints parA_parBC) ∧
    OracleBounded runShared parA_parBC (schedPoints parA_parBC) := by
  refine ⟨fun o => ?_, fun o => ?_⟩ <;>
    rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩⟩ <;> rfl

/-- With repeated labels the per-step generator can need fewer bits than
`schedPoints`: on `a ∥ (a ∥ a)` (`schedPoints = 3`) every run is `a a a`, so no
bit is needed. -/
theorem perStep_oracleBounded_zero_parA_parAA :
    schedPoints parA_parAA = 3 ∧ OracleBounded runPerStep parA_parAA 0 := by
  refine ⟨by decide, fun o => ?_⟩
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩⟩ <;> rfl

/-- `schedPoints` is quadratic on a right-nested chain (not proved here for general chain length): on `a ∥ (b ∥ (c ∥ d))`
it is `6`, the per-step generator does need all `6` bits (5 do not suffice),
while the shared-choice generator needs at most `size - 1 = 3`. -/
theorem schedPoints_spine4 :
    schedPoints spine4 = 6 ∧ spine4.size = 4 ∧ ¬ OracleBounded runPerStep spine4 5 ∧
    OracleBounded runShared spine4 3 := by
  refine ⟨by decide, rfl, fun h => ?_, shared_oracleBounded_size_pred spine4⟩
  have := h [true, true, true, true, true, true]
  exact absurd this (by decide)

/-- **Decision procedure.** For every generator `gen` with list-of-bits oracles,
program `p` and bound `n` such that `gen` on `p` reads at most the first `n`
oracle bits, `checkComplete` decides `Complete gen p` and `checkSound` decides
`Sound gen p`. -/
theorem check_correct_of_oracleBounded [DecidableEq α] (gen : Gen Oracle α) (p : Prog α) (n : Nat)
    (h : OracleBounded gen p n) :
    (checkComplete gen p n = true ↔ Complete gen p) ∧ (checkSound gen p n = true ↔ Sound gen p) := by
  refine ⟨⟨complete_of_checkComplete, fun hc => ?_⟩, ⟨fun hs o => ?_, fun hs => ?_⟩⟩
  · apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨o, rfl⟩ := hc t ht
    rw [← h o]
    apply decide_eq_true
    exact List.mem_map.mpr ⟨o.take n, mem_oraclesUpTo (List.length_take_le n o), rfl⟩
  · rw [← h o]
    have hmem : gen (o.take n) p ∈ generatedUpTo gen p n :=
      List.mem_map.mpr ⟨o.take n, mem_oraclesUpTo (List.length_take_le n o), rfl⟩
    exact of_decide_eq_true (List.all_eq_true.mp hs _ hmem)
  · apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp ht
    exact decide_eq_true (hs o)

/-- The decision procedure run on the example programs (fully proved by
evaluation). -/
theorem check_on_examples :
    (checkComplete runShared parA_parBC (schedPoints parA_parBC) = false ∧
      checkSound runShared parA_parBC (schedPoints parA_parBC) = true ∧
      checkComplete runPerStep parA_parBC (schedPoints parA_parBC) = true ∧
      checkSound runPerStep parA_parBC (schedPoints parA_parBC) = true) ∧
    (checkComplete runShared parA_seqParBC_D (schedPoints parA_seqParBC_D) = false ∧
      checkSound runShared parA_seqParBC_D (schedPoints parA_seqParBC_D) = true ∧
      checkComplete runPerStep parA_seqParBC_D (schedPoints parA_seqParBC_D) = true ∧
      checkSound runPerStep parA_seqParBC_D (schedPoints parA_seqParBC_D) = true) ∧
    (checkComplete runShared parSeqAB_seqCD (schedPoints parSeqAB_seqCD) = true ∧
      checkSound runShared parSeqAB_seqCD (schedPoints parSeqAB_seqCD) = true) := by
  decide

/-- Tightness of `h` in `check_correct_of_oracleBounded` (canonical form;
witnesses at bound `n = 0` on the 2-action programs `a ∥ b` with `runPerStep` and
`a ; b` with `runIgnoringSeq`): the bound fails and the conclusion fails. -/
theorem check_needs_oracleBounded :
    (¬ OracleBounded runPerStep parAB 0 ∧
      ¬ ((checkComplete runPerStep parAB 0 = true ↔ Complete runPerStep parAB) ∧
         (checkSound runPerStep parAB 0 = true ↔ Sound runPerStep parAB))) ∧
    (¬ OracleBounded runIgnoringSeq seqAB 0 ∧
      ¬ ((checkComplete runIgnoringSeq seqAB 0 = true ↔ Complete runIgnoringSeq seqAB) ∧
         (checkSound runIgnoringSeq seqAB 0 = true ↔ Sound runIgnoringSeq seqAB))) := by
  have hcf : checkComplete runPerStep parAB 0 = false := by decide
  have hc : Complete runPerStep parAB := complete_of_checkComplete (n := 1) (by decide)
  have hst : checkSound runIgnoringSeq seqAB 0 = true := by decide
  refine ⟨⟨oracleBounded_neg, fun h => ?_⟩, ⟨fun hob => ?_, fun h => sound_neg (h.2.mp hst)⟩⟩
  · have := h.1.mpr hc
    rw [hcf] at this
    exact Bool.noConfusion this
  · have := hob [true]
    exact absurd this (by decide)

/-- Non-vacuity of `check_correct_of_oracleBounded`: the bound hypothesis holds
for both generators on `a ∥ (b ∥ c)` at `n = schedPoints = 3`, and the checks
return the expected answers there. -/
theorem check_correct_nonvacuous :
    OracleBounded runPerStep parA_parBC (schedPoints parA_parBC) ∧
    OracleBounded runShared parA_parBC (schedPoints parA_parBC) ∧
    checkComplete runPerStep parA_parBC (schedPoints parA_parBC) = true ∧
    checkSound runPerStep parA_parBC (schedPoints parA_parBC) = true ∧
    checkComplete runShared parA_parBC (schedPoints parA_parBC) = false ∧
    checkSound runShared parA_parBC (schedPoints parA_parBC) = true :=
  ⟨oracleBounded_schedPoints_parA_parBC.1, oracleBounded_schedPoints_parA_parBC.2,
   by decide, by decide, by decide, by decide⟩

/-- `schedPoints` cannot be lowered uniformly for `runPerStep`: on `a ∥ (b ∥ c)`
(where `schedPoints = 3`) two bits do not suffice. -/
theorem perStep_not_oracleBounded_below_schedPoints :
    schedPoints parA_parBC = 3 ∧ ¬ OracleBounded runPerStep parA_parBC 2 := by
  refine ⟨by decide, fun h => ?_⟩
  have := h [true, true, true]
  exact absurd this (by decide)

/-! ## What a claim over generated runs must say -/

/-- **Adequacy, universal form.** For every generator `gen` (any oracle type) and
program `p`: "`P` holds on every run generated by `gen`" is equivalent to "`P`
holds on every interleaving of `p`" for every trace property `P` iff `gen` is
both complete and sound on `p`. -/
theorem universal_claims_equiv_iff_complete_and_sound {O : Type} (gen : Gen O α) (p : Prog α) :
    (∀ P : List α → Prop, (∀ o, P (gen o p)) ↔ ∀ t ∈ Interleavings p, P t) ↔
      Complete gen p ∧ Sound gen p := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hc, hs⟩ P => ⟨?_, ?_⟩⟩
  · exact (h (fun r => ∃ o, gen o p = r)).mp (fun o => ⟨o, rfl⟩)
  · exact (h (· ∈ Interleavings p)).mpr (fun _ ht => ht)
  · exact fun ho t ht => let ⟨o, heq⟩ := hc t ht; heq ▸ ho o
  · exact fun ht o => ht (gen o p) (hs o)

/-- **Adequacy, existential form.** For every generator `gen` (any oracle type) and
program `p`: "some run generated by `gen` satisfies `Bad`" is equivalent to "some
interleaving of `p` satisfies `Bad`" for every trace property `Bad` iff `gen` is
both complete and sound on `p`. -/
theorem existential_claims_equiv_iff_complete_and_sound {O : Type} (gen : Gen O α) (p : Prog α) :
    (∀ Bad : List α → Prop, (∃ o, Bad (gen o p)) ↔ ∃ t ∈ Interleavings p, Bad t) ↔
      Complete gen p ∧ Sound gen p := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hc, hs⟩ Bad => ⟨?_, ?_⟩⟩
  · intro t ht
    exact (h (· = t)).mpr ⟨t, ht, rfl⟩
  · intro o
    obtain ⟨_, ht, heq⟩ := (h (· = gen o p)).mp ⟨o, rfl⟩
    exact heq ▸ ht
  · exact fun ⟨o, hb⟩ => ⟨gen o p, hs o, hb⟩
  · exact fun ⟨t, ht, hb⟩ => let ⟨o, heq⟩ := hc t ht; ⟨o, heq.symm ▸ hb⟩

/-- Completeness alone does not give the equivalences of
`universal_claims_equiv_iff_complete_and_sound` and
`existential_claims_equiv_iff_complete_and_sound`: the sequencing-ignoring
generator is complete on `a ; b`, and both equivalences fail. -/
theorem complete_alone_does_not_give_equivalence :
    Complete runIgnoringSeq seqAB ∧
    ¬ (∀ P : List Act → Prop, (∀ o, P (runIgnoringSeq o seqAB)) ↔ ∀ t ∈ Interleavings seqAB, P t) ∧
    ¬ (∀ Bad : List Act → Prop, (∃ o, Bad (runIgnoringSeq o seqAB)) ↔ ∃ t ∈ Interleavings seqAB, Bad t) := by
  refine ⟨ignoringSeq_false_positive.1, fun h => ?_, fun h => ?_⟩
  · have := ((h (· ∈ Interleavings seqAB)).mpr (fun t ht => ht)) [true]
    exact absurd this (by decide)
  · obtain ⟨t, ht, rfl⟩ := (h (· = [b, a])).mp ⟨[true], by decide⟩
    exact absurd ht (by decide)

/-- Soundness alone does not give these equivalences: the shared-choice
generator is sound on `a ∥ (b ∥ c)`, and both equivalences fail. -/
theorem sound_alone_does_not_give_equivalence :
    Sound runShared parA_parBC ∧
    ¬ (∀ P : List Act → Prop,
        (∀ o, P (runShared o parA_parBC)) ↔ ∀ t ∈ Interleavings parA_parBC, P t) ∧
    ¬ (∀ Bad : List Act → Prop,
        (∃ o, Bad (runShared o parA_parBC)) ↔ ∃ t ∈ Interleavings parA_parBC, Bad t) := by
  refine ⟨sound_pos, fun h => ?_, fun h => ?_⟩
  · have := (h (fun t => t.head? ≠ some b)).mp runShared_neg
    exact this [b, a, c] (by decide) rfl
  · obtain ⟨o, ho⟩ := (h (fun t => t.head? = some b)).mpr ⟨[b, a, c], by decide, rfl⟩
    exact runShared_neg o ho

/-- Non-vacuity of the two adequacy equivalences: for the per-step generator on
`a ∥ (b ∥ c)` both sides of both equivalences hold. -/
theorem claims_equiv_nonvacuous :
    Complete runPerStep parA_parBC ∧ Sound runPerStep parA_parBC ∧
    (∀ P : List Act → Prop,
      (∀ o, P (runPerStep o parA_parBC)) ↔ ∀ t ∈ Interleavings parA_parBC, P t) ∧
    (∀ Bad : List Act → Prop,
      (∃ o, Bad (runPerStep o parA_parBC)) ↔ ∃ t ∈ Interleavings parA_parBC, Bad t) :=
  ⟨perStep_adequate_parA_parBC.2, perStep_adequate_parA_parBC.1,
   (universal_claims_equiv_iff_complete_and_sound _ _).mpr
     ⟨perStep_adequate_parA_parBC.2, perStep_adequate_parA_parBC.1⟩,
   (existential_claims_equiv_iff_complete_and_sound _ _).mpr
     ⟨perStep_adequate_parA_parBC.2, perStep_adequate_parA_parBC.1⟩⟩

end Toy.SchedAdequacy
