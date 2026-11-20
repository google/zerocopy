import ToyLink.Counterexamples

/-!
# Supplementary results

* Conclusions obtained by applying the two assume-guarantee rules to their non-vacuity
  witnesses (`evenOddProg_partial_correct`, `evenOddProg_total_correct`), and the empty
  module as an edge case of the total-correctness rule (`empty_module_ag_total`).
* The closed-source disjunct of the collapse characterization, on a syntactically open
  target (`closed_source_open_target_collapse_witness`).
* The third premise of the behavioural separate-compilation corollary
  `separate_compilation_preserves_partial_correctness_of_pass_ctxRefines`: a non-vacuity
  witness with public modules (`nonvacuous_sep_comp_behavioural_corollary`) and a tightness
  counterexample (`Cex.cex_sep_comp_behavioural_corollary_without_hSrc`).
* Independently chosen termination measures do not compose under linking
  (`Cex.independent_measures_do_not_compose`).
* An unfolded form of `ctxRefines_sameDom` (`Unfolded.ctxRefines_sameDom_unfolded_iff`).
-/

namespace Toy.Link.Examples

open Toy.Link

/-- Applying `ag_partial_correctness` to its non-vacuity witness: the mutually recursive
`even`/`odd` program is partially correct for the parity contract. -/
theorem evenOddProg_partial_correct : ProgramPartialCorrect evenOddProg evenOddSpec :=
  ag_partial_correctness nonvacuous_ag_partial_correctness.1
    nonvacuous_ag_partial_correctness.2

/-- Applying `ag_total_correctness_of_wf_call_measure` to its non-vacuity witness: the
mutually recursive `even`/`odd` program is totally correct for the parity contract. -/
theorem evenOddProg_total_correct : ProgramTotalCorrect evenOddProg evenOddSpec :=
  ag_total_correctness_of_wf_call_measure
    nonvacuous_ag_total_correctness.1
    nonvacuous_ag_total_correctness.2.1
    nonvacuous_ag_total_correctness.2.2

/-- Edge case of `ag_total_correctness_of_wf_call_measure`: the empty module with the
everywhere-unsatisfiable contract `falseSpec` and a `Unit`-valued measure. -/
theorem empty_module_ag_total :
    ProgramTotalCorrect ([] : Module) falseSpec :=
  ag_total_correctness_of_wf_call_measure
    (α := Unit) (rel := fun _ _ => False) (μ := fun _ _ => ())
    ⟨fun _ => .intro _ fun _ h => False.elim h⟩
    (fun _ _ h => False.elim h)
    (fun _ _ hlu => by simp [Module.lookup] at hlu)

/-- A syntactically open module whose only external call (to `5`) is dead:
`0 ↦ if 1 ≤ 0 then call 5 var else 1`. -/
def deadImportTgt : Module := [(0, .ifLe (.lit 1) (.lit 0) (.call 5 .var) (.lit 1))]

/-- The closed-source disjunct of `ctxRefines_iff_standaloneRefines_of_closed_source_or_target`
on a syntactically open target: `const1Mod` is closed, `deadImportTgt` is not, standalone
refinement holds, and therefore contextual refinement holds. -/
theorem closed_source_open_target_collapse_witness :
    ClosedModule const1Mod ∧ ¬ ClosedModule deadImportTgt ∧
    StandaloneRefines const1Mod deadImportTgt ∧
    CtxRefines const1Mod deadImportTgt := by
  have hSt : StandaloneRefines const1Mod deadImportTgt := by
    intro entry fuel arg out h
    by_cases h0 : entry = 0
    · subst h0
      cases fuel with
      | zero => simpa [HasBehavior, eval] using h
      | succ n =>
        simpa [HasBehavior, eval, const1Mod, deadImportTgt, Module.lookup, evalExprWith] using h
    · cases fuel with
      | zero => simpa [HasBehavior, eval] using h
      | succ n =>
        simpa [HasBehavior, eval, const1Mod, deadImportTgt, Module.lookup, Ne.symm h0] using h
  refine ⟨by decide, by decide, hSt,
    (ctxRefines_iff_standaloneRefines_of_closed_source_or_target (.inl (by decide))).2 hSt⟩

/-- Caller module for the behavioural separate-compilation corollary:
`0 ↦ call 1 var + 0`. -/
def scMod1 : Module := [(0, .add (.call 1 .var) (.lit 0))]

/-- Callee module for the behavioural separate-compilation corollary: `1 ↦ 0 + var`. -/
def scMod2 : Module := [(1, .add (.lit 0) .var)]

/-- Interface for `scMod1` and `scMod2`: functions `0` and `1` return their argument;
every other name has an unsatisfiable precondition. -/
def scSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else if fn = 1 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Non-vacuity of all three premises of
`separate_compilation_preserves_partial_correctness_of_pass_ctxRefines`: the constant folder
`constFoldPass` is a contextually refining pass, `scMod1` and `scMod2` are disjoint, the
pass changes `scMod1`, the linked source program is partially correct for `scSpec`, and so
is the linked compiled program. -/
theorem nonvacuous_sep_comp_behavioural_corollary :
    PassCtxRefines constFoldPass ∧
    Linkable scMod1 scMod2 ∧
    constFoldPass scMod1 ≠ scMod1 ∧
    ProgramPartialCorrect (link scMod1 scMod2) scSpec ∧
    ProgramPartialCorrect (link (constFoldPass scMod1) (constFoldPass scMod2)) scSpec := by
  have hV1 : ModuleVerifiedPartial scMod1 scSpec scSpec := by
    intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [scMod1, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpPartial, scSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      exact ⟨trivial, fun v hv => by omega⟩
    · simp [scMod1, Module.lookup, Ne.symm h0] at hlu
  have hV2 : ModuleVerifiedPartial scMod2 scSpec scSpec := by
    intro fn body hlu x _
    by_cases h1 : fn = 1
    · subst h1
      simp only [scMod2, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpPartial, scSpec]
    · simp [scMod2, Module.lookup, Ne.symm h1] at hlu
  have hImpl : SpecsImplemented (link scMod1 scMod2) scSpec := by
    intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [scSpec, h0, h1] at hpre
  have hSrc : ProgramPartialCorrect (link scMod1 scMod2) scSpec :=
    ag_partial_correctness hImpl (moduleVerifiedPartial_link hV1 hV2)
  have hLink : Linkable scMod1 scMod2 := by decide
  exact ⟨passCtxRefines_pos, hLink, by decide, hSrc,
    separate_compilation_preserves_partial_correctness_of_pass_ctxRefines
      passCtxRefines_pos hLink hSrc⟩

end Toy.Link.Examples

namespace Toy.Link.Cex

open Toy.Link Toy.Link.Examples

/-- Tightness of the third premise (`ProgramPartialCorrect (link M₁ M₂) S`) of
`separate_compilation_preserves_partial_correctness_of_pass_ctxRefines`: the identity pass is
contextually refining and `const1Mod` is disjoint from the empty module, but the source link
is not partially correct for `zeroOutSpec`, and neither is the compiled link. -/
theorem cex_sep_comp_behavioural_corollary_without_hSrc :
    PassCtxRefines id ∧
    Linkable const1Mod ([] : Module) ∧
    ¬ ProgramPartialCorrect (link const1Mod []) zeroOutSpec ∧
    ¬ ProgramPartialCorrect (link (id const1Mod) (id [])) zeroOutSpec :=
  ⟨fun M => ctxRefines_refl M, by decide, programPartialCorrect_neg, programPartialCorrect_neg⟩

/-- `0 ↦ call 1 var`. -/
def pingMod : Module := [(0, .call 1 .var)]

/-- `1 ↦ call 0 var`. -/
def pongMod : Module := [(1, .call 0 .var)]

/-- Functions `0` and `1` accept every argument and must return `0`; every other name has
an unsatisfiable precondition. -/
def pingPongSpec : SpecEnv := fun fn =>
  if fn = 0 ∨ fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

private theorem pingPong_mayDiverge :
    ∀ fuel fn, (fn = 0 ∨ fn = 1) → HasBehavior fn (link pingMod pongMod) fuel 0 .outOfFuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _; simp [HasBehavior, eval]
  | succ n ih =>
    intro fn hfn
    rcases hfn with rfl | rfl
    · simpa [HasBehavior, eval, link, pingMod, pongMod, Module.lookup, evalExprWith] using
        ih 1 (.inr rfl)
    · simpa [HasBehavior, eval, link, pingMod, pongMod, Module.lookup, evalExprWith] using
        ih 0 (.inl rfl)

/-- Separately chosen termination measures do not compose under linking. `pingMod` is
verified for total correctness with the measure `μ₁ fn _ = if fn = 0 then 1 else 0` and
`pongMod` with `μ₂ fn _ = if fn = 1 then 1 else 0`, both over the well-founded `Nat.lt`;
the two modules are disjoint and their link implements every satisfiable precondition of
the shared interface; yet the linked program is not totally correct (it calls `0` and `1`
alternately forever). `ag_total_correctness_of_wf_call_measure` needs one measure `(rel, μ)`
shared by every function of the program. -/
theorem independent_measures_do_not_compose :
    Linkable pingMod pongMod ∧
    SpecsImplemented (link pingMod pongMod) pingPongSpec ∧
    WellFounded Nat.lt ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 0 then 1 else 0)
      pingMod pingPongSpec pingPongSpec ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 1 then 1 else 0)
      pongMod pingPongSpec pingPongSpec ∧
    ¬ ProgramTotalCorrect (link pingMod pongMod) pingPongSpec := by
  refine ⟨by decide, ?_, Nat.lt_wfRel.wf, ?_, ?_, ?_⟩
  · intro fn x hpre
    by_cases h01 : fn = 0 ∨ fn = 1
    · rcases h01 with rfl | rfl <;> decide
    · simp [pingPongSpec, h01] at hpre
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [pingMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpCallDec, pingPongSpec]
    · simp [pingMod, Module.lookup, Ne.symm h0] at hlu
  · intro fn body hlu x _
    by_cases h1 : fn = 1
    · subst h1
      simp only [pongMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpCallDec, pingPongSpec]
    · simp [pongMod, Module.lookup, Ne.symm h1] at hlu
  · intro hTot
    obtain ⟨fuel, hf⟩ := hTot 0 0 (by simp [pingPongSpec])
    obtain ⟨_, heq, _⟩ := hf .outOfFuel (pingPong_mayDiverge fuel 0 (.inl rfl))
    cases heq

end Toy.Link.Cex

namespace Toy.Link.Unfolded

open Toy.Link

/-- Unfolded statement of `ctxRefines_sameDom`, with `CtxRefines`, `Linkable`,
`EntryRefines`, `HasBehavior`, and `SameDom` unfolded. -/
def ctxRefines_sameDom_unfolded (M M' : Module) : Prop :=
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg →
          out ∈ eval fuel (link C M) entry arg) →
  (∀ fn, M.Defines fn ↔ M'.Defines fn)

theorem ctxRefines_sameDom_unfolded_iff (M M' : Module) :
    ctxRefines_sameDom_unfolded M M' ↔ (CtxRefines M M' → SameDom M M') :=
  Iff.rfl

end Toy.Link.Unfolded
