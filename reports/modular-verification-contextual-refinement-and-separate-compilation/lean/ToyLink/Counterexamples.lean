import ToyLink.Examples

/-!
# Counterexamples and canonical hypothesis-tightness witnesses

All theorems in this file are fully proved without `sorry` and depend only on
standard Lean axioms.
Contains:
- negative results: main-entry refinement of closed modules is not contextual refinement
  (only other entries separate them); for open modules, standalone refinement plus
  refinement in the shipped program is not contextual refinement (the context supplies
  the separating behaviour); adding or deleting a function breaks contextual refinement
  (domain observability); contextual refinement rejects new divergence and changes of
  call depth; circular total correctness is unsound without a measure; an incomparable
  callee spec breaks link composition; verifiability preservation is not behavioural
  refinement; a callee-dependent rewrite breaks under spec-compliant callee replacement;
- canonical tightness counterexamples for every `tight` hypothesis of the main theorems
  in `ToyLink.Statements`, each proving all remaining hypotheses and the negation of the
  theorem's conclusion.
-/

namespace Toy.Link.Cex

open Toy.Link
open Toy.Link.Examples

/-! ## Closed modules: refinement at one entry is not contextual refinement

For closed modules, contextual refinement coincides with standalone refinement at every
entry (`ctxRefines_iff_standaloneRefines_of_closed_source_or_target`), so the only gap
between "refines at the designated entry" and `CtxRefines` is the other exported entries;
no context is needed to exhibit it. -/

/-- Closed source module exporting `0` (calls `1(5)`) and `1` (returns `var`). -/
def specSrc : Module := [(0, .call 1 (.lit 5)), (1, .var)]

/-- Closed target module specializing exported `1` to return `5` regardless of argument. -/
def specTgt : Module := [(0, .call 1 (.lit 5)), (1, .lit 5)]

private theorem specSrc_specTgt_entryRefines :
    EntryRefines 0 specSrc specTgt ∧ EntryRefines 0 specTgt specSrc := by
  have hEq : ∀ fuel arg, eval fuel specSrc 0 arg = eval fuel specTgt 0 arg := by
    intro fuel arg
    cases fuel with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ m =>
        simp [eval, specSrc, specTgt, Module.lookup, evalExprWith]
  exact ⟨fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h,
         fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h⟩

/-- **Closed modules: main-entry refinement is not contextual refinement.**
Specializing the exported function `1` to the argument `5` used by its only in-module
caller keeps both modules closed with equal domains and gives refinement in both
directions at the designated entry `0`; refinement already fails at entry `1` with no
context at all, hence `CtxRefines` fails. -/
theorem cex_closed_main_entry_refines_not_ctxRefines :
    ClosedModule specSrc ∧
    ClosedModule specTgt ∧
    SameDom specSrc specTgt ∧
    EntryRefines 0 specSrc specTgt ∧
    EntryRefines 0 specTgt specSrc ∧
    ¬ EntryRefines 1 specSrc specTgt ∧
    ¬ CtxRefines specSrc specTgt := by
  have hNot1 : ¬ EntryRefines 1 specSrc specTgt := by
    intro h
    have h5 : HasBehavior 1 specTgt 1 9 (.val 5) := by decide
    exact absurd (h 1 9 _ h5) (by decide)
  refine ⟨by decide, by decide, ?_,
    specSrc_specTgt_entryRefines.1, specSrc_specTgt_entryRefines.2, hNot1,
    fun h => hNot1 (standaloneRefines_of_ctxRefines h 1)⟩
  intro fn
  by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
    simp [Module.Defines, Module.lookup, specSrc, specTgt, h0, h1, Ne.symm]

/-! ## Open modules: the context genuinely supplies behaviour -/

/-- Open source module: `1(x)` forwards `x` to the import `5`; the only in-module caller,
`0`, calls `1(3)`. -/
def openSpecSrc : Module := [(0, .call 1 (.lit 3)), (1, .call 5 .var)]

/-- Open target module: `1` specialized to the argument `3` used by its only in-module
caller. -/
def openSpecTgt : Module := [(0, .call 1 (.lit 3)), (1, .call 5 (.lit 3))]

/-- The program the module ships in: the import `5` is the identity. -/
def identityImport : Module := [(5, .var)]

/-- A context whose import `5` calls back into the module's exported `1`. -/
def callbackImport : Module := [(5, .ifLe .var (.lit 3) (.call 1 (.lit 9)) .var)]

private theorem openSpec_standalone_eq :
    ∀ fuel e a, eval fuel openSpecSrc e a = eval fuel openSpecTgt e a := by
  intro fuel e a
  by_cases h0 : e = 0
  · subst h0
    rcases fuel with _ | _ | _ | n
    · rfl
    · rfl
    · rfl
    · simp [eval, openSpecSrc, openSpecTgt, Module.lookup, evalExprWith]
  · by_cases h1 : e = 1
    · subst h1
      rcases fuel with _ | _ | n
      · rfl
      · rfl
      · simp [eval, openSpecSrc, openSpecTgt, Module.lookup, evalExprWith]
    · rcases fuel with _ | n
      · rfl
      · simp [eval, openSpecSrc, openSpecTgt, Module.lookup, Ne.symm h0, Ne.symm h1]

private theorem openSpec_identity_main_eq :
    ∀ fuel a, eval fuel (link identityImport openSpecSrc) 0 a =
      eval fuel (link identityImport openSpecTgt) 0 a := by
  intro fuel a
  rcases fuel with _ | _ | _ | _ | n
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [eval, link, identityImport, openSpecSrc, openSpecTgt, Module.lookup, evalExprWith]

/-- **Open modules: standalone refinement and refinement in the shipped program are not
contextual refinement.** The specialization of `1` to the argument `3` used by its only
in-module caller is a refinement (in both directions) at every entry when the modules run
standalone (the import `5` is then unresolved), and at the designated entry `0` of the
program `link identityImport _` they ship in. Yet in that same program, calling `1(9)`
separates them; and a context whose import calls back into `1` separates them even at the
designated entry `0`. Both modules are open; by
`ctxRefines_iff_standaloneRefines_of_closed_source_or_target` this is necessary. -/
theorem cex_open_specialization_standalone_refines_not_ctxRefines :
    ¬ ClosedModule openSpecSrc ∧ ¬ ClosedModule openSpecTgt ∧
    SameDom openSpecSrc openSpecTgt ∧
    StandaloneRefines openSpecSrc openSpecTgt ∧
    StandaloneRefines openSpecTgt openSpecSrc ∧
    Linkable identityImport openSpecSrc ∧ Linkable identityImport openSpecTgt ∧
    EntryRefines 0 (link identityImport openSpecSrc) (link identityImport openSpecTgt) ∧
    EntryRefines 0 (link identityImport openSpecTgt) (link identityImport openSpecSrc) ∧
    ¬ EntryRefines 1 (link identityImport openSpecSrc) (link identityImport openSpecTgt) ∧
    Linkable callbackImport openSpecSrc ∧ Linkable callbackImport openSpecTgt ∧
    ¬ EntryRefines 0 (link callbackImport openSpecSrc) (link callbackImport openSpecTgt) ∧
    ¬ CtxRefines openSpecSrc openSpecTgt := by
  have hNot1 :
      ¬ EntryRefines 1 (link identityImport openSpecSrc) (link identityImport openSpecTgt) := by
    intro h
    have ht : HasBehavior 1 (link identityImport openSpecTgt) 2 9 (.val 3) := by decide
    exact absurd (h 2 9 _ ht) (by decide)
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide, by decide, ?_, ?_, hNot1,
    by decide, by decide, ?_, ?_⟩
  · intro fn
    by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
      simp [Module.Defines, Module.lookup, openSpecSrc, openSpecTgt, h0, h1, Ne.symm]
  · intro e fuel a out h
    simpa [HasBehavior, openSpec_standalone_eq] using h
  · intro e fuel a out h
    simpa [HasBehavior, openSpec_standalone_eq] using h
  · intro fuel a out h
    simpa [HasBehavior, openSpec_identity_main_eq] using h
  · intro fuel a out h
    simpa [HasBehavior, openSpec_identity_main_eq] using h
  · intro h
    have ht : HasBehavior 0 (link callbackImport openSpecTgt) 5 0 .outOfFuel := by decide
    exact absurd (h 5 0 _ ht) (by decide)
  · intro h
    exact hNot1 (h identityImport (by decide) (by decide) 1)

/-- Tightness of the closedness disjunction in
`ctxRefines_iff_standaloneRefines_of_closed_source_or_target`: with both modules open, the
equivalence fails. -/
theorem cex_collapse_without_closed_side :
    ¬ (ClosedModule openSpecSrc ∨ ClosedModule openSpecTgt) ∧
    ¬ (CtxRefines openSpecSrc openSpecTgt ↔ StandaloneRefines openSpecSrc openSpecTgt) := by
  obtain ⟨h1, h2, _, h4, -, -, -, -, -, -, -, -, -, h14⟩ :=
    cex_open_specialization_standalone_refines_not_ctxRefines
  exact ⟨fun h => h.elim h1 h2, fun h => h14 (h.2 h4)⟩

/-! ## Domain observability: adding or deleting any function breaks `CtxRefines` -/

/-- Source module exporting `0` (`42`) and an unused export `1` (`7`). -/
def deadSrc : Module := [(0, .lit 42), (1, .lit 7)]

/-- Target module with the unused export `1` deleted. -/
def deadTgt : Module := [(0, .lit 42)]

private theorem deadSrc_deadTgt_entryRefines :
    EntryRefines 0 deadSrc deadTgt ∧ EntryRefines 0 deadTgt deadSrc := by
  have hEq : ∀ fuel arg, eval fuel deadSrc 0 arg = eval fuel deadTgt 0 arg := by
    intro fuel arg
    cases fuel <;> rfl
  exact ⟨fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h,
         fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h⟩

/-- **Deleting an unused export fails `CtxRefines`, by domain observability alone.**
Both modules are closed and agree at the designated entry `0`, but they have different
domains, so `ctxRefines_sameDom` already rules out `CtxRefines`; calling `1` with the
empty context observes `undefinedCall`. This is an instance of `ctxRefines_sameDom`, not a
context-interaction phenomenon. -/
theorem cex_delete_unused_export_not_ctxRefines :
    ClosedModule deadSrc ∧
    ClosedModule deadTgt ∧
    EntryRefines 0 deadSrc deadTgt ∧
    EntryRefines 0 deadTgt deadSrc ∧
    ¬ SameDom deadSrc deadTgt ∧
    ¬ EntryRefines 1 deadSrc deadTgt ∧
    ¬ CtxRefines deadSrc deadTgt := by
  have hDom : ¬ SameDom deadSrc deadTgt := fun h => absurd ((h 1).1 (by decide)) (by decide)
  refine ⟨by decide, by decide, deadSrc_deadTgt_entryRefines.1,
    deadSrc_deadTgt_entryRefines.2, hDom, ?_, fun h => hDom (ctxRefines_sameDom h)⟩
  intro h
  have hu : HasBehavior 1 deadTgt 1 0 .undefinedCall := by decide
  exact absurd (h 1 0 _ hu) (by decide)

/-- **Adding an unused helper function fails `CtxRefines`.** The model has no private
symbols, so a fresh helper (as introduced by cloning-based specialization or outlining)
is a new export and changes the domain. -/
theorem cex_add_fresh_helper_not_ctxRefines :
    EntryRefines 0 [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] ∧
    EntryRefines 0 [(0, .lit 0), (7, .lit 0)] [(0, .lit 0)] ∧
    ¬ SameDom [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] ∧
    ¬ CtxRefines [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] := by
  have hEq : ∀ fuel arg, eval fuel [(0, .lit 0)] 0 arg =
      eval fuel [(0, .lit 0), (7, .lit 0)] 0 arg := by
    intro fuel arg; cases fuel <;> rfl
  have hDom : ¬ SameDom [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] :=
    fun h => absurd ((h 7).2 (by decide)) (by decide)
  exact ⟨fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h,
    fun fuel arg out h => by simpa [HasBehavior, hEq fuel arg] using h, hDom,
    fun h => hDom (ctxRefines_sameDom h)⟩

/-! ## Contextual refinement observes divergence and call depth -/

/-- `0` calls `1`, which returns `0`. -/
def termSrc : Module := [(0, .call 1 .var), (1, .lit 0)]

/-- `0` calls `1`, which loops. -/
def divTgt : Module := [(0, .call 1 .var), (1, .call 1 .var)]

private theorem divTgt_one_mayDiverge : ∀ fuel, HasBehavior 1 divTgt fuel 0 .outOfFuel := by
  intro fuel
  induction fuel with
  | zero => simp [HasBehavior, eval]
  | succ n ih => simpa [HasBehavior, eval, divTgt, Module.lookup, evalExprWith] using ih

/-- **`CtxRefines` rejects newly introduced divergence** (tightness of `CtxRefines` in
`ctxRefines_reflects_mayDiverge`). With equal domains and the empty context, the target
may diverge at entry `0` where the source cannot, and `CtxRefines` fails. -/
theorem cex_ctxRefines_rejects_new_divergence :
    SameDom termSrc divTgt ∧
    Linkable [] termSrc ∧
    MayDiverge (link [] divTgt) 0 0 ∧
    ¬ MayDiverge (link [] termSrc) 0 0 ∧
    ¬ CtxRefines termSrc divTgt := by
  have hDiv : MayDiverge (link [] divTgt) 0 0 := by
    intro fuel
    cases fuel with
    | zero => simp [HasBehavior, eval]
    | succ n =>
      simpa [HasBehavior, eval, link, divTgt, Module.lookup, evalExprWith] using
        divTgt_one_mayDiverge n
  have hNot : ¬ MayDiverge (link [] termSrc) 0 0 := fun h => absurd (h 2) (by decide)
  refine ⟨?_, by decide, hDiv, hNot, fun h => hNot (ctxRefines_reflects_mayDiverge h
    (by decide) hDiv)⟩
  intro fn
  by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
    simp [Module.Defines, Module.lookup, termSrc, divTgt, h0, h1, Ne.symm]

/-- `0` returns `0` directly. -/
def directMod : Module := [(0, .lit 0), (1, .lit 0)]

/-- `0` returns `0` through a call to `1`. -/
def viaCallMod : Module := [(0, .call 1 .var), (1, .lit 0)]

/-- **`CtxRefines` fixes call depth, in both directions.** `directMod` and `viaCallMod`
have equal domains and return the same value at every entry and argument once the fuel is
at least `2`, yet neither contextually refines the other: at fuel `1` one returns and the
other is out of fuel. So `CtxRefines` is strictly finer than inclusion of eventual results
(or of divergence-sensitive behaviour); it forbids adding or removing calls on any path. -/
theorem cex_ctxRefines_fixes_call_depth :
    SameDom directMod viaCallMod ∧
    (∀ fuel e a, 2 ≤ fuel → eval fuel directMod e a = eval fuel viaCallMod e a) ∧
    ¬ CtxRefines directMod viaCallMod ∧
    ¬ CtxRefines viaCallMod directMod := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fn
    by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
      simp [Module.Defines, Module.lookup, directMod, viaCallMod, h0, h1, Ne.symm]
  · intro fuel e a hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    by_cases h0 : e = 0
    · subst h0; simp [eval, directMod, viaCallMod, Module.lookup, evalExprWith]
    · by_cases h1 : e = 1
      · subst h1; simp [eval, directMod, viaCallMod, Module.lookup, evalExprWith]
      · simp [eval, directMod, viaCallMod, Module.lookup, Ne.symm h0, Ne.symm h1]
  · intro h
    have ht : HasBehavior 0 (link [] viaCallMod) 1 0 .outOfFuel := by decide
    exact absurd (h [] (by decide) (by decide) 0 1 0 _ ht) (by decide)
  · intro h
    have ht : HasBehavior 0 (link [] directMod) 1 0 (.val 0) := by decide
    exact absurd (h [] (by decide) (by decide) 0 1 0 _ ht) (by decide)

/-! ## Circular assume-guarantee total correctness is unsound without a measure -/

private theorem selfLoop_not_total_zeroOut : ¬ FnTotalCorrect selfLoopMod 0 (zeroOutSpec 0) := by
  intro h
  obtain ⟨fuel, htot⟩ := h 0 trivial
  have hof : HasBehavior 0 selfLoopMod fuel 0 .outOfFuel := by
    clear htot
    induction fuel with
    | zero => simp [HasBehavior, eval]
    | succ n ih =>
      simpa [HasBehavior, eval, selfLoopMod, Module.lookup, evalExprWith] using ih
  rcases htot .outOfFuel hof with ⟨_, heq, _⟩
  cases heq

/-- **Circular assume-guarantee is unsound for total correctness.**
`selfLoopMod` (`0` simply calls `0(var)`) is closed, implements `zeroOutSpec`, and
satisfies `ModuleVerifiedPartial selfLoopMod zeroOutSpec zeroOutSpec` (verified to
return `0` assuming `0` returns `0`), yet fails `ProgramTotalCorrect`. -/
theorem cex_ag_total_unsound_without_measure :
    ClosedModule selfLoopMod ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ModuleVerifiedPartial selfLoopMod zeroOutSpec zeroOutSpec ∧
    (zeroOutSpec 0).pre 0 ∧
    (∃ v, (zeroOutSpec 0).post 0 v) ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec := by
  refine ⟨by decide, ?_, ?_, trivial, ⟨0, rfl⟩, ?_⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zeroOutSpec, h0] at hpre
  · intro fn body hlu x hpre
    by_cases h0 : fn = 0
    · subst h0
      simp only [selfLoopMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpPartial, zeroOutSpec, ite_true]
      exact ⟨trivial, fun vRes hv => hv⟩
    · simp [selfLoopMod, Module.lookup, Ne.symm h0] at hlu
  · intro hTot
    exact selfLoop_not_total_zeroOut (hTot 0)

/-! ## Incomparable callee specification breaks link composition -/

/-- Caller: `0` returns `1(0)`. -/
def incCaller : Module := [(0, .call 1 (.lit 0))]
/-- Callee: `1` returns `11`. -/
def incCallee : Module := [(1, .lit 11)]
/-- Caller guarantee: `0` returns exactly `10`. -/
def incGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
/-- Interface the caller assumes for `1`: on `x ≥ 0`, returns exactly `10`. -/
def incAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
/-- Spec the callee satisfies: on every input, returns at least `10`
(weaker precondition, but a postcondition that does not imply the assumed one). -/
def incActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

private theorem incCaller_verified :
    ModuleVerifiedPartial incCaller (mixEnv incCaller incGuar incAssumed) incGuar := by
  intro fn body hlu x _
  by_cases h0 : fn = 0
  · subst h0
    simp only [incCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    have hd1 : ¬ incCaller.Defines 1 := by decide
    have hA1 : mixEnv incCaller incGuar incAssumed 1 = incAssumed 1 := by simp [mixEnv, hd1]
    simp only [wpPartial, hA1]
    simp [incAssumed, incGuar]
  · simp [incCaller, Module.lookup, Ne.symm h0] at hlu

private theorem incCallee_correct : ProgramPartialCorrect incCallee incActual := by
  intro fn fuel x out hpre hbeh
  by_cases h1 : fn = 1
  · subst h1
    cases fuel with
    | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
    | succ n =>
      simp only [HasBehavior, eval, incCallee, Module.lookup, ite_true, evalExprWith,
        List.mem_singleton] at hbeh
      subst hbeh
      exact .inr ⟨11, rfl, by simp [incActual]⟩
  · simp [incActual, h1] at hpre

/-- **A callee spec incomparable with the assumed one breaks composition, even when its
precondition is weaker.** `incCaller` is verified assuming `incAssumed` for its import `1`
(`pre: x ≥ 0, post: v = 10`). The callee satisfies `incActual` (`pre: True, post: v ≥ 10`):
the precondition side refines (`WeakensPre` holds at every external name), the
postcondition side does not, and the assumed spec does not refine `incActual` either
(neither spec refines the other). Linking violates the caller's guarantee. The
precondition-side failure is witnessed separately by
`cex_spec_refinement_without_weakensPre`. -/
theorem cex_link_fails_for_incomparable_callee_spec :
    Linkable incCaller incCallee ∧
    ModuleVerifiedPartial incCaller (mixEnv incCaller incGuar incAssumed) incGuar ∧
    ProgramPartialCorrect incCallee incActual ∧
    (∀ g, ¬ incCaller.Defines g → WeakensPre (incAssumed g) (incActual g)) ∧
    ¬ StrengthensPostUnderPre (incAssumed 1) (incActual 1) ∧
    ¬ WeakensPre (incActual 1) (incAssumed 1) ∧
    ¬ (∀ f, incCaller.Defines f → FnPartialCorrect (link incCaller incCallee) f (incGuar f)) := by
  refine ⟨by decide, incCaller_verified, incCallee_correct, ?_, ?_, ?_, ?_⟩
  · intro g _ x hx
    by_cases h1 : g = 1
    · subst h1; simp [incActual]
    · simp [incAssumed, h1] at hx
  · intro h
    have := h 0 11 (by simp [incAssumed]) (by simp [incActual])
    simp [incAssumed] at this
  · intro h
    have := h (-1) trivial
    simp [incAssumed] at this
  · intro h
    have hBeh : HasBehavior 0 (link incCaller incCallee) 2 0 (.val 11) := by decide
    rcases h 0 (by decide) 2 0 (.val 11) trivial hBeh with h1 | ⟨v, h2, hpost⟩
    · cases h1
    · cases h2
      simp [incGuar] at hpost

/-! ## Separate compilation: a callee-dependent rewrite breaks on callee replacement -/

def inlSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 1 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v ≥ 1 }
  else { pre := fun _ => False, post := fun _ _ => False }

def inlCaller : Module := [(0, .call 1 .var)]
def inlCallerOpt : Module := [(0, .sub (.add (.call 1 .var) (.call 1 .var)) (.lit 2))]
def inlCallee1 : Module := [(1, .lit 2)]
def inlCallee2 : Module := [(1, .lit 1)]

private theorem inlCaller_ver : ModuleVerifiedPartial inlCaller inlSpec inlSpec := by
  intro fn body hlu x _
  by_cases h0 : fn = 0
  · subst h0
    simp only [inlCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp only [wpPartial, inlSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
    exact ⟨trivial, fun v hv => hv⟩
  · simp [inlCaller, Module.lookup, Ne.symm h0] at hlu

private theorem inlCallee1_ver : ModuleVerifiedPartial inlCallee1 inlSpec inlSpec := by
  intro fn body hlu x _
  by_cases h1 : fn = 1
  · subst h1
    simp only [inlCallee1, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp [wpPartial, inlSpec]
  · simp [inlCallee1, Module.lookup, Ne.symm h1] at hlu

private theorem inlCallee2_ver : ModuleVerifiedPartial inlCallee2 inlSpec inlSpec := by
  intro fn body hlu x _
  by_cases h1 : fn = 1
  · subst h1
    simp only [inlCallee2, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp [wpPartial, inlSpec]
  · simp [inlCallee2, Module.lookup, Ne.symm h1] at hlu

private theorem inlCallee2_fn1_correct : FnPartialCorrect inlCallee2 1 (inlSpec 1) := by
  intro fuel x out _ hbeh
  cases fuel with
  | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
  | succ n =>
    simp only [HasBehavior, eval, inlCallee2, Module.lookup, ite_true, evalExprWith,
      List.mem_singleton] at hbeh
    subst hbeh
    exact .inr ⟨1, rfl, by simp [inlSpec]⟩

private theorem inl_orig_callee2_correct :
    ProgramPartialCorrect (link inlCaller inlCallee2) inlSpec := by
  intro fn fuel x out hpre hbeh
  by_cases h0 : fn = 0
  · subst h0
    cases fuel with
    | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
    | succ n =>
      cases n with
      | zero =>
        simp [HasBehavior, eval, link, inlCaller, inlCallee2, Module.lookup, evalExprWith] at hbeh
        exact .inl hbeh
      | succ m =>
        simp [HasBehavior, eval, link, inlCaller, inlCallee2, Module.lookup, evalExprWith] at hbeh
        subst hbeh
        exact .inr ⟨1, rfl, by simp [inlSpec]⟩
  · by_cases h1 : fn = 1
    · subst h1
      cases fuel with
      | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
      | succ n =>
        simp [HasBehavior, eval, link, inlCaller, inlCallee2, Module.lookup, evalExprWith] at hbeh
        subst hbeh
        exact .inr ⟨1, rfl, by simp [inlSpec]⟩
    · simp [inlSpec, h0, h1] at hpre

private theorem link_inl_equiv_under_callee1 :
    CtxRefines (link inlCaller inlCallee1) (link inlCallerOpt inlCallee1) ∧
    CtxRefines (link inlCallerOpt inlCallee1) (link inlCaller inlCallee1) := by
  have hStep : ∀ C, Linkable C (link inlCaller inlCallee1) →
      ∀ fuel fn arg,
        eval fuel (link C (link inlCaller inlCallee1)) fn arg =
        eval fuel (link C (link inlCallerOpt inlCallee1)) fn arg := by
    intro C hC fuel
    have hc0 : ¬ C.Defines 0 := fun hc => hC 0 ⟨hc, by decide⟩
    have hc1 : ¬ C.Defines 1 := fun hc => hC 1 ⟨hc, by decide⟩
    have hL : ∀ fn, (link C (link inlCaller inlCallee1)).lookup fn =
        if fn = 0 then some (.call 1 .var)
        else if fn = 1 then some (.lit 2)
        else C.lookup fn := by
      intro fn; rw [lookup_link]
      by_cases hf0 : fn = 0
      · subst hf0; rw [lookup_none_of_not_defines hc0]; rfl
      · by_cases hf1 : fn = 1
        · subst hf1; rw [lookup_none_of_not_defines hc1]
          simp [link, inlCaller, inlCallee1, Module.lookup]
        · cases C.lookup fn <;>
            simp [link, inlCaller, inlCallee1, Module.lookup, hf0, hf1, Ne.symm hf0, Ne.symm hf1]
    have hR : ∀ fn, (link C (link inlCallerOpt inlCallee1)).lookup fn =
        if fn = 0 then some (.sub (.add (.call 1 .var) (.call 1 .var)) (.lit 2))
        else if fn = 1 then some (.lit 2)
        else C.lookup fn := by
      intro fn; rw [lookup_link]
      by_cases hf0 : fn = 0
      · subst hf0; rw [lookup_none_of_not_defines hc0]; rfl
      · by_cases hf1 : fn = 1
        · subst hf1; rw [lookup_none_of_not_defines hc1]
          simp [link, inlCallerOpt, inlCallee1, Module.lookup]
        · cases C.lookup fn <;>
            simp [link, inlCallerOpt, inlCallee1, Module.lookup, hf0, hf1, Ne.symm hf0, Ne.symm hf1]
    clear hC hc0 hc1
    induction fuel with
    | zero => intro fn arg; rfl
    | succ n ih =>
      intro fn arg
      simp only [eval, hL fn, hR fn]
      by_cases hf0 : fn = 0
      · subst hf0
        simp only [ite_true]
        cases n with
        | zero => rfl
        | succ m =>
          have hCallee : eval (m + 1) (link C (link inlCaller inlCallee1)) 1 arg = [.val 2] := by
            simp [eval, hL 1, evalExprWith]
          have hCalleeR : eval (m + 1) (link C (link inlCallerOpt inlCallee1)) 1 arg = [.val 2] := by
            simp [eval, hR 1, evalExprWith]
          simp [evalExprWith, hCallee, hCalleeR]
      · by_cases hf1 : fn = 1
        · subst hf1; simp [evalExprWith]
        · simp only [hf0, hf1, ite_false]
          cases C.lookup fn with
          | none => rfl
          | some body => exact evalExprWith_congr ih arg body
  constructor
  · intro C hC₁ _ entry fuel arg out hOut
    simpa [HasBehavior, hStep C hC₁ fuel entry arg] using hOut
  · intro C _ hC₂ entry fuel arg out hOut
    have hC₁ : Linkable C (link inlCaller inlCallee1) := by
      refine linkable_of_sameDom_right ?_ hC₂
      intro fn
      by_cases h0 : fn = 0 <;> by_cases h1 : fn = 1 <;>
        simp [Module.Defines, link, inlCaller, inlCallee1,
          Module.lookup, h0, h1, Ne.symm]
    simpa [HasBehavior, hStep C hC₁ fuel entry arg] using hOut

/-- The rewritten caller is not modularly verified against the shared interface. -/
theorem inlCallerOpt_not_verified : ¬ ModuleVerifiedPartial inlCallerOpt inlSpec inlSpec := by
  intro h
  have h0 := h 0 _ rfl 0 trivial
  have hne : (1 : Nat) ≠ 0 := by decide
  simp only [wpPartial, inlSpec, hne, ite_true, ite_false] at h0
  have := h0.2 1 (by decide) |>.2 1 (by decide)
  omega

/-- The rewrite is not a contextual refinement of the caller module. -/
theorem inlCaller_not_ctxRefines_inlCallerOpt : ¬ CtxRefines inlCaller inlCallerOpt := by
  intro h
  have hB : HasBehavior 0 (link inlCallee2 inlCallerOpt) 2 0 (.val 0) := by decide
  exact absurd (h inlCallee2 (by decide) (by decide) 0 2 0 _ hB) (by decide)

/-- A concrete per-module pass performing the rewrite. -/
def inlPass (M : Module) : Module := if M = inlCaller then inlCallerOpt else M

/-- The rewriting pass violates `PreservesVerifiedPartial` (and `PassCtxRefines`). -/
theorem inlPass_not_preservesVerified :
    ¬ PreservesVerifiedPartial inlPass inlSpec ∧ ¬ PassCtxRefines inlPass := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h inlCaller inlCaller_ver
    rw [show inlPass inlCaller = inlCallerOpt by simp [inlPass]] at this
    exact inlCallerOpt_not_verified this
  · have := h inlCaller
    rw [show inlPass inlCaller = inlCallerOpt by simp [inlPass]] at this
    exact inlCaller_not_ctxRefines_inlCallerOpt this

/-- **A rewrite justified by one callee's body breaks when the callee is replaced by
another implementation of the same spec.** `inlCallerOpt` rewrites `call 1 var` to
`(call 1 var + call 1 var) - 2` (keeping both calls; this is an algebraic rewrite, not
inlining), which is valid only because `inlCallee1` returns `2`: in the whole program with
`inlCallee1` the two callers are contextually equivalent. The rewrite is not a per-module
refinement (`¬ CtxRefines inlCaller inlCallerOpt`) and not verifiable against the shared
interface `inlSpec`. Replacing `inlCallee1` by `inlCallee2` (`1 ↦ 1`), which satisfies
`inlSpec` too and keeps the original program partially correct, makes the rewritten program
return `0`, violating `inlSpec` and refinement. -/
theorem cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement :
    Linkable inlCaller inlCallee1 ∧
    Linkable inlCaller inlCallee2 ∧
    ModuleVerifiedPartial inlCaller inlSpec inlSpec ∧
    ModuleVerifiedPartial inlCallee1 inlSpec inlSpec ∧
    ModuleVerifiedPartial inlCallee2 inlSpec inlSpec ∧
    FnPartialCorrect inlCallee2 1 (inlSpec 1) ∧
    ProgramPartialCorrect (link inlCaller inlCallee2) inlSpec ∧
    CtxRefines (link inlCaller inlCallee1) (link inlCallerOpt inlCallee1) ∧
    CtxRefines (link inlCallerOpt inlCallee1) (link inlCaller inlCallee1) ∧
    ¬ ModuleVerifiedPartial inlCallerOpt inlSpec inlSpec ∧
    ¬ CtxRefines inlCaller inlCallerOpt ∧
    ¬ ProgramPartialCorrect (link inlCallerOpt inlCallee2) inlSpec ∧
    ¬ EntryRefines 0 (link inlCaller inlCallee2) (link inlCallerOpt inlCallee2) := by
  refine ⟨by decide, by decide, inlCaller_ver, inlCallee1_ver, inlCallee2_ver,
    inlCallee2_fn1_correct, inl_orig_callee2_correct,
    link_inl_equiv_under_callee1.1, link_inl_equiv_under_callee1.2,
    inlCallerOpt_not_verified, inlCaller_not_ctxRefines_inlCallerOpt, ?_, ?_⟩
  · intro hSat
    have hBeh : HasBehavior 0 (link inlCallerOpt inlCallee2) 2 0 (.val 0) := by decide
    rcases hSat 0 2 0 (.val 0) trivial hBeh with h1 | ⟨v, h2, hpost⟩
    · cases h1
    · cases h2
      simp [inlSpec] at hpost
  · intro hRef
    have hBehOpt : HasBehavior 0 (link inlCallerOpt inlCallee2) 2 0 (.val 0) := by decide
    have hBehOrig : HasBehavior 0 (link inlCaller inlCallee2) 2 0 (.val 0) :=
      hRef 2 0 (.val 0) hBehOpt
    exact absurd hBehOrig (by decide)

/-! ## Canonical tightness counterexamples for `ctxRefines_trans` -/

private def const2Mod : Module := [(0, .lit 2)]

/-- Tightness of the first premise of `ctxRefines_trans` (with `M₂ = M₃ = const1Mod`; the
second premise holds by reflexivity, and the conclusion is the negated first premise).
Tightness of transitivity premises is immediate for any relation that is not total. -/
theorem cex_ctxRefines_trans_without_first :
    ¬ CtxRefines const0Mod const1Mod ∧
    CtxRefines const1Mod const1Mod :=
  ⟨ctxRefines_neg, ctxRefines_refl const1Mod⟩

theorem cex_ctxRefines_trans_without_second :
    CtxRefines choose01Mod const0Mod ∧
    ¬ CtxRefines const0Mod const2Mod ∧
    ¬ CtxRefines choose01Mod const2Mod := by
  refine ⟨ctxRefines_pos, ?_, ?_⟩
  · intro h
    have h2 : HasBehavior 0 (link [] const2Mod) 1 0 (.val 2) := by decide
    exact absurd (h [] (by decide) (by decide) 0 1 0 (.val 2) h2) (by decide)
  · intro h
    have h2 : HasBehavior 0 (link [] const2Mod) 1 0 (.val 2) := by decide
    exact absurd (h [] (by decide) (by decide) 0 1 0 (.val 2) h2) (by decide)

/-! ## Canonical tightness counterexamples for `ctxRefines_link_congr` -/

private def oneZeroMod : Module := [(1, .lit 0)]

theorem cex_link_congr_without_first_refines :
    ¬ CtxRefines const0Mod const1Mod ∧
    CtxRefines oneZeroMod oneZeroMod ∧
    Linkable const0Mod oneZeroMod ∧
    ¬ CtxRefines (link const0Mod oneZeroMod) (link const1Mod oneZeroMod) := by
  refine ⟨ctxRefines_neg, ctxRefines_refl oneZeroMod, by decide, ?_⟩
  intro h
  have h1 : HasBehavior 0 (link [] (link const1Mod oneZeroMod)) 1 0 (.val 1) := by decide
  exact absurd (h [] (by decide) (by decide) 0 1 0 (.val 1) h1) (by decide)

theorem cex_link_congr_without_second_refines :
    CtxRefines oneZeroMod oneZeroMod ∧
    ¬ CtxRefines const0Mod const1Mod ∧
    Linkable oneZeroMod const0Mod ∧
    ¬ CtxRefines (link oneZeroMod const0Mod) (link oneZeroMod const1Mod) := by
  refine ⟨ctxRefines_refl oneZeroMod, ctxRefines_neg, by decide, ?_⟩
  intro h
  have h1 : HasBehavior 0 (link [] (link oneZeroMod const1Mod)) 1 0 (.val 1) := by decide
  exact absurd (h [] (by decide) (by decide) 0 1 0 (.val 1) h1) (by decide)

private def ipMod1 : Module := [(0, .lit 99)]
private def ipMod2 : Module := [(0, .lit 10), (1, .call 0 .var), (2, .lit 10)]
private def ipMod2' : Module := [(0, .lit 10), (1, .call 2 .var), (2, .lit 10)]

private theorem ip_eval_eq (C : Module) (hC₁ : Linkable C ipMod2) :
    ∀ f e a, eval f (link C ipMod2) e a = eval f (link C ipMod2') e a := by
    have hc0 : ¬ C.Defines 0 := fun hc => hC₁ 0 ⟨hc, by decide⟩
    have hc2 : ¬ C.Defines 2 := fun hc => hC₁ 2 ⟨hc, by decide⟩
    have hL : ∀ fn, (link C ipMod2).lookup fn =
        if fn = 0 then some (.lit 10)
        else if fn = 1 then some (.call 0 .var)
        else if fn = 2 then some (.lit 10)
        else C.lookup fn := by
      intro fn; rw [lookup_link]
      by_cases hf0 : fn = 0
      · subst hf0; rw [lookup_none_of_not_defines hc0]; rfl
      · by_cases hf1 : fn = 1
        · subst hf1
          have hc1 : ¬ C.Defines 1 := fun hc => hC₁ 1 ⟨hc, by decide⟩
          rw [lookup_none_of_not_defines hc1]
          simp [ipMod2, Module.lookup]
        · by_cases hf2 : fn = 2
          · subst hf2; rw [lookup_none_of_not_defines hc2]
            simp [ipMod2, Module.lookup]
          · cases C.lookup fn <;>
              simp [ipMod2, Module.lookup, hf0, hf1, hf2, Ne.symm hf0, Ne.symm hf1, Ne.symm hf2]
    have hR : ∀ fn, (link C ipMod2').lookup fn =
        if fn = 0 then some (.lit 10)
        else if fn = 1 then some (.call 2 .var)
        else if fn = 2 then some (.lit 10)
        else C.lookup fn := by
      intro fn; rw [lookup_link]
      by_cases hf0 : fn = 0
      · subst hf0; rw [lookup_none_of_not_defines hc0]; rfl
      · by_cases hf1 : fn = 1
        · subst hf1
          have hc1 : ¬ C.Defines 1 := fun hc => hC₁ 1 ⟨hc, by decide⟩
          rw [lookup_none_of_not_defines hc1]
          simp [ipMod2', Module.lookup]
        · by_cases hf2 : fn = 2
          · subst hf2; rw [lookup_none_of_not_defines hc2]
            simp [ipMod2', Module.lookup]
          · cases C.lookup fn <;>
              simp [ipMod2', Module.lookup, hf0, hf1, hf2, Ne.symm hf0, Ne.symm hf1, Ne.symm hf2]
    clear hC₁ hc0 hc2
    intro f
    induction f with
    | zero => intro e a; rfl
    | succ n ih =>
      intro e a
      simp only [eval, hL e, hR e]
      by_cases he0 : e = 0
      · subst he0; simp [evalExprWith]
      · by_cases he1 : e = 1
        · subst he1
          simp only [ite_true]
          cases n with
          | zero => rfl
          | succ m =>
            have h0 : eval (m + 1) (link C ipMod2) 0 a = [.val 10] := by
              simp [eval, hL 0, evalExprWith]
            have h2 : eval (m + 1) (link C ipMod2') 2 a = [.val 10] := by
              simp [eval, hR 2, evalExprWith]
            simp [evalExprWith, h0, h2]
        · by_cases he2 : e = 2
          · subst he2; simp [evalExprWith]
          · simp only [he0, he1, he2, ite_false]
            cases C.lookup e with
            | none => rfl
            | some body => exact evalExprWith_congr ih a body

private theorem ip_ctxRefines : CtxRefines ipMod2 ipMod2' ∧ CtxRefines ipMod2' ipMod2 := by
  constructor
  · intro C hC₁ _ entry fuel arg out hOut
    simpa [HasBehavior, ip_eval_eq C hC₁] using hOut
  · intro C _ hC₂ entry fuel arg out hOut
    simpa [HasBehavior, ip_eval_eq C hC₂] using hOut

/-- Dropping `Linkable M₁ M₂` from `ctxRefines_link_congr` fails via symbol interposition:
`ipMod2` and `ipMod2'` are contextually equivalent under all contexts disjoint from them
(none can redefine `0` or `2`), yet the overlapping `ipMod1` shadows `0` with `99`. -/
theorem cex_link_congr_without_linkable :
    CtxRefines ipMod1 ipMod1 ∧
    CtxRefines ipMod2 ipMod2' ∧
    ¬ Linkable ipMod1 ipMod2 ∧
    ¬ CtxRefines (link ipMod1 ipMod2) (link ipMod1 ipMod2') := by
  refine ⟨ctxRefines_refl ipMod1, ip_ctxRefines.1, by decide, ?_⟩
  intro h
  have h10 : HasBehavior 1 (link [] (link ipMod1 ipMod2')) 2 0 (.val 10) := by decide
  exact absurd (h [] (by decide) (by decide) 1 2 0 (.val 10) h10) (by decide)

/-- An overlapping context that redefines `0` as a self-loop. -/
private def ipLoopCtx : Module := [(0, .call 0 .var)]

private theorem ipLoop_mayDiverge : ∀ fuel, HasBehavior 0 (link ipLoopCtx ipMod2) fuel 0 .outOfFuel := by
  intro fuel
  induction fuel with
  | zero => simp [HasBehavior, eval]
  | succ n ih =>
    simpa [HasBehavior, eval, link, ipLoopCtx, ipMod2, Module.lookup, evalExprWith] using ih

/-- Tightness of `Linkable C M` in `ctxRefines_reflects_mayDiverge`: `ipMod2` contextually
refines `ipMod2'` (`CtxRefines ipMod2' ipMod2`; they are contextually equivalent), but under
the overlapping context `ipLoopCtx`, which shadows `0` by a self-loop, entry `1` may
diverge in `link ipLoopCtx ipMod2` (it calls `0`) and not in `link ipLoopCtx ipMod2'`
(it calls `2`). -/
theorem cex_reflects_mayDiverge_without_linkable :
    CtxRefines ipMod2' ipMod2 ∧
    ¬ Linkable ipLoopCtx ipMod2' ∧
    MayDiverge (link ipLoopCtx ipMod2) 1 0 ∧
    ¬ MayDiverge (link ipLoopCtx ipMod2') 1 0 := by
  refine ⟨ip_ctxRefines.2, by decide, ?_, fun h => absurd (h 2) (by decide)⟩
  intro fuel
  cases fuel with
  | zero => simp [HasBehavior, eval]
  | succ n =>
    simpa [HasBehavior, eval, link, ipLoopCtx, ipMod2, Module.lookup, evalExprWith] using
      ipLoop_mayDiverge n

/-- The pass that rewrites exactly `ipMod2` to the contextually equivalent `ipMod2'`. -/
private def ipPass (M : Module) : Module := if M = ipMod2 then ipMod2' else M

/-- Tightness of `Linkable M₁ M₂` in `separate_compilation_ctxRefines_of_pass_ctxRefines`:
`ipPass` is a contextual refinement on every module, but compiling the overlapping
`ipMod1` and `ipMod2` separately and linking does not refine the source link. -/
theorem cex_sep_comp_ctx_without_linkable :
    PassCtxRefines ipPass ∧
    ¬ Linkable ipMod1 ipMod2 ∧
    ¬ CtxRefines (link ipMod1 ipMod2) (link (ipPass ipMod1) (ipPass ipMod2)) := by
  refine ⟨?_, by decide, ?_⟩
  · intro M
    by_cases hM : M = ipMod2
    · subst hM; rw [show ipPass ipMod2 = ipMod2' by simp [ipPass]]; exact ip_ctxRefines.1
    · rw [show ipPass M = M by simp [ipPass, hM]]; exact ctxRefines_refl M
  · rw [show ipPass ipMod1 = ipMod1 by decide, show ipPass ipMod2 = ipMod2' by simp [ipPass]]
    exact cex_link_congr_without_linkable.2.2.2

/-! ## Canonical tightness counterexamples for `ag_partial_correctness` -/

private def twoZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

theorem cex_ag_partial_without_specsImplemented :
    ¬ SpecsImplemented openCallerMod twoZeroSpec ∧
    ModuleVerifiedPartial openCallerMod twoZeroSpec twoZeroSpec ∧
    ¬ ProgramPartialCorrect openCallerMod twoZeroSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd (h 1 0 (by simp [twoZeroSpec])) (by decide)
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [openCallerMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpPartial, twoZeroSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      exact ⟨trivial, fun vRes hv => hv⟩
    · simp [openCallerMod, Module.lookup, Ne.symm h0] at hlu
  · intro hSat
    have hBeh : HasBehavior 0 openCallerMod 2 0 .undefinedCall := by decide
    rcases hSat 0 2 0 .undefinedCall trivial hBeh with h1 | ⟨_, h2, _⟩
    · cases h1
    · cases h2

theorem cex_ag_partial_without_moduleVerified :
    SpecsImplemented const1Mod zeroOutSpec ∧
    ¬ ModuleVerifiedPartial const1Mod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramPartialCorrect const1Mod zeroOutSpec := by
  refine ⟨?_, ?_, programPartialCorrect_neg⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zeroOutSpec, h0] at hpre
  · intro hVer
    have h0 := hVer 0 (.lit 1) rfl 0 trivial
    simp [wpPartial, zeroOutSpec] at h0

/-! ## Canonical tightness counterexamples for `ag_total_correctness_of_wf_call_measure` -/

theorem cex_ag_total_without_wf :
    ¬ WellFounded (fun _ _ : Unit => True) ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ModuleVerifiedTotal (fun _ _ : Unit => True) (fun _ _ => ()) selfLoopMod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec := by
  refine ⟨?_, ?_, ?_, fun h => selfLoop_not_total_zeroOut (h 0)⟩
  · intro hwf
    have : ∀ u : Unit, Acc (fun _ _ : Unit => True) u → False := by
      intro u ha
      induction ha with
      | intro _ _ ih => exact ih () trivial
    exact this () (hwf.apply ())
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zeroOutSpec, h0] at hpre
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [selfLoopMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpCallDec, zeroOutSpec, ite_true]
      exact ⟨trivial, trivial, fun vRes hv => hv⟩
    · simp [selfLoopMod, Module.lookup, Ne.symm h0] at hlu

theorem cex_ag_total_without_specsImplemented :
    WellFounded Nat.lt ∧
    ¬ SpecsImplemented openCallerMod twoZeroSpec ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 0 then 1 else 0)
      openCallerMod twoZeroSpec twoZeroSpec ∧
    ¬ ProgramTotalCorrect openCallerMod twoZeroSpec := by
  refine ⟨Nat.lt_wfRel.wf, ?_, ?_, ?_⟩
  · intro h
    exact absurd (h 1 0 (by simp [twoZeroSpec])) (by decide)
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [openCallerMod, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpCallDec, twoZeroSpec, show ¬ ((1 : Nat) = 0) by decide, ite_false, ite_true]
      exact ⟨Nat.zero_lt_one, trivial, fun vRes hv => hv⟩
    · simp [openCallerMod, Module.lookup, Ne.symm h0] at hlu
  · intro hTot
    obtain ⟨fuel, hTot0⟩ := hTot 0 0 trivial
    cases fuel with
    | zero =>
      rcases hTot0 .outOfFuel (by decide) with ⟨_, h1, _⟩
      cases h1
    | succ m =>
      cases m with
      | zero =>
        rcases hTot0 .outOfFuel (by decide) with ⟨_, h1, _⟩
        cases h1
      | succ k =>
        have hUndef : HasBehavior 0 openCallerMod (k + 2) 0 .undefinedCall := by
          simp [HasBehavior, eval, openCallerMod, Module.lookup, evalExprWith]
        rcases hTot0 .undefinedCall hUndef with ⟨_, h1, _⟩
        cases h1

theorem cex_ag_total_without_moduleVerifiedTotal :
    WellFounded Nat.lt ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ¬ ModuleVerifiedTotal Nat.lt (fun _ _ => 0) selfLoopMod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec := by
  refine ⟨Nat.lt_wfRel.wf, ?_, ?_, fun h => selfLoop_not_total_zeroOut (h 0)⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zeroOutSpec, h0] at hpre
  · intro hVer
    have h0 := hVer 0 (.call 0 .var) rfl 0 trivial
    simp only [wpCallDec, zeroOutSpec, ite_true] at h0
    exact Nat.lt_irrefl 0 h0.1

/-! ## Canonical tightness counterexamples for `verified_recursive_caller_links_with_refined_callee` -/

private def tenZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

private def tenOneSpec : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

private def lkCaller : Module := [(0, .call 1 .var), (2, .lit 7)]
private def lkCallee : Module := [(1, .call 2 .var), (2, .lit 10)]
private def lkGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else if fn = 2 then { pre := fun _ => True, post := fun _ v => v = 7 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def badCaller : Module := [(0, .lit 999)]
private def goodCallee : Module := [(1, .lit 10)]
private def badCallee : Module := [(1, .lit 999)]

private theorem goodCallee_correct : ProgramPartialCorrect goodCallee tenOneSpec := by
  intro fn fuel x out hpre hbeh
  by_cases h1 : fn = 1
  · subst h1
    cases fuel with
    | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
    | succ n =>
      simp only [HasBehavior, eval, goodCallee, Module.lookup, ite_true, evalExprWith,
        List.mem_singleton] at hbeh
      subst hbeh
      exact .inr ⟨10, rfl, by simp [tenOneSpec]⟩
  · simp [tenOneSpec, h1] at hpre

private theorem openCaller_verified_tenOne :
    ModuleVerifiedPartial openCallerMod (mixEnv openCallerMod tenZeroSpec tenOneSpec)
      tenZeroSpec := by
  intro fn body hlu x _
  by_cases h0 : fn = 0
  · subst h0
    simp only [openCallerMod, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    have hA1 : mixEnv openCallerMod tenZeroSpec tenOneSpec 1 = tenOneSpec 1 := by
      simp [mixEnv, (by decide : ¬ openCallerMod.Defines 1)]
    simp only [wpPartial, hA1]
    simp [tenOneSpec, tenZeroSpec]
  · simp [openCallerMod, Module.lookup, Ne.symm h0] at hlu

/-- Dropping `Linkable M N`: the callee's internal call to `2` is captured by the caller's
own definition of `2` (symbol interposition), although each module is verified. -/
theorem cex_spec_refinement_without_linkable :
    ¬ Linkable lkCaller lkCallee ∧
    ModuleVerifiedPartial lkCaller (mixEnv lkCaller lkGuar tenOneSpec) lkGuar ∧
    ProgramPartialCorrect lkCallee tenOneSpec ∧
    (∀ g, ¬ lkCaller.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ lkCaller.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, lkCaller.Defines f → FnPartialCorrect (link lkCaller lkCallee) f (lkGuar f)) := by
  refine ⟨by decide, ?_, ?_, fun _ _ _ h => h, fun _ _ _ _ _ h => h, ?_⟩
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [lkCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      have hA1 : mixEnv lkCaller lkGuar tenOneSpec 1 = tenOneSpec 1 := by
        simp [mixEnv, (by decide : ¬ lkCaller.Defines 1)]
      simp only [wpPartial, hA1]
      simp [tenOneSpec, lkGuar]
    · by_cases h2 : fn = 2
      · subst h2
        simp only [lkCaller, Module.lookup, show ¬ ((0 : Nat) = 2) by decide, ite_false,
          ite_true, Option.some.injEq] at hlu
        subst hlu
        simp [wpPartial, lkGuar]
      · simp [lkCaller, Module.lookup, Ne.symm h0, Ne.symm h2] at hlu
  · intro fn fuel x out hpre hbeh
    by_cases h1 : fn = 1
    · subst h1
      rcases fuel with _ | _ | n
      · exact .inl (by simpa [HasBehavior, eval] using hbeh)
      · exact .inl (by simpa [HasBehavior, eval, lkCallee, Module.lookup, evalExprWith] using hbeh)
      · simp [HasBehavior, eval, lkCallee, Module.lookup, evalExprWith] at hbeh
        subst hbeh
        exact .inr ⟨10, rfl, by simp [tenOneSpec]⟩
    · simp [tenOneSpec, h1] at hpre
  · intro h
    have hBeh : HasBehavior 0 (link lkCaller lkCallee) 3 0 (.val 7) := by decide
    rcases h 0 (by decide) 3 0 (.val 7) trivial hBeh with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [lkGuar] at hpost

theorem cex_spec_refinement_without_caller_verified :
    Linkable badCaller goodCallee ∧
    ¬ ModuleVerifiedPartial badCaller (mixEnv badCaller tenZeroSpec tenOneSpec) tenZeroSpec ∧
    ProgramPartialCorrect goodCallee tenOneSpec ∧
    (∀ g, ¬ badCaller.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ badCaller.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, badCaller.Defines f → FnPartialCorrect (link badCaller goodCallee) f (tenZeroSpec f)) := by
  refine ⟨by decide, ?_, goodCallee_correct, fun _ _ _ h => h, fun _ _ _ _ _ h => h, ?_⟩
  · intro hVer
    have h0 := hVer 0 (.lit 999) rfl 0 trivial
    simp [wpPartial, tenZeroSpec] at h0
  · intro h
    have hBeh : HasBehavior 0 (link badCaller goodCallee) 1 0 (.val 999) := by decide
    rcases h 0 (by decide) 1 0 (.val 999) trivial hBeh with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [tenZeroSpec] at hpost

theorem cex_spec_refinement_without_callee_correct :
    Linkable openCallerMod badCallee ∧
    ModuleVerifiedPartial openCallerMod (mixEnv openCallerMod tenZeroSpec tenOneSpec)
      tenZeroSpec ∧
    ¬ ProgramPartialCorrect badCallee tenOneSpec ∧
    (∀ g, ¬ openCallerMod.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ openCallerMod.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, openCallerMod.Defines f →
        FnPartialCorrect (link openCallerMod badCallee) f (tenZeroSpec f)) := by
  refine ⟨by decide, openCaller_verified_tenOne, ?_, fun _ _ _ h => h,
    fun _ _ _ _ _ h => h, ?_⟩
  · intro hSat
    rcases hSat 1 1 0 (.val 999) (by simp [tenOneSpec]) (by decide) with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [tenOneSpec] at hpost
  · intro h
    have hBeh : HasBehavior 0 (link openCallerMod badCallee) 2 0 (.val 999) := by decide
    rcases h 0 (by decide) 2 0 (.val 999) trivial hBeh with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [tenZeroSpec] at hpost

private def preZeroCallee : Module := [(1, .ifLe .var (.lit 9) (.lit 999) (.lit 10))]
private def weakPreAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def weakPreActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 10, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Dropping `WeakensPre` at external names: the callee only guarantees its result for
`x ≥ 10`, while the caller calls it with `0`. -/
theorem cex_spec_refinement_without_weakensPre :
    Linkable incCaller preZeroCallee ∧
    ModuleVerifiedPartial incCaller (mixEnv incCaller tenZeroSpec weakPreAssumed) tenZeroSpec ∧
    ProgramPartialCorrect preZeroCallee weakPreActual ∧
    ¬ (∀ g, ¬ incCaller.Defines g → WeakensPre (weakPreAssumed g) (weakPreActual g)) ∧
    (∀ g, ¬ incCaller.Defines g →
        StrengthensPostUnderPre (weakPreAssumed g) (weakPreActual g)) ∧
    ¬ (∀ f, incCaller.Defines f →
        FnPartialCorrect (link incCaller preZeroCallee) f (tenZeroSpec f)) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [incCaller, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      have hA1 : mixEnv incCaller tenZeroSpec weakPreAssumed 1 = weakPreAssumed 1 := by
        simp [mixEnv, (by decide : ¬ incCaller.Defines 1)]
      simp only [wpPartial, hA1]
      simp [weakPreAssumed, tenZeroSpec]
    · simp [incCaller, Module.lookup, Ne.symm h0] at hlu
  · intro fn fuel x out hpre hbeh
    by_cases h1 : fn = 1
    · subst h1
      simp only [weakPreActual, ite_true] at hpre
      cases fuel with
      | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
      | succ n =>
        have hNotLe : ¬ x ≤ 9 := by omega
        simp only [HasBehavior, eval, preZeroCallee, Module.lookup, ite_true, evalExprWith,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, hNotLe, ite_false,
          List.mem_singleton] at hbeh
        subst hbeh
        exact .inr ⟨10, rfl, by simp [weakPreActual]⟩
    · simp [weakPreActual, h1] at hpre
  · intro h
    have h10 : (weakPreActual 1).pre 0 := h 1 (by decide) 0 (by simp [weakPreAssumed])
    simp [weakPreActual] at h10
  · intro g _ x v hx hv
    by_cases h1 : g = 1
    · subst h1; simpa [weakPreAssumed, weakPreActual] using hv
    · simp [weakPreAssumed, h1] at hx
  · intro h
    have hBeh : HasBehavior 0 (link incCaller preZeroCallee) 2 0 (.val 999) := by decide
    rcases h 0 (by decide) 2 0 (.val 999) trivial hBeh with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [tenZeroSpec] at hpost

private def trivOneSpec : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ _ => True }
  else { pre := fun _ => False, post := fun _ _ => False }

/-- Dropping `StrengthensPostUnderPre` at external names: the callee only guarantees a
trivial postcondition. -/
theorem cex_spec_refinement_without_strengthensPost :
    Linkable openCallerMod badCallee ∧
    ModuleVerifiedPartial openCallerMod (mixEnv openCallerMod tenZeroSpec tenOneSpec)
      tenZeroSpec ∧
    ProgramPartialCorrect badCallee trivOneSpec ∧
    (∀ g, ¬ openCallerMod.Defines g → WeakensPre (tenOneSpec g) (trivOneSpec g)) ∧
    ¬ (∀ g, ¬ openCallerMod.Defines g →
        StrengthensPostUnderPre (tenOneSpec g) (trivOneSpec g)) ∧
    ¬ (∀ f, openCallerMod.Defines f →
        FnPartialCorrect (link openCallerMod badCallee) f (tenZeroSpec f)) := by
  refine ⟨by decide, openCaller_verified_tenOne, ?_, ?_, ?_, ?_⟩
  · intro fn fuel x out hpre hbeh
    by_cases h1 : fn = 1
    · subst h1
      cases fuel with
      | zero => exact .inl (by simpa [HasBehavior, eval] using hbeh)
      | succ n =>
        simp only [HasBehavior, eval, badCallee, Module.lookup, ite_true, evalExprWith,
          List.mem_singleton] at hbeh
        subst hbeh
        exact .inr ⟨999, rfl, by simp [trivOneSpec]⟩
    · simp [trivOneSpec, h1] at hpre
  · intro g _ x hx
    by_cases h1 : g = 1
    · subst h1; simp [trivOneSpec]
    · simp [tenOneSpec, h1] at hx
  · intro h
    have h10 : (tenOneSpec 1).post 0 0 :=
      h 1 (by decide) 0 0 (by simp [tenOneSpec]) (by simp [trivOneSpec])
    simp [tenOneSpec] at h10
  · intro h
    have hBeh : HasBehavior 0 (link openCallerMod badCallee) 2 0 (.val 999) := by decide
    rcases h 0 (by decide) 2 0 (.val 999) trivial hBeh with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [tenZeroSpec] at hpost

/-- The flat variant `verified_flat_caller_links_with_refined_callee` can never be applied
to the recursive caller `recCaller` with guarantee `recGuar`, for any library `N` and specs
`S`, `S'`: its hypotheses force `(S 0).pre` to be unsatisfiable, while verifying the
recursive call requires `(S 0).pre 0`. -/
theorem flat_spec_refinement_inapplicable_to_recursive_caller :
    ∀ (N : Module) (S S' : SpecEnv),
      ¬ (Linkable recCaller N ∧ ModuleVerifiedPartial recCaller S recGuar ∧
         ProgramPartialCorrect N S' ∧ (∀ g, WeakensPre (S g) (S' g))) := by
  rintro N S S' ⟨hLink, hVer, hSat, hWeak⟩
  have hUnsat := caller_spec_unsat_on_own_symbols hLink hSat hWeak 0 (by decide)
  have hw := hVer 0 _ rfl 1 (by simp [recGuar])
  simp only [wpPartial] at hw
  exact hUnsat _ (hw.2 (by decide)).1

/-! ## Canonical tightness counterexamples for `separate_compilation_partial_correct_of_preserves_verified` -/

private def scZero : Module := [(0, .lit 0)]
private def scOne : Module := [(1, .lit 0)]
private def scZeroBad : Module := [(0, .lit 1)]
private def scOneBad : Module := [(1, .lit 1)]
private def scZeroCalls2 : Module := [(0, .call 2 .var)]

private theorem scZero_ver : ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec := by
  intro fn body hlu x _
  by_cases h0 : fn = 0
  · subst h0
    simp only [scZero, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp [wpPartial, twoZeroSpec]
  · simp [scZero, Module.lookup, Ne.symm h0] at hlu

private theorem scOne_ver : ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec := by
  intro fn body hlu x _
  by_cases h1 : fn = 1
  · subst h1
    simp only [scOne, Module.lookup, ite_true, Option.some.injEq] at hlu
    subst hlu
    simp [wpPartial, twoZeroSpec]
  · simp [scOne, Module.lookup, Ne.symm h1] at hlu

theorem cex_sep_comp_without_first_verified :
    ¬ ModuleVerifiedPartial scZeroBad twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZeroBad scOne) twoZeroSpec ∧
    PreservesVerifiedPartial id twoZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZeroBad) (id scOne)) twoZeroSpec := by
  refine ⟨?_, scOne_ver, ?_, fun _ h => h, fun _ _ h => h, ?_⟩
  · intro hVer
    have h0 := hVer 0 (.lit 1) rfl 0 trivial
    simp [wpPartial, twoZeroSpec] at h0
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [twoZeroSpec, h0, h1] at hpre
  · intro hSat
    rcases hSat 0 1 0 (.val 1) trivial (by decide) with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [twoZeroSpec] at hpost

theorem cex_sep_comp_without_second_verified :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ¬ ModuleVerifiedPartial scOneBad twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOneBad) twoZeroSpec ∧
    PreservesVerifiedPartial id twoZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZero) (id scOneBad)) twoZeroSpec := by
  refine ⟨scZero_ver, ?_, ?_, fun _ h => h, fun _ _ h => h, ?_⟩
  · intro hVer
    have h1 := hVer 1 (.lit 1) rfl 0 trivial
    simp [wpPartial, twoZeroSpec] at h1
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [twoZeroSpec, h0, h1] at hpre
  · intro hSat
    rcases hSat 1 1 0 (.val 1) (by simp [twoZeroSpec]) (by decide) with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [twoZeroSpec] at hpost

private def threeZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 2 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

theorem cex_sep_comp_without_specsImplemented :
    ModuleVerifiedPartial scZeroCalls2 threeZeroSpec threeZeroSpec ∧
    ModuleVerifiedPartial scOne threeZeroSpec threeZeroSpec ∧
    ¬ SpecsImplemented (link scZeroCalls2 scOne) threeZeroSpec ∧
    PreservesVerifiedPartial id threeZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZeroCalls2) (id scOne)) threeZeroSpec := by
  refine ⟨?_, ?_, ?_, fun _ h => h, fun _ _ h => h, ?_⟩
  · intro fn body hlu x _
    by_cases h0 : fn = 0
    · subst h0
      simp only [scZeroCalls2, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp only [wpPartial, threeZeroSpec, show ¬ ((2 : Nat) = 0) by decide,
        show ¬ ((2 : Nat) = 1) by decide, ite_false, ite_true]
      exact ⟨trivial, fun v hv => hv⟩
    · simp [scZeroCalls2, Module.lookup, Ne.symm h0] at hlu
  · intro fn body hlu x _
    by_cases h1 : fn = 1
    · subst h1
      simp only [scOne, Module.lookup, ite_true, Option.some.injEq] at hlu
      subst hlu
      simp [wpPartial, threeZeroSpec]
    · simp [scOne, Module.lookup, Ne.symm h1] at hlu
  · intro h
    exact absurd (h 2 0 (by simp [threeZeroSpec])) (by decide)
  · intro hSat
    have hUndef : HasBehavior 0 (link (id scZeroCalls2) (id scOne)) 2 0 .undefinedCall := by decide
    rcases hSat 0 2 0 .undefinedCall trivial hUndef with h1 | ⟨_, h2, _⟩
    · cases h1
    · cases h2

private def badBodyCompile (M : Module) : Module :=
  M.map fun (fn, _) => (fn, .lit 1)

private theorem badBodyCompile_preservesDefines : PreservesDefines badBodyCompile := by
  intro M fn hdef
  induction M with
  | nil => simp [Module.Defines, Module.lookup] at hdef
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [badBodyCompile, List.map_cons, Module.Defines, Module.lookup] at hdef ⊢
    by_cases hk : k = fn
    · simp [hk]
    · simp only [hk, ite_false] at hdef ⊢
      exact ih hdef

theorem cex_sep_comp_without_preservesVerified :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOne) twoZeroSpec ∧
    ¬ PreservesVerifiedPartial badBodyCompile twoZeroSpec ∧
    PreservesDefines badBodyCompile ∧
    ¬ ProgramPartialCorrect (link (badBodyCompile scZero) (badBodyCompile scOne)) twoZeroSpec := by
  refine ⟨scZero_ver, scOne_ver, ?_, ?_, badBodyCompile_preservesDefines, ?_⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [twoZeroSpec, h0, h1] at hpre
  · intro hPres
    have hVerBad := hPres scZero scZero_ver
    have h0 := hVerBad 0 (.lit 1) rfl 0 trivial
    simp [wpPartial, twoZeroSpec] at h0
  · intro hSat
    rcases hSat 0 1 0 (.val 1) trivial (by decide) with h1 | ⟨_, h2, hpost⟩
    · cases h1
    · cases h2
      simp [twoZeroSpec] at hpost

private def dropCompile (_ : Module) : Module := []

theorem cex_sep_comp_without_preservesDefines :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOne) twoZeroSpec ∧
    PreservesVerifiedPartial dropCompile twoZeroSpec ∧
    ¬ PreservesDefines dropCompile ∧
    ¬ ProgramPartialCorrect (link (dropCompile scZero) (dropCompile scOne)) twoZeroSpec := by
  refine ⟨scZero_ver, scOne_ver, ?_, ?_, preservesDefines_neg, ?_⟩
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · by_cases h1 : fn = 1
      · subst h1; decide
      · simp [twoZeroSpec, h0, h1] at hpre
  · intro M _ fn body hlu
    simp [dropCompile, Module.lookup] at hlu
  · intro hSat
    have hUndef : HasBehavior 0 (link (dropCompile scZero) (dropCompile scOne)) 1 0 .undefinedCall := by
      decide
    rcases hSat 0 1 0 .undefinedCall trivial hUndef with h1 | ⟨_, h2, _⟩
    · cases h1
    · cases h2

/-! ## Verifiability preservation is not behavioural refinement -/

/-- Interface: `0` returns a non-negative value; nothing else is specified. -/
def zSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 0 }
  else { pre := fun _ => False, post := fun _ _ => False }

private theorem lookup_zeroBodies (M : Module) (fn : Fname) :
    (zeroBodies M).lookup fn = (M.lookup fn).map (fun _ => Expr.lit 0) := by
  induction M with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [zeroBodies, List.map_cons, Module.lookup] at ih ⊢
    by_cases hk : k = fn
    · simp [hk]
    · simp only [hk, ite_false]; exact ih

/-- **Verifiability preservation does not imply behavioural refinement.** The pass
`zeroBodies` (replace every body by `lit 0`) preserves verification against `zSpec` and
keeps every name, and every hypothesis of
`separate_compilation_partial_correct_of_preserves_verified` holds for `const1Mod` and the
empty module; yet the compiled program returns `0` where the source returns `1`, so it
neither refines the source at entry `0` nor contextually. This pass is also the tightness
counterexample for `PassCtxRefines` in `separate_compilation_ctxRefines_of_pass_ctxRefines`
(the modules are disjoint and the conclusion fails). -/
theorem cex_verifiability_preservation_not_behavioural :
    PreservesVerifiedPartial zeroBodies zSpec ∧
    PreservesDefines zeroBodies ∧
    ModuleVerifiedPartial const1Mod zSpec zSpec ∧
    ModuleVerifiedPartial ([] : Module) zSpec zSpec ∧
    SpecsImplemented (link const1Mod []) zSpec ∧
    Linkable const1Mod [] ∧
    ¬ PassCtxRefines zeroBodies ∧
    ¬ EntryRefines 0 (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies [])) ∧
    ¬ CtxRefines (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies [])) := by
  have hNot : ¬ EntryRefines 0 (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies [])) := by
    intro h
    have ht : HasBehavior 0 (link (zeroBodies const1Mod) (zeroBodies [])) 1 0 (.val 0) := by
      decide
    exact absurd (h 1 0 _ ht) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide, passCtxRefines_neg, hNot,
    fun h => hNot (standaloneRefines_of_ctxRefines h 0)⟩
  · intro M _ fn body hlu x hpre
    rw [lookup_zeroBodies] at hlu
    cases hm : M.lookup fn with
    | none => simp [hm] at hlu
    | some b =>
      simp [hm] at hlu
      subst hlu
      by_cases h0 : fn = 0
      · subst h0; simp [wpPartial, zSpec]
      · simp [zSpec, h0] at hpre
  · intro M fn hdef
    simp only [Module.Defines, lookup_zeroBodies] at hdef ⊢
    cases hm : M.lookup fn <;> simp_all
  · intro fn body hlu x hpre
    by_cases h0 : fn = 0
    · subst h0
      simp [const1Mod, Module.lookup] at hlu
      subst hlu
      simp [wpPartial, zSpec]
    · simp [zSpec, h0] at hpre
  · intro fn body hlu
    simp [Module.lookup] at hlu
  · intro fn x hpre
    by_cases h0 : fn = 0
    · subst h0; decide
    · simp [zSpec, h0] at hpre

end Toy.Link.Cex
