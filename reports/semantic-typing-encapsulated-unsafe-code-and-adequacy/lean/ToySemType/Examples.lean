import ToySemType.Results

/-!
# Positive and negative examples for every definition

Each definition gets at least one intended instance it admits and one it
must reject, fully proved.
-/

namespace Toy.SemType

open Expr

/-! ### `Expr.isValue` -/
theorem isValue_pos : checkedRead.isValue = true ∧ (Expr.loc 3).isValue = true := ⟨rfl, rfl⟩
theorem isValue_neg : forgedRead.isValue = false ∧ (Expr.var 0).isValue = false := ⟨rfl, rfl⟩

/-! ### `Expr.closedAt` -/
theorem closedAt_pos : checkedRead.closedAt 0 = true ∧ (Expr.var 0).closedAt 1 = true :=
  ⟨rfl, rfl⟩
theorem closedAt_neg : (Expr.lam (.var 1)).closedAt 0 = false ∧ (Expr.var 0).closedAt 0 = false :=
  ⟨rfl, rfl⟩

/-! ### `Expr.castFree` -/
theorem castFree_pos : derefArg.castFree = true ∧ allocThenRead.castFree = true := ⟨rfl, rfl⟩
theorem castFree_neg : checkedRead.castFree = false ∧ forgedRead.castFree = false := ⟨rfl, rfl⟩

/-! ### Substitution (`substAllAt`, `substAll`, `substAt`) -/
/-- β-substitution replaces the bound index and leaves inner-bound indices alone. -/
theorem substAt_pos :
    substAt 0 (.num 3) (.read (.cast (.var 0))) = .read (.cast (.num 3)) ∧
    substAt 0 (.num 3) (.lam (.app (.var 0) (.var 1))) = .lam (.app (.var 0) (.num 3)) :=
  ⟨rfl, rfl⟩
/-- Substitution respects shadowing: an inner binder's own index `0` is not
replaced. (Substitution performs no shifting, so it is capture-free only for
closed substituends; see `substAt_open_captures`.) -/
theorem substAt_neg : substAt 0 (.num 3) (.lam (.var 0)) ≠ .lam (.num 3) := by decide
/-- Substituting an *open* term captures: the free `var 0` substituted under a
binder becomes bound. The semantic model only substitutes closed values. -/
theorem substAt_open_captures : substAt 0 (.var 0) (.lam (.var 1)) = .lam (.var 0) := rfl
theorem substAll_pos :
    substAll [.num 1, .num 2] (.lt (.var 0) (.var 1)) = .lt (.num 1) (.num 2) := rfl
/-- Indices beyond the substitution are renumbered down, not replaced. -/
theorem substAll_neg : substAll [.num 1] (.var 1) ≠ .num 1 ∧ substAll [.num 1] (.var 1) = .var 0 :=
  ⟨by decide, rfl⟩

/-! ### `step` -/
theorem step_pos :
    step (.alloc (.num 5)) [] = some (.loc 0, [5]) ∧
    step (.read (.loc 0)) [4] = some (.num 4, [4]) ∧
    step (.cast (.num 9)) [] = some (.loc 9, []) := ⟨rfl, rfl, rfl⟩
/-- Reads and writes through invalid references do not step; neither do values. -/
theorem step_neg :
    step (.read (.loc 0)) [] = none ∧ step (.write (.loc 1) (.num 0)) [4] = none ∧
    step (.num 0) [] = none := ⟨rfl, rfl, rfl⟩

/-! ### `Reaches` -/
theorem reaches_pos : Reaches (allocThenRead, []) (.num 5, [5]) := by reach
theorem reaches_neg : ¬ Reaches (.num 0, []) (.num 1, []) := by
  intro h
  have := reaches_of_isValue rfl h
  simp at this

/-! ### `Stuck` -/
theorem stuck_pos : Stuck (.read (.loc 0), []) ∧ Stuck (.app (.num 0) (.num 0), []) ∧
    Stuck (.var 0, []) := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
theorem stuck_neg : ¬ Stuck (.read (.loc 0), [4]) ∧ ¬ Stuck (.num 0, []) :=
  ⟨not_stuck_of_step (c' := (.num 4, [4])) rfl, not_stuck_of_isValue rfl⟩

/-! ### `Safe` -/
theorem safe_pos : Safe (allocThenRead, []) := by
  refine safe_of_step (c' := (.app derefArg (.loc 0), [5])) rfl ?_
  refine safe_of_step (c' := (.read (.loc 0), [5])) rfl ?_
  exact safe_of_step (c' := (.num 5, [5])) rfl (safe_of_isValue rfl)
theorem safe_neg : ¬ Safe (forgedRead, []) := forgedRead_unsafe_ill_typed.2.2

/-! ### `HasType` -/
theorem hasType_pos :
    HasType [] derefArg (.arrow .ref .int) ∧ HasType [] allocThenRead .int ∧
    HasType [.ref] (.write (.var 0) (.ifz .size (.num 1) (.num 2))) .int :=
  ⟨.lam (.read (.var rfl)), fundamental_nonvacuous.1,
    .write (.var rfl) (.ifz .size .num .num)⟩
/-- The type system rejects safe-fragment type errors as well as every use of `cast`
and every runtime reference literal. -/
theorem hasType_neg :
    (∀ τ, ¬ HasType [] (.app (.num 0) (.num 0)) τ) ∧ (∀ Γ τ, ¬ HasType Γ forgedRead τ) ∧
    (∀ Γ τ, ¬ HasType Γ (.loc 0) τ) := by
  refine ⟨fun τ h => ?_, forgedRead_unsafe_ill_typed.1, fun Γ τ h => (nomatch h)⟩
  cases h with
  | app hf _ => nomatch hf

/-! ### `safeAndIn` -/
theorem safeAndIn_pos : safeAndIn (V Recipe.std .int) 0 allocThenRead := by
  intro h _
  refine goodFrom_step (e₁ := .app derefArg (.loc h.length)) (h₁ := h ++ [5]) rfl ?_
  refine goodFrom_step (e₁ := .read (.loc h.length)) (h₁ := h ++ [5]) rfl ?_
  refine goodFrom_step (e₁ := .num 5) (h₁ := h ++ [5]) (by simp [step, Expr.isValue]) ?_
  exact goodFrom_value rfl ⟨5, rfl⟩
/-- `safeAndIn` rejects unsafe expressions, and also safe expressions whose
result is outside the value predicate (`cast 7` at `ref` from the empty heap). -/
theorem safeAndIn_neg :
    ¬ safeAndIn (V Recipe.std .int) 0 forgedRead ∧ ¬ safeAndIn (V Recipe.std .ref) 0 (.cast (.num 7)) := by
  refine ⟨not_safeAndIn_of_reaches_stuck (h := []) (Nat.le_refl _)
    forgedRead_reaches_stuck.1 forgedRead_reaches_stuck.2, fun hs => ?_⟩
  obtain ⟨l, hl, hlt⟩ := (hs [] (Nat.le_refl _) (.loc 7) [] (by reach)).2 rfl
  cases hl
  exact Nat.not_lt_zero _ hlt

/-! ### `V` (standard recipe) -/
theorem V_std_pos :
    V Recipe.std .ref 1 (.loc 0) ∧ V Recipe.std (.arrow .ref .int) 0 derefArg ∧
    V Recipe.std (.arrow .int .int) 0 checkedRead :=
  ⟨V_std_mono_nonvacuous.1.2, V_std_mono_nonvacuous.2.2, checkedRead_V 0⟩
theorem V_std_neg :
    ¬ V Recipe.std .ref 1 (.loc 1) ∧ ¬ V Recipe.std .int 0 (.loc 0) ∧
    ¬ V Recipe.std (.arrow .int .int) 0 uncheckedRead := by
  refine ⟨fun ⟨l, hl, hlt⟩ => ?_, fun ⟨n, hn⟩ => (nomatch hn), fun hV => ?_⟩
  · cases hl; exact Nat.lt_irrefl _ hlt
  · obtain ⟨b, hb, _, hf⟩ := hV
    simp only [uncheckedRead, Expr.lam.injEq] at hb
    subst hb
    exact not_safeAndIn_of_reaches_stuck (h := []) (d := (.read (.loc 7), []))
      (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hf 0 (Nat.le_refl 0) (.num 7) ⟨7, rfl⟩)

/-! ### `E` (standard recipe) -/
theorem E_std_pos : E Recipe.std .int 0 (.app checkedRead (.num 0)) :=
  semTyped_nil_iff.mp adequacy_nonvacuous 0
theorem E_std_neg : ¬ E Recipe.std .int 0 forgedRead :=
  not_safeAndIn_of_reaches_stuck (h := []) (Nat.le_refl _)
    forgedRead_reaches_stuck.1 forgedRead_reaches_stuck.2

/-! ### `G` -/
theorem G_pos : G Recipe.std [.ref, .int] 1 [.loc 0, .num 3] :=
  ⟨⟨0, rfl, Nat.zero_lt_one⟩, ⟨3, rfl⟩, trivial⟩
theorem G_neg :
    ¬ G Recipe.std [.ref] 1 [.loc 1] ∧ ¬ G Recipe.std [.int] 0 [] ∧
    ¬ G Recipe.std [] 0 [.num 0] := by
  refine ⟨fun ⟨⟨l, hl, hlt⟩, _⟩ => ?_, fun h => (nomatch h), fun h => (nomatch h)⟩
  cases hl; exact Nat.lt_irrefl _ hlt

/-! ### `SemTyped` (standard recipe) -/
theorem semTyped_pos :
    SemTyped Recipe.std [] checkedRead (.arrow .int .int) ∧
    SemTyped Recipe.std [.arrow .int .int] callWith7 .int :=
  ⟨checkedRead_semTyped, callWith7_semTyped⟩
theorem semTyped_neg :
    ¬ SemTyped Recipe.std [] uncheckedRead (.arrow .int .int) ∧
    ¬ SemTyped Recipe.std [.int] (.cast (.var 0)) .ref :=
  ⟨fundamental_hasType_hyp_tight.2, cast_of_int_var_not_semTyped .ref⟩

/-! ### `safeOnly` and `Recipe.safetyOnly` -/
theorem safeOnly_pos (P : Nat → Expr → Prop) : safeOnly P 0 (.cast (.num 7)) := by
  intro h _
  exact safe_of_step (c' := (.loc 7, h)) rfl (safe_of_isValue rfl)
theorem safeOnly_neg (P : Nat → Expr → Prop) : ¬ safeOnly P 0 forgedRead :=
  not_safeOnly_of_reaches_stuck (h := []) (Nat.le_refl _)
    forgedRead_reaches_stuck.1 forgedRead_reaches_stuck.2
/-- Under the safety-only recipe even `checkedRead` (which returns words) is
accepted at `int ⇒ ref`; the unguarded library is still rejected. -/
theorem safetyOnly_pos :
    V Recipe.safetyOnly (.arrow .int .ref) 0 castSeven ∧
    V Recipe.safetyOnly (.arrow .int .ref) 0 checkedRead := by
  refine ⟨castSeven_V_safetyOnly 0, ⟨_, rfl, rfl, fun W' _ v hv => ?_⟩⟩
  obtain ⟨n, rfl⟩ := hv
  intro h _ d hr
  exact (checkedBody_good n h d.1 d.2 hr).1
theorem safetyOnly_neg : ¬ V Recipe.safetyOnly (.arrow .int .int) 0 uncheckedRead := by
  intro hV
  obtain ⟨b, hb, _, hf⟩ := hV
  simp only [uncheckedRead, Expr.lam.injEq] at hb
  subst hb
  exact not_safeOnly_of_reaches_stuck (P := V Recipe.safetyOnly .int) (h := []) (d := (.read (.loc 7), []))
    (Nat.le_refl _) (by reach) ⟨rfl, rfl⟩ (hf 0 (Nat.le_refl 0) (.num 7) ⟨7, rfl⟩)

/-! ### `valuesIn` and `Recipe.valuesOnly` -/
theorem valuesIn_pos : valuesIn (V Recipe.std .int) 0 forgedRead :=
  (semTyped_nil_iff.mp valuesOnly_adequacy_fails.1 0)
theorem valuesIn_neg : ¬ valuesIn (V Recipe.std .ref) 0 (.cast (.num 7)) := by
  intro hs
  obtain ⟨l, hl, hlt⟩ := hs [] (Nat.le_refl _) (.loc 7) [] (by reach) rfl
  cases hl
  exact Nat.not_lt_zero _ hlt
/-- Under the values-only recipe the unguarded library is accepted at `int ⇒ int`. -/
theorem valuesOnly_pos : V Recipe.valuesOnly (.arrow .int .int) 0 uncheckedRead := by
  refine ⟨_, rfl, rfl, fun W' _ v hv => ?_⟩
  obtain ⟨n, rfl⟩ := hv
  intro h _
  refine valFrom_step (e₁ := .read (.loc n)) (h₁ := h) rfl ?_
  by_cases hn : n < h.length
  · refine valFrom_step (e₁ := .num h[n]) (h₁ := h)
      (by simp [step, Expr.isValue, List.getElem?_eq_getElem hn]) ?_
    intro e' h' hr _
    have := reaches_of_isValue rfl hr
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨_, rfl⟩
  · exact valFrom_stuck ⟨rfl, by
      simp [step, Expr.isValue, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hn)]⟩
/-- The values-only recipe still constrains result values: `checkedRead`
(which returns words) is rejected at `int ⇒ ref`. -/
theorem valuesOnly_neg : ¬ V Recipe.valuesOnly (.arrow .int .ref) 0 checkedRead := by
  intro hV
  obtain ⟨b, hb, _, hf⟩ := hV
  simp only [checkedRead, Expr.lam.injEq] at hb
  subst hb
  have := hf 0 (Nat.le_refl 0) (.num 0) ⟨0, rfl⟩ [] (Nat.le_refl _) (.num 0) [] (by reach) rfl
  obtain ⟨l, hl, _⟩ := this
  cases hl

/-! ### `Recipe.nonKripke` -/
theorem nonKripke_pos : V Recipe.nonKripke (.arrow .ref .int) 1 probeCellZero :=
  probeCellZero_V_nonKripke_one
theorem nonKripke_neg : ¬ V Recipe.nonKripke (.arrow .ref .int) 2 probeCellZero :=
  nonKripke_breaks_monotonicity_and_fundamental.2.1

/-! ### `Recipe.anyLoc` -/
theorem anyLoc_pos : V Recipe.anyLoc .ref 0 (.loc 5) := ⟨5, rfl, trivial⟩
theorem anyLoc_neg : ¬ V Recipe.anyLoc .ref 0 (.num 5) := fun ⟨_, h, _⟩ => nomatch h

/-! ### `Recipe.std` -/
/-- The standard recipe accepts exactly allocated addresses as references. -/
theorem std_pos : Recipe.std.refOK 1 0 ∧ Recipe.std.future 1 2 :=
  ⟨Nat.zero_lt_one, Nat.le_succ 1⟩
theorem std_neg : ¬ Recipe.std.refOK 1 1 ∧ ¬ Recipe.std.future 2 1 :=
  ⟨Nat.lt_irrefl 1, show ¬ (2 ≤ 1) by decide⟩

/-! ### `HasTypeStore` -/
/-- Store typing admits runtime references to allocated cells, inside closures too. -/
theorem hasTypeStore_pos :
    HasTypeStore 1 [] (.loc 0) .ref ∧ HasTypeStore 1 [] capturedClosure (.arrow .int .int) ∧
    HasTypeStore 0 [] derefArg (.arrow .ref .int) :=
  ⟨.loc Nat.zero_lt_one, .lam (.read (.loc Nat.zero_lt_one)), .lam (.read (.var rfl))⟩
/-- Store typing rejects references to unallocated cells and every use of `cast`. -/
theorem hasTypeStore_neg :
    ¬ HasTypeStore 1 [] (.loc 1) .ref ∧ (∀ W Γ τ, ¬ HasTypeStore W Γ checkedRead τ) := by
  refine ⟨fun h => ?_, fun W Γ τ h => ?_⟩
  · cases h with
    | loc hl => exact Nat.lt_irrefl _ hl
  · have := h.castFree
    simp [checkedRead, Expr.castFree] at this

/-! ### `SynVal` -/
/-- `SynVal` admits syntactically typed values, including the runtime closure
`λ _. read (loc 0)` (which captures an allocated reference) in world 1. -/
theorem synVal_pos :
    SynVal (.arrow .ref .int) 0 derefArg ∧ SynVal .ref 1 (.loc 0) ∧
    SynVal (.arrow .int .int) 1 capturedClosure :=
  ⟨⟨rfl, .lam (.read (.var rfl))⟩, ⟨0, rfl, Nat.zero_lt_one⟩,
    ⟨rfl, .lam (.read (.loc Nat.zero_lt_one))⟩⟩
/-- `SynVal` rejects `checkedRead` (it uses `cast`) and the closure capturing
`loc 0` in world 0 (cell 0 is not allocated there). -/
theorem synVal_neg :
    ¬ SynVal (.arrow .int .int) 0 checkedRead ∧ ¬ SynVal (.arrow .int .int) 0 capturedClosure := by
  refine ⟨synVal_rejects_checkedRead.2.1 _ _, fun ⟨_, h⟩ => ?_⟩
  cases h with
  | lam hb =>
    cases hb with
    | read ha =>
      cases ha with
      | loc hl => exact Nat.not_lt_zero _ hl

/-! ### `Recipe.ClosureEnforcesValues` -/
theorem closureEnforcesValues_pos :
    Recipe.std.ClosureEnforcesValues ∧ Recipe.nonKripke.ClosureEnforcesValues :=
  ⟨std_closureEnforcesValues, fun _ _ _ h => valuesIn_of_safeAndIn h⟩
/-- The safety-only closure does not enforce values: `cast 7` is safe from every
heap but its result is not a valid reference at world 0. -/
theorem closureEnforcesValues_neg : ¬ Recipe.safetyOnly.ClosureEnforcesValues := by
  intro h
  have hs : safeOnly (V Recipe.safetyOnly .ref) 0 (.cast (.num 7)) := safeOnly_pos _
  obtain ⟨l, hl, hlt⟩ := h (V Recipe.safetyOnly .ref) 0 (.cast (.num 7)) hs [] (Nat.le_refl _)
    (.loc 7) [] (by reach) rfl
  cases hl
  exact Nat.not_lt_zero _ hlt

/-! ### `Recipe.HasInvalidRef` -/
theorem hasInvalidRef_pos : Recipe.std.HasInvalidRef ∧ Recipe.safetyOnly.HasInvalidRef :=
  ⟨std_hasInvalidRef, ⟨0, 0, Nat.lt_irrefl 0⟩⟩
theorem hasInvalidRef_neg : ¬ Recipe.anyLoc.HasInvalidRef :=
  fun ⟨_, _, h⟩ => h trivial

/-! ### `withCastRootRule` -/
theorem withCastRootRule_pos :
    withCastRootRule [] derefArg (.arrow .ref .int) ∧
    withCastRootRule [.int] (.cast (.var 0)) .ref :=
  ⟨Or.inl (.lam (.read (.var rfl))), typing_relation_nonvacuous⟩
/-- The extension only types `cast` at the root at type `ref`, and still rejects
`read (cast 7)` (no rule types `cast` below `read`). -/
theorem withCastRootRule_neg :
    ¬ withCastRootRule [.int] (.cast (.var 0)) .int ∧ ¬ withCastRootRule [] forgedRead .int := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨a, _, hτ, _⟩
    · exact not_hasType_of_not_castFree rfl _ _ h
    · cases hτ
  · rcases h with h | ⟨a, he, _, _⟩
    · exact forgedRead_unsafe_ill_typed.1 _ _ h
    · cases he

/-! ### `RestrictedCastRule` -/
theorem restrictedCastRule_pos :
    RestrictedCastRule [.ref] (.cast (.num 0)) .ref ∧
    RestrictedCastRule [] (.cast zeroAfterAlloc) .ref :=
  ⟨.refCtx, .allocArg⟩
theorem restrictedCastRule_neg :
    ¬ RestrictedCastRule [] (.cast (.num 0)) .ref ∧
    ¬ RestrictedCastRule [.int] (.cast (.var 0)) .ref :=
  ⟨fun h => (by cases h), typing_relation_hyp_tight.1 _⟩

end Toy.SemType
