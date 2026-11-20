import ToyLink.Statements

/-!
# Unfolded restatements of the main positive results

Restates each main result from `ToyLink.Statements` with interface wrappers
(`CtxRefines`, `EntryRefines`, `StandaloneRefines`, `MayDiverge`, `HasBehavior`,
`Linkable`, `SpecsImplemented`, `ModuleVerifiedPartial`, `ModuleVerifiedTotal`,
`ProgramPartialCorrect`, `ProgramTotalCorrect`, `WeakensPre`, `StrengthensPostUnderPre`,
`mixEnv`, `PreservesVerifiedPartial`, `PreservesDefines`, `PassCtxRefines`) unfolded,
and proves exact logical equivalence (`↔`) to the folded proposition (by `Iff.rfl`).
-/

namespace Toy.Link.Unfolded

open Toy.Link

/-- Unfolded statement of `ctxRefines_refl`. -/
def ctxRefines_refl_unfolded (M : Module) : Prop :=
  ∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
       (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
    ∀ entry fuel arg out, out ∈ eval fuel (link C M) entry arg → out ∈ eval fuel (link C M) entry arg

theorem ctxRefines_refl_unfolded_iff (M : Module) :
    ctxRefines_refl_unfolded M ↔ CtxRefines M M :=
  Iff.rfl

/-- Unfolded statement of `ctxRefines_trans`. -/
def ctxRefines_trans_unfolded (M₁ M₂ M₃ : Module) : Prop :=
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M₁.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M₂.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M₂) entry arg → out ∈ eval fuel (link C M₁) entry arg) →
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M₂.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M₃.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M₃) entry arg → out ∈ eval fuel (link C M₂) entry arg) →
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M₁.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M₃.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M₃) entry arg → out ∈ eval fuel (link C M₁) entry arg)

theorem ctxRefines_trans_unfolded_iff (M₁ M₂ M₃ : Module) :
    ctxRefines_trans_unfolded M₁ M₂ M₃ ↔
      (CtxRefines M₁ M₂ → CtxRefines M₂ M₃ → CtxRefines M₁ M₃) :=
  Iff.rfl

/-- Unfolded statement of `ctxRefines_link_congr`. -/
def ctxRefines_link_congr_unfolded (M₁ M₁' M₂ M₂' : Module) : Prop :=
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M₁.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M₁'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M₁') entry arg → out ∈ eval fuel (link C M₁) entry arg) →
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M₂.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M₂'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M₂') entry arg → out ∈ eval fuel (link C M₂) entry arg) →
  (∀ fn, ¬ (M₁.Defines fn ∧ M₂.Defines fn)) →
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ (link M₁ M₂).Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ (link M₁' M₂').Defines fn)) →
        ∀ entry fuel arg out,
          out ∈ eval fuel (link C (link M₁' M₂')) entry arg →
          out ∈ eval fuel (link C (link M₁ M₂)) entry arg)

theorem ctxRefines_link_congr_unfolded_iff (M₁ M₁' M₂ M₂' : Module) :
    ctxRefines_link_congr_unfolded M₁ M₁' M₂ M₂' ↔
      (CtxRefines M₁ M₁' → CtxRefines M₂ M₂' → Linkable M₁ M₂ →
        CtxRefines (link M₁ M₂) (link M₁' M₂')) :=
  Iff.rfl

/-- Unfolded statement of `ag_partial_correctness`. -/
def ag_partial_correctness_unfolded (P : Module) (S : SpecEnv) : Prop :=
  (∀ fn x, (S fn).pre x → P.Defines fn) →
  (∀ fn body, P.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)) →
  (∀ fn fuel x out, (S fn).pre x → out ∈ eval fuel P fn x →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S fn).post x v)

theorem ag_partial_correctness_unfolded_iff (P : Module) (S : SpecEnv) :
    ag_partial_correctness_unfolded P S ↔
      (SpecsImplemented P S → ModuleVerifiedPartial P S S → ProgramPartialCorrect P S) :=
  Iff.rfl

/-- Unfolded statement of `ag_total_correctness_of_wf_call_measure`. -/
def ag_total_correctness_of_wf_call_measure_unfolded {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (P : Module) (S : SpecEnv) : Prop :=
  WellFounded rel →
  (∀ fn x, (S fn).pre x → P.Defines fn) →
  (∀ fn body, P.lookup fn = some body →
    ∀ x, (S fn).pre x → wpCallDec rel μ S (μ fn x) x body ((S fn).post x)) →
  (∀ fn x, (S fn).pre x → ∃ fuel, ∀ out, out ∈ eval fuel P fn x →
    ∃ v, out = .val v ∧ (S fn).post x v)

theorem ag_total_correctness_of_wf_call_measure_unfolded_iff {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (P : Module) (S : SpecEnv) :
    ag_total_correctness_of_wf_call_measure_unfolded rel μ P S ↔
      (WellFounded rel → SpecsImplemented P S → ModuleVerifiedTotal rel μ P S S →
        ProgramTotalCorrect P S) :=
  Iff.rfl

/-- Unfolded statement of `verified_recursive_caller_links_with_refined_callee`. -/
def verified_recursive_caller_links_with_refined_callee_unfolded
    (M N : Module) (S S' G : SpecEnv) : Prop :=
  (∀ fn, ¬ (M.Defines fn ∧ N.Defines fn)) →
  (∀ fn body, M.lookup fn = some body → ∀ x, (G fn).pre x →
    wpPartial (fun g => if M.Defines g then G g else S g) x body ((G fn).post x)) →
  (∀ fn fuel x out, (S' fn).pre x → out ∈ eval fuel N fn x →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S' fn).post x v) →
  (∀ g, ¬ M.Defines g → ∀ x, (S g).pre x → (S' g).pre x) →
  (∀ g, ¬ M.Defines g → ∀ x v, (S g).pre x → (S' g).post x v → (S g).post x v) →
  (∀ f, M.Defines f → ∀ fuel x out, (G f).pre x → out ∈ eval fuel (link M N) f x →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ (G f).post x v)

theorem verified_recursive_caller_links_with_refined_callee_unfolded_iff
    (M N : Module) (S S' G : SpecEnv) :
    verified_recursive_caller_links_with_refined_callee_unfolded M N S S' G ↔
      (Linkable M N → ModuleVerifiedPartial M (mixEnv M G S) G → ProgramPartialCorrect N S' →
        (∀ g, ¬ M.Defines g → WeakensPre (S g) (S' g)) →
        (∀ g, ¬ M.Defines g → StrengthensPostUnderPre (S g) (S' g)) →
        ∀ f, M.Defines f → FnPartialCorrect (link M N) f (G f)) :=
  Iff.rfl

/-- Unfolded statement of `separate_compilation_partial_correct_of_preserves_verified`. -/
def separate_compilation_partial_correct_of_preserves_verified_unfolded
    (M₁ M₂ : Module) (S : SpecEnv) (compile : Module → Module) : Prop :=
  (∀ fn body, M₁.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)) →
  (∀ fn body, M₂.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)) →
  (∀ fn x, (S fn).pre x → (link M₁ M₂).Defines fn) →
  (∀ M, (∀ fn body, M.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)) →
        (∀ fn body, (compile M).lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x))) →
  (∀ M fn, M.Defines fn → (compile M).Defines fn) →
  (∀ fn fuel x out, (S fn).pre x → out ∈ eval fuel (link (compile M₁) (compile M₂)) fn x →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S fn).post x v)

theorem separate_compilation_partial_correct_of_preserves_verified_unfolded_iff
    (M₁ M₂ : Module) (S : SpecEnv) (compile : Module → Module) :
    separate_compilation_partial_correct_of_preserves_verified_unfolded M₁ M₂ S compile ↔
      (ModuleVerifiedPartial M₁ S S → ModuleVerifiedPartial M₂ S S →
        SpecsImplemented (link M₁ M₂) S →
        PreservesVerifiedPartial compile S → PreservesDefines compile →
        ProgramPartialCorrect (link (compile M₁) (compile M₂)) S) :=
  Iff.rfl

/-- Unfolded statement of `separate_compilation_ctxRefines_of_pass_ctxRefines`. -/
def separate_compilation_ctxRefines_of_pass_ctxRefines_unfolded
    (M₁ M₂ : Module) (compile : Module → Module) : Prop :=
  (∀ M C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ (compile M).Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C (compile M)) entry arg →
          out ∈ eval fuel (link C M) entry arg) →
  (∀ fn, ¬ (M₁.Defines fn ∧ M₂.Defines fn)) →
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ (link M₁ M₂).Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ (link (compile M₁) (compile M₂)).Defines fn)) →
        ∀ entry fuel arg out,
          out ∈ eval fuel (link C (link (compile M₁) (compile M₂))) entry arg →
          out ∈ eval fuel (link C (link M₁ M₂)) entry arg)

theorem separate_compilation_ctxRefines_of_pass_ctxRefines_unfolded_iff
    (M₁ M₂ : Module) (compile : Module → Module) :
    separate_compilation_ctxRefines_of_pass_ctxRefines_unfolded M₁ M₂ compile ↔
      (PassCtxRefines compile → Linkable M₁ M₂ →
        CtxRefines (link M₁ M₂) (link (compile M₁) (compile M₂))) :=
  Iff.rfl

/-- Unfolded statement of `ctxRefines_iff_standaloneRefines_of_closed_source_or_target`. -/
def ctxRefines_iff_standaloneRefines_of_closed_source_or_target_unfolded
    (M M' : Module) : Prop :=
  ((∀ fn body, M.lookup fn = some body → body.CalleesIn M.Defines) ∨
   (∀ fn body, M'.lookup fn = some body → body.CalleesIn M'.Defines)) →
  ((∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg →
          out ∈ eval fuel (link C M) entry arg) ↔
   (∀ entry fuel arg out, out ∈ eval fuel M' entry arg → out ∈ eval fuel M entry arg))

theorem ctxRefines_iff_standaloneRefines_of_closed_source_or_target_unfolded_iff
    (M M' : Module) :
    ctxRefines_iff_standaloneRefines_of_closed_source_or_target_unfolded M M' ↔
      (ClosedModule M ∨ ClosedModule M' → (CtxRefines M M' ↔ StandaloneRefines M M')) :=
  Iff.rfl

/-- Unfolded statement of `ctxRefines_reflects_mayDiverge`. -/
def ctxRefines_reflects_mayDiverge_unfolded (M M' C : Module) (entry : Fname) (arg : Int) :
    Prop :=
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg →
          out ∈ eval fuel (link C M) entry arg) →
  (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
  (∀ fuel, Outcome.outOfFuel ∈ eval fuel (link C M') entry arg) →
  (∀ fuel, Outcome.outOfFuel ∈ eval fuel (link C M) entry arg)

theorem ctxRefines_reflects_mayDiverge_unfolded_iff (M M' C : Module) (entry : Fname)
    (arg : Int) :
    ctxRefines_reflects_mayDiverge_unfolded M M' C entry arg ↔
      (CtxRefines M M' → Linkable C M →
        MayDiverge (link C M') entry arg → MayDiverge (link C M) entry arg) :=
  Iff.rfl

end Toy.Link.Unfolded
