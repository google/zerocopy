import ToyHoare.Logic
import ToyHoare.Incomplete

/-!
# Verification-condition generation with user-supplied loop invariants

`ACom` is the While language with every loop annotated by a (semantic) invariant.
`vcgen a Q` computes, backwards from the postcondition `Q`, a precondition and a list of side
conditions. Each side condition is an assertion that must hold in *every* store (`VCsValid`):
side conditions are not guarded by the conditions of enclosing branches, and a loop's side
conditions do not carry facts about variables the loop does not modify (unlike verifiers that
cut loops by havocking only the modified variables), so such facts must be repeated in the loop
invariant. This follows the textbook generator of Nipkow and Klein (`VCG.thy`).
-/

namespace Toy.Hoare

/-- Annotated commands: like `Com`, but every loop carries a candidate invariant. -/
inductive ACom where
  | skip : ACom
  | assign : Nat → AExp → ACom
  | seq : ACom → ACom → ACom
  | cond : BExp → ACom → ACom → ACom
  | whileDo : Assn → BExp → ACom → ACom

/-- Forget the annotations. -/
def ACom.erase : ACom → Com
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a₁ a₂ => .seq a₁.erase a₂.erase
  | .cond b a₁ a₂ => .cond b a₁.erase a₂.erase
  | .whileDo _ b a => .whileDo b a.erase

/-- Verification-condition generator. `(vcgen a Q).1` is the computed precondition and
`(vcgen a Q).2` the list of side conditions. A loop `whileDo I b a` contributes precondition `I`
and the side conditions `I ∧ b → pre(a, I)` (preservation) and `I ∧ ¬b → Q` (exit). Side
conditions of a conditional's branches are concatenated without the branch condition; across
`seq` and assignments the precondition is propagated semantically, with no admissibility check on
the intermediate assertion. -/
def vcgen : ACom → Assn → Assn × List Assn
  | .skip, Q => (Q, [])
  | .assign x e, Q => (fun s => Q (upd s x (e.eval s)), [])
  | .seq a₁ a₂, Q =>
    ((vcgen a₁ (vcgen a₂ Q).1).1, (vcgen a₁ (vcgen a₂ Q).1).2 ++ (vcgen a₂ Q).2)
  | .cond b a₁ a₂, Q =>
    (fun s => (b.eval s = true → (vcgen a₁ Q).1 s) ∧ (b.eval s = false → (vcgen a₂ Q).1 s),
      (vcgen a₁ Q).2 ++ (vcgen a₂ Q).2)
  | .whileDo I b a, Q =>
    (I, (fun s => I s → b.eval s = true → (vcgen a I).1 s) ::
        (fun s => I s → b.eval s = false → Q s) :: (vcgen a I).2)

/-- A list of side conditions is valid if each one holds in every store. -/
def VCsValid (l : List Assn) : Prop := ∀ φ ∈ l, ∀ s, φ s

theorem VCsValid.append {l₁ l₂ : List Assn} : VCsValid (l₁ ++ l₂) ↔ VCsValid l₁ ∧ VCsValid l₂ := by
  simp only [VCsValid, List.mem_append]
  constructor
  · intro h; exact ⟨fun φ hφ => h φ (Or.inl hφ), fun φ hφ => h φ (Or.inr hφ)⟩
  · rintro ⟨h₁, h₂⟩ φ (hφ | hφ)
    · exact h₁ φ hφ
    · exact h₂ φ hφ

theorem VCsValid.cons {φ : Assn} {l : List Assn} : VCsValid (φ :: l) ↔ (∀ s, φ s) ∧ VCsValid l := by
  simp only [VCsValid, List.mem_cons]
  constructor
  · intro h; exact ⟨h φ (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩
  · rintro ⟨h₁, h₂⟩ ψ (rfl | hψ)
    · exact h₁
    · exact h₂ ψ hψ

/-- Valid side conditions yield a derivation of `{pre} erase a {Q}` with semantic assertions. -/
theorem vcgen_deriv (a : ACom) :
    ∀ Q : Assn, VCsValid (vcgen a Q).2 → Deriv AnyAssn (vcgen a Q).1 a.erase Q := by
  induction a with
  | skip => intro Q _; exact Deriv.skip Q
  | assign x e => intro Q _; exact Deriv.assign x e Q
  | seq a₁ a₂ ih₁ ih₂ =>
    intro Q h
    simp only [vcgen, VCsValid.append] at h
    exact Deriv.seq trivial (ih₁ _ h.1) (ih₂ Q h.2)
  | cond b a₁ a₂ ih₁ ih₂ =>
    intro Q h
    simp only [vcgen, VCsValid.append] at h
    refine Deriv.cond ?_ ?_
    · exact Deriv.conseq (fun s hs => hs.1.1 hs.2) (ih₁ Q h.1) (fun _ h => h)
    · exact Deriv.conseq (fun s hs => hs.1.2 hs.2) (ih₂ Q h.2) (fun _ h => h)
  | whileDo I b a ih =>
    intro Q h
    simp only [vcgen, VCsValid.cons] at h
    obtain ⟨hpres, hexit, hrest⟩ := h
    have hbody : Deriv AnyAssn (fun s => I s ∧ b.eval s = true) a.erase I :=
      Deriv.conseq (fun s hs => hpres s hs.1 hs.2) (ih I hrest) (fun _ h => h)
    exact Deriv.conseq (fun _ h => h) (Deriv.whileDo trivial hbody)
      (fun s hs => hexit s hs.1 hs.2)

/-- **VC soundness.** If every side condition generated for the annotated program `a` and
postcondition `Q` holds in every store, and `P` implies the generated precondition, then
`{P} erase a {Q}` is valid in partial correctness. -/
theorem vcgen_sound {a : ACom} {P Q : Assn} (hvc : VCsValid (vcgen a Q).2)
    (hpre : ∀ s, P s → (vcgen a Q).1 s) : Valid P a.erase Q :=
  fun s s' hP hx => hoare_sound (vcgen_deriv a Q hvc) s s' (hpre s hP) hx

/-! ### Completeness relative to the weakest-liberal-precondition annotation -/

/-- The canonical annotation: each loop is annotated with the weakest liberal precondition of
that loop for the postcondition that holds after it (computed backwards from `Q`). -/
def annotWlp : Com → Assn → ACom
  | .skip, _ => .skip
  | .assign x e, _ => .assign x e
  | .seq c₁ c₂, Q => .seq (annotWlp c₁ (wlp c₂ Q)) (annotWlp c₂ Q)
  | .cond b c₁ c₂, Q => .cond b (annotWlp c₁ Q) (annotWlp c₂ Q)
  | .whileDo b c, Q => .whileDo (wlp (.whileDo b c) Q) b (annotWlp c (wlp (.whileDo b c) Q))

theorem erase_annotWlp (c : Com) : ∀ Q, (annotWlp c Q).erase = c := by
  induction c with
  | skip => intro; rfl
  | assign => intro; rfl
  | seq c₁ c₂ ih₁ ih₂ => intro Q; simp [annotWlp, ACom.erase, ih₁, ih₂]
  | cond b c₁ c₂ ih₁ ih₂ => intro Q; simp [annotWlp, ACom.erase, ih₁, ih₂]
  | whileDo b c ih => intro Q; simp [annotWlp, ACom.erase, ih]

/-- With the `wlp` annotation, the generated precondition is (pointwise) the `wlp` and every
side condition is valid. -/
theorem vcgen_annotWlp (c : Com) :
    ∀ Q, (∀ s, (vcgen (annotWlp c Q) Q).1 s ↔ wlp c Q s) ∧ VCsValid (vcgen (annotWlp c Q) Q).2 := by
  induction c with
  | skip =>
    intro Q
    refine ⟨fun s => ⟨fun h s' hx => by cases hx; exact h, fun h => h s (Exec.skip s)⟩, ?_⟩
    intro φ hφ; simp [annotWlp, vcgen] at hφ
  | assign x e =>
    intro Q
    refine ⟨fun s => ⟨fun h s' hx => by cases hx; exact h, fun h => h _ (Exec.assign x e s)⟩, ?_⟩
    intro φ hφ; simp [annotWlp, vcgen] at hφ
  | seq c₁ c₂ ih₁ ih₂ =>
    intro Q
    obtain ⟨hpre₂, hvc₂⟩ := ih₂ Q
    obtain ⟨hpre₁, hvc₁⟩ := ih₁ (wlp c₂ Q)
    have key : ∀ R : Assn, (∀ s, R s ↔ wlp c₂ Q s) →
        ∀ s, (vcgen (annotWlp c₁ (wlp c₂ Q)) R).1 s ↔ (vcgen (annotWlp c₁ (wlp c₂ Q)) (wlp c₂ Q)).1 s := by
      intro R hR
      have : R = wlp c₂ Q := funext fun s => propext (hR s)
      subst this; intro s; rfl
    have hR : (vcgen (annotWlp c₂ Q) Q).1 = wlp c₂ Q := funext fun s => propext (hpre₂ s)
    refine ⟨fun s => ?_, ?_⟩
    · simp only [annotWlp, vcgen, hR]
      rw [hpre₁, wlp_seq]
    · simp only [annotWlp, vcgen, hR, VCsValid.append]
      exact ⟨hvc₁, hvc₂⟩
  | cond b c₁ c₂ ih₁ ih₂ =>
    intro Q
    obtain ⟨hpre₁, hvc₁⟩ := ih₁ Q
    obtain ⟨hpre₂, hvc₂⟩ := ih₂ Q
    refine ⟨fun s => ?_, ?_⟩
    · simp only [annotWlp, vcgen, hpre₁, hpre₂]
      constructor
      · rintro ⟨h₁, h₂⟩ s' hx
        cases hx with
        | condTrue hb hx => exact h₁ hb s' hx
        | condFalse hb hx => exact h₂ hb s' hx
      · intro h
        exact ⟨fun hb s' hx => h s' (Exec.condTrue hb hx), fun hb s' hx => h s' (Exec.condFalse hb hx)⟩
    · simp only [annotWlp, vcgen, VCsValid.append]
      exact ⟨hvc₁, hvc₂⟩
  | whileDo b c ih =>
    intro Q
    obtain ⟨hpre, hvc⟩ := ih (wlp (.whileDo b c) Q)
    refine ⟨fun s => Iff.rfl, ?_⟩
    simp only [annotWlp, vcgen, VCsValid.cons]
    refine ⟨fun s hI hb => ?_, fun s hI hb => hI s (Exec.whileFalse hb), hvc⟩
    rw [hpre]
    intro s₁ hx₁ s₂ hx₂
    exact hI s₂ (Exec.whileTrue hb hx₁ hx₂)

/-- **VC generation is complete relative to the wlp annotation.** For every command `c` and
assertions `P`, `Q`: `{P} c {Q}` is valid iff, for the annotation `annotWlp c Q` (which erases
to `c`), all generated side conditions are valid and `P` implies the generated precondition. -/
theorem valid_iff_vcs_annotWlp {P : Assn} {c : Com} {Q : Assn} :
    Valid P c Q ↔
      (VCsValid (vcgen (annotWlp c Q) Q).2 ∧ ∀ s, P s → (vcgen (annotWlp c Q) Q).1 s) := by
  obtain ⟨hpre, hvc⟩ := vcgen_annotWlp c Q
  constructor
  · intro hv
    exact ⟨hvc, fun s hP => (hpre s).mpr (valid_iff_imp_wlp.mp hv s hP)⟩
  · rintro ⟨hvc', hP⟩
    have := vcgen_sound hvc' hP
    rwa [erase_annotWlp] at this

/-! ### Reachable-state annotations need not be inductive -/

/-- States reachable at the head of `while b do c` from a state satisfying `P`. -/
inductive HeadReach (P : Assn) (b : BExp) (c : Com) : Store → Prop where
  | init {s : Store} : P s → HeadReach P b c s
  | step {s s' : Store} : HeadReach P b c s → b.eval s = true → Exec c s s' → HeadReach P b c s'

/-- Guard `x < 2`. -/
def ncGuard : BExp := .lt (.var 0) (.lit 2)

theorem ncGuard_eval (s : Store) : ncGuard.eval s = decide (s 0 < 2) := rfl

/-- Body `x := x + 2`. -/
def ncBody : Com := .assign 0 (.add (.var 0) (.lit 2))

/-- Annotation `x ≤ 2`: true on every reachable loop-head state from `x = 0`, but not inductive
(it admits the unreachable state `x = 1`, whose successor `x = 3` violates it). -/
def ncInv : Assn := fun s => s 0 ≤ 2

/-- `while x < 2 do x := x + 2` annotated with `x ≤ 2`. -/
def ncAnn : ACom := .whileDo ncInv ncGuard (.assign 0 (.add (.var 0) (.lit 2)))

def ncPre : Assn := fun s => s 0 = 0
def ncPost : Assn := fun s => s 0 = 2

theorem headReach_nc {s : Store} (h : HeadReach ncPre ncGuard ncBody s) : s 0 = 0 ∨ s 0 = 2 := by
  induction h with
  | init h => exact Or.inl h
  | step _ hb hx ih =>
    cases hx
    rw [ncGuard_eval, decide_eq_true_iff] at hb
    simp [upd, AExp.eval]
    omega

/-- **Counterexample (VCs need inductive annotations).** For `{x = 0} while x < 2 do x := x + 2
{x = 2}` annotated with `x ≤ 2`: the triple is valid, the annotation holds on every reachable
loop-head state, the precondition implies the generated precondition, and the exit side
condition `x ≤ 2 ∧ ¬(x < 2) → x = 2` is valid; yet the preservation side condition fails at the
store `st2 1 0` (`x = 1`), which satisfies the annotation and the guard but is not reachable at
the loop head; hence not all side conditions are valid. -/
theorem vcgen_reachable_noninductive_annotation_fails :
    Valid ncPre ncAnn.erase ncPost ∧
    (∀ s, HeadReach ncPre ncGuard ncBody s → ncInv s) ∧
    (∀ s, ncPre s → (vcgen ncAnn ncPost).1 s) ∧
    (∀ s, ncInv s → ncGuard.eval s = false → ncPost s) ∧
    ¬ HeadReach ncPre ncGuard ncBody (st2 1 0) ∧
    (ncInv (st2 1 0) ∧ ncGuard.eval (st2 1 0) = true ∧
      ¬ (vcgen (.assign 0 (.add (.var 0) (.lit 2))) ncInv).1 (st2 1 0)) ∧
    ¬ VCsValid (vcgen ncAnn ncPost).2 := by
  refine ⟨?_, fun s h => ?_, fun s h => ?_, ?_, ?_, ?_, fun h => ?_⟩
  · -- validity via the inductive invariant `x = 0 ∨ x = 2`
    have hd : Deriv AnyAssn ncPre ncAnn.erase ncPost := by
      refine Deriv.conseq (P' := fun s => s 0 = 0 ∨ s 0 = 2) (fun s h => Or.inl h)
        (Deriv.whileDo trivial ?_) (fun s h => ?_)
      · refine Deriv.conseq (fun s h => ?_) (Deriv.assign 0 _ _) (fun _ h => h)
        obtain ⟨h₁, h₂⟩ := h
        rw [ncGuard_eval, decide_eq_true_iff] at h₂
        simp [upd, AExp.eval]
        omega
      · obtain ⟨h₁, h₂⟩ := h
        rw [ncGuard_eval, decide_eq_false_iff_not] at h₂
        simp only [ncPost]
        omega
    exact hoare_sound hd
  · have := headReach_nc h
    simp only [ncInv]; omega
  · simp only [ncPre] at h; simp only [vcgen, ncAnn, ncInv]; omega
  · intro s hI hb
    rw [ncGuard_eval, decide_eq_false_iff_not] at hb
    simp only [ncInv] at hI
    simp only [ncPost]
    omega
  · intro hr
    have := headReach_nc hr
    simp [st2] at this
  · refine ⟨by simp [ncInv, st2], by simp [ncGuard, BExp.eval, AExp.eval, st2], ?_⟩
    simp [vcgen, ncInv, upd, AExp.eval, st2]
  · simp only [ncAnn, vcgen, VCsValid.cons] at h
    have := h.1 (fun _ => 1) (by simp [ncInv]) (by simp [ncGuard, BExp.eval, AExp.eval])
    simp [ncInv, upd, AExp.eval] at this

/-! ### With linear annotations, VC generation is incomplete -/

/-- Every loop annotation in `a` satisfies `L`. -/
def ACom.InvsIn (L : Assn → Prop) : ACom → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq a₁ a₂ => a₁.InvsIn L ∧ a₂.InvsIn L
  | .cond _ a₁ a₂ => a₁.InvsIn L ∧ a₂.InvsIn L
  | .whileDo I _ a => L I ∧ a.InvsIn L

/-- **Expressiveness matters (VC generation).** The triple `{x = y + y} while 2 ≤ x do
x := x - 2 {x ≠ 1}`, whose pre- and postcondition are linearly definable, is valid, but it cannot
be verified by VC generation with any annotation whose loop invariants are definable in
divisibility-free quantifier-free linear integer arithmetic: for every such annotation `a`
erasing to the loop, either some side condition is invalid or the precondition does not imply
the generated precondition. -/
theorem vcgen_linear_qf_annotations_incomplete :
    LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoop exPost ∧
    ∀ a : ACom, a.erase = exLoop → a.InvsIn LinDef →
      ¬ (VCsValid (vcgen a exPost).2 ∧ ∀ s, exPre s → (vcgen a exPost).1 s) := by
  refine ⟨exPre_linDef, exPost_linDef, exLoop_valid, fun a ha hL ⟨hvc, hpre⟩ => ?_⟩
  cases a with
  | skip => cases ha
  | assign => cases ha
  | seq => cases ha
  | cond => cases ha
  | whileDo I b a' =>
    simp only [ACom.erase, exLoop, Com.whileDo.injEq] at ha
    obtain ⟨rfl, ha'⟩ := ha
    simp only [ACom.InvsIn] at hL
    simp only [vcgen, VCsValid.cons] at hvc hpre
    obtain ⟨hpres, hexit, hrest⟩ := hvc
    refine exLoop_no_linDef_invariant ⟨I, hL.1, hpre, ?_, hexit⟩
    have hb := vcgen_sound (P := fun s => I s ∧ exGuard.eval s = true) hrest
      (fun s hs => hpres s hs.1 hs.2)
    rwa [ha'] at hb

/-- The parity annotation `while[x even] 2 ≤ x do x := x - 2`. -/
def exParityAnn : ACom := .whileDo exParityInv exGuard (.assign 0 (.sub (.var 0) (.lit 2)))

/-- **Positive control.** With the (non-linear-definable) semantic invariant "x is even", the
same loop is verified by VC generation. -/
theorem exParityAnn_verifies :
    exParityAnn.erase = exLoop ∧ exParityAnn.InvsIn AnyAssn ∧
    VCsValid (vcgen exParityAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exParityAnn exPost).1 s := by
  refine ⟨rfl, ⟨trivial, trivial⟩, ?_, fun s h => ?_⟩
  · simp only [exParityAnn, vcgen, VCsValid.cons]
    refine ⟨fun s h _ => ?_, fun s h hb => ?_, fun φ hφ => by simp at hφ⟩
    · simp only [exParityInv] at h
      simp [exParityInv, upd, AExp.eval]
      omega
    · simp only [exParityInv] at h
      simp only [exPost]
      omega
  · simp only [exPre] at h
    simp only [exParityAnn, vcgen, exParityInv]
    omega

end Toy.Hoare
