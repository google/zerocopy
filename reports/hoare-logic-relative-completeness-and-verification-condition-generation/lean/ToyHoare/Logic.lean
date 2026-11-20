import ToyHoare.Basic

/-!
# Hoare logic for partial correctness: rules, soundness, relative completeness

`Deriv L P c Q` is derivability of `{P} c {Q}` in the textbook partial-correctness rule system
(skip, assignment, sequencing, conditional, while, consequence). The rule of consequence takes
*semantic* implications as premises (an oracle for the assertion logic).

The parameter `L : Assn → Prop` says which assertions a derivation may *invent*: the intermediate
assertion `R` of the sequencing rule and the invariant `I` of the while rule must satisfy `L`.
All other assertions (preconditions and postconditions, the assignment precondition `Q[e/x]`,
the guard conjunctions `P ∧ b`, `I ∧ ¬b`, and the intermediate assertions `P'`, `Q'` of the
consequence rule) are unrestricted predicates. With `L := fun _ => True` this is Hoare logic
over semantic assertions; with `L := LinDef` (see `ToyHoare.Linear`) the invented assertions must
be definable in divisibility-free quantifier-free linear integer arithmetic.
-/

namespace Toy.Hoare

/-- Derivability of the partial-correctness triple `{P} c {Q}`; `L` constrains exactly the
intermediate assertions of `seq` and the invariants of `whileDo`. Consequence premises are
semantic implications. -/
inductive Deriv (L : Assn → Prop) : Assn → Com → Assn → Prop where
  | skip (P : Assn) : Deriv L P .skip P
  | assign (x : Nat) (e : AExp) (Q : Assn) :
      Deriv L (fun s => Q (upd s x (e.eval s))) (.assign x e) Q
  | seq {P R Q : Assn} {c₁ c₂ : Com} :
      L R → Deriv L P c₁ R → Deriv L R c₂ Q → Deriv L P (.seq c₁ c₂) Q
  | cond {P Q : Assn} {b : BExp} {c₁ c₂ : Com} :
      Deriv L (fun s => P s ∧ b.eval s = true) c₁ Q →
      Deriv L (fun s => P s ∧ b.eval s = false) c₂ Q →
      Deriv L P (.cond b c₁ c₂) Q
  | whileDo {I : Assn} {b : BExp} {c : Com} :
      L I → Deriv L (fun s => I s ∧ b.eval s = true) c I →
      Deriv L I (.whileDo b c) (fun s => I s ∧ b.eval s = false)
  | conseq {P P' Q Q' : Assn} {c : Com} :
      (∀ s, P s → P' s) → Deriv L P' c Q' → (∀ s, Q' s → Q s) → Deriv L P c Q

/-- The unrestricted admissibility predicate: every semantic assertion may be invented. -/
def AnyAssn : Assn → Prop := fun _ => True

/-- Derivability is monotone in the admissibility predicate. -/
theorem Deriv.mono {L₁ L₂ : Assn → Prop} (hL : ∀ R, L₁ R → L₂ R) {P : Assn} {c : Com} {Q : Assn}
    (h : Deriv L₁ P c Q) : Deriv L₂ P c Q := by
  induction h with
  | skip P => exact Deriv.skip P
  | assign x e Q => exact Deriv.assign x e Q
  | seq hR _ _ ih₁ ih₂ => exact Deriv.seq (hL _ hR) ih₁ ih₂
  | cond _ _ ih₁ ih₂ => exact Deriv.cond ih₁ ih₂
  | whileDo hI _ ih => exact Deriv.whileDo (hL _ hI) ih
  | conseq hP _ hQ ih => exact Deriv.conseq hP ih hQ

/-- A loop invariant is preserved by every terminating run of the loop and the guard is false
on exit. -/
theorem exec_while_invariant {I : Assn} {b : BExp} {c : Com}
    (hbody : Valid (fun s => I s ∧ b.eval s = true) c I) :
    ∀ {w : Com} {s s' : Store}, Exec w s s' → w = .whileDo b c → I s →
      I s' ∧ b.eval s' = false := by
  intro w s s' hx
  induction hx with
  | whileFalse hb => intro hw hI; cases hw; exact ⟨hI, hb⟩
  | whileTrue hb hc _ _ ih₂ =>
    intro hw hI; cases hw; exact ih₂ rfl (hbody _ _ ⟨hI, hb⟩ hc)
  | skip => intro hw; cases hw
  | assign => intro hw; cases hw
  | seq => intro hw; cases hw
  | condTrue => intro hw; cases hw
  | condFalse => intro hw; cases hw

/-- **Soundness.** For every admissibility predicate `L`, every derivable triple is valid in
partial correctness. -/
theorem hoare_sound {L : Assn → Prop} {P : Assn} {c : Com} {Q : Assn}
    (h : Deriv L P c Q) : Valid P c Q := by
  induction h with
  | skip P => intro s s' hP hx; cases hx; exact hP
  | assign x e Q => intro s s' hP hx; cases hx; exact hP
  | seq _ _ _ ih₁ ih₂ =>
    intro s s' hP hx
    cases hx with
    | seq h₁ h₂ => exact ih₂ _ _ (ih₁ _ _ hP h₁) h₂
  | cond _ _ ih₁ ih₂ =>
    intro s s' hP hx
    cases hx with
    | condTrue hb h => exact ih₁ _ _ ⟨hP, hb⟩ h
    | condFalse hb h => exact ih₂ _ _ ⟨hP, hb⟩ h
  | whileDo _ _ ih =>
    intro s s' hI hx
    exact exec_while_invariant ih hx rfl hI
  | conseq hP _ hQ ih =>
    intro s s' h hx
    exact hQ _ (ih _ _ (hP _ h) hx)

/-- `wlp` of a sequence is the composition of `wlp`s (as predicates, by extensionality). -/
theorem wlp_seq (c₁ c₂ : Com) (Q : Assn) : wlp (.seq c₁ c₂) Q = wlp c₁ (wlp c₂ Q) := by
  funext s
  apply propext
  constructor
  · intro h s₁ h₁ s₂ h₂; exact h s₂ (Exec.seq h₁ h₂)
  · intro h s₂ hx
    cases hx with
    | seq h₁ h₂ => exact h _ h₁ _ h₂

/-! ### The assertions a Cook-style completeness proof invents -/

/-- `WlpInvented c Q R`: `R` is one of the assertions invented by the canonical derivation of
`{wlp c Q} c {Q}`, namely, for every occurrence of `seq c₁ c₂` reached with postcondition `S`, the
midpoint `wlp c₂ S`, and for every loop `while b do c'` reached with postcondition `S`, the
invariant `wlp (while b do c') S`. Postconditions are propagated backwards: the body of a loop is
reached with postcondition `wlp (while b do c') S`, and the first component of a sequence with
postcondition `wlp c₂ S`. -/
def WlpInvented : Com → Assn → Assn → Prop
  | .skip, _, _ => False
  | .assign _ _, _, _ => False
  | .seq c₁ c₂, Q, R => R = wlp c₂ Q ∨ WlpInvented c₁ (wlp c₂ Q) R ∨ WlpInvented c₂ Q R
  | .cond _ c₁ c₂, Q, R => WlpInvented c₁ Q R ∨ WlpInvented c₂ Q R
  | .whileDo b c, Q, R =>
    R = wlp (.whileDo b c) Q ∨ WlpInvented c (wlp (.whileDo b c) Q) R

/-- **Command-local `wlp` admissibility.** Every assertion in `WlpInvented c Q` (the `seq`
midpoints `wlp c₂ S` and the loop invariants `wlp (while b do c') S` met when computing
`wlp c Q` backwards) satisfies `L`. This is a property of the finitely many `wlp`s along `c`,
not of all commands. -/
def WlpAdmissibleFor (L : Assn → Prop) (c : Com) (Q : Assn) : Prop :=
  ∀ R, WlpInvented c Q R → L R

/-- Cook-style core lemma: `{wlp c Q} c {Q}` is derivable using as invented assertions exactly
the members of `WlpInvented c Q`. -/
theorem deriv_wlp_wlpInvented (c : Com) : ∀ Q : Assn, Deriv (WlpInvented c Q) (wlp c Q) c Q := by
  induction c with
  | skip =>
    intro Q
    exact Deriv.conseq (fun s h => h s (Exec.skip s)) (Deriv.skip Q) (fun _ h => h)
  | assign x e =>
    intro Q
    exact Deriv.conseq (fun s h => h _ (Exec.assign x e s)) (Deriv.assign x e Q) (fun _ h => h)
  | seq c₁ c₂ ih₁ ih₂ =>
    intro Q
    have h₁ : Deriv (WlpInvented (.seq c₁ c₂) Q) (wlp c₁ (wlp c₂ Q)) c₁ (wlp c₂ Q) :=
      Deriv.mono (fun R h => Or.inr (Or.inl h)) (ih₁ (wlp c₂ Q))
    have h₂ : Deriv (WlpInvented (.seq c₁ c₂) Q) (wlp c₂ Q) c₂ Q :=
      Deriv.mono (fun R h => Or.inr (Or.inr h)) (ih₂ Q)
    exact Deriv.conseq (fun s h s₁ hx₁ s₂ hx₂ => h s₂ (Exec.seq hx₁ hx₂))
      (Deriv.seq (Or.inl rfl) h₁ h₂) (fun _ h => h)
  | cond b c₁ c₂ ih₁ ih₂ =>
    intro Q
    refine Deriv.cond ?_ ?_
    · exact Deriv.conseq (fun s h s' hx => h.1 s' (Exec.condTrue h.2 hx))
        (Deriv.mono (fun R h => Or.inl h) (ih₁ Q)) (fun _ h => h)
    · exact Deriv.conseq (fun s h s' hx => h.1 s' (Exec.condFalse h.2 hx))
        (Deriv.mono (fun R h => Or.inr h) (ih₂ Q)) (fun _ h => h)
  | whileDo b c ih =>
    intro Q
    have hbody : Deriv (WlpInvented (.whileDo b c) Q) (wlp c (wlp (.whileDo b c) Q)) c
        (wlp (.whileDo b c) Q) :=
      Deriv.mono (fun R h => Or.inr h) (ih (wlp (.whileDo b c) Q))
    have hb : Deriv (WlpInvented (.whileDo b c) Q)
        (fun s => wlp (.whileDo b c) Q s ∧ b.eval s = true) c (wlp (.whileDo b c) Q) :=
      Deriv.conseq (fun s h s₁ hx₁ s₂ hx₂ => h.1 s₂ (Exec.whileTrue h.2 hx₁ hx₂)) hbody
        (fun _ h => h)
    exact Deriv.conseq (fun _ h => h) (Deriv.whileDo (Or.inl rfl) hb)
      (fun s h => h.1 s (Exec.whileFalse h.2))

/-- **Exposed witness for relative completeness.** A partial-correctness triple `{P} c {Q}` is
valid iff it has a derivation all of whose `seq` midpoints and loop invariants are among the
`wlp` assertions `WlpInvented c Q`. -/
theorem valid_iff_deriv_wlpInvented {P : Assn} {c : Com} {Q : Assn} :
    Valid P c Q ↔ Deriv (WlpInvented c Q) P c Q :=
  ⟨fun hv => Deriv.conseq (valid_iff_imp_wlp.mp hv) (deriv_wlp_wlpInvented c Q) (fun _ h => h),
    hoare_sound⟩

/-- If every assertion in `WlpInvented c Q` is admissible, then `{wlp c Q} c {Q}` is derivable
with all invented assertions admissible. -/
theorem deriv_wlp_of_wlpAdmissibleFor {L : Assn → Prop} {c : Com} {Q : Assn}
    (hwlp : WlpAdmissibleFor L c Q) : Deriv L (wlp c Q) c Q :=
  Deriv.mono hwlp (deriv_wlp_wlpInvented c Q)

/-- **Relative completeness (Cook-style, command-local hypothesis).** If the `seq` midpoints
`wlp c₂ S` and loop invariants `wlp (while b do c') S` met when computing `wlp c Q` backwards are
all admissible (`WlpAdmissibleFor L c Q`), then every valid partial-correctness triple
`{P} c {Q}` is derivable with all invented assertions admissible. -/
theorem hoare_relatively_complete_of_wlpAdmissibleFor {L : Assn → Prop} {P : Assn} {c : Com}
    {Q : Assn} (hwlp : WlpAdmissibleFor L c Q) (hv : Valid P c Q) : Deriv L P c Q :=
  Deriv.mono hwlp (valid_iff_deriv_wlpInvented.mp hv)

/-- Bridge: admissibility of `wlp c' Q` for *every* command `c'` implies the command-local
hypothesis. (For `L := LinDef` the global form only holds when `Q` is valid; see
`linDef_forall_wlp_iff_tautology`.) -/
theorem wlpAdmissibleFor_of_forall_wlp {L : Assn → Prop} (c : Com) :
    ∀ Q : Assn, (∀ c' : Com, L (wlp c' Q)) → WlpAdmissibleFor L c Q := by
  induction c with
  | skip => intro _ _ R h; exact h.elim
  | assign _ _ => intro _ _ R h; exact h.elim
  | seq c₁ c₂ ih₁ ih₂ =>
    intro Q hQ R h
    rcases h with rfl | h | h
    · exact hQ c₂
    · exact ih₁ (wlp c₂ Q) (fun c' => by rw [← wlp_seq]; exact hQ (.seq c' c₂)) R h
    · exact ih₂ Q hQ R h
  | cond _ c₁ c₂ ih₁ ih₂ =>
    intro Q hQ R h
    rcases h with h | h
    · exact ih₁ Q hQ R h
    · exact ih₂ Q hQ R h
  | whileDo b c ih =>
    intro Q hQ R h
    rcases h with rfl | h
    · exact hQ (.whileDo b c)
    · exact ih (wlp (.whileDo b c) Q)
        (fun c' => by rw [← wlp_seq]; exact hQ (.seq c' (.whileDo b c))) R h

/-- Bridge: Cook's expressiveness (closure of `L` under `wlp`) together with `L Q` yields the
command-local admissibility hypothesis for every command. -/
theorem wlpAdmissibleFor_of_expressive {L : Assn → Prop} {Q : Assn}
    (hexp : ∀ (c : Com) (R : Assn), L R → L (wlp c R)) (hQ : L Q) (c : Com) :
    WlpAdmissibleFor L c Q :=
  wlpAdmissibleFor_of_forall_wlp c Q (fun c' => hexp c' Q hQ)

/-- **Semantic Hoare logic is sound and complete.** With all semantic assertions admissible,
`{P} c {Q}` is derivable iff it is valid in partial correctness. -/
theorem deriv_anyAssn_iff_valid {P : Assn} {c : Com} {Q : Assn} :
    Deriv AnyAssn P c Q ↔ Valid P c Q :=
  ⟨hoare_sound, hoare_relatively_complete_of_wlpAdmissibleFor (fun _ _ => trivial)⟩

end Toy.Hoare
