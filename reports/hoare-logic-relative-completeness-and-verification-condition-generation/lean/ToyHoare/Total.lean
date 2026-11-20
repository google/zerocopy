import ToyHoare.Logic

/-!
# Total correctness with variants

`TValid P c Q`: from every state satisfying `P`, `c` terminates in a state satisfying `Q`.
`TDeriv requireBound P c Q`: the partial-correctness rules with a while rule that additionally
asks for an integer-valued variant `V` that strictly decreases on every iteration. When
`requireBound = true` the rule also demands `0 ≤ V` whenever the invariant and the guard hold;
`requireBound = false` drops that premise and is unsound.

Invariants, intermediate assertions and variants are arbitrary semantic predicates and functions
on stores (not syntactic expressions); no total-correctness VC generator is formalized. `TValid`
uses an existential over final states, which expresses guaranteed termination only because `Exec`
is deterministic (`Exec.deterministic`).
-/

namespace Toy.Hoare

/-- Total-correctness validity of `[P] c [Q]`: every state satisfying `P` has a terminating run
ending in `Q` (by determinism, the unique run). -/
def TValid (P : Assn) (c : Com) (Q : Assn) : Prop :=
  ∀ s, P s → ∃ s', Exec c s s' ∧ Q s'

/-- Total correctness implies partial correctness (by determinism of `Exec`). -/
theorem TValid.valid {P : Assn} {c : Com} {Q : Assn} (h : TValid P c Q) : Valid P c Q := by
  intro s s' hP hx
  obtain ⟨s'', hx', hQ⟩ := h s hP
  rwa [Exec.deterministic hx hx']

/-- Total-correctness derivability with integer-valued loop variants. The while rule takes an
invariant `I`, a variant `V : Store → Int`, a derivation (for every `n`) that one iteration from a
state with `I`, guard true and `V = n` re-establishes `I` with `V < n`, and — only when
`requireBound = true` — the side condition that `V ≥ 0` whenever `I` and the guard hold. -/
inductive TDeriv (requireBound : Bool) : Assn → Com → Assn → Prop where
  | skip (P : Assn) : TDeriv requireBound P .skip P
  | assign (x : Nat) (e : AExp) (Q : Assn) :
      TDeriv requireBound (fun s => Q (upd s x (e.eval s))) (.assign x e) Q
  | seq {P R Q : Assn} {c₁ c₂ : Com} :
      TDeriv requireBound P c₁ R → TDeriv requireBound R c₂ Q →
      TDeriv requireBound P (.seq c₁ c₂) Q
  | cond {P Q : Assn} {b : BExp} {c₁ c₂ : Com} :
      TDeriv requireBound (fun s => P s ∧ b.eval s = true) c₁ Q →
      TDeriv requireBound (fun s => P s ∧ b.eval s = false) c₂ Q →
      TDeriv requireBound P (.cond b c₁ c₂) Q
  | whileDo {I : Assn} {b : BExp} {c : Com} (V : Store → Int) :
      (∀ n : Int, TDeriv requireBound (fun s => I s ∧ b.eval s = true ∧ V s = n) c
        (fun s => I s ∧ V s < n)) →
      (requireBound = true → ∀ s, I s → b.eval s = true → 0 ≤ V s) →
      TDeriv requireBound I (.whileDo b c) (fun s => I s ∧ b.eval s = false)
  | conseq {P P' Q Q' : Assn} {c : Com} :
      (∀ s, P s → P' s) → TDeriv requireBound P' c Q' → (∀ s, Q' s → Q s) →
      TDeriv requireBound P c Q

/-- **Total-correctness soundness with bounded variants.** Every triple derivable in the system
whose while rule requires the integer variant to be nonnegative under the invariant and guard
is valid in total correctness. -/
theorem total_sound_of_bounded_variant {P : Assn} {c : Com} {Q : Assn}
    (h : TDeriv true P c Q) : TValid P c Q := by
  induction h with
  | skip P => intro s hP; exact ⟨s, Exec.skip s, hP⟩
  | assign x e Q => intro s hP; exact ⟨_, Exec.assign x e s, hP⟩
  | seq _ _ ih₁ ih₂ =>
    intro s hP
    obtain ⟨s₁, hx₁, hR⟩ := ih₁ s hP
    obtain ⟨s₂, hx₂, hQ⟩ := ih₂ s₁ hR
    exact ⟨s₂, Exec.seq hx₁ hx₂, hQ⟩
  | cond _ _ ih₁ ih₂ =>
    intro s hP
    cases hb : _root_.Toy.Hoare.BExp.eval _ s with
    | true =>
      obtain ⟨s', hx, hQ⟩ := ih₁ s ⟨hP, hb⟩
      exact ⟨s', Exec.condTrue hb hx, hQ⟩
    | false =>
      obtain ⟨s', hx, hQ⟩ := ih₂ s ⟨hP, hb⟩
      exact ⟨s', Exec.condFalse hb hx, hQ⟩
  | @whileDo I b c V _ hbnd ih =>
    have key : ∀ m : Nat, ∀ s, I s → V s < m →
        ∃ s', Exec (.whileDo b c) s s' ∧ I s' ∧ b.eval s' = false := by
      intro m
      induction m with
      | zero =>
        intro s hI hV
        cases hb : b.eval s with
        | false => exact ⟨s, Exec.whileFalse hb, hI, hb⟩
        | true => have := hbnd rfl s hI hb; omega
      | succ m ihm =>
        intro s hI hV
        cases hb : b.eval s with
        | false => exact ⟨s, Exec.whileFalse hb, hI, hb⟩
        | true =>
          obtain ⟨s₁, hx₁, hI₁, hV₁⟩ := ih (V s) s ⟨hI, hb, rfl⟩
          obtain ⟨s', hx', hI', hb'⟩ := ihm s₁ hI₁ (by omega)
          exact ⟨s', Exec.whileTrue hb hx₁ hx', hI', hb'⟩
    intro s hI
    exact key ((V s).toNat + 1) s hI (by omega)
  | conseq hP _ hQ ih =>
    intro s h
    obtain ⟨s', hx, hQ'⟩ := ih s (hP s h)
    exact ⟨s', hx, hQ _ hQ'⟩

/-- Body `x := x - 1`. -/
def downBody : Com := .assign 0 (.sub (.var 0) (.lit 1))

/-- `while true do x := x - 1`: the variant `x` decreases on every iteration but is unbounded
below, and the loop diverges. -/
def downLoop : Com := .whileDo .tt downBody

/-- A loop whose guard is constantly `true` has no terminating run. -/
theorem exec_while_tt_diverges {c : Com} {s s' : Store} : ¬ Exec (.whileDo .tt c) s s' := by
  intro hx
  generalize hw : Com.whileDo .tt c = w at hx
  induction hx with
  | whileFalse hb => cases hw; cases hb
  | whileTrue _ _ _ _ ih₂ => exact ih₂ hw
  | skip => cases hw
  | assign => cases hw
  | seq => cases hw
  | condTrue => cases hw
  | condFalse => cases hw

/-- **Counterexample (variant must be bounded below).** For `while true do x := x - 1` with
invariant `true` and variant `x`: the per-iteration premise of the while rule holds (one iteration
from a state with `x = n` ends with `x < n`), the lower-bound premise `0 ≤ x` fails, so in the
system without that premise the rule yields `[true] while true do x := x - 1 [true]`; but the
loop has no terminating run from any state, so this triple is not valid in total correctness. -/
theorem unbounded_variant_unsound :
    (∀ n : Int, TDeriv false (fun s => True ∧ BExp.tt.eval s = true ∧ s 0 = n) downBody
      (fun s => True ∧ s 0 < n)) ∧
    ¬ (∀ s : Store, True → BExp.tt.eval s = true → 0 ≤ s 0) ∧
    TDeriv false (fun _ => True) downLoop (fun _ => True) ∧
    (∀ s s' : Store, ¬ Exec downLoop s s') ∧
    ¬ TValid (fun _ => True) downLoop (fun _ => True) := by
  have hstep : ∀ n : Int, TDeriv false (fun s => True ∧ BExp.tt.eval s = true ∧ s 0 = n) downBody
      (fun s => True ∧ s 0 < n) := by
    intro n
    refine TDeriv.conseq (fun s hs => ?_) (TDeriv.assign 0 _ (fun s => True ∧ s 0 < n))
      (fun _ h => h)
    obtain ⟨_, _, hn⟩ := hs
    refine ⟨trivial, ?_⟩
    simp only [upd_same, AExp.eval]
    omega
  have hdiv : ∀ s s' : Store, ¬ Exec downLoop s s' := fun _ _ => exec_while_tt_diverges
  refine ⟨hstep, fun h => ?_, ?_, hdiv, fun h => ?_⟩
  · have := h (fun _ => -1) trivial rfl
    omega
  · exact TDeriv.conseq (fun _ h => h)
      (TDeriv.whileDo (I := fun _ => True) (fun s => s 0) hstep (fun h => by cases h))
      (fun _ _ => trivial)
  · obtain ⟨s', hx, _⟩ := h (fun _ => 0) trivial
    exact hdiv _ _ hx

end Toy.Hoare
