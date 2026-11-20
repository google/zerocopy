import ToyGhost.Ghost

/-!
# Behavioural relations: refinement, triples, noninterference

All relations compare *real-observable* behaviours (`RBehaviour`): the final real
store, failure, or divergence. Ghost values are never observed.
-/

namespace Toy.Ghost

/-- Bottom set "abort": failure and divergence (the refinement-calculus `abort`). -/
def abortBot (b : RBehaviour) : Prop := b = .fail ∨ b = .diverge

/-- Bottom set containing only failure. -/
def failBot (b : RBehaviour) : Prop := b = .fail

/-- Bottom set containing only divergence. -/
def divBot (b : RBehaviour) : Prop := b = .diverge

/-- `RefinesUpTo Bot A σ C τ` ("`C` from `τ` refines `A` from `σ` up to `Bot`"):
either `A` from `σ` has a behaviour in `Bot` (which any behaviour refines), or
every real behaviour of `C` from `τ` is a real behaviour of `A` from `σ`.

`A` is the abstract (original) program, `C` the concrete (erased) one. With
`Bot = abortBot` this is the total-correctness refinement order of the refinement
calculus (Back and von Wright, *Refinement Calculus*, 1998), in which failure and
divergence are both bottom. In this deterministic language the `∀ b` clause says
that the unique behaviour of `C` equals that of `A`. -/
def RefinesUpTo (Bot : RBehaviour → Prop) (A : Stmt) (σ : Store) (C : Stmt) (τ : Store) : Prop :=
  (∃ a, Bot a ∧ RBehaves A σ a) ∨ ∀ b, RBehaves C τ b → RBehaves A σ b

/-- Partial correctness *with safety* (semantic validity, not derivability in a
proof system): from every state whose real part satisfies `Pre`, `s` does not fail
(no assertion, real or ghost, is violated), and if it terminates normally its final
real part satisfies `Post`. Divergence satisfies every triple; failure satisfies
none. `Pre` and `Post` are predicates on real stores, so the triple is "about real
variables" and the initial ghost values are universally quantified. Compare
`WeakPartialTriple`, in which failure is also vacuous. -/
def SafePartialTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ¬ Fails s σ ∧ ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')

/-- Weak (classical) partial correctness: from every state whose real part satisfies
`Pre`, if `s` terminates normally its final real part satisfies `Post`. Both
divergence and failure satisfy every weak triple. -/
def WeakPartialTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ∀ σ', Behaves s σ (.term σ') → Post (realPart σ')

/-- Total correctness (semantic validity): from every state whose real part
satisfies `Pre`, `s` terminates normally in a state whose real part satisfies
`Post`. -/
def TotalTriple (Pre : RStore → Prop) (s : Stmt) (Post : RStore → Prop) : Prop :=
  ∀ σ, Pre (realPart σ) → ∃ σ', Behaves s σ (.term σ') ∧ Post (realPart σ')

/-- Termination-sensitive noninterference from ghost to real: the real-observable
behaviour of `P` (final real store, failure, divergence) does not depend on the
initial values of ghost variables. -/
def GhostToRealNI (P : Stmt) : Prop :=
  ∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves P τ b

/-- Abort-insensitive noninterference from ghost to real (the analogue of
termination-insensitive noninterference in a language that can also fail):
whenever two runs from states with equal real parts both terminate normally, their
final real parts agree. Neither failure nor divergence is compared, so both the
termination channel and the failure channel are ignored. -/
def GhostToRealNI_AbortInsensitive (P : Stmt) : Prop :=
  ∀ σ τ σ' τ', realPart σ = realPart τ → Behaves P σ (.term σ') → Behaves P τ (.term τ') →
    realPart σ' = realPart τ'

/-- `ErasureExact P`: for all initial states `σ`, `τ` with the same real part, the
real-observable behaviours of `P` from `σ` and of `erase P` from `τ` coincide. The
erased program starts from an *arbitrary* ghost part, modelling that ghost
variables no longer exist after erasure. -/
def ErasureExact (P : Stmt) : Prop :=
  ∀ σ τ, realPart σ = realPart τ → ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b

/-- `ErasureAgrees P`: `P` and `erase P` have the same real-observable behaviour
when started from the *same* full store. -/
def ErasureAgrees (P : Stmt) : Prop :=
  ∀ σ b, RBehaves P σ b ↔ RBehaves (erase P) σ b

/-! ## Unfolding lemmas for refinement (fully proved) -/

/-- In this deterministic language, refinement up to `abortBot` is exactly
preservation of normal termination together with the final real store. -/
theorem refinesUpTo_abortBot_iff {A C : Stmt} {σ τ : Store} :
    RefinesUpTo abortBot A σ C τ ↔
      ∀ σ', Behaves A σ (.term σ') → ∃ τ', Behaves C τ (.term τ') ∧ realPart τ' = realPart σ' := by
  constructor
  · intro h σ' hA
    obtain ⟨b, hb⟩ := Behaves.exists C τ
    rcases h with ⟨a, ha, hAa⟩ | h
    · have := RBehaves.unique hAa (RBehaves.of_behaves (b := .term σ') hA)
      rcases ha with rfl | rfl <;> cases this
    · have h1 := h b.real (RBehaves.of_behaves hb)
      have h2 := RBehaves.unique h1 (RBehaves.of_behaves (b := .term σ') hA)
      cases b with
      | term τ' =>
        refine ⟨τ', hb, ?_⟩
        simp only [Behaviour.real, RBehaviour.term.injEq] at h2
        exact h2
      | fail => cases h2
      | diverge => cases h2
  · intro h
    obtain ⟨a, ha⟩ := Behaves.exists A σ
    cases a with
    | term σ' =>
      right
      obtain ⟨τ', hC, hr⟩ := h σ' ha
      intro b hb
      rw [(RBehaves.iff_of_behaves hC b).1 hb, Behaviour.real, hr]
      exact RBehaves.of_behaves (b := .term σ') ha
    | fail => exact Or.inl ⟨.fail, Or.inl rfl, RBehaves.of_behaves ha⟩
    | diverge => exact Or.inl ⟨.diverge, Or.inr rfl, RBehaves.of_behaves ha⟩

/-- Refinement is monotone in the bottom set. -/
theorem RefinesUpTo.mono {B B' : RBehaviour → Prop} (hBB' : ∀ b, B b → B' b)
    {A C : Stmt} {σ τ : Store} (h : RefinesUpTo B A σ C τ) : RefinesUpTo B' A σ C τ := by
  rcases h with ⟨a, ha, hA⟩ | h
  · exact Or.inl ⟨a, hBB' a ha, hA⟩
  · exact Or.inr h

/-- Equality of real behaviours implies refinement up to any bottom set. -/
theorem refinesUpTo_of_rbehaves_iff {B : RBehaviour → Prop} {A C : Stmt} {σ τ : Store}
    (h : ∀ b, RBehaves A σ b ↔ RBehaves C τ b) : RefinesUpTo B A σ C τ :=
  Or.inr fun b hb => (h b).2 hb

end Toy.Ghost
