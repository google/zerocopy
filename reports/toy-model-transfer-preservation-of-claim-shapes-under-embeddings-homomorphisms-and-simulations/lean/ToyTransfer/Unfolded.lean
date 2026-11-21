import ToyTransfer.Disclaimer
import ToyTransfer.Simulation

/-!
# Unfolded renderings of key definitions

Each lemma states a definition in unfolded form; the unfolded right-hand sides are the
renderings quoted in the documentation.
-/

namespace Toy.Transfer

theorem preserves_fwd_iff (c : Cls) (k : MapKind) :
    Preserves c k .fwd ↔
      ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
        ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
          Sat A φ e → Sat B φ (h ∘ e) :=
  Iff.rfl

theorem preserves_bwd_iff (c : Cls) (k : MapKind) :
    Preserves c k .bwd ↔
      ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
        ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
          Sat B φ (h ∘ e) → Sat A φ e :=
  Iff.rfl

theorem isEmbedding_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsEmbedding h ↔
      (∀ a a', h a = h a' → a = a') ∧ (∀ a b, A.R a b → B.R (h a) (h b)) ∧
      (∀ a, A.P a → B.P (h a)) ∧ (∀ a b, B.R (h a) (h b) → A.R a b) ∧
      (∀ a, B.P (h a) → A.P a) :=
  ⟨fun ⟨i, a, b, c, d⟩ => ⟨fun _ _ e => i e, a, b, c, d⟩,
    fun ⟨i, a, b, c, d⟩ => ⟨fun _ _ e => i _ _ e, a, b, c, d⟩⟩

theorem isSurjHom_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsSurjHom h ↔
      (∀ b, ∃ a, h a = b) ∧ (∀ a b, A.R a b → B.R (h a) (h b)) ∧ (∀ a, A.P a → B.P (h a)) :=
  ⟨fun ⟨s, a, b⟩ => ⟨s, a, b⟩, fun ⟨s, a, b⟩ => ⟨s, a, b⟩⟩

/-- The licensed cells of the transfer table, listed. -/
theorem licensedB_eq_true_iff (c : Cls) (k : MapKind) (d : Dir) :
    licensedB c k d = true ↔
      (c = .qf ∧ k = .emb) ∨ (c = .univ ∧ k = .emb ∧ d = .bwd) ∨
      (c = .exist ∧ k = .emb ∧ d = .fwd) ∨ (c = .posExist ∧ d = .fwd) ∨
      (c = .pos ∧ k = .surj ∧ d = .fwd) := by
  cases c <;> cases k <;> cases d <;> decide

theorem allRunsFinite_iff (T : TS) :
    AllRunsFinite T ↔ ∀ s, Reach T s → Acc (fun y x => T.step x y) s :=
  Iff.rfl

theorem simStepWF_iff (C A : TS) (S : C.St → A.St → Prop) {W : Type} (lt : W → W → Prop)
    (μ : C.St → A.St → W) :
    SimStepWF C A S lt μ ↔
      ∀ c c' a, C.step c c' → S c a →
        (∃ a', A.step a a' ∧ S c' a') ∨ (S c' a ∧ lt (μ c' a) (μ c a)) :=
  Iff.rfl

theorem bothOutcomesNonIso_fwd_iff (c : Cls) (k : MapKind) :
    BothOutcomesNonIso c k .fwd ↔
      ∃ (A : Str) (n : Nat) (φ : Fml n) (e : Fin n → A.carrier), c.Mem φ ∧ Sat A φ e ∧
        (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ Sat B φ (h ∘ e)) ∧
        (∃ (B : Str) (h : A.carrier → B.carrier), k.Holds h ∧ ¬ IsIso h ∧ ¬ Sat B φ (h ∘ e)) :=
  Iff.rfl

theorem isIso_iff {A B : Str} (h : A.carrier → B.carrier) :
    IsIso h ↔
      (∀ a a', h a = h a' → a = a') ∧ (∀ b, ∃ a, h a = b) ∧
      (∀ a b, A.R a b → B.R (h a) (h b)) ∧ (∀ a, A.P a → B.P (h a)) ∧
      (∀ a b, B.R (h a) (h b) → A.R a b) ∧ (∀ a, B.P (h a) → A.P a) :=
  ⟨fun ⟨i, s, a, b, c, d⟩ => ⟨fun _ _ e => i e, s, a, b, c, d⟩,
    fun ⟨i, s, a, b, c, d⟩ => ⟨fun _ _ e => i _ _ e, s, a, b, c, d⟩⟩

end Toy.Transfer
