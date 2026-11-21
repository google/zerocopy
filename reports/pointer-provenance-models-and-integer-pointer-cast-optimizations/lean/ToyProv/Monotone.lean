import ToyProv.Basic

/-!
# Provenance monotonicity of byte decoding (R7b)

The ordering results (R6a), the cast fold in `strict` (R6g) and the exposed-model fold (R2b) all
rest on one property of the semantics: giving a pointer *more* provenance (replacing `none` by
`some id`) never introduces UB. At the byte level this requires that decoding two pointer
fragments does not depend on whether their provenances agree. This module defines the
information order on provenances, pointers and abstract bytes and proves that `decodeInt` and
`decodePtr` are monotone in it.
-/

namespace Toy.Prov

/-- Information order on provenances: `none` is below every provenance, `some id` only below
itself. -/
def ProvLE (a b : Option AllocId) : Prop := a = none ∨ a = b

/-- Information order on pointers: same address, provenance below. -/
def PtrLE (p q : Ptr) : Prop := p.addr = q.addr ∧ ProvLE p.prov q.prov

/-- Information order on abstract bytes: identical, except that a pointer fragment may carry a
pointer with more provenance. -/
def AByteLE : AByte → AByte → Prop
  | .uninit, .uninit => True
  | .intFrag n i, .intFrag n' i' => n = n' ∧ i = i'
  | .ptrFrag p i, .ptrFrag q i' => PtrLE p q ∧ i = i'
  | _, _ => False

theorem ProvLE.refl (a : Option AllocId) : ProvLE a a := Or.inr rfl

theorem AByteLE.refl (b : AByte) : AByteLE b b := by
  cases b <;> simp [AByteLE, PtrLE, ProvLE.refl]

/-- Positive example: a provenance-less fragment is below the same fragment with provenance. -/
theorem ex_AByteLE_pos : AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 1) := by
  simp [AByteLE, PtrLE, ProvLE]

/-- Negative examples: provenance cannot be changed or dropped, and addresses must agree. -/
theorem ex_AByteLE_neg :
    ¬ AByteLE (.ptrFrag ⟨some 0, 16⟩ 1) (.ptrFrag ⟨some 1, 16⟩ 1) ∧
      ¬ AByteLE (.ptrFrag ⟨some 0, 16⟩ 1) (.ptrFrag ⟨none, 16⟩ 1) ∧
      ¬ AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨none, 18⟩ 1) := by
  simp [AByteLE, PtrLE, ProvLE]

theorem mergeProv_mono {a a' b b' : Option AllocId} (ha : ProvLE a a') (hb : ProvLE b b') :
    ProvLE (mergeProv a b) (mergeProv a' b') := by
  unfold ProvLE at *
  rcases ha with rfl | rfl
  · left; unfold mergeProv; split <;> simp_all
  · rcases hb with rfl | rfl
    · left; unfold mergeProv; split <;> simp_all
    · right; rfl

theorem mem_provsOf_mono {a a' b b' : Option AllocId} (ha : ProvLE a a') (hb : ProvLE b b')
    {x : AllocId} (hx : x ∈ provsOf a b) : x ∈ provsOf a' b' := by
  have hsub : x ∈ a.toList ++ b.toList := by
    unfold provsOf at hx; split at hx <;> simp_all
  have hsub' : x ∈ a'.toList ++ b'.toList := by
    unfold ProvLE at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  unfold provsOf; split
  · rename_i h; subst h; simpa using hsub'
  · exact hsub'

theorem decodeInt_ptrFrag_eq (p p' : Ptr) (i j : Nat) :
    decodeInt (.ptrFrag p i) (.ptrFrag p' j) =
      if i = 0 ∧ j = 1 ∧ p.addr = p'.addr then some (p.addr, provsOf p.prov p'.prov) else none := by
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [decodeInt]

theorem decodeInt_intFrag_eq (n n' i j : Nat) :
    decodeInt (.intFrag n i) (.intFrag n' j) =
      if i = 0 ∧ j = 1 ∧ n = n' then some (n, []) else none := by
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [decodeInt]

theorem decodePtr_ptrFrag_eq (p p' : Ptr) (i j : Nat) :
    decodePtr (.ptrFrag p i) (.ptrFrag p' j) =
      if i = 0 ∧ j = 1 ∧ p.addr = p'.addr then some (.inl ⟨mergeProv p.prov p'.prov, p.addr⟩)
      else none := by
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [decodePtr]

theorem decodePtr_intFrag_eq (n n' i j : Nat) :
    decodePtr (.intFrag n i) (.intFrag n' j) =
      if i = 0 ∧ j = 1 ∧ n = n' then some (.inr n) else none := by
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [decodePtr]

/-- **R7b (integer decoding).** If each byte is below the corresponding byte of a second pair
(the second pair may carry more provenance), a defined integer decoding of the first pair stays
defined on the second, with the same integer and a superset of exposed provenances. -/
theorem decodeInt_mono {b₀ b₁ c₀ c₁ : AByte} (h₀ : AByteLE b₀ c₀) (h₁ : AByteLE b₁ c₁)
    {n : Nat} {ps : List AllocId} (h : decodeInt b₀ b₁ = some (n, ps)) :
    ∃ ps', decodeInt c₀ c₁ = some (n, ps') ∧ ∀ x ∈ ps, x ∈ ps' := by
  cases b₀ <;> cases c₀ <;> simp only [AByteLE] at h₀ <;>
    cases b₁ <;> cases c₁ <;> simp only [AByteLE] at h₁ <;>
    first | (simp [decodeInt] at h; done) | skip
  · rename_i n₀ i₀ n₀' i₀' n₁ i₁ n₁' i₁'
    obtain ⟨rfl, rfl⟩ := h₀
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨ps, h, fun x hx => hx⟩
  · rename_i p₀ i₀ q₀ i₀' p₁ i₁ q₁ i₁'
    obtain ⟨⟨ha₀, hp₀⟩, rfl⟩ := h₀
    obtain ⟨⟨ha₁, hp₁⟩, rfl⟩ := h₁
    rw [decodeInt_ptrFrag_eq] at h ⊢
    split at h
    · rename_i hc
      obtain ⟨hi₀, hi₁, haddr⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨provsOf q₀.prov q₁.prov, ?_, fun x hx => mem_provsOf_mono hp₀ hp₁ hx⟩
      subst hi₀ hi₁
      simp [← ha₀, ← ha₁, haddr]
    · simp at h

/-- **R7b (pointer decoding).** Under the same hypotheses, a defined pointer decoding stays
defined: integer fragments give the same bare address, and pointer fragments give a pointer with
the same address and at least as much provenance. -/
theorem decodePtr_mono {b₀ b₁ c₀ c₁ : AByte} (h₀ : AByteLE b₀ c₀) (h₁ : AByteLE b₁ c₁) :
    (∀ n, decodePtr b₀ b₁ = some (.inr n) → decodePtr c₀ c₁ = some (.inr n)) ∧
      (∀ q, decodePtr b₀ b₁ = some (.inl q) →
        ∃ q', decodePtr c₀ c₁ = some (.inl q') ∧ PtrLE q q') := by
  cases b₀ <;> cases c₀ <;> simp only [AByteLE] at h₀ <;>
    cases b₁ <;> cases c₁ <;> simp only [AByteLE] at h₁ <;>
    first | (simp [decodePtr]; done) | skip
  · rename_i n₀ i₀ n₀' i₀' n₁ i₁ n₁' i₁'
    obtain ⟨rfl, rfl⟩ := h₀
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨fun _ h => h, fun _ h => ⟨_, h, rfl, ProvLE.refl _⟩⟩
  · rename_i p₀ i₀ q₀ i₀' p₁ i₁ q₁ i₁'
    obtain ⟨⟨ha₀, hp₀⟩, rfl⟩ := h₀
    obtain ⟨⟨ha₁, hp₁⟩, rfl⟩ := h₁
    rw [decodePtr_ptrFrag_eq, decodePtr_ptrFrag_eq]
    refine ⟨fun n h => ?_, fun q h => ?_⟩
    · split at h <;> simp at h
    · split at h
      · rename_i hc
        obtain ⟨hi₀, hi₁, haddr⟩ := hc
        simp only [Option.some.injEq, Sum.inl.injEq] at h
        subst h
        refine ⟨⟨mergeProv q₀.prov q₁.prov, q₀.addr⟩, ?_, ha₀, mergeProv_mono hp₀ hp₁⟩
        subst hi₀ hi₁
        simp [← ha₀, ← ha₁, haddr]
      · simp at h

/-- **R7b, `h₀` needed.** If the first byte of the second pair is not above the first byte of the
first pair (here its address differs), a defined decoding can become UB. -/
theorem decode_mono_h₀_needed :
    AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨none, 16⟩ 1) ∧
      ¬ AByteLE (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 18⟩ 0) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodeInt (.ptrFrag ⟨none, 18⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = none ∧
      decodePtr (.ptrFrag ⟨none, 18⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = none := by
  refine ⟨AByteLE.refl _, ?_, by decide, by decide, by decide⟩
  simp [AByteLE, PtrLE]

/-- **R7b, `h₁` needed.** Symmetric, for the second byte. -/
theorem decode_mono_h₁_needed :
    AByteLE (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 0) ∧
      ¬ AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨none, 18⟩ 1) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 18⟩ 1) = none ∧
      decodePtr (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 18⟩ 1) = none := by
  refine ⟨AByteLE.refl _, ?_, by decide, by decide, by decide⟩
  simp [AByteLE, PtrLE]

/-- **R7b (integer decoding), `h` needed.** Both byte hypotheses hold (the second pair gains a
provenance), but the first pair's integer decoding is not defined (the fragments carry different
addresses), and neither is the second pair's: the conclusion fails for `n = 16`, `ps = []`. -/
theorem decodeInt_mono_h_needed :
    AByteLE (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 0) ∧
      AByteLE (.ptrFrag ⟨none, 18⟩ 1) (.ptrFrag ⟨some 0, 18⟩ 1) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 18⟩ 1) ≠ some (16, []) ∧
      ¬ ∃ ps', decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 18⟩ 1) = some (16, ps') ∧
        ∀ x ∈ ([] : List AllocId), x ∈ ps' := by
  refine ⟨AByteLE.refl _, ⟨⟨rfl, Or.inl rfl⟩, rfl⟩, by decide, ?_⟩
  rintro ⟨ps', h, -⟩
  have hnone : decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 18⟩ 1) = none := by decide
  rw [hnone] at h
  cases h

/-- **R7b non-vacuity.** Both hypotheses hold with the second pair strictly more defined (one
fragment gains provenance), and both decodings of the first pair are defined. -/
theorem decode_mono_nonvacuous :
    AByteLE (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 0) ∧
      AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 1) ∧
      decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodePtr (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (.inl ⟨none, 16⟩) :=
  ⟨AByteLE.refl _, ex_AByteLE_pos, by decide, by decide⟩

/-- Mixed provenance at the same address: both decodings are defined (positive control for the
counterexamples in `ToyProv.EqProvDecode`). -/
theorem decode_mixed_provenance_defined :
    decodeInt (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = some (16, [0]) ∧
      decodePtr (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = some (.inl ⟨none, 16⟩) := by
  decide

end Toy.Prov
