/-
Toy.Float.Lemmas
================

Fully proved structural lemmas about the rewrite framework: with no
permissions the only permitted form of an expression is itself; validity is
monotone in the flag set; and the "exact flag set" principle that turns a
sufficiency check plus one counterexample per flag into a characterization of
all sufficient flag sets.
-/
import Toy.Float.Enum

namespace Toy.Float

variable {f : Fmt} {n : Nat}

/-- The five flags, for indexing `Flags`. -/
inductive Flag where
  | nnan | ninf | nsz | reassoc | contract
  deriving DecidableEq, Repr

namespace Flags

/-- Whether flag `fl` is in the set. -/
def has (S : Flags) : Flag → Bool
  | .nnan => S.nnan
  | .ninf => S.ninf
  | .nsz => S.nsz
  | .reassoc => S.reassoc
  | .contract => S.contract

/-- All flags except `fl`. -/
def allBut : Flag → Flags
  | .nnan => { all with nnan := false }
  | .ninf => { all with ninf := false }
  | .nsz => { all with nsz := false }
  | .reassoc => { all with reassoc := false }
  | .contract => { all with contract := false }

instance (S T : Flags) : Decidable (Sub S T) := by unfold Sub; infer_instance

theorem sub_refl (S : Flags) : Sub S S :=
  ⟨id, id, id, id, id⟩

/-- `S ⊆ T` iff every flag of `S` is in `T`. -/
theorem sub_iff_has (S T : Flags) : Sub S T ↔ ∀ fl, S.has fl = true → T.has fl = true := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩ fl
    cases fl <;> simp only [has] <;> assumption
  · intro h
    exact ⟨h .nnan, h .ninf, h .nsz, h .reassoc, h .contract⟩

/-- If `T` lacks flag `fl`, then `T ⊆ allBut fl`. -/
theorem sub_allBut_of_not_has (T : Flags) (fl : Flag) (h : T.has fl = false) :
    Sub T (allBut fl) := by
  obtain ⟨a, b, c, d, e⟩ := T
  cases fl <;> simp_all [Sub, has, allBut, all]

end Flags

namespace Expr

/-- With no permissions, the only permitted form of `e` is `e` itself. -/
theorem variants_noPerm (e : Expr f n) : e.variants {} = [e] := by
  induction e with
  | var i => rfl
  | lit c => rfl
  | neg a ih => simp [variants, ih]
  | add a b iha ihb => simp [variants, iha, ihb]
  | sub a b iha ihb => simp [variants, iha, ihb]
  | mul a b iha ihb => simp [variants, iha, ihb]
  | fma a b c iha ihb ihc => simp [variants, iha, ihb, ihc]

/-- More permissions allow more forms. -/
theorem variants_mono {S T : Flags} (hST : Flags.Sub S T) (e : Expr f n) :
    ∀ v, v ∈ e.variants S → v ∈ e.variants T := by
  obtain ⟨_, _, _, hr, hc⟩ := hST
  induction e with
  | var i => exact fun v h => h
  | lit c => exact fun v h => h
  | neg a ih =>
    intro v hv
    simp only [variants, List.mem_map] at hv ⊢
    obtain ⟨a', ha', rfl⟩ := hv
    exact ⟨a', ih a' ha', rfl⟩
  | add a b iha ihb =>
    intro v hv
    simp only [variants, List.mem_flatMap, List.mem_cons, List.mem_append] at hv ⊢
    obtain ⟨a', ha', b', hb', hv⟩ := hv
    refine ⟨a', iha a' ha', b', ihb b' hb', ?_⟩
    rcases hv with hv | hv | hv
    · exact Or.inl hv
    · by_cases h : S.reassoc = true
      · simp only [h, ite_true] at hv; simp only [hr h, ite_true]; exact Or.inr (Or.inl hv)
      · simp only [h] at hv; simp at hv
    · by_cases h : S.contract = true
      · simp only [h, ite_true] at hv; simp only [hc h, ite_true]; exact Or.inr (Or.inr hv)
      · simp only [h] at hv; simp at hv
  | sub a b iha ihb =>
    intro v hv
    simp only [variants, List.mem_flatMap, List.mem_cons] at hv ⊢
    obtain ⟨a', ha', b', hb', hv⟩ := hv
    refine ⟨a', iha a' ha', b', ihb b' hb', ?_⟩
    rcases hv with hv | hv
    · exact Or.inl hv
    · by_cases h : S.contract = true
      · simp only [h, ite_true] at hv; simp only [hc h, ite_true]; exact Or.inr hv
      · simp only [h] at hv; simp at hv
  | mul a b iha ihb =>
    intro v hv
    simp only [variants, List.mem_flatMap, List.mem_cons] at hv ⊢
    obtain ⟨a', ha', b', hb', hv⟩ := hv
    refine ⟨a', iha a' ha', b', ihb b' hb', ?_⟩
    rcases hv with hv | hv
    · exact Or.inl hv
    · by_cases h : S.reassoc = true
      · simp only [h, ite_true] at hv; simp only [hr h, ite_true]; exact Or.inr hv
      · simp only [h] at hv; simp at hv
  | fma a b c iha ihb ihc =>
    intro v hv
    simp only [variants, List.mem_flatMap, List.mem_map] at hv ⊢
    obtain ⟨a', ha', b', hb', c', hc', rfl⟩ := hv
    exact ⟨a', iha a' ha', b', ihb b' hb', c', ihc c' hc', rfl⟩

end Expr

/-- Flag-free validity is bitwise equality of the two sides on every input. -/
theorem valid_iff_forall_eq (r : Rewrite f n) :
    Valid r ↔ ∀ env, r.rhs.eval env = r.lhs.eval env := by
  unfold Valid ValidMod Rel
  simp only [Expr.variants_noPerm, List.mem_singleton, exists_eq_left]
  constructor
  · intro h env
    exact h env (fun v _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
  · intro h env _
    simpa using h env

theorem admissible_anti {S T : Flags} (hST : Flags.Sub S T) {e : Expr f n}
    {env : Fin n → FP f} (h : Admissible T e env) : Admissible S e env := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  exact ⟨fun hs => h1 (hST.1 hs), fun hs => h2 (hST.2.1 hs)⟩

theorem rel_mono {S T : Flags} (hST : Flags.Sub S T) {x y : FP f} (h : Rel S x y) :
    Rel T x y := by
  unfold Rel at *
  by_cases hs : S.nsz = true
  · simp only [hs, ite_true] at h
    simp only [hST.2.2.1 hs, ite_true]; exact h
  · simp only [hs] at h
    simp only [Bool.false_eq_true, ite_false] at h
    subst h
    by_cases ht : T.nsz = true
    · simp only [ht, ite_true]; rfl
    · simp only [ht]; simp

/-- Validity is monotone in the flag set: a rewrite valid modulo `S` is valid
modulo every `T ⊇ S`. -/
theorem validMod_mono {S T : Flags} (hST : Flags.Sub S T) {r : Rewrite f n}
    (h : ValidMod S r) : ValidMod T r := by
  intro env hT
  obtain ⟨v, hv, hrel⟩ := h env (admissible_anti hST hT)
  exact ⟨v, Expr.variants_mono hST _ v hv, rel_mono hST hrel⟩

/-- Exact flag set principle: if `r` is valid modulo `S`, and for every flag
`fl ∈ S` it is invalid modulo all flags except `fl`, then the flag sets
modulo which `r` is valid are exactly the supersets of `S`. -/
theorem validMod_iff_sub_of_minimal {S : Flags} {r : Rewrite f n}
    (hS : ValidMod S r) (hmin : ∀ fl, S.has fl = true → ¬ ValidMod (Flags.allBut fl) r)
    (T : Flags) : ValidMod T r ↔ Flags.Sub S T := by
  constructor
  · intro hT
    rw [Flags.sub_iff_has]
    intro fl hfl
    cases hTfl : T.has fl
    · exact absurd (validMod_mono (Flags.sub_allBut_of_not_has T fl hTfl) hT) (hmin fl hfl)
    · rfl
  · intro hST
    exact validMod_mono hST hS

end Toy.Float
