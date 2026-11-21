import ToyTransfer.Basic

/-!
# Maps between structures, claim classes, and the transfer predicate

Each law of a map is a separate named `Prop`, so that every theorem names exactly
the laws it uses. The four map kinds of the transfer matrix are bundles of laws.
-/

namespace Toy.Transfer

section Laws
variable {A B : Str}

/-- `h` preserves `R`: related elements are mapped to related elements. -/
def PreservesR (h : A.carrier → B.carrier) : Prop := ∀ a b, A.R a b → B.R (h a) (h b)

/-- `h` preserves `P`. -/
def PreservesP (h : A.carrier → B.carrier) : Prop := ∀ a, A.P a → B.P (h a)

/-- `h` reflects `R`: if the images are related, so are the arguments. -/
def ReflectsR (h : A.carrier → B.carrier) : Prop := ∀ a b, B.R (h a) (h b) → A.R a b

/-- `h` reflects `P`. -/
def ReflectsP (h : A.carrier → B.carrier) : Prop := ∀ a, B.P (h a) → A.P a

/-- Homomorphism: preserves `R` and `P`. (Every map preserves equality.) -/
structure IsHom (h : A.carrier → B.carrier) : Prop where
  presR : PreservesR h
  presP : PreservesP h

/-- Strong homomorphism: preserves and reflects `R` and `P`; neither injectivity nor
surjectivity is required. (This is the relational convention in which reflection is
part of the definition.) Equality is not reflected unless `h` is injective, which is
why strong homomorphisms preserve the same classes as homomorphisms here
(`neq_not_preserved_by_strongHom`, `eq_not_reflected_by_strongHom`); on equality-free
quantifier-free formulas they preserve and reflect satisfaction
(`qf_sat_iff_of_strongHom_of_eqFree`). -/
structure IsStrongHom (h : A.carrier → B.carrier) : Prop where
  presR : PreservesR h
  presP : PreservesP h
  reflR : ReflectsR h
  reflP : ReflectsP h

/-- Embedding: an injective strong homomorphism. `h : A → B` is an embedding exactly
when `A` is isomorphic, via `h`, to the induced substructure of `B` on the image of `h`:
`R` and `P` hold in `A` if and only if they hold at the images in `B`. `B` is then called
an extension of `A`. An injective homomorphism that does not reflect `R` or `P` (for
example, the inclusion of a structure obtained by deleting some `R`-edges) is not an
embedding. -/
structure IsEmbedding (h : A.carrier → B.carrier) : Prop where
  inj : Function.Injective h
  presR : PreservesR h
  presP : PreservesP h
  reflR : ReflectsR h
  reflP : ReflectsP h

/-- Surjective homomorphism (a homomorphic image). -/
structure IsSurjHom (h : A.carrier → B.carrier) : Prop where
  surj : Function.Surjective h
  presR : PreservesR h
  presP : PreservesP h

/-- Isomorphism: a bijection that preserves and reflects `R` and `P`. -/
def IsIso (h : A.carrier → B.carrier) : Prop :=
  Function.Injective h ∧ Function.Surjective h ∧ PreservesR h ∧ PreservesP h ∧
    ReflectsR h ∧ ReflectsP h

theorem IsEmbedding.toStrongHom {h : A.carrier → B.carrier} (hh : IsEmbedding h) :
    IsStrongHom h := ⟨hh.presR, hh.presP, hh.reflR, hh.reflP⟩

theorem IsStrongHom.toHom {h : A.carrier → B.carrier} (hh : IsStrongHom h) : IsHom h :=
  ⟨hh.presR, hh.presP⟩

theorem IsEmbedding.toHom {h : A.carrier → B.carrier} (hh : IsEmbedding h) : IsHom h :=
  ⟨hh.presR, hh.presP⟩

theorem IsSurjHom.toHom {h : A.carrier → B.carrier} (hh : IsSurjHom h) : IsHom h :=
  ⟨hh.presR, hh.presP⟩

end Laws

/-- The four map kinds that index the columns of the transfer matrix. -/
inductive MapKind where
  | hom
  | strong
  | emb
  | surj
  deriving DecidableEq, Repr

/-- `k.Holds h`: the map `h` is of kind `k`. -/
def MapKind.Holds : MapKind → {A B : Str} → (A.carrier → B.carrier) → Prop
  | .hom, _, _, h => IsHom h
  | .strong, _, _, h => IsStrongHom h
  | .emb, _, _, h => IsEmbedding h
  | .surj, _, _, h => IsSurjHom h

theorem MapKind.Holds.toHom {k : MapKind} {A B : Str} {h : A.carrier → B.carrier}
    (hk : k.Holds h) : IsHom h := by
  cases k with
  | hom => exact hk
  | strong => exact IsStrongHom.toHom hk
  | emb => exact IsEmbedding.toHom hk
  | surj => exact IsSurjHom.toHom hk

/-- The identity map is of every kind. -/
theorem MapKind.holds_id (k : MapKind) (A : Str) : k.Holds (A := A) (B := A) id := by
  cases k with
  | hom => exact ⟨fun _ _ h => h, fun _ h => h⟩
  | strong => exact ⟨fun _ _ h => h, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  | emb => exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  | surj => exact ⟨fun b => ⟨b, rfl⟩, fun _ _ h => h, fun _ h => h⟩

/-- Direction of transfer along a map `h : A → B`: `fwd` is from the source `A` to the
target `B`, `bwd` from the target back to the source. -/
inductive Dir where
  | fwd
  | bwd
  deriving DecidableEq, Repr

/-- `d.Transfer p q` with `p` the source-side fact and `q` the target-side fact:
`fwd` is `p → q`, `bwd` is `q → p`. -/
def Dir.Transfer : Dir → Prop → Prop → Prop
  | .fwd, p, q => p → q
  | .bwd, p, q => q → p

/-- The seven syntactic claim classes that index the rows of the transfer matrix. -/
inductive Cls where
  | qf
  | univ
  | exist
  | ae
  | ea
  | pos
  | posExist
  deriving DecidableEq, Repr

/-- Membership of a formula in a claim class (semantic side: the inductive classes). -/
def Cls.Mem : Cls → {n : Nat} → Fml n → Prop
  | .qf, _, φ => IsQF φ
  | .univ, _, φ => IsUniv φ
  | .exist, _, φ => IsExist φ
  | .ae, _, φ => IsAE φ
  | .ea, _, φ => IsEA φ
  | .pos, _, φ => IsPos φ
  | .posExist, _, φ => IsPosExist φ

/-- Boolean membership test (a recognizer, distinct from `Cls.Mem`; see `Cls.test_iff`). -/
def Cls.test : Cls → {n : Nat} → Fml n → Bool
  | .qf, _, φ => φ.qfB
  | .univ, _, φ => φ.univB
  | .exist, _, φ => φ.existB
  | .ae, _, φ => φ.aeB
  | .ea, _, φ => φ.eaB
  | .pos, _, φ => φ.posB
  | .posExist, _, φ => φ.posExistB

theorem Cls.test_iff (c : Cls) {n : Nat} (φ : Fml n) : c.test φ = true ↔ c.Mem φ := by
  cases c
  · exact qfB_iff φ
  · exact univB_iff φ
  · exact existB_iff φ
  · exact aeB_iff φ
  · exact eaB_iff φ
  · exact posB_iff φ
  · exact posExistB_iff φ

instance (c : Cls) {n : Nat} (φ : Fml n) : Decidable (c.Mem φ) :=
  decidable_of_iff _ (c.test_iff φ)

/-- The class `c` transfers along every map of kind `k` in direction `d`: for every
structures `A`, `B`, every `k`-map `h : A → B`, every formula `φ` in `c` and every
environment `e` in `A`, `d.Transfer (A ⊨ φ[e]) (B ⊨ φ[h ∘ e])`. This is preservation of
formulas with parameters (for sentences, the environment is empty). -/
def Preserves (c : Cls) (k : MapKind) (d : Dir) : Prop :=
  ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
    ∀ (n : Nat) (φ : Fml n), c.Mem φ → ∀ e : Fin n → A.carrier,
      d.Transfer (Sat A φ e) (Sat B φ (h ∘ e))

/-- Sentence-level transfer: `Preserves` restricted to sentences (`Fml 0`, evaluated in the
empty environment). -/
def PreservesSent (c : Cls) (k : MapKind) (d : Dir) : Prop :=
  ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
    ∀ φ : Fml 0, c.Mem φ → d.Transfer (SatS A φ) (SatS B φ)

/-- Transfer of formulas with parameters implies transfer of sentences. -/
theorem Preserves.toSent {c : Cls} {k : MapKind} {d : Dir} (hp : Preserves c k d) :
    PreservesSent c k d := by
  intro A B h hk φ hc
  have hφ := hp A B h hk 0 φ hc Fin.elim0
  rw [sat_comp_elim0_iff] at hφ
  exact hφ

/-- A sentence that fails to transfer forward along a `k`-map refutes
`PreservesSent c k .fwd`. -/
theorem not_preservesSent_fwd {c : Cls} {k : MapKind} {A B : Str} (h : A.carrier → B.carrier)
    (hk : k.Holds h) (φ : Fml 0) (hc : c.Mem φ) (hA : Sat A φ Fin.elim0)
    (hB : ¬ Sat B φ (h ∘ Fin.elim0)) : ¬ PreservesSent c k .fwd :=
  fun hp => hB ((sat_comp_elim0_iff h φ).2 (hp A B h hk φ hc hA))

/-- Backward analogue of `not_preservesSent_fwd`. -/
theorem not_preservesSent_bwd {c : Cls} {k : MapKind} {A B : Str} (h : A.carrier → B.carrier)
    (hk : k.Holds h) (φ : Fml 0) (hc : c.Mem φ) (hB : Sat B φ (h ∘ Fin.elim0))
    (hA : ¬ Sat A φ Fin.elim0) : ¬ PreservesSent c k .bwd :=
  fun hp => hA (hp A B h hk φ hc ((sat_comp_elim0_iff h φ).1 hB))

/-- A single instance where a class-`c` formula fails to transfer forward along a
`k`-map refutes `Preserves c k .fwd`. -/
theorem not_preserves_fwd {c : Cls} {k : MapKind} {A B : Str} (h : A.carrier → B.carrier)
    (hk : k.Holds h) {n : Nat} (φ : Fml n) (hc : c.Mem φ) (e : Fin n → A.carrier)
    (hA : Sat A φ e) (hB : ¬ Sat B φ (h ∘ e)) : ¬ Preserves c k .fwd :=
  fun hp => hB (hp A B h hk n φ hc e hA)

/-- Backward analogue of `not_preserves_fwd`. -/
theorem not_preserves_bwd {c : Cls} {k : MapKind} {A B : Str} (h : A.carrier → B.carrier)
    (hk : k.Holds h) {n : Nat} (φ : Fml n) (hc : c.Mem φ) (e : Fin n → A.carrier)
    (hB : Sat B φ (h ∘ e)) (hA : ¬ Sat A φ e) : ¬ Preserves c k .bwd :=
  fun hp => hA (hp A B h hk n φ hc e hB)

/-! ## Finite structures with decidable satisfaction (used for all countermodels) -/

/-- A finite structure on `Fin k` given by Boolean tables. -/
structure FinStr (k : Nat) where
  r : Fin k → Fin k → Bool
  p : Fin k → Bool

/-- The structure denoted by Boolean tables. -/
@[reducible] def FinStr.toStr {k : Nat} (M : FinStr k) : Str where
  carrier := Fin k
  R a b := M.r a b = true
  P a := M.p a = true

/-- Satisfaction in a finite structure is decidable (by exhaustive evaluation). -/
instance FinStr.decSat {k : Nat} (M : FinStr k) :
    {n : Nat} → (φ : Fml n) → (e : Fin n → Fin k) → Decidable (Sat M.toStr φ e)
  | _, .rel i j, e => inferInstanceAs (Decidable (M.r (e i) (e j) = true))
  | _, .pred i, e => inferInstanceAs (Decidable (M.p (e i) = true))
  | _, .eq i j, e => inferInstanceAs (Decidable (e i = e j))
  | _, .neg φ, e => @instDecidableNot _ (FinStr.decSat M φ e)
  | _, .and φ ψ, e => @instDecidableAnd _ _ (FinStr.decSat M φ e) (FinStr.decSat M ψ e)
  | _, .or φ ψ, e => @instDecidableOr _ _ (FinStr.decSat M φ e) (FinStr.decSat M ψ e)
  | _, .all φ, e => @Nat.decidableForallFin k _ (fun a => FinStr.decSat M φ (Env.cons a e))
  | _, .ex φ, e => @Nat.decidableExistsFin k _ (fun a => FinStr.decSat M φ (Env.cons a e))

instance {k : Nat} (M : FinStr k) (φ : Fml 0) : Decidable (SatS M.toStr φ) :=
  FinStr.decSat M φ _

section FinLaws
variable {m k : Nat} {M : FinStr m} {N : FinStr k} {h : Fin m → Fin k}

instance : Decidable (PreservesR (A := M.toStr) (B := N.toStr) h) :=
  inferInstanceAs (Decidable (∀ a b : Fin m, M.r a b = true → N.r (h a) (h b) = true))
instance : Decidable (PreservesP (A := M.toStr) (B := N.toStr) h) :=
  inferInstanceAs (Decidable (∀ a : Fin m, M.p a = true → N.p (h a) = true))
instance : Decidable (ReflectsR (A := M.toStr) (B := N.toStr) h) :=
  inferInstanceAs (Decidable (∀ a b : Fin m, N.r (h a) (h b) = true → M.r a b = true))
instance : Decidable (ReflectsP (A := M.toStr) (B := N.toStr) h) :=
  inferInstanceAs (Decidable (∀ a : Fin m, N.p (h a) = true → M.p a = true))
instance : Decidable (Function.Injective h) :=
  inferInstanceAs (Decidable (∀ a b : Fin m, h a = h b → a = b))
instance : Decidable (Function.Surjective h) :=
  inferInstanceAs (Decidable (∀ b : Fin k, ∃ a : Fin m, h a = b))

instance : Decidable (IsHom (A := M.toStr) (B := N.toStr) h) :=
  decidable_of_iff (PreservesR (A := M.toStr) (B := N.toStr) h ∧
      PreservesP (A := M.toStr) (B := N.toStr) h)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩
instance : Decidable (IsStrongHom (A := M.toStr) (B := N.toStr) h) :=
  decidable_of_iff (PreservesR (A := M.toStr) (B := N.toStr) h ∧
      PreservesP (A := M.toStr) (B := N.toStr) h ∧ ReflectsR (A := M.toStr) (B := N.toStr) h ∧
      ReflectsP (A := M.toStr) (B := N.toStr) h)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩
instance : Decidable (IsEmbedding (A := M.toStr) (B := N.toStr) h) :=
  decidable_of_iff (Function.Injective h ∧ PreservesR (A := M.toStr) (B := N.toStr) h ∧
      PreservesP (A := M.toStr) (B := N.toStr) h ∧ ReflectsR (A := M.toStr) (B := N.toStr) h ∧
      ReflectsP (A := M.toStr) (B := N.toStr) h)
    ⟨fun ⟨i, a, b, c, d⟩ => ⟨i, a, b, c, d⟩, fun ⟨i, a, b, c, d⟩ => ⟨i, a, b, c, d⟩⟩
instance : Decidable (IsSurjHom (A := M.toStr) (B := N.toStr) h) :=
  decidable_of_iff (Function.Surjective h ∧ PreservesR (A := M.toStr) (B := N.toStr) h ∧
      PreservesP (A := M.toStr) (B := N.toStr) h)
    ⟨fun ⟨s, a, b⟩ => ⟨s, a, b⟩, fun ⟨s, a, b⟩ => ⟨s, a, b⟩⟩

instance : Decidable (IsIso (A := M.toStr) (B := N.toStr) h) :=
  inferInstanceAs (Decidable (Function.Injective h ∧ Function.Surjective h ∧
    PreservesR (A := M.toStr) (B := N.toStr) h ∧ PreservesP (A := M.toStr) (B := N.toStr) h ∧
    ReflectsR (A := M.toStr) (B := N.toStr) h ∧ ReflectsP (A := M.toStr) (B := N.toStr) h))

instance (kd : MapKind) : Decidable (kd.Holds (A := M.toStr) (B := N.toStr) h) := by
  cases kd <;> unfold MapKind.Holds <;> exact inferInstance

end FinLaws

end Toy.Transfer
