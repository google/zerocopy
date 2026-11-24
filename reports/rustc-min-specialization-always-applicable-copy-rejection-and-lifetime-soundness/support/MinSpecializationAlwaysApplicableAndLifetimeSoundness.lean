/-!
# Soundness Model: `rustc` `min_specialization` (`check_always_applicable`),
# `Copy` Rejection vs. `#[rustc_specialization_trait]` / Marker Whitelists,
# Specialization-Graph Ordering, Lifetime-Erasure Invariance, and `default type` Separation

Standalone kernel-checked Lean `v4.34.1` formalization companion to the reference package
`rustc-min-specialization-always-applicable-copy-rejection-and-lifetime-soundness`.

Purity & TCB guarantees (verified against the Lean `v4.34.1` kernel):
- Zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool`,
  zero `Lean.trustCompiler`, zero `omega`, zero `bv_decide`, zero `native_decide`,
  zero `partial def`, zero `unsafe`, and zero `._unsafe_rec` auxiliary constants.
- Every `def` carries `noncomputable` explicitly (no `noncomputable section`, no
  `deriving DecidableEq`/`Repr` on recursive inductives), suppressing compiler
  `._unsafe_rec` synthesis while keeping every definition and theorem constructive.
-/

namespace MinSpecializationSoundness

/-!
## Part 1: Constructive Primitives, List Combinators, and Equality Lemmas
-/

abbrev TraitId := Nat
abbrev AdtId := Nat
abbrev ImplId := Nat
abbrev VarId := Nat
abbrev RegId := Nat

noncomputable def boolNot : Bool → Bool
  | true => false
  | false => true

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem nat_beq_true_eq {m n : Nat} (h : Nat.beq m n = true) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => cases h
  | succ m ih =>
    cases n with
    | zero => cases h
    | succ n =>
      have hmn : m = n := ih h
      rw [hmn]

private theorem nat_beq_false_of_ne {m n : Nat} (hne : m ≠ n) : Nat.beq m n = false := by
  cases h : Nat.beq m n with
  | false => rfl
  | true => exact False.elim (hne (nat_beq_true_eq h))

private theorem nat_succ_ne_self (n : Nat) : n + 1 ≠ n := by
  induction n with
  | zero =>
    intro h
    cases h
  | succ _ ih =>
    intro h
    injection h with h'
    exact ih h'

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => cases h

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => cases h

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

/-- Constructive list membership (`Mem x xs`). -/
inductive Mem {α : Type} (x : α) : List α → Prop where
  | head {xs : List α} : Mem x (x :: xs)
  | tail {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

/-- Constructive negative list membership (`NoMem x xs`). -/
inductive NoMem {α : Type} (x : α) : List α → Prop where
  | nil : NoMem x []
  | cons {y : α} {xs : List α} : y ≠ x → NoMem x xs → NoMem x (y :: xs)

/-- Constructive duplicate-free list predicate (`NoDup xs`). -/
inductive NoDup {α : Type} : List α → Prop where
  | nil : NoDup []
  | cons {x : α} {xs : List α} : NoMem x xs → NoDup xs → NoDup (x :: xs)

/-- Constructive list disjointness (`Disjoint xs ys`). -/
noncomputable def Disjoint {α : Type} (xs ys : List α) : Prop :=
  ∀ x : α, Mem x xs → NoMem x ys

private theorem mem_and_noMem_false {α : Type} {x : α} {xs : List α}
    (hm : Mem x xs) (hn : NoMem x xs) : False := by
  induction hm with
  | head =>
    cases hn with
    | cons hne _ => exact hne rfl
  | tail _ ih =>
    cases hn with
    | cons _ hns => exact ih hns

private theorem mem_append_left {α : Type} {x : α} {xs ys : List α}
    (h : Mem x xs) : Mem x (xs ++ ys) := by
  induction h with
  | head => exact .head
  | tail _ ih => exact .tail ih

private theorem mem_append_right {α : Type} {x : α} {xs ys : List α}
    (h : Mem x ys) : Mem x (xs ++ ys) := by
  induction xs with
  | nil => exact h
  | cons _ _ ih => exact .tail ih

private theorem mem_append_elim {α : Type} {x : α} {xs ys : List α}
    (h : Mem x (xs ++ ys)) : Mem x xs ∨ Mem x ys := by
  induction xs with
  | nil => exact Or.inr h
  | cons _ _ ih =>
    cases h with
    | head => exact Or.inl .head
    | tail hm =>
      cases ih hm with
      | inl h1 => exact Or.inl (.tail h1)
      | inr h2 => exact Or.inr h2

private theorem noMem_of_noMem_append_left {α : Type} {x : α} {xs ys : List α}
    (h : NoMem x (xs ++ ys)) : NoMem x xs := by
  induction xs with
  | nil => exact .nil
  | cons _ _ ih =>
    cases h with
    | cons hne hrest => exact .cons hne (ih hrest)

private theorem noMem_of_noMem_append_right {α : Type} {x : α} {xs ys : List α}
    (h : NoMem x (xs ++ ys)) : NoMem x ys := by
  induction xs with
  | nil => exact h
  | cons _ _ ih =>
    cases h with
    | cons _ hrest => exact ih hrest

private theorem noDup_append_left {α : Type} {xs ys : List α}
    (h : NoDup (xs ++ ys)) : NoDup xs := by
  induction xs with
  | nil => exact .nil
  | cons _ _ ih =>
    cases h with
    | cons hnm hnd => exact .cons (noMem_of_noMem_append_left hnm) (ih hnd)

private theorem noDup_append_right {α : Type} {xs ys : List α}
    (h : NoDup (xs ++ ys)) : NoDup ys := by
  induction xs with
  | nil => exact h
  | cons _ _ ih =>
    cases h with
    | cons _ hnd => exact ih hnd

private theorem noDup_append_disjoint_rev {α : Type} {xs ys : List α}
    (h : NoDup (xs ++ ys)) : Disjoint ys xs := by
  intro z hmz
  induction xs with
  | nil => exact .nil
  | cons y _ ih =>
    cases h with
    | cons hnm hnd =>
      have hne : y ≠ z := by
        intro heq
        rw [heq] at hnm
        exact mem_and_noMem_false (mem_append_right hmz) hnm
      exact .cons hne (ih hnd)

private theorem noDup_append_disjoint_fwd {α : Type} {xs ys : List α}
    (h : NoDup (xs ++ ys)) : Disjoint xs ys := by
  intro z hmx
  induction xs with
  | nil => cases hmx
  | cons _ _ ih =>
    cases h with
    | cons hnm hnd =>
      cases hmx with
      | head => exact noMem_of_noMem_append_right hnm
      | tail hm => exact ih hnd hm

private theorem noMem_symm_ne {α : Type} {x : α} {xs : List α}
    (h : NoMem x xs) {y : α} (hy : Mem y xs) : y ≠ x := by
  induction hy with
  | head =>
    cases h with
    | cons hne _ => exact hne
  | tail _ ih =>
    cases h with
    | cons _ hrest => exact ih hrest

noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

noncomputable def natMemBool (n : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Nat.beq n x || natMemBool n xs

noncomputable def natNoDupBool : List Nat → Bool
  | [] => true
  | x :: xs => boolNot (natMemBool x xs) && natNoDupBool xs

private theorem natMemBool_of_mem {x : Nat} {xs : List Nat} (h : Mem x xs) :
    natMemBool x xs = true := by
  induction h with
  | head =>
    dsimp only [natMemBool]
    rw [nat_beq_refl]
    rfl
  | tail _ ih =>
    dsimp only [natMemBool]
    rw [ih]
    cases Nat.beq x _ <;> rfl

private theorem natMemBool_of_noMem {x : Nat} {xs : List Nat} (h : NoMem x xs) :
    natMemBool x xs = false := by
  induction h with
  | nil => rfl
  | cons hne _ ih =>
    dsimp only [natMemBool]
    rw [nat_beq_false_of_ne (fun heq => hne heq.symm), ih]
    rfl

private theorem natMemBool_false_noMem {x : Nat} {xs : List Nat}
    (h : natMemBool x xs = false) : NoMem x xs := by
  induction xs with
  | nil => exact .nil
  | cons y _ ih =>
    dsimp only [natMemBool] at h
    cases hb : Nat.beq x y with
    | true =>
      rw [hb] at h
      cases h
    | false =>
      rw [hb] at h
      have hne : y ≠ x := by
        intro heq
        rw [heq, nat_beq_refl] at hb
        cases hb
      exact .cons hne (ih h)

private theorem mem_of_natMemBool_true {x : Nat} {xs : List Nat}
    (h : natMemBool x xs = true) : Mem x xs := by
  induction xs with
  | nil => cases h
  | cons y _ ih =>
    dsimp only [natMemBool] at h
    cases hb : Nat.beq x y with
    | true =>
      have heq := nat_beq_true_eq hb
      rw [heq]
      exact .head
    | false =>
      rw [hb] at h
      exact .tail (ih h)

private theorem natNoDupBool_sound {xs : List Nat} (h : natNoDupBool xs = true) :
    NoDup xs := by
  induction xs with
  | nil => exact .nil
  | cons _ _ ih =>
    dsimp only [natNoDupBool] at h
    have hl : boolNot (natMemBool _ _) = true := bool_and_left h
    have hr : natNoDupBool _ = true := bool_and_right h
    cases hm : natMemBool _ _ with
    | true =>
      rw [hm] at hl
      cases hl
    | false => exact .cons (natMemBool_false_noMem hm) (ih hr)

private theorem listAll_mem {α : Type} {p : α → Bool} {xs : List α}
    (h : listAll p xs = true) {x : α} (hm : Mem x xs) : p x = true := by
  induction hm with
  | head => exact bool_and_left h
  | tail _ ih => exact ih (bool_and_right h)

private theorem listAny_true_exists {α : Type} {p : α → Bool} {xs : List α}
    (h : listAny p xs = true) : ∃ x : α, Mem x xs ∧ p x = true := by
  induction xs with
  | nil => cases h
  | cons x _ ih =>
    dsimp only [listAny] at h
    cases hp : p x with
    | true => exact ⟨x, .head, hp⟩
    | false =>
      rw [hp] at h
      rcases ih h with ⟨y, hm, hpy⟩
      exact ⟨y, .tail hm, hpy⟩

private theorem listAny_intro {α : Type} {p : α → Bool} {x : α} {xs : List α}
    (hm : Mem x xs) (hp : p x = true) : listAny p xs = true := by
  induction hm with
  | head =>
    dsimp only [listAny]
    rw [hp]
    rfl
  | tail _ ih =>
    dsimp only [listAny]
    rw [ih]
    cases p _ <;> rfl

/-!
## Part 2: Rust Type Grammar (`Ty`), Ground Types (`GroundTy`), Erased Types (`ErasedTy`),
## and Linear No-`'static` Pattern-Matching Invariance
-/

/-- Surface/impl-header lifetime AST (`'static` vs generic parameter `'a`). -/
inductive Region where
  | rStatic
  | rNamed (id : RegId)

/-- Concrete region during type checking (`'static` vs local stack borrow `'local_k`). -/
inductive GroundRegion where
  | rStatic
  | rLocal (id : Nat)

/-- Surface/impl-header Rust type pattern covering generic type variables, primitives,
references, `Vec`, pairs, iterators, nominal ADTs, and const-length arrays. -/
inductive Ty where
  | var (id : VarId)
  | prim (id : Nat)
  | ref (r : Region) (inner : Ty)
  | vecTy (elem : Ty)
  | pair (fst snd : Ty)
  | sliceIter (r : Region) (elem : Ty)
  | intoIter (elem : Ty)
  | adt0 (adtId : AdtId)
  | adt1r (adtId : AdtId) (r : Region)
  | adt1t (adtId : AdtId) (arg : Ty)
  | arrConst (elem : Ty) (lenParam : Option Nat)

/-- Concrete lifetime-carrying ground Rust type (pre-monomorphization typeck view). -/
inductive GroundTy where
  | prim (id : Nat)
  | ref (r : GroundRegion) (inner : GroundTy)
  | vecTy (elem : GroundTy)
  | pair (fst snd : GroundTy)
  | sliceIter (r : GroundRegion) (elem : GroundTy)
  | intoIter (elem : GroundTy)
  | adt0 (adtId : AdtId)
  | adt1r (adtId : AdtId) (r : GroundRegion)
  | adt1t (adtId : AdtId) (arg : GroundTy)
  | arrConst (elem : GroundTy) (lenVal : Nat)

/-- Post-monomorphization lifetime-erased ground Rust type (`ReErased`). -/
inductive ErasedTy where
  | prim (id : Nat)
  | ref (inner : ErasedTy)
  | vecTy (elem : ErasedTy)
  | pair (fst snd : ErasedTy)
  | sliceIter (elem : ErasedTy)
  | intoIter (elem : ErasedTy)
  | adt0 (adtId : AdtId)
  | adt1r (adtId : AdtId)
  | adt1t (adtId : AdtId) (arg : ErasedTy)
  | arrConst (elem : ErasedTy) (lenVal : Nat)

/-- Lifetime-erased impl-header pattern (used by region-blind `specializes` & monomorphization). -/
inductive ErasedPat where
  | var (id : VarId)
  | prim (id : Nat)
  | ref (inner : ErasedPat)
  | vecTy (elem : ErasedPat)
  | pair (fst snd : ErasedPat)
  | sliceIter (elem : ErasedPat)
  | intoIter (elem : ErasedPat)
  | adt0 (adtId : AdtId)
  | adt1r (adtId : AdtId)
  | adt1t (adtId : AdtId) (arg : ErasedPat)
  | arrConst (elem : ErasedPat) (lenParam : Option Nat)

noncomputable def groundRegBeq : GroundRegion → GroundRegion → Bool
  | .rStatic, .rStatic => true
  | .rLocal a, .rLocal b => Nat.beq a b
  | _, _ => false

private theorem groundRegBeq_refl (r : GroundRegion) : groundRegBeq r r = true := by
  cases r with
  | rStatic => rfl
  | rLocal a => exact nat_beq_refl a

private theorem groundRegBeq_eq {r₁ r₂ : GroundRegion} (h : groundRegBeq r₁ r₂ = true) :
    r₁ = r₂ := by
  cases r₁ with
  | rStatic =>
    cases r₂ with
    | rStatic => rfl
    | rLocal _ => cases h
  | rLocal a =>
    cases r₂ with
    | rStatic => cases h
    | rLocal b =>
      have hab : a = b := nat_beq_true_eq h
      rw [hab]

noncomputable def groundTyBeq : GroundTy → GroundTy → Bool
  | .prim a, .prim b => Nat.beq a b
  | .ref r₁ t₁, .ref r₂ t₂ => groundRegBeq r₁ r₂ && groundTyBeq t₁ t₂
  | .vecTy t₁, .vecTy t₂ => groundTyBeq t₁ t₂
  | .pair a₁ b₁, .pair a₂ b₂ => groundTyBeq a₁ a₂ && groundTyBeq b₁ b₂
  | .sliceIter r₁ t₁, .sliceIter r₂ t₂ => groundRegBeq r₁ r₂ && groundTyBeq t₁ t₂
  | .intoIter t₁, .intoIter t₂ => groundTyBeq t₁ t₂
  | .adt0 a, .adt0 b => Nat.beq a b
  | .adt1r id₁ r₁, .adt1r id₂ r₂ => Nat.beq id₁ id₂ && groundRegBeq r₁ r₂
  | .adt1t id₁ t₁, .adt1t id₂ t₂ => Nat.beq id₁ id₂ && groundTyBeq t₁ t₂
  | .arrConst t₁ n₁, .arrConst t₂ n₂ => groundTyBeq t₁ t₂ && Nat.beq n₁ n₂
  | _, _ => false

private theorem groundTyBeq_refl (g : GroundTy) : groundTyBeq g g = true := by
  induction g with
  | prim a => exact nat_beq_refl a
  | ref r _ ih => exact bool_and_intro (groundRegBeq_refl r) ih
  | vecTy _ ih => exact ih
  | pair _ _ iha ihb => exact bool_and_intro iha ihb
  | sliceIter r _ ih => exact bool_and_intro (groundRegBeq_refl r) ih
  | intoIter _ ih => exact ih
  | adt0 id => exact nat_beq_refl id
  | adt1r id r => exact bool_and_intro (nat_beq_refl id) (groundRegBeq_refl r)
  | adt1t id _ ih => exact bool_and_intro (nat_beq_refl id) ih
  | arrConst _ n ih => exact bool_and_intro ih (nat_beq_refl n)

/-- Erase all lifetimes from a `GroundTy` (monomorphization `ReErased` view). -/
noncomputable def eraseRegions : GroundTy → ErasedTy
  | .prim id => .prim id
  | .ref _ inner => .ref (eraseRegions inner)
  | .vecTy elem => .vecTy (eraseRegions elem)
  | .pair a b => .pair (eraseRegions a) (eraseRegions b)
  | .sliceIter _ elem => .sliceIter (eraseRegions elem)
  | .intoIter elem => .intoIter (eraseRegions elem)
  | .adt0 id => .adt0 id
  | .adt1r id _ => .adt1r id
  | .adt1t id arg => .adt1t id (eraseRegions arg)
  | .arrConst elem n => .arrConst (eraseRegions elem) n

/-- Erase all lifetimes from a surface `Ty` pattern. -/
noncomputable def erasePatRegions : Ty → ErasedPat
  | .var id => .var id
  | .prim id => .prim id
  | .ref _ inner => .ref (erasePatRegions inner)
  | .vecTy elem => .vecTy (erasePatRegions elem)
  | .pair a b => .pair (erasePatRegions a) (erasePatRegions b)
  | .sliceIter _ elem => .sliceIter (erasePatRegions elem)
  | .intoIter elem => .intoIter (erasePatRegions elem)
  | .adt0 id => .adt0 id
  | .adt1r id _ => .adt1r id
  | .adt1t id arg => .adt1t id (erasePatRegions arg)
  | .arrConst elem lp => .arrConst (erasePatRegions elem) lp

/-- Embed an erased ground type back into `GroundTy` using a canonical local region `.rLocal 0`. -/
noncomputable def liftErasedWithLocal0 : ErasedTy → GroundTy
  | .prim id => .prim id
  | .ref inner => .ref (.rLocal 0) (liftErasedWithLocal0 inner)
  | .vecTy elem => .vecTy (liftErasedWithLocal0 elem)
  | .pair a b => .pair (liftErasedWithLocal0 a) (liftErasedWithLocal0 b)
  | .sliceIter elem => .sliceIter (.rLocal 0) (liftErasedWithLocal0 elem)
  | .intoIter elem => .intoIter (liftErasedWithLocal0 elem)
  | .adt0 id => .adt0 id
  | .adt1r id => .adt1r id (.rLocal 0)
  | .adt1t id arg => .adt1t id (liftErasedWithLocal0 arg)
  | .arrConst elem n => .arrConst (liftErasedWithLocal0 elem) n

private theorem eraseRegions_liftErased (e : ErasedTy) :
    eraseRegions (liftErasedWithLocal0 e) = e := by
  induction e with
  | prim _ => rfl
  | ref _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]
  | vecTy _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]
  | pair _ _ iha ihb =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [iha, ihb]
  | sliceIter _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]
  | intoIter _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]
  | adt0 _ => rfl
  | adt1r _ => rfl
  | adt1t _ _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]
  | arrConst _ _ ih =>
    dsimp only [liftErasedWithLocal0, eraseRegions]
    rw [ih]

/-- Ground substitution mapping region vars, type vars, and const vars. -/
structure Subst where
  regSubst : RegId → GroundRegion
  tySubst : VarId → GroundTy
  constSubst : Nat → Nat

/-- Erased substitution mapping type vars and const vars (regions stripped). -/
structure ErasedSubst where
  tySubst : VarId → ErasedTy
  constSubst : Nat → Nat

noncomputable def defaultSubst : Subst :=
  { regSubst := fun _ => .rLocal 0
    tySubst := fun _ => .prim 0
    constSubst := fun _ => 4 }

noncomputable def eraseSubst (σ : Subst) : ErasedSubst :=
  { tySubst := fun v => eraseRegions (σ.tySubst v)
    constSubst := σ.constSubst }

noncomputable def liftErasedSubst (τ : ErasedSubst) : Subst :=
  { regSubst := fun _ => .rLocal 0
    tySubst := fun v => liftErasedWithLocal0 (τ.tySubst v)
    constSubst := τ.constSubst }

noncomputable def instRegion (σ : Subst) : Region → GroundRegion
  | .rStatic => .rStatic
  | .rNamed id => σ.regSubst id

noncomputable def instTy (σ : Subst) : Ty → GroundTy
  | .var id => σ.tySubst id
  | .prim id => .prim id
  | .ref r inner => .ref (instRegion σ r) (instTy σ inner)
  | .vecTy elem => .vecTy (instTy σ elem)
  | .pair a b => .pair (instTy σ a) (instTy σ b)
  | .sliceIter r elem => .sliceIter (instRegion σ r) (instTy σ elem)
  | .intoIter elem => .intoIter (instTy σ elem)
  | .adt0 id => .adt0 id
  | .adt1r id r => .adt1r id (instRegion σ r)
  | .adt1t id arg => .adt1t id (instTy σ arg)
  | .arrConst elem none => .arrConst (instTy σ elem) 4
  | .arrConst elem (some k) => .arrConst (instTy σ elem) (σ.constSubst k)

noncomputable def instErasedPat (τ : ErasedSubst) : ErasedPat → ErasedTy
  | .var id => τ.tySubst id
  | .prim id => .prim id
  | .ref inner => .ref (instErasedPat τ inner)
  | .vecTy elem => .vecTy (instErasedPat τ elem)
  | .pair a b => .pair (instErasedPat τ a) (instErasedPat τ b)
  | .sliceIter elem => .sliceIter (instErasedPat τ elem)
  | .intoIter elem => .intoIter (instErasedPat τ elem)
  | .adt0 id => .adt0 id
  | .adt1r id => .adt1r id
  | .adt1t id arg => .adt1t id (instErasedPat τ arg)
  | .arrConst elem none => .arrConst (instErasedPat τ elem) 4
  | .arrConst elem (some k) => .arrConst (instErasedPat τ elem) (τ.constSubst k)

/-- Theorem: `eraseRegions` commutes unconditionally with pattern instantiation! -/
theorem instTy_erase_commutes (σ : Subst) :
    (t : Ty) → eraseRegions (instTy σ t) = instErasedPat (eraseSubst σ) (erasePatRegions t)
  | .var _ => rfl
  | .prim _ => rfl
  | .ref _ inner => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ inner]
  | .vecTy elem => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ elem]
  | .pair a b => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ a, instTy_erase_commutes σ b]
  | .sliceIter _ elem => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ elem]
  | .intoIter elem => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ elem]
  | .adt0 _ => rfl
  | .adt1r _ _ => rfl
  | .adt1t _ arg => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ arg]
  | .arrConst elem none => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ elem]
  | .arrConst elem (some _) => by
    dsimp only [instTy, eraseRegions, erasePatRegions, instErasedPat]
    rw [instTy_erase_commutes σ elem]
    rfl

/-- Check whether a region is NOT `.rStatic` (`check_static_lifetimes`, `min_specialization.rs` L297). -/
noncomputable def regNoStatic : Region → Bool
  | .rStatic => false
  | .rNamed _ => true

/-- Boolean checker for absence of `'static` anywhere in a `Ty` (`check_static_lifetimes`). -/
noncomputable def tyNoStatic : Ty → Bool
  | .var _ => true
  | .prim _ => true
  | .ref r inner => regNoStatic r && tyNoStatic inner
  | .vecTy elem => tyNoStatic elem
  | .pair a b => tyNoStatic a && tyNoStatic b
  | .sliceIter r elem => regNoStatic r && tyNoStatic elem
  | .intoIter elem => tyNoStatic elem
  | .adt0 _ => true
  | .adt1r _ r => regNoStatic r
  | .adt1t _ arg => tyNoStatic arg
  | .arrConst elem _ => tyNoStatic elem

/-- Collect all type variable occurrences (`cgp::parameters_for`). -/
noncomputable def collectTyVars : Ty → List VarId
  | .var id => [id]
  | .prim _ => []
  | .ref _ inner => collectTyVars inner
  | .vecTy elem => collectTyVars elem
  | .pair a b => collectTyVars a ++ collectTyVars b
  | .sliceIter _ elem => collectTyVars elem
  | .intoIter elem => collectTyVars elem
  | .adt0 _ => []
  | .adt1r _ _ => []
  | .adt1t _ arg => collectTyVars arg
  | .arrConst elem _ => collectTyVars elem

/-- Collect all named region variable occurrences (`cgp::parameters_for` regions). -/
noncomputable def collectRegVarsReg : Region → List RegId
  | .rStatic => []
  | .rNamed id => [id]

noncomputable def collectRegVars : Ty → List RegId
  | .var _ => []
  | .prim _ => []
  | .ref r inner => collectRegVarsReg r ++ collectRegVars inner
  | .vecTy elem => collectRegVars elem
  | .pair a b => collectRegVars a ++ collectRegVars b
  | .sliceIter r elem => collectRegVarsReg r ++ collectRegVars elem
  | .intoIter elem => collectRegVars elem
  | .adt0 _ => []
  | .adt1r _ r => collectRegVarsReg r
  | .adt1t _ arg => collectRegVars arg
  | .arrConst elem _ => collectRegVars elem

/-- Collect const parameter occurrences. -/
noncomputable def collectConstVars : Ty → List Nat
  | .var _ => []
  | .prim _ => []
  | .ref _ inner => collectConstVars inner
  | .vecTy elem => collectConstVars elem
  | .pair a b => collectConstVars a ++ collectConstVars b
  | .sliceIter _ elem => collectConstVars elem
  | .intoIter elem => collectConstVars elem
  | .adt0 _ => []
  | .adt1r _ _ => []
  | .adt1t _ arg => collectConstVars arg
  | .arrConst elem none => collectConstVars elem
  | .arrConst elem (some k) => collectConstVars elem ++ [k]

/-- Boolean check that unconstrained parameters do not repeat and `'static` is absent. -/
noncomputable def linearNoStaticCheck (t : Ty) : Bool :=
  tyNoStatic t &&
  natNoDupBool (collectTyVars t) &&
  natNoDupBool (collectRegVars t) &&
  natNoDupBool (collectConstVars t)

/-- Structural linearity and `'static`-freedom predicate (`check_static_lifetimes` + `check_duplicate_params`). -/
noncomputable def LinearNoStaticPat (t : Ty) : Prop :=
  tyNoStatic t = true ∧
  NoDup (collectTyVars t) ∧
  NoDup (collectRegVars t) ∧
  NoDup (collectConstVars t)

private theorem linearNoStaticCheck_sound {t : Ty} (h : linearNoStaticCheck t = true) :
    LinearNoStaticPat t := by
  dsimp only [linearNoStaticCheck] at h
  have h1 := bool_and_left h
  have hconst := bool_and_right h
  have h2 := bool_and_left h1
  have hreg := bool_and_right h1
  have hns := bool_and_left h2
  have hty := bool_and_right h2
  exact ⟨hns, natNoDupBool_sound hty, natNoDupBool_sound hreg, natNoDupBool_sound hconst⟩

/-- Substitution agreement on active variables of `t`. -/
noncomputable def SubstAgreeOn (σ₁ σ₂ : Subst) (t : Ty) : Prop :=
  (∀ r, Mem r (collectRegVars t) → σ₁.regSubst r = σ₂.regSubst r) ∧
  (∀ v, Mem v (collectTyVars t) → σ₁.tySubst v = σ₂.tySubst v) ∧
  (∀ k, Mem k (collectConstVars t) → σ₁.constSubst k = σ₂.constSubst k)

private theorem instRegion_agree {σ₁ σ₂ : Subst} {r : Region}
    (h : ∀ rid, Mem rid (collectRegVarsReg r) → σ₁.regSubst rid = σ₂.regSubst rid) :
    instRegion σ₁ r = instRegion σ₂ r := by
  cases r with
  | rStatic => rfl
  | rNamed id => exact h id .head

private theorem instTy_agree_on_vars {σ₁ σ₂ : Subst} :
    (t : Ty) → SubstAgreeOn σ₁ σ₂ t → instTy σ₁ t = instTy σ₂ t
  | .var id, ⟨_, hv, _⟩ => hv id .head
  | .prim _, _ => rfl
  | .ref r inner, ⟨hr, hv, hc⟩ => by
    dsimp only [instTy]
    have hreg := instRegion_agree (fun rid hm => hr rid (mem_append_left hm))
    have hin := instTy_agree_on_vars inner
      ⟨fun rid hm => hr rid (mem_append_right hm), hv, hc⟩
    rw [hreg, hin]
  | .vecTy elem, h => by
    dsimp only [instTy]
    rw [instTy_agree_on_vars elem h]
  | .pair a b, ⟨hr, hv, hc⟩ => by
    dsimp only [instTy]
    have ha := instTy_agree_on_vars a
      ⟨fun rid hm => hr rid (mem_append_left hm),
       fun vid hm => hv vid (mem_append_left hm),
       fun cid hm => hc cid (mem_append_left hm)⟩
    have hb := instTy_agree_on_vars b
      ⟨fun rid hm => hr rid (mem_append_right hm),
       fun vid hm => hv vid (mem_append_right hm),
       fun cid hm => hc cid (mem_append_right hm)⟩
    rw [ha, hb]
  | .sliceIter r elem, ⟨hr, hv, hc⟩ => by
    dsimp only [instTy]
    have hreg := instRegion_agree (fun rid hm => hr rid (mem_append_left hm))
    have hel := instTy_agree_on_vars elem
      ⟨fun rid hm => hr rid (mem_append_right hm), hv, hc⟩
    rw [hreg, hel]
  | .intoIter elem, h => by
    dsimp only [instTy]
    rw [instTy_agree_on_vars elem h]
  | .adt0 _, _ => rfl
  | .adt1r _ r, ⟨hr, _, _⟩ => by
    dsimp only [instTy]
    have hreg := instRegion_agree hr
    rw [hreg]
  | .adt1t _ arg, h => by
    dsimp only [instTy]
    rw [instTy_agree_on_vars arg h]
  | .arrConst elem none, h => by
    dsimp only [instTy]
    rw [instTy_agree_on_vars elem h]
  | .arrConst elem (some k), ⟨hr, hv, hc⟩ => by
    dsimp only [instTy]
    have hel := instTy_agree_on_vars elem
      ⟨hr, hv, fun cid hm => hc cid (mem_append_left hm)⟩
    have hk := hc k (mem_append_right .head)
    rw [hel, hk]

noncomputable def overrideSubst (regs : List RegId) (vars : List VarId) (consts : List Nat)
    (σ_new σ_base : Subst) : Subst :=
  { regSubst := fun r => if natMemBool r regs then σ_new.regSubst r else σ_base.regSubst r
    tySubst := fun v => if natMemBool v vars then σ_new.tySubst v else σ_base.tySubst v
    constSubst := fun k => if natMemBool k consts then σ_new.constSubst k else σ_base.constSubst k }

private theorem instTy_override_self (σ₁ σ₂ : Subst) (t : Ty) :
    instTy (overrideSubst (collectRegVars t) (collectTyVars t) (collectConstVars t) σ₁ σ₂) t =
    instTy σ₁ t := by
  apply instTy_agree_on_vars t
  refine ⟨?_, ?_, ?_⟩
  · intro r hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_mem hm]
    rfl
  · intro v hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_mem hm]
    rfl
  · intro k hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_mem hm]
    rfl

private theorem instTy_override_disjoint (σ₁ σ₂ : Subst) (t_over t_keep : Ty)
    (hReg : Disjoint (collectRegVars t_keep) (collectRegVars t_over))
    (hTy : Disjoint (collectTyVars t_keep) (collectTyVars t_over))
    (hConst : Disjoint (collectConstVars t_keep) (collectConstVars t_over)) :
    instTy (overrideSubst (collectRegVars t_over) (collectTyVars t_over)
      (collectConstVars t_over) σ₁ σ₂) t_keep = instTy σ₂ t_keep := by
  apply instTy_agree_on_vars t_keep
  refine ⟨?_, ?_, ?_⟩
  · intro r hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_noMem (hReg r hm)]
    rfl
  · intro v hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_noMem (hTy v hm)]
    rfl
  · intro k hm
    dsimp only [overrideSubst]
    rw [natMemBool_of_noMem (hConst k hm)]
    rfl

private theorem linear_pair_left {a b : Ty} (h : LinearNoStaticPat (.pair a b)) :
    LinearNoStaticPat a := by
  rcases h with ⟨hns, hty, hreg, hconst⟩
  exact ⟨bool_and_left hns, noDup_append_left hty, noDup_append_left hreg, noDup_append_left hconst⟩

private theorem linear_pair_right {a b : Ty} (h : LinearNoStaticPat (.pair a b)) :
    LinearNoStaticPat b := by
  rcases h with ⟨hns, hty, hreg, hconst⟩
  exact ⟨bool_and_right hns, noDup_append_right hty, noDup_append_right hreg, noDup_append_right hconst⟩

private theorem linear_pair_disjoint_rev {a b : Ty} (h : LinearNoStaticPat (.pair a b)) :
    Disjoint (collectRegVars b) (collectRegVars a) ∧
    Disjoint (collectTyVars b) (collectTyVars a) ∧
    Disjoint (collectConstVars b) (collectConstVars a) := by
  rcases h with ⟨_, hty, hreg, hconst⟩
  exact ⟨noDup_append_disjoint_rev hreg, noDup_append_disjoint_rev hty,
    noDup_append_disjoint_rev hconst⟩

private theorem linear_pair_disjoint_fwd {a b : Ty} (h : LinearNoStaticPat (.pair a b)) :
    Disjoint (collectRegVars a) (collectRegVars b) ∧
    Disjoint (collectTyVars a) (collectTyVars b) ∧
    Disjoint (collectConstVars a) (collectConstVars b) := by
  rcases h with ⟨_, hty, hreg, hconst⟩
  exact ⟨noDup_append_disjoint_fwd hreg, noDup_append_disjoint_fwd hty,
    noDup_append_disjoint_fwd hconst⟩

private theorem linear_ref_sub {r : Region} {inner : Ty} (h : LinearNoStaticPat (.ref r inner)) :
    regNoStatic r = true ∧ NoDup (collectRegVarsReg r ++ collectRegVars inner) ∧ LinearNoStaticPat inner := by
  rcases h with ⟨hns, hty, hreg, hconst⟩
  exact ⟨bool_and_left hns, hreg, bool_and_right hns, hty, noDup_append_right hreg, hconst⟩

private theorem linear_sliceIter_sub {r : Region} {elem : Ty}
    (h : LinearNoStaticPat (.sliceIter r elem)) :
    regNoStatic r = true ∧ NoDup (collectRegVarsReg r ++ collectRegVars elem) ∧ LinearNoStaticPat elem := by
  rcases h with ⟨hns, hty, hreg, hconst⟩
  exact ⟨bool_and_left hns, hreg, bool_and_right hns, hty, noDup_append_right hreg, hconst⟩

private theorem linear_arrConst_sub {elem : Ty} {lp : Option Nat}
    (h : LinearNoStaticPat (.arrConst elem lp)) :
    LinearNoStaticPat elem ∧
    match lp with
    | none => True
    | some k => NoMem k (collectConstVars elem) := by
  rcases h with ⟨hns, hty, hreg, hconst⟩
  cases lp with
  | none => exact ⟨⟨hns, hty, hreg, hconst⟩, trivial⟩
  | some _ => exact ⟨⟨hns, hty, hreg, noDup_append_left hconst⟩, noDup_append_disjoint_rev hconst _ .head⟩

private theorem linear_reg_merge_exact {r : Region} {t : Ty} {gr : GroundRegion} {gt : GroundTy}
    (hns : regNoStatic r = true)
    (hnd : NoDup (collectRegVarsReg r ++ collectRegVars t))
    (σ_t : Subst) (ht : instTy σ_t t = gt) :
    ∃ σ : Subst,
      instRegion σ r = gr ∧
      instTy σ t = gt ∧
      σ.tySubst = σ_t.tySubst ∧
      σ.constSubst = σ_t.constSubst := by
  cases r with
  | rStatic => cases hns
  | rNamed id =>
    let σ' : Subst :=
      { regSubst := fun x => if Nat.beq x id then gr else σ_t.regSubst x
        tySubst := σ_t.tySubst
        constSubst := σ_t.constSubst }
    refine ⟨σ', ?_, ?_, rfl, rfl⟩
    · dsimp only [instRegion, σ']
      rw [nat_beq_refl]
      rfl
    · rw [← ht]
      apply instTy_agree_on_vars t
      refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩
      intro x hx
      dsimp only [σ']
      cases hnd with
      | cons hnm _ =>
        have hne : x ≠ id := noMem_symm_ne hnm hx
        rw [nat_beq_false_of_ne hne]
        rfl

/-- Surface applicability of pattern `p` to ground type `g` (`∃ σ, instTy σ p = g`). -/
noncomputable def MatchesSurfacePat (p : Ty) (g : GroundTy) : Prop :=
  ∃ σ : Subst, instTy σ p = g

/-- Post-erasure applicability of erased pattern `ep` to erased type `e` (`∃ τ, instErasedPat τ ep = e`). -/
noncomputable def MatchesErasedPat (ep : ErasedPat) (e : ErasedTy) : Prop :=
  ∃ τ : ErasedSubst, instErasedPat τ ep = e

/-- Forward direction (unconditional for any pattern `p`):
if `g` matches `p`, then `eraseRegions g` matches `erasePatRegions p`. -/
theorem matchesSurface_implies_matchesErased (p : Ty) (g : GroundTy)
    (h : MatchesSurfacePat p g) : MatchesErasedPat (erasePatRegions p) (eraseRegions g) := by
  rcases h with ⟨σ, hσ⟩
  refine ⟨eraseSubst σ, ?_⟩
  rw [← hσ]
  exact (instTy_erase_commutes σ p).symm

/-- Constructive linear pattern-matching inversion preserving erased variable bindings (`τ`)
on every variable appearing in `p`. -/
private theorem linear_match_preserves_erased_vars :
    (p : Ty) → (g : GroundTy) → (τ : ErasedSubst) →
    LinearNoStaticPat p →
    instErasedPat τ (erasePatRegions p) = eraseRegions g →
    ∃ σ : Subst,
      instTy σ p = g ∧
      (∀ v, Mem v (collectTyVars p) → eraseRegions (σ.tySubst v) = τ.tySubst v)
  | .var id, g, τ, _, hτ => by
    dsimp only [erasePatRegions, instErasedPat] at hτ
    refine ⟨{ defaultSubst with tySubst := fun v => if Nat.beq v id then g else defaultSubst.tySubst v },
      ?_, ?_⟩
    · dsimp only [instTy]
      rw [nat_beq_refl]
      rfl
    · intro v hm
      cases hm with
      | head =>
        dsimp only []
        rw [nat_beq_refl]
        exact hτ.symm
      | tail hm' => cases hm'
  | .prim _, g, _, _, hτ => by
    cases g with
    | prim _ =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with heq
      rw [← heq]
      exact ⟨defaultSubst, rfl, fun _ hm => by cases hm⟩
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .ref r inner, g, τ, hlin, hτ => by
    cases g with
    | ref gr ginner =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with hin_e
      rcases linear_ref_sub hlin with ⟨hrns, hrnd, hlin_in⟩
      rcases linear_match_preserves_erased_vars inner ginner τ hlin_in hin_e with
        ⟨σ_in, hσ_in, hv_in⟩
      rcases linear_reg_merge_exact hrns hrnd σ_in hσ_in with ⟨σ, hreg, hin, htyEq, _⟩
      refine ⟨σ, by dsimp only [instTy]; rw [hreg, hin], ?_⟩
      intro v hm
      rw [htyEq]
      exact hv_in v hm
    | prim _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .vecTy elem, g, τ, hlin, hτ => by
    cases g with
    | vecTy gelem =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with he
      rcases linear_match_preserves_erased_vars elem gelem τ hlin he with ⟨σ, hσ, hv⟩
      exact ⟨σ, by dsimp only [instTy]; rw [hσ], hv⟩
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .pair a b, g, τ, hlin, hτ => by
    cases g with
    | pair ga gb =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with hea heb
      rcases linear_match_preserves_erased_vars a ga τ (linear_pair_left hlin) hea with
        ⟨σ_a, hσ_a, hva⟩
      rcases linear_match_preserves_erased_vars b gb τ (linear_pair_right hlin) heb with
        ⟨σ_b, hσ_b, hvb⟩
      rcases linear_pair_disjoint_fwd hlin with ⟨hRegFwd, hTyFwd, hConstFwd⟩
      let σ := overrideSubst (collectRegVars b) (collectTyVars b) (collectConstVars b) σ_b σ_a
      refine ⟨σ, ?_, ?_⟩
      · dsimp only [instTy]
        have ha : instTy σ a = ga := by
          rw [instTy_override_disjoint σ_b σ_a b a hRegFwd hTyFwd hConstFwd]
          exact hσ_a
        have hb : instTy σ b = gb := by
          rw [instTy_override_self σ_b σ_a b]
          exact hσ_b
        rw [ha, hb]
      · intro v hm
        dsimp only [collectTyVars] at hm
        cases mem_append_elim hm with
        | inl hma =>
          dsimp only [σ, overrideSubst]
          rw [natMemBool_of_noMem (hTyFwd v hma)]
          exact hva v hma
        | inr hmb =>
          dsimp only [σ, overrideSubst]
          rw [natMemBool_of_mem hmb]
          exact hvb v hmb
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .sliceIter r elem, g, τ, hlin, hτ => by
    cases g with
    | sliceIter gr gelem =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with he
      rcases linear_sliceIter_sub hlin with ⟨hrns, hrnd, hlin_el⟩
      rcases linear_match_preserves_erased_vars elem gelem τ hlin_el he with
        ⟨σ_el, hσ_el, hvel⟩
      rcases linear_reg_merge_exact hrns hrnd σ_el hσ_el with ⟨σ, hreg, hel, htyEq, _⟩
      refine ⟨σ, by dsimp only [instTy]; rw [hreg, hel], ?_⟩
      intro v hm
      rw [htyEq]
      exact hvel v hm
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .intoIter elem, g, τ, hlin, hτ => by
    cases g with
    | intoIter gelem =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with he
      rcases linear_match_preserves_erased_vars elem gelem τ hlin he with ⟨σ, hσ, hv⟩
      exact ⟨σ, by dsimp only [instTy]; rw [hσ], hv⟩
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .adt0 _, g, _, _, hτ => by
    cases g with
    | adt0 _ =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with heq
      rw [← heq]
      exact ⟨defaultSubst, rfl, fun _ hm => by cases hm⟩
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .adt1r _ r, g, _, hlin, hτ => by
    cases g with
    | adt1r _ gr =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with heq
      rw [← heq]
      rcases hlin with ⟨hns, _, _, _⟩
      cases r with
      | rStatic => cases hns
      | rNamed rid =>
        refine ⟨{ defaultSubst with regSubst := fun x => if Nat.beq x rid then gr else .rLocal 0 },
          ?_, fun _ hm => by cases hm⟩
        dsimp only [instTy, instRegion]
        rw [nat_beq_refl]
        rfl
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1t _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .adt1t _ arg, g, τ, hlin, hτ => by
    cases g with
    | adt1t _ garg =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with hid harg_e
      rcases linear_match_preserves_erased_vars arg garg τ hlin harg_e with ⟨σ, hσ, hv⟩
      rw [← hid]
      exact ⟨σ, by dsimp only [instTy]; rw [hσ], hv⟩
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | arrConst _ _ => cases hτ
  | .arrConst elem none, g, τ, hlin, hτ => by
    cases g with
    | arrConst gelem _ =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with he hn
      rcases linear_arrConst_sub hlin with ⟨hlin_el, _⟩
      rcases linear_match_preserves_erased_vars elem gelem τ hlin_el he with ⟨σ, hσ, hv⟩
      rw [← hn]
      exact ⟨σ, by dsimp only [instTy]; rw [hσ], hv⟩
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ
  | .arrConst elem (some k), g, τ, hlin, hτ => by
    cases g with
    | arrConst gelem gn =>
      dsimp only [erasePatRegions, eraseRegions, instErasedPat] at hτ
      injection hτ with he _
      rcases linear_arrConst_sub hlin with ⟨hlin_el, hnoMem⟩
      rcases linear_match_preserves_erased_vars elem gelem τ hlin_el he with ⟨σ_el, hσ_el, hvel⟩
      let σ : Subst :=
        { regSubst := σ_el.regSubst
          tySubst := σ_el.tySubst
          constSubst := fun x => if Nat.beq x k then gn else σ_el.constSubst x }
      refine ⟨σ, ?_, hvel⟩
      dsimp only [instTy, σ]
      have hel : instTy σ elem = gelem := by
        rw [← hσ_el]
        apply instTy_agree_on_vars elem
        refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
        intro c hc
        dsimp only [σ]
        have hne : c ≠ k := by
          intro hck
          rw [hck] at hc
          exact mem_and_noMem_false hc hnoMem
        rw [nat_beq_false_of_ne hne]
        rfl
      rw [hel, nat_beq_refl]
      rfl
    | prim _ => cases hτ
    | ref _ _ => cases hτ
    | vecTy _ => cases hτ
    | pair _ _ => cases hτ
    | sliceIter _ _ => cases hτ
    | intoIter _ => cases hτ
    | adt0 _ => cases hτ
    | adt1r _ _ => cases hτ
    | adt1t _ _ => cases hτ

/-- Complete global substitution lifting: if `erasePatRegions p` matches `eraseRegions g`
under `τ` and `LinearNoStaticPat p`, then there exists `σ` matching `p` to `g` whose
region-erased type substitution equals `τ.tySubst` for EVERY `v : VarId`! -/
theorem linearNoStatic_lift_subst_exact (p : Ty) (g : GroundTy) (τ : ErasedSubst)
    (hlin : LinearNoStaticPat p)
    (hmatch : instErasedPat τ (erasePatRegions p) = eraseRegions g) :
    ∃ σ : Subst,
      instTy σ p = g ∧
      (∀ v : VarId, eraseRegions (σ.tySubst v) = τ.tySubst v) := by
  rcases linear_match_preserves_erased_vars p g τ hlin hmatch with ⟨σ₀, hσ₀, hv₀⟩
  let σ : Subst :=
    { regSubst := σ₀.regSubst
      tySubst := fun v => if natMemBool v (collectTyVars p) then σ₀.tySubst v else liftErasedWithLocal0 (τ.tySubst v)
      constSubst := σ₀.constSubst }
  refine ⟨σ, ?_, ?_⟩
  · rw [← hσ₀]
    apply instTy_agree_on_vars p
    refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl⟩
    intro v hm
    dsimp only [σ]
    rw [natMemBool_of_mem hm]
    rfl
  · intro v
    dsimp only [σ]
    cases hb : natMemBool v (collectTyVars p) with
    | true => exact hv₀ v (mem_of_natMemBool_true hb)
    | false => exact eraseRegions_liftErased (τ.tySubst v)

/-- Reverse direction (**Theorem: Linearity + No-`'static` Completeness**). -/
theorem linearNoStatic_matchesErased_implies_matchesSurface (p : Ty) (g : GroundTy)
    (hlin : LinearNoStaticPat p)
    (h : MatchesErasedPat (erasePatRegions p) (eraseRegions g)) :
    MatchesSurfacePat p g := by
  rcases h with ⟨τ, hτ⟩
  rcases linearNoStatic_lift_subst_exact p g τ hlin hτ with ⟨σ, hσ, _⟩
  exact ⟨σ, hσ⟩

/-- Bi-implication corollary: for every `LinearNoStaticPat p`, surface matching depends
strictly on `eraseRegions g`. -/
theorem linearNoStatic_matchesSurface_erasure_invariant (p : Ty) (g₁ g₂ : GroundTy)
    (hlin : LinearNoStaticPat p) (her : eraseRegions g₁ = eraseRegions g₂) :
    MatchesSurfacePat p g₁ ↔ MatchesSurfacePat p g₂ := by
  constructor
  · intro h1
    have he1 := matchesSurface_implies_matchesErased p g₁ h1
    rw [her] at he1
    exact linearNoStatic_matchesErased_implies_matchesSurface p g₂ hlin he1
  · intro h2
    have he2 := matchesSurface_implies_matchesErased p g₂ h2
    rw [← her] at he2
    exact linearNoStatic_matchesErased_implies_matchesSurface p g₁ hlin he2

/-!
## Part 3: Trait Registry, `TraitSpecializationKind`, Supertrait Elaboration, and `checkAlwaysApplicable`
-/

/-- Compiler specialization classification (`rustc_middle::ty::trait_def::TraitSpecializationKind`). -/
inductive TraitSpecKind where
  | none
  | alwaysApplicable
  | marker

/-- Predicate clauses on impl `where`-clauses (`ty::ClauseKind`). -/
inductive Clause where
  | traitVar (traitId : TraitId) (varId : VarId)
  | regionOutlivesStatic (regId : RegId)
  | regionEq (r₁ r₂ : RegId)
  | projEq (traitId : TraitId) (varId : VarId) (rhs : Ty)
  | globalTrait (traitId : TraitId) (groundSelf : GroundTy)
  | constHasType (constVar : Nat)

noncomputable def clauseBeq : Clause → Clause → Bool
  | .traitVar t₁ v₁, .traitVar t₂ v₂ => Nat.beq t₁ t₂ && Nat.beq v₁ v₂
  | .regionOutlivesStatic r₁, .regionOutlivesStatic r₂ => Nat.beq r₁ r₂
  | .regionEq a₁ b₁, .regionEq a₂ b₂ => Nat.beq a₁ a₂ && Nat.beq b₁ b₂
  | .projEq t₁ v₁ _, .projEq t₂ v₂ _ => Nat.beq t₁ t₂ && Nat.beq v₁ v₂
  | .globalTrait t₁ g₁, .globalTrait t₂ g₂ => Nat.beq t₁ t₂ && groundTyBeq g₁ g₂
  | .constHasType c₁, .constHasType c₂ => Nat.beq c₁ c₂
  | _, _ => false

/-- Trait registry modeling `TyCtxt` trait definitions, supertraits, and ground satisfaction. -/
structure TraitRegistry where
  specKind : TraitId → TraitSpecKind
  superTraits : TraitId → List TraitId
  hasMethods : TraitId → Bool
  traitSatisfied : TraitId → GroundTy → Prop
  traitSatErased : TraitId → ErasedTy → Prop

/-- Soundness invariant on a `TraitRegistry` (`#[rustc_specialization_trait]` contract):
every `.alwaysApplicable` trait's own satisfaction (and that of every supertrait it elaborates)
depends strictly on `eraseRegions g` and agrees with `traitSatErased`.
Notice `Copy` (`specKind = .none`) is NOT subject to this invariant! -/
noncomputable def SoundAlwaysApplicableRegistry (reg : TraitRegistry) : Prop :=
  ∀ tid : TraitId, reg.specKind tid = .alwaysApplicable →
    (∀ g : GroundTy, reg.traitSatisfied tid g ↔ reg.traitSatErased tid (eraseRegions g)) ∧
    (∀ sup : TraitId, Mem sup (reg.superTraits tid) →
      ∀ g : GroundTy, reg.traitSatisfied sup g ↔ reg.traitSatErased sup (eraseRegions g))

/-- Surface satisfaction of a single clause under substitution `σ` (`ty::Clause` evaluation). -/
noncomputable def ClauseHoldsSurface (reg : TraitRegistry) (σ : Subst) : Clause → Prop
  | .traitVar tid vid => reg.traitSatisfied tid (σ.tySubst vid)
  | .regionOutlivesStatic rid => σ.regSubst rid = .rStatic
  | .regionEq r₁ r₂ => σ.regSubst r₁ = σ.regSubst r₂
  | .projEq _ _ _ => True
  | .globalTrait tid g => reg.traitSatisfied tid g
  | .constHasType _ => True

/-- Modulo-region erased satisfaction of a single clause under `τ`. -/
noncomputable def ClauseHoldsErased (reg : TraitRegistry) (τ : ErasedSubst) : Clause → Prop
  | .traitVar tid vid => reg.traitSatErased tid (τ.tySubst vid)
  | .regionOutlivesStatic _ => True
  | .regionEq _ _ => True
  | .projEq _ _ _ => True
  | .globalTrait tid g => reg.traitSatErased tid (eraseRegions g)
  | .constHasType _ => True

/-- Expand supertraits onto `impl1_clauses` (mirrors `min_specialization.rs` L325-332).
Because `Copy: Clone`, specializing on `T: Copy` elaborates both `T: Copy` and `T: Clone`. -/
noncomputable def elaborateSuperClauses (reg : TraitRegistry) : List Clause → List Clause
  | [] => []
  | c :: cs =>
    match c with
    | .traitVar tid vid =>
      let sups := listMap (fun sup => Clause.traitVar sup vid) (reg.superTraits tid)
      c :: (sups ++ elaborateSuperClauses reg cs)
    | _ => c :: elaborateSuperClauses reg cs

/-- Expand supertraits of `AlwaysApplicable` clauses ONLY (`min_specialization.rs` L365-392).
Crucially, `Marker` (`#[unsafe(rustc_allow_lifetime_dependent_specialization)]`) does NOT
expand its supertraits into `impl2_clauses` (`spec-marker-supertraits.rs`)! -/
noncomputable def elaborateAlwaysApplicableSup (reg : TraitRegistry) : List Clause → List Clause
  | [] => []
  | c :: cs =>
    match c with
    | .traitVar tid vid =>
      match reg.specKind tid with
      | .alwaysApplicable =>
        let sups := listMap (fun sup => Clause.traitVar sup vid) (reg.superTraits tid)
        sups ++ elaborateAlwaysApplicableSup reg cs
      | _ => elaborateAlwaysApplicableSup reg cs
    | _ => elaborateAlwaysApplicableSup reg cs

/-- Specialization impl node modeling `impl<...> Tr for <headerSelf>`. -/
structure ImplDef where
  id : ImplId
  headerSelf : Ty
  unconstrainedHeader : Ty
  bounds : List Clause
  hasItems : Bool
  hasDefaultType : Bool
  hasDefaultImpl : Bool
  hasAsyncOrRpitit : Bool
  assocIsDefault : Bool
  assocSizeBytes : Option Nat
  methodTag : Nat

noncomputable def clauseInList (c : Clause) (clauses : List Clause) : Bool :=
  listAny (clauseBeq c) clauses

/-- `check_specialization_on` (`min_specialization.rs` L404-457). -/
noncomputable def checkClauseAllowed (reg : TraitRegistry) (baseClauses : List Clause)
    (allowMarker : Bool) (c : Clause) : Bool :=
  if clauseInList c baseClauses then
    true
  else
    match c with
    | .globalTrait _ _ => true
    | .constHasType _ => true
    | .traitVar tid _ =>
      match reg.specKind tid with
      | .alwaysApplicable => true
      | .marker => allowMarker
      | .none => false
    | .regionOutlivesStatic _ => false
    | .regionEq _ _ => false
    | .projEq _ _ _ => false

/-- Complete executable `check_always_applicable` decision procedure (`min_specialization.rs`
L114-457 + `feature_gate.rs` L392-401 + `check.rs` L1445-1472). -/
noncomputable def checkAlwaysApplicableBool (reg : TraitRegistry) (parentBounds : List Clause)
    (allowMarker : Bool) (imp : ImplDef) : Bool :=
  let parentElab :=
    elaborateSuperClauses reg parentBounds ++
    elaborateAlwaysApplicableSup reg imp.bounds
  let childElab := elaborateSuperClauses reg imp.bounds
  imp.hasItems &&
  boolNot imp.hasDefaultType &&
  boolNot imp.hasDefaultImpl &&
  boolNot imp.hasAsyncOrRpitit &&
  linearNoStaticCheck imp.unconstrainedHeader &&
  listAll (checkClauseAllowed reg parentElab allowMarker) childElab

/-- Strict Prop-level soundness predicate (`allowMarker = false`, i.e., pure `AlwaysApplicable`
without the explicitly-documented `rustc_allow_lifetime_dependent_specialization` marker escape hatch):
guarantees `ImplAppliesSurface reg imp g ↔ ImplAppliesErased reg imp (eraseRegions g)`! -/
noncomputable def StrictAlwaysApplicableImpl (reg : TraitRegistry) (imp : ImplDef) : Prop :=
  imp.hasItems = true ∧
  imp.hasDefaultType = false ∧
  imp.hasDefaultImpl = false ∧
  imp.hasAsyncOrRpitit = false ∧
  LinearNoStaticPat imp.headerSelf ∧
  ∀ c : Clause, Mem c imp.bounds →
    match c with
    | .traitVar tid _ => reg.specKind tid = .alwaysApplicable
    | .globalTrait tid _ =>
        ∀ g : GroundTy, reg.traitSatisfied tid g ↔ reg.traitSatErased tid (eraseRegions g)
    | .constHasType _ => True
    | _ => False

/-- Surface impl applicability: `g` matches `imp.headerSelf` via `σ` AND all `imp.bounds` hold. -/
noncomputable def ImplAppliesSurface (reg : TraitRegistry) (imp : ImplDef) (g : GroundTy) : Prop :=
  ∃ σ : Subst, instTy σ imp.headerSelf = g ∧ (∀ c : Clause, Mem c imp.bounds → ClauseHoldsSurface reg σ c)

/-- Post-erasure monomorphization applicability: `eraseRegions g` matches `erasePatRegions imp.headerSelf`
and all erased bounds hold. -/
noncomputable def ImplAppliesErased (reg : TraitRegistry) (imp : ImplDef) (e : ErasedTy) : Prop :=
  ∃ τ : ErasedSubst, instErasedPat τ (erasePatRegions imp.headerSelf) = e ∧
    (∀ c : Clause, Mem c imp.bounds → ClauseHoldsErased reg τ c)

private theorem strict_clause_surface_iff_erased (reg : TraitRegistry)
    (hreg : SoundAlwaysApplicableRegistry reg) (imp : ImplDef)
    (hstrict : StrictAlwaysApplicableImpl reg imp)
    (σ : Subst) :
    (∀ c : Clause, Mem c imp.bounds → ClauseHoldsSurface reg σ c) ↔
    (∀ c : Clause, Mem c imp.bounds → ClauseHoldsErased reg (eraseSubst σ) c) := by
  rcases hstrict with ⟨_, _, _, _, _, hbounds⟩
  constructor
  · intro hs c hmc
    have hspec := hbounds c hmc
    have hcs := hs c hmc
    cases c with
    | traitVar tid vid =>
      have hk : reg.specKind tid = .alwaysApplicable := hspec
      rcases hreg tid hk with ⟨heq, _⟩
      dsimp only [ClauseHoldsSurface] at hcs
      dsimp only [ClauseHoldsErased, eraseSubst]
      exact (heq (σ.tySubst vid)).mp hcs
    | globalTrait tid g =>
      dsimp only [ClauseHoldsSurface] at hcs
      dsimp only [ClauseHoldsErased]
      exact (hspec g).mp hcs
    | constHasType _ => trivial
    | regionOutlivesStatic _ => cases hspec
    | regionEq _ _ => cases hspec
    | projEq _ _ _ => cases hspec
  · intro he c hmc
    have hspec := hbounds c hmc
    have hce := he c hmc
    cases c with
    | traitVar tid vid =>
      have hk : reg.specKind tid = .alwaysApplicable := hspec
      rcases hreg tid hk with ⟨heq, _⟩
      dsimp only [ClauseHoldsErased, eraseSubst] at hce
      dsimp only [ClauseHoldsSurface]
      exact (heq (σ.tySubst vid)).mpr hce
    | globalTrait tid g =>
      dsimp only [ClauseHoldsErased] at hce
      dsimp only [ClauseHoldsSurface]
      exact (hspec g).mpr hce
    | constHasType _ => trivial
    | regionOutlivesStatic _ => cases hspec
    | regionEq _ _ => cases hspec
    | projEq _ _ _ => cases hspec

/-- **Exact Equivalence (`strict_impl_surface_iff_erased`)**:
For every `StrictAlwaysApplicableImpl` over a sound registry, surface typechecking
applicability on `g` holds if and only if post-erasure monomorphization applicability
holds on `eraseRegions g`! -/
theorem strict_impl_surface_iff_erased (reg : TraitRegistry)
    (hreg : SoundAlwaysApplicableRegistry reg) (imp : ImplDef)
    (hstrict : StrictAlwaysApplicableImpl reg imp) (g : GroundTy) :
    ImplAppliesSurface reg imp g ↔ ImplAppliesErased reg imp (eraseRegions g) := by
  constructor
  · rintro ⟨σ, hinst, hc⟩
    refine ⟨eraseSubst σ, ?_, ?_⟩
    · rw [← hinst]
      exact (instTy_erase_commutes σ imp.headerSelf).symm
    · exact (strict_clause_surface_iff_erased reg hreg imp hstrict σ).mp hc
  · rintro ⟨τ, hinst, hc⟩
    have hlin := hstrict.2.2.2.2.1
    rcases linearNoStatic_lift_subst_exact imp.headerSelf g τ hlin hinst with ⟨σ, hσ, heqTy⟩
    refine ⟨σ, hσ, ?_⟩
    apply (strict_clause_surface_iff_erased reg hreg imp hstrict σ).mpr
    intro c hmc
    have hce := hc c hmc
    have hspec := hstrict.2.2.2.2.2 c hmc
    cases c with
    | traitVar tid vid =>
      dsimp only [ClauseHoldsErased, eraseSubst] at *
      rw [heqTy vid]
      exact hce
    | globalTrait _ _ => exact hce
    | constHasType _ => trivial
    | regionOutlivesStatic _ => cases hspec
    | regionEq _ _ => cases hspec
    | projEq _ _ _ => cases hspec

/-- **Lifetime-Erasure Invariance for Any Single Strictly Always-Applicable Impl**:
If `eraseRegions g₁ = eraseRegions g₂`, then `ImplAppliesSurface reg imp g₁ ↔ ImplAppliesSurface reg imp g₂`. -/
theorem strict_impl_applicability_erasure_invariant (reg : TraitRegistry)
    (hreg : SoundAlwaysApplicableRegistry reg) (imp : ImplDef)
    (hstrict : StrictAlwaysApplicableImpl reg imp)
    (g₁ g₂ : GroundTy) (her : eraseRegions g₁ = eraseRegions g₂) :
    ImplAppliesSurface reg imp g₁ ↔ ImplAppliesSurface reg imp g₂ := by
  rw [strict_impl_surface_iff_erased reg hreg imp hstrict g₁,
      strict_impl_surface_iff_erased reg hreg imp hstrict g₂,
      her]

/-!
## Part 4: Specialization-Graph Ordering (`SpecializesModuloRegions`),
## Tree Antisymmetry, `E0119` Conflict Detection, & Most-Specific-Impl Uniqueness
-/

/-- Region-blind specialization subset relation (`tcx.specializes((i₁, i₂))` in
`compiler/rustc_trait_selection/src/traits/specialize/mod.rs` L239-388):
every lifetime-erased ground type matching `i₁` also matches `i₂` modulo regions. -/
noncomputable def SpecializesModuloRegions (reg : TraitRegistry) (i₁ i₂ : ImplDef) : Prop :=
  ∀ e : ErasedTy, ImplAppliesErased reg i₁ e → ImplAppliesErased reg i₂ e

/-- Strict specialization relation (`le && !ge` in `specialization_graph::Children::insert`). -/
noncomputable def StrictSpec (reg : TraitRegistry) (i₁ i₂ : ImplDef) : Prop :=
  SpecializesModuloRegions reg i₁ i₂ ∧ ¬ SpecializesModuloRegions reg i₂ i₁

/-- Tree irreflexivity: no impl strictly specializes itself. -/
theorem strictSpec_irrefl (reg : TraitRegistry) (i : ImplDef) :
    ¬ StrictSpec reg i i := by
  intro h
  exact h.2 h.1

/-- Tree asymmetry: `StrictSpec reg a b → ¬ StrictSpec reg b a`. -/
theorem strictSpec_asymm (reg : TraitRegistry) (a b : ImplDef)
    (hab : StrictSpec reg a b) : ¬ StrictSpec reg b a := by
  intro hba
  exact hab.2 hba.1

/-- Transitivity of `SpecializesModuloRegions`. -/
theorem specializes_trans (reg : TraitRegistry) (a b c : ImplDef)
    (hab : SpecializesModuloRegions reg a b)
    (hbc : SpecializesModuloRegions reg b c) :
    SpecializesModuloRegions reg a c :=
  fun e ha => hbc e (hab e ha)

/-- `StrictSpec` is transitive when strictness holds on either step! -/
theorem strictSpec_trans_left (reg : TraitRegistry) (a b c : ImplDef)
    (hab : StrictSpec reg a b) (hbc : SpecializesModuloRegions reg b c) :
    StrictSpec reg a c := by
  refine ⟨specializes_trans reg a b c hab.1 hbc, ?_⟩
  intro hca
  exact hab.2 (specializes_trans reg b c a hbc hca)

/-- `Children::insert` outcome (`specialization_graph.rs` L26-35, L140-163). -/
inductive ChildrenInsertOutcome where
  | becameNewSibling
  | shouldRecurseOnChild
  | replaceChildAsParent
  | conflictE0119

/-- Exact `le == ge` branching rule inside `specialization_graph::Children::insert`:
whenever two impls overlap (`overlap = true`) and `le == ge` (either both `true` due to
region blindness, or both `false` in a diamond conflict), emit `E0119`! -/
noncomputable def childrenInsertDecision (overlap le ge : Bool) : ChildrenInsertOutcome :=
  if overlap then
    match le, ge with
    | true, true => .conflictE0119
    | false, false => .conflictE0119
    | true, false => .shouldRecurseOnChild
    | false, true => .replaceChildAsParent
  else
    .becameNewSibling

/-- Theorem: whenever `le = true` and `ge = true` (region-blind mutual implication),
`Children::insert` unconditionally emits `E0119`! -/
theorem childrenInsert_mutual_specializes_e0119 :
    childrenInsertDecision true true true = .conflictE0119 :=
  rfl

/-- Theorem: whenever `le = false` and `ge = false` on overlapping impls (diamond conflict),
`Children::insert` unconditionally emits `E0119`! -/
theorem childrenInsert_diamond_conflict_e0119 :
    childrenInsertDecision true false false = .conflictE0119 :=
  rfl

/-- Concrete Layer-1 Witness (`b01`): `impl<'a, 'b> Tr for (&'a u8, &'b u8)` vs
`impl<'a> Tr for (&'a u8, &'a u8)` have identical erased patterns `(.pair (.ref (.prim 1)) (.ref (.prim 1)))`,
so both satisfy `SpecializesModuloRegions` of each other (`le = true ∧ ge = true`), triggering `E0119`! -/
noncomputable def implPairDistinctLt : ImplDef :=
  { id := 1
    headerSelf := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 1) (.prim 1))
    unconstrainedHeader := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 1) (.prim 1))
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 1 }

noncomputable def implPairEqualLt : ImplDef :=
  { id := 2
    headerSelf := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 0) (.prim 1))
    unconstrainedHeader := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 0) (.prim 1))
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 2 }

theorem lifetime_eq_pairs_trigger_e0119 (reg : TraitRegistry) :
    SpecializesModuloRegions reg implPairEqualLt implPairDistinctLt ∧
    SpecializesModuloRegions reg implPairDistinctLt implPairEqualLt ∧
    childrenInsertDecision true true true = .conflictE0119 := by
  refine ⟨?_, ?_, rfl⟩
  · intro e ⟨τ, hτ, _⟩
    refine ⟨τ, hτ, fun _ hm => by cases hm⟩
  · intro e ⟨τ, hτ, _⟩
    refine ⟨τ, hτ, fun _ hm => by cases hm⟩

/-- Concrete Layer-1 Witness (`b02`): `impl<T> Tr for T` vs `impl<T: 'static> Tr for T`
also satisfy mutual `SpecializesModuloRegions` because `.regionOutlivesStatic` holds trivially
under `ClauseHoldsErased` (`specializes` never resolves regions), triggering `E0119`! -/
noncomputable def implBlanket : ImplDef :=
  { id := 10
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 10 }

noncomputable def implBlanketStaticBound : ImplDef :=
  { id := 11
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.regionOutlivesStatic 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 11 }

theorem static_bound_triggers_e0119 (reg : TraitRegistry) :
    SpecializesModuloRegions reg implBlanketStaticBound implBlanket ∧
    SpecializesModuloRegions reg implBlanket implBlanketStaticBound ∧
    childrenInsertDecision true true true = .conflictE0119 := by
  refine ⟨?_, ?_, rfl⟩
  · intro e ⟨τ, hτ, _⟩
    refine ⟨τ, hτ, fun _ hm => by cases hm⟩
  · intro e ⟨τ, hτ, _⟩
    refine ⟨τ, hτ, fun c hm => by
      cases hm with
      | head => trivial
      | tail hm' => cases hm'⟩

/-- Specialization-Graph Chain ordering (matching `rustc`'s specialization chain invariant:
`specialize/mod.rs` L4-5 *"If any two impls overlap, one must be a strict subset of the other"*). -/
noncomputable def ChainDistinctIds (chain : List ImplDef) : Prop :=
  NoDup (listMap (fun i => i.id) chain)

/-- A list of impls `[i_n, ..., i_1]` ordered from most-specific head to least-specific tail:
every earlier impl strictly specializes every later impl in the chain! -/
inductive IsSpecializationChain (reg : TraitRegistry) : List ImplDef → Prop where
  | nil : IsSpecializationChain reg []
  | cons {hd : ImplDef} {tl : List ImplDef} :
      (∀ t : ImplDef, Mem t tl → StrictSpec reg hd t) →
      IsSpecializationChain reg tl →
      IsSpecializationChain reg (hd :: tl)

/-- Every member of a `StrictSpec`-ordered chain has distinct `ImplDef`s (`hd ≠ t` in tail),
proving acyclicity (zero specialization cycles)! -/
theorem spec_chain_acyclic (reg : TraitRegistry) :
    (chain : List ImplDef) → IsSpecializationChain reg chain →
    ∀ hd tl, chain = hd :: tl → ∀ t, Mem t tl → hd ≠ t := by
  intro chain hchain hd tl heq t hmt
  rw [heq] at hchain
  cases hchain with
  | cons hstrict _ =>
    intro hsame
    have hs := hstrict t hmt
    rw [hsame] at hs
    exact strictSpec_irrefl reg t hs

/-- Most-specific applicable impl in an ordered specialization chain (`hd` first). -/
noncomputable def IsMostSpecificInChain (reg : TraitRegistry) (chain : List ImplDef)
    (g : GroundTy) (winner : ImplDef) : Prop :=
  Mem winner chain ∧
  ImplAppliesSurface reg winner g ∧
  (∀ other : ImplDef, Mem other chain → ImplAppliesSurface reg other g →
    other = winner ∨ StrictSpec reg winner other)

/-- **Most-Specific-Impl Uniqueness Theorem (`most_specific_impl_unique`)**:
In any `IsSpecializationChain`, any two maximal applicable impls `w₁, w₂` for ground type `g`
must be identical (`w₁ = w₂`)! -/
theorem most_specific_impl_unique (reg : TraitRegistry) (chain : List ImplDef) (g : GroundTy)
    (w₁ w₂ : ImplDef)
    (h₁ : IsMostSpecificInChain reg chain g w₁)
    (h₂ : IsMostSpecificInChain reg chain g w₂) :
    w₁ = w₂ := by
  rcases h₁ with ⟨hm₁, ha₁, hmax₁⟩
  rcases h₂ with ⟨hm₂, ha₂, hmax₂⟩
  cases hmax₁ w₂ hm₂ ha₂ with
  | inl heq => exact heq.symm
  | inr hstrict12 =>
    cases hmax₂ w₁ hm₁ ha₁ with
    | inl heq => exact heq
    | inr hstrict21 => exact False.elim (strictSpec_asymm reg w₁ w₂ hstrict12 hstrict21)

/-!
## Part 5: Flagship Lifetime-Erasure Invariance & Typeck–Monomorphization Equivalence Theorem
-/

/-- Abstract decidable-or-relational dispatch over an ordered specialization chain `[most_spec, ..., base]`:
returns the `methodTag` of the first impl in `chain` that applies on surface `g`, or `fallback`.
Modeled cleanly as a deterministic Prop/Spec relation `DispatchesSurface` and `DispatchesErased`. -/
inductive DispatchesSurface (reg : TraitRegistry) (fallback : Nat) : List ImplDef → GroundTy → Nat → Prop where
  | nil (g : GroundTy) : DispatchesSurface reg fallback [] g fallback
  | hit {hd : ImplDef} {tl : List ImplDef} {g : GroundTy} :
      ImplAppliesSurface reg hd g →
      DispatchesSurface reg fallback (hd :: tl) g hd.methodTag
  | miss {hd : ImplDef} {tl : List ImplDef} {g : GroundTy} {res : Nat} :
      ¬ ImplAppliesSurface reg hd g →
      DispatchesSurface reg fallback tl g res →
      DispatchesSurface reg fallback (hd :: tl) g res

inductive DispatchesErased (reg : TraitRegistry) (fallback : Nat) : List ImplDef → ErasedTy → Nat → Prop where
  | nil (e : ErasedTy) : DispatchesErased reg fallback [] e fallback
  | hit {hd : ImplDef} {tl : List ImplDef} {e : ErasedTy} :
      ImplAppliesErased reg hd e →
      DispatchesErased reg fallback (hd :: tl) e hd.methodTag
  | miss {hd : ImplDef} {tl : List ImplDef} {e : ErasedTy} {res : Nat} :
      ¬ ImplAppliesErased reg hd e →
      DispatchesErased reg fallback tl e res →
      DispatchesErased reg fallback (hd :: tl) e res

/-- Determinism of `DispatchesSurface`: each `(chain, g)` has at most one dispatch result. -/
theorem dispatchesSurface_deterministic (reg : TraitRegistry) (fallback : Nat) :
    (chain : List ImplDef) → (g : GroundTy) → (r₁ r₂ : Nat) →
    DispatchesSurface reg fallback chain g r₁ →
    DispatchesSurface reg fallback chain g r₂ →
    r₁ = r₂
  | [], _, _, _, .nil _, .nil _ => rfl
  | _ :: _, _, _, _, .hit _, .hit _ => rfl
  | _ :: _, _, _, _, .hit ha, .miss hna _ => False.elim (hna ha)
  | _ :: _, _, _, _, .miss hna _, .hit ha => False.elim (hna ha)
  | _ :: tl, g, r₁, r₂, .miss _ d₁, .miss _ d₂ =>
    dispatchesSurface_deterministic reg fallback tl g r₁ r₂ d₁ d₂

/-- Determinism of `DispatchesErased`. -/
theorem dispatchesErased_deterministic (reg : TraitRegistry) (fallback : Nat) :
    (chain : List ImplDef) → (e : ErasedTy) → (r₁ r₂ : Nat) →
    DispatchesErased reg fallback chain e r₁ →
    DispatchesErased reg fallback chain e r₂ →
    r₁ = r₂
  | [], _, _, _, .nil _, .nil _ => rfl
  | _ :: _, _, _, _, .hit _, .hit _ => rfl
  | _ :: _, _, _, _, .hit ha, .miss hna _ => False.elim (hna ha)
  | _ :: _, _, _, _, .miss hna _, .hit ha => False.elim (hna ha)
  | _ :: tl, e, r₁, r₂, .miss _ d₁, .miss _ d₂ =>
    dispatchesErased_deterministic reg fallback tl e r₁ r₂ d₁ d₂

/-- Chain-wide strict always-applicability invariant. -/
noncomputable def AllStrictAlwaysApplicable (reg : TraitRegistry) : List ImplDef → Prop
  | [] => True
  | imp :: rest => StrictAlwaysApplicableImpl reg imp ∧ AllStrictAlwaysApplicable reg rest

/-- **Flagship Theorem 1 (`min_specialization_surface_equals_monomorphization`)**:
For every `alwaysApplicable` specialization chain `chain` over a sound `TraitRegistry`,
surface typeck dispatch on `g` agrees **bi-directionally** with post-erasure monomorphization
dispatch on `eraseRegions g`! -/
theorem min_specialization_surface_equals_monomorphization
    (reg : TraitRegistry) (hreg : SoundAlwaysApplicableRegistry reg) (fallback : Nat) :
    (chain : List ImplDef) → AllStrictAlwaysApplicable reg chain →
    (g : GroundTy) → (res : Nat) →
    (DispatchesSurface reg fallback chain g res ↔
     DispatchesErased reg fallback chain (eraseRegions g) res)
  | [], _, g, res => by
    constructor
    · intro h
      cases h
      exact .nil (eraseRegions g)
    · intro h
      cases h
      exact .nil g
  | hd :: tl, ⟨hhd, htl⟩, g, res => by
    have hiff := strict_impl_surface_iff_erased reg hreg hd hhd g
    have ih := min_specialization_surface_equals_monomorphization reg hreg fallback tl htl g res
    constructor
    · intro hs
      cases hs with
      | hit ha => exact .hit (hiff.mp ha)
      | miss hna ds => exact .miss (fun he => hna (hiff.mpr he)) (ih.mp ds)
    · intro he
      cases he with
      | hit ha => exact .hit (hiff.mpr ha)
      | miss hna de => exact .miss (fun hs => hna (hiff.mp hs)) (ih.mpr de)

/-- **Lifetime-Erasure Invariance Theorem (`lifetime_erasure_invariance_theorem`)**:
For every `alwaysApplicable` specialization chain `chain` and any two ground types `g₁, g₂`
with identical region erasure (`eraseRegions g₁ = eraseRegions g₂`), surface dispatch produces
identical results (`r₁ = r₂`) — zero soundness gap between typechecking and monomorphization! -/
theorem lifetime_erasure_invariance_theorem
    (reg : TraitRegistry) (hreg : SoundAlwaysApplicableRegistry reg) (fallback : Nat)
    (chain : List ImplDef) (hchain : AllStrictAlwaysApplicable reg chain)
    (g₁ g₂ : GroundTy) (her : eraseRegions g₁ = eraseRegions g₂)
    (r₁ r₂ : Nat)
    (d₁ : DispatchesSurface reg fallback chain g₁ r₁)
    (d₂ : DispatchesSurface reg fallback chain g₂ r₂) :
    r₁ = r₂ := by
  have e₁ := (min_specialization_surface_equals_monomorphization reg hreg fallback chain hchain g₁ r₁).mp d₁
  have e₂ := (min_specialization_surface_equals_monomorphization reg hreg fallback chain hchain g₂ r₂).mp d₂
  rw [her] at e₁
  exact dispatchesErased_deterministic reg fallback chain (eraseRegions g₂) r₁ r₂ e₁ e₂

/-- **Zero Soundness Gap Witness (`zero_typeck_monomorphization_soundness_gap`)**:
Whenever monomorphization selects an impl `hd` (rather than `miss`) for `eraseRegions g` in
an `alwaysApplicable` specialization chain, the surface applicability and predicates of `hd`
are guaranteed to hold for the un-erased type `g`! -/
theorem zero_typeck_monomorphization_soundness_gap
    (reg : TraitRegistry) (hreg : SoundAlwaysApplicableRegistry reg)
    (imp : ImplDef) (himp : StrictAlwaysApplicableImpl reg imp)
    (g : GroundTy) (he : ImplAppliesErased reg imp (eraseRegions g)) :
    ImplAppliesSurface reg imp g :=
  (strict_impl_surface_iff_erased reg hreg imp himp g).mpr he

/-!
## Part 6: Concrete Standard Library Model (`Copy` Rejection vs. `Sized`/`TrustedStep`/`TrustedLen`/`TrivialClone`)
-/

-- Canonical Trait IDs matching `library/core`
noncomputable def tidCopy : TraitId := 1
noncomputable def tidClone : TraitId := 2
noncomputable def tidSized : TraitId := 3
noncomputable def tidMetaSized : TraitId := 4
noncomputable def tidPointeeSized : TraitId := 5
noncomputable def tidStep : TraitId := 6
noncomputable def tidTrustedStep : TraitId := 7
noncomputable def tidIterator : TraitId := 8
noncomputable def tidTrustedLen : TraitId := 9
noncomputable def tidFusedIterator : TraitId := 10
noncomputable def tidTrivialClone : TraitId := 11
noncomputable def tidBytewiseEq : TraitId := 12

-- Canonical ADT IDs (`OnlyStaticCopy<'a>`, `Range<T>`)
noncomputable def adtOnlyStaticCopy : AdtId := 100
noncomputable def adtRange : AdtId := 101

/-- Concrete ground satisfaction of `Copy`:
`u32` (`prim 1`), `bool` (`prim 2`), `&'r T`, and `OnlyStaticCopy<'static>` satisfy `Copy`,
whereas `OnlyStaticCopy<'local_k>` does NOT satisfy `Copy` (mirroring probe `b05b`/`c05`)! -/
noncomputable def stdCopySat : GroundTy → Prop
  | .prim _ => True
  | .ref _ _ => True
  | .adt1r id r => id = adtOnlyStaticCopy ∧ r = .rStatic
  | _ => False

/-- Concrete erased satisfaction of `Copy` (when region-blind specialization ignores `'a`):
`OnlyStaticCopy` appears `Copy`-capable once regions are erased! -/
noncomputable def stdCopySatErased : ErasedTy → Prop
  | .prim _ => True
  | .ref _ => True
  | .adt1r id => id = adtOnlyStaticCopy
  | _ => False

/-- Concrete satisfaction of `Sized` / `MetaSized` / `PointeeSized` / `TrustedStep`:
depends purely on erased type constructors (`prim`, `ref`, etc.), invariant under region erasure. -/
noncomputable def stdSizedSatErased : ErasedTy → Prop
  | .prim _ => True
  | .ref _ => True
  | .vecTy _ => True
  | .pair _ _ => True
  | .sliceIter _ => True
  | .intoIter _ => True
  | .adt0 _ => True
  | .adt1r _ => True
  | .adt1t _ _ => True
  | .arrConst _ _ => True

noncomputable def stdTrustedStepSatErased : ErasedTy → Prop
  | .prim 1 => True  -- u32
  | _ => False

noncomputable def stdRegistry : TraitRegistry :=
  { specKind := fun tid =>
      if Nat.beq tid tidSized || Nat.beq tid tidMetaSized || Nat.beq tid tidPointeeSized ||
         Nat.beq tid tidTrustedStep || Nat.beq tid tidBytewiseEq then
        .alwaysApplicable
      else if Nat.beq tid tidTrustedLen || Nat.beq tid tidFusedIterator ||
              Nat.beq tid tidTrivialClone then
        .marker
      else
        .none
    superTraits := fun tid =>
      if Nat.beq tid tidCopy then [tidClone]
      else if Nat.beq tid tidClone then [tidSized]
      else if Nat.beq tid tidSized then [tidMetaSized]
      else if Nat.beq tid tidMetaSized then [tidPointeeSized]
      else if Nat.beq tid tidTrustedStep then [tidStep, tidCopy]
      else if Nat.beq tid tidTrustedLen then [tidIterator]
      else if Nat.beq tid tidFusedIterator then [tidIterator]
      else if Nat.beq tid tidTrivialClone then [tidClone]
      else []
    hasMethods := fun tid =>
      if Nat.beq tid tidClone || Nat.beq tid tidStep || Nat.beq tid tidIterator then true
      else false
    traitSatisfied := fun tid g =>
      if Nat.beq tid tidCopy then stdCopySat g
      else if Nat.beq tid tidClone then stdCopySat g
      else if Nat.beq tid tidSized || Nat.beq tid tidMetaSized || Nat.beq tid tidPointeeSized then
        stdSizedSatErased (eraseRegions g)
      else if Nat.beq tid tidTrustedStep || Nat.beq tid tidStep then
        stdTrustedStepSatErased (eraseRegions g)
      else
        False
    traitSatErased := fun tid e =>
      if Nat.beq tid tidCopy || Nat.beq tid tidClone then stdCopySatErased e
      else if Nat.beq tid tidSized || Nat.beq tid tidMetaSized || Nat.beq tid tidPointeeSized then
        stdSizedSatErased e
      else if Nat.beq tid tidTrustedStep || Nat.beq tid tidStep then
        stdTrustedStepSatErased e
      else
        False }

-- Helper: `impl<T> Tr for T` (base) specialized by `impl<T: Copy> Tr for T`
noncomputable def implCopySpec : ImplDef :=
  { id := 20
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidCopy 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := some 32
    methodTag := 20 }

noncomputable def implCloneSpec : ImplDef :=
  { id := 21
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidClone 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 21 }

noncomputable def implSizedSpec : ImplDef :=
  { id := 22
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidSized 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 22 }

noncomputable def implTrustedStepSpec : ImplDef :=
  { id := 23
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidTrustedStep 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 23 }

noncomputable def implTrustedLenSpec : ImplDef :=
  { id := 24
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidTrustedLen 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 24 }

noncomputable def implTrivialCloneSpec : ImplDef :=
  { id := 25
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := [.traitVar tidTrivialClone 0]
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 25 }

/-- **Theorem (`copy_and_clone_rejected_under_min_specialization`)**:
1. `impl<T: Copy> Tr for T` over `impl<T> Tr for T` is REJECTED by `checkAlwaysApplicableBool`.
2. Furthermore, BOTH `T: Copy` AND its elaborated supertrait `T: Clone` individually fail
   `checkClauseAllowed` (explaining the 2 compiler errors in live probe `b05`), whereas
   `T: Sized` passes! -/
theorem copy_and_clone_rejected_under_min_specialization :
    checkAlwaysApplicableBool stdRegistry [] true implCopySpec = false ∧
    checkClauseAllowed stdRegistry [] true (.traitVar tidCopy 0) = false ∧
    checkClauseAllowed stdRegistry [] true (.traitVar tidClone 0) = false ∧
    checkAlwaysApplicableBool stdRegistry [] true implCloneSpec = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem (`sized_and_trusted_step_admitted`)**:
Both `impl<T: Sized> Tr for T` AND `impl<T: TrustedStep> Tr for T` over `impl<T> Tr for T`
PASS `checkAlwaysApplicableBool` (even though `TrustedStep` has supertrait `: Step + Copy`!),
because `elaborateAlwaysApplicableSup` elaborates `TrustedStep`'s supertraits (`Step`, `Copy`)
into `parentElab` while `Copy` itself lacks `#[rustc_specialization_trait]`! -/
theorem sized_and_trusted_step_admitted :
    checkAlwaysApplicableBool stdRegistry [] false implSizedSpec = true ∧
    checkAlwaysApplicableBool stdRegistry [] false implTrustedStepSpec = true :=
  ⟨rfl, rfl⟩

/-- **Theorem (`trusted_len_marker_supertrait_discrimination`)**:
`impl<I: TrustedLen> Tr for I` FAILS over `impl<I> Tr for I` (because `TrustedLen` is
`Marker`, so its supertrait `Iterator` is NOT elaborated into `parentElab`, matching live probe `b07`),
AND PASSES over `impl<I: Iterator> Tr for I` (where `Iterator` is already in `parentBounds`,
matching live probe `a03`)! Similarly `TrivialClone` passes over `T: Clone` (`RcFromSlice`)! -/
theorem trusted_len_marker_supertrait_discrimination :
    checkAlwaysApplicableBool stdRegistry [] true implTrustedLenSpec = false ∧
    checkAlwaysApplicableBool stdRegistry [.traitVar tidIterator 0] true implTrustedLenSpec = true ∧
    checkAlwaysApplicableBool stdRegistry [] true implTrivialCloneSpec = false ∧
    checkAlwaysApplicableBool stdRegistry [.traitVar tidClone 0] true implTrivialCloneSpec = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Concrete witnesses for Layer-2 rejections:
1. `impl<T> Tr for (T, T)` fails `linearNoStaticCheck` (`b09`).
2. `impl<'a> Tr for (&'a u8, &'a u8)` fails `linearNoStaticCheck` (`b10`).
3. `impl Tr for &'static i32` fails `linearNoStaticCheck` (`b03`).
4. `impl<T> SpecCollect<T> for IntoIter<T>` passes `linearNoStaticCheck` because `T` is
   constrained in parent `impl<T, I: Iterator<Item = T>>` so `unconstrainedHeader = IntoIter<T>` (`a02`).
5. `impl<T> Tr for T` + `impl Tr for u32 {}` (empty) fails `checkAlwaysApplicableBool` (`b12`). -/
noncomputable def implTupleDup : ImplDef :=
  { id := 30
    headerSelf := .pair (.var 0) (.var 0)
    unconstrainedHeader := .pair (.var 0) (.var 0)
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 30 }

noncomputable def implLtDup : ImplDef :=
  { id := 31
    headerSelf := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 0) (.prim 1))
    unconstrainedHeader := .pair (.ref (.rNamed 0) (.prim 1)) (.ref (.rNamed 0) (.prim 1))
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 31 }

noncomputable def implStaticRef : ImplDef :=
  { id := 32
    headerSelf := .ref .rStatic (.prim 2)
    unconstrainedHeader := .ref .rStatic (.prim 2)
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 32 }

noncomputable def implIntoIterConstrained : ImplDef :=
  { id := 33
    headerSelf := .intoIter (.var 0)
    unconstrainedHeader := .intoIter (.var 0)
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 33 }

noncomputable def implEmptySpec : ImplDef :=
  { id := 34
    headerSelf := .prim 1
    unconstrainedHeader := .prim 1
    bounds := []
    hasItems := false
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 34 }

theorem layer2_rejection_and_constrained_projection_witnesses :
    checkAlwaysApplicableBool stdRegistry [] true implTupleDup = false ∧
    checkAlwaysApplicableBool stdRegistry [] true implLtDup = false ∧
    checkAlwaysApplicableBool stdRegistry [] true implStaticRef = false ∧
    checkAlwaysApplicableBool stdRegistry [] true implIntoIterConstrained = true ∧
    checkAlwaysApplicableBool stdRegistry [] true implEmptySpec = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-!
## Part 7: Lifetime-Dependent Unsoundness Counterexamples & `default type` Separation
-/

/-- **Counterexample 1 (`ce_static_specialization_unsound_after_erasure`)**:
If `'static` specialization (`implStaticRef`: `&'static i32` -> tag `32`) were permitted over
`implBlanket` (`T` -> tag `10`), then `gStatic = &'static i32` and `gLocal = &'local_1 i32`
have identical `eraseRegions`, yet `DispatchesSurface` returns `32` for `gStatic` and `10`
for `gLocal` (`32 ≠ 10`) — proving NO function `f : ErasedTy → Nat` can factor surface
dispatch through region erasure! -/
theorem ce_static_specialization_unsound_after_erasure :
    let chain := [implStaticRef, implBlanket]
    let gStatic := GroundTy.ref .rStatic (.prim 2)
    let gLocal := GroundTy.ref (.rLocal 1) (.prim 2)
    eraseRegions gStatic = eraseRegions gLocal ∧
    DispatchesSurface stdRegistry 0 chain gStatic 32 ∧
    DispatchesSurface stdRegistry 0 chain gLocal 10 ∧
    ¬ (∃ f : ErasedTy → Nat,
        ∀ g r, DispatchesSurface stdRegistry 0 chain g r → f (eraseRegions g) = r) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply DispatchesSurface.hit
    exact ⟨defaultSubst, rfl, fun _ hm => by cases hm⟩
  · apply DispatchesSurface.miss
    · intro ⟨σ, hσ, _⟩
      dsimp only [implStaticRef, instTy, instRegion] at hσ
      cases hσ
    · apply DispatchesSurface.hit
      refine ⟨{ defaultSubst with tySubst := fun _ => .ref (.rLocal 1) (.prim 2) }, rfl,
        fun _ hm => by cases hm⟩
  · rintro ⟨f, hf⟩
    have d1 : DispatchesSurface stdRegistry 0 [implStaticRef, implBlanket]
        (.ref .rStatic (.prim 2)) 32 := by
      apply DispatchesSurface.hit
      exact ⟨defaultSubst, rfl, fun _ hm => by cases hm⟩
    have d2 : DispatchesSurface stdRegistry 0 [implStaticRef, implBlanket]
        (.ref (.rLocal 1) (.prim 2)) 10 := by
      apply DispatchesSurface.miss
      · intro ⟨σ, hσ, _⟩
        dsimp only [implStaticRef, instTy, instRegion] at hσ
        cases hσ
      · apply DispatchesSurface.hit
        refine ⟨{ defaultSubst with tySubst := fun _ => .ref (.rLocal 1) (.prim 2) }, rfl,
          fun _ hm => by cases hm⟩
    have h1 := hf (.ref .rStatic (.prim 2)) 32 d1
    have h2 := hf (.ref (.rLocal 1) (.prim 2)) 10 d2
    have her : eraseRegions (.ref .rStatic (.prim 2)) = eraseRegions (.ref (.rLocal 1) (.prim 2)) := rfl
    rw [her, h2] at h1
    cases h1

/-- **Counterexample 2 (`ce_only_static_copy_generic_bypass_unsound`)**:
Formalizes the exact full-`specialization` exploit verified live in probes `c05a`/`c05b`:
- `OnlyStaticCopy<'static>` satisfies `stdCopySat`, whereas `OnlyStaticCopy<'local_1>` does NOT.
- Yet `eraseRegions (OnlyStaticCopy<'static>) = eraseRegions (OnlyStaticCopy<'local_1>)`.
- Under full `specialization` (`DispatchesErased` on `[implCopySpec, implBlanket]`),
  `DispatchesErased` selects `implCopySpec` (`20`) for `OnlyStaticCopy<'local_1>`, violating
  `ImplAppliesSurface stdRegistry implCopySpec (OnlyStaticCopy<'local_1>)`! -/
theorem ce_only_static_copy_generic_bypass_unsound :
    let gStatic := GroundTy.adt1r adtOnlyStaticCopy .rStatic
    let gLocal := GroundTy.adt1r adtOnlyStaticCopy (.rLocal 1)
    let chain := [implCopySpec, implBlanket]
    eraseRegions gStatic = eraseRegions gLocal ∧
    ¬ stdRegistry.traitSatisfied tidCopy gLocal ∧
    ¬ ImplAppliesSurface stdRegistry implCopySpec gLocal ∧
    DispatchesSurface stdRegistry 0 chain gLocal 10 ∧
    DispatchesErased stdRegistry 0 chain (eraseRegions gLocal) 20 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro hsat
    dsimp only [stdRegistry, stdCopySat] at hsat
    rcases hsat with ⟨_, hr⟩
    cases hr
  · rintro ⟨σ, hσ, hc⟩
    dsimp only [implCopySpec, instTy] at hσ
    have hcopy := hc (.traitVar tidCopy 0) .head
    dsimp only [ClauseHoldsSurface, stdRegistry, stdCopySat] at hcopy
    rw [hσ] at hcopy
    rcases hcopy with ⟨_, hr⟩
    cases hr
  · apply DispatchesSurface.miss
    · rintro ⟨σ, hσ, hc⟩
      dsimp only [implCopySpec, instTy] at hσ
      have hcopy := hc (.traitVar tidCopy 0) .head
      dsimp only [ClauseHoldsSurface, stdRegistry, stdCopySat] at hcopy
      rw [hσ] at hcopy
      rcases hcopy with ⟨_, hr⟩
      cases hr
    · apply DispatchesSurface.hit
      refine ⟨{ defaultSubst with tySubst := fun _ => .adt1r adtOnlyStaticCopy (.rLocal 1) },
        rfl, fun _ hm => by cases hm⟩
  · apply DispatchesErased.hit
    refine ⟨{ tySubst := fun _ => .adt1r adtOnlyStaticCopy, constSubst := fun _ => 0 }, rfl, ?_⟩
    intro c hm
    cases hm with
    | head =>
      dsimp only [ClauseHoldsErased, stdRegistry, stdCopySatErased]
      rfl
    | tail hm' => cases hm'

/-- **Theorem 4a (`default_type_rejected_under_min_specialization`)**:
`default type Assoc` (`hasDefaultType = true`) and `default impl` (`hasDefaultImpl = true`) are
rejected unconditionally by `checkAlwaysApplicableBool` (mirroring `feature_gate.rs` L392-401,
live probes `c01` and `c02`). -/
noncomputable def implDefaultTypeBlanket : ImplDef :=
  { id := 40
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := []
    hasItems := true
    hasDefaultType := true
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := true
    assocSizeBytes := some 2
    methodTag := 40 }

noncomputable def implDefaultHeaderBlanket : ImplDef :=
  { id := 41
    headerSelf := .var 0
    unconstrainedHeader := .var 0
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := true
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 41 }

theorem default_type_and_impl_rejected_under_min_specialization :
    checkAlwaysApplicableBool stdRegistry [] true implDefaultTypeBlanket = false ∧
    checkAlwaysApplicableBool stdRegistry [] true implDefaultHeaderBlanket = false :=
  ⟨rfl, rfl⟩

/-- TypingMode (`TypingMode::Typeck` vs `TypingMode::PostAnalysis` in `project.rs` L1056-1078). -/
inductive TypingMode where
  | typeck
  | postAnalysis

/-- Projection resolution oracle matching `rustc_trait_selection/src/traits/project.rs` L1048-1078:
if `assocIsDefault = true` (`!node_item.is_final()`), projection returns `none` (opaque,
triggering `E0308` if body expects concrete type, e.g., `#152409` / probes `c01` & `c04`) during
`TypingMode::typeck`, and reveals `assocSizeBytes` only in `TypingMode::postAnalysis` when
no further specializations apply! -/
noncomputable def resolveAssocSize (mode : TypingMode) (imp : ImplDef)
    (stillSpecializable : Bool) : Option Nat :=
  match imp.assocIsDefault with
  | false => imp.assocSizeBytes
  | true =>
    match mode with
    | .typeck => none
    | .postAnalysis => if stillSpecializable then none else imp.assocSizeBytes

/-- **Theorem 4b (`default_type_eager_norm_unsound_witness` & `default_type_typeck_opacity_necessity`)**:
1. Under sound `project.rs` rules, `resolveAssocSize .typeck implDefaultTypeBlanket` returns `none`
   (opaque), forcing `E0308` inside polymorphic bodies (`c01`/`c04`)!
2. If a naive `typeck` resolver instead eagerly revealed `implDefaultTypeBlanket.assocSizeBytes = some 2`,
   then specializing with `implCopySpec` (`type Assoc = [u64; 4]`, `some 32`) breaks type
   preservation (`2 ≠ 32`)!
3. Under full `specialization`, `resolveAssocSize .postAnalysis implCopySpec false = some 32`,
   and because `DispatchesErased` selects `implCopySpec` on `OnlyStaticCopy<'local_1>`,
   monomorphization projects `[u64; 4]` (size 32, matching live probe `c06`) onto a non-`Copy` type! -/
theorem default_type_projection_separation_and_unsoundness :
    resolveAssocSize .typeck implDefaultTypeBlanket true = none ∧
    resolveAssocSize .typeck implDefaultTypeBlanket false = none ∧
    resolveAssocSize .postAnalysis implCopySpec false = some 32 ∧
    (some 2 : Option Nat) ≠ some 32 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  injection h with h2
  cases h2

/-- Any sound polymorphic `typeck` associated-type size resolver that must agree with all
monomorphic `postAnalysis` specializations in a chain cannot return `some 2` for `implDefaultTypeBlanket`
when `implCopySpec` (`some 32`) specializes it! -/
theorem default_type_typeck_opacity_necessity
    (typeckGuess : Option Nat)
    (hSoundOverParent : typeckGuess = none ∨ typeckGuess = implDefaultTypeBlanket.assocSizeBytes)
    (hSoundOverChild : typeckGuess = none ∨ typeckGuess = implCopySpec.assocSizeBytes) :
    typeckGuess = none := by
  cases hSoundOverParent with
  | inl hnone => exact hnone
  | inr h2 =>
    cases hSoundOverChild with
    | inl hnone => exact hnone
    | inr h32 =>
      rw [h2] at h32
      dsimp only [implDefaultTypeBlanket, implCopySpec] at h32
      injection h32 with hnum
      cases hnum

/-- `GroundTyAllStatic g` (`T: 'static` outlives constraint): every embedded `GroundRegion` is `.rStatic`. -/
noncomputable def groundTyAllStatic : GroundTy → Bool
  | .prim _ => true
  | .ref .rStatic inner => groundTyAllStatic inner
  | .ref (.rLocal _) _ => false
  | .vecTy elem => groundTyAllStatic elem
  | .pair a b => groundTyAllStatic a && groundTyAllStatic b
  | .sliceIter .rStatic elem => groundTyAllStatic elem
  | .sliceIter (.rLocal _) _ => false
  | .intoIter elem => groundTyAllStatic elem
  | .adt0 _ => true
  | .adt1r _ .rStatic => true
  | .adt1r _ (.rLocal _) => false
  | .adt1t _ arg => groundTyAllStatic arg
  | .arrConst elem _ => groundTyAllStatic elem

noncomputable def implRefA : ImplDef :=
  { id := 42
    headerSelf := .ref (.rNamed 0) (.prim 2)
    unconstrainedHeader := .ref (.rNamed 0) (.prim 2)
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 42 }

/-- **Witness (`issue_79457_generalize_lifetimes_layer1_blind_layer2_reject`)**:
Mirrors Rust issue #79457 (`b04`): `impl<'a> Tr for &'a i32` (`implRefA`) over
`impl<T: 'static> Tr for T` passes region-blind `SpecializesModuloRegions` in Layer 1
(even when `'static` is on the parent impl!) because `specializes` skips `resolve_regions`,
yet fails surface `'static` outlives checking (`groundTyAllStatic g = false`) on
`gLocal = &'local_1 i32` (`E0477` in Layer 2 `get_impl_args`)! -/
theorem issue_79457_generalize_lifetimes_layer1_blind_layer2_reject :
    let gLocal := GroundTy.ref (.rLocal 1) (.prim 2)
    SpecializesModuloRegions stdRegistry implRefA implBlanketStaticBound ∧
    ImplAppliesSurface stdRegistry implRefA gLocal ∧
    groundTyAllStatic gLocal = false := by
  refine ⟨?_, ?_, rfl⟩
  · intro e ⟨_, _⟩
    refine ⟨{ tySubst := fun _ => e, constSubst := fun _ => 0 }, rfl, fun c hm => by
      cases hm with
      | head => trivial
      | tail hm' => cases hm'⟩
  · exact ⟨{ defaultSubst with regSubst := fun _ => .rLocal 1 }, rfl, fun _ hm => by cases hm⟩

/-- **Witness (`diamond_non_chain_conflict_e0119`)**:
Mirrors live probe `b15`: `[u8; N]` (`implArrU8N`) and `[T; 4]` (`implArrT4`) both
match `[u8; 4]` (`GroundTy.arrConst (.prim 1) 4`), yet neither specializes the other
(`le = false ∧ ge = false`), so `Children::insert` emits `E0119`! -/
noncomputable def implArrU8N : ImplDef :=
  { id := 43
    headerSelf := .arrConst (.prim 1) (some 0)
    unconstrainedHeader := .arrConst (.prim 1) (some 0)
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 43 }

noncomputable def implArrT4 : ImplDef :=
  { id := 44
    headerSelf := .arrConst (.var 0) none
    unconstrainedHeader := .arrConst (.var 0) none
    bounds := []
    hasItems := true
    hasDefaultType := false
    hasDefaultImpl := false
    hasAsyncOrRpitit := false
    assocIsDefault := false
    assocSizeBytes := none
    methodTag := 44 }

theorem diamond_non_chain_conflict_e0119 :
    let gOverlap := GroundTy.arrConst (.prim 1) 4
    ImplAppliesSurface stdRegistry implArrU8N gOverlap ∧
    ImplAppliesSurface stdRegistry implArrT4 gOverlap ∧
    ¬ SpecializesModuloRegions stdRegistry implArrU8N implArrT4 ∧
    ¬ SpecializesModuloRegions stdRegistry implArrT4 implArrU8N ∧
    childrenInsertDecision true false false = .conflictE0119 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · exact ⟨{ defaultSubst with constSubst := fun _ => 4 }, rfl, fun _ hm => by cases hm⟩
  · exact ⟨{ defaultSubst with tySubst := fun _ => .prim 1 }, rfl, fun _ hm => by cases hm⟩
  · intro hspec
    have hex : ImplAppliesErased stdRegistry implArrU8N (.arrConst (.prim 1) 3) :=
      ⟨{ tySubst := fun _ => .prim 1, constSubst := fun _ => 3 }, rfl, fun _ hm => by cases hm⟩
    rcases hspec (.arrConst (.prim 1) 3) hex with ⟨τ, hτ, _⟩
    dsimp only [implArrT4, erasePatRegions, instErasedPat] at hτ
    injection hτ with _ hlen
    cases hlen
  · intro hspec
    have hex : ImplAppliesErased stdRegistry implArrT4 (.arrConst (.prim 2) 4) :=
      ⟨{ tySubst := fun _ => .prim 2, constSubst := fun _ => 4 }, rfl, fun _ hm => by cases hm⟩
    rcases hspec (.arrConst (.prim 2) 4) hex with ⟨τ, hτ, _⟩
    dsimp only [implArrU8N, erasePatRegions, instErasedPat] at hτ
    injection hτ with hprim _
    cases hprim

/-- **Witness (`full_spec_default_type_lifetime_copy_bypass_witness`)**:
Combines `ce_only_static_copy_generic_bypass_unsound` and `resolveAssocSize`:
under full `specialization` (`c06`), `OnlyStaticCopy<'local_1>` violates `Copy`
(`¬ ImplAppliesSurface stdRegistry implCopySpec gLocal`), yet `DispatchesErased` selects
`implCopySpec` (`20`) and `resolveAssocSize .postAnalysis implCopySpec false` evaluates
`Assoc` to `some 32` (`[u64; 4]`) rather than `some 2` (`u16`)! -/
theorem full_spec_default_type_lifetime_copy_bypass_witness :
    let gLocal := GroundTy.adt1r adtOnlyStaticCopy (.rLocal 1)
    ¬ ImplAppliesSurface stdRegistry implCopySpec gLocal ∧
    DispatchesErased stdRegistry 0 [implCopySpec, implDefaultTypeBlanket] (eraseRegions gLocal) 20 ∧
    resolveAssocSize .postAnalysis implCopySpec false = some 32 ∧
    resolveAssocSize .typeck implDefaultTypeBlanket false = none := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rintro ⟨σ, hσ, hc⟩
    dsimp only [implCopySpec, instTy] at hσ
    have hcopy := hc (.traitVar tidCopy 0) .head
    dsimp only [ClauseHoldsSurface, stdRegistry, stdCopySat] at hcopy
    rw [hσ] at hcopy
    rcases hcopy with ⟨_, hr⟩
    cases hr
  · apply DispatchesErased.hit
    refine ⟨{ tySubst := fun _ => .adt1r adtOnlyStaticCopy, constSubst := fun _ => 0 }, rfl, ?_⟩
    intro c hm
    cases hm with
    | head =>
      dsimp only [ClauseHoldsErased, stdRegistry, stdCopySatErased]
      rfl
    | tail hm' => cases hm'

end MinSpecializationSoundness

