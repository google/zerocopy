/-
  DynCompatibilityVtableSlotSoundness.lean

  Kernel-checked Lean v4.34.1 mechanization of Rust's `dyn`-compatibility
  (object safety) rules, `where Self: Sized` vtable-omission exemptions,
  the `fn by_val(self)` `E0161` vs. `E0038` special case, `DispatchFromDyn`
  smart-pointer uniform ABI erasure, violation necessity counterexamples,
  and `google/zerocopy` trait `dyn`-compatibility classification.

  Upstream correspondence:
  - `compiler/rustc_trait_selection/src/traits/dyn_compatibility.rs`
  - `compiler/rustc_trait_selection/src/traits/vtable.rs`
  - `compiler/rustc_middle/src/traits/mod.rs`
  - `compiler/rustc_middle/src/ty/vtable.rs`
  - `compiler/rustc_hir_analysis/src/coherence/builtin.rs`
  - `compiler/rustc_mir_transform/src/shim.rs`
  - `google/zerocopy:zerocopy/src/lib.rs` (`Immutable`, `Unaligned`,
    `KnownLayout`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`)

  Purity invariants:
  - Pure `prelude` + `Init.*` only.
  - Every term/value/Prop definition carries `noncomputable def`
    (zero plain recursive `def`, zero `partial def`, zero `noncomputable section`,
    zero `deriving` clauses -> zero `._unsafe_rec` helpers).
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
    zero `native_decide`.
-/
prelude
import Init.Core
import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace DynCompatSoundness

/-! ## Section 1: Pure `noncomputable` Kernel Combinators & Arithmetic Lemmas -/

noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => natEq a b
  | _, _ => false

noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLe a b

noncomputable def natLt (a b : Nat) : Bool :=
  natLe (Nat.succ a) b

noncomputable def boolAnd : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

noncomputable def boolOr : Bool → Bool → Bool
  | false, false => false
  | _, _ => true

noncomputable def boolNot : Bool → Bool
  | true => false
  | false => true

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem ite_true_eq {α : Type} (b : Bool) (hb : b = true) (x y : α) :
    (if b then x else y) = x := by
  subst hb; rfl

theorem ite_false_eq {α : Type} (b : Bool) (hb : b = false) (x y : α) :
    (if b then x else y) = y := by
  subst hb; rfl

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem natEq_eq_iff (a b : Nat) : natEq a b = true ↔ a = b := by
  constructor
  · intro h
    induction a generalizing b with
    | zero =>
      cases b with
      | zero => rfl
      | succ _ => cases h
    | succ a ih =>
      cases b with
      | zero => cases h
      | succ b =>
        have hsub : natEq a b = true := h
        rw [ih b hsub]
  · intro h
    subst h
    exact natEq_refl a

theorem natEq_false_iff (a b : Nat) : natEq a b = false ↔ a ≠ b := by
  constructor
  · intro hf heq
    subst heq
    have ht := natEq_refl a
    rw [ht] at hf
    cases hf
  · intro hne
    cases h : natEq a b with
    | false => rfl
    | true =>
      have heq := (natEq_eq_iff a b).mp h
      exact False.elim (hne heq)

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem natLe_true_iff (a b : Nat) : natLe a b = true ↔ a ≤ b := by
  constructor
  · intro h
    induction a generalizing b with
    | zero => exact Nat.zero_le b
    | succ a ih =>
      cases b with
      | zero => cases h
      | succ b =>
        exact Nat.succ_le_succ (ih b h)
  · intro h
    induction a generalizing b with
    | zero => rfl
    | succ a ih =>
      cases b with
      | zero => cases h
      | succ b =>
        exact ih b (Nat.le_of_succ_le_succ h)

theorem natLt_true_iff (a b : Nat) : natLt a b = true ↔ a < b :=
  natLe_true_iff (Nat.succ a) b

theorem boolAnd_eq_true_iff (a b : Bool) : boolAnd a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> constructor <;> intro h
  · exact False.elim (Bool.false_ne_true h)
  · exact False.elim (Bool.false_ne_true h.1)
  · exact False.elim (Bool.false_ne_true h)
  · exact False.elim (Bool.false_ne_true h.1)
  · exact False.elim (Bool.false_ne_true h)
  · exact False.elim (Bool.false_ne_true h.2)
  · exact ⟨rfl, rfl⟩
  · rfl

theorem boolOr_eq_true_iff (a b : Bool) : boolOr a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> constructor <;> intro h
  · exact False.elim (Bool.false_ne_true h)
  · cases h with
    | inl h1 => exact False.elim (Bool.false_ne_true h1)
    | inr h2 => exact False.elim (Bool.false_ne_true h2)
  · exact Or.inr rfl
  · rfl
  · exact Or.inl rfl
  · rfl
  · exact Or.inl rfl
  · rfl

theorem boolOr_eq_false_iff (a b : Bool) : boolOr a b = false ↔ a = false ∧ b = false := by
  cases a <;> cases b <;> constructor <;> intro h
  · exact ⟨rfl, rfl⟩
  · rfl
  · cases h
  · cases h.2
  · cases h
  · cases h.1
  · cases h
  · cases h.1

theorem boolNot_eq_true_iff (a : Bool) : boolNot a = true ↔ a = false := by
  cases a <;> constructor <;> intro h <;> first | rfl | cases h

theorem boolNot_eq_false_iff (a : Bool) : boolNot a = false ↔ a = true := by
  cases a <;> constructor <;> intro h <;> first | rfl | cases h

noncomputable def listLen {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => Nat.succ (listLen xs)

noncomputable def listAppend {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: listAppend xs ys

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

noncomputable def listFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: listFilter p xs else listFilter p xs

noncomputable def listFilterMap {α β : Type} (f : α → Option β) : List α → List β
  | [] => []
  | x :: xs =>
    match f x with
    | some y => y :: listFilterMap f xs
    | none => listFilterMap f xs

noncomputable def listConcatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => listAppend (f x) (listConcatMap f xs)

noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => boolOr (p x) (listAny p xs)

noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => boolAnd (p x) (listAll p xs)

noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ k => listGet? xs k

noncomputable def listFind? {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else listFind? p xs

noncomputable def listElemNat (k : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => boolOr (natEq k x) (listElemNat k xs)

noncomputable def listNodupNat : List Nat → Bool
  | [] => true
  | x :: xs => boolAnd (boolNot (listElemNat x xs)) (listNodupNat xs)

noncomputable def listIndexOf? {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs =>
    if p x then some 0
    else match listIndexOf? p xs with
      | some i => some (Nat.succ i)
      | none => none

noncomputable def listIsEmpty {α : Type} : List α → Bool
  | [] => true
  | _ :: _ => false

noncomputable def memList {α : Type} (a : α) : List α → Prop
  | [] => False
  | x :: xs => a = x ∨ memList a xs

noncomputable def listMemNat (k : Nat) (xs : List Nat) : Prop :=
  memList k xs

theorem listIsEmpty_eq_true_iff {α : Type} (xs : List α) :
    listIsEmpty xs = true ↔ xs = [] := by
  cases xs with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons _ _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem listLen_map {α β : Type} (f : α → β) (xs : List α) :
    listLen (listMap f xs) = listLen xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    change Nat.succ (listLen (listMap f _)) = Nat.succ (listLen _)
    rw [ih]

theorem listGet?_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    listGet? (listMap f xs) i = match listGet? xs i with | some a => some (f a) | none => none := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

theorem listLen_append {α : Type} (xs ys : List α) :
    listLen (listAppend xs ys) = listLen xs + listLen ys := by
  induction xs with
  | nil =>
    change listLen ys = 0 + listLen ys
    rw [Nat.zero_add]
  | cons x xs ih =>
    change Nat.succ (listLen (listAppend xs ys)) = Nat.succ (listLen xs) + listLen ys
    rw [ih, Nat.succ_add]

theorem listGet?_append_left {α : Type} (xs ys : List α) (i : Nat)
    (hi : i < listLen xs) :
    listGet? (listAppend xs ys) i = listGet? xs i := by
  induction xs generalizing i with
  | nil =>
    cases (Nat.not_lt_zero i hi)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k =>
      exact ih k (Nat.lt_of_succ_lt_succ hi)

theorem listGet?_append_right {α : Type} (xs ys : List α) (i : Nat) :
    listGet? (listAppend xs ys) (listLen xs + i) = listGet? ys i := by
  induction xs with
  | nil =>
    change listGet? ys (0 + i) = listGet? ys i
    rw [Nat.zero_add]
  | cons x xs ih =>
    change listGet? (x :: listAppend xs ys) (Nat.succ (listLen xs) + i) = listGet? ys i
    rw [Nat.succ_add]
    exact ih

theorem listIndexOf?_lt_len {α : Type} (p : α → Bool) (xs : List α) (i : Nat)
    (h : listIndexOf? p xs = some i) :
    i < listLen xs := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [listIndexOf?] at h
    cases hp : p x with
    | true =>
      rw [hp] at h
      cases h
      exact Nat.zero_lt_succ _
    | false =>
      rw [hp] at h
      cases hind : listIndexOf? p xs with
      | none =>
        rw [hind] at h
        cases h
      | some j =>
        rw [hind] at h
        cases h
        exact Nat.succ_lt_succ (ih j hind)

theorem listIndexOf?_some_get? {α : Type} (p : α → Bool) (xs : List α) (i : Nat)
    (h : listIndexOf? p xs = some i) :
    ∃ x, listGet? xs i = some x ∧ p x = true ∧ memList x xs := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [listIndexOf?] at h
    cases hp : p x with
    | true =>
      rw [hp] at h
      cases h
      exact ⟨x, rfl, hp, Or.inl rfl⟩
    | false =>
      rw [hp] at h
      cases hind : listIndexOf? p xs with
      | none =>
        rw [hind] at h
        cases h
      | some j =>
        rw [hind] at h
        cases h
        have ⟨y, hyget, hyp, hymem⟩ := ih j hind
        exact ⟨y, hyget, hyp, Or.inr hymem⟩

theorem listIndexOf?_of_mem {α : Type} (p : α → Bool) (xs : List α) (x : α)
    (hmem : memList x xs) (hp : p x = true) :
    ∃ i, listIndexOf? p xs = some i := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    dsimp only [listIndexOf?]
    cases hpy : p y with
    | true => exact ⟨0, rfl⟩
    | false =>
      cases hmem with
      | inl heq =>
        subst heq
        rw [hp] at hpy
        cases hpy
      | inr htail =>
        have ⟨j, hj⟩ := ih htail
        rw [hj]
        exact ⟨Nat.succ j, rfl⟩

theorem listAny_true_of_mem {α : Type} (p : α → Bool) (xs : List α) (x : α)
    (hmem : memList x xs) (hp : p x = true) :
    listAny p xs = true := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    dsimp only [listAny]
    rw [boolOr_eq_true_iff]
    cases hmem with
    | inl heq =>
      subst heq
      exact Or.inl hp
    | inr htail =>
      exact Or.inr (ih htail)

theorem listAny_false_of_mem {α : Type} (p : α → Bool) (xs : List α)
    (h : listAny p xs = false) (x : α) (hmem : memList x xs) :
    p x = false := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    dsimp only [listAny] at h
    rw [boolOr_eq_false_iff] at h
    cases hmem with
    | inl heq =>
      subst heq
      exact h.1
    | inr htail =>
      exact ih h.2 htail

theorem listFilterMap_mem {α β : Type} (f : α → Option β) (xs : List α) (y : β)
    (hmem : memList y (listFilterMap f xs)) :
    ∃ x, memList x xs ∧ f x = some y := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
    dsimp only [listFilterMap] at hmem
    cases hfx : f x with
    | none =>
      rw [hfx] at hmem
      have ⟨x', hm', hf'⟩ := ih hmem
      exact ⟨x', Or.inr hm', hf'⟩
    | some z =>
      rw [hfx] at hmem
      cases hmem with
      | inl heq =>
        subst heq
        exact ⟨x, Or.inl rfl, hfx⟩
      | inr htail =>
        have ⟨x', hm', hf'⟩ := ih htail
        exact ⟨x', Or.inr hm', hf'⟩

theorem mem_listFilterMap_of_mem {α β : Type} (f : α → Option β) (xs : List α) (x : α) (y : β)
    (hmem : memList x xs) (hf : f x = some y) :
    memList y (listFilterMap f xs) := by
  induction xs with
  | nil => cases hmem
  | cons z zs ih =>
    dsimp only [listFilterMap]
    cases hmem with
    | inl heq =>
      subst heq
      rw [hf]
      exact Or.inl rfl
    | inr htail =>
      cases hfz : f z with
      | none => exact ih htail
      | some w => exact Or.inr (ih htail)

theorem listConcatMap_empty_of_all {α β : Type} (f : α → List β) (xs : List α)
    (hall : ∀ x, memList x xs → f x = []) :
    listConcatMap f xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [listConcatMap]
    have hx : f x = [] := hall x (Or.inl rfl)
    have hxs : listConcatMap f xs = [] := ih (fun y hy => hall y (Or.inr hy))
    rw [hx, hxs]
    rfl

theorem mem_listConcatMap_of_mem {α β : Type} (f : α → List β) (xs : List α) (x : α) (y : β)
    (hx : memList x xs) (hy : memList y (f x)) :
    memList y (listConcatMap f xs) := by
  induction xs with
  | nil => cases hx
  | cons z zs ih =>
    dsimp only [listConcatMap]
    have app_left : ∀ (as bs : List β) (b : β), memList b as → memList b (listAppend as bs) := by
      intro as bs b hb
      induction as with
      | nil => cases hb
      | cons a as' iha =>
        cases hb with
        | inl hba => exact Or.inl hba
        | inr hbt => exact Or.inr (iha hbt)
    have app_right : ∀ (as bs : List β) (b : β), memList b bs → memList b (listAppend as bs) := by
      intro as bs b hb
      induction as with
      | nil => exact hb
      | cons a as' iha => exact Or.inr iha
    cases hx with
    | inl heq =>
      subst heq
      exact app_left (f x) (listConcatMap f zs) y hy
    | inr htail =>
      exact app_right (f z) (listConcatMap f zs) y (ih htail)

theorem listConcatMap_empty_forall {α β : Type} (f : α → List β) (xs : List α)
    (he : listConcatMap f xs = []) (x : α) (hx : memList x xs) :
    f x = [] := by
  cases hfx : f x with
  | nil => rfl
  | cons y ys =>
    have hmem : memList y (listConcatMap f xs) :=
      mem_listConcatMap_of_mem f xs x y hx (by rw [hfx]; exact Or.inl rfl)
    rw [he] at hmem
    cases hmem

theorem listElemNat_eq_true_iff (k : Nat) (xs : List Nat) :
    listElemNat k xs = true ↔ memList k xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons x xs ih =>
    dsimp only [listElemNat]
    rw [boolOr_eq_true_iff, natEq_eq_iff, ih]
    exact Iff.rfl

theorem listElemNat_eq_false_iff (k : Nat) (xs : List Nat) :
    listElemNat k xs = false ↔ ¬ memList k xs := by
  constructor
  · intro hf hm
    have ht := (listElemNat_eq_true_iff k xs).mpr hm
    rw [ht] at hf
    cases hf
  · intro hn
    cases h : listElemNat k xs with
    | false => rfl
    | true => exact False.elim (hn ((listElemNat_eq_true_iff k xs).mp h))

theorem memList_app_left {α : Type} (xs ys : List α) (x : α) (hx : memList x xs) :
    memList x (listAppend xs ys) := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    cases hx with
    | inl heq => exact Or.inl heq
    | inr htail => exact Or.inr (ih htail)

theorem memList_app_right {α : Type} (xs ys : List α) (y : α) (hy : memList y ys) :
    memList y (listAppend xs ys) := by
  induction xs with
  | nil => exact hy
  | cons _ _ ih => exact Or.inr ih

theorem memList_map_of_mem {α β : Type} (f : α → β) {xs : List α} {x : α} (hx : memList x xs) :
    memList (f x) (listMap f xs) := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    cases hx with
    | inl heq => subst heq; exact Or.inl rfl
    | inr htail => exact Or.inr (ih htail)

theorem mem_listMap_iff {α β : Type} (f : α → β) (xs : List α) (y : β) :
    memList y (listMap f xs) ↔ ∃ x, memList x xs ∧ f x = y := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨_, hx, _⟩; cases hx
  | cons a as ih =>
    constructor
    · intro h
      cases h with
      | inl heq => exact ⟨a, Or.inl rfl, heq.symm⟩
      | inr htail =>
        have ⟨x, hxm, hfx⟩ := ih.mp htail
        exact ⟨x, Or.inr hxm, hfx⟩
    · intro ⟨x, hxm, hfx⟩
      cases hxm with
      | inl heq => subst heq; subst hfx; exact Or.inl rfl
      | inr htail => exact Or.inr (ih.mpr ⟨x, htail, hfx⟩)

noncomputable def listRemoveAll (k : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if natEq k x then listRemoveAll k xs else x :: listRemoveAll k xs

theorem mem_listRemoveAll_iff (k y : Nat) (xs : List Nat) :
    memList y (listRemoveAll k xs) ↔ memList y xs ∧ y ≠ k := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro ⟨h, _⟩; cases h
  | cons x xs ih =>
    dsimp only [listRemoveAll]
    cases hkx : natEq k x with
    | true =>
      have hkxeq : k = x := (natEq_eq_iff k x).mp hkx
      rw [ite_true_eq true rfl, ih]
      constructor
      · intro ⟨hym, hyne⟩; exact ⟨Or.inr hym, hyne⟩
      · intro ⟨hym, hyne⟩
        cases hym with
        | inl hyx => exact False.elim (hyne (hyx.trans hkxeq.symm))
        | inr htail => exact ⟨htail, hyne⟩
    | false =>
      have hkxne : k ≠ x := (natEq_false_iff k x).mp hkx
      rw [ite_false_eq false rfl]
      constructor
      · intro hy
        cases hy with
        | inl hyx => exact ⟨Or.inl hyx, fun hyk => hkxne (hyk.symm.trans hyx)⟩
        | inr htail =>
          have ⟨hm, hne⟩ := ih.mp htail
          exact ⟨Or.inr hm, hne⟩
      · intro ⟨hy, hyne⟩
        cases hy with
        | inl hyx => exact Or.inl hyx
        | inr htail => exact Or.inr (ih.mpr ⟨htail, hyne⟩)

theorem listLen_listRemoveAll_le (k : Nat) (xs : List Nat) :
    listLen (listRemoveAll k xs) ≤ listLen xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    dsimp only [listRemoveAll]
    cases hkx : natEq k x with
    | true => rw [ite_true_eq true rfl]; exact Nat.le_trans ih (Nat.le_succ _)
    | false =>
      rw [ite_false_eq false rfl]
      change Nat.succ (listLen (listRemoveAll k xs)) ≤ Nat.succ (listLen xs)
      exact Nat.succ_le_succ ih

theorem listLen_listRemoveAll_lt_of_mem (k : Nat) (xs : List Nat) (hm : memList k xs) :
    listLen (listRemoveAll k xs) < listLen xs := by
  induction xs with
  | nil => cases hm
  | cons x xs ih =>
    dsimp only [listRemoveAll]
    cases hkx : natEq k x with
    | true => rw [ite_true_eq true rfl]; exact Nat.lt_succ_of_le (listLen_listRemoveAll_le k xs)
    | false =>
      rw [ite_false_eq false rfl]
      have hkxne : k ≠ x := (natEq_false_iff k x).mp hkx
      cases hm with
      | inl hkx' => exact False.elim (hkxne hkx')
      | inr htail =>
        change Nat.succ (listLen (listRemoveAll k xs)) < Nat.succ (listLen xs)
        exact Nat.succ_lt_succ (ih htail)

theorem pigeonhole_distinct :
    ∀ (cs xs : List Nat),
      listNodupNat cs = true →
      listLen xs < listLen cs →
      ∃ c, memList c cs ∧ ¬ memList c xs := by
  intro cs
  induction cs with
  | nil =>
    intro xs _ hlt
    cases hlt
  | cons c cs' ih =>
    intro xs hnodup hlt
    dsimp only [listNodupNat] at hnodup
    rw [boolAnd_eq_true_iff, boolNot_eq_true_iff, listElemNat_eq_false_iff] at hnodup
    cases hmem : listElemNat c xs with
    | false =>
      exact ⟨c, Or.inl rfl, (listElemNat_eq_false_iff c xs).mp hmem⟩
    | true =>
      have hmemc : memList c xs := (listElemNat_eq_true_iff c xs).mp hmem
      have hlt_rm : listLen (listRemoveAll c xs) < listLen xs :=
        listLen_listRemoveAll_lt_of_mem c xs hmemc
      have hlt_cs : listLen (listRemoveAll c xs) < listLen cs' :=
        Nat.lt_of_lt_of_le hlt_rm (Nat.le_of_lt_succ hlt)
      have ⟨d, hdmem, hdnot⟩ := ih (listRemoveAll c xs) hnodup.2 hlt_cs
      have hdne : d ≠ c := fun h => hnodup.1 (by rw [← h]; exact hdmem)
      refine ⟨d, Or.inr hdmem, fun hdx => ?_⟩
      exact hdnot ((mem_listRemoveAll_iff c d xs).mpr ⟨hdx, hdne⟩)

noncomputable def rangeNat : Nat → List Nat
  | 0 => []
  | Nat.succ n => n :: rangeNat n

theorem listLen_rangeNat (n : Nat) : listLen (rangeNat n) = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (listLen (rangeNat k)) = Nat.succ k
    rw [ih]

theorem mem_rangeNat_iff (k n : Nat) : memList k (rangeNat n) ↔ k < n := by
  induction n with
  | zero =>
    constructor
    · intro h; cases h
    · intro h; cases (Nat.not_lt_zero k h)
  | succ m ih =>
    dsimp only [rangeNat]
    constructor
    · intro h
      cases h with
      | inl heq => subst heq; exact Nat.lt_succ_self k
      | inr htail => exact Nat.lt_succ_of_lt (ih.mp htail)
    · intro hlt
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with
      | inl heq => subst heq; exact Or.inl rfl
      | inr hltm => exact Or.inr (ih.mpr hltm)

theorem listNodupNat_rangeNat (n : Nat) : listNodupNat (rangeNat n) = true := by
  induction n with
  | zero => rfl
  | succ m ih =>
    dsimp only [rangeNat, listNodupNat]
    rw [boolAnd_eq_true_iff, boolNot_eq_true_iff, listElemNat_eq_false_iff]
    refine ⟨fun hm => Nat.lt_irrefl m ((mem_rangeNat_iff m m).mp hm), ih⟩

theorem listNodupNat_map_inj (f : Nat → Nat) (hinj : ∀ a b, f a = f b → a = b) :
    ∀ xs : List Nat, listNodupNat xs = true → listNodupNat (listMap f xs) = true := by
  intro xs hnodup
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [listNodupNat] at hnodup
    rw [boolAnd_eq_true_iff, boolNot_eq_true_iff, listElemNat_eq_false_iff] at hnodup
    dsimp only [listMap, listNodupNat]
    rw [boolAnd_eq_true_iff, boolNot_eq_true_iff, listElemNat_eq_false_iff]
    constructor
    · intro hfx
      have ⟨a, ha, hfa⟩ := (mem_listMap_iff f xs (f x)).mp hfx
      have hax : a = x := hinj a x hfa
      subst hax
      exact hnodup.1 ha
    · exact ih hnodup.2

theorem pigeonhole_inj_nat (f : Nat → Nat) (hinj : ∀ a b, f a = f b → a = b)
    (vt : List Nat) : ∃ k : Nat, ¬ memList (f k) vt := by
  have hnodup : listNodupNat (listMap f (rangeNat (Nat.succ (listLen vt)))) = true :=
    listNodupNat_map_inj f hinj _ (listNodupNat_rangeNat _)
  have hlen : listLen vt < listLen (listMap f (rangeNat (Nat.succ (listLen vt)))) := by
    rw [listLen_map, listLen_rangeNat]
    exact Nat.lt_succ_self (listLen vt)
  have ⟨c, hcmem, hcnot⟩ := pigeonhole_distinct _ vt hnodup hlen
  have ⟨k, _, hfk⟩ := (mem_listMap_iff f _ c).mp hcmem
  subst hfk
  exact ⟨k, hcnot⟩

/-! ## Section 2: `rustc` Type, Receiver, Clause, and Trait AST -/

/-- Rust type expression model covering `Self`, supertrait projections
`Self::Assoc`, primitives, named ADTs, `dyn Trait`, references, raw pointers,
`Box`/`Rc`/`Arc`/`Pin`, custom `#[repr(transparent)]` smart pointers,
RPITIT / `async` opaque types, and function pointers. -/
inductive TyExpr where
  | selfParam
  | selfAssoc (traitId : Nat) (itemId : Nat)
  | unit
  | prim (primId : Nat)
  | named (ctorId : Nat) (args : List TyExpr)
  | dynObj (traitId : Nat)
  | ref (mutbl : Bool) (inner : TyExpr)
  | rawPtr (mutbl : Bool) (inner : TyExpr)
  | boxPtr (inner : TyExpr)
  | rcPtr (inner : TyExpr)
  | arcPtr (inner : TyExpr)
  | pinPtr (inner : TyExpr)
  | customPtr (ctorId : Nat) (isTransparent singleNon1Zst noGeneric1Zst : Bool) (inner : TyExpr)
  | rpitit (opaqueId : Nat)
  | fnPtr (params : List TyExpr) (ret : TyExpr)

mutual
  noncomputable def tyExprBeq : TyExpr → TyExpr → Bool
    | .selfParam, .selfParam => true
    | .selfAssoc t1 i1, .selfAssoc t2 i2 => boolAnd (natEq t1 t2) (natEq i1 i2)
    | .unit, .unit => true
    | .prim p1, .prim p2 => natEq p1 p2
    | .named c1 as1, .named c2 as2 => boolAnd (natEq c1 c2) (tyExprListBeq as1 as2)
    | .dynObj d1, .dynObj d2 => natEq d1 d2
    | .ref m1 a1, .ref m2 a2 => boolAnd (boolEq m1 m2) (tyExprBeq a1 a2)
    | .rawPtr m1 a1, .rawPtr m2 a2 => boolAnd (boolEq m1 m2) (tyExprBeq a1 a2)
    | .boxPtr a1, .boxPtr a2 => tyExprBeq a1 a2
    | .rcPtr a1, .rcPtr a2 => tyExprBeq a1 a2
    | .arcPtr a1, .arcPtr a2 => tyExprBeq a1 a2
    | .pinPtr a1, .pinPtr a2 => tyExprBeq a1 a2
    | .customPtr c1 tr1 s1 ng1 a1, .customPtr c2 tr2 s2 ng2 a2 =>
      boolAnd (natEq c1 c2)
        (boolAnd (boolEq tr1 tr2)
          (boolAnd (boolEq s1 s2)
            (boolAnd (boolEq ng1 ng2) (tyExprBeq a1 a2))))
    | .rpitit o1, .rpitit o2 => natEq o1 o2
    | .fnPtr ps1 r1, .fnPtr ps2 r2 => boolAnd (tyExprListBeq ps1 ps2) (tyExprBeq r1 r2)
    | _, _ => false

  noncomputable def tyExprListBeq : List TyExpr → List TyExpr → Bool
    | [], [] => true
    | a :: as', b :: bs' => boolAnd (tyExprBeq a b) (tyExprListBeq as' bs')
    | _, _ => false
end

/-- Mirrors `dyn_compatibility::AllowSelfProjections` (`dyn_compatibility.rs:841`). -/
inductive AllowSelfProj where
  | yes
  | no

mutual
  /-- Mirrors `contains_illegal_self_type_reference` (`dyn_compatibility.rs:887-998`).
  `Self::Assoc` is permitted when `allowProj == .yes` and `traitId` is the trait
  itself or one of its supertraits; bare `Self` is always illegal here. -/
  noncomputable def tyContainsIllegalSelf (superIds : List Nat) (allowProj : AllowSelfProj) : TyExpr → Bool
    | .selfParam => true
    | .selfAssoc traitId _ =>
      match allowProj with
      | .yes => boolNot (listElemNat traitId superIds)
      | .no => true
    | .unit => false
    | .prim _ => false
    | .named _ args => tyListContainsIllegalSelf superIds allowProj args
    | .dynObj _ => false
    | .ref _ inner => tyContainsIllegalSelf superIds allowProj inner
    | .rawPtr _ inner => tyContainsIllegalSelf superIds allowProj inner
    | .boxPtr inner => tyContainsIllegalSelf superIds allowProj inner
    | .rcPtr inner => tyContainsIllegalSelf superIds allowProj inner
    | .arcPtr inner => tyContainsIllegalSelf superIds allowProj inner
    | .pinPtr inner => tyContainsIllegalSelf superIds allowProj inner
    | .customPtr _ _ _ _ inner => tyContainsIllegalSelf superIds allowProj inner
    | .rpitit _ => false
    | .fnPtr params ret =>
      boolOr (tyListContainsIllegalSelf superIds allowProj params)
        (tyContainsIllegalSelf superIds allowProj ret)

  noncomputable def tyListContainsIllegalSelf (superIds : List Nat) (allowProj : AllowSelfProj) : List TyExpr → Bool
    | [] => false
    | t :: ts => boolOr (tyContainsIllegalSelf superIds allowProj t) (tyListContainsIllegalSelf superIds allowProj ts)
end

mutual
  /-- Mirrors `IllegalRpititVisitor` (`dyn_compatibility.rs:1051-1069`). -/
  noncomputable def tyContainsRpitit : TyExpr → Bool
    | .selfParam => false
    | .selfAssoc _ _ => false
    | .unit => false
    | .prim _ => false
    | .named _ args => tyListContainsRpitit args
    | .dynObj _ => false
    | .ref _ inner => tyContainsRpitit inner
    | .rawPtr _ inner => tyContainsRpitit inner
    | .boxPtr inner => tyContainsRpitit inner
    | .rcPtr inner => tyContainsRpitit inner
    | .arcPtr inner => tyContainsRpitit inner
    | .pinPtr inner => tyContainsRpitit inner
    | .customPtr _ _ _ _ inner => tyContainsRpitit inner
    | .rpitit _ => true
    | .fnPtr params ret => boolOr (tyListContainsRpitit params) (tyContainsRpitit ret)

  noncomputable def tyListContainsRpitit : List TyExpr → Bool
    | [] => false
    | t :: ts => boolOr (tyContainsRpitit t) (tyListContainsRpitit ts)
end

/-- `Self`-parameterized receiver classification, modeling `wfcheck::receiver_is_valid`
and `coherence/builtin::visit_implementation_of_dispatch_from_dyn`. -/
inductive ReceiverKind where
  | none
  | byValueSelf
  | refSelf (mutbl : Bool)
  | rawPtrSelf (mutbl : Bool)
  | boxSelf
  | rcSelf
  | arcSelf
  | pinSelf (inner : ReceiverKind)
  | customDispatch (isTransparent singleNon1Zst noGeneric1Zst : Bool) (inner : ReceiverKind)
  | doubleIndirection

noncomputable def receiverKindBeq : ReceiverKind → ReceiverKind → Bool
  | .none, .none => true
  | .byValueSelf, .byValueSelf => true
  | .refSelf a, .refSelf b => boolEq a b
  | .rawPtrSelf a, .rawPtrSelf b => boolEq a b
  | .boxSelf, .boxSelf => true
  | .rcSelf, .rcSelf => true
  | .arcSelf, .arcSelf => true
  | .pinSelf a, .pinSelf b => receiverKindBeq a b
  | .customDispatch t1 s1 g1 a, .customDispatch t2 s2 g2 b =>
    boolAnd (boolEq t1 t2) (boolAnd (boolEq s1 s2) (boolAnd (boolEq g1 g2) (receiverKindBeq a b)))
  | .doubleIndirection, .doubleIndirection => true
  | _, _ => false

/-- Models `DispatchFromDyn` eligibility (`dyn_compatibility.rs:695-838`,
`coherence/builtin.rs:287-463`). Note `.byValueSelf` returns `false` here,
yet is explicitly exempted at `dyn_compatibility.rs:520/526` (`receiver_ty != tcx.types.self_param`). -/
noncomputable def isDispatchFromDynReceiver : ReceiverKind → Bool
  | .none => false
  | .byValueSelf => false
  | .refSelf _ => true
  | .rawPtrSelf _ => true
  | .boxSelf => true
  | .rcSelf => true
  | .arcSelf => true
  | .pinSelf inner => isDispatchFromDynReceiver inner
  | .customDispatch isTransp singleNon1Zst noGen1Zst inner =>
    boolAnd isTransp (boolAnd singleNon1Zst (boolAnd noGen1Zst (isDispatchFromDynReceiver inner)))
  | .doubleIndirection => false

/-- Trait and method `where` clauses affecting `dyn`-compatibility and elaboration. -/
inductive ClausePred where
  | sizedSelf
  | outlivesStatic
  | autoTrait (traitId : Nat)
  | nonAutoSizedTrait (traitId : Nat)
  | nonAutoUnsizedTrait (traitId : Nat)
  | supertrait (superId : Nat) (args : List TyExpr)

/-- Models `elaborate(tcx, clauses)` inside `generics_require_sized_self`
(`dyn_compatibility.rs:319-346`): both explicit `Self: Sized` and supertrait-elaborated
`Self: Sized` (such as `Self: Clone` where `Clone: Sized`) yield `true`. -/
noncomputable def clauseImpliesSizedSelf : ClausePred → Bool
  | .sizedSelf => true
  | .nonAutoSizedTrait _ => true
  | _ => false

noncomputable def clauseIsWhereSelfViolation (superIds : List Nat) : ClausePred → Bool
  | .sizedSelf => false
  | .outlivesStatic => false
  | .autoTrait _ => false
  | .nonAutoSizedTrait _ => false
  | .nonAutoUnsizedTrait _ => true
  | .supertrait _ args => tyListContainsIllegalSelf superIds .yes args

structure MethodDecl where
  methodId : Nat
  hasExplicitSizedSelf : Bool
  isFinal : Bool
  isAsync : Bool
  isCVariadic : Bool
  ownTypeParamCount : Nat
  ownConstParamCount : Nat
  receiver : ReceiverKind
  extraParams : List TyExpr
  retTy : TyExpr
  clauses : List ClausePred

structure AssocConstDecl where
  constId : Nat
  hasExplicitSizedSelf : Bool
  isFinal : Bool
  gcaMinConstEnabled : Bool
  isTypeConst : Bool
  ownParamCount : Nat
  constTy : TyExpr
  clauses : List ClausePred

structure AssocTyDecl where
  tyId : Nat
  hasExplicitSizedSelf : Bool
  ownGenericCount : Nat
  itemBounds : List ClausePred
  clauses : List ClausePred

inductive AssocItemDecl where
  | fnDecl (m : MethodDecl)
  | constDecl (c : AssocConstDecl)
  | tyDecl (a : AssocTyDecl)

structure TraitDecl where
  traitId : Nat
  superTraitIds : List Nat
  forceDynIncompatible : Bool
  traitClauses : List ClausePred
  items : List AssocItemDecl

/-! ## Section 3: `rustc` Dyn-Compatibility Checker (`dyn_compatibility.rs`) -/

inductive MethodViolation where
  | staticMethod
  | referencesSelfInput
  | referencesSelfOutput
  | referencesImplTraitInTrait
  | asyncFn
  | cVariadic
  | whereClauseReferencesSelf
  | generic
  | undispatchableReceiver

inductive AssocConstViolation where
  | featureNotEnabled
  | nonType
  | generic
  | typeReferencesSelf

inductive DynCompatViolation where
  | explicitlyDynIncompatible
  | sizedSelf
  | supertraitSelf
  | method (methodId : Nat) (v : MethodViolation)
  | assocConst (constId : Nat) (v : AssocConstViolation)
  | genericAssocTy (tyId : Nat)

noncomputable def methodRequiresSizedSelf (m : MethodDecl) : Bool :=
  boolOr m.hasExplicitSizedSelf (listAny clauseImpliesSizedSelf m.clauses)

noncomputable def constRequiresSizedSelf (c : AssocConstDecl) : Bool :=
  boolOr c.hasExplicitSizedSelf (listAny clauseImpliesSizedSelf c.clauses)

noncomputable def tyRequiresSizedSelf (a : AssocTyDecl) : Bool :=
  boolOr a.hasExplicitSizedSelf (listAny clauseImpliesSizedSelf a.clauses)

noncomputable def itemRequiresSizedSelf : AssocItemDecl → Bool
  | .fnDecl m => methodRequiresSizedSelf m
  | .constDecl c => constRequiresSizedSelf c
  | .tyDecl a => tyRequiresSizedSelf a

noncomputable def traitRequiresSizedSelf (t : TraitDecl) : Bool :=
  listAny clauseImpliesSizedSelf t.traitClauses

/-- Mirrors `virtual_call_violations_for_method` (`dyn_compatibility.rs:443-623`),
preserving:
1. Early return `[.staticMethod]` when `receiver == .none` (line 475),
2. Skipping `isDispatchFromDynReceiver` when `receiver == .byValueSelf` (line 520/526),
3. Allowing `Self: 'static` and positive `Self: AutoTrait` in `where` clauses (lines 580-615). -/
noncomputable def virtualCallViolationsForMethod (superIds : List Nat) (m : MethodDecl) :
    List MethodViolation :=
  match m.receiver with
  | .none => [.staticMethod]
  | _ =>
    let vIn := if tyListContainsIllegalSelf superIds .yes m.extraParams then [.referencesSelfInput] else []
    let vOut := if tyContainsIllegalSelf superIds .yes m.retTy then [.referencesSelfOutput] else []
    let vRpit :=
      if m.isAsync then [.asyncFn]
      else if tyContainsRpitit m.retTy then [.referencesImplTraitInTrait]
      else []
    let vVar := if m.isCVariadic then [.cVariadic] else []
    let vGen :=
      if boolOr (natLt 0 m.ownTypeParamCount) (natLt 0 m.ownConstParamCount) then [.generic] else []
    let vRecv :=
      if boolAnd (boolNot (receiverKindBeq m.receiver .byValueSelf))
           (boolNot (isDispatchFromDynReceiver m.receiver))
      then [.undispatchableReceiver]
      else []
    let vWhere :=
      if listAny (clauseIsWhereSelfViolation superIds) m.clauses then [.whereClauseReferencesSelf] else []
    listAppend vIn (listAppend vOut (listAppend vRpit (listAppend vVar (listAppend vGen (listAppend vRecv vWhere)))))

/-- Mirrors `dyn_compatibility_violations_for_assoc_item` (`dyn_compatibility.rs:349-437`). -/
noncomputable def dynCompatViolationsForAssocItem (superIds : List Nat) :
    AssocItemDecl → List DynCompatViolation
  | .fnDecl m =>
    if m.isFinal then []
    else if methodRequiresSizedSelf m then []
    else listMap (DynCompatViolation.method m.methodId) (virtualCallViolationsForMethod superIds m)
  | .constDecl c =>
    if c.isFinal then []
    else if constRequiresSizedSelf c then []
    else
      if boolNot c.gcaMinConstEnabled then [DynCompatViolation.assocConst c.constId .featureNotEnabled]
      else
        let eGen := if natLt 0 c.ownParamCount then [DynCompatViolation.assocConst c.constId .generic] else []
        let eType := if boolAnd (natEq c.ownParamCount 0) (boolNot c.isTypeConst) then [DynCompatViolation.assocConst c.constId .nonType] else []
        let eSelf := if tyContainsIllegalSelf superIds .yes c.constTy then [DynCompatViolation.assocConst c.constId .typeReferencesSelf] else []
        listAppend eGen (listAppend eType eSelf)
  | .tyDecl a =>
    if tyRequiresSizedSelf a then []
    else if natLt 0 a.ownGenericCount then [DynCompatViolation.genericAssocTy a.tyId]
    else []

noncomputable def clauseIsSupertraitSelf (superIds : List Nat) : ClausePred → Bool
  | .supertrait _ args => tyListContainsIllegalSelf superIds .no args
  | _ => false

/-- Mirrors `dyn_compatibility_violations_for_trait` (`dyn_compatibility.rs:82-120`). -/
noncomputable def dynCompatViolationsForTrait (t : TraitDecl) : List DynCompatViolation :=
  let itemViols := listConcatMap (dynCompatViolationsForAssocItem t.superTraitIds) t.items
  let traitViols :=
    if traitRequiresSizedSelf t then [DynCompatViolation.sizedSelf]
    else if t.forceDynIncompatible then [DynCompatViolation.explicitlyDynIncompatible]
    else []
  let superViols :=
    if listAny (clauseIsSupertraitSelf t.superTraitIds) t.traitClauses then [DynCompatViolation.supertraitSelf] else []
  listAppend itemViols (listAppend traitViols superViols)

noncomputable def isDynCompatible (t : TraitDecl) : Bool :=
  listIsEmpty (dynCompatViolationsForTrait t)

/-- Mirrors `is_vtable_safe_method` (`dyn_compatibility.rs:70-79`, plus `is_final` skip at `vtable.rs:217`). -/
noncomputable def isVtableSafeMethod (superIds : List Nat) (m : MethodDecl) : Bool :=
  if m.isFinal then false
  else if methodRequiresSizedSelf m then false
  else listIsEmpty (virtualCallViolationsForMethod superIds m)

/-! ## Section 4: Vtable Slot Layout & Monomorphic ABI Erasure (`vtable.rs`) -/

/-- Monomorphic target-ABI type representation inside a compiled vtable signature.
Notice there is NO `selfParam`, NO `rpitit`, and NO generic type parameter. -/
inductive ErasedAbiTy where
  | thinPtr
  | unit
  | prim (primId : Nat)
  | agg (ctorId : Nat) (args : List ErasedAbiTy)
  | dynPtr (traitId : Nat)
  | fnAbiPtr (params : List ErasedAbiTy) (ret : ErasedAbiTy)

mutual
  /-- Erases a checked `TyExpr` into a monomorphic `ErasedAbiTy`.
  Returns `none` if an unprojected `Self` or an `RPITIT` survives. -/
  noncomputable def eraseMonoTy (superIds : List Nat) : TyExpr → Option ErasedAbiTy
    | .selfParam => none
    | .selfAssoc traitId itemId =>
      if listElemNat traitId superIds then some (.prim itemId) else none
    | .unit => some .unit
    | .prim p => some (.prim p)
    | .named ctorId args =>
      match eraseMonoTyList superIds args with
      | some eargs => some (.agg ctorId eargs)
      | none => none
    | .dynObj tid => some (.dynPtr tid)
    | .ref _ inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .rawPtr _ inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .boxPtr inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .rcPtr inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .arcPtr inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .pinPtr inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .customPtr _ _ _ _ inner =>
      match eraseMonoTy superIds inner with
      | some _ => some .thinPtr
      | none => none
    | .rpitit _ => none
    | .fnPtr params ret =>
      match eraseMonoTyList superIds params, eraseMonoTy superIds ret with
      | some eparams, some eret => some (.fnAbiPtr eparams eret)
      | _, _ => none

  noncomputable def eraseMonoTyList (superIds : List Nat) : List TyExpr → Option (List ErasedAbiTy)
    | [] => some []
    | t :: ts =>
      match eraseMonoTy superIds t, eraseMonoTyList superIds ts with
      | some et, some ets => some (et :: ets)
      | _, _ => none
end

/-- Mirrors `rustc_middle::ty::vtable::VtblEntry<'tcx>` (`middle/ty/vtable.rs:13-26`). -/
inductive VtblEntry where
  | metadataDropInPlace (fnSym : Option Nat)
  | metadataSize (bytes : Nat)
  | metadataAlign (bytes : Nat)
  | vacant (traitId methodId : Nat)
  | method (traitId methodId : Nat) (fnSym : Nat) (viaVTableShim : Bool)
      (erasedParams : List ErasedAbiTy) (erasedRet : ErasedAbiTy)
  | traitVPtr (superTraitId : Nat)

noncomputable def vtblEntryMatchesMethod (tid mid : Nat) : VtblEntry → Bool
  | .vacant t m => boolAnd (natEq t tid) (natEq m mid)
  | .method t m _ _ _ _ => boolAnd (natEq t tid) (natEq m mid)
  | _ => false

/-- Mirrors `own_existential_vtable_entries_iter` (`vtable.rs:204-231`):
omits `final` items, omits non-`fn` items, and omits `!is_vtable_safe_method`
(including all `where Self: Sized` methods!). -/
noncomputable def ownExistentialVtableEntries (t : TraitDecl) : List MethodDecl :=
  listFilterMap
    (fun item =>
      match item with
      | .fnDecl m => if isVtableSafeMethod t.superTraitIds m then some m else none
      | _ => none)
    t.items

structure ConcreteImpl where
  concreteSelfId : Nat
  sizeBytes : Nat
  alignBytes : Nat
  dropGlueSym : Option Nat
  clausesHoldForSelf : MethodDecl → Bool
  methodSym : Nat → Nat

noncomputable def commonVtableHeader (impl_ : ConcreteImpl) : List VtblEntry :=
  [.metadataDropInPlace impl_.dropGlueSym, .metadataSize impl_.sizeBytes, .metadataAlign impl_.alignBytes]

/-- Mirrors `vtable_entries` (`vtable.rs:235-310`) + `vtable_allocation_provider`
(`middle/ty/vtable.rs:84-156`): 3-word DSA header followed by one slot per
`ownExistentialVtableEntries t` entry (`VtblEntry.method` when clauses hold,
`VtblEntry.vacant` when `instantiate_and_check_impossible_clauses` triggers). -/
noncomputable def buildVtable (t : TraitDecl) (impl_ : ConcreteImpl) : List VtblEntry :=
  let ownSlots := listMap
    (fun m =>
      if impl_.clausesHoldForSelf m then
        let eParams := match eraseMonoTyList t.superTraitIds m.extraParams with | some ps => ps | none => []
        let eRet := match eraseMonoTy t.superTraitIds m.retTy with | some r => r | none => .unit
        let isShim := receiverKindBeq m.receiver .byValueSelf
        VtblEntry.method t.traitId m.methodId (impl_.methodSym m.methodId) isShim eParams eRet
      else
        VtblEntry.vacant t.traitId m.methodId)
    (ownExistentialVtableEntries t)
  listAppend (commonVtableHeader impl_) ownSlots

noncomputable def vtableSlotIndexOfMethod (t : TraitDecl) (methodId : Nat) : Option Nat :=
  match listIndexOf? (fun m => natEq m.methodId methodId) (ownExistentialVtableEntries t) with
  | some idx => some (3 + idx)
  | none => none

/-- Concrete smart-pointer value before unsized coercion to `dyn Trait`. -/
structure ConcretePtrVal where
  concreteSelfId : Nat
  dataPtr : Nat
  receiver : ReceiverKind

/-- Type-erased wide pointer `(dataPtr, vtablePtr)` constructed via `CoerceUnsized`. -/
structure DynFatPtr where
  erasedConcreteId : Nat
  dataPtr : Nat
  traitId : Nat
  vtable : List VtblEntry
  receiver : ReceiverKind

/-- Coerces a concrete pointer into a `DynFatPtr` iff the trait is `dyn`-compatible
and the receiver satisfies `DispatchFromDyn` (or is `self: Self` behind `Box`/`Value`).
Notice `dataPtr` and concrete `Self` identity pass through without reboxing. -/
noncomputable def coerceToDyn (t : TraitDecl) (impl_ : ConcreteImpl) (p : ConcretePtrVal) :
    Option DynFatPtr :=
  if isDynCompatible t then
    if isDispatchFromDynReceiver p.receiver then
      some {
        erasedConcreteId := impl_.concreteSelfId
        dataPtr := p.dataPtr
        traitId := t.traitId
        vtable := buildVtable t impl_
        receiver := p.receiver
      }
    else none
  else none

inductive CallRejectionReason where
  | e0599SizedRequirement
  | e0161MoveUnsized
  | e0277DynClauseUnsatisfied
  | missingVtableSlot
  | unexpectedVacantSlot

inductive DispatchOutcome where
  | invoked (concreteSelfId fnSym arg0DataPtr : Nat) (viaVTableShim : Bool)
  | rejected (reason : CallRejectionReason)

/-- Models method call typechecking + MIR/vtable dispatch on a `DynFatPtr`. -/
noncomputable def canInvokeMethodOnDyn (hasUnsizedFnParams : Bool) (dynHasMethodClauses : Bool)
    (m : MethodDecl) : Bool :=
  boolAnd (boolNot (methodRequiresSizedSelf m))
    (boolAnd (boolNot m.isFinal)
      (boolAnd dynHasMethodClauses
        (boolOr (boolNot (receiverKindBeq m.receiver .byValueSelf)) hasUnsizedFnParams)))

noncomputable def evalDynCall (t : TraitDecl) (d : DynFatPtr) (m : MethodDecl)
    (hasUnsizedFnParams dynHasMethodClauses : Bool) : DispatchOutcome :=
  if methodRequiresSizedSelf m then .rejected .e0599SizedRequirement
  else if m.isFinal then .rejected .e0599SizedRequirement
  else if boolAnd (receiverKindBeq m.receiver .byValueSelf) (boolNot hasUnsizedFnParams) then
    .rejected .e0161MoveUnsized
  else if boolNot dynHasMethodClauses then .rejected .e0277DynClauseUnsatisfied
  else
    match vtableSlotIndexOfMethod t m.methodId with
    | none => .rejected .missingVtableSlot
    | some idx =>
      match listGet? d.vtable idx with
      | some (.method _ _ fnSym viaShim _ _) => .invoked d.erasedConcreteId fnSym d.dataPtr viaShim
      | some (.vacant _ _) => .rejected .unexpectedVacantSlot
      | _ => .rejected .missingVtableSlot

/-! ## Section 5: Theorem Family 1 — Vtable Completeness & Monomorphic Determinism -/

theorem virtualCall_empty_implies_no_static (superIds : List Nat) (m : MethodDecl)
    (h : virtualCallViolationsForMethod superIds m = []) :
    m.receiver ≠ .none := by
  intro hnone
  cases hr : m.receiver with
  | none =>
    dsimp only [virtualCallViolationsForMethod] at h
    rw [hr] at h
    cases h
  | byValueSelf => rw [hr] at hnone; cases hnone
  | refSelf _ => rw [hr] at hnone; cases hnone
  | rawPtrSelf _ => rw [hr] at hnone; cases hnone
  | boxSelf => rw [hr] at hnone; cases hnone
  | rcSelf => rw [hr] at hnone; cases hnone
  | arcSelf => rw [hr] at hnone; cases hnone
  | pinSelf _ => rw [hr] at hnone; cases hnone
  | customDispatch _ _ _ _ => rw [hr] at hnone; cases hnone
  | doubleIndirection => rw [hr] at hnone; cases hnone

theorem listAppend_eq_nil_iff {α : Type} (a b : List α) :
    listAppend a b = [] ↔ a = [] ∧ b = [] := by
  cases a with
  | nil => exact ⟨fun hb => ⟨rfl, hb⟩, fun ⟨_, hb⟩ => hb⟩
  | cons _ _ => exact ⟨fun h => (by cases h), fun ⟨ha, _⟩ => (by cases ha)⟩

theorem bool_false_of_ite_singleton_nil {α : Type} (b : Bool) (x : α)
    (h : (if b then [x] else []) = []) : b = false := by
  cases hb : b with
  | false => rfl
  | true =>
    rw [ite_true_eq _ hb] at h
    cases h

theorem virtualCall_empty_properties (superIds : List Nat) (m : MethodDecl)
    (h : virtualCallViolationsForMethod superIds m = []) :
    m.receiver ≠ .none ∧
    tyListContainsIllegalSelf superIds .yes m.extraParams = false ∧
    tyContainsIllegalSelf superIds .yes m.retTy = false ∧
    m.isAsync = false ∧
    tyContainsRpitit m.retTy = false ∧
    m.isCVariadic = false ∧
    m.ownTypeParamCount = 0 ∧
    m.ownConstParamCount = 0 ∧
    (m.receiver = .byValueSelf ∨ isDispatchFromDynReceiver m.receiver = true) := by
  have hne := virtualCall_empty_implies_no_static superIds m h
  have hsplit : ∀ (r : ReceiverKind), r = m.receiver → r ≠ .none →
      (if tyListContainsIllegalSelf superIds .yes m.extraParams then [MethodViolation.referencesSelfInput] else []) = [] ∧
      (if tyContainsIllegalSelf superIds .yes m.retTy then [MethodViolation.referencesSelfOutput] else []) = [] ∧
      (if m.isAsync then [MethodViolation.asyncFn]
        else if tyContainsRpitit m.retTy then [MethodViolation.referencesImplTraitInTrait] else []) = [] ∧
      (if m.isCVariadic then [MethodViolation.cVariadic] else []) = [] ∧
      (if boolOr (natLt 0 m.ownTypeParamCount) (natLt 0 m.ownConstParamCount) then [MethodViolation.generic] else []) = [] ∧
      (if boolAnd (boolNot (receiverKindBeq r .byValueSelf)) (boolNot (isDispatchFromDynReceiver r))
        then [MethodViolation.undispatchableReceiver] else []) = [] := by
    intro r hr hnr
    dsimp only [virtualCallViolationsForMethod] at h
    rw [← hr] at h
    cases r with
    | none => exact False.elim (hnr rfl)
    | byValueSelf =>
      dsimp only at h
      rw [listAppend_eq_nil_iff, listAppend_eq_nil_iff, listAppend_eq_nil_iff,
          listAppend_eq_nil_iff, listAppend_eq_nil_iff, listAppend_eq_nil_iff] at h
      have ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
    | customDispatch _ _ _ _ | doubleIndirection =>
      dsimp only at h
      rw [listAppend_eq_nil_iff, listAppend_eq_nil_iff, listAppend_eq_nil_iff,
          listAppend_eq_nil_iff, listAppend_eq_nil_iff, listAppend_eq_nil_iff] at h
      have ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
      exact ⟨h1, h2, h3, h4, h5, h6⟩
  have ⟨hIn, hOut, hRpit, hVar, hGen, hRecv⟩ := hsplit m.receiver rfl hne
  have bIn := bool_false_of_ite_singleton_nil _ _ hIn
  have bOut := bool_false_of_ite_singleton_nil _ _ hOut
  have bAsync : m.isAsync = false := by
    cases h0 : m.isAsync with
    | false => rfl
    | true => rw [ite_true_eq _ h0] at hRpit; cases hRpit
  have bRpit : tyContainsRpitit m.retTy = false := by
    rw [ite_false_eq _ bAsync] at hRpit
    exact bool_false_of_ite_singleton_nil _ _ hRpit
  have bVar := bool_false_of_ite_singleton_nil _ _ hVar
  have bGen := bool_false_of_ite_singleton_nil _ _ hGen
  rw [boolOr_eq_false_iff] at bGen
  have bGenT : m.ownTypeParamCount = 0 := by
    cases ht : m.ownTypeParamCount with
    | zero => rfl
    | succ k =>
      have hlt : natLt 0 (Nat.succ k) = true := (natLt_true_iff 0 (Nat.succ k)).mpr (Nat.zero_lt_succ k)
      have h1 := bGen.1
      rw [ht, hlt] at h1
      cases h1
  have bGenC : m.ownConstParamCount = 0 := by
    cases hc : m.ownConstParamCount with
    | zero => rfl
    | succ k =>
      have hlt : natLt 0 (Nat.succ k) = true := (natLt_true_iff 0 (Nat.succ k)).mpr (Nat.zero_lt_succ k)
      have h2 := bGen.2
      rw [hc, hlt] at h2
      cases h2
  have bRecvCond := bool_false_of_ite_singleton_nil _ _ hRecv
  have bDispOr : m.receiver = .byValueSelf ∨ isDispatchFromDynReceiver m.receiver = true := by
    cases hbv : m.receiver with
    | byValueSelf => exact Or.inl rfl
    | none | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
    | customDispatch _ _ _ _ | doubleIndirection =>
      rw [hbv] at bRecvCond
      dsimp only [receiverKindBeq, boolNot] at bRecvCond
      cases hdp : isDispatchFromDynReceiver _ with
      | true => exact Or.inr rfl
      | false =>
        rw [hdp] at bRecvCond
        cases bRecvCond
  exact ⟨hne, bIn, bOut, bAsync, bRpit, bVar, bGenT, bGenC, bDispOr⟩

/-- Whenever `TyExpr` contains neither illegal `Self` nor RPITIT, `eraseMonoTy`
succeeds deterministically with a monomorphic `ErasedAbiTy`. -/
theorem eraseMonoTy_succeeds_of_safe (superIds : List Nat) :
    (∀ (t : TyExpr),
      tyContainsIllegalSelf superIds .yes t = false →
      tyContainsRpitit t = false →
      ∃ et, eraseMonoTy superIds t = some et) ∧
    (∀ (ts : List TyExpr),
      tyListContainsIllegalSelf superIds .yes ts = false →
      tyListContainsRpitit ts = false →
      ∃ ets, eraseMonoTyList superIds ts = some ets) := by
  have hTy : ∀ (t : TyExpr),
      tyContainsIllegalSelf superIds .yes t = false →
      tyContainsRpitit t = false →
      ∃ et, eraseMonoTy superIds t = some et := by
    refine @TyExpr.rec
      (motive_1 := fun t =>
        tyContainsIllegalSelf superIds .yes t = false →
        tyContainsRpitit t = false →
        ∃ et, eraseMonoTy superIds t = some et)
      (motive_2 := fun ts =>
        tyListContainsIllegalSelf superIds .yes ts = false →
        tyListContainsRpitit ts = false →
        ∃ ets, eraseMonoTyList superIds ts = some ets)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro hs _; cases hs
    · intro tid iid hs _
      dsimp only [tyContainsIllegalSelf] at hs
      rw [boolNot_eq_false_iff] at hs
      dsimp only [eraseMonoTy]
      rw [ite_true_eq _ hs]
      exact ⟨.prim iid, rfl⟩
    · intro _ _; exact ⟨.unit, rfl⟩
    · intro pid _ _; exact ⟨.prim pid, rfl⟩
    · intro cid args ihargs hs hr
      dsimp only [tyContainsIllegalSelf] at hs
      dsimp only [tyContainsRpitit] at hr
      have ⟨ets, hets⟩ := ihargs hs hr
      dsimp only [eraseMonoTy]
      rw [hets]
      exact ⟨.agg cid ets, rfl⟩
    · intro tid _ _; exact ⟨.dynPtr tid, rfl⟩
    · intro _ inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro _ inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro _ _ _ _ inner ih hs hr
      have ⟨_, het⟩ := ih hs hr
      dsimp only [eraseMonoTy]
      rw [het]
      exact ⟨.thinPtr, rfl⟩
    · intro _ _ hr; cases hr
    · intro params ret ihp ihr hs hr
      dsimp only [tyContainsIllegalSelf] at hs
      dsimp only [tyContainsRpitit] at hr
      rw [boolOr_eq_false_iff] at hs hr
      have ⟨eps, heps⟩ := ihp hs.1 hr.1
      have ⟨eret, heret⟩ := ihr hs.2 hr.2
      dsimp only [eraseMonoTy]
      rw [heps, heret]
      exact ⟨.fnAbiPtr eps eret, rfl⟩
    · intro _ _; exact ⟨[], rfl⟩
    · intro t ts iht ihts hs hr
      dsimp only [tyListContainsIllegalSelf] at hs
      dsimp only [tyListContainsRpitit] at hr
      rw [boolOr_eq_false_iff] at hs hr
      have ⟨et, het⟩ := iht hs.1 hr.1
      have ⟨ets, hets⟩ := ihts hs.2 hr.2
      dsimp only [eraseMonoTyList]
      rw [het, hets]
      exact ⟨et :: ets, rfl⟩
  have hTs : ∀ (ts : List TyExpr),
      tyListContainsIllegalSelf superIds .yes ts = false →
      tyListContainsRpitit ts = false →
      ∃ ets, eraseMonoTyList superIds ts = some ets := by
    intro ts hs hr
    induction ts with
    | nil => exact ⟨[], rfl⟩
    | cons t ts' ihts =>
      dsimp only [tyListContainsIllegalSelf] at hs
      dsimp only [tyListContainsRpitit] at hr
      rw [boolOr_eq_false_iff] at hs hr
      have ⟨et, het⟩ := hTy t hs.1 hr.1
      have ⟨ets, hets⟩ := ihts hs.2 hr.2
      dsimp only [eraseMonoTyList]
      rw [het, hets]
      exact ⟨et :: ets, rfl⟩
  exact ⟨hTy, hTs⟩

/-- In Rust HIR lowering (`rustc_hir_analysis`), `impl Trait` in argument position (APIT)
desugars into a hidden generic type parameter (`ownTypeParamCount > 0`), never an
RPITIT opaque `DefId`. Accordingly, `rustc`'s `IllegalRpititVisitor` (`dyn_compatibility.rs:507`)
scans `sig.output()` while `hNoInputRpit` witnesses input well-formedness.
Every vtable-safe method then admits exact non-generic monomorphic ABI erasure
for all extra parameters and return type. -/
theorem vtable_safe_method_monomorphic_signature (superIds : List Nat) (m : MethodDecl)
    (hsafe : isVtableSafeMethod superIds m = true)
    (hNoInputRpit : tyListContainsRpitit m.extraParams = false) :
    m.ownTypeParamCount = 0 ∧
    m.ownConstParamCount = 0 ∧
    (∃ eparams, eraseMonoTyList superIds m.extraParams = some eparams) ∧
    (∃ eret, eraseMonoTy superIds m.retTy = some eret) := by
  dsimp only [isVtableSafeMethod] at hsafe
  cases hf : m.isFinal with
  | true => rw [ite_true_eq _ hf] at hsafe; cases hsafe
  | false =>
    rw [ite_false_eq _ hf] at hsafe
    cases hs : methodRequiresSizedSelf m with
    | true => rw [ite_true_eq _ hs] at hsafe; cases hsafe
    | false =>
      rw [ite_false_eq _ hs] at hsafe
      have hv : virtualCallViolationsForMethod superIds m = [] :=
        (listIsEmpty_eq_true_iff _).mp hsafe
      have props := virtualCall_empty_properties superIds m hv
      have ⟨_, hIn, hOut, _, hRpit, _, hT, hC, _⟩ := props
      have ⟨hErase1, hErase2⟩ := eraseMonoTy_succeeds_of_safe superIds
      exact ⟨hT, hC, hErase2 m.extraParams hIn hNoInputRpit, hErase1 m.retTy hOut hRpit⟩

theorem mem_ownExistentialVtableEntries_iff (t : TraitDecl) (m : MethodDecl) :
    memList m (ownExistentialVtableEntries t) ↔
      memList (.fnDecl m) t.items ∧ isVtableSafeMethod t.superTraitIds m = true := by
  constructor
  · intro hmem
    dsimp only [ownExistentialVtableEntries] at hmem
    have ⟨item, hitem, hf⟩ := listFilterMap_mem
      (fun item =>
        match item with
        | .fnDecl m' => if isVtableSafeMethod t.superTraitIds m' then some m' else none
        | _ => none)
      t.items m hmem
    cases item with
    | fnDecl m' =>
      dsimp only at hf
      cases hs : isVtableSafeMethod t.superTraitIds m' with
      | false => rw [ite_false_eq _ hs] at hf; cases hf
      | true =>
        rw [ite_true_eq _ hs] at hf
        cases hf
        exact ⟨hitem, hs⟩
    | constDecl _ => cases hf
    | tyDecl _ => cases hf
  · intro ⟨hitem, hsafe⟩
    dsimp only [ownExistentialVtableEntries]
    refine mem_listFilterMap_of_mem
      (fun item =>
        match item with
        | .fnDecl m' => if isVtableSafeMethod t.superTraitIds m' then some m' else none
        | _ => none)
      t.items (.fnDecl m) m hitem ?_
    dsimp only
    rw [ite_true_eq _ hsafe]

theorem dynCompatViolations_item_empty (t : TraitDecl) (hcompat : isDynCompatible t = true)
    (item : AssocItemDecl) (hmem : memList item t.items) :
    dynCompatViolationsForAssocItem t.superTraitIds item = [] := by
  dsimp only [isDynCompatible, dynCompatViolationsForTrait] at hcompat
  rw [listIsEmpty_eq_true_iff, listAppend_eq_nil_iff] at hcompat
  exact listConcatMap_empty_forall (dynCompatViolationsForAssocItem t.superTraitIds) t.items
    hcompat.1 item hmem

theorem dyn_compatible_trait_no_sized_self (t : TraitDecl) (hcompat : isDynCompatible t = true) :
    traitRequiresSizedSelf t = false ∧ t.forceDynIncompatible = false := by
  dsimp only [isDynCompatible, dynCompatViolationsForTrait] at hcompat
  rw [listIsEmpty_eq_true_iff, listAppend_eq_nil_iff, listAppend_eq_nil_iff] at hcompat
  have htrait := hcompat.2.1
  have hsized : traitRequiresSizedSelf t = false := by
    cases hs : traitRequiresSizedSelf t with
    | false => rfl
    | true => rw [ite_true_eq _ hs] at htrait; cases htrait
  have hforce : t.forceDynIncompatible = false := by
    rw [ite_false_eq _ hsized] at htrait
    cases hf : t.forceDynIncompatible with
    | false => rfl
    | true => rw [ite_true_eq _ hf] at htrait; cases htrait
  exact ⟨hsized, hforce⟩

theorem dyn_compatible_trait_live_method_vtable_safe (t : TraitDecl)
    (hcompat : isDynCompatible t = true)
    (m : MethodDecl) (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false) :
    isVtableSafeMethod t.superTraitIds m = true := by
  have hitem := dynCompatViolations_item_empty t hcompat (.fnDecl m) hmem
  dsimp only [dynCompatViolationsForAssocItem] at hitem
  rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized] at hitem
  dsimp only [isVtableSafeMethod]
  rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
  cases hvc : virtualCallViolationsForMethod t.superTraitIds m with
  | nil => rfl
  | cons _ _ =>
    rw [hvc] at hitem
    cases hitem

theorem buildVtable_len (t : TraitDecl) (impl_ : ConcreteImpl) :
    listLen (buildVtable t impl_) = 3 + listLen (ownExistentialVtableEntries t) := by
  dsimp only [buildVtable]
  rw [listLen_append, listLen_map]
  rfl

theorem buildVtable_get?_header_0 (t : TraitDecl) (impl_ : ConcreteImpl) :
    listGet? (buildVtable t impl_) 0 = some (.metadataDropInPlace impl_.dropGlueSym) := by
  rfl

theorem buildVtable_get?_header_1 (t : TraitDecl) (impl_ : ConcreteImpl) :
    listGet? (buildVtable t impl_) 1 = some (.metadataSize impl_.sizeBytes) := by
  rfl

theorem buildVtable_get?_header_2 (t : TraitDecl) (impl_ : ConcreteImpl) :
    listGet? (buildVtable t impl_) 2 = some (.metadataAlign impl_.alignBytes) := by
  rfl

theorem buildVtable_get?_own_slot (t : TraitDecl) (impl_ : ConcreteImpl) (k : Nat) (m : MethodDecl)
    (hm : listGet? (ownExistentialVtableEntries t) k = some m) :
    listGet? (buildVtable t impl_) (3 + k) =
      some (
        if impl_.clausesHoldForSelf m then
          let eParams := match eraseMonoTyList t.superTraitIds m.extraParams with | some ps => ps | none => []
          let eRet := match eraseMonoTy t.superTraitIds m.retTy with | some r => r | none => .unit
          let isShim := receiverKindBeq m.receiver .byValueSelf
          VtblEntry.method t.traitId m.methodId (impl_.methodSym m.methodId) isShim eParams eRet
        else
          VtblEntry.vacant t.traitId m.methodId) := by
  dsimp only [buildVtable]
  change listGet? (listAppend (commonVtableHeader impl_) _) (listLen (commonVtableHeader impl_) + k) = _
  rw [listGet?_append_right, listGet?_map, hm]

theorem dyn_compatible_trait_complete_vtable_slots (t : TraitDecl) (impl_ : ConcreteImpl)
    (hcompat : isDynCompatible t = true)
    (m : MethodDecl) (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false)
    (hUnique : ∀ m', memList m' (ownExistentialVtableEntries t) → natEq m'.methodId m.methodId = true → m' = m) :
    ∃ idx,
      vtableSlotIndexOfMethod t m.methodId = some idx ∧
      3 ≤ idx ∧
      idx < listLen (buildVtable t impl_) ∧
      listGet? (buildVtable t impl_) idx =
        some (
          if impl_.clausesHoldForSelf m then
            let eParams := match eraseMonoTyList t.superTraitIds m.extraParams with | some ps => ps | none => []
            let eRet := match eraseMonoTy t.superTraitIds m.retTy with | some r => r | none => .unit
            let isShim := receiverKindBeq m.receiver .byValueSelf
            VtblEntry.method t.traitId m.methodId (impl_.methodSym m.methodId) isShim eParams eRet
          else
            VtblEntry.vacant t.traitId m.methodId) := by
  have hsafe := dyn_compatible_trait_live_method_vtable_safe t hcompat m hmem hnotfinal hnotsized
  have hm_vt : memList m (ownExistentialVtableEntries t) :=
    (mem_ownExistentialVtableEntries_iff t m).mpr ⟨hmem, hsafe⟩
  have ⟨k, hk⟩ := listIndexOf?_of_mem (fun m' => natEq m'.methodId m.methodId)
    (ownExistentialVtableEntries t) m hm_vt (natEq_refl m.methodId)
  have ⟨m', hm'get, hm'pred, hm'mem⟩ := listIndexOf?_some_get?
    (fun m' => natEq m'.methodId m.methodId) (ownExistentialVtableEntries t) k hk
  have hm'_eq : m' = m := hUnique m' hm'mem hm'pred
  rw [hm'_eq] at hm'get
  have hklt : k < listLen (ownExistentialVtableEntries t) :=
    listIndexOf?_lt_len (fun m' => natEq m'.methodId m.methodId) (ownExistentialVtableEntries t) k hk
  refine ⟨3 + k, ?_, ?_, ?_, ?_⟩
  · dsimp only [vtableSlotIndexOfMethod]
    rw [hk]
  · exact Nat.le_add_right 3 k
  · rw [buildVtable_len]
    exact Nat.add_lt_add_left hklt 3
  · exact buildVtable_get?_own_slot t impl_ k m hm'get

theorem vtable_slot_determinism_across_impls (t : TraitDecl) (impl1 impl2 : ConcreteImpl) :
    listLen (buildVtable t impl1) = listLen (buildVtable t impl2) ∧
    (∀ k m entry1 entry2,
      listGet? (ownExistentialVtableEntries t) k = some m →
      listGet? (buildVtable t impl1) (3 + k) = some entry1 →
      listGet? (buildVtable t impl2) (3 + k) = some entry2 →
      vtblEntryMatchesMethod t.traitId m.methodId entry1 = true ∧
      vtblEntryMatchesMethod t.traitId m.methodId entry2 = true) := by
  constructor
  · rw [buildVtable_len t impl1, buildVtable_len t impl2]
  · intro k m entry1 entry2 hm he1 he2
    rw [buildVtable_get?_own_slot t impl1 k m hm] at he1
    rw [buildVtable_get?_own_slot t impl2 k m hm] at he2
    cases he1
    cases he2
    constructor
    · cases _hc1 : impl1.clausesHoldForSelf m with
      | false =>
        rw [ite_false_eq false rfl]
        dsimp only [vtblEntryMatchesMethod]
        rw [boolAnd_eq_true_iff]
        exact ⟨natEq_refl t.traitId, natEq_refl m.methodId⟩
      | true =>
        rw [ite_true_eq true rfl]
        dsimp only [vtblEntryMatchesMethod]
        rw [boolAnd_eq_true_iff]
        exact ⟨natEq_refl t.traitId, natEq_refl m.methodId⟩
    · cases _hc2 : impl2.clausesHoldForSelf m with
      | false =>
        rw [ite_false_eq false rfl]
        dsimp only [vtblEntryMatchesMethod]
        rw [boolAnd_eq_true_iff]
        exact ⟨natEq_refl t.traitId, natEq_refl m.methodId⟩
      | true =>
        rw [ite_true_eq true rfl]
        dsimp only [vtblEntryMatchesMethod]
        rw [boolAnd_eq_true_iff]
        exact ⟨natEq_refl t.traitId, natEq_refl m.methodId⟩

/-! ## Section 6: Theorem Family 2 — `where Self: Sized` Unreachability & `fn by_val(self)` -/

theorem self_sized_item_exempt_from_violations (superIds : List Nat) :
    (∀ (m : MethodDecl), methodRequiresSizedSelf m = true →
      dynCompatViolationsForAssocItem superIds (.fnDecl m) = []) ∧
    (∀ (c : AssocConstDecl), constRequiresSizedSelf c = true →
      dynCompatViolationsForAssocItem superIds (.constDecl c) = []) ∧
    (∀ (a : AssocTyDecl), tyRequiresSizedSelf a = true →
      dynCompatViolationsForAssocItem superIds (.tyDecl a) = []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    dsimp only [dynCompatViolationsForAssocItem]
    cases _hf : m.isFinal with
    | true => rw [ite_true_eq true rfl]
    | false => rw [ite_false_eq false rfl, ite_true_eq _ hm]
  · intro c hc
    dsimp only [dynCompatViolationsForAssocItem]
    cases _hf : c.isFinal with
    | true => rw [ite_true_eq true rfl]
    | false => rw [ite_false_eq false rfl, ite_true_eq _ hc]
  · intro a ha
    dsimp only [dynCompatViolationsForAssocItem]
    rw [ite_true_eq _ ha]

theorem where_self_clone_elaborates_sized_self (m : MethodDecl) (cloneTraitId : Nat)
    (hclone : memList (.nonAutoSizedTrait cloneTraitId) m.clauses) :
    methodRequiresSizedSelf m = true := by
  dsimp only [methodRequiresSizedSelf]
  have hany : listAny clauseImpliesSizedSelf m.clauses = true :=
    listAny_true_of_mem clauseImpliesSizedSelf m.clauses (.nonAutoSizedTrait cloneTraitId) hclone rfl
  rw [hany, boolOr_eq_true_iff]
  exact Or.inr rfl

theorem self_sized_method_not_vtable_safe (superIds : List Nat) (m : MethodDecl)
    (hsized : methodRequiresSizedSelf m = true) :
    isVtableSafeMethod superIds m = false := by
  dsimp only [isVtableSafeMethod]
  cases _hf : m.isFinal with
  | true => rw [ite_true_eq true rfl]
  | false => rw [ite_false_eq false rfl, ite_true_eq _ hsized]

theorem self_sized_method_omitted_from_vtable (t : TraitDecl) (m : MethodDecl)
    (_hsized : methodRequiresSizedSelf m = true)
    (hNoAlias : ∀ m', memList (.fnDecl m') t.items → m'.methodId = m.methodId → methodRequiresSizedSelf m' = true) :
    vtableSlotIndexOfMethod t m.methodId = none := by
  dsimp only [vtableSlotIndexOfMethod]
  cases hind : listIndexOf? (fun m' => natEq m'.methodId m.methodId) (ownExistentialVtableEntries t) with
  | none => rfl
  | some k =>
    have ⟨m', _, hpred, hmemVt⟩ := listIndexOf?_some_get?
      (fun m' => natEq m'.methodId m.methodId) (ownExistentialVtableEntries t) k hind
    have ⟨hitem, hsafe⟩ := (mem_ownExistentialVtableEntries_iff t m').mp hmemVt
    have heqid : m'.methodId = m.methodId := (natEq_eq_iff m'.methodId m.methodId).mp hpred
    have hmsized := hNoAlias m' hitem heqid
    have hnotsafe := self_sized_method_not_vtable_safe t.superTraitIds m' hmsized
    rw [hnotsafe] at hsafe
    cases hsafe

theorem self_sized_method_rejected_e0599_never_missing_slot (t : TraitDecl) (d : DynFatPtr)
    (m : MethodDecl) (hsized : methodRequiresSizedSelf m = true)
    (hasUnsizedFnParams dynHasMethodClauses : Bool) :
    canInvokeMethodOnDyn hasUnsizedFnParams dynHasMethodClauses m = false ∧
    evalDynCall t d m hasUnsizedFnParams dynHasMethodClauses = .rejected .e0599SizedRequirement := by
  dsimp only [canInvokeMethodOnDyn, evalDynCall]
  rw [ite_true_eq _ hsized, hsized]
  exact ⟨rfl, rfl⟩

/-- Any method callable on `dyn Trait` (`canInvokeMethodOnDyn = true`) of a
`dyn`-compatible trait is guaranteed `vtable_safe` and present in `buildVtable`,
so omitting `Self: Sized` methods can never cause a missing vtable slot. -/
theorem callable_dyn_method_never_missing_slot (t : TraitDecl) (impl_ : ConcreteImpl)
    (p : ConcretePtrVal) (d : DynFatPtr) (m : MethodDecl)
    (hasUnsizedFnParams : Bool)
    (hcompat : isDynCompatible t = true)
    (hmem : memList (.fnDecl m) t.items)
    (hcall : canInvokeMethodOnDyn hasUnsizedFnParams true m = true)
    (hcoerce : coerceToDyn t impl_ p = some d)
    (hclauses : impl_.clausesHoldForSelf m = true)
    (hUnique : ∀ m', memList m' (ownExistentialVtableEntries t) → natEq m'.methodId m.methodId = true → m' = m) :
    isVtableSafeMethod t.superTraitIds m = true ∧
    evalDynCall t d m hasUnsizedFnParams true =
      .invoked impl_.concreteSelfId (impl_.methodSym m.methodId) p.dataPtr
        (receiverKindBeq m.receiver .byValueSelf) := by
  dsimp only [canInvokeMethodOnDyn] at hcall
  rw [boolAnd_eq_true_iff, boolAnd_eq_true_iff, boolAnd_eq_true_iff,
      boolNot_eq_true_iff, boolNot_eq_true_iff] at hcall
  have hnotsized := hcall.1
  have hnotfinal := hcall.2.1
  have hrecvOk := hcall.2.2.2
  have hsafe := dyn_compatible_trait_live_method_vtable_safe t hcompat m hmem hnotfinal hnotsized
  have ⟨idx, hslot, _, _, hget⟩ :=
    dyn_compatible_trait_complete_vtable_slots t impl_ hcompat m hmem hnotfinal hnotsized hUnique
  dsimp only [coerceToDyn] at hcoerce
  rw [ite_true_eq _ hcompat] at hcoerce
  cases hdisp : isDispatchFromDynReceiver p.receiver with
  | false => rw [ite_false_eq _ hdisp] at hcoerce; cases hcoerce
  | true =>
    rw [ite_true_eq _ hdisp] at hcoerce
    cases hcoerce
    dsimp only [evalDynCall]
    rw [ite_false_eq _ hnotsized, ite_false_eq _ hnotfinal]
    have hbyvalCond : boolAnd (receiverKindBeq m.receiver .byValueSelf) (boolNot hasUnsizedFnParams) = false := by
      cases hbv : receiverKindBeq m.receiver .byValueSelf with
      | false => rfl
      | true =>
        rw [hbv] at hrecvOk
        dsimp only [boolNot] at hrecvOk
        cases hu : hasUnsizedFnParams with
        | false => rw [hu] at hrecvOk; cases hrecvOk
        | true => rfl
    rw [ite_false_eq _ hbyvalCond]
    rw [ite_false_eq _ (rfl : boolNot true = false)]
    rw [hslot]
    dsimp only
    rw [hget, ite_true_eq _ hclauses]
    exact ⟨hsafe, rfl⟩

/-- Models `dyn_compatibility.rs:520/526` (`receiver_ty != tcx.types.self_param`) +
`rustc_mir_transform::shim::ShimKind::VTable` + `rustc_borrowck::MoveUnsized` (`E0161`):
a non-generic non-`Self: Sized` `fn by_val(self)` method incurs ZERO `E0038`
violations, receives a vtable slot with `viaVTableShim = true`, fails safe calls
with `E0161` rather than `E0038`, and succeeds under `#![feature(unsized_fn_params)]`. -/
theorem by_val_self_exempt_from_e0038_yet_fails_safe_call (t : TraitDecl) (impl_ : ConcreteImpl)
    (p : ConcretePtrVal) (d : DynFatPtr) (m : MethodDecl)
    (hcompat : isDynCompatible t = true)
    (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false)
    (hnotsized : methodRequiresSizedSelf m = false)
    (hbyval : m.receiver = .byValueSelf)
    (hcoerce : coerceToDyn t impl_ p = some d)
    (hclauses : impl_.clausesHoldForSelf m = true)
    (hUnique : ∀ m', memList m' (ownExistentialVtableEntries t) → natEq m'.methodId m.methodId = true → m' = m) :
    virtualCallViolationsForMethod t.superTraitIds m = [] ∧
    isVtableSafeMethod t.superTraitIds m = true ∧
    (∃ idx eParams eRet,
      vtableSlotIndexOfMethod t m.methodId = some idx ∧
      listGet? d.vtable idx = some (.method t.traitId m.methodId (impl_.methodSym m.methodId) true eParams eRet)) ∧
    evalDynCall t d m false true = .rejected .e0161MoveUnsized ∧
    evalDynCall t d m true true = .invoked impl_.concreteSelfId (impl_.methodSym m.methodId) p.dataPtr true := by
  have hitem := dynCompatViolations_item_empty t hcompat (.fnDecl m) hmem
  dsimp only [dynCompatViolationsForAssocItem] at hitem
  rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized] at hitem
  have hvc : virtualCallViolationsForMethod t.superTraitIds m = [] := by
    cases h0 : virtualCallViolationsForMethod t.superTraitIds m with
    | nil => rfl
    | cons _ _ => rw [h0] at hitem; cases hitem
  have hsafe := dyn_compatible_trait_live_method_vtable_safe t hcompat m hmem hnotfinal hnotsized
  have ⟨idx, hslot, _, _, hget⟩ :=
    dyn_compatible_trait_complete_vtable_slots t impl_ hcompat m hmem hnotfinal hnotsized hUnique
  dsimp only [coerceToDyn] at hcoerce
  rw [ite_true_eq _ hcompat] at hcoerce
  cases hdisp : isDispatchFromDynReceiver p.receiver with
  | false => rw [ite_false_eq _ hdisp] at hcoerce; cases hcoerce
  | true =>
    rw [ite_true_eq _ hdisp] at hcoerce
    cases hcoerce
    rw [ite_true_eq _ hclauses, hbyval] at hget
    dsimp only [receiverKindBeq] at hget
    refine ⟨hvc, hsafe, ⟨idx, _, _, hslot, hget⟩, ?_, ?_⟩
    · dsimp only [evalDynCall]
      rw [ite_false_eq _ hnotsized, ite_false_eq _ hnotfinal, hbyval]
      rw [ite_true_eq _ (rfl : boolAnd (receiverKindBeq .byValueSelf .byValueSelf) (boolNot false) = true)]
    · dsimp only [evalDynCall]
      rw [ite_false_eq _ hnotsized, ite_false_eq _ hnotfinal, hbyval]
      rw [ite_false_eq _ (rfl : boolAnd (receiverKindBeq .byValueSelf .byValueSelf) (boolNot true) = false)]
      rw [ite_false_eq _ (rfl : boolNot true = false)]
      rw [hslot]
      dsimp only
      rw [hget]

/-! ## Section 7: Theorem Family 3 — Uniform ABI Erasure & `DispatchFromDyn` Receivers -/

theorem smart_ptr_receivers_dispatch_from_dyn :
    (∀ mutbl, isDispatchFromDynReceiver (.refSelf mutbl) = true) ∧
    (∀ mutbl, isDispatchFromDynReceiver (.rawPtrSelf mutbl) = true) ∧
    isDispatchFromDynReceiver .boxSelf = true ∧
    isDispatchFromDynReceiver .rcSelf = true ∧
    isDispatchFromDynReceiver .arcSelf = true ∧
    (∀ inner, isDispatchFromDynReceiver inner = true → isDispatchFromDynReceiver (.pinSelf inner) = true) ∧
    (∀ inner, isDispatchFromDynReceiver inner = true → isDispatchFromDynReceiver (.customDispatch true true true inner) = true) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · intro mutbl; rfl
  · intro mutbl; rfl
  · intro inner h; exact h
  · intro inner h; dsimp only [isDispatchFromDynReceiver]; rw [h]; rfl

theorem double_indirection_undispatchable (superIds : List Nat) (m : MethodDecl)
    (hrec : m.receiver = .doubleIndirection)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false) :
    isDispatchFromDynReceiver m.receiver = false ∧
    memList (DynCompatViolation.method m.methodId .undispatchableReceiver)
      (dynCompatViolationsForAssocItem superIds (.fnDecl m)) := by
  rw [hrec]
  constructor
  · rfl
  · dsimp only [dynCompatViolationsForAssocItem]
    rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
    dsimp only [virtualCallViolationsForMethod]
    rw [hrec]
    dsimp only
    refine memList_map_of_mem (DynCompatViolation.method m.methodId) ?_
    have hcond : boolAnd (boolNot (receiverKindBeq ReceiverKind.doubleIndirection ReceiverKind.byValueSelf))
        (boolNot (isDispatchFromDynReceiver ReceiverKind.doubleIndirection)) = true := rfl
    rw [ite_true_eq _ hcond]
    exact memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_right _ _ _
      (memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_left _ _ _ (Or.inl rfl))))))

theorem bad_custom_ptr_undispatchable (isTr s1 g1 : Bool) (inner : ReceiverKind)
    (hfail : boolAnd isTr (boolAnd s1 (boolAnd g1 (isDispatchFromDynReceiver inner))) = false) :
    isDispatchFromDynReceiver (.customDispatch isTr s1 g1 inner) = false :=
  hfail

/-- Uniform ABI Erasure Soundness across `&`/`&mut`/`Box`/`Rc`/`Arc`/`Pin`/raw pointers
and valid transparent `DispatchFromDyn` wrappers: unsized coercion preserves `dataPtr`
verbatim and dispatches `evalDynCall` through the concrete `impl_` vtable without reboxing. -/
theorem dispatch_from_dyn_uniform_abi_soundness (t : TraitDecl) (impl_ : ConcreteImpl)
    (p : ConcretePtrVal) (m : MethodDecl) (hasUnsizedFnParams : Bool)
    (hcompat : isDynCompatible t = true)
    (hdisp : isDispatchFromDynReceiver p.receiver = true)
    (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false)
    (hnotsized : methodRequiresSizedSelf m = false)
    (hrecvCall : m.receiver ≠ .byValueSelf ∨ hasUnsizedFnParams = true)
    (hclauses : impl_.clausesHoldForSelf m = true)
    (hUnique : ∀ m', memList m' (ownExistentialVtableEntries t) → natEq m'.methodId m.methodId = true → m' = m) :
    ∃ d,
      coerceToDyn t impl_ p = some d ∧
      d.dataPtr = p.dataPtr ∧
      d.erasedConcreteId = impl_.concreteSelfId ∧
      evalDynCall t d m hasUnsizedFnParams true =
        .invoked impl_.concreteSelfId (impl_.methodSym m.methodId) p.dataPtr
          (receiverKindBeq m.receiver .byValueSelf) := by
  have ⟨idx, hslot, _, _, hget⟩ :=
    dyn_compatible_trait_complete_vtable_slots t impl_ hcompat m hmem hnotfinal hnotsized hUnique
  let d : DynFatPtr := {
    erasedConcreteId := impl_.concreteSelfId
    dataPtr := p.dataPtr
    traitId := t.traitId
    vtable := buildVtable t impl_
    receiver := p.receiver
  }
  have hcoerce : coerceToDyn t impl_ p = some d := by
    dsimp only [coerceToDyn]
    rw [ite_true_eq _ hcompat, ite_true_eq _ hdisp]
  have hbyvalCond : boolAnd (receiverKindBeq m.receiver .byValueSelf) (boolNot hasUnsizedFnParams) = false := by
    cases hrecvCall with
    | inl hne =>
      have hb : receiverKindBeq m.receiver .byValueSelf = false := by
        cases hmr : m.receiver with
        | byValueSelf => exact False.elim (hne hmr)
        | none | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
        | customDispatch _ _ _ _ | doubleIndirection => rfl
      rw [hb]; rfl
    | inr huns =>
      rw [huns]
      cases receiverKindBeq m.receiver .byValueSelf <;> rfl
  refine ⟨d, hcoerce, rfl, rfl, ?_⟩
  dsimp only [evalDynCall]
  rw [ite_false_eq _ hnotsized, ite_false_eq _ hnotfinal, ite_false_eq _ hbyvalCond]
  rw [ite_false_eq _ (rfl : boolNot true = false)]
  rw [hslot]
  dsimp only
  change (match listGet? (buildVtable t impl_) idx with
    | some (.method _ _ fnSym viaShim _ _) => DispatchOutcome.invoked impl_.concreteSelfId fnSym p.dataPtr viaShim
    | some (.vacant _ _) => DispatchOutcome.rejected CallRejectionReason.unexpectedVacantSlot
    | _ => DispatchOutcome.rejected CallRejectionReason.missingVtableSlot) =
    DispatchOutcome.invoked impl_.concreteSelfId (impl_.methodSym m.methodId) p.dataPtr
      (receiverKindBeq m.receiver .byValueSelf)
  rw [hget, ite_true_eq _ hclauses]

/-! ## Section 8: Theorem Family 4 — Violation Necessity Counterexamples -/

/-- No finite vtable symbol list can contain every monomorphization of an
unbounded injective family `instSym : Nat → Nat` over concrete type indices
(`f::<T_0>, f::<T_1>, ...`), proving necessity of rejecting `ownTypeParamCount > 0`
without `Self: Sized`. Constructively proved via `pigeonhole_inj_nat` (`omega`-free). -/
theorem generic_method_finite_vtable_impossible (instSym : Nat → Nat)
    (hinj : ∀ a b, instSym a = instSym b → a = b) (vt : List Nat) :
    ∃ tyArg : Nat, ¬ memList (instSym tyArg) vt :=
  pigeonhole_inj_nat instSym hinj vt

theorem generic_method_rejected_e0038 (t : TraitDecl) (m : MethodDecl)
    (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false)
    (hnotstatic : m.receiver ≠ .none)
    (hgen : 0 < m.ownTypeParamCount ∨ 0 < m.ownConstParamCount) :
    memList (DynCompatViolation.method m.methodId .generic) (dynCompatViolationsForTrait t) ∧
    isDynCompatible t = false := by
  have hcond : boolOr (natLt 0 m.ownTypeParamCount) (natLt 0 m.ownConstParamCount) = true := by
    rw [boolOr_eq_true_iff, natLt_true_iff, natLt_true_iff]
    exact hgen
  have hviol : memList .generic (virtualCallViolationsForMethod t.superTraitIds m) := by
    have extract : ∀ r, r = m.receiver → r ≠ .none →
        memList .generic (virtualCallViolationsForMethod t.superTraitIds m) := by
      intro r hr hnr
      dsimp only [virtualCallViolationsForMethod]
      rw [← hr]
      cases r with
      | none => exact False.elim (hnr rfl)
      | byValueSelf | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
      | customDispatch _ _ _ _ | doubleIndirection =>
        dsimp only
        rw [ite_true_eq _ hcond]
        exact memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_right _ _ _
          (memList_app_right _ _ _ (memList_app_left _ _ _ (Or.inl rfl)))))
    exact extract m.receiver rfl hnotstatic
  have hitem : memList (DynCompatViolation.method m.methodId .generic)
      (dynCompatViolationsForAssocItem t.superTraitIds (.fnDecl m)) := by
    dsimp only [dynCompatViolationsForAssocItem]
    rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
    exact memList_map_of_mem (DynCompatViolation.method m.methodId) hviol
  have htrait : memList (DynCompatViolation.method m.methodId .generic)
      (dynCompatViolationsForTrait t) := by
    dsimp only [dynCompatViolationsForTrait]
    exact memList_app_left _ _ _ (mem_listConcatMap_of_mem
      (dynCompatViolationsForAssocItem t.superTraitIds) t.items (.fnDecl m)
      (DynCompatViolation.method m.methodId .generic) hmem hitem)
  refine ⟨htrait, ?_⟩
  dsimp only [isDynCompatible]
  cases hnn : dynCompatViolationsForTrait t with
  | nil => rw [hnn] at htrait; cases htrait
  | cons _ _ => rfl

/-- No finite `dyn` existential projection dictionary can cover an unbounded
injective GAT family `Self::Item<k>` (`k : Nat`) without forcing callers to supply
concrete GAT bindings at trait-object formation time. -/
theorem gat_finite_existential_erasure_impossible (projSym : Nat → Nat)
    (hinj : ∀ a b, projSym a = projSym b → a = b) (erasedTable : List Nat) :
    ∃ gatArg : Nat, ¬ memList (projSym gatArg) erasedTable :=
  pigeonhole_inj_nat projSym hinj erasedTable

theorem gat_without_sized_rejected_e0038 (t : TraitDecl) (a : AssocTyDecl)
    (hmem : memList (.tyDecl a) t.items)
    (hnotsized : tyRequiresSizedSelf a = false)
    (hgat : 0 < a.ownGenericCount) :
    memList (DynCompatViolation.genericAssocTy a.tyId) (dynCompatViolationsForTrait t) ∧
    isDynCompatible t = false := by
  have hlt : natLt 0 a.ownGenericCount = true := (natLt_true_iff 0 a.ownGenericCount).mpr hgat
  have hitem : memList (DynCompatViolation.genericAssocTy a.tyId)
      (dynCompatViolationsForAssocItem t.superTraitIds (.tyDecl a)) := by
    dsimp only [dynCompatViolationsForAssocItem]
    rw [ite_false_eq _ hnotsized, ite_true_eq _ hlt]
    exact Or.inl rfl
  have htrait : memList (DynCompatViolation.genericAssocTy a.tyId)
      (dynCompatViolationsForTrait t) := by
    dsimp only [dynCompatViolationsForTrait]
    exact memList_app_left _ _ _ (mem_listConcatMap_of_mem
      (dynCompatViolationsForAssocItem t.superTraitIds) t.items (.tyDecl a)
      (DynCompatViolation.genericAssocTy a.tyId) hmem hitem)
  refine ⟨htrait, ?_⟩
  dsimp only [isDynCompatible]
  cases hnn : dynCompatViolationsForTrait t with
  | nil => rw [hnn] at htrait; cases htrait
  | cons _ _ => rfl

/-- An unboxed RPITIT return layout `(size, align)` varies across concrete impls;
no single caller-allocated stack ABI pair `(abiSize, abiAlign)` can match two
distinct concrete impl layouts simultaneously. -/
structure AbiLayoutPair where
  sizeBytes : Nat
  alignBytes : Nat

theorem rpitit_single_fixed_abi_impossible (l1 l2 : AbiLayoutPair)
    (hdiff : l1.sizeBytes ≠ l2.sizeBytes ∨ l1.alignBytes ≠ l2.alignBytes) :
    ∀ abi : AbiLayoutPair, ¬ (abi = l1 ∧ abi = l2) := by
  intro abi ⟨h1, h2⟩
  have heq : l1 = l2 := h1.symm.trans h2
  cases hdiff with
  | inl hs => exact hs (congrArg AbiLayoutPair.sizeBytes heq)
  | inr ha => exact ha (congrArg AbiLayoutPair.alignBytes heq)

theorem rpitit_and_async_fn_rejected_e0038 (t : TraitDecl) (m : MethodDecl)
    (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false)
    (hnotstatic : m.receiver ≠ .none) :
    (m.isAsync = true →
      memList (DynCompatViolation.method m.methodId .asyncFn) (dynCompatViolationsForTrait t) ∧
      isDynCompatible t = false) ∧
    (m.isAsync = false → tyContainsRpitit m.retTy = true →
      memList (DynCompatViolation.method m.methodId .referencesImplTraitInTrait) (dynCompatViolationsForTrait t) ∧
      isDynCompatible t = false) := by
  constructor
  · intro hasync
    have hviol : memList .asyncFn (virtualCallViolationsForMethod t.superTraitIds m) := by
      have ex : ∀ r, r = m.receiver → r ≠ .none →
          memList .asyncFn (virtualCallViolationsForMethod t.superTraitIds m) := by
        intro r hr hnr
        dsimp only [virtualCallViolationsForMethod]
        rw [← hr]
        cases r with
        | none => exact False.elim (hnr rfl)
        | byValueSelf | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
        | customDispatch _ _ _ _ | doubleIndirection =>
          dsimp only
          rw [ite_true_eq _ hasync]
          exact memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_left _ _ _ (Or.inl rfl)))
      exact ex m.receiver rfl hnotstatic
    have hitem : memList (DynCompatViolation.method m.methodId .asyncFn)
        (dynCompatViolationsForAssocItem t.superTraitIds (.fnDecl m)) := by
      dsimp only [dynCompatViolationsForAssocItem]
      rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
      exact memList_map_of_mem (DynCompatViolation.method m.methodId) hviol
    have htr : memList (DynCompatViolation.method m.methodId .asyncFn) (dynCompatViolationsForTrait t) := by
      dsimp only [dynCompatViolationsForTrait]
      exact memList_app_left _ _ _ (mem_listConcatMap_of_mem
        (dynCompatViolationsForAssocItem t.superTraitIds) t.items (.fnDecl m) _ hmem hitem)
    refine ⟨htr, ?_⟩
    dsimp only [isDynCompatible]
    cases hnn : dynCompatViolationsForTrait t with
    | nil => rw [hnn] at htr; cases htr
    | cons _ _ => rfl
  · intro hnotasync hrpit
    have hviol : memList .referencesImplTraitInTrait (virtualCallViolationsForMethod t.superTraitIds m) := by
      have ex : ∀ r, r = m.receiver → r ≠ .none →
          memList .referencesImplTraitInTrait (virtualCallViolationsForMethod t.superTraitIds m) := by
        intro r hr hnr
        dsimp only [virtualCallViolationsForMethod]
        rw [← hr]
        cases r with
        | none => exact False.elim (hnr rfl)
        | byValueSelf | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
        | customDispatch _ _ _ _ | doubleIndirection =>
          dsimp only
          rw [ite_false_eq _ hnotasync, ite_true_eq _ hrpit]
          exact memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_left _ _ _ (Or.inl rfl)))
      exact ex m.receiver rfl hnotstatic
    have hitem : memList (DynCompatViolation.method m.methodId .referencesImplTraitInTrait)
        (dynCompatViolationsForAssocItem t.superTraitIds (.fnDecl m)) := by
      dsimp only [dynCompatViolationsForAssocItem]
      rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
      exact memList_map_of_mem (DynCompatViolation.method m.methodId) hviol
    have htr : memList (DynCompatViolation.method m.methodId .referencesImplTraitInTrait)
        (dynCompatViolationsForTrait t) := by
      dsimp only [dynCompatViolationsForTrait]
      exact memList_app_left _ _ _ (mem_listConcatMap_of_mem
        (dynCompatViolationsForAssocItem t.superTraitIds) t.items (.fnDecl m) _ hmem hitem)
    refine ⟨htr, ?_⟩
    dsimp only [isDynCompatible]
    cases hnn : dynCompatViolationsForTrait t with
    | nil => rw [hnn] at htr; cases htr
    | cons _ _ => rfl

theorem where_non_auto_unsized_rejected_e0038 (t : TraitDecl) (m : MethodDecl)
    (cid : Nat) (hmem : memList (.fnDecl m) t.items)
    (hnotfinal : m.isFinal = false) (hnotsized : methodRequiresSizedSelf m = false)
    (hnotstatic : m.receiver ≠ .none)
    (hclause : memList (.nonAutoUnsizedTrait cid) m.clauses) :
    memList (DynCompatViolation.method m.methodId .whereClauseReferencesSelf)
      (dynCompatViolationsForTrait t) ∧
    isDynCompatible t = false := by
  have hcl : listAny (clauseIsWhereSelfViolation t.superTraitIds) m.clauses = true :=
    listAny_true_of_mem (clauseIsWhereSelfViolation t.superTraitIds) m.clauses (.nonAutoUnsizedTrait cid) hclause rfl
  have hviol : memList .whereClauseReferencesSelf (virtualCallViolationsForMethod t.superTraitIds m) := by
    have ex : ∀ r, r = m.receiver → r ≠ .none →
        memList .whereClauseReferencesSelf (virtualCallViolationsForMethod t.superTraitIds m) := by
      intro r hr hnr
      dsimp only [virtualCallViolationsForMethod]
      rw [← hr]
      cases r with
      | none => exact False.elim (hnr rfl)
      | byValueSelf | refSelf _ | rawPtrSelf _ | boxSelf | rcSelf | arcSelf | pinSelf _
      | customDispatch _ _ _ _ | doubleIndirection =>
        dsimp only
        rw [ite_true_eq _ hcl]
        exact memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_right _ _ _
          (memList_app_right _ _ _ (memList_app_right _ _ _ (memList_app_right _ _ _ (Or.inl rfl))))))
    exact ex m.receiver rfl hnotstatic
  have hitem : memList (DynCompatViolation.method m.methodId .whereClauseReferencesSelf)
      (dynCompatViolationsForAssocItem t.superTraitIds (.fnDecl m)) := by
    dsimp only [dynCompatViolationsForAssocItem]
    rw [ite_false_eq _ hnotfinal, ite_false_eq _ hnotsized]
    exact memList_map_of_mem (DynCompatViolation.method m.methodId) hviol
  have htr : memList (DynCompatViolation.method m.methodId .whereClauseReferencesSelf)
      (dynCompatViolationsForTrait t) := by
    dsimp only [dynCompatViolationsForTrait]
    exact memList_app_left _ _ _ (mem_listConcatMap_of_mem
      (dynCompatViolationsForAssocItem t.superTraitIds) t.items (.fnDecl m) _ hmem hitem)
  refine ⟨htr, ?_⟩
  dsimp only [isDynCompatible]
  cases hnn : dynCompatViolationsForTrait t with
  | nil => rw [hnn] at htr; cases htr
  | cons _ _ => rfl

/-! ## Section 9: Audited Concrete Rust & `google/zerocopy` Specimens (`rfl`) -/

noncomputable def mkSimpleFn (mid : Nat) (recv : ReceiverKind)
    (sized : Bool := false) (ownTy : Nat := 0) (clauses : List ClausePred := [])
    (extraParams : List TyExpr := []) (retTy : TyExpr := .prim 1)
    (isAsync : Bool := false) : AssocItemDecl :=
  .fnDecl {
    methodId := mid
    hasExplicitSizedSelf := sized
    isFinal := false
    isAsync := isAsync
    isCVariadic := false
    ownTypeParamCount := ownTy
    ownConstParamCount := 0
    receiver := recv
    extraParams := extraParams
    retTy := retTy
    clauses := clauses
  }

/-- `zerocopy::Immutable` (`src/lib.rs:1731-1738`): only method has `where Self: Sized`. -/
noncomputable def zcImmutableTrait : TraitDecl := {
  traitId := 10
  superTraitIds := [10]
  forceDynIncompatible := false
  traitClauses := []
  items := [mkSimpleFn 101 .none true 0 [] [] .unit]
}

/-- `zerocopy::Unaligned` (`src/lib.rs:6669-6676`): only method has `where Self: Sized`. -/
noncomputable def zcUnalignedTrait : TraitDecl := {
  traitId := 11
  superTraitIds := [11]
  forceDynIncompatible := false
  traitClauses := []
  items := [mkSimpleFn 111 .none true 0 [] [] .unit]
}

/-- `zerocopy::KnownLayout` (`src/lib.rs:748-907`): assoc const `LAYOUT` + 7 static fns
(`raw_from_ptr_len`, `pointer_to_metadata`, `size_of_val_raw`, `raw_dangling`,
`size_for_metadata`, `size_for_metadata_unchecked`, `is_valid_metadata`). -/
noncomputable def zcKnownLayoutTrait : TraitDecl := {
  traitId := 12
  superTraitIds := [12]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    mkSimpleFn 120 .none true 0 [] [] .unit,
    .tyDecl { tyId := 121, hasExplicitSizedSelf := false, ownGenericCount := 0, itemBounds := [], clauses := [] },
    .constDecl { constId := 122, hasExplicitSizedSelf := false, isFinal := false, gcaMinConstEnabled := false, isTypeConst := false, ownParamCount := 0, constTy := .prim 10, clauses := [] },
    mkSimpleFn 123 .none false,
    mkSimpleFn 124 .none false,
    mkSimpleFn 125 .none false,
    mkSimpleFn 126 .none false,
    mkSimpleFn 127 .none false,
    mkSimpleFn 128 .none false,
    mkSimpleFn 129 .none false
  ]
}

/-- `zerocopy::TryFromBytes` (`src/lib.rs:1967-3277+`): `is_safe<A>` + 12 `try_*` static fns.
Note `is_safe<A>` reports `.staticMethod` (dyn_compatibility.rs:475 returns early before generic check!). -/
noncomputable def zcTryFromBytesTrait : TraitDecl := {
  traitId := 13
  superTraitIds := [13]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    mkSimpleFn 130 .none true 0 [] [] .unit,
    mkSimpleFn 131 .none false 1,
    mkSimpleFn 132 .none false,
    mkSimpleFn 133 .none false,
    mkSimpleFn 134 .none false,
    mkSimpleFn 135 .none false,
    mkSimpleFn 136 .none false,
    mkSimpleFn 137 .none false,
    mkSimpleFn 138 .none false,
    mkSimpleFn 139 .none false,
    mkSimpleFn 140 .none false,
    mkSimpleFn 141 .none false,
    mkSimpleFn 142 .none false,
    mkSimpleFn 143 .none false
  ]
}

/-- `zerocopy::FromZeros` (`src/lib.rs:3770+`): `zero(&mut self)` is vtable-safe,
`new_zeroed` has `Self: Sized`, and supertrait `TryFromBytes` brings `is_safe` etc. -/
noncomputable def zcFromZerosZeroMethod : MethodDecl := {
  methodId := 152
  hasExplicitSizedSelf := false
  isFinal := false
  isAsync := false
  isCVariadic := false
  ownTypeParamCount := 0
  ownConstParamCount := 0
  receiver := .refSelf true
  extraParams := []
  retTy := .unit
  clauses := []
}

noncomputable def zcFromZerosTrait : TraitDecl := {
  traitId := 15
  superTraitIds := [15, 13]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    mkSimpleFn 131 .none false 1,
    mkSimpleFn 150 .none true 0 [] [] .unit,
    mkSimpleFn 151 .none true 0 [] [] .selfParam,
    .fnDecl zcFromZerosZeroMethod
  ]
}

/-- `zerocopy::FromBytes` (`src/lib.rs:4382-5733+`): static constructors cause `E0038`. -/
noncomputable def zcFromBytesTrait : TraitDecl := {
  traitId := 16
  superTraitIds := [16, 15, 13]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    mkSimpleFn 131 .none false 1,
    mkSimpleFn 161 .none false,
    mkSimpleFn 162 .none false
  ]
}

/-- `zerocopy::IntoBytes` (`src/lib.rs:6029-6534`):
- `as_bytes`, `as_mut_bytes`, `as_bytes_mut` hit `.whereClauseReferencesSelf` (`Self: Immutable`/`FromBytes`),
- `write_to`, `write_to_prefix`, `write_to_suffix` hit BOTH `.referencesSelfOutput` and `.whereClauseReferencesSelf`. -/
noncomputable def zcIntoBytesTrait : TraitDecl := {
  traitId := 17
  superTraitIds := [17]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    mkSimpleFn 170 .none true 0 [] [] .unit,
    mkSimpleFn 171 (.refSelf false) false 0 [.nonAutoUnsizedTrait 10] [] (.ref false (.prim 8)),
    mkSimpleFn 172 (.refSelf true) false 0 [.nonAutoUnsizedTrait 10, .nonAutoUnsizedTrait 16] [] (.ref true (.prim 8)),
    mkSimpleFn 173 (.refSelf false) false 0 [.nonAutoUnsizedTrait 16] [.ref true (.prim 8)] (.named 99 [.ref false .selfParam]),
    mkSimpleFn 174 (.refSelf false) false 0 [.nonAutoUnsizedTrait 16] [.ref true (.prim 8)] (.named 99 [.ref false .selfParam]),
    mkSimpleFn 175 (.refSelf false) false 0 [.nonAutoUnsizedTrait 16] [.ref true (.prim 8)] (.named 99 [.ref false .selfParam]),
    mkSimpleFn 176 (.refSelf true) false 0 [.nonAutoUnsizedTrait 16] [] (.ref true (.prim 8))
  ]
}

theorem zc_immutable_and_unaligned_dyn_compatible :
    isDynCompatible zcImmutableTrait = true ∧
    isDynCompatible zcUnalignedTrait = true ∧
    listLen (ownExistentialVtableEntries zcImmutableTrait) = 0 ∧
    listLen (ownExistentialVtableEntries zcUnalignedTrait) = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem zc_known_layout_and_conversion_traits_e0038 :
    isDynCompatible zcKnownLayoutTrait = false ∧
    isDynCompatible zcTryFromBytesTrait = false ∧
    isDynCompatible zcFromZerosTrait = false ∧
    isDynCompatible zcFromBytesTrait = false ∧
    isDynCompatible zcIntoBytesTrait = false ∧
    isVtableSafeMethod zcFromZerosTrait.superTraitIds zcFromZerosZeroMethod = true ∧
    dynCompatViolationsForAssocItem zcTryFromBytesTrait.superTraitIds (mkSimpleFn 131 .none false 1) =
      [.method 131 .staticMethod] ∧
    dynCompatViolationsForAssocItem zcIntoBytesTrait.superTraitIds
      (mkSimpleFn 173 (.refSelf false) false 0 [.nonAutoUnsizedTrait 16] [.ref true (.prim 8)] (.named 99 [.ref false .selfParam])) =
      [.method 173 .referencesSelfOutput, .method 173 .whereClauseReferencesSelf] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SlotProbe` LLVM IR vtable specimen matching compiled `@vtable.0` (`Rc<u32>`)
and `@vtable.1` (`u32`):
`m1` (slot 3), `m_sized` (OMITTED!), `m_send` (slot 4: vacant in `@vtable.0`, fn in `@vtable.1`),
`m_by_val` (slot 5: `viaVTableShim = true`), `m2` (slot 6). Total = 7 words!
Small IDs (`traitId := 20`, `methodId := 1..5`) keep kernel unary `natEq` reduction sub-ms. -/
noncomputable def spM1 : MethodDecl := {
  methodId := 1, hasExplicitSizedSelf := false, isFinal := false, isAsync := false, isCVariadic := false,
  ownTypeParamCount := 0, ownConstParamCount := 0, receiver := .refSelf false, extraParams := [], retTy := .prim 1, clauses := []
}
noncomputable def spMSized : MethodDecl := {
  methodId := 2, hasExplicitSizedSelf := true, isFinal := false, isAsync := false, isCVariadic := false,
  ownTypeParamCount := 0, ownConstParamCount := 0, receiver := .refSelf false, extraParams := [], retTy := .prim 1, clauses := []
}
noncomputable def spMSend : MethodDecl := {
  methodId := 3, hasExplicitSizedSelf := false, isFinal := false, isAsync := false, isCVariadic := false,
  ownTypeParamCount := 0, ownConstParamCount := 0, receiver := .refSelf false, extraParams := [], retTy := .prim 1,
  clauses := [.autoTrait 25]
}
noncomputable def spMByVal : MethodDecl := {
  methodId := 4, hasExplicitSizedSelf := false, isFinal := false, isAsync := false, isCVariadic := false,
  ownTypeParamCount := 0, ownConstParamCount := 0, receiver := .byValueSelf, extraParams := [], retTy := .prim 1, clauses := []
}
noncomputable def spM2 : MethodDecl := {
  methodId := 5, hasExplicitSizedSelf := false, isFinal := false, isAsync := false, isCVariadic := false,
  ownTypeParamCount := 0, ownConstParamCount := 0, receiver := .refSelf false, extraParams := [], retTy := .prim 1, clauses := []
}

noncomputable def slotProbeTrait : TraitDecl := {
  traitId := 20
  superTraitIds := [20]
  forceDynIncompatible := false
  traitClauses := []
  items := [.fnDecl spM1, .fnDecl spMSized, .fnDecl spMSend, .fnDecl spMByVal, .fnDecl spM2]
}

noncomputable def slotProbeImplU32 : ConcreteImpl := {
  concreteSelfId := 1
  sizeBytes := 4
  alignBytes := 4
  dropGlueSym := none
  clausesHoldForSelf := fun _ => true
  methodSym := fun mid => 20 + mid
}

noncomputable def slotProbeImplRcU32 : ConcreteImpl := {
  concreteSelfId := 2
  sizeBytes := 8
  alignBytes := 8
  dropGlueSym := some 90
  clausesHoldForSelf := fun m => boolNot (natEq m.methodId 3)
  methodSym := fun mid => 30 + mid
}

noncomputable def slotProbeDynBox : DynFatPtr := {
  erasedConcreteId := 1
  dataPtr := 64
  traitId := 20
  vtable := buildVtable slotProbeTrait slotProbeImplU32
  receiver := .boxSelf
}

theorem slotProbe_exact_vtable_layout_and_vacant_slot :
    isDynCompatible slotProbeTrait = true ∧
    listLen (buildVtable slotProbeTrait slotProbeImplRcU32) = 7 ∧
    listLen (buildVtable slotProbeTrait slotProbeImplU32) = 7 ∧
    vtableSlotIndexOfMethod slotProbeTrait 1 = some 3 ∧
    vtableSlotIndexOfMethod slotProbeTrait 2 = none ∧
    vtableSlotIndexOfMethod slotProbeTrait 3 = some 4 ∧
    vtableSlotIndexOfMethod slotProbeTrait 4 = some 5 ∧
    vtableSlotIndexOfMethod slotProbeTrait 5 = some 6 ∧
    listGet? (buildVtable slotProbeTrait slotProbeImplRcU32) 4 = some (.vacant 20 3) ∧
    listGet? (buildVtable slotProbeTrait slotProbeImplU32) 4 = some (.method 20 3 23 false [] (.prim 1)) ∧
    listGet? (buildVtable slotProbeTrait slotProbeImplU32) 5 = some (.method 20 4 24 true [] (.prim 1)) ∧
    evalDynCall slotProbeTrait slotProbeDynBox spMSized false true = .rejected .e0599SizedRequirement ∧
    evalDynCall slotProbeTrait slotProbeDynBox spMByVal false true = .rejected .e0161MoveUnsized ∧
    evalDynCall slotProbeTrait slotProbeDynBox spMByVal true true = .invoked 1 24 64 true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `AsyncFn` / `AsyncFnMut` (GAT `CallRefFuture<'a>`) vs `AsyncFnOnce`
(unparameterized associated type `CallOnceFuture` — `dyn`-compatible once unstable
features `async_fn_traits` + `unboxed_closures` expose `CallOnceFuture`) and
`WhereClone` (accepted via `Clone: Sized` elaboration) vs `WhereNonAuto` (`E0038`). -/
noncomputable def asyncFnMutTrait : TraitDecl := {
  traitId := 30
  superTraitIds := [30]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    .tyDecl { tyId := 31, hasExplicitSizedSelf := false, ownGenericCount := 1, itemBounds := [], clauses := [] },
    mkSimpleFn 32 (.refSelf true) false 0 [] [] (.selfAssoc 30 31)
  ]
}

noncomputable def asyncFnOnceTrait : TraitDecl := {
  traitId := 40
  superTraitIds := [40]
  forceDynIncompatible := false
  traitClauses := []
  items := [
    .tyDecl { tyId := 41, hasExplicitSizedSelf := false, ownGenericCount := 0, itemBounds := [], clauses := [] },
    mkSimpleFn 42 .byValueSelf false 0 [] [] (.selfAssoc 40 41)
  ]
}

noncomputable def whereCloneTrait : TraitDecl := {
  traitId := 50
  superTraitIds := [50]
  forceDynIncompatible := false
  traitClauses := []
  items := [mkSimpleFn 51 (.refSelf false) false 0 [.nonAutoSizedTrait 50] [] (.prim 1)]
}

noncomputable def whereNonAutoTrait : TraitDecl := {
  traitId := 60
  superTraitIds := [60]
  forceDynIncompatible := false
  traitClauses := []
  items := [mkSimpleFn 61 (.refSelf false) false 0 [.nonAutoUnsizedTrait 51] [] (.prim 1)]
}

theorem async_fn_and_where_self_specimens :
    isDynCompatible asyncFnMutTrait = false ∧
    isDynCompatible asyncFnOnceTrait = true ∧
    isDynCompatible whereCloneTrait = true ∧
    listLen (ownExistentialVtableEntries whereCloneTrait) = 0 ∧
    isDynCompatible whereNonAutoTrait = false ∧
    dynCompatViolationsForTrait whereNonAutoTrait = [.method 61 .whereClauseReferencesSelf] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end DynCompatSoundness
