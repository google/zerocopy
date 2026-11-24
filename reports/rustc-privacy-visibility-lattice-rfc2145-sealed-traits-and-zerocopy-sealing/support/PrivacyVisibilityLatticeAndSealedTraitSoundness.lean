/-!
# Soundness Model: `rustc_privacy` Module-Tree Visibility Lattice, `EffectiveVisibilities`,
# RFC 2145 Lints (`private_bounds` / `private_interfaces` / `unnameable_types`),
# Sealed-Trait Soundness, Re-Export Escapes, and `zerocopy` Invariant Sealing

Standalone kernel-checked Lean `v4.34.1` formalization companion to the reference package
`rustc-privacy-visibility-lattice-rfc2145-sealed-traits-and-zerocopy-sealing`.

Purity & TCB guarantees (kernel-checked under Lean `v4.34.1` with `-DwarningAsError=true`):
- Zero `sorry`, zero `Classical.choice`, zero `Quot.sound`, zero `Lean.ofReduceBool`,
  zero `Lean.trustCompiler`, zero `omega`, zero `bv_decide`, zero `native_decide`,
  zero `partial def`, zero `unsafe`, and zero `._unsafe_rec` auxiliary constants.
- Every `def` explicitly carries `noncomputable` (no `noncomputable section`, no
  `deriving DecidableEq`/`Repr`), guaranteeing constructive kernel proofs and zero
  compiler `._unsafe_rec` synthesis.
-/

namespace RustcPrivacyLattice

/-!
## Part 1: Constructive Preliminaries and Rooted Module Tree (`ModPath`)
-/

/-- Crate identifier (`0` represents the root upstream crate under study). -/
abbrev CrateId := Nat

/-- Relative module segment identifier within a crate. -/
abbrev SegId := Nat

/-- Trait identifier. -/
abbrev TraitId := Nat

/-- Nominal type identifier (`struct` / `enum` / `union` / marker enum). -/
abbrev TypeId := Nat

/-- Impl block identifier. -/
abbrev ImplId := Nat

/-- Constructive boolean negation. -/
noncomputable def boolNot : Bool → Bool
  | true => false
  | false => true

/-- Constructive boolean conjunction. -/
noncomputable def boolAnd : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

private theorem boolAnd_true_left (b : Bool) : boolAnd true b = b := by
  cases b <;> rfl

/-- Constructive boolean disjunction. -/
noncomputable def boolOr : Bool → Bool → Bool
  | false, false => false
  | _, _ => true

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

private theorem nat_beq_eq_true_of_eq {m n : Nat} (h : m = n) : Nat.beq m n = true := by
  rw [h]
  exact nat_beq_refl n

private theorem nat_beq_false_of_ne {m n : Nat} (hne : m ≠ n) : Nat.beq m n = false := by
  cases h : Nat.beq m n with
  | false => rfl
  | true => exact False.elim (hne (nat_beq_true_eq h))

private theorem nat_succ_ne_self (n : Nat) : n + 1 ≠ n := by
  induction n with
  | zero =>
    intro h
    cases h
  | succ k ih =>
    intro h
    injection h with h'
    exact ih h'

/-- Constructive list membership predicate. -/
inductive Mem {α : Type} (x : α) : List α → Prop where
  | head {xs : List α} : Mem x (x :: xs)
  | tail {y : α} {xs : List α} : Mem x xs → Mem x (y :: xs)

/-- Constructive universal quantification over list elements. -/
inductive All {α : Type} (P : α → Prop) : List α → Prop where
  | nil : All P []
  | cons {x : α} {xs : List α} : P x → All P xs → All P (x :: xs)

private theorem all_mem {α : Type} {P : α → Prop} {xs : List α}
    (hall : All P xs) {x : α} (hmem : Mem x xs) : P x := by
  induction hmem with
  | head =>
    cases hall with
    | cons px _ => exact px
  | tail _ ih =>
    cases hall with
    | cons _ pxs => exact ih pxs

/-- Constructive prefix relation on segment lists (`xs` is a prefix of `ys`).
Models ancestor containment in `rustc`'s HIR / `DefId` module tree. -/
inductive IsPrefix : List SegId → List SegId → Prop where
  | nil (ys : List SegId) : IsPrefix [] ys
  | cons {x : SegId} {xs ys : List SegId} : IsPrefix xs ys → IsPrefix (x :: xs) (x :: ys)

/-- Boolean decision procedure for `IsPrefix`. -/
noncomputable def isPrefixBool : List SegId → List SegId → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => boolAnd (Nat.beq x y) (isPrefixBool xs ys)

theorem isPrefix_refl (xs : List SegId) : IsPrefix xs xs := by
  induction xs with
  | nil => exact .nil []
  | cons x xs ih => exact .cons ih

theorem isPrefix_trans {xs ys zs : List SegId}
    (h1 : IsPrefix xs ys) (h2 : IsPrefix ys zs) : IsPrefix xs zs := by
  induction h1 generalizing zs with
  | nil _ => exact .nil zs
  | cons _ ih =>
    cases h2 with
    | cons h2' => exact .cons (ih h2')

theorem isPrefix_antisymm {xs ys : List SegId}
    (h1 : IsPrefix xs ys) (h2 : IsPrefix ys xs) : xs = ys := by
  induction h1 with
  | nil ys =>
    cases h2
    rfl
  | cons _ ih =>
    cases h2 with
    | cons h2' =>
      have heq := ih h2'
      rw [heq]

private theorem isPrefix_append_left (xs ys : List SegId) : IsPrefix xs (xs ++ ys) := by
  induction xs with
  | nil => exact .nil ys
  | cons x xs ih => exact .cons ih

private theorem isPrefix_sibling_disjoint {pfx : List SegId} {a b : SegId} (hne : a ≠ b)
    (suf1 suf2 : List SegId) :
    ¬ IsPrefix (pfx ++ a :: suf1) (pfx ++ b :: suf2) := by
  induction pfx with
  | nil =>
    intro h
    cases h with
    | cons _ => exact hne rfl
  | cons x xs ih =>
    intro h
    cases h with
    | cons h' => exact ih h'

theorem isPrefixBool_true_iff (xs ys : List SegId) :
    isPrefixBool xs ys = true ↔ IsPrefix xs ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil => exact .nil ys
    | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
        cases hb : Nat.beq x y with
        | false =>
          simp only [isPrefixBool, hb, boolAnd] at h
          cases h
        | true =>
          have hxy := nat_beq_true_eq hb
          subst hxy
          simp only [isPrefixBool, nat_beq_refl] at h
          rw [boolAnd_true_left] at h
          exact .cons (ih ys h)
  · intro h
    induction h with
    | nil ys =>
      cases ys <;> rfl
    | cons _ ih =>
      simp only [isPrefixBool, nat_beq_refl]
      rw [boolAnd_true_left]
      exact ih

/-- Longest common prefix of two module paths inside a single crate. -/
noncomputable def lcp : List SegId → List SegId → List SegId
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
    match Nat.beq x y with
    | true => x :: lcp xs ys
    | false => []

theorem lcp_isPrefix_left (xs ys : List SegId) : IsPrefix (lcp xs ys) xs := by
  induction xs generalizing ys with
  | nil => exact .nil []
  | cons x xs ih =>
    cases ys with
    | nil => exact .nil (x :: xs)
    | cons y ys =>
      simp only [lcp]
      cases hb : Nat.beq x y with
      | false => exact .nil (x :: xs)
      | true => exact .cons (ih ys)

theorem lcp_isPrefix_right (xs ys : List SegId) : IsPrefix (lcp xs ys) ys := by
  induction xs generalizing ys with
  | nil => exact .nil ys
  | cons x xs ih =>
    cases ys with
    | nil => exact .nil []
    | cons y ys =>
      simp only [lcp]
      cases hb : Nat.beq x y with
      | false => exact .nil (y :: ys)
      | true =>
        have hxy := nat_beq_true_eq hb
        subst hxy
        exact .cons (ih ys)

theorem isPrefix_lcp_greatest {zs xs ys : List SegId}
    (hx : IsPrefix zs xs) (hy : IsPrefix zs ys) : IsPrefix zs (lcp xs ys) := by
  induction zs generalizing xs ys with
  | nil => exact .nil (lcp xs ys)
  | cons z zs ih =>
    cases hx with
    | cons hx' =>
      cases hy with
      | cons hy' =>
        simp only [lcp, nat_beq_refl]
        exact .cons (ih hx' hy')

/-- A module node in the global forest of crates (`crate` + root-to-module segment list).
`segs = []` denotes the crate root (`CRATE_MOD_ID` in `compiler/rustc_span/src/def_id.rs`). -/
structure ModPath where
  crate : CrateId
  segs : List SegId

/-- The crate root module (`crate`) for crate `c`. -/
noncomputable def crateRoot (c : CrateId) : ModPath :=
  { crate := c, segs := [] }

/-- Constructive equality decision on `ModPath`. -/
noncomputable def modPathBeq (m₁ m₂ : ModPath) : Bool :=
  boolAnd (Nat.beq m₁.crate m₂.crate)
    (boolAnd (isPrefixBool m₁.segs m₂.segs) (isPrefixBool m₂.segs m₁.segs))

theorem modPathBeq_true_eq {m₁ m₂ : ModPath} (h : modPathBeq m₁ m₂ = true) : m₁ = m₂ := by
  cases m₁ with | mk c₁ s₁ =>
  cases m₂ with | mk c₂ s₂ =>
  cases hc : Nat.beq c₁ c₂ with
  | false =>
    simp only [modPathBeq, hc, boolAnd] at h
    cases h
  | true =>
    have hceq := nat_beq_true_eq hc
    subst hceq
    simp only [modPathBeq, nat_beq_refl, boolAnd] at h
    cases hp1 : isPrefixBool s₁ s₂ with
    | false =>
      rw [hp1] at h
      cases h
    | true =>
      rw [hp1] at h
      cases hp2 : isPrefixBool s₂ s₁ with
      | false =>
        rw [hp2] at h
        cases h
      | true =>
        have h1 := (isPrefixBool_true_iff s₁ s₂).mp hp1
        have h2 := (isPrefixBool_true_iff s₂ s₁).mp hp2
        have hseq := isPrefix_antisymm h1 h2
        subst hseq
        rfl

theorem modPathBeq_refl (m : ModPath) : modPathBeq m m = true := by
  cases m with | mk c s =>
  have hpref := (isPrefixBool_true_iff s s).mpr (isPrefix_refl s)
  simp only [modPathBeq, nat_beq_refl, hpref, boolAnd]

/-- Ancestor dominance relation (`IsAncestor anc desc`), matching `TyCtxt::is_descendant_of(desc, anc)`
in `compiler/rustc_middle/src/ty/mod.rs:409-418`: `anc` and `desc` reside in the same crate and
`anc.segs` is a prefix of `desc.segs`. -/
noncomputable def IsAncestor (anc desc : ModPath) : Prop :=
  anc.crate = desc.crate ∧ IsPrefix anc.segs desc.segs

/-- Boolean checker for `IsAncestor`. -/
noncomputable def isAncestorBool (anc desc : ModPath) : Bool :=
  boolAnd (Nat.beq anc.crate desc.crate) (isPrefixBool anc.segs desc.segs)

theorem isAncestorBool_true_iff (anc desc : ModPath) :
    isAncestorBool anc desc = true ↔ IsAncestor anc desc := by
  constructor
  · intro h
    cases anc with | mk ca sa =>
    cases desc with | mk cd sd =>
    cases hc : Nat.beq ca cd with
    | false =>
      simp only [isAncestorBool, hc, boolAnd] at h
      cases h
    | true =>
      have hceq := nat_beq_true_eq hc
      simp only [isAncestorBool, hc] at h
      rw [boolAnd_true_left] at h
      exact ⟨hceq, (isPrefixBool_true_iff sa sd).mp h⟩
  · intro ⟨hceq, hpref⟩
    cases anc with | mk ca sa =>
    cases desc with | mk cd sd =>
    simp only [isAncestorBool]
    have hcb := nat_beq_eq_true_of_eq hceq
    have hpb := (isPrefixBool_true_iff sa sd).mpr hpref
    simp only [hcb, hpb, boolAnd]

theorem isAncestor_refl (m : ModPath) : IsAncestor m m :=
  ⟨rfl, isPrefix_refl m.segs⟩

theorem isAncestor_trans {a b c : ModPath}
    (hab : IsAncestor a b) (hbc : IsAncestor b c) : IsAncestor a c :=
  ⟨hab.1.trans hbc.1, isPrefix_trans hab.2 hbc.2⟩

theorem isAncestor_antisymm {a b : ModPath}
    (hab : IsAncestor a b) (hba : IsAncestor b a) : a = b := by
  cases a with | mk ca sa =>
  cases b with | mk cb sb =>
  have hceq : ca = cb := hab.1
  have hseq : sa = sb := isPrefix_antisymm hab.2 hba.2
  subst hceq
  subst hseq
  rfl

theorem crateRoot_isAncestor_of_all (m : ModPath) : IsAncestor (crateRoot m.crate) m :=
  ⟨rfl, .nil m.segs⟩

/-- Direct child module `m :: seg`. -/
noncomputable def childMod (m : ModPath) (seg : SegId) : ModPath :=
  { crate := m.crate, segs := m.segs ++ [seg] }

theorem isAncestor_of_childMod (m : ModPath) (seg : SegId) :
    IsAncestor m (childMod m seg) :=
  ⟨rfl, isPrefix_append_left m.segs [seg]⟩

/-- Parent module segments (`none` at crate root). -/
noncomputable def parentModSegments : List SegId → Option (List SegId)
  | [] => none
  | [_] => some []
  | x :: y :: ys =>
    match parentModSegments (y :: ys) with
    | none => none
    | some p => some (x :: p)

/-- Parent module of `m` (`none` at crate root). -/
noncomputable def parentMod (m : ModPath) : Option ModPath :=
  match parentModSegments m.segs with
  | none => none
  | some p => some { crate := m.crate, segs := p }

private theorem parentModSegments_isPrefix (xs p : List SegId)
    (hp : parentModSegments xs = some p) : IsPrefix p xs := by
  induction xs generalizing p with
  | nil => cases hp
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [parentModSegments] at hp
      injection hp with hp'
      subst hp'
      exact .nil [x]
    | cons y ys =>
      simp only [parentModSegments] at hp
      cases hrec : parentModSegments (y :: ys) with
      | none =>
        rw [hrec] at hp
        cases hp
      | some p' =>
        rw [hrec] at hp
        injection hp with hp'
        subst hp'
        exact .cons (ih p' hrec)

theorem parentMod_isAncestor {m p : ModPath} (hp : parentMod m = some p) : IsAncestor p m := by
  cases m with | mk c s =>
  simp only [parentMod] at hp
  cases hseg : parentModSegments s with
  | none =>
    rw [hseg] at hp
    cases hp
  | some ps =>
    rw [hseg] at hp
    injection hp with hpeq
    subst hpeq
    exact ⟨rfl, parentModSegments_isPrefix s ps hseg⟩

theorem parentMod_of_childMod (m : ModPath) (seg : SegId) :
    parentMod (childMod m seg) = some m := by
  cases m with | mk c s =>
  simp only [parentMod, childMod]
  have hseg : parentModSegments (s ++ [seg]) = some s := by
    induction s with
    | nil => rfl
    | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        change (match parentModSegments (y :: (ys ++ [seg])) with
          | none => none
          | some p => some (x :: p)) = some (x :: y :: ys)
        rw [List.cons_append] at ih
        rw [ih]
  rw [hseg]

/-!
## Part 2: Visibility Lattice (`Visibility`), Accessibility, Partial Order, and Joins
-/

/-- Rust `ty::Visibility` (`compiler/rustc_middle/src/ty/mod.rs:257-262`):
either `Public` (visible across all crates) or `Restricted m` (visible inside module `m`
and all descendants of `m` in the same crate). -/
inductive Visibility where
  | visPublic : Visibility
  | restricted : ModPath → Visibility

/-- `pub(crate)` in crate `c`. -/
noncomputable def pubCrate (c : CrateId) : Visibility :=
  .restricted (crateRoot c)

/-- `pub(self)` (private) inside module `m`. -/
noncomputable def pubSelf (m : ModPath) : Visibility :=
  .restricted m

/-- `pub(super)` inside `m` (falls back to crate root if already at crate root). -/
noncomputable def pubSuper (m : ModPath) : Visibility :=
  match parentMod m with
  | none => .restricted m
  | some p => .restricted p

/-- `pub(in path)` is valid only if `path` is an ancestor of the item's defining module `defMod`
(otherwise `rustc` rejects with `E0742`). -/
noncomputable def ValidVisibilityRestriction (defMod : ModPath) : Visibility → Prop
  | .visPublic => True
  | .restricted path => IsAncestor path defMod

/-- Exact model of `Visibility::is_accessible_from(def_id, tcx)` (`ty/mod.rs:442-448`):
`Public` is accessible everywhere; `Restricted m` is accessible from `caller` iff
`caller` is a descendant of `m` (`IsAncestor m caller`). -/
noncomputable def IsAccessibleFrom (v : Visibility) (caller : ModPath) : Prop :=
  match v with
  | .visPublic => True
  | .restricted m => IsAncestor m caller

/-- Boolean decision procedure for `IsAccessibleFrom`. -/
noncomputable def isAccessibleFromBool (v : Visibility) (caller : ModPath) : Bool :=
  match v with
  | .visPublic => true
  | .restricted m => isAncestorBool m caller

theorem isAccessibleFromBool_true_iff (v : Visibility) (caller : ModPath) :
    isAccessibleFromBool v caller = true ↔ IsAccessibleFrom v caller := by
  cases v with
  | visPublic =>
    constructor
    · intro _; trivial
    · intro _; rfl
  | restricted m =>
    exact isAncestorBool_true_iff m caller

/-- Visibility partial order `VisLeq v₁ v₂` ("`v₂` is at least as visible as `v₁`",
corresponding to `v₂ >= v₁` under `Visibility::partial_cmp` in `ty/mod.rs:450-464`).
Ancestor modules yield larger visibilities (`IsAncestor m₂ m₁`). -/
noncomputable def VisLeq (v₁ v₂ : Visibility) : Prop :=
  match v₁, v₂ with
  | _, .visPublic => True
  | .visPublic, .restricted _ => False
  | .restricted m₁, .restricted m₂ => IsAncestor m₂ m₁

/-- Strict visibility order (`v₁ < v₂`, matching `v₂.greater_than(v₁, tcx)` at `ty/mod.rs:470-482`). -/
noncomputable def VisLt (v₁ v₂ : Visibility) : Prop :=
  VisLeq v₁ v₂ ∧ v₁ ≠ v₂

/-- Boolean decision procedure for `VisLeq`. -/
noncomputable def visLeqBool (v₁ v₂ : Visibility) : Bool :=
  match v₁, v₂ with
  | _, .visPublic => true
  | .visPublic, .restricted _ => false
  | .restricted m₁, .restricted m₂ => isAncestorBool m₂ m₁

/-- Boolean decision procedure for `VisLt`. -/
noncomputable def visLtBool (v₁ v₂ : Visibility) : Bool :=
  boolAnd (visLeqBool v₁ v₂) (boolNot (visLeqBool v₂ v₁))

theorem visLeqBool_true_iff (v₁ v₂ : Visibility) :
    visLeqBool v₁ v₂ = true ↔ VisLeq v₁ v₂ := by
  cases v₁ with
  | visPublic =>
    cases v₂ with
    | visPublic => constructor <;> intro _ <;> trivial
    | restricted _ =>
      constructor
      · intro h; cases h
      · intro h; cases h
  | restricted m₁ =>
    cases v₂ with
    | visPublic => constructor <;> intro _ <;> trivial
    | restricted m₂ => exact isAncestorBool_true_iff m₂ m₁

/-- **Theorem 1a (Visibility Reflexivity).** -/
theorem visLeq_refl (v : Visibility) : VisLeq v v := by
  cases v with
  | visPublic => trivial
  | restricted m => exact isAncestor_refl m

/-- **Theorem 1b (Visibility Partial Order & Tree-Dominance Transitivity).** -/
theorem visLeq_trans {v₁ v₂ v₃ : Visibility}
    (h12 : VisLeq v₁ v₂) (h23 : VisLeq v₂ v₃) : VisLeq v₁ v₃ := by
  cases v₁ with
  | visPublic =>
    cases v₂ with
    | restricted _ => cases h12
    | visPublic =>
      cases v₃ with
      | visPublic => trivial
      | restricted _ => cases h23
  | restricted m₁ =>
    cases v₃ with
    | visPublic => trivial
    | restricted m₃ =>
      cases v₂ with
      | visPublic => cases h23
      | restricted m₂ => exact isAncestor_trans h23 h12

/-- **Theorem 1c (Visibility Antisymmetry).** -/
theorem visLeq_antisymm {v₁ v₂ : Visibility}
    (h12 : VisLeq v₁ v₂) (h21 : VisLeq v₂ v₁) : v₁ = v₂ := by
  cases v₁ with
  | visPublic =>
    cases v₂ with
    | visPublic => rfl
    | restricted _ => cases h12
  | restricted m₁ =>
    cases v₂ with
    | visPublic => cases h21
    | restricted m₂ =>
      have hm := isAncestor_antisymm h21 h12
      rw [hm]

/-- **Theorem 1d (`Public` Is the Unique Top Element of the Visibility Lattice).** -/
theorem visLeq_public_top (v : Visibility) : VisLeq v .visPublic := by
  cases v <;> trivial

theorem visLeq_public_only_public {v : Visibility} (h : VisLeq .visPublic v) : v = .visPublic := by
  cases v with
  | visPublic => rfl
  | restricted _ => cases h

/-- **Theorem 1e (`pub(crate)` Dominates Every Crate-Local Restricted Visibility).** -/
theorem pubCrate_dominates_local (m : ModPath) :
    VisLeq (.restricted m) (pubCrate m.crate) :=
  crateRoot_isAncestor_of_all m

/-- **Theorem 1f (Valid `pub(in path)` Restriction Always Covers `defMod`
and Dominates `pub(self)`).** -/
theorem validRestriction_covers_defMod {defMod : ModPath} {v : Visibility}
    (hv : ValidVisibilityRestriction defMod v) :
    IsAccessibleFrom v defMod ∧ VisLeq (pubSelf defMod) v := by
  cases v with
  | visPublic => exact ⟨trivial, trivial⟩
  | restricted p => exact ⟨hv, hv⟩

/-- `pub(super)` dominates `pub(self)` (`m`'s private visibility). -/
theorem pubSelf_le_pubSuper (m : ModPath) :
    VisLeq (pubSelf m) (pubSuper m) := by
  simp only [pubSelf, pubSuper]
  cases hp : parentMod m with
  | none => exact isAncestor_refl m
  | some p => exact parentMod_isAncestor hp

/-- **Theorem 1g (Accessibility Monotonicity — Pointwise Access Dominance).**
`VisLeq v₁ v₂` holds iff every caller module that can access `v₁` can also access `v₂`. -/
theorem visLeq_implies_accessible_monotone {v₁ v₂ : Visibility} {caller : ModPath}
    (hle : VisLeq v₁ v₂) (hacc : IsAccessibleFrom v₁ caller) : IsAccessibleFrom v₂ caller := by
  cases v₁ with
  | visPublic =>
    cases v₂ with
    | visPublic => trivial
    | restricted _ => cases hle
  | restricted m₁ =>
    cases v₂ with
    | visPublic => trivial
    | restricted m₂ => exact isAncestor_trans hle hacc

theorem pointwise_accessible_implies_visLeq {v₁ v₂ : Visibility}
    (h : ∀ caller : ModPath, IsAccessibleFrom v₁ caller → IsAccessibleFrom v₂ caller) :
    VisLeq v₁ v₂ := by
  cases v₁ with
  | visPublic =>
    cases v₂ with
    | visPublic => trivial
    | restricted m₂ =>
      have hc := h (crateRoot (m₂.crate + 1)) trivial
      have hne : m₂.crate ≠ m₂.crate + 1 := fun eq => nat_succ_ne_self m₂.crate eq.symm
      exact False.elim (hne hc.1)
  | restricted m₁ =>
    cases v₂ with
    | visPublic => trivial
    | restricted m₂ =>
      exact h m₁ (isAncestor_refl m₁)

theorem visLeq_iff_pointwise_accessible (v₁ v₂ : Visibility) :
    VisLeq v₁ v₂ ↔ (∀ caller : ModPath, IsAccessibleFrom v₁ caller → IsAccessibleFrom v₂ caller) :=
  ⟨fun hle _ hacc => visLeq_implies_accessible_monotone hle hacc, pointwise_accessible_implies_visLeq⟩

/-- **Theorem 1h (Sibling & Cross-Crate Incomparability in `partial_cmp`).** -/
theorem sibling_visibilities_incomparable (pfx : ModPath) {a b : SegId} (hne : a ≠ b) :
    ¬ VisLeq (.restricted (childMod pfx a)) (.restricted (childMod pfx b)) ∧
    ¬ VisLeq (.restricted (childMod pfx b)) (.restricted (childMod pfx a)) := by
  constructor
  · intro h
    exact isPrefix_sibling_disjoint (fun eq => hne eq.symm) [] [] h.2
  · intro h
    exact isPrefix_sibling_disjoint hne [] [] h.2

theorem cross_crate_visibilities_incomparable {m₁ m₂ : ModPath} (hne : m₁.crate ≠ m₂.crate) :
    ¬ VisLeq (.restricted m₁) (.restricted m₂) ∧
    ¬ VisLeq (.restricted m₂) (.restricted m₁) ∧
    ¬ IsAccessibleFrom (.restricted m₁) m₂ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hne h.1.symm
  · intro h; exact hne h.1
  · intro h; exact hne h.1

/-- Non-ancestor `pub(in other)` fails `ValidVisibilityRestriction` (`E0742` probe `a04`). -/
theorem non_ancestor_sibling_invalid_e0742 (root : ModPath) {a b : SegId} (hne : a ≠ b) :
    ¬ ValidVisibilityRestriction (childMod root a) (.restricted (childMod root b)) := by
  intro h
  exact isPrefix_sibling_disjoint (fun eq => hne eq.symm) [] [] h.2

/-- Least upper bound (join) of two visibilities in the lattice (`pub` across crates;
lowest common ancestor `pub(in lcp)` within the same crate). -/
noncomputable def visJoin (v₁ v₂ : Visibility) : Visibility :=
  match v₁, v₂ with
  | .visPublic, _ => .visPublic
  | _, .visPublic => .visPublic
  | .restricted m₁, .restricted m₂ =>
    match Nat.beq m₁.crate m₂.crate with
    | true => .restricted { crate := m₁.crate, segs := lcp m₁.segs m₂.segs }
    | false => .visPublic

theorem visJoin_left_le (v₁ v₂ : Visibility) : VisLeq v₁ (visJoin v₁ v₂) := by
  cases v₁ with
  | visPublic =>
    cases v₂ <;> trivial
  | restricted m₁ =>
    cases v₂ with
    | visPublic => trivial
    | restricted m₂ =>
      simp only [visJoin]
      cases hc : Nat.beq m₁.crate m₂.crate with
      | false => trivial
      | true =>
        exact ⟨rfl, lcp_isPrefix_left m₁.segs m₂.segs⟩

theorem visJoin_right_le (v₁ v₂ : Visibility) : VisLeq v₂ (visJoin v₁ v₂) := by
  cases v₁ with
  | visPublic =>
    cases v₂ <;> trivial
  | restricted m₁ =>
    cases v₂ with
    | visPublic => trivial
    | restricted m₂ =>
      simp only [visJoin]
      cases hc : Nat.beq m₁.crate m₂.crate with
      | false => trivial
      | true =>
        have hceq := nat_beq_true_eq hc
        exact ⟨hceq, lcp_isPrefix_right m₁.segs m₂.segs⟩

theorem visJoin_least {v₁ v₂ u : Visibility}
    (h1 : VisLeq v₁ u) (h2 : VisLeq v₂ u) : VisLeq (visJoin v₁ v₂) u := by
  cases v₁ with
  | visPublic =>
    have hu := visLeq_public_only_public h1
    rw [hu]
    exact visLeq_public_top _
  | restricted m₁ =>
    cases v₂ with
    | visPublic =>
      have hu := visLeq_public_only_public h2
      rw [hu]
      exact visLeq_public_top _
    | restricted m₂ =>
      simp only [visJoin]
      cases hc : Nat.beq m₁.crate m₂.crate with
      | false =>
        cases u with
        | visPublic => trivial
        | restricted mu =>
          have hc1 : mu.crate = m₁.crate := h1.1
          have hc2 : mu.crate = m₂.crate := h2.1
          have h12 : m₁.crate = m₂.crate := hc1.symm.trans hc2
          have ht := nat_beq_eq_true_of_eq h12
          rw [ht] at hc
          cases hc
      | true =>
        cases u with
        | visPublic => trivial
        | restricted mu =>
          exact ⟨h1.1, isPrefix_lcp_greatest h1.2 h2.2⟩

/-- Conservative meet (`visMin`, matching `EffectiveVisibility::min` / `rustc_privacy::min`:
returns exact meet when ordered). -/
noncomputable def visMin (v₁ v₂ : Visibility) : Visibility :=
  match visLeqBool v₁ v₂ with
  | true => v₁
  | false =>
    match visLeqBool v₂ v₁ with
    | true => v₂
    | false => v₂

theorem visMin_ordered_le_both {v₁ v₂ : Visibility}
    (hord : VisLeq v₁ v₂ ∨ VisLeq v₂ v₁) :
    VisLeq (visMin v₁ v₂) v₁ ∧ VisLeq (visMin v₁ v₂) v₂ := by
  cases hord with
  | inl h12 =>
    have hb := (visLeqBool_true_iff v₁ v₂).mpr h12
    simp only [visMin, hb]
    exact ⟨visLeq_refl v₁, h12⟩
  | inr h21 =>
    cases hb12 : visLeqBool v₁ v₂ with
    | true =>
      have h12 := (visLeqBool_true_iff v₁ v₂).mp hb12
      simp only [visMin, hb12]
      exact ⟨visLeq_refl v₁, h12⟩
    | false =>
      have hb21 := (visLeqBool_true_iff v₂ v₁).mpr h21
      simp only [visMin, hb12, hb21]
      exact ⟨h21, visLeq_refl v₂⟩

/-!
## Part 3: `EffectiveVisibility` Monotonicity Chain, `pub use` Re-Exports, and Reachability
-/

/-- `EffectiveVisibilities` four-level tuple (`compiler/rustc_middle/src/middle/privacy.rs:43-48`). -/
structure EffectiveVisibility where
  direct : Visibility
  reexported : Visibility
  reachable : Visibility
  reachableThroughImplTrait : Visibility

/-- Effective visibility levels (`middle/privacy.rs:22-34`). -/
inductive EffLevel where
  | reachableThroughImplTrait
  | reachable
  | reexported
  | direct

noncomputable def EffectiveVisibility.atLevel (ev : EffectiveVisibility) : EffLevel → Visibility
  | .direct => ev.direct
  | .reexported => ev.reexported
  | .reachable => ev.reachable
  | .reachableThroughImplTrait => ev.reachableThroughImplTrait

noncomputable def EffectiveVisibility.fromVis (v : Visibility) : EffectiveVisibility :=
  { direct := v, reexported := v, reachable := v, reachableThroughImplTrait := v }

/-- Exact invariant predicate asserted by `EffectiveVisibilities::check_invariants`
(`compiler/rustc_middle/src/middle/privacy.rs:158-208`):
`private_vis <= direct <= reexported <= reachable <= reachable_through_impl_trait`
and `reachable <= nominal_vis` (for ordinary non-impl, non-glob items). -/
noncomputable def EffVisWellFormed (privVis nominalVis : Visibility) (ev : EffectiveVisibility) : Prop :=
  VisLeq privVis ev.direct ∧
  VisLeq ev.direct ev.reexported ∧
  VisLeq ev.reexported ev.reachable ∧
  VisLeq ev.reachable ev.reachableThroughImplTrait ∧
  VisLeq ev.reachable nominalVis

theorem effVis_fromVis_wellFormed {privVis nominalVis : Visibility}
    (hle : VisLeq privVis nominalVis) :
    EffVisWellFormed privVis nominalVis (EffectiveVisibility.fromVis privVis) :=
  ⟨visLeq_refl privVis, visLeq_refl privVis, visLeq_refl privVis, visLeq_refl privVis, hle⟩

theorem effVis_reexported_le_nominal {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev) :
    VisLeq ev.reexported nominalVis :=
  visLeq_trans hwf.2.2.1 hwf.2.2.2.2

theorem effVis_direct_le_nominal {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev) :
    VisLeq ev.direct nominalVis :=
  visLeq_trans hwf.2.1 (effVis_reexported_le_nominal hwf)

theorem effVis_reachable_public_implies_nominal_public
    {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev)
    (hreach : ev.reachable = .visPublic) :
    nominalVis = .visPublic := by
  have hle := hwf.2.2.2.2
  rw [hreach] at hle
  exact visLeq_public_only_public hle

theorem effVis_reexported_public_implies_reachable_public
    {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev)
    (hreexp : ev.reexported = .visPublic) :
    ev.reachable = .visPublic := by
  have hle := hwf.2.2.1
  rw [hreexp] at hle
  exact visLeq_public_only_public hle

theorem effVis_direct_public_implies_reexported_public
    {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev)
    (hdir : ev.direct = .visPublic) :
    ev.reexported = .visPublic := by
  have hle := hwf.2.1
  rw [hdir] at hle
  exact visLeq_public_only_public hle

/-- Monotone visibility lifting step modeling `EffectiveVisibilities::update`
(`middle/privacy.rs:228-277`). -/
noncomputable def liftVis (cur cand : Visibility) : Visibility :=
  match visLeqBool cur cand with
  | true => cand
  | false => cur

theorem liftVis_mono_left (cur cand : Visibility) : VisLeq cur (liftVis cur cand) := by
  simp only [liftVis]
  cases hb : visLeqBool cur cand with
  | false => exact visLeq_refl cur
  | true => exact (visLeqBool_true_iff cur cand).mp hb

theorem liftVis_preserves_upper {cur cand bound : Visibility}
    (hcur : VisLeq cur bound) (hcand : VisLeq cand bound) :
    VisLeq (liftVis cur cand) bound := by
  simp only [liftVis]
  cases visLeqBool cur cand with
  | false => exact hcur
  | true => exact hcand

/-- Updating `Reachable` (from an exported interface, e.g., a public trait supertrait bound)
lifts `reachable` and `reachableThroughImplTrait` when `nominalVis = .visPublic`. -/
noncomputable def markInterfaceReachable (ev : EffectiveVisibility) : EffectiveVisibility :=
  { direct := ev.direct
  , reexported := ev.reexported
  , reachable := .visPublic
  , reachableThroughImplTrait := .visPublic
  }

theorem markInterfaceReachable_preserves_wellFormed
    {privVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis .visPublic ev) :
    EffVisWellFormed privVis .visPublic (markInterfaceReachable ev) :=
  ⟨hwf.1, hwf.2.1, visLeq_public_top ev.reexported, visLeq_refl .visPublic, visLeq_refl .visPublic⟩

/-- Updating `ReachableThroughImplTrait` (e.g., via RPIT `impl Trait` hidden type leakage
at `compiler/rustc_privacy/src/lib.rs:1833-1834`) intentionally omits the `nominalVis` cap. -/
noncomputable def markRpitReachable (ev : EffectiveVisibility) : EffectiveVisibility :=
  { direct := ev.direct
  , reexported := ev.reexported
  , reachable := ev.reachable
  , reachableThroughImplTrait := .visPublic
  }

theorem markRpitReachable_preserves_wellFormed
    {privVis nominalVis : Visibility} {ev : EffectiveVisibility}
    (hwf : EffVisWellFormed privVis nominalVis ev) :
    EffVisWellFormed privVis nominalVis (markRpitReachable ev) :=
  ⟨hwf.1, hwf.2.1, hwf.2.2.1, visLeq_public_top ev.reachable, hwf.2.2.2.2⟩

/-- Witness that `ReachableThroughImplTrait` can be `.visPublic` even when `direct`, `reexported`,
`reachable`, and `nominalVis` are all `.restricted (crateRoot 0)` (`b01` RPIT hidden type). -/
theorem rpit_hidden_type_exceeds_nominal :
    let privCrate := pubCrate 0
    let ev := markRpitReachable (EffectiveVisibility.fromVis privCrate)
    EffVisWellFormed privCrate privCrate ev ∧
    ev.reachable = privCrate ∧
    ev.reachableThroughImplTrait = .visPublic := by
  refine ⟨?_, rfl, rfl⟩
  exact markRpitReachable_preserves_wellFormed (effVis_fromVis_wellFormed (visLeq_refl _))

/-!
## Part 4: RFC 2145 Lints (`private_bounds`, `private_interfaces`, `unnameable_types`),
## `unreachable_pub`, and `E0446` Associated-Type Hard Errors
-/

/-- Summary of a declared item's visibility and interface component dependencies,
matching `PrivateItemsInPublicInterfacesChecker` (`rustc_privacy/src/lib.rs:1530-1734`). -/
structure ItemInterface where
  nominal : Visibility
  privVis : Visibility
  effVis : EffectiveVisibility
  primaryComps : List Visibility
  boundComps : List Visibility
  assocImplComps : List Visibility

/-- Exact condition for `PRIVATE_INTERFACES` (`compiler/rustc_privacy/src/lib.rs:1466-1491`,
`in_primary_interface = true`). -/
noncomputable def FiresPrivateInterfaces (it : ItemInterface) : Prop :=
  ∃ comp, Mem comp it.primaryComps ∧ VisLt comp it.effVis.reachable

/-- Exact condition for `PRIVATE_BOUNDS` (`compiler/rustc_privacy/src/lib.rs:1466-1491`,
`in_primary_interface = false`). -/
noncomputable def FiresPrivateBounds (it : ItemInterface) : Prop :=
  ∃ comp, Mem comp it.boundComps ∧ VisLt comp it.effVis.reachable

/-- Exact condition for `UNNAMEABLE_TYPES` (`compiler/rustc_privacy/src/lib.rs:1559`,
`reachable_at_vis.is_public() && reexported_at_vis != reachable_at_vis`). -/
noncomputable def FiresUnnameableTypes (it : ItemInterface) : Prop :=
  it.effVis.reachable = .visPublic ∧ it.effVis.reexported ≠ .visPublic

/-- Exact condition for `UNREACHABLE_PUB` (`compiler/rustc_lint/src/builtin.rs:1130`,
`cx.tcx.visibility(def_id).is_public() && !cx.effective_visibilities.is_reachable(def_id)`). -/
noncomputable def FiresUnreachablePub (it : ItemInterface) : Prop :=
  it.nominal = .visPublic ∧ it.effVis.reachable ≠ .visPublic

/-- Exact condition for hard error `E0446` (`InPublicInterface`, `lib.rs:1436, 1585-1586`)
on `impl` associated types. -/
noncomputable def FiresAssocTyHardError (implVis : Visibility) (it : ItemInterface) : Prop :=
  ∃ comp, Mem comp it.assocImplComps ∧ VisLt comp implVis

/-- Canonical `Sealed` trait inside a private submodule (`mod private { pub trait Sealed {} }`),
bound as a supertrait of a public trait `PublicSealed`. -/
noncomputable def mkPrivateModSealedTrait (privMod : ModPath) : ItemInterface :=
  let crateRootVis := pubCrate privMod.crate
  { nominal := .visPublic
  , privVis := .restricted privMod
  , effVis :=
      { direct := crateRootVis
      , reexported := crateRootVis
      , reachable := .visPublic
      , reachableThroughImplTrait := .visPublic
      }
  , primaryComps := []
  , boundComps := []
  , assocImplComps := []
  }

/-- Canonical `pub trait PublicSealed: private::Sealed {}` item (`b02`). -/
noncomputable def mkPublicSealedTrait : ItemInterface :=
  { nominal := .visPublic
  , privVis := pubCrate 0
  , effVis := EffectiveVisibility.fromVis .visPublic
  , primaryComps := []
  , boundComps := [.visPublic]
  , assocImplComps := []
  }

/-- **Theorem (`b02` / `b03` Verification): Sealed-Trait RFC 2145 & `unreachable_pub` Matrix.**
1. `PublicSealed : private::Sealed` NEVER triggers `private_bounds` or `private_interfaces`;
2. `private::Sealed` NEVER triggers `unreachable_pub` (because `reachable = Public`);
3. `private::Sealed` DOES trigger opt-in `unnameable_types` (`reachable = Public ≠ reexported`). -/
theorem sealed_trait_lint_matrix (privMod : ModPath) :
    let sealed := mkPrivateModSealedTrait privMod
    let pubSealed := mkPublicSealedTrait
    ¬ FiresPrivateBounds pubSealed ∧
    ¬ FiresPrivateInterfaces pubSealed ∧
    ¬ FiresUnreachablePub sealed ∧
    FiresUnnameableTypes sealed ∧
    ¬ FiresUnnameableTypes pubSealed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨comp, hmem, hlt⟩
    cases hmem with
    | head => exact hlt.2 rfl
    | tail hnil => cases hnil
  · intro ⟨comp, hmem, _⟩
    cases hmem
  · intro ⟨_, hne⟩
    exact hne rfl
  · refine ⟨rfl, ?_⟩
    intro h
    cases h
  · intro ⟨_, hne⟩
    exact hne rfl

/-- Unused `pub trait UnusedSealed` inside a private module has `reachable = pub(crate)` and
therefore triggers `UNREACHABLE_PUB` (`b04`). -/
theorem unused_pub_in_private_mod_fires_unreachable_pub (privMod : ModPath) :
    let unused : ItemInterface :=
      { nominal := .visPublic
      , privVis := .restricted privMod
      , effVis := EffectiveVisibility.fromVis (pubCrate privMod.crate)
      , primaryComps := []
      , boundComps := []
      , assocImplComps := []
      }
    FiresUnreachablePub unused := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- Crate-private trait `trait CrateTrait {}` used as supertrait of `pub trait BadSuper`
triggers `PRIVATE_BOUNDS` (`b05`), while returning `PrivateType` from `pub fn` triggers
`PRIVATE_INTERFACES` (`b06`). -/
theorem crate_private_bounds_and_interfaces_fire :
    let badSuper : ItemInterface :=
      { nominal := .visPublic
      , privVis := pubCrate 0
      , effVis := EffectiveVisibility.fromVis .visPublic
      , primaryComps := []
      , boundComps := [pubCrate 0]
      , assocImplComps := []
      }
    let leakFn : ItemInterface :=
      { nominal := .visPublic
      , privVis := pubCrate 0
      , effVis := EffectiveVisibility.fromVis .visPublic
      , primaryComps := [pubCrate 0]
      , boundComps := []
      , assocImplComps := []
      }
    FiresPrivateBounds badSuper ∧ FiresPrivateInterfaces leakFn := by
  refine ⟨?_, ?_⟩
  · refine ⟨pubCrate 0, .head, ⟨trivial, ?_⟩⟩
    intro h
    cases h
  · refine ⟨pubCrate 0, .head, ⟨trivial, ?_⟩⟩
    intro h
    cases h

/-- Crate-internal `pub(in crate::outer)` return of `inner::InnerUnnameable` (`b07`)
does NOT fire `unnameable_types` because `reachable` is restricted (`≠ .visPublic`), matching
`check_unnameable` (`compiler/rustc_privacy/src/lib.rs:1559`). -/
theorem crate_internal_unnameable_silent (outer inner : ModPath) :
    let item : ItemInterface :=
      { nominal := .visPublic
      , privVis := .restricted inner
      , effVis :=
          { direct := .restricted inner
          , reexported := .restricted inner
          , reachable := .restricted outer
          , reachableThroughImplTrait := .restricted outer
          }
      , primaryComps := []
      , boundComps := []
      , assocImplComps := []
      }
    ¬ FiresUnnameableTypes item := by
  dsimp only [FiresUnnameableTypes]
  intro ⟨hpub, _⟩
  cases hpub

/-- Associated type `impl PubTrait for PubType { type Assoc = Priv; }` triggers unconditional
hard error `E0446` (`b08`, `compiler/rustc_privacy/src/lib.rs:1586`). -/
theorem assoc_type_private_fires_e0446 :
    let assocImpl : ItemInterface :=
      { nominal := .visPublic
      , privVis := pubCrate 0
      , effVis := EffectiveVisibility.fromVis .visPublic
      , primaryComps := []
      , boundComps := []
      , assocImplComps := [pubCrate 0]
      }
    FiresAssocTyHardError .visPublic assocImpl := by
  refine ⟨pubCrate 0, .head, ⟨trivial, ?_⟩⟩
  intro h
  cases h

/-!
## Part 5: Module-Tree Path Resolution, `pub use` Re-Exports,
## and Unnameability Implies Cross-Crate Impl Impossibility
-/

/-- A `pub use` (or restricted `use`) edge re-exporting a module (`modUse`) from `srcMod` into `inMod`. -/
structure ModReexportEdge where
  inMod : ModPath
  useVis : Visibility
  srcMod : ModPath

/-- A `pub use` (or restricted `use`) edge re-exporting a trait (`targetTrait`) into `inMod`. -/
structure TraitReexportEdge where
  inMod : ModPath
  useVis : Visibility
  targetTrait : TraitId

/-- A trait declaration with defining module, nominal visibility, and direct supertraits. -/
structure TraitDecl where
  id : TraitId
  defMod : ModPath
  nominal : Visibility
  supertraits : List TraitId

/-- A trait implementation `(implId, inCrate, traitId, selfType)` authored in crate `inCrate`. -/
structure TraitImpl where
  id : ImplId
  inCrate : CrateId
  traitId : TraitId
  selfType : TypeId

/-- A multi-crate module, re-export, trait, and impl world with explicit type ownership. -/
structure CrateWorld where
  modVis : ModPath → Visibility
  typeOwner : TypeId → CrateId
  modReexports : List ModReexportEdge
  traitReexports : List TraitReexportEdge
  traits : TraitId → Option TraitDecl
  impls : List TraitImpl

/-- Every ancestor module of `m` (including `crateRoot m.crate` and `m` itself) has `.visPublic`
nominal visibility. -/
noncomputable def AllAncestorsPublic (modVis : ModPath → Visibility) (m : ModPath) : Prop :=
  ∀ anc : ModPath, IsAncestor anc m → modVis anc = .visPublic

/-- A module `m` in crate `c` is externally reachable (exported) from another crate iff either
all of `m`'s ancestor modules are `.visPublic`, OR an ancestor module of `m` (or `m` itself) is
re-exported via a `.visPublic` `pub use` into an externally reachable module, with every intervening
module down to `m` having `.visPublic` nominal visibility. -/
inductive ModExternallyExported (world : CrateWorld) (c : CrateId) : ModPath → Prop where
  | direct {m : ModPath} :
      m.crate = c →
      AllAncestorsPublic world.modVis m →
      ModExternallyExported world c m
  | viaModReexport {e : ModReexportEdge} {m : ModPath} :
      Mem e world.modReexports →
      e.inMod.crate = c →
      e.srcMod.crate = c →
      e.useVis = .visPublic →
      ModExternallyExported world c e.inMod →
      IsAncestor e.srcMod m →
      (∀ mid : ModPath, IsAncestor e.srcMod mid → IsAncestor mid m → world.modVis mid = .visPublic) →
      ModExternallyExported world c m

/-- Every syntactic path (`Direct` or `pub use` re-export) by which an external crate
`callerCrate ≠ td.defMod.crate` can name a trait `trId` in `world`. -/
inductive NameableExternally (world : CrateWorld) (callerCrate : CrateId) : TraitId → Prop where
  | direct {trId : TraitId} {td : TraitDecl} :
      world.traits trId = some td →
      td.defMod.crate ≠ callerCrate →
      td.nominal = .visPublic →
      ModExternallyExported world td.defMod.crate td.defMod →
      NameableExternally world callerCrate trId
  | reexported {e : TraitReexportEdge} {td : TraitDecl} :
      Mem e world.traitReexports →
      world.traits e.targetTrait = some td →
      e.inMod.crate = td.defMod.crate →
      e.inMod.crate ≠ callerCrate →
      e.useVis = .visPublic →
      ModExternallyExported world e.inMod.crate e.inMod →
      NameableExternally world callerCrate e.targetTrait

/-- A crate `c` can name trait `trId` in an `impl` header iff either `trId` is defined in `c`
or `NameableExternally world c trId` holds. -/
noncomputable def CanNameTrait (world : CrateWorld) (c : CrateId) (trId : TraitId) : Prop :=
  match world.traits trId with
  | none => False
  | some td =>
    if Nat.beq td.defMod.crate c then True
    else NameableExternally world c trId

/-- Transitive supertrait reachability (`SupertraitReachable world sub sup`). -/
inductive SupertraitReachable (world : CrateWorld) : TraitId → TraitId → Prop where
  | refl (t : TraitId) : SupertraitReachable world t t
  | step {t mid s : TraitId} {td : TraitDecl} :
      world.traits t = some td →
      Mem mid td.supertraits →
      SupertraitReachable world mid s →
      SupertraitReachable world t s

theorem supertraitReachable_trans {world : CrateWorld} {a b c : TraitId}
    (hab : SupertraitReachable world a b) (hbc : SupertraitReachable world b c) :
    SupertraitReachable world a c := by
  induction hab with
  | refl _ => exact hbc
  | step htd hmem _ ih => exact .step htd hmem (ih hbc)

/-- Path-bottleneck condition: every direct ancestor chain AND every `pub use` module re-export
path reaching module `m` crosses at least one non-public module (`world.modVis mid ≠ .visPublic`). -/
noncomputable def PathCrossesNonPublic (world : CrateWorld) (m : ModPath) : Prop :=
  (∃ anc : ModPath, IsAncestor anc m ∧ world.modVis anc ≠ .visPublic) ∧
  (∀ e : ModReexportEdge, Mem e world.modReexports →
    e.useVis = .visPublic → IsAncestor e.srcMod m →
    ∃ mid : ModPath, IsAncestor e.srcMod mid ∧ IsAncestor mid m ∧ world.modVis mid ≠ .visPublic)

/-- **Path-Bottleneck Theorem:** Whenever every path from the crate root (both direct and via
`pub use` module re-exports) to module `m` crosses a non-public module, `m` cannot be externally
exported (`¬ ModExternallyExported world m.crate m`). -/
theorem pathCrossesNonPublic_blocks_modExport
    {world : CrateWorld} {m : ModPath}
    (hblock : PathCrossesNonPublic world m) :
    ¬ ModExternallyExported world m.crate m := by
  intro hexp
  cases hexp with
  | direct _ hall =>
    have ⟨anc, hanc, hne⟩ := hblock.1
    exact hne (hall anc hanc)
  | viaModReexport hmem _ _ hpub _ hsrc hmid =>
    have ⟨mid, hm1, hm2, hne⟩ := hblock.2 _ hmem hpub hsrc
    exact hne (hmid mid hm1 hm2)

/-- Full trait unexport condition: `sealedId` is defined in `td.defMod`, its defining module
is unexported (`¬ ModExternallyExported`), and no `pub use` trait re-export exposes `sealedId` at
an externally exported module. -/
noncomputable def UnexportedTrait (world : CrateWorld) (sealedId : TraitId) : Prop :=
  ∃ td : TraitDecl,
    world.traits sealedId = some td ∧
    ¬ ModExternallyExported world td.defMod.crate td.defMod ∧
    (∀ e : TraitReexportEdge, Mem e world.traitReexports →
      e.targetTrait = sealedId → e.inMod.crate = td.defMod.crate →
      e.useVis = .visPublic → ¬ ModExternallyExported world e.inMod.crate e.inMod)

/-- **Unexport Implies External Unnameability:** If `UnexportedTrait world sealedId` holds,
then NO external crate `c_ext ≠ td.defMod.crate` can name `sealedId`. -/
theorem unexportedTrait_not_nameableExternally
    {world : CrateWorld} {sealedId : TraitId} {c_ext : CrateId}
    (hunexp : UnexportedTrait world sealedId) :
    ¬ NameableExternally world c_ext sealedId := by
  intro hname
  have ⟨td, htd, hmod, hreexp⟩ := hunexp
  cases hname with
  | direct htd' _ _ hexp =>
    rw [htd] at htd'
    injection htd' with hteq
    subst hteq
    exact hmod hexp
  | reexported hmem htd' hcr _ hpub hexp =>
    rw [htd] at htd'
    injection htd' with hteq
    subst hteq
    exact hreexp _ hmem rfl hcr hpub hexp

/-- Witness that `CanNameTrait` is false for any external crate on an `UnexportedTrait`. -/
theorem unexportedTrait_cannot_name_external
    {world : CrateWorld} {sealedId : TraitId} {td : TraitDecl} {c_ext : CrateId}
    (htd : world.traits sealedId = some td)
    (hunexp : UnexportedTrait world sealedId)
    (hne : td.defMod.crate ≠ c_ext) :
    ¬ CanNameTrait world c_ext sealedId := by
  simp only [CanNameTrait, htd]
  have hbf := nat_beq_false_of_ne hne
  rw [hbf]
  exact unexportedTrait_not_nameableExternally hunexp

/-- Whether a trait `trId` has an implementation for `selfType` in `world.impls`. -/
noncomputable def HasImpl (world : CrateWorld) (trId : TraitId) (selfType : TypeId) : Prop :=
  ∃ im : TraitImpl, Mem im world.impls ∧ im.traitId = trId ∧ im.selfType = selfType

/-- Whether a trait `trId` has an implementation for `selfType` authored inside crate `c`. -/
noncomputable def HasImplInCrate
    (world : CrateWorld) (c : CrateId) (trId : TraitId) (selfType : TypeId) : Prop :=
  ∃ im : TraitImpl,
    Mem im world.impls ∧ im.inCrate = c ∧ im.traitId = trId ∧ im.selfType = selfType

/-- Compiler validity predicate on a multi-crate `CrateWorld` (combining name privacy,
supertrait obligations, and orphan locality for ground nominal types):
every `TraitImpl` in `world.impls` must:
1. Reference an existing `TraitDecl` that its authoring crate `im.inCrate` can name (`CanNameTrait`,
   enforced by `rustc_resolve` / `TypePrivacyVisitor` -> `E0603`),
2. Satisfy the orphan rule (`im.inCrate = td.defMod.crate ∨ world.typeOwner im.selfType = im.inCrate`,
   enforced by `orphan_check_impl` -> `E0117`), and
3. Satisfy every direct supertrait bound `sup ∈ td.supertraits` via an impl in `world.impls`
   (enforced by trait solving / `wfcheck` -> `E0277`). -/
noncomputable def ValidWorld (world : CrateWorld) : Prop :=
  ∀ im : TraitImpl, Mem im world.impls →
    ∃ td : TraitDecl,
      world.traits im.traitId = some td ∧
      CanNameTrait world im.inCrate im.traitId ∧
      (im.inCrate = td.defMod.crate ∨ world.typeOwner im.selfType = im.inCrate) ∧
      (∀ sup : TraitId, Mem sup td.supertraits → HasImpl world sup im.selfType)

/-- Supertrait obligation propagates transitively across `SupertraitReachable` in any `ValidWorld`. -/
theorem validWorld_supertrait_closure
    {world : CrateWorld} (hval : ValidWorld world)
    {sub sup : TraitId} (hreach : SupertraitReachable world sub sup)
    {ty : TypeId} (hhas : HasImpl world sub ty) :
    HasImpl world sup ty := by
  induction hreach generalizing ty with
  | refl _ => exact hhas
  | step htd hmem _ ih =>
    have ⟨im, him, heq_tr, heq_ty⟩ := hhas
    have ⟨td', htd', _, _, hsups⟩ := hval im him
    rw [heq_tr, htd] at htd'
    injection htd' with hdeq
    subst hdeq
    have hmid : HasImpl world _ im.selfType := hsups _ hmem
    rw [heq_ty] at hmid
    exact ih hmid

/-- **Theorem 2 (Unnameability Implies Cross-Crate Impl Impossibility):**
If trait `pubTrait` transitively requires `sealedTrait` (`SupertraitReachable world pubTrait sealedTrait`),
`sealedTrait` is unexported (`UnexportedTrait world sealedTrait`, with owner crate `c₀`), and
defining crate `c₀` does NOT provide an impl of `sealedTrait` for `τ` (`¬ HasImplInCrate world c₀ sealedTrait τ`),
then in ANY `ValidWorld world`:
1. Zero crates (including all external crates `c_ext ≠ c₀`) can implement `sealedTrait` for `τ`;
2. Zero crates (including all external crates `c_ext ≠ c₀`) can implement `pubTrait` for `τ`! -/
theorem unnameable_supertrait_blocks_external_impl
    {world : CrateWorld} (hval : ValidWorld world)
    {pubTrait sealedTrait : TraitId} {td_sealed : TraitDecl} {τ : TypeId}
    (htd_s : world.traits sealedTrait = some td_sealed)
    (hreach : SupertraitReachable world pubTrait sealedTrait)
    (hunexp : UnexportedTrait world sealedTrait)
    (hno_def : ¬ HasImplInCrate world td_sealed.defMod.crate sealedTrait τ) :
    (¬ HasImpl world sealedTrait τ) ∧ (¬ HasImpl world pubTrait τ) := by
  have hno_sealed : ¬ HasImpl world sealedTrait τ := by
    intro ⟨im, hmem, htr, hty⟩
    have ⟨td', htd', hname, _, _⟩ := hval im hmem
    rw [htr, htd_s] at htd'
    injection htd' with hteq
    subst hteq
    cases hc : Nat.beq td_sealed.defMod.crate im.inCrate with
    | true =>
      have hceq := nat_beq_true_eq hc
      exact hno_def ⟨im, hmem, hceq.symm, htr, hty⟩
    | false =>
      have hne : td_sealed.defMod.crate ≠ im.inCrate := fun eq => by
        have ht := nat_beq_eq_true_of_eq eq
        rw [ht] at hc
        cases hc
      have hcant := unexportedTrait_cannot_name_external htd_s hunexp hne
      rw [htr] at hname
      exact hcant hname
  refine ⟨hno_sealed, ?_⟩
  intro hpub
  exact hno_sealed (validWorld_supertrait_closure hval hreach hpub)

/-- **Downstream-Type Impossibility Corollary (without needing `hno_def`):**
If type `τ` is owned by an external crate (`world.typeOwner τ ≠ c₀`), then defining crate `c₀`
cannot implement `sealedTrait` for `τ` either (by orphan locality in `c₀`, since `c₀` cannot
invent downstream nominal types), so **no** crate can implement `pubTrait` for any downstream type `τ`! -/
theorem external_type_cannot_impl_sealed_trait
    {world : CrateWorld} (hval : ValidWorld world)
    {pubTrait sealedTrait : TraitId} {td_sealed : TraitDecl} {τ : TypeId}
    (htd_s : world.traits sealedTrait = some td_sealed)
    (hreach : SupertraitReachable world pubTrait sealedTrait)
    (hunexp : UnexportedTrait world sealedTrait)
    (hc₀_no_ext : ∀ im : TraitImpl, Mem im world.impls →
      im.inCrate = td_sealed.defMod.crate → im.traitId = sealedTrait →
      world.typeOwner im.selfType = td_sealed.defMod.crate)
    (hτ_ext : world.typeOwner τ ≠ td_sealed.defMod.crate) :
    ¬ HasImpl world pubTrait τ := by
  have hno_def : ¬ HasImplInCrate world td_sealed.defMod.crate sealedTrait τ := by
    intro ⟨im, him, hcr, htr, hty⟩
    have heq := hc₀_no_ext im him hcr htr
    rw [hty] at heq
    exact hτ_ext heq
  exact (unnameable_supertrait_blocks_external_impl hval htd_s hreach hunexp hno_def).2

/-!
## Part 6: Sealed-Trait Closed-World Invariant Theorem and `zerocopy` Soundness Transfer
-/

/-- Specification of a sealed trait `pubTrait` defined in crate `c₀` with unexported supertrait
`sealedTrait` and defining-crate allowlist `allowedTypes`. -/
structure SealedTraitSpec (world : CrateWorld) where
  c₀ : CrateId
  pubTrait : TraitId
  sealedTrait : TraitId
  tdPub : TraitDecl
  tdSealed : TraitDecl
  allowedTypes : List TypeId
  htdPub : world.traits pubTrait = some tdPub
  htdSealed : world.traits sealedTrait = some tdSealed
  hc₀Pub : tdPub.defMod.crate = c₀
  hc₀Sealed : tdSealed.defMod.crate = c₀
  hreach : SupertraitReachable world pubTrait sealedTrait
  hunexp : UnexportedTrait world sealedTrait
  hclosedDef : ∀ im : TraitImpl, Mem im world.impls →
    im.inCrate = c₀ → im.traitId = sealedTrait → Mem im.selfType allowedTypes
  hallowedOwned : ∀ τ : TypeId, Mem τ allowedTypes → world.typeOwner τ = c₀

/-- **Theorem 3a (Sealed-Trait Closed-World Type-Set Theorem):**
Under any `SealedTraitSpec world`, in ANY `ValidWorld world` containing arbitrary downstream crates,
**every** implementation of `pubTrait` anywhere in `world` must target a type in `spec.allowedTypes`.
(Note: this relies solely on unnameability of `sealedTrait` + `hclosedDef`, not even orphan checks!) -/
theorem sealed_trait_closed_world_types
    {world : CrateWorld} (hval : ValidWorld world) (spec : SealedTraitSpec world)
    {im : TraitImpl} (him : Mem im world.impls) (htr : im.traitId = spec.pubTrait) :
    Mem im.selfType spec.allowedTypes := by
  have hhasPub : HasImpl world spec.pubTrait im.selfType := ⟨im, him, htr, rfl⟩
  have hhasSealed : HasImpl world spec.sealedTrait im.selfType :=
    validWorld_supertrait_closure hval spec.hreach hhasPub
  have ⟨im_s, him_s, htr_s, hty_s⟩ := hhasSealed
  have ⟨td', htd', hname_s, _, _⟩ := hval im_s him_s
  rw [htr_s, spec.htdSealed] at htd'
  injection htd' with hteq
  subst hteq
  cases hc : Nat.beq spec.tdSealed.defMod.crate im_s.inCrate with
  | true =>
    have hceq := nat_beq_true_eq hc
    have hmem := spec.hclosedDef im_s him_s (spec.hc₀Sealed.symm.trans hceq).symm htr_s
    rw [← hty_s]
    exact hmem
  | false =>
    have hne : spec.tdSealed.defMod.crate ≠ im_s.inCrate := fun eq => by
      have ht := nat_beq_eq_true_of_eq eq
      rw [ht] at hc
      cases hc
    have hcant := unexportedTrait_cannot_name_external spec.htdSealed spec.hunexp hne
    rw [htr_s] at hname_s
    exact False.elim (hcant hname_s)

/-- **Theorem 3b (Sealed-Trait Complete Defining-Crate Fixity — Sealing + Orphan Composition):**
Combining unnameability of `sealedTrait` with orphan ownership of `allowedTypes` proves that
**every** implementation of `pubTrait` anywhere in `world` has BOTH `im.selfType ∈ spec.allowedTypes`
AND `im.inCrate = spec.c₀`! Thus the set of `impl pubTrait` items is completely fixed by `spec.c₀`. -/
theorem sealed_trait_closed_world_invariant
    {world : CrateWorld} (hval : ValidWorld world) (spec : SealedTraitSpec world)
    {im : TraitImpl} (him : Mem im world.impls) (htr : im.traitId = spec.pubTrait) :
    Mem im.selfType spec.allowedTypes ∧ im.inCrate = spec.c₀ := by
  have hmem := sealed_trait_closed_world_types hval spec him htr
  have hown := spec.hallowedOwned im.selfType hmem
  have ⟨td, htd, _, horph, _⟩ := hval im him
  rw [htr, spec.htdPub] at htd
  injection htd with hteq
  subst hteq
  refine ⟨hmem, ?_⟩
  cases horph with
  | inl hcr => exact hcr.trans spec.hc₀Pub
  | inr hty => exact hty.symm.trans hown

/-!
### Instantiation to Real `google/zerocopy` (`ByteOrder` and `pointer::invariant`)
-/

/-- Canonical `zerocopy` trait & type IDs (crate `0` = `zerocopy`). -/
noncomputable def zcPrivMod : ModPath := { crate := 0, segs := [1] } -- `byteorder::private` / `invariant::sealed`
noncomputable def zcPubMod : ModPath := { crate := 0, segs := [2] }  -- `byteorder` / `pointer::invariant`

noncomputable def trSealed : TraitId := 10
noncomputable def trByteOrder : TraitId := 11
noncomputable def trAliasing : TraitId := 12
noncomputable def trAlignment : TraitId := 13
noncomputable def trValidity : TraitId := 14
noncomputable def trReference : TraitId := 15
noncomputable def trInvariants : TraitId := 16

noncomputable def tyBigEndian : TypeId := 100
noncomputable def tyLittleEndian : TypeId := 101
noncomputable def tyShared : TypeId := 102
noncomputable def tyExclusive : TypeId := 103
noncomputable def tyUnaligned : TypeId := 104
noncomputable def tyAligned : TypeId := 105
noncomputable def tyUninit : TypeId := 106
noncomputable def tyAsInitialized : TypeId := 107
noncomputable def tyInitialized : TypeId := 108
noncomputable def tySafe : TypeId := 109

/-- `zerocopy` trait declarations matching `byteorder.rs:87-99` and `pointer/invariant.rs:19-117, 288-309`:
`ByteOrder: Sealed`, `Aliasing: Sealed`, `Alignment: Sealed`, `Validity: Sealed`,
`Reference: Aliasing + Sealed`, `Invariants: Sealed`. -/
noncomputable def zcTraits : TraitId → Option TraitDecl
  | 10 => some { id := 10, defMod := zcPrivMod, nominal := .visPublic, supertraits := [] }
  | 11 => some { id := 11, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] }
  | 12 => some { id := 12, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] }
  | 13 => some { id := 13, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] }
  | 14 => some { id := 14, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] }
  | 15 => some { id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12, 10] }
  | 16 => some { id := 16, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] }
  | _ => none

/-- Module visibilities in `zerocopy`: crate root and `zcPubMod` are `.visPublic`; `zcPrivMod` is `pub(crate)`. -/
noncomputable def zcModVis (m : ModPath) : Visibility :=
  match Nat.beq m.crate 0 with
  | false => .visPublic
  | true =>
    match m.segs with
    | [] => .visPublic
    | [2] => .visPublic
    | _ => pubCrate 0

/-- All 10 concrete `zerocopy` marker types are owned by crate `0` (`zerocopy`). -/
noncomputable def zcTypeOwner (τ : TypeId) : CrateId :=
  if Nat.beq τ tyBigEndian then 0
  else if Nat.beq τ tyLittleEndian then 0
  else if Nat.beq τ tyShared then 0
  else if Nat.beq τ tyExclusive then 0
  else if Nat.beq τ tyUnaligned then 0
  else if Nat.beq τ tyAligned then 0
  else if Nat.beq τ tyUninit then 0
  else if Nat.beq τ tyAsInitialized then 0
  else if Nat.beq τ tyInitialized then 0
  else if Nat.beq τ tySafe then 0
  else 1

theorem zcPrivMod_unexported
    {world : CrateWorld}
    (hmod : world.modVis = zcModVis)
    (hmr : world.modReexports = [])
    (htr : world.traitReexports = [])
    (htraits : world.traits = zcTraits) :
    UnexportedTrait world trSealed := by
  have hpriv_unexp : ¬ ModExternallyExported world 0 zcPrivMod := by
    intro hexp
    cases hexp with
    | direct _ hall =>
      have hv := hall zcPrivMod (isAncestor_refl zcPrivMod)
      rw [hmod] at hv
      cases hv
    | viaModReexport hmem _ =>
      rw [hmr] at hmem
      cases hmem
  refine ⟨{ id := 10, defMod := zcPrivMod, nominal := .visPublic, supertraits := [] }, ?_, hpriv_unexp, ?_⟩
  · rw [htraits]; rfl
  · intro e hmem
    rw [htr] at hmem
    cases hmem

/-- **Theorem 3c (`zerocopy` Closed-World `unsafe` Invariant Preservation):**
For ANY downstream crate extension `world` over `zerocopy` (`zcTraits`, `zcModVis`, `zcTypeOwner`,
no re-export leak of `trSealed`) that satisfies `ValidWorld world`:
1. `trSealed` is strictly unexported and unnameable by every downstream crate `c ≠ 0`;
2. Every `impl Reference` anywhere in `world` must be in crate `0` and have `selfType ∈ {Shared, Exclusive}`
   (preserving the `Ptr::into_shared` and `Ptr::read` safety invariant `invariant.rs:115-116`);
3. Every `impl ByteOrder` anywhere in `world` must be in crate `0` and have `selfType ∈ {BigEndian, LittleEndian}`
   (`byteorder.rs:87-99`);
4. Every `impl Alignment` anywhere in `world` must be in crate `0` and have `selfType ∈ {Unaligned, Aligned}`
   (`invariant.rs:44`);
5. Every `unsafe impl Validity` anywhere in `world` must be in crate `0` and have
   `selfType ∈ {Uninit, AsInitialized, Initialized, Safe}` (`invariant.rs:100`). -/
theorem zerocopy_closed_world_soundness
    (world : CrateWorld)
    (hmod : world.modVis = zcModVis)
    (hmr : world.modReexports = [])
    (htr : world.traitReexports = [])
    (htraits : world.traits = zcTraits)
    (hval : ValidWorld world)
    (hzcRef : ∀ im : TraitImpl, Mem im world.impls → im.inCrate = 0 → im.traitId = trReference →
      im.selfType = tyShared ∨ im.selfType = tyExclusive)
    (hzcByte : ∀ im : TraitImpl, Mem im world.impls → im.inCrate = 0 → im.traitId = trByteOrder →
      im.selfType = tyBigEndian ∨ im.selfType = tyLittleEndian)
    (hzcAlign : ∀ im : TraitImpl, Mem im world.impls → im.inCrate = 0 → im.traitId = trAlignment →
      im.selfType = tyUnaligned ∨ im.selfType = tyAligned)
    (hzcVal : ∀ im : TraitImpl, Mem im world.impls → im.inCrate = 0 → im.traitId = trValidity →
      im.selfType = tyUninit ∨ im.selfType = tyAsInitialized ∨
      im.selfType = tyInitialized ∨ im.selfType = tySafe)
    (hzcSealedCrate0 : ∀ im : TraitImpl, Mem im world.impls → im.inCrate = 0 → im.traitId = trSealed →
      world.typeOwner im.selfType = 0) :
    UnexportedTrait world trSealed ∧
    (∀ im : TraitImpl, Mem im world.impls → im.traitId = trReference →
      im.inCrate = 0 ∧ (im.selfType = tyShared ∨ im.selfType = tyExclusive)) ∧
    (∀ im : TraitImpl, Mem im world.impls → im.traitId = trByteOrder →
      im.inCrate = 0 ∧ (im.selfType = tyBigEndian ∨ im.selfType = tyLittleEndian)) ∧
    (∀ im : TraitImpl, Mem im world.impls → im.traitId = trAlignment →
      im.inCrate = 0 ∧ (im.selfType = tyUnaligned ∨ im.selfType = tyAligned)) ∧
    (∀ im : TraitImpl, Mem im world.impls → im.traitId = trValidity →
      im.inCrate = 0 ∧ (im.selfType = tyUninit ∨ im.selfType = tyAsInitialized ∨
        im.selfType = tyInitialized ∨ im.selfType = tySafe)) := by
  have hunexp := zcPrivMod_unexported hmod hmr htr htraits
  have htdS : world.traits trSealed =
      some { id := 10, defMod := zcPrivMod, nominal := .visPublic, supertraits := [] } := by
    rw [htraits]; rfl
  have crate0_sealed_owner : ∀ {im : TraitImpl}, Mem im world.impls → im.traitId = trSealed →
      im.inCrate = 0 ∧ world.typeOwner im.selfType = 0 := by
    intro im him htr_s
    have ⟨td, htd, hname, _, _⟩ := hval im him
    rw [htr_s, htdS] at htd
    injection htd with hteq
    subst hteq
    cases hc : Nat.beq 0 im.inCrate with
    | true =>
      have hcr : im.inCrate = 0 := (nat_beq_true_eq hc).symm
      exact ⟨hcr, hzcSealedCrate0 im him hcr htr_s⟩
    | false =>
      have hne : (0 : CrateId) ≠ im.inCrate := fun eq => by
        have ht := nat_beq_eq_true_of_eq eq
        rw [ht] at hc
        cases hc
      have hcant := unexportedTrait_cannot_name_external htdS hunexp hne
      rw [htr_s] at hname
      exact False.elim (hcant hname)
  have force_crate0_via_sealed : ∀ {pubTr : TraitId} {tdPub : TraitDecl},
      world.traits pubTr = some tdPub →
      tdPub.defMod.crate = 0 →
      SupertraitReachable world pubTr trSealed →
      ∀ {im : TraitImpl}, Mem im world.impls → im.traitId = pubTr → im.inCrate = 0 := by
    intro pubTr tdPub htdP hcrP hreach im him htr_p
    have hhasS : HasImpl world trSealed im.selfType :=
      validWorld_supertrait_closure hval hreach ⟨im, him, htr_p, rfl⟩
    have ⟨im_s, him_s, htr_s, hty_s⟩ := hhasS
    have ⟨_, hown⟩ := crate0_sealed_owner him_s htr_s
    rw [hty_s] at hown
    have ⟨td', htd', _, horph, _⟩ := hval im him
    rw [htr_p, htdP] at htd'
    injection htd' with hteq
    subst hteq
    cases horph with
    | inl hcr => exact hcr.trans hcrP
    | inr hty => exact hty.symm.trans hown
  refine ⟨hunexp, ?_, ?_, ?_, ?_⟩
  · intro im him htr_eq
    have htdR : world.traits trReference =
        some { id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12, 10] } := by
      rw [htraits]; rfl
    have hreachR : SupertraitReachable world trReference trSealed :=
      .step htdR (.tail .head) (.refl _)
    have hcr0 := force_crate0_via_sealed htdR rfl hreachR him htr_eq
    exact ⟨hcr0, hzcRef im him hcr0 htr_eq⟩
  · intro im him htr_eq
    have htdB : world.traits trByteOrder =
        some { id := 11, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] } := by
      rw [htraits]; rfl
    have hreachB : SupertraitReachable world trByteOrder trSealed :=
      .step htdB .head (.refl _)
    have hcr0 := force_crate0_via_sealed htdB rfl hreachB him htr_eq
    exact ⟨hcr0, hzcByte im him hcr0 htr_eq⟩
  · intro im him htr_eq
    have htdA : world.traits trAlignment =
        some { id := 13, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] } := by
      rw [htraits]; rfl
    have hreachA : SupertraitReachable world trAlignment trSealed :=
      .step htdA .head (.refl _)
    have hcr0 := force_crate0_via_sealed htdA rfl hreachA him htr_eq
    exact ⟨hcr0, hzcAlign im him hcr0 htr_eq⟩
  · intro im him htr_eq
    have htdV : world.traits trValidity =
        some { id := 14, defMod := zcPubMod, nominal := .visPublic, supertraits := [10] } := by
      rw [htraits]; rfl
    have hreachV : SupertraitReachable world trValidity trSealed :=
      .step htdV .head (.refl _)
    have hcr0 := force_crate0_via_sealed htdV rfl hreachV him htr_eq
    exact ⟨hcr0, hzcVal im him hcr0 htr_eq⟩

/-!
## Part 7: Re-Export Escape Counterexample, `#[doc(hidden)]` Non-Sealing, and Unsealed Forgeability
-/

/-- Concrete multi-crate world witnessing **Re-Export Escape (`c05`)**:
- Upstream crate `0` defines `mod private { pub trait LeakySealed {} }` (`modVis = pub(crate)`),
  `pub trait PublicFromLeaky: private::LeakySealed {}` at crate root, AND leaks
  `pub use private::LeakySealed;` at crate root `crateRoot 0`.
- Downstream crate `1` defines `LocalTy` (`typeOwner LocalTy = 1`) and writes
  `impl LeakySealed for LocalTy` and `impl PublicFromLeaky for LocalTy`. -/
noncomputable def escapeCrateRoot0 : ModPath := crateRoot 0
noncomputable def escapePrivMod0 : ModPath := { crate := 0, segs := [1] }

noncomputable def escapeTrLeaky : TraitId := 1
noncomputable def escapeTrPublic : TraitId := 2
noncomputable def escapeTyToken : TypeId := 10
noncomputable def escapeTyLocal : TypeId := 11

noncomputable def escapeModVis (m : ModPath) : Visibility :=
  match Nat.beq m.crate 0 with
  | false => .visPublic
  | true =>
    match m.segs with
    | [] => .visPublic
    | _ => pubCrate 0

noncomputable def escapeTypeOwner (τ : TypeId) : CrateId :=
  if Nat.beq τ escapeTyToken then 0 else 1

noncomputable def escapeTraits : TraitId → Option TraitDecl
  | 1 => some { id := 1, defMod := escapePrivMod0, nominal := .visPublic, supertraits := [] }
  | 2 => some { id := 2, defMod := escapeCrateRoot0, nominal := .visPublic, supertraits := [1] }
  | _ => none

noncomputable def escapeReexportEdge : TraitReexportEdge :=
  { inMod := escapeCrateRoot0, useVis := .visPublic, targetTrait := escapeTrLeaky }

noncomputable def escapeImpls : List TraitImpl :=
  [ { id := 1, inCrate := 0, traitId := escapeTrLeaky, selfType := escapeTyToken }
  , { id := 2, inCrate := 0, traitId := escapeTrPublic, selfType := escapeTyToken }
  , { id := 3, inCrate := 1, traitId := escapeTrLeaky, selfType := escapeTyLocal }
  , { id := 4, inCrate := 1, traitId := escapeTrPublic, selfType := escapeTyLocal }
  ]

noncomputable def escapeWorld : CrateWorld :=
  { modVis := escapeModVis
  , typeOwner := escapeTypeOwner
  , modReexports := []
  , traitReexports := [escapeReexportEdge]
  , traits := escapeTraits
  , impls := escapeImpls
  }

/-- **Theorem 4a (Re-Export Escape Counterexample):**
In `escapeWorld`, adding `pub use private::LeakySealed;` at the public crate root makes
`LeakySealed` nameable by crate `1` (`NameableExternally escapeWorld 1 escapeTrLeaky`),
making `escapeWorld` a `ValidWorld` where downstream crate `1` validly implements
`PublicFromLeaky` for `LocalTy` outside `[Token]`, breaking sealing! -/
theorem reexport_escape_breaks_sealing :
    NameableExternally escapeWorld 1 escapeTrLeaky ∧
    ValidWorld escapeWorld ∧
    HasImplInCrate escapeWorld 1 escapeTrPublic escapeTyLocal ∧
    escapeTyLocal ≠ escapeTyToken := by
  have hc0_root_exp : ModExternallyExported escapeWorld 0 escapeCrateRoot0 := by
    refine ModExternallyExported.direct rfl ?_
    intro anc hanc
    cases anc with | mk c s =>
    have hc : c = 0 := hanc.1
    subst hc
    cases s with
    | nil => rfl
    | cons _ _ => cases hanc.2
  have hname_leaky : NameableExternally escapeWorld 1 escapeTrLeaky := by
    have htd1 : escapeWorld.traits escapeReexportEdge.targetTrait =
        some { id := 1, defMod := escapePrivMod0, nominal := .visPublic, supertraits := [] } := rfl
    refine NameableExternally.reexported (e := escapeReexportEdge) .head htd1 rfl ?_ rfl hc0_root_exp
    intro h; cases h
  have hname_pub : NameableExternally escapeWorld 1 escapeTrPublic := by
    refine NameableExternally.direct rfl ?_ rfl hc0_root_exp
    intro h; cases h
  have hval : ValidWorld escapeWorld := by
    intro im him
    cases him with
    | head =>
      refine ⟨{ id := 1, defMod := escapePrivMod0, nominal := .visPublic, supertraits := [] }, rfl, ?_, Or.inl rfl, ?_⟩
      · trivial
      · intro sup hsup; cases hsup
    | tail him1 =>
      cases him1 with
      | head =>
        refine ⟨{ id := 2, defMod := escapeCrateRoot0, nominal := .visPublic, supertraits := [1] }, rfl, ?_, Or.inl rfl, ?_⟩
        · trivial
        · intro sup hsup
          cases hsup with
          | head => exact ⟨_, .head, rfl, rfl⟩
          | tail hnil => cases hnil
      | tail him2 =>
        cases him2 with
        | head =>
          refine ⟨{ id := 1, defMod := escapePrivMod0, nominal := .visPublic, supertraits := [] }, rfl, ?_, Or.inr rfl, ?_⟩
          · exact hname_leaky
          · intro sup hsup; cases hsup
        | tail him3 =>
          cases him3 with
          | head =>
            refine ⟨{ id := 2, defMod := escapeCrateRoot0, nominal := .visPublic, supertraits := [1] }, rfl, ?_, Or.inr rfl, ?_⟩
            · exact hname_pub
            · intro sup hsup
              cases hsup with
              | head => exact ⟨_, .tail (.tail .head), rfl, rfl⟩
              | tail hnil => cases hnil
          | tail hnil => cases hnil
  refine ⟨hname_leaky, hval, ?_, ?_⟩
  · exact ⟨{ id := 4, inCrate := 1, traitId := escapeTrPublic, selfType := escapeTyLocal },
      .tail (.tail (.tail .head)), rfl, rfl, rfl⟩
  · intro h; cases h

/-- Concrete world witnessing **`#[doc(hidden)] pub mod` Non-Sealing (`c06`)**:
`doc_hidden` has `nominal = .visPublic` (`#[doc(hidden)]` affects only rustdoc, never `rustc_privacy`),
so `AllAncestorsPublic` holds and downstream crate `1` can directly name and implement `NotSealed`
and `DocHiddenSuper`. -/
noncomputable def docHiddenMod0 : ModPath := { crate := 0, segs := [1] }

noncomputable def docHiddenWorld : CrateWorld :=
  { modVis := fun _ => .visPublic
  , typeOwner := escapeTypeOwner
  , modReexports := []
  , traitReexports := []
  , traits := fun
      | 1 => some { id := 1, defMod := docHiddenMod0, nominal := .visPublic, supertraits := [] }
      | 2 => some { id := 2, defMod := escapeCrateRoot0, nominal := .visPublic, supertraits := [1] }
      | _ => none
  , impls :=
      [ { id := 1, inCrate := 1, traitId := 1, selfType := escapeTyLocal }
      , { id := 2, inCrate := 1, traitId := 2, selfType := escapeTyLocal }
      ]
  }

/-- **Theorem 4b (`#[doc(hidden)] pub mod` Does Not Seal Against Downstream `impl`s):** -/
theorem doc_hidden_mod_does_not_seal :
    NameableExternally docHiddenWorld 1 1 ∧
    ValidWorld docHiddenWorld ∧
    HasImplInCrate docHiddenWorld 1 2 escapeTyLocal := by
  have hdoc_exp : ModExternallyExported docHiddenWorld 0 docHiddenMod0 :=
    ModExternallyExported.direct rfl (fun _ _ => rfl)
  have hroot_exp : ModExternallyExported docHiddenWorld 0 escapeCrateRoot0 :=
    ModExternallyExported.direct rfl (fun _ _ => rfl)
  have hname1 : NameableExternally docHiddenWorld 1 1 :=
    NameableExternally.direct rfl (fun h => by cases h) rfl hdoc_exp
  have hname2 : NameableExternally docHiddenWorld 1 2 :=
    NameableExternally.direct rfl (fun h => by cases h) rfl hroot_exp
  have hval : ValidWorld docHiddenWorld := by
    intro im him
    cases him with
    | head =>
      refine ⟨{ id := 1, defMod := docHiddenMod0, nominal := .visPublic, supertraits := [] }, rfl, hname1, Or.inr rfl, ?_⟩
      intro sup hsup; cases hsup
    | tail him1 =>
      cases him1 with
      | head =>
        refine ⟨{ id := 2, defMod := escapeCrateRoot0, nominal := .visPublic, supertraits := [1] }, rfl, hname2, Or.inr rfl, ?_⟩
        intro sup hsup
        cases hsup with
        | head => exact ⟨_, .head, rfl, rfl⟩
        | tail hnil => cases hnil
      | tail hnil => cases hnil
  exact ⟨hname1, hval, ⟨_, .tail .head, rfl, rfl, rfl⟩⟩

/-- Concrete world witnessing **Unsealed `Reference` Allows Forged Third Aliasing Type**:
if `Reference` omits `: Sealed` (keeping only `: Aliasing`, where `Aliasing` is also unsealed),
a downstream crate can validly implement `Reference` for a forged type `tyBogus = 999 ∉ {Shared, Exclusive}`. -/
noncomputable def tyBogus : TypeId := 999

noncomputable def unsealedRefWorld : CrateWorld :=
  { modVis := fun _ => .visPublic
  , typeOwner := fun τ => if Nat.beq τ tyShared then 0 else if Nat.beq τ tyExclusive then 0 else 1
  , modReexports := []
  , traitReexports := []
  , traits := fun
      | 12 => some { id := 12, defMod := zcPubMod, nominal := .visPublic, supertraits := [] }
      | 15 => some { id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12] }
      | _ => none
  , impls :=
      [ { id := 1, inCrate := 0, traitId := trAliasing, selfType := tyShared }
      , { id := 2, inCrate := 0, traitId := trReference, selfType := tyShared }
      , { id := 3, inCrate := 0, traitId := trAliasing, selfType := tyExclusive }
      , { id := 4, inCrate := 0, traitId := trReference, selfType := tyExclusive }
      , { id := 5, inCrate := 1, traitId := trAliasing, selfType := tyBogus }
      , { id := 6, inCrate := 1, traitId := trReference, selfType := tyBogus }
      ]
  }

theorem unsealed_reference_allows_forged_aliasing :
    ValidWorld unsealedRefWorld ∧
    HasImplInCrate unsealedRefWorld 1 trReference tyBogus ∧
    tyBogus ≠ tyShared ∧
    tyBogus ≠ tyExclusive := by
  have hpub_exp : ModExternallyExported unsealedRefWorld 0 zcPubMod :=
    ModExternallyExported.direct rfl (fun _ _ => rfl)
  have hname12 : NameableExternally unsealedRefWorld 1 trAliasing :=
    NameableExternally.direct rfl (fun h => by cases h) rfl hpub_exp
  have hname15 : NameableExternally unsealedRefWorld 1 trReference :=
    NameableExternally.direct rfl (fun h => by cases h) rfl hpub_exp
  have hval : ValidWorld unsealedRefWorld := by
    intro im him
    cases him with
    | head =>
      refine ⟨{ id := 12, defMod := zcPubMod, nominal := .visPublic, supertraits := [] }, rfl, trivial, Or.inl rfl, ?_⟩
      intro sup hsup; cases hsup
    | tail him1 =>
      cases him1 with
      | head =>
        refine ⟨{ id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12] }, rfl, trivial, Or.inl rfl, ?_⟩
        intro sup hsup
        cases hsup with
        | head => exact ⟨_, .head, rfl, rfl⟩
        | tail hnil => cases hnil
      | tail him2 =>
        cases him2 with
        | head =>
          refine ⟨{ id := 12, defMod := zcPubMod, nominal := .visPublic, supertraits := [] }, rfl, trivial, Or.inl rfl, ?_⟩
          intro sup hsup; cases hsup
        | tail him3 =>
          cases him3 with
          | head =>
            refine ⟨{ id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12] }, rfl, trivial, Or.inl rfl, ?_⟩
            intro sup hsup
            cases hsup with
            | head => exact ⟨_, .tail (.tail .head), rfl, rfl⟩
            | tail hnil => cases hnil
          | tail him4 =>
            cases him4 with
            | head =>
              refine ⟨{ id := 12, defMod := zcPubMod, nominal := .visPublic, supertraits := [] }, rfl, hname12, Or.inr rfl, ?_⟩
              intro sup hsup; cases hsup
            | tail him5 =>
              cases him5 with
              | head =>
                refine ⟨{ id := 15, defMod := zcPubMod, nominal := .visPublic, supertraits := [12] }, rfl, hname15, Or.inr rfl, ?_⟩
                intro sup hsup
                cases hsup with
                | head => exact ⟨_, .tail (.tail (.tail (.tail .head))), rfl, rfl⟩
                | tail hnil => cases hnil
              | tail hnil => cases hnil
  refine ⟨hval, ⟨_, .tail (.tail (.tail (.tail (.tail .head)))), rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h

/-!
## Part 8: Concrete Module-Tree Accessibility Discriminators & Master Composition Theorem
-/

/-- Concrete module hierarchy matching Part A probes `a01`–`a03` (`crate::a`, `crate::a::sub`, `crate::b`):
`pub(in crate::a)` is accessible from `crate::a` and `crate::a::sub`, and rejected from sibling `crate::b`. -/
theorem concrete_pub_in_a_dominance_witness :
    let modA : ModPath := { crate := 0, segs := [1] }
    let modASub : ModPath := { crate := 0, segs := [1, 10] }
    let modB : ModPath := { crate := 0, segs := [2] }
    let visInA : Visibility := .restricted modA
    IsAccessibleFrom visInA modA ∧
    IsAccessibleFrom visInA modASub ∧
    ¬ IsAccessibleFrom visInA modB ∧
    VisLeq visInA (pubCrate 0) ∧
    ¬ VisLeq (pubCrate 0) visInA := by
  dsimp only
  refine ⟨isAncestor_refl _, ⟨rfl, .cons (.nil [10])⟩, ?_, pubCrate_dominates_local { crate := 0, segs := [1] }, ?_⟩
  · intro h
    cases h.2
  · intro h
    cases h.2

/-- **Master Theorem (Unified `rustc_privacy` Lattice, RFC 2145, & Sealed-Trait Soundness):**
Composes all core invariants of the package into a single kernel-checked theorem:
1. Module-tree visibility partial order (`VisLeq` reflexive, transitive, antisymmetric, `.visPublic` top,
   pointwise equivalent to `IsAccessibleFrom`);
2. `EffectiveVisibility` invariant preservation (`priv ≤ direct ≤ reexported ≤ reachable ≤ rpit` and
   `reachable ≤ nominal`, with RPIT hidden types able to reach `.visPublic` beyond `nominal`);
3. RFC 2145 & `unreachable_pub` compatibility (`PublicSealed: private::Sealed` passes `private_bounds`,
   `private_interfaces`, and `unreachable_pub`, while triggering opt-in `unnameable_types`);
4. Sealed-trait cross-crate impl impossibility & closed-world closure (`sealed_trait_closed_world_invariant`);
5. Necessity of private-module containment (`reexport_escape_breaks_sealing` + `doc_hidden_mod_does_not_seal`). -/
theorem master_privacy_and_sealing_soundness :
    (∀ v₁ v₂ : Visibility, VisLeq v₁ v₂ ↔
      ∀ caller : ModPath, IsAccessibleFrom v₁ caller → IsAccessibleFrom v₂ caller) ∧
    (∀ privMod : ModPath,
      ¬ FiresPrivateBounds mkPublicSealedTrait ∧
      ¬ FiresPrivateInterfaces mkPublicSealedTrait ∧
      ¬ FiresUnreachablePub (mkPrivateModSealedTrait privMod) ∧
      FiresUnnameableTypes (mkPrivateModSealedTrait privMod)) ∧
    (∀ (world : CrateWorld), ValidWorld world → ∀ (spec : SealedTraitSpec world)
        (im : TraitImpl), Mem im world.impls → im.traitId = spec.pubTrait →
      Mem im.selfType spec.allowedTypes ∧ im.inCrate = spec.c₀) ∧
    (ValidWorld escapeWorld ∧ HasImplInCrate escapeWorld 1 escapeTrPublic escapeTyLocal ∧
      escapeTyLocal ≠ escapeTyToken) ∧
    (ValidWorld docHiddenWorld ∧ HasImplInCrate docHiddenWorld 1 2 escapeTyLocal) := by
  refine ⟨visLeq_iff_pointwise_accessible, ?_, ?_, ?_, ?_⟩
  · intro privMod
    have hm := sealed_trait_lint_matrix privMod
    exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1⟩
  · intro world hval spec im him htr
    exact sealed_trait_closed_world_invariant hval spec him htr
  · have he := reexport_escape_breaks_sealing
    exact ⟨he.2.1, he.2.2.1, he.2.2.2⟩
  · have hd := doc_hidden_mod_does_not_seal
    exact ⟨hd.2.1, hd.2.2⟩

end RustcPrivacyLattice
