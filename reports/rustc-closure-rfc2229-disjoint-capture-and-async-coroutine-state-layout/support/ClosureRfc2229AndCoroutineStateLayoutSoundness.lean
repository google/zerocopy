prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Tactics
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation
import Init.Data.Option.Basic

/-!
# RFC 2229 Disjoint Closure Capture & Coroutine `StateTransform` Layout Soundness

Standalone, kernel-checked Lean `v4.34.1` formalization using only locked
`Init.*` foundation modules with:
- zero `sorry` / `sorryAx`,
- zero `Classical.choice`,
- zero `omega`, `bv_decide`, or `native_decide`,
- zero `partial def` and zero `._unsafe_rec` constants (`noncomputable def` on
  every value/predicate definition),
- universe-monomorphic (`Type 0`) theorem statements.

Part I mechanizes RFC 2229 place-prefix minimization (`MinCaptureList`),
capture-mode and `ClosureKind` lattices, wildcard non-capture (`fake_read`),
deref truncation (`truncate_capture_for_optimization` and `UniqueImmutable`
downgrades), `move` copy-field preservation, and disjoint-place memory
non-interference.

Part II mechanizes `StateTransform` coroutine state discriminants
(`UNRESUMED=0`, `RETURNED=1`, `POISONED=2`, `SuspendN=3+N`), deterministic state
transitions and panic-poisoning traps (`ResumedAfterPanic`, zero double-drop),
`storage_conflicts`-guided variant/prefix layout packing safety, and
self-referential `!Unpin` pinning address stability.
-/

namespace ClosureRfc2229AndCoroutineLayout

section BasicHelpers

noncomputable def maxNat (a b : Nat) : Nat :=
  if Nat.ble a b then b else a

theorem nat_le_refl (a : Nat) : a ≤ a :=
  Nat.le_refl a

theorem nat_le_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

theorem nat_lt_of_lt_of_le {a b c : Nat} (hab : a < b) (hbc : b ≤ c) : a < c :=
  Nat.lt_of_lt_of_le hab hbc

theorem nat_lt_of_le_of_lt {a b c : Nat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Nat.lt_of_le_of_lt hab hbc

theorem nat_add_le_add_left {a b : Nat} (h : a ≤ b) (c : Nat) : c + a ≤ c + b :=
  Nat.add_le_add_left h c

theorem nat_add_le_add_right {a b : Nat} (h : a ≤ b) (c : Nat) : a + c ≤ b + c :=
  Nat.add_le_add_right h c

theorem nat_add_le_add {a b c d : Nat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Nat.add_le_add hab hcd

theorem nat_le_add_right (a b : Nat) : a ≤ a + b :=
  Nat.le_add_right a b

theorem nat_le_add_left (a b : Nat) : b ≤ a + b :=
  Nat.le_add_left b a

theorem nat_ble_true_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b := by
  rw [Nat.ble_eq]

theorem nat_ble_false_iff (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  constructor
  · intro h
    cases Nat.lt_or_ge b a with
    | inl hlt => exact hlt
    | inr hle =>
      have ht : Nat.ble a b = true := (nat_ble_true_iff a b).2 hle
      rw [ht] at h
      cases h
  · intro hlt
    cases h : Nat.ble a b with
    | false => rfl
    | true =>
      have hle : a ≤ b := (nat_ble_true_iff a b).1 h
      exact False.elim (Nat.not_le_of_gt hlt hle)

theorem nat_blt_true_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  rw [Nat.beq_eq]

theorem bool_or_eq_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem nat_le_maxNat_left (a b : Nat) : a ≤ maxNat a b := by
  unfold maxNat
  cases h : Nat.ble a b with
  | true => exact (nat_ble_true_iff a b).1 h
  | false => exact Nat.le_refl a

theorem nat_le_maxNat_right (a b : Nat) : b ≤ maxNat a b := by
  unfold maxNat
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false =>
    have hlt : b < a := (nat_ble_false_iff a b).1 h
    exact Nat.le_of_lt hlt

theorem nat_maxNat_le {a b c : Nat} (hac : a ≤ c) (hbc : b ≤ c) :
    maxNat a b ≤ c := by
  unfold maxNat
  cases Nat.ble a b with
  | true => exact hbc
  | false => exact hac

noncomputable def listLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => listLength xs + 1

noncomputable def listNth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listNth? xs n

noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

noncomputable def listFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: listFilter p xs else listFilter p xs

noncomputable def listTake {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs => x :: listTake n xs

noncomputable def listDrop {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | _, [] => []
  | n + 1, _ :: xs => listDrop n xs

noncomputable def listMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: listMap f xs

inductive ListMem {α : Type} : α → List α → Prop where
  | head (x : α) (xs : List α) : ListMem x (x :: xs)
  | tail {x : α} (y : α) {xs : List α} : ListMem x xs → ListMem x (y :: xs)

theorem listAll_implies {α : Type} {p : α → Bool} {xs : List α}
    (hall : listAll p xs = true) {x : α} (hmem : ListMem x xs) :
    p x = true := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    simp only [listAll, Bool.and_eq_true] at hall
    cases hmem with
    | head => exact hall.1
    | tail _ htail => exact ih hall.2 htail

theorem listFilter_mem_iff {α : Type} {p : α → Bool} {xs : List α} {x : α} :
    ListMem x (listFilter p xs) ↔ ListMem x xs ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h.1
  | cons y ys ih =>
    unfold listFilter
    cases hpy : p y with
    | true =>
      change ListMem x (y :: listFilter p ys) ↔ ListMem x (y :: ys) ∧ p x = true
      constructor
      · intro h
        cases h with
        | head => exact ⟨ListMem.head x ys, hpy⟩
        | tail _ htail =>
          have r := ih.1 htail
          exact ⟨ListMem.tail y r.1, r.2⟩
      · intro h
        cases h.1 with
        | head => exact ListMem.head x (listFilter p ys)
        | tail _ htail => exact ListMem.tail y (ih.2 ⟨htail, h.2⟩)
    | false =>
      change ListMem x (listFilter p ys) ↔ ListMem x (y :: ys) ∧ p x = true
      constructor
      · intro h
        have r := ih.1 h
        exact ⟨ListMem.tail y r.1, r.2⟩
      · intro h
        cases h.1 with
        | head =>
          rw [hpy] at h
          cases h.2
        | tail _ htail =>
          exact ih.2 ⟨htail, h.2⟩

theorem listMap_mem {α β : Type} {f : α → β} {xs : List α} {x : α}
    (h : ListMem x xs) : ListMem (f x) (listMap f xs) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head => exact ListMem.head (f x) (listMap f ys)
    | tail _ htail => exact ListMem.tail (f y) (ih htail)

theorem listAny_true_iff {α : Type} {p : α → Bool} {xs : List α} :
    listAny p xs = true ↔ ∃ x, ListMem x xs ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h
      cases h with
      | intro _ hx => cases hx.1
  | cons y ys ih =>
    unfold listAny
    cases hpy : p y with
    | true =>
      change true = true ↔ ∃ x, ListMem x (y :: ys) ∧ p x = true
      constructor
      · intro _; exact ⟨y, ListMem.head y ys, hpy⟩
      · intro _; rfl
    | false =>
      simp only [Bool.false_or]
      constructor
      · intro h
        cases ih.1 h with
        | intro x hx => exact ⟨x, ListMem.tail y hx.1, hx.2⟩
      · intro h
        cases h with
        | intro x hx =>
          cases hx.1 with
          | head => rw [hpy] at hx; cases hx.2
          | tail _ htail => exact ih.2 ⟨x, htail, hx.2⟩

theorem listAny_false_iff {α : Type} {p : α → Bool} {xs : List α} :
    listAny p xs = false ↔ ∀ x, ListMem x xs → p x = false := by
  constructor
  · intro h x hm
    cases hpx : p x with
    | false => rfl
    | true =>
      have ht := (listAny_true_iff).2 ⟨x, hm, hpx⟩
      rw [ht] at h
      cases h
  · intro hall
    cases ha : listAny p xs with
    | false => rfl
    | true =>
      cases (listAny_true_iff).1 ha with
      | intro x hx =>
        have hf := hall x hx.1
        rw [hf] at hx
        cases hx.2

noncomputable def pairwiseDistinct {α : Type} (r : α → α → Prop) : List α → Prop
  | [] => True
  | x :: xs => (∀ y, ListMem y xs → r x y ∧ r y x) ∧ pairwiseDistinct r xs

end BasicHelpers

/-!
## Part I: RFC 2229 Disjoint Closure Capture Analysis & `ClosureKind` Lattice

Matches `compiler/rustc_hir_typeck/src/upvar.rs` and
`compiler/rustc_middle/src/ty/closure.rs`.
-/

section Rfc2229Capture

/-- Borrow kind (`ty::BorrowKind` in `compiler/rustc_middle/src/ty/closure.rs`). -/
inductive BorrowKind where
  | immutable
  | uniqueImmutable
  | mutable

noncomputable def BorrowKind.beq : BorrowKind → BorrowKind → Bool
  | .immutable, .immutable => true
  | .uniqueImmutable, .uniqueImmutable => true
  | .mutable, .mutable => true
  | _, _ => false

theorem BorrowKind.beq_eq {a b : BorrowKind} (h : BorrowKind.beq a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

noncomputable def BorrowKind.rank : BorrowKind → Nat
  | .immutable => 0
  | .uniqueImmutable => 1
  | .mutable => 2

noncomputable def BorrowKind.le (a b : BorrowKind) : Prop :=
  a.rank ≤ b.rank

noncomputable def BorrowKind.join : BorrowKind → BorrowKind → BorrowKind
  | .mutable, _ | _, .mutable => .mutable
  | .uniqueImmutable, _ | _, .uniqueImmutable => .uniqueImmutable
  | .immutable, .immutable => .immutable

/-- Lossy MIR lowering (`BorrowKind::to_mutbl_lossy`, `ty/closure.rs:442-452`). -/
inductive MirMutability where
  | shared
  | mut

noncomputable def MirMutability.beq : MirMutability → MirMutability → Bool
  | .shared, .shared => true
  | .mut, .mut => true
  | _, _ => false

noncomputable def BorrowKind.toMutblLossy : BorrowKind → MirMutability
  | .immutable => .shared
  | .uniqueImmutable => .mut
  | .mutable => .mut

theorem BorrowKind.join_comm (a b : BorrowKind) :
    BorrowKind.join a b = BorrowKind.join b a := by
  cases a <;> cases b <;> rfl

theorem BorrowKind.join_assoc (a b c : BorrowKind) :
    BorrowKind.join (BorrowKind.join a b) c =
      BorrowKind.join a (BorrowKind.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem BorrowKind.join_idem (a : BorrowKind) :
    BorrowKind.join a a = a := by
  cases a <;> rfl

theorem BorrowKind.le_join_left (a b : BorrowKind) :
    BorrowKind.le a (BorrowKind.join a b) := by
  unfold BorrowKind.le BorrowKind.join BorrowKind.rank
  cases a <;> cases b <;> dsimp only <;>
    first | exact Nat.le_refl _ | exact Nat.zero_le _ | exact Nat.le_succ _

theorem BorrowKind.le_join_right (a b : BorrowKind) :
    BorrowKind.le b (BorrowKind.join a b) := by
  unfold BorrowKind.le BorrowKind.join BorrowKind.rank
  cases a <;> cases b <;> dsimp only <;>
    first | exact Nat.le_refl _ | exact Nat.zero_le _ | exact Nat.le_succ _

/-- Capture kind (`ty::UpvarCapture` in `compiler/rustc_middle/src/ty/closure.rs`). -/
inductive UpvarCapture where
  | byRef (bk : BorrowKind)
  | byUse
  | byValue

noncomputable def UpvarCapture.beq : UpvarCapture → UpvarCapture → Bool
  | .byRef a, .byRef b => BorrowKind.beq a b
  | .byUse, .byUse => true
  | .byValue, .byValue => true
  | _, _ => false

theorem UpvarCapture.beq_eq {a b : UpvarCapture} (h : UpvarCapture.beq a b = true) :
    a = b := by
  cases a <;> cases b <;> first
    | rfl
    | cases h
    | (rename_i x y; have heq := BorrowKind.beq_eq h; subst heq; rfl)

noncomputable def UpvarCapture.rank : UpvarCapture → Nat
  | .byRef bk => bk.rank
  | .byUse => 3
  | .byValue => 4

noncomputable def UpvarCapture.dominates : UpvarCapture → UpvarCapture → Bool
  | .byValue, .byValue => true
  | .byValue, .byRef _ => true
  | .byValue, .byUse => true
  | .byUse, .byUse => true
  | .byUse, .byRef _ => true
  | .byRef a, .byRef b => Nat.ble b.rank a.rank
  | _, _ => false

theorem UpvarCapture.dominates_refl (c : UpvarCapture) :
    UpvarCapture.dominates c c = true := by
  cases c with
  | byRef bk => cases bk <;> rfl
  | byUse => rfl
  | byValue => rfl

theorem UpvarCapture.dominates_trans {a b c : UpvarCapture}
    (hab : UpvarCapture.dominates a b = true)
    (hbc : UpvarCapture.dominates b c = true) :
    UpvarCapture.dominates a c = true := by
  cases a with
  | byValue =>
    cases c <;> rfl
  | byUse =>
    cases b with
    | byValue => cases hab
    | byUse =>
      cases c with
      | byValue => cases hbc
      | byUse => rfl
      | byRef _ => rfl
    | byRef _ =>
      cases c with
      | byValue => cases hbc
      | byUse => cases hbc
      | byRef _ => rfl
  | byRef ba =>
    cases b with
    | byValue => cases hab
    | byUse => cases hab
    | byRef bb =>
      cases c with
      | byValue => cases hbc
      | byUse => cases hbc
      | byRef bc =>
        unfold UpvarCapture.dominates BorrowKind.rank at hab hbc ⊢
        exact (nat_ble_true_iff _ _).2
          (Nat.le_trans ((nat_ble_true_iff _ _).1 hbc) ((nat_ble_true_iff _ _).1 hab))

/-- Join two capture requirements (`determine_capture_info`, `upvar.rs:2608-2625`). -/
noncomputable def UpvarCapture.join : UpvarCapture → UpvarCapture → UpvarCapture
  | .byValue, _ | _, .byValue => .byValue
  | .byUse, _ | _, .byUse => .byUse
  | .byRef a, .byRef b => .byRef (BorrowKind.join a b)

theorem UpvarCapture.join_comm (a b : UpvarCapture) :
    UpvarCapture.join a b = UpvarCapture.join b a := by
  cases a <;> cases b <;> first
    | rfl
    | (simp only [UpvarCapture.join, BorrowKind.join_comm])

theorem UpvarCapture.join_assoc (a b c : UpvarCapture) :
    UpvarCapture.join (UpvarCapture.join a b) c =
      UpvarCapture.join a (UpvarCapture.join b c) := by
  cases a <;> cases b <;> cases c <;>
    simp only [UpvarCapture.join, BorrowKind.join_assoc]

theorem UpvarCapture.join_dominates_left (a b : UpvarCapture) :
    UpvarCapture.dominates (UpvarCapture.join a b) a = true := by
  cases a with
  | byValue => cases b <;> rfl
  | byUse => cases b <;> rfl
  | byRef ba =>
    cases b with
    | byValue => rfl
    | byUse => rfl
    | byRef bb => cases ba <;> cases bb <;> rfl

theorem UpvarCapture.join_dominates_right (a b : UpvarCapture) :
    UpvarCapture.dominates (UpvarCapture.join a b) b = true := by
  rw [UpvarCapture.join_comm]
  exact UpvarCapture.join_dominates_left b a

/-- Closure trait lattice (`ty::ClosureKind`: `Fn < FnMut < FnOnce`). -/
inductive ClosureKind where
  | fn
  | fnMut
  | fnOnce

noncomputable def ClosureKind.beq : ClosureKind → ClosureKind → Bool
  | .fn, .fn => true
  | .fnMut, .fnMut => true
  | .fnOnce, .fnOnce => true
  | _, _ => false

noncomputable def ClosureKind.rank : ClosureKind → Nat
  | .fn => 0
  | .fnMut => 1
  | .fnOnce => 2

noncomputable def ClosureKind.join : ClosureKind → ClosureKind → ClosureKind
  | .fnOnce, _ | _, .fnOnce => .fnOnce
  | .fnMut, _ | _, .fnMut => .fnMut
  | .fn, .fn => .fn

theorem ClosureKind.join_comm (a b : ClosureKind) :
    ClosureKind.join a b = ClosureKind.join b a := by
  cases a <;> cases b <;> rfl

theorem ClosureKind.join_assoc (a b c : ClosureKind) :
    ClosureKind.join (ClosureKind.join a b) c =
      ClosureKind.join a (ClosureKind.join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ClosureKind.join_fn_left (a : ClosureKind) :
    ClosureKind.join .fn a = a := by
  cases a <;> rfl

/-- Exact mapping from capture kind to minimum required `ClosureKind`
(`process_collected_capture_information`, `upvar.rs:757-781`). -/
noncomputable def UpvarCapture.toClosureKind : UpvarCapture → ClosureKind
  | .byValue => .fnOnce
  | .byUse => .fn
  | .byRef .immutable => .fn
  | .byRef .uniqueImmutable => .fnMut
  | .byRef .mutable => .fnMut

theorem UpvarCapture.toClosureKind_monotone {a b : UpvarCapture}
    (hdom : UpvarCapture.dominates a b = true)
    (hnotUse : a ≠ .byUse) :
    b.toClosureKind.rank ≤ a.toClosureKind.rank := by
  cases a with
  | byValue =>
    cases b with
    | byValue => exact Nat.le_refl _
    | byUse => exact Nat.zero_le _
    | byRef br =>
      cases br <;> dsimp only [UpvarCapture.toClosureKind, ClosureKind.rank] <;>
        first | exact Nat.zero_le _ | exact Nat.le_succ _
  | byUse => exact False.elim (hnotUse rfl)
  | byRef ba =>
    cases b with
    | byValue => cases hdom
    | byUse => cases hdom
    | byRef bb =>
      unfold UpvarCapture.dominates BorrowKind.rank at hdom
      cases ba <;> cases bb <;>
        dsimp only [UpvarCapture.toClosureKind, ClosureKind.rank] at hdom ⊢ <;>
        first | exact Nat.le_refl _ | exact Nat.zero_le _ | cases hdom

/-- Place projections (`hir::place::ProjectionKind`). -/
inductive ProjElem where
  | field (idx : Nat)
  | derefShared
  | derefMut
  | derefRaw
  | index
  | subslice
  | opaqueCast

noncomputable def ProjElem.beq : ProjElem → ProjElem → Bool
  | .field a, .field b => Nat.beq a b
  | .derefShared, .derefShared => true
  | .derefMut, .derefMut => true
  | .derefRaw, .derefRaw => true
  | .index, .index => true
  | .subslice, .subslice => true
  | .opaqueCast, .opaqueCast => true
  | _, _ => false

theorem ProjElem.beq_refl (e : ProjElem) : ProjElem.beq e e = true := by
  cases e with
  | field i => exact (nat_beq_true_iff i i).2 rfl
  | _ => rfl

theorem ProjElem.beq_eq {a b : ProjElem} (h : ProjElem.beq a b = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | cases h
    | (rename_i i j; have heq := (nat_beq_true_iff i j).1 h; subst heq; rfl)

noncomputable def ProjElem.isDeref : ProjElem → Bool
  | .derefShared | .derefMut | .derefRaw => true
  | _ => false

noncomputable def ProjElem.isMutRefDeref : ProjElem → Bool
  | .derefMut => true
  | _ => false

noncomputable def ProjElem.isSharedRefDeref : ProjElem → Bool
  | .derefShared => true
  | _ => false

structure CapturePlace where
  rootVar : Nat
  projs : List ProjElem

noncomputable def projsBeq : List ProjElem → List ProjElem → Bool
  | [], [] => true
  | x :: xs, y :: ys => ProjElem.beq x y && projsBeq xs ys
  | _, _ => false

theorem projsBeq_refl (ps : List ProjElem) : projsBeq ps ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [projsBeq, Bool.and_eq_true]
    exact ⟨ProjElem.beq_refl p, ih⟩

theorem projsBeq_eq {xs ys : List ProjElem} (h : projsBeq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      simp only [projsBeq, Bool.and_eq_true] at h
      have hxy := ProjElem.beq_eq h.1
      have htail := ih h.2
      subst hxy
      subst htail
      rfl

/-- Prefix test matching `is_ancestor_or_same_capture` (`ty/closure.rs:259-270`). -/
noncomputable def isProjPrefix : List ProjElem → List ProjElem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => ProjElem.beq x y && isProjPrefix xs ys

theorem isProjPrefix_refl (ps : List ProjElem) : isProjPrefix ps ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [isProjPrefix, Bool.and_eq_true]
    exact ⟨ProjElem.beq_refl p, ih⟩

theorem isProjPrefix_trans {a b c : List ProjElem}
    (hab : isProjPrefix a b = true) (hbc : isProjPrefix b c = true) :
    isProjPrefix a c = true := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => cases hab
    | cons y ys =>
      cases c with
      | nil => cases hbc
      | cons z zs =>
        simp only [isProjPrefix, Bool.and_eq_true] at hab hbc ⊢
        have hxy := ProjElem.beq_eq hab.1
        have hyz := ProjElem.beq_eq hbc.1
        subst hxy
        subst hyz
        exact ⟨ProjElem.beq_refl x, ih hab.2 hbc.2⟩

theorem isProjPrefix_len_le {a b : List ProjElem} (h : isProjPrefix a b = true) :
    listLength a ≤ listLength b := by
  induction a generalizing b with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      simp only [isProjPrefix, Bool.and_eq_true] at h
      exact Nat.add_le_add_right (ih h.2) 1

theorem isProjPrefix_antisymm {a b : List ProjElem}
    (hab : isProjPrefix a b = true) (hba : isProjPrefix b a = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases hba
  | cons x xs ih =>
    cases b with
    | nil => cases hab
    | cons y ys =>
      simp only [isProjPrefix, Bool.and_eq_true] at hab hba
      have hxy := ProjElem.beq_eq hab.1
      subst hxy
      have htail := ih hab.2 hba.2
      subst htail
      rfl

theorem isProjPrefix_take (n : Nat) (ps : List ProjElem) :
    isProjPrefix (listTake n ps) ps = true := by
  induction n generalizing ps with
  | zero => rfl
  | succ k ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      simp only [listTake, isProjPrefix, Bool.and_eq_true]
      exact ⟨ProjElem.beq_refl p, ih ps⟩

inductive PlaceAncestry where
  | ancestor
  | samePlace
  | descendant
  | divergent

noncomputable def PlaceAncestry.beq : PlaceAncestry → PlaceAncestry → Bool
  | .ancestor, .ancestor => true
  | .samePlace, .samePlace => true
  | .descendant, .descendant => true
  | .divergent, .divergent => true
  | _, _ => false

noncomputable def projsCompare : List ProjElem → List ProjElem → PlaceAncestry
  | [], [] => .samePlace
  | [], _ :: _ => .ancestor
  | _ :: _, [] => .descendant
  | x :: xs, y :: ys =>
    if ProjElem.beq x y then projsCompare xs ys else .divergent

/-- Exact mechanization of `determine_place_ancestry_relation` (`upvar.rs:2665-2696`). -/
noncomputable def determinePlaceAncestry (a b : CapturePlace) : PlaceAncestry :=
  if Nat.beq a.rootVar b.rootVar then projsCompare a.projs b.projs else .divergent

theorem projsCompare_ancestor_iff (xs ys : List ProjElem) :
    (projsCompare xs ys = .ancestor ∨ projsCompare xs ys = .samePlace) ↔
      isProjPrefix xs ys = true := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro _; rfl
      · intro _; exact Or.inr rfl
    | cons _ _ =>
      constructor
      · intro _; rfl
      · intro _; exact Or.inl rfl
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h
        cases h with
        | inl h1 => cases h1
        | inr h2 => cases h2
      · intro h; cases h
    | cons y ys =>
      unfold projsCompare isProjPrefix
      cases hxy : ProjElem.beq x y with
      | true =>
        simp only [ite_true, Bool.true_and]
        exact ih ys
      | false =>
        simp only [Bool.false_and]
        constructor
        · intro h
          cases h with
          | inl h1 => cases h1
          | inr h2 => cases h2
        · intro h; cases h

theorem projsCompare_descendant_iff (xs ys : List ProjElem) :
    projsCompare xs ys = .descendant ↔
      (isProjPrefix ys xs = true ∧ xs ≠ ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro h; cases h
      · intro h; exact False.elim (h.2 rfl)
    | cons _ _ =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro _; exact ⟨rfl, by intro h; cases h⟩
      · intro _; rfl
    | cons y ys =>
      unfold projsCompare isProjPrefix
      cases hxy : ProjElem.beq x y with
      | true =>
        have heq := ProjElem.beq_eq hxy
        subst heq
        rw [ProjElem.beq_refl]
        simp only [Bool.true_and, ite_true]
        have hr := ih ys
        constructor
        · intro h
          have r := hr.1 h
          exact ⟨r.1, by intro hc; cases hc; exact r.2 rfl⟩
        · intro h
          apply hr.2
          exact ⟨h.1, by intro hc; subst hc; exact h.2 rfl⟩
      | false =>
        have hyx : ProjElem.beq y x = false := by
          cases hyx' : ProjElem.beq y x with
          | false => rfl
          | true =>
            have heq := ProjElem.beq_eq hyx'
            subst heq
            rw [ProjElem.beq_refl] at hxy
            cases hxy
        rw [hyx]
        simp only [Bool.false_and]
        constructor
        · intro h; cases h
        · intro h; cases h.1

theorem projsCompare_divergent_symm (xs ys : List ProjElem) :
    projsCompare xs ys = .divergent → projsCompare ys xs = .divergent := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> intro h <;> cases h
  | cons x xs ih =>
    cases ys with
    | nil => intro h; cases h
    | cons y ys =>
      unfold projsCompare
      cases hxy : ProjElem.beq x y with
      | true =>
        have heq := ProjElem.beq_eq hxy
        subst heq
        simp only [ite_true, ProjElem.beq_refl]
        exact ih ys
      | false =>
        have hyx : ProjElem.beq y x = false := by
          cases hyx' : ProjElem.beq y x with
          | false => rfl
          | true =>
            have heq := ProjElem.beq_eq hyx'
            subst heq
            rw [ProjElem.beq_refl] at hxy
            cases hxy
        simp only [hyx]
        intro _; rfl

theorem determinePlaceAncestry_divergent_symm {a b : CapturePlace}
    (h : determinePlaceAncestry a b = .divergent) :
    determinePlaceAncestry b a = .divergent := by
  unfold determinePlaceAncestry at h ⊢
  cases hr : Nat.beq a.rootVar b.rootVar with
  | true =>
    have hre := (nat_beq_true_iff a.rootVar b.rootVar).1 hr
    rw [hre] at h ⊢
    rw [(nat_beq_true_iff b.rootVar b.rootVar).2 rfl] at h ⊢
    simp only [ite_true] at h ⊢
    exact projsCompare_divergent_symm a.projs b.projs h
  | false =>
    have hba : Nat.beq b.rootVar a.rootVar = false := by
      cases hba' : Nat.beq b.rootVar a.rootVar with
      | false => rfl
      | true =>
        have heq := (nat_beq_true_iff b.rootVar a.rootVar).1 hba'
        rw [heq] at hr
        rw [(nat_beq_true_iff a.rootVar a.rootVar).2 rfl] at hr
        cases hr
    rw [hba]
    rfl

theorem prefix_preserves_divergent {a a' b : CapturePlace}
    (hroot : a'.rootVar = a.rootVar)
    (hpref : isProjPrefix a'.projs a.projs = true)
    (hdiv : determinePlaceAncestry a' b = .divergent) :
    determinePlaceAncestry a b = .divergent := by
  unfold determinePlaceAncestry at hdiv ⊢
  rw [hroot] at hdiv
  cases hr : Nat.beq a.rootVar b.rootVar with
  | false => rfl
  | true =>
    simp only [ite_true] at hdiv ⊢
    have hgo : ∀ (pa pa' pb : List ProjElem),
        isProjPrefix pa' pa = true →
        projsCompare pa' pb = .divergent →
        projsCompare pa pb = .divergent := by
      intro pa
      induction pa with
      | nil =>
        intro pa' pb hpr hd
        cases pa' with
        | nil => cases pb <;> cases hd
        | cons _ _ => cases hpr
      | cons e1 pa1 ih =>
        intro pa' pb hpr hd
        cases pa' with
        | nil => cases pb <;> cases hd
        | cons e1' pa1' =>
          simp only [isProjPrefix, Bool.and_eq_true] at hpr
          have heq := ProjElem.beq_eq hpr.1
          subst heq
          cases pb with
          | nil => cases hd
          | cons e2 pb1 =>
            unfold projsCompare at hd ⊢
            cases h12 : ProjElem.beq e1' e2 with
            | false => rfl
            | true =>
              rw [h12] at hd
              change projsCompare pa1' pb1 = .divergent at hd
              change projsCompare pa1 pb1 = .divergent
              exact ih pa1' pb1 hpr.2 hd
    rw [hr] at hdiv
    change projsCompare a'.projs b.projs = .divergent at hdiv
    exact hgo a.projs a'.projs b.projs hpref hdiv

/-! ### Memory Disjointness & Field-Slice Non-Interference Model -/

inductive LayoutTree where
  | leaf (size : Nat)
  | struct (fields : List (Nat × LayoutTree))

mutual
  noncomputable def LayoutTree.totalSize : LayoutTree → Nat
    | .leaf s => s
    | .struct fields => LayoutTree.fieldsSize fields

  noncomputable def LayoutTree.fieldsSize : List (Nat × LayoutTree) → Nat
    | [] => 0
    | (_, sub) :: rest => sub.totalSize + LayoutTree.fieldsSize rest
end

structure ByteRange where
  offset : Nat
  size : Nat

noncomputable def rangesDisjoint (r1 r2 : ByteRange) : Prop :=
  r1.offset + r1.size ≤ r2.offset ∨ r2.offset + r2.size ≤ r1.offset

theorem rangesDisjoint_symm {r1 r2 : ByteRange} (h : rangesDisjoint r1 r2) :
    rangesDisjoint r2 r1 := by
  cases h with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2

noncomputable def rangeContained (inner outer : ByteRange) : Prop :=
  outer.offset ≤ inner.offset ∧ inner.offset + inner.size ≤ outer.offset + outer.size

theorem rangeContained_disjoint_left {a b c : ByteRange}
    (hac : rangeContained a c) (hbc : rangesDisjoint c b) :
    rangesDisjoint a b := by
  cases hbc with
  | inl hcb => exact Or.inl (nat_le_trans hac.2 hcb)
  | inr hbc' => exact Or.inr (nat_le_trans hbc' hac.1)

theorem rangeContained_disjoint_right {a b c : ByteRange}
    (hbc : rangeContained b c) (hac : rangesDisjoint a c) :
    rangesDisjoint a b :=
  rangesDisjoint_symm (rangeContained_disjoint_left hbc (rangesDisjoint_symm hac))

/-- Resolve field path `fs : List Nat` inside `LayoutTree` starting at `baseOff`. -/
noncomputable def resolveFieldList (off : Nat) :
    List (Nat × LayoutTree) → Nat → Option (ByteRange × LayoutTree)
  | [], _ => none
  | (fid, sub) :: rest, targetId =>
    if Nat.beq fid targetId then
      some ({ offset := off, size := sub.totalSize }, sub)
    else
      resolveFieldList (off + sub.totalSize) rest targetId

noncomputable def resolveFieldPath (t : LayoutTree) (off : Nat) :
    List Nat → Option ByteRange
  | [] => some { offset := off, size := t.totalSize }
  | fid :: rest =>
    match t with
    | .leaf _ => none
    | .struct fields =>
      match resolveFieldList off fields fid with
      | some (subRng, subTree) => resolveFieldPath subTree subRng.offset rest
      | none => none

theorem resolveFieldList_size_eq {off : Nat} {fields : List (Nat × LayoutTree)}
    {fid : Nat} {rng : ByteRange} {sub : LayoutTree}
    (h : resolveFieldList off fields fid = some (rng, sub)) :
    rng.size = sub.totalSize := by
  induction fields generalizing off with
  | nil => cases h
  | cons entry rest ih =>
    cases entry with
    | mk eid esub =>
      unfold resolveFieldList at h
      cases heq : Nat.beq eid fid with
      | true =>
        rw [heq] at h
        cases h
        rfl
      | false =>
        rw [heq] at h
        exact ih h

theorem resolveFieldList_bounds {off : Nat} {fields : List (Nat × LayoutTree)}
    {fid : Nat} {rng : ByteRange} {sub : LayoutTree}
    (h : resolveFieldList off fields fid = some (rng, sub)) :
    rng.offset + rng.size ≤ off + LayoutTree.fieldsSize fields ∧
      off ≤ rng.offset := by
  induction fields generalizing off with
  | nil => cases h
  | cons entry rest ih =>
    cases entry with
    | mk eid esub =>
      unfold resolveFieldList at h
      cases heq : Nat.beq eid fid with
      | true =>
        rw [heq] at h
        cases h
        dsimp only [LayoutTree.fieldsSize]
        exact ⟨nat_add_le_add_left (nat_le_add_right _ _) off, Nat.le_refl _⟩
      | false =>
        rw [heq] at h
        have r := ih h
        dsimp only [LayoutTree.fieldsSize]
        have hstep1 : rng.offset + rng.size ≤
            off + esub.totalSize + LayoutTree.fieldsSize rest := r.1
        have hstep2 :
            off + esub.totalSize + LayoutTree.fieldsSize rest =
              off + (esub.totalSize + LayoutTree.fieldsSize rest) :=
          Nat.add_assoc off esub.totalSize _
        have hle : off ≤ off + esub.totalSize := nat_le_add_right off esub.totalSize
        exact ⟨by rw [← hstep2]; exact hstep1, nat_le_trans hle r.2⟩

theorem resolveFieldPath_contained {t : LayoutTree} {off : Nat} {fs : List Nat}
    {rng : ByteRange} (h : resolveFieldPath t off fs = some rng) :
    rangeContained rng { offset := off, size := t.totalSize } := by
  induction fs generalizing t off with
  | nil =>
    cases h
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons fid rest ih =>
    cases t with
    | leaf _ => cases h
    | struct fields =>
      unfold resolveFieldPath at h
      dsimp only at h
      cases hr : resolveFieldList off fields fid with
      | none => rw [hr] at h; cases h
      | some pair =>
        rw [hr] at h
        dsimp only at h
        have hb := resolveFieldList_bounds hr
        have hsz : pair.1.size = pair.2.totalSize := resolveFieldList_size_eq hr
        have hsub := ih h
        dsimp only [LayoutTree.totalSize]
        dsimp only [rangeContained] at hsub ⊢
        rw [← hsz] at hsub
        exact ⟨nat_le_trans hb.2 hsub.1, nat_le_trans hsub.2 hb.1⟩

/-- Distinct field IDs in the same struct resolve to strictly disjoint byte ranges. -/
theorem resolveFieldList_distinct_disjoint {off : Nat}
    {fields : List (Nat × LayoutTree)} {f1 f2 : Nat}
    (hne : f1 ≠ f2) {r1 r2 : ByteRange} {t1 t2 : LayoutTree}
    (h1 : resolveFieldList off fields f1 = some (r1, t1))
    (h2 : resolveFieldList off fields f2 = some (r2, t2)) :
    rangesDisjoint r1 r2 := by
  induction fields generalizing off with
  | nil => cases h1
  | cons entry rest ih =>
    cases entry with
    | mk eid esub =>
      unfold resolveFieldList at h1 h2
      cases he1 : Nat.beq eid f1 with
      | true =>
        have heq1 := (nat_beq_true_iff eid f1).1 he1
        subst heq1
        have he2 : Nat.beq eid f2 = false := by
          cases he2' : Nat.beq eid f2 with
          | false => rfl
          | true =>
            exact False.elim (hne ((nat_beq_true_iff eid f2).1 he2'))
        rw [he1] at h1
        rw [he2] at h2
        cases h1
        have hb2 := resolveFieldList_bounds h2
        exact Or.inl hb2.2
      | false =>
        cases he2 : Nat.beq eid f2 with
        | true =>
          rw [he1] at h1
          rw [he2] at h2
          cases h2
          have hb1 := resolveFieldList_bounds h1
          exact Or.inr hb1.2
        | false =>
          rw [he1] at h1
          rw [he2] at h2
          exact ih h1 h2

noncomputable def extractFieldPath : List ProjElem → Option (List Nat)
  | [] => some []
  | .field idx :: rest =>
    match extractFieldPath rest with
    | some fs => some (idx :: fs)
    | none => none
  | _ => none

noncomputable def sliceDisjoint (root1 : Nat) (r1 : ByteRange)
    (root2 : Nat) (r2 : ByteRange) : Prop :=
  root1 ≠ root2 ∨ rangesDisjoint r1 r2

theorem divergent_field_places_disjoint
    {p1 p2 : CapturePlace} {fs1 fs2 : List Nat}
    {t : LayoutTree} {r1 r2 : ByteRange}
    (hdiv : determinePlaceAncestry p1 p2 = .divergent)
    (hf1 : extractFieldPath p1.projs = some fs1)
    (hf2 : extractFieldPath p2.projs = some fs2)
    (hr1 : resolveFieldPath t 0 fs1 = some r1)
    (hr2 : resolveFieldPath t 0 fs2 = some r2) :
    sliceDisjoint p1.rootVar r1 p2.rootVar r2 := by
  unfold determinePlaceAncestry at hdiv
  cases hroot : Nat.beq p1.rootVar p2.rootVar with
  | false =>
    left
    intro heq
    rw [heq] at hroot
    rw [(nat_beq_true_iff p2.rootVar p2.rootVar).2 rfl] at hroot
    cases hroot
  | true =>
    right
    rw [hroot] at hdiv
    clear hroot
    have hmain : ∀ (ps1 ps2 : List ProjElem) (ks1 ks2 : List Nat)
        (lt : LayoutTree) (off : Nat) (ra rb : ByteRange),
        projsCompare ps1 ps2 = .divergent →
        extractFieldPath ps1 = some ks1 →
        extractFieldPath ps2 = some ks2 →
        resolveFieldPath lt off ks1 = some ra →
        resolveFieldPath lt off ks2 = some rb →
        rangesDisjoint ra rb := by
      intro ps1
      induction ps1 with
      | nil =>
        intro ps2 _ _ _ _ _ _ hcmp
        cases ps2 <;> cases hcmp
      | cons e1 ps1' ih =>
        intro ps2 ks1 ks2 lt off ra rb hcmp he1 he2 hla hlb
        cases ps2 with
        | nil => cases hcmp
        | cons e2 ps2' =>
          cases e1 <;> first
            | cases he1
            | (rename_i f1;
               cases e2 <;> first
                 | cases he2
                 | (rename_i f2;
                    unfold extractFieldPath at he1 he2;
                    cases hf1' : extractFieldPath ps1' with
                    | none => rw [hf1'] at he1; cases he1
                    | some ks1' =>
                      cases hf2' : extractFieldPath ps2' with
                      | none => rw [hf2'] at he2; cases he2
                      | some ks2' =>
                        rw [hf1'] at he1; rw [hf2'] at he2;
                        cases he1; cases he2;
                        cases lt with
                        | leaf _ => cases hla
                        | struct fields =>
                          unfold resolveFieldPath at hla hlb;
                          dsimp only at hla hlb;
                          cases rl1 : resolveFieldList off fields f1 with
                          | none => rw [rl1] at hla; cases hla
                          | some pair1 =>
                            cases rl2 : resolveFieldList off fields f2 with
                            | none => rw [rl2] at hlb; cases hlb
                            | some pair2 =>
                              rw [rl1] at hla; rw [rl2] at hlb;
                              dsimp only at hla hlb;
                              unfold projsCompare at hcmp;
                              cases hfeq : ProjElem.beq (.field f1) (.field f2) with
                              | true =>
                                have hfe : f1 = f2 := by
                                  have pe := ProjElem.beq_eq hfeq
                                  cases pe; rfl
                                subst hfe
                                rw [rl1] at rl2
                                cases rl2
                                rw [hfeq] at hcmp
                                exact ih ps2' ks1' ks2' pair1.2 pair1.1.offset ra rb
                                  hcmp hf1' hf2' hla hlb
                              | false =>
                                have hfne : f1 ≠ f2 := by
                                  intro heq; subst heq
                                  rw [ProjElem.beq_refl] at hfeq; cases hfeq
                                have hdisj := resolveFieldList_distinct_disjoint
                                  hfne rl1 rl2
                                have hc1 := resolveFieldPath_contained hla
                                have hc2 := resolveFieldPath_contained hlb
                                rw [← resolveFieldList_size_eq rl1] at hc1
                                rw [← resolveFieldList_size_eq rl2] at hc2
                                exact rangeContained_disjoint_left hc1
                                  (rangeContained_disjoint_right hc2 hdisj)))
    exact hmain p1.projs p2.projs fs1 fs2 t 0 r1 r2 hdiv hf1 hf2 hr1 hr2

/-! ### Prefix Truncation, `truncate_capture_for_optimization`, & `MinCaptureList` -/

noncomputable def suffixHasMutRefDeref (len : Nat) (projs : List ProjElem) : Bool :=
  listAny ProjElem.isMutRefDeref (listDrop len projs)

/-- Exact mechanization of `truncate_place_to_len_and_update_capture_kind`
(`upvar.rs:2633-2658`). -/
noncomputable def truncatePlaceAndUpdateKind (p : CapturePlace)
    (k : UpvarCapture) (len : Nat) : CapturePlace × UpvarCapture :=
  let k' :=
    match k with
    | .byRef .mutable =>
      if suffixHasMutRefDeref len p.projs then .byRef .uniqueImmutable else k
    | _ => k
  ({ rootVar := p.rootVar, projs := listTake len p.projs }, k')

theorem truncatePlace_is_prefix (p : CapturePlace) (k : UpvarCapture) (len : Nat) :
    isProjPrefix (truncatePlaceAndUpdateKind p k len).1.projs p.projs = true := by
  unfold truncatePlaceAndUpdateKind
  exact isProjPrefix_take len p.projs

theorem truncatePlace_closureKind_preserved (p : CapturePlace)
    (k : UpvarCapture) (len : Nat) :
    (truncatePlaceAndUpdateKind p k len).2.toClosureKind = k.toClosureKind := by
  unfold truncatePlaceAndUpdateKind
  cases k with
  | byValue => rfl
  | byUse => rfl
  | byRef bk =>
    cases bk with
    | immutable => rfl
    | uniqueImmutable => rfl
    | mutable =>
      cases suffixHasMutRefDeref len p.projs <;> rfl

noncomputable def rightmostIdxPlus1Go (pred : ProjElem → Bool)
    (idx : Nat) (acc : Option Nat) : List ProjElem → Option Nat
  | [] => acc
  | e :: rest => rightmostIdxPlus1Go pred (idx + 1) (if pred e then some (idx + 1) else acc) rest

noncomputable def rightmostIdxPlus1 (pred : ProjElem → Bool) (ps : List ProjElem) :
    Option Nat :=
  rightmostIdxPlus1Go pred 0 none ps

noncomputable def leftmostIdxGo (pred : ProjElem → Bool) (idx : Nat) :
    List ProjElem → Option Nat
  | [] => none
  | e :: rest => if pred e then some idx else leftmostIdxGo pred (idx + 1) rest

noncomputable def leftmostIdx (pred : ProjElem → Bool) (ps : List ProjElem) :
    Option Nat :=
  leftmostIdxGo pred 0 ps

/-- Exact mechanization of `truncate_capture_for_optimization`
(`upvar.rs:2727-2747`): finds the rightmost `Deref`; if it is a shared-ref
deref (`.derefShared`), truncates right after that deref (`idx + 1`). -/
noncomputable def truncateCaptureForOptimization (p : CapturePlace)
    (k : UpvarCapture) : CapturePlace × UpvarCapture :=
  match rightmostIdxPlus1 ProjElem.isDeref p.projs with
  | some len =>
    match listNth? p.projs (len - 1) with
    | some .derefShared => truncatePlaceAndUpdateKind p k len
    | _ => (p, k)
  | none => (p, k)

theorem truncateCaptureForOptimization_is_prefix (p : CapturePlace)
    (k : UpvarCapture) :
    isProjPrefix (truncateCaptureForOptimization p k).1.projs p.projs = true := by
  unfold truncateCaptureForOptimization
  cases hr : rightmostIdxPlus1 ProjElem.isDeref p.projs with
  | none => dsimp only; exact isProjPrefix_refl p.projs
  | some len =>
    dsimp only
    cases hn : listNth? p.projs (len - 1) with
    | none => dsimp only; exact isProjPrefix_refl p.projs
    | some e =>
      cases e with
      | derefShared => exact truncatePlace_is_prefix p k len
      | _ => exact isProjPrefix_refl p.projs

/-- Exact mechanization of `restrict_capture_precision` (`upvar.rs:2378-2404`). -/
noncomputable def isRawOrArrProj : ProjElem → Bool
  | .index | .subslice | .derefRaw => true
  | _ => false

noncomputable def restrictCapturePrecision (p : CapturePlace)
    (k : UpvarCapture) : CapturePlace × UpvarCapture :=
  match leftmostIdx isRawOrArrProj p.projs with
  | some idx => truncatePlaceAndUpdateKind p k idx
  | none => (p, k)

theorem restrictCapturePrecision_is_prefix (p : CapturePlace) (k : UpvarCapture) :
    isProjPrefix (restrictCapturePrecision p k).1.projs p.projs = true := by
  unfold restrictCapturePrecision
  cases leftmostIdx isRawOrArrProj p.projs with
  | none => exact isProjPrefix_refl p.projs
  | some idx => exact truncatePlace_is_prefix p k idx

/-- Exact mechanization of `adjust_for_move_closure` (`upvar.rs:2408-2419`). -/
noncomputable def adjustForMoveClosure (p : CapturePlace)
    (k : UpvarCapture) : CapturePlace × UpvarCapture :=
  let p' :=
    match leftmostIdx ProjElem.isDeref p.projs with
    | some idx => (truncatePlaceAndUpdateKind p k idx).1
    | none => p
  (p', .byValue)

theorem adjustForMoveClosure_preserves_direct_fields (p : CapturePlace)
    (k : UpvarCapture) (hnoDeref : listAny ProjElem.isDeref p.projs = false) :
    (adjustForMoveClosure p k).1 = p ∧ (adjustForMoveClosure p k).2 = .byValue := by
  have hgo : ∀ (xs : List ProjElem) (idx : Nat),
      listAny ProjElem.isDeref xs = false →
      leftmostIdxGo ProjElem.isDeref idx xs = none := by
    intro xs
    induction xs with
    | nil => intro _ _; rfl
    | cons x xs ih =>
      intro idx hfalse
      unfold listAny at hfalse
      have hpair := bool_or_eq_false hfalse
      unfold leftmostIdxGo
      rw [hpair.1]
      exact ih (idx + 1) hpair.2
  have hleft : leftmostIdx ProjElem.isDeref p.projs = none :=
    hgo p.projs 0 hnoDeref
  unfold adjustForMoveClosure
  rw [hleft]
  exact ⟨rfl, rfl⟩

/-- Body statements driving `ExprUseVisitor` (`fake_read`, `borrow`, `consume`, `use`). -/
inductive StmtUse where
  | fakeRead (p : CapturePlace)
  | borrow (p : CapturePlace) (bk : BorrowKind)
  | consume (p : CapturePlace)
  | useCloned (p : CapturePlace)

inductive CaptureClause where
  | refClause
  | moveClause
  | useClause

noncomputable def collectEdition2021Uses :
    List StmtUse → List (CapturePlace × UpvarCapture)
  | [] => []
  | .fakeRead _ :: rest => collectEdition2021Uses rest
  | .borrow p bk :: rest => (p, .byRef bk) :: collectEdition2021Uses rest
  | .consume p :: rest => (p, .byValue) :: collectEdition2021Uses rest
  | .useCloned p :: rest => (p, .byUse) :: collectEdition2021Uses rest

theorem wildcard_fake_read_zero_capture (p : CapturePlace) (rest : List StmtUse) :
    collectEdition2021Uses (.fakeRead p :: rest) = collectEdition2021Uses rest :=
  rfl

noncomputable def adjustForClause (clause : CaptureClause)
    (p : CapturePlace) (k : UpvarCapture) : CapturePlace × UpvarCapture :=
  match clause with
  | .moveClause => adjustForMoveClosure p k
  | .useClause =>
    let p' :=
      match leftmostIdx ProjElem.isDeref p.projs with
      | some idx => (truncatePlaceAndUpdateKind p k idx).1
      | none => p
    (p', .byUse)
  | .refClause =>
    match k with
    | .byValue =>
      match leftmostIdx ProjElem.isDeref p.projs with
      | some idx => truncatePlaceAndUpdateKind p k idx
      | none => (p, .byValue)
    | .byUse => (p, .byRef .immutable)
    | .byRef _ => (p, k)

/-- Exact model of `process_collected_capture_information` (`upvar.rs:733-804`). -/
noncomputable def processCollectedCaptures (clause : CaptureClause)
    (uses : List (CapturePlace × UpvarCapture)) :
    List (CapturePlace × UpvarCapture) × ClosureKind :=
  match uses with
  | [] => ([], .fn)
  | (p, k) :: rest =>
    let (p1, k1) := restrictCapturePrecision p k
    let (p2, k2) := truncateCaptureForOptimization p1 k1
    let stepCk := k2.toClosureKind
    let (p3, k3) := adjustForClause clause p2 k2
    let (tailList, tailCk) := processCollectedCaptures clause rest
    ((p3, k3) :: tailList, ClosureKind.join stepCk tailCk)

theorem restrictCapturePrecision_imm (p : CapturePlace) :
    (restrictCapturePrecision p (.byRef .immutable)).2 = .byRef .immutable := by
  unfold restrictCapturePrecision
  cases leftmostIdx isRawOrArrProj p.projs with
  | none => rfl
  | some _ => rfl

theorem truncateCaptureForOptimization_imm (p : CapturePlace) :
    (truncateCaptureForOptimization p (.byRef .immutable)).2 = .byRef .immutable := by
  unfold truncateCaptureForOptimization
  cases hr : rightmostIdxPlus1 ProjElem.isDeref p.projs with
  | none => rfl
  | some len =>
    dsimp only
    cases hn : listNth? p.projs (len - 1) with
    | none => rfl
    | some e => cases e <;> rfl

theorem processCollectedCaptures_fn_on_reads (clause : CaptureClause)
    (uses : List (CapturePlace × UpvarCapture))
    (hallImm : listAll (fun u => match u.2 with | .byRef .immutable => true | _ => false) uses = true) :
    (processCollectedCaptures clause uses).2 = .fn := by
  induction uses with
  | nil => rfl
  | cons u rest ih =>
    cases u with
    | mk p k =>
      simp only [listAll, Bool.and_eq_true] at hallImm
      cases k with
      | byValue => cases hallImm.1
      | byUse => cases hallImm.1
      | byRef bk =>
        cases bk with
        | uniqueImmutable => cases hallImm.1
        | mutable => cases hallImm.1
        | immutable =>
          unfold processCollectedCaptures
          dsimp only
          cases hr1 : restrictCapturePrecision p (.byRef .immutable) with
          | mk p1 k1 =>
            have hk1 : k1 = .byRef .immutable := by
              have h1 := restrictCapturePrecision_imm p
              rw [hr1] at h1
              exact h1
            subst hk1
            cases hr2 : truncateCaptureForOptimization p1 (.byRef .immutable) with
            | mk p2 k2 =>
              have hk2 : k2 = .byRef .immutable := by
                have h2 := truncateCaptureForOptimization_imm p1
                rw [hr2] at h2
                exact h2
              subst hk2
              dsimp only [UpvarCapture.toClosureKind]
              rw [ClosureKind.join_fn_left]
              exact ih hallImm.2

/-- Insert one `(place, kind)` into a root-local `MinCaptureList`
(`compute_min_captures`, `upvar.rs:879-1001`). -/
noncomputable def insertMinCapture (p : CapturePlace) (k : UpvarCapture)
    (cur : List (CapturePlace × UpvarCapture)) :
    List (CapturePlace × UpvarCapture) :=
  let nonDesc := listFilter (fun e =>
    match determinePlaceAncestry p e.1 with
    | .ancestor => false
    | _ => true) cur
  let mergedK :=
    cur.foldr (fun e acc =>
      match determinePlaceAncestry p e.1 with
      | .ancestor =>
        let truncated := truncatePlaceAndUpdateKind e.1 e.2 (listLength p.projs)
        UpvarCapture.join acc truncated.2
      | _ => acc) k
  let hasAncOrSame := listAny (fun e =>
    match determinePlaceAncestry p e.1 with
    | .samePlace | .descendant => true
    | _ => false) nonDesc
  if hasAncOrSame then
    listMap (fun e =>
      match determinePlaceAncestry p e.1 with
      | .samePlace => (e.1, UpvarCapture.join e.2 mergedK)
      | .descendant =>
        let truncated := truncatePlaceAndUpdateKind p mergedK (listLength e.1.projs)
        (e.1, UpvarCapture.join e.2 truncated.2)
      | _ => e) nonDesc
  else
    (p, mergedK) :: nonDesc

noncomputable def computeMinCaptures :
    List (CapturePlace × UpvarCapture) → List (CapturePlace × UpvarCapture)
  | [] => []
  | (p, k) :: rest => insertMinCapture p k (computeMinCaptures rest)

noncomputable def captureCovers (cap target : CapturePlace × UpvarCapture) : Prop :=
  cap.1.rootVar = target.1.rootVar ∧
  isProjPrefix cap.1.projs target.1.projs = true ∧
  UpvarCapture.dominates cap.2 target.2 = true

theorem captureCovers_refl (u : CapturePlace × UpvarCapture) :
    captureCovers u u :=
  ⟨rfl, isProjPrefix_refl u.1.projs, UpvarCapture.dominates_refl u.2⟩

/-- Every entry produced by `insertMinCapture p k cur` is either `p` or an
existing element from `cur` (with updated mode) — never introducing unrelated
sibling roots or sibling fields! -/
theorem insertMinCapture_preserves_disjoint_sibling
    (p : CapturePlace) (k : UpvarCapture)
    (cur : List (CapturePlace × UpvarCapture))
    (q : CapturePlace)
    (hpq : determinePlaceAncestry p q = .divergent)
    (hcur : ∀ e, ListMem e cur → determinePlaceAncestry e.1 q = .divergent) :
    ∀ e', ListMem e' (insertMinCapture p k cur) →
      determinePlaceAncestry e'.1 q = .divergent := by
  unfold insertMinCapture
  dsimp only
  cases hasAnc : listAny _ _ with
  | false =>
    intro e' he'
    cases he' with
    | head => exact hpq
    | tail _ htail =>
      have hf := (listFilter_mem_iff).1 htail
      exact hcur e' hf.1
  | true =>
    intro e' he'
    have hmap : ∀ (mk : UpvarCapture) (xs : List (CapturePlace × UpvarCapture)),
        (∀ e, ListMem e xs → determinePlaceAncestry e.1 q = .divergent) →
        ∀ e', ListMem e' (listMap (fun e =>
          match determinePlaceAncestry p e.1 with
          | .samePlace => (e.1, UpvarCapture.join e.2 mk)
          | .descendant =>
            let truncated := truncatePlaceAndUpdateKind p mk (listLength e.1.projs)
            (e.1, UpvarCapture.join e.2 truncated.2)
          | _ => e) xs) →
        determinePlaceAncestry e'.1 q = .divergent := by
      intro mk xs hxs e1 hm1
      induction xs with
      | nil => cases hm1
      | cons x xs' ih =>
        cases hm1 with
        | head =>
          dsimp only
          have hxq := hxs x (ListMem.head x xs')
          cases determinePlaceAncestry p x.1 <;> exact hxq
        | tail _ htail =>
          exact ih (fun e he => hxs e (ListMem.tail x he)) htail
    exact hmap _ _ (fun e he => hcur e (listFilter_mem_iff.1 he).1) e' he'

theorem computeMinCaptures_preserves_disjoint_sibling
    (uses : List (CapturePlace × UpvarCapture)) (q : CapturePlace)
    (hdisj : ∀ u, ListMem u uses → determinePlaceAncestry u.1 q = .divergent) :
    ∀ c, ListMem c (computeMinCaptures uses) →
      determinePlaceAncestry c.1 q = .divergent := by
  induction uses with
  | nil =>
    intro c hc
    cases hc
  | cons u rest ih =>
    cases u with
    | mk p k =>
      unfold computeMinCaptures
      exact insertMinCapture_preserves_disjoint_sibling p k
        (computeMinCaptures rest) q
        (hdisj (p, k) (ListMem.head (p, k) rest))
        (ih (fun w hw => hdisj w (ListMem.tail (p, k) hw)))

/-- **Main Theorem 1 (RFC 2229 Disjoint-Place Non-Interference & Prefix-Truncation Soundness):**
1. Prefix-capture optimization (`truncateCaptureForOptimization`,
   `restrictCapturePrecision`) produces a prefix of the accessed place;
2. `adjustForMoveClosure` preserves all direct field projections, so
   `move || s.copy_field` captures ONLY `s.copy_field` and leaves sibling
   `s.non_copy_field` disjoint (unmoved);
3. Any two divergent direct-field places (`determinePlaceAncestry p1 p2 = .divergent`)
   occupy strictly disjoint root/byte-range slices;
4. Wildcard `let _ = p3;` (`StmtUse.fakeRead`) emits zero capture entries while
   `let _ = &p3;` (`.borrow`) emits `.byRef .immutable` and `let _x = s;`
   (`.consume`) emits `.byValue`;
5. `computeMinCaptures` preserves disjointness of every uncaptured sibling
   place `q`, and `UniqueImmutable` upgrades to `FnMut` (`toMutblLossy = .mut`). -/
theorem rfc2229_disjoint_capture_and_prefix_truncation_soundness :
    (∀ p k, isProjPrefix (truncateCaptureForOptimization p k).1.projs p.projs = true) ∧
    (∀ p k, isProjPrefix (restrictCapturePrecision p k).1.projs p.projs = true) ∧
    (∀ p k, listAny ProjElem.isDeref p.projs = false →
      (adjustForMoveClosure p k).1 = p ∧ (adjustForMoveClosure p k).2 = .byValue) ∧
    (∀ (p1 p2 : CapturePlace) (fs1 fs2 : List Nat) (t : LayoutTree) (r1 r2 : ByteRange),
      determinePlaceAncestry p1 p2 = .divergent →
      extractFieldPath p1.projs = some fs1 →
      extractFieldPath p2.projs = some fs2 →
      resolveFieldPath t 0 fs1 = some r1 →
      resolveFieldPath t 0 fs2 = some r2 →
      sliceDisjoint p1.rootVar r1 p2.rootVar r2) ∧
    (∀ p rest, collectEdition2021Uses (.fakeRead p :: rest) = collectEdition2021Uses rest) ∧
    (∀ uses q,
      (∀ u, ListMem u uses → determinePlaceAncestry u.1 q = .divergent) →
      ∀ c, ListMem c (computeMinCaptures uses) →
        determinePlaceAncestry c.1 q = .divergent) ∧
    (UpvarCapture.toClosureKind (.byRef .uniqueImmutable) = .fnMut ∧
     BorrowKind.toMutblLossy .uniqueImmutable = .mut) := by
  refine ⟨truncateCaptureForOptimization_is_prefix,
         restrictCapturePrecision_is_prefix,
         adjustForMoveClosure_preserves_direct_fields,
         ?_,
         wildcard_fake_read_zero_capture,
         computeMinCaptures_preserves_disjoint_sibling,
         ⟨rfl, rfl⟩⟩
  intro p1 p2 fs1 fs2 t r1 r2 hdiv hf1 hf2 hr1 hr2
  exact divergent_field_places_disjoint hdiv hf1 hf2 hr1 hr2

/-! ### Concrete RFC 2229 Compiler-Probe Witnesses (Verified by Kernel Reduction) -/

noncomputable def pairLayoutTree : LayoutTree :=
  .struct [(0, .leaf 4), (1, .leaf 24)]

noncomputable def placePA : CapturePlace :=
  { rootVar := 1, projs := [.field 0] }

noncomputable def placePB : CapturePlace :=
  { rootVar := 1, projs := [.field 1] }

theorem edition2024_pair_disjoint_witness :
    determinePlaceAncestry placePA placePB = .divergent :=
  rfl

theorem edition2024_pair_ranges_disjoint_witness :
    resolveFieldPath pairLayoutTree 0 [0] = some { offset := 0, size := 4 } ∧
    resolveFieldPath pairLayoutTree 0 [1] = some { offset := 4, size := 24 } :=
  ⟨rfl, rfl⟩

theorem wildcard_vs_ref_witness :
    listLength (collectEdition2021Uses [.fakeRead { rootVar := 3, projs := [] }]) = 0 ∧
    listLength (collectEdition2021Uses [.borrow { rootVar := 3, projs := [] } .immutable]) = 1 :=
  ⟨rfl, rfl⟩

theorem move_split_copy_field_witness :
    (adjustForMoveClosure { rootVar := 4, projs := [.field 0] } (.byRef .immutable)) =
      ({ rootVar := 4, projs := [.field 0] }, .byValue) ∧
    determinePlaceAncestry { rootVar := 4, projs := [.field 0] }
                           { rootVar := 4, projs := [.field 1] } = .divergent :=
  ⟨rfl, rfl⟩

theorem shared_deref_truncation_witness :
    (truncateCaptureForOptimization
      { rootVar := 5, projs := [.derefShared, .field 0] }
      (.byRef .immutable)) =
      ({ rootVar := 5, projs := [.derefShared] }, .byRef .immutable) :=
  rfl

theorem unique_immutable_truncation_witness :
    (truncatePlaceAndUpdateKind
      { rootVar := 6, projs := [.derefMut] }
      (.byRef .mutable) 0) =
      ({ rootVar := 6, projs := [] }, .byRef .uniqueImmutable) :=
  rfl

end Rfc2229Capture

/-!
## Part II: `StateTransform` Coroutine State Machine, Storage-Conflict Layout
Packing, and Self-Referential `!Unpin` Pinning Soundness

Matches `compiler/rustc_middle/src/ty/sty.rs`,
`compiler/rustc_mir_transform/src/coroutine/{mod.rs,layout.rs}`,
`compiler/rustc_middle/src/mir/query.rs`, and
`compiler/rustc_abi/src/layout/coroutine.rs`.
-/

section CoroutineStateMachine

/-- Coroutine discriminant variant tag (`ty::CoroutineArgsExt` in `sty.rs:83-144`). -/
inductive CoroVariantTag where
  | unresumed
  | returned
  | panicked
  | suspend (idx : Nat)

noncomputable def CoroVariantTag.beq : CoroVariantTag → CoroVariantTag → Bool
  | .unresumed, .unresumed => true
  | .returned, .returned => true
  | .panicked, .panicked => true
  | .suspend a, .suspend b => Nat.beq a b
  | _, _ => false

noncomputable def discrOfVariant : CoroVariantTag → Nat
  | .unresumed => 0
  | .returned => 1
  | .panicked => 2
  | .suspend k => k + 3

noncomputable def variantOfDiscr : Nat → CoroVariantTag
  | 0 => .unresumed
  | 1 => .returned
  | 2 => .panicked
  | k + 3 => .suspend k

theorem variantOfDiscr_discrOfVariant (v : CoroVariantTag) :
    variantOfDiscr (discrOfVariant v) = v := by
  cases v <;> rfl

theorem discrOfVariant_inj {v1 v2 : CoroVariantTag}
    (h : discrOfVariant v1 = discrOfVariant v2) : v1 = v2 := by
  have h1 := variantOfDiscr_discrOfVariant v1
  have h2 := variantOfDiscr_discrOfVariant v2
  rw [h] at h1
  rw [← h1, h2]

inductive CoroStepOutcome where
  | pending
  | ready (val : Nat)
  | panicReturnTrap
  | panicPoisonTrap
  | unwindPoisoned
  | unreachableUb

noncomputable def CoroStepOutcome.beq : CoroStepOutcome → CoroStepOutcome → Bool
  | .pending, .pending => true
  | .ready a, .ready b => Nat.beq a b
  | .panicReturnTrap, .panicReturnTrap => true
  | .panicPoisonTrap, .panicPoisonTrap => true
  | .unwindPoisoned, .unwindPoisoned => true
  | .unreachableUb, .unreachableUb => true
  | _, _ => false

inductive ActiveTransition where
  | yieldTo (nextSuspend : Nat) (newSaved : Nat)
  | finish (retVal : Nat)
  | unwindWithCleanup (cleanupDrops : Nat)

structure CoroSpec where
  numSuspends : Nat
  canUnwind : Bool
  asyncPanic : Bool
  unresumedDropCount : Nat
  suspendDropCounts : Nat → Nat
  stepFromUnresumed : Nat → ActiveTransition
  stepFromSuspend : Nat → Nat → ActiveTransition

structure CoroExecState where
  discr : Nat
  savedPayload : Nat
  dropsRun : Nat

/-- Operational semantics of `StateTransform::create_coroutine_resume_function`
(`coroutine/mod.rs:877-950`, `coroutine.rs:1223-1275`). -/
noncomputable def stepPoll (spec : CoroSpec) (st : CoroExecState) (resumeArg : Nat) :
    CoroStepOutcome × CoroExecState :=
  if Nat.beq st.discr 0 then
    match spec.stepFromUnresumed resumeArg with
    | .yieldTo k payload =>
      if Nat.blt k spec.numSuspends then
        (.pending, { discr := k + 3, savedPayload := payload, dropsRun := st.dropsRun })
      else
        (.unreachableUb, st)
    | .finish v =>
      (.ready v, { discr := 1, savedPayload := 0, dropsRun := st.dropsRun })
    | .unwindWithCleanup dc =>
      if spec.canUnwind then
        (.unwindPoisoned, { discr := 2, savedPayload := 0, dropsRun := st.dropsRun + dc })
      else
        (.unreachableUb, st)
  else if Nat.beq st.discr 1 then
    if spec.asyncPanic then (.panicReturnTrap, st) else (.pending, st)
  else if Nat.beq st.discr 2 then
    if spec.canUnwind then
      if spec.asyncPanic then (.panicPoisonTrap, st) else (.pending, st)
    else
      (.unreachableUb, st)
  else
    let k := st.discr - 3
    if Nat.blt k spec.numSuspends then
      match spec.stepFromSuspend k st.savedPayload with
      | .yieldTo nk payload =>
        if Nat.blt nk spec.numSuspends then
          (.pending, { discr := nk + 3, savedPayload := payload, dropsRun := st.dropsRun })
        else
          (.unreachableUb, st)
      | .finish v =>
        (.ready v, { discr := 1, savedPayload := 0, dropsRun := st.dropsRun })
      | .unwindWithCleanup dc =>
        if spec.canUnwind then
          (.unwindPoisoned, { discr := 2, savedPayload := 0, dropsRun := st.dropsRun + dc })
        else
          (.unreachableUb, st)
    else
      (.unreachableUb, st)

/-- Operational semantics of `create_coroutine_drop_shim` (`coroutine/drop.rs`). -/
noncomputable def dropCoro (spec : CoroSpec) (st : CoroExecState) : CoroExecState :=
  if Nat.beq st.discr 0 then
    { discr := 1, savedPayload := 0, dropsRun := st.dropsRun + spec.unresumedDropCount }
  else if Nat.beq st.discr 1 || Nat.beq st.discr 2 then
    st
  else
    let k := st.discr - 3
    if Nat.blt k spec.numSuspends then
      { discr := 1, savedPayload := 0, dropsRun := st.dropsRun + spec.suspendDropCounts k }
    else
      st

noncomputable def runPolls (spec : CoroSpec) (st : CoroExecState) :
    List Nat → List CoroStepOutcome × CoroExecState
  | [] => ([], st)
  | arg :: rest =>
    let (out, st1) := stepPoll spec st arg
    let (outs, stFinal) := runPolls spec st1 rest
    (out :: outs, stFinal)

theorem stepPoll_deterministic (spec : CoroSpec) (st : CoroExecState) (arg : Nat)
    {o1 o2 : CoroStepOutcome} {s1 s2 : CoroExecState}
    (h1 : stepPoll spec st arg = (o1, s1))
    (h2 : stepPoll spec st arg = (o2, s2)) :
    o1 = o2 ∧ s1 = s2 := by
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

theorem poisoned_repoll_traps (spec : CoroSpec) (st : CoroExecState) (arg : Nat)
    (hdiscr : st.discr = 2) (hunw : spec.canUnwind = true)
    (hpanic : spec.asyncPanic = true) :
    stepPoll spec st arg = (.panicPoisonTrap, st) := by
  unfold stepPoll
  rw [hdiscr, hunw, hpanic]
  rfl

theorem poisoned_repoll_trace_stays_poisoned (spec : CoroSpec)
    (args : List Nat) (st : CoroExecState)
    (hdiscr : st.discr = 2) (hunw : spec.canUnwind = true)
    (hpanic : spec.asyncPanic = true) :
    (runPolls spec st args).2 = st ∧
    listAll (fun o => CoroStepOutcome.beq o .panicPoisonTrap)
      (runPolls spec st args).1 = true := by
  induction args with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rest ih =>
    unfold runPolls
    rw [poisoned_repoll_traps spec st a hdiscr hunw hpanic]
    simp only [listAll, CoroStepOutcome.beq, Bool.true_and]
    exact ih

theorem returned_repoll_traps (spec : CoroSpec) (st : CoroExecState) (arg : Nat)
    (hdiscr : st.discr = 1) (hpanic : spec.asyncPanic = true) :
    stepPoll spec st arg = (.panicReturnTrap, st) := by
  unfold stepPoll
  rw [hdiscr, hpanic]
  rfl

theorem dropCoro_poisoned_zero_drops (spec : CoroSpec) (st : CoroExecState)
    (hdiscr : st.discr = 2) :
    dropCoro spec st = st ∧ (dropCoro spec st).dropsRun = st.dropsRun := by
  unfold dropCoro
  rw [hdiscr]
  exact ⟨rfl, rfl⟩

theorem dropCoro_returned_zero_drops (spec : CoroSpec) (st : CoroExecState)
    (hdiscr : st.discr = 1) :
    dropCoro spec st = st ∧ (dropCoro spec st).dropsRun = st.dropsRun := by
  unfold dropCoro
  rw [hdiscr]
  exact ⟨rfl, rfl⟩

theorem unwind_then_repoll_and_drop_exact_once (spec : CoroSpec)
    (st : CoroExecState) (arg1 arg2 : Nat) (dc : Nat)
    (hunw : spec.canUnwind = true) (hpanic : spec.asyncPanic = true)
    (h0 : st.discr = 0) (htrans : spec.stepFromUnresumed arg1 = .unwindWithCleanup dc) :
    let (out1, st1) := stepPoll spec st arg1
    let (out2, st2) := stepPoll spec st1 arg2
    let st3 := dropCoro spec st2
    out1 = .unwindPoisoned ∧
    st1.discr = 2 ∧
    out2 = .panicPoisonTrap ∧
    st2.discr = 2 ∧
    st3.dropsRun = st.dropsRun + dc := by
  have hstep1 : stepPoll spec st arg1 =
      (.unwindPoisoned, { discr := 2, savedPayload := 0, dropsRun := st.dropsRun + dc }) := by
    unfold stepPoll
    rw [h0, htrans, hunw]
    rfl
  dsimp only
  rw [hstep1]
  dsimp only
  have hrep := poisoned_repoll_traps spec
    { discr := 2, savedPayload := 0, dropsRun := st.dropsRun + dc } arg2 rfl hunw hpanic
  rw [hrep]
  dsimp only
  have hdrop := dropCoro_poisoned_zero_drops spec
    { discr := 2, savedPayload := 0, dropsRun := st.dropsRun + dc } rfl
  exact ⟨rfl, rfl, rfl, rfl, hdrop.2⟩

/-- **Main Theorem 2 (Coroutine State-Transition Determinism & Panic-Poisoning Re-Poll Trap Invariant).** -/
theorem coroutine_determinism_and_poison_trap_invariant :
    (∀ v, variantOfDiscr (discrOfVariant v) = v) ∧
    (∀ spec st arg o1 o2 s1 s2,
      stepPoll spec st arg = (o1, s1) →
      stepPoll spec st arg = (o2, s2) → o1 = o2 ∧ s1 = s2) ∧
    (∀ spec args st, st.discr = 2 → spec.canUnwind = true → spec.asyncPanic = true →
      (runPolls spec st args).2 = st ∧
      listAll (fun o => CoroStepOutcome.beq o .panicPoisonTrap)
        (runPolls spec st args).1 = true) ∧
    (∀ spec st, st.discr = 2 →
      dropCoro spec st = st ∧ (dropCoro spec st).dropsRun = st.dropsRun) ∧
    (∀ spec st, st.discr = 1 →
      dropCoro spec st = st ∧ (dropCoro spec st).dropsRun = st.dropsRun) :=
  ⟨variantOfDiscr_discrOfVariant,
   fun spec st arg _ _ _ _ h1 h2 => stepPoll_deterministic spec st arg h1 h2,
   fun spec args st hd hu hp => poisoned_repoll_trace_stays_poisoned spec args st hd hu hp,
   dropCoro_poisoned_zero_drops,
   dropCoro_returned_zero_drops⟩

/-! ### Storage-Conflict Graph & Variant Union Packing Safety -/

structure SavedLocalSpec where
  localId : Nat
  size : Nat
  align : Nat

structure CoroutineLayoutInput where
  discrSize : Nat
  savedLocals : List SavedLocalSpec
  variantFields : List (List Nat)
  conflicts : Nat → Nat → Bool

inductive SavedLocalElig where
  | unassigned
  | assigned (variantIdx : Nat)
  | ineligible

noncomputable def SavedLocalElig.beq : SavedLocalElig → SavedLocalElig → Bool
  | .unassigned, .unassigned => true
  | .assigned a, .assigned b => Nat.beq a b
  | .ineligible, .ineligible => true
  | _, _ => false

theorem SavedLocalElig.beq_eq {a b : SavedLocalElig}
    (h : SavedLocalElig.beq a b = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | cases h
    | (rename_i x y; have heq := (nat_beq_true_iff x y).1 h; subst heq; rfl)

noncomputable def countInVariants (l : Nat) : List (List Nat) → Nat
  | [] => 0
  | fs :: rest =>
    countInVariants l rest + (if listAny (Nat.beq l) fs then 1 else 0)

noncomputable def firstVariantIdxGo (l : Nat) (idx : Nat) : List (List Nat) → Option Nat
  | [] => none
  | fs :: rest =>
    if listAny (Nat.beq l) fs then some idx else firstVariantIdxGo l (idx + 1) rest

noncomputable def firstVariantIdx (l : Nat) (vfs : List (List Nat)) : Option Nat :=
  firstVariantIdxGo l 0 vfs

theorem listAny_beq_iff (l : Nat) (xs : List Nat) :
    listAny (Nat.beq l) xs = true ↔ ListMem l xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    unfold listAny
    cases heq : Nat.beq l y with
    | true =>
      have he := (nat_beq_true_iff l y).1 heq
      subst he
      constructor
      · intro _; exact ListMem.head l ys
      · intro _; rfl
    | false =>
      simp only [Bool.false_or]
      constructor
      · intro h; exact ListMem.tail y (ih.1 h)
      · intro h
        cases h with
        | head =>
          rw [(nat_beq_true_iff l l).2 rfl] at heq
          cases heq
        | tail _ htail => exact ih.2 htail

theorem firstVariantIdxGo_correct (l : Nat) (vfs : List (List Nat)) (base v : Nat)
    (h : firstVariantIdxGo l base vfs = some v) :
    base ≤ v ∧
    ∃ fs, listNth? vfs (v - base) = some fs ∧ ListMem l fs := by
  induction vfs generalizing base with
  | nil => cases h
  | cons fs rest ih =>
    unfold firstVariantIdxGo at h
    cases hany : listAny (Nat.beq l) fs with
    | true =>
      rw [hany] at h
      cases h
      have hsub : v - v = 0 := Nat.sub_self v
      refine ⟨Nat.le_refl v, fs, ?_, (listAny_beq_iff l fs).1 hany⟩
      rw [hsub]
      rfl
    | false =>
      rw [hany] at h
      have hr := ih (base + 1) h
      have hle : base ≤ v := nat_le_trans (nat_le_add_right base 1) hr.1
      have hsucc : v - base = (v - (base + 1)) + 1 := by
        cases hdiff : v - (base + 1) with
        | zero =>
          have hle1 : v ≤ base + 1 := Nat.le_of_sub_eq_zero hdiff
          have heqv : v = base + 1 := Nat.le_antisymm hle1 hr.1
          subst heqv
          rw [Nat.add_sub_cancel_left]
        | succ d =>
          have hadd : v = (d + 1) + (base + 1) :=
            (Nat.sub_eq_iff_eq_add hr.1).1 hdiff
          rw [hadd, Nat.add_comm (d + 1) (base + 1), Nat.add_assoc,
              Nat.add_sub_cancel_left, Nat.add_comm 1 (d + 1)]
      refine ⟨hle, ?_⟩
      cases hr.2 with
      | intro fs' hpair =>
        refine ⟨fs', ?_, hpair.2⟩
        rw [hsucc]
        exact hpair.1

theorem countInVariants_eq_one_unique {l : Nat} {vfs : List (List Nat)}
    (hcnt : countInVariants l vfs = 1) :
    ∃ v fs, listNth? vfs v = some fs ∧ ListMem l fs ∧
      ∀ v' fs', listNth? vfs v' = some fs' → ListMem l fs' → v' = v := by
  induction vfs with
  | nil => cases hcnt
  | cons fs rest ih =>
    unfold countInVariants at hcnt
    cases hany : listAny (Nat.beq l) fs with
    | true =>
      rw [hany] at hcnt
      have hrest0 : countInVariants l rest = 0 := by
        cases hcr : countInVariants l rest with
        | zero => rfl
        | succ k =>
          rw [hcr] at hcnt
          cases hcnt
      have hnoRest : ∀ v' fs', listNth? rest v' = some fs' → ¬ ListMem l fs' := by
        clear ih hcnt
        induction rest with
        | nil => intro _ _ hn; cases hn
        | cons rhd rtl ihr =>
          intro v' fs' hnth hmem
          unfold countInVariants at hrest0
          cases har : listAny (Nat.beq l) rhd with
          | true =>
            rw [har] at hrest0
            cases hrest0
          | false =>
            rw [har] at hrest0
            cases v' with
            | zero =>
              cases hnth
              have hf := (listAny_beq_iff l rhd).2 hmem
              rw [hf] at har
              cases har
            | succ k =>
              exact ihr hrest0 k fs' hnth hmem
      refine ⟨0, fs, rfl, (listAny_beq_iff l fs).1 hany, ?_⟩
      intro v' fs' hnth hmem
      cases v' with
      | zero => rfl
      | succ k => exact False.elim (hnoRest k fs' hnth hmem)
    | false =>
      rw [hany] at hcnt
      cases ih hcnt with
      | intro v hv1 =>
        cases hv1 with
        | intro fs' hpair =>
          refine ⟨v + 1, fs', hpair.1, hpair.2.1, ?_⟩
          intro v' fs'' hnth' hmem'
          cases v' with
          | zero =>
            cases hnth'
            have hf := (listAny_beq_iff l fs).2 hmem'
            rw [hf] at hany
            cases hany
          | succ k =>
            have hk := hpair.2.2 k fs'' hnth' hmem'
            rw [hk]

/-- Pass 1 of `coroutine_saved_local_eligibility` (`layout/coroutine.rs:77-96`). -/
noncomputable def pass1Elig (vfs : List (List Nat)) (l : Nat) : SavedLocalElig :=
  if Nat.beq (countInVariants l vfs) 1 then
    match firstVariantIdx l vfs with
    | some v => .assigned v
    | none => .ineligible
  else
    .ineligible

theorem pass1Elig_assigned_spec {vfs : List (List Nat)} {l v : Nat}
    (h : pass1Elig vfs l = .assigned v) :
    ∃ fs, listNth? vfs v = some fs ∧ ListMem l fs := by
  unfold pass1Elig at h
  cases hbeq : Nat.beq (countInVariants l vfs) 1 with
  | false =>
    rw [hbeq] at h
    cases h
  | true =>
    rw [hbeq] at h
    cases hfv : firstVariantIdx l vfs with
    | none => rw [hfv] at h; cases h
    | some v0 =>
      rw [hfv] at h
      cases h
      have hr := firstVariantIdxGo_correct l vfs 0 v hfv
      cases hr.2 with
      | intro fs hpair =>
        rw [Nat.sub_zero] at hpair
        exact ⟨fs, hpair.1, hpair.2⟩

theorem mem_variant_inelig_or_assigned {vfs : List (List Nat)} {l v : Nat} {fs : List Nat}
    (hnth : listNth? vfs v = some fs) (hmem : ListMem l fs) :
    pass1Elig vfs l = .assigned v ∨ pass1Elig vfs l = .ineligible := by
  unfold pass1Elig
  cases hcnt : countInVariants l vfs with
  | zero =>
    have hno : ∀ idx f, listNth? vfs idx = some f → ¬ ListMem l f := by
      clear hnth hmem
      induction vfs with
      | nil => intro _ _ hn; cases hn
      | cons x xs ih =>
        intro idx f hn hm
        unfold countInVariants at hcnt
        cases hax : listAny (Nat.beq l) x with
        | true =>
          rw [hax] at hcnt
          cases hcnt
        | false =>
          rw [hax] at hcnt
          cases idx with
          | zero =>
            cases hn
            rw [(listAny_beq_iff l x).2 hm] at hax
            cases hax
          | succ k => exact ih hcnt k f hn hm
    exact False.elim (hno v fs hnth hmem)
  | succ k =>
    cases k with
    | zero =>
      cases countInVariants_eq_one_unique hcnt with
      | intro vu hvu =>
        cases hvu with
        | intro _ huniq1 =>
          have huniq := huniq1.2.2
          cases hfv : firstVariantIdx l vfs with
          | none => exact Or.inr rfl
          | some vf =>
            have hr := firstVariantIdxGo_correct l vfs 0 vf hfv
            cases hr.2 with
            | intro fsf hpairf =>
              rw [Nat.sub_zero] at hpairf
              have hvu1 := huniq vf fsf hpairf.1 hpairf.2
              have hvu2 := huniq v fs hnth hmem
              rw [hvu1, ← hvu2]
              exact Or.inl rfl
    | succ m =>
      have hbf : Nat.beq (m + 2) 1 = false := rfl
      rw [hbf]
      exact Or.inr rfl

/-- Pass 2 of `coroutine_saved_local_eligibility` (`layout/coroutine.rs:100-125`). -/
noncomputable def crossVariantConflict (inp : CoroutineLayoutInput)
    (l1 l2 : Nat) : Bool :=
  match pass1Elig inp.variantFields l1, pass1Elig inp.variantFields l2 with
  | .assigned v1, .assigned v2 =>
    !Nat.beq v1 v2 && (inp.conflicts l1 l2 || inp.conflicts l2 l1)
  | _, _ => false

noncomputable def hasCrossConflictWinner (inp : CoroutineLayoutInput)
    (l : Nat) : Bool :=
  listAny (fun spec =>
    let l2 := spec.localId
    crossVariantConflict inp l l2 && Nat.ble l l2) inp.savedLocals

noncomputable def assignEligibility (inp : CoroutineLayoutInput) (l : Nat) :
    SavedLocalElig :=
  match pass1Elig inp.variantFields l with
  | .ineligible => .ineligible
  | .unassigned => .ineligible
  | .assigned v =>
    if hasCrossConflictWinner inp l then .ineligible else .assigned v

theorem assignEligibility_resolves_cross_variant_conflicts
    (inp : CoroutineLayoutInput) {l1 l2 : SavedLocalSpec}
    (hm1 : ListMem l1 inp.savedLocals) (hm2 : ListMem l2 inp.savedLocals)
    (hc : inp.conflicts l1.localId l2.localId = true)
    {v1 v2 : Nat}
    (ha1 : assignEligibility inp l1.localId = .assigned v1)
    (ha2 : assignEligibility inp l2.localId = .assigned v2) :
    v1 = v2 := by
  unfold assignEligibility at ha1 ha2
  cases hp1 : pass1Elig inp.variantFields l1.localId with
  | ineligible => rw [hp1] at ha1; cases ha1
  | unassigned => rw [hp1] at ha1; cases ha1
  | assigned pv1 =>
    rw [hp1] at ha1
    cases hcw1 : hasCrossConflictWinner inp l1.localId with
    | true => rw [hcw1] at ha1; cases ha1
    | false =>
      rw [hcw1] at ha1
      cases ha1
      cases hp2 : pass1Elig inp.variantFields l2.localId with
      | ineligible => rw [hp2] at ha2; cases ha2
      | unassigned => rw [hp2] at ha2; cases ha2
      | assigned pv2 =>
        rw [hp2] at ha2
        cases hcw2 : hasCrossConflictWinner inp l2.localId with
        | true => rw [hcw2] at ha2; cases ha2
        | false =>
          rw [hcw2] at ha2
          cases ha2
          cases hveq : Nat.beq v1 v2 with
          | true => exact (nat_beq_true_iff v1 v2).1 hveq
          | false =>
            cases Nat.lt_or_ge l1.localId l2.localId with
            | inl hlt =>
              have hle : Nat.ble l1.localId l2.localId = true :=
                (nat_ble_true_iff _ _).2 (Nat.le_of_lt hlt)
              have hcross : crossVariantConflict inp l1.localId l2.localId = true := by
                unfold crossVariantConflict
                rw [hp1, hp2]
                dsimp only
                rw [hveq, hc]
                rfl
              have hhit : hasCrossConflictWinner inp l1.localId = true := by
                unfold hasCrossConflictWinner
                exact (listAny_true_iff).2 ⟨l2, hm2, by dsimp only; rw [hcross, hle]; rfl⟩
              rw [hhit] at hcw1
              cases hcw1
            | inr hge =>
              have hle : Nat.ble l2.localId l1.localId = true :=
                (nat_ble_true_iff _ _).2 hge
              have hv21 : Nat.beq v2 v1 = false := by
                cases hv21' : Nat.beq v2 v1 with
                | false => rfl
                | true =>
                  have heq := (nat_beq_true_iff v2 v1).1 hv21'
                  rw [heq] at hveq
                  rw [(nat_beq_true_iff v1 v1).2 rfl] at hveq
                  cases hveq
              have hcross : crossVariantConflict inp l2.localId l1.localId = true := by
                unfold crossVariantConflict
                rw [hp2, hp1]
                dsimp only
                rw [hv21, hc]
                simp only [Bool.not_false, Bool.or_true, Bool.and_true]
              have hhit : hasCrossConflictWinner inp l2.localId = true := by
                unfold hasCrossConflictWinner
                exact (listAny_true_iff).2 ⟨l1, hm1, by dsimp only; rw [hcross, hle]; rfl⟩
              rw [hhit] at hcw2
              cases hcw2

/-- Sequential byte layout packer starting at `cursor`. -/
structure PlacedSlot where
  localId : Nat
  range : ByteRange

noncomputable def packSeqFrom (cursor : Nat) : List SavedLocalSpec → List PlacedSlot × Nat
  | [] => ([], cursor)
  | s :: rest =>
    let rng : ByteRange := { offset := cursor, size := s.size }
    let (tail, endCursor) := packSeqFrom (cursor + s.size) rest
    ({ localId := s.localId, range := rng } :: tail, endCursor)

theorem packSeqFrom_bounds {cursor : Nat} {xs : List SavedLocalSpec}
    {slots : List PlacedSlot} {endCursor : Nat}
    (hpack : packSeqFrom cursor xs = (slots, endCursor)) :
    cursor ≤ endCursor ∧
    (∀ sl, ListMem sl slots →
      cursor ≤ sl.range.offset ∧ sl.range.offset + sl.range.size ≤ endCursor) := by
  induction xs generalizing cursor slots endCursor with
  | nil =>
    cases hpack
    refine ⟨Nat.le_refl _, ?_⟩
    intro sl hmem
    cases hmem
  | cons s rest ih =>
    unfold packSeqFrom at hpack
    cases htail : packSeqFrom (cursor + s.size) rest with
    | mk tslots tend =>
      rw [htail] at hpack
      cases hpack
      have hr := ih htail
      refine ⟨nat_le_trans (nat_le_add_right cursor s.size) hr.1, ?_⟩
      intro sl hmem
      cases hmem with
      | head =>
        exact ⟨Nat.le_refl _, nat_le_trans (Nat.le_refl _) hr.1⟩
      | tail _ htm =>
        have hb := hr.2 sl htm
        exact ⟨nat_le_trans (nat_le_add_right cursor s.size) hb.1, hb.2⟩

theorem packSeqFrom_pairwise_disjoint {cursor : Nat} {xs : List SavedLocalSpec}
    (huniqIds : pairwiseDistinct (fun a b => a.localId ≠ b.localId) xs)
    {slots : List PlacedSlot} {endCursor : Nat}
    (hpack : packSeqFrom cursor xs = (slots, endCursor)) :
    ∀ s1 s2, ListMem s1 slots → ListMem s2 slots → s1.localId ≠ s2.localId →
      rangesDisjoint s1.range s2.range := by
  induction xs generalizing cursor slots endCursor with
  | nil =>
    cases hpack
    intro _ _ hm1; cases hm1
  | cons s rest ih =>
    unfold packSeqFrom at hpack
    cases htail : packSeqFrom (cursor + s.size) rest with
    | mk tslots tend =>
      rw [htail] at hpack
      cases hpack
      have hrest := ih huniqIds.2 htail
      have hbounds := packSeqFrom_bounds htail
      intro s1 s2 hm1 hm2 hne
      cases hm1 with
      | head =>
        cases hm2 with
        | head => exact False.elim (hne rfl)
        | tail _ hm2t =>
          have hb2 := hbounds.2 s2 hm2t
          exact Or.inl hb2.1
      | tail _ hm1t =>
        cases hm2 with
        | head =>
          have hb1 := hbounds.2 s1 hm1t
          exact Or.inr hb1.1
        | tail _ hm2t =>
          exact hrest s1 s2 hm1t hm2t hne

theorem packSeqFrom_maps_all {cursor : Nat} {xs : List SavedLocalSpec}
    {slots : List PlacedSlot} {endCursor : Nat}
    (hpack : packSeqFrom cursor xs = (slots, endCursor)) :
    ∀ s, ListMem s xs → ∃ sl, ListMem sl slots ∧ sl.localId = s.localId := by
  induction xs generalizing cursor slots endCursor with
  | nil =>
    cases hpack
    intro _ hm; cases hm
  | cons x rest ih =>
    unfold packSeqFrom at hpack
    cases htail : packSeqFrom (cursor + x.size) rest with
    | mk tslots tend =>
      rw [htail] at hpack
      cases hpack
      intro s hm
      cases hm with
      | head =>
        exact ⟨{ localId := x.localId, range := { offset := cursor, size := x.size } },
          ListMem.head _ _, rfl⟩
      | tail _ htailm =>
        cases ih htail s htailm with
        | intro sl hpair =>
          exact ⟨sl, ListMem.tail _ hpair.1, hpair.2⟩

noncomputable def maxEndOver (variantSlots : Nat → List PlacedSlot × Nat)
    (idx : Nat) (acc : Nat) : List (List Nat) → Nat
  | [] => acc
  | _ :: rest => maxEndOver variantSlots (idx + 1) (maxNat acc (variantSlots idx).2) rest

noncomputable def packCoroutineLayout (inp : CoroutineLayoutInput) :
    List PlacedSlot × (Nat → List PlacedSlot) × Nat :=
  let prefixSpecs :=
    listFilter (fun s => SavedLocalElig.beq (assignEligibility inp s.localId) .ineligible)
      inp.savedLocals
  let (prefixSlots, prefixEnd) := packSeqFrom inp.discrSize prefixSpecs
  let variantSlots (v : Nat) : List PlacedSlot × Nat :=
    let vSpecs :=
      listFilter (fun s => SavedLocalElig.beq (assignEligibility inp s.localId) (.assigned v))
        inp.savedLocals
    packSeqFrom prefixEnd vSpecs
  (prefixSlots, fun v => (variantSlots v).1, maxEndOver variantSlots 0 prefixEnd inp.variantFields)

theorem pairwiseDistinct_filter {α : Type} {r : α → α → Prop} {p : α → Bool}
    {xs : List α} (h : pairwiseDistinct r xs) :
    pairwiseDistinct r (listFilter p xs) := by
  induction xs with
  | nil => exact True.intro
  | cons x xs ih =>
    unfold listFilter
    cases hpx : p x with
    | false => exact ih h.2
    | true =>
      refine ⟨?_, ih h.2⟩
      intro y hy
      exact h.1 y (listFilter_mem_iff.1 hy).1

noncomputable def WellFormedCoroLayoutInput (inp : CoroutineLayoutInput) : Prop :=
  pairwiseDistinct (fun a b => a.localId ≠ b.localId) inp.savedLocals ∧
  (∀ v fs l1 l2,
    listNth? inp.variantFields v = some fs →
    ListMem l1 fs → ListMem l2 fs → l1 ≠ l2 →
    inp.conflicts l1 l2 = true) ∧
  (∀ v fs l,
    listNth? inp.variantFields v = some fs →
    ListMem l fs →
    ∃ s, ListMem s inp.savedLocals ∧ s.localId = l)

noncomputable def findPlacedSlot (lid : Nat) : List PlacedSlot → Option PlacedSlot
  | [] => none
  | sl :: rest => if Nat.beq sl.localId lid then some sl else findPlacedSlot lid rest

theorem findPlacedSlot_correct {slots : List PlacedSlot} {lid : Nat} {sl : PlacedSlot}
    (hf : findPlacedSlot lid slots = some sl) :
    ListMem sl slots ∧ sl.localId = lid := by
  induction slots with
  | nil => cases hf
  | cons x rest ih =>
    unfold findPlacedSlot at hf
    cases hbeq : Nat.beq x.localId lid with
    | true =>
      rw [hbeq] at hf
      have hid := (nat_beq_true_iff x.localId lid).1 hbeq
      cases hf
      exact ⟨ListMem.head _ rest, hid⟩
    | false =>
      rw [hbeq] at hf
      have r := ih hf
      exact ⟨ListMem.tail x r.1, r.2⟩

theorem findPlacedSlot_exists_of_mem {slots : List PlacedSlot} {lid : Nat}
    (hex : ∃ sl, ListMem sl slots ∧ sl.localId = lid) :
    ∃ sl, findPlacedSlot lid slots = some sl ∧
      ListMem sl slots ∧ sl.localId = lid := by
  induction slots with
  | nil =>
    cases hex with
    | intro _ hpair => cases hpair.1
  | cons x rest ih =>
    unfold findPlacedSlot
    cases hbeq : Nat.beq x.localId lid with
    | true =>
      exact ⟨x, rfl, ListMem.head x rest, (nat_beq_true_iff x.localId lid).1 hbeq⟩
    | false =>
      have hexRest : ∃ sl, ListMem sl rest ∧ sl.localId = lid := by
        cases hex with
        | intro sl hpair =>
          cases hpair.1 with
          | head =>
            rw [hpair.2, (nat_beq_true_iff lid lid).2 rfl] at hbeq
            cases hbeq
          | tail _ htail => exact ⟨sl, htail, hpair.2⟩
      cases ih hexRest with
      | intro sl hres =>
        exact ⟨sl, hres.1, ListMem.tail x hres.2.1, hres.2.2⟩

noncomputable def assignedSlotFor (inp : CoroutineLayoutInput) (s : SavedLocalSpec) :
    Option PlacedSlot :=
  let prefixSpecs :=
    listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) .ineligible)
      inp.savedLocals
  let (prefixSlots, prefixEnd) := packSeqFrom inp.discrSize prefixSpecs
  match assignEligibility inp s.localId with
  | .ineligible => findPlacedSlot s.localId prefixSlots
  | .assigned v =>
    let vSpecs :=
      listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) (.assigned v))
        inp.savedLocals
    let (vSlots, _) := packSeqFrom prefixEnd vSpecs
    findPlacedSlot s.localId vSlots
  | .unassigned => none

theorem assignedSlotFor_total (inp : CoroutineLayoutInput) {s : SavedLocalSpec}
    (hm : ListMem s inp.savedLocals) :
    ∃ sl, assignedSlotFor inp s = some sl ∧ sl.localId = s.localId ∧
      inp.discrSize ≤ sl.range.offset := by
  unfold assignedSlotFor
  dsimp only
  let prefixSpecs :=
    listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) .ineligible)
      inp.savedLocals
  cases hpackP : packSeqFrom inp.discrSize prefixSpecs with
  | mk prefixSlots prefixEnd =>
    dsimp only
    cases helig : assignEligibility inp s.localId with
    | unassigned =>
      unfold assignEligibility at helig
      cases hp : pass1Elig inp.variantFields s.localId with
      | ineligible => rw [hp] at helig; cases helig
      | unassigned => rw [hp] at helig; cases helig
      | assigned v =>
        rw [hp] at helig
        cases hcw : hasCrossConflictWinner inp s.localId with
        | true => rw [hcw] at helig; cases helig
        | false => rw [hcw] at helig; cases helig
    | ineligible =>
      have hmf : ListMem s prefixSpecs :=
        listFilter_mem_iff.2 ⟨hm, by rw [helig]; rfl⟩
      have hex := packSeqFrom_maps_all hpackP s hmf
      cases findPlacedSlot_exists_of_mem hex with
      | intro sl hsl =>
        have hbounds := packSeqFrom_bounds hpackP
        exact ⟨sl, hsl.1, hsl.2.2, (hbounds.2 sl hsl.2.1).1⟩
    | assigned v =>
      dsimp only
      let vSpecs :=
        listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) (.assigned v))
          inp.savedLocals
      have hmf : ListMem s vSpecs :=
        listFilter_mem_iff.2 ⟨hm, by rw [helig]; exact (nat_beq_true_iff v v).2 rfl⟩
      cases hpackV : packSeqFrom prefixEnd vSpecs with
      | mk vSlots vEnd =>
        dsimp only
        have hex := packSeqFrom_maps_all hpackV s hmf
        cases findPlacedSlot_exists_of_mem hex with
        | intro sl hsl =>
          have hbP := packSeqFrom_bounds hpackP
          have hbV := packSeqFrom_bounds hpackV
          exact ⟨sl, hsl.1, hsl.2.2, nat_le_trans hbP.1 (hbV.2 sl hsl.2.1).1⟩

/-- **Main Theorem 3 (Conflict-Graph Non-Overlapping Storage Packing Safety):**
For ANY well-formed `CoroutineLayoutInput` and ANY two distinct saved locals
`s1, s2 ∈ savedLocals` that conflict (`inp.conflicts s1.localId s2.localId = true`),
and therefore in particular ANY two distinct locals simultaneously live at ANY
suspend point `v`, their assigned byte intervals in `packCoroutineLayout` are
strictly disjoint (`rangesDisjoint sl1.range sl2.range`) and disjoint from the
discriminant (`inp.discrSize ≤ offset`). -/
theorem conflict_graph_non_overlapping_packing_safety
    (inp : CoroutineLayoutInput) (hwf : WellFormedCoroLayoutInput inp)
    {s1 s2 : SavedLocalSpec}
    (hm1 : ListMem s1 inp.savedLocals) (hm2 : ListMem s2 inp.savedLocals)
    (hne : s1.localId ≠ s2.localId)
    (hconf : inp.conflicts s1.localId s2.localId = true) :
    ∃ sl1 sl2,
      assignedSlotFor inp s1 = some sl1 ∧
      assignedSlotFor inp s2 = some sl2 ∧
      inp.discrSize ≤ sl1.range.offset ∧
      inp.discrSize ≤ sl2.range.offset ∧
      rangesDisjoint sl1.range sl2.range := by
  cases assignedSlotFor_total inp hm1 with
  | intro sl1 hres1 =>
    cases assignedSlotFor_total inp hm2 with
    | intro sl2 hres2 =>
      have has1 := hres1.1
      have hid1 := hres1.2.1
      have hge1 := hres1.2.2
      have has2 := hres2.1
      have hid2 := hres2.2.1
      have hge2 := hres2.2.2
      refine ⟨sl1, sl2, has1, has2, hge1, hge2, ?_⟩
      let prefixSpecs :=
        listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) .ineligible)
          inp.savedLocals
      cases hpackP : packSeqFrom inp.discrSize prefixSpecs with
      | mk prefixSlots prefixEnd =>
        have hboundsP := packSeqFrom_bounds hpackP
        have huniqP : pairwiseDistinct (fun a b => a.localId ≠ b.localId) prefixSpecs :=
          pairwiseDistinct_filter hwf.1
        have hdisjP := packSeqFrom_pairwise_disjoint huniqP hpackP
        cases he1 : assignEligibility inp s1.localId with
        | unassigned =>
          unfold assignedSlotFor at has1
          dsimp only at has1
          rw [hpackP, he1] at has1
          cases has1
        | ineligible =>
          unfold assignedSlotFor at has1
          dsimp only at has1
          rw [hpackP, he1] at has1
          dsimp only at has1
          have hmsl1 := (findPlacedSlot_correct has1).1
          cases he2 : assignEligibility inp s2.localId with
          | unassigned =>
            unfold assignedSlotFor at has2
            dsimp only at has2
            rw [hpackP, he2] at has2
            cases has2
          | ineligible =>
            unfold assignedSlotFor at has2
            dsimp only at has2
            rw [hpackP, he2] at has2
            dsimp only at has2
            have hmsl2 := (findPlacedSlot_correct has2).1
            have hids : sl1.localId ≠ sl2.localId := by rw [hid1, hid2]; exact hne
            exact hdisjP sl1 sl2 hmsl1 hmsl2 hids
          | assigned v2 =>
            unfold assignedSlotFor at has2
            dsimp only at has2
            rw [hpackP, he2] at has2
            dsimp only at has2
            let v2Specs :=
              listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) (.assigned v2))
                inp.savedLocals
            cases hpackV2 : packSeqFrom prefixEnd v2Specs with
            | mk v2Slots v2End =>
              rw [hpackV2] at has2
              dsimp only at has2
              have hmsl2 := (findPlacedSlot_correct has2).1
              have hb1 := hboundsP.2 sl1 hmsl1
              have hb2 := (packSeqFrom_bounds hpackV2).2 sl2 hmsl2
              exact Or.inl (nat_le_trans hb1.2 hb2.1)
        | assigned v1 =>
          unfold assignedSlotFor at has1
          dsimp only at has1
          rw [hpackP, he1] at has1
          dsimp only at has1
          let v1Specs :=
            listFilter (fun x => SavedLocalElig.beq (assignEligibility inp x.localId) (.assigned v1))
              inp.savedLocals
          cases hpackV1 : packSeqFrom prefixEnd v1Specs with
          | mk v1Slots v1End =>
            rw [hpackV1] at has1
            dsimp only at has1
            have hmsl1 := (findPlacedSlot_correct has1).1
            cases he2 : assignEligibility inp s2.localId with
            | unassigned =>
              unfold assignedSlotFor at has2
              dsimp only at has2
              rw [hpackP, he2] at has2
              cases has2
            | ineligible =>
              unfold assignedSlotFor at has2
              dsimp only at has2
              rw [hpackP, he2] at has2
              dsimp only at has2
              have hmsl2 := (findPlacedSlot_correct has2).1
              have hb1 := (packSeqFrom_bounds hpackV1).2 sl1 hmsl1
              have hb2 := hboundsP.2 sl2 hmsl2
              exact Or.inr (nat_le_trans hb2.2 hb1.1)
            | assigned v2 =>
              have hveq : v1 = v2 :=
                assignEligibility_resolves_cross_variant_conflicts inp hm1 hm2 hconf he1 he2
              subst hveq
              unfold assignedSlotFor at has2
              dsimp only at has2
              rw [hpackP, he2] at has2
              dsimp only at has2
              rw [hpackV1] at has2
              dsimp only at has2
              have hmsl2 := (findPlacedSlot_correct has2).1
              have huniqV : pairwiseDistinct (fun a b => a.localId ≠ b.localId) v1Specs :=
                pairwiseDistinct_filter hwf.1
              have hdisjV := packSeqFrom_pairwise_disjoint huniqV hpackV1
              have hids : sl1.localId ≠ sl2.localId := by rw [hid1, hid2]; exact hne
              exact hdisjV sl1 sl2 hmsl1 hmsl2 hids

theorem colive_at_suspend_non_overlapping
    (inp : CoroutineLayoutInput) (hwf : WellFormedCoroLayoutInput inp)
    {v : Nat} {fs : List Nat} {l1 l2 : Nat}
    (hv : listNth? inp.variantFields v = some fs)
    (hm1 : ListMem l1 fs) (hm2 : ListMem l2 fs) (hne : l1 ≠ l2) :
    ∃ s1 s2 sl1 sl2,
      ListMem s1 inp.savedLocals ∧ s1.localId = l1 ∧
      ListMem s2 inp.savedLocals ∧ s2.localId = l2 ∧
      assignedSlotFor inp s1 = some sl1 ∧
      assignedSlotFor inp s2 = some sl2 ∧
      rangesDisjoint sl1.range sl2.range := by
  cases hwf.2.2 v fs l1 hv hm1 with
  | intro s1 hs1 =>
    cases hwf.2.2 v fs l2 hv hm2 with
    | intro s2 hs2 =>
      have hconf : inp.conflicts s1.localId s2.localId = true := by
        rw [hs1.2, hs2.2]
        exact hwf.2.1 v fs l1 l2 hv hm1 hm2 hne
      have hnes : s1.localId ≠ s2.localId := by rw [hs1.2, hs2.2]; exact hne
      cases conflict_graph_non_overlapping_packing_safety inp hwf hs1.1 hs2.1 hnes hconf with
      | intro sl1 hsl1 =>
        cases hsl1 with
        | intro sl2 hsl2 =>
          exact ⟨s1, s2, sl1, sl2, hs1.1, hs1.2, hs2.1, hs2.2,
            hsl2.1, hsl2.2.1, hsl2.2.2.2.2⟩

/-! ### Concrete Layout Compression Witnesses (`seq` 67 B vs `ovl` 131 B) -/

noncomputable def seqCoroInput : CoroutineLayoutInput :=
  { discrSize := 1
    savedLocals :=
      [ { localId := 0, size := 1, align := 1 }
      , { localId := 1, size := 64, align := 1 }
      , { localId := 2, size := 1, align := 1 }
      , { localId := 3, size := 64, align := 1 }
      , { localId := 4, size := 1, align := 1 } ]
    variantFields := [[], [], [], [1, 2], [0, 3, 4]]
    conflicts := fun a b =>
      (Nat.beq a b) ||
      ((Nat.beq a 0) && (Nat.beq b 1 || Nat.beq b 3 || Nat.beq b 4)) ||
      ((Nat.beq b 0) && (Nat.beq a 1 || Nat.beq a 3 || Nat.beq a 4)) ||
      ((Nat.beq a 1) && (Nat.beq b 2)) || ((Nat.beq b 1) && (Nat.beq a 2)) ||
      ((Nat.beq a 3) && (Nat.beq b 4)) || ((Nat.beq b 3) && (Nat.beq a 4)) }

noncomputable def ovlCoroInput : CoroutineLayoutInput :=
  { discrSize := 1
    savedLocals :=
      [ { localId := 0, size := 64, align := 1 }
      , { localId := 1, size := 64, align := 1 }
      , { localId := 2, size := 1, align := 1 }
      , { localId := 3, size := 1, align := 1 }
      , { localId := 4, size := 1, align := 1 } ]
    variantFields := [[], [], [], [0, 1, 2], [0, 1, 3, 4]]
    conflicts := fun a b =>
      (Nat.beq a b) ||
      ((Nat.beq a 0 || Nat.beq a 1) && true) ||
      ((Nat.beq b 0 || Nat.beq b 1) && true) ||
      ((Nat.beq a 3) && (Nat.beq b 4)) || ((Nat.beq b 3) && (Nat.beq a 4)) }

theorem seq_coro_overlap_packing_witness :
    (packCoroutineLayout seqCoroInput).2.2 = 67 ∧
    assignedSlotFor seqCoroInput { localId := 1, size := 64, align := 1 } =
      some { localId := 1, range := { offset := 2, size := 64 } } ∧
    assignedSlotFor seqCoroInput { localId := 3, size := 64, align := 1 } =
      some { localId := 3, range := { offset := 2, size := 64 } } := by
  exact ⟨rfl, rfl, rfl⟩

theorem ovl_coro_full_conflict_witness :
    (packCoroutineLayout ovlCoroInput).2.2 = 131 ∧
    assignedSlotFor ovlCoroInput { localId := 0, size := 64, align := 1 } =
      some { localId := 0, range := { offset := 1, size := 64 } } ∧
    assignedSlotFor ovlCoroInput { localId := 1, size := 64, align := 1 } =
      some { localId := 1, range := { offset := 65, size := 64 } } := by
  exact ⟨rfl, rfl, rfl⟩

end CoroutineStateMachine

/-!
## Part III: Self-Referential Pinning Preservation (`!Unpin` Stable Base Address
Invariant Across Resumes)
-/

section SelfRefPinning

structure PinCoroMem where
  baseAddr : Nat
  frameSize : Nat
  unpinFlag : Bool
  pinned : Bool
  dropped : Bool
  selfRefTargetOff : Option Nat
  storedSelfPtr : Option Nat

noncomputable def selfRefValid (m : PinCoroMem) : Prop :=
  ¬ m.dropped ∧
  match m.selfRefTargetOff, m.storedSelfPtr with
  | none, none => True
  | some off, some ptr => off < m.frameSize ∧ ptr = m.baseAddr + off
  | _, _ => False

inductive PinAction where
  | pinFrame
  | initSelfRef (targetOff : Nat)
  | pollResume
  | safeMutMove (newBase : Nat)
  | dropFrame

noncomputable def execPinAction (m : PinCoroMem) : PinAction → Option PinCoroMem
  | .pinFrame =>
    if m.dropped then none
    else some { m with pinned := true }
  | .initSelfRef off =>
    if m.dropped || !m.pinned || !Nat.blt off m.frameSize then none
    else some
      { m with
        selfRefTargetOff := some off
        storedSelfPtr := some (m.baseAddr + off) }
  | .pollResume =>
    if m.dropped || !m.pinned then none
    else some m
  | .safeMutMove newBase =>
    if m.dropped then none
    else if m.pinned && !m.unpinFlag then none
    else some { m with baseAddr := newBase }
  | .dropFrame =>
    if m.dropped then none
    else some { m with dropped := true, selfRefTargetOff := none, storedSelfPtr := none }

noncomputable def execPinTrace (m : PinCoroMem) : List PinAction → Option PinCoroMem
  | [] => some m
  | act :: rest =>
    match execPinAction m act with
    | none => none
    | some m' => execPinTrace m' rest

noncomputable def isNonDropSafeAction : PinAction → Bool
  | .dropFrame => false
  | _ => true

theorem pin_action_preserves_not_unpin_invariant {m m' : PinCoroMem} {act : PinAction}
    (hunpin : m.unpinFlag = false)
    (hpinned : m.pinned = true)
    (hvalid : selfRefValid m)
    (hsafe : isNonDropSafeAction act = true)
    (hstep : execPinAction m act = some m') :
    m'.baseAddr = m.baseAddr ∧
    m'.unpinFlag = false ∧
    m'.pinned = true ∧
    selfRefValid m' := by
  cases act with
  | dropFrame => cases hsafe
  | pinFrame =>
    dsimp only [execPinAction] at hstep
    cases hd : m.dropped with
    | true => rw [hd] at hstep; cases hstep
    | false =>
      rw [hd] at hstep
      cases hstep
      refine ⟨rfl, hunpin, rfl, (fun hc => by cases hc), hvalid.2⟩
  | initSelfRef off =>
    dsimp only [execPinAction] at hstep
    cases hd : m.dropped with
    | true => rw [hd] at hstep; cases hstep
    | false =>
      rw [hd, hpinned] at hstep
      cases hlt : Nat.blt off m.frameSize with
      | false => rw [hlt] at hstep; cases hstep
      | true =>
        rw [hlt] at hstep
        cases hstep
        refine ⟨rfl, hunpin, rfl, (fun hc => by cases hc), ?_⟩
        exact ⟨(nat_blt_true_iff off m.frameSize).1 hlt, rfl⟩
  | pollResume =>
    dsimp only [execPinAction] at hstep
    cases hd : m.dropped with
    | true => rw [hd] at hstep; cases hstep
    | false =>
      rw [hd, hpinned] at hstep
      cases hstep
      exact ⟨rfl, hunpin, hpinned, hvalid⟩
  | safeMutMove newBase =>
    dsimp only [execPinAction] at hstep
    rw [hunpin, hpinned] at hstep
    cases hd : m.dropped with
    | true => rw [hd] at hstep; cases hstep
    | false =>
      rw [hd] at hstep
      cases hstep

/-- **Main Theorem 4 (Self-Referential Pinning Preservation — `!Unpin` Stable Base
Address Invariant Across Resumes):**
For any reachable execution trace of non-drop safe operations on a pinned `!Unpin`
coroutine (`unpinFlag = false`, `pinned = true`),
1. `baseAddr` is strictly invariant across arbitrary sequences of `pollResume`
   and `initSelfRef` operations;
2. `selfRefValid` (every stored self-pointer equals `baseAddr + off` inside the
   live frame) holds at the final state;
3. Any attempt to move/relocate (`safeMutMove`) a pinned `!Unpin` coroutine
   fails closed (`none`);
4. Negative witness: forging `unpinFlag = true` (`impl Unpin`) admits a 2-step
   safe trace (`initSelfRef -> safeMutMove`) that breaks `selfRefValid`. -/
theorem self_referential_pinning_stability_invariant
    (m m' : PinCoroMem) (trace : List PinAction)
    (hunpin : m.unpinFlag = false)
    (hpinned : m.pinned = true)
    (hvalid : selfRefValid m)
    (hallSafe : listAll isNonDropSafeAction trace = true)
    (htrace : execPinTrace m trace = some m') :
    m'.baseAddr = m.baseAddr ∧
    m'.unpinFlag = false ∧
    m'.pinned = true ∧
    selfRefValid m' := by
  induction trace generalizing m with
  | nil =>
    cases htrace
    exact ⟨rfl, hunpin, hpinned, hvalid⟩
  | cons act rest ih =>
    simp only [listAll, Bool.and_eq_true] at hallSafe
    unfold execPinTrace at htrace
    cases hstep : execPinAction m act with
    | none => rw [hstep] at htrace; cases htrace
    | some m1 =>
      rw [hstep] at htrace
      have h1 := pin_action_preserves_not_unpin_invariant
        hunpin hpinned hvalid hallSafe.1 hstep
      have htail := ih m1 h1.2.1 h1.2.2.1 h1.2.2.2 hallSafe.2 htrace
      exact ⟨htail.1.trans h1.1, htail.2.1, htail.2.2.1, htail.2.2.2⟩

theorem forged_unpin_breaks_self_ref_witness :
    let m0 : PinCoroMem :=
      { baseAddr := 0x1000
        frameSize := 80
        unpinFlag := true
        pinned := true
        dropped := false
        selfRefTargetOff := none
        storedSelfPtr := none }
    ∃ mFinal,
      execPinTrace m0 [.initSelfRef 0, .safeMutMove 0x2000] = some mFinal ∧
      mFinal.storedSelfPtr = some 0x1000 ∧
      mFinal.baseAddr = 0x2000 ∧
      ¬ selfRefValid mFinal := by
  refine ⟨{ baseAddr := 0x2000
            frameSize := 80
            unpinFlag := true
            pinned := true
            dropped := false
            selfRefTargetOff := some 0
            storedSelfPtr := some 0x1000 }, rfl, rfl, rfl, ?_⟩
  intro hbad
  have hptr : 0x1000 = 0x2000 + 0 := hbad.2.2
  have hneq : Nat.beq 0x1000 (0x2000 + 0) = false := rfl
  have hbeq : Nat.beq 0x1000 (0x2000 + 0) = true := (nat_beq_true_iff _ _).2 hptr
  rw [hneq] at hbeq
  cases hbeq

end SelfRefPinning

end ClosureRfc2229AndCoroutineLayout
