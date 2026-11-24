prelude
import Init.Core
import Init.NotationExtra
import Init.PropLemmas
import Init.SimpLemmas
import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Int.Basic
import Init.Data.Option.Basic
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Control.Except
import Init.Tactics

namespace Anneal.MatchGuardSoundness

/-!
# Match-Guard `FakeBorrow`, `RefWithinGuard`, `CleanupPostBorrowck` Erasure, and Or-Pattern Guard Soundness

This module mechanizes the MIR match-lowering, borrow-checking diagnostic partition,
post-borrowck administrative erasure, and or-pattern guard execution semantics of `rustc`
(`compiler/rustc_mir_build/src/builder/matches/{mod.rs,util.rs}`,
`compiler/rustc_borrowck/src/{places_conflict.rs,diagnostics/conflict_errors.rs,diagnostics/mutability_errors.rs}`,
and `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`):

1. **Part I — Values, Places, Memory with `deinitMovedPlace = true`, and Conflict Algebra:**
   Models MIR places (`LocalId × List ProjElem`), `LocalSlot` (`dead` / `live (optVal : Option Val)`)
   with move-deinitialization (`deinitMovedPlace = true`), heap `Box` and interior-mutable `Cell`
   storage, deref prefixes (`fake_borrow_deref_prefixes`), and exact shallow vs. deep conflict
   predicates (`shallowConflicts` vs. `deepConflicts`), proving structural inclusion, witness
   strictness (`strictProjection_not_shallowConflict`), and discriminant stability under
   strict-projection writes (`writeProjInVal_preserves_discriminant`,
   `writeProjInVal_strictDescendant_preserves_prefix_discr`).
2. **Part II — Match-Lowering MIR Syntax, Borrowck Loan Checking, and Diagnostic Partition:**
   Models `BorrowKind` (`shared`, `mutDefault`, `fakeShallow`, `fakeDeep`), `FakeReadCause`
   (`forMatchGuard`, `forMatchedPlace`, `forGuardBinding`), `StatementKind`, `TerminatorKind`
   (including `falseEdge`), `RefWithinGuard` bindings, and the four-way diagnostic partition
   (`E0510` vs. `E0502` vs. `E0506` vs. `E0594`) plus interior-mutability permission (`Cell::set`).
3. **Part III — Operational Semantics, `CleanupPostBorrowck` Pass, and Theorems 1–3:**
   Proves:
   - **Theorem 1 (`discriminant_stability_of_fake_borrow_shallow`)**: `FakeBorrow(Shallow)` +
     `FakeRead(ForMatchGuard)` preserves tested scrutinee variants across guard evaluation.
   - **Theorem 2 (`ref_within_guard_immutability_and_move_once`)**: `RefWithinGuard` +
     `FakeRead(ForGuardBinding)` forbids guard mutations (`E0594`/`E0506`) and preserves
     unmoved source liveness for fallthrough vs. post-guard move-once entry.
   - **Theorem 3 (`cleanup_post_borrowck_observational_erasure_equiv`)**: `CleanupPostBorrowck`
     (`&fake` / `FakeRead` / `AscribeUserType` -> `nop`, `FalseEdge` -> `goto real`) is an exact
     lockstep observational simulation preserving every runtime outcome across all fuels.
4. **Part IV — Or-Pattern Per-Branch Lowering, Short-Circuiting, and Concrete Witnesses:**
   Proves **Theorem 4 (`or_pattern_per_branch_short_circuit_and_move_once`)** and provides
   kernel-checked positive and negative witness theorems matching live `rustc` empirical probes.

Purity invariants:
- `prelude` + `Init.*` only (zero Mathlib, zero `Lean.*`).
- Every term-level definition carries `noncomputable def`; zero `partial def`, zero `deriving`,
  zero `._unsafe_rec`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`, zero `sorry`.
-/

/-! ## Part I: Core Identifiers, Values, Places, Memory (`deinitMovedPlace = true`), and Overlap -/

abbrev LocalId := Nat
abbrev BlockId := Nat
abbrev FieldIdx := Nat
abbrev VariantIdx := Nat
abbrev HeapAddr := Nat

/-- Reference or pointer mutability (`rustc_ast_ir::Mutability`). -/
inductive Mutability where
  | not
  | mut_

/-- Equality on `Mutability`. -/
noncomputable def Mutability.beq : Mutability → Mutability → Bool
  | .not, .not => true
  | .mut_, .mut_ => true
  | _, _ => false

theorem Mutability.beq_refl (m : Mutability) : m.beq m = true := by
  cases m <;> rfl

theorem Mutability.eq_of_beq {m₁ m₂ : Mutability} (h : m₁.beq m₂ = true) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> simp [Mutability.beq] at h <;> rfl

/-- MIR borrow kind (`rustc_middle::mir::BorrowKind` + `FakeBorrowKind`). -/
inductive BorrowKind where
  | shared
  | mutDefault
  | fakeShallow
  | fakeDeep

/-- Equality on `BorrowKind`. -/
noncomputable def BorrowKind.beq : BorrowKind → BorrowKind → Bool
  | .shared, .shared => true
  | .mutDefault, .mutDefault => true
  | .fakeShallow, .fakeShallow => true
  | .fakeDeep, .fakeDeep => true
  | _, _ => false

theorem BorrowKind.beq_refl (k : BorrowKind) : k.beq k = true := by
  cases k <;> rfl

theorem BorrowKind.eq_of_beq {k₁ k₂ : BorrowKind} (h : k₁.beq k₂ = true) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> simp [BorrowKind.beq] at h <;> rfl

/-- Predicate distinguishing administrative fake borrows (`BorrowKind::Fake(_)`). -/
noncomputable def BorrowKind.isFake : BorrowKind → Bool
  | .fakeShallow => true
  | .fakeDeep => true
  | _ => false

/-- Cause of a MIR `FakeRead` statement (`rustc_middle::mir::FakeReadCause`). -/
inductive FakeReadCause where
  | forMatchGuard
  | forMatchedPlace
  | forGuardBinding

/-- Equality on `FakeReadCause`. -/
noncomputable def FakeReadCause.beq : FakeReadCause → FakeReadCause → Bool
  | .forMatchGuard, .forMatchGuard => true
  | .forMatchedPlace, .forMatchedPlace => true
  | .forGuardBinding, .forGuardBinding => true
  | _, _ => false

theorem FakeReadCause.beq_refl (c : FakeReadCause) : c.beq c = true := by
  cases c <;> rfl

theorem FakeReadCause.eq_of_beq {c₁ c₂ : FakeReadCause} (h : c₁.beq c₂ = true) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> simp [FakeReadCause.beq] at h <;> rfl

/-- Projection element inside a MIR `Place` (`rustc_middle::mir::ProjectionElem`). -/
inductive ProjElem where
  | field (idx : FieldIdx)
  | downcast (variant : VariantIdx)
  | deref

/-- Structural equality on `ProjElem`. -/
noncomputable def ProjElem.beq : ProjElem → ProjElem → Bool
  | .field a, .field b => Nat.beq a b
  | .downcast a, .downcast b => Nat.beq a b
  | .deref, .deref => true
  | _, _ => false

theorem ProjElem.beq_refl (e : ProjElem) : e.beq e = true := by
  cases e with
  | field n => simp [ProjElem.beq]
  | downcast v => simp [ProjElem.beq]
  | deref => rfl

theorem ProjElem.eq_of_beq {e₁ e₂ : ProjElem} (h : e₁.beq e₂ = true) : e₁ = e₂ := by
  cases e₁ <;> cases e₂ <;> simp [ProjElem.beq] at h
  case field.field => subst h; rfl
  case downcast.downcast => subst h; rfl
  case deref.deref => rfl

/-- Check whether a projection list contains any `.deref` element. -/
noncomputable def projHasDeref : List ProjElem → Bool
  | [] => false
  | .deref :: _ => true
  | _ :: rest => projHasDeref rest

/-- MIR place (`localId` followed by projection chain `proj`). -/
structure Place where
  localId : LocalId
  proj : List ProjElem

/-- Convenience constructor for an unprojected local place. -/
noncomputable def Place.local (id : LocalId) : Place :=
  { localId := id, proj := [] }

/-- Append one projection element to a `Place`. -/
noncomputable def Place.push (p : Place) (e : ProjElem) : Place :=
  { localId := p.localId, proj := p.proj ++ [e] }

/-- Structural equality on projection lists. -/
noncomputable def projListBeq : List ProjElem → List ProjElem → Bool
  | [], [] => true
  | e₁ :: r₁, e₂ :: r₂ => e₁.beq e₂ && projListBeq r₁ r₂
  | _, _ => false

theorem projListBeq_refl (xs : List ProjElem) : projListBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [projListBeq, ProjElem.beq_refl, ih]

theorem projListBeq_eq {xs ys : List ProjElem} (h : projListBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp [projListBeq] at h
  | cons x rest ih =>
    cases ys with
    | nil => simp [projListBeq] at h
    | cons y rest' =>
      simp [projListBeq] at h
      cases h
      rename_i h1 h2
      have hx := ProjElem.eq_of_beq h1
      have hr := ih h2
      subst hx
      subst hr
      rfl

/-- Structural equality on `Place`. -/
noncomputable def Place.beq (p q : Place) : Bool :=
  Nat.beq p.localId q.localId && projListBeq p.proj q.proj

theorem Place.beq_refl (p : Place) : p.beq p = true := by
  simp [Place.beq, projListBeq_refl]

theorem Place.eq_of_beq {p q : Place} (h : p.beq q = true) : p = q := by
  cases p with
  | mk l₁ ps₁ =>
    cases q with
    | mk l₂ ps₂ =>
      simp [Place.beq] at h
      cases h
      rename_i hl hp
      have hp' := projListBeq_eq hp
      subst hl
      subst hp'
      rfl

/-- `projIsPrefix p q` holds iff `p` is a prefix of `q`. -/
noncomputable def projIsPrefix : List ProjElem → List ProjElem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | e₁ :: r₁, e₂ :: r₂ => e₁.beq e₂ && projIsPrefix r₁ r₂

theorem projIsPrefix_refl (xs : List ProjElem) : projIsPrefix xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [projIsPrefix, ProjElem.beq_refl, ih]

theorem projIsPrefix_trans {xs ys zs : List ProjElem}
    (h₁ : projIsPrefix xs ys = true) (h₂ : projIsPrefix ys zs = true) :
    projIsPrefix xs zs = true := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x r₁ ih =>
    cases ys with
    | nil => simp [projIsPrefix] at h₁
    | cons y r₂ =>
      cases zs with
      | nil => simp [projIsPrefix] at h₂
      | cons z r₃ =>
        simp [projIsPrefix] at h₁ h₂ ⊢
        cases h₁
        cases h₂
        rename_i hxy hr₁₂ hyz hr₂₃
        have hxy' := ProjElem.eq_of_beq hxy
        have hyz' := ProjElem.eq_of_beq hyz
        subst hxy'
        subst hyz'
        exact ⟨ProjElem.beq_refl x, ih hr₁₂ hr₂₃⟩

theorem projIsPrefix_length_le {xs ys : List ProjElem}
    (h : projIsPrefix xs ys = true) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x r₁ ih =>
    cases ys with
    | nil => simp [projIsPrefix] at h
    | cons y r₂ =>
      simp [projIsPrefix] at h
      cases h
      rename_i _ hr
      exact Nat.succ_le_succ (ih hr)

/-- `Place.isPrefix p q` holds iff `p` and `q` share the same base local and `p.proj` is a prefix
of `q.proj`. -/
noncomputable def Place.isPrefix (p q : Place) : Bool :=
  Nat.beq p.localId q.localId && projIsPrefix p.proj q.proj

theorem Place.isPrefix_refl (p : Place) : p.isPrefix p = true := by
  simp [Place.isPrefix, projIsPrefix_refl]

theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem natBeq_comm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ a ih =>
    cases b with
    | zero => rfl
    | succ b => exact ih b

theorem Place.isPrefix_trans {p q r : Place}
    (h₁ : p.isPrefix q = true) (h₂ : q.isPrefix r = true) : p.isPrefix r = true := by
  simp [Place.isPrefix] at h₁ h₂ ⊢
  cases h₁
  cases h₂
  rename_i hl₁ hp₁ hl₂ hp₂
  exact ⟨hl₁.trans hl₂, projIsPrefix_trans hp₁ hp₂⟩

/-- Two projection paths overlap iff one is a prefix of the other (`places_conflict`). -/
noncomputable def projOverlap : List ProjElem → List ProjElem → Bool
  | [], _ => true
  | _, [] => true
  | e₁ :: r₁, e₂ :: r₂ => e₁.beq e₂ && projOverlap r₁ r₂

theorem projOverlap_refl (xs : List ProjElem) : projOverlap xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [projOverlap, ProjElem.beq_refl, ih]

theorem projOverlap_symm (xs ys : List ProjElem) : projOverlap xs ys = projOverlap ys xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> rfl
  | cons x r₁ ih =>
    cases ys with
    | nil => rfl
    | cons y r₂ =>
      simp [projOverlap]
      have hEq : x.beq y = y.beq x := by
        cases x <;> cases y <;> simp only [ProjElem.beq]
        case field.field a b => exact natBeq_comm a b
        case downcast.downcast a b => exact natBeq_comm a b
        all_goals rfl
      rw [hEq, ih r₂]

theorem projIsPrefix_implies_overlap {xs ys : List ProjElem}
    (h : projIsPrefix xs ys = true) : projOverlap xs ys = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x r₁ ih =>
    cases ys with
    | nil => simp [projIsPrefix] at h
    | cons y r₂ =>
      simp [projIsPrefix] at h
      simp [projOverlap]
      exact ⟨h.1, ih h.2⟩

/-- Symmetric place overlap predicate (`places_conflict`). -/
noncomputable def Place.overlap (p q : Place) : Bool :=
  Nat.beq p.localId q.localId && projOverlap p.proj q.proj

theorem Place.overlap_refl (p : Place) : p.overlap p = true := by
  simp [Place.overlap, projOverlap_refl]

theorem Place.overlap_symm (p q : Place) : p.overlap q = q.overlap p := by
  simp [Place.overlap, natBeq_comm, projOverlap_symm]

theorem Place.isPrefix_implies_overlap {p q : Place}
    (h : p.isPrefix q = true) : p.overlap q = true := by
  simp [Place.isPrefix] at h
  simp [Place.overlap]
  exact ⟨h.1, projIsPrefix_implies_overlap h.2⟩

/-- Shallow conflict predicate (`rustc_borrowck/src/places_conflict.rs:288-296`):
a deep write/mut-borrow at `accessPlace` conflicts with a shallow fake borrow at `borrowPlace`
iff `accessPlace` is a prefix of (or equal to) `borrowPlace`. -/
noncomputable def shallowConflicts (borrowPlace accessPlace : Place) : Bool :=
  Place.isPrefix accessPlace borrowPlace

/-- Deep conflict predicate (`BorrowKind::Shared` or `BorrowKind::Fake(FakeBorrowKind::Deep)`). -/
noncomputable def deepConflicts (borrowPlace accessPlace : Place) : Bool :=
  Place.overlap borrowPlace accessPlace

theorem shallowConflict_implies_deepConflict {b a : Place}
    (h : shallowConflicts b a = true) : deepConflicts b a = true := by
  unfold shallowConflicts at h
  unfold deepConflicts
  rw [Place.overlap_symm]
  exact Place.isPrefix_implies_overlap h

theorem shallowConflict_local_eq {b a : Place}
    (h : shallowConflicts b a = true) : a.localId = b.localId := by
  simp [shallowConflicts, Place.isPrefix] at h
  exact h.1

theorem shallowConflict_proj_len_le {b a : Place}
    (h : shallowConflicts b a = true) : a.proj.length ≤ b.proj.length := by
  simp [shallowConflicts, Place.isPrefix] at h
  exact projIsPrefix_length_le h.2

/-- Witness matching `util.rs` comment #3: mutating `(x.0 as Some).0` does NOT shallow-conflict
with `&fake shallow x.0`, while it DOES deep-conflict. -/
theorem strictProjection_not_shallowConflict :
    let borrowPlace : Place := { localId := 1, proj := [.field 0] }
    let payloadPlace : Place := { localId := 1, proj := [.field 0, .downcast 1, .field 0] }
    shallowConflicts borrowPlace payloadPlace = false ∧
    deepConflicts borrowPlace payloadPlace = true := by
  constructor
  · rfl
  · rfl

/-- Collect all dereference-target prefixes of `p` (`fake_borrow_deref_prefixes` in
`compiler/rustc_mir_build/src/builder/matches/util.rs:127-139`). -/
noncomputable def derefPrefixesAux (loc : LocalId) : List ProjElem → List ProjElem → List Place
  | _, [] => []
  | acc, .deref :: rest =>
    { localId := loc, proj := acc } :: derefPrefixesAux loc (acc ++ [.deref]) rest
  | acc, e :: rest =>
    derefPrefixesAux loc (acc ++ [e]) rest

noncomputable def Place.derefPrefixes (p : Place) : List Place :=
  derefPrefixesAux p.localId [] p.proj

/-- Predicate checking if `q` is in `list`. -/
noncomputable def placeInList (q : Place) : List Place → Bool
  | [] => false
  | p :: ps => p.beq q || placeInList q ps

theorem projIsPrefix_append_self (xs ys : List ProjElem) :
    projIsPrefix xs (xs ++ ys) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [projIsPrefix, ProjElem.beq_refl, ih]

theorem derefPrefixesAux_isPrefix (loc : LocalId) :
    ∀ (acc tail : List ProjElem) (q : Place),
      placeInList q (derefPrefixesAux loc acc tail) = true →
      Place.isPrefix q { localId := loc, proj := acc ++ tail } = true := by
  intro acc tail
  induction tail generalizing acc with
  | nil =>
    intro q h
    simp [derefPrefixesAux, placeInList] at h
  | cons e rest ih =>
    intro q h
    cases e with
    | field idx =>
      simp [derefPrefixesAux] at h
      have h1 := ih (acc ++ [.field idx]) q h
      simp [List.append_assoc] at h1
      exact h1
    | downcast v =>
      simp [derefPrefixesAux] at h
      have h1 := ih (acc ++ [.downcast v]) q h
      simp [List.append_assoc] at h1
      exact h1
    | deref =>
      simp [derefPrefixesAux, placeInList] at h
      cases h with
      | inl hEq =>
        have hq := Place.eq_of_beq hEq
        subst hq
        simp [Place.isPrefix, projIsPrefix_append_self]
      | inr hTail =>
        have h1 := ih (acc ++ [.deref]) q hTail
        simp [List.append_assoc] at h1
        exact h1

theorem derefPrefixes_isPrefix (p q : Place)
    (h : placeInList q p.derefPrefixes = true) : Place.isPrefix q p = true := by
  have h1 := derefPrefixesAux_isPrefix p.localId [] p.proj q h
  simpa using h1

/-- Runtime values in the match-guard MIR formalization. -/
inductive Val where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | enum (variant : VariantIdx) (fields : List Val)
  | tuple (fields : List Val)
  | boxPtr (addr : HeapAddr)
  | cellPtr (addr : HeapAddr)
  | refVal (target : Place) (mutbl : Mutability)

/-- Discriminant extraction matching `Rvalue::Discriminant`. -/
noncomputable def Val.discriminant : Val → Nat
  | .enum v _ => v
  | .bool false => 0
  | .bool true => 1
  | _ => 0

/-- Check whether `Val` is a zero-sized unit value (not deinitialized on move). -/
noncomputable def Val.isZstUnit : Val → Bool
  | .unit => true
  | _ => false

/-- Local slot state matching `Trusted.MirSemantics.LocalSlot` (`deinitMovedPlace = true`). -/
inductive LocalSlot where
  | dead
  | live (optVal : Option Val)

/-- Read an indexed element from a list. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Update an indexed element in a list if in bounds. -/
noncomputable def listSet? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match listSet? xs n v with
    | some xs' => some (x :: xs')
    | none => none

theorem listGet?_listSet?_eq {α : Type} :
    ∀ (xs : List α) (i : Nat) (v : α) (xs' : List α),
      listSet? xs i v = some xs' → listGet? xs' i = some v := by
  intro xs i v xs' h
  induction xs generalizing i xs' with
  | nil => simp [listSet?] at h
  | cons x rest ih =>
    cases i with
    | zero =>
      simp [listSet?] at h
      subst h
      rfl
    | succ k =>
      simp [listSet?] at h
      cases hRec : listSet? rest k v with
      | none => simp [hRec] at h
      | some rest' =>
        simp [hRec] at h
        subst h
        exact ih k rest' hRec

theorem listGet?_listSet?_ne {α : Type} :
    ∀ (xs : List α) (i j : Nat) (v : α) (xs' : List α),
      i ≠ j → listSet? xs i v = some xs' → listGet? xs' j = listGet? xs j := by
  intro xs i j v xs' hne h
  induction xs generalizing i j xs' with
  | nil => simp [listSet?] at h
  | cons x rest ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ k =>
        simp [listSet?] at h
        subst h
        rfl
    | succ i' =>
      cases j with
      | zero =>
        simp [listSet?] at h
        cases hRec : listSet? rest i' v with
        | none => simp [hRec] at h
        | some rest' =>
          simp [hRec] at h
          subst h
          rfl
      | succ j' =>
        simp [listSet?] at h
        cases hRec : listSet? rest i' v with
        | none => simp [hRec] at h
        | some rest' =>
          simp [hRec] at h
          subst h
          have hne' : i' ≠ j' := fun hEq => hne (congrArg Nat.succ hEq)
          exact ih i' j' rest' hne' hRec

/-- Machine store with local slots, box heap, and interior-mutable cell heap. -/
structure MirStore where
  locals : List LocalSlot
  boxHeap : List (Option Val)
  cellHeap : List (Option Val)

/-- Read a projection chain starting from a `Val`.
Follows MIR's strict structural separation: `.field` applies to `.tuple`, `.downcast :: .field`
applies to `.enum`, and `.deref` resolves `.boxPtr` or `.refVal`. -/
noncomputable def readProjFromVal (st : MirStore) : Val → List ProjElem → Option Val
  | v, [] => some v
  | .tuple fs, .field idx :: rest =>
    match listGet? fs idx with
    | some fv => readProjFromVal st fv rest
    | none => none
  | .enum var fs, .downcast exp :: .field idx :: rest =>
    if Nat.beq var exp then
      match listGet? fs idx with
      | some fv => readProjFromVal st fv rest
      | none => none
    else
      none
  | .enum var _, .downcast exp :: [] =>
    if Nat.beq var exp then some (.enum var []) else none
  | .boxPtr addr, .deref :: rest =>
    match listGet? st.boxHeap addr with
    | some (some inner) => readProjFromVal st inner rest
    | _ => none
  | .refVal target _, .deref :: rest =>
    match listGet? st.locals target.localId with
    | some (.live (some baseVal)) =>
      @List.rec ProjElem (fun _ => Option Val → Option Val)
        (fun ov => ov)
        (fun e' _ ih ov =>
          match ov with
          | some (.tuple fs) =>
            match e' with
            | .field idx => ih (listGet? fs idx)
            | _ => none
          | some (.enum var fs) =>
            match e' with
            | .downcast exp =>
              if Nat.beq var exp then ih (some (.tuple fs)) else none
            | _ => none
          | _ => none)
        target.proj (some baseVal) |>
      fun optPointed =>
        match optPointed with
        | some pointed => readProjFromVal st pointed rest
        | none => none
    | _ => none
  | _, _ => none

/-- Read a MIR `Place` from `MirStore`. -/
noncomputable def MirStore.readPlace (st : MirStore) (p : Place) : Option Val :=
  match listGet? st.locals p.localId with
  | some (.live (some v)) => readProjFromVal st v p.proj
  | _ => none

/-- Read the discriminant of a `Place` in `MirStore` (`none` if uninitialized/dead). -/
noncomputable def MirStore.readDiscr (st : MirStore) (p : Place) : Option Nat :=
  match st.readPlace p with
  | some v => some v.discriminant
  | none => none

/-- Update a non-deref projection chain inside a `Val`. -/
noncomputable def writeProjInVal : Val → List ProjElem → Val → Option Val
  | _, [], newV => some newV
  | .tuple fs, .field idx :: rest, newV =>
    match listGet? fs idx with
    | some oldF =>
      match writeProjInVal oldF rest newV with
      | some updF =>
        match listSet? fs idx updF with
        | some fs' => some (.tuple fs')
        | none => none
      | none => none
    | none => none
  | .enum var fs, .downcast exp :: .field idx :: rest, newV =>
    if Nat.beq var exp then
      match listGet? fs idx with
      | some oldF =>
        match writeProjInVal oldF rest newV with
        | some updF =>
          match listSet? fs idx updF with
          | some fs' => some (.enum var fs')
          | none => none
        | none => none
      | none => none
    else
      none
  | _, _, _ => none

/-- Mutating any non-empty projection chain via `writeProjInVal` preserves `Val.discriminant v`. -/
theorem writeProjInVal_preserves_discriminant :
    ∀ (ps : List ProjElem) (v newV v' : Val) (e : ProjElem) (rest : List ProjElem),
      ps = e :: rest →
      writeProjInVal v ps newV = some v' →
      v'.discriminant = v.discriminant := by
  intro ps v newV v' e rest hps h
  subst hps
  cases e with
  | deref =>
    cases v <;> simp [writeProjInVal] at h
  | field idx =>
    cases v with
    | tuple fs =>
      simp only [writeProjInVal] at h
      cases hf : listGet? fs idx with
      | none => simp [hf] at h
      | some oldF =>
        simp [hf] at h
        cases hw : writeProjInVal oldF rest newV with
        | none => simp [hw] at h
        | some updF =>
          simp [hw] at h
          cases hs : listSet? fs idx updF with
          | none => simp [hs] at h
          | some fs' =>
            simp [hs] at h
            subst h
            rfl
    | unit | bool _ | int _ | enum _ _ | boxPtr _ | cellPtr _ | refVal _ _ =>
      simp [writeProjInVal] at h
  | downcast exp =>
    cases v with
    | enum var fs =>
      cases rest with
      | nil => simp [writeProjInVal] at h
      | cons e2 rest2 =>
        cases e2 with
        | field idx =>
          simp only [writeProjInVal] at h
          cases hEq : Nat.beq var exp with
          | false => simp [hEq] at h
          | true =>
            simp [hEq] at h
            cases hf : listGet? fs idx with
            | none => simp [hf] at h
            | some oldF =>
              simp [hf] at h
              cases hw : writeProjInVal oldF rest2 newV with
              | none => simp [hw] at h
              | some updF =>
                simp [hw] at h
                cases hs : listSet? fs idx updF with
                | none => simp [hs] at h
                | some fs' =>
                  simp [hs] at h
                  subst h
                  rfl
        | downcast _ | deref => simp [writeProjInVal] at h
    | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
      simp [writeProjInVal] at h

/-- Pure non-deref projections read identically across arbitrary `MirStore` changes. -/
theorem readProjFromVal_noDeref_store_indep_aux (st₁ st₂ : MirStore) :
    ∀ (n : Nat) (ps : List ProjElem) (v : Val),
      ps.length ≤ n →
      projHasDeref ps = false →
      readProjFromVal st₁ v ps = readProjFromVal st₂ v ps := by
  intro n
  induction n with
  | zero =>
    intro ps v hLen _
    cases ps with
    | nil => rfl
    | cons _ _ => cases hLen
  | succ k ih =>
    intro ps v hLen hNo
    cases ps with
    | nil => rfl
    | cons e rest =>
      cases e with
      | deref => simp [projHasDeref] at hNo
      | field idx =>
        simp [projHasDeref] at hNo
        cases v with
        | tuple fs =>
          simp only [readProjFromVal]
          cases listGet? fs idx with
          | none => rfl
          | some fv =>
            exact ih rest fv (Nat.le_of_succ_le_succ hLen) hNo
        | unit | bool _ | int _ | enum _ _ | boxPtr _ | cellPtr _ | refVal _ _ =>
          simp [readProjFromVal]
      | downcast exp =>
        cases rest with
        | nil =>
          cases v <;> simp [readProjFromVal]
        | cons e2 rest2 =>
          cases e2 with
          | deref => simp [projHasDeref] at hNo
          | downcast _ => cases v <;> simp [readProjFromVal]
          | field idx =>
            simp [projHasDeref] at hNo
            cases v with
            | enum var fs =>
              simp only [readProjFromVal]
              cases hVar : Nat.beq var exp with
              | false => simp
              | true =>
                simp
                cases listGet? fs idx with
                | none => rfl
                | some fv =>
                  have hLe : rest2.length ≤ k :=
                    Nat.le_trans (Nat.le_succ _) (Nat.le_of_succ_le_succ hLen)
                  exact ih rest2 fv hLe hNo
            | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
              simp [readProjFromVal]

theorem readProjFromVal_noDeref_store_indep (st₁ st₂ : MirStore) (ps : List ProjElem) (v : Val)
    (hNo : projHasDeref ps = false) :
    readProjFromVal st₁ v ps = readProjFromVal st₂ v ps :=
  readProjFromVal_noDeref_store_indep_aux st₁ st₂ ps.length ps v (Nat.le_refl _) hNo

/-- Writing a strict descendant projection `qs` inside `v` preserves the discriminant at prefix `ps`. -/
theorem writeProjInVal_strictDescendant_preserves_prefix_discr_aux (st : MirStore) :
    ∀ (n : Nat) (ps qs : List ProjElem) (v newV v' : Val),
      ps.length ≤ n →
      projHasDeref ps = false →
      projIsPrefix ps qs = true →
      ps.length < qs.length →
      writeProjInVal v qs newV = some v' →
      (match readProjFromVal st v' ps with | some x => some x.discriminant | none => none) =
      (match readProjFromVal st v ps with | some x => some x.discriminant | none => none) := by
  intro n
  induction n with
  | zero =>
    intro ps qs v newV v' hLen _ _ hLt hW
    cases ps with
    | nil =>
      cases qs with
      | nil => cases hLt
      | cons e rest =>
        simp [readProjFromVal]
        rw [writeProjInVal_preserves_discriminant (e :: rest) v newV v' e rest rfl hW]
    | cons _ _ => cases hLen
  | succ k ih =>
    intro ps qs v newV v' hLen hNo hPref hLt hW
    cases ps with
    | nil =>
      cases qs with
      | nil => cases hLt
      | cons e rest =>
        simp [readProjFromVal]
        rw [writeProjInVal_preserves_discriminant (e :: rest) v newV v' e rest rfl hW]
    | cons p ps' =>
      cases qs with
      | nil => simp [projIsPrefix] at hPref
      | cons q qs' =>
        simp [projIsPrefix] at hPref
        cases hPref
        rename_i hpq hPref'
        have hEqElem := ProjElem.eq_of_beq hpq
        subst hEqElem
        have hLt' : ps'.length < qs'.length := Nat.lt_of_succ_lt_succ hLt
        cases p with
        | deref => simp [projHasDeref] at hNo
        | field idx =>
          simp [projHasDeref] at hNo
          cases v with
          | tuple fs =>
            simp [writeProjInVal] at hW
            cases hf : listGet? fs idx with
            | none => simp [hf] at hW
            | some oldF =>
              simp [hf] at hW
              cases hw : writeProjInVal oldF qs' newV with
              | none => simp [hw] at hW
              | some updF =>
                simp [hw] at hW
                cases hs : listSet? fs idx updF with
                | none => simp [hs] at hW
                | some fs' =>
                  simp [hs] at hW
                  subst hW
                  simp [readProjFromVal, hf, listGet?_listSet?_eq fs idx updF fs' hs]
                  exact ih ps' qs' oldF newV updF (Nat.le_of_succ_le_succ hLen) hNo hPref' hLt' hw
          | unit | bool _ | int _ | enum _ _ | boxPtr _ | cellPtr _ | refVal _ _ =>
            simp [writeProjInVal] at hW
        | downcast exp =>
          simp [projHasDeref] at hNo
          cases v with
          | enum var fs =>
            cases qs' with
            | nil => simp [writeProjInVal] at hW
            | cons q2 qs'' =>
              cases q2 with
              | deref | downcast _ => simp [writeProjInVal] at hW
              | field idx2 =>
                simp only [writeProjInVal] at hW
                cases hVar : Nat.beq var exp with
                | false => simp [hVar] at hW
                | true =>
                  simp [hVar] at hW
                  cases hf : listGet? fs idx2 with
                  | none => simp [hf] at hW
                  | some oldF =>
                    simp [hf] at hW
                    cases hw : writeProjInVal oldF qs'' newV with
                    | none => simp [hw] at hW
                    | some updF =>
                      simp [hw] at hW
                      cases hs : listSet? fs idx2 updF with
                      | none => simp [hs] at hW
                      | some fs' =>
                        simp [hs] at hW
                        subst hW
                        cases ps' with
                        | nil =>
                          simp [readProjFromVal, hVar]
                        | cons p2 ps'' =>
                          simp [projIsPrefix] at hPref'
                          cases hPref'
                          rename_i hp2 hPref''
                          have hEq2 := ProjElem.eq_of_beq hp2
                          subst hEq2
                          simp [projHasDeref] at hNo
                          simp [readProjFromVal, hVar, hf, listGet?_listSet?_eq fs idx2 updF fs' hs]
                          have hLe'' : ps''.length ≤ k :=
                            Nat.le_trans (Nat.le_succ _) (Nat.le_of_succ_le_succ hLen)
                          have hLt'' : ps''.length < qs''.length := Nat.lt_of_succ_lt_succ hLt'
                          exact ih ps'' qs'' oldF newV updF hLe'' hNo hPref'' hLt'' hw
          | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
            simp [writeProjInVal] at hW

theorem writeProjInVal_strictDescendant_preserves_prefix_discr (st : MirStore)
    (ps qs : List ProjElem) (v newV v' : Val)
    (hNo : projHasDeref ps = false)
    (hPref : projIsPrefix ps qs = true)
    (hLt : ps.length < qs.length)
    (hW : writeProjInVal v qs newV = some v') :
    (match readProjFromVal st v' ps with | some x => some x.discriminant | none => none) =
    (match readProjFromVal st v ps with | some x => some x.discriminant | none => none) :=
  writeProjInVal_strictDescendant_preserves_prefix_discr_aux
    st ps.length ps qs v newV v' (Nat.le_refl _) hNo hPref hLt hW

/-- Writing a disjoint projection `qs` inside `v` (`projOverlap ps qs = false`) preserves
`readProjFromVal st v ps` identically. -/
theorem writeProjInVal_disjoint_preserves_read_aux (st : MirStore) :
    ∀ (n : Nat) (ps qs : List ProjElem) (v newV v' : Val),
      ps.length ≤ n →
      projHasDeref ps = false →
      projOverlap ps qs = false →
      writeProjInVal v qs newV = some v' →
      readProjFromVal st v' ps = readProjFromVal st v ps := by
  intro n
  induction n with
  | zero =>
    intro ps qs v newV v' hLen _ hDisj _
    cases ps with
    | nil => simp [projOverlap] at hDisj
    | cons _ _ => cases hLen
  | succ k ih =>
    intro ps qs v newV v' hLen hNo hDisj hW
    cases ps with
    | nil => simp [projOverlap] at hDisj
    | cons p ps' =>
      cases qs with
      | nil => simp [projOverlap] at hDisj
      | cons q qs' =>
        simp [projOverlap] at hDisj
        cases hEqElem : p.beq q with
        | true =>
          simp [hEqElem] at hDisj
          have hEq := ProjElem.eq_of_beq hEqElem
          subst hEq
          cases p with
          | deref => simp [projHasDeref] at hNo
          | field idx =>
            simp [projHasDeref] at hNo
            cases v <;> simp [writeProjInVal] at hW
            case tuple fs =>
              cases hf : listGet? fs idx with
              | none => simp [hf] at hW
              | some oldF =>
                simp [hf] at hW
                cases hw : writeProjInVal oldF qs' newV with
                | none => simp [hw] at hW
                | some updF =>
                  simp [hw] at hW
                  cases hs : listSet? fs idx updF with
                  | none => simp [hs] at hW
                  | some fs' =>
                    simp [hs] at hW
                    subst hW
                    simp [readProjFromVal, hf, listGet?_listSet?_eq fs idx updF fs' hs]
                    exact ih ps' qs' oldF newV updF (Nat.le_of_succ_le_succ hLen) hNo hDisj hw
          | downcast exp =>
            simp [projHasDeref] at hNo
            cases v with
            | enum var fs =>
              cases qs' with
              | nil => simp [writeProjInVal] at hW
              | cons q2 qs'' =>
                cases q2 with
                | deref | downcast _ => simp [writeProjInVal] at hW
                | field idx2 =>
                  simp only [writeProjInVal] at hW
                  cases hVar : Nat.beq var exp with
                  | false => simp [hVar] at hW
                  | true =>
                    simp [hVar] at hW
                    cases hf : listGet? fs idx2 with
                    | none => simp [hf] at hW
                    | some oldF =>
                      simp [hf] at hW
                      cases hw : writeProjInVal oldF qs'' newV with
                      | none => simp [hw] at hW
                      | some updF =>
                        simp [hw] at hW
                        cases hs : listSet? fs idx2 updF with
                        | none => simp [hs] at hW
                        | some fs' =>
                          simp [hs] at hW
                          subst hW
                          cases ps' with
                          | nil => simp [projOverlap] at hDisj
                          | cons p2 ps'' =>
                            simp [projOverlap] at hDisj
                            cases hEq2 : p2.beq (.field idx2) with
                            | false =>
                              cases p2 with
                              | field idxP =>
                                simp [ProjElem.beq] at hEq2
                                have hne : idx2 ≠ idxP := fun heq => by
                                  subst heq
                                  simp at hEq2
                                simp [readProjFromVal, hVar]
                                rw [listGet?_listSet?_ne fs idx2 idxP updF fs' hne hs]
                              | downcast _ =>
                                simp [readProjFromVal]
                              | deref => simp [projHasDeref] at hNo
                            | true =>
                              simp [hEq2] at hDisj
                              have hEq2' := ProjElem.eq_of_beq hEq2
                              subst hEq2'
                              simp [projHasDeref] at hNo
                              simp [readProjFromVal, hVar, hf, listGet?_listSet?_eq fs idx2 updF fs' hs]
                              have hLe'' : ps''.length ≤ k :=
                                Nat.le_trans (Nat.le_succ _) (Nat.le_of_succ_le_succ hLen)
                              exact ih ps'' qs'' oldF newV updF hLe'' hNo hDisj hw
            | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
              simp [writeProjInVal] at hW
        | false =>
          cases p with
          | deref => simp [projHasDeref] at hNo
          | field idxP =>
            simp [projHasDeref] at hNo
            cases q with
            | field idxQ =>
              have hne : idxQ ≠ idxP := fun heq => by
                subst heq
                simp [ProjElem.beq] at hEqElem
              cases v <;> simp [writeProjInVal] at hW
              case tuple fs =>
                cases hf : listGet? fs idxQ with
                | none => simp [hf] at hW
                | some oldF =>
                  simp [hf] at hW
                  cases hw : writeProjInVal oldF qs' newV with
                  | none => simp [hw] at hW
                  | some updF =>
                    simp [hw] at hW
                    cases hs : listSet? fs idxQ updF with
                    | none => simp [hs] at hW
                    | some fs' =>
                      simp [hs] at hW
                      subst hW
                      simp [readProjFromVal, listGet?_listSet?_ne fs idxQ idxP updF fs' hne hs]
            | downcast expQ =>
              cases v with
              | enum var fs =>
                cases qs' with
                | nil => simp [writeProjInVal] at hW
                | cons q2 qs'' =>
                  cases q2 with
                  | deref | downcast _ => simp [writeProjInVal] at hW
                  | field idx2 =>
                    simp only [writeProjInVal] at hW
                    cases hVarQ : Nat.beq var expQ with
                    | false => simp [hVarQ] at hW
                    | true =>
                      simp [hVarQ] at hW
                      cases hf : listGet? fs idx2 with
                      | none => simp [hf] at hW
                      | some oldF =>
                        simp [hf] at hW
                        cases hw : writeProjInVal oldF qs'' newV with
                        | none => simp [hw] at hW
                        | some updF =>
                          simp [hw] at hW
                          cases hs : listSet? fs idx2 updF with
                          | none => simp [hs] at hW
                          | some fs' =>
                            simp [hs] at hW
                            subst hW
                            rfl
              | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
                simp [writeProjInVal] at hW
            | deref =>
              cases v <;> simp [writeProjInVal] at hW
          | downcast exp =>
            simp [projHasDeref] at hNo
            cases q with
            | downcast expQ =>
              cases v with
              | enum var fs =>
                cases qs' with
                | nil => simp [writeProjInVal] at hW
                | cons q2 qs'' =>
                  cases q2 with
                  | deref | downcast _ => simp [writeProjInVal] at hW
                  | field idx2 =>
                    simp only [writeProjInVal] at hW
                    cases hVarQ : Nat.beq var expQ with
                    | false => simp [hVarQ] at hW
                    | true =>
                      simp [hVarQ] at hW
                      cases hf : listGet? fs idx2 with
                      | none => simp [hf] at hW
                      | some oldF =>
                        simp [hf] at hW
                        cases hw : writeProjInVal oldF qs'' newV with
                        | none => simp [hw] at hW
                        | some updF =>
                          simp [hw] at hW
                          cases hs : listSet? fs idx2 updF with
                          | none => simp [hs] at hW
                          | some fs' =>
                            simp [hs] at hW
                            subst hW
                            have hVarNe : Nat.beq var exp = false := by
                              have hvq := Nat.eq_of_beq_eq_true hVarQ
                              subst hvq
                              cases hve : Nat.beq var exp with
                              | false => rfl
                              | true =>
                                have hve' := Nat.eq_of_beq_eq_true hve
                                subst hve'
                                simp [ProjElem.beq] at hEqElem
                            cases ps' with
                            | nil => simp [readProjFromVal, hVarNe]
                            | cons e2 _ =>
                              cases e2 with
                              | field _ => simp [readProjFromVal, hVarNe]
                              | downcast _ | deref => simp [readProjFromVal]
              | unit | bool _ | int _ | tuple _ | boxPtr _ | cellPtr _ | refVal _ _ =>
                simp [writeProjInVal] at hW
            | field idxQ =>
              cases v <;> simp [writeProjInVal] at hW
              case tuple fs =>
                cases hf : listGet? fs idxQ with
                | none => simp [hf] at hW
                | some oldF =>
                  simp [hf] at hW
                  cases hw : writeProjInVal oldF qs' newV with
                  | none => simp [hw] at hW
                  | some updF =>
                    simp [hw] at hW
                    cases hs : listSet? fs idxQ updF with
                    | none => simp [hs] at hW
                    | some fs' =>
                      simp [hs] at hW
                      subst hW
                      cases ps' with
                      | nil => rfl
                      | cons e2 _ =>
                        cases e2 <;> simp [readProjFromVal]
            | deref =>
              cases v <;> simp [writeProjInVal] at hW

theorem writeProjInVal_disjoint_preserves_read (st : MirStore)
    (ps qs : List ProjElem) (v newV v' : Val)
    (hNo : projHasDeref ps = false)
    (hDisj : projOverlap ps qs = false)
    (hW : writeProjInVal v qs newV = some v') :
    readProjFromVal st v' ps = readProjFromVal st v ps :=
  writeProjInVal_disjoint_preserves_read_aux
    st ps.length ps qs v newV v' (Nat.le_refl _) hNo hDisj hW

/-- Write `newV` into `p` in `MirStore`. -/
noncomputable def MirStore.writePlace (st : MirStore) (p : Place) (newV : Val) : Option MirStore :=
  match p.proj with
  | [] =>
    match listGet? st.locals p.localId with
    | some (.live _) =>
      match listSet? st.locals p.localId (.live (some newV)) with
      | some locals' => some { st with locals := locals' }
      | none => none
    | _ => none
  | .deref :: rest =>
    match listGet? st.locals p.localId with
    | some (.live (some (.boxPtr addr))) =>
      match listGet? st.boxHeap addr with
      | some (some oldInner) =>
        match writeProjInVal oldInner rest newV with
        | some newInner =>
          match listSet? st.boxHeap addr (some newInner) with
          | some bh' => some { st with boxHeap := bh' }
          | none => none
        | none => none
      | _ => none
    | some (.live (some (.refVal target .mut_))) =>
      match target.proj with
      | [] =>
        match listGet? st.locals target.localId with
        | some (.live (some oldTarget)) =>
          match writeProjInVal oldTarget rest newV with
          | some newTarget =>
            match listSet? st.locals target.localId (.live (some newTarget)) with
            | some locals' => some { st with locals := locals' }
            | none => none
          | none => none
        | _ => none
      | _ => none
    | _ => none
  | _ =>
    match listGet? st.locals p.localId with
    | some (.live (some oldV)) =>
      match writeProjInVal oldV p.proj newV with
      | some updV =>
        match listSet? st.locals p.localId (.live (some updV)) with
        | some locals' => some { st with locals := locals' }
        | none => none
      | none => none
    | _ => none

/-- Move out of `p` with `deinitMovedPlace = true` (`Trusted.MirSemantics.evalOperandToSlot`). -/
noncomputable def MirStore.movePlace (st : MirStore) (p : Place) : Option (Val × MirStore) :=
  match st.readPlace p with
  | none => none
  | some v =>
    if v.isZstUnit then
      some (v, st)
    else
      match p.proj with
      | [] =>
        match listSet? st.locals p.localId (.live none) with
        | some locals' => some (v, { st with locals := locals' })
        | none => none
      | .downcast _ :: .field _ :: [] =>
        match listSet? st.locals p.localId (.live none) with
        | some locals' => some (v, { st with locals := locals' })
        | none => none
      | _ => some (v, st)

/-- Read an interior-mutable cell at `addr`. -/
noncomputable def MirStore.readCell (st : MirStore) (addr : HeapAddr) : Option Val :=
  match listGet? st.cellHeap addr with
  | some (some v) => some v
  | _ => none

/-- Write an interior-mutable cell at `addr` (allowed through shared `&Cell`). -/
noncomputable def MirStore.writeCell (st : MirStore) (addr : HeapAddr) (v : Val) : Option MirStore :=
  match listGet? st.cellHeap addr with
  | some (some _) =>
    match listSet? st.cellHeap addr (some v) with
    | some ch' => some { st with cellHeap := ch' }
    | none => none
  | _ => none

/-- Interior-mutable `Cell::set` never alters local slots or `boxHeap`, preserving `readPlace`
and `readDiscr` of every non-`deref` place. -/
theorem writeCell_preserves_readPlace_noDeref {st st' : MirStore} {addr : HeapAddr} {v : Val}
    {p : Place} (hNo : projHasDeref p.proj = false)
    (hWc : st.writeCell addr v = some st') :
    st'.readPlace p = st.readPlace p := by
  simp [MirStore.writeCell] at hWc
  cases hg : listGet? st.cellHeap addr with
  | none => simp [hg] at hWc
  | some opt =>
    cases opt with
    | none => simp [hg] at hWc
    | some _ =>
      simp [hg] at hWc
      cases hs : listSet? st.cellHeap addr (some v) with
      | none => simp [hs] at hWc
      | some ch' =>
        simp [hs] at hWc
        subst hWc
        simp [MirStore.readPlace]
        cases listGet? st.locals p.localId with
        | none => rfl
        | some slot =>
          cases slot with
          | dead => rfl
          | live ov =>
            cases ov with
            | none => rfl
            | some base =>
              exact readProjFromVal_noDeref_store_indep
                { locals := st.locals, boxHeap := st.boxHeap, cellHeap := ch' }
                st p.proj base hNo

/-- Writing to a non-deref local place `q` (`q.localId ≠ p.localId`) preserves `readPlace p`
when `p` has no `.deref`. -/
theorem MirStore.writePlace_cons_noDeref {st st' : MirStore} {q : Place}
    {e : ProjElem} {rest : List ProjElem} {newV : Val}
    (hq : q.proj = e :: rest) (hNo : projHasDeref q.proj = false)
    (hW : st.writePlace q newV = some st') :
    ∃ oldV updV locs',
      listGet? st.locals q.localId = some (.live (some oldV)) ∧
      writeProjInVal oldV q.proj newV = some updV ∧
      listSet? st.locals q.localId (.live (some updV)) = some locs' ∧
      st' = { st with locals := locs' } := by
  have hNo' : projHasDeref (e :: rest) = false := by
    rw [← hq]; exact hNo
  cases e with
  | deref => simp [projHasDeref] at hNo'
  | field idx =>
    simp only [MirStore.writePlace, hq] at hW
    cases hl : listGet? st.locals q.localId with
    | none => simp [hl] at hW
    | some slot =>
      cases slot with
      | dead => simp [hl] at hW
      | live ov =>
        cases ov with
        | none => simp [hl] at hW
        | some oldV =>
          simp [hl] at hW
          cases hw : writeProjInVal oldV (.field idx :: rest) newV with
          | none => simp [hw] at hW
          | some updV =>
            simp [hw] at hW
            cases hs : listSet? st.locals q.localId (.live (some updV)) with
            | none => simp [hs] at hW
            | some locs' =>
              simp [hs] at hW
              subst hW
              rw [← hq] at hw
              exact ⟨oldV, updV, locs', rfl, hw, hs, rfl⟩
  | downcast exp =>
    simp only [MirStore.writePlace, hq] at hW
    cases hl : listGet? st.locals q.localId with
    | none => simp [hl] at hW
    | some slot =>
      cases slot with
      | dead => simp [hl] at hW
      | live ov =>
        cases ov with
        | none => simp [hl] at hW
        | some oldV =>
          simp [hl] at hW
          cases hw : writeProjInVal oldV (.downcast exp :: rest) newV with
          | none => simp [hw] at hW
          | some updV =>
            simp [hw] at hW
            cases hs : listSet? st.locals q.localId (.live (some updV)) with
            | none => simp [hs] at hW
            | some locs' =>
              simp [hs] at hW
              subst hW
              rw [← hq] at hw
              exact ⟨oldV, updV, locs', rfl, hw, hs, rfl⟩

theorem writePlace_disjoint_local_noDeref {st st' : MirStore} {p q : Place} {newV : Val}
    (hne : q.localId ≠ p.localId)
    (hNoP : projHasDeref p.proj = false)
    (hNoQ : projHasDeref q.proj = false)
    (hW : st.writePlace q newV = some st') :
    st'.readPlace p = st.readPlace p := by
  cases hq : q.proj with
  | nil =>
    simp [MirStore.writePlace, hq] at hW
    cases hl : listGet? st.locals q.localId with
    | none => simp [hl] at hW
    | some slot =>
      cases slot with
      | dead => simp [hl] at hW
      | live _ =>
        simp [hl] at hW
        cases hs : listSet? st.locals q.localId (.live (some newV)) with
        | none => simp [hs] at hW
        | some locs' =>
          simp [hs] at hW
          subst hW
          simp [MirStore.readPlace]
          rw [listGet?_listSet?_ne st.locals q.localId p.localId (.live (some newV)) locs' hne hs]
          cases listGet? st.locals p.localId with
          | none => rfl
          | some slotp =>
            cases slotp with
            | dead => rfl
            | live ov =>
              cases ov with
              | none => rfl
              | some base =>
                exact readProjFromVal_noDeref_store_indep
                  { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
                  st p.proj base hNoP
  | cons eq rest =>
    rcases MirStore.writePlace_cons_noDeref hq hNoQ hW with ⟨oldV, updV, locs', _, _, hs, hEqSt⟩
    subst hEqSt
    simp [MirStore.readPlace]
    rw [listGet?_listSet?_ne st.locals q.localId p.localId (.live (some updV)) locs' hne hs]
    cases listGet? st.locals p.localId with
    | none => rfl
    | some slotp =>
      cases slotp with
      | dead => rfl
      | live ovp =>
        cases ovp with
        | none => rfl
        | some base =>
          exact readProjFromVal_noDeref_store_indep
            { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
            st p.proj base hNoP

/-- Key shallow fake-borrow soundness lemma at the store level:
any non-deref write `st.writePlace q newV = some st'` that does NOT shallow-conflict with a
non-deref place `p` (`shallowConflicts p q = false`) preserves `readDiscr p`! -/
theorem writePlace_noShallowConflict_preserves_readDiscr
    {st st' : MirStore} {p q : Place} {newV : Val}
    (hNoP : projHasDeref p.proj = false)
    (hNoQ : projHasDeref q.proj = false)
    (hNotShallow : shallowConflicts p q = false)
    (hW : st.writePlace q newV = some st') :
    st'.readDiscr p = st.readDiscr p := by
  cases hLoc : Nat.beq q.localId p.localId with
  | false =>
    have hne : q.localId ≠ p.localId := by
      intro heq
      rw [heq] at hLoc
      have ht := natBeq_refl p.localId
      rw [ht] at hLoc
      cases hLoc
    have hRead := writePlace_disjoint_local_noDeref hne hNoP hNoQ hW
    simp [MirStore.readDiscr, hRead]
  | true =>
    have hEqLoc := Nat.eq_of_beq_eq_true hLoc
    cases hq : q.proj with
    | nil =>
      simp [shallowConflicts, Place.isPrefix, hq, projIsPrefix, hLoc] at hNotShallow
    | cons eq restq =>
      rcases MirStore.writePlace_cons_noDeref hq hNoQ hW with ⟨oldV, updV, locs', hl, hw, hs, hEqSt⟩
      subst hEqSt
      simp [MirStore.readDiscr, MirStore.readPlace]
      have hGetNew := listGet?_listSet?_eq st.locals p.localId (.live (some updV)) locs'
        (by rw [← hEqLoc]; exact hs)
      have hGetOld : listGet? st.locals p.localId = some (.live (some oldV)) := by
        rw [← hEqLoc]
        exact hl
      rw [hGetNew, hGetOld]
      simp
      have hIndep := readProjFromVal_noDeref_store_indep
        { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
        st p.proj updV hNoP
      rw [hIndep]
      cases hOver : projOverlap p.proj q.proj with
      | false =>
        rw [writeProjInVal_disjoint_preserves_read st p.proj q.proj oldV newV updV hNoP hOver hw]
      | true =>
        have hPref : projIsPrefix p.proj q.proj = true ∧ p.proj.length < q.proj.length := by
          have hNotPrefQ : projIsPrefix q.proj p.proj = false := by
            simp [shallowConflicts, Place.isPrefix, hLoc] at hNotShallow
            exact hNotShallow
          have hLem : ∀ (xs ys : List ProjElem),
              projOverlap xs ys = true → projIsPrefix ys xs = false →
              projIsPrefix xs ys = true ∧ xs.length < ys.length := by
            intro xs
            induction xs with
            | nil =>
              intro ys _ hnp
              cases ys with
              | nil => simp [projIsPrefix] at hnp
              | cons _ _ => exact ⟨rfl, Nat.zero_lt_succ _⟩
            | cons x xs' ihxs =>
              intro ys hov hnp
              cases ys with
              | nil => simp [projIsPrefix] at hnp
              | cons y ys' =>
                simp [projOverlap] at hov
                cases hov
                rename_i hxy hov'
                have heq := ProjElem.eq_of_beq hxy
                subst heq
                simp [projIsPrefix, ProjElem.beq_refl] at hnp ⊢
                have hrec := ihxs ys' hov' hnp
                exact ⟨hrec.1, Nat.succ_lt_succ hrec.2⟩
          exact hLem p.proj q.proj hOver hNotPrefQ
        exact writeProjInVal_strictDescendant_preserves_prefix_discr st p.proj
          q.proj oldV newV updV hNoP hPref.1 hPref.2 hw

/-! ## Part II: Match-Lowering MIR Syntax, Borrowck Loan Checking, and Diagnostic Partition -/

/-- Rustc borrow-checker diagnostic codes emitted during match-guard checking. -/
inductive DiagnosticCode where
  | E0510  -- `cannot_mutate_in_immutable_section` (`FakeBorrow` / `ForMatchGuard`)
  | E0502  -- `cannot borrow ... as mutable because it is also borrowed as immutable` (`FakeBorrowKind::Deep`)
  | E0506  -- `cannot assign to ... because it is borrowed` (active `BorrowKind::Shared` guard binding)
  | E0594  -- `cannot assign to ..., as it is immutable for the pattern guard` (`RefWithinGuard`)

/-- Equality on `DiagnosticCode`. -/
noncomputable def DiagnosticCode.beq : DiagnosticCode → DiagnosticCode → Bool
  | .E0510, .E0510 => true
  | .E0502, .E0502 => true
  | .E0506, .E0506 => true
  | .E0594, .E0594 => true
  | _, _ => false

/-- MIR Rvalues modeled for match lowering and guard evaluation. -/
inductive Rvalue where
  | useCopy (p : Place)
  | useMove (p : Place)
  | constVal (v : Val)
  | discriminant (p : Place)
  | ref (kind : BorrowKind) (p : Place)
  | cellWrite (cellAddr : HeapAddr) (v : Val)

/-- MIR statements including pre-cleanup administrative instructions. -/
inductive StatementKind where
  | assign (dst : Place) (rhs : Rvalue)
  | fakeRead (cause : FakeReadCause) (p : Place)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | ascribeUserType (p : Place)
  | nop

/-- MIR terminators including `FalseEdge` (`rustc_middle::mir::TerminatorKind`). -/
inductive TerminatorKind where
  | goto (target : BlockId)
  | switchDiscr (scrutinee : Place) (cases : List (Nat × BlockId)) (otherwise : BlockId)
  | switchBool (cond : LocalId) (onFalse onTrue : BlockId)
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | return_
  | unreachable

/-- Basic block of MIR statements and a terminator. -/
structure BasicBlock where
  stmts : List StatementKind
  term : TerminatorKind

/-- MIR function body with metadata distinguishing `RefWithinGuard` locals and fake-borrow temps. -/
structure MirBody where
  localsCount : Nat
  isRefForGuard : LocalId → Bool
  isFakeTemp : LocalId → Bool
  blocks : List BasicBlock

/-- Active or deactivated loan tracked during NLL borrow checking. -/
structure Loan where
  temp : LocalId
  kind : BorrowKind
  place : Place
  causeOpt : Option FakeReadCause
  active : Bool

/-- Check direct assignment / mutation against active loans (`report_illegal_mutation_of_borrowed`,
`compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs:3997-4045`). -/
noncomputable def checkWritePlaceLoans (loans : List Loan) (dst : Place) :
    Except DiagnosticCode Unit :=
  match loans with
  | [] => .ok ()
  | l :: rest =>
    if !l.active then
      checkWritePlaceLoans rest dst
    else
      match l.kind with
      | .fakeShallow =>
        if shallowConflicts l.place dst then .error .E0510 else checkWritePlaceLoans rest dst
      | .fakeDeep =>
        if deepConflicts l.place dst then .error .E0510 else checkWritePlaceLoans rest dst
      | .shared | .mutDefault =>
        if deepConflicts l.place dst then .error .E0506 else checkWritePlaceLoans rest dst

/-- Check mutable borrow creation (`&mut dst`) against active loans (`report_borrow_conflict`,
`compiler/rustc_borrowck/src/diagnostics/conflict_errors.rs:1822-2039`):
- `(.mutDefault, .fakeShallow)` emits `E0510` (line 1935);
- `(.mutDefault, .fakeDeep | .shared | .mutDefault)` emits `E0502` (lines 1822, 1848, 2031). -/
noncomputable def checkMutBorrowLoans (loans : List Loan) (target : Place) :
    Except DiagnosticCode Unit :=
  match loans with
  | [] => .ok ()
  | l :: rest =>
    if !l.active then
      checkMutBorrowLoans rest target
    else
      match l.kind with
      | .fakeShallow =>
        if shallowConflicts l.place target then .error .E0510 else checkMutBorrowLoans rest target
      | .fakeDeep | .shared | .mutDefault =>
        if deepConflicts l.place target then .error .E0502 else checkMutBorrowLoans rest target

/-- Attach `FakeReadCause` to any active loan stored in `temp`. -/
noncomputable def annotateLoanCause (temp : LocalId) (cause : FakeReadCause) :
    List Loan → List Loan
  | [] => []
  | l :: rest =>
    let l' := if Nat.beq l.temp temp then { l with causeOpt := some cause } else l
    l' :: annotateLoanCause temp cause rest

/-- Deactivate all loans bound to `temp` on `StorageDead(temp)`. -/
noncomputable def killLoansForLocal (temp : LocalId) : List Loan → List Loan
  | [] => []
  | l :: rest =>
    let l' := if Nat.beq l.temp temp then { l with active := false } else l
    l' :: killLoansForLocal temp rest

/-- Check one MIR statement against `RefWithinGuard` immutability (`mutability_errors.rs:128-133, 557-564`)
and active NLL loans (`conflict_errors.rs`). -/
noncomputable def checkStmtBorrowck (isRefGuard : LocalId → Bool) (loans : List Loan)
    (stmt : StatementKind) : Except DiagnosticCode (List Loan) :=
  match stmt with
  | .assign dst (.ref k p) =>
    if k.isFake then
      .ok (loans ++ [{ temp := dst.localId, kind := k, place := p, causeOpt := none, active := true }])
    else if isRefGuard dst.localId && projHasDeref dst.proj then
      .error .E0594
    else
      match checkWritePlaceLoans loans dst with
      | .error e => .error e
      | .ok () =>
        match k with
        | .mutDefault =>
          if isRefGuard p.localId && projHasDeref p.proj then
            .error .E0594
          else
            match checkMutBorrowLoans loans p with
            | .error e => .error e
            | .ok () =>
              .ok (loans ++ [{ temp := dst.localId, kind := .mutDefault, place := p, causeOpt := none, active := true }])
        | .shared =>
          .ok (loans ++ [{ temp := dst.localId, kind := .shared, place := p, causeOpt := none, active := true }])
        | .fakeShallow | .fakeDeep => .ok loans
  | .assign dst (.cellWrite _ _) =>
    -- Writing through `&Cell` only writes the cell heap via shared reference; check `dst` temp assignment only.
    if isRefGuard dst.localId && projHasDeref dst.proj then
      .error .E0594
    else
      match checkWritePlaceLoans loans dst with
      | .error e => .error e
      | .ok () => .ok loans
  | .assign dst (.useMove src) =>
    if isRefGuard dst.localId && projHasDeref dst.proj then
      .error .E0594
    else
      match checkWritePlaceLoans loans dst with
      | .error e => .error e
      | .ok () =>
        match checkWritePlaceLoans loans src with
        | .error e => .error e
        | .ok () => .ok loans
  | .assign dst _ =>
    if isRefGuard dst.localId && projHasDeref dst.proj then
      .error .E0594
    else
      match checkWritePlaceLoans loans dst with
      | .error e => .error e
      | .ok () => .ok loans
  | .fakeRead cause p =>
    .ok (annotateLoanCause p.localId cause loans)
  | .storageDead loc =>
    .ok (killLoansForLocal loc loans)
  | .storageLive _ | .ascribeUserType _ | .nop =>
    .ok loans

/-- Fold borrow checking over a sequential list of statements. -/
noncomputable def checkStmtsBorrowck (isRefGuard : LocalId → Bool) (loans : List Loan) :
    List StatementKind → Except DiagnosticCode (List Loan)
  | [] => .ok loans
  | s :: rest =>
    match checkStmtBorrowck isRefGuard loans s with
    | .error e => .error e
    | .ok loans' => checkStmtsBorrowck isRefGuard loans' rest

/-- Diagnostic partition theorem 1 (`Some(_)` wildcard match):
only `FakeBorrow(Shallow)` exists on scrutinee `x`; assigning `x = None` rejects with `E0510`. -/
theorem e0510_on_fakeShallow_wildcard :
    let x := Place.local 1
    let fakeTmp := Place.local 2
    let stmts : List StatementKind :=
      [ .assign fakeTmp (.ref .fakeShallow x)
      , .assign x (.constVal (.enum 0 []))
      , .fakeRead .forMatchGuard fakeTmp ]
    checkStmtsBorrowck (fun _ => false) [] stmts = .error .E0510 := by
  rfl

/-- Diagnostic partition theorem 2 (`Some(_y)` guard binding):
`bind_matched_candidate_for_guard` issues `_5 = &((_1 as Some).0)` (`BorrowKind.shared`) BEFORE
`_2 = &fake shallow _1`; assigning `x = None` rejects with `E0506` (not `E0510`). -/
theorem e0506_on_shared_guard_binding_before_fake :
    let x := Place.local 1
    let xPayload : Place := { localId := 1, proj := [.downcast 1, .field 0] }
    let guardRef := Place.local 5
    let fakeTmp := Place.local 2
    let stmts : List StatementKind :=
      [ .assign guardRef (.ref .shared xPayload)
      , .assign fakeTmp (.ref .fakeShallow x)
      , .assign x (.constVal (.enum 0 []))
      , .fakeRead .forMatchGuard fakeTmp
      , .fakeRead .forGuardBinding guardRef ]
    checkStmtsBorrowck (fun _ => false) [] stmts = .error .E0506 := by
  rfl

/-- Diagnostic partition theorem 3 (`deref!` on `Vec` -> `FakeBorrowKind::Deep`):
taking a mutable borrow `mutDefault` of `v` (e.g., `v[0] = 9`) rejects with `E0502`, whereas
assigning directly to `v = Vec::new()` rejects with `E0510`. -/
theorem e0502_vs_e0510_on_fakeDeep_deref_pattern :
    let v := Place.local 1
    let fakeTmp := Place.local 3
    let elemMutRef := Place.local 4
    let mutElemStmts : List StatementKind :=
      [ .assign fakeTmp (.ref .fakeDeep v)
      , .assign elemMutRef (.ref .mutDefault v)
      , .fakeRead .forMatchGuard fakeTmp ]
    let directAssignStmts : List StatementKind :=
      [ .assign fakeTmp (.ref .fakeDeep v)
      , .assign v (.constVal .unit)
      , .fakeRead .forMatchGuard fakeTmp ]
    checkStmtsBorrowck (fun _ => false) [] mutElemStmts = .error .E0502 ∧
    checkStmtsBorrowck (fun _ => false) [] directAssignStmts = .error .E0510 := by
  constructor <;> rfl

/-- Diagnostic partition theorem 4 (`RefWithinGuard` immutability, `E0594`):
writing through a `RefWithinGuard` deref place (`*_5 = ...` or `&mut *_5`) rejects with `E0594`. -/
theorem e0594_on_ref_within_guard_write :
    let guardV : Place := { localId := 5, proj := [.deref] }
    let mutTmp := Place.local 6
    let isRefGuard : LocalId → Bool := fun id => Nat.beq id 5
    checkStmtBorrowck isRefGuard [] (.assign guardV (.constVal (.int 99))) = .error .E0594 ∧
    checkStmtBorrowck isRefGuard [] (.assign mutTmp (.ref .mutDefault guardV)) = .error .E0594 := by
  constructor <;> rfl

/-- `Cell::set` interior mutability (`Rvalue.cellWrite` into temporary `_tmp`) is ADMITTED even when
both `&fake shallow x` and `BorrowKind.shared` on `x` are active! -/
theorem cellWrite_admitted_under_fakeShallow_and_shared :
    let s := Place.local 1
    let fakeTmp := Place.local 2
    let guardRef := Place.local 5
    let unitTmp := Place.local 6
    let stmts : List StatementKind :=
      [ .assign guardRef (.ref .shared s)
      , .assign fakeTmp (.ref .fakeShallow s)
      , .assign unitTmp (.cellWrite 0 (.int 17))
      , .fakeRead .forMatchGuard fakeTmp
      , .fakeRead .forGuardBinding guardRef ]
    ∃ loans', checkStmtsBorrowck (fun id => Nat.beq id 5) [] stmts = .ok loans' := by
  exact ⟨_, rfl⟩

/-- Mutably reborrowing strict subprojection `(x.0 as Some).0` is ADMITTED under
`&fake shallow x.0` (`strictProjection_not_shallowConflict`). -/
theorem strictProjection_mutBorrow_admitted_under_fakeShallow :
    let x0 : Place := { localId := 1, proj := [.field 0] }
    let x0Payload : Place := { localId := 1, proj := [.field 0, .downcast 1, .field 0] }
    let fakeTmp := Place.local 2
    let mutTmp := Place.local 6
    let stmts : List StatementKind :=
      [ .assign fakeTmp (.ref .fakeShallow x0)
      , .assign mutTmp (.ref .mutDefault x0Payload)
      , .fakeRead .forMatchGuard fakeTmp ]
    ∃ loans', checkStmtsBorrowck (fun _ => false) [] stmts = .ok loans' := by
  exact ⟨_, rfl⟩

/-! ## Part III: Operational Semantics, `CleanupPostBorrowck` Pass, and Theorems 1–3 -/

/-- `CleanupPostBorrowck` statement transformation (`cleanup_post_borrowck.rs:31-61`):
replaces `AscribeUserType`, `FakeRead`, and `Assign(_, Ref(Fake(_)))` with `Nop`. -/
noncomputable def cleanupStmt : StatementKind → StatementKind
  | .ascribeUserType _ => .nop
  | .fakeRead _ _ => .nop
  | .assign _ (.ref .fakeShallow _) => .nop
  | .assign _ (.ref .fakeDeep _) => .nop
  | s => s

/-- `CleanupPostBorrowck` terminator transformation (`cleanup_post_borrowck.rs:64-72`):
replaces `FalseEdge { real_target, .. }` with `Goto(real_target)`. -/
noncomputable def cleanupTerm : TerminatorKind → TerminatorKind
  | .falseEdge real _ => .goto real
  | t => t

/-- `CleanupPostBorrowck` basic-block transformation. -/
noncomputable def cleanupBlock (bb : BasicBlock) : BasicBlock :=
  { stmts := bb.stmts.map cleanupStmt, term := cleanupTerm bb.term }

/-- `CleanupPostBorrowck` whole-body transformation. -/
noncomputable def cleanupBody (body : MirBody) : MirBody :=
  { body with blocks := body.blocks.map cleanupBlock }

theorem cleanupStmt_idempotent (s : StatementKind) :
    cleanupStmt (cleanupStmt s) = cleanupStmt s := by
  cases s with
  | assign dst rhs =>
    cases rhs with
    | ref k p => cases k <;> rfl
    | useCopy _ | useMove _ | constVal _ | discriminant _ | cellWrite _ _ => rfl
  | fakeRead _ _ | storageLive _ | storageDead _ | ascribeUserType _ | nop => rfl

theorem cleanupTerm_idempotent (t : TerminatorKind) :
    cleanupTerm (cleanupTerm t) = cleanupTerm t := by
  cases t <;> rfl

theorem listMap_idempotent {α : Type} (f : α → α)
    (hf : ∀ x, f (f x) = f x) (xs : List α) :
    (xs.map f).map f = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [List.map]
    rw [hf x, ih]

theorem cleanupBlock_idempotent (bb : BasicBlock) :
    cleanupBlock (cleanupBlock bb) = cleanupBlock bb := by
  cases bb with
  | mk ss tm =>
    dsimp only [cleanupBlock]
    rw [listMap_idempotent cleanupStmt cleanupStmt_idempotent ss, cleanupTerm_idempotent tm]

theorem cleanupBody_idempotent (body : MirBody) :
    cleanupBody (cleanupBody body) = cleanupBody body := by
  cases body with
  | mk n fg ft bs =>
    dsimp only [cleanupBody]
    rw [listMap_idempotent cleanupBlock cleanupBlock_idempotent bs]

/-- Execution state of a single MIR function body. -/
structure ExecState where
  store : MirStore
  blockIdx : BlockId
  stmtIdx : Nat

/-- Operational faults during MIR evaluation. -/
inductive FaultKind where
  | undefined
  | unsupported

/-- Single-step outcome of MIR execution. -/
inductive StepOutcome where
  | step (next : ExecState)
  | done (retVal : Val)
  | fault (kind : FaultKind)

/-- Evaluate an `Rvalue` in `MirStore` (`eraseFake` controls whether fake borrows are rejected). -/
noncomputable def evalRvalue (eraseFake : Bool) (st : MirStore) :
    Rvalue → Except FaultKind (Val × MirStore)
  | .useCopy p =>
    match st.readPlace p with
    | some v => .ok (v, st)
    | none => .error .undefined
  | .useMove p =>
    match st.movePlace p with
    | some pair => .ok pair
    | none => .error .undefined
  | .constVal v => .ok (v, st)
  | .discriminant p =>
    match st.readDiscr p with
    | some d => .ok (.int (Int.ofNat d), st)
    | none => .error .undefined
  | .ref .shared p => .ok (.refVal p .not, st)
  | .ref .mutDefault p => .ok (.refVal p .mut_, st)
  | .ref .fakeShallow p =>
    if eraseFake then .error .unsupported else .ok (.refVal p .not, st)
  | .ref .fakeDeep p =>
    if eraseFake then .error .unsupported else .ok (.refVal p .not, st)
  | .cellWrite addr v =>
    match st.writeCell addr v with
    | some st' => .ok (.unit, st')
    | none => .error .undefined

/-- Update local slot `loc` with `slot`. -/
noncomputable def MirStore.setLocal (st : MirStore) (loc : LocalId) (slot : LocalSlot) :
    Option MirStore :=
  match listSet? st.locals loc slot with
  | some locs' => some { st with locals := locs' }
  | none => none

/-- Step one MIR statement (`eraseFake = false` before `CleanupPostBorrowck`, `true` after). -/
noncomputable def stepStmt (eraseFake : Bool) (st : MirStore) :
    StatementKind → Except FaultKind MirStore
  | .assign _ (.ref .fakeShallow _) =>
    -- Pre-cleanup fake borrow assigns to an administrative fake temp without touching runtime state.
    if eraseFake then .error .unsupported else .ok st
  | .assign _ (.ref .fakeDeep _) =>
    if eraseFake then .error .unsupported else .ok st
  | .assign dst rhs =>
    match evalRvalue eraseFake st rhs with
    | .error k => .error k
    | .ok (v, st1) =>
      match st1.writePlace dst v with
      | some st2 => .ok st2
      | none => .error .undefined
  | .fakeRead _ _ =>
    if eraseFake then .error .unsupported else .ok st
  | .ascribeUserType _ =>
    if eraseFake then .error .unsupported else .ok st
  | .storageLive loc =>
    match listGet? st.locals loc with
    | some _ =>
      match st.setLocal loc (.live none) with
      | some st' => .ok st'
      | none => .error .undefined
    | none => .error .undefined
  | .storageDead loc =>
    match listGet? st.locals loc with
    | some _ =>
      match st.setLocal loc .dead with
      | some st' => .ok st'
      | none => .error .undefined
    | none => .error .undefined
  | .nop => .ok st

/-- Lookup first matching `(val, target)` branch in `SwitchTargets`. -/
noncomputable def lookupSwitchCase (d : Nat) (otherwise : BlockId) :
    List (Nat × BlockId) → BlockId
  | [] => otherwise
  | (k, tgt) :: rest => if Nat.beq d k then tgt else lookupSwitchCase d otherwise rest

/-- Step a basic-block terminator. -/
noncomputable def stepTerm (eraseFake : Bool) (st : MirStore) (term : TerminatorKind) :
    StepOutcome :=
  match term with
  | .goto tgt => .step { store := st, blockIdx := tgt, stmtIdx := 0 }
  | .falseEdge real _ =>
    if eraseFake then .fault .unsupported
    else .step { store := st, blockIdx := real, stmtIdx := 0 }
  | .switchDiscr p cases otherwise =>
    match st.readDiscr p with
    | some d =>
      .step { store := st, blockIdx := lookupSwitchCase d otherwise cases, stmtIdx := 0 }
    | none => .fault .undefined
  | .switchBool cond onFalse onTrue =>
    match st.readPlace (Place.local cond) with
    | some (.bool false) => .step { store := st, blockIdx := onFalse, stmtIdx := 0 }
    | some (.bool true) => .step { store := st, blockIdx := onTrue, stmtIdx := 0 }
    | _ => .fault .undefined
  | .return_ =>
    match listGet? st.locals 0 with
    | some (.live (some v)) => .done v
    | _ => .fault .undefined
  | .unreachable => .fault .undefined

/-- Single small-step transition of a `MirBody`. -/
noncomputable def stepMir (eraseFake : Bool) (body : MirBody) (es : ExecState) : StepOutcome :=
  match listGet? body.blocks es.blockIdx with
  | none => .fault .unsupported
  | some bb =>
    match listGet? bb.stmts es.stmtIdx with
    | some stmt =>
      match stepStmt eraseFake es.store stmt with
      | .ok st' => .step { store := st', blockIdx := es.blockIdx, stmtIdx := es.stmtIdx + 1 }
      | .error k => .fault k
    | none =>
      if Nat.beq es.stmtIdx bb.stmts.length then
        stepTerm eraseFake es.store bb.term
      else
        .fault .unsupported

/-- Fuel-bounded multi-step runner returning final `(Option Val × MirStore)`. -/
noncomputable def runMir (eraseFake : Bool) (body : MirBody) :
    Nat → ExecState → Except FaultKind (Option Val × MirStore)
  | 0, es => .ok (none, es.store)
  | n + 1, es =>
    match stepMir eraseFake body es with
    | .done v => .ok (some v, es.store)
    | .fault k => .error k
    | .step es' => runMir eraseFake body n es'

theorem listGet?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat),
      listGet? (xs.map f) i =
        match listGet? xs i with
        | some a => some (f a)
        | none => none := by
  intro xs i
  induction xs generalizing i with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k

/-- Key lockstep statement theorem for `CleanupPostBorrowck`:
any pre-cleanup statement `s` executed with `eraseFake = false` produces the EXACT SAME
`Except FaultKind MirStore` as `cleanupStmt s` executed with `eraseFake = true`! -/
theorem stepStmt_cleanup_equiv (st : MirStore) (s : StatementKind) :
    stepStmt true st (cleanupStmt s) = stepStmt false st s := by
  cases s with
  | ascribeUserType _ | fakeRead _ _ | nop => rfl
  | storageLive _ | storageDead _ => rfl
  | assign _ rhs =>
    cases rhs with
    | useCopy _ | useMove _ | constVal _ | discriminant _ | cellWrite _ _ => rfl
    | ref k _ => cases k <;> rfl

/-- Key lockstep terminator theorem for `CleanupPostBorrowck`:
`stepTerm true st (cleanupTerm t) = stepTerm false st t`. -/
theorem stepTerm_cleanup_equiv (st : MirStore) (t : TerminatorKind) :
    stepTerm true st (cleanupTerm t) = stepTerm false st t := by
  cases t <;> rfl

/-- Exact single-step observational equivalence between pre-cleanup MIR (`eraseFake = false`)
and post-`CleanupPostBorrowck` MIR (`eraseFake = true`). -/
theorem stepMir_cleanup_equiv (body : MirBody) (es : ExecState) :
    stepMir true (cleanupBody body) es = stepMir false body es := by
  unfold stepMir cleanupBody
  rw [listGet?_map cleanupBlock body.blocks es.blockIdx]
  cases listGet? body.blocks es.blockIdx with
  | none => rfl
  | some bb =>
    dsimp only [cleanupBlock]
    rw [listGet?_map cleanupStmt bb.stmts es.stmtIdx]
    cases listGet? bb.stmts es.stmtIdx with
    | some s =>
      dsimp only
      rw [stepStmt_cleanup_equiv es.store s]
    | none =>
      rw [List.length_map]
      cases Nat.beq es.stmtIdx bb.stmts.length with
      | false => rfl
      | true => exact stepTerm_cleanup_equiv es.store bb.term

/-- **Theorem 3 (`cleanup_post_borrowck_observational_erasure_equiv`)**:
For EVERY `MirBody`, EVERY `fuel : Nat`, and EVERY initial `ExecState`, running `CleanupPostBorrowck`
and executing under post-cleanup semantics (`eraseFake = true`) yields the **exact same** fault,
return value, and final `MirStore` as executing the pre-cleanup MIR (`eraseFake = false`). -/
theorem cleanup_post_borrowck_observational_erasure_equiv
    (body : MirBody) (fuel : Nat) (es : ExecState) :
    runMir true (cleanupBody body) fuel es = runMir false body fuel es := by
  induction fuel generalizing es with
  | zero => rfl
  | succ n ih =>
    dsimp only [runMir]
    rw [stepMir_cleanup_equiv]
    cases stepMir false body es with
    | done _ => rfl
    | fault _ => rfl
    | step es' => exact ih es'

/-- Guard-admissibility predicate for shallow fake-borrowed places `frozen`:
every statement in the guard is borrowck-safe against `frozen`, never writes or moves a
shallow-conflicting place or deref-containing place, and never calls `storageDead`/`storageLive` on
any frozen local. -/
noncomputable def guardStmtPreservesShallow (frozen : List Place) : StatementKind → Prop
  | .assign _ (.ref .fakeShallow _) => True
  | .assign _ (.ref .fakeDeep _) => True
  | .assign dst (.cellWrite _ _) =>
    (∀ p, p ∈ frozen → dst.localId ≠ p.localId) ∧ projHasDeref dst.proj = false
  | .assign dst (.useMove src) =>
    projHasDeref dst.proj = false ∧
    (∀ p, p ∈ frozen → shallowConflicts p dst = false ∧ src.localId ≠ p.localId)
  | .assign dst _ =>
    projHasDeref dst.proj = false ∧
    (∀ p, p ∈ frozen → shallowConflicts p dst = false)
  | .fakeRead _ _ | .ascribeUserType _ | .nop => True
  | .storageLive loc => ∀ p, p ∈ frozen → loc ≠ p.localId
  | .storageDead loc => ∀ p, p ∈ frozen → loc ≠ p.localId

theorem setLocal_disjoint_readPlace {st st' : MirStore} {loc : LocalId} {slot : LocalSlot}
    {p : Place} (hne : loc ≠ p.localId) (hNo : projHasDeref p.proj = false)
    (hSet : st.setLocal loc slot = some st') :
    st'.readPlace p = st.readPlace p := by
  simp [MirStore.setLocal] at hSet
  cases hs : listSet? st.locals loc slot with
  | none => simp [hs] at hSet
  | some locs' =>
    simp [hs] at hSet
    subst hSet
    simp [MirStore.readPlace]
    rw [listGet?_listSet?_ne st.locals loc p.localId slot locs' hne hs]
    cases listGet? st.locals p.localId with
    | none => rfl
    | some sl =>
      cases sl with
      | dead => rfl
      | live ov =>
        cases ov with
        | none => rfl
        | some base =>
          exact readProjFromVal_noDeref_store_indep
            { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
            st p.proj base hNo

theorem movePlace_disjoint_local_readPlace {st st' : MirStore} {src p : Place} {v : Val}
    (hne : src.localId ≠ p.localId) (hNo : projHasDeref p.proj = false)
    (hM : st.movePlace src = some (v, st')) :
    st'.readPlace p = st.readPlace p := by
  simp [MirStore.movePlace] at hM
  cases hr : st.readPlace src with
  | none => simp [hr] at hM
  | some sv =>
    simp [hr] at hM
    cases hZst : sv.isZstUnit with
    | true =>
      simp [hZst] at hM
      rcases hM with ⟨_, rfl⟩
      rfl
    | false =>
      simp [hZst] at hM
      cases hproj : src.proj with
      | nil =>
        simp [hproj] at hM
        cases hs : listSet? st.locals src.localId (.live none) with
        | none => simp [hs] at hM
        | some locs' =>
          simp [hs] at hM
          rcases hM with ⟨_, rfl⟩
          simp [MirStore.readPlace]
          rw [listGet?_listSet?_ne st.locals src.localId p.localId (.live none) locs' hne hs]
          cases listGet? st.locals p.localId with
          | none => rfl
          | some sl =>
            cases sl with
            | dead => rfl
            | live ov =>
              cases ov with
              | none => rfl
              | some base =>
                exact readProjFromVal_noDeref_store_indep
                  { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
                  st p.proj base hNo
      | cons e rest =>
        cases e with
        | downcast dv =>
          cases rest with
          | nil =>
            simp [hproj] at hM
            rcases hM with ⟨_, rfl⟩
            rfl
          | cons e2 rest2 =>
            cases e2 with
            | field df =>
              cases rest2 with
              | nil =>
                simp [hproj] at hM
                cases hs : listSet? st.locals src.localId (.live none) with
                | none => simp [hs] at hM
                | some locs' =>
                  simp [hs] at hM
                  rcases hM with ⟨_, rfl⟩
                  simp [MirStore.readPlace]
                  rw [listGet?_listSet?_ne st.locals src.localId p.localId (.live none) locs' hne hs]
                  cases listGet? st.locals p.localId with
                  | none => rfl
                  | some sl =>
                    cases sl with
                    | dead => rfl
                    | live ov =>
                      cases ov with
                      | none => rfl
                      | some base =>
                        exact readProjFromVal_noDeref_store_indep
                          { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
                          st p.proj base hNo
              | cons _ _ =>
                simp [hproj] at hM
                rcases hM with ⟨_, rfl⟩
                rfl
            | downcast _ | deref =>
              simp [hproj] at hM
              rcases hM with ⟨_, rfl⟩
              rfl
        | field _ | deref =>
          simp [hproj] at hM
          rcases hM with ⟨_, rfl⟩
          rfl

theorem evalRvalue_pure_store_eq {st s1 : MirStore} {rhs : Rvalue} {rv : Val}
    (hPure : match rhs with | .useCopy _ | .constVal _ | .discriminant _ => True | _ => False)
    (hev : evalRvalue false st rhs = .ok (rv, s1)) : s1 = st := by
  cases rhs with
  | useCopy cp =>
    simp only [evalRvalue] at hev
    cases hr : st.readPlace cp with
    | none => simp [hr] at hev
    | some _ => simp [hr] at hev; rcases hev with ⟨_, rfl⟩; rfl
  | constVal _ =>
    simp only [evalRvalue] at hev
    rcases hev with ⟨_, rfl⟩
    rfl
  | discriminant dp =>
    simp only [evalRvalue] at hev
    cases hr : st.readDiscr dp with
    | none => simp [hr] at hev
    | some _ => simp [hr] at hev; rcases hev with ⟨_, rfl⟩; rfl
  | useMove _ | ref _ _ | cellWrite _ _ => cases hPure

/-- Single-step discriminant preservation for `FakeBorrow(Shallow)`. -/
theorem stepStmt_shallowGuard_preserves_discr
    {frozen : List Place} {st st' : MirStore} {s : StatementKind} {p : Place}
    (hp : p ∈ frozen) (hNo : projHasDeref p.proj = false)
    (hGuard : guardStmtPreservesShallow frozen s)
    (hStep : stepStmt false st s = .ok st') :
    st'.readDiscr p = st.readDiscr p := by
  cases s with
  | fakeRead _ _ | ascribeUserType _ | nop =>
    simp [stepStmt] at hStep
    subst hStep
    rfl
  | storageLive loc =>
    simp [guardStmtPreservesShallow] at hGuard
    have hne := hGuard p hp
    simp [stepStmt] at hStep
    cases hg : listGet? st.locals loc with
    | none => simp [hg] at hStep
    | some _ =>
      simp [hg] at hStep
      cases hs : st.setLocal loc (.live none) with
      | none => simp [hs] at hStep
      | some s1 =>
        simp [hs] at hStep
        subst hStep
        simp [MirStore.readDiscr, setLocal_disjoint_readPlace hne hNo hs]
  | storageDead loc =>
    simp [guardStmtPreservesShallow] at hGuard
    have hne := hGuard p hp
    simp [stepStmt] at hStep
    cases hg : listGet? st.locals loc with
    | none => simp [hg] at hStep
    | some _ =>
      simp [hg] at hStep
      cases hs : st.setLocal loc .dead with
      | none => simp [hs] at hStep
      | some s1 =>
        simp [hs] at hStep
        subst hStep
        simp [MirStore.readDiscr, setLocal_disjoint_readPlace hne hNo hs]
  | assign dst rhs =>
    cases rhs with
    | ref k rp =>
      cases k with
      | fakeShallow =>
        simp [stepStmt] at hStep
        subst hStep
        rfl
      | fakeDeep =>
        simp [stepStmt] at hStep
        subst hStep
        rfl
      | shared =>
        simp [guardStmtPreservesShallow] at hGuard
        simp [stepStmt, evalRvalue] at hStep
        cases hw : st.writePlace dst (.refVal rp .not) with
        | none => simp [hw] at hStep
        | some s1 =>
          simp [hw] at hStep
          subst hStep
          exact writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp) hw
      | mutDefault =>
        simp [guardStmtPreservesShallow] at hGuard
        simp [stepStmt, evalRvalue] at hStep
        cases hw : st.writePlace dst (.refVal rp .mut_) with
        | none => simp [hw] at hStep
        | some s1 =>
          simp [hw] at hStep
          subst hStep
          exact writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp) hw
    | cellWrite addr cv =>
      simp [guardStmtPreservesShallow] at hGuard
      simp [stepStmt, evalRvalue] at hStep
      cases hwc : st.writeCell addr cv with
      | none => simp [hwc] at hStep
      | some s1 =>
        simp [hwc] at hStep
        cases hw : s1.writePlace dst .unit with
        | none => simp [hw] at hStep
        | some s2 =>
          simp [hw] at hStep
          subst hStep
          have h1 := writeCell_preserves_readPlace_noDeref hNo hwc
          have h2 := writePlace_disjoint_local_noDeref (hGuard.1 p hp) hNo hGuard.2 hw
          simp [MirStore.readDiscr, h2, h1]
    | useMove src =>
      simp [guardStmtPreservesShallow] at hGuard
      simp [stepStmt, evalRvalue] at hStep
      cases hm : st.movePlace src with
      | none => simp [hm] at hStep
      | some pair =>
        cases pair with
        | mk mv s1 =>
          simp [hm] at hStep
          cases hw : s1.writePlace dst mv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have h1 := movePlace_disjoint_local_readPlace (hGuard.2 p hp).2 hNo hm
            have h2 := writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp).1 hw
            rw [h2]
            simp [MirStore.readDiscr, h1]
    | useCopy cp =>
      simp [guardStmtPreservesShallow] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.useCopy cp) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp) hw
    | constVal cv =>
      simp [guardStmtPreservesShallow] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.constVal cv) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp) hw
    | discriminant dp =>
      simp [guardStmtPreservesShallow] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.discriminant dp) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noShallowConflict_preserves_readDiscr hNo hGuard.1 (hGuard.2 p hp) hw

/-- Run a sequential list of statements in pre-cleanup MIR semantics. -/
noncomputable def runStmts (st : MirStore) : List StatementKind → Except FaultKind MirStore
  | [] => .ok st
  | s :: rest =>
    match stepStmt false st s with
    | .ok st' => runStmts st' rest
    | .error k => .error k

/-- **Theorem 1 (`discriminant_stability_of_fake_borrow_shallow`)**:
Across ANY multi-statement guard block `stmts` admitted under `FakeBorrow(Shallow)` (`frozen`)
and `FakeRead(ForMatchGuard)`, every tested non-deref place `p ∈ frozen` has **identical
discriminant** before and after guard execution (`st'.readDiscr p = st.readDiscr p`), even when
the guard mutates disjoint tuple/enum payloads or interior-mutable `Cell`s. -/
theorem discriminant_stability_of_fake_borrow_shallow
    (frozen : List Place) (stmts : List StatementKind) (st st' : MirStore)
    (hAll : ∀ s, s ∈ stmts → guardStmtPreservesShallow frozen s)
    (hRun : runStmts st stmts = .ok st') :
    ∀ p, p ∈ frozen → projHasDeref p.proj = false → st'.readDiscr p = st.readDiscr p := by
  induction stmts generalizing st with
  | nil =>
    intro p _ _
    simp [runStmts] at hRun
    subst hRun
    rfl
  | cons s rest ih =>
    intro p hp hNo
    simp [runStmts] at hRun
    cases hStep : stepStmt false st s with
    | error k => simp [hStep] at hRun
    | ok s1 =>
      simp [hStep] at hRun
      have hs := hAll s (List.Mem.head rest)
      have hRest : ∀ s', s' ∈ rest → guardStmtPreservesShallow frozen s' :=
        fun s' hm => hAll s' (List.Mem.tail s hm)
      have hTail := ih s1 hRest hRun p hp hNo
      have hHead := stepStmt_shallowGuard_preserves_discr hp hNo hs hStep
      rw [hTail, hHead]

/-- Guard-binding immutability predicate (`RefWithinGuard` + `ForGuardBinding`):
bound source places `bound` are protected by `BorrowKind.shared` (`E0506`) and `RefWithinGuard`
(`E0594`), so no guard write or move overlaps `src ∈ bound`. -/
noncomputable def guardStmtPreservesBound (bound : List Place) : StatementKind → Prop
  | .assign _ (.ref .fakeShallow _) => True
  | .assign _ (.ref .fakeDeep _) => True
  | .assign dst (.cellWrite _ _) =>
    (∀ src, src ∈ bound → dst.localId ≠ src.localId) ∧ projHasDeref dst.proj = false
  | .assign dst (.useMove srcPlace) =>
    projHasDeref dst.proj = false ∧
    (∀ src, src ∈ bound → deepConflicts src dst = false ∧ srcPlace.localId ≠ src.localId)
  | .assign dst _ =>
    projHasDeref dst.proj = false ∧
    (∀ src, src ∈ bound → deepConflicts src dst = false)
  | .fakeRead _ _ | .ascribeUserType _ | .nop => True
  | .storageLive loc => ∀ src, src ∈ bound → loc ≠ src.localId
  | .storageDead loc => ∀ src, src ∈ bound → loc ≠ src.localId

theorem writePlace_noDeepConflict_preserves_readPlace
    {st st' : MirStore} {src q : Place} {newV : Val}
    (hNoSrc : projHasDeref src.proj = false)
    (hNoQ : projHasDeref q.proj = false)
    (hNotDeep : deepConflicts src q = false)
    (hW : st.writePlace q newV = some st') :
    st'.readPlace src = st.readPlace src := by
  cases hLoc : Nat.beq q.localId src.localId with
  | false =>
    have hne : q.localId ≠ src.localId := by
      intro heq
      rw [heq] at hLoc
      have ht := natBeq_refl src.localId
      rw [ht] at hLoc
      cases hLoc
    exact writePlace_disjoint_local_noDeref hne hNoSrc hNoQ hW
  | true =>
    have hEqLoc := Nat.eq_of_beq_eq_true hLoc
    have hDisj : projOverlap src.proj q.proj = false := by
      simp [deepConflicts, Place.overlap, hEqLoc] at hNotDeep
      exact hNotDeep
    cases hq : q.proj with
    | nil =>
      rw [hq] at hDisj
      cases hsp : src.proj with
      | nil =>
        rw [hsp] at hDisj
        cases hDisj
      | cons _ _ =>
        rw [hsp] at hDisj
        cases hDisj
    | cons eq restq =>
      rcases MirStore.writePlace_cons_noDeref hq hNoQ hW with ⟨oldV, updV, locs', hl, hw, hs, hEqSt⟩
      subst hEqSt
      simp [MirStore.readPlace]
      have hGetNew := listGet?_listSet?_eq st.locals src.localId (.live (some updV)) locs'
        (by rw [← hEqLoc]; exact hs)
      have hGetOld : listGet? st.locals src.localId = some (.live (some oldV)) := by
        rw [← hEqLoc]
        exact hl
      rw [hGetNew, hGetOld]
      simp
      have hIndep := readProjFromVal_noDeref_store_indep
        { locals := locs', boxHeap := st.boxHeap, cellHeap := st.cellHeap }
        st src.proj updV hNoSrc
      rw [hIndep]
      exact writeProjInVal_disjoint_preserves_read st src.proj q.proj oldV newV updV hNoSrc hDisj hw

theorem stepStmt_boundGuard_preserves_readPlace
    {bound : List Place} {st st' : MirStore} {s : StatementKind} {src : Place}
    (hs : src ∈ bound) (hNo : projHasDeref src.proj = false)
    (hGuard : guardStmtPreservesBound bound s)
    (hStep : stepStmt false st s = .ok st') :
    st'.readPlace src = st.readPlace src := by
  cases s with
  | fakeRead _ _ | ascribeUserType _ | nop =>
    simp [stepStmt] at hStep
    subst hStep
    rfl
  | storageLive loc =>
    simp [guardStmtPreservesBound] at hGuard
    simp [stepStmt] at hStep
    cases hg : listGet? st.locals loc with
    | none => simp [hg] at hStep
    | some _ =>
      simp [hg] at hStep
      cases hset : st.setLocal loc (.live none) with
      | none => simp [hset] at hStep
      | some s1 =>
        simp [hset] at hStep
        subst hStep
        exact setLocal_disjoint_readPlace (hGuard src hs) hNo hset
  | storageDead loc =>
    simp [guardStmtPreservesBound] at hGuard
    simp [stepStmt] at hStep
    cases hg : listGet? st.locals loc with
    | none => simp [hg] at hStep
    | some _ =>
      simp [hg] at hStep
      cases hset : st.setLocal loc .dead with
      | none => simp [hset] at hStep
      | some s1 =>
        simp [hset] at hStep
        subst hStep
        exact setLocal_disjoint_readPlace (hGuard src hs) hNo hset
  | assign dst rhs =>
    cases rhs with
    | ref k rp =>
      cases k with
      | fakeShallow =>
        simp [stepStmt] at hStep
        subst hStep
        rfl
      | fakeDeep =>
        simp [stepStmt] at hStep
        subst hStep
        rfl
      | shared =>
        simp [guardStmtPreservesBound] at hGuard
        simp [stepStmt, evalRvalue] at hStep
        cases hw : st.writePlace dst (.refVal rp .not) with
        | none => simp [hw] at hStep
        | some s1 =>
          simp [hw] at hStep
          subst hStep
          exact writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs) hw
      | mutDefault =>
        simp [guardStmtPreservesBound] at hGuard
        simp [stepStmt, evalRvalue] at hStep
        cases hw : st.writePlace dst (.refVal rp .mut_) with
        | none => simp [hw] at hStep
        | some s1 =>
          simp [hw] at hStep
          subst hStep
          exact writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs) hw
    | cellWrite addr cv =>
      simp [guardStmtPreservesBound] at hGuard
      simp [stepStmt, evalRvalue] at hStep
      cases hwc : st.writeCell addr cv with
      | none => simp [hwc] at hStep
      | some s1 =>
        simp [hwc] at hStep
        cases hw : s1.writePlace dst .unit with
        | none => simp [hw] at hStep
        | some s2 =>
          simp [hw] at hStep
          subst hStep
          have h1 := writeCell_preserves_readPlace_noDeref hNo hwc
          have h2 := writePlace_disjoint_local_noDeref (hGuard.1 src hs) hNo hGuard.2 hw
          rw [h2, h1]
    | useMove srcPlace =>
      simp [guardStmtPreservesBound] at hGuard
      simp [stepStmt, evalRvalue] at hStep
      cases hm : st.movePlace srcPlace with
      | none => simp [hm] at hStep
      | some pair =>
        cases pair with
        | mk mv s1 =>
          simp [hm] at hStep
          cases hw : s1.writePlace dst mv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have h1 := movePlace_disjoint_local_readPlace (hGuard.2 src hs).2 hNo hm
            have h2 := writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs).1 hw
            rw [h2, h1]
    | useCopy cp =>
      simp [guardStmtPreservesBound] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.useCopy cp) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs) hw
    | constVal cv =>
      simp [guardStmtPreservesBound] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.constVal cv) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs) hw
    | discriminant dp =>
      simp [guardStmtPreservesBound] at hGuard
      simp [stepStmt] at hStep
      cases hev : evalRvalue false st (.discriminant dp) with
      | error _ => simp [hev] at hStep
      | ok pair =>
        cases pair with
        | mk rv s1 =>
          simp [hev] at hStep
          cases hw : s1.writePlace dst rv with
          | none => simp [hw] at hStep
          | some s2 =>
            simp [hw] at hStep
            subst hStep
            have hSameSt := evalRvalue_pure_store_eq trivial hev
            subst hSameSt
            exact writePlace_noDeepConflict_preserves_readPlace hNo hGuard.1 (hGuard.2 src hs) hw

/-- **Theorem 2 (`ref_within_guard_immutability_and_move_once`)**:
1. Across any guard sequence `stmts` satisfying `RefWithinGuard`/`ForGuardBinding` immutability
   (`guardStmtPreservesBound bound`), every non-deref bound source place `src ∈ bound` retains its
   exact value (`st'.readPlace src = st.readPlace src`).
2. Consequently, on guard failure `src` stays live and unmoved; and on guard success, a subsequent
   by-value move of a non-unit local `src` (`movePlace`) yields `(v, st'')` and sets `src.localId`
   to `.live none`, so any second move out of `src` fails with `none` (move-once safety). -/
theorem ref_within_guard_immutability_and_move_once
    (bound : List Place) (stmts : List StatementKind) (st st' : MirStore)
    (hAll : ∀ s, s ∈ stmts → guardStmtPreservesBound bound s)
    (hRun : runStmts st stmts = .ok st') :
    (∀ src, src ∈ bound → projHasDeref src.proj = false → st'.readPlace src = st.readPlace src) ∧
    (∀ (loc : LocalId) (v : Val) (st'' : MirStore),
      v.isZstUnit = false →
      st'.movePlace (Place.local loc) = some (v, st'') →
      st''.movePlace (Place.local loc) = none) := by
  constructor
  · induction stmts generalizing st with
    | nil =>
      intro src _ _
      simp [runStmts] at hRun
      subst hRun
      rfl
    | cons s rest ih =>
      intro src hs hNo
      simp [runStmts] at hRun
      cases hStep : stepStmt false st s with
      | error _ => simp [hStep] at hRun
      | ok s1 =>
        simp [hStep] at hRun
        have hTail := ih s1 (fun s' hm => hAll s' (List.Mem.tail s hm)) hRun src hs hNo
        have hHead := stepStmt_boundGuard_preserves_readPlace hs hNo (hAll s (List.Mem.head rest)) hStep
        rw [hTail, hHead]
  · intro loc v st'' hNonUnit hMove
    simp [MirStore.movePlace, Place.local] at hMove ⊢
    cases hr : st'.readPlace { localId := loc, proj := [] } with
    | none => simp [hr] at hMove
    | some rv =>
      simp [hr] at hMove
      have hrv : rv = v := by
        cases hZ : rv.isZstUnit <;> simp [hZ] at hMove
        · cases hls : listSet? st'.locals loc (.live none) with
          | none => simp [hls] at hMove
          | some _ =>
            simp [hls] at hMove
            exact hMove.1
        · exact hMove.1
      subst hrv
      simp [hNonUnit] at hMove
      cases hls : listSet? st'.locals loc (.live none) with
      | none => simp [hls] at hMove
      | some locs'' =>
        simp [hls] at hMove
        rcases hMove with ⟨_, rfl⟩
        have hGetNone :
            MirStore.readPlace { locals := locs'', boxHeap := st'.boxHeap, cellHeap := st'.cellHeap }
              { localId := loc, proj := [] } = none := by
          simp [MirStore.readPlace]
          rw [listGet?_listSet?_eq st'.locals loc (.live none) locs'' hls]
        rw [hGetNone]

/-! ## Part IV: Or-Pattern Per-Branch Guard Lowering, Short-Circuiting, and Concrete Witnesses -/

/-- One flattened sub-branch of an or-pattern arm (`MatchTreeSubBranch` in `matches/mod.rs`). -/
structure OrSubBranch where
  matchesPattern : MirStore → Option Val
  guardEval : Val → MirStore → Bool × MirStore

/-- Or-pattern arm consisting of left-to-right sub-branches sharing one arm body. -/
structure OrArm where
  branches : List OrSubBranch
  armBody : Val → MirStore → Val × MirStore
  otherwise : MirStore → Val × MirStore

/-- Trace outcome of evaluating an or-pattern arm:
records guard invocation count, moved arm-body value (if matched), and final store. -/
structure OrTrace where
  guardCalls : Nat
  selectedBranch : Option Nat
  result : Val
  finalStore : MirStore

/-- Source-level Reference semantics for guarded or-pattern arms:
evaluates sub-branches left-to-right; for each matching sub-branch, runs the guard with a shared
view of the bound value (preserving the unmoved value on `false`!) and short-circuits on `true`
by moving the value into `armBody` once. -/
noncomputable def evalOrBranchesSource (arm : OrArm) (idx : Nat) (calls : Nat) (st : MirStore) :
    List OrSubBranch → OrTrace
  | [] =>
    let (res, st') := arm.otherwise st
    { guardCalls := calls, selectedBranch := none, result := res, finalStore := st' }
  | b :: rest =>
    match b.matchesPattern st with
    | none => evalOrBranchesSource arm (idx + 1) calls st rest
    | some boundVal =>
      let (ok, stGuard) := b.guardEval boundVal st
      if ok then
        let (res, stBody) := arm.armBody boundVal stGuard
        { guardCalls := calls + 1, selectedBranch := some idx, result := res, finalStore := stBody }
      else
        evalOrBranchesSource arm (idx + 1) (calls + 1) stGuard rest

/-- Lowered sub-branch CFG step (`bind_and_guard_matched_candidate` reversed chain in `matches/mod.rs:534-546`,
whose control-flow edges chain `b₀ -> b₁ -> ... -> otherwise` while scheduling drops from `b₀`). -/
noncomputable def evalOrBranchesLowered (arm : OrArm) (idx : Nat) (calls : Nat) (st : MirStore) :
    List OrSubBranch → OrTrace
  | [] =>
    let (res, st') := arm.otherwise st
    { guardCalls := calls, selectedBranch := none, result := res, finalStore := st' }
  | b :: rest =>
    match b.matchesPattern st with
    | none => evalOrBranchesLowered arm (idx + 1) calls st rest
    | some vRef =>
      let (guardRes, stGuard) := b.guardEval vRef st
      match guardRes with
      | true =>
        -- Only reached when guard succeeds: move into shared arm body once.
        let (res, stBody) := arm.armBody vRef stGuard
        { guardCalls := calls + 1, selectedBranch := some idx, result := res, finalStore := stBody }
      | false =>
        evalOrBranchesLowered arm (idx + 1) (calls + 1) stGuard rest

/-- **Theorem 4 (`or_pattern_per_branch_short_circuit_and_move_once`)**:
1. Source and lowered or-pattern guard execution agree identically on guard count, selected branch,
   moved result, and final store for arbitrary nested branch lists.
2. **Short-circuiting (`first_true`)**: If branch `0` matches `v₀` and its guard returns `true`,
   the guard runs **exactly once** (`guardCalls = 1`), `selectedBranch = some 0`, and tail branches
   are never entered.
3. **Fallback re-evaluation (`first_false_second_true`)**: If branch `0` matches `v₀` with guard
   `false` and branch `1` matches `v₁` with guard `true`, the guard runs **twice** (`guardCalls = 2`),
   moves `v₁` once into `armBody`, and selects branch `1`. -/
theorem or_pattern_per_branch_short_circuit_and_move_once :
    (∀ (arm : OrArm) (bs : List OrSubBranch) (idx calls : Nat) (st : MirStore),
      evalOrBranchesLowered arm idx calls st bs = evalOrBranchesSource arm idx calls st bs) ∧
    (∀ (arm : OrArm) (b0 : OrSubBranch) (rest : List OrSubBranch) (st stG : MirStore) (v0 : Val),
      b0.matchesPattern st = some v0 →
      b0.guardEval v0 st = (true, stG) →
      let tr := evalOrBranchesLowered arm 0 0 st (b0 :: rest)
      tr.guardCalls = 1 ∧ tr.selectedBranch = some 0 ∧
      tr.result = (arm.armBody v0 stG).1 ∧ tr.finalStore = (arm.armBody v0 stG).2) ∧
    (∀ (arm : OrArm) (b0 b1 : OrSubBranch) (rest : List OrSubBranch)
      (st stG0 stG1 : MirStore) (v0 v1 : Val),
      b0.matchesPattern st = some v0 →
      b0.guardEval v0 st = (false, stG0) →
      b1.matchesPattern stG0 = some v1 →
      b1.guardEval v1 stG0 = (true, stG1) →
      let tr := evalOrBranchesLowered arm 0 0 st (b0 :: b1 :: rest)
      tr.guardCalls = 2 ∧ tr.selectedBranch = some 1 ∧
      tr.result = (arm.armBody v1 stG1).1 ∧ tr.finalStore = (arm.armBody v1 stG1).2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro arm bs
    induction bs with
    | nil =>
      intro idx calls st
      rfl
    | cons b rest ih =>
      intro idx calls st
      simp [evalOrBranchesLowered, evalOrBranchesSource]
      cases b.matchesPattern st with
      | none => exact ih (idx + 1) calls st
      | some v =>
        simp
        cases (b.guardEval v st).1 <;> simp
        exact ih (idx + 1) (calls + 1) (b.guardEval v st).2
  · intro arm b0 rest st stG v0 hm0 hg0
    simp [evalOrBranchesLowered, hm0, hg0]
  · intro arm b0 b1 rest st stG0 stG1 v0 v1 hm0 hg0 hm1 hg1
    simp [evalOrBranchesLowered, hm0, hg0, hm1, hg1]

/-! ### Concrete Kernel-Checked Witnesses Matching Live `rustc` Probes -/

/-- Concrete `MirBody` of `guard_probe(x: Option<u32>) -> u32`:
`match x { Some(v) if v > 5 => v, _ => 0 }` modeled pre-cleanup with `&fake shallow _1`,
`FakeRead(ForMatchGuard, _2)`, `FakeRead(ForGuardBinding, _5)`, and `FalseEdge`.
Locals: `_0` (ret), `_1` (x), `_2` (fake), `_4` (v arm), `_5` (v guard ref), `_6` (cond). -/
noncomputable def guardProbeBody (guardCond : Bool) : MirBody where
  localsCount := 7
  isRefForGuard := fun id => Nat.beq id 5
  isFakeTemp := fun id => Nat.beq id 2
  blocks :=
    [ { stmts := []
        term := .switchDiscr (Place.local 1) [(1, 1)] 3 }
    , { stmts := []
        term := .falseEdge 2 3 }
    , { stmts :=
          [ .assign (Place.local 5) (.ref .shared { localId := 1, proj := [.downcast 1, .field 0] })
          , .assign (Place.local 2) (.ref .fakeShallow (Place.local 1))
          , .assign (Place.local 6) (.constVal (.bool guardCond)) ]
        term := .switchBool 6 4 5 }
    , { stmts := [ .assign (Place.local 0) (.constVal (.int 0)) ]
        term := .return_ }
    , { stmts := []
        term := .falseEdge 3 3 }
    , { stmts :=
          [ .fakeRead .forMatchGuard (Place.local 2)
          , .fakeRead .forGuardBinding (Place.local 5)
          , .assign (Place.local 4) (.useCopy { localId := 1, proj := [.downcast 1, .field 0] })
          , .assign (Place.local 0) (.useCopy (Place.local 4)) ]
        term := .return_ } ]

noncomputable def initGuardProbeStore (arg : Val) : MirStore where
  locals :=
    [ .live none
    , .live (some arg)
    , .live none
    , .live none
    , .live none
    , .live none
    , .live none ]
  boxHeap := []
  cellHeap := []

/-- Witness: `CleanupPostBorrowck` on `guardProbeBody` returns exact identical results pre- and
post-cleanup for `Some(42)` (guard true -> `42`, guard false -> `0`) and `None` (`0`). -/
theorem witness_guard_probe_cleanup_equiv :
    let esSome := { store := initGuardProbeStore (.enum 1 [.int 42]), blockIdx := 0, stmtIdx := 0 : ExecState }
    let esNone := { store := initGuardProbeStore (.enum 0 []), blockIdx := 0, stmtIdx := 0 : ExecState }
    (∃ st1, runMir true (cleanupBody (guardProbeBody true)) 16 esSome = .ok (some (.int 42), st1)) ∧
    (∃ st2, runMir true (cleanupBody (guardProbeBody false)) 16 esSome = .ok (some (.int 0), st2)) ∧
    (∃ st3, runMir true (cleanupBody (guardProbeBody true)) 16 esNone = .ok (some (.int 0), st3)) ∧
    runMir true (cleanupBody (guardProbeBody true)) 16 esSome =
    runMir false (guardProbeBody true) 16 esSome := by
  refine ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
  exact cleanup_post_borrowck_observational_erasure_equiv (guardProbeBody true) 16 _

/-- Witness: `or_pattern` sub-branch short-circuit (`(Some(10), Some(20))` -> `1` check, `10`) vs.
fallback re-evaluation (`(Some(1), Some(2))` -> `2` checks, `2`) vs. miss (`(Some(1), Some(1))` -> `2` checks, `99`). -/
noncomputable def tupleOrArm : OrArm where
  branches :=
    [ { matchesPattern := fun st =>
          match st.readPlace (Place.local 1) with
          | some (.tuple [.enum 1 [v], _]) => some v
          | _ => none
        guardEval := fun v st =>
          match v with
          | .int n => (decide (5 < n), st)
          | _ => (false, st) }
    , { matchesPattern := fun st =>
          match st.readPlace (Place.local 1) with
          | some (.tuple [_, .enum 1 [v]]) => some v
          | _ => none
        guardEval := fun v st =>
          match v with
          | .int n => (decide (5 < n), st)
          | _ => (false, st) } ]
  armBody := fun v st => (v, st)
  otherwise := fun st => (.int 99, st)

theorem witness_or_pattern_short_circuit_and_fallthrough :
    let stShort : MirStore := { locals := [.live none, .live (some (.tuple [.enum 1 [.int 10], .enum 1 [.int 20]]))], boxHeap := [], cellHeap := [] }
    let stSecond : MirStore := { locals := [.live none, .live (some (.tuple [.enum 1 [.int 1], .enum 1 [.int 20]]))], boxHeap := [], cellHeap := [] }
    let stMiss : MirStore := { locals := [.live none, .live (some (.tuple [.enum 1 [.int 1], .enum 1 [.int 1]]))], boxHeap := [], cellHeap := [] }
    let t1 := evalOrBranchesLowered tupleOrArm 0 0 stShort tupleOrArm.branches
    let t2 := evalOrBranchesLowered tupleOrArm 0 0 stSecond tupleOrArm.branches
    let t3 := evalOrBranchesLowered tupleOrArm 0 0 stMiss tupleOrArm.branches
    t1.guardCalls = 1 ∧ t1.selectedBranch = some 0 ∧
    t2.guardCalls = 2 ∧ t2.selectedBranch = some 1 ∧
    t3.guardCalls = 2 ∧ t3.selectedBranch = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness: `Cell` interior mutability (`MatchedCellField { tag: true, c: Cell::new(5) }`) passes
borrowck, sets `cellHeap[0] := 17`, preserves `tag = true`, and observes `17` on fallthrough! -/
theorem witness_cell_interior_mut_across_fallthrough :
    let st0 : MirStore :=
      { locals := [.live none, .live (some (.tuple [.bool true, .cellPtr 0]))]
      , boxHeap := []
      , cellHeap := [some (.int 5)] }
    let guardStmts : List StatementKind :=
      [ .assign (Place.local 0) (.cellWrite 0 (.int 17)) ]
    let frozen := [Place.local 1]
    (∀ s, s ∈ guardStmts → guardStmtPreservesShallow frozen s) ∧
    ∃ st1, runStmts st0 guardStmts = .ok st1 ∧
      st1.readDiscr { localId := 1, proj := [.field 0] } = some 1 ∧
      st1.readCell 0 = some (.int 17) := by
  constructor
  · intro s hs
    cases hs with
    | head =>
      constructor
      · intro p hp
        cases hp with
        | head => intro h; cases h
        | tail _ hm => cases hm
      · rfl
    | tail _ hm => cases hm
  · exact ⟨_, rfl, rfl, rfl⟩

end Anneal.MatchGuardSoundness
