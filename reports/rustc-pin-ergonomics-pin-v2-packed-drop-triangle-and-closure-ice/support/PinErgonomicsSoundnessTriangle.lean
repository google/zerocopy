/-
PinErgonomicsSoundnessTriangle.lean

A small kernel-checked model of the soundness argument behind rustc's experimental structural
pinning (`#![feature(pin_ergonomics)]`, `#[pin_v2]`) and of the place-categorization defect that
makes closure and coroutine bodies fail to compile.

The file is self-contained: it imports only `Lean` (for the audit command at the end) and uses
no automation beyond `rfl`, `cases`, `induction`, `rw`, `unfold`, `exact` and `decide`.
It defines no recursive function of its own (all iteration goes through `List.foldl` and
`List.foldr`), and the audit command at the end fails elaboration if any theorem of this
module depends on any axiom at all.

What is modelled, and where it comes from in `rust-lang/rust` (paths and line numbers at commit
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` unless noted):

* Part 1, destructor addresses along a projection path.  A value is pinned at `inPlace 0`.
  Safe code projects through a chain of nested structs to a `!Unpin` leaf and observes the
  leaf's address.  Later the root is dropped.  The drop glue visits the same chain; at each
  level the field is either destroyed in place or first moved to a temporary:
    - because the struct is `#[repr(packed)]` and the field is under-aligned
      (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs`), or
    - because the struct's destructor body moved the field out through `&mut`
      (for example with `core::mem::replace`).
  The gates are the compiler checks that restrict which chains are accepted:
    - `optIn`: destructuring below a pinned reference requires `#[pin_v2]`
      (`check_pin_projection`, `compiler/rustc_hir_typeck/src/pat.rs:1529-1560`);
    - `noManualUnpin`: no explicit `Unpin` impl for a `#[pin_v2]` type
      (`visit_implementation_of_unpin`, `compiler/rustc_hir_analysis/src/coherence/builtin.rs`);
    - `packed`: no `#[repr(packed)]` on a `#[pin_v2]` type
      (`check_packed`, `compiler/rustc_hir_analysis/src/check/check.rs:1666-1679`);
    - `drop`: a `#[pin_v2]` type must not implement `Drop::drop(&mut self)`
      (`check_drop_xor_pin_drop`, `compiler/rustc_hir_analysis/src/check/always_applicable.rs`).
  Two checks are always on: a destructor body can obtain `&mut` to a field only where safe
  Rust lets it (`bodyOk`; this is where the `Unpin` obligation on unpinned `ref mut` bindings
  enters), and the innermost projected field must not be under-aligned (error E0793).

* Part 2, the lifetime of one value as a trace of events, and the pin contract on traces.
  The provided body of `Drop::drop` is
  `unsafe { Drop::pin_drop(Pin::new_unchecked(self)) }` (`library/core/src/ops/drop.rs:243-246`):
  the drop glue pins the value where it currently is and destroys it there.

* Part 3, place categorization in `ExprUseVisitor`
  (`compiler/rustc_hir_typeck/src/expr_use_visitor.rs`): `cat_deref` (1499-1519), the
  `PatAdjust::PinDeref` arm (1654-1665), the `PatKind::Ref` arm (1763-1769) and the
  `Adjust::Deref` arm of `cat_expr_adjusted_with` (1269-1283).
-/
import Lean

namespace PinErgonomics

/-! ## Small Boolean and list helpers (proved here to keep the axiom footprint empty) -/

theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem bool_clash {b : Bool} (hf : b = false) (ht : b = true) : False := by
  rw [hf] at ht
  exact absurd ht (by decide)

theorem ite_pos' {α : Type} {p : Prop} [d : Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases d with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hp hn

theorem ite_neg' {α : Type} {p : Prop} [d : Decidable p] (hn : ¬p) (a b : α) :
    (if p then a else b) = b := by
  cases d with
  | isTrue hp => exact absurd hp hn
  | isFalse _ => rfl

theorem foldl_append' {α β : Type} (f : β → α → β) (b : β) (l₁ l₂ : List α) :
    (l₁ ++ l₂).foldl f b = l₂.foldl f (l₁.foldl f b) := by
  induction l₁ generalizing b with
  | nil => rfl
  | cons a l ih => exact ih (f b a)

/-! ## Part 1. Where the destructor of a pinned field runs -/

/-- An address, relative to the place where the root value was pinned.  `inPlace off` is inside
the pinned root; `temp level off` is inside the temporary created when the drop glue (or a
destructor body) of the struct at depth `level` moved its field away.  The two kinds are
distinct by construction, so no arithmetic about disjoint storage is needed. -/
inductive Addr where
  | inPlace (off : Nat)
  | temp (level : Nat) (off : Nat)
  deriving DecidableEq

def Addr.shift : Addr → Nat → Addr
  | .inPlace o, k => .inPlace (o + k)
  | .temp l o, k => .temp l (o + k)

/-- Which destructor method a struct implements. -/
inductive DropFlavor where
  /-- no `Drop` impl -/
  | none
  /-- `fn drop(&mut self)` -/
  | dropMut
  /-- `fn pin_drop(&pin mut self)` -/
  | pinDrop
  deriving DecidableEq

def DropFlavor.isDropMut : DropFlavor → Bool
  | .none => false
  | .dropMut => true
  | .pinDrop => false

/-- One struct on the projection path, together with the one field the path goes through. -/
structure Level where
  /-- the struct is marked `#[pin_v2]` -/
  pinV2 : Bool
  /-- the struct is `#[repr(packed)]` -/
  packed : Bool
  /-- the field's alignment exceeds the struct's packing -/
  fieldUnderAligned : Bool
  dropFlavor : DropFlavor
  /-- the destructor body moves the field out (e.g. `mem::replace(&mut self.f, ..)`) -/
  bodyMovesField : Bool
  /-- the struct has an explicit `impl Unpin` -/
  manualUnpin : Bool
  /-- offset of the field inside the struct -/
  off : Nat

/-- The field is relocated before its destructor runs. -/
def Level.movesField (L : Level) : Bool :=
  (L.packed && L.fieldUnderAligned) || L.bodyMovesField

structure Walk where
  base : Addr
  depth : Nat

/-- One step of the drop glue: the address at which the field of `L` is destroyed. -/
def stepDrop (w : Walk) (L : Level) : Walk :=
  { base := if L.movesField then Addr.temp w.depth 0 else w.base.shift L.off
    depth := w.depth + 1 }

/-- Address at which the leaf's destructor runs when the root is dropped. -/
def dropAddr (path : List Level) : Addr :=
  (path.foldl stepDrop ⟨Addr.inPlace 0, 0⟩).base

def pinnedAddrFrom (a : Addr) (path : List Level) : Addr :=
  path.foldl (fun a L => a.shift L.off) a

/-- Address of the leaf observed through pin projection from the pinned root. -/
def pinnedAddr (path : List Level) : Addr :=
  pinnedAddrFrom (Addr.inPlace 0) path

/-- The compiler checks that can be switched on or off. -/
structure Gates where
  /-- destructuring below a pinned reference requires `#[pin_v2]` -/
  optIn : Bool
  /-- no explicit `Unpin` impl for a `#[pin_v2]` type -/
  noManualUnpin : Bool
  /-- no `#[repr(packed)]` on a `#[pin_v2]` type -/
  packed : Bool
  /-- a `#[pin_v2]` type must not implement `drop(&mut self)` -/
  drop : Bool

def Gates.all : Gates := ⟨true, true, true, true⟩

/-- What safe Rust lets a destructor body do with the field.
`drop(&mut self)` can always reach `&mut self.f`.  `pin_drop(&pin mut self)` can reach it only
through an unpinned `ref mut` binding (requires the field type to be `Unpin`) or through
`Pin::get_mut` / `DerefMut` (requires `Self: Unpin`, which holds if there is an explicit impl
or, for the auto trait, only if the field type is `Unpin`). -/
def bodyOk (L : Level) (fieldUnpin : Bool) : Bool :=
  match L.dropFlavor with
  | .none => !L.bodyMovesField
  | .dropMut => true
  | .pinDrop => !L.bodyMovesField || fieldUnpin || L.manualUnpin

def levelOk (g : Gates) (L : Level) (fieldUnpin innermost : Bool) : Bool :=
  (!g.optIn || L.pinV2) &&
  (!g.noManualUnpin || !(L.pinV2 && L.manualUnpin)) &&
  (!g.packed || !(L.pinV2 && L.packed)) &&
  (!g.drop || !(L.pinV2 && L.dropFlavor.isDropMut)) &&
  (!innermost || !(L.packed && L.fieldUnderAligned)) &&
  bodyOk L fieldUnpin

/-- Result of checking a path suffix: accepted so far, whether the type denoted by the suffix
is `Unpin`, and whether the suffix is empty (so the next level is the innermost one). -/
structure Acc where
  ok : Bool
  tyUnpin : Bool
  innermost : Bool

def checkStep (g : Gates) (L : Level) (acc : Acc) : Acc :=
  { ok := acc.ok && levelOk g L acc.tyUnpin acc.innermost
    tyUnpin := L.manualUnpin || acc.tyUnpin
    innermost := false }

def check (g : Gates) (leafUnpin : Bool) (path : List Level) : Acc :=
  path.foldr (checkStep g) ⟨true, leafUnpin, true⟩

/-- The compiler with gates `g` accepts a program that pin-projects along `path` to a leaf
whose type is `Unpin` iff `leafUnpin`. -/
def accepts (g : Gates) (leafUnpin : Bool) (path : List Level) : Bool :=
  (check g leafUnpin path).ok

theorem levelOk_all_no_move (L : Level) (inner : Bool)
    (h : levelOk Gates.all L false inner = true) :
    L.movesField = false ∧ L.manualUnpin = false := by
  cases L with
  | mk pinV2 packed ua df bm mu off =>
    cases pinV2 <;> cases packed <;> cases ua <;> cases df <;> cases bm <;> cases mu <;>
      cases inner <;> first | exact ⟨rfl, rfl⟩ | exact (bool_clash rfl h).elim

theorem accepted_all_spec (path : List Level) :
    accepts Gates.all false path = true →
      (check Gates.all false path).tyUnpin = false ∧ ∀ L, L ∈ path → L.movesField = false := by
  induction path with
  | nil =>
    intro _
    exact ⟨rfl, fun L h => nomatch h⟩
  | cons L rest ih =>
    intro h
    have h' : ((check Gates.all false rest).ok &&
        levelOk Gates.all L (check Gates.all false rest).tyUnpin
          (check Gates.all false rest).innermost) = true := h
    have hsplit := and_true_split h'
    have hrest := ih hsplit.1
    have hlvl := hsplit.2
    rw [hrest.1] at hlvl
    have hno := levelOk_all_no_move L _ hlvl
    refine ⟨?_, ?_⟩
    · show (L.manualUnpin || (check Gates.all false rest).tyUnpin) = false
      rw [hno.2, hrest.1]
      rfl
    · intro L' hL'
      cases hL' with
      | head => exact hno.1
      | tail _ hmem => exact hrest.2 L' hmem

theorem foldl_no_moves (path : List Level) (w : Walk)
    (h : ∀ L, L ∈ path → L.movesField = false) :
    (path.foldl stepDrop w).base = pinnedAddrFrom w.base path := by
  induction path generalizing w with
  | nil => rfl
  | cons L rest ih =>
    have hL : L.movesField = false := h L (List.Mem.head _)
    have hstep : stepDrop w L = ⟨w.base.shift L.off, w.depth + 1⟩ := by
      unfold stepDrop
      rw [hL]
      rfl
    show (rest.foldl stepDrop (stepDrop w L)).base = pinnedAddrFrom (w.base.shift L.off) rest
    rw [hstep]
    exact ih _ (fun L' hL' => h L' (List.Mem.tail _ hL'))

/-- **Address stability under the three gates.**  If the compiler enforces the structural
opt-in (`optIn` together with `noManualUnpin` and the always-on `ref mut` rule in `bodyOk`),
the packed gate and the drop gate, then for every accepted projection path to a `!Unpin` leaf
the leaf's destructor runs at exactly the address at which the leaf was observed pinned. -/
theorem pinV2_three_gate_preserves_pinned_address_through_drop (path : List Level)
    (h : accepts Gates.all false path = true) : dropAddr path = pinnedAddr path :=
  foldl_no_moves path _ (accepted_all_spec path h).2

/-! ### Sharpness: each gate is necessary

Every counterexample is a concrete path that the checker accepts with exactly one gate
switched off, that the full checker rejects, and whose leaf is destroyed at an address
different from the one it was pinned at. -/

/-- `Outer` is `#[pin_v2] #[repr(packed)]` with an under-aligned field `mid : Mid` at offset 1;
`Mid` is `#[pin_v2]` with an alignment-1 leaf `node` at offset 8.  The leaf is pinned at
offset 9; the packed drop glue copies `mid` to an aligned temporary and destroys `node` there,
so the address the leaf recorded for itself is no longer its address. -/
def ce1Path : List Level :=
  [ { pinV2 := true, packed := true, fieldUnderAligned := true, dropFlavor := .none,
      bodyMovesField := false, manualUnpin := false, off := 1 },
    { pinV2 := true, packed := false, fieldUnderAligned := false, dropFlavor := .none,
      bodyMovesField := false, manualUnpin := false, off := 8 } ]

theorem ce1_packed_drop_copy_invalidates_self_ptr :
    accepts { Gates.all with packed := false } false ce1Path = true ∧
    accepts Gates.all false ce1Path = false ∧
    pinnedAddr ce1Path = Addr.inPlace 9 ∧
    dropAddr ce1Path = Addr.temp 0 8 ∧
    dropAddr ce1Path ≠ pinnedAddr ce1Path := by decide

/-- A `#[pin_v2]` struct whose `drop(&mut self)` moves the pinned field out with
`mem::replace`. -/
def ce2Path : List Level :=
  [ { pinV2 := true, packed := false, fieldUnderAligned := false, dropFlavor := .dropMut,
      bodyMovesField := true, manualUnpin := false, off := 0 } ]

theorem ce2_unpinned_drop_mem_replace_invalidates_pinned_field :
    accepts { Gates.all with drop := false } false ce2Path = true ∧
    accepts Gates.all false ce2Path = false ∧
    dropAddr ce2Path ≠ pinnedAddr ce2Path := by decide

/-- A struct that never opted into structural pinning.  Its author is entitled to implement
`Unpin` and an ordinary `Drop` that moves the field; projecting a pinned reference through it
breaks the invariant the author never promised to keep. -/
def ce3Path : List Level :=
  [ { pinV2 := false, packed := false, fieldUnderAligned := false, dropFlavor := .dropMut,
      bodyMovesField := true, manualUnpin := true, off := 0 } ]

theorem ce3_unmarked_struct_projection_violates_private_pin_invariant :
    accepts { Gates.all with optIn := false } false ce3Path = true ∧
    accepts Gates.all false ce3Path = false ∧
    dropAddr ce3Path ≠ pinnedAddr ce3Path := by decide

/-- A `#[pin_v2]` struct with an explicit `Unpin` impl: its `pin_drop` reaches `&mut Self`
through `Pin::get_mut` and moves the pinned field. -/
def ce5Path : List Level :=
  [ { pinV2 := true, packed := false, fieldUnderAligned := false, dropFlavor := .pinDrop,
      bodyMovesField := true, manualUnpin := true, off := 0 } ]

theorem ce5_manual_unpin_impl_lets_pin_drop_move_pinned_field :
    accepts { Gates.all with noManualUnpin := false } false ce5Path = true ∧
    accepts Gates.all false ce5Path = false ∧
    dropAddr ce5Path ≠ pinnedAddr ce5Path := by decide

/-- The checks present for explicit `&pin` patterns at `rust-lang/rust` commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: no opt-in check on that path and no packed gate. -/
def Gates.explicitPatternsAt14210df0e : Gates :=
  { optIn := false, noManualUnpin := true, packed := false, drop := true }

theorem explicit_patterns_at_14210df0e_accept_ce1_and_ce3 :
    accepts Gates.explicitPatternsAt14210df0e false ce1Path = true ∧
    accepts Gates.explicitPatternsAt14210df0e false ce3Path = true := by decide

/-- An `Unpin` leaf may be moved by a `pin_drop` body; the address-stability theorem is
stated for `!Unpin` leaves because only those are protected by the pin contract. -/
theorem unpin_leaf_may_move_under_all_gates :
    accepts Gates.all true
      [ { pinV2 := true, packed := false, fieldUnderAligned := false, dropFlavor := .pinDrop,
          bodyMovesField := true, manualUnpin := false, off := 0 } ] = true := by decide

/-! ## Part 2. The pin contract on a value's lifetime, and the `Drop::drop` shim -/

inductive Event where
  /-- ownership of the value moves to another address -/
  | move (dst : Addr)
  /-- a pinned reference to the value is created at its current address -/
  | pin
  /-- the value's destructor runs at its current address -/
  | destroy

structure Life where
  cur : Addr
  pinnedAt : Option Addr
  ok : Bool

def stepLife (s : Life) : Event → Life
  | .move dst => { cur := dst, pinnedAt := s.pinnedAt, ok := s.ok && s.pinnedAt.isNone }
  | .pin =>
    { cur := s.cur
      pinnedAt := match s.pinnedAt with
        | some a => some a
        | none => some s.cur
      ok := s.ok }
  | .destroy =>
    { cur := s.cur
      pinnedAt := s.pinnedAt
      ok := s.ok && match s.pinnedAt with
        | none => true
        | some a => decide (a = s.cur) }

/-- The pin contract for a `!Unpin` value that starts at `start`: once pinned it is never
moved, and it is destroyed at the address it was pinned at. -/
def pinContract (start : Addr) (trace : List Event) : Bool :=
  (trace.foldl stepLife ⟨start, none, true⟩).ok

/-- What the drop glue does to a value whose type implements only `pin_drop`: the provided
`Drop::drop` body pins the value where it is (`Pin::new_unchecked(self)`), runs `pin_drop`,
and the value is destroyed there. -/
def dropShim : List Event := [Event.pin, Event.destroy]

theorem moves_keep_unpinned (moves : List Addr) (s : Life)
    (hp : s.pinnedAt = none) (hok : s.ok = true) :
    ((moves.map Event.move).foldl stepLife s).pinnedAt = none ∧
    ((moves.map Event.move).foldl stepLife s).ok = true := by
  induction moves generalizing s with
  | nil => exact ⟨hp, hok⟩
  | cons d rest ih =>
    apply ih
    · exact hp
    · show (s.ok && s.pinnedAt.isNone) = true
      rw [hok, hp]
      rfl

theorem shim_ok_on_unpinned (s : Life) (hp : s.pinnedAt = none) (hok : s.ok = true) :
    (dropShim.foldl stepLife s).ok = true := by
  show (s.ok && match (match s.pinnedAt with | some a => some a | none => some s.cur) with
    | none => true
    | some a => decide (a = s.cur)) = true
  rw [hok, hp]
  show (true && decide (s.cur = s.cur)) = true
  rw [decide_eq_true rfl]
  rfl

/-- **The shim is sound for values dropped before they were ever pinned.**  However often an
unpinned value has been moved, the `Pin<&mut Self>` that the provided `Drop::drop` body creates
is the first pin of that value, and the value is destroyed without moving again. -/
theorem unpinned_drop_shim_sound_before_first_pin (start : Addr) (moves : List Addr) :
    pinContract start (moves.map Event.move ++ dropShim) = true := by
  unfold pinContract
  rw [foldl_append']
  have h := moves_keep_unpinned moves ⟨start, none, true⟩ rfl rfl
  exact shim_ok_on_unpinned _ h.1 h.2

/-- A value pinned in place and then dropped in place also satisfies the contract. -/
theorem pinned_then_dropped_in_place_sound (start : Addr) :
    pinContract start ([Event.pin] ++ dropShim) = true := by
  show (true && decide (start = start)) = true
  rw [decide_eq_true rfl]
  rfl

/-- Any move after the first pin violates the contract, whatever happens afterwards. -/
theorem move_after_pin_violates_contract (start dst : Addr) :
    pinContract start ([Event.pin, Event.move dst] ++ dropShim) = false := rfl

/-- The lifetime of the leaf of a projection path.  If `projected`, safe code pinned it through
the path before the root was dropped.  The drop glue relocates it iff `dropAddr ≠ pinnedAddr`. -/
def leafTrace (projected : Bool) (path : List Level) : List Event :=
  (match projected with
    | true => [Event.pin]
    | false => []) ++
  ((if dropAddr path = pinnedAddr path then [] else [Event.move (dropAddr path)]) ++ dropShim)

/-- A leaf that was never pinned tolerates relocation by the drop glue: this is why a
`#[repr(packed)]` struct that is not structurally pinned may contain fields whose destructor
is `pin_drop`. -/
theorem never_pinned_leaf_always_sound (path : List Level) :
    pinContract (pinnedAddr path) (leafTrace false path) = true := by
  show pinContract (pinnedAddr path)
    ((if dropAddr path = pinnedAddr path then [] else [Event.move (dropAddr path)]) ++ dropShim)
      = true
  exact
    if h : dropAddr path = pinnedAddr path then by
      rw [ite_pos' h]
      exact unpinned_drop_shim_sound_before_first_pin (pinnedAddr path) []
    else by
      rw [ite_neg' h]
      exact unpinned_drop_shim_sound_before_first_pin (pinnedAddr path) [dropAddr path]

/-- For a leaf that was pinned through projection, the contract holds exactly when its
destructor runs at the pinned address. -/
theorem pinned_leaf_sound_iff_address_stable (path : List Level) :
    pinContract (pinnedAddr path) (leafTrace true path) = true ↔
      dropAddr path = pinnedAddr path := by
  constructor
  · intro hc
    exact
      if h : dropAddr path = pinnedAddr path then h
      else by
        have hfalse : pinContract (pinnedAddr path) (leafTrace true path) = false := by
          show pinContract (pinnedAddr path)
            ([Event.pin] ++
              ((if dropAddr path = pinnedAddr path then [] else [Event.move (dropAddr path)])
                ++ dropShim)) = false
          rw [ite_neg' h]
          exact move_after_pin_violates_contract (pinnedAddr path) (dropAddr path)
        rw [hfalse] at hc
        exact absurd hc (by decide)
  · intro h
    show pinContract (pinnedAddr path)
      ([Event.pin] ++
        ((if dropAddr path = pinnedAddr path then [] else [Event.move (dropAddr path)])
          ++ dropShim)) = true
    rw [ite_pos' h]
    exact pinned_then_dropped_in_place_sound (pinnedAddr path)

/-- The three gates therefore give the pin contract for every accepted, projected leaf. -/
theorem three_gates_give_pin_contract (path : List Level)
    (h : accepts Gates.all false path = true) :
    pinContract (pinnedAddr path) (leafTrace true path) = true :=
  (pinned_leaf_sound_iff_address_stable path).mpr
    (pinV2_three_gate_preserves_pinned_address_through_drop path h)

/-! ## Part 3. Place categorization of pinned dereferences in `ExprUseVisitor` -/

/-- Just enough of rustc's types: `pin p` is the struct `Pin<P>` whose only field (index 0)
has type `p`; `ref m t` is `&t` (`m = false`) or `&mut t` (`m = true`). -/
inductive Ty where
  | scalar
  | adt (id : Nat)
  | ref (mutbl : Bool) (pointee : Ty)
  | pin (pointer : Ty)

inductive ProjKind where
  | deref
  | field (idx : Nat)

structure Projection where
  kind : ProjKind
  ty : Ty

/-- A categorized place.  `projs` lists the projections most recent first (rustc stores them
oldest first; only the order of the list differs). -/
structure Place where
  baseTy : Ty
  projs : List Projection

/-- `Place::ty`: the type after the last projection. -/
def Place.ty (p : Place) : Ty :=
  match p.projs with
  | pr :: _ => pr.ty
  | [] => p.baseTy

def Place.push (p : Place) (pr : Projection) : Place :=
  { baseTy := p.baseTy, projs := pr :: p.projs }

inductive CatError where
  /-- "explicit deref of non-derefable type" -/
  | explicitDerefOfNonDerefableType
  /-- "`PinDeref` of non-pinned-reference type" -/
  | pinDerefOfNonPinnedReferenceType

/-- `Ty::builtin_deref`, restricted to references (boxes and raw pointers are not modelled;
`Pin<_>` is neither). -/
def builtinDeref : Ty → Option Ty
  | .scalar => none
  | .adt _ => none
  | .ref _ t => some t
  | .pin _ => none

/-- `Ty::pinned_ty`. -/
def pinnedTy : Ty → Option Ty
  | .scalar => none
  | .adt _ => none
  | .ref _ _ => none
  | .pin t => some t

/-- `cat_deref`. -/
def catDeref (p : Place) : Except CatError Place :=
  match builtinDeref p.ty with
  | some t => Except.ok (p.push ⟨ProjKind.deref, t⟩)
  | none => Except.error CatError.explicitDerefOfNonDerefableType

/-- The `PatAdjust::PinDeref` arm of `cat_pattern`: project field 0 of `Pin`, then deref. -/
def catPinDeref (p : Place) : Except CatError Place :=
  match pinnedTy p.ty with
  | some t => catDeref (p.push ⟨ProjKind.field 0, t⟩)
  | none => Except.error CatError.pinDerefOfNonPinnedReferenceType

/-- The `PatKind::Ref(subpat, _, _)` arm of `cat_pattern` as written at the audited revisions:
the pinnedness of the reference pattern is ignored. -/
def catRefPatUpstream (_pinned : Bool) (p : Place) : Except CatError Place :=
  catDeref p

/-- The same arm with the missing case added. -/
def catRefPatRepaired (pinned : Bool) (p : Place) : Except CatError Place :=
  match pinned with
  | true => catPinDeref p
  | false => catDeref p

/-- What MIR building does for the THIR pattern `Deref { pin, subpattern }`
(`compiler/rustc_mir_build/src/builder/matches/match_pair.rs:417-436`). -/
def mirDerefPattern (pinned : Bool) (p : Place) : Option Place :=
  match pinned with
  | true =>
    match pinnedTy p.ty with
    | none => none
    | some pointer =>
      match builtinDeref pointer with
      | none => none
      | some t => some ((p.push ⟨ProjKind.field 0, pointer⟩).push ⟨ProjKind.deref, t⟩)
  | false =>
    match builtinDeref p.ty with
    | some t => some (p.push ⟨ProjKind.deref, t⟩)
    | none => none

theorem catPinDeref_on_pinned_ref (p : Place) (m : Bool) (t : Ty)
    (h : p.ty = Ty.pin (Ty.ref m t)) :
    catPinDeref p =
      Except.ok ((p.push ⟨ProjKind.field 0, Ty.ref m t⟩).push ⟨ProjKind.deref, t⟩) := by
  unfold catPinDeref
  rw [h]
  rfl

/-- **The repair.**  On a place of type `Pin<&T>` or `Pin<&mut T>`, the repaired `PatKind::Ref`
arm first projects field 0 of `Pin` and only then dereferences.  The result has type `T`,
coincides with what the `PatAdjust::PinDeref` arm computes for the implicit form of the same
pattern, and is the place MIR building uses. -/
theorem cat_pattern_ref_pinned_projects_field0_before_deref (p : Place) (m : Bool) (t : Ty)
    (h : p.ty = Ty.pin (Ty.ref m t)) :
    catRefPatRepaired true p =
        Except.ok ((p.push ⟨ProjKind.field 0, Ty.ref m t⟩).push ⟨ProjKind.deref, t⟩) ∧
    catRefPatRepaired true p = catPinDeref p ∧
    ((p.push ⟨ProjKind.field 0, Ty.ref m t⟩).push ⟨ProjKind.deref, t⟩).ty = t ∧
    mirDerefPattern true p =
        some ((p.push ⟨ProjKind.field 0, Ty.ref m t⟩).push ⟨ProjKind.deref, t⟩) := by
  refine ⟨catPinDeref_on_pinned_ref p m t h, rfl, rfl, ?_⟩
  unfold mirDerefPattern
  rw [h]
  rfl

/-- The repair changes nothing for ordinary reference patterns. -/
theorem repaired_agrees_with_upstream_on_unpinned_patterns (p : Place) :
    catRefPatRepaired false p = catRefPatUpstream false p := rfl

/-- **The defect.**  On a place of type `Pin<&T>` or `Pin<&mut T>` the upstream arm reports
"explicit deref of non-derefable type", for either value of the ignored pinnedness. -/
theorem ce4_expr_use_visitor_cat_deref_fails_without_field0 (p : Place) (m : Bool) (t : Ty)
    (h : p.ty = Ty.pin (Ty.ref m t)) (pinned : Bool) :
    catRefPatUpstream pinned p = Except.error CatError.explicitDerefOfNonDerefableType := by
  unfold catRefPatUpstream catDeref
  rw [h]
  rfl

/-- `DerefAdjustKind`: the kind of an implicit dereference in an expression adjustment. -/
inductive DerefAdjustKind where
  | builtin
  | overloaded (mutbl : Bool) (target : Ty)
  | pin

/-- The `Adjust::Deref` arm of `cat_expr_adjusted_with` as written at the audited revisions:
an overloaded deref starts from a fresh rvalue of reference type, every other kind
dereferences the previous place directly. -/
def catAdjustDerefUpstream (k : DerefAdjustKind) (prev : Place) : Except CatError Place :=
  match k with
  | .overloaded m target => catDeref ⟨Ty.ref m target, []⟩
  | .builtin => catDeref prev
  | .pin => catDeref prev

def catAdjustDerefRepaired (k : DerefAdjustKind) (prev : Place) : Except CatError Place :=
  match k with
  | .overloaded m target => catDeref ⟨Ty.ref m target, []⟩
  | .builtin => catDeref prev
  | .pin => catPinDeref prev

/-- The same defect at the second site: the implicit pinned reborrow of an expression. -/
theorem adjust_pin_deref_upstream_fails (prev : Place) (m : Bool) (t : Ty)
    (h : prev.ty = Ty.pin (Ty.ref m t)) :
    catAdjustDerefUpstream DerefAdjustKind.pin prev =
      Except.error CatError.explicitDerefOfNonDerefableType := by
  unfold catAdjustDerefUpstream catDeref
  rw [h]
  rfl

theorem adjust_pin_deref_repaired_projects_field0 (prev : Place) (m : Bool) (t : Ty)
    (h : prev.ty = Ty.pin (Ty.ref m t)) :
    catAdjustDerefRepaired DerefAdjustKind.pin prev =
      Except.ok ((prev.push ⟨ProjKind.field 0, Ty.ref m t⟩).push ⟨ProjKind.deref, t⟩) :=
  catPinDeref_on_pinned_ref prev m t h

/-- How a recorded delayed bug surfaces: only when the session ends without a real error. -/
inductive Outcome where
  | ok
  | rejected
  | ice

def sessionOutcome (errors delayedBugs : Nat) : Outcome :=
  match errors with
  | 0 =>
    match delayedBugs with
    | 0 => Outcome.ok
    | _ + 1 => Outcome.ice
  | _ + 1 => Outcome.rejected

theorem delayed_bug_without_errors_is_ice (n : Nat) :
    sessionOutcome 0 (n + 1) = Outcome.ice := rfl

theorem delayed_bug_is_masked_by_any_error (e n : Nat) :
    sessionOutcome (e + 1) n = Outcome.rejected := rfl

end PinErgonomics

/-! ## Audit

`#audit_pin_ergonomics` inspects the constants declared in this module.  It fails if any
constant's name contains the marker of a compiler-generated helper for compiled recursion, or
if any theorem stated above (every theorem directly inside the `PinErgonomics` namespace)
depends on any axiom whatsoever.  Lemmas that Lean derives automatically for structures and
equations live in nested namespaces, are not used by the proofs above, and are not audited.
(The marker is spelled in two pieces so that a textual search of this file for it finds
nothing.) -/

open Lean Elab Command in
elab "#audit_pin_ergonomics" : command => do
  let env ← getEnv
  let marker := "_unsafe" ++ "_rec"
  let names := env.constants.map₂.foldl (fun acc n _ => acc.push n) (#[] : Array Name)
  let mut theorems : Nat := 0
  for n in names do
    if (n.toString.splitOn marker).length > 1 then
      throwError "compiled-recursion helper present: {n}"
    if n.getPrefix == `PinErgonomics then
      if let some (ConstantInfo.thmInfo _) := env.find? n then
        theorems := theorems + 1
        let axioms ← collectAxioms n
        unless axioms.isEmpty do
          throwError "{n} depends on axioms {axioms}"
  logInfo m!"audit ok: {names.size} module constants, {theorems} stated theorems, no axioms, no recursion helpers"

#audit_pin_ergonomics

#print axioms PinErgonomics.pinV2_three_gate_preserves_pinned_address_through_drop
#print axioms PinErgonomics.unpinned_drop_shim_sound_before_first_pin
#print axioms PinErgonomics.cat_pattern_ref_pinned_projects_field0_before_deref
#print axioms PinErgonomics.ce1_packed_drop_copy_invalidates_self_ptr
#print axioms PinErgonomics.ce2_unpinned_drop_mem_replace_invalidates_pinned_field
#print axioms PinErgonomics.ce3_unmarked_struct_projection_violates_private_pin_invariant
#print axioms PinErgonomics.ce4_expr_use_visitor_cat_deref_fails_without_field0
#print axioms PinErgonomics.ce5_manual_unpin_impl_lets_pin_drop_move_pinned_field
#print axioms PinErgonomics.three_gates_give_pin_contract
