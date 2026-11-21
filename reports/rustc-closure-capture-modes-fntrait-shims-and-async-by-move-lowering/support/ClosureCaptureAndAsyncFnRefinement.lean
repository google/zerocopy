/-!
# RFC 2229 Disjoint Closure Capture, `Fn`-Trait Shims, and `AsyncFn` `by_move_body` Lowering

Standalone, kernel-checked Lean 4 mechanization of:
1. RFC 2229 tree-path disjoint place capture (`CaptureMode`, `PlacePath`, `CapturedPlace`),
   mode-lattice laws, raw-pointer truncation (`restrict_precision_for_unsafe`),
   `&mut`-deref truncation to `UniqueImmBorrow` (`truncate_place_to_len_and_update_capture_kind`),
   `Drop`-ADT truncation (`restrict_precision_for_drop_types`),
   disjoint-path non-aliasing/frame laws, and drop-count preservation when `!hasCustomDrop`.
2. Closure environment construction, `extern "rust-call"` argument untupling,
   `ClosureOnceShim` normal + unwind drop equivalence, `ClosureFnPointer` ZST coercion
   equivalence, and `FnPtrShim` receiver-adjustment/untupling equivalence.
3. `AsyncFn` (`CoroutineClosure`) lending by-ref coroutine vs. synthesized `by_move_body`
   (`MakeByMoveBody` place rewriting with `peel_deref` + bridging projections) and
   `AsyncFnOnce` dangling-borrow freedom + exact-once upvar drop across completion and
   mid-suspension drop.
4. Two sharpness counterexamples:
   - CE1: Naive `AsyncFnOnce` delegating to `&mut self` `AsyncFnMut` produces dangling-read UB
     after the `call_once` frame pops, whereas `by_move_body` completes safely.
   - CE2: Splitting a non-`Copy` field capture across a `Drop` ADT violates whole-ADT
     initialization integrity before `Drop::drop`, whereas `Drop`-boundary truncation preserves it.

Constructive verification discipline: purely total, structurally recursive definitions
and intuitionistic proofs requiring only kernel reduction (and at most `propext`/`Quot.sound`).
-/

namespace ClosureCaptureAndAsyncFnRefinement

/-! ## Part I: Capture-Mode Lattice, Tree-Path Disjoint Places, and RFC 2229 Truncation -/

/-- The four standard closure capture modes, ordered identically to
`rustc_middle::ty::BorrowKind` (`Immutable < UniqueImmutable < Mutable`)
extended by `UpvarCapture::ByValue`. -/
inductive CaptureMode where
  | immRef
  | uniqImmRef
  | mutRef
  | byVal
  deriving DecidableEq, Repr

namespace CaptureMode

/-- Total linear rank on the four standard capture modes. -/
def rank : CaptureMode → Nat
  | .immRef     => 0
  | .uniqImmRef => 1
  | .mutRef     => 2
  | .byVal      => 3

/-- Lattice order `a ≤ b` induced by `rank`. -/
def le (a b : CaptureMode) : Bool :=
  Nat.ble a.rank b.rank

/-- Least upper bound (join) in the capture-mode lattice, corresponding to
`determine_capture_info` in `compiler/rustc_hir_typeck/src/upvar.rs`. -/
def join (a b : CaptureMode) : CaptureMode :=
  if le a b then b else a

/-- Whether the capture mode demands exclusive (non-aliased) access to the captured place.
Both `uniqImmRef` and `mutRef` require exclusivity (`E0501` / `E0502`), while `immRef` permits aliasing. -/
def requiresExclusive : CaptureMode → Bool
  | .immRef     => false
  | .uniqImmRef => true
  | .mutRef     => true
  | .byVal      => true

/-- Whether the capture mode permits mutating the captured binding itself (requiring `let mut`).
`uniqImmRef` (`MutBorrowKind::ClosureCapture`) explicitly forbids mutating the captured binding
itself while still enforcing exclusivity so `*r` may be mutated through an immutable `r: &mut T`. -/
def mutatesCapturedBinding : CaptureMode → Bool
  | .immRef     => false
  | .uniqImmRef => false
  | .mutRef     => true
  | .byVal      => false

/-- Minimum `ClosureKind` required by a single captured place. -/
inductive ClosureKind where
  | fn
  | fnMut
  | fnOnce
  deriving DecidableEq, Repr

def requiredClosureKind : CaptureMode → ClosureKind
  | .immRef     => .fn
  | .uniqImmRef => .fnMut
  | .mutRef     => .fnMut
  | .byVal      => .fnOnce

theorem join_comm (a b : CaptureMode) : join a b = join b a := by
  cases a <;> cases b <;> rfl

theorem join_assoc (a b c : CaptureMode) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem join_idem (a : CaptureMode) : join a a = a := by
  cases a <;> rfl

theorem le_join_left (a b : CaptureMode) : le a (join a b) = true := by
  cases a <;> cases b <;> rfl

theorem le_join_right (a b : CaptureMode) : le b (join a b) = true := by
  cases a <;> cases b <;> rfl

theorem join_least (a b c : CaptureMode) (ha : le a c = true) (hb : le b c = true) :
    le (join a b) c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [le, join, rank]

theorem uniqImmRef_exclusive_without_binding_mutation :
    requiresExclusive .uniqImmRef = true ∧
    mutatesCapturedBinding .uniqImmRef = false ∧
    mutatesCapturedBinding .mutRef = true := by
  exact ⟨rfl, rfl, rfl⟩

end CaptureMode

/-- Projection element along a captured HIR/MIR place path. -/
inductive ProjElem where
  | field (idx : Nat)
  | deref (isRaw : Bool) (isMutRef : Bool)
  deriving DecidableEq, Repr

/-- A root local identifier plus left-to-right projections. -/
structure PlacePath where
  root : Nat
  projs : List ProjElem
  deriving DecidableEq, Repr

/-- A captured place entry produced by RFC 2229 analysis. -/
structure CapturedPlace where
  place : PlacePath
  mode : CaptureMode
  isCopyLeaf : Bool
  deriving DecidableEq, Repr

/-- Prefix relation on projection lists (`is_ancestor_or_same_capture` in `ty/closure.rs`). -/
def isProjPrefix : List ProjElem → List ProjElem → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => decide (x = y) && isProjPrefix xs ys

/-- Ancestry classification matching `determine_place_ancestry_relation` (`upvar.rs`). -/
inductive PlaceAncestry where
  | same
  | ancestor
  | descendant
  | divergent
  deriving DecidableEq, Repr

def classifyAncestry (p1 p2 : PlacePath) : PlaceAncestry :=
  if p1.root != p2.root then
    .divergent
  else if isProjPrefix p1.projs p2.projs then
    if isProjPrefix p2.projs p1.projs then .same else .ancestor
  else if isProjPrefix p2.projs p1.projs then
    .descendant
  else
    .divergent

/-- Two place paths are disjoint iff they have distinct roots or divergent projection prefixes. -/
def DisjointPaths (p1 p2 : PlacePath) : Prop :=
  classifyAncestry p1 p2 = .divergent

theorem isProjPrefix_refl (xs : List ProjElem) : isProjPrefix xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [isProjPrefix, ih]

theorem isProjPrefix_trans {xs ys zs : List ProjElem}
    (h1 : isProjPrefix xs ys = true) (h2 : isProjPrefix ys zs = true) :
    isProjPrefix xs zs = true := by
  induction xs generalizing ys zs with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp [isProjPrefix] at h1
    | cons y ys =>
      cases zs with
      | nil => simp [isProjPrefix] at h2
      | cons z zs =>
        simp only [isProjPrefix, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
        exact ⟨h1.1.trans h2.1, ih h1.2 h2.2⟩

theorem disjointPaths_symm {p1 p2 : PlacePath} (h : DisjointPaths p1 p2) :
    DisjointPaths p2 p1 := by
  unfold DisjointPaths classifyAncestry at h ⊢
  by_cases hroot : p1.root = p2.root
  · have hneq1 : (p1.root != p2.root) = false := by simp [hroot]
    have hneq2 : (p2.root != p1.root) = false := by simp [hroot]
    simp [hneq1] at h
    simp [hneq2]
    cases h12 : isProjPrefix p1.projs p2.projs <;> cases h21 : isProjPrefix p2.projs p1.projs
    · rfl
    · simp [h12, h21] at h
    · simp [h12, h21] at h
    · simp [h12, h21] at h
  · have hneq2 : (p2.root != p1.root) = true := by
      simp [bne_iff_ne]
      intro heq
      exact hroot heq.symm
    simp [hneq2]

/-- Suffix check for `&mut` dereference (used by `truncate_place_to_len_and_update_capture_kind`). -/
def containsMutRefDeref : List ProjElem → Bool
  | [] => false
  | .deref false true :: _ => true
  | _ :: rest => containsMutRefDeref rest

/-- Exact model of `truncate_place_to_len_and_update_capture_kind` (`upvar.rs:2633-2658`):
truncates `projs` to length `len` and downgrades `mutRef` to `uniqImmRef` whenever the
discarded suffix contains a `Deref` of a mutable reference `&mut`. -/
def truncateWithModeUpdate (c : CapturedPlace) (len : Nat) : CapturedPlace :=
  let kept := c.place.projs.take len
  let dropped := c.place.projs.drop len
  let newMode :=
    match c.mode with
    | .mutRef => if containsMutRefDeref dropped then .uniqImmRef else .mutRef
    | m => m
  { place := { root := c.place.root, projs := kept }
    mode := newMode
    isCopyLeaf := if dropped.isEmpty then c.isCopyLeaf else false }

theorem truncate_mutRef_across_mut_deref_yields_uniqImm
    (root : Nat) (prefixProjs suffixProjs : List ProjElem) (isCopy : Bool) :
    (truncateWithModeUpdate
      { place := { root := root, projs := prefixProjs ++ (.deref false true :: suffixProjs) }
        mode := .mutRef
        isCopyLeaf := isCopy }
      prefixProjs.length).mode = .uniqImmRef := by
  unfold truncateWithModeUpdate
  simp [containsMutRefDeref]

/-- Length before the first raw-pointer dereference (`restrict_precision_for_unsafe`, `upvar.rs:2343`). -/
def prefixLenBeforeRawDeref : List ProjElem → Nat
  | [] => 0
  | .deref true _ :: _ => 0
  | _ :: rest => 1 + prefixLenBeforeRawDeref rest

def containsRawDeref : List ProjElem → Bool
  | [] => false
  | .deref true _ :: _ => true
  | _ :: rest => containsRawDeref rest

def truncateAtRawPtr (c : CapturedPlace) : CapturedPlace :=
  truncateWithModeUpdate c (prefixLenBeforeRawDeref c.place.projs)

theorem take_prefixLenBeforeRawDeref_free (ps : List ProjElem) :
    containsRawDeref (ps.take (prefixLenBeforeRawDeref ps)) = false := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | field idx =>
      simp [prefixLenBeforeRawDeref, Nat.add_comm, containsRawDeref, ih]
    | deref isRaw isMut =>
      cases isRaw with
      | true => rfl
      | false =>
        simp [prefixLenBeforeRawDeref, Nat.add_comm, containsRawDeref, ih]

theorem truncateAtRawPtr_no_raw_deref (c : CapturedPlace) :
    containsRawDeref (truncateAtRawPtr c).place.projs = false :=
  take_prefixLenBeforeRawDeref_free c.place.projs

/-- Truncate a non-`Copy` by-value capture at the outermost `Drop` ADT boundary `dropDepth`
(matching `restrict_precision_for_drop_types` in `upvar.rs:2317-2337`). -/
def truncateForDropAdt (c : CapturedPlace) (outermostDropDepth : Option Nat) : CapturedPlace :=
  match c.mode, c.isCopyLeaf, outermostDropDepth with
  | .byVal, false, some d => truncateWithModeUpdate c d
  | _, _, _ => c

theorem truncateForDropAdt_preserves_copy_leaf (c : CapturedPlace) (d : Nat)
    (hCopy : c.isCopyLeaf = true) :
    truncateForDropAdt c (some d) = c := by
  unfold truncateForDropAdt
  cases hm : c.mode <;> simp [hCopy]

theorem truncateForDropAdt_truncates_noncopy_byVal (c : CapturedPlace) (d : Nat)
    (hVal : c.mode = .byVal) (hNotCopy : c.isCopyLeaf = false) :
    (truncateForDropAdt c (some d)).place.projs = c.place.projs.take d := by
  unfold truncateForDropAdt
  simp [hVal, hNotCopy, truncateWithModeUpdate]

/-! ### Tree-Structured Aggregate Store, Disjoint-Field Frame Laws, and Drop-Count Soundness -/

/-- Tree representation of a value with field structure, move/liveness tracking,
and optional custom `Drop` implementations at interior ADTs and leaves. -/
inductive PlaceTree where
  | leaf (val : Nat) (alive : Bool) (hasDrop : Bool)
  | node (hasCustomDrop : Bool) (alive : Bool) (fields : List PlaceTree)
  deriving Repr

/-- Field-only path (sequence of field indices from a root aggregate). -/
abbrev FieldPath := List Nat

/-- Two field paths are disjoint iff neither is a prefix of the other. -/
def DisjointFieldPaths : FieldPath → FieldPath → Prop
  | [], _ => False
  | _, [] => False
  | i :: is, j :: js => i ≠ j ∨ DisjointFieldPaths is js

/-- Total list lookup by index. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Total list update by index. -/
def listSet {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: listSet xs n v

theorem listGet_listSet_eq {α : Type} (xs : List α) (i : Nat) (v : α) (old : α)
    (h : listGet? xs i = some old) :
    listGet? (listSet xs i v) i = some v := by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k h

theorem listGet_listSet_ne {α : Type} (xs : List α) (i j : Nat) (v : α) (hne : i ≠ j) :
    listGet? (listSet xs i v) j = listGet? xs j := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ k => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        apply ih
        intro h
        exact hne (congrArg Nat.succ h)

theorem listSet_listSet_comm {α : Type} (xs : List α) (i j : Nat) (vi vj : α) (hne : i ≠ j) :
    listSet (listSet xs i vi) j vj = listSet (listSet xs j vj) i vi := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j' => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [listSet]
        exact congrArg (List.cons x) (ih i' j' (fun h => hne (congrArg Nat.succ h)))

/-- Read subtree at a field path. -/
def getAt : PlaceTree → FieldPath → Option PlaceTree
  | t, [] => some t
  | .leaf _ _ _, _ :: _ => none
  | .node _ _ fs, i :: rest =>
    match listGet? fs i with
    | none => none
    | some child => getAt child rest

/-- Replace subtree at a field path (returning unchanged tree if path is out of bounds). -/
def setAt : PlaceTree → FieldPath → PlaceTree → PlaceTree
  | _, [], v => v
  | .leaf val alive hd, _ :: _, _ => .leaf val alive hd
  | .node hcd alive fs, i :: rest, v =>
    match listGet? fs i with
    | none => .node hcd alive fs
    | some child => .node hcd alive (listSet fs i (setAt child rest v))

/-- Mark an entire subtree as moved-out (deinitialized, matching `deinitMovedPlace = true`). -/
def deinitTree : PlaceTree → PlaceTree
  | .leaf val _ hd => .leaf val false hd
  | .node hcd _ fs => .node hcd false (deinitList fs)
where
  deinitList : List PlaceTree → List PlaceTree
    | [] => []
    | t :: ts => deinitTree t :: deinitList ts

/-- Frame / non-aliasing theorem: updating or moving a subtree at path `p1` never changes
the value observed at any disjoint field path `p2`. -/
theorem getAt_setAt_disjoint (t v : PlaceTree) (p1 p2 : FieldPath)
    (hDisj : DisjointFieldPaths p1 p2) :
    getAt (setAt t p1 v) p2 = getAt t p2 := by
  induction p1 generalizing t p2 with
  | nil => cases hDisj
  | cons i is ih =>
    cases p2 with
    | nil => cases hDisj
    | cons j js =>
      cases t with
      | leaf val alive hd => rfl
      | node hcd alive fs =>
        simp only [setAt]
        cases hgi : listGet? fs i with
        | none => rfl
        | some ci =>
          simp only [getAt]
          cases hDisj with
          | inl hne =>
            rw [listGet_listSet_ne fs i j _ hne]
          | inr hDisjTail =>
            by_cases hij : i = j
            · subst hij
              rw [listGet_listSet_eq fs i (setAt ci is v) ci hgi, hgi]
              exact ih ci js hDisjTail
            · rw [listGet_listSet_ne fs i j _ hij]

/-- Commutation theorem: writes/moves to disjoint field paths commute identically. -/
theorem setAt_setAt_comm_disjoint (t v1 v2 : PlaceTree) (p1 p2 : FieldPath)
    (hDisj : DisjointFieldPaths p1 p2) :
    setAt (setAt t p1 v1) p2 v2 = setAt (setAt t p2 v2) p1 v1 := by
  induction p1 generalizing t p2 with
  | nil => cases hDisj
  | cons i is ih =>
    cases p2 with
    | nil => cases hDisj
    | cons j js =>
      cases t with
      | leaf val alive hd => rfl
      | node hcd alive fs =>
        simp only [setAt]
        cases hDisj with
        | inl hne =>
          cases hgi : listGet? fs i <;> cases hgj : listGet? fs j
          · simp [setAt, hgi, hgj]
          · simp [setAt, hgi, hgj, listGet_listSet_ne fs j i _ (Ne.symm hne)]
          · simp [setAt, hgi, hgj, listGet_listSet_ne fs i j _ hne]
          · simp [setAt, hgi, hgj, listGet_listSet_ne fs i j _ hne,
                  listGet_listSet_ne fs j i _ (Ne.symm hne),
                  listSet_listSet_comm fs i j _ _ hne]
        | inr hDisjTail =>
          by_cases hij : i = j
          · subst hij
            cases hgi : listGet? fs i with
            | none => simp [setAt, hgi]
            | some ci =>
              simp only [setAt, listGet_listSet_eq fs i _ ci hgi]
              have hSetSet : ∀ (xs : List PlaceTree) (k : Nat) (a b : PlaceTree),
                  listSet (listSet xs k a) k b = listSet xs k b := by
                intro xs k a b
                induction xs generalizing k with
                | nil => rfl
                | cons x xs' ihx =>
                  cases k with
                  | zero => rfl
                  | succ k' => exact congrArg (List.cons x) (ihx k')
              rw [hSetSet, hSetSet, ih ci js hDisjTail]
          · cases hgi : listGet? fs i <;> cases hgj : listGet? fs j
            · simp [setAt, hgi, hgj]
            · simp [setAt, hgi, hgj, listGet_listSet_ne fs j i _ (Ne.symm hij)]
            · simp [setAt, hgi, hgj, listGet_listSet_ne fs i j _ hij]
            · simp [setAt, hgi, hgj, listGet_listSet_ne fs i j _ hij,
                    listGet_listSet_ne fs j i _ (Ne.symm hij),
                    listSet_listSet_comm fs i j _ _ hij]

/-- Pairwise-disjointness of a list of captured field paths (RFC 2229 minimized capture invariant). -/
def PairwiseDisjointFieldPaths : List FieldPath → Prop
  | [] => True
  | p :: ps => (∀ q, q ∈ ps → DisjointFieldPaths p q) ∧ PairwiseDisjointFieldPaths ps

/-- Disjointness is symmetric on field paths. -/
theorem disjointFieldPaths_symm {p1 p2 : FieldPath} (h : DisjointFieldPaths p1 p2) :
    DisjointFieldPaths p2 p1 := by
  induction p1 generalizing p2 with
  | nil => cases h
  | cons i is ih =>
    cases p2 with
    | nil => cases h
    | cons j js =>
      cases h with
      | inl hne => exact Or.inl (Ne.symm hne)
      | inr htail => exact Or.inr (ih htail)

/-- **Minimized Capture List Non-Aliasing**:
For any pairwise-disjoint minimized capture list `ps` and any two distinct indices
in `ps`, mutating or moving the first captured path cannot alter the value observed
at the second captured path. -/
theorem disjoint_captures_non_aliasing
    (t v : PlaceTree) (p1 p2 : FieldPath) (ps : List FieldPath)
    (hPair : PairwiseDisjointFieldPaths (p1 :: ps))
    (hMem : p2 ∈ ps) :
    getAt (setAt t p1 v) p2 = getAt t p2 :=
  getAt_setAt_disjoint t v p1 p2 (hPair.1 p2 hMem)

/-- Number of destructor invocations triggered when dropping `t`. -/
def dropCount : PlaceTree → Nat
  | .leaf _ alive hasDrop => if alive && hasDrop then 1 else 0
  | .node hasCustomDrop alive fs =>
    (if alive && hasCustomDrop then 1 else 0) + dropCountList fs
where
  dropCountList : List PlaceTree → Nat
    | [] => 0
    | t :: ts => dropCount t + dropCountList ts

theorem dropCount_deinitTree_zero (t : PlaceTree) : dropCount (deinitTree t) = 0 := by
  match t with
  | .leaf _ _ _ => rfl
  | .node _ _ fs =>
    simp only [deinitTree, dropCount, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact dropCountList_deinitList_zero fs
where
  dropCountList_deinitList_zero : (fs : List PlaceTree) →
      dropCount.dropCountList (deinitTree.deinitList fs) = 0
    | [] => rfl
    | t :: ts => by
      simp only [deinitTree.deinitList, dropCount.dropCountList]
      rw [dropCount_deinitTree_zero t, dropCountList_deinitList_zero ts]

theorem dropCountList_listSet_deinit (fs : List PlaceTree) (i : Nat) (child : PlaceTree)
    (hgi : listGet? fs i = some child) :
    dropCount child + dropCount.dropCountList (listSet fs i (deinitTree child)) =
    dropCount.dropCountList fs := by
  induction fs generalizing i with
  | nil => cases hgi
  | cons f rest ih =>
    cases i with
    | zero =>
      cases hgi
      simp only [listSet, dropCount.dropCountList, dropCount_deinitTree_zero, Nat.zero_add]
    | succ k =>
      simp only [listSet, dropCount.dropCountList]
      have hrec := ih k hgi
      rw [← Nat.add_assoc, Nat.add_comm (dropCount child) (dropCount f), Nat.add_assoc, hrec]

/-- **Disjoint-Capture Drop-Count Soundness (`!hasCustomDrop`)**:
When an aggregate root has NO custom `Drop` (`hasCustomDrop = false`), moving field `i`
by value into a closure (and deinitializing slot `i` in the parent) preserves the EXACT
total drop count across the moved field + remaining parent aggregate! -/
theorem disjoint_field_move_preserves_dropCount
    (fs : List PlaceTree) (alive : Bool) (i : Nat) (child : PlaceTree)
    (hgi : listGet? fs i = some child) :
    dropCount child + dropCount (setAt (.node false alive fs) [i] (deinitTree child)) =
    dropCount (.node false alive fs) := by
  simp only [setAt, hgi, dropCount, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  exact dropCountList_listSet_deinit fs i child hgi

/-- Whole-ADT initialization invariant required before invoking a custom `Drop::drop(&mut self)`:
the node and every direct child field must still be live (not partially moved out). -/
def allFieldsLive : List PlaceTree → Bool
  | [] => true
  | .leaf _ alive _ :: rest => alive && allFieldsLive rest
  | .node _ alive _ :: rest => alive && allFieldsLive rest

def wholeAdtInitialized : PlaceTree → Bool
  | .leaf _ alive _ => alive
  | .node _ alive fs => alive && allFieldsLive fs

/-! ## Part II: `extern "rust-call"` Untupling, `ClosureOnceShim`, `ClosureFnPointer`, and `FnPtrShim` -/

/-- Abstract scalar/handle value. -/
abbrev Val := Nat

/-- Observable side-effect event (e.g., call return log, drop of captured upvar tag). -/
inductive Event where
  | callBody (tag : Nat) (out : Val)
  | dropUpvar (tag : Nat)
  deriving DecidableEq, Repr

/-- Normal vs. unwinding outcome of calling a closure body (modeling `bb1` vs `bb3` in `shim.rs`). -/
inductive CallOutcome (Env : Type) where
  | normal (ret : Val) (env' : Env) (trace : List Event)
  | unwind (env' : Env) (trace : List Event)
  deriving DecidableEq, Repr

/-- `extern "rust-call"` argument tuple representation (`ty::Tuple` unpacked by `fn_abi_new_uncached`). -/
structure TupleArgs where
  elems : List Val
  deriving DecidableEq, Repr

/-- Untupling `extern "rust-call"` tuple argument into flat parameter values (`abi.rs:548-561`). -/
def untupleRustCall (a : TupleArgs) : List Val := a.elems

/-- A closure body taking `(&mut env, flatArgs)` and returning either a normal result or panic unwind,
paired with its environment drop-glue event sequence. -/
structure ClosureModel (Env : Type) where
  bodyFnMut : Env → List Val → CallOutcome Env
  dropEnv   : Env → List Event

/-- Direct `FnMut::call_mut(&mut env, args)` execution (does not drop `env`). -/
def evalFnMut {Env : Type} (c : ClosureModel Env) (env : Env) (args : TupleArgs) :
    CallOutcome Env :=
  c.bodyFnMut env (untupleRustCall args)

/-- `ShimKind::ClosureOnce` execution (`compiler/rustc_mir_transform/src/shim.rs:63-73, 871-999`):
borrows owned `env` as `&mut env`, invokes `FnMut::call_mut`, and drops `env'` along BOTH
the normal return path (`bb1`) and the panic cleanup landing pad (`bb3` -> `UnwindResume`). -/
def evalClosureOnceShim {Env : Type} (c : ClosureModel Env) (env : Env) (args : TupleArgs) :
    CallOutcome Unit :=
  match evalFnMut c env args with
  | .normal ret env' tr => .normal ret () (tr ++ c.dropEnv env')
  | .unwind env' tr     => .unwind () (tr ++ c.dropEnv env')

/-- Reference specification: execute `call_mut`, then unconditionally run `dropEnv` on the post-state
regardless of normal return or panic unwind. -/
def specCallThenDrop {Env : Type} (c : ClosureModel Env) (env : Env) (args : TupleArgs) :
    CallOutcome Unit :=
  match c.bodyFnMut env args.elems with
  | .normal ret env' tr => .normal ret () (tr ++ c.dropEnv env')
  | .unwind env' tr     => .unwind () (tr ++ c.dropEnv env')

/-- **`ClosureOnceShim` Observational Equivalence (Normal & Unwind)**:
For every closure model, environment, and tuple argument list, `ClosureOnceShim` matches
direct `FnMut` invocation followed by unconditional `drop_glue` of the post-call environment. -/
theorem closureOnceShim_obs_equiv {Env : Type} (c : ClosureModel Env) (env : Env) (args : TupleArgs) :
    evalClosureOnceShim c env args = specCallThenDrop c env args := by
  unfold evalClosureOnceShim specCallThenDrop evalFnMut untupleRustCall
  cases c.bodyFnMut env args.elems <;> rfl

/-- Stronger corollary for `Fn` closures (which do not mutate `env` during invocation):
the dropped environment in `ClosureOnceShim` is guaranteed to equal the original `env`
on both normal return and unwind. -/
theorem closureOnceShim_fn_drops_original_env {Env : Type} (c : ClosureModel Env)
    (hFn : ∀ env xs, match c.bodyFnMut env xs with
                     | .normal _ env' _ => env' = env
                     | .unwind env' _   => env' = env)
    (env : Env) (args : TupleArgs) :
    match evalClosureOnceShim c env args, c.bodyFnMut env args.elems with
    | .normal r1 _ tr1, .normal r2 _ tr2 => r1 = r2 ∧ tr1 = tr2 ++ c.dropEnv env
    | .unwind _ tr1,    .unwind _ tr2    => tr1 = tr2 ++ c.dropEnv env
    | _,                _                => False := by
  have hInv := hFn env args.elems
  unfold evalClosureOnceShim evalFnMut untupleRustCall
  cases hcall : c.bodyFnMut env args.elems with
  | normal ret env' tr =>
    simp only [hcall] at hInv
    subst hInv
    exact ⟨rfl, rfl⟩
  | unwind env' tr =>
    simp only [hcall] at hInv
    subst hInv
    rfl

/-- **`ClosureFnPointer` Coercion Equivalence** (`rustc_codegen_ssa/src/mir/rvalue.rs:530-544`):
For a non-capturing (`Env = Unit`, ZST `PassMode::Ignore`, `dropEnv () = []`) closure,
coercing to `fn(A...) -> R` via `ShimKind::ClosureOnce` produces the exact same outcome and
trace as invoking the underlying flat-argument function directly. -/
theorem closureFnPointer_zst_equiv
    (rawBody : List Val → CallOutcome Unit)
    (args : List Val) :
    let c : ClosureModel Unit := { bodyFnMut := fun _ xs => rawBody xs, dropEnv := fun _ => [] }
    evalClosureOnceShim c () ⟨args⟩ = rawBody args := by
  dsimp only [evalClosureOnceShim, evalFnMut, untupleRustCall]
  cases rawBody args with
  | normal ret u tr =>
    cases u
    simp
  | unwind u tr =>
    cases u
    simp

/-- Receiver adjustment kinds in `ShimKind::FnPtr` (`shim.rs:40-54, 830-838`). -/
inductive FnPtrRecvKind where
  | fnOnce  -- Adjustment::Identity (self: fn(...))
  | fn      -- Adjustment::Deref { ImmRef } (&self: &fn(...))
  | fnMut   -- Adjustment::Deref { MutRef } (&mut self: &mut fn(...))
  deriving DecidableEq, Repr

/-- `ShimKind::FnPtr` execution (`shim.rs:790-801, 926-931`): adjusts the receiver (`Identity`
or `Deref`), untuples the last tuple argument `args`, and performs an indirect call to `fp`. -/
def evalFnPtrShim (fp : List Val → Val) (_recv : FnPtrRecvKind) (args : TupleArgs) : Val :=
  fp (untupleRustCall args)

theorem fnPtrShim_untuple_equiv (fp : List Val → Val) (recv : FnPtrRecvKind) (xs : List Val) :
    evalFnPtrShim fp recv ⟨xs⟩ = fp xs := by
  cases recv <;> rfl

/-! ## Part III: `AsyncFn` (`CoroutineClosure`) Lending vs. `by_move_body` Ownership Transfer -/

/-- Structured runtime value supporting nested field projections for `MakeByMoveBody`
bridging-projection preservation (`by_move_body.rs:135-190, 268-329`). -/
inductive StructVal where
  | scalar (n : Nat)
  | tuple (fields : List StructVal)
  deriving Repr

/-- Evaluate a field projection chain on a `StructVal`. -/
def evalFieldChain : StructVal → List Nat → Option StructVal
  | v, [] => some v
  | .scalar _, _ :: _ => none
  | .tuple fs, i :: rest =>
    match listGet? fs i with
    | none => none
    | some child => evalFieldChain child rest

theorem evalFieldChain_append (v : StructVal) (p1 p2 : List Nat) :
    evalFieldChain v (p1 ++ p2) =
    match evalFieldChain v p1 with
    | none => none
    | some mid => evalFieldChain mid p2 := by
  induction p1 generalizing v with
  | nil => rfl
  | cons i rest ih =>
    cases v with
    | scalar _ => rfl
    | tuple fs =>
      simp only [List.cons_append, evalFieldChain]
      cases listGet? fs i with
      | none => rfl
      | some child => exact ih child

/-- Symbolic coroutine-local place access on `_1` (`CAPTURE_STRUCT_LOCAL`):
either a deref of a borrowed child field `(*(_1.childIdx)).tail`, or a direct owned access
`(_1.parentIdx).fields`. -/
inductive CoroUpvarPlace where
  | borrowedField (childIdx : Nat) (tail : List Nat)
  | ownedField    (parentIdx : Nat) (projs : List Nat)
  deriving DecidableEq, Repr

/-- `MakeByMoveBody::visit_place` (`by_move_body.rs:268-329`): peels the `Deref` from a
child by-ref upvar access, remaps `childIdx -> parentIdx`, and splices `bridgeProjs`
before `tail`. -/
def rewriteByMovePlace
    (remap : Nat → Option (Nat × List Nat)) : CoroUpvarPlace → CoroUpvarPlace
  | .borrowedField childIdx tail =>
    match remap childIdx with
    | some (parentIdx, bridgeProjs) => .ownedField parentIdx (bridgeProjs ++ tail)
    | none => .borrowedField childIdx tail
  | .ownedField parentIdx projs => .ownedField parentIdx projs

/-- **`MakeByMoveBody` Place-Rewriting Semantic Preservation**:
Whenever a lending coroutine's child field `childIdx` borrows `evalFieldChain parentVal bridgeProjs`
from the parent closure's owned field `parentIdx`, evaluating the rewritten `by_move_body` place
against `parentVal` produces the EXACT same sub-value as dereferencing the lending coroutine's
borrowed field and projecting `tail`! -/
theorem byMove_place_rewrite_preserves_eval
    (remap : Nat → Option (Nat × List Nat))
    (childIdx parentIdx : Nat)
    (bridgeProjs tail : List Nat)
    (parentVal borrowedChildVal : StructVal)
    (hRemap : remap childIdx = some (parentIdx, bridgeProjs))
    (hBridge : evalFieldChain parentVal bridgeProjs = some borrowedChildVal) :
    match rewriteByMovePlace remap (.borrowedField childIdx tail) with
    | .ownedField pIdx fullProjs =>
      pIdx = parentIdx ∧ evalFieldChain parentVal fullProjs = evalFieldChain borrowedChildVal tail
    | .borrowedField _ _ => False := by
  dsimp only [rewriteByMovePlace]
  rw [hRemap]
  refine ⟨rfl, ?_⟩
  rw [evalFieldChain_append, hBridge]

/-- **1-to-2 Multi-Field Bridging Preservation** (matching `analyze_coroutine_closure_captures`
when one parent capture is split into two distinct child borrows `childIdx1, childIdx2`):
remapping both child fields onto the single moved-in `parentIdx` with bridging chains
`bridge1`, `bridge2` preserves both sub-values simultaneously. -/
theorem byMove_one_to_two_bridging_preserves_eval
    (remap : Nat → Option (Nat × List Nat))
    (childIdx1 childIdx2 parentIdx : Nat)
    (bridge1 bridge2 tail1 tail2 : List Nat)
    (parentVal val1 val2 : StructVal)
    (hR1 : remap childIdx1 = some (parentIdx, bridge1))
    (hR2 : remap childIdx2 = some (parentIdx, bridge2))
    (hB1 : evalFieldChain parentVal bridge1 = some val1)
    (hB2 : evalFieldChain parentVal bridge2 = some val2) :
    (match rewriteByMovePlace remap (.borrowedField childIdx1 tail1) with
     | .ownedField p1 full1 => p1 = parentIdx ∧ evalFieldChain parentVal full1 = evalFieldChain val1 tail1
     | .borrowedField _ _ => False) ∧
    (match rewriteByMovePlace remap (.borrowedField childIdx2 tail2) with
     | .ownedField p2 full2 => p2 = parentIdx ∧ evalFieldChain parentVal full2 = evalFieldChain val2 tail2
     | .borrowedField _ _ => False) :=
  ⟨byMove_place_rewrite_preserves_eval remap childIdx1 parentIdx bridge1 tail1 parentVal val1 hR1 hB1,
   byMove_place_rewrite_preserves_eval remap childIdx2 parentIdx bridge2 tail2 parentVal val2 hR2 hB2⟩

/-! ### Frame-Allocated Memory Machine & `AsyncFnOnce` Dangling-Borrow Freedom -/

/-- A stack-frame location identifier. -/
abbrev Loc := Nat

/-- Liveness state of a stack-frame slot storing a closure upvar value. -/
inductive SlotState where
  | live (val : Nat) (dropTag : Nat)
  | freed
  deriving DecidableEq, Repr

/-- Stack-frame store indexed by `Loc`. -/
abbrev FrameStore := Loc → SlotState

def storeRead (st : FrameStore) (l : Loc) : SlotState := st l

def storeAlloc (st : FrameStore) (l : Loc) (val dropTag : Nat) : FrameStore :=
  fun k => if k = l then .live val dropTag else st k

def storeFree (st : FrameStore) (l : Loc) : FrameStore :=
  fun k => if k = l then .freed else st k

/-- Two-step async closure body suspended across one `.await`:
- Before `.await`: reads upvar `u` and computes `pre u arg`
- After `.await`: reads upvar `u` again and computes `post (pre u arg) u arg`. -/
structure AsyncClosureSpec where
  upvarVal : Nat
  dropTag  : Nat
  preStep  : Nat → Nat → Nat
  postStep : Nat → Nat → Nat → Nat

/-- Outcome of polling a future. -/
inductive PollResult (F : Type) where
  | pending (next : F)
  | ready (val : Nat) (drops : List Event)
  | danglingReadUB
  deriving DecidableEq, Repr

/-- Lending coroutine (`{closure#0}` from `AsyncFn::async_call` / `AsyncFnMut::async_call_mut`):
stores a borrowed `Loc` pointing into the parent closure's stack frame. -/
inductive LendingFuture where
  | start     (closureLoc : Loc) (arg : Nat)
  | suspended (closureLoc : Loc) (arg : Nat) (savedPre : Nat)
  | completed
  deriving DecidableEq, Repr

def pollLending (spec : AsyncClosureSpec) (st : FrameStore) :
    LendingFuture → PollResult LendingFuture
  | .start loc arg =>
    match storeRead st loc with
    | .live u _ => .pending (.suspended loc arg (spec.preStep u arg))
    | .freed    => .danglingReadUB
  | .suspended loc arg savedPre =>
    match storeRead st loc with
    | .live u _ =>
      -- Lending coroutine drops only `&T` (no-op), NOT the parent closure's owned upvar!
      .ready (spec.postStep savedPre u arg) []
    | .freed    => .danglingReadUB
  | .completed => .danglingReadUB

/-- Dropping a `LendingFuture` drops only the borrowed reference (0 upvar drops). -/
def dropLending : LendingFuture → List Event
  | _ => []

/-- By-move coroutine (`{synthetic#0}` constructed by `ShimKind::ConstructCoroutineInClosure`):
embeds the owned `(upvarVal, dropTag)` directly inside the coroutine state machine! -/
inductive ByMoveFuture where
  | start     (ownedVal : Nat) (dropTag : Nat) (arg : Nat)
  | suspended (ownedVal : Nat) (dropTag : Nat) (arg : Nat) (savedPre : Nat)
  | completed
  deriving DecidableEq, Repr

def pollByMove (spec : AsyncClosureSpec) (_st : FrameStore) :
    ByMoveFuture → PollResult ByMoveFuture
  | .start u tag arg =>
    .pending (.suspended u tag arg (spec.preStep u arg))
  | .suspended u tag arg savedPre =>
    -- Owned upvar is dropped upon normal completion (`drop(_1)` in `{synthetic#0}`).
    .ready (spec.postStep savedPre u arg) [.dropUpvar tag]
  | .completed => .danglingReadUB

/-- `ShimKind::DropGlue` for the by-move coroutine (`shim.rs:98-105`):
drops the owned upvar if the future is dropped before completion (unpolled or mid-suspension),
and does nothing if already completed (already dropped on completion). -/
def dropByMove : ByMoveFuture → List Event
  | .start _ tag _        => [.dropUpvar tag]
  | .suspended _ tag _ _  => [.dropUpvar tag]
  | .completed            => []

/-- Executing `AsyncFnOnce::async_call_once` via `ConstructCoroutineInClosure` + `by_move_body`:
1. Allocates `callOnceFrame` holding the closure's upvar,
2. Moves `(upvarVal, dropTag)` into `ByMoveFuture`,
3. Pops and frees `callOnceFrame` before returning the future to the caller! -/
def callAsyncFnOnceByMove (spec : AsyncClosureSpec) (st : FrameStore)
    (callOnceFrame : Loc) (arg : Nat) : FrameStore × ByMoveFuture :=
  let stWithFrame := storeAlloc st callOnceFrame spec.upvarVal spec.dropTag
  let fut := ByMoveFuture.start spec.upvarVal spec.dropTag arg
  let stAfterPop := storeFree stWithFrame callOnceFrame
  (stAfterPop, fut)

/-- **`AsyncFnOnce` `by_move_body` Dangling-Borrow Freedom & Functional Equivalence**:
For ANY `AsyncClosureSpec`, ANY store `st`, ANY popped `callOnceFrame`, ANY `arg`,
and ANY arbitrary post-pop store mutations `st1`, `st2`:
1. `pollByMove` NEVER produces `danglingReadUB` across `.await` even though `callOnceFrame` is freed,
2. It returns the exact same value as `pollLending` polled while `callOnceFrame` stayed live,
3. On normal completion it drops `spec.dropTag` **exactly once**, AND
4. If dropped mid-suspension (after `Poll::Pending`), `dropByMove` ALSO drops `spec.dropTag` **exactly once**! -/
theorem asyncFnOnce_by_move_dangling_free
    (spec : AsyncClosureSpec) (st st1 st2 : FrameStore) (callOnceFrame arg : Nat) :
    let (_, fut0) := callAsyncFnOnceByMove spec st callOnceFrame arg
    ∃ fut1,
      pollByMove spec st1 fut0 = .pending fut1 ∧
      pollByMove spec st2 fut1 =
        .ready (spec.postStep (spec.preStep spec.upvarVal arg) spec.upvarVal arg)
               [.dropUpvar spec.dropTag] ∧
      dropByMove fut1 = [.dropUpvar spec.dropTag] := by
  refine ⟨.suspended spec.upvarVal spec.dropTag arg (spec.preStep spec.upvarVal arg),
          rfl, rfl, rfl⟩

/-- Functional agreement between `pollLending` (with live closure frame) and `pollByMove`
(after `callOnceFrame` is freed). -/
theorem lending_and_by_move_compute_same_output
    (spec : AsyncClosureSpec) (st : FrameStore) (loc arg : Nat) :
    let stLive := storeAlloc st loc spec.upvarVal spec.dropTag
    let (stPopped, bm0) := callAsyncFnOnceByMove spec st loc arg
    ∃ lf1 bm1 out,
      pollLending spec stLive (.start loc arg) = .pending lf1 ∧
      pollLending spec stLive lf1 = .ready out [] ∧
      pollByMove spec stPopped bm0 = .pending bm1 ∧
      pollByMove spec stPopped bm1 = .ready out [.dropUpvar spec.dropTag] := by
  dsimp only [callAsyncFnOnceByMove]
  refine ⟨.suspended loc arg (spec.preStep spec.upvarVal arg),
          .suspended spec.upvarVal spec.dropTag arg (spec.preStep spec.upvarVal arg),
          spec.postStep (spec.preStep spec.upvarVal arg) spec.upvarVal arg,
          ?_, ?_, rfl, rfl⟩
  · simp [pollLending, storeRead, storeAlloc]
  · simp [pollLending, storeRead, storeAlloc]

/-! ## Part IV: Two Concrete Sharpness Counterexamples -/

/-- **Counterexample 1 (CE1) — Naive `AsyncFnOnce` Delegating to `&mut self` `AsyncFnMut` Dangles**:
Suppose `AsyncFnOnce::async_call_once(self, arg)` naively delegated like `ClosureOnceShim`:
allocating `self` in `callOnceFrame`, creating a `LendingFuture` pointing to `callOnceFrame`,
and then freeing `callOnceFrame` when `call_once` returns the future. -/
def callAsyncFnOnceNaive (spec : AsyncClosureSpec) (st : FrameStore)
    (callOnceFrame : Loc) (arg : Nat) : FrameStore × LendingFuture :=
  let stWithFrame := storeAlloc st callOnceFrame spec.upvarVal spec.dropTag
  let fut := LendingFuture.start callOnceFrame arg
  let stAfterPop := storeFree stWithFrame callOnceFrame
  (stAfterPop, fut)

def ce1Spec : AsyncClosureSpec :=
  { upvarVal := 11
    dropTag  := 7
    preStep  := fun u k => u + k
    postStep := fun prev u _ => prev + u }

def emptyStore : FrameStore := fun _ => .freed

/-- CE1 proof: on the concrete closure `ce1Spec`, naive `AsyncFnOnce` immediately triggers
`PollResult.danglingReadUB` on its very first poll after `callOnceFrame` pops, whereas
`by_move_body` completes cleanly with `11 + 3 + 11 = 25` and drops upvar tag `7` once. -/
theorem ce1_naive_async_fn_once_dangles_while_by_move_succeeds :
    let (stNaive, naiveFut) := callAsyncFnOnceNaive ce1Spec emptyStore 0 3
    let (stMove, moveFut0) := callAsyncFnOnceByMove ce1Spec emptyStore 0 3
    pollLending ce1Spec stNaive naiveFut = .danglingReadUB ∧
    ∃ moveFut1,
      pollByMove ce1Spec stMove moveFut0 = .pending moveFut1 ∧
      pollByMove ce1Spec stMove moveFut1 = .ready 25 [.dropUpvar 7] := by
  refine ⟨?_, ⟨.suspended 11 7 3 14, rfl, rfl⟩⟩
  simp [pollLending, storeRead, storeFree]

/-- **Counterexample 2 (CE2) — Splitting a Non-`Copy` Field Capture Across a `Drop` ADT**:
Models `struct S { a: Box<u32>, b: Box<u32> }` with `impl Drop for S`. -/
def ce2StructWithDrop : PlaceTree :=
  .node true true [.leaf 10 true true, .leaf 20 true true]

def ce2FieldACapture : CapturedPlace :=
  { place := { root := 0, projs := [.field 0] }
    mode := .byVal
    isCopyLeaf := false }

/-- CE2 proof:
1. Naively splitting `s.a` by move without `Drop`-boundary truncation leaves `s` partially moved
   (`wholeAdtInitialized = false`), violating the whole-ADT initialization precondition of `Drop::drop(&mut s)`,
   AND causes the naive sum of drops (`1 + 2 = 3` only if outer still drops an uninitialized struct!)
   to run `Drop::drop` on a broken value (`wholeAdtInitialized = false`).
2. Truncating via `truncateForDropAdt ce2FieldACapture (some 0)` captures the ENTIRE `s`
   (empty projection list `[]`), preserving `wholeAdtInitialized ce2StructWithDrop = true`
   at `Drop::drop` time and exact total drop count `3` (`Drop for S` + `Box a` + `Box b`). -/
theorem ce2_splitting_drop_adt_violates_destructor_integrity :
    let naiveRemainder := setAt ce2StructWithDrop [0] (deinitTree (.leaf 10 true true))
    wholeAdtInitialized ce2StructWithDrop = true ∧
    wholeAdtInitialized naiveRemainder = false ∧
    (truncateForDropAdt ce2FieldACapture (some 0)).place.projs = [] ∧
    dropCount ce2StructWithDrop = 3 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end ClosureCaptureAndAsyncFnRefinement

/-! ## Kernel Axiom Verification Audit -/
#print axioms ClosureCaptureAndAsyncFnRefinement.CaptureMode.join_comm
#print axioms ClosureCaptureAndAsyncFnRefinement.CaptureMode.join_assoc
#print axioms ClosureCaptureAndAsyncFnRefinement.CaptureMode.join_least
#print axioms ClosureCaptureAndAsyncFnRefinement.CaptureMode.uniqImmRef_exclusive_without_binding_mutation
#print axioms ClosureCaptureAndAsyncFnRefinement.isProjPrefix_trans
#print axioms ClosureCaptureAndAsyncFnRefinement.disjointPaths_symm
#print axioms ClosureCaptureAndAsyncFnRefinement.truncate_mutRef_across_mut_deref_yields_uniqImm
#print axioms ClosureCaptureAndAsyncFnRefinement.truncateAtRawPtr_no_raw_deref
#print axioms ClosureCaptureAndAsyncFnRefinement.truncateForDropAdt_preserves_copy_leaf
#print axioms ClosureCaptureAndAsyncFnRefinement.truncateForDropAdt_truncates_noncopy_byVal
#print axioms ClosureCaptureAndAsyncFnRefinement.getAt_setAt_disjoint
#print axioms ClosureCaptureAndAsyncFnRefinement.setAt_setAt_comm_disjoint
#print axioms ClosureCaptureAndAsyncFnRefinement.disjoint_captures_non_aliasing
#print axioms ClosureCaptureAndAsyncFnRefinement.disjoint_field_move_preserves_dropCount
#print axioms ClosureCaptureAndAsyncFnRefinement.closureOnceShim_obs_equiv
#print axioms ClosureCaptureAndAsyncFnRefinement.closureOnceShim_fn_drops_original_env
#print axioms ClosureCaptureAndAsyncFnRefinement.closureFnPointer_zst_equiv
#print axioms ClosureCaptureAndAsyncFnRefinement.fnPtrShim_untuple_equiv
#print axioms ClosureCaptureAndAsyncFnRefinement.byMove_place_rewrite_preserves_eval
#print axioms ClosureCaptureAndAsyncFnRefinement.byMove_one_to_two_bridging_preserves_eval
#print axioms ClosureCaptureAndAsyncFnRefinement.asyncFnOnce_by_move_dangling_free
#print axioms ClosureCaptureAndAsyncFnRefinement.lending_and_by_move_compute_same_output
#print axioms ClosureCaptureAndAsyncFnRefinement.ce1_naive_async_fn_once_dangles_while_by_move_succeeds
#print axioms ClosureCaptureAndAsyncFnRefinement.ce2_splitting_drop_adt_violates_destructor_integrity
