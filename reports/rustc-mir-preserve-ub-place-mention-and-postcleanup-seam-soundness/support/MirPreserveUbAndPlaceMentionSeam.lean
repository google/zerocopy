/-!
# Formal Semantics and Soundness of `-Zmir-preserve-ub`, `PlaceMention`, `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`

Standalone Lean 4 (`v4.34.1`, zero external imports) formalization of:
1. Pointer, allocation, and `checkAndDerefPtr` / `offsetPtrInbounds` operational semantics
   matching `compiler/rustc_const_eval/src/interpret/{step,place,projection,memory,intrinsics}.rs`
   (`rust-lang/rust`).
2. Place evaluation `evalPlaceMPlace` (implementing RFC 2582 raw-pointer zero-offset place
   creation without dereferenceability/alignment/read checks vs. `OffsetMode::Inbounds` on
   non-zero field/index offsets vs. reference validity checks) contrasted against the naive
   counterfactual model `evalPlaceNaiveFullRead`.
3. `Runtime(Initial)` to `Runtime(PostCleanup)` lowering parameterized by `mirPreserveUb : Bool`
   (`RemovePlaceMention` + `SimplifyCfg::PreOptimizations` (`stripNops` and `simplifyEqualBranch`))
   and pre-cleanup `Derefer` + `EraseDerefTemps` hoisting on chained dereferences.
4. Core soundness, unsoundness, and conditional soundness theorems:
   - Exact semantic equivalence (`evalBody`) between `Runtime(Initial)` and
     `Runtime(PostCleanup, mirPreserveUb := true)` (both on `nop`-free bodies and up to exact
     `nop`-compression fuel adjustment for arbitrary bodies);
   - Strict unsoundness (silent UB erasure) of `Runtime(PostCleanup, mirPreserveUb := false)`
     relative to `Runtime(Initial)` / Miri operational semantics;
   - Exact equivalence of `RemovePlaceMention` and default `Runtime(PostCleanup)` when restricted
     to certified places (`safeToErasePlaceMention`, covering unprojected/local-only places and
     initialized raw-pointer zero-offset places) and certified switch discriminants.
5. Four constructive, kernel-evaluated (`rfl`) counterexamples proving exact theorem sharpness.
-/

namespace MirPreserveUbSeam

/-! ## Section 1: Primitive List Helpers, Values, Pointers, and Memory -/

def listGet {α : Type} (xs : List α) (n : Nat) : Option α :=
  (Nat.rec (motive := fun _ => List α → Option α)
    (fun l => match l with | [] => none | x :: _ => some x)
    (fun _ ih l => match l with | [] => none | _ :: tl => ih tl)
    n) xs

theorem listGet_nil {α : Type} (n : Nat) : listGet ([] : List α) n = none := by
  cases n <;> rfl

theorem listGet_cons_zero {α : Type} (x : α) (xs : List α) :
    listGet (x :: xs) 0 = some x := rfl

theorem listGet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) :
    listGet (x :: xs) (n + 1) = listGet xs n := rfl

theorem listGet_map {α β : Type} (f : α → β) (xs : List α) (n : Nat) :
    listGet (xs.map f) n = (listGet xs n).map f := by
  induction xs generalizing n with
  | nil => simp only [List.map_nil, listGet_nil]; rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ k => simp only [List.map_cons, listGet_cons_succ, ih]

def listSet {α : Type} (xs : List α) (n : Nat) (v : α) : Option (List α) :=
  (Nat.rec (motive := fun _ => List α → α → Option (List α))
    (fun l val => match l with | [] => none | _ :: tl => some (val :: tl))
    (fun _ ih l val =>
      match l with
      | [] => none
      | x :: tl =>
        match ih tl val with
        | some tl' => some (x :: tl')
        | none => none)
    n) xs v

theorem listSet_nil {α : Type} (n : Nat) (v : α) : listSet ([] : List α) n v = none := by
  cases n <;> rfl

theorem listSet_cons_zero {α : Type} (x : α) (xs : List α) (v : α) :
    listSet (x :: xs) 0 v = some (v :: xs) := rfl

theorem listSet_cons_succ {α : Type} (x : α) (xs : List α) (n : Nat) (v : α) :
    listSet (x :: xs) (n + 1) v =
      match listSet xs n v with
      | some xs' => some (x :: xs')
      | none => none := rfl

theorem listGet_length_lt {α : Type} {xs : List α} {n : Nat} {v : α}
    (h : listGet xs n = some v) : n < xs.length := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at h; cases h
  | cons _ xs ih =>
    cases n with
    | zero => exact Nat.zero_lt_succ _
    | succ k =>
      rw [listGet_cons_succ] at h
      exact Nat.succ_lt_succ (ih h)

theorem listSet_length_eq {α : Type} {xs xs' : List α} {n : Nat} {v : α}
    (h : listSet xs n v = some xs') : xs'.length = xs.length := by
  induction xs generalizing xs' n with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ xs ih =>
    cases n with
    | zero =>
      rw [listSet_cons_zero] at h
      cases h
      rfl
    | succ k =>
      rw [listSet_cons_succ] at h
      cases hrec : listSet xs k v with
      | none => rw [hrec] at h; cases h
      | some tail =>
        rw [hrec] at h
        cases h
        exact congrArg Nat.succ (ih hrec)

theorem listGet_listSet_eq {α : Type} {xs xs' : List α} {n : Nat} {v : α}
    (h : listSet xs n v = some xs') : listGet xs' n = some v := by
  induction xs generalizing xs' n with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ xs ih =>
    cases n with
    | zero =>
      rw [listSet_cons_zero] at h
      cases h
      rfl
    | succ k =>
      rw [listSet_cons_succ] at h
      cases hrec : listSet xs k v with
      | none => rw [hrec] at h; cases h
      | some tail =>
        rw [hrec] at h
        cases h
        rw [listGet_cons_succ]
        exact ih hrec

theorem listGet_listSet_ne {α : Type} {xs xs' : List α} {n m : Nat} {v : α}
    (h : listSet xs n v = some xs') (hne : n ≠ m) :
    listGet xs' m = listGet xs m := by
  induction xs generalizing xs' n m with
  | nil => rw [listSet_nil] at h; cases h
  | cons _ xs ih =>
    cases n with
    | zero =>
      cases m with
      | zero => exact False.elim (hne rfl)
      | succ k =>
        rw [listSet_cons_zero] at h
        cases h
        rfl
    | succ n' =>
      cases m with
      | zero =>
        rw [listSet_cons_succ] at h
        cases hrec : listSet xs n' v with
        | none => rw [hrec] at h; cases h
        | some tail =>
          rw [hrec] at h
          cases h
          rfl
      | succ m' =>
        rw [listSet_cons_succ] at h
        cases hrec : listSet xs n' v with
        | none => rw [hrec] at h; cases h
        | some tail =>
          rw [hrec] at h
          cases h
          rw [listGet_cons_succ, listGet_cons_succ]
          exact ih hrec (fun heq => hne (congrArg Nat.succ heq))

def listAll {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  xs.foldr (fun x ih => p x && ih) true

theorem listAll_nil {α : Type} (p : α → Bool) : listAll p [] = true := rfl

theorem listAll_cons {α : Type} (p : α → Bool) (x : α) (xs : List α) :
    listAll p (x :: xs) = (p x && listAll p xs) := rfl

theorem listAll_map {α β : Type} (p : β → Bool) (f : α → β) (xs : List α) :
    listAll p (xs.map f) = listAll (fun x => p (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, listAll_cons, ih]

theorem listAll_get {α : Type} {p : α → Bool} {xs : List α} {n : Nat} {x : α}
    (hall : listAll p xs = true) (hget : listGet xs n = some x) : p x = true := by
  induction xs generalizing n with
  | nil => rw [listGet_nil] at hget; cases hget
  | cons hd tl ih =>
    simp only [listAll_cons, Bool.and_eq_true] at hall
    cases n with
    | zero =>
      rw [listGet_cons_zero] at hget
      cases hget
      exact hall.1
    | succ k =>
      rw [listGet_cons_succ] at hget
      exact ih hall.2 hget

def listMapFold {α β : Type} (f : α → β) (xs : List α) : List β :=
  xs.foldr (fun x ih => f x :: ih) []

theorem listMapFold_nil {α β : Type} (f : α → β) : listMapFold f [] = [] := rfl

theorem listMapFold_cons {α β : Type} (f : α → β) (x : α) (xs : List α) :
    listMapFold f (x :: xs) = f x :: listMapFold f xs := rfl

theorem listMapFold_eq_map {α β : Type} (f : α → β) (xs : List α) :
    listMapFold f xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listMapFold_cons, List.map_cons, ih]

inductive PtrKind where
  | rawPtr
  | safeRef
  deriving Repr, DecidableEq

inductive PtrVal where
  | null
  | danglingAddr (addr : Nat)
  | allocPtr (allocId : Nat) (offset : Nat)
  deriving Repr, DecidableEq

structure PointeeLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq

inductive Val where
  | intVal (n : Nat)
  | boolVal (b : Bool)
  | invalidBoolByte (byteVal : Nat)
  | ptrVal (p : PtrVal)
  | unitVal
  deriving Repr, DecidableEq

inductive LocalSlot where
  | dead
  | liveUninit
  | liveInit (v : Val)
  deriving Repr, DecidableEq

structure AllocInfo where
  live : Bool
  sizeBytes : Nat
  alignBytes : Nat
  baseAddr : Nat
  storedVal : Option Val := none
  deriving Repr, DecidableEq

structure MachineState where
  locals : List LocalSlot
  allocs : List AllocInfo
  deriving Repr, DecidableEq

inductive UbKind where
  | uninitRead
  | invalidBoolRead
  | deadLocalAccess
  | nullInboundsOrDeref
  | danglingPtrAccess
  | outOfBoundsPtrArithmetic
  | misalignedRefDeref
  | boundsCheckFailed
  | reachedUnreachable
  | malformedProgram
  deriving Repr, DecidableEq

/-- `checkAndDerefPtr` models `InterpCx::check_and_deref_ptr` in
`compiler/rustc_const_eval/src/interpret/memory.rs`. Crucially, a zero-byte
request (`accessSize = 0`) returns `.ok ()` unconditionally without resolving
allocation bounds or nullness, whereas any non-zero `accessSize` requires a live
allocation with `offset + accessSize <= sizeBytes`. -/
def checkAndDerefPtr (allocs : List AllocInfo) (p : PtrVal) (accessSize : Nat) :
    Except UbKind Unit :=
  if accessSize == 0 then
    .ok ()
  else
    match p with
    | .null => .error .nullInboundsOrDeref
    | .danglingAddr _ => .error .danglingPtrAccess
    | .allocPtr aid off =>
      match listGet allocs aid with
      | none => .error .danglingPtrAccess
      | some info =>
        if !info.live then
          .error .danglingPtrAccess
        else if off + accessSize <= info.sizeBytes then
          .ok ()
        else
          .error .outOfBoundsPtrArithmetic

def ptrAddr (allocs : List AllocInfo) : PtrVal → Option Nat
  | .null => some 0
  | .danglingAddr addr => some addr
  | .allocPtr aid off =>
    match listGet allocs aid with
    | none => none
    | some info => some (info.baseAddr + off)

def ptrAligned (allocs : List AllocInfo) (p : PtrVal) (align : Nat) : Bool :=
  if align <= 1 then
    true
  else
    match ptrAddr allocs p with
    | none => false
    | some addr => addr % align == 0

/-- `checkRefDeref` models the reference/box branch of `InterpCx::deref_pointer`
(`compiler/rustc_const_eval/src/interpret/place.rs`): references and `Box`
forbid null (even for zero-sized pointees), check dereferenceability of
`layout.size` bytes, and check alignment `layout.align`. -/
def checkRefDeref (allocs : List AllocInfo) (p : PtrVal) (layout : PointeeLayout) :
    Except UbKind Unit :=
  match p with
  | .null => .error .nullInboundsOrDeref
  | _ =>
    match checkAndDerefPtr allocs p layout.size with
    | .error k => .error k
    | .ok () =>
      if ptrAligned allocs p layout.align then
        .ok ()
      else
        .error .misalignedRefDeref

def shiftPtr (p : PtrVal) (delta : Nat) : PtrVal :=
  if delta == 0 then
    p
  else
    match p with
    | .null => .danglingAddr delta
    | .danglingAddr a => .danglingAddr (a + delta)
    | .allocPtr aid off => .allocPtr aid (off + delta)

/-- `offsetPtrInbounds` models `InterpCx::ptr_offset_inbounds`
(`compiler/rustc_const_eval/src/interpret/intrinsics.rs` ->
`check_ptr_access_signed` -> `check_and_deref_ptr`). Zero-offset field
projections succeed on null/dangling pointers because `checkAndDerefPtr` short-
circuits on `delta = 0`; non-zero field offsets (`delta > 0`) trigger immediate
`InboundsPointerArithmetic` UB on null/dangling/OOB pointers. -/
def offsetPtrInbounds (allocs : List AllocInfo) (p : PtrVal) (delta : Nat) :
    Except UbKind PtrVal :=
  match checkAndDerefPtr allocs p delta with
  | .error k => .error k
  | .ok () => .ok (shiftPtr p delta)

/-! ## Section 2: MIR Place Evaluation (`evalPlaceMPlace` vs. Naive Full Read) -/

inductive ProjElem where
  | deref (kind : PtrKind) (pointee : PointeeLayout)
  | field (offsetBytes : Nat)
  | index (idxLocal : Nat) (elemStride : Nat) (sliceLen : Nat)
  deriving Repr, DecidableEq

structure Place where
  localId : Nat
  projs : List ProjElem
  deriving Repr, DecidableEq

inductive PlaceBase where
  | localBase (lid : Nat)
  | memBase (ptr : PtrVal)
  deriving Repr, DecidableEq

def readPtrFromLocal (locals : List LocalSlot) (lid : Nat) : Except UbKind PtrVal :=
  match listGet locals lid with
  | none => .error .malformedProgram
  | some .dead => .error .deadLocalAccess
  | some .liveUninit => .error .uninitRead
  | some (.liveInit (.ptrVal p)) => .ok p
  | some (.liveInit _) => .error .malformedProgram

def readNatFromLocal (locals : List LocalSlot) (lid : Nat) : Except UbKind Nat :=
  match listGet locals lid with
  | none => .error .malformedProgram
  | some .dead => .error .deadLocalAccess
  | some .liveUninit => .error .uninitRead
  | some (.liveInit (.intVal n)) => .ok n
  | some (.liveInit _) => .error .malformedProgram

def stepProjMPlace (st : MachineState) (base : PlaceBase) (elem : ProjElem) :
    Except UbKind PlaceBase :=
  match elem with
  | .deref kind layout =>
    match base with
    | .memBase _ => .error .malformedProgram
    | .localBase lid =>
      match readPtrFromLocal st.locals lid with
      | .error k => .error k
      | .ok p =>
        match kind with
        | .rawPtr => .ok (.memBase p)
        | .safeRef =>
          match checkRefDeref st.allocs p layout with
          | .error k => .error k
          | .ok () => .ok (.memBase p)
  | .field offsetBytes =>
    match base with
    | .localBase lid => .ok (.localBase lid)
    | .memBase p =>
      match offsetPtrInbounds st.allocs p offsetBytes with
      | .error k => .error k
      | .ok p' => .ok (.memBase p')
  | .index idxLocal elemStride sliceLen =>
    match readNatFromLocal st.locals idxLocal with
    | .error k => .error k
    | .ok idx =>
      if idx < sliceLen then
        match base with
        | .localBase lid => .ok (.localBase lid)
        | .memBase p =>
          match offsetPtrInbounds st.allocs p (idx * elemStride) with
          | .error k => .error k
          | .ok p' => .ok (.memBase p')
      else
        .error .boundsCheckFailed

def runProjs (stepFn : PlaceBase → ProjElem → Except UbKind PlaceBase)
    (projs : List ProjElem) (base : PlaceBase) : Except UbKind PlaceBase :=
  (projs.foldr
    (fun elem ih b =>
      match stepFn b elem with
      | .error k => .error k
      | .ok b' => ih b')
    (fun b => .ok b)) base

theorem runProjs_nil (stepFn : PlaceBase → ProjElem → Except UbKind PlaceBase) (b : PlaceBase) :
    runProjs stepFn [] b = .ok b := rfl

theorem runProjs_cons (stepFn : PlaceBase → ProjElem → Except UbKind PlaceBase)
    (elem : ProjElem) (rest : List ProjElem) (b : PlaceBase) :
    runProjs stepFn (elem :: rest) b =
      match stepFn b elem with
      | .error k => .error k
      | .ok b' => runProjs stepFn rest b' := rfl

/-- `evalPlaceMPlace` models `InterpCx::eval_place` (`place.rs`) executed by
`StatementKind::PlaceMention(place)` (`step.rs`): it resolves the local base
without reading pointee memory bytes, enforces reference validity only for
`.safeRef` (never for `.rawPtr`, implementing RFC 2582), and enforces
`OffsetMode::Inbounds` on every subsequent `.field` or `.index` projection. -/
def evalPlaceMPlace (st : MachineState) (pl : Place) : Except UbKind PlaceBase :=
  if pl.localId < st.locals.length then
    runProjs (stepProjMPlace st) pl.projs (.localBase pl.localId)
  else
    .error .malformedProgram

/-- Counterfactual naive place evaluator that checks dereferenceability and
alignment even on raw-pointer dereferences inside `PlaceMention`. Proven in
`ce3_naive_full_read_semantics_for_place_mention_falsely_rejects_rfc2582_raw_deref`
to falsely reject valid RFC 2582 raw dereferences such as `let _ = *unaligned_raw_ptr;`. -/
def stepProjNaiveFullRead (st : MachineState) (base : PlaceBase) (elem : ProjElem) :
    Except UbKind PlaceBase :=
  match elem with
  | .deref _ layout =>
    match base with
    | .memBase _ => .error .malformedProgram
    | .localBase lid =>
      match readPtrFromLocal st.locals lid with
      | .error k => .error k
      | .ok p =>
        match checkRefDeref st.allocs p layout with
        | .error k => .error k
        | .ok () => .ok (.memBase p)
  | other => stepProjMPlace st base other

def evalPlaceNaiveFullRead (st : MachineState) (pl : Place) : Except UbKind PlaceBase :=
  if pl.localId < st.locals.length then
    runProjs (stepProjNaiveFullRead st) pl.projs (.localBase pl.localId)
  else
    .error .malformedProgram

theorem evalPlaceMPlace_raw_deref_zero_offset_ok (st : MachineState) (lid : Nat)
    (layout : PointeeLayout) (p : PtrVal)
    (hptr : readPtrFromLocal st.locals lid = .ok p) :
    evalPlaceMPlace st { localId := lid, projs := [.deref .rawPtr layout, .field 0] } =
      .ok (.memBase p) := by
  have hlt : lid < st.locals.length := by
    unfold readPtrFromLocal at hptr
    cases hget : listGet st.locals lid with
    | none => rw [hget] at hptr; cases hptr
    | some _ => exact listGet_length_lt hget
  unfold evalPlaceMPlace
  simp only [hlt, ↓reduceIte, runProjs_nil, runProjs_cons, stepProjMPlace, hptr,
    offsetPtrInbounds, checkAndDerefPtr, shiftPtr]
  rfl

theorem evalPlaceMPlace_null_nonzero_field_ub (st : MachineState) (lid : Nat)
    (layout : PointeeLayout) (off : Nat) (hoff : (off == 0) = false)
    (hptr : readPtrFromLocal st.locals lid = .ok .null) :
    evalPlaceMPlace st { localId := lid, projs := [.deref .rawPtr layout, .field off] } =
      .error .nullInboundsOrDeref := by
  have hlt : lid < st.locals.length := by
    unfold readPtrFromLocal at hptr
    cases hget : listGet st.locals lid with
    | none => rw [hget] at hptr; cases hptr
    | some _ => exact listGet_length_lt hget
  unfold evalPlaceMPlace
  simp only [hlt, ↓reduceIte, runProjs_nil, runProjs_cons, stepProjMPlace, hptr,
    offsetPtrInbounds, checkAndDerefPtr, hoff]
  rfl

theorem evalPlaceMPlace_safeRef_null_ub (st : MachineState) (lid : Nat)
    (layout : PointeeLayout) (rest : List ProjElem)
    (hptr : readPtrFromLocal st.locals lid = .ok .null) :
    evalPlaceMPlace st { localId := lid, projs := .deref .safeRef layout :: rest } =
      .error .nullInboundsOrDeref := by
  have hlt : lid < st.locals.length := by
    unfold readPtrFromLocal at hptr
    cases hget : listGet st.locals lid with
    | none => rw [hget] at hptr; cases hptr
    | some _ => exact listGet_length_lt hget
  unfold evalPlaceMPlace
  simp only [hlt, ↓reduceIte, runProjs_cons, stepProjMPlace, hptr, checkRefDeref]

/-! ## Section 3: MIR Syntax, Small-Step Operational Semantics, and Lowering Pipeline -/

inductive Stmt where
  | assignConst (dst : Nat) (v : Val)
  | assignCopy (dst : Nat) (src : Nat)
  | assignDerefRead (dst : Nat) (ptrLocal : Nat) (kind : PtrKind) (layout : PointeeLayout)
  | storageLive (lid : Nat)
  | storageDead (lid : Nat)
  | placeMention (pl : Place)
  | nop
  deriving Repr, DecidableEq

inductive Term where
  | goto (target : Nat)
  | switchInt (discrLocal : Nat) (branches : List (Nat × Nat)) (otherwise : Nat)
  | ret (retLocal : Nat)
  | unreachable
  deriving Repr, DecidableEq

structure BasicBlock where
  stmts : List Stmt
  term : Term
  deriving Repr, DecidableEq

structure Body where
  blocks : List BasicBlock
  deriving Repr, DecidableEq

inductive ExecOutcome where
  | returned (v : Val)
  | ub (k : UbKind)
  | stuck
  | outOfFuel
  deriving Repr, DecidableEq

def evalOperandLocal (locals : List LocalSlot) (lid : Nat) : Except UbKind Val :=
  match listGet locals lid with
  | none => .error .malformedProgram
  | some .dead => .error .deadLocalAccess
  | some .liveUninit => .error .uninitRead
  | some (.liveInit (.invalidBoolByte _)) => .error .invalidBoolRead
  | some (.liveInit v) => .ok v

def writeLocalSlot (locals : List LocalSlot) (dst : Nat) (v : Val) :
    Except UbKind (List LocalSlot) :=
  match listGet locals dst with
  | none => .error .malformedProgram
  | some .dead => .error .deadLocalAccess
  | some _ =>
    match listSet locals dst (.liveInit v) with
    | none => .error .malformedProgram
    | some locals' => .ok locals'

def evalStmt (st : MachineState) : Stmt → Except UbKind MachineState
  | .nop => .ok st
  | .storageLive lid =>
    match listSet st.locals lid .liveUninit with
    | none => .error .malformedProgram
    | some locals' => .ok { st with locals := locals' }
  | .storageDead lid =>
    if lid == 0 then
      .error .malformedProgram
    else
      match listSet st.locals lid .dead with
      | none => .error .malformedProgram
      | some locals' => .ok { st with locals := locals' }
  | .assignConst dst v =>
    match writeLocalSlot st.locals dst v with
    | .error k => .error k
    | .ok locals' => .ok { st with locals := locals' }
  | .assignCopy dst src =>
    match evalOperandLocal st.locals src with
    | .error k => .error k
    | .ok v =>
      match writeLocalSlot st.locals dst v with
      | .error k => .error k
      | .ok locals' => .ok { st with locals := locals' }
  | .assignDerefRead dst ptrLocal kind layout =>
    match evalPlaceMPlace st { localId := ptrLocal, projs := [.deref kind layout] } with
    | .error k => .error k
    | .ok (.localBase _) => .error .malformedProgram
    | .ok (.memBase p) =>
      match checkRefDeref st.allocs p layout with
      | .error k => .error k
      | .ok () =>
        match p with
        | .allocPtr aid _ =>
          match listGet st.allocs aid with
          | none => .error .danglingPtrAccess
          | some info =>
            match info.storedVal with
            | none => .error .uninitRead
            | some loaded =>
              match writeLocalSlot st.locals dst loaded with
              | .error k => .error k
              | .ok locals' => .ok { st with locals := locals' }
        | _ => .error .danglingPtrAccess
  | .placeMention pl =>
    match evalPlaceMPlace st pl with
    | .error k => .error k
    | .ok _ => .ok st

def valToSwitchNat : Val → Except UbKind Nat
  | .intVal n => .ok n
  | .boolVal false => .ok 0
  | .boolVal true => .ok 1
  | .invalidBoolByte _ => .error .invalidBoolRead
  | _ => .error .malformedProgram

def lookupSwitchTarget (discr : Nat) (otherwise : Nat) (branches : List (Nat × Nat)) : Nat :=
  branches.foldr (fun pair ih => if discr == pair.1 then pair.2 else ih) otherwise

theorem lookupSwitchTarget_nil (discr otherwise : Nat) :
    lookupSwitchTarget discr otherwise [] = otherwise := rfl

theorem lookupSwitchTarget_cons (discr otherwise cv tgt : Nat) (rest : List (Nat × Nat)) :
    lookupSwitchTarget discr otherwise ((cv, tgt) :: rest) =
      if discr == cv then tgt else lookupSwitchTarget discr otherwise rest := rfl

inductive StepOut where
  | next (st : MachineState) (bb : Nat) (stmtIdx : Nat)
  | done (out : ExecOutcome)
  deriving Repr, DecidableEq

/-- `stepBody` executes one MIR statement or terminator transition, matching
`InterpCx::step` (`compiler/rustc_const_eval/src/interpret/step.rs`). Notice
that `.switchInt` calls `evalOperandLocal st.locals discrLocal` before matching
`branches`, so an uninitialized or invalid-bool discriminant causes `.ub` even if
all targets jump to the same block. -/
def stepBody (body : Body) (st : MachineState) (bb : Nat) (stmtIdx : Nat) : StepOut :=
  match listGet body.blocks bb with
  | none => .done .stuck
  | some blk =>
    match listGet blk.stmts stmtIdx with
    | some stmt =>
      match evalStmt st stmt with
      | .error k => .done (.ub k)
      | .ok st' => .next st' bb (stmtIdx + 1)
    | none =>
      match blk.term with
      | .goto target => .next st target 0
      | .ret retLocal =>
        match evalOperandLocal st.locals retLocal with
        | .error k => .done (.ub k)
        | .ok v => .done (.returned v)
      | .unreachable => .done (.ub .reachedUnreachable)
      | .switchInt discrLocal branches otherwise =>
        match evalOperandLocal st.locals discrLocal with
        | .error k => .done (.ub k)
        | .ok v =>
          match valToSwitchNat v with
          | .error k => .done (.ub k)
          | .ok discrNat => .next st (lookupSwitchTarget discrNat otherwise branches) 0

def runSteps (body : Body) (st : MachineState) (bb : Nat) (stmtIdx : Nat) (fuel : Nat) :
    ExecOutcome :=
  (Nat.rec (motive := fun _ => MachineState → Nat → Nat → ExecOutcome)
    (fun _ _ _ => .outOfFuel)
    (fun _ ih s curBb curIdx =>
      match stepBody body s curBb curIdx with
      | .done out => out
      | .next s' bb' idx' => ih s' bb' idx')
    fuel) st bb stmtIdx

def evalBody (body : Body) (st : MachineState) (fuel : Nat) : ExecOutcome :=
  runSteps body st 0 0 fuel

theorem runSteps_zero (body : Body) (st : MachineState) (bb stmtIdx : Nat) :
    runSteps body st bb stmtIdx 0 = .outOfFuel := rfl

theorem runSteps_succ (body : Body) (st : MachineState) (bb stmtIdx fuel : Nat) :
    runSteps body st bb stmtIdx (fuel + 1) =
      match stepBody body st bb stmtIdx with
      | .done out => out
      | .next s' bb' idx' => runSteps body s' bb' idx' fuel := rfl

theorem stepBody_none {body : Body} {st : MachineState} {bb stmtIdx : Nat}
    (hbb : listGet body.blocks bb = none) :
    stepBody body st bb stmtIdx = .done .stuck := by
  simp only [stepBody, hbb]

theorem stepBody_stmt {body : Body} {st : MachineState} {bb stmtIdx : Nat}
    {blk : BasicBlock} {stmt : Stmt}
    (hbb : listGet body.blocks bb = some blk)
    (hst : listGet blk.stmts stmtIdx = some stmt) :
    stepBody body st bb stmtIdx =
      match evalStmt st stmt with
      | .error k => .done (.ub k)
      | .ok st' => .next st' bb (stmtIdx + 1) := by
  simp only [stepBody, hbb, hst]

theorem stepBody_term {body : Body} {st : MachineState} {bb stmtIdx : Nat}
    {blk : BasicBlock}
    (hbb : listGet body.blocks bb = some blk)
    (hst : listGet blk.stmts stmtIdx = none) :
    stepBody body st bb stmtIdx =
      match blk.term with
      | .goto target => .next st target 0
      | .ret retLocal =>
        match evalOperandLocal st.locals retLocal with
        | .error k => .done (.ub k)
        | .ok v => .done (.returned v)
      | .unreachable => .done (.ub .reachedUnreachable)
      | .switchInt discrLocal branches otherwise =>
        match evalOperandLocal st.locals discrLocal with
        | .error k => .done (.ub k)
        | .ok v =>
          match valToSwitchNat v with
          | .error k => .done (.ub k)
          | .ok discrNat => .next st (lookupSwitchTarget discrNat otherwise branches) 0 := by
  simp only [stepBody, hbb, hst]

/-! ### Lowering Passes: `RemovePlaceMention` and `SimplifyCfg::PreOptimizations` -/

def allTargetsEqual (otherwise : Nat) (branches : List (Nat × Nat)) : Bool :=
  branches.foldr (fun pair ih => (pair.2 == otherwise) && ih) true

theorem allTargetsEqual_nil (otherwise : Nat) :
    allTargetsEqual otherwise [] = true := rfl

theorem allTargetsEqual_cons (otherwise cv tgt : Nat) (rest : List (Nat × Nat)) :
    allTargetsEqual otherwise ((cv, tgt) :: rest) =
      ((tgt == otherwise) && allTargetsEqual otherwise rest) := rfl

theorem lookupSwitchTarget_of_allTargetsEqual {discr otherwise : Nat}
    {branches : List (Nat × Nat)} (heq : allTargetsEqual otherwise branches = true) :
    lookupSwitchTarget discr otherwise branches = otherwise := by
  induction branches with
  | nil => rfl
  | cons pair rest ih =>
    cases pair with
    | mk cv tgt =>
      simp only [allTargetsEqual_cons, Bool.and_eq_true, beq_iff_eq] at heq
      simp only [lookupSwitchTarget_cons]
      cases hcmp : (discr == cv) with
      | true => exact heq.1
      | false => exact ih heq.2

def isRetainedStmt (preserveUb : Bool) : Stmt → Bool
  | .nop => false
  | .placeMention _ => preserveUb
  | _ => true

def filterStmts (p : Stmt → Bool) (xs : List Stmt) : List Stmt :=
  xs.foldr (fun s ih => if p s then s :: ih else ih) []

theorem filterStmts_nil (p : Stmt → Bool) : filterStmts p [] = [] := rfl

theorem filterStmts_cons (p : Stmt → Bool) (s : Stmt) (rest : List Stmt) :
    filterStmts p (s :: rest) =
      if p s then s :: filterStmts p rest else filterStmts p rest := rfl

def removePlaceMentionBlock (preserveUb : Bool) (blk : BasicBlock) : BasicBlock :=
  if preserveUb then
    blk
  else
    { blk with stmts := filterStmts (isRetainedStmt false) blk.stmts }

/-- Models `RemovePlaceMention` (`compiler/rustc_mir_transform/src/remove_place_mention.rs`):
optional pass enabled iff `!ctx.opts.unstable_opts.mir_preserve_ub`; when enabled it
retains all statements except `PlaceMention` and `Nop`. -/
def passRemovePlaceMention (mirPreserveUb : Bool) (body : Body) : Body :=
  if mirPreserveUb then
    body
  else
    { blocks := body.blocks.map (removePlaceMentionBlock false) }

def simplifyEqualBranchTerm (preserveSwitchReads : Bool) : Term → Term
  | .switchInt discr branches otherwise =>
    if !preserveSwitchReads && allTargetsEqual otherwise branches then
      .goto otherwise
    else
      .switchInt discr branches otherwise
  | other => other

def stmtNotNop : Stmt → Bool
  | .nop => false
  | _ => true

def simplifyCfgPreOptBlock (preserveSwitchReads : Bool) (blk : BasicBlock) : BasicBlock :=
  { stmts := filterStmts stmtNotNop blk.stmts
    term := simplifyEqualBranchTerm preserveSwitchReads blk.term }

/-- Models `SimplifyCfg::PreOptimizations` (`compiler/rustc_mir_transform/src/simplify.rs`):
strips `Nop` unconditionally (`strip_nops`) and collapses equal-target `SwitchInt`
terminators to `Goto` unless `preserve_switch_reads` holds (which at `MirPhase::Runtime(_)`
equals `mir_preserve_ub`). -/
def passSimplifyCfgPreOpt (mirPreserveUb : Bool) (body : Body) : Body :=
  { blocks := body.blocks.map (simplifyCfgPreOptBlock mirPreserveUb) }

/-- Full `Runtime(Initial) -> Runtime(PostCleanup)` lowering pipeline for cleanup
passes controlled by `-Zmir-preserve-ub`. -/
def toRuntimePostCleanup (mirPreserveUb : Bool) (body : Body) : Body :=
  passSimplifyCfgPreOpt mirPreserveUb (passRemovePlaceMention mirPreserveUb body)

/-- `Derefer` + `EraseDerefTemps` pre-runtime lowering for a chained dereference
`(*(*pp).0)` or `(*(*pp)).1`: `Derefer` (`deref_separator.rs`, `PassPolicy::Required`)
hoists the inner dereference load into a temporary `_tmp = copy (*pp)` prior to
`RemovePlaceMention`, so the inner pointer load survives even when `mir_preserve_ub = false`,
while the outer `PlaceMention(((*_tmp).1))` is still erased unless `mir_preserve_ub = true`. -/
def lowerChainedPlaceMentionDerefer (tmpLocal : Nat) (ppLocal : Nat)
    (innerLayout outerLayout : PointeeLayout) (outerOffset : Nat) : List Stmt :=
  [ .storageLive tmpLocal,
    .assignDerefRead tmpLocal ppLocal .rawPtr innerLayout,
    .placeMention { localId := tmpLocal, projs := [.deref .rawPtr outerLayout, .field outerOffset] } ]

/-! ## Section 4: Exact Equivalence of `Runtime(Initial)` and `Runtime(PostCleanup, true)` -/

def blockHasNoNops (blk : BasicBlock) : Bool :=
  listAll stmtNotNop blk.stmts

def bodyHasNoNops (body : Body) : Bool :=
  listAll blockHasNoNops body.blocks

theorem filterStmts_stmtNotNop_eq {xs : List Stmt} (h : listAll stmtNotNop xs = true) :
    filterStmts stmtNotNop xs = xs := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    simp only [listAll_cons, Bool.and_eq_true] at h
    simp only [filterStmts_cons, h.1, ↓reduceIte]
    exact congrArg (s :: ·) (ih h.2)

theorem simplifyEqualBranchTerm_true_eq (t : Term) :
    simplifyEqualBranchTerm true t = t := by
  cases t <;> rfl

theorem simplifyCfgPreOptBlock_true_eq {blk : BasicBlock} (h : blockHasNoNops blk = true) :
    simplifyCfgPreOptBlock true blk = blk := by
  unfold simplifyCfgPreOptBlock
  have hs := filterStmts_stmtNotNop_eq h
  have ht := simplifyEqualBranchTerm_true_eq blk.term
  rw [hs, ht]

theorem listMap_id_of_all {α : Type} {f : α → α} {p : α → Bool} {xs : List α}
    (hall : listAll p xs = true) (hf : ∀ x, p x = true → f x = x) :
    xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [listAll_cons, Bool.and_eq_true] at hall
    simp only [List.map_cons, hf x hall.1, ih hall.2]

theorem toRuntimePostCleanup_true_eq_of_noNops {body : Body}
    (h : bodyHasNoNops body = true) :
    toRuntimePostCleanup true body = body := by
  unfold toRuntimePostCleanup passRemovePlaceMention passSimplifyCfgPreOpt
  simp only [↓reduceIte]
  have hmap : body.blocks.map (simplifyCfgPreOptBlock true) = body.blocks :=
    listMap_id_of_all h (fun blk hb => simplifyCfgPreOptBlock_true_eq hb)
  rw [hmap]

/-- Theorem 1A (Exact Structural Identity on `Nop`-Free Bodies):
`toRuntimePostCleanup true` is the identity on every `Nop`-free `Runtime(Initial)` body,
so `evalBody` agrees identically for every state and every fuel bound. -/
theorem evalBody_runtimePostCleanup_preserveUb_true_exact_noNops
    {body : Body} (h : bodyHasNoNops body = true) (st : MachineState) (fuel : Nat) :
    evalBody (toRuntimePostCleanup true body) st fuel = evalBody body st fuel := by
  rw [toRuntimePostCleanup_true_eq_of_noNops h]

def countRetainedBefore (p : Stmt → Bool) (xs : List Stmt) (idx : Nat) : Nat :=
  (xs.foldr
    (fun s ih k =>
      match k with
      | 0 => 0
      | k' + 1 => (if p s then 1 else 0) + ih k')
    (fun _ => 0)) idx

theorem countRetainedBefore_nil (p : Stmt → Bool) (idx : Nat) :
    countRetainedBefore p [] idx = 0 := rfl

theorem countRetainedBefore_cons_zero (p : Stmt → Bool) (s : Stmt) (rest : List Stmt) :
    countRetainedBefore p (s :: rest) 0 = 0 := rfl

theorem countRetainedBefore_cons_succ (p : Stmt → Bool) (s : Stmt) (rest : List Stmt) (k : Nat) :
    countRetainedBefore p (s :: rest) (k + 1) =
      (if p s then 1 else 0) + countRetainedBefore p rest k := rfl

theorem filterStmts_index_preserved {p : Stmt → Bool} {xs : List Stmt} {idx : Nat} {s : Stmt}
    (hget : listGet xs idx = some s) (hp : p s = true) :
    listGet (filterStmts p xs) (countRetainedBefore p xs idx) = some s := by
  induction xs generalizing idx with
  | nil => rw [listGet_nil] at hget; cases hget
  | cons hd tl ih =>
    cases idx with
    | zero =>
      rw [listGet_cons_zero] at hget
      cases hget
      simp only [countRetainedBefore_cons_zero, filterStmts_cons, hp, ↓reduceIte,
        listGet_cons_zero]
    | succ k =>
      rw [listGet_cons_succ] at hget
      simp only [countRetainedBefore_cons_succ, filterStmts_cons]
      cases hhd : p hd with
      | true =>
        simp only [↓reduceIte]
        rw [Nat.add_comm]
        exact ih hget
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih hget

theorem filterStmts_index_terminator {p : Stmt → Bool} {xs : List Stmt} {idx : Nat}
    (hget : listGet xs idx = none) :
    listGet (filterStmts p xs) (countRetainedBefore p xs idx) = none := by
  induction xs generalizing idx with
  | nil => simp only [filterStmts_nil, listGet_nil]
  | cons hd tl ih =>
    cases idx with
    | zero => rw [listGet_cons_zero] at hget; cases hget
    | succ k =>
      rw [listGet_cons_succ] at hget
      simp only [countRetainedBefore_cons_succ, filterStmts_cons]
      cases hhd : p hd with
      | true =>
        simp only [↓reduceIte]
        rw [Nat.add_comm]
        exact ih hget
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih hget

theorem countRetainedBefore_zero (p : Stmt → Bool) (xs : List Stmt) :
    countRetainedBefore p xs 0 = 0 := by
  cases xs <;> rfl

theorem countRetainedBefore_succ_skip {p : Stmt → Bool} {xs : List Stmt} {idx : Nat} {s : Stmt}
    (hget : listGet xs idx = some s) (hnot : p s = false) :
    countRetainedBefore p xs (idx + 1) = countRetainedBefore p xs idx := by
  induction xs generalizing idx with
  | nil => rw [listGet_nil] at hget; cases hget
  | cons hd tl ih =>
    cases idx with
    | zero =>
      rw [listGet_cons_zero] at hget
      cases hget
      simp only [countRetainedBefore_cons_succ, countRetainedBefore_cons_zero, hnot,
        Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact countRetainedBefore_zero p tl
    | succ k =>
      rw [listGet_cons_succ] at hget
      simp only [countRetainedBefore_cons_succ]
      rw [ih hget]

theorem countRetainedBefore_succ_keep {p : Stmt → Bool} {xs : List Stmt} {idx : Nat} {s : Stmt}
    (hget : listGet xs idx = some s) (hp : p s = true) :
    countRetainedBefore p xs (idx + 1) = countRetainedBefore p xs idx + 1 := by
  induction xs generalizing idx with
  | nil => rw [listGet_nil] at hget; cases hget
  | cons hd tl ih =>
    cases idx with
    | zero =>
      rw [listGet_cons_zero] at hget
      cases hget
      simp only [countRetainedBefore_cons_succ, hp, ↓reduceIte, countRetainedBefore_zero]
    | succ k =>
      rw [listGet_cons_succ] at hget
      simp only [countRetainedBefore_cons_succ]
      rw [ih hget, Nat.add_assoc]

/-- General Simulation Theorem for `Stmt`-Filtering Transforms:
If `body'` maps each block `blk` to `{ stmts := filterStmts keepStmt blk.stmts, term := tFn blk.term }`,
and whenever a statement in `blk` fails `keepStmt`, `evalStmt` is the identity (`= .ok st`),
and `tFn` preserves terminator behavior (`ValidTermTransform`), then every terminating or
UB-faulting execution of `body` produces the **exact same** `ExecOutcome` in `body'`. -/
def isNoopOnState (s : Stmt) : Prop := ∀ st : MachineState, evalStmt st s = .ok st

def ValidTermTransform (tFn : Term → Term) : Prop :=
  ∀ (st : MachineState) (t : Term),
    match t with
    | .goto target => tFn t = .goto target
    | .ret retLocal => tFn t = .ret retLocal
    | .unreachable => tFn t = .unreachable
    | .switchInt discrLocal branches otherwise =>
      match evalOperandLocal st.locals discrLocal with
      | .error _ => tFn t = .switchInt discrLocal branches otherwise
      | .ok v =>
        match valToSwitchNat v with
        | .error _ => tFn t = .switchInt discrLocal branches otherwise
        | .ok discrNat =>
          (tFn t = .switchInt discrLocal branches otherwise) ∨
          (tFn t = .goto (lookupSwitchTarget discrNat otherwise branches))

def transformBody (keepStmt : Stmt → Bool) (tFn : Term → Term) (body : Body) : Body :=
  { blocks := body.blocks.map (fun blk =>
      { stmts := filterStmts keepStmt blk.stmts, term := tFn blk.term }) }

def NotOutOfFuel : ExecOutcome → Prop
  | .outOfFuel => False
  | _ => True

theorem countRetainedBefore_at_zero (keepStmt : Stmt → Bool) (body : Body) (tgt : Nat) :
    (match listGet body.blocks tgt with
     | some b => countRetainedBefore keepStmt b.stmts 0
     | none => 0) = 0 := by
  cases listGet body.blocks tgt with
  | none => rfl
  | some b => exact countRetainedBefore_zero keepStmt b.stmts

theorem runSteps_transform_forward_inv
    {keepStmt : Stmt → Bool} {tFn : Term → Term} {body : Body}
    {Inv : MachineState → Nat → Nat → Nat → Prop}
    (hStmtSkip : ∀ f s bb idx blk stmt,
      listGet body.blocks bb = some blk →
      listGet blk.stmts idx = some stmt →
      keepStmt stmt = false →
      Inv s bb idx (f + 1) →
      evalStmt s stmt = .ok s ∧ Inv s bb (idx + 1) f)
    (hStmtKeep : ∀ f s bb idx blk stmt s',
      listGet body.blocks bb = some blk →
      listGet blk.stmts idx = some stmt →
      keepStmt stmt = true →
      Inv s bb idx (f + 1) →
      evalStmt s stmt = .ok s' →
      Inv s' bb (idx + 1) f)
    (hGoto : ∀ f s bb idx blk tgt,
      listGet body.blocks bb = some blk →
      listGet blk.stmts idx = none →
      blk.term = .goto tgt →
      Inv s bb idx (f + 1) →
      tFn (.goto tgt) = .goto tgt ∧ Inv s tgt 0 f)
    (hRet : ∀ retLocal, tFn (.ret retLocal) = .ret retLocal)
    (hUnreach : tFn .unreachable = .unreachable)
    (hSwitch : ∀ f s bb idx blk discr branches otherwise,
      listGet body.blocks bb = some blk →
      listGet blk.stmts idx = none →
      blk.term = .switchInt discr branches otherwise →
      Inv s bb idx (f + 1) →
      match evalOperandLocal s.locals discr with
      | .error _ => tFn (.switchInt discr branches otherwise) = .switchInt discr branches otherwise
      | .ok v =>
        match valToSwitchNat v with
        | .error _ => tFn (.switchInt discr branches otherwise) = .switchInt discr branches otherwise
        | .ok discrNat =>
          (tFn (.switchInt discr branches otherwise) = .switchInt discr branches otherwise ∨
           tFn (.switchInt discr branches otherwise) =
             .goto (lookupSwitchTarget discrNat otherwise branches)) ∧
          Inv s (lookupSwitchTarget discrNat otherwise branches) 0 f)
    (fuel : Nat) (st : MachineState) (bb stmtIdx : Nat)
    (hInv : Inv st bb stmtIdx fuel)
    (hNoOOM : NotOutOfFuel (runSteps body st bb stmtIdx fuel)) :
    ∃ fuel', runSteps (transformBody keepStmt tFn body) st bb
        (match listGet body.blocks bb with
         | some blk => countRetainedBefore keepStmt blk.stmts stmtIdx
         | none => 0)
        fuel' =
      runSteps body st bb stmtIdx fuel := by
  induction fuel generalizing st bb stmtIdx with
  | zero =>
    rw [runSteps_zero] at hNoOOM
    exact False.elim hNoOOM
  | succ f ih =>
    rw [runSteps_succ] at hNoOOM ⊢
    cases hbb : listGet body.blocks bb with
    | none =>
      rw [stepBody_none hbb]
      have hbb' : listGet (transformBody keepStmt tFn body).blocks bb = none := by
        unfold transformBody; rw [listGet_map, hbb]; rfl
      exists 1
      rw [runSteps_succ, stepBody_none hbb']
    | some blk =>
      have hbb' : listGet (transformBody keepStmt tFn body).blocks bb =
          some { stmts := filterStmts keepStmt blk.stmts, term := tFn blk.term } := by
        unfold transformBody; rw [listGet_map, hbb]; rfl
      dsimp only at hNoOOM ⊢
      cases hst : listGet blk.stmts stmtIdx with
      | some s =>
        rw [stepBody_stmt hbb hst] at hNoOOM ⊢
        cases hkeep : keepStmt s with
        | false =>
          obtain ⟨hsnoop, hInv'⟩ := hStmtSkip f st bb stmtIdx blk s hbb hst hkeep hInv
          rw [hsnoop] at hNoOOM ⊢
          dsimp only at hNoOOM ⊢
          have ⟨fuel', hrec⟩ := ih st bb (stmtIdx + 1) hInv' hNoOOM
          rw [hbb] at hrec
          dsimp only at hrec
          rw [countRetainedBefore_succ_skip hst hkeep] at hrec
          exact ⟨fuel', hrec⟩
        | true =>
          have hst' := filterStmts_index_preserved hst hkeep
          cases hev : evalStmt st s with
          | error k =>
            exists 1
            rw [runSteps_succ, stepBody_stmt hbb' hst', hev]
          | ok st' =>
            rw [hev] at hNoOOM
            dsimp only at hNoOOM ⊢
            have hInv' := hStmtKeep f st bb stmtIdx blk s st' hbb hst hkeep hInv hev
            have ⟨fuel', hrec⟩ := ih st' bb (stmtIdx + 1) hInv' hNoOOM
            rw [hbb] at hrec
            dsimp only at hrec
            rw [countRetainedBefore_succ_keep hst hkeep] at hrec
            exists (fuel' + 1)
            rw [runSteps_succ, stepBody_stmt hbb' hst', hev]
            exact hrec
      | none =>
        rw [stepBody_term hbb hst] at hNoOOM ⊢
        have hst' := filterStmts_index_terminator (p := keepStmt) hst
        cases hterm : blk.term with
        | goto target =>
          rw [hterm] at hNoOOM
          dsimp only at hNoOOM ⊢
          obtain ⟨htf, hInv'⟩ := hGoto f st bb stmtIdx blk target hbb hst hterm hInv
          have ⟨fuel', hrec⟩ := ih st target 0 hInv' hNoOOM
          rw [countRetainedBefore_at_zero] at hrec
          exists (fuel' + 1)
          rw [runSteps_succ, stepBody_term hbb' hst']
          dsimp only
          rw [hterm, htf]
          exact hrec
        | ret retLocal =>
          exists 1
          rw [runSteps_succ, stepBody_term hbb' hst']
          dsimp only
          rw [hterm, hRet]
          dsimp only
          cases evalOperandLocal st.locals retLocal <;> rfl
        | unreachable =>
          exists 1
          rw [runSteps_succ, stepBody_term hbb' hst']
          dsimp only
          rw [hterm, hUnreach]
        | switchInt discrLocal branches otherwise =>
          rw [hterm] at hNoOOM
          have hsw := hSwitch f st bb stmtIdx blk discrLocal branches otherwise hbb hst hterm hInv
          dsimp only at hNoOOM hsw ⊢
          cases hop : evalOperandLocal st.locals discrLocal with
          | error k =>
            rw [hop] at hsw
            exists 1
            rw [runSteps_succ, stepBody_term hbb' hst']
            dsimp only
            rw [hterm, hsw]
            dsimp only
            rw [hop]
          | ok v =>
            rw [hop] at hsw hNoOOM
            dsimp only at hsw hNoOOM ⊢
            cases hnat : valToSwitchNat v with
            | error k =>
              rw [hnat] at hsw
              exists 1
              rw [runSteps_succ, stepBody_term hbb' hst']
              dsimp only
              rw [hterm, hsw]
              dsimp only
              simp only [hop, hnat]
            | ok discrNat =>
              rw [hnat] at hsw hNoOOM
              dsimp only at hsw hNoOOM ⊢
              obtain ⟨htfOpt, hInv'⟩ := hsw
              have ⟨fuel', hrec⟩ := ih st (lookupSwitchTarget discrNat otherwise branches) 0 hInv' hNoOOM
              rw [countRetainedBefore_at_zero] at hrec
              exists (fuel' + 1)
              rw [runSteps_succ, stepBody_term hbb' hst']
              dsimp only
              rw [hterm]
              cases htfOpt with
              | inl heq =>
                rw [heq]
                dsimp only
                simp only [hop, hnat]
                exact hrec
              | inr heq =>
                rw [heq]
                exact hrec

theorem runSteps_transform_forward
    {keepStmt : Stmt → Bool} {tFn : Term → Term} {body : Body}
    (hNoop : ∀ s, keepStmt s = false → isNoopOnState s)
    (hTerm : ValidTermTransform tFn)
    (fuel : Nat) (st : MachineState) (bb stmtIdx : Nat)
    (hNoOOM : NotOutOfFuel (runSteps body st bb stmtIdx fuel)) :
    ∃ fuel', runSteps (transformBody keepStmt tFn body) st bb
        (match listGet body.blocks bb with
         | some blk => countRetainedBefore keepStmt blk.stmts stmtIdx
         | none => 0)
        fuel' =
      runSteps body st bb stmtIdx fuel := by
  refine runSteps_transform_forward_inv
    (Inv := fun _ _ _ _ => True)
    (fun _ s _ _ _ stmt _ _ hkeep _ => ⟨hNoop stmt hkeep s, trivial⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ s _ _ _ tgt _ _ _ _ => ⟨hTerm s (.goto tgt), trivial⟩)
    (fun r => hTerm st (.ret r))
    (hTerm st .unreachable)
    (fun _ s _ _ _ d b o _ _ _ _ => by
      have hspec := hTerm s (.switchInt d b o)
      dsimp only at hspec
      cases hop : evalOperandLocal s.locals d with
      | error _ => rw [hop] at hspec; exact hspec
      | ok v =>
        rw [hop] at hspec
        dsimp only at hspec ⊢
        cases hnat : valToSwitchNat v with
        | error _ => rw [hnat] at hspec; exact hspec
        | ok dn =>
          rw [hnat] at hspec
          dsimp only at hspec ⊢
          exact ⟨hspec, trivial⟩)
    fuel st bb stmtIdx trivial hNoOOM

theorem nop_isNoop : isNoopOnState .nop := fun _ => rfl

theorem simplifyEqualBranchTerm_true_valid : ValidTermTransform (simplifyEqualBranchTerm true) := by
  unfold ValidTermTransform
  intro st t
  cases t with
  | goto _ => exact simplifyEqualBranchTerm_true_eq _
  | ret _ => exact simplifyEqualBranchTerm_true_eq _
  | unreachable => exact simplifyEqualBranchTerm_true_eq _
  | switchInt discrLocal branches otherwise =>
    dsimp only
    cases evalOperandLocal st.locals discrLocal with
    | error _ => exact simplifyEqualBranchTerm_true_eq _
    | ok v =>
      dsimp only
      cases valToSwitchNat v with
      | error _ => exact simplifyEqualBranchTerm_true_eq _
      | ok _ => exact Or.inl (simplifyEqualBranchTerm_true_eq _)

theorem toRuntimePostCleanup_true_is_transformBody (body : Body) :
    toRuntimePostCleanup true body =
      transformBody stmtNotNop (simplifyEqualBranchTerm true) body := by
  rfl

/-- Theorem 1B (Exact Semantics Preservation for `toRuntimePostCleanup true` with Arbitrary `Nop`s):
Every terminating or UB-faulting execution of a `Runtime(Initial)` body produces the exact same
`ExecOutcome` under `toRuntimePostCleanup true` (`-Zmir-preserve-ub=yes`), even when `Nop`
statements are compressed away by `SimplifyCfg::PreOptimizations` (`strip_nops`). -/
theorem evalBody_runtimePostCleanup_preserveUb_true_complete
    (body : Body) (st : MachineState) (fuel : Nat)
    (hNoOOM : NotOutOfFuel (evalBody body st fuel)) :
    ∃ fuel', evalBody (toRuntimePostCleanup true body) st fuel' = evalBody body st fuel := by
  rw [toRuntimePostCleanup_true_is_transformBody]
  have hf := runSteps_transform_forward
    (keepStmt := stmtNotNop) (tFn := simplifyEqualBranchTerm true) (body := body)
    (fun s hs => by cases s with | nop => exact nop_isNoop | _ => cases hs)
    simplifyEqualBranchTerm_true_valid
    fuel st 0 0 hNoOOM
  rw [countRetainedBefore_at_zero] at hf
  exact hf

/-! ## Section 5: Conditional Soundness Under Certified PlaceMention & Switch Discriminant Safety -/

/-- `isLocalOnlyPlace numLocals pl` checks that `pl` refers to an in-bounds frame
local and performs no `.deref` or `.index` projections (so `local_to_place` +
field projections never dereference memory or perform inbounds pointer arithmetic). -/
def isLocalOnlyProj : ProjElem → Bool
  | .deref _ _ => false
  | .field _ => true
  | .index _ _ _ => false

def isLocalOnlyPlace (numLocals : Nat) (pl : Place) : Bool :=
  (pl.localId < numLocals) && listAll isLocalOnlyProj pl.projs

/-- `safeToErasePlaceMention st pl` is a decidable state+place predicate certifying
that `StatementKind::PlaceMention(pl)` evaluates cleanly to `.ok _` without UB:
either `pl` is local-only (`isLocalOnlyPlace`), OR `pl` is an initialized raw-pointer
zero-offset place (`*raw_ptr` or `(*raw_ptr).field_at_offset_0`, where RFC 2582
skips pointer dereferenceability/alignment and `checkAndDerefPtr` short-circuits
at `offsetBytes = 0`). -/
def isSafeRawZeroOffsetProjs : List ProjElem → Bool
  | [.deref .rawPtr _] => true
  | [.deref .rawPtr _, .field 0] => true
  | _ => false

def isInitializedPtrAt (locals : List LocalSlot) (lid : Nat) : Bool :=
  match listGet locals lid with
  | some (.liveInit (.ptrVal _)) => true
  | _ => false

def safeToErasePlaceMention (st : MachineState) (pl : Place) : Bool :=
  isLocalOnlyPlace st.locals.length pl ||
  (isInitializedPtrAt st.locals pl.localId && isSafeRawZeroOffsetProjs pl.projs)

theorem stepProjMPlace_localOnly {st : MachineState} {lid : Nat} {elem : ProjElem}
    (h : isLocalOnlyProj elem = true) :
    stepProjMPlace st (.localBase lid) elem = .ok (.localBase lid) := by
  cases elem with
  | deref _ _ => cases h
  | field _ => rfl
  | index _ _ _ => cases h

theorem runProjs_localOnly {st : MachineState} {lid : Nat} {projs : List ProjElem}
    (h : listAll isLocalOnlyProj projs = true) :
    runProjs (stepProjMPlace st) projs (.localBase lid) = .ok (.localBase lid) := by
  induction projs with
  | nil => rfl
  | cons elem rest ih =>
    simp only [listAll_cons, Bool.and_eq_true] at h
    simp only [runProjs_cons, stepProjMPlace_localOnly h.1]
    exact ih h.2

theorem evalPlaceMPlace_ok_of_safeToErasePlaceMention {st : MachineState} {pl : Place}
    (hsafe : safeToErasePlaceMention st pl = true) :
    ∃ bp, evalPlaceMPlace st pl = .ok bp := by
  unfold safeToErasePlaceMention at hsafe
  simp only [Bool.or_eq_true] at hsafe
  cases hsafe with
  | inl hloc =>
    unfold isLocalOnlyPlace at hloc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hloc
    exists .localBase pl.localId
    unfold evalPlaceMPlace
    simp only [hloc.1, ↓reduceIte]
    exact runProjs_localOnly hloc.2
  | inr hraw =>
    simp only [Bool.and_eq_true] at hraw
    obtain ⟨hinit, hprojs⟩ := hraw
    unfold isInitializedPtrAt at hinit
    cases hget : listGet st.locals pl.localId with
    | none => rw [hget] at hinit; cases hinit
    | some slot =>
      cases slot with
      | dead => rw [hget] at hinit; cases hinit
      | liveUninit => rw [hget] at hinit; cases hinit
      | liveInit v =>
        cases v with
        | ptrVal p =>
          have hlt : pl.localId < st.locals.length := listGet_length_lt hget
          have hread : readPtrFromLocal st.locals pl.localId = .ok p := by
            unfold readPtrFromLocal; rw [hget]
          rcases pl with ⟨lid, projs⟩
          dsimp only at hprojs hlt hread
          cases projs with
          | nil => cases hprojs
          | cons e1 r1 =>
            cases e1 with
            | field _ => cases hprojs
            | index _ _ _ => cases hprojs
            | deref k1 lay1 =>
              cases k1 with
              | safeRef => cases hprojs
              | rawPtr =>
                cases r1 with
                | nil =>
                  exists .memBase p
                  unfold evalPlaceMPlace
                  simp only [hlt, ↓reduceIte, runProjs_nil, runProjs_cons, stepProjMPlace, hread]
                | cons e2 r2 =>
                  cases e2 with
                  | deref _ _ => cases hprojs
                  | index _ _ _ => cases hprojs
                  | field off2 =>
                    cases off2 with
                    | succ _ => cases hprojs
                    | zero =>
                      cases r2 with
                      | cons _ _ => cases hprojs
                      | nil =>
                        exists .memBase p
                        exact evalPlaceMPlace_raw_deref_zero_offset_ok st lid lay1 p hread
        | intVal _ => rw [hget] at hinit; cases hinit
        | boolVal _ => rw [hget] at hinit; cases hinit
        | invalidBoolByte _ => rw [hget] at hinit; cases hinit
        | unitVal => rw [hget] at hinit; cases hinit

/-- State-independent (syntactically safe) place predicate: a local-only place
with `pl.localId < minLocals` never faults in ANY state with `st.locals.length ≥ minLocals`.
When every `PlaceMention(pl)` in `body` satisfies `isLocalOnlyPlace minLocals pl`,
`RemovePlaceMention` is **unconditionally exact** on every state of size ≥ `minLocals`. -/
def allPlaceMentionsLocalOnly (minLocals : Nat) (body : Body) : Bool :=
  listAll (fun blk =>
    listAll (fun s =>
      match s with
      | .placeMention pl => isLocalOnlyPlace minLocals pl
      | _ => true) blk.stmts) body.blocks

theorem isLocalOnlyPlace_mono {n m : Nat} {pl : Place}
    (hle : n ≤ m) (h : isLocalOnlyPlace n pl = true) :
    isLocalOnlyPlace m pl = true := by
  unfold isLocalOnlyPlace at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨Nat.lt_of_lt_of_le h.1 hle, h.2⟩

theorem writeLocalSlot_length {locals locals' : List LocalSlot} {dst : Nat} {v : Val}
    (h : writeLocalSlot locals dst v = .ok locals') :
    locals'.length = locals.length := by
  unfold writeLocalSlot at h
  cases hget : listGet locals dst with
  | none => rw [hget] at h; cases h
  | some slot =>
    rw [hget] at h
    cases slot with
    | dead => cases h
    | liveUninit =>
      dsimp only at h
      cases hset : listSet locals dst (.liveInit v) with
      | none => rw [hset] at h; cases h
      | some l' => rw [hset] at h; cases h; exact listSet_length_eq hset
    | liveInit _ =>
      dsimp only at h
      cases hset : listSet locals dst (.liveInit v) with
      | none => rw [hset] at h; cases h
      | some l' => rw [hset] at h; cases h; exact listSet_length_eq hset

theorem evalStmt_locals_length {st st' : MachineState} {s : Stmt}
    (h : evalStmt st s = .ok st') : st'.locals.length = st.locals.length := by
  cases s with
  | nop => simp only [evalStmt] at h; cases h; rfl
  | storageLive lid =>
    simp only [evalStmt] at h
    cases hset : listSet st.locals lid .liveUninit with
    | none => rw [hset] at h; cases h
    | some l' => rw [hset] at h; cases h; exact listSet_length_eq hset
  | storageDead lid =>
    simp only [evalStmt] at h
    cases hzero : (lid == 0) with
    | true => rw [hzero] at h; cases h
    | false =>
      rw [hzero] at h
      cases hset : listSet st.locals lid .dead with
      | none => rw [hset] at h; cases h
      | some l' => rw [hset] at h; cases h; exact listSet_length_eq hset
  | assignConst dst v =>
    simp only [evalStmt] at h
    cases hw : writeLocalSlot st.locals dst v with
    | error _ => rw [hw] at h; cases h
    | ok l' => rw [hw] at h; cases h; exact writeLocalSlot_length hw
  | assignCopy dst src =>
    simp only [evalStmt] at h
    cases hop : evalOperandLocal st.locals src with
    | error _ => rw [hop] at h; cases h
    | ok v =>
      rw [hop] at h
      dsimp only at h
      cases hw : writeLocalSlot st.locals dst v with
      | error _ => rw [hw] at h; cases h
      | ok l' => rw [hw] at h; cases h; exact writeLocalSlot_length hw
  | assignDerefRead dst ptrLocal kind layout =>
    simp only [evalStmt] at h
    cases hev : evalPlaceMPlace st { localId := ptrLocal, projs := [.deref kind layout] } with
    | error _ => rw [hev] at h; cases h
    | ok bp =>
      rw [hev] at h
      cases bp with
      | localBase _ => cases h
      | memBase p =>
        dsimp only at h
        cases hchk : checkRefDeref st.allocs p layout with
        | error _ => rw [hchk] at h; cases h
        | ok _ =>
          rw [hchk] at h
          dsimp only at h
          cases p with
          | null => cases h
          | danglingAddr _ => cases h
          | allocPtr aid off =>
            dsimp only at h
            cases haid : listGet st.allocs aid with
            | none => rw [haid] at h; cases h
            | some info =>
              rw [haid] at h
              dsimp only at h
              cases hval : info.storedVal with
              | none => rw [hval] at h; cases h
              | some loaded =>
                rw [hval] at h
                dsimp only at h
                cases hw : writeLocalSlot st.locals dst loaded with
                | error _ => rw [hw] at h; cases h
                | ok l' => rw [hw] at h; cases h; exact writeLocalSlot_length hw
  | placeMention pl =>
    simp only [evalStmt] at h
    cases hev : evalPlaceMPlace st pl with
    | error _ => rw [hev] at h; cases h
    | ok _ => rw [hev] at h; cases h; rfl

theorem filterStmts_stmtNotNop_retainedFalse (xs : List Stmt) :
    filterStmts stmtNotNop (filterStmts (isRetainedStmt false) xs) =
      filterStmts (isRetainedStmt false) xs := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> first
      | exact ih
      | exact congrArg (_ :: ·) ih

theorem passSimplifyCfgPreOpt_passRemovePlaceMention_false_eq
    (preserveSwitchReads : Bool) (body : Body) :
    passSimplifyCfgPreOpt preserveSwitchReads (passRemovePlaceMention false body) =
      transformBody (isRetainedStmt false) (simplifyEqualBranchTerm preserveSwitchReads) body := by
  unfold passRemovePlaceMention passSimplifyCfgPreOpt simplifyCfgPreOptBlock
    removePlaceMentionBlock transformBody
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [List.map_map]
  have hmap : body.blocks.map ((fun (blk : BasicBlock) =>
      ({ stmts := filterStmts stmtNotNop blk.stmts
         term := simplifyEqualBranchTerm preserveSwitchReads blk.term } : BasicBlock)) ∘
      (fun (blk : BasicBlock) =>
        ({ stmts := filterStmts (isRetainedStmt false) blk.stmts, term := blk.term } : BasicBlock))) =
      body.blocks.map (fun (blk : BasicBlock) =>
      ({ stmts := filterStmts (isRetainedStmt false) blk.stmts
         term := simplifyEqualBranchTerm preserveSwitchReads blk.term } : BasicBlock)) := by
    induction body.blocks with
    | nil => rfl
    | cons b bs ih =>
      cases b with
      | mk bStmts bTerm =>
        simp only [List.map_cons, Function.comp_apply, filterStmts_stmtNotNop_retainedFalse, ih]
  exact congrArg Body.mk hmap

theorem evalBody_removePlaceMention_exact_of_localOnly
    {body : Body} {st : MachineState} {minLocals fuel : Nat}
    (hlen : minLocals ≤ st.locals.length)
    (hsafe : allPlaceMentionsLocalOnly minLocals body = true)
    (hNoOOM : NotOutOfFuel (evalBody body st fuel)) :
    ∃ fuel',
      evalBody (passSimplifyCfgPreOpt true (passRemovePlaceMention false body)) st fuel' =
        evalBody body st fuel := by
  rw [passSimplifyCfgPreOpt_passRemovePlaceMention_false_eq]
  have hf := runSteps_transform_forward_inv
    (keepStmt := isRetainedStmt false)
    (tFn := simplifyEqualBranchTerm true)
    (body := body)
    (Inv := fun s _ _ _ => minLocals ≤ s.locals.length)
    (fun _ s _ _ blk stmt hbb hst hkeep hsLen => by
      have hsNoop : evalStmt s stmt = .ok s := by
        cases stmt with
        | nop => rfl
        | placeMention pl =>
          have hblkSafe := listAll_get hsafe hbb
          have hplSafe := listAll_get hblkSafe hst
          have hplCur := isLocalOnlyPlace_mono hsLen hplSafe
          have ⟨bp, hbp⟩ := @evalPlaceMPlace_ok_of_safeToErasePlaceMention s pl
            (by simp only [safeToErasePlaceMention, hplCur, Bool.true_or])
          dsimp only [evalStmt]; rw [hbp]
        | assignConst _ _ => cases hkeep
        | assignCopy _ _ => cases hkeep
        | assignDerefRead _ _ _ _ => cases hkeep
        | storageLive _ => cases hkeep
        | storageDead _ => cases hkeep
      exact ⟨hsNoop, hsLen⟩)
    (fun _ _ _ _ _ _ s' _ _ _ hsLen hev => (evalStmt_locals_length hev) ▸ hsLen)
    (fun _ _ _ _ _ tgt _ _ _ hsLen => ⟨rfl, hsLen⟩)
    (fun _ => rfl)
    rfl
    (fun _ s _ _ _ d b o _ _ _ hsLen => by
      rw [simplifyEqualBranchTerm_true_eq]
      cases evalOperandLocal s.locals d with
      | error _ => rfl
      | ok v =>
        dsimp only
        cases valToSwitchNat v with
        | error _ => rfl
        | ok _ => exact ⟨Or.inl rfl, hsLen⟩)
    fuel st 0 0 hlen hNoOOM
  rw [countRetainedBefore_at_zero] at hf
  exact hf

/-- Dynamic Trace Certification Predicate: every `PlaceMention` actually executed along
the trace up to `fuel` steps satisfies `safeToErasePlaceMention` (covers both local-only
places and dynamically initialized zero-offset raw pointer places like `(*raw_ptr)` and
`(*raw_ptr).0`), and every executed equal-target `SwitchInt` has a valid integer/bool
discriminant. -/
def traceCertifiedSafe (body : Body) (st : MachineState) (bb stmtIdx fuel : Nat) : Prop :=
  (Nat.rec (motive := fun _ => MachineState → Nat → Nat → Prop)
    (fun _ _ _ => True)
    (fun _ ih s curBb curIdx =>
      match listGet body.blocks curBb with
      | none => True
      | some blk =>
        match listGet blk.stmts curIdx with
        | some stmt =>
          (match stmt with
           | .placeMention pl => safeToErasePlaceMention s pl = true
           | _ => True) ∧
          (match evalStmt s stmt with
           | .error _ => True
           | .ok s' => ih s' curBb (curIdx + 1))
        | none =>
          match blk.term with
          | .goto target => ih s target 0
          | .switchInt discrLocal branches otherwise =>
            (allTargetsEqual otherwise branches = false ∨
              ∃ v discrNat, evalOperandLocal s.locals discrLocal = .ok v ∧
                valToSwitchNat v = .ok discrNat) ∧
            (match evalOperandLocal s.locals discrLocal with
             | .error _ => True
             | .ok v =>
               match valToSwitchNat v with
               | .error _ => True
               | .ok discrNat => ih s (lookupSwitchTarget discrNat otherwise branches) 0)
          | _ => True)
    fuel) st bb stmtIdx

theorem traceCertifiedSafe_succ (body : Body) (s : MachineState) (curBb curIdx fuel : Nat) :
    traceCertifiedSafe body s curBb curIdx (fuel + 1) =
      (match listGet body.blocks curBb with
       | none => True
       | some blk =>
         match listGet blk.stmts curIdx with
         | some stmt =>
           (match stmt with
            | .placeMention pl => safeToErasePlaceMention s pl = true
            | _ => True) ∧
           (match evalStmt s stmt with
            | .error _ => True
            | .ok s' => traceCertifiedSafe body s' curBb (curIdx + 1) fuel)
         | none =>
           match blk.term with
           | .goto target => traceCertifiedSafe body s target 0 fuel
           | .switchInt discrLocal branches otherwise =>
             (allTargetsEqual otherwise branches = false ∨
               ∃ v discrNat, evalOperandLocal s.locals discrLocal = .ok v ∧
                 valToSwitchNat v = .ok discrNat) ∧
             (match evalOperandLocal s.locals discrLocal with
              | .error _ => True
              | .ok v =>
                match valToSwitchNat v with
                | .error _ => True
                | .ok discrNat =>
                  traceCertifiedSafe body s (lookupSwitchTarget discrNat otherwise branches) 0 fuel)
           | _ => True) := rfl

/-- Theorem 3B (Exact Trace-Certified Equivalence for Full Default `toRuntimePostCleanup false`):
Whenever a `Runtime(Initial)` trace only executes `PlaceMention`s satisfying
`safeToErasePlaceMention` (including raw `*ptr` and `(*ptr).0` on initialized pointers)
and only collapses equal-target `SwitchInt`s whose discriminant is initialized/valid,
`toRuntimePostCleanup false` (`-Zmir-preserve-ub=no`) preserves `evalBody` identically. -/
theorem evalBody_postCleanup_false_exact_of_traceCertified
    (body : Body) (st : MachineState) (fuel : Nat)
    (hcert : traceCertifiedSafe body st 0 0 fuel)
    (hNoOOM : NotOutOfFuel (evalBody body st fuel)) :
    ∃ fuel', evalBody (toRuntimePostCleanup false body) st fuel' = evalBody body st fuel := by
  unfold toRuntimePostCleanup
  rw [passSimplifyCfgPreOpt_passRemovePlaceMention_false_eq]
  have hf := runSteps_transform_forward_inv
    (keepStmt := isRetainedStmt false)
    (tFn := simplifyEqualBranchTerm false)
    (body := body)
    (Inv := fun s bb idx f => traceCertifiedSafe body s bb idx f)
    (fun f s bb idx blk stmt hbb hst hkeep hc => by
      simp only [traceCertifiedSafe_succ, hbb, hst] at hc
      have hsNoop : evalStmt s stmt = .ok s := by
        cases stmt with
        | nop => rfl
        | placeMention pl =>
          dsimp only at hc
          have ⟨bp, hbp⟩ := evalPlaceMPlace_ok_of_safeToErasePlaceMention hc.1
          dsimp only [evalStmt]; rw [hbp]
        | assignConst _ _ => cases hkeep
        | assignCopy _ _ => cases hkeep
        | assignDerefRead _ _ _ _ => cases hkeep
        | storageLive _ => cases hkeep
        | storageDead _ => cases hkeep
      have hc2 := hc.2
      rw [hsNoop] at hc2
      exact ⟨hsNoop, hc2⟩)
    (fun f s bb idx blk stmt s' hbb hst _ hc hev => by
      simp only [traceCertifiedSafe_succ, hbb, hst, hev] at hc
      exact hc.2)
    (fun f s bb idx blk tgt hbb hst hterm hc => by
      simp only [traceCertifiedSafe_succ, hbb, hst, hterm] at hc
      exact ⟨rfl, hc⟩)
    (fun _ => rfl)
    rfl
    (fun f s bb idx blk discr branches otherwise hbb hst hterm hc => by
      simp only [traceCertifiedSafe_succ, hbb, hst, hterm] at hc
      cases heq : allTargetsEqual otherwise branches with
      | true =>
        rcases hc.1 with hfalse | ⟨v, discrNat, hv, hnat⟩
        · rw [heq] at hfalse; cases hfalse
        · simp only [hv, hnat]
          have hc2 := hc.2
          simp only [hv, hnat] at hc2
          refine ⟨Or.inr ?_, hc2⟩
          simp only [simplifyEqualBranchTerm, Bool.not_false, Bool.true_and, heq, ↓reduceIte]
          rw [lookupSwitchTarget_of_allTargetsEqual heq]
      | false =>
        have hsimp : simplifyEqualBranchTerm false (.switchInt discr branches otherwise) =
            .switchInt discr branches otherwise := by
          simp only [simplifyEqualBranchTerm, Bool.not_false, Bool.true_and, heq,
            Bool.false_eq_true, ↓reduceIte]
        rw [hsimp]
        cases hop : evalOperandLocal s.locals discr with
        | error _ => rfl
        | ok v =>
          dsimp only
          cases hnat : valToSwitchNat v with
          | error _ => rfl
          | ok discrNat =>
            have hc2 := hc.2
            simp only [hop, hnat] at hc2
            exact ⟨Or.inl rfl, hc2⟩)
    fuel st 0 0 hcert hNoOOM
  rw [countRetainedBefore_at_zero] at hf
  exact hf

/-! ## Section 6: Constructive Counterexamples and Strict Unsoundness of `mirPreserveUb = false` -/

namespace Examples

def pairLayout : PointeeLayout := { size := 16, align := 8 }
def u64Layout : PointeeLayout := { size := 8, align := 8 }

/-- Specimen 1: `fn trigger(p: *const Pair) -> u32 { let _ = (*p).1; 42 }`
(inside a raw-pointer block) with `p = null`. Under `-Zmir-preserve-ub=yes`,
`PlaceMention(((*_1).1))` survives into `Runtime(PostCleanup)` and triggers
`.ub .nullInboundsOrDeref`; under default `-Zmir-preserve-ub=no`,
`RemovePlaceMention` erases it, turning UB into `.returned 42`. -/
def bodyNullNonzeroFieldPlaceMention : Body :=
  { blocks :=
      [ { stmts :=
            [ .storageLive 2,
              .placeMention { localId := 1, projs := [.deref .rawPtr pairLayout, .field 8] },
              .assignConst 2 .unitVal,
              .storageDead 2,
              .assignConst 0 (.intVal 42) ],
          term := .ret 0 } ] }

def stateNullPtrArg : MachineState :=
  { locals := [.liveUninit, .liveInit (.ptrVal .null), .dead], allocs := [] }

theorem ce1_null_nonzero_field_place_mention_ub_erased_in_default_postcleanup :
    evalBody (toRuntimePostCleanup true bodyNullNonzeroFieldPlaceMention) stateNullPtrArg 16 =
      .ub .nullInboundsOrDeref ∧
    evalBody (toRuntimePostCleanup false bodyNullNonzeroFieldPlaceMention) stateNullPtrArg 16 =
      .returned (.intVal 42) ∧
    evalBody (toRuntimePostCleanup false bodyNullNonzeroFieldPlaceMention) stateNullPtrArg 16 ≠
      evalBody bodyNullNonzeroFieldPlaceMention stateNullPtrArg 16 := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- Specimen 1B: `(*p).0` at offset `0` on `p = null` has `accessSize = 0` in
`checkAndDerefPtr`, so BOTH `mirPreserveUb = true` and `mirPreserveUb = false`
evaluate to `.returned (.intVal 42)`. -/
def bodyNullZeroOffsetField0PlaceMention : Body :=
  { blocks :=
      [ { stmts :=
            [ .storageLive 2,
              .placeMention { localId := 1, projs := [.deref .rawPtr pairLayout, .field 0] },
              .assignConst 2 .unitVal,
              .storageDead 2,
              .assignConst 0 (.intVal 42) ],
          term := .ret 0 } ] }

theorem ce1b_null_zero_offset_field0_defined_both_modes :
    evalBody (toRuntimePostCleanup true bodyNullZeroOffsetField0PlaceMention) stateNullPtrArg 16 =
      .returned (.intVal 42) ∧
    evalBody (toRuntimePostCleanup false bodyNullZeroOffsetField0PlaceMention) stateNullPtrArg 16 =
      .returned (.intVal 42) :=
  ⟨rfl, rfl⟩

/-- Specimen 2: Equal-target `SwitchInt` over an uninitialized local `u8`:
`bb0: StorageLive(1); switchInt(_1) -> [0: bb1, otherwise: bb1]; bb1: _0 = 42; Return()`.
Zero `PlaceMention` statements are present, yet `SimplifyCfg::PreOptimizations` with
`mir_preserve_ub = false` collapses `switchInt` into `goto bb1`, erasing the `.ub .uninitRead`. -/
def bodyUninitEqualTargetSwitchInt : Body :=
  { blocks :=
      [ { stmts := [.storageLive 1],
          term := .switchInt 1 [(0, 1)] 1 },
        { stmts := [.storageDead 1, .assignConst 0 (.intVal 42)],
          term := .ret 0 } ] }

def stateTwoLocals : MachineState :=
  { locals := [.liveUninit, .dead], allocs := [] }

theorem ce2_uninit_local_equal_target_switchint_ub_erased_in_default_postcleanup :
    evalBody (toRuntimePostCleanup true bodyUninitEqualTargetSwitchInt) stateTwoLocals 16 =
      .ub .uninitRead ∧
    evalBody (toRuntimePostCleanup false bodyUninitEqualTargetSwitchInt) stateTwoLocals 16 =
      .returned (.intVal 42) ∧
    evalBody (toRuntimePostCleanup false bodyUninitEqualTargetSwitchInt) stateTwoLocals 16 ≠
      evalBody bodyUninitEqualTargetSwitchInt stateTwoLocals 16 := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- Specimen 3: `let _ = *misaligned_raw_ptr;` where `p : *const u64` is misaligned
(address `0x1001`, alignment `8` required for a read, NOT aligned for `u64`).
Under RFC 2582 (`evalPlaceMPlace`), evaluating `PlaceMention((*p))` succeeds (`.returned 42`).
Under the counterfactual naive full-read evaluator (`evalPlaceNaiveFullRead`), it falsely
rejects the program with `.error .misalignedRefDeref`. -/
def bodyMisalignedRawDerefPlaceMention : Body :=
  { blocks :=
      [ { stmts :=
            [ .placeMention { localId := 1, projs := [.deref .rawPtr u64Layout] },
              .assignConst 0 (.intVal 42) ],
          term := .ret 0 } ] }

def stateMisalignedRawPtr : MachineState :=
  { locals := [.liveUninit, .liveInit (.ptrVal (.allocPtr 0 1))],
    allocs := [{ live := true, sizeBytes := 16, alignBytes := 8, baseAddr := 4096, storedVal := none }] }

theorem ce3_naive_full_read_semantics_for_place_mention_falsely_rejects_rfc2582_raw_deref :
    evalPlaceMPlace stateMisalignedRawPtr
        { localId := 1, projs := [.deref .rawPtr u64Layout] } =
      .ok (.memBase (.allocPtr 0 1)) ∧
    evalBody (toRuntimePostCleanup true bodyMisalignedRawDerefPlaceMention) stateMisalignedRawPtr 16 =
      .returned (.intVal 42) ∧
    evalPlaceNaiveFullRead stateMisalignedRawPtr
        { localId := 1, projs := [.deref .rawPtr u64Layout] } =
      .error .misalignedRefDeref :=
  ⟨rfl, rfl, rfl⟩

/-- Specimen 4: `Derefer` hoisting on chained dereference `(*(*pp)).1` (`pp : *const *const Pair`).
`lowerChainedPlaceMentionDerefer` hoists `_2 = copy (*pp)` via `Derefer` + `EraseDerefTemps`
before `RemovePlaceMention`:
- When `*pp` points to uninitialized memory (`storedVal := none`), `assignDerefRead` reads
  `*pp` and faults `.ub .uninitRead` under BOTH `mirPreserveUb = true` and `false`;
- When `*pp` points to initialized memory holding `null` (`storedVal := some (.ptrVal .null)`),
  the hoisted inner load succeeds, and only the outer `PlaceMention(((*_2).1))` detects
  `.ub .nullInboundsOrDeref` under `mirPreserveUb = true`, while `mirPreserveUb = false`
  silently erases it and returns `42`. -/
def bodyChainedDerefAfterDerefer : Body :=
  { blocks :=
      [ { stmts :=
            lowerChainedPlaceMentionDerefer 2 1 u64Layout pairLayout 8 ++
              [.storageDead 2, .assignConst 0 (.intVal 42)],
          term := .ret 0 } ] }

def stateChainedInnerUninit : MachineState :=
  { locals := [.liveUninit, .liveInit (.ptrVal (.allocPtr 0 0)), .dead],
    allocs := [{ live := true, sizeBytes := 8, alignBytes := 8, baseAddr := 4096, storedVal := none }] }

def stateChainedInnerHoldsNull : MachineState :=
  { locals := [.liveUninit, .liveInit (.ptrVal (.allocPtr 0 0)), .dead],
    allocs := [{ live := true, sizeBytes := 8, alignBytes := 8, baseAddr := 4096,
                 storedVal := some (.ptrVal .null) }] }

theorem ce4_derefer_chained_deref_inner_uninit_survives_while_outer_field_ub_erased :
    evalBody (toRuntimePostCleanup true bodyChainedDerefAfterDerefer) stateChainedInnerUninit 16 =
      .ub .uninitRead ∧
    evalBody (toRuntimePostCleanup false bodyChainedDerefAfterDerefer) stateChainedInnerUninit 16 =
      .ub .uninitRead ∧
    evalBody (toRuntimePostCleanup true bodyChainedDerefAfterDerefer) stateChainedInnerHoldsNull 16 =
      .ub .nullInboundsOrDeref ∧
    evalBody (toRuntimePostCleanup false bodyChainedDerefAfterDerefer) stateChainedInnerHoldsNull 16 =
      .returned (.intVal 42) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 2 (Strict Unsoundness of Default `Runtime(PostCleanup, mirPreserveUb := false)`):
There is no semantic-preserving guarantee for `toRuntimePostCleanup false`: concretely,
`toRuntimePostCleanup false` maps UB-triggering `Runtime(Initial)` bodies (both via
`PlaceMention` and via equal-target `SwitchInt`) to normal terminating returns `.returned 42`. -/
theorem runtimePostCleanup_preserveUb_false_unsound :
    (∃ b st fuel k v,
      evalBody b st fuel = .ub k ∧
      ∀ fuel', evalBody (toRuntimePostCleanup false b) st fuel' ≠ .ub k ∧
        evalBody (toRuntimePostCleanup false b) st fuel = .returned v) ∧
    (∃ b st fuel k v,
      allPlaceMentionsLocalOnly st.locals.length b = true →
      evalBody b st fuel = .ub k ∧
      evalBody (toRuntimePostCleanup false b) st fuel = .returned v) := by
  refine ⟨⟨bodyNullNonzeroFieldPlaceMention, stateNullPtrArg, 16, .nullInboundsOrDeref, .intVal 42,
      rfl, ?_⟩, ?_⟩
  · intro fuel'
    refine ⟨?_, rfl⟩
    cases fuel' with
    | zero => intro h; cases h
    | succ f1 => cases f1 with
      | zero => intro h; cases h
      | succ f2 => cases f2 with
        | zero => intro h; cases h
        | succ f3 => cases f3 with
          | zero => intro h; cases h
          | succ f4 => cases f4 with
            | zero => intro h; cases h
            | succ _ => intro h; cases h
  · refine ⟨bodyUninitEqualTargetSwitchInt, stateTwoLocals, 16, .uninitRead, .intVal 42,
      fun _ => ⟨rfl, rfl⟩⟩

end Examples

end MirPreserveUbSeam
