/-!
# Soundness of `PromoteTemps` (RFC 3027 Infallibility, Zero-Sized `&'static mut`, Value-Based `HasMutInterior`) and `CheckConstItemMutation` Destructor Asymmetry

Mechanized in pure Lean v4.34.1 without extra declarations, compiler reflection,
choice principles, or non-total definitions.

Upstream pinned references:
- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`)
- `rust-lang/rust@940498dad7cb35a753a7cce104ab510b414e84de` (`needs_drop` fix in `CheckConstItemMutation`)
- `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`)
- `rust-lang/rust@ce66487ebbd7541212d22d01c39a808057d69f1f` (`rust-lang/rust` HEAD)
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirSemantics` `deinitMovedPlace = true`)
-/

namespace PromoteTempsSoundness

/-! ## Common List and Arithmetic Helpers -/

noncomputable def getElem? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getElem? xs n

noncomputable def setElem? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match setElem? xs n v with
    | some xs' => some (x :: xs')
    | none => none

noncomputable def replicateList {α : Type} (v : α) : Nat → List α
  | 0 => []
  | n + 1 => v :: replicateList v n

noncomputable def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

theorem nat_blt_succ_succ (a b : Nat) : Nat.blt (a + 1) (b + 1) = Nat.blt a b := by
  simp [Nat.blt, Nat.ble]

theorem nat_ble_succ_succ (a b : Nat) : Nat.ble (a + 1) (b + 1) = Nat.ble a b := by
  simp [Nat.ble]

theorem nat_blt_imp_ble (a b : Nat) : Nat.blt a b = true → Nat.ble a b = true := by
  induction a generalizing b with
  | zero =>
    intro _
    rfl
  | succ a' ih =>
    cases b with
    | zero =>
      intro h
      cases h
    | succ b' =>
      intro h
      rw [nat_blt_succ_succ] at h
      rw [nat_ble_succ_succ]
      exact ih b' h

theorem getElem_replicate_some {α : Type} (v : α) (n i : Nat) (h : Nat.blt i n = true) :
    getElem? (replicateList v n) i = some v := by
  induction n generalizing i with
  | zero => cases h
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ j =>
      rw [nat_blt_succ_succ] at h
      exact ih j h

/-! ## Part 1: `Collector` (`TempState` Lattice) and Single-Assignment Tree Discipline -/

/-- Classification of MIR locals (`promote_consts.rs:106-110`). -/
inductive LocalKind where
  | returnPointer
  | arg
  | userVar
  | temp

/-- Context in which a MIR visitor visits a local (`promote_consts.rs:115-145`). -/
inductive PlaceUseCtx where
  | store
  | callDest
  | mutBorrow
  | sharedBorrow
  | nonMutRead
  | otherMutUse
  | dropUse
  | storageMarker

noncomputable def PlaceUseCtx.isDrop : PlaceUseCtx → Bool
  | .dropUse => true
  | _ => false

noncomputable def PlaceUseCtx.isUse : PlaceUseCtx → Bool
  | .storageMarker => false
  | _ => true

/-- Exact `TempState` lattice (`promote_consts.rs:73-86`). -/
inductive TempState where
  | undefined
  | defined (loc : Nat) (uses : Nat) (valid : Bool)
  | unpromotable
  | promotedOut

/-- Transition step matching `Collector::visit_local` (`promote_consts.rs:104-147`). -/
noncomputable def collectorVisitLocal
    (kind : LocalKind) (cur : TempState) (ctx : PlaceUseCtx) (loc : Nat) : TempState :=
  match kind with
  | .arg | .userVar => cur
  | .returnPointer | .temp =>
    if ctx.isDrop || !ctx.isUse then
      cur
    else
      match cur with
      | .undefined =>
        match ctx with
        | .store | .callDest => .defined loc 0 false
        | _ => .unpromotable
      | .defined dloc uses valid =>
        match ctx with
        | .mutBorrow | .sharedBorrow | .nonMutRead => .defined dloc (uses + 1) valid
        | .store | .callDest | .otherMutUse | .dropUse | .storageMarker => .unpromotable
      | .unpromotable | .promotedOut => .unpromotable

structure LocalEvent where
  kind : LocalKind
  ctx : PlaceUseCtx
  loc : Nat

noncomputable def collectorRunEvents (kind : LocalKind) : TempState → List LocalEvent → TempState
  | st, [] => st
  | st, ev :: rest =>
    collectorRunEvents kind (collectorVisitLocal kind st ev.ctx ev.loc) rest

noncomputable def allTempsRunEvents : TempState → List (PlaceUseCtx × Nat) → TempState
  | st, [] => st
  | st, (ctx, loc) :: rest =>
    allTempsRunEvents (collectorVisitLocal .temp st ctx loc) rest

/-- Non-temporaries (`arg` and `userVar`) are left unchanged by `Collector::visit_local`. -/
theorem collector_ignores_non_temps (k : LocalKind) (hk : k = .arg ∨ k = .userVar)
    (st : TempState) (evs : List LocalEvent) :
    collectorRunEvents k st evs = st := by
  induction evs generalizing st with
  | nil => rfl
  | cons ev rest ih =>
    rcases hk with rfl | rfl
    · simp [collectorRunEvents, collectorVisitLocal]
      exact ih st
    · simp [collectorRunEvents, collectorVisitLocal]
      exact ih st

/-- Drops and non-uses (`StorageLive`, `StorageDead`, mentions) leave `TempState` invariant. -/
theorem collector_drop_and_storage_noop (k : LocalKind) (st : TempState) (loc : Nat) :
    collectorVisitLocal k st .dropUse loc = st ∧
    collectorVisitLocal k st .storageMarker loc = st := by
  cases k <;> simp [collectorVisitLocal, PlaceUseCtx.isDrop, PlaceUseCtx.isUse]

/-- `.unpromotable` is an absorbing sink of `Collector`. -/
theorem collector_unpromotable_absorbing (k : LocalKind) (evs : List LocalEvent) :
    collectorRunEvents k .unpromotable evs = .unpromotable := by
  induction evs with
  | nil => rfl
  | cons ev rest ih =>
    have hstep : collectorVisitLocal k .unpromotable ev.ctx ev.loc = .unpromotable := by
      cases k <;> cases ev.ctx <;> rfl
    simp [collectorRunEvents, hstep, ih]

/-- `PromotedOut` transitions to `Unpromotable` on any active use (`promote_consts.rs:144`). -/
theorem collector_promotedOut_active_use_unpromotable (k : LocalKind)
    (hk : k = .returnPointer ∨ k = .temp) (ctx : PlaceUseCtx)
    (hdrop : ctx.isDrop = false) (huse : ctx.isUse = true) (loc : Nat) :
    collectorVisitLocal k .promotedOut ctx loc = .unpromotable := by
  rcases hk with rfl | rfl <;> simp [collectorVisitLocal, hdrop, huse]

/-- Two `store` or `callDest` initializations force a temporary to `.unpromotable`. -/
theorem collector_double_init_unpromotable (loc1 loc2 : Nat)
    (c1 c2 : PlaceUseCtx) (hc1 : c1 = .store ∨ c1 = .callDest)
    (hc2 : c2 = .store ∨ c2 = .callDest) :
    collectorVisitLocal .temp (collectorVisitLocal .temp .undefined c1 loc1) c2 loc2 =
      .unpromotable := by
  rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;> rfl

/-- `MutatingUseContext::Borrow` on a `.defined` temp increments `uses` (`promote_consts.rs:133`). -/
theorem collector_mutBorrow_increments_uses (dloc uses : Nat) (valid : Bool) (loc : Nat) :
    collectorVisitLocal .temp (.defined dloc uses valid) .mutBorrow loc =
      .defined dloc (uses + 1) valid := by
  rfl

noncomputable def activeReadsOrBorrowsOnly : List (PlaceUseCtx × Nat) → Bool
  | [] => true
  | (ctx, _) :: rest =>
    (match ctx with
     | .mutBorrow | .sharedBorrow | .nonMutRead | .dropUse | .storageMarker => true
     | .store | .callDest | .otherMutUse => false) && activeReadsOrBorrowsOnly rest

/-- Any sequence of visits preserving `.defined` contains strictly reads, borrows, drops, or storage markers. -/
theorem collector_defined_after_single_init (dloc uses : Nat) (valid : Bool)
    (evs : List (PlaceUseCtx × Nat)) (dloc' uses' : Nat) (valid' : Bool) :
    allTempsRunEvents (.defined dloc uses valid) evs = .defined dloc' uses' valid' →
    dloc' = dloc ∧ valid' = valid ∧ activeReadsOrBorrowsOnly evs = true := by
  induction evs generalizing uses with
  | nil =>
    intro h
    simp [allTempsRunEvents] at h
    rcases h with ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3.symm, rfl⟩
  | cons hd rest ih =>
    rcases hd with ⟨ctx, loc⟩
    intro h
    have habs : allTempsRunEvents .unpromotable rest = .unpromotable := by
      clear h ih
      induction rest with
      | nil => rfl
      | cons x xs ihx =>
        cases x.1 <;> simpa [allTempsRunEvents, collectorVisitLocal] using ihx
    cases ctx with
    | store =>
      simp [allTempsRunEvents, collectorVisitLocal, PlaceUseCtx.isDrop, PlaceUseCtx.isUse] at h
      rw [habs] at h
      cases h
    | callDest =>
      simp [allTempsRunEvents, collectorVisitLocal, PlaceUseCtx.isDrop, PlaceUseCtx.isUse] at h
      rw [habs] at h
      cases h
    | otherMutUse =>
      simp [allTempsRunEvents, collectorVisitLocal, PlaceUseCtx.isDrop, PlaceUseCtx.isUse] at h
      rw [habs] at h
      cases h
    | mutBorrow =>
      simp [allTempsRunEvents, collectorVisitLocal] at h
      obtain ⟨hloc, hval, hact⟩ := ih (uses + 1) h
      exact ⟨hloc, hval, by simpa [activeReadsOrBorrowsOnly] using hact⟩
    | sharedBorrow =>
      simp [allTempsRunEvents, collectorVisitLocal] at h
      obtain ⟨hloc, hval, hact⟩ := ih (uses + 1) h
      exact ⟨hloc, hval, by simpa [activeReadsOrBorrowsOnly] using hact⟩
    | nonMutRead =>
      simp [allTempsRunEvents, collectorVisitLocal] at h
      obtain ⟨hloc, hval, hact⟩ := ih (uses + 1) h
      exact ⟨hloc, hval, by simpa [activeReadsOrBorrowsOnly] using hact⟩
    | dropUse =>
      simp [allTempsRunEvents, collectorVisitLocal] at h
      obtain ⟨hloc, hval, hact⟩ := ih uses h
      exact ⟨hloc, hval, by simpa [activeReadsOrBorrowsOnly] using hact⟩
    | storageMarker =>
      simp [allTempsRunEvents, collectorVisitLocal] at h
      obtain ⟨hloc, hval, hact⟩ := ih uses h
      exact ⟨hloc, hval, by simpa [activeReadsOrBorrowsOnly] using hact⟩

/-! ## Part 2: Value-Based `Qualif`, RFC 3027 `Validator`, and Promotion Soundness -/

inductive MirTy where
  | int (signed : Bool) (bytes : Nat)
  | bool
  | unit
  | array (elem : MirTy) (len : Nat)
  | ref (isMut : Bool) (inner : MirTy)
  | unsafeCell (inner : MirTy)
  | option (inner : MirTy)
  | adt (hasDtor : Bool) (hasParam : Bool) (fields : List MirTy)

mutual

noncomputable def MirTy.sizeOf : MirTy → Nat
  | .int _ bytes => bytes
  | .bool => 1
  | .unit => 0
  | .array elem len => elem.sizeOf * len
  | .ref _ _ => 8
  | .unsafeCell inner => inner.sizeOf
  | .option _ => 1
  | .adt _ _ fields => mirTyListSizeOf fields

noncomputable def mirTyListSizeOf : List MirTy → Nat
  | [] => 0
  | t :: ts => t.sizeOf + mirTyListSizeOf ts

end

mutual

/-- Recursive `Ty::needs_drop` model (`qualifs.rs:155-161` and `check_const_item_mutation.rs:73`). -/
noncomputable def tyNeedsDrop : MirTy → Bool
  | .int _ _ | .bool | .unit | .ref _ _ => false
  | .array elem _ => tyNeedsDrop elem
  | .unsafeCell inner => tyNeedsDrop inner
  | .option inner => tyNeedsDrop inner
  | .adt hasDtor hasParam fields =>
    hasDtor || hasParam || tyListNeedsDrop fields

noncomputable def tyListNeedsDrop : List MirTy → Bool
  | [] => false
  | t :: ts => tyNeedsDrop t || tyListNeedsDrop ts

end

mutual

/-- Type-level `HasMutInterior` fallback (`qualifs.rs:95-130`). -/
noncomputable def tyHasMutInterior : MirTy → Bool
  | .int _ _ | .bool | .unit | .ref _ _ => false
  | .array elem _ => tyHasMutInterior elem
  | .unsafeCell _ => true
  | .option inner => tyHasMutInterior inner
  | .adt _ hasParam fields => hasParam || tyListHasMutInterior fields

noncomputable def tyListHasMutInterior : List MirTy → Bool
  | [] => false
  | t :: ts => tyHasMutInterior t || tyListHasMutInterior ts

end

inductive ConstContext where
  | fnBody
  | constItem (allowConstFnPromotion : Bool)
  | staticItem
  | inlineConst

/-- Atomic promotion rvalue/call leaf covering literals, `AddWithOverflow`, `Div`/`Rem`,
array place-borrow vs value-copy indexing, `#[rustc_promotable]` calls, `UnsafeCell`,
`Option`, and `Operand::Move` with `deinitMovedPlace = true`. -/
inductive CandLeaf where
  | litInt (signed : Bool) (val : Int)
  | litBool (b : Bool)
  | litUnit
  | emptyArray (elemTy : MirTy)
  | unsafeCellUnit
  | checkedAddU8 (lhs rhs : Nat)
  | intDiv (signed : Bool) (lhs rhs : Int)
  | intRem (signed : Bool) (lhs rhs : Int)
  | copyArrayIndex (elemTy : MirTy) (len idx : Nat) (elems : List Int)
  | placeArrayIndexBase (elemTy : MirTy) (len idx : Nat) (elems : List Int)
  | constFnCall (isPromotable isConstFn canPanic : Bool) (retTy : MirTy) (retVal : Int)
  | moveTemp (ty : MirTy) (val : Int) (usedTwice : Bool)

/-- Aggregate wrapper capturing value-based `Qualif` structural traversal (`Option`, `UnsafeCell`, `Adt`). -/
inductive CandExpr where
  | leaf (node : CandLeaf)
  | optionNone (innerTy : MirTy)
  | optionSome (innerTy : MirTy) (arg : CandLeaf)
  | unsafeCellWrap (innerTy : MirTy) (arg : CandLeaf)
  | adtWrap (hasDtor hasParam : Bool) (fields : List (MirTy × CandLeaf))

noncomputable def leafHasMutInterior : CandLeaf → Bool
  | .litInt _ _ | .litBool _ | .litUnit | .emptyArray _ => false
  | .unsafeCellUnit => true
  | .checkedAddU8 _ _ | .intDiv _ _ _ | .intRem _ _ _ => false
  | .copyArrayIndex elemTy _ _ _ => tyHasMutInterior elemTy
  | .placeArrayIndexBase elemTy _ _ _ => tyHasMutInterior elemTy
  | .constFnCall _ _ _ retTy _ => tyHasMutInterior retTy
  | .moveTemp ty _ _ => tyHasMutInterior ty

noncomputable def listLeafHasMutInterior : List (MirTy × CandLeaf) → Bool
  | [] => false
  | (_, l) :: rest => leafHasMutInterior l || listLeafHasMutInterior rest

/-- Value-based `HasMutInterior` qualification (`qualifs.rs:84-137, 268-287`). -/
noncomputable def qualifHasMutInterior : CandExpr → Bool
  | .leaf n => leafHasMutInterior n
  | .optionNone _ => false
  | .optionSome _ arg => leafHasMutInterior arg
  | .unsafeCellWrap _ _ => true
  | .adtWrap _ hasParam fields => hasParam || listLeafHasMutInterior fields

noncomputable def leafNeedsDrop : CandLeaf → Bool
  | .litInt _ _ | .litBool _ | .litUnit | .emptyArray _ | .unsafeCellUnit => false
  | .checkedAddU8 _ _ | .intDiv _ _ _ | .intRem _ _ _ => false
  | .copyArrayIndex elemTy _ _ _ => tyNeedsDrop elemTy
  | .placeArrayIndexBase elemTy _ _ _ => tyNeedsDrop elemTy
  | .constFnCall _ _ _ retTy _ => tyNeedsDrop retTy
  | .moveTemp ty _ _ => tyNeedsDrop ty

noncomputable def listLeafNeedsDrop : List (MirTy × CandLeaf) → Bool
  | [] => false
  | (_, l) :: rest => leafNeedsDrop l || listLeafNeedsDrop rest

/-- Value-based `NeedsDrop` qualification (`qualifs.rs:144-162, 268-287`). -/
noncomputable def qualifNeedsDrop : CandExpr → Bool
  | .leaf n => leafNeedsDrop n
  | .optionNone _ => false
  | .optionSome _ arg => leafNeedsDrop arg
  | .unsafeCellWrap _ arg => leafNeedsDrop arg
  | .adtWrap hasDtor hasParam fields =>
    hasDtor || hasParam || listLeafNeedsDrop fields

theorem qualifHasMutInterior_optionNone_unsafeCellZst_false :
    qualifHasMutInterior (.optionNone (.unsafeCell .unit)) = false := by
  rfl

theorem qualifHasMutInterior_unsafeCellZst_true :
    qualifHasMutInterior (.leaf .unsafeCellUnit) = true ∧
    (.unsafeCell .unit : MirTy).sizeOf = 0 := by
  exact ⟨rfl, rfl⟩

theorem qualifHasMutInterior_optionSome_unsafeCellZst_true :
    qualifHasMutInterior (.optionSome (.unsafeCell .unit) .unsafeCellUnit) = true := by
  rfl

/-- `Validator::validate_ref` (`promote_consts.rs:400-430`). -/
noncomputable def validateRef (isMut : Bool) (placeTy : MirTy) (hasMutInterior : Bool) : Bool :=
  if isMut then
    match placeTy with
    | .array _ 0 => true
    | _ => false
  else
    !hasMutInterior

noncomputable def i8Min : Int := -128

/-- `Validator::validate_rvalue` + `validate_call` (`promote_consts.rs:432-693`). -/
noncomputable def validateLeaf (ctx : ConstContext) (inSafeBlock : Bool) : CandLeaf → Bool
  | .litInt _ _ | .litBool _ | .litUnit | .emptyArray _ | .unsafeCellUnit => true
  | .checkedAddU8 _ _ => true
  | .intDiv signed lhs rhs =>
    rhs != 0 && (!signed || !(rhs == -1 && lhs == i8Min))
  | .intRem signed lhs rhs =>
    rhs != 0 && (!signed || !(rhs == -1 && lhs == i8Min))
  | .copyArrayIndex _ len idx _ => Nat.blt idx len
  | .placeArrayIndexBase _ _ _ _ => true
  | .constFnCall isPromotable isConstFn _ _ _ =>
    if isPromotable then true
    else
      let promoteAllFn := match ctx with
        | .staticItem => true
        | .constItem allow => allow
        | .fnBody | .inlineConst => false
      promoteAllFn && isConstFn && inSafeBlock
  | .moveTemp _ _ usedTwice => !usedTwice

noncomputable def validateLeafList (ctx : ConstContext) (inSafeBlock : Bool) :
    List (MirTy × CandLeaf) → Bool
  | [] => true
  | (_, l) :: rest => validateLeaf ctx inSafeBlock l && validateLeafList ctx inSafeBlock rest

noncomputable def validateCandExpr (ctx : ConstContext) (inSafeBlock : Bool) : CandExpr → Bool
  | .leaf l => validateLeaf ctx inSafeBlock l
  | .optionNone _ => true
  | .optionSome _ arg => validateLeaf ctx inSafeBlock arg
  | .unsafeCellWrap _ arg => validateLeaf ctx inSafeBlock arg
  | .adtWrap _ _ fields => validateLeafList ctx inSafeBlock fields

noncomputable def leafTargetTy : CandLeaf → MirTy
  | .litInt signed _ => .int signed 1
  | .litBool _ => .bool
  | .litUnit => .unit
  | .emptyArray elemTy => .array elemTy 0
  | .unsafeCellUnit => .unsafeCell .unit
  | .checkedAddU8 _ _ => .adt false false [.int false 1, .bool]
  | .intDiv signed _ _ => .int signed 1
  | .intRem signed _ _ => .int signed 1
  | .copyArrayIndex elemTy _ _ _ => elemTy
  | .placeArrayIndexBase elemTy len _ _ => .array elemTy len
  | .constFnCall _ _ _ retTy _ => retTy
  | .moveTemp ty _ _ => ty

noncomputable def candTargetTy : CandExpr → MirTy
  | .leaf l => leafTargetTy l
  | .optionNone innerTy => .option innerTy
  | .optionSome innerTy _ => .option innerTy
  | .unsafeCellWrap innerTy _ => .unsafeCell innerTy
  | .adtWrap hasDtor hasParam fields => .adt hasDtor hasParam (fields.map Prod.fst)

/-- Full candidate admission predicate (`validate_candidate`, `promote_consts.rs:197-216`). -/
noncomputable def validatePromotionCandidate
    (ctx : ConstContext) (inSafeBlock isMut : Bool) (expr : CandExpr) : Bool :=
  !qualifNeedsDrop expr &&
  validateCandExpr ctx inSafeBlock expr &&
  validateRef isMut (candTargetTy expr) (qualifHasMutInterior expr)

inductive CtfeOutcome where
  | ok (val : Int)
  | faultPanic
  | uninitMoveFault

noncomputable def ctfeEvalLeaf : CandLeaf → CtfeOutcome
  | .litInt _ v => .ok v
  | .litBool b => .ok (if b then 1 else 0)
  | .litUnit => .ok 0
  | .emptyArray _ => .ok 0
  | .unsafeCellUnit => .ok 0
  | .checkedAddU8 lhs rhs => .ok (Int.ofNat ((lhs + rhs) % 256))
  | .intDiv signed lhs rhs =>
    if rhs == 0 || (signed && rhs == -1 && lhs == i8Min) then .faultPanic
    else .ok (lhs / rhs)
  | .intRem signed lhs rhs =>
    if rhs == 0 || (signed && rhs == -1 && lhs == i8Min) then .faultPanic
    else .ok (lhs % rhs)
  | .copyArrayIndex _ len idx elems =>
    if Nat.blt idx len then
      match getElem? elems idx with
      | some v => .ok v
      | none => .ok 0
    else .faultPanic
  | .placeArrayIndexBase _ _ _ _ => .ok 0
  | .constFnCall _ _ canPanic _ retVal =>
    if canPanic then .faultPanic else .ok retVal
  | .moveTemp ty val usedTwice =>
    if usedTwice && !(ty.sizeOf == 0) then .uninitMoveFault else .ok val

noncomputable def ctfeEvalLeafList : List (MirTy × CandLeaf) → CtfeOutcome
  | [] => .ok 0
  | (_, l) :: rest =>
    match ctfeEvalLeaf l with
    | .ok _ => ctfeEvalLeafList rest
    | .faultPanic => .faultPanic
    | .uninitMoveFault => .uninitMoveFault

noncomputable def ctfeEvalPromoted : CandExpr → CtfeOutcome
  | .leaf l => ctfeEvalLeaf l
  | .optionNone _ => .ok 0
  | .optionSome _ arg => ctfeEvalLeaf arg
  | .unsafeCellWrap _ arg => ctfeEvalLeaf arg
  | .adtWrap _ _ fields => ctfeEvalLeafList fields

/-- `#[rustc_promotable]` contract: annotated promotable calls cannot panic at CTFE, and
legacy `const`/`static` `const fn` calls are only evaluated when `canPanic = false`. -/
noncomputable def callContractSatisfiedLeaf : CandLeaf → Bool
  | .constFnCall _ _ canPanic _ _ => !canPanic
  | _ => true

noncomputable def callContractSatisfiedList : List (MirTy × CandLeaf) → Bool
  | [] => true
  | (_, l) :: rest => callContractSatisfiedLeaf l && callContractSatisfiedList rest

noncomputable def callContractSatisfied : CandExpr → Bool
  | .leaf l => callContractSatisfiedLeaf l
  | .optionNone _ => true
  | .optionSome _ arg => callContractSatisfiedLeaf arg
  | .unsafeCellWrap _ arg => callContractSatisfiedLeaf arg
  | .adtWrap _ _ fields => callContractSatisfiedList fields

theorem ctfeEvalLeaf_ok_of_validate (ctx : ConstContext) (inSafeBlock : Bool) (l : CandLeaf)
    (hv : validateLeaf ctx inSafeBlock l = true)
    (hc : callContractSatisfiedLeaf l = true) :
    ∃ v, ctfeEvalLeaf l = .ok v := by
  cases l with
  | litInt s v => exact ⟨v, rfl⟩
  | litBool b => exact ⟨if b then 1 else 0, rfl⟩
  | litUnit => exact ⟨0, rfl⟩
  | emptyArray _ => exact ⟨0, rfl⟩
  | unsafeCellUnit => exact ⟨0, rfl⟩
  | checkedAddU8 lhs rhs => exact ⟨Int.ofNat ((lhs + rhs) % 256), rfl⟩
  | intDiv s l r =>
    dsimp only [validateLeaf] at hv
    cases hr : r == 0 with
    | true =>
      have hne : (r != 0) = false := by
        have h : (r != 0) = !(r == 0) := rfl
        rw [h, hr]; rfl
      rw [hne] at hv
      cases hv
    | false =>
      dsimp only [ctfeEvalLeaf]
      rw [hr]
      cases hsg : s with
      | false => exact ⟨l / r, rfl⟩
      | true =>
        cases hr1 : r == -1 with
        | false => exact ⟨l / r, rfl⟩
        | true =>
          cases hl1 : l == i8Min with
          | false => exact ⟨l / r, rfl⟩
          | true =>
            have hnz : (r != 0) = true := by
              have h : (r != 0) = !(r == 0) := rfl
              rw [h, hr]; rfl
            rw [hnz, hsg, hr1, hl1] at hv
            cases hv
  | intRem s l r =>
    dsimp only [validateLeaf] at hv
    cases hr : r == 0 with
    | true =>
      have hne : (r != 0) = false := by
        have h : (r != 0) = !(r == 0) := rfl
        rw [h, hr]; rfl
      rw [hne] at hv
      cases hv
    | false =>
      dsimp only [ctfeEvalLeaf]
      rw [hr]
      cases hsg : s with
      | false => exact ⟨l % r, rfl⟩
      | true =>
        cases hr1 : r == -1 with
        | false => exact ⟨l % r, rfl⟩
        | true =>
          cases hl1 : l == i8Min with
          | false => exact ⟨l % r, rfl⟩
          | true =>
            have hnz : (r != 0) = true := by
              have h : (r != 0) = !(r == 0) := rfl
              rw [h, hr]; rfl
            rw [hnz, hsg, hr1, hl1] at hv
            cases hv
  | copyArrayIndex _ len idx elems =>
    dsimp only [validateLeaf] at hv
    cases hg : getElem? elems idx with
    | none => exact ⟨0, by dsimp only [ctfeEvalLeaf]; rw [hv, hg]; rfl⟩
    | some v => exact ⟨v, by dsimp only [ctfeEvalLeaf]; rw [hv, hg]; rfl⟩
  | placeArrayIndexBase _ _ _ _ => exact ⟨0, rfl⟩
  | constFnCall ip ic cp rt rv =>
    dsimp only [callContractSatisfiedLeaf] at hc
    cases cp with
    | true => cases hc
    | false => exact ⟨rv, rfl⟩
  | moveTemp ty val ut =>
    dsimp only [validateLeaf] at hv
    cases ut with
    | true => cases hv
    | false => exact ⟨val, rfl⟩

theorem ctfeEvalLeafList_ok_of_validate (ctx : ConstContext) (inSafeBlock : Bool) :
    ∀ fields : List (MirTy × CandLeaf),
      validateLeafList ctx inSafeBlock fields = true →
      callContractSatisfiedList fields = true →
      ∃ v, ctfeEvalLeafList fields = .ok v
  | [] => fun _ _ => ⟨0, rfl⟩
  | (_, l) :: rest => fun hv hc => by
    simp [validateLeafList, Bool.and_eq_true] at hv
    simp [callContractSatisfiedList, Bool.and_eq_true] at hc
    obtain ⟨v1, hv1⟩ := ctfeEvalLeaf_ok_of_validate ctx inSafeBlock l hv.1 hc.1
    obtain ⟨v2, hv2⟩ := ctfeEvalLeafList_ok_of_validate ctx inSafeBlock rest hv.2 hc.2
    exact ⟨v2, by simp [ctfeEvalLeafList, hv1, hv2]⟩

/-- Every candidate admitted by `validatePromotionCandidate` evaluates to `.ok v` at CTFE (RFC 3027 infallibility). -/
theorem validator_implies_ctfe_infallible
    (ctx : ConstContext) (inSafeBlock isMut : Bool) (e : CandExpr)
    (hval : validatePromotionCandidate ctx inSafeBlock isMut e = true)
    (hcall : callContractSatisfied e = true) :
    ∃ v, ctfeEvalPromoted e = .ok v := by
  have hvc : validateCandExpr ctx inSafeBlock e = true := by
    simp [validatePromotionCandidate] at hval
    exact hval.1.2
  cases e with
  | leaf l =>
    exact ctfeEvalLeaf_ok_of_validate ctx inSafeBlock l hvc hcall
  | optionNone _ => exact ⟨0, rfl⟩
  | optionSome _ arg =>
    exact ctfeEvalLeaf_ok_of_validate ctx inSafeBlock arg hvc hcall
  | unsafeCellWrap _ arg =>
    exact ctfeEvalLeaf_ok_of_validate ctx inSafeBlock arg hvc hcall
  | adtWrap _ _ fields =>
    simp [validateCandExpr] at hvc
    simp [callContractSatisfied] at hcall
    simpa [ctfeEvalPromoted] using ctfeEvalLeafList_ok_of_validate ctx inSafeBlock fields hvc hcall

inductive RuntimeOutcome where
  | returned (val : Int) (drops : List Nat)
  | runtimePanic (drops : List Nat)
  | uninitMoveFault (drops : List Nat)

noncomputable def evalLeafRuntime (overflowChecks : Bool) (needsDrop : Bool) (l : CandLeaf) :
    RuntimeOutcome :=
  let drops : List Nat := if needsDrop then [1] else []
  match l with
  | .checkedAddU8 lhs rhs =>
    if overflowChecks && !Nat.blt (lhs + rhs) 256 then
      .runtimePanic drops
    else
      .returned (Int.ofNat ((lhs + rhs) % 256)) drops
  | .placeArrayIndexBase _ len idx elems =>
    if Nat.blt idx len then
      match getElem? elems idx with
      | some v => .returned v drops
      | none => .returned 0 drops
    else
      .runtimePanic drops
  | _ =>
    match ctfeEvalLeaf l with
    | .ok v => .returned v drops
    | .faultPanic => .runtimePanic drops
    | .uninitMoveFault => .uninitMoveFault drops

noncomputable def evalExprRuntime (overflowChecks : Bool) (e : CandExpr) : RuntimeOutcome :=
  let nd := qualifNeedsDrop e
  let drops : List Nat := if nd then [1] else []
  match e with
  | .leaf l => evalLeafRuntime overflowChecks nd l
  | .optionNone _ => .returned 0 drops
  | .optionSome _ arg => evalLeafRuntime overflowChecks nd arg
  | .unsafeCellWrap _ arg => evalLeafRuntime overflowChecks nd arg
  | .adtWrap _ _ fields =>
    match ctfeEvalLeafList fields with
    | .ok v => .returned v drops
    | .faultPanic => .runtimePanic drops
    | .uninitMoveFault => .uninitMoveFault drops

/-- Execution before `PromoteTemps` (`if branchCond then use(&e) else skip`). -/
noncomputable def evalParentBeforePromote
    (overflowChecks branchCond : Bool) (e : CandExpr) : RuntimeOutcome :=
  if branchCond then evalExprRuntime overflowChecks e
  else .returned 0 []

/-- Execution after `PromoteTemps`: CTFE evaluates `promoted[0]` unconditionally, while
`checkedAddU8` (`uses = 2`, `keepOriginal = true`) and `placeArrayIndexBase` keep their
runtime `Assert` checks in the active branch (`promote_consts.rs:778-827, 923-956`). -/
noncomputable def evalParentAfterPromote
    (overflowChecks branchCond : Bool) (e : CandExpr) : RuntimeOutcome :=
  match ctfeEvalPromoted e with
  | .faultPanic => .runtimePanic []
  | .uninitMoveFault => .uninitMoveFault []
  | .ok vProm =>
    if !branchCond then .returned 0 []
    else
      match e with
      | .leaf (.checkedAddU8 lhs rhs) =>
        if overflowChecks && !Nat.blt (lhs + rhs) 256 then .runtimePanic []
        else .returned (Int.ofNat ((lhs + rhs) % 256)) []
      | .optionSome _ (.checkedAddU8 lhs rhs) =>
        if overflowChecks && !Nat.blt (lhs + rhs) 256 then .runtimePanic []
        else .returned (Int.ofNat ((lhs + rhs) % 256)) []
      | .unsafeCellWrap _ (.checkedAddU8 lhs rhs) =>
        if overflowChecks && !Nat.blt (lhs + rhs) 256 then .runtimePanic []
        else .returned (Int.ofNat ((lhs + rhs) % 256)) []
      | .leaf (.placeArrayIndexBase _ len idx elems) =>
        if Nat.blt idx len then
          match getElem? elems idx with
          | some v => .returned v []
          | none => .returned 0 []
        else .runtimePanic []
      | .optionSome _ (.placeArrayIndexBase _ len idx elems) =>
        if Nat.blt idx len then
          match getElem? elems idx with
          | some v => .returned v []
          | none => .returned 0 []
        else .runtimePanic []
      | .unsafeCellWrap _ (.placeArrayIndexBase _ len idx elems) =>
        if Nat.blt idx len then
          match getElem? elems idx with
          | some v => .returned v []
          | none => .returned 0 []
        else .runtimePanic []
      | _ => .returned vProm []

/-- Validated promotion preserves runtime results and destructor traces across all branches and overflow modes. -/
theorem promoteTemps_runtime_and_drop_trace_preserved
    (ctx : ConstContext) (inSafeBlock isMut overflowChecks branchCond : Bool) (e : CandExpr)
    (hval : validatePromotionCandidate ctx inSafeBlock isMut e = true)
    (hcall : callContractSatisfied e = true) :
    evalParentAfterPromote overflowChecks branchCond e =
      evalParentBeforePromote overflowChecks branchCond e := by
  have hnd : qualifNeedsDrop e = false := by
    simp [validatePromotionCandidate] at hval
    exact hval.1.1
  have hvc : validateCandExpr ctx inSafeBlock e = true := by
    simp [validatePromotionCandidate] at hval
    exact hval.1.2
  cases branchCond with
  | false =>
    obtain ⟨vProm, hvProm⟩ := validator_implies_ctfe_infallible ctx inSafeBlock isMut e hval hcall
    simp [evalParentAfterPromote, evalParentBeforePromote, hvProm]
  | true =>
    cases e with
    | leaf l =>
      obtain ⟨vProm, hvProm⟩ := ctfeEvalLeaf_ok_of_validate ctx inSafeBlock l hvc hcall
      cases l <;>
        simp [evalParentAfterPromote, evalParentBeforePromote, evalExprRuntime, evalLeafRuntime,
          ctfeEvalPromoted, hnd, hvProm]
    | optionNone _ =>
      simp [evalParentAfterPromote, evalParentBeforePromote, evalExprRuntime, ctfeEvalPromoted, hnd]
    | optionSome _ arg =>
      obtain ⟨vProm, hvProm⟩ := ctfeEvalLeaf_ok_of_validate ctx inSafeBlock arg hvc hcall
      cases arg <;>
        simp [evalParentAfterPromote, evalParentBeforePromote, evalExprRuntime, evalLeafRuntime,
          ctfeEvalPromoted, hnd, hvProm]
    | unsafeCellWrap _ arg =>
      obtain ⟨vProm, hvProm⟩ := ctfeEvalLeaf_ok_of_validate ctx inSafeBlock arg hvc hcall
      cases arg <;>
        simp [evalParentAfterPromote, evalParentBeforePromote, evalExprRuntime, evalLeafRuntime,
          ctfeEvalPromoted, hnd, hvProm]
    | adtWrap _ _ fields =>
      obtain ⟨vProm, hvProm⟩ := validator_implies_ctfe_infallible ctx inSafeBlock isMut (.adtWrap _ _ fields) hval hcall
      simp [ctfeEvalPromoted] at hvProm
      simp [evalParentAfterPromote, evalParentBeforePromote, evalExprRuntime, ctfeEvalPromoted, hvProm, hnd]

noncomputable def RuntimeOutcome.drops : RuntimeOutcome → List Nat
  | .returned _ d => d
  | .runtimePanic d => d
  | .uninitMoveFault d => d

theorem evalLeafRuntime_drops (oc : Bool) (l : CandLeaf) :
    (evalLeafRuntime oc true l).drops = [1] := by
  cases l with
  | checkedAddU8 lhs rhs =>
    dsimp [evalLeafRuntime]
    cases (oc && !Nat.blt (lhs + rhs) 256) <;> rfl
  | placeArrayIndexBase _ len idx elems =>
    dsimp [evalLeafRuntime]
    cases Nat.blt idx len with
    | false => rfl
    | true => cases getElem? elems idx <;> rfl
  | litInt _ _ | litBool _ | litUnit | emptyArray _ | unsafeCellUnit
  | intDiv _ _ _ | intRem _ _ _ | copyArrayIndex _ _ _ _
  | constFnCall _ _ _ _ _ | moveTemp _ _ _ =>
    dsimp [evalLeafRuntime]
    cases ctfeEvalLeaf _ <;> rfl

theorem evalExprRuntime_drops_of_needsDrop (oc : Bool) (e : CandExpr)
    (hnd : qualifNeedsDrop e = true) :
    (evalExprRuntime oc e).drops = [1] := by
  cases e with
  | leaf l => simpa [evalExprRuntime, hnd] using evalLeafRuntime_drops oc l
  | optionNone _ => simp [qualifNeedsDrop] at hnd
  | optionSome _ arg => simpa [evalExprRuntime, hnd] using evalLeafRuntime_drops oc arg
  | unsafeCellWrap _ arg => simpa [evalExprRuntime, hnd] using evalLeafRuntime_drops oc arg
  | adtWrap _ _ fields =>
    dsimp [evalExprRuntime]
    rw [hnd]
    dsimp
    cases ctfeEvalLeafList fields <;> rfl

theorem evalParentAfterPromote_drops_nil (oc bc : Bool) (e : CandExpr) :
    (evalParentAfterPromote oc bc e).drops = [] := by
  cases h : ctfeEvalPromoted e with
  | faultPanic => simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
  | uninitMoveFault => simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
  | ok v =>
    cases bc with
    | false => simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
    | true =>
      cases e with
      | leaf l =>
        cases l with
        | checkedAddU8 lhs rhs =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases (oc && !Nat.blt (lhs + rhs) 256) <;> rfl
        | placeArrayIndexBase _ len idx elems =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases Nat.blt idx len with
          | false => rfl
          | true => cases getElem? elems idx <;> rfl
        | litInt _ _ | litBool _ | litUnit | emptyArray _ | unsafeCellUnit
        | intDiv _ _ _ | intRem _ _ _ | copyArrayIndex _ _ _ _
        | constFnCall _ _ _ _ _ | moveTemp _ _ _ =>
          simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
      | optionNone _ => simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
      | optionSome _ arg =>
        cases arg with
        | checkedAddU8 lhs rhs =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases (oc && !Nat.blt (lhs + rhs) 256) <;> rfl
        | placeArrayIndexBase _ len idx elems =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases Nat.blt idx len with
          | false => rfl
          | true => cases getElem? elems idx <;> rfl
        | litInt _ _ | litBool _ | litUnit | emptyArray _ | unsafeCellUnit
        | intDiv _ _ _ | intRem _ _ _ | copyArrayIndex _ _ _ _
        | constFnCall _ _ _ _ _ | moveTemp _ _ _ =>
          simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
      | unsafeCellWrap _ arg =>
        cases arg with
        | checkedAddU8 lhs rhs =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases (oc && !Nat.blt (lhs + rhs) 256) <;> rfl
        | placeArrayIndexBase _ len idx elems =>
          dsimp [evalParentAfterPromote]; rw [h]; dsimp
          cases Nat.blt idx len with
          | false => rfl
          | true => cases getElem? elems idx <;> rfl
        | litInt _ _ | litBool _ | litUnit | emptyArray _ | unsafeCellUnit
        | intDiv _ _ _ | intRem _ _ _ | copyArrayIndex _ _ _ _
        | constFnCall _ _ _ _ _ | moveTemp _ _ _ =>
          simp [evalParentAfterPromote, h, RuntimeOutcome.drops]
      | adtWrap _ _ _ => simp [evalParentAfterPromote, h, RuntimeOutcome.drops]

/-- Combined CTFE-totality and runtime/drop-trace soundness iff criterion for `PromoteTemps`. -/
theorem promoteTemps_infallible_preserves_semantics_iff
    (ctx : ConstContext) (inSafeBlock isMut : Bool) (e : CandExpr)
    (hvc : validateCandExpr ctx inSafeBlock e = true)
    (hcall : callContractSatisfied e = true)
    (href : validateRef isMut (candTargetTy e) (qualifHasMutInterior e) = true) :
    ((∃ v, ctfeEvalPromoted e = .ok v) ∧
     (∀ overflowChecks branchCond,
       evalParentAfterPromote overflowChecks branchCond e =
         evalParentBeforePromote overflowChecks branchCond e)) ↔
      qualifNeedsDrop e = false := by
  constructor
  · intro ⟨_, hsem⟩
    have htrue := hsem false true
    cases hnd : qualifNeedsDrop e with
    | false => rfl
    | true =>
      have hdrops := congrArg RuntimeOutcome.drops htrue
      rw [evalParentAfterPromote_drops_nil] at hdrops
      simp [evalParentBeforePromote] at hdrops
      rw [evalExprRuntime_drops_of_needsDrop false e hnd] at hdrops
      cases hdrops
  · intro hnd
    have hval : validatePromotionCandidate ctx inSafeBlock isMut e = true := by
      simp [validatePromotionCandidate, hnd, hvc, href]
    refine ⟨validator_implies_ctfe_infallible ctx inSafeBlock isMut e hval hcall, ?_⟩
    intro oc bc
    exact promoteTemps_runtime_and_drop_trace_preserved ctx inSafeBlock isMut oc bc e hval hcall

/-- Witness 1: `if false { &(1 / 0) }` is rejected by `validatePromotionCandidate` and panics at CTFE. -/
theorem ce_div_zero_dead_branch_breaks_ctfe :
    validatePromotionCandidate .fnBody true false (.leaf (.intDiv false 1 0)) = false ∧
    ctfeEvalPromoted (.leaf (.intDiv false 1 0)) = .faultPanic ∧
    evalParentBeforePromote true false (.leaf (.intDiv false 1 0)) = .returned 0 [] ∧
    evalParentAfterPromote true false (.leaf (.intDiv false 1 0)) = .runtimePanic [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness 2: `&(i8::MIN / -1)` is rejected by `validatePromotionCandidate` (`promote_consts.rs:510-524`). -/
theorem ce_signed_min_div_neg1_breaks_ctfe :
    validatePromotionCandidate .fnBody true false (.leaf (.intDiv true i8Min (-1))) = false ∧
    validatePromotionCandidate .fnBody true false (.leaf (.intDiv true (-5) (-1))) = true ∧
    ctfeEvalPromoted (.leaf (.intDiv true i8Min (-1))) = .faultPanic ∧
    ctfeEvalPromoted (.leaf (.intDiv true (-5) (-1))) = .ok 5 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness 3: value-copy `&({ [10, 20][2] })` is rejected by `validate_place` (`idx < len`), whereas
place-borrow `&([10, 20][2])` promotes the array base and preserves the runtime bounds check! -/
theorem ce_copy_index_oob_rejected_vs_place_index_base_promoted :
    validatePromotionCandidate .fnBody true false
      (.leaf (.copyArrayIndex (.int false 4) 2 2 [10, 20])) = false ∧
    validatePromotionCandidate .fnBody true false
      (.leaf (.placeArrayIndexBase (.int false 4) 2 2 [10, 20])) = true ∧
    evalParentAfterPromote true false (.leaf (.placeArrayIndexBase (.int false 4) 2 2 [10, 20])) =
      .returned 0 [] ∧
    evalParentAfterPromote true true (.leaf (.placeArrayIndexBase (.int false 4) 2 2 [10, 20])) =
      .runtimePanic [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness 4: promoting a `NeedsDrop` value silently erases its destructor side effect from `DropTrace`. -/
theorem ce_needsDrop_promotion_drops_side_effect :
    let dtorExpr : CandExpr := .adtWrap true false [(.int false 4, .litInt false 7)]
    validatePromotionCandidate .fnBody true false dtorExpr = false ∧
    evalParentBeforePromote true true dtorExpr = .returned 0 [1] ∧
    evalParentAfterPromote true true dtorExpr = .returned 0 [] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Witness 5: `200_u8 + 200_u8` in a dead branch (`uses = 2`, `keepOriginal = true`) promotes infallibly
under `overflowChecks = true` while keeping the overflow panic strictly in the dead branch. -/
theorem ce_addWithOverflow_dead_branch_keepOriginal_sound :
    let addExpr : CandExpr := .leaf (.checkedAddU8 200 200)
    validatePromotionCandidate .fnBody true false addExpr = true ∧
    ctfeEvalPromoted addExpr = .ok 144 ∧
    evalParentAfterPromote true false addExpr = .returned 0 [] ∧
    evalParentAfterPromote true true addExpr = .runtimePanic [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness 6: `deinitMovedPlace = true` (`Trusted.MirSemantics.lean`) allows repeated moves of `.unit`
(`sizeOf = 0`) while faulting on double-move of non-ZST storage (`usedTwice = true`). -/
theorem ce_non_zst_move_deinit_preserved :
    validatePromotionCandidate .fnBody true false (.leaf (.moveTemp (.int false 4) 9 true)) = false ∧
    ctfeEvalPromoted (.leaf (.moveTemp .unit 0 true)) = .ok 0 ∧
    ctfeEvalPromoted (.leaf (.moveTemp (.int false 4) 9 true)) = .uninitMoveFault := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Part 3: Byte-Range Borrow Permissions (Stacked Borrows & Tree Borrows) and 0-Byte ZST `&'static mut` Soundness -/

inductive AllocMut where
  | readOnly
  | mutable

abbrev Tag := Nat

inductive SbPerm where
  | unique
  | sharedReadWrite
  | sharedReadOnly

structure SbItem where
  tag : Tag
  perm : SbPerm
  isProtected : Bool

inductive TbPerm where
  | active
  | reserved (tyIsFreeze : Bool)
  | frozen
  | disabled

structure TbNode where
  tag : Tag
  perm : TbPerm
  isProtected : Bool

structure AllocState where
  size : Nat
  mutability : AllocMut
  sbStacks : List (List SbItem)
  tbNodes : List TbNode
  nextTag : Tag

inductive BorrowFault where
  | outOfBounds
  | writeToReadOnly
  | missingAlloc

inductive BorrowOutcome (α : Type) where
  | ok (val : α)
  | error (fault : BorrowFault)

/-- Exact model of `sb_reborrow` (`src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs:667-752`).
When `reborrowSize = 0` and `offset ≤ alloc.size`, returns immediately with a fresh tag without
updating any byte stack or checking `AllocMut.mutable`. -/
noncomputable def sbRetag
    (alloc : AllocState) (offset reborrowSize : Nat) (isMut protect : Bool) :
    BorrowOutcome (AllocState × Tag) :=
  if !Nat.ble (offset + reborrowSize) alloc.size then
    .error .outOfBounds
  else if reborrowSize == 0 then
    let newTag := alloc.nextTag
    .ok ({ alloc with nextTag := newTag + 1 }, newTag)
  else if isMut then
    match alloc.mutability with
    | .readOnly => .error .writeToReadOnly
    | .mutable =>
      let newTag := alloc.nextTag
      let item : SbItem := { tag := newTag, perm := .unique, isProtected := protect }
      let sbStacks' := alloc.sbStacks.map (fun st => item :: st)
      .ok ({ alloc with sbStacks := sbStacks', nextTag := newTag + 1 }, newTag)
  else
    let newTag := alloc.nextTag
    let item : SbItem := { tag := newTag, perm := .sharedReadOnly, isProtected := protect }
    let sbStacks' := alloc.sbStacks.map (fun st => item :: st)
    .ok ({ alloc with sbStacks := sbStacks', nextTag := newTag + 1 }, newTag)

/-- Exact model of `tb_reborrow` (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:274-425`).
When `reborrowSize = 0` (`DedupRangeMap` empty), zero write accesses are checked against
`get_alloc_mutability(alloc_id).is_not()` (`line 374-378`), so even a `StrongProtector` mutable
reborrow succeeds on `.readOnly` static memory. -/
noncomputable def tbRetag
    (alloc : AllocState) (offset reborrowSize : Nat) (isMut tyIsFreeze protect : Bool)
    (immediateWriteOnEntry : Bool) :
    BorrowOutcome (AllocState × Tag) :=
  if !Nat.ble (offset + reborrowSize) alloc.size then
    .error .outOfBounds
  else if reborrowSize == 0 then
    let newTag := alloc.nextTag
    let perm := if isMut then TbPerm.reserved tyIsFreeze else TbPerm.frozen
    let node : TbNode := { tag := newTag, perm := perm, isProtected := protect }
    .ok ({ alloc with tbNodes := node :: alloc.tbNodes, nextTag := newTag + 1 }, newTag)
  else if isMut && immediateWriteOnEntry then
    match alloc.mutability with
    | .readOnly => .error .writeToReadOnly
    | .mutable =>
      let newTag := alloc.nextTag
      let node : TbNode := { tag := newTag, perm := .active, isProtected := protect }
      .ok ({ alloc with tbNodes := node :: alloc.tbNodes, nextTag := newTag + 1 }, newTag)
  else
    let newTag := alloc.nextTag
    let perm := if isMut then TbPerm.reserved tyIsFreeze else TbPerm.frozen
    let node : TbNode := { tag := newTag, perm := perm, isProtected := protect }
    .ok ({ alloc with tbNodes := node :: alloc.tbNodes, nextTag := newTag + 1 }, newTag)

/-- Memory access permission check in both Stacked Borrows and Tree Borrows for nonzero byte width. -/
noncomputable def checkByteWrite (alloc : AllocState) (offset writeSize : Nat) :
    BorrowOutcome Unit :=
  if writeSize == 0 then
    if Nat.ble offset alloc.size then .ok () else .error .outOfBounds
  else if !Nat.ble (offset + writeSize) alloc.size then
    .error .outOfBounds
  else
    match alloc.mutability with
    | .readOnly => .error .writeToReadOnly
    | .mutable => .ok ()

/-- 0-byte `&'static mut` reborrow on read-only static memory succeeds in both SB and TB and preserves `sbStacks`. -/
theorem zst_mut_borrow_promoted_rodata_sound
    (alloc : AllocState) (hro : alloc.mutability = .readOnly)
    (offset : Nat) (hoff : Nat.ble offset alloc.size = true)
    (tyIsFreeze protect immediateWrite : Bool) :
    (∃ allocSb tSb,
      sbRetag alloc offset 0 true protect = .ok (allocSb, tSb) ∧
      allocSb.mutability = .readOnly ∧
      allocSb.sbStacks = alloc.sbStacks ∧
      tSb = alloc.nextTag) ∧
    (∃ allocTb tTb,
      tbRetag alloc offset 0 true tyIsFreeze protect immediateWrite = .ok (allocTb, tTb) ∧
      allocTb.mutability = .readOnly ∧
      tTb = alloc.nextTag) := by
  refine ⟨⟨{ alloc with nextTag := alloc.nextTag + 1 }, alloc.nextTag, ?_, hro, rfl, rfl⟩,
          ⟨{ alloc with tbNodes := { tag := alloc.nextTag, perm := .reserved tyIsFreeze, isProtected := protect } :: alloc.tbNodes,
                        nextTag := alloc.nextTag + 1 },
           alloc.nextTag, ?_, hro, rfl⟩⟩
  · dsimp only [sbRetag]; rw [Nat.add_zero, hoff]; rfl
  · dsimp only [tbRetag]; rw [Nat.add_zero, hoff]; rfl

/-- Two simultaneous `StrongProtector` (`FnEntry`) `&mut [u32]` reborrows on the same read-only 0-byte allocation succeed. -/
theorem dual_protected_zst_mut_borrows_rodata_sound
    (alloc : AllocState) (hro : alloc.mutability = .readOnly) :
    (∃ a1 a2 t1 t2,
      sbRetag alloc 0 0 true true = .ok (a1, t1) ∧
      sbRetag a1 0 0 true true = .ok (a2, t2) ∧
      t1 ≠ t2 ∧ a2.mutability = .readOnly) ∧
    (∃ b1 b2 u1 u2,
      tbRetag alloc 0 0 true true true true = .ok (b1, u1) ∧
      tbRetag b1 0 0 true true true true = .ok (b2, u2) ∧
      u1 ≠ u2 ∧ b2.mutability = .readOnly) := by
  have h0 : Nat.ble 0 alloc.size = true := by rfl
  have hne : alloc.nextTag ≠ alloc.nextTag + 1 := by
    intro h
    have hlt : alloc.nextTag < alloc.nextTag + 1 := Nat.lt_succ_self alloc.nextTag
    rw [← h] at hlt
    exact Nat.lt_irrefl alloc.nextTag hlt
  refine ⟨⟨{ alloc with nextTag := alloc.nextTag + 1 },
           { alloc with nextTag := alloc.nextTag + 2 },
           alloc.nextTag, alloc.nextTag + 1, ?_, ?_, hne, hro⟩,
          ⟨{ alloc with tbNodes := { tag := alloc.nextTag, perm := .reserved true, isProtected := true } :: alloc.tbNodes,
                        nextTag := alloc.nextTag + 1 },
           { alloc with tbNodes := { tag := alloc.nextTag + 1, perm := .reserved true, isProtected := true } ::
                                      { tag := alloc.nextTag, perm := .reserved true, isProtected := true } :: alloc.tbNodes,
                        nextTag := alloc.nextTag + 2 },
           alloc.nextTag, alloc.nextTag + 1, ?_, ?_, hne, hro⟩⟩
  · dsimp only [sbRetag]; rw [h0]; rfl
  · dsimp only [sbRetag]; rw [h0]; rfl
  · dsimp only [tbRetag]; rw [h0]; rfl
  · dsimp only [tbRetag]; rw [h0]; rfl

/-- Nonzero mutable reborrow (`size = n + 1`) on read-only promoted memory immediately causes `writeToReadOnly` UB. -/
theorem nonzst_mut_borrow_rodata_ub_counterexample
    (alloc : AllocState) (hro : alloc.mutability = .readOnly)
    (offset n : Nat) (hoff : Nat.ble (offset + (n + 1)) alloc.size = true)
    (tyIsFreeze protect : Bool) :
    sbRetag alloc offset (n + 1) true protect = .error .writeToReadOnly ∧
    tbRetag alloc offset (n + 1) true tyIsFreeze protect true = .error .writeToReadOnly := by
  have hne : (n + 1 == 0) = false := by rfl
  constructor
  · simp [sbRetag, hoff, hne, hro]
  · simp [tbRetag, hoff, hne, hro]

/-- Writing 4 bytes (`*a.as_mut_ptr() = 1`) through a 0-byte promoted `&'static mut [u32]` is `outOfBounds` UB. -/
theorem zst_mut_promoted_write_oob_ub (alloc : AllocState) (hsz : alloc.size = 0) :
    checkByteWrite alloc 0 4 = .error .outOfBounds := by
  simp [checkByteWrite, hsz]

/-- `Validator::validate_ref` accepts `&mut [T; 0]`, syntactically rejects `&mut ()` despite size `0`,
and `HasMutInterior` rejects `&UnsafeCell<()>` at size `0` while accepting `&Option::<UnsafeCell<()>>::None`. -/
theorem validateRef_mut_syntactic_conservatism_and_unsafecell_zst_witness :
    validatePromotionCandidate .fnBody true true (.leaf (.emptyArray (.int false 4))) = true ∧
    validatePromotionCandidate .fnBody true true (.leaf .litUnit) = false ∧
    (.unit : MirTy).sizeOf = 0 ∧
    validatePromotionCandidate .fnBody true false (.leaf .unsafeCellUnit) = false ∧
    (.unsafeCell .unit : MirTy).sizeOf = 0 ∧
    validatePromotionCandidate .fnBody true false (.optionNone (.unsafeCell .unit)) = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 4: `CheckConstItemMutation` Observational Equivalence Criterion & Asymmetry Witnesses -/

inductive ConstMutLint where
  | modify
  | mutBorrow

inductive ConstRefOp where
  | directFieldWrite (newVal : Nat)
  | mutBorrowMethodCall (newVal : Nat)
  | mutBorrowBlockWrite (newVal : Nat)
  | derefPtrEscapeWrite (newVal : Nat)
  | nop

/-- Operational model of a `LocalInfo::ConstRef` temporary statement (`check_const_item_mutation.rs`):
- Non-deref mutations mutate the temporary copy to `newVal` and run scope-exit drop logic,
  appending the final value to the observable trace iff `tyNeedsDrop ty = true`.
- `derefPtrEscapeWrite` writes through a dereferenced raw pointer outside the constant temporary,
  leaving the constant temporary at `initVal`. -/
noncomputable def execConstRefUsage
    (ty : MirTy) (initVal : Nat) (op : ConstRefOp) (log : List Nat) : List Nat :=
  let finalConstVal := match op with
    | .directFieldWrite v | .mutBorrowMethodCall v | .mutBorrowBlockWrite v => v
    | .derefPtrEscapeWrite _ | .nop => initVal
  if tyNeedsDrop ty then log ++ [finalConstVal] else log

noncomputable def opHasDeref : ConstRefOp → Bool
  | .derefPtrEscapeWrite _ => true
  | _ => false

noncomputable def opIsAssignment : ConstRefOp → Bool
  | .directFieldWrite _ => true
  | _ => false

noncomputable def opIsMutBorrow : ConstRefOp → Bool
  | .mutBorrowMethodCall _ | .mutBorrowBlockWrite _ => true
  | _ => false

/-- `rustc 1.98.0-nightly` (`14210df0e2`): `visit_statement` checks `adt.has_dtor`, while `visit_rvalue`
checks `is_const_item` without checking destructors at all (`check_const_item_mutation.rs:59, 97, 134`). -/
noncomputable def lintRustc198 (ty : MirTy) (op : ConstRefOp) : Option ConstMutLint :=
  if opHasDeref op then none
  else if opIsAssignment op then
    let hasDtor := match ty with | .adt hd _ _ => hd | _ => false
    if hasDtor then none else some .modify
  else if opIsMutBorrow op then
    some .mutBorrow
  else none

/-- `rustc 1.102.0-nightly` (`3ef0c22cdb`, post-`940498dad7cb`): `visit_statement` upgrades to
`ty.has_param() || !ty.needs_drop()`, while `visit_rvalue` still calls `is_const_item` unconditionally! -/
noncomputable def lintRustc1102 (ty : MirTy) (op : ConstRefOp) : Option ConstMutLint :=
  if opHasDeref op then none
  else if opIsAssignment op then
    if tyNeedsDrop ty then none else some .modify
  else if opIsMutBorrow op then
    some .mutBorrow
  else none

/-- Symmetric `needs_drop`-aware repair applying `is_const_item_without_destructor` in both
`visit_statement` and `visit_rvalue` (when concrete, i.e., `hasParam = false`). -/
noncomputable def lintRepaired (ty : MirTy) (op : ConstRefOp) : Option ConstMutLint :=
  if opHasDeref op then none
  else if tyNeedsDrop ty then none
  else if opIsAssignment op then some .modify
  else if opIsMutBorrow op then some .mutBorrow
  else none

theorem list_append_single_eq (xs : List Nat) (a b : Nat) :
    xs ++ [a] = xs ++ [b] → a = b := by
  induction xs with
  | nil =>
    intro h
    injection h with h1
  | cons x rest ih =>
    intro h
    injection h with _ hrest
    exact ih hrest

/-- Observational equivalence criterion: a non-deref mutation on a `const` temporary is
unobservable (`execConstRefUsage ty initVal op log = execConstRefUsage ty initVal .nop log`
for all `initVal`, `newVal`, `log`) if and only if `tyNeedsDrop ty = false`.
Holds symmetrically for `directFieldWrite`, `mutBorrowMethodCall`, and `mutBorrowBlockWrite`. -/
theorem constMutation_unobservable_iff_no_needsDrop
    (ty : MirTy)
    (mkOp : Nat → ConstRefOp)
    (hmk : (∀ v, mkOp v = .directFieldWrite v) ∨
           (∀ v, mkOp v = .mutBorrowMethodCall v) ∨
           (∀ v, mkOp v = .mutBorrowBlockWrite v)) :
    (∀ initVal newVal log,
      execConstRefUsage ty initVal (mkOp newVal) log =
      execConstRefUsage ty initVal .nop log) ↔
      tyNeedsDrop ty = false := by
  constructor
  · intro heq
    have h0 := heq 0 1 []
    cases hnd : tyNeedsDrop ty with
    | false => rfl
    | true =>
      rcases hmk with hf | hm | hb
      · rw [hf 1] at h0
        simp [execConstRefUsage, hnd] at h0
      · rw [hm 1] at h0
        simp [execConstRefUsage, hnd] at h0
      · rw [hb 1] at h0
        simp [execConstRefUsage, hnd] at h0
  · intro hnd initVal newVal log
    rcases hmk with hf | hm | hb
    · rw [hf newVal]; simp [execConstRefUsage, hnd]
    · rw [hm newVal]; simp [execConstRefUsage, hnd]
    · rw [hb newVal]; simp [execConstRefUsage, hnd]

noncomputable def dropLoggerTy : MirTy := .adt true false [.int false 4]
noncomputable def innerDropTy : MirTy := .adt true false [.int false 4]
noncomputable def outerNestedDropTy : MirTy := .adt false false [innerDropTy]

/-- Concrete witness of the `CheckConstItemMutation` `visit_rvalue` false-positive asymmetry
on `C_DIRECT : DropLogger`, reproducing `OBSERVED_DROPS = 75` (`10 + 15 + 50`). -/
theorem checkConstItemMutation_visitRvalue_false_positive_witness :
    tyNeedsDrop dropLoggerTy = true ∧
    lintRustc1102 dropLoggerTy (.directFieldWrite 10) = none ∧
    lintRustc1102 dropLoggerTy (.mutBorrowMethodCall 15) = some .mutBorrow ∧
    lintRustc1102 dropLoggerTy (.mutBorrowBlockWrite 50) = some .mutBorrow ∧
    lintRustc1102 dropLoggerTy (.derefPtrEscapeWrite 7) = none ∧
    execConstRefUsage dropLoggerTy 0 (.directFieldWrite 10) [] ≠
      execConstRefUsage dropLoggerTy 0 .nop [] ∧
    execConstRefUsage dropLoggerTy 0 (.mutBorrowMethodCall 15) [] ≠
      execConstRefUsage dropLoggerTy 0 .nop [] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> (intro h; cases h)

theorem observed_drops_sum_eq_75 :
    let log1 := execConstRefUsage dropLoggerTy 0 (.directFieldWrite 10) []
    let log2 := execConstRefUsage dropLoggerTy 0 (.mutBorrowMethodCall 15) log1
    let log3 := execConstRefUsage dropLoggerTy 0 (.directFieldWrite 50) log2
    log3 = [10, 15, 50] ∧ sumList log3 = 75 := by
  exact ⟨rfl, rfl⟩

/-- Cross-version witness on `Outer { inner : Inner }` (`hasDtor = false`, `needsDrop = true`):
`rustc 1.98.0` falsely warns on `O.inner.val = 42`, `rustc 1.102.0` (`940498dad7cb`) suppresses
`O.inner.val = 42`, yet `rustc 1.102.0` still falsely warns on `O.set_inner(42)`! -/
theorem checkConstItemMutation_nestedDrop_198_vs_1102_witness :
    tyNeedsDrop outerNestedDropTy = true ∧
    lintRustc198 outerNestedDropTy (.directFieldWrite 42) = some .modify ∧
    lintRustc1102 outerNestedDropTy (.directFieldWrite 42) = none ∧
    lintRustc1102 outerNestedDropTy (.mutBorrowMethodCall 42) = some .mutBorrow := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `lintRepaired` warns on non-deref mutations if and only if the mutation is observationally unobservable. -/
theorem lintRepaired_exact_soundness_and_completeness
    (ty : MirTy) (op : ConstRefOp) (hderef : opHasDeref op = false) (hnop : op ≠ .nop) :
    (lintRepaired ty op).isSome = true ↔
    (∀ initVal log, execConstRefUsage ty initVal op log = execConstRefUsage ty initVal .nop log) := by
  cases op with
  | derefPtrEscapeWrite _ => cases hderef
  | nop => cases hnop rfl
  | directFieldWrite v =>
    cases hnd : tyNeedsDrop ty with
    | true =>
      constructor
      · intro h; dsimp only [lintRepaired, opHasDeref] at h; rw [hnd] at h; cases h
      · intro heq
        have h0 := heq (v + 1) []
        dsimp only [execConstRefUsage] at h0
        rw [hnd] at h0
        have heq_v := list_append_single_eq [] v (v + 1) h0
        have hlt : v < v + 1 := Nat.lt_succ_self v
        rw [← heq_v] at hlt
        exact False.elim (Nat.lt_irrefl v hlt)
    | false =>
      constructor
      · intro _ initVal log; dsimp only [execConstRefUsage]; rw [hnd]; rfl
      · intro _; dsimp only [lintRepaired, opHasDeref, opIsAssignment]; rw [hnd]; rfl
  | mutBorrowMethodCall v =>
    cases hnd : tyNeedsDrop ty with
    | true =>
      constructor
      · intro h; dsimp only [lintRepaired, opHasDeref] at h; rw [hnd] at h; cases h
      · intro heq
        have h0 := heq (v + 1) []
        dsimp only [execConstRefUsage] at h0
        rw [hnd] at h0
        have heq_v := list_append_single_eq [] v (v + 1) h0
        have hlt : v < v + 1 := Nat.lt_succ_self v
        rw [← heq_v] at hlt
        exact False.elim (Nat.lt_irrefl v hlt)
    | false =>
      constructor
      · intro _ initVal log; dsimp only [execConstRefUsage]; rw [hnd]; rfl
      · intro _; dsimp only [lintRepaired, opHasDeref, opIsAssignment, opIsMutBorrow]; rw [hnd]; rfl
  | mutBorrowBlockWrite v =>
    cases hnd : tyNeedsDrop ty with
    | true =>
      constructor
      · intro h; dsimp only [lintRepaired, opHasDeref] at h; rw [hnd] at h; cases h
      · intro heq
        have h0 := heq (v + 1) []
        dsimp only [execConstRefUsage] at h0
        rw [hnd] at h0
        have heq_v := list_append_single_eq [] v (v + 1) h0
        have hlt : v < v + 1 := Nat.lt_succ_self v
        rw [← heq_v] at hlt
        exact False.elim (Nat.lt_irrefl v hlt)
    | false =>
      constructor
      · intro _ initVal log; dsimp only [execConstRefUsage]; rw [hnd]; rfl
      · intro _; dsimp only [lintRepaired, opHasDeref, opIsAssignment, opIsMutBorrow]; rw [hnd]; rfl

end PromoteTempsSoundness
