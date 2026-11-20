/-
  F1-2 Statement-First Compiler Formalization (Stage 2 Revised, Ready to Freeze)
  Target Theorem Family: `MirTreeBorrows_PartialSroa_Unwind_Refinement`

  Anchored in `stage0_adversarial_epistemic_audit.md` (`SEAM-6`, `F1-2`, closing audited gaps
  `C17 (N8-N10)`, `C43 (L2_)`, `C44 (L5_, L6_)`, `C45 (L7_)`) and Villani et al. (PLDI 2025)
  Tree Borrows semantics (`tree_borrows/perms.rs`, `PermissionPriv::Cell` for `&UnsafeCell<T>`,
  sub-place `outside_perm (accessed = false)`, `ReservedFrz` vs. `ReservedIM` under protectors,
  and call-scoped protectors released on both normal return and unwind).

  What this statement module formalizes (`namespace VrustcFormal.F1_2`):
    1. Core MIR with stack/heap struct allocations (`fields : List FieldMeta`), per-field
       `isUnsafeCell : Bool`, `val : UInt64`, Tree Borrows permissions (`cell`/`reserved`/
       `active`/`frozen`/`disabled`), call-scoped `protector : Option CallId` on child borrow
       tags, sub-place `TakeFieldPtr`, `&s` `TakeRootSharedRef`, `&raw mut s` `TakeRootRawPtr`,
       `PtrOffset` (`container_of!`), `CallMayUnwind`, `LandingPad`, `Resume`, `CatchUnwind`,
       and `PanicMode` (`unwind` vs `abort`).
    2. Optimization A (`PartialSroaCert`):
       - `.fullSplit`: promotes a non-escaping `Freeze` (`!isUnsafeCell`), non-root-raw-aliased
         field completely into an SSA register while leaving escaping or `UnsafeCell` sibling
         fields in memory.
       - `.sharedReadPromote`: write-through scalar promotion of a `Freeze`, non-root-raw-aliased,
         non-mutably-escaped field across `&T` / `&s` shared-borrow calls (including hybrid
         structs with `UnsafeCell` siblings mutated across multiple calls / aliased `&s` refs).
    3. Optimization B (`StoreSinkToCleanupCert`):
       - Sinks an overwritten store `s.f = v1` across a potentially-unwinding call (with
         normal-path overwrite `s.f = v2`) into the unique-predecessor unwind `cleanup` pad,
         when `s.f` is unobserved by the unwinding callee (conservatively requiring `Freeze` +
         zero pointers to `(alloc, field)`).
    4. Profile Subsumption (`UnwindToAbortCert`):
       - Proves `panic=abort` refines `panic=unwind` (exact normal-return equivalence,
         trace-and-payload-preserving panic subsumption, no-recovery, and zero new errors/UB)
         ONLY under `noCatchUnwind = true` and side-effect-free cleanup pads.
    5. Non-vacuity positive canaries (4, including multi-call & aliased `&s` hybrid `UnsafeCell`
       structs and post-protector-release `&mut` activation) and kernel-checked sharpness
       counterexamples (4 mandatory + 4 Tree Borrows / unwind witnesses).

  Explicit Scope Boundaries vs. Full `Trusted.MirSemantics.lean` / Full Miri Tree Borrows:
    - Uses a 2-level borrow tree (allocation root tag `0` plus derived child tags `≥ 1`)
      over zero-initialized `UInt64` struct fields (not `MaybeUninit` byte poison) and scripted
      non-recursive external callees (`CalleeBody`), rather than arbitrary-depth borrow trees,
      raw byte-level memory, or recursive MIR calls.
    - Function-entry call retagging activates a protector on each argument's existing borrow
      tag rather than creating fresh child reborrows per duplicate `PtrRegId` argument; passing
      duplicate `&mut` register IDs `[r, r]` is outside the modeled retag scope.
    - `takeFieldPtr ... .rawMut` / `takeRootRawPtr` conservatively execute an implicit root
      read at tag creation (stronger than Miri's raw-pointer creation, which omits that read).
    - `MirBody` takes scalar `initArgs : List UInt64` (no incoming external mutable references
      or statics), so local `writeField`/`writePtr` mutations inside cleanup pads are discarded
      on unwind and treated as side-effect-free under `UnwindToAbortCert`; `UnwindToAbortCert`
      does not enforce cleanup-pad well-formedness or termination (`panic=abort` skips cleanup).
    - Uses `namespace VrustcFormal.F1_2` (NEVER shadows `namespace Trusted`).
    - Zero imports, zero `bv_decide`, zero `native_decide`, zero `partial`, zero `@[extern]`,
      zero `unsafe`, zero `opaque`, zero `axiom`.
-/

namespace VrustcFormal.F1_2

/-! ### Core Identifiers & List Utilities -/

abbrev AllocId  := Nat
abbrev FieldIdx := Nat
abbrev TagId    := Nat
abbrev CallId   := Nat
abbrev ValRegId := Nat
abbrev PtrRegId := Nat
abbrev BlockId  := Nat
abbrev CalleeId := Nat

def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

def setAt? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v => (setAt? xs n v).map (x :: ·)

def splitAtIdx? {α : Type} : List α → Nat → Option (List α × α × List α)
  | [], _ => none
  | x :: xs, 0 => some ([], x, xs)
  | x :: xs, n + 1 =>
    (splitAtIdx? xs n).map fun (pre, elem, post) => (x :: pre, elem, post)

/-! ### Tree Borrows Permissions, Borrow Nodes & Per-Field Struct Allocations -/

/-- Tree Borrows permission state (matching Miri `tree_borrows/perms.rs`).
- `cell`: shared `&UnsafeCell<T>` (`PermissionPriv::Cell`): permits all child and foreign
  reads/writes and never activates to `active`.
- `reserved conflicted`: two-phase `&mut` or raw pointer before write. `conflicted = true`
  marks a protected `reserved` tag that witnessed a foreign read; a child write WHILE protected
  triggers UB, whereas after protector release child writes activate to `active`.
- `active`: unique writable permission after a child write.
- `frozen`: read-only permission (`&T` on `Freeze` fields, or unprotected `active` after foreign read).
- `disabled`: invalidated by a foreign write; any subsequent child access is UB. -/
inductive TbPerm where
  | cell
  | reserved (conflicted : Bool)
  | active
  | frozen
  | disabled
  deriving DecidableEq, Repr

/-- Borrow / pointer creation kind. -/
inductive BorrowKind where
  | shared  -- `&T`: `frozen` on Freeze fields, `cell` on `UnsafeCell` fields; protected in calls
  | mutRef  -- `&mut T`: `reserved false`; transitions to `active` on write; protected in calls
  | rawMut  -- `*mut T` (`&raw mut`): `reserved false`; NOT protected in calls
  deriving DecidableEq, Repr

/-- Pointer provenance scope:
- `fieldOnly f`: single-field borrow with `outside_perm (accessed = false)` on sibling fields.
- `wholeStruct`: root borrow/raw-pointer provenance spanning all fields (enables `container_of!`). -/
inductive PtrScope where
  | fieldOnly (f : FieldIdx)
  | wholeStruct
  deriving DecidableEq, Repr

/-- Runtime pointer value with explicit field cursor, provenance scope, kind, and Tree Borrows tag. -/
structure PtrVal where
  allocId : AllocId
  field   : FieldIdx
  scope   : PtrScope
  kind    : BorrowKind
  tag     : TagId
  deriving DecidableEq, Repr

/-- A derived borrow tag node attached to a field (child of root tag `0`). -/
structure BorrowNode where
  tag       : TagId
  perm      : TbPerm
  protector : Option CallId
  deriving DecidableEq, Repr

/-- Per-field metadata in a struct allocation: `UnsafeCell` flag, current `UInt64` value,
root-owner Tree Borrows permission, plus derived child borrow tags. -/
structure FieldMeta where
  isUnsafeCell : Bool
  val          : UInt64
  perm         : TbPerm
  children     : List BorrowNode
  deriving DecidableEq, Repr

/-- Heap/stack struct allocation tracking per-field Tree Borrows state. -/
structure StructAlloc where
  fields : List FieldMeta
  deriving DecidableEq, Repr

/-- Static declaration of a struct allocation's fields (`isUnsafeCell` flag per field). -/
structure StructDecl where
  fieldUnsafeCell : List Bool
  deriving DecidableEq, Repr

def initFieldMeta (isUnsafeCell : Bool) : FieldMeta :=
  { isUnsafeCell := isUnsafeCell
  , val := 0
  , perm := .reserved false
  , children := [] }

def initHeap (decls : List StructDecl) : List StructAlloc :=
  decls.map fun d =>
    { fields := d.fieldUnsafeCell.map initFieldMeta }

/-! ### Tree Borrows State Transitions -/

inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- Initial Tree Borrows permission for a newly created borrow tag on a field.
Matches Miri `tree_borrows/perms.rs`: `.shared` (`&T`) yields `.frozen` on `Freeze` fields
and `.cell` (`PermissionPriv::Cell`) on `UnsafeCell` fields. -/
def initialBorrowPerm (isUnsafeCell : Bool) : BorrowKind → TbPerm
  | .shared => if isUnsafeCell then .cell else .frozen
  | .mutRef => .reserved false
  | .rawMut => .reserved false

/-- Tree Borrows CHILD access transition (`none` = UB).
Matches Miri `child_write(state, protected)`: `reserved true` rejects writes ONLY while
`isProtected = true`; once the protector is released, a child write activates to `.active`. -/
def tbChildStep (isProtected : Bool) (acc : AccessKind) (perm : TbPerm) : Option TbPerm :=
  match acc, perm with
  | _,      .cell           => some .cell
  | .read,  .reserved c     => some (.reserved c)
  | .read,  .active         => some .active
  | .read,  .frozen         => some .frozen
  | .read,  .disabled       => none
  | .write, .reserved false => some .active
  | .write, .reserved true  => if isProtected then none else some .active
  | .write, .active         => some .active
  | .write, .frozen         => none
  | .write, .disabled       => none

/-- Tree Borrows FOREIGN access transition (`none` = protector UB).
Matches Miri `tree_borrows/perms.rs`:
- `.cell` (`&UnsafeCell<T>`) is immune to all foreign reads/writes even when protected.
- Protected `.reserved` (`&mut T`, including `&mut UnsafeCell<T>`) uses `ReservedFrz`
  semantics (`isProtected` checked BEFORE `isUnsafeCell`): foreign reads mark `conflicted := true`,
  and foreign writes trigger immediate protector UB (`none`).
- Unprotected `.reserved` on `UnsafeCell` (`ReservedIM`) ignores foreign writes before activation. -/
def tbForeignStep (isUnsafeCell : Bool) (isProtected : Bool)
    (acc : AccessKind) (perm : TbPerm) : Option TbPerm :=
  match acc, perm with
  | _, .cell => some .cell
  | .read, .reserved c =>
    if isProtected then some (.reserved true)
    else some (.reserved c)
  | .read, .active =>
    if isProtected then none
    else some .frozen
  | .read, .frozen   => some .frozen
  | .read, .disabled => some .disabled
  | .write, .reserved c =>
    if isProtected then none
    else if isUnsafeCell then some (.reserved c)
    else some .disabled
  | .write, .active =>
    if isProtected then none
    else some .disabled
  | .write, .frozen =>
    if isProtected then none
    else some .disabled
  | .write, .disabled => some .disabled

/-- Sub-place provenance check (`outside_perm (accessed = false)` on siblings). -/
def ptrInScope (p : PtrVal) : Bool :=
  match p.scope with
  | .wholeStruct => true
  | .fieldOnly f => p.field == f

def stepForeignChildren (isUnsafeCell : Bool) (acc : AccessKind) :
    List BorrowNode → Option (List BorrowNode)
  | [] => some []
  | n :: rest =>
    match tbForeignStep isUnsafeCell n.protector.isSome acc n.perm,
          stepForeignChildren isUnsafeCell acc rest with
    | some perm', some rest' => some ({ n with perm := perm' } :: rest')
    | _, _ => none

/-- Step child nodes for an access performed through child tag `accTag`.
Returns `(updatedChildren, foundTargetTag)`. -/
def stepTagChildren (isUnsafeCell : Bool) (acc : AccessKind) (accTag : TagId) :
    List BorrowNode → Option (List BorrowNode × Bool)
  | [] => some ([], false)
  | n :: rest =>
    if n.tag == accTag then
      match tbChildStep n.protector.isSome acc n.perm, stepTagChildren isUnsafeCell acc accTag rest with
      | some perm', some (rest', _) => some ({ n with perm := perm' } :: rest', true)
      | _, _ => none
    else
      match tbForeignStep isUnsafeCell n.protector.isSome acc n.perm,
            stepTagChildren isUnsafeCell acc accTag rest with
      | some perm', some (rest', found) => some ({ n with perm := perm' } :: rest', found)
      | _, _ => none

/-- Direct owner-root (tag `0`) access on a single field. -/
def tbRootAccessField (acc : AccessKind) (newVal : Option UInt64) (fm : FieldMeta) :
    Option FieldMeta :=
  match tbChildStep false acc fm.perm, stepForeignChildren fm.isUnsafeCell acc fm.children with
  | some perm', some children' =>
    some { fm with
      val := newVal.getD fm.val
      perm := perm'
      children := children' }
  | _, _ => none

/-- Derived-pointer (tag `t ≥ 1`) access on a single field (parent root `0` gets child step;
target tag gets child step; sibling tags get foreign step). -/
def tbPtrAccessField (acc : AccessKind) (accTag : TagId) (newVal : Option UInt64) (fm : FieldMeta) :
    Option FieldMeta :=
  match tbChildStep false acc fm.perm, stepTagChildren fm.isUnsafeCell acc accTag fm.children with
  | some perm', some (children', true) =>
    some { fm with
      val := newVal.getD fm.val
      perm := perm'
      children := children' }
  | _, _ => none

/-- Retag a field when creating a new derived borrow tag (performs implicit read on root + foreign
read on existing children, then appends the new `BorrowNode`). -/
def tbRetagField (tag : TagId) (kind : BorrowKind) (fm : FieldMeta) : Option FieldMeta :=
  match tbRootAccessField .read none fm with
  | none => none
  | some fm1 =>
    let node : BorrowNode :=
      { tag := tag
      , perm := initialBorrowPerm fm1.isUnsafeCell kind
      , protector := none }
    some { fm1 with children := fm1.children ++ [node] }

def tbRetagAllFields (tag : TagId) (kind : BorrowKind) :
    List FieldMeta → Option (List FieldMeta)
  | [] => some []
  | fm :: rest =>
    match tbRetagField tag kind fm, tbRetagAllFields tag kind rest with
    | some fm', some rest' => some (fm' :: rest')
    | _, _ => none

/-- Activate a Tree Borrows protector `callId` on `tag` within a field (`none` if tag is missing
or already `disabled`). -/
def activateProtectorNodes (tag : TagId) (callId : CallId) :
    List BorrowNode → Option (List BorrowNode × Bool)
  | [] => some ([], false)
  | n :: rest =>
    if n.tag == tag then
      if n.perm == .disabled then none
      else
        (activateProtectorNodes tag callId rest).map fun (rest', _) =>
          ({ n with protector := some callId } :: rest', true)
    else
      (activateProtectorNodes tag callId rest).map fun (rest', found) =>
        (n :: rest', found)

def activateProtectorField (tag : TagId) (callId : CallId) (fm : FieldMeta) : Option FieldMeta :=
  match activateProtectorNodes tag callId fm.children with
  | some (children', true) => some { fm with children := children' }
  | _ => none

def activateProtectorAllFields (tag : TagId) (callId : CallId) :
    List FieldMeta → Option (List FieldMeta)
  | [] => some []
  | fm :: rest =>
    match activateProtectorField tag callId fm, activateProtectorAllFields tag callId rest with
    | some fm', some rest' => some (fm' :: rest')
    | _, _ => none

/-- Release protector `callId` across the entire heap (executed on BOTH normal return and unwind). -/
def releaseProtectorField (callId : CallId) (fm : FieldMeta) : FieldMeta :=
  { fm with
    children := fm.children.map fun n =>
      if n.protector == some callId then { n with protector := none } else n }

def releaseProtectorHeap (callId : CallId) (heap : List StructAlloc) : List StructAlloc :=
  heap.map fun sa => { sa with fields := sa.fields.map (releaseProtectorField callId) }

/-! ### Core MIR Syntax, External Callees & Panic Modes -/

inductive BinOp where
  | add | sub | xor
  deriving DecidableEq, Repr

def evalBinOp (op : BinOp) (a b : UInt64) : UInt64 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .xor => a ^^^ b

inductive ValOp where
  | constU64 (k : UInt64)
  | reg (r : ValRegId)
  deriving DecidableEq, Repr

inductive MirStmt where
  | assignReg        (dst : ValRegId) (v : ValOp)
  | binOp            (dst : ValRegId) (op : BinOp) (lhs rhs : ValOp)
  | readField        (dst : ValRegId) (alloc : AllocId) (field : FieldIdx)
  | writeField       (alloc : AllocId) (field : FieldIdx) (v : ValOp)
  | readPtr          (dst : ValRegId) (ptr : PtrRegId)
  | writePtr         (ptr : PtrRegId) (v : ValOp)
  | takeFieldPtr     (dst : PtrRegId) (alloc : AllocId) (field : FieldIdx) (kind : BorrowKind)
  | takeRootSharedRef (dst : PtrRegId) (alloc : AllocId)
  | takeRootRawPtr   (dst : PtrRegId) (alloc : AllocId)
  | ptrOffset        (dst : PtrRegId) (src : PtrRegId) (targetField : FieldIdx)
  | emitObs          (v : ValOp)
  | landingPad       (dst : Option ValRegId)
  deriving DecidableEq, Repr

inductive MirTerm where
  | goto          (target : BlockId)
  | switchZero    (discr : ValOp) (zeroTarget nonZeroTarget : BlockId)
  | callMayUnwind (callee : CalleeId) (argPtrs : List PtrRegId)
                  (retDst : Option ValRegId) (normalTarget cleanupTarget : BlockId)
  | resume
  | catchUnwind   (payloadDst : Option ValRegId) (recoverTarget : BlockId)
  | ret           (v : ValOp)
  deriving DecidableEq, Repr

structure MirBlock where
  stmts : List MirStmt
  term  : MirTerm
  deriving DecidableEq, Repr

structure MirBody where
  allocDecls : List StructDecl
  blocks     : List MirBlock
  deriving DecidableEq, Repr

/-- External callee atomic operations (operating exclusively on passed pointer arguments). -/
inductive CalleeOp where
  | readArg   (ptrIdx : Nat) (offsetField : Option FieldIdx) (emitLog : Bool)
  | writeArg  (ptrIdx : Nat) (offsetField : Option FieldIdx) (v : UInt64)
  | emitEvent (code : UInt64)
  deriving DecidableEq, Repr

inductive CalleeExit where
  | normal (retVal : UInt64)
  | panic  (payload : UInt64)
  deriving DecidableEq, Repr

structure CalleeBody where
  ops  : List CalleeOp
  exit : CalleeExit
  deriving DecidableEq, Repr

abbrev CalleeEnv := CalleeId → Option CalleeBody

/-- Rust compilation panic strategy (`-C panic=unwind` vs `-C panic=abort`). -/
inductive PanicMode where
  | unwind
  | abort
  deriving DecidableEq, Repr

/-! ### Operational Semantics & Trace Refinement -/

inductive FaultKind where
  | tbUb        -- Tree Borrows / provenance / uninitialized-register undefined behavior
  | unsupported -- malformed IR (OOB block/alloc/field, missing callee, bad landingPad/resume/ret)
  deriving DecidableEq, Repr

inductive ObsEvent where
  | mirObs     (code : UInt64)
  | calleeRead (val : UInt64)
  | calleeIo   (code : UInt64)
  deriving DecidableEq, Repr

inductive ExecOutcome where
  | ret       (v : UInt64)
  | unwound   (payload : UInt64)
  | aborted   (payload : UInt64)
  | outOfFuel
  deriving DecidableEq, Repr

abbrev ExecResult := Except FaultKind (List ObsEvent × ExecOutcome)

/-- Standard compiler trace refinement: source UB refines any target behavior; non-UB source
executions must be matched identically by the target with zero new Tree Borrows UB. -/
def refines (srcRes tgtRes : ExecResult) : Prop :=
  match srcRes with
  | .error .tbUb => True
  | _ => tgtRes = srcRes

inductive UnwindState where
  | normal
  | enteringCleanup (payload : UInt64)
  | inCleanup       (payload : UInt64)
  deriving DecidableEq, Repr

abbrev ValRegEnv := ValRegId → Option UInt64
abbrev PtrRegEnv := PtrRegId → Option PtrVal

structure ExecState where
  heap        : List StructAlloc
  valRegs     : ValRegEnv
  ptrRegs     : PtrRegEnv
  nextTag     : TagId
  nextCallId  : CallId
  trace       : List ObsEvent
  unwindState : UnwindState

def bindValReg (env : ValRegEnv) (r : ValRegId) (v : UInt64) : ValRegEnv :=
  fun x => if x == r then some v else env x

def bindOptValReg (env : ValRegEnv) : Option ValRegId → UInt64 → ValRegEnv
  | none, _ => env
  | some r, v => bindValReg env r v

def bindPtrReg (env : PtrRegEnv) (r : PtrRegId) (p : PtrVal) : PtrRegEnv :=
  fun x => if x == r then some p else env x

def initValRegsAux (idx : Nat) : List UInt64 → ValRegEnv
  | [] => fun _ => none
  | v :: vs => bindValReg (initValRegsAux (idx + 1) vs) idx v

def initState (body : MirBody) (initArgs : List UInt64) : ExecState :=
  { heap := initHeap body.allocDecls
  , valRegs := initValRegsAux 0 initArgs
  , ptrRegs := fun _ => none
  , nextTag := 1
  , nextCallId := 0
  , trace := []
  , unwindState := .normal }

def evalValOp (regs : ValRegEnv) : ValOp → Except FaultKind UInt64
  | .constU64 k => .ok k
  | .reg r =>
    match regs r with
    | some v => .ok v
    | none => .error .tbUb

def applyPtrOffset (p : PtrVal) : Option FieldIdx → PtrVal
  | none => p
  | some f => { p with field := f }

/-- Perform a pointer read/write on the heap, checking `ptrInScope` (`outside_perm`),
bounds, and full Tree Borrows child/foreign transitions. -/
def accessHeapByPtr (heap : List StructAlloc) (p : PtrVal) (acc : AccessKind)
    (newVal : Option UInt64) : Except FaultKind (UInt64 × List StructAlloc) :=
  if !ptrInScope p then
    .error .tbUb
  else
    match getAt? heap p.allocId with
    | none => .error .tbUb
    | some sa =>
      match getAt? sa.fields p.field with
      | none => .error .tbUb
      | some fm =>
        match tbPtrAccessField acc p.tag newVal fm with
        | none => .error .tbUb
        | some fm' =>
          match setAt? sa.fields p.field fm' with
          | none => .error .unsupported
          | some fields' =>
            match setAt? heap p.allocId { sa with fields := fields' } with
            | none => .error .unsupported
            | some heap' => .ok (fm'.val, heap')

def evalArgPtrs (ptrRegs : PtrRegEnv) : List PtrRegId → Except FaultKind (List PtrVal)
  | [] => .ok []
  | r :: rs =>
    match ptrRegs r, evalArgPtrs ptrRegs rs with
    | some p, .ok ps => .ok (p :: ps)
    | none, _ => .error .tbUb
    | _, .error e => .error e

/-- Activate Tree Borrows protectors for `.shared` and `.mutRef` call arguments (`.rawMut`
pointers are unprotected in Rust/Tree Borrows). -/
def activateProtectorOne (callId : CallId) (heap : List StructAlloc) (p : PtrVal) :
    Except FaultKind (List StructAlloc) :=
  match p.kind with
  | .rawMut => .ok heap
  | .shared | .mutRef =>
    if !ptrInScope p then .error .tbUb
    else
      match getAt? heap p.allocId with
      | none => .error .tbUb
      | some sa =>
        match p.scope with
        | .wholeStruct =>
          match activateProtectorAllFields p.tag callId sa.fields with
          | none => .error .tbUb
          | some fields' =>
            match setAt? heap p.allocId { sa with fields := fields' } with
            | none => .error .unsupported
            | some heap' => .ok heap'
        | .fieldOnly f =>
          match getAt? sa.fields f with
          | none => .error .tbUb
          | some fm =>
            match activateProtectorField p.tag callId fm with
            | none => .error .tbUb
            | some fm' =>
              match setAt? sa.fields f fm' with
              | none => .error .unsupported
              | some fields' =>
                match setAt? heap p.allocId { sa with fields := fields' } with
                | none => .error .unsupported
                | some heap' => .ok heap'

def activateProtectors (callId : CallId) (heap : List StructAlloc) :
    List PtrVal → Except FaultKind (List StructAlloc)
  | [] => .ok heap
  | p :: ps =>
    match activateProtectorOne callId heap p with
    | .error e => .error e
    | .ok heap' => activateProtectors callId heap' ps

def stepCalleeOps (args : List PtrVal) (heap : List StructAlloc) (trace : List ObsEvent) :
    List CalleeOp → Except FaultKind (List StructAlloc × List ObsEvent)
  | [] => .ok (heap, trace)
  | .emitEvent code :: rest =>
    stepCalleeOps args heap (trace ++ [.calleeIo code]) rest
  | .readArg idx off emitLog :: rest =>
    match getAt? args idx with
    | none => .error .unsupported
    | some p =>
      match accessHeapByPtr heap (applyPtrOffset p off) .read none with
      | .error e => .error e
      | .ok (v, heap') =>
        let trace' := if emitLog then trace ++ [.calleeRead v] else trace
        stepCalleeOps args heap' trace' rest
  | .writeArg idx off v :: rest =>
    match getAt? args idx with
    | none => .error .unsupported
    | some p =>
      match accessHeapByPtr heap (applyPtrOffset p off) .write (some v) with
      | .error e => .error e
      | .ok (_, heap') => stepCalleeOps args heap' trace rest

/-- Execute a single MIR statement. Every non-`landingPad` statement rejects `.enteringCleanup`
(matching MIR/LLVM's rule that `LandingPad` must open an unwind pad). -/
def stepMirStmt (st : ExecState) (stmt : MirStmt) : Except FaultKind ExecState :=
  match stmt with
  | .landingPad dst =>
    match st.unwindState with
    | .enteringCleanup payload =>
      .ok { st with
        unwindState := .inCleanup payload
        valRegs := bindOptValReg st.valRegs dst payload }
    | _ => .error .unsupported
  | _ =>
    match st.unwindState with
    | .enteringCleanup _ => .error .unsupported
    | _ =>
      match stmt with
      | .landingPad _ => .error .unsupported
      | .assignReg dst op =>
        match evalValOp st.valRegs op with
        | .error e => .error e
        | .ok v => .ok { st with valRegs := bindValReg st.valRegs dst v }
      | .binOp dst bop lhs rhs =>
        match evalValOp st.valRegs lhs, evalValOp st.valRegs rhs with
        | .ok va, .ok vb =>
          .ok { st with valRegs := bindValReg st.valRegs dst (evalBinOp bop va vb) }
        | .error e, _ => .error e
        | _, .error e => .error e
      | .readField dst alloc field =>
        match getAt? st.heap alloc with
        | none => .error .unsupported
        | some sa =>
          match getAt? sa.fields field with
          | none => .error .unsupported
          | some fm =>
            match tbRootAccessField .read none fm with
            | none => .error .tbUb
            | some fm' =>
              match setAt? sa.fields field fm' with
              | none => .error .unsupported
              | some fields' =>
                match setAt? st.heap alloc { sa with fields := fields' } with
                | none => .error .unsupported
                | some heap' =>
                  .ok { st with
                    heap := heap'
                    valRegs := bindValReg st.valRegs dst fm'.val }
      | .writeField alloc field op =>
        match getAt? st.heap alloc with
        | none => .error .unsupported
        | some sa =>
          match getAt? sa.fields field with
          | none => .error .unsupported
          | some fm =>
            match evalValOp st.valRegs op with
            | .error e => .error e
            | .ok v =>
              match tbRootAccessField .write (some v) fm with
              | none => .error .tbUb
              | some fm' =>
                match setAt? sa.fields field fm' with
                | none => .error .unsupported
                | some fields' =>
                  match setAt? st.heap alloc { sa with fields := fields' } with
                  | none => .error .unsupported
                  | some heap' => .ok { st with heap := heap' }
      | .readPtr dst pr =>
        match st.ptrRegs pr with
        | none => .error .tbUb
        | some p =>
          match accessHeapByPtr st.heap p .read none with
          | .error e => .error e
          | .ok (v, heap') =>
            .ok { st with heap := heap', valRegs := bindValReg st.valRegs dst v }
      | .writePtr pr op =>
        match st.ptrRegs pr with
        | none => .error .tbUb
        | some p =>
          match evalValOp st.valRegs op with
          | .error e => .error e
          | .ok v =>
            match accessHeapByPtr st.heap p .write (some v) with
            | .error e => .error e
            | .ok (_, heap') => .ok { st with heap := heap' }
      | .takeFieldPtr dst alloc field kind =>
        match getAt? st.heap alloc with
        | none => .error .unsupported
        | some sa =>
          match getAt? sa.fields field with
          | none => .error .unsupported
          | some fm =>
            let tag := st.nextTag
            match tbRetagField tag kind fm with
            | none => .error .tbUb
            | some fm' =>
              match setAt? sa.fields field fm' with
              | none => .error .unsupported
              | some fields' =>
                match setAt? st.heap alloc { sa with fields := fields' } with
                | none => .error .unsupported
                | some heap' =>
                  let ptr : PtrVal :=
                    { allocId := alloc, field := field, scope := .fieldOnly field, kind := kind, tag := tag }
                  .ok { st with
                    heap := heap'
                    ptrRegs := bindPtrReg st.ptrRegs dst ptr
                    nextTag := tag + 1 }
      | .takeRootSharedRef dst alloc =>
        match getAt? st.heap alloc with
        | none => .error .unsupported
        | some sa =>
          let tag := st.nextTag
          match tbRetagAllFields tag .shared sa.fields with
          | none => .error .tbUb
          | some fields' =>
            match setAt? st.heap alloc { sa with fields := fields' } with
            | none => .error .unsupported
            | some heap' =>
              let ptr : PtrVal :=
                { allocId := alloc, field := 0, scope := .wholeStruct, kind := .shared, tag := tag }
              .ok { st with
                heap := heap'
                ptrRegs := bindPtrReg st.ptrRegs dst ptr
                nextTag := tag + 1 }
      | .takeRootRawPtr dst alloc =>
        match getAt? st.heap alloc with
        | none => .error .unsupported
        | some sa =>
          let tag := st.nextTag
          match tbRetagAllFields tag .rawMut sa.fields with
          | none => .error .tbUb
          | some fields' =>
            match setAt? st.heap alloc { sa with fields := fields' } with
            | none => .error .unsupported
            | some heap' =>
              let ptr : PtrVal :=
                { allocId := alloc, field := 0, scope := .wholeStruct, kind := .rawMut, tag := tag }
              .ok { st with
                heap := heap'
                ptrRegs := bindPtrReg st.ptrRegs dst ptr
                nextTag := tag + 1 }
      | .ptrOffset dst src targetField =>
        match st.ptrRegs src with
        | none => .error .tbUb
        | some p =>
          .ok { st with ptrRegs := bindPtrReg st.ptrRegs dst { p with field := targetField } }
      | .emitObs op =>
        match evalValOp st.valRegs op with
        | .error e => .error e
        | .ok v => .ok { st with trace := st.trace ++ [.mirObs v] }

def stepMirStmts (st : ExecState) : List MirStmt → Except FaultKind ExecState
  | [] => .ok st
  | s :: rest =>
    match stepMirStmt st s with
    | .error e => .error e
    | .ok st' => stepMirStmts st' rest

/-- Fuel-indexed operational CFG execution parameterized by `PanicMode` (`unwind` vs `abort`). -/
def execMirLoop (pm : PanicMode) (body : MirBody) (env : CalleeEnv) :
    Nat → BlockId → ExecState → ExecResult
  | 0, _, st => .ok (st.trace, .outOfFuel)
  | fuel + 1, pc, st =>
    match getAt? body.blocks pc with
    | none => .error .unsupported
    | some blk =>
      match stepMirStmts st blk.stmts with
      | .error e => .error e
      | .ok st1 =>
        match st1.unwindState with
        | .enteringCleanup _ => .error .unsupported
        | _ =>
          match blk.term with
          | .goto tgt => execMirLoop pm body env fuel tgt st1
          | .switchZero discr zTgt nzTgt =>
            match evalValOp st1.valRegs discr with
            | .error e => .error e
            | .ok n =>
              if n == 0 then execMirLoop pm body env fuel zTgt st1
              else execMirLoop pm body env fuel nzTgt st1
          | .ret op =>
            match st1.unwindState with
            | .normal =>
              match evalValOp st1.valRegs op with
              | .error e => .error e
              | .ok v => .ok (st1.trace, .ret v)
            | _ => .error .unsupported
          | .resume =>
            match st1.unwindState with
            | .inCleanup payload => .ok (st1.trace, .unwound payload)
            | _ => .error .unsupported
          | .catchUnwind dst recTgt =>
            match st1.unwindState with
            | .inCleanup payload =>
              let st2 := { st1 with
                unwindState := .normal
                valRegs := bindOptValReg st1.valRegs dst payload }
              execMirLoop pm body env fuel recTgt st2
            | _ => .error .unsupported
          | .callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
            match env cid with
            | none => .error .unsupported
            | some callee =>
              match evalArgPtrs st1.ptrRegs argPtrs with
              | .error e => .error e
              | .ok ptrVals =>
                let callId := st1.nextCallId
                match activateProtectors callId st1.heap ptrVals with
                | .error e => .error e
                | .ok heapProt =>
                  match stepCalleeOps ptrVals heapProt st1.trace callee.ops with
                  | .error e => .error e
                  | .ok (heapAfter, traceAfter) =>
                    let heapRel := releaseProtectorHeap callId heapAfter
                    let st2 : ExecState :=
                      { st1 with
                        heap := heapRel
                        nextCallId := callId + 1
                        trace := traceAfter }
                    match callee.exit with
                    | .normal retVal =>
                      let st3 := { st2 with valRegs := bindOptValReg st2.valRegs retDst retVal }
                      execMirLoop pm body env fuel normTgt st3
                    | .panic payload =>
                      match pm, st2.unwindState with
                      | .unwind, .normal =>
                        execMirLoop pm body env fuel cleanTgt
                          { st2 with unwindState := .enteringCleanup payload }
                      | _, _ =>
                        -- `panic=abort` or double-panic while unwinding terminates immediately
                        .ok (st2.trace, .aborted payload)

def execMir (pm : PanicMode) (body : MirBody) (env : CalleeEnv)
    (initArgs : List UInt64) (fuel : Nat) : ExecResult :=
  execMirLoop pm body env fuel 0 (initState body initArgs)

/-! ### Shared Static CFG & Escape Analysis Helpers -/

def termTargets (t : MirTerm) (pc : BlockId) : Bool :=
  match t with
  | .goto tgt => tgt == pc
  | .switchZero _ z nz => z == pc || nz == pc
  | .callMayUnwind _ _ _ norm clean => norm == pc || clean == pc
  | .resume => false
  | .catchUnwind _ rec => rec == pc
  | .ret _ => false

def hasPredecessor (body : MirBody) (pc : BlockId) : Bool :=
  body.blocks.any fun blk => termTargets blk.term pc

def fieldIsFreeze (body : MirBody) (alloc : AllocId) (field : FieldIdx) : Bool :=
  match getAt? body.allocDecls alloc with
  | none => false
  | some decl =>
    match getAt? decl.fieldUnsafeCell field with
    | some false => true
    | _ => false

def valOpUnused (op : ValOp) (r : ValRegId) : Bool :=
  match op with
  | .constU64 _ => true
  | .reg x => x != r

def stmtValRegUnused (r : ValRegId) : MirStmt → Bool
  | .assignReg dst op => dst != r && valOpUnused op r
  | .binOp dst _ lhs rhs => dst != r && valOpUnused lhs r && valOpUnused rhs r
  | .readField dst _ _ => dst != r
  | .writeField _ _ op => valOpUnused op r
  | .readPtr dst _ => dst != r
  | .writePtr _ op => valOpUnused op r
  | .takeFieldPtr _ _ _ _ => true
  | .takeRootSharedRef _ _ => true
  | .takeRootRawPtr _ _ => true
  | .ptrOffset _ _ _ => true
  | .emitObs op => valOpUnused op r
  | .landingPad dst => dst != some r

def termValRegUnused (r : ValRegId) : MirTerm → Bool
  | .goto _ => true
  | .switchZero op _ _ => valOpUnused op r
  | .callMayUnwind _ _ retDst _ _ => retDst != some r
  | .resume => true
  | .catchUnwind dst _ => dst != some r
  | .ret op => valOpUnused op r

def valRegUnusedInBody (body : MirBody) (r : ValRegId) : Bool :=
  body.blocks.all fun blk =>
    blk.stmts.all (stmtValRegUnused r) && termValRegUnused r blk.term

/-! ### Optimization A: `PartialSroaCert` (Field-Granular Hybrid SROA) -/

inductive SroaMode where
  | fullSplit         -- field never escapes: promote BOTH reads and writes to SSA register
  | sharedReadPromote -- field may be shared via `&T`/`&s` (never `&mut`/`*mut`): write-through + SSA read promotion
  deriving DecidableEq, Repr

structure PartialSroaCert where
  mode   : SroaMode
  alloc  : AllocId
  field  : FieldIdx
  ssaReg : ValRegId
  deriving DecidableEq, Repr

def stmtAllowedForSroa (mode : SroaMode) (alloc : AllocId) (field : FieldIdx) : MirStmt → Bool
  | .takeRootRawPtr _ a => a != alloc
  | .takeRootSharedRef _ a =>
    match mode with
    | .fullSplit => a != alloc
    | .sharedReadPromote => true
  | .takeFieldPtr _ a f kind =>
    if a == alloc && f == field then
      match mode, kind with
      | .sharedReadPromote, .shared => true
      | _, _ => false
    else true
  | _ => true

def rewriteStmtForSroa (mode : SroaMode) (alloc : AllocId) (field : FieldIdx) (ssaReg : ValRegId) :
    MirStmt → List MirStmt
  | .writeField a f op =>
    if a == alloc && f == field then
      match mode with
      | .fullSplit => [.assignReg ssaReg op]
      | .sharedReadPromote => [.writeField a f op, .assignReg ssaReg op]
    else [.writeField a f op]
  | .readField dst a f =>
    if a == alloc && f == field then
      [.assignReg dst (.reg ssaReg)]
    else [.readField dst a f]
  | s => [s]

def rewriteStmtsForSroa (mode : SroaMode) (alloc : AllocId) (field : FieldIdx) (ssaReg : ValRegId)
    (stmts : List MirStmt) : List MirStmt :=
  stmts.flatMap (rewriteStmtForSroa mode alloc field ssaReg)

def applyPartialSroa (body : MirBody) (cert : PartialSroaCert) : MirBody :=
  let blocks' := match body.blocks with
    | [] => []
    | b0 :: rest =>
      let b0' : MirBlock :=
        { stmts := .assignReg cert.ssaReg (.constU64 0) ::
            rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg b0.stmts
        , term := b0.term }
      let rest' := rest.map fun b =>
        { stmts := rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg b.stmts
        , term := b.term }
      b0' :: rest'
  { allocDecls := body.allocDecls, blocks := blocks' }

/-- Decidable certificate checker for `PartialSROA`:
Verifies `Freeze` (`!isUnsafeCell`), `!rootAddressTaken` (no `TakeRootRawPtr`), escape discipline
per `SroaMode`, fresh `ssaReg`, entry-block non-reentrancy, and exact transformed body. -/
def checkPartialSroaCert (src tgt : MirBody) (cert : PartialSroaCert) : Bool :=
  fieldIsFreeze src cert.alloc cert.field &&
  (src.blocks.length > 0) &&
  (!hasPredecessor src 0) &&
  valRegUnusedInBody src cert.ssaReg &&
  (src.blocks.all fun blk => blk.stmts.all (stmtAllowedForSroa cert.mode cert.alloc cert.field)) &&
  (tgt == applyPartialSroa src cert)

/-! ### Optimization B: `StoreSinkToCleanupCert` (Unwinding Cleanup Store Sinking) -/

structure StoreSinkToCleanupCert where
  sinkBlock : BlockId
  storeIdx  : Nat
  alloc     : AllocId
  field     : FieldIdx
  deriving DecidableEq, Repr

def stmtNoPtrToField (alloc : AllocId) (field : FieldIdx) : MirStmt → Bool
  | .takeRootRawPtr _ a => a != alloc
  | .takeRootSharedRef _ a => a != alloc
  | .takeFieldPtr _ a f _ => !(a == alloc && f == field)
  | _ => true

def stmtWritesValReg : MirStmt → Option ValRegId
  | .assignReg dst _ => some dst
  | .binOp dst _ _ _ => some dst
  | .readField dst _ _ => some dst
  | .readPtr dst _ => some dst
  | .landingPad dst => dst
  | _ => none

def stmtDisjointForSink (alloc : AllocId) (field : FieldIdx) (valOp : ValOp) (s : MirStmt) : Bool :=
  let noRegClobber := match valOp, stmtWritesValReg s with
    | .reg r, some dst => r != dst
    | _, _ => true
  let noFieldTouch := match s with
    | .landingPad _ => false
    | .readField _ a f => !(a == alloc && f == field)
    | .writeField a f _ => !(a == alloc && f == field)
    | _ => true
  noRegClobber && noFieldTouch

/-- Apply the `StoreSinkToCleanup` transformation (used by both certified canaries and uncertified
sharpness counterexamples). Returns `none` only if indices/shapes are syntactically malformed. -/
def applyStoreSink? (src : MirBody) (cert : StoreSinkToCleanupCert) : Option MirBody :=
  match getAt? src.blocks cert.sinkBlock with
  | none => none
  | some sinkBlk =>
    match splitAtIdx? sinkBlk.stmts cert.storeIdx, sinkBlk.term with
    | some (pre, .writeField a f valOp, mid), .callMayUnwind _ _ _ _ cleanTgt =>
      if a != cert.alloc || f != cert.field then none
      else
        match getAt? src.blocks cleanTgt with
        | none => none
        | some cleanBlk =>
          match cleanBlk.stmts with
          | .landingPad lpDst :: cleanRest =>
            let sinkBlk' : MirBlock := { stmts := pre ++ mid, term := sinkBlk.term }
            let cleanBlk' : MirBlock :=
              { stmts := .landingPad lpDst :: .writeField a f valOp :: cleanRest
              , term := cleanBlk.term }
            match setAt? src.blocks cert.sinkBlock sinkBlk' with
            | none => none
            | some b1 =>
              match setAt? b1 cleanTgt cleanBlk' with
              | none => none
              | some b2 => some { allocDecls := src.allocDecls, blocks := b2 }
          | _ => none
    | _, _ => none

/-- Decidable certificate checker for `StoreSinkToCleanup`:
Verifies `Freeze` (`!isUnsafeCell`), zero pointers to `(alloc, field)` across `src` (so the
unwinding callee cannot observe `s.f`, while sibling fields `f' ≠ field` may freely escape!),
unique predecessor for `cleanupTarget`, normal-path immediate overwrite `s.f = v2`, non-clobbering
`mid` statements and `landingPad`, and exact transformed body. -/
def checkStoreSinkCert (src tgt : MirBody) (cert : StoreSinkToCleanupCert) : Bool :=
  fieldIsFreeze src cert.alloc cert.field &&
  (src.blocks.all fun blk => blk.stmts.all (stmtNoPtrToField cert.alloc cert.field)) &&
  match getAt? src.blocks cert.sinkBlock with
  | none => false
  | some sinkBlk =>
    match splitAtIdx? sinkBlk.stmts cert.storeIdx, sinkBlk.term with
    | some (_, .writeField a f valOp, mid), .callMayUnwind _ _ _ normTgt cleanTgt =>
      (a == cert.alloc) &&
      (f == cert.field) &&
      (normTgt < src.blocks.length) &&
      (cleanTgt < src.blocks.length) &&
      (cleanTgt != 0) &&
      (cleanTgt != cert.sinkBlock) &&
      (normTgt != cert.sinkBlock) &&
      (cleanTgt != normTgt) &&
      -- `sinkBlock` is never entered as a cleanup target (prevents `.enteringCleanup` mismatch)
      (src.blocks.all fun blk =>
        match blk.term with
        | .callMayUnwind _ _ _ _ cl => cl != cert.sinkBlock
        | _ => true) &&
      -- `cleanupTarget` has unique predecessor (`sinkBlock`'s unwind edge only)
      ((List.range src.blocks.length).all fun pc =>
        if pc == cert.sinkBlock then true
        else match getAt? src.blocks pc with
          | some blk => !termTargets blk.term cleanTgt
          | none => false) &&
      -- intervening statements in `sinkBlock` commute with `s.f = v1` and preserve `valOp`
      (mid.all (stmtDisjointForSink cert.alloc cert.field valOp)) &&
      -- normal target immediately overwrites `s.f = v2`
      (match getAt? src.blocks normTgt with
       | some normBlk =>
         match normBlk.stmts with
         | .writeField a2 f2 _ :: _ => a2 == cert.alloc && f2 == cert.field
         | _ => false
       | none => false) &&
      -- cleanup target starts with `landingPad` not clobbering `valOp`
      (match getAt? src.blocks cleanTgt with
       | some cleanBlk =>
         match cleanBlk.stmts with
         | .landingPad lpDst :: _ =>
           match valOp, lpDst with
           | .reg r, some d => r != d
           | _, _ => true
         | _ => false
       | none => false) &&
      (applyStoreSink? src cert == some tgt)
    | _, _ => false

/-! ### Profile Subsumption: `UnwindToAbortCert` (`panic=unwind` vs `panic=abort`) -/

structure UnwindToAbortCert where
  noCatchUnwind : Bool
  cleanupBlocks : List BlockId
  deriving DecidableEq, Repr

def stmtIsSideEffectFree : MirStmt → Bool
  | .emitObs _ => false
  | _ => true

/-- Decidable certificate checker for `UnwindToAbortSubsumption`:
Requires `noCatchUnwind = true`, disjoint normal vs. cleanup CFG partition, zero `CatchUnwind`
anywhere, and zero external observable side effects (`EmitObs` or nested `CallMayUnwind`) inside
any reachable cleanup pad. -/
def checkUnwindToAbortCert (body : MirBody) (cert : UnwindToAbortCert) : Bool :=
  cert.noCatchUnwind &&
  (!cert.cleanupBlocks.contains 0) &&
  ((List.range body.blocks.length).all fun pc =>
    match getAt? body.blocks pc with
    | none => false
    | some blk =>
      if cert.cleanupBlocks.contains pc then
        blk.stmts.all stmtIsSideEffectFree &&
        match blk.term with
        | .goto tgt => cert.cleanupBlocks.contains tgt
        | .switchZero _ z nz => cert.cleanupBlocks.contains z && cert.cleanupBlocks.contains nz
        | .resume => true
        | .ret _ => false
        | .catchUnwind _ _ => false
        | .callMayUnwind _ _ _ _ _ => false
      else
        match blk.term with
        | .goto tgt => !cert.cleanupBlocks.contains tgt
        | .switchZero _ z nz => !cert.cleanupBlocks.contains z && !cert.cleanupBlocks.contains nz
        | .callMayUnwind _ _ _ norm clean =>
          (!cert.cleanupBlocks.contains norm) && cert.cleanupBlocks.contains clean
        | .ret _ => true
        | .resume => false
        | .catchUnwind _ _ => false)

/-! ### Private Proof Helpers (Stage 4) -/

private theorem getAt?_lt {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, getAt? xs i = some x → i < xs.length
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, _ + 1, _, h => Nat.succ_lt_succ (getAt?_lt (xs := xs) h)

private theorem getAt?_of_lt {α : Type} :
    ∀ {xs : List α} {i : Nat}, i < xs.length → ∃ x, getAt? xs i = some x
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, _ + 1, h => getAt?_of_lt (xs := xs) (Nat.lt_of_succ_lt_succ h)

private theorem getAt?_eq_none_of_ge {α : Type} :
    ∀ {xs : List α} {i : Nat}, xs.length ≤ i → getAt? xs i = none
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, _ + 1, h => getAt?_eq_none_of_ge (xs := xs) (Nat.le_of_succ_le_succ h)

private theorem getAt?_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, getAt? xs i = some x → x ∈ xs
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, h => by simp [getAt?] at h; subst h; exact List.mem_cons_self
  | _ :: xs, _ + 1, _, h => List.mem_cons_of_mem _ (getAt?_mem (xs := xs) h)

private theorem getAt?_map {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Nat), getAt? (xs.map f) i = (getAt? xs i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => getAt?_map f xs i

private theorem setAt?_length {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α}, setAt? xs i v = some xs' → xs'.length = xs.length
  | [], _, _, _, h => by simp [setAt?] at h
  | _ :: _, _, 0, _, h => by simp [setAt?] at h; subst h; rfl
  | x :: xs, _, i + 1, v, h => by
    simp only [setAt?] at h
    cases h1 : setAt? xs i v with
    | none => simp [h1] at h
    | some ys =>
      simp [h1] at h
      subst h
      simp [setAt?_length h1]

private theorem setAt?_of_getAt? {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α} (v : α),
      getAt? xs i = some x → ∃ xs', setAt? xs i v = some xs'
  | [], _, _, _, h => by simp [getAt?] at h
  | _ :: xs, 0, _, v, _ => ⟨v :: xs, rfl⟩
  | x :: xs, i + 1, _, v, h => by
    obtain ⟨ys, hy⟩ := setAt?_of_getAt? (xs := xs) v h
    exact ⟨x :: ys, by simp [setAt?, hy]⟩

private theorem getAt?_setAt?_same {α : Type} :
    ∀ {xs xs' : List α} {i : Nat} {v : α}, setAt? xs i v = some xs' → getAt? xs' i = some v
  | [], _, _, _, h => by simp [setAt?] at h
  | _ :: _, _, 0, _, h => by simp [setAt?] at h; subst h; rfl
  | x :: xs, _, i + 1, v, h => by
    simp only [setAt?] at h
    cases h1 : setAt? xs i v with
    | none => simp [h1] at h
    | some ys =>
      simp [h1] at h
      subst h
      simp only [getAt?]
      exact getAt?_setAt?_same h1

private theorem getAt?_setAt?_ne {α : Type} :
    ∀ {xs xs' : List α} {i j : Nat} {v : α},
      setAt? xs i v = some xs' → j ≠ i → getAt? xs' j = getAt? xs j
  | [], _, _, _, _, h, _ => by simp [setAt?] at h
  | _ :: _, _, 0, 0, _, _, hne => absurd rfl hne
  | _ :: _, _, 0, _ + 1, _, h, _ => by simp [setAt?] at h; subst h; rfl
  | x :: xs, _, i + 1, 0, v, h, _ => by
    simp only [setAt?] at h
    cases h1 : setAt? xs i v with
    | none => simp [h1] at h
    | some ys => simp [h1] at h; subst h; rfl
  | x :: xs, _, i + 1, j + 1, v, h, hne => by
    simp only [setAt?] at h
    cases h1 : setAt? xs i v with
    | none => simp [h1] at h
    | some ys =>
      simp [h1] at h
      subst h
      simp only [getAt?]
      exact getAt?_setAt?_ne h1 (fun heq => hne (congrArg Nat.succ heq))

private theorem setAt?_getAt? {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, getAt? xs i = some x → setAt? xs i x = some xs
  | [], _, _, h => by simp [getAt?] at h
  | _ :: _, 0, _, h => by simp [getAt?] at h; subst h; rfl
  | x :: xs, _ + 1, _, h => by
    simp [setAt?, setAt?_getAt? (xs := xs) h]

private theorem list_eq_of_getAt? {α : Type} :
    ∀ {xs ys : List α}, xs.length = ys.length → (∀ i, getAt? xs i = getAt? ys i) → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => nomatch hlen
  | _ :: _, [], hlen, _ => nomatch hlen
  | x :: xs, y :: ys, hlen, hget => by
    have h0 : some x = some y := hget 0
    injection h0 with hxy
    subst hxy
    exact congrArg (x :: ·) (list_eq_of_getAt? (Nat.succ.inj hlen) (fun i => hget (i + 1)))

private theorem splitAtIdx?_sound {α : Type} :
    ∀ {xs : List α} {i : Nat} {pre post : List α} {x : α},
      splitAtIdx? xs i = some (pre, x, post) → xs = pre ++ x :: post
  | [], _, _, _, _, h => by simp [splitAtIdx?] at h
  | y :: ys, 0, pre, post, x, h => by
    simp [splitAtIdx?] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl
  | y :: ys, i + 1, pre, post, x, h => by
    simp only [splitAtIdx?] at h
    cases h1 : splitAtIdx? ys i with
    | none => simp [h1] at h
    | some t =>
      rcases t with ⟨pre', x', post'⟩
      simp [h1] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simp [splitAtIdx?_sound h1]

private theorem all_of_mem {α : Type} {xs : List α} {p : α → Bool} {x : α}
    (hall : xs.all p = true) (hmem : x ∈ xs) : p x = true := by
  rw [List.all_eq_true] at hall
  exact hall x hmem

private theorem all_of_getAt? {α : Type} {xs : List α} {p : α → Bool} {i : Nat} {x : α}
    (hall : xs.all p = true) (hget : getAt? xs i = some x) : p x = true :=
  all_of_mem hall (getAt?_mem hget)

private theorem any_eq_false_of_mem {α : Type} {xs : List α} {p : α → Bool} {x : α}
    (hany : xs.any p = false) (hmem : x ∈ xs) : p x = false := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hany
    cases hmem with
    | head => exact hany.1
    | tail _ htail => exact ih hany.2 htail

private theorem any_eq_false_of_getAt? {α : Type} {xs : List α} {p : α → Bool} {i : Nat} {x : α}
    (hany : xs.any p = false) (hget : getAt? xs i = some x) : p x = false :=
  any_eq_false_of_mem hany (getAt?_mem hget)

private theorem range_all_apply {n : Nat} {p : Nat → Bool}
    (hall : (List.range n).all p = true) {i : Nat} (hlt : i < n) : p i = true := by
  rw [List.all_eq_true] at hall
  exact hall i (List.mem_range.mpr hlt)

private theorem stepMirStmts_append (st : ExecState) (s1 s2 : List MirStmt) :
    stepMirStmts st (s1 ++ s2) =
      match stepMirStmts st s1 with
      | .error e => .error e
      | .ok st1 => stepMirStmts st1 s2 := by
  induction s1 generalizing st with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, stepMirStmts]
    cases h : stepMirStmt st s with
    | error e => rfl
    | ok st' => exact ih st'

private theorem stepMirStmt_unwindState_normal {st st' : ExecState} {s : MirStmt}
    (hn : st.unwindState = .normal) (hstep : stepMirStmt st s = .ok st') :
    st'.unwindState = .normal := by
  cases s <;> simp only [stepMirStmt, hn] at hstep
  all_goals
    repeat (first
      | (split at hstep <;> try contradiction)
      | (simp only [Except.ok.injEq] at hstep; subst hstep; rfl)
      | contradiction)

private theorem stepMirStmts_unwindState_normal {st st' : ExecState} {ss : List MirStmt}
    (hn : st.unwindState = .normal) (hstep : stepMirStmts st ss = .ok st') :
    st'.unwindState = .normal := by
  induction ss generalizing st with
  | nil =>
    simp only [stepMirStmts, Except.ok.injEq] at hstep
    subst hstep
    exact hn
  | cons s rest ih =>
    simp only [stepMirStmts] at hstep
    cases h1 : stepMirStmt st s with
    | error e => simp [h1] at hstep
    | ok st1 =>
      simp [h1] at hstep
      exact ih (stepMirStmt_unwindState_normal hn h1) hstep

private theorem stepMirStmt_unwindState_ne_entering {st st' : ExecState} {s : MirStmt}
    (hne : ∀ p, st.unwindState ≠ .enteringCleanup p) (hstep : stepMirStmt st s = .ok st') :
    ∀ p, st'.unwindState ≠ .enteringCleanup p := by
  cases hu : st.unwindState with
  | enteringCleanup payload => exact absurd hu (hne payload)
  | normal =>
    have hn := stepMirStmt_unwindState_normal hu hstep
    intro p hp
    rw [hn] at hp
    cases hp
  | inCleanup payload =>
    cases s <;> simp only [stepMirStmt, hu] at hstep
    all_goals
      repeat (first
        | (split at hstep <;> try contradiction)
        | (simp only [Except.ok.injEq] at hstep; subst hstep; intro p hp; cases hp)
        | contradiction)

private theorem stepMirStmts_unwindState_ne_entering {st st' : ExecState} {ss : List MirStmt}
    (hne : ∀ p, st.unwindState ≠ .enteringCleanup p) (hstep : stepMirStmts st ss = .ok st') :
    ∀ p, st'.unwindState ≠ .enteringCleanup p := by
  induction ss generalizing st with
  | nil =>
    simp only [stepMirStmts, Except.ok.injEq] at hstep
    subst hstep
    exact hne
  | cons s rest ih =>
    simp only [stepMirStmts] at hstep
    cases h1 : stepMirStmt st s with
    | error e => simp [h1] at hstep
    | ok st1 =>
      simp [h1] at hstep
      exact ih (stepMirStmt_unwindState_ne_entering hne h1) hstep

private theorem nat_beq_self (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

private theorem bindValReg_same (env : ValRegEnv) (r : ValRegId) (v : UInt64) :
    bindValReg env r v r = some v := by
  dsimp only [bindValReg]
  exact if_pos (nat_beq_self r)

private theorem bindValReg_ne (env : ValRegEnv) {r x : ValRegId} (v : UInt64) (hne : x ≠ r) :
    bindValReg env r v x = env x := by
  dsimp only [bindValReg]
  exact if_neg (fun h => hne (beq_iff_eq.mp h))

private theorem bindPtrReg_same (env : PtrRegEnv) (r : PtrRegId) (p : PtrVal) :
    bindPtrReg env r p r = some p := by
  dsimp only [bindPtrReg]
  exact if_pos (nat_beq_self r)

private theorem bindPtrReg_ne (env : PtrRegEnv) {r x : PtrRegId} (p : PtrVal) (hne : x ≠ r) :
    bindPtrReg env r p x = env x := by
  dsimp only [bindPtrReg]
  exact if_neg (fun h => hne (beq_iff_eq.mp h))

private theorem refines_of_eq {srcRes tgtRes : ExecResult} (h : tgtRes = srcRes) :
    refines srcRes tgtRes := by
  cases srcRes with
  | ok r => exact h
  | error e =>
    cases e with
    | tbUb => trivial
    | unsupported => exact h

/-! #### Theorem 3 Helpers (`unwind_to_abort_subsumption`) -/

private theorem stepMirStmt_cleanup {st st' : ExecState} {s : MirStmt} {p : UInt64}
    (hse : stmtIsSideEffectFree s = true)
    (hu : st.unwindState = .enteringCleanup p ∨ st.unwindState = .inCleanup p)
    (hstep : stepMirStmt st s = .ok st') :
    st'.trace = st.trace ∧
      (st'.unwindState = .enteringCleanup p ∨ st'.unwindState = .inCleanup p) := by
  cases s with
  | emitObs _ => simp [stmtIsSideEffectFree] at hse
  | landingPad dst =>
    simp only [stepMirStmt] at hstep
    rcases hu with hu | hu
    · simp only [hu, Except.ok.injEq] at hstep
      subst hstep
      exact ⟨rfl, Or.inr rfl⟩
    · simp [hu] at hstep
  | _ =>
    rcases hu with hu | hu
    · simp [stepMirStmt, hu] at hstep
    · simp only [stepMirStmt, hu] at hstep
      repeat (first
        | (split at hstep <;> try contradiction)
        | (simp only [Except.ok.injEq] at hstep; subst hstep; exact ⟨rfl, Or.inr rfl⟩)
        | contradiction)

private theorem stepMirStmts_cleanup {st st' : ExecState} {ss : List MirStmt} {p : UInt64}
    (hse : ss.all stmtIsSideEffectFree = true)
    (hu : st.unwindState = .enteringCleanup p ∨ st.unwindState = .inCleanup p)
    (hstep : stepMirStmts st ss = .ok st') :
    st'.trace = st.trace ∧
      (st'.unwindState = .enteringCleanup p ∨ st'.unwindState = .inCleanup p) := by
  induction ss generalizing st with
  | nil =>
    simp only [stepMirStmts, Except.ok.injEq] at hstep
    subst hstep
    exact ⟨rfl, hu⟩
  | cons s rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hse
    simp only [stepMirStmts] at hstep
    cases h1 : stepMirStmt st s with
    | error e => simp [h1] at hstep
    | ok st1 =>
      simp only [h1] at hstep
      obtain ⟨htr1, hu1⟩ := stepMirStmt_cleanup hse.1 hu h1
      obtain ⟨htr2, hu2⟩ := ih hse.2 hu1 hstep
      exact ⟨htr2.trans htr1, hu2⟩

private theorem checkUnwindToAbort_block {body : MirBody} {cert : UnwindToAbortCert}
    (hcert : checkUnwindToAbortCert body cert = true)
    {pc : BlockId} {blk : MirBlock} (hblk : getAt? body.blocks pc = some blk) :
    if cert.cleanupBlocks.contains pc then
      blk.stmts.all stmtIsSideEffectFree = true ∧
      match blk.term with
      | .goto tgt => cert.cleanupBlocks.contains tgt = true
      | .switchZero _ z nz =>
        cert.cleanupBlocks.contains z = true ∧ cert.cleanupBlocks.contains nz = true
      | .resume => True
      | .ret _ => False
      | .catchUnwind _ _ => False
      | .callMayUnwind _ _ _ _ _ => False
    else
      match blk.term with
      | .goto tgt => cert.cleanupBlocks.contains tgt = false
      | .switchZero _ z nz =>
        cert.cleanupBlocks.contains z = false ∧ cert.cleanupBlocks.contains nz = false
      | .callMayUnwind _ _ _ norm clean =>
        cert.cleanupBlocks.contains norm = false ∧ cert.cleanupBlocks.contains clean = true
      | .ret _ => True
      | .resume => False
      | .catchUnwind _ _ => False := by
  simp only [checkUnwindToAbortCert, Bool.and_eq_true] at hcert
  have hall := range_all_apply hcert.2 (getAt?_lt hblk)
  simp only [hblk] at hall
  cases hcl : cert.cleanupBlocks.contains pc
  · simp only [hcl, Bool.false_eq_true, ↓reduceIte] at hall ⊢
    cases ht : blk.term <;> simp [ht] at hall ⊢
    · exact hall
    · exact hall
    · exact hall
  · simp only [hcl, ↓reduceIte, Bool.and_eq_true] at hall ⊢
    refine ⟨hall.1, ?_⟩
    have h2 := hall.2
    cases ht : blk.term <;> simp [ht] at h2 ⊢
    · exact h2
    · exact h2

private theorem unwind_cleanup_absorption {body : MirBody} {cert : UnwindToAbortCert}
    (hcert : checkUnwindToAbortCert body cert = true) (env : CalleeEnv) :
    ∀ fuel pc st p,
      cert.cleanupBlocks.contains pc = true →
      (st.unwindState = .enteringCleanup p ∨ st.unwindState = .inCleanup p) →
      (∀ tr v, execMirLoop .unwind body env fuel pc st ≠ .ok (tr, .ret v)) ∧
      (∀ tr q, execMirLoop .unwind body env fuel pc st = .ok (tr, .unwound q) →
        tr = st.trace ∧ q = p)
  | 0, _, _, _, _, _ => by
    exact ⟨(fun _ _ h => by simp [execMirLoop] at h), (fun _ _ h => by simp [execMirLoop] at h)⟩
  | fuel + 1, pc, st, p, hcl, hu => by
    simp only [execMirLoop]
    cases hblk : getAt? body.blocks pc with
    | none =>
      dsimp only []
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
    | some blk =>
      dsimp only []
      have hprop := checkUnwindToAbort_block hcert hblk
      simp only [hcl, ↓reduceIte] at hprop
      rcases hprop with ⟨hse, hterm⟩
      cases hst : stepMirStmts st blk.stmts with
      | error e =>
        dsimp only []
        exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
      | ok st1 =>
        dsimp only []
        obtain ⟨htr1, hu1⟩ := stepMirStmts_cleanup hse hu hst
        cases hu1' : st1.unwindState with
        | enteringCleanup _ =>
          dsimp only []
          exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
        | normal =>
          rw [hu1'] at hu1
          rcases hu1 with h | h <;> cases h
        | inCleanup q0 =>
          dsimp only []
          have hqp : q0 = p := by
            rw [hu1'] at hu1
            rcases hu1 with h | h
            · cases h
            · injection h
          subst hqp
          cases ht : blk.term with
          | goto tgt =>
            rw [ht] at hterm
            dsimp only []
            have ih := unwind_cleanup_absorption hcert env fuel tgt st1 q0 hterm (Or.inr hu1')
            exact ⟨ih.1, fun tr q h => by
              obtain ⟨htr2, hq⟩ := ih.2 tr q h
              exact ⟨htr2.trans htr1, hq⟩⟩
          | switchZero discr zTgt nzTgt =>
            rw [ht] at hterm
            dsimp only []
            cases hev : evalValOp st1.valRegs discr with
            | error e =>
              dsimp only []
              exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
            | ok n =>
              dsimp only []
              split
              · have ih := unwind_cleanup_absorption hcert env fuel zTgt st1 q0 hterm.1 (Or.inr hu1')
                exact ⟨ih.1, fun tr q h => by
                  obtain ⟨htr2, hq⟩ := ih.2 tr q h
                  exact ⟨htr2.trans htr1, hq⟩⟩
              · have ih := unwind_cleanup_absorption hcert env fuel nzTgt st1 q0 hterm.2 (Or.inr hu1')
                exact ⟨ih.1, fun tr q h => by
                  obtain ⟨htr2, hq⟩ := ih.2 tr q h
                  exact ⟨htr2.trans htr1, hq⟩⟩
          | resume =>
            dsimp only []
            constructor
            · intro tr v h; cases h
            · intro tr q h
              injection h with hpair
              injection hpair with htr hres
              injection hres with hq
              exact ⟨htr.symm.trans htr1, hq.symm⟩
          | ret _ => rw [ht] at hterm; exact False.elim hterm
          | catchUnwind _ _ => rw [ht] at hterm; exact False.elim hterm
          | callMayUnwind _ _ _ _ _ => rw [ht] at hterm; exact False.elim hterm

private theorem unwind_abort_same_fuel {body : MirBody} {cert : UnwindToAbortCert}
    (hcert : checkUnwindToAbortCert body cert = true) (env : CalleeEnv) :
    ∀ fuel pc st,
      cert.cleanupBlocks.contains pc = false →
      st.unwindState = .normal →
      (∀ tr v,
        execMirLoop .unwind body env fuel pc st = .ok (tr, .ret v) ↔
        execMirLoop .abort body env fuel pc st = .ok (tr, .ret v)) ∧
      (∀ tr payload,
        execMirLoop .unwind body env fuel pc st = .ok (tr, .unwound payload) →
        execMirLoop .abort body env fuel pc st = .ok (tr, .aborted payload)) ∧
      (∀ e,
        execMirLoop .abort body env fuel pc st = .error e →
        execMirLoop .unwind body env fuel pc st = .error e)
  | 0, _, _, _, _ => by
    refine ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by simp [execMirLoop] at h), (fun _ h => by simp [execMirLoop] at h)⟩
  | fuel + 1, pc, st, hnc, hn => by
    simp only [execMirLoop]
    cases hblk : getAt? body.blocks pc with
    | none =>
      dsimp only []
      exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
    | some blk =>
      dsimp only []
      have hprop := checkUnwindToAbort_block hcert hblk
      simp only [hnc, Bool.false_eq_true, ↓reduceIte] at hprop
      cases hst : stepMirStmts st blk.stmts with
      | error e =>
        dsimp only []
        exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
      | ok st1 =>
        dsimp only []
        have hn1 : st1.unwindState = .normal := stepMirStmts_unwindState_normal hn hst
        simp only [hn1]
        cases ht : blk.term with
        | goto tgt =>
          rw [ht] at hprop
          dsimp only []
          exact unwind_abort_same_fuel hcert env fuel tgt st1 hprop hn1
        | switchZero discr zTgt nzTgt =>
          rw [ht] at hprop
          dsimp only []
          cases hev : evalValOp st1.valRegs discr with
          | error e =>
            dsimp only []
            exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
          | ok n =>
            dsimp only []
            split
            · exact unwind_abort_same_fuel hcert env fuel zTgt st1 hprop.1 hn1
            · exact unwind_abort_same_fuel hcert env fuel nzTgt st1 hprop.2 hn1
        | ret op =>
          dsimp only []
          cases hev : evalValOp st1.valRegs op with
          | error e =>
            dsimp only []
            exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
          | ok v =>
            dsimp only []
            exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩
        | resume => rw [ht] at hprop; exact False.elim hprop
        | catchUnwind _ _ => rw [ht] at hprop; exact False.elim hprop
        | callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
          rw [ht] at hprop
          dsimp only []
          cases henv : env cid with
          | none =>
            dsimp only []
            exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
          | some callee =>
            dsimp only []
            cases hargs : evalArgPtrs st1.ptrRegs argPtrs with
            | error e =>
              dsimp only []
              exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
            | ok ptrVals =>
              dsimp only []
              cases hprot : activateProtectors st1.nextCallId st1.heap ptrVals with
              | error e =>
                dsimp only []
                exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
              | ok heapProt =>
                dsimp only []
                cases hops : stepCalleeOps ptrVals heapProt st1.trace callee.ops with
                | error e =>
                  dsimp only []
                  exact ⟨(fun _ _ => Iff.rfl), (fun _ _ h => by cases h), (fun _ h => h)⟩
                | ok res =>
                  rcases res with ⟨heapAfter, traceAfter⟩
                  dsimp only []
                  cases hexit : callee.exit with
                  | normal retVal =>
                    dsimp only []
                    exact unwind_abort_same_fuel hcert env fuel normTgt
                      { st1 with
                        heap := releaseProtectorHeap st1.nextCallId heapAfter
                        nextCallId := st1.nextCallId + 1
                        trace := traceAfter
                        valRegs := bindOptValReg st1.valRegs retDst retVal
                        unwindState := .normal }
                      hprop.1 rfl
                  | panic payload =>
                    dsimp only []
                    have habs := unwind_cleanup_absorption hcert env fuel cleanTgt
                      { st1 with
                        heap := releaseProtectorHeap st1.nextCallId heapAfter
                        nextCallId := st1.nextCallId + 1
                        trace := traceAfter
                        unwindState := .enteringCleanup payload }
                      payload hprop.2 (Or.inl rfl)
                    refine ⟨(fun tr v => ?_), (fun tr p hu => ?_), (fun e he => by cases he)⟩
                    · constructor
                      · intro hu
                        exact absurd hu (habs.1 tr v)
                      · intro ha
                        cases ha
                    · obtain ⟨htr, hp⟩ := habs.2 tr p hu
                      subst htr; subst hp
                      rfl

private theorem abort_implies_unwind_subsumption {body : MirBody} {cert : UnwindToAbortCert}
    (hcert : checkUnwindToAbortCert body cert = true) (env : CalleeEnv) :
    ∀ fuel fuel' pc st tr payload,
      cert.cleanupBlocks.contains pc = false →
      st.unwindState = .normal →
      execMirLoop .abort body env fuel pc st = .ok (tr, .aborted payload) →
      (∀ tr' v, execMirLoop .unwind body env fuel' pc st ≠ .ok (tr', .ret v)) ∧
      (∀ tr' p', execMirLoop .unwind body env fuel' pc st = .ok (tr', .unwound p') →
        tr' = tr ∧ p' = payload)
  | 0, _, _, _, _, _, _, _ => fun ha => by simp [execMirLoop] at ha
  | _ + 1, 0, _, _, _, _, _, _ => fun _ =>
    ⟨(fun _ _ h => by simp [execMirLoop] at h), (fun _ _ h => by simp [execMirLoop] at h)⟩
  | fuel + 1, fuel' + 1, pc, st, tr, payload, hnc, hn => by
    simp only [execMirLoop]
    cases hblk : getAt? body.blocks pc with
    | none =>
      dsimp only []
      intro ha; cases ha
    | some blk =>
      dsimp only []
      have hprop := checkUnwindToAbort_block hcert hblk
      simp only [hnc, Bool.false_eq_true, ↓reduceIte] at hprop
      cases hst : stepMirStmts st blk.stmts with
      | error e =>
        dsimp only []
        intro ha; cases ha
      | ok st1 =>
        dsimp only []
        have hn1 : st1.unwindState = .normal := stepMirStmts_unwindState_normal hn hst
        simp only [hn1]
        cases ht : blk.term with
        | goto tgt =>
          rw [ht] at hprop
          dsimp only []
          exact abort_implies_unwind_subsumption hcert env fuel fuel' tgt st1 tr payload hprop hn1
        | switchZero discr zTgt nzTgt =>
          rw [ht] at hprop
          dsimp only []
          cases hev : evalValOp st1.valRegs discr with
          | error e =>
            dsimp only []
            intro ha; cases ha
          | ok n =>
            dsimp only []
            split
            · exact abort_implies_unwind_subsumption hcert env fuel fuel' zTgt st1 tr payload hprop.1 hn1
            · exact abort_implies_unwind_subsumption hcert env fuel fuel' nzTgt st1 tr payload hprop.2 hn1
        | ret op =>
          dsimp only []
          cases hev : evalValOp st1.valRegs op with
          | error e => dsimp only []; intro ha; cases ha
          | ok v => dsimp only []; intro ha; cases ha
        | resume => rw [ht] at hprop; exact False.elim hprop
        | catchUnwind _ _ => rw [ht] at hprop; exact False.elim hprop
        | callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
          rw [ht] at hprop
          dsimp only []
          cases henv : env cid with
          | none => dsimp only []; intro ha; cases ha
          | some callee =>
            dsimp only []
            cases hargs : evalArgPtrs st1.ptrRegs argPtrs with
            | error e => dsimp only []; intro ha; cases ha
            | ok ptrVals =>
              dsimp only []
              cases hprot : activateProtectors st1.nextCallId st1.heap ptrVals with
              | error e => dsimp only []; intro ha; cases ha
              | ok heapProt =>
                dsimp only []
                cases hops : stepCalleeOps ptrVals heapProt st1.trace callee.ops with
                | error e => dsimp only []; intro ha; cases ha
                | ok res =>
                  rcases res with ⟨heapAfter, traceAfter⟩
                  dsimp only []
                  cases hexit : callee.exit with
                  | normal retVal =>
                    dsimp only []
                    exact abort_implies_unwind_subsumption hcert env fuel fuel' normTgt
                      { st1 with
                        heap := releaseProtectorHeap st1.nextCallId heapAfter
                        nextCallId := st1.nextCallId + 1
                        trace := traceAfter
                        valRegs := bindOptValReg st1.valRegs retDst retVal
                        unwindState := .normal }
                      tr payload hprop.1 rfl
                  | panic payload0 =>
                    dsimp only []
                    intro ha
                    injection ha with hpair
                    injection hpair with htr hres
                    injection hres with hp
                    subst htr; subst hp
                    exact unwind_cleanup_absorption hcert env fuel' cleanTgt
                      { st1 with
                        heap := releaseProtectorHeap st1.nextCallId heapAfter
                        nextCallId := st1.nextCallId + 1
                        trace := traceAfter
                        unwindState := .enteringCleanup payload0 }
                      payload0 hprop.2 (Or.inl rfl)

/-! #### Shared Pointer-Disjointness & Heap-Difference Helpers (Theorems 1 & 2) -/

private def PtrDisjoint (a : AllocId) (f : FieldIdx) (p : PtrVal) : Prop :=
  p.allocId ≠ a ∨ (∃ f', p.scope = .fieldOnly f' ∧ f' ≠ f)

private theorem PtrDisjoint_applyPtrOffset {a : AllocId} {f : FieldIdx} {p : PtrVal}
    (h : PtrDisjoint a f p) (off : Option FieldIdx) :
    PtrDisjoint a f (applyPtrOffset p off) := by
  cases off with
  | none => exact h
  | some _ => exact h

private theorem PtrDisjoint_inScope_ne {a : AllocId} {f : FieldIdx} {p : PtrVal}
    (hd : PtrDisjoint a f p) (hin : ptrInScope p = true) :
    p.allocId ≠ a ∨ p.field ≠ f := by
  rcases hd with hne | ⟨f', hsc, hfn⟩
  · exact Or.inl hne
  · right
    simp only [ptrInScope, hsc, beq_iff_eq] at hin
    rw [hin]
    exact hfn

private theorem PtrDisjoint_evalArgPtrs {a : AllocId} {f : FieldIdx} {ptrRegs : PtrRegEnv}
    (hinv : ∀ r p, ptrRegs r = some p → PtrDisjoint a f p) :
    ∀ {argPtrs : List PtrRegId} {ptrVals : List PtrVal},
      evalArgPtrs ptrRegs argPtrs = .ok ptrVals → ∀ p ∈ ptrVals, PtrDisjoint a f p
  | [], _, h, _, hmem => by
    simp only [evalArgPtrs, Except.ok.injEq] at h
    subst h
    cases hmem
  | r :: rs, _, h, p, hmem => by
    simp only [evalArgPtrs] at h
    cases hr : ptrRegs r with
    | none => simp [hr] at h
    | some q =>
      cases hrs : evalArgPtrs ptrRegs rs with
      | error e => simp [hr, hrs] at h
      | ok ps =>
        simp only [hr, hrs, Except.ok.injEq] at h
        subst h
        cases hmem with
        | head => exact hinv r p hr
        | tail _ ht => exact PtrDisjoint_evalArgPtrs hinv hrs p ht

private def FieldNoChildrenInv (fm : FieldMeta) : Prop :=
  fm.isUnsafeCell = false ∧
  fm.children = [] ∧
  (fm.perm = .reserved false ∨ fm.perm = .active)

private theorem FieldNoChildrenInv_init : FieldNoChildrenInv (initFieldMeta false) :=
  ⟨rfl, rfl, Or.inl rfl⟩

private theorem tbRootAccessField_read_noChildren {fm : FieldMeta} (h : FieldNoChildrenInv fm) :
    tbRootAccessField .read none fm = some fm := by
  rcases h with ⟨_, hch, hp⟩
  rcases fm with ⟨uc, val, perm, children⟩
  dsimp only at hch hp
  subst hch
  rcases hp with rfl | rfl <;> rfl

private theorem tbRootAccessField_write_noChildren {fm : FieldMeta} (h : FieldNoChildrenInv fm)
    (v : UInt64) :
    tbRootAccessField .write (some v) fm =
      some { isUnsafeCell := false, val := v, perm := .active, children := [] } := by
  rcases h with ⟨huc, hch, hp⟩
  rcases fm with ⟨uc, val, perm, children⟩
  dsimp only at huc hch hp
  subst huc; subst hch
  rcases hp with rfl | rfl <;> rfl

private theorem FieldNoChildrenInv_active (v : UInt64) :
    FieldNoChildrenInv { isUnsafeCell := false, val := v, perm := .active, children := [] } :=
  ⟨rfl, rfl, Or.inr rfl⟩

private theorem releaseProtectorField_noChildren (callId : CallId) {fm : FieldMeta}
    (hch : fm.children = []) :
    releaseProtectorField callId fm = fm := by
  rcases fm with ⟨uc, val, perm, children⟩
  dsimp only at hch
  subst hch
  rfl

private def HeapAgreeExcept (a : AllocId) (f : FieldIdx) (fm1 fm2 : FieldMeta)
    (h1 h2 : List StructAlloc) : Prop :=
  h1.length = h2.length ∧
  (∀ a', a' ≠ a → getAt? h1 a' = getAt? h2 a') ∧
  FieldNoChildrenInv fm1 ∧
  FieldNoChildrenInv fm2 ∧
  ∃ sa1 sa2,
    getAt? h1 a = some sa1 ∧
    getAt? h2 a = some sa2 ∧
    sa1.fields.length = sa2.fields.length ∧
    (∀ f', f' ≠ f → getAt? sa1.fields f' = getAt? sa2.fields f') ∧
    getAt? sa1.fields f = some fm1 ∧
    getAt? sa2.fields f = some fm2

private theorem HeapAgreeExcept_refl {a : AllocId} {f : FieldIdx} {h : List StructAlloc}
    {sa : StructAlloc} {fm : FieldMeta}
    (hsa : getAt? h a = some sa) (hfm : getAt? sa.fields f = some fm)
    (hinv : FieldNoChildrenInv fm) :
    HeapAgreeExcept a f fm fm h h :=
  ⟨rfl, fun _ _ => rfl, hinv, hinv, sa, sa, hsa, hsa, rfl, fun _ _ => rfl, hfm, hfm⟩

private theorem HeapAgreeExcept_eq_of_fm_eq {a : AllocId} {f : FieldIdx} {fm : FieldMeta}
    {h1 h2 : List StructAlloc} (h : HeapAgreeExcept a f fm fm h1 h2) : h1 = h2 := by
  rcases h with ⟨hlen, hother, _, _, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
  apply list_eq_of_getAt? hlen
  intro a'
  by_cases ha : a' = a
  · subst ha
    rw [hsa1, hsa2]
    rcases sa1 with ⟨fs1⟩
    rcases sa2 with ⟨fs2⟩
    apply congrArg some
    apply congrArg StructAlloc.mk
    apply list_eq_of_getAt? hflen
    intro f'
    by_cases hf : f' = f
    · subst hf; rw [hfm1, hfm2]
    · exact hfother f' hf
  · exact hother a' ha

private theorem HeapAgreeExcept_set_other_alloc {a a' : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} {h1 h2 h1' h2' : List StructAlloc} {sa' : StructAlloc}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hne : a' ≠ a)
    (hs1 : setAt? h1 a' sa' = some h1') (hs2 : setAt? h2 a' sa' = some h2') :
    HeapAgreeExcept a f fm1 fm2 h1' h2' := by
  rcases h with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
  refine ⟨by rw [setAt?_length hs1, setAt?_length hs2, hlen], ?_, hinv1, hinv2, sa1, sa2,
    by rw [getAt?_setAt?_ne hs1 (Ne.symm hne), hsa1],
    by rw [getAt?_setAt?_ne hs2 (Ne.symm hne), hsa2],
    hflen, hfother, hfm1, hfm2⟩
  intro x hx
  by_cases hxa : x = a'
  · subst hxa
    rw [getAt?_setAt?_same hs1, getAt?_setAt?_same hs2]
  · rw [getAt?_setAt?_ne hs1 hxa, getAt?_setAt?_ne hs2 hxa, hother x hx]

private theorem HeapAgreeExcept_set_other_field {a : AllocId} {f f' : FieldIdx}
    {fm1 fm2 fm' : FieldMeta} {h1 h2 h1' h2' : List StructAlloc}
    {sa1 sa2 : StructAlloc} {fs1 fs2 : List FieldMeta}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hne : f' ≠ f)
    (hsa1 : getAt? h1 a = some sa1) (hsa2 : getAt? h2 a = some sa2)
    (hfs1 : setAt? sa1.fields f' fm' = some fs1) (hfs2 : setAt? sa2.fields f' fm' = some fs2)
    (hs1 : setAt? h1 a { sa1 with fields := fs1 } = some h1')
    (hs2 : setAt? h2 a { sa2 with fields := fs2 } = some h2') :
    HeapAgreeExcept a f fm1 fm2 h1' h2' := by
  rcases h with ⟨hlen, hother, hinv1, hinv2, sa1', sa2', hsa1', hsa2', hflen, hfother, hfm1, hfm2⟩
  rw [hsa1] at hsa1'; injection hsa1' with hsa1eq; subst hsa1eq
  rw [hsa2] at hsa2'; injection hsa2' with hsa2eq; subst hsa2eq
  refine ⟨by rw [setAt?_length hs1, setAt?_length hs2, hlen], ?_, hinv1, hinv2,
    { sa1 with fields := fs1 }, { sa2 with fields := fs2 },
    getAt?_setAt?_same hs1, getAt?_setAt?_same hs2,
    by rw [setAt?_length hfs1, setAt?_length hfs2, hflen], ?_,
    by rw [getAt?_setAt?_ne hfs1 (Ne.symm hne), hfm1],
    by rw [getAt?_setAt?_ne hfs2 (Ne.symm hne), hfm2]⟩
  · intro x hx
    rw [getAt?_setAt?_ne hs1 hx, getAt?_setAt?_ne hs2 hx, hother x hx]
  · intro y hy
    by_cases hyf : y = f'
    · subst hyf
      rw [getAt?_setAt?_same hfs1, getAt?_setAt?_same hfs2]
    · rw [getAt?_setAt?_ne hfs1 hyf, getAt?_setAt?_ne hfs2 hyf, hfother y hy]

private theorem HeapAgreeExcept_set_target_left {a : AllocId} {f : FieldIdx}
    {fm1 fm1' fm2 : FieldMeta} {h1 h2 h1' : List StructAlloc}
    {sa1 : StructAlloc} {fs1 : List FieldMeta}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hinv1' : FieldNoChildrenInv fm1')
    (hsa1 : getAt? h1 a = some sa1)
    (hfs1 : setAt? sa1.fields f fm1' = some fs1)
    (hs1 : setAt? h1 a { sa1 with fields := fs1 } = some h1') :
    HeapAgreeExcept a f fm1' fm2 h1' h2 := by
  rcases h with ⟨hlen, hother, _, hinv2, sa1', sa2, hsa1', hsa2, hflen, hfother, _, hfm2⟩
  rw [hsa1] at hsa1'; injection hsa1' with hsa1eq; subst hsa1eq
  refine ⟨by rw [setAt?_length hs1, hlen], ?_, hinv1', hinv2,
    { sa1 with fields := fs1 }, sa2,
    getAt?_setAt?_same hs1, hsa2,
    by rw [setAt?_length hfs1, hflen], ?_,
    getAt?_setAt?_same hfs1, hfm2⟩
  · intro x hx
    rw [getAt?_setAt?_ne hs1 hx, hother x hx]
  · intro y hy
    rw [getAt?_setAt?_ne hfs1 hy, hfother y hy]

private theorem HeapAgreeExcept_set_target_right {a : AllocId} {f : FieldIdx}
    {fm1 fm2 fm2' : FieldMeta} {h1 h2 h2' : List StructAlloc}
    {sa2 : StructAlloc} {fs2 : List FieldMeta}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hinv2' : FieldNoChildrenInv fm2')
    (hsa2 : getAt? h2 a = some sa2)
    (hfs2 : setAt? sa2.fields f fm2' = some fs2)
    (hs2 : setAt? h2 a { sa2 with fields := fs2 } = some h2') :
    HeapAgreeExcept a f fm1 fm2' h1 h2' := by
  rcases h with ⟨hlen, hother, hinv1, _, sa1, sa2', hsa1, hsa2', hflen, hfother, hfm1, _⟩
  rw [hsa2] at hsa2'; injection hsa2' with hsa2eq; subst hsa2eq
  refine ⟨by rw [setAt?_length hs2, hlen], ?_, hinv1, hinv2',
    sa1, { sa2 with fields := fs2 },
    hsa1, getAt?_setAt?_same hs2,
    by rw [setAt?_length hfs2, hflen], ?_,
    hfm1, getAt?_setAt?_same hfs2⟩
  · intro x hx
    rw [getAt?_setAt?_ne hs2 hx, hother x hx]
  · intro y hy
    rw [getAt?_setAt?_ne hfs2 hy, hfother y hy]

private theorem HeapAgreeExcept_accessHeapByPtr {a : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} {h1 h2 : List StructAlloc} {p : PtrVal}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hd : PtrDisjoint a f p)
    (acc : AccessKind) (newVal : Option UInt64) :
    (∃ e, accessHeapByPtr h1 p acc newVal = .error e ∧
          accessHeapByPtr h2 p acc newVal = .error e) ∨
    (∃ v h1' h2', accessHeapByPtr h1 p acc newVal = .ok (v, h1') ∧
                  accessHeapByPtr h2 p acc newVal = .ok (v, h2') ∧
                  HeapAgreeExcept a f fm1 fm2 h1' h2') := by
  unfold accessHeapByPtr
  cases hin : ptrInScope p with
  | false =>
    left; exact ⟨.tbUb, rfl, rfl⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases ha : p.allocId = a
    · have hfn : p.field ≠ f := by
        rcases PtrDisjoint_inScope_ne hd hin with hne | hne
        · exact absurd ha hne
        · exact hne
      rcases h with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
      have hfull : HeapAgreeExcept a f fm1 fm2 h1 h2 :=
        ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
      rw [ha, hsa1, hsa2]
      dsimp only []
      have hgf := hfother p.field hfn
      rw [← hgf]
      cases hg1 : getAt? sa1.fields p.field with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some fm0 =>
        dsimp only []
        cases htb : tbPtrAccessField acc p.tag newVal fm0 with
        | none => left; exact ⟨.tbUb, rfl, rfl⟩
        | some fm' =>
          dsimp only []
          obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
          obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
          obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
          obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
          simp only [hfs1, hfs2, hs1, hs2]
          right
          exact ⟨fm'.val, h1', h2', rfl, rfl,
            HeapAgreeExcept_set_other_field hfull hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2⟩
    · have hga := h.2.1 p.allocId ha
      rw [← hga]
      cases hg1 : getAt? h1 p.allocId with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some sa =>
        dsimp only []
        cases hgf : getAt? sa.fields p.field with
        | none => left; exact ⟨.tbUb, rfl, rfl⟩
        | some fm0 =>
          dsimp only []
          cases htb : tbPtrAccessField acc p.tag newVal fm0 with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fm' =>
            dsimp only []
            obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
            obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
            simp only [hfs', hs1, hs2]
            right
            exact ⟨fm'.val, h1', h2', rfl, rfl,
              HeapAgreeExcept_set_other_alloc h ha hs1 hs2⟩

private theorem HeapAgreeExcept_activateProtectorOne {a : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} {h1 h2 : List StructAlloc} {p : PtrVal}
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) (hd : PtrDisjoint a f p) (callId : CallId) :
    (∃ e, activateProtectorOne callId h1 p = .error e ∧
          activateProtectorOne callId h2 p = .error e) ∨
    (∃ h1' h2', activateProtectorOne callId h1 p = .ok h1' ∧
                activateProtectorOne callId h2 p = .ok h2' ∧
                HeapAgreeExcept a f fm1 fm2 h1' h2') := by
  unfold activateProtectorOne
  cases hk : p.kind with
  | rawMut => right; exact ⟨h1, h2, rfl, rfl, h⟩
  | shared | mutRef =>
    dsimp only []
    cases hin : ptrInScope p with
    | false => left; exact ⟨.tbUb, rfl, rfl⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases ha : p.allocId = a
      · rcases hd with hne | ⟨f', hsc, hfn⟩
        · exact absurd ha hne
        · rcases h with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hfull : HeapAgreeExcept a f fm1 fm2 h1 h2 :=
            ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          rw [ha, hsa1, hsa2, hsc]
          dsimp only []
          have hgf := hfother f' hfn
          rw [← hgf]
          cases hg1 : getAt? sa1.fields f' with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases hap : activateProtectorField p.tag callId fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
              obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
              simp only [hfs1, hfs2, hs1, hs2]
              right
              exact ⟨h1', h2', rfl, rfl,
                HeapAgreeExcept_set_other_field hfull hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2⟩
      · have hga := h.2.1 p.allocId ha
        rw [← hga]
        cases hg1 : getAt? h1 p.allocId with
        | none => left; exact ⟨.tbUb, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases hsc : p.scope with
          | wholeStruct =>
            dsimp only []
            cases hap : activateProtectorAllFields p.tag callId sa.fields with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fs' =>
              dsimp only []
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
              simp only [hs1, hs2]
              right
              exact ⟨h1', h2', rfl, rfl, HeapAgreeExcept_set_other_alloc h ha hs1 hs2⟩
          | fieldOnly f' =>
            dsimp only []
            cases hgf : getAt? sa.fields f' with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases hap : activateProtectorField p.tag callId fm0 with
              | none => left; exact ⟨.tbUb, rfl, rfl⟩
              | some fm' =>
                dsimp only []
                obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
                simp only [hfs', hs1, hs2]
                right
                exact ⟨h1', h2', rfl, rfl, HeapAgreeExcept_set_other_alloc h ha hs1 hs2⟩

private theorem HeapAgreeExcept_activateProtectors {a : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} (callId : CallId) :
    ∀ {ps : List PtrVal} {h1 h2 : List StructAlloc},
      HeapAgreeExcept a f fm1 fm2 h1 h2 →
      (∀ p ∈ ps, PtrDisjoint a f p) →
      (∃ e, activateProtectors callId h1 ps = .error e ∧
            activateProtectors callId h2 ps = .error e) ∨
      (∃ h1' h2', activateProtectors callId h1 ps = .ok h1' ∧
                  activateProtectors callId h2 ps = .ok h2' ∧
                  HeapAgreeExcept a f fm1 fm2 h1' h2')
  | [], h1, h2, h, _ => Or.inr ⟨h1, h2, rfl, rfl, h⟩
  | p :: ps, h1, h2, h, hds => by
    simp only [activateProtectors]
    have h1step := HeapAgreeExcept_activateProtectorOne h (hds p List.mem_cons_self) callId
    rcases h1step with ⟨e, he1, he2⟩ | ⟨h1', h2', ho1, ho2, h'⟩
    · left; exact ⟨e, by rw [he1], by rw [he2]⟩
    · rw [ho1, ho2]
      exact HeapAgreeExcept_activateProtectors callId h' (fun q hq => hds q (List.mem_cons_of_mem _ hq))

private theorem HeapAgreeExcept_stepCalleeOps {a : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} {args : List PtrVal}
    (hds : ∀ p ∈ args, PtrDisjoint a f p) :
    ∀ {ops : List CalleeOp} {h1 h2 : List StructAlloc} {tr : List ObsEvent},
      HeapAgreeExcept a f fm1 fm2 h1 h2 →
      (∃ e, stepCalleeOps args h1 tr ops = .error e ∧
            stepCalleeOps args h2 tr ops = .error e) ∨
      (∃ h1' h2' tr', stepCalleeOps args h1 tr ops = .ok (h1', tr') ∧
                      stepCalleeOps args h2 tr ops = .ok (h2', tr') ∧
                      HeapAgreeExcept a f fm1 fm2 h1' h2')
  | [], h1, h2, tr, h => Or.inr ⟨h1, h2, tr, rfl, rfl, h⟩
  | .emitEvent code :: rest, h1, h2, tr, h =>
    HeapAgreeExcept_stepCalleeOps hds (ops := rest) (tr := tr ++ [.calleeIo code]) h
  | .readArg idx off emitLog :: rest, h1, h2, tr, h => by
    simp only [stepCalleeOps]
    cases hg : getAt? args idx with
    | none => left; exact ⟨.unsupported, rfl, rfl⟩
    | some p =>
      dsimp only []
      have hp := PtrDisjoint_applyPtrOffset (hds p (getAt?_mem hg)) off
      rcases HeapAgreeExcept_accessHeapByPtr h hp .read none with ⟨e, he1, he2⟩ | ⟨v, h1', h2', ho1, ho2, h'⟩
      · left; exact ⟨e, by rw [he1], by rw [he2]⟩
      · rw [ho1, ho2]
        exact HeapAgreeExcept_stepCalleeOps hds (ops := rest) h'
  | .writeArg idx off v :: rest, h1, h2, tr, h => by
    simp only [stepCalleeOps]
    cases hg : getAt? args idx with
    | none => left; exact ⟨.unsupported, rfl, rfl⟩
    | some p =>
      dsimp only []
      have hp := PtrDisjoint_applyPtrOffset (hds p (getAt?_mem hg)) off
      rcases HeapAgreeExcept_accessHeapByPtr h hp .write (some v) with ⟨e, he1, he2⟩ | ⟨_, h1', h2', ho1, ho2, h'⟩
      · left; exact ⟨e, by rw [he1], by rw [he2]⟩
      · rw [ho1, ho2]
        exact HeapAgreeExcept_stepCalleeOps hds (ops := rest) h'

private theorem HeapAgreeExcept_releaseProtectorHeap {a : AllocId} {f : FieldIdx}
    {fm1 fm2 : FieldMeta} {h1 h2 : List StructAlloc} (callId : CallId)
    (h : HeapAgreeExcept a f fm1 fm2 h1 h2) :
    HeapAgreeExcept a f fm1 fm2 (releaseProtectorHeap callId h1) (releaseProtectorHeap callId h2) := by
  rcases h with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
  refine ⟨by simp [releaseProtectorHeap, hlen], ?_, hinv1, hinv2,
    { sa1 with fields := sa1.fields.map (releaseProtectorField callId) },
    { sa2 with fields := sa2.fields.map (releaseProtectorField callId) },
    by simp [releaseProtectorHeap, getAt?_map, hsa1],
    by simp [releaseProtectorHeap, getAt?_map, hsa2],
    by simp [hflen], ?_,
    by simp [getAt?_map, hfm1, releaseProtectorField_noChildren callId hinv1.2.1],
    by simp [getAt?_map, hfm2, releaseProtectorField_noChildren callId hinv2.2.1]⟩
  · intro a' ha
    simp [releaseProtectorHeap, getAt?_map, hother a' ha]
  · intro f' hf
    simp [getAt?_map, hfother f' hf]

/-! #### Theorem 1 Helpers (`partial_sroa_refinement`) -/

private def SharedChildrenInv (cs : List BorrowNode) : Prop :=
  ∀ n ∈ cs, n.perm = .frozen ∨ n.perm = .disabled

private def SharedFieldInv (fm : FieldMeta) : Prop :=
  fm.isUnsafeCell = false ∧
  (fm.perm = .reserved false ∨ fm.perm = .active) ∧
  SharedChildrenInv fm.children

private def HeapSharedInv (a : AllocId) (f : FieldIdx) (fm : FieldMeta) (h : List StructAlloc) : Prop :=
  SharedFieldInv fm ∧
  ∃ sa, getAt? h a = some sa ∧ getAt? sa.fields f = some fm

private theorem SharedFieldInv_init : SharedFieldInv (initFieldMeta false) :=
  ⟨rfl, Or.inl rfl, fun _ h => by cases h⟩

private theorem stepForeignChildren_read_shared :
    ∀ {cs : List BorrowNode}, SharedChildrenInv cs →
      stepForeignChildren false .read cs = some cs
  | [], _ => rfl
  | n :: rest, h => by
    have hn := h n List.mem_cons_self
    have hrest := stepForeignChildren_read_shared (fun m hm => h m (List.mem_cons_of_mem _ hm))
    simp only [stepForeignChildren, hrest]
    rcases n with ⟨tag, perm, prot⟩
    dsimp only at hn
    rcases hn with rfl | rfl <;> rfl

private theorem tbRootAccessField_read_shared {fm : FieldMeta} (h : SharedFieldInv fm) :
    tbRootAccessField .read none fm = some fm := by
  rcases h with ⟨huc, hp, hcs⟩
  rcases fm with ⟨uc, val, perm, children⟩
  dsimp only at huc hp hcs
  subst huc
  have hfc := stepForeignChildren_read_shared hcs
  simp only [tbRootAccessField, hfc]
  rcases hp with rfl | rfl <;> rfl

private theorem stepForeignChildren_write_shared :
    ∀ {cs cs' : List BorrowNode}, SharedChildrenInv cs →
      stepForeignChildren false .write cs = some cs' → SharedChildrenInv cs'
  | [], _, _, h => by
    simp only [stepForeignChildren, Option.some.injEq] at h
    subst h
    intro _ hm; cases hm
  | n :: rest, _, h, hstep => by
    simp only [stepForeignChildren] at hstep
    cases ht : tbForeignStep false n.protector.isSome .write n.perm with
    | none => simp [ht] at hstep
    | some perm' =>
      cases hr : stepForeignChildren false .write rest with
      | none => simp [ht, hr] at hstep
      | some rest' =>
        simp only [ht, hr, Option.some.injEq] at hstep
        subst hstep
        intro m hm
        cases hm with
        | head =>
          have hn := h n List.mem_cons_self
          rcases hn with hfr | hdis
          · rw [hfr] at ht
            simp only [tbForeignStep] at ht
            cases hp : n.protector.isSome <;> simp [hp] at ht
            subst ht; exact Or.inr rfl
          · rw [hdis] at ht
            simp only [tbForeignStep, Option.some.injEq] at ht
            subst ht; exact Or.inr rfl
        | tail _ hmt =>
          exact stepForeignChildren_write_shared (fun x hx => h x (List.mem_cons_of_mem _ hx)) hr m hmt

private theorem tbRootAccessField_write_shared {fm fm' : FieldMeta} {v : UInt64}
    (h : SharedFieldInv fm) (hw : tbRootAccessField .write (some v) fm = some fm') :
    SharedFieldInv fm' ∧ fm'.val = v := by
  rcases h with ⟨huc, hp, hcs⟩
  simp only [tbRootAccessField, huc] at hw
  cases hfc : stepForeignChildren false .write fm.children with
  | none =>
    rcases hp with hp | hp <;> simp [hp, tbChildStep, hfc] at hw
  | some cs' =>
    have hcs' := stepForeignChildren_write_shared hcs hfc
    rcases hp with hp | hp <;>
      (simp only [hp, tbChildStep, hfc, Option.some.injEq] at hw; subst hw;
       exact ⟨⟨rfl, Or.inr rfl, hcs'⟩, rfl⟩)

private theorem stepTagChildren_read_shared (accTag : TagId) :
    ∀ {cs cs' : List BorrowNode} {b : Bool}, SharedChildrenInv cs →
      stepTagChildren false .read accTag cs = some (cs', b) → SharedChildrenInv cs'
  | [], _, _, _, h => by
    simp only [stepTagChildren, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    intro _ hm; cases hm
  | n :: rest, _, _, h, hstep => by
    simp only [stepTagChildren] at hstep
    have hn := h n List.mem_cons_self
    have hrest : SharedChildrenInv rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases htag : n.tag == accTag
    · simp only [htag, ↓reduceIte] at hstep
      cases hc : tbChildStep n.protector.isSome .read n.perm with
      | none => simp [hc] at hstep
      | some perm' =>
        cases hr : stepTagChildren false .read accTag rest with
        | none => simp [hc, hr] at hstep
        | some res =>
          rcases res with ⟨rest', b'⟩
          simp only [hc, hr, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, _⟩
          intro m hm
          cases hm with
          | head =>
            rcases hn with hfr | hdis
            · rw [hfr] at hc; simp [tbChildStep] at hc; subst hc; exact Or.inl rfl
            · rw [hdis] at hc; simp [tbChildStep] at hc
          | tail _ hmt => exact stepTagChildren_read_shared accTag hrest hr m hmt
    · simp only [htag, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hf : tbForeignStep false n.protector.isSome .read n.perm with
      | none => simp [hf] at hstep
      | some perm' =>
        cases hr : stepTagChildren false .read accTag rest with
        | none => simp [hf, hr] at hstep
        | some res =>
          rcases res with ⟨rest', b'⟩
          simp only [hf, hr, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, _⟩
          intro m hm
          cases hm with
          | head =>
            rcases hn with hfr | hdis
            · rw [hfr] at hf; simp [tbForeignStep] at hf; subst hf; exact Or.inl rfl
            · rw [hdis] at hf; simp [tbForeignStep] at hf; subst hf; exact Or.inr rfl
          | tail _ hmt => exact stepTagChildren_read_shared accTag hrest hr m hmt

private theorem tbPtrAccessField_read_shared {fm fm' : FieldMeta} {accTag : TagId}
    (h : SharedFieldInv fm) (hr : tbPtrAccessField .read accTag none fm = some fm') :
    SharedFieldInv fm' ∧ fm'.val = fm.val := by
  rcases h with ⟨huc, hp, hcs⟩
  simp only [tbPtrAccessField, huc] at hr
  cases hst : stepTagChildren false .read accTag fm.children with
  | none =>
    rcases hp with hp | hp <;> simp [hp, tbChildStep, hst] at hr
  | some res =>
    rcases res with ⟨cs', found⟩
    cases found with
    | false => rcases hp with hp | hp <;> simp [hp, tbChildStep, hst] at hr
    | true =>
      have hcs' := stepTagChildren_read_shared accTag hcs hst
      rcases hp with hp | hp <;>
        (simp only [hp, tbChildStep, hst, Option.some.injEq] at hr; subst hr;
         exact ⟨⟨rfl, by first | exact Or.inl rfl | exact Or.inr rfl, hcs'⟩, rfl⟩)

private theorem stepTagChildren_write_shared_false (accTag : TagId) :
    ∀ {cs cs' : List BorrowNode} {b : Bool}, SharedChildrenInv cs →
      stepTagChildren false .write accTag cs = some (cs', b) → b = false
  | [], _, _, _, h => by
    simp only [stepTagChildren, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | n :: rest, _, _, h, hstep => by
    simp only [stepTagChildren] at hstep
    have hn := h n List.mem_cons_self
    have hrest : SharedChildrenInv rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases htag : n.tag == accTag
    · simp only [htag, ↓reduceIte] at hstep
      rcases hn with hfr | hdis
      · simp [hfr, tbChildStep] at hstep
      · simp [hdis, tbChildStep] at hstep
    · simp only [htag, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hf : tbForeignStep false n.protector.isSome .write n.perm with
      | none => simp [hf] at hstep
      | some perm' =>
        cases hr : stepTagChildren false .write accTag rest with
        | none => simp [hf, hr] at hstep
        | some res =>
          rcases res with ⟨rest', b'⟩
          simp only [hf, hr, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨_, rfl⟩
          exact stepTagChildren_write_shared_false accTag hrest hr

private theorem tbPtrAccessField_write_shared_none {fm : FieldMeta} {accTag : TagId} {v : UInt64}
    (h : SharedFieldInv fm) :
    tbPtrAccessField .write accTag (some v) fm = none := by
  rcases h with ⟨huc, _, hcs⟩
  simp only [tbPtrAccessField, huc]
  cases hst : stepTagChildren false .write accTag fm.children with
  | none => cases tbChildStep false .write fm.perm <;> rfl
  | some res =>
    rcases res with ⟨cs', found⟩
    have hf := stepTagChildren_write_shared_false accTag hcs hst
    subst hf
    cases tbChildStep false .write fm.perm <;> rfl

private theorem tbRetagField_shared {fm fm' : FieldMeta} {tag : TagId}
    (h : SharedFieldInv fm) (hr : tbRetagField tag .shared fm = some fm') :
    SharedFieldInv fm' ∧ fm'.val = fm.val := by
  have hread := tbRootAccessField_read_shared h
  simp only [tbRetagField, hread, Option.some.injEq] at hr
  subst hr
  rcases h with ⟨huc, hp, hcs⟩
  refine ⟨⟨huc, hp, ?_⟩, rfl⟩
  intro n hn
  simp only [List.mem_append, List.mem_singleton] at hn
  rcases hn with hin | rfl
  · exact hcs n hin
  · simp [huc, initialBorrowPerm]

private theorem tbRetagAllFields_getAt? (tag : TagId) (kind : BorrowKind) :
    ∀ {fs fs' : List FieldMeta} {i : Nat} {fm : FieldMeta},
      tbRetagAllFields tag kind fs = some fs' →
      getAt? fs i = some fm →
      ∃ fm', tbRetagField tag kind fm = some fm' ∧ getAt? fs' i = some fm'
  | [], _, _, _, _, hg => by simp [getAt?] at hg
  | x :: xs, _, 0, fm, h, hg => by
    simp only [getAt?, Option.some.injEq] at hg
    subst hg
    simp only [tbRetagAllFields] at h
    cases h1 : tbRetagField tag kind x with
    | none => simp [h1] at h
    | some fm' =>
      cases h2 : tbRetagAllFields tag kind xs with
      | none => simp [h1, h2] at h
      | some xs' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact ⟨fm', rfl, rfl⟩
  | x :: xs, _, i + 1, fm, h, hg => by
    simp only [tbRetagAllFields] at h
    cases h1 : tbRetagField tag kind x with
    | none => simp [h1] at h
    | some x' =>
      cases h2 : tbRetagAllFields tag kind xs with
      | none => simp [h1, h2] at h
      | some xs' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        simp only [getAt?]
        exact tbRetagAllFields_getAt? tag kind h2 hg

private theorem activateProtectorNodes_shared (tag : TagId) (callId : CallId) :
    ∀ {cs cs' : List BorrowNode} {b : Bool}, SharedChildrenInv cs →
      activateProtectorNodes tag callId cs = some (cs', b) → SharedChildrenInv cs'
  | [], _, _, _, h => by
    simp only [activateProtectorNodes, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    intro _ hm; cases hm
  | n :: rest, _, _, h, hstep => by
    have hn := h n List.mem_cons_self
    have hrest : SharedChildrenInv rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [activateProtectorNodes] at hstep
    by_cases htag : n.tag == tag
    · simp only [htag, ↓reduceIte] at hstep
      by_cases hdis : n.perm == .disabled
      · simp [hdis] at hstep
      · simp only [hdis, Bool.false_eq_true, ↓reduceIte] at hstep
        cases hr : activateProtectorNodes tag callId rest with
        | none => simp [hr] at hstep
        | some res =>
          rcases res with ⟨rest', b'⟩
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, _⟩
          intro m hm
          cases hm with
          | head => exact hn
          | tail _ hmt => exact activateProtectorNodes_shared tag callId hrest hr m hmt
    · simp only [htag, Bool.false_eq_true, ↓reduceIte] at hstep
      cases hr : activateProtectorNodes tag callId rest with
      | none => simp [hr] at hstep
      | some res =>
        rcases res with ⟨rest', b'⟩
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨rfl, _⟩
        intro m hm
        cases hm with
        | head => exact hn
        | tail _ hmt => exact activateProtectorNodes_shared tag callId hrest hr m hmt

private theorem activateProtectorField_shared {fm fm' : FieldMeta} {tag : TagId} {callId : CallId}
    (h : SharedFieldInv fm) (ha : activateProtectorField tag callId fm = some fm') :
    SharedFieldInv fm' ∧ fm'.val = fm.val := by
  simp only [activateProtectorField] at ha
  cases hn : activateProtectorNodes tag callId fm.children with
  | none => simp [hn] at ha
  | some res =>
    rcases res with ⟨cs', found⟩
    cases found with
    | false => simp [hn] at ha
    | true =>
      simp only [hn, Option.some.injEq] at ha
      subst ha
      exact ⟨⟨h.1, h.2.1, activateProtectorNodes_shared tag callId h.2.2 hn⟩, rfl⟩

private theorem activateProtectorAllFields_getAt? (tag : TagId) (callId : CallId) :
    ∀ {fs fs' : List FieldMeta} {i : Nat} {fm : FieldMeta},
      activateProtectorAllFields tag callId fs = some fs' →
      getAt? fs i = some fm →
      ∃ fm', activateProtectorField tag callId fm = some fm' ∧ getAt? fs' i = some fm'
  | [], _, _, _, _, hg => by simp [getAt?] at hg
  | x :: xs, _, 0, fm, h, hg => by
    simp only [getAt?, Option.some.injEq] at hg
    subst hg
    simp only [activateProtectorAllFields] at h
    cases h1 : activateProtectorField tag callId x with
    | none => simp [h1] at h
    | some fm' =>
      cases h2 : activateProtectorAllFields tag callId xs with
      | none => simp [h1, h2] at h
      | some xs' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact ⟨fm', rfl, rfl⟩
  | x :: xs, _, i + 1, fm, h, hg => by
    simp only [activateProtectorAllFields] at h
    cases h1 : activateProtectorField tag callId x with
    | none => simp [h1] at h
    | some x' =>
      cases h2 : activateProtectorAllFields tag callId xs with
      | none => simp [h1, h2] at h
      | some xs' =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        simp only [getAt?]
        exact activateProtectorAllFields_getAt? tag callId h2 hg

private theorem releaseProtectorField_shared (callId : CallId) {fm : FieldMeta}
    (h : SharedFieldInv fm) :
    SharedFieldInv (releaseProtectorField callId fm) ∧
      (releaseProtectorField callId fm).val = fm.val := by
  refine ⟨⟨h.1, h.2.1, ?_⟩, rfl⟩
  intro n hn
  simp only [releaseProtectorField, List.mem_map] at hn
  rcases hn with ⟨m, hm, rfl⟩
  have hmp := h.2.2 m hm
  by_cases hp : m.protector == some callId <;> simp [hp, hmp]

private theorem HeapSharedInv_accessHeapByPtr {a : AllocId} {f : FieldIdx} {fm : FieldMeta}
    {h h' : List StructAlloc} {p : PtrVal} {acc : AccessKind} {newVal : Option UInt64} {v : UInt64}
    (hinv : HeapSharedInv a f fm h)
    (hacc : accessHeapByPtr h p acc newVal = .ok (v, h'))
    (hnoWrite : acc = .read → newVal = none) :
    ∃ fm', HeapSharedInv a f fm' h' ∧ fm'.val = fm.val := by
  rcases hinv with ⟨hsf, sa, hsa, hfm⟩
  unfold accessHeapByPtr at hacc
  cases hin : ptrInScope p with
  | false => simp [hin] at hacc
  | true =>
    simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hacc
    cases hga : getAt? h p.allocId with
    | none => simp [hga] at hacc
    | some sa0 =>
      simp only [hga] at hacc
      cases hgf : getAt? sa0.fields p.field with
      | none => simp [hgf] at hacc
      | some fm0 =>
        simp only [hgf] at hacc
        cases htb : tbPtrAccessField acc p.tag newVal fm0 with
        | none => simp [htb] at hacc
        | some fm1 =>
          simp only [htb] at hacc
          cases hfs : setAt? sa0.fields p.field fm1 with
          | none => simp [hfs] at hacc
          | some fs' =>
            simp only [hfs] at hacc
            cases hhs : setAt? h p.allocId { sa0 with fields := fs' } with
            | none => simp [hhs] at hacc
            | some h1 =>
              simp only [hhs, Except.ok.injEq, Prod.mk.injEq] at hacc
              rcases hacc with ⟨_, rfl⟩
              by_cases ha : p.allocId = a
              · subst ha
                rw [hsa] at hga; injection hga with heq; subst heq
                by_cases hf : p.field = f
                · subst hf
                  rw [hfm] at hgf; injection hgf with hfeq; subst hfeq
                  cases acc with
                  | read =>
                    have hnv := hnoWrite rfl
                    subst hnv
                    obtain ⟨hsf1, hv1⟩ := tbPtrAccessField_read_shared hsf htb
                    exact ⟨fm1, ⟨hsf1, { sa with fields := fs' }, getAt?_setAt?_same hhs,
                      getAt?_setAt?_same hfs⟩, hv1⟩
                  | write =>
                    cases newVal with
                    | some w =>
                      rw [tbPtrAccessField_write_shared_none hsf] at htb
                      cases htb
                    | none =>
                      rcases hsf with ⟨huc, _, hcs⟩
                      simp only [tbPtrAccessField, huc] at htb
                      cases hst : stepTagChildren false .write p.tag fm.children with
                      | none => cases tbChildStep false .write fm.perm <;> simp [hst] at htb
                      | some res =>
                        rcases res with ⟨_, found⟩
                        have hfalse := stepTagChildren_write_shared_false p.tag hcs hst
                        subst hfalse
                        cases tbChildStep false .write fm.perm <;> simp [hst] at htb
                · exact ⟨fm, ⟨hsf, { sa with fields := fs' }, getAt?_setAt?_same hhs,
                    by rw [getAt?_setAt?_ne hfs (Ne.symm hf), hfm]⟩, rfl⟩
              · exact ⟨fm, ⟨hsf, sa, by rw [getAt?_setAt?_ne hhs (Ne.symm ha), hsa], hfm⟩, rfl⟩

private theorem HeapSharedInv_activateProtectorOne {a : AllocId} {f : FieldIdx} {fm : FieldMeta}
    {h h' : List StructAlloc} {p : PtrVal} {callId : CallId}
    (hinv : HeapSharedInv a f fm h)
    (hap : activateProtectorOne callId h p = .ok h') :
    ∃ fm', HeapSharedInv a f fm' h' ∧ fm'.val = fm.val := by
  rcases hinv with ⟨hsf, sa, hsa, hfm⟩
  unfold activateProtectorOne at hap
  cases hk : p.kind with
  | rawMut =>
    simp only [hk, Except.ok.injEq] at hap; subst hap
    exact ⟨fm, ⟨hsf, sa, hsa, hfm⟩, rfl⟩
  | shared | mutRef =>
    simp only [hk] at hap
    cases hin : ptrInScope p with
    | false => simp [hin] at hap
    | true =>
      simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hap
      cases hga : getAt? h p.allocId with
      | none => simp [hga] at hap
      | some sa0 =>
        simp only [hga] at hap
        cases hsc : p.scope with
        | wholeStruct =>
          simp only [hsc] at hap
          cases hall : activateProtectorAllFields p.tag callId sa0.fields with
          | none => simp [hall] at hap
          | some fs' =>
            simp only [hall] at hap
            cases hhs : setAt? h p.allocId { sa0 with fields := fs' } with
            | none => simp [hhs] at hap
            | some h1 =>
              simp only [hhs, Except.ok.injEq] at hap; subst hap
              by_cases ha : p.allocId = a
              · subst ha
                rw [hsa] at hga; injection hga with heq; subst heq
                obtain ⟨fm', hact, hget'⟩ := activateProtectorAllFields_getAt? p.tag callId hall hfm
                obtain ⟨hsf', hv'⟩ := activateProtectorField_shared hsf hact
                exact ⟨fm', ⟨hsf', { sa with fields := fs' }, getAt?_setAt?_same hhs, hget'⟩, hv'⟩
              · exact ⟨fm, ⟨hsf, sa, by rw [getAt?_setAt?_ne hhs (Ne.symm ha), hsa], hfm⟩, rfl⟩
        | fieldOnly f' =>
          simp only [hsc] at hap
          cases hgf : getAt? sa0.fields f' with
          | none => simp [hgf] at hap
          | some fm0 =>
            simp only [hgf] at hap
            cases hact : activateProtectorField p.tag callId fm0 with
            | none => simp [hact] at hap
            | some fm1 =>
              simp only [hact] at hap
              cases hfs : setAt? sa0.fields f' fm1 with
              | none => simp [hfs] at hap
              | some fs' =>
                simp only [hfs] at hap
                cases hhs : setAt? h p.allocId { sa0 with fields := fs' } with
                | none => simp [hhs] at hap
                | some h1 =>
                  simp only [hhs, Except.ok.injEq] at hap; subst hap
                  by_cases ha : p.allocId = a
                  · subst ha
                    rw [hsa] at hga; injection hga with heq; subst heq
                    by_cases hf : f' = f
                    · subst hf
                      rw [hfm] at hgf; injection hgf with hfeq; subst hfeq
                      obtain ⟨hsf1, hv1⟩ := activateProtectorField_shared hsf hact
                      exact ⟨fm1, ⟨hsf1, { sa with fields := fs' }, getAt?_setAt?_same hhs,
                        getAt?_setAt?_same hfs⟩, hv1⟩
                    · exact ⟨fm, ⟨hsf, { sa with fields := fs' }, getAt?_setAt?_same hhs,
                        by rw [getAt?_setAt?_ne hfs (Ne.symm hf), hfm]⟩, rfl⟩
                  · exact ⟨fm, ⟨hsf, sa, by rw [getAt?_setAt?_ne hhs (Ne.symm ha), hsa], hfm⟩, rfl⟩

private theorem HeapSharedInv_activateProtectors {a : AllocId} {f : FieldIdx} (callId : CallId) :
    ∀ {ps : List PtrVal} {fm : FieldMeta} {h h' : List StructAlloc},
      HeapSharedInv a f fm h →
      activateProtectors callId h ps = .ok h' →
      ∃ fm', HeapSharedInv a f fm' h' ∧ fm'.val = fm.val
  | [], fm, h, _, hinv, hap => by
    simp only [activateProtectors, Except.ok.injEq] at hap; subst hap
    exact ⟨fm, hinv, rfl⟩
  | p :: ps, fm, h, _, hinv, hap => by
    simp only [activateProtectors] at hap
    cases h1 : activateProtectorOne callId h p with
    | error e => simp [h1] at hap
    | ok h1' =>
      simp only [h1] at hap
      obtain ⟨fm1, hinv1, hv1⟩ := HeapSharedInv_activateProtectorOne hinv h1
      obtain ⟨fm2, hinv2, hv2⟩ := HeapSharedInv_activateProtectors callId hinv1 hap
      exact ⟨fm2, hinv2, hv2.trans hv1⟩

private theorem HeapSharedInv_stepCalleeOps {a : AllocId} {f : FieldIdx} {args : List PtrVal} :
    ∀ {ops : List CalleeOp} {fm : FieldMeta} {h h' : List StructAlloc} {tr tr' : List ObsEvent},
      HeapSharedInv a f fm h →
      stepCalleeOps args h tr ops = .ok (h', tr') →
      ∃ fm', HeapSharedInv a f fm' h' ∧ fm'.val = fm.val
  | [], fm, h, _, tr, _, hinv, hst => by
    simp only [stepCalleeOps, Except.ok.injEq, Prod.mk.injEq] at hst
    rcases hst with ⟨rfl, _⟩
    exact ⟨fm, hinv, rfl⟩
  | .emitEvent code :: rest, fm, h, h', tr, tr', hinv, hst =>
    HeapSharedInv_stepCalleeOps (ops := rest) hinv hst
  | .readArg idx off emitLog :: rest, fm, h, h', tr, tr', hinv, hst => by
    simp only [stepCalleeOps] at hst
    cases hg : getAt? args idx with
    | none => simp [hg] at hst
    | some p =>
      simp only [hg] at hst
      cases hacc : accessHeapByPtr h (applyPtrOffset p off) .read none with
      | error e => simp [hacc] at hst
      | ok res =>
        rcases res with ⟨v, h1⟩
        simp only [hacc] at hst
        obtain ⟨fm1, hinv1, hv1⟩ := HeapSharedInv_accessHeapByPtr hinv hacc (fun _ => rfl)
        obtain ⟨fm2, hinv2, hv2⟩ := HeapSharedInv_stepCalleeOps (ops := rest) hinv1 hst
        exact ⟨fm2, hinv2, hv2.trans hv1⟩
  | .writeArg idx off v :: rest, fm, h, h', tr, tr', hinv, hst => by
    simp only [stepCalleeOps] at hst
    cases hg : getAt? args idx with
    | none => simp [hg] at hst
    | some p =>
      simp only [hg] at hst
      cases hacc : accessHeapByPtr h (applyPtrOffset p off) .write (some v) with
      | error e => simp [hacc] at hst
      | ok res =>
        rcases res with ⟨_, h1⟩
        simp only [hacc] at hst
        obtain ⟨fm1, hinv1, hv1⟩ := HeapSharedInv_accessHeapByPtr hinv hacc (fun h => by cases h)
        obtain ⟨fm2, hinv2, hv2⟩ := HeapSharedInv_stepCalleeOps (ops := rest) hinv1 hst
        exact ⟨fm2, hinv2, hv2.trans hv1⟩

private theorem HeapSharedInv_releaseProtectorHeap {a : AllocId} {f : FieldIdx} {fm : FieldMeta}
    {h : List StructAlloc} (callId : CallId) (hinv : HeapSharedInv a f fm h) :
    ∃ fm', HeapSharedInv a f fm' (releaseProtectorHeap callId h) ∧ fm'.val = fm.val := by
  rcases hinv with ⟨hsf, sa, hsa, hfm⟩
  obtain ⟨hsf', hv'⟩ := releaseProtectorField_shared callId hsf
  exact ⟨releaseProtectorField callId fm,
    ⟨hsf', { sa with fields := sa.fields.map (releaseProtectorField callId) },
      by simp [releaseProtectorHeap, getAt?_map, hsa],
      by simp [getAt?_map, hfm]⟩, hv'⟩

private def ValRegsAgreeExcept (r : ValRegId) (e1 e2 : ValRegEnv) : Prop :=
  ∀ x, x ≠ r → e1 x = e2 x

private theorem evalValOp_congr {r : ValRegId} {e1 e2 : ValRegEnv} {op : ValOp}
    (hagr : ValRegsAgreeExcept r e1 e2) (hun : valOpUnused op r = true) :
    evalValOp e1 op = evalValOp e2 op := by
  cases op with
  | constU64 _ => rfl
  | reg x =>
    simp only [valOpUnused, bne_iff_ne, ne_eq] at hun
    simp only [evalValOp, hagr x hun]

private theorem ValRegsAgreeExcept_bind {r dst : ValRegId} {e1 e2 : ValRegEnv} (v : UInt64)
    (hagr : ValRegsAgreeExcept r e1 e2) :
    ValRegsAgreeExcept r (bindValReg e1 dst v) (bindValReg e2 dst v) := by
  intro x hne
  unfold bindValReg
  cases x == dst
  · exact hagr x hne
  · rfl

private theorem ValRegsAgreeExcept_bindOpt {r : ValRegId} {dst : Option ValRegId}
    {e1 e2 : ValRegEnv} (v : UInt64) (hagr : ValRegsAgreeExcept r e1 e2) :
    ValRegsAgreeExcept r (bindOptValReg e1 dst v) (bindOptValReg e2 dst v) := by
  cases dst with
  | none => exact hagr
  | some d => exact ValRegsAgreeExcept_bind v hagr

private theorem bindOptValReg_ne {r : ValRegId} {dst : Option ValRegId} {env : ValRegEnv}
    (v : UInt64) (hne : dst ≠ some r) :
    bindOptValReg env dst v r = env r := by
  cases dst with
  | none => rfl
  | some d =>
    apply bindValReg_ne
    intro h; exact hne (congrArg some h.symm)

private def SroaStateRel (cert : PartialSroaCert) (st_s st_t : ExecState) : Prop :=
  ValRegsAgreeExcept cert.ssaReg st_s.valRegs st_t.valRegs ∧
  st_s.ptrRegs = st_t.ptrRegs ∧
  st_s.nextTag = st_t.nextTag ∧
  st_s.nextCallId = st_t.nextCallId ∧
  st_s.trace = st_t.trace ∧
  st_s.unwindState = st_t.unwindState ∧
  match cert.mode with
  | .fullSplit =>
    (∀ pr p, st_s.ptrRegs pr = some p → PtrDisjoint cert.alloc cert.field p) ∧
    ∃ fm_s fm_t,
      HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap ∧
      st_t.valRegs cert.ssaReg = some fm_s.val
  | .sharedReadPromote =>
    st_s.heap = st_t.heap ∧
    ∃ fm_s,
      HeapSharedInv cert.alloc cert.field fm_s st_s.heap ∧
      st_t.valRegs cert.ssaReg = some fm_s.val

private theorem sroa_step_stmt {cert : PartialSroaCert} {st_s st_t : ExecState} {s : MirStmt}
    (hrel : SroaStateRel cert st_s st_t)
    (hun : stmtValRegUnused cert.ssaReg s = true)
    (hall : stmtAllowedForSroa cert.mode cert.alloc cert.field s = true) :
    (∃ e, stepMirStmt st_s s = .error e ∧
          stepMirStmts st_t (rewriteStmtForSroa cert.mode cert.alloc cert.field cert.ssaReg s) = .error e) ∨
    (∃ st_s' st_t',
      stepMirStmt st_s s = .ok st_s' ∧
      stepMirStmts st_t (rewriteStmtForSroa cert.mode cert.alloc cert.field cert.ssaReg s) = .ok st_t' ∧
      SroaStateRel cert st_s' st_t') := by
  rcases hrel with ⟨hvr, hpr, hnt, hnc, htr, huw, hmode⟩
  cases s with
  | landingPad dst =>
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, stmtValRegUnused, bne_iff_ne, ne_eq] at hun ⊢
    rw [← huw]
    cases hu : st_s.unwindState with
    | enteringCleanup payload =>
      right
      refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bindOpt payload hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
      cases hm : cert.mode <;> simp only [hm] at hmode ⊢
      · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
        exact ⟨hpd, fm_s, fm_t, hha, by rw [bindOptValReg_ne payload hun, hreg]⟩
      · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
        exact ⟨hheq, fm_s, hsh, by rw [bindOptValReg_ne payload hun, hreg]⟩
    | normal => left; exact ⟨.unsupported, rfl, rfl⟩
    | inCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
  | assignReg dst op =>
    simp only [stmtValRegUnused, Bool.and_eq_true, bne_iff_ne, ne_eq] at hun
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      rw [← evalValOp_congr hvr hun.2]
      cases hev : evalValOp st_s.valRegs op with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok v =>
        right
        refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind v hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
        cases hm : cert.mode <;> simp only [hm] at hmode ⊢
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          exact ⟨hpd, fm_s, fm_t, hha, by rw [bindValReg_ne _ v (Ne.symm hun.1), hreg]⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          exact ⟨hheq, fm_s, hsh, by rw [bindValReg_ne _ v (Ne.symm hun.1), hreg]⟩
  | binOp dst bop lhs rhs =>
    simp only [stmtValRegUnused, Bool.and_eq_true, bne_iff_ne, ne_eq] at hun
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      rw [← evalValOp_congr hvr hun.1.2, ← evalValOp_congr hvr hun.2]
      cases hl : evalValOp st_s.valRegs lhs with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok va =>
        cases hr : evalValOp st_s.valRegs rhs with
        | error e => left; exact ⟨e, rfl, rfl⟩
        | ok vb =>
          right
          refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
          cases hm : cert.mode <;> simp only [hm] at hmode ⊢
          · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
            exact ⟨hpd, fm_s, fm_t, hha, by rw [bindValReg_ne _ _ (Ne.symm hun.1.1), hreg]⟩
          · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
            exact ⟨hheq, fm_s, hsh, by rw [bindValReg_ne _ _ (Ne.symm hun.1.1), hreg]⟩
  | readField dst a f =>
    simp only [stmtValRegUnused, bne_iff_ne, ne_eq] at hun
    by_cases hmatch : a == cert.alloc && f == cert.field
    · have haf : a = cert.alloc ∧ f = cert.field := by simpa [Bool.and_eq_true, beq_iff_eq] using hmatch
      rcases haf with ⟨rfl, rfl⟩
      simp only [rewriteStmtForSroa, hmatch, ↓reduceIte, stepMirStmts, stepMirStmt, ← huw]
      cases hu : st_s.unwindState with
      | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | normal | inCleanup _ =>
        dsimp only []
        cases hm : cert.mode <;> simp only [hm] at hmode
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
            ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hread := tbRootAccessField_read_noChildren hinv1
          have hfs := setAt?_getAt? hfm1
          have hhs := setAt?_getAt? hsa1
          simp only [hsa1, hfm1, hread, hfs, hhs, evalValOp, hreg]
          right
          refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
          simp only [hm]
          exact ⟨hpd, fm_s, fm_t, hha_full, by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          rcases hsh with ⟨hsf, sa, hsa, hfm⟩
          have hsh_full : HeapSharedInv cert.alloc cert.field fm_s st_s.heap := ⟨hsf, sa, hsa, hfm⟩
          have hread := tbRootAccessField_read_shared hsf
          have hfs := setAt?_getAt? hfm
          have hhs := setAt?_getAt? hsa
          simp only [hsa, hfm, hread, hfs, hhs, evalValOp, hreg]
          right
          refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
          simp only [hm]
          exact ⟨hheq, fm_s, hsh_full, by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
    · simp only [rewriteStmtForSroa, hmatch, Bool.false_eq_true, ↓reduceIte, stepMirStmts, stepMirStmt, ← huw]
      cases hu : st_s.unwindState with
      | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | normal | inCleanup _ =>
        dsimp only []
        have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
          by_cases ha : a = cert.alloc
          · right; intro hf; subst ha; subst hf; exact hmatch (by rw [nat_beq_self, nat_beq_self]; rfl)
          · exact Or.inl ha
        cases hm : cert.mode <;> simp only [hm] at hmode
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          by_cases ha : a = cert.alloc
          · subst ha
            have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
            rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
            have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
              ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
            have hgf := hfother f hfn
            simp only [hsa1, hsa2, ← hgf]
            cases hg1 : getAt? sa1.fields f with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases htb : tbRootAccessField .read none fm0 with
              | none => left; exact ⟨.tbUb, rfl, rfl⟩
              | some fm' =>
                dsimp only []
                obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
                obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
                obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
                obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
                simp only [hfs1, hfs2, hs1, hs2]
                right
                refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                simp only [hm]
                exact ⟨hpd, fm_s, fm_t,
                  HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2,
                  by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
          · have hga := hha.2.1 a ha
            rw [← hga]
            cases hg1 : getAt? st_s.heap a with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some sa =>
              dsimp only []
              cases hgf : getAt? sa.fields f with
              | none => left; exact ⟨.unsupported, rfl, rfl⟩
              | some fm0 =>
                dsimp only []
                cases htb : tbRootAccessField .read none fm0 with
                | none => left; exact ⟨.tbUb, rfl, rfl⟩
                | some fm' =>
                  dsimp only []
                  obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                  obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                  obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
                  simp only [hfs', hs1, hs2]
                  right
                  refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                  simp only [hm]
                  exact ⟨hpd, fm_s, fm_t,
                    HeapAgreeExcept_set_other_alloc hha ha hs1 hs2,
                    by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          rw [← hheq]
          cases hg1 : getAt? st_s.heap a with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some sa =>
            dsimp only []
            cases hgf : getAt? sa.fields f with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases htb : tbRootAccessField .read none fm0 with
              | none => left; exact ⟨.tbUb, rfl, rfl⟩
              | some fm' =>
                dsimp only []
                obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                simp only [hfs', hs1]
                right
                refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                rw [hm]; dsimp only []
                rcases hsh with ⟨hsf, sa_c, hsa_c, hfm_c⟩
                refine ⟨rfl, fm_s, ⟨hsf, ?_⟩, by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
                by_cases ha : a = cert.alloc
                · subst ha
                  have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
                  rw [hsa_c] at hg1; injection hg1 with heq; subst sa_c
                  exact ⟨{ sa with fields := fs' }, getAt?_setAt?_same hs1,
                    by rw [getAt?_setAt?_ne hfs' (Ne.symm hfn), hfm_c]⟩
                · exact ⟨sa_c, by rw [getAt?_setAt?_ne hs1 (Ne.symm ha), hsa_c], hfm_c⟩
  | writeField a f op =>
    simp only [stmtValRegUnused] at hun
    by_cases hmatch : a == cert.alloc && f == cert.field
    · have haf : a = cert.alloc ∧ f = cert.field := by simpa [Bool.and_eq_true, beq_iff_eq] using hmatch
      rcases haf with ⟨rfl, rfl⟩
      simp only [rewriteStmtForSroa, hmatch, ↓reduceIte]
      cases hm : cert.mode <;> simp only [hm] at hmode ⊢
      · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
        simp only [stepMirStmts, stepMirStmt, ← huw]
        cases hu : st_s.unwindState with
        | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | normal | inCleanup _ =>
          dsimp only []
          rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
            ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          simp only [hsa1, hfm1, ← evalValOp_congr hvr hun]
          cases hev : evalValOp st_s.valRegs op with
          | error e => left; exact ⟨e, rfl, rfl⟩
          | ok v =>
            dsimp only []
            have hw := tbRootAccessField_write_noChildren hinv1 v
            let fm1' : FieldMeta := { isUnsafeCell := false, val := v, perm := .active, children := [] }
            obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm1' hfm1
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
            rw [hw]; dsimp only []; rw [hfs1]; dsimp only []; rw [hs1]; dsimp only []
            right
            refine ⟨_, _, rfl, rfl, ?_, hpr, hnt, hnc, htr, rfl, ?_⟩
            · intro x hne
              dsimp only []
              rw [bindValReg_ne _ v hne, hvr x hne]
            · rw [hm]; dsimp only []
              exact ⟨hpd, fm1', fm_t,
                HeapAgreeExcept_set_target_left hha_full (FieldNoChildrenInv_active v) hsa1 hfs1 hs1,
                bindValReg_same _ _ _⟩
      · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
        simp only [stepMirStmts, stepMirStmt, ← huw]
        cases hu : st_s.unwindState with
        | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
        | normal | inCleanup _ =>
          dsimp only []
          rcases hsh with ⟨hsf, sa, hsa, hfm⟩
          simp only [← hheq, ← evalValOp_congr hvr hun, hsa, hfm]
          cases hev : evalValOp st_s.valRegs op with
          | error e => left; exact ⟨e, rfl, rfl⟩
          | ok v =>
            dsimp only []
            cases htb : tbRootAccessField .write (some v) fm_s with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨hsf', hv'⟩ := tbRootAccessField_write_shared hsf htb
              obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hfm
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hsa
              have hev_t : evalValOp st_t.valRegs op = .ok v := (evalValOp_congr hvr hun).symm.trans hev
              simp only [hfs', hs1, hev_t]
              right
              refine ⟨_, _, rfl, rfl, ?_, hpr, hnt, hnc, htr, rfl, ?_⟩
              · intro x hne
                dsimp only []
                rw [bindValReg_ne _ v hne, hvr x hne]
              · rw [hm]; dsimp only []
                exact ⟨rfl, fm', ⟨hsf', { sa with fields := fs' }, getAt?_setAt?_same hs1,
                  getAt?_setAt?_same hfs'⟩, by rw [hv', bindValReg_same]⟩
    · simp only [rewriteStmtForSroa, hmatch, Bool.false_eq_true, ↓reduceIte, stepMirStmts, stepMirStmt, ← huw]
      cases hu : st_s.unwindState with
      | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
      | normal | inCleanup _ =>
        dsimp only []
        have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
          by_cases ha : a = cert.alloc
          · right; intro hf; subst ha; subst hf; exact hmatch (by rw [nat_beq_self, nat_beq_self]; rfl)
          · exact Or.inl ha
        rw [← evalValOp_congr hvr hun]
        cases hm : cert.mode <;> simp only [hm] at hmode
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          by_cases ha : a = cert.alloc
          · subst ha
            have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
            rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
            have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
              ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
            have hgf := hfother f hfn
            simp only [hsa1, hsa2, ← hgf]
            cases hg1 : getAt? sa1.fields f with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases hev : evalValOp st_s.valRegs op with
              | error e => left; exact ⟨e, rfl, rfl⟩
              | ok v =>
                dsimp only []
                cases htb : tbRootAccessField .write (some v) fm0 with
                | none => left; exact ⟨.tbUb, rfl, rfl⟩
                | some fm' =>
                  dsimp only []
                  obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
                  obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
                  obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
                  obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
                  simp only [hfs1, hfs2, hs1, hs2]
                  right
                  refine ⟨_, _, rfl, rfl, hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                  simp only [hm]
                  exact ⟨hpd, fm_s, fm_t,
                    HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2, hreg⟩
          · have hga := hha.2.1 a ha
            rw [← hga]
            cases hg1 : getAt? st_s.heap a with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some sa =>
              dsimp only []
              cases hgf : getAt? sa.fields f with
              | none => left; exact ⟨.unsupported, rfl, rfl⟩
              | some fm0 =>
                dsimp only []
                cases hev : evalValOp st_s.valRegs op with
                | error e => left; exact ⟨e, rfl, rfl⟩
                | ok v =>
                  dsimp only []
                  cases htb : tbRootAccessField .write (some v) fm0 with
                  | none => left; exact ⟨.tbUb, rfl, rfl⟩
                  | some fm' =>
                    dsimp only []
                    obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                    obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                    obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
                    simp only [hfs', hs1, hs2]
                    right
                    refine ⟨_, _, rfl, rfl, hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                    simp only [hm]
                    exact ⟨hpd, fm_s, fm_t, HeapAgreeExcept_set_other_alloc hha ha hs1 hs2, hreg⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          rw [← hheq]
          cases hg1 : getAt? st_s.heap a with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some sa =>
            dsimp only []
            cases hgf : getAt? sa.fields f with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases hev : evalValOp st_s.valRegs op with
              | error e => left; exact ⟨e, rfl, rfl⟩
              | ok v =>
                dsimp only []
                cases htb : tbRootAccessField .write (some v) fm0 with
                | none => left; exact ⟨.tbUb, rfl, rfl⟩
                | some fm' =>
                  dsimp only []
                  obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                  obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                  simp only [hfs', hs1]
                  right
                  refine ⟨_, _, rfl, rfl, hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
                  rw [hm]; dsimp only []
                  rcases hsh with ⟨hsf, sa_c, hsa_c, hfm_c⟩
                  refine ⟨rfl, fm_s, ⟨hsf, ?_⟩, hreg⟩
                  by_cases ha : a = cert.alloc
                  · subst ha
                    have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
                    rw [hsa_c] at hg1; injection hg1 with heq; subst sa_c
                    exact ⟨{ sa with fields := fs' }, getAt?_setAt?_same hs1,
                      by rw [getAt?_setAt?_ne hfs' (Ne.symm hfn), hfm_c]⟩
                  · exact ⟨sa_c, by rw [getAt?_setAt?_ne hs1 (Ne.symm ha), hsa_c], hfm_c⟩
  | readPtr dst pr =>
    simp only [stmtValRegUnused, bne_iff_ne, ne_eq] at hun
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hpr]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      cases hptr : st_s.ptrRegs pr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        dsimp only []
        cases hm : cert.mode <;> simp only [hm] at hmode
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hptr) .read none with
            ⟨e, he1, he2⟩ | ⟨v, h1', h2', ho1, ho2, hha'⟩
          · left; exact ⟨e, by rw [he1], by rw [he2]⟩
          · simp only [ho1, ho2]
            right
            refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, rfl, hnt, hnc, htr, rfl, ?_⟩
            rw [hm]; dsimp only []
            exact ⟨hpd, fm_s, fm_t, hha', by rw [bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          rw [← hheq]
          cases hacc : accessHeapByPtr st_s.heap p .read none with
          | error e => left; exact ⟨e, rfl, rfl⟩
          | ok res =>
            rcases res with ⟨v, h1'⟩
            obtain ⟨fm_s', hsh', hv'⟩ := HeapSharedInv_accessHeapByPtr hsh hacc (fun _ => rfl)
            right
            refine ⟨_, _, rfl, rfl, ValRegsAgreeExcept_bind _ hvr, rfl, hnt, hnc, htr, rfl, ?_⟩
            rw [hm]; dsimp only []
            exact ⟨rfl, fm_s', hsh', by rw [hv', bindValReg_ne _ _ (Ne.symm hun), hreg]⟩
  | writePtr pr op =>
    simp only [stmtValRegUnused] at hun
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hpr]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      rw [← evalValOp_congr hvr hun]
      cases hptr : st_s.ptrRegs pr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        dsimp only []
        cases hev : evalValOp st_s.valRegs op with
        | error e => left; exact ⟨e, rfl, rfl⟩
        | ok v =>
          dsimp only []
          cases hm : cert.mode <;> simp only [hm] at hmode
          · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
            rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hptr) .write (some v) with
              ⟨e, he1, he2⟩ | ⟨_, h1', h2', ho1, ho2, hha'⟩
            · left; exact ⟨e, by rw [he1], by rw [he2]⟩
            · simp only [ho1, ho2]
              right
              refine ⟨_, _, rfl, rfl, hvr, rfl, hnt, hnc, htr, rfl, ?_⟩
              rw [hm]; dsimp only []
              exact ⟨hpd, fm_s, fm_t, hha', hreg⟩
          · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
            rw [← hheq]
            cases hacc : accessHeapByPtr st_s.heap p .write (some v) with
            | error e => left; exact ⟨e, rfl, rfl⟩
            | ok res =>
              rcases res with ⟨_, h1'⟩
              obtain ⟨fm_s', hsh', hv'⟩ := HeapSharedInv_accessHeapByPtr hsh hacc (fun h => by cases h)
              right
              refine ⟨_, _, rfl, rfl, hvr, rfl, hnt, hnc, htr, rfl, ?_⟩
              rw [hm]; dsimp only []
              exact ⟨rfl, fm_s', hsh', by rw [hv', hreg]⟩
  | takeFieldPtr dst a f kind =>
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      cases hm : cert.mode <;> simp only [hm, stmtAllowedForSroa] at hmode hall
      · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
        have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
          by_cases ha : a = cert.alloc
          · right; intro hf; subst ha; subst hf; rw [nat_beq_self, nat_beq_self] at hall; cases kind <;> cases hall
          · exact Or.inl ha
        have hpd_new : ∀ pr p, bindPtrReg st_s.ptrRegs dst
            { allocId := a, field := f, scope := .fieldOnly f, kind := kind, tag := st_s.nextTag } pr = some p →
            PtrDisjoint cert.alloc cert.field p := by
          intro pr p hp
          by_cases hprd : pr = dst
          · subst hprd
            rw [bindPtrReg_same] at hp
            injection hp with hp; subst hp
            rcases hne with ha | hf
            · exact Or.inl ha
            · exact Or.inr ⟨f, rfl, hf⟩
          · rw [bindPtrReg_ne _ _ hprd] at hp
            exact hpd pr p hp
        by_cases ha : a = cert.alloc
        · subst ha
          have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
          rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
            ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
          have hgf := hfother f hfn
          simp only [hsa1, hsa2, ← hgf]
          cases hg1 : getAt? sa1.fields f with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases htb : tbRetagField st_s.nextTag kind fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
              obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
              simp only [hfs1, hfs2, hs1, hs2]
              right
              refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
              simp only [hm]
              exact ⟨hpd_new, fm_s, fm_t,
                HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2, hreg⟩
        · have hga := hha.2.1 a ha
          rw [← hga]
          cases hg1 : getAt? st_s.heap a with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some sa =>
            dsimp only []
            cases hgf : getAt? sa.fields f with
            | none => left; exact ⟨.unsupported, rfl, rfl⟩
            | some fm0 =>
              dsimp only []
              cases htb : tbRetagField st_s.nextTag kind fm0 with
              | none => left; exact ⟨.tbUb, rfl, rfl⟩
              | some fm' =>
                dsimp only []
                obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
                simp only [hfs', hs1, hs2]
                right
                refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
                simp only [hm]
                exact ⟨hpd_new, fm_s, fm_t, HeapAgreeExcept_set_other_alloc hha ha hs1 hs2, hreg⟩
      · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
        rw [← hheq]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases hgf : getAt? sa.fields f with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases htb : tbRetagField st_s.nextTag kind fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
              simp only [hfs', hs1]
              right
              refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
              rw [hm]; dsimp only []
              rcases hsh with ⟨hsf, sa_c, hsa_c, hfm_c⟩
              by_cases ha : a = cert.alloc
              · subst ha
                rw [hsa_c] at hg1; injection hg1 with heq; subst sa_c
                by_cases hf : f = cert.field
                · subst hf
                  have hkind : kind = .shared := by
                    rw [nat_beq_self, nat_beq_self] at hall
                    cases kind <;> cases hall <;> rfl
                  subst hkind
                  rw [hfm_c] at hgf; injection hgf with hfeq; subst hfeq
                  obtain ⟨hsf', hv'⟩ := tbRetagField_shared hsf htb
                  exact ⟨rfl, fm', ⟨hsf', { sa with fields := fs' }, getAt?_setAt?_same hs1,
                    getAt?_setAt?_same hfs'⟩, by rw [hv', hreg]⟩
                · exact ⟨rfl, fm_s, ⟨hsf, { sa with fields := fs' }, getAt?_setAt?_same hs1,
                    by rw [getAt?_setAt?_ne hfs' (Ne.symm hf), hfm_c]⟩, hreg⟩
              · exact ⟨rfl, fm_s, ⟨hsf, sa_c, by rw [getAt?_setAt?_ne hs1 (Ne.symm ha), hsa_c], hfm_c⟩, hreg⟩
  | takeRootSharedRef dst a =>
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      cases hm : cert.mode <;> simp only [hm, stmtAllowedForSroa] at hmode hall
      · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
        simp only [bne_iff_ne, ne_eq] at hall
        have hga := hha.2.1 a hall
        rw [← hga]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases htb : tbRetagAllFields st_s.nextTag .shared sa.fields with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fs' =>
            dsimp only []
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
            obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
            simp only [hs1, hs2]
            right
            refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
            simp only [hm]
            refine ⟨?_, fm_s, fm_t, HeapAgreeExcept_set_other_alloc hha hall hs1 hs2, hreg⟩
            intro pr p hp
            by_cases hprd : pr = dst
            · subst hprd
              rw [bindPtrReg_same] at hp
              injection hp with hp; subst hp; exact Or.inl hall
            · rw [bindPtrReg_ne _ _ hprd] at hp
              exact hpd pr p hp
      · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
        rw [← hheq]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases htb : tbRetagAllFields st_s.nextTag .shared sa.fields with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fs' =>
            dsimp only []
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
            simp only [hs1]
            right
            refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
            rw [hm]; dsimp only []
            rcases hsh with ⟨hsf, sa_c, hsa_c, hfm_c⟩
            by_cases ha : a = cert.alloc
            · subst ha
              rw [hsa_c] at hg1; injection hg1 with heq; subst sa_c
              obtain ⟨fm', hretag, hget'⟩ := tbRetagAllFields_getAt? st_s.nextTag .shared htb hfm_c
              obtain ⟨hsf', hv'⟩ := tbRetagField_shared hsf hretag
              exact ⟨rfl, fm', ⟨hsf', { sa with fields := fs' }, getAt?_setAt?_same hs1, hget'⟩,
                by rw [hv', hreg]⟩
            · exact ⟨rfl, fm_s, ⟨hsf, sa_c, by rw [getAt?_setAt?_ne hs1 (Ne.symm ha), hsa_c], hfm_c⟩, hreg⟩
  | takeRootRawPtr dst a =>
    simp only [stmtAllowedForSroa, bne_iff_ne, ne_eq] at hall
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      cases hm : cert.mode <;> simp only [hm] at hmode
      · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
        have hga := hha.2.1 a hall
        rw [← hga]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases htb : tbRetagAllFields st_s.nextTag .rawMut sa.fields with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fs' =>
            dsimp only []
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
            obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
            simp only [hs1, hs2]
            right
            refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
            simp only [hm]
            refine ⟨?_, fm_s, fm_t, HeapAgreeExcept_set_other_alloc hha hall hs1 hs2, hreg⟩
            intro pr p hp
            by_cases hprd : pr = dst
            · subst hprd
              rw [bindPtrReg_same] at hp
              injection hp with hp; subst hp; exact Or.inl hall
            · rw [bindPtrReg_ne _ _ hprd] at hp
              exact hpd pr p hp
      · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
        rw [← hheq]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases htb : tbRetagAllFields st_s.nextTag .rawMut sa.fields with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fs' =>
            dsimp only []
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
            simp only [hs1]
            right
            refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], rfl, hnc, htr, rfl, ?_⟩
            rw [hm]; dsimp only []
            rcases hsh with ⟨hsf, sa_c, hsa_c, hfm_c⟩
            exact ⟨rfl, fm_s, ⟨hsf, sa_c, by rw [getAt?_setAt?_ne hs1 (Ne.symm hall), hsa_c], hfm_c⟩, hreg⟩
  | ptrOffset dst srcPr targetField =>
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw, ← hpr]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      cases hptr : st_s.ptrRegs srcPr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        right
        refine ⟨_, _, rfl, rfl, hvr, by rw [hpr], hnt, hnc, htr, rfl, ?_⟩
        cases hm : cert.mode <;> simp only [hm] at hmode ⊢
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          refine ⟨?_, fm_s, fm_t, hha, hreg⟩
          intro pr q hq
          by_cases hprd : pr = dst
          · subst hprd
            rw [bindPtrReg_same] at hq
            injection hq with hq; subst hq
            exact hpd srcPr p hptr
          · rw [bindPtrReg_ne _ _ hprd] at hq
            exact hpd pr q hq
        · exact hmode
  | emitObs op =>
    simp only [stmtValRegUnused] at hun
    simp only [rewriteStmtForSroa, stepMirStmts, stepMirStmt, ← huw]
    cases hu : st_s.unwindState with
    | enteringCleanup _ => left; exact ⟨.unsupported, rfl, rfl⟩
    | normal | inCleanup _ =>
      dsimp only []
      rw [← evalValOp_congr hvr hun]
      cases hev : evalValOp st_s.valRegs op with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok v =>
        right
        refine ⟨_, _, rfl, rfl, hvr, hpr, hnt, hnc, by rw [htr], rfl, hmode⟩

private theorem sroa_step_stmts {cert : PartialSroaCert} :
    ∀ {stmts : List MirStmt} {st_s st_t : ExecState},
      SroaStateRel cert st_s st_t →
      stmts.all (stmtValRegUnused cert.ssaReg) = true →
      stmts.all (stmtAllowedForSroa cert.mode cert.alloc cert.field) = true →
      (∃ e, stepMirStmts st_s stmts = .error e ∧
            stepMirStmts st_t (rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg stmts) = .error e) ∨
      (∃ st_s' st_t',
        stepMirStmts st_s stmts = .ok st_s' ∧
        stepMirStmts st_t (rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg stmts) = .ok st_t' ∧
        SroaStateRel cert st_s' st_t')
  | [], st_s, st_t, hrel, _, _ => Or.inr ⟨st_s, st_t, rfl, rfl, hrel⟩
  | s :: rest, st_s, st_t, hrel, hun, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hun hall
    simp only [rewriteStmtsForSroa, List.flatMap_cons, stepMirStmts_append, stepMirStmts]
    rcases sroa_step_stmt hrel hun.1 hall.1 with ⟨e, he1, he2⟩ | ⟨st_s1, st_t1, ho1, ho2, hrel1⟩
    · left; exact ⟨e, by rw [he1], by rw [he2]⟩
    · rw [ho1, ho2]
      exact sroa_step_stmts hrel1 hun.2 hall.2

private def execMirBlockBody (pm : PanicMode) (body : MirBody) (env : CalleeEnv)
    (fuel : Nat) (stmts : List MirStmt) (term : MirTerm) (st : ExecState) : ExecResult :=
  match stepMirStmts st stmts with
  | .error e => .error e
  | .ok st1 =>
    match st1.unwindState with
    | .enteringCleanup _ => .error .unsupported
    | _ =>
      match term with
      | .goto tgtPc => execMirLoop pm body env fuel tgtPc st1
      | .switchZero discr zTgt nzTgt =>
        match evalValOp st1.valRegs discr with
        | .error e => .error e
        | .ok n =>
          if n == 0 then execMirLoop pm body env fuel zTgt st1
          else execMirLoop pm body env fuel nzTgt st1
      | .ret op =>
        match st1.unwindState with
        | .normal =>
          match evalValOp st1.valRegs op with
          | .error e => .error e
          | .ok v => .ok (st1.trace, .ret v)
        | _ => .error .unsupported
      | .resume =>
        match st1.unwindState with
        | .inCleanup payload => .ok (st1.trace, .unwound payload)
        | _ => .error .unsupported
      | .catchUnwind dst recTgt =>
        match st1.unwindState with
        | .inCleanup payload =>
          execMirLoop pm body env fuel recTgt
            { st1 with unwindState := .normal, valRegs := bindOptValReg st1.valRegs dst payload }
        | _ => .error .unsupported
      | .callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
        match env cid with
        | none => .error .unsupported
        | some callee =>
          match evalArgPtrs st1.ptrRegs argPtrs with
          | .error e => .error e
          | .ok ptrVals =>
            let callId := st1.nextCallId
            match activateProtectors callId st1.heap ptrVals with
            | .error e => .error e
            | .ok heapProt =>
              match stepCalleeOps ptrVals heapProt st1.trace callee.ops with
              | .error e => .error e
              | .ok (heapAfter, traceAfter) =>
                let heapRel := releaseProtectorHeap callId heapAfter
                let st2 : ExecState :=
                  { st1 with heap := heapRel, nextCallId := callId + 1, trace := traceAfter }
                match callee.exit with
                | .normal retVal =>
                  execMirLoop pm body env fuel normTgt
                    { st2 with valRegs := bindOptValReg st2.valRegs retDst retVal }
                | .panic payload =>
                  match pm, st2.unwindState with
                  | .unwind, .normal =>
                    execMirLoop pm body env fuel cleanTgt
                      { st2 with unwindState := .enteringCleanup payload }
                  | _, _ => .ok (st2.trace, .aborted payload)

private theorem sroa_exec_block_continuation {src tgt : MirBody} {cert : PartialSroaCert}
    {pm : PanicMode} {env : CalleeEnv} {fuel : Nat} {blk : MirBlock}
    {st_s st_t : ExecState}
    (hrel : SroaStateRel cert st_s st_t)
    (hun_stmts : blk.stmts.all (stmtValRegUnused cert.ssaReg) = true)
    (hun_term : termValRegUnused cert.ssaReg blk.term = true)
    (hall_stmts : blk.stmts.all (stmtAllowedForSroa cert.mode cert.alloc cert.field) = true)
    (hno0 : termTargets blk.term 0 = false)
    (ih : ∀ pc', pc' ≠ 0 → ∀ s1 t1, SroaStateRel cert s1 t1 →
      execMirLoop pm tgt env fuel pc' t1 = execMirLoop pm src env fuel pc' s1) :
    execMirBlockBody pm tgt env fuel
      (rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg blk.stmts) blk.term st_t =
    execMirBlockBody pm src env fuel blk.stmts blk.term st_s := by
  unfold execMirBlockBody
  rcases sroa_step_stmts hrel hun_stmts hall_stmts with ⟨e, he1, he2⟩ | ⟨st_s1, st_t1, ho1, ho2, hrel1⟩
  · rw [he1, he2]
  · rw [ho1, ho2]
    dsimp only []
    rcases hrel1 with ⟨hvr, hpr, hnt, hnc, htr, huw, hmode⟩
    have hrel1_full : SroaStateRel cert st_s1 st_t1 := ⟨hvr, hpr, hnt, hnc, htr, huw, hmode⟩
    rw [← huw]
    cases hu : st_s1.unwindState with
    | enteringCleanup _ => rfl
    | normal =>
      dsimp only []
      cases ht : blk.term with
      | goto tgtPc =>
        simp only [ht, termTargets, beq_eq_false_iff_ne] at hno0
        exact ih tgtPc hno0 st_s1 st_t1 hrel1_full
      | switchZero discr zTgt nzTgt =>
        simp only [ht, termValRegUnused] at hun_term
        simp only [ht, termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hno0
        dsimp only []
        rw [← evalValOp_congr hvr hun_term]
        cases evalValOp st_s1.valRegs discr with
        | error _ => rfl
        | ok n =>
          dsimp only []
          split
          · exact ih zTgt hno0.1 st_s1 st_t1 hrel1_full
          · exact ih nzTgt hno0.2 st_s1 st_t1 hrel1_full
      | ret op =>
        simp only [ht, termValRegUnused] at hun_term
        dsimp only []
        rw [← evalValOp_congr hvr hun_term, htr]
      | resume => rfl
      | catchUnwind _ _ => rfl
      | callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
        simp only [ht, termValRegUnused, bne_iff_ne, ne_eq] at hun_term
        simp only [ht, termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hno0
        dsimp only []
        cases env cid with
        | none => rfl
        | some callee =>
          dsimp only []
          rw [← hpr, ← hnc, ← htr]
          cases hargs : evalArgPtrs st_s1.ptrRegs argPtrs with
          | error _ => rfl
          | ok ptrVals =>
            dsimp only []
            cases hm : cert.mode <;> simp only [hm] at hmode
            · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
              have hds := PtrDisjoint_evalArgPtrs hpd hargs
              rcases HeapAgreeExcept_activateProtectors st_s1.nextCallId hha hds with
                ⟨e, he1, he2⟩ | ⟨hp1, hp2, ho1, ho2, hha1⟩
              · rw [he1, he2]
              · rw [ho1, ho2]
                dsimp only []
                rcases HeapAgreeExcept_stepCalleeOps hds hha1 (ops := callee.ops) (tr := st_s1.trace) with
                  ⟨e, he1, he2⟩ | ⟨ha1, ha2, tr', ho1', ho2', hha2⟩
                · rw [he1, he2]
                · rw [ho1', ho2']
                  dsimp only []
                  have hha3 := HeapAgreeExcept_releaseProtectorHeap st_s1.nextCallId hha2
                  cases callee.exit with
                  | normal retVal =>
                    apply ih normTgt hno0.1
                    refine ⟨ValRegsAgreeExcept_bindOpt retVal hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                    rw [hm]; dsimp only []
                    exact ⟨hpd, fm_s, fm_t, hha3, by rw [bindOptValReg_ne retVal hun_term, hreg]⟩
                  | panic payload =>
                    cases pm with
                    | abort => rfl
                    | unwind =>
                      apply ih cleanTgt hno0.2
                      refine ⟨hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                      rw [hm]; dsimp only []
                      exact ⟨hpd, fm_s, fm_t, hha3, hreg⟩
            · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
              rw [← hheq]
              cases hap : activateProtectors st_s1.nextCallId st_s1.heap ptrVals with
              | error _ => rfl
              | ok heapProt =>
                dsimp only []
                obtain ⟨fm1, hsh1, hv1⟩ := HeapSharedInv_activateProtectors st_s1.nextCallId hsh hap
                cases hops : stepCalleeOps ptrVals heapProt st_s1.trace callee.ops with
                | error _ => rfl
                | ok res =>
                  rcases res with ⟨heapAfter, traceAfter⟩
                  dsimp only []
                  obtain ⟨fm2, hsh2, hv2⟩ := HeapSharedInv_stepCalleeOps hsh1 hops
                  obtain ⟨fm3, hsh3, hv3⟩ := HeapSharedInv_releaseProtectorHeap st_s1.nextCallId hsh2
                  have hvf : fm3.val = fm_s.val := hv3.trans (hv2.trans hv1)
                  cases callee.exit with
                  | normal retVal =>
                    apply ih normTgt hno0.1
                    refine ⟨ValRegsAgreeExcept_bindOpt retVal hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                    rw [hm]; dsimp only []
                    exact ⟨rfl, fm3, hsh3, by rw [hvf, bindOptValReg_ne retVal hun_term, hreg]⟩
                  | panic payload =>
                    cases pm with
                    | abort => rfl
                    | unwind =>
                      apply ih cleanTgt hno0.2
                      refine ⟨hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                      rw [hm]; dsimp only []
                      exact ⟨rfl, fm3, hsh3, by rw [hvf, hreg]⟩
    | inCleanup cpPayload =>
      dsimp only []
      cases ht : blk.term with
      | goto tgtPc =>
        simp only [ht, termTargets, beq_eq_false_iff_ne] at hno0
        exact ih tgtPc hno0 st_s1 st_t1 hrel1_full
      | switchZero discr zTgt nzTgt =>
        simp only [ht, termValRegUnused] at hun_term
        simp only [ht, termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hno0
        dsimp only []
        rw [← evalValOp_congr hvr hun_term]
        cases evalValOp st_s1.valRegs discr with
        | error _ => rfl
        | ok n =>
          dsimp only []
          split
          · exact ih zTgt hno0.1 st_s1 st_t1 hrel1_full
          · exact ih nzTgt hno0.2 st_s1 st_t1 hrel1_full
      | ret _ => rfl
      | resume =>
        dsimp only []
        rw [htr]
      | catchUnwind dst recTgt =>
        simp only [ht, termValRegUnused, bne_iff_ne, ne_eq] at hun_term
        simp only [ht, termTargets, beq_eq_false_iff_ne] at hno0
        apply ih recTgt hno0
        refine ⟨ValRegsAgreeExcept_bindOpt _ hvr, hpr, hnt, hnc, htr, rfl, ?_⟩
        cases hm : cert.mode <;> simp only [hm] at hmode <;> dsimp only []
        · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
          exact ⟨hpd, fm_s, fm_t, hha, by rw [bindOptValReg_ne _ hun_term, hreg]⟩
        · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
          exact ⟨hheq, fm_s, hsh, by rw [bindOptValReg_ne _ hun_term, hreg]⟩
      | callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
        simp only [ht, termValRegUnused, bne_iff_ne, ne_eq] at hun_term
        simp only [ht, termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hno0
        dsimp only []
        cases env cid with
        | none => rfl
        | some callee =>
          dsimp only []
          rw [← hpr, ← hnc, ← htr]
          cases hargs : evalArgPtrs st_s1.ptrRegs argPtrs with
          | error _ => rfl
          | ok ptrVals =>
            dsimp only []
            cases hm : cert.mode <;> simp only [hm] at hmode
            · rcases hmode with ⟨hpd, fm_s, fm_t, hha, hreg⟩
              have hds := PtrDisjoint_evalArgPtrs hpd hargs
              rcases HeapAgreeExcept_activateProtectors st_s1.nextCallId hha hds with
                ⟨e, he1, he2⟩ | ⟨hp1, hp2, ho1, ho2, hha1⟩
              · rw [he1, he2]
              · rw [ho1, ho2]
                dsimp only []
                rcases HeapAgreeExcept_stepCalleeOps hds hha1 (ops := callee.ops) (tr := st_s1.trace) with
                  ⟨e, he1, he2⟩ | ⟨ha1, ha2, tr', ho1', ho2', hha2⟩
                · rw [he1, he2]
                · rw [ho1', ho2']
                  dsimp only []
                  have hha3 := HeapAgreeExcept_releaseProtectorHeap st_s1.nextCallId hha2
                  cases callee.exit with
                  | normal retVal =>
                    apply ih normTgt hno0.1
                    refine ⟨ValRegsAgreeExcept_bindOpt retVal hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                    rw [hm]; dsimp only []
                    exact ⟨hpd, fm_s, fm_t, hha3, by rw [bindOptValReg_ne retVal hun_term, hreg]⟩
                  | panic _ => cases pm <;> rfl
            · rcases hmode with ⟨hheq, fm_s, hsh, hreg⟩
              rw [← hheq]
              cases hap : activateProtectors st_s1.nextCallId st_s1.heap ptrVals with
              | error _ => rfl
              | ok heapProt =>
                dsimp only []
                obtain ⟨fm1, hsh1, hv1⟩ := HeapSharedInv_activateProtectors st_s1.nextCallId hsh hap
                cases hops : stepCalleeOps ptrVals heapProt st_s1.trace callee.ops with
                | error _ => rfl
                | ok res =>
                  rcases res with ⟨heapAfter, traceAfter⟩
                  dsimp only []
                  obtain ⟨fm2, hsh2, hv2⟩ := HeapSharedInv_stepCalleeOps hsh1 hops
                  obtain ⟨fm3, hsh3, hv3⟩ := HeapSharedInv_releaseProtectorHeap st_s1.nextCallId hsh2
                  have hvf : fm3.val = fm_s.val := hv3.trans (hv2.trans hv1)
                  cases callee.exit with
                  | normal retVal =>
                    apply ih normTgt hno0.1
                    refine ⟨ValRegsAgreeExcept_bindOpt retVal hvr, rfl, hnt, rfl, rfl, rfl, ?_⟩
                    rw [hm]; dsimp only []
                    exact ⟨rfl, fm3, hsh3, by rw [hvf, bindOptValReg_ne retVal hun_term, hreg]⟩
                  | panic _ => cases pm <;> rfl

private theorem getAt?_applyPartialSroa_ne_zero {src : MirBody} {cert : PartialSroaCert}
    {pc : BlockId} (hne : pc ≠ 0) :
    getAt? (applyPartialSroa src cert).blocks pc =
      (getAt? src.blocks pc).map fun b =>
        { stmts := rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg b.stmts
        , term := b.term } := by
  cases pc with
  | zero => exact absurd rfl hne
  | succ k =>
    cases hb : src.blocks with
    | nil => simp [applyPartialSroa, hb, getAt?]
    | cons b0 rest =>
      simp only [applyPartialSroa, hb, getAt?, getAt?_map]

private theorem sroa_execMirLoop_ne_zero {src : MirBody} {cert : PartialSroaCert}
    (hno0 : hasPredecessor src 0 = false)
    (hun : valRegUnusedInBody src cert.ssaReg = true)
    (hall : (src.blocks.all fun blk => blk.stmts.all (stmtAllowedForSroa cert.mode cert.alloc cert.field)) = true)
    (pm : PanicMode) (env : CalleeEnv) :
    ∀ fuel pc st_s st_t,
      pc ≠ 0 →
      SroaStateRel cert st_s st_t →
      execMirLoop pm (applyPartialSroa src cert) env fuel pc st_t =
        execMirLoop pm src env fuel pc st_s
  | 0, _, st_s, st_t, _, hrel => by
    simp [execMirLoop, hrel.2.2.2.2.1]
  | fuel + 1, pc, st_s, st_t, hne, hrel => by
    simp only [execMirLoop, getAt?_applyPartialSroa_ne_zero hne]
    cases hblk : getAt? src.blocks pc with
    | none => rfl
    | some blk =>
      dsimp only [Option.map_some]
      have hun_blk := all_of_getAt? hun hblk
      simp only [Bool.and_eq_true] at hun_blk
      have hall_blk := all_of_getAt? hall hblk
      have hno0_blk := any_eq_false_of_getAt? hno0 hblk
      exact sroa_exec_block_continuation hrel hun_blk.1 hun_blk.2 hall_blk hno0_blk
        (fun pc' hne' s1 t1 hr => sroa_execMirLoop_ne_zero hno0 hun hall pm env fuel pc' s1 t1 hne' hr)

/-! #### Theorem 2 Helpers (`store_sink_to_cleanup_refinement`) -/

private theorem execMirLoop_succ (pm : PanicMode) (body : MirBody) (env : CalleeEnv)
    (fuel : Nat) (pc : BlockId) (st : ExecState) :
    execMirLoop pm body env (fuel + 1) pc st =
      match getAt? body.blocks pc with
      | none => .error .unsupported
      | some blk => execMirBlockBody pm body env fuel blk.stmts blk.term st := rfl

private theorem execMirBlockBody_cons (pm : PanicMode) (body : MirBody) (env : CalleeEnv)
    (fuel : Nat) (s : MirStmt) (rest : List MirStmt) (term : MirTerm) (st : ExecState) :
    execMirBlockBody pm body env fuel (s :: rest) term st =
      match stepMirStmt st s with
      | .error e => .error e
      | .ok st' => execMirBlockBody pm body env fuel rest term st' := by
  unfold execMirBlockBody
  simp only [stepMirStmts]
  cases stepMirStmt st s <;> rfl

private theorem all_append_split {α : Type} {p : α → Bool} :
    ∀ {xs ys : List α}, (xs ++ ys).all p = true → xs.all p = true ∧ ys.all p = true
  | [], _, h => ⟨rfl, h⟩
  | _ :: _, _, h => by
    simp only [List.cons_append, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := all_append_split h.2
    exact ⟨by simp [List.all_cons, h.1, h1], h2⟩

private theorem evalValOp_error_tbUb {regs : ValRegEnv} {op : ValOp} {e : FaultKind}
    (h : evalValOp regs op = .error e) : e = .tbUb := by
  cases op with
  | constU64 _ => simp [evalValOp] at h
  | reg r =>
    simp only [evalValOp] at h
    cases hr : regs r <;> simp [hr] at h
    exact h.symm

private theorem evalValOp_bindValReg_unchanged {regs : ValRegEnv} {valOp : ValOp}
    {dst : ValRegId} (v : UInt64)
    (hnc : (match valOp with | .reg r => r != dst | .constU64 _ => true) = true) :
    evalValOp (bindValReg regs dst v) valOp = evalValOp regs valOp := by
  cases valOp with
  | constU64 _ => rfl
  | reg r =>
    dsimp only [] at hnc
    simp only [bne_iff_ne, ne_eq] at hnc
    simp only [evalValOp, bindValReg_ne regs v hnc]

private def termNoCleanSink (sinkBlock : BlockId) : MirTerm → Bool
  | .callMayUnwind _ _ _ _ cl => cl != sinkBlock
  | _ => true

private def valOpDisjointOptReg (valOp : ValOp) (lpDst : Option ValRegId) : Bool :=
  match valOp, lpDst with
  | .reg r, some d => r != d
  | _, _ => true

private theorem evalValOp_bindOptValReg_unchanged {regs : ValRegEnv} {valOp : ValOp}
    {lpDst : Option ValRegId} (v : UInt64)
    (hnc : valOpDisjointOptReg valOp lpDst = true) :
    evalValOp (bindOptValReg regs lpDst v) valOp = evalValOp regs valOp := by
  cases lpDst with
  | none => rfl
  | some d =>
    exact evalValOp_bindValReg_unchanged v (by
      cases valOp with
      | constU64 _ => rfl
      | reg r => exact hnc)

private def SinkStateInv (cert : StoreSinkToCleanupCert) (st : ExecState) : Prop :=
  (∀ pr p, st.ptrRegs pr = some p → PtrDisjoint cert.alloc cert.field p) ∧
  ∃ fm, HeapAgreeExcept cert.alloc cert.field fm fm st.heap st.heap

private theorem SinkStateInv_stepMirStmt {cert : StoreSinkToCleanupCert} {st st' : ExecState}
    {s : MirStmt}
    (hinv : SinkStateInv cert st)
    (hnoptr : stmtNoPtrToField cert.alloc cert.field s = true)
    (hstep : stepMirStmt st s = .ok st') :
    SinkStateInv cert st' := by
  rcases hinv with ⟨hpd, fm, hha⟩
  cases s with
  | landingPad dst =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState <;> simp [hu] at hstep
    subst hstep
    exact ⟨hpd, fm, hha⟩
  | assignReg dst op =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hev : evalValOp st.valRegs op <;> simp [hev] at hstep
      subst hstep
      exact ⟨hpd, fm, hha⟩
  | binOp dst bop lhs rhs =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hl : evalValOp st.valRegs lhs <;> cases hr : evalValOp st.valRegs rhs <;>
        simp [hl, hr] at hstep
      subst hstep
      exact ⟨hpd, fm, hha⟩
  | emitObs op =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hev : evalValOp st.valRegs op <;> simp [hev] at hstep
      subst hstep
      exact ⟨hpd, fm, hha⟩
  | ptrOffset dst srcPr targetField =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hp : st.ptrRegs srcPr with
      | none => simp [hp] at hstep
      | some p0 =>
        simp only [hp, Except.ok.injEq] at hstep
        subst hstep
        refine ⟨?_, fm, hha⟩
        intro pr q hq
        dsimp only [] at hq
        by_cases hprd : pr = dst
        · subst hprd
          rw [bindPtrReg_same] at hq
          injection hq with hq; subst hq
          exact hpd srcPr p0 hp
        · rw [bindPtrReg_ne _ _ hprd] at hq
          exact hpd pr q hq
  | readPtr dst pr =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hp : st.ptrRegs pr with
      | none => simp [hp] at hstep
      | some p =>
        simp only [hp] at hstep
        cases hacc : accessHeapByPtr st.heap p .read none with
        | error _ => simp [hacc] at hstep
        | ok res =>
          rcases res with ⟨v, h1'⟩
          simp only [hacc, Except.ok.injEq] at hstep
          subst hstep
          rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hp) .read none with
            ⟨e, he, _⟩ | ⟨v', ha1, ha2, ho1, ho2, hha'⟩
          · rw [hacc] at he; cases he
          · rw [hacc] at ho1 ho2
            simp only [Except.ok.injEq, Prod.mk.injEq] at ho1 ho2
            rcases ho1 with ⟨_, rfl⟩
            rcases ho2 with ⟨_, rfl⟩
            exact ⟨hpd, fm, hha'⟩
  | writePtr pr op =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hp : st.ptrRegs pr with
      | none => simp [hp] at hstep
      | some p =>
        simp only [hp] at hstep
        cases hev : evalValOp st.valRegs op with
        | error _ => simp [hev] at hstep
        | ok v =>
          simp only [hev] at hstep
          cases hacc : accessHeapByPtr st.heap p .write (some v) with
          | error _ => simp [hacc] at hstep
          | ok res =>
            rcases res with ⟨_, h1'⟩
            simp only [hacc, Except.ok.injEq] at hstep
            subst hstep
            rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hp) .write (some v) with
              ⟨e, he, _⟩ | ⟨_, ha1, ha2, ho1, ho2, hha'⟩
            · rw [hacc] at he; cases he
            · rw [hacc] at ho1 ho2
              simp only [Except.ok.injEq, Prod.mk.injEq] at ho1 ho2
              rcases ho1 with ⟨_, rfl⟩
              rcases ho2 with ⟨_, rfl⟩
              exact ⟨hpd, fm, hha'⟩
  | readField dst a f =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hga : getAt? st.heap a with
      | none => simp [hga] at hstep
      | some sa =>
        simp only [hga] at hstep
        cases hgf : getAt? sa.fields f with
        | none => simp [hgf] at hstep
        | some fm0 =>
          simp only [hgf] at hstep
          cases htb : tbRootAccessField .read none fm0 with
          | none => simp [htb] at hstep
          | some fm' =>
            simp only [htb] at hstep
            cases hfs : setAt? sa.fields f fm' with
            | none => simp [hfs] at hstep
            | some fs' =>
              simp only [hfs] at hstep
              cases hhs : setAt? st.heap a { sa with fields := fs' } with
              | none => simp [hhs] at hstep
              | some h1' =>
                simp only [hhs, Except.ok.injEq] at hstep
                subst hstep
                refine ⟨hpd, ?_⟩
                by_cases ha : a = cert.alloc
                · subst ha
                  by_cases hf : f = cert.field
                  · subst hf
                    rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
                    have hha_full : HeapAgreeExcept cert.alloc cert.field fm fm st.heap st.heap :=
                      ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
                    rw [hga] at hsa1; injection hsa1 with heq; subst sa1
                    rw [hgf] at hfm1; injection hfm1 with hfeq; subst fm0
                    rw [tbRootAccessField_read_noChildren hinv1] at htb
                    injection htb with htb'; subst fm'
                    exact ⟨fm, HeapAgreeExcept_set_target_right
                      (HeapAgreeExcept_set_target_left hha_full hinv1 hga hfs hhs) hinv1 hga hfs hhs⟩
                  · exact ⟨fm, HeapAgreeExcept_set_other_field hha hf hga hga hfs hfs hhs hhs⟩
                · exact ⟨fm, HeapAgreeExcept_set_other_alloc hha ha hhs hhs⟩
  | writeField a f op =>
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hga : getAt? st.heap a with
      | none => simp [hga] at hstep
      | some sa =>
        simp only [hga] at hstep
        cases hgf : getAt? sa.fields f with
        | none => simp [hgf] at hstep
        | some fm0 =>
          simp only [hgf] at hstep
          cases hev : evalValOp st.valRegs op with
          | error _ => simp [hev] at hstep
          | ok v =>
            simp only [hev] at hstep
            cases htb : tbRootAccessField .write (some v) fm0 with
            | none => simp [htb] at hstep
            | some fm' =>
              simp only [htb] at hstep
              cases hfs : setAt? sa.fields f fm' with
              | none => simp [hfs] at hstep
              | some fs' =>
                simp only [hfs] at hstep
                cases hhs : setAt? st.heap a { sa with fields := fs' } with
                | none => simp [hhs] at hstep
                | some h1' =>
                  simp only [hhs, Except.ok.injEq] at hstep
                  subst hstep
                  refine ⟨hpd, ?_⟩
                  by_cases ha : a = cert.alloc
                  · subst ha
                    by_cases hf : f = cert.field
                    · subst hf
                      rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
                      have hha_full : HeapAgreeExcept cert.alloc cert.field fm fm st.heap st.heap :=
                        ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
                      rw [hga] at hsa1; injection hsa1 with heq; subst sa1
                      rw [hgf] at hfm1; injection hfm1 with hfeq; subst fm0
                      rw [tbRootAccessField_write_noChildren hinv1 v] at htb
                      injection htb with htb'; subst fm'
                      have hact := FieldNoChildrenInv_active v
                      exact ⟨_, HeapAgreeExcept_set_target_right
                        (HeapAgreeExcept_set_target_left hha_full hact hga hfs hhs) hact hga hfs hhs⟩
                    · exact ⟨fm, HeapAgreeExcept_set_other_field hha hf hga hga hfs hfs hhs hhs⟩
                  · exact ⟨fm, HeapAgreeExcept_set_other_alloc hha ha hhs hhs⟩
  | takeFieldPtr dst a f kind =>
    simp only [stmtNoPtrToField] at hnoptr
    have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
      by_cases ha : a = cert.alloc
      · right; intro hf; subst ha; subst hf; rw [nat_beq_self, nat_beq_self] at hnoptr; cases hnoptr
      · exact Or.inl ha
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hga : getAt? st.heap a with
      | none => simp [hga] at hstep
      | some sa =>
        simp only [hga] at hstep
        cases hgf : getAt? sa.fields f with
        | none => simp [hgf] at hstep
        | some fm0 =>
          simp only [hgf] at hstep
          cases htb : tbRetagField st.nextTag kind fm0 with
          | none => simp [htb] at hstep
          | some fm' =>
            simp only [htb] at hstep
            cases hfs : setAt? sa.fields f fm' with
            | none => simp [hfs] at hstep
            | some fs' =>
              simp only [hfs] at hstep
              cases hhs : setAt? st.heap a { sa with fields := fs' } with
              | none => simp [hhs] at hstep
              | some h1' =>
                simp only [hhs, Except.ok.injEq] at hstep
                subst hstep
                refine ⟨?_, ?_⟩
                · intro pr q hq
                  dsimp only [] at hq
                  by_cases hprd : pr = dst
                  · subst hprd
                    rw [bindPtrReg_same] at hq
                    injection hq with hq; subst hq
                    rcases hne with ha | hf
                    · exact Or.inl ha
                    · exact Or.inr ⟨f, rfl, hf⟩
                  · rw [bindPtrReg_ne _ _ hprd] at hq
                    exact hpd pr q hq
                · by_cases ha : a = cert.alloc
                  · subst ha
                    have hf : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
                    exact ⟨fm, HeapAgreeExcept_set_other_field hha hf hga hga hfs hfs hhs hhs⟩
                  · exact ⟨fm, HeapAgreeExcept_set_other_alloc hha ha hhs hhs⟩
  | takeRootSharedRef dst a =>
    simp only [stmtNoPtrToField, bne_iff_ne, ne_eq] at hnoptr
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hga : getAt? st.heap a with
      | none => simp [hga] at hstep
      | some sa =>
        simp only [hga] at hstep
        cases htb : tbRetagAllFields st.nextTag .shared sa.fields with
        | none => simp [htb] at hstep
        | some fs' =>
          simp only [htb] at hstep
          cases hhs : setAt? st.heap a { sa with fields := fs' } with
          | none => simp [hhs] at hstep
          | some h1' =>
            simp only [hhs, Except.ok.injEq] at hstep
            subst hstep
            refine ⟨?_, fm, HeapAgreeExcept_set_other_alloc hha hnoptr hhs hhs⟩
            intro pr q hq
            dsimp only [] at hq
            by_cases hprd : pr = dst
            · subst hprd
              rw [bindPtrReg_same] at hq
              injection hq with hq; subst hq
              exact Or.inl hnoptr
            · rw [bindPtrReg_ne _ _ hprd] at hq
              exact hpd pr q hq
  | takeRootRawPtr dst a =>
    simp only [stmtNoPtrToField, bne_iff_ne, ne_eq] at hnoptr
    simp only [stepMirStmt] at hstep
    cases hu : st.unwindState with
    | enteringCleanup _ => simp [hu] at hstep
    | normal | inCleanup _ =>
      simp only [hu] at hstep
      cases hga : getAt? st.heap a with
      | none => simp [hga] at hstep
      | some sa =>
        simp only [hga] at hstep
        cases htb : tbRetagAllFields st.nextTag .rawMut sa.fields with
        | none => simp [htb] at hstep
        | some fs' =>
          simp only [htb] at hstep
          cases hhs : setAt? st.heap a { sa with fields := fs' } with
          | none => simp [hhs] at hstep
          | some h1' =>
            simp only [hhs, Except.ok.injEq] at hstep
            subst hstep
            refine ⟨?_, fm, HeapAgreeExcept_set_other_alloc hha hnoptr hhs hhs⟩
            intro pr q hq
            dsimp only [] at hq
            by_cases hprd : pr = dst
            · subst hprd
              rw [bindPtrReg_same] at hq
              injection hq with hq; subst hq
              exact Or.inl hnoptr
            · rw [bindPtrReg_ne _ _ hprd] at hq
              exact hpd pr q hq

private theorem SinkStateInv_stepMirStmts {cert : StoreSinkToCleanupCert} :
    ∀ {ss : List MirStmt} {st st' : ExecState},
      SinkStateInv cert st →
      ss.all (stmtNoPtrToField cert.alloc cert.field) = true →
      stepMirStmts st ss = .ok st' →
      SinkStateInv cert st'
  | [], _, _, hinv, _, hstep => by
    simp only [stepMirStmts, Except.ok.injEq] at hstep
    subst hstep
    exact hinv
  | s :: rest, st, _, hinv, hnoptr, hstep => by
    simp only [List.all_cons, Bool.and_eq_true] at hnoptr
    simp only [stepMirStmts] at hstep
    cases h1 : stepMirStmt st s with
    | error _ => simp [h1] at hstep
    | ok st1 =>
      simp only [h1] at hstep
      exact SinkStateInv_stepMirStmts (SinkStateInv_stepMirStmt hinv hnoptr.1 h1) hnoptr.2 hstep

private def SinkMidRel (cert : StoreSinkToCleanupCert) (valOp : ValOp) (v1 : UInt64)
    (fm_s : FieldMeta) (st_s st_t : ExecState) : Prop :=
  st_s.valRegs = st_t.valRegs ∧
  st_s.ptrRegs = st_t.ptrRegs ∧
  st_s.nextTag = st_t.nextTag ∧
  st_s.nextCallId = st_t.nextCallId ∧
  st_s.trace = st_t.trace ∧
  st_s.unwindState = st_t.unwindState ∧
  (∀ p, st_s.unwindState ≠ .enteringCleanup p) ∧
  evalValOp st_t.valRegs valOp = .ok v1 ∧
  (∀ pr p, st_s.ptrRegs pr = some p → PtrDisjoint cert.alloc cert.field p) ∧
  ∃ fm_t, HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap

private theorem sink_step_mid_stmt {cert : StoreSinkToCleanupCert} {valOp : ValOp} {v1 : UInt64}
    {fm_s : FieldMeta} {st_s st_t : ExecState} {s : MirStmt}
    (hrel : SinkMidRel cert valOp v1 fm_s st_s st_t)
    (hnoptr : stmtNoPtrToField cert.alloc cert.field s = true)
    (hdisj : stmtDisjointForSink cert.alloc cert.field valOp s = true) :
    (∃ e, stepMirStmt st_s s = .error e ∧ stepMirStmt st_t s = .error e) ∨
    (∃ st_s' st_t',
      stepMirStmt st_s s = .ok st_s' ∧
      stepMirStmt st_t s = .ok st_t' ∧
      SinkMidRel cert valOp v1 fm_s st_s' st_t') := by
  rcases hrel with ⟨hvr, hpr, hnt, hnc, htr, huw, hnoEnt, heval, hpd, fm_t, hha⟩
  cases s with
  | landingPad _ => simp [stmtDisjointForSink] at hdisj
  | assignReg dst op =>
    simp only [stmtDisjointForSink, stmtWritesValReg, Bool.and_true] at hdisj
    simp only [stepMirStmt, ← huw, ← hvr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hev : evalValOp st_s.valRegs op with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok v =>
        right
        refine ⟨_, _, rfl, rfl, rfl, hpr, hnt, hnc, htr, rfl,
          fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
          ?_, hpd, fm_t, hha⟩
        dsimp only []
        rw [hvr, evalValOp_bindValReg_unchanged v (by cases valOp <;> exact hdisj)]
        exact heval
  | binOp dst bop lhs rhs =>
    simp only [stmtDisjointForSink, stmtWritesValReg, Bool.and_true] at hdisj
    simp only [stepMirStmt, ← huw, ← hvr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hl : evalValOp st_s.valRegs lhs with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok va =>
        cases hr : evalValOp st_s.valRegs rhs with
        | error e => left; exact ⟨e, rfl, rfl⟩
        | ok vb =>
          right
          refine ⟨_, _, rfl, rfl, rfl, hpr, hnt, hnc, htr, rfl,
            fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
            ?_, hpd, fm_t, hha⟩
          dsimp only []
          rw [hvr, evalValOp_bindValReg_unchanged _ (by cases valOp <;> exact hdisj)]
          exact heval
  | readField dst a f =>
    simp only [stmtDisjointForSink, stmtWritesValReg, Bool.and_eq_true] at hdisj
    rcases hdisj with ⟨hregDisj, hftDisj⟩
    have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
      by_cases ha : a = cert.alloc
      · right; intro hf; subst ha; subst hf; rw [nat_beq_self, nat_beq_self] at hftDisj; cases hftDisj
      · exact Or.inl ha
    simp only [stepMirStmt, ← huw]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      by_cases ha : a = cert.alloc
      · subst ha
        have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
        rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
          ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hgf := hfother f hfn
        simp only [hsa1, hsa2, ← hgf]
        cases hg1 : getAt? sa1.fields f with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some fm0 =>
          dsimp only []
          cases htb : tbRootAccessField .read none fm0 with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fm' =>
            dsimp only []
            obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
            obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
            obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
            simp only [hfs1, hfs2, hs1, hs2]
            right
            refine ⟨_, _, rfl, rfl, by dsimp only []; rw [hvr], hpr, hnt, hnc, htr, rfl,
              fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
              ?_, hpd, fm_t, HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2⟩
            dsimp only []
            rw [evalValOp_bindValReg_unchanged _ (by cases valOp <;> exact hregDisj)]
            exact heval
      · have hga := hha.2.1 a ha
        rw [← hga]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases hgf : getAt? sa.fields f with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases htb : tbRootAccessField .read none fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
              simp only [hfs', hs1, hs2]
              right
              refine ⟨_, _, rfl, rfl, by dsimp only []; rw [hvr], hpr, hnt, hnc, htr, rfl,
                fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
                ?_, hpd, fm_t, HeapAgreeExcept_set_other_alloc hha ha hs1 hs2⟩
              dsimp only []
              rw [evalValOp_bindValReg_unchanged _ (by cases valOp <;> exact hregDisj)]
              exact heval
  | writeField a f op =>
    simp only [stmtDisjointForSink, stmtWritesValReg, Bool.and_eq_true] at hdisj
    have hftDisj := hdisj.2
    have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
      by_cases ha : a = cert.alloc
      · right; intro hf; subst ha; subst hf; rw [nat_beq_self, nat_beq_self] at hftDisj; cases hftDisj
      · exact Or.inl ha
    simp only [stepMirStmt, ← huw, ← hvr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      by_cases ha : a = cert.alloc
      · subst ha
        have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
        rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
          ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hgf := hfother f hfn
        simp only [hsa1, hsa2, ← hgf]
        cases hg1 : getAt? sa1.fields f with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some fm0 =>
          dsimp only []
          cases hev : evalValOp st_s.valRegs op with
          | error e => left; exact ⟨e, rfl, rfl⟩
          | ok v =>
            dsimp only []
            cases htb : tbRootAccessField .write (some v) fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
              obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
              simp only [hfs1, hfs2, hs1, hs2]
              right
              exact ⟨_, _, rfl, rfl, rfl, hpr, hnt, hnc, htr, rfl,
                fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
                by dsimp only []; rw [hvr]; exact heval,
                hpd, fm_t, HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2⟩
      · have hga := hha.2.1 a ha
        rw [← hga]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases hgf : getAt? sa.fields f with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases hev : evalValOp st_s.valRegs op with
            | error e => left; exact ⟨e, rfl, rfl⟩
            | ok v =>
              dsimp only []
              cases htb : tbRootAccessField .write (some v) fm0 with
              | none => left; exact ⟨.tbUb, rfl, rfl⟩
              | some fm' =>
                dsimp only []
                obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
                obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
                obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
                simp only [hfs', hs1, hs2]
                right
                exact ⟨_, _, rfl, rfl, rfl, hpr, hnt, hnc, htr, rfl,
                  fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
                  by dsimp only []; rw [hvr]; exact heval,
                  hpd, fm_t, HeapAgreeExcept_set_other_alloc hha ha hs1 hs2⟩
  | readPtr dst pr =>
    simp only [stmtDisjointForSink, stmtWritesValReg, Bool.and_true] at hdisj
    simp only [stepMirStmt, ← huw, ← hpr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hptr : st_s.ptrRegs pr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        dsimp only []
        rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hptr) .read none with
          ⟨e, he1, he2⟩ | ⟨v, h1', h2', ho1, ho2, hha'⟩
        · left; exact ⟨e, by rw [he1], by rw [he2]⟩
        · simp only [ho1, ho2]
          right
          refine ⟨_, _, rfl, rfl, by dsimp only []; rw [hvr], rfl, hnt, hnc, htr, rfl,
            fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
            ?_, hpd, fm_t, hha'⟩
          dsimp only []
          rw [evalValOp_bindValReg_unchanged _ (by cases valOp <;> exact hdisj)]
          exact heval
  | writePtr pr op =>
    simp only [stepMirStmt, ← huw, ← hpr, ← hvr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hptr : st_s.ptrRegs pr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        dsimp only []
        cases hev : evalValOp st_s.valRegs op with
        | error e => left; exact ⟨e, rfl, rfl⟩
        | ok v =>
          dsimp only []
          rcases HeapAgreeExcept_accessHeapByPtr hha (hpd pr p hptr) .write (some v) with
            ⟨e, he1, he2⟩ | ⟨_, h1', h2', ho1, ho2, hha'⟩
          · left; exact ⟨e, by rw [he1], by rw [he2]⟩
          · simp only [ho1, ho2]
            right
            exact ⟨_, _, rfl, rfl, rfl, rfl, hnt, hnc, htr, rfl,
              fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
              by dsimp only []; rw [hvr]; exact heval,
              hpd, fm_t, hha'⟩
  | takeFieldPtr dst a f kind =>
    simp only [stmtNoPtrToField] at hnoptr
    have hne : a ≠ cert.alloc ∨ f ≠ cert.field := by
      by_cases ha : a = cert.alloc
      · right; intro hf; subst ha; subst hf; rw [nat_beq_self, nat_beq_self] at hnoptr; cases hnoptr
      · exact Or.inl ha
    have hpd_new : ∀ pr p, bindPtrReg st_s.ptrRegs dst
        { allocId := a, field := f, scope := .fieldOnly f, kind := kind, tag := st_s.nextTag } pr = some p →
        PtrDisjoint cert.alloc cert.field p := by
      intro pr p hp
      by_cases hprd : pr = dst
      · subst hprd
        rw [bindPtrReg_same] at hp
        injection hp with hp; subst hp
        rcases hne with ha | hf
        · exact Or.inl ha
        · exact Or.inr ⟨f, rfl, hf⟩
      · rw [bindPtrReg_ne _ _ hprd] at hp
        exact hpd pr p hp
    simp only [stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      by_cases ha : a = cert.alloc
      · subst ha
        have hfn : f ≠ cert.field := by rcases hne with h | h; exact absurd rfl h; exact h
        rcases hha with ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hha_full : HeapAgreeExcept cert.alloc cert.field fm_s fm_t st_s.heap st_t.heap :=
          ⟨hlen, hother, hinv1, hinv2, sa1, sa2, hsa1, hsa2, hflen, hfother, hfm1, hfm2⟩
        have hgf := hfother f hfn
        simp only [hsa1, hsa2, ← hgf]
        cases hg1 : getAt? sa1.fields f with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some fm0 =>
          dsimp only []
          cases htb : tbRetagField st_s.nextTag kind fm0 with
          | none => left; exact ⟨.tbUb, rfl, rfl⟩
          | some fm' =>
            dsimp only []
            obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm' hg1
            obtain ⟨fs2, hfs2⟩ := setAt?_of_getAt? fm' (hgf.symm.trans hg1)
            obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa1 with fields := fs1 } hsa1
            obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa2 with fields := fs2 } hsa2
            simp only [hfs1, hfs2, hs1, hs2]
            right
            exact ⟨_, _, rfl, rfl, hvr, by dsimp only []; rw [hpr], rfl, hnc, htr, rfl,
              fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
              heval, hpd_new, fm_t, HeapAgreeExcept_set_other_field hha_full hfn hsa1 hsa2 hfs1 hfs2 hs1 hs2⟩
      · have hga := hha.2.1 a ha
        rw [← hga]
        cases hg1 : getAt? st_s.heap a with
        | none => left; exact ⟨.unsupported, rfl, rfl⟩
        | some sa =>
          dsimp only []
          cases hgf : getAt? sa.fields f with
          | none => left; exact ⟨.unsupported, rfl, rfl⟩
          | some fm0 =>
            dsimp only []
            cases htb : tbRetagField st_s.nextTag kind fm0 with
            | none => left; exact ⟨.tbUb, rfl, rfl⟩
            | some fm' =>
              dsimp only []
              obtain ⟨fs', hfs'⟩ := setAt?_of_getAt? fm' hgf
              obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
              obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
              simp only [hfs', hs1, hs2]
              right
              exact ⟨_, _, rfl, rfl, hvr, by dsimp only []; rw [hpr], rfl, hnc, htr, rfl,
                fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
                heval, hpd_new, fm_t, HeapAgreeExcept_set_other_alloc hha ha hs1 hs2⟩
  | takeRootSharedRef dst a =>
    simp only [stmtNoPtrToField, bne_iff_ne, ne_eq] at hnoptr
    simp only [stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      have hga := hha.2.1 a hnoptr
      rw [← hga]
      cases hg1 : getAt? st_s.heap a with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some sa =>
        dsimp only []
        cases htb : tbRetagAllFields st_s.nextTag .shared sa.fields with
        | none => left; exact ⟨.tbUb, rfl, rfl⟩
        | some fs' =>
          dsimp only []
          obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
          obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
          simp only [hs1, hs2]
          right
          refine ⟨_, _, rfl, rfl, hvr, by dsimp only []; rw [hpr], rfl, hnc, htr, rfl,
            fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
            heval, ?_, fm_t, HeapAgreeExcept_set_other_alloc hha hnoptr hs1 hs2⟩
          intro pr p hp
          dsimp only [] at hp
          by_cases hprd : pr = dst
          · subst hprd
            rw [bindPtrReg_same] at hp
            injection hp with hp; subst hp; exact Or.inl hnoptr
          · rw [bindPtrReg_ne _ _ hprd] at hp
            exact hpd pr p hp
  | takeRootRawPtr dst a =>
    simp only [stmtNoPtrToField, bne_iff_ne, ne_eq] at hnoptr
    simp only [stepMirStmt, ← huw, ← hnt]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      have hga := hha.2.1 a hnoptr
      rw [← hga]
      cases hg1 : getAt? st_s.heap a with
      | none => left; exact ⟨.unsupported, rfl, rfl⟩
      | some sa =>
        dsimp only []
        cases htb : tbRetagAllFields st_s.nextTag .rawMut sa.fields with
        | none => left; exact ⟨.tbUb, rfl, rfl⟩
        | some fs' =>
          dsimp only []
          obtain ⟨h1', hs1⟩ := setAt?_of_getAt? { sa with fields := fs' } hg1
          obtain ⟨h2', hs2⟩ := setAt?_of_getAt? { sa with fields := fs' } (hga.symm.trans hg1)
          simp only [hs1, hs2]
          right
          refine ⟨_, _, rfl, rfl, hvr, by dsimp only []; rw [hpr], rfl, hnc, htr, rfl,
            fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
            heval, ?_, fm_t, HeapAgreeExcept_set_other_alloc hha hnoptr hs1 hs2⟩
          intro pr p hp
          dsimp only [] at hp
          by_cases hprd : pr = dst
          · subst hprd
            rw [bindPtrReg_same] at hp
            injection hp with hp; subst hp; exact Or.inl hnoptr
          · rw [bindPtrReg_ne _ _ hprd] at hp
            exact hpd pr p hp
  | ptrOffset dst srcPr targetField =>
    simp only [stepMirStmt, ← huw, ← hpr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hptr : st_s.ptrRegs srcPr with
      | none => left; exact ⟨.tbUb, rfl, rfl⟩
      | some p =>
        right
        refine ⟨_, _, rfl, rfl, hvr, rfl, hnt, hnc, htr, rfl,
          fun q hq => by dsimp only [] at hq; rw [← hu] at hq; exact hnoEnt q hq,
          heval, ?_, fm_t, hha⟩
        intro pr q hq
        dsimp only [] at hq
        by_cases hprd : pr = dst
        · subst hprd
          rw [bindPtrReg_same] at hq
          injection hq with hq; subst hq
          exact hpd srcPr p hptr
        · rw [bindPtrReg_ne _ _ hprd] at hq
          exact hpd pr q hq
  | emitObs op =>
    simp only [stepMirStmt, ← huw, ← hvr]
    cases hu : st_s.unwindState with
    | enteringCleanup p => exact absurd hu (hnoEnt p)
    | normal | inCleanup _ =>
      cases hev : evalValOp st_s.valRegs op with
      | error e => left; exact ⟨e, rfl, rfl⟩
      | ok v =>
        right
        exact ⟨_, _, rfl, rfl, rfl, hpr, hnt, hnc, by dsimp only []; rw [htr], rfl,
          fun p hp => by dsimp only [] at hp; rw [← hu] at hp; exact hnoEnt p hp,
          by dsimp only []; rw [hvr]; exact heval,
          hpd, fm_t, hha⟩

private theorem sink_step_mid_stmts {cert : StoreSinkToCleanupCert} {valOp : ValOp} {v1 : UInt64}
    {fm_s : FieldMeta} :
    ∀ {mid : List MirStmt} {st_s st_t : ExecState},
      SinkMidRel cert valOp v1 fm_s st_s st_t →
      mid.all (stmtNoPtrToField cert.alloc cert.field) = true →
      mid.all (stmtDisjointForSink cert.alloc cert.field valOp) = true →
      (∃ e, stepMirStmts st_s mid = .error e ∧ stepMirStmts st_t mid = .error e) ∨
      (∃ st_s' st_t',
        stepMirStmts st_s mid = .ok st_s' ∧
        stepMirStmts st_t mid = .ok st_t' ∧
        SinkMidRel cert valOp v1 fm_s st_s' st_t')
  | [], st_s, st_t, hrel, _, _ => Or.inr ⟨st_s, st_t, rfl, rfl, hrel⟩
  | s :: rest, st_s, st_t, hrel, hnoptr, hdisj => by
    simp only [List.all_cons, Bool.and_eq_true] at hnoptr hdisj
    simp only [stepMirStmts]
    rcases sink_step_mid_stmt hrel hnoptr.1 hdisj.1 with
      ⟨e, he1, he2⟩ | ⟨st_s1, st_t1, ho1, ho2, hrel1⟩
    · left; exact ⟨e, by rw [he1], by rw [he2]⟩
    · rw [ho1, ho2]
      exact sink_step_mid_stmts hrel1 hnoptr.2 hdisj.2

private structure SinkCtx (src tgt : MirBody) (cert : StoreSinkToCleanupCert) where
  sinkBlk      : MirBlock
  pre          : List MirStmt
  valOp        : ValOp
  mid          : List MirStmt
  cid          : CalleeId
  argPtrs      : List PtrRegId
  retDst       : Option ValRegId
  normTgt      : BlockId
  cleanTgt     : BlockId
  normBlk      : MirBlock
  op2          : ValOp
  normRest     : List MirStmt
  cleanBlk     : MirBlock
  lpDst        : Option ValRegId
  cleanRest    : List MirStmt
  hfrz         : fieldIsFreeze src cert.alloc cert.field = true
  hdecls       : tgt.allocDecls = src.allocDecls
  hnoptr       : (src.blocks.all fun blk => blk.stmts.all (stmtNoPtrToField cert.alloc cert.field)) = true
  hsinkSrc     : getAt? src.blocks cert.sinkBlock = some sinkBlk
  hsinkStmts   : sinkBlk.stmts = pre ++ .writeField cert.alloc cert.field valOp :: mid
  hsinkTerm    : sinkBlk.term = .callMayUnwind cid argPtrs retDst normTgt cleanTgt
  hsinkTgt     : getAt? tgt.blocks cert.sinkBlock = some { stmts := pre ++ mid, term := sinkBlk.term }
  hcleanNe0    : cleanTgt ≠ 0
  hcleanNeSink : cleanTgt ≠ cert.sinkBlock
  hnormNeSink  : normTgt ≠ cert.sinkBlock
  hcleanNeNorm : cleanTgt ≠ normTgt
  hnoCleanSink : (src.blocks.all fun blk => termNoCleanSink cert.sinkBlock blk.term) = true
  huniqPred    : ((List.range src.blocks.length).all fun pc =>
    if pc = cert.sinkBlock then true
    else match getAt? src.blocks pc with
      | some blk => !termTargets blk.term cleanTgt
      | none => false) = true
  hmidDisj     : mid.all (stmtDisjointForSink cert.alloc cert.field valOp) = true
  hnormSrc     : getAt? src.blocks normTgt = some normBlk
  hnormStmts   : normBlk.stmts = .writeField cert.alloc cert.field op2 :: normRest
  hcleanSrc    : getAt? src.blocks cleanTgt = some cleanBlk
  hcleanStmts  : cleanBlk.stmts = .landingPad lpDst :: cleanRest
  hcleanTgt    : getAt? tgt.blocks cleanTgt =
    some { stmts := .landingPad lpDst :: .writeField cert.alloc cert.field valOp :: cleanRest
         , term := cleanBlk.term }
  hlpDisj      : valOpDisjointOptReg valOp lpDst = true
  hotherTgt    : ∀ pc, pc ≠ cert.sinkBlock → pc ≠ cleanTgt → getAt? tgt.blocks pc = getAt? src.blocks pc

private theorem unpackStoreSinkCert {src tgt : MirBody} {cert : StoreSinkToCleanupCert}
    (hcert : checkStoreSinkCert src tgt cert = true) : Nonempty (SinkCtx src tgt cert) := by
  unfold checkStoreSinkCert at hcert
  simp only [Bool.and_eq_true] at hcert
  rcases hcert with ⟨⟨hfrz, hnoptr⟩, hrest⟩
  cases hsinkSrc : getAt? src.blocks cert.sinkBlock with
  | none => simp [hsinkSrc] at hrest
  | some sinkBlk =>
    simp only [hsinkSrc] at hrest
    cases hsp : splitAtIdx? sinkBlk.stmts cert.storeIdx with
    | none => simp [hsp] at hrest
    | some triple =>
      rcases triple with ⟨pre, stmt0, mid⟩
      cases hst0 : stmt0 with
      | writeField a f valOp =>
        cases hterm : sinkBlk.term with
        | callMayUnwind cid argPtrs retDst normTgt cleanTgt =>
          simp only [hsp, hst0, hterm, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hrest
          rcases hrest with
            ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hf⟩, _⟩, _⟩, hcleanNe0⟩, hcleanNeSink⟩, hnormNeSink⟩, hcleanNeNorm⟩,
              hnoCleanSink⟩, huniqPred⟩, hmidDisj⟩, hnormMatch⟩, hcleanMatch⟩, happ⟩
          subst ha; subst hf
          cases hnormSrc : getAt? src.blocks normTgt with
          | none => simp [hnormSrc] at hnormMatch
          | some normBlk =>
            simp only [hnormSrc] at hnormMatch
            cases hns : normBlk.stmts with
            | nil => simp [hns] at hnormMatch
            | cons ns0 normRest =>
              cases hns0 : ns0 with
              | writeField a2 f2 op2 =>
                simp only [hns, hns0, Bool.and_eq_true, beq_iff_eq] at hnormMatch
                rcases hnormMatch with ⟨rfl, rfl⟩
                cases hcleanSrc : getAt? src.blocks cleanTgt with
                | none => simp [hcleanSrc] at hcleanMatch
                | some cleanBlk =>
                  simp only [hcleanSrc] at hcleanMatch
                  cases hcs : cleanBlk.stmts with
                  | nil => simp [hcs] at hcleanMatch
                  | cons cs0 cleanRest =>
                    cases hcs0 : cs0 with
                    | landingPad lpDst =>
                      simp only [hcs, hcs0] at hcleanMatch
                      unfold applyStoreSink? at happ
                      simp only [hsinkSrc, hsp, hst0, hterm, bne_self_eq_false, Bool.or_self,
                        Bool.false_eq_true, ↓reduceIte, hcleanSrc, hcs, hcs0] at happ
                      let sinkBlk' : MirBlock :=
                        { stmts := pre ++ mid, term := .callMayUnwind cid argPtrs retDst normTgt cleanTgt }
                      let cleanBlk' : MirBlock :=
                        { stmts := .landingPad lpDst :: .writeField cert.alloc cert.field valOp :: cleanRest
                        , term := cleanBlk.term }
                      cases hs1 : setAt? src.blocks cert.sinkBlock sinkBlk' with
                      | none => simp [sinkBlk', hs1] at happ
                      | some b1 =>
                        simp only [sinkBlk', hs1] at happ
                        cases hs2 : setAt? b1 cleanTgt cleanBlk' with
                        | none => simp [cleanBlk', hs2] at happ
                        | some b2 =>
                          simp only [cleanBlk', hs2, Option.some.injEq] at happ
                          have hdecls : tgt.allocDecls = src.allocDecls := by rw [← happ]
                          have hb2 : tgt.blocks = b2 := by rw [← happ]
                          refine ⟨{
                            sinkBlk := sinkBlk
                            pre := pre
                            valOp := valOp
                            mid := mid
                            cid := cid
                            argPtrs := argPtrs
                            retDst := retDst
                            normTgt := normTgt
                            cleanTgt := cleanTgt
                            normBlk := normBlk
                            op2 := op2
                            normRest := normRest
                            cleanBlk := cleanBlk
                            lpDst := lpDst
                            cleanRest := cleanRest
                            hfrz := hfrz
                            hdecls := hdecls
                            hnoptr := hnoptr
                            hsinkSrc := hsinkSrc
                            hsinkStmts := by rw [← hst0]; exact splitAtIdx?_sound hsp
                            hsinkTerm := hterm
                            hsinkTgt := by
                              rw [hb2, getAt?_setAt?_ne hs2 (Ne.symm hcleanNeSink),
                                getAt?_setAt?_same hs1]
                              simp [sinkBlk', hterm]
                            hcleanNe0 := hcleanNe0
                            hcleanNeSink := hcleanNeSink
                            hnormNeSink := hnormNeSink
                            hcleanNeNorm := hcleanNeNorm
                            hnoCleanSink := by
                              rw [List.all_eq_true] at hnoCleanSink ⊢
                              intro blk hmem
                              exact hnoCleanSink blk hmem
                            huniqPred := huniqPred
                            hmidDisj := hmidDisj
                            hnormSrc := hnormSrc
                            hnormStmts := by rw [hns, hns0]
                            hcleanSrc := hcleanSrc
                            hcleanStmts := by rw [hcs, hcs0]
                            hcleanTgt := by
                              rw [hb2, getAt?_setAt?_same hs2]
                            hlpDisj := by
                              cases valOp with
                              | constU64 _ => rfl
                              | reg r =>
                                cases lpDst with
                                | none => rfl
                                | some d => exact hcleanMatch
                            hotherTgt := fun pc hne1 hne2 => by
                              rw [hb2, getAt?_setAt?_ne hs2 hne2, getAt?_setAt?_ne hs1 hne1]
                          }⟩
                    | _ => simp [hcs, hcs0] at hcleanMatch
              | _ => simp [hns, hns0] at hnormMatch
        | _ => simp [hsp, hst0, hterm] at hrest
      | _ => simp [hsp, hst0] at hrest

private theorem sink_not_clean_of_ne_sink {src tgt : MirBody} {cert : StoreSinkToCleanupCert}
    (ctx : SinkCtx src tgt cert) {pc : BlockId} {blk : MirBlock}
    (hne : pc ≠ cert.sinkBlock) (hblk : getAt? src.blocks pc = some blk) :
    termTargets blk.term ctx.cleanTgt = false := by
  have h := range_all_apply ctx.huniqPred (getAt?_lt hblk)
  simp only [hne, ↓reduceIte, hblk, Bool.not_eq_true'] at h
  exact h

private theorem sink_exec_equal_block_body {src tgt : MirBody} {cert : StoreSinkToCleanupCert}
    (ctx : SinkCtx src tgt cert) (pm : PanicMode) (env : CalleeEnv)
    {fuel : Nat} {stmts : List MirStmt} {term : MirTerm} {st : ExecState}
    (hinv : SinkStateInv cert st)
    (hnoptr : stmts.all (stmtNoPtrToField cert.alloc cert.field) = true)
    (hnotClean : termTargets term ctx.cleanTgt = false)
    (hnotSinkClean : termNoCleanSink cert.sinkBlock term = true)
    (ih : ∀ pc' st',
      pc' ≠ ctx.cleanTgt →
      (pc' = cert.sinkBlock → ∀ p, st'.unwindState ≠ .enteringCleanup p) →
      SinkStateInv cert st' →
      refines (execMirLoop pm src env fuel pc' st') (execMirLoop pm tgt env fuel pc' st')) :
    refines (execMirBlockBody pm src env fuel stmts term st)
            (execMirBlockBody pm tgt env fuel stmts term st) := by
  unfold execMirBlockBody
  cases hst : stepMirStmts st stmts with
  | error e => exact refines_of_eq rfl
  | ok st1 =>
    dsimp only []
    have hinv1 : SinkStateInv cert st1 := SinkStateInv_stepMirStmts hinv hnoptr hst
    cases hu : st1.unwindState with
    | enteringCleanup _ => exact refines_of_eq rfl
    | normal =>
      have hnoEnt1 : ∀ p, st1.unwindState ≠ .enteringCleanup p := by
        intro p hp; rw [hu] at hp; cases hp
      cases term with
      | goto tgtPc =>
        simp only [termTargets, beq_eq_false_iff_ne] at hnotClean
        exact ih tgtPc st1 hnotClean (fun _ => hnoEnt1) hinv1
      | switchZero discr zTgt nzTgt =>
        simp only [termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnotClean
        dsimp only []
        cases evalValOp st1.valRegs discr with
        | error _ => exact refines_of_eq rfl
        | ok n =>
          dsimp only []
          split
          · exact ih zTgt st1 hnotClean.1 (fun _ => hnoEnt1) hinv1
          · exact ih nzTgt st1 hnotClean.2 (fun _ => hnoEnt1) hinv1
      | ret op =>
        dsimp only []
        cases evalValOp st1.valRegs op <;> exact refines_of_eq rfl
      | resume => exact refines_of_eq rfl
      | catchUnwind _ _ => exact refines_of_eq rfl
      | callMayUnwind cid argPtrs retDst nTgt cTgt =>
        simp only [termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnotClean
        simp only [termNoCleanSink, bne_iff_ne, ne_eq] at hnotSinkClean
        dsimp only []
        cases env cid with
        | none => exact refines_of_eq rfl
        | some callee =>
          dsimp only []
          cases hargs : evalArgPtrs st1.ptrRegs argPtrs with
          | error _ => exact refines_of_eq rfl
          | ok ptrVals =>
            dsimp only []
            rcases hinv1 with ⟨hpd, fm, hha⟩
            have hds := PtrDisjoint_evalArgPtrs hpd hargs
            cases hap : activateProtectors st1.nextCallId st1.heap ptrVals with
            | error _ => exact refines_of_eq rfl
            | ok heapProt =>
              dsimp only []
              have hha1 : HeapAgreeExcept cert.alloc cert.field fm fm heapProt heapProt := by
                rcases HeapAgreeExcept_activateProtectors st1.nextCallId hha hds with
                  ⟨e, he, _⟩ | ⟨hp1, hp2, ho1, ho2, h'⟩
                · rw [hap] at he; cases he
                · rw [hap] at ho1 ho2
                  injection ho1 with heq1; injection ho2 with heq2
                  subst heq1; subst heq2; exact h'
              cases hops : stepCalleeOps ptrVals heapProt st1.trace callee.ops with
              | error _ => exact refines_of_eq rfl
              | ok res =>
                rcases res with ⟨heapAfter, traceAfter⟩
                dsimp only []
                have hha2 : HeapAgreeExcept cert.alloc cert.field fm fm heapAfter heapAfter := by
                  rcases HeapAgreeExcept_stepCalleeOps hds hha1 (ops := callee.ops) (tr := st1.trace) with
                    ⟨e, he, _⟩ | ⟨ha1, ha2, tr', ho1, ho2, h'⟩
                  · rw [hops] at he; cases he
                  · rw [hops] at ho1 ho2
                    simp only [Except.ok.injEq, Prod.mk.injEq] at ho1 ho2
                    rcases ho1 with ⟨rfl, _⟩; rcases ho2 with ⟨rfl, _⟩
                    exact h'
                have hha3 := HeapAgreeExcept_releaseProtectorHeap st1.nextCallId hha2
                cases callee.exit with
                | normal retVal =>
                  dsimp only []
                  exact ih nTgt
                    { st1 with
                      heap := releaseProtectorHeap st1.nextCallId heapAfter
                      nextCallId := st1.nextCallId + 1
                      trace := traceAfter
                      valRegs := bindOptValReg st1.valRegs retDst retVal
                      unwindState := .normal }
                    hnotClean.1
                    (fun _ _ hp => by cases hp)
                    ⟨hpd, fm, hha3⟩
                | panic payload =>
                  dsimp only []
                  cases pm with
                  | abort => exact refines_of_eq rfl
                  | unwind =>
                    dsimp only []
                    exact ih cTgt
                      { st1 with
                        heap := releaseProtectorHeap st1.nextCallId heapAfter
                        nextCallId := st1.nextCallId + 1
                        trace := traceAfter
                        unwindState := .enteringCleanup payload }
                      hnotClean.2
                      (fun hc => absurd hc hnotSinkClean)
                      ⟨hpd, fm, hha3⟩
    | inCleanup cpPayload =>
      have hnoEnt1 : ∀ p, st1.unwindState ≠ .enteringCleanup p := by
        intro p hp; rw [hu] at hp; cases hp
      cases term with
      | goto tgtPc =>
        simp only [termTargets, beq_eq_false_iff_ne] at hnotClean
        exact ih tgtPc st1 hnotClean (fun _ => hnoEnt1) hinv1
      | switchZero discr zTgt nzTgt =>
        simp only [termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnotClean
        dsimp only []
        cases evalValOp st1.valRegs discr with
        | error _ => exact refines_of_eq rfl
        | ok n =>
          dsimp only []
          split
          · exact ih zTgt st1 hnotClean.1 (fun _ => hnoEnt1) hinv1
          · exact ih nzTgt st1 hnotClean.2 (fun _ => hnoEnt1) hinv1
      | ret _ => exact refines_of_eq rfl
      | resume => exact refines_of_eq rfl
      | catchUnwind dst recTgt =>
        simp only [termTargets, beq_eq_false_iff_ne] at hnotClean
        dsimp only []
        exact ih recTgt
          { st1 with unwindState := .normal, valRegs := bindOptValReg st1.valRegs dst cpPayload }
          hnotClean (fun _ _ hp => by cases hp) ⟨hinv1.1, hinv1.2⟩
      | callMayUnwind cid argPtrs retDst nTgt cTgt =>
        simp only [termTargets, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnotClean
        dsimp only []
        cases env cid with
        | none => exact refines_of_eq rfl
        | some callee =>
          dsimp only []
          cases hargs : evalArgPtrs st1.ptrRegs argPtrs with
          | error _ => exact refines_of_eq rfl
          | ok ptrVals =>
            dsimp only []
            rcases hinv1 with ⟨hpd, fm, hha⟩
            have hds := PtrDisjoint_evalArgPtrs hpd hargs
            cases hap : activateProtectors st1.nextCallId st1.heap ptrVals with
            | error _ => exact refines_of_eq rfl
            | ok heapProt =>
              dsimp only []
              have hha1 : HeapAgreeExcept cert.alloc cert.field fm fm heapProt heapProt := by
                rcases HeapAgreeExcept_activateProtectors st1.nextCallId hha hds with
                  ⟨e, he, _⟩ | ⟨hp1, hp2, ho1, ho2, h'⟩
                · rw [hap] at he; cases he
                · rw [hap] at ho1 ho2
                  injection ho1 with heq1; injection ho2 with heq2
                  subst heq1; subst heq2; exact h'
              cases hops : stepCalleeOps ptrVals heapProt st1.trace callee.ops with
              | error _ => exact refines_of_eq rfl
              | ok res =>
                rcases res with ⟨heapAfter, traceAfter⟩
                dsimp only []
                have hha2 : HeapAgreeExcept cert.alloc cert.field fm fm heapAfter heapAfter := by
                  rcases HeapAgreeExcept_stepCalleeOps hds hha1 (ops := callee.ops) (tr := st1.trace) with
                    ⟨e, he, _⟩ | ⟨ha1, ha2, tr', ho1, ho2, h'⟩
                  · rw [hops] at he; cases he
                  · rw [hops] at ho1 ho2
                    simp only [Except.ok.injEq, Prod.mk.injEq] at ho1 ho2
                    rcases ho1 with ⟨rfl, _⟩; rcases ho2 with ⟨rfl, _⟩
                    exact h'
                have hha3 := HeapAgreeExcept_releaseProtectorHeap st1.nextCallId hha2
                cases callee.exit with
                | normal retVal =>
                  dsimp only []
                  exact ih nTgt
                    { st1 with
                      heap := releaseProtectorHeap st1.nextCallId heapAfter
                      nextCallId := st1.nextCallId + 1
                      trace := traceAfter
                      valRegs := bindOptValReg st1.valRegs retDst retVal
                      unwindState := .inCleanup cpPayload }
                    hnotClean.1
                    (fun _ _ hp => by cases hp)
                    ⟨hpd, fm, hha3⟩
                | panic _ =>
                  cases pm <;> exact refines_of_eq rfl

private theorem sink_execMirLoop_bounded {src tgt : MirBody} {cert : StoreSinkToCleanupCert}
    (ctx : SinkCtx src tgt cert) (pm : PanicMode) (env : CalleeEnv) :
    ∀ n fuel, fuel ≤ n → ∀ pc st,
      pc ≠ ctx.cleanTgt →
      (pc = cert.sinkBlock → ∀ p, st.unwindState ≠ .enteringCleanup p) →
      SinkStateInv cert st →
      refines (execMirLoop pm src env fuel pc st) (execMirLoop pm tgt env fuel pc st)
  | _, 0, _, _, _, _, _, _ => refines_of_eq rfl
  | 0, _ + 1, hle, _, _, _, _, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, f1 + 1, hle, pc, st, hneClean, hnoEntSink, hinv => by
    have hf1 : f1 ≤ n := Nat.le_of_succ_le_succ hle
    by_cases hpc : pc = cert.sinkBlock
    · subst hpc
      have hnoEnt := hnoEntSink rfl
      rw [execMirLoop_succ, execMirLoop_succ, ctx.hsinkSrc, ctx.hsinkTgt]
      dsimp only []
      rw [ctx.hsinkStmts]
      unfold execMirBlockBody
      rw [stepMirStmts_append, stepMirStmts_append]
      have hblkNoPtr := all_of_getAt? ctx.hnoptr ctx.hsinkSrc
      rw [ctx.hsinkStmts] at hblkNoPtr
      obtain ⟨hpreNoPtr, hstoreMidNoPtr⟩ := all_append_split hblkNoPtr
      simp only [List.all_cons, Bool.and_eq_true] at hstoreMidNoPtr
      have hmidNoPtr := hstoreMidNoPtr.2
      cases hpre : stepMirStmts st ctx.pre with
      | error e => exact refines_of_eq rfl
      | ok st_pre =>
        dsimp only []
        have hinv_pre : SinkStateInv cert st_pre := SinkStateInv_stepMirStmts hinv hpreNoPtr hpre
        have hnoEnt_pre : ∀ p, st_pre.unwindState ≠ .enteringCleanup p :=
          stepMirStmts_unwindState_ne_entering hnoEnt hpre
        rw [stepMirStmts]
        rcases hinv_pre with ⟨hpd_pre, fm0, hha0⟩
        rcases hha0 with ⟨hlen0, hother0, hinv_fm0, _, sa0, _, hsa0, _, hflen0, hfother0, hfm0, _⟩
        have hha0_refl : HeapAgreeExcept cert.alloc cert.field fm0 fm0 st_pre.heap st_pre.heap :=
          HeapAgreeExcept_refl hsa0 hfm0 hinv_fm0
        -- Evaluate the sunk store `.writeField cert.alloc cert.field ctx.valOp` on `st_pre`
        have hstore_cases :
            (stepMirStmt st_pre (.writeField cert.alloc cert.field ctx.valOp) = .error .tbUb) ∨
            (∃ v1 h_s1,
              evalValOp st_pre.valRegs ctx.valOp = .ok v1 ∧
              stepMirStmt st_pre (.writeField cert.alloc cert.field ctx.valOp) =
                .ok { st_pre with heap := h_s1 } ∧
              HeapAgreeExcept cert.alloc cert.field
                { isUnsafeCell := false, val := v1, perm := .active, children := [] }
                fm0 h_s1 st_pre.heap) := by
          simp only [stepMirStmt]
          cases hu_pre : st_pre.unwindState with
          | enteringCleanup p => exact absurd hu_pre (hnoEnt_pre p)
          | normal | inCleanup _ =>
            rw [hsa0]; dsimp only []
            rw [hfm0]; dsimp only []
            cases hev : evalValOp st_pre.valRegs ctx.valOp with
            | error e =>
              left
              rw [evalValOp_error_tbUb hev]
            | ok v1 =>
              dsimp only []
              rw [tbRootAccessField_write_noChildren hinv_fm0 v1]; dsimp only []
              let fm_v1 : FieldMeta :=
                { isUnsafeCell := false, val := v1, perm := .active, children := [] }
              obtain ⟨fs1, hfs1⟩ := setAt?_of_getAt? fm_v1 hfm0
              obtain ⟨h_s1, hhs1⟩ := setAt?_of_getAt? { sa0 with fields := fs1 } hsa0
              rw [hfs1]; dsimp only []
              rw [hhs1]; dsimp only []
              right
              exact ⟨v1, h_s1, rfl, by rw [← hu_pre],
                HeapAgreeExcept_set_target_left hha0_refl (FieldNoChildrenInv_active v1) hsa0 hfs1 hhs1⟩
        rcases hstore_cases with htbUb | ⟨v1, h_s1, hev1, hstep_store, hha_store⟩
        · rw [htbUb]
          simp [refines]
        · rw [hstep_store]
          dsimp only []
          let fm_v1 : FieldMeta :=
            { isUnsafeCell := false, val := v1, perm := .active, children := [] }
          have hmid_rel0 : SinkMidRel cert ctx.valOp v1 fm_v1 { st_pre with heap := h_s1 } st_pre :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, hnoEnt_pre, hev1, hpd_pre, fm0, hha_store⟩
          rcases sink_step_mid_stmts hmid_rel0 hmidNoPtr ctx.hmidDisj with
            ⟨e, he_s, he_t⟩ | ⟨st_s1, st_t1, ho_s, ho_t, hmid_rel1⟩
          · rw [he_s, he_t]
            exact refines_of_eq rfl
          · rw [ho_s, ho_t]
            dsimp only []
            rcases hmid_rel1 with ⟨hvr1, hpr1, hnt1, hnc1, htr1, huw1, hnoEnt1, heval1, hpd1, fm_t1, hha1⟩
            rw [← huw1, ctx.hsinkTerm]
            cases hu1 : st_s1.unwindState with
            | enteringCleanup p => exact absurd hu1 (hnoEnt1 p)
            | normal | inCleanup _ =>
              dsimp only []
              cases env ctx.cid with
              | none => exact refines_of_eq rfl
              | some callee =>
                dsimp only []
                rw [← hpr1, ← hnc1, ← htr1]
                cases hargs : evalArgPtrs st_s1.ptrRegs ctx.argPtrs with
                | error _ => exact refines_of_eq rfl
                | ok ptrVals =>
                  dsimp only []
                  have hds := PtrDisjoint_evalArgPtrs hpd1 hargs
                  rcases HeapAgreeExcept_activateProtectors st_s1.nextCallId hha1 hds with
                    ⟨e, he1, he2⟩ | ⟨hp_s, hp_t, ho1, ho2, hha2⟩
                  · rw [he1, he2]; exact refines_of_eq rfl
                  · rw [ho1, ho2]
                    dsimp only []
                    rcases HeapAgreeExcept_stepCalleeOps hds hha2 (ops := callee.ops) (tr := st_s1.trace) with
                      ⟨e, he1, he2⟩ | ⟨ha_s, ha_t, tr', ho1', ho2', hha3⟩
                    · rw [he1, he2]; exact refines_of_eq rfl
                    · rw [ho1', ho2']
                      dsimp only []
                      have hha4 := HeapAgreeExcept_releaseProtectorHeap st_s1.nextCallId hha3
                      cases callee.exit with
                      | normal retVal =>
                        dsimp only []
                        cases f1 with
                        | zero => exact refines_of_eq rfl
                        | succ f2 =>
                          have hf2 : f2 ≤ n := Nat.le_of_succ_le hf1
                          rw [execMirLoop_succ, execMirLoop_succ,
                            ctx.hotherTgt ctx.normTgt ctx.hnormNeSink (Ne.symm ctx.hcleanNeNorm),
                            ctx.hnormSrc]
                          dsimp only []
                          rw [ctx.hnormStmts, execMirBlockBody_cons, execMirBlockBody_cons]
                          -- Step `.writeField cert.alloc cert.field ctx.op2` on both sides
                          rcases hha4 with
                            ⟨hlen4, hother4, hinv_s4, hinv_t4, sa_s4, sa_t4, hsa_s4, hsa_t4,
                             hflen4, hfother4, hfm_s4, hfm_t4⟩
                          have hha4_full : HeapAgreeExcept cert.alloc cert.field fm_v1 fm_t1
                              (releaseProtectorHeap st_s1.nextCallId ha_s)
                              (releaseProtectorHeap st_s1.nextCallId ha_t) :=
                            ⟨hlen4, hother4, hinv_s4, hinv_t4, sa_s4, sa_t4, hsa_s4, hsa_t4,
                             hflen4, hfother4, hfm_s4, hfm_t4⟩
                          simp only [stepMirStmt, ← hvr1, ← hnt1, hsa_s4, hsa_t4, hfm_s4, hfm_t4]
                          cases hev2 : evalValOp (bindOptValReg st_s1.valRegs ctx.retDst retVal) ctx.op2 with
                          | error e => exact refines_of_eq rfl
                          | ok v2 =>
                            dsimp only []
                            rw [tbRootAccessField_write_noChildren hinv_s4 v2,
                                tbRootAccessField_write_noChildren hinv_t4 v2]
                            dsimp only []
                            let fm_v2 : FieldMeta :=
                              { isUnsafeCell := false, val := v2, perm := .active, children := [] }
                            obtain ⟨fs_s, hfs_s⟩ := setAt?_of_getAt? fm_v2 hfm_s4
                            obtain ⟨fs_t, hfs_t⟩ := setAt?_of_getAt? fm_v2 hfm_t4
                            obtain ⟨hr_s', hhs_s⟩ := setAt?_of_getAt? { sa_s4 with fields := fs_s } hsa_s4
                            obtain ⟨hr_t', hhs_t⟩ := setAt?_of_getAt? { sa_t4 with fields := fs_t } hsa_t4
                            rw [hfs_s, hfs_t]; dsimp only []
                            rw [hhs_s, hhs_t]; dsimp only []
                            have hact2 := FieldNoChildrenInv_active v2
                            have hha_both : HeapAgreeExcept cert.alloc cert.field fm_v2 fm_v2 hr_s' hr_t' :=
                              HeapAgreeExcept_set_target_right
                                (HeapAgreeExcept_set_target_left hha4_full hact2 hsa_s4 hfs_s hhs_s)
                                hact2 hsa_t4 hfs_t hhs_t
                            have hheap_eq : hr_s' = hr_t' := HeapAgreeExcept_eq_of_fm_eq hha_both
                            subst hheap_eq
                            have hnormNoPtr := all_of_getAt? ctx.hnoptr ctx.hnormSrc
                            rw [ctx.hnormStmts] at hnormNoPtr
                            simp only [List.all_cons, Bool.and_eq_true] at hnormNoPtr
                            exact sink_exec_equal_block_body ctx pm env
                              ⟨hpd1, fm_v2, hha_both⟩
                              hnormNoPtr.2
                              (sink_not_clean_of_ne_sink ctx ctx.hnormNeSink ctx.hnormSrc)
                              (all_of_getAt? (p := fun blk => termNoCleanSink cert.sinkBlock blk.term)
                                ctx.hnoCleanSink ctx.hnormSrc)
                              (fun pc' st' hc1 hc2 hi =>
                                sink_execMirLoop_bounded ctx pm env n f2 hf2 pc' st' hc1 hc2 hi)
                      | panic payload =>
                        dsimp only []
                        cases pm with
                        | abort => exact refines_of_eq rfl
                        | unwind =>
                          first
                          | exact refines_of_eq rfl
                          | (dsimp only []
                             cases f1 with
                             | zero => exact refines_of_eq rfl
                             | succ f2 =>
                               have hf2 : f2 ≤ n := Nat.le_of_succ_le hf1
                               rw [execMirLoop_succ, execMirLoop_succ, ctx.hcleanSrc, ctx.hcleanTgt]
                               dsimp only []
                               rw [ctx.hcleanStmts, execMirBlockBody_cons, execMirBlockBody_cons]
                               dsimp only [stepMirStmt]
                               rw [execMirBlockBody_cons]
                               rcases hha4 with
                                 ⟨hlen4, hother4, hinv_s4, hinv_t4, sa_s4, sa_t4, hsa_s4, hsa_t4,
                                  hflen4, hfother4, hfm_s4, hfm_t4⟩
                               have hha4_full : HeapAgreeExcept cert.alloc cert.field fm_v1 fm_t1
                                   (releaseProtectorHeap st_s1.nextCallId ha_s)
                                   (releaseProtectorHeap st_s1.nextCallId ha_t) :=
                                 ⟨hlen4, hother4, hinv_s4, hinv_t4, sa_s4, sa_t4, hsa_s4, hsa_t4,
                                  hflen4, hfother4, hfm_s4, hfm_t4⟩
                               have heval_lp : evalValOp (bindOptValReg st_s1.valRegs ctx.lpDst payload) ctx.valOp =
                                   .ok v1 := by
                                 rw [hvr1, evalValOp_bindOptValReg_unchanged payload ctx.hlpDisj]
                                 exact heval1
                               simp only [stepMirStmt, hsa_t4, hfm_t4, ← hvr1, ← hnt1, heval_lp]
                               rw [tbRootAccessField_write_noChildren hinv_t4 v1]
                               dsimp only []
                               obtain ⟨fs_t, hfs_t⟩ := setAt?_of_getAt? fm_v1 hfm_t4
                               obtain ⟨hr_t', hhs_t⟩ := setAt?_of_getAt? { sa_t4 with fields := fs_t } hsa_t4
                               rw [hfs_t]; dsimp only []
                               rw [hhs_t]; dsimp only []
                               have hha_sync : HeapAgreeExcept cert.alloc cert.field fm_v1 fm_v1
                                   (releaseProtectorHeap st_s1.nextCallId ha_s) hr_t' :=
                                 HeapAgreeExcept_set_target_right hha4_full (FieldNoChildrenInv_active v1)
                                   hsa_t4 hfs_t hhs_t
                               have hheap_eq : releaseProtectorHeap st_s1.nextCallId ha_s = hr_t' :=
                                 HeapAgreeExcept_eq_of_fm_eq hha_sync
                               rw [← hheap_eq]
                               have hcleanNoPtr := all_of_getAt? ctx.hnoptr ctx.hcleanSrc
                               rw [ctx.hcleanStmts] at hcleanNoPtr
                               simp only [List.all_cons, Bool.and_eq_true] at hcleanNoPtr
                               exact sink_exec_equal_block_body ctx .unwind env
                                 ⟨hpd1, fm_v1, by rw [← hheap_eq] at hha_sync; exact hha_sync⟩
                                 hcleanNoPtr.2
                                 (sink_not_clean_of_ne_sink ctx ctx.hcleanNeSink ctx.hcleanSrc)
                                 (all_of_getAt? (p := fun blk => termNoCleanSink cert.sinkBlock blk.term)
                                   ctx.hnoCleanSink ctx.hcleanSrc)
                                 (fun pc' st' hc1 hc2 hi =>
                                   sink_execMirLoop_bounded ctx .unwind env n f2 hf2 pc' st' hc1 hc2 hi))
    · rw [execMirLoop_succ, execMirLoop_succ, ctx.hotherTgt pc hpc hneClean]
      cases hblk : getAt? src.blocks pc with
      | none => exact refines_of_eq rfl
      | some blk =>
        dsimp only []
        have hblkNoPtr := all_of_getAt? ctx.hnoptr hblk
        exact sink_exec_equal_block_body ctx pm env hinv
          hblkNoPtr
          (sink_not_clean_of_ne_sink ctx hpc hblk)
          (all_of_getAt? (p := fun b => termNoCleanSink cert.sinkBlock b.term)
            ctx.hnoCleanSink hblk)
          (fun pc' st' hc1 hc2 hi =>
            sink_execMirLoop_bounded ctx pm env n f1 hf1 pc' st' hc1 hc2 hi)

/-! ### Core Theorems (Stage 1-2 Pre-Freeze Statement Surface) -/

/-- **Theorem 1 (`partial_sroa_refinement`):**
Any certified `PartialSroaCert` (either `.fullSplit` or `.sharedReadPromote`) preserves all
observable normal-return, unwind, abort, and fuel-bounded outcomes for EVERY `PanicMode`,
EVERY external callee environment `env`, EVERY scalar argument vector `initArgs`, and EVERY
`fuel`, introducing zero new Tree Borrows UB. -/
theorem partial_sroa_refinement
    (src tgt : MirBody) (cert : PartialSroaCert)
    (hcert : checkPartialSroaCert src tgt cert = true)
    (pm : PanicMode) (env : CalleeEnv) (initArgs : List UInt64) (fuel : Nat) :
    refines (execMir pm src env initArgs fuel) (execMir pm tgt env initArgs fuel) := by
  apply refines_of_eq
  simp only [checkPartialSroaCert, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcert
  rcases hcert with ⟨⟨⟨⟨⟨hfrz, hlen⟩, hno0⟩, hun⟩, hall⟩, htgt⟩
  subst htgt
  unfold execMir
  cases fuel with
  | zero => rfl
  | succ fuel' =>
    cases hb : src.blocks with
    | nil => simp [hb] at hlen
    | cons b0 rest =>
      have hb0 : getAt? src.blocks 0 = some b0 := by simp [hb, getAt?]
      have hun_b0 := all_of_getAt? hun hb0
      simp only [Bool.and_eq_true] at hun_b0
      have hall_b0 := all_of_getAt? hall hb0
      have hno0_b0 := any_eq_false_of_getAt? hno0 hb0
      have hfrz' : ∃ decl, getAt? src.allocDecls cert.alloc = some decl ∧
          getAt? decl.fieldUnsafeCell cert.field = some false := by
        unfold fieldIsFreeze at hfrz
        cases h1 : getAt? src.allocDecls cert.alloc with
        | none => simp [h1] at hfrz
        | some decl =>
          simp only [h1] at hfrz
          cases h2 : getAt? decl.fieldUnsafeCell cert.field with
          | none => simp [h2] at hfrz
          | some b =>
            cases b with
            | true => simp [h2] at hfrz
            | false => exact ⟨decl, rfl, h2⟩
      rcases hfrz' with ⟨decl, hdecl, hcell⟩
      have hsa0 : getAt? (initHeap src.allocDecls) cert.alloc =
          some { fields := decl.fieldUnsafeCell.map initFieldMeta } := by
        simp [initHeap, getAt?_map, hdecl]
      have hfm0 : getAt? ({ fields := decl.fieldUnsafeCell.map initFieldMeta } : StructAlloc).fields cert.field =
          some (initFieldMeta false) := by
        simp [getAt?_map, hcell]
      let st0 := initState src initArgs
      let st_t0 : ExecState := { st0 with valRegs := bindValReg st0.valRegs cert.ssaReg 0 }
      have hrel0 : SroaStateRel cert st0 st_t0 := by
        refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
        · intro x hne
          symm
          exact bindValReg_ne st0.valRegs 0 hne
        · cases cert.mode <;> dsimp only []
          · refine ⟨(fun _ _ h => nomatch h), initFieldMeta false, initFieldMeta false,
              HeapAgreeExcept_refl hsa0 hfm0 FieldNoChildrenInv_init, bindValReg_same _ _ _⟩
          · refine ⟨rfl, initFieldMeta false, ⟨SharedFieldInv_init, _, hsa0, hfm0⟩,
              bindValReg_same _ _ _⟩
      have hinit_eq : initState (applyPartialSroa src cert) initArgs = st0 := rfl
      simp only [execMirLoop, hinit_eq]
      have hget_t : getAt? (applyPartialSroa src cert).blocks 0 =
          some { stmts := .assignReg cert.ssaReg (.constU64 0) ::
                   rewriteStmtsForSroa cert.mode cert.alloc cert.field cert.ssaReg b0.stmts
               , term := b0.term } := by
        simp [applyPartialSroa, hb, getAt?]
      rw [hget_t, hb0]
      dsimp only [stepMirStmts, stepMirStmt, evalValOp]
      exact sroa_exec_block_continuation hrel0 hun_b0.1 hun_b0.2 hall_b0 hno0_b0
        (fun pc' hne' s1 t1 hr => sroa_execMirLoop_ne_zero hno0 hun hall pm env fuel' pc' s1 t1 hne' hr)

/-- **Theorem 2 (`store_sink_to_cleanup_refinement`):**
Any certified `StoreSinkToCleanupCert` preserves BOTH normal-return AND unwind-cleanup
observable states, I/O traces, and panic outcomes (under both `panic=unwind` and `panic=abort`)
for EVERY external callee environment `env`, EVERY `initArgs`, and EVERY `fuel`. -/
theorem store_sink_to_cleanup_refinement
    (src tgt : MirBody) (cert : StoreSinkToCleanupCert)
    (hcert : checkStoreSinkCert src tgt cert = true)
    (pm : PanicMode) (env : CalleeEnv) (initArgs : List UInt64) (fuel : Nat) :
    refines (execMir pm src env initArgs fuel) (execMir pm tgt env initArgs fuel) := by
  obtain ⟨ctx⟩ := unpackStoreSinkCert hcert
  have hfrz' : ∃ decl, getAt? src.allocDecls cert.alloc = some decl ∧
      getAt? decl.fieldUnsafeCell cert.field = some false := by
    have hf := ctx.hfrz
    unfold fieldIsFreeze at hf
    cases h1 : getAt? src.allocDecls cert.alloc with
    | none => simp [h1] at hf
    | some decl =>
      simp only [h1] at hf
      cases h2 : getAt? decl.fieldUnsafeCell cert.field with
      | none => simp [h2] at hf
      | some b =>
        cases b with
        | true => simp [h2] at hf
        | false => exact ⟨decl, rfl, h2⟩
  rcases hfrz' with ⟨decl, hdecl, hcell⟩
  have hsa0 : getAt? (initHeap src.allocDecls) cert.alloc =
      some { fields := decl.fieldUnsafeCell.map initFieldMeta } := by
    simp [initHeap, getAt?_map, hdecl]
  have hfm0 : getAt? ({ fields := decl.fieldUnsafeCell.map initFieldMeta } : StructAlloc).fields cert.field =
      some (initFieldMeta false) := by
    simp [getAt?_map, hcell]
  have hinit_eq : initState tgt initArgs = initState src initArgs := by
    simp [initState, ctx.hdecls]
  unfold execMir
  rw [hinit_eq]
  exact sink_execMirLoop_bounded ctx pm env fuel fuel (Nat.le_refl fuel) 0 (initState src initArgs)
    (Ne.symm ctx.hcleanNe0)
    (fun _ _ hp => by cases hp)
    ⟨(fun _ _ h => nomatch h), initFieldMeta false, HeapAgreeExcept_refl hsa0 hfm0 FieldNoChildrenInv_init⟩

/-- **Theorem 3 (`unwind_to_abort_subsumption`):**
Under `checkUnwindToAbortCert body cert = true` (`noCatchUnwind = true` and side-effect-free
cleanup pads), `panic=abort` refines `panic=unwind`:
1. Exact normal-return equivalence (same I/O trace and return value for every `fuel`).
2. Every `panic=unwind` unwind outcome `(tr, .unwound payload)` is subsumed by `panic=abort`
   terminating with the exact same trace and payload `(tr, .aborted payload)`.
3. Whenever `panic=abort` aborts with `(tr, .aborted payload)`, `panic=unwind` can NEVER recover
   a normal return for any `fuel'`, and any `panic=unwind` unwind outcome has the exact same
   observable I/O trace `tr` and `payload`.
4. `panic=abort` introduces zero new errors/UB (every `.error e` under `.abort` already occurs
   under `.unwind` at the same `fuel`). -/
theorem unwind_to_abort_subsumption
    (body : MirBody) (cert : UnwindToAbortCert)
    (hcert : checkUnwindToAbortCert body cert = true)
    (env : CalleeEnv) (initArgs : List UInt64) :
    (∀ fuel tr v,
      execMir .unwind body env initArgs fuel = .ok (tr, .ret v) ↔
      execMir .abort body env initArgs fuel = .ok (tr, .ret v)) ∧
    (∀ fuel tr payload,
      execMir .unwind body env initArgs fuel = .ok (tr, .unwound payload) →
      execMir .abort body env initArgs fuel = .ok (tr, .aborted payload)) ∧
    (∀ fuel tr payload,
      execMir .abort body env initArgs fuel = .ok (tr, .aborted payload) →
        (∀ fuel' tr' v, execMir .unwind body env initArgs fuel' ≠ .ok (tr', .ret v)) ∧
        (∀ fuel' tr' p', execMir .unwind body env initArgs fuel' = .ok (tr', .unwound p') →
          tr' = tr ∧ p' = payload)) ∧
    (∀ fuel e,
      execMir .abort body env initArgs fuel = .error e →
      execMir .unwind body env initArgs fuel = .error e) := by
  have hnc0 : cert.cleanupBlocks.contains 0 = false := by
    simp only [checkUnwindToAbortCert, Bool.and_eq_true, Bool.not_eq_true'] at hcert
    exact hcert.1.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fuel tr v
    exact (unwind_abort_same_fuel hcert env fuel 0 (initState body initArgs) hnc0 rfl).1 tr v
  · intro fuel tr payload
    exact (unwind_abort_same_fuel hcert env fuel 0 (initState body initArgs) hnc0 rfl).2.1 tr payload
  · intro fuel tr payload ha
    refine ⟨?_, ?_⟩
    · intro fuel' tr' v
      exact (abort_implies_unwind_subsumption hcert env fuel fuel' 0 (initState body initArgs)
        tr payload hnc0 rfl ha).1 tr' v
    · intro fuel' tr' p'
      exact (abort_implies_unwind_subsumption hcert env fuel fuel' 0 (initState body initArgs)
        tr payload hnc0 rfl ha).2 tr' p'
  · intro fuel e
    exact (unwind_abort_same_fuel hcert env fuel 0 (initState body initArgs) hnc0 rfl).2.2 e

/-! ### Positive Non-Vacuity Canaries (All Kernel-Checked by `rfl`) -/

/-- **Positive Canary 1A (`fullSplit`) & 1B (`sharedReadPromote` on Hybrid `Freeze` + `UnsafeCell`):**
- 1A: 2-field struct `{ f0: Freeze, f1: Freeze }`; `&mut s.f1` escapes to a potentially-unwinding
  callee that mutates `s.f1 := 50` (or unwinds `99`), while `s.f0` is `fullSplit`-promoted to SSA
  reg `10`. Both normal return (`10 + 50 = 60`) and unwind cleanup (`[.mirObs 10], .unwound 99`)
  match identically.
- 1B: Hybrid struct `{ f0: Freeze, f1: UnsafeCell }`; `&s` (`takeRootSharedRef`) is passed to a
  callee that reads `s.f0` AND legally mutates `s.f1 := 99` via `UnsafeCell`, while `s.f0` is
  `sharedReadPromote`-promoted to SSA reg `10` (`[.calleeRead 10], .ret 109`). -/
def canaryFullSplitSrc : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .writeField 0 1 (.constU64 20),
          .takeFieldPtr 0 0 1 .mutRef
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [
          .readField 0 0 0,
          .readField 1 0 1,
          .binOp 2 .add (.reg 0) (.reg 1)
        ]
      , term := .ret (.reg 2) },
      { stmts := [
          .landingPad none,
          .readField 3 0 0,
          .emitObs (.reg 3)
        ]
      , term := .resume }
    ] }

def canaryFullSplitCert : PartialSroaCert :=
  { mode := .fullSplit, alloc := 0, field := 0, ssaReg := 10 }

def canaryFullSplitEnvNormal : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 none 50], exit := .normal 0 } else none

def canaryFullSplitEnvPanic : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 none 50], exit := .panic 99 } else none

def canaryHybridSharedSrc : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, true] }] -- f0=Freeze, f1=UnsafeCell!
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .writeField 0 1 (.constU64 20),
          .takeRootSharedRef 0 0
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [
          .readField 0 0 0,
          .readField 1 0 1,
          .binOp 2 .add (.reg 0) (.reg 1)
        ]
      , term := .ret (.reg 2) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def canaryHybridSharedCert : PartialSroaCert :=
  { mode := .sharedReadPromote, alloc := 0, field := 0, ssaReg := 10 }

def canaryHybridSharedEnv : CalleeEnv := fun cid =>
  if cid == 0 then
    some { ops := [.readArg 0 (some 0) true, .writeArg 0 (some 1) 99], exit := .normal 0 }
  else none

theorem canary_partial_sroa_hybrid_struct_accepted :
    let tgtA := applyPartialSroa canaryFullSplitSrc canaryFullSplitCert
    let tgtB := applyPartialSroa canaryHybridSharedSrc canaryHybridSharedCert
    checkPartialSroaCert canaryFullSplitSrc tgtA canaryFullSplitCert = true ∧
    execMir .unwind canaryFullSplitSrc canaryFullSplitEnvNormal [] 10 = .ok ([], .ret 60) ∧
    execMir .unwind tgtA canaryFullSplitEnvNormal [] 10 = .ok ([], .ret 60) ∧
    execMir .unwind canaryFullSplitSrc canaryFullSplitEnvPanic [] 10 = .ok ([.mirObs 10], .unwound 99) ∧
    execMir .unwind tgtA canaryFullSplitEnvPanic [] 10 = .ok ([.mirObs 10], .unwound 99) ∧
    checkPartialSroaCert canaryHybridSharedSrc tgtB canaryHybridSharedCert = true ∧
    execMir .unwind canaryHybridSharedSrc canaryHybridSharedEnv [] 10 = .ok ([.calleeRead 10], .ret 109) ∧
    execMir .unwind tgtB canaryHybridSharedEnv [] 10 = .ok ([.calleeRead 10], .ret 109) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Positive Canary 2 (`canary_store_sink_to_cleanup_accepted`):**
Sinks `s.f0 = 10` past `p = &mut s.f1; call may_unwind(p)` into the unique cleanup pad `bb2`,
while sibling field `s.f1` is mutated by the callee! Both normal return (`20 + 7 = 27`) and unwind
cleanup observation (`[.mirObs 10], .unwound 55`) are preserved identically. -/
def canaryStoreSinkSrc : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, false] }]
  , blocks := [
      { stmts := [
          .writeField 0 1 (.constU64 5),
          .writeField 0 0 (.constU64 10),
          .takeFieldPtr 0 0 1 .mutRef
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [
          .writeField 0 0 (.constU64 20),
          .readField 0 0 0,
          .readField 1 0 1,
          .binOp 2 .add (.reg 0) (.reg 1)
        ]
      , term := .ret (.reg 2) },
      { stmts := [
          .landingPad none,
          .readField 3 0 0,
          .emitObs (.reg 3)
        ]
      , term := .resume }
    ] }

def canaryStoreSinkCert : StoreSinkToCleanupCert :=
  { sinkBlock := 0, storeIdx := 1, alloc := 0, field := 0 }

def canaryStoreSinkTgt : MirBody :=
  (applyStoreSink? canaryStoreSinkSrc canaryStoreSinkCert).getD canaryStoreSinkSrc

def canaryStoreSinkEnvNormal : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 none 7], exit := .normal 0 } else none

def canaryStoreSinkEnvPanic : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 none 7], exit := .panic 55 } else none

theorem canary_store_sink_to_cleanup_accepted :
    checkStoreSinkCert canaryStoreSinkSrc canaryStoreSinkTgt canaryStoreSinkCert = true ∧
    execMir .unwind canaryStoreSinkSrc canaryStoreSinkEnvNormal [] 10 = .ok ([], .ret 27) ∧
    execMir .unwind canaryStoreSinkTgt canaryStoreSinkEnvNormal [] 10 = .ok ([], .ret 27) ∧
    execMir .unwind canaryStoreSinkSrc canaryStoreSinkEnvPanic [] 10 = .ok ([.mirObs 10], .unwound 55) ∧
    execMir .unwind canaryStoreSinkTgt canaryStoreSinkEnvPanic [] 10 = .ok ([.mirObs 10], .unwound 55) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Positive Canary 3 (`canary_unwind_to_abort_subsumption_accepted`):**
Pure local drop cleanup (`s.f0 = 0; resume`, no `CatchUnwind`, no `EmitObs` in cleanup) passes
`checkUnwindToAbortCert = true` and agrees on both normal return and panic trace/payload. -/
def canaryUnwindSubBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .emitObs (.constU64 1)
        ]
      , term := .callMayUnwind 0 [] none 1 2 },
      { stmts := [.readField 0 0 0], term := .ret (.reg 0) },
      { stmts := [.landingPad none, .writeField 0 0 (.constU64 0)], term := .resume }
    ] }

def canaryUnwindSubCert : UnwindToAbortCert :=
  { noCatchUnwind := true, cleanupBlocks := [2] }

def canaryPanicEnv : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [], exit := .panic 77 } else none

def canaryNormalEnv : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [], exit := .normal 0 } else none

theorem canary_unwind_to_abort_subsumption_accepted :
    checkUnwindToAbortCert canaryUnwindSubBody canaryUnwindSubCert = true ∧
    execMir .unwind canaryUnwindSubBody canaryNormalEnv [] 10 = .ok ([.mirObs 1], .ret 10) ∧
    execMir .abort  canaryUnwindSubBody canaryNormalEnv [] 10 = .ok ([.mirObs 1], .ret 10) ∧
    execMir .unwind canaryUnwindSubBody canaryPanicEnv  [] 10 = .ok ([.mirObs 1], .unwound 77) ∧
    execMir .abort  canaryUnwindSubBody canaryPanicEnv  [] 10 = .ok ([.mirObs 1], .aborted 77) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Mandatory Sharpness Counterexamples (All Kernel-Checked, Zero `sorry`) -/

/-- **Counterexample 1 (`ce_root_raw_ptr_breaks_partial_sroa`):**
Taking `&raw mut s` (`takeRootRawPtr`, setting `rootAddressTaken = true`) then shifting to field `1`
still retains `wholeStruct` provenance, allowing `container_of!` pointer arithmetic inside the
callee to legally mutate sibling `s.f0 := 99` (zero UB!). Naive PartialSROA (both `.fullSplit` and
`.sharedReadPromote`, ignoring `rootAddressTaken`) returns stale `10` instead of `99`, and
`checkPartialSroaCert` rejects EVERY `(mode, ssaReg, tgt)` targeting `(0, 0)`. -/
def rootRawPtrBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .writeField 0 1 (.constU64 20),
          .takeRootRawPtr 0 0,
          .ptrOffset 1 0 1
        ]
      , term := .callMayUnwind 0 [1] none 1 2 },
      { stmts := [.readField 0 0 0], term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def containerOfMutateF0Env : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 (some 0) 99], exit := .normal 0 } else none

def badSroaFullCert : PartialSroaCert :=
  { mode := .fullSplit, alloc := 0, field := 0, ssaReg := 10 }

def badSroaSharedCert : PartialSroaCert :=
  { mode := .sharedReadPromote, alloc := 0, field := 0, ssaReg := 10 }

theorem ce_root_raw_ptr_breaks_partial_sroa :
    let naiveFull   := applyPartialSroa rootRawPtrBody badSroaFullCert
    let naiveShared := applyPartialSroa rootRawPtrBody badSroaSharedCert
    execMir .unwind rootRawPtrBody containerOfMutateF0Env [] 10 = .ok ([], .ret 99) ∧
    execMir .unwind naiveFull      containerOfMutateF0Env [] 10 = .ok ([], .ret 10) ∧
    execMir .unwind naiveShared    containerOfMutateF0Env [] 10 = .ok ([], .ret 10) ∧
    ¬ refines (execMir .unwind rootRawPtrBody containerOfMutateF0Env [] 10)
              (execMir .unwind naiveFull      containerOfMutateF0Env [] 10) ∧
    ¬ refines (execMir .unwind rootRawPtrBody containerOfMutateF0Env [] 10)
              (execMir .unwind naiveShared    containerOfMutateF0Env [] 10) ∧
    (∀ mode ssaReg tgt,
      checkPartialSroaCert rootRawPtrBody tgt
        { mode := mode, alloc := 0, field := 0, ssaReg := ssaReg } = false) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro mode ssaReg tgt
    cases mode <;> simp [checkPartialSroaCert, rootRawPtrBody, fieldIsFreeze, getAt?,
      hasPredecessor, termTargets, stmtAllowedForSroa]

/-- **Counterexample 2 (`ce_unsafecell_breaks_partial_sroa`):**
An `UnsafeCell` (`isUnsafeCell = true`) field shared via `&T` (`takeFieldPtr ... .shared`, with
`!rootAddressTaken` and zero `&mut`/`*mut` borrows) gets `Reserved` non-Freeze permission and can
be legally mutated by a callee (`99`, zero UB!), breaking naive scalar promotion (`10 ≠ 99`).
Flipping `isUnsafeCell` to `false` on the exact same program causes the callee write to fault with
`.error .tbUb` (so certified `.sharedReadPromote` IS sound on the `Freeze` twin!). -/
def unsafeCellSharedBody (cellFlag : Bool) : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [cellFlag, false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .takeFieldPtr 0 0 0 .shared
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [.readField 0 0 0], term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def mutateArg0Env : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.writeArg 0 none 99], exit := .normal 0 } else none

theorem ce_unsafecell_breaks_partial_sroa :
    let srcCell   := unsafeCellSharedBody true
    let naiveCell := applyPartialSroa srcCell badSroaSharedCert
    let srcFreeze := unsafeCellSharedBody false
    let tgtFreeze := applyPartialSroa srcFreeze badSroaSharedCert
    execMir .unwind srcCell   mutateArg0Env [] 10 = .ok ([], .ret 99) ∧
    execMir .unwind naiveCell mutateArg0Env [] 10 = .ok ([], .ret 10) ∧
    ¬ refines (execMir .unwind srcCell   mutateArg0Env [] 10)
              (execMir .unwind naiveCell mutateArg0Env [] 10) ∧
    (∀ mode ssaReg tgt,
      checkPartialSroaCert srcCell tgt
        { mode := mode, alloc := 0, field := 0, ssaReg := ssaReg } = false) ∧
    -- Freeze twin contrast: `!isUnsafeCell` turns the callee write into Tree Borrows UB!
    checkPartialSroaCert srcFreeze tgtFreeze badSroaSharedCert = true ∧
    execMir .unwind srcFreeze mutateArg0Env [] 10 = .error .tbUb := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩
  · intro h
    cases h
  · intro mode ssaReg tgt
    simp [checkPartialSroaCert, unsafeCellSharedBody, fieldIsFreeze, getAt?]

/-- **Counterexample 3 (`ce_unsound_store_sink_observed_by_callee`):**
Sinking `s.f0 = 10` past `p = &s.f0; call callee(p)` into the cleanup pad changes the value
observed by `callee(p)` from `10` (`[.calleeRead 10]`) to `0` (`[.calleeRead 0]`), with zero UB
in either execution! `checkStoreSinkCert` unconditionally rejects every sink cert targeting `(0, 0)`. -/
def observedStoreBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .takeFieldPtr 0 0 0 .shared
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [.writeField 0 0 (.constU64 20)], term := .ret (.constU64 20) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def observeArg0Env : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [.readArg 0 none true], exit := .normal 0 } else none

def badStoreSinkCert : StoreSinkToCleanupCert :=
  { sinkBlock := 0, storeIdx := 0, alloc := 0, field := 0 }

def naiveSunkObservedTgt : MirBody :=
  (applyStoreSink? observedStoreBody badStoreSinkCert).getD observedStoreBody

theorem ce_unsound_store_sink_observed_by_callee :
    execMir .unwind observedStoreBody    observeArg0Env [] 10 = .ok ([.calleeRead 10], .ret 20) ∧
    execMir .unwind naiveSunkObservedTgt observeArg0Env [] 10 = .ok ([.calleeRead 0],  .ret 20) ∧
    ¬ refines (execMir .unwind observedStoreBody    observeArg0Env [] 10)
              (execMir .unwind naiveSunkObservedTgt observeArg0Env [] 10) ∧
    (∀ sinkBlock storeIdx tgt,
      checkStoreSinkCert observedStoreBody tgt
        { sinkBlock := sinkBlock, storeIdx := storeIdx, alloc := 0, field := 0 } = false) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro sinkBlock storeIdx tgt
    rfl

/-- **Counterexample 4 (`ce_catch_unwind_breaks_abort_subsumption`):**
When `CatchUnwind` is present (`noCatchUnwind = false`), `panic=unwind` catches the panic payload
`777` and recovers a normal return `.ret 777`, whereas `panic=abort` terminates immediately with
`.aborted 777` — refuting unconditional `L7_` unwind-to-abort subsumption! `checkUnwindToAbortCert`
unconditionally rejects `catchUnwindBody` for EVERY `cert`. -/
def catchUnwindBody : MirBody :=
  { allocDecls := []
  , blocks := [
      { stmts := [], term := .callMayUnwind 0 [] none 1 2 },
      { stmts := [], term := .ret (.constU64 1) },
      { stmts := [.landingPad (some 0)], term := .catchUnwind (some 1) 3 },
      { stmts := [], term := .ret (.reg 1) }
    ] }

def panic777Env : CalleeEnv := fun cid =>
  if cid == 0 then some { ops := [], exit := .panic 777 } else none

theorem ce_catch_unwind_breaks_abort_subsumption :
    execMir .unwind catchUnwindBody panic777Env [] 10 = .ok ([], .ret 777) ∧
    execMir .abort  catchUnwindBody panic777Env [] 10 = .ok ([], .aborted 777) ∧
    (∀ cert, checkUnwindToAbortCert catchUnwindBody cert = false) := by
  refine ⟨rfl, rfl, ?_⟩
  intro cert
  have hr : List.range catchUnwindBody.blocks.length = [0, 1, 2, 3] := rfl
  unfold checkUnwindToAbortCert
  rw [hr]
  dsimp only [List.all_cons, List.all_nil, catchUnwindBody, getAt?]
  cases hnc : cert.noCatchUnwind
  · rfl
  · cases h0 : cert.cleanupBlocks.contains 0
    · cases h1 : cert.cleanupBlocks.contains 1
      · cases h2 : cert.cleanupBlocks.contains 2
        · rfl
        · cases h3 : cert.cleanupBlocks.contains 3 <;> rfl
      · rfl
    · rfl

/-- **Bonus Counterexample 5 (`ce_observable_cleanup_breaks_abort_subsumption`):**
Even with ZERO `CatchUnwind` in the program, an observable external side effect (`emitObs 999`)
inside a cleanup pad causes `panic=unwind` to emit `[.mirObs 999]` before unwinding while
`panic=abort` emits `[]` before aborting — proving the side-effect-free cleanup condition is also
strictly necessary! -/
def obsCleanupBody : MirBody :=
  { allocDecls := []
  , blocks := [
      { stmts := [], term := .callMayUnwind 0 [] none 1 2 },
      { stmts := [], term := .ret (.constU64 1) },
      { stmts := [.landingPad none, .emitObs (.constU64 999)], term := .resume }
    ] }

theorem ce_observable_cleanup_breaks_abort_subsumption :
    execMir .unwind obsCleanupBody panic777Env [] 10 = .ok ([.mirObs 999], .unwound 777) ∧
    execMir .abort  obsCleanupBody panic777Env [] 10 = .ok ([], .aborted 777) ∧
    (∀ cert, checkUnwindToAbortCert obsCleanupBody cert = false) := by
  refine ⟨rfl, rfl, ?_⟩
  intro cert
  have hr : List.range obsCleanupBody.blocks.length = [0, 1, 2] := rfl
  unfold checkUnwindToAbortCert
  rw [hr]
  dsimp only [List.all_cons, List.all_nil, obsCleanupBody, getAt?]
  cases hnc : cert.noCatchUnwind
  · rfl
  · cases h0 : cert.cleanupBlocks.contains 0
    · cases h1 : cert.cleanupBlocks.contains 1
      · cases h2 : cert.cleanupBlocks.contains 2 <;> rfl
      · rfl
    · rfl

/-- **Bonus Tree Borrows Semantics Witness (`ce_tb_protector_and_subplace_ub`):**
Verifies directly by `rfl` that our operational semantics enforces:
1. Tree Borrows protector UB: passing two `&mut` borrows of `s.f0` to a callee that writes through
   one triggers `.error .tbUb` (foreign write against protected `Reserved` sibling tag).
2. Sub-place `outside_perm (accessed = false)` provenance UB: offsetting a `TakeFieldPtr s 1`
   pointer to sibling `s.f0` and writing triggers `.error .tbUb` (contrasting with `TakeRootRawPtr`
   in Counterexample 1, which succeeds!). -/
def tbAliasedMutProtectorBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false] }]
  , blocks := [
      { stmts := [
          .takeFieldPtr 0 0 0 .mutRef,
          .takeFieldPtr 1 0 0 .mutRef
        ]
      , term := .callMayUnwind 0 [0, 1] none 1 2 },
      { stmts := [], term := .ret (.constU64 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def subplaceEscapeAttemptBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, false] }]
  , blocks := [
      { stmts := [
          .takeFieldPtr 0 0 1 .rawMut
        ]
      , term := .callMayUnwind 0 [0] none 1 2 },
      { stmts := [.readField 0 0 0], term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

theorem ce_tb_protector_and_subplace_ub :
    execMir .unwind tbAliasedMutProtectorBody mutateArg0Env [] 10 = .error .tbUb ∧
    execMir .unwind subplaceEscapeAttemptBody containerOfMutateF0Env [] 10 = .error .tbUb :=
  ⟨rfl, rfl⟩

/-! ### Stage 2 Tree Borrows Faithfulness Regression Witnesses (`B1`–`B4`) -/

/-- **`B1` Positive Canary (Aliased `&s` + Two-Call Hybrid `{Freeze, UnsafeCell}` Struct):**
Verifies that `TbPerm.cell` avoids false `.tbUb` when:
1. Two aliased `&s` references mutate and read an `UnsafeCell` field inside one call; AND
2. A single `&s` on a hybrid `{ f0: Freeze, f1: UnsafeCell }` struct is passed across TWO
   sequential calls with an intervening caller read of `s.f1`, while `PartialSroaCert`
   `.sharedReadPromote` legally promotes `s.f0` into SSA reg `10` with matching `.ok` outcomes! -/
def aliasedSharedCellBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, true] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .takeRootSharedRef 0 0,
          .takeRootSharedRef 1 0
        ]
      , term := .callMayUnwind 0 [0, 1] none 1 2 },
      { stmts := [.readField 0 0 1], term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def aliasedSharedCellEnv : CalleeEnv
  | 0 => some { ops := [.writeArg 0 (some 1) 30, .readArg 1 (some 1) true], exit := .normal 0 }
  | _ => none

def twoCallHybridSrc : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, true] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .takeRootSharedRef 0 0
        ]
      , term := .callMayUnwind 0 [0] none 1 3 },
      { stmts := [.readField 2 0 1]
      , term := .callMayUnwind 0 [0] none 2 3 },
      { stmts := [
          .readField 0 0 0,
          .readField 1 0 1,
          .binOp 3 .add (.reg 0) (.reg 1)
        ]
      , term := .ret (.reg 3) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def twoCallHybridCert : PartialSroaCert :=
  { alloc := 0, field := 0, ssaReg := 10, mode := .sharedReadPromote }

theorem canary_b1_cell_aliased_and_two_call_hybrid_ok :
    execMir .unwind aliasedSharedCellBody aliasedSharedCellEnv [] 10 =
      .ok ([.calleeRead 30], .ret 30) ∧
    checkPartialSroaCert twoCallHybridSrc (applyPartialSroa twoCallHybridSrc twoCallHybridCert)
      twoCallHybridCert = true ∧
    execMir .unwind twoCallHybridSrc canaryHybridSharedEnv [] 10 =
      .ok ([.calleeRead 10, .calleeRead 10], .ret 109) ∧
    execMir .unwind (applyPartialSroa twoCallHybridSrc twoCallHybridCert)
      canaryHybridSharedEnv [] 10 =
      .ok ([.calleeRead 10, .calleeRead 10], .ret 109) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`B2`–`B4` Tree Borrows Faithfulness Witnesses:**
1. **`B2` (`ReservedFrz` protector UB on `&mut UnsafeCell<T>`):** Two aliased protected `&mut`
   borrows of an `UnsafeCell` field where the callee reads through arg 1 and writes through arg 0
   MUST trigger `.error .tbUb` (matching Miri `reservedim_spurious_write.rs`).
2. **`B3` (Post-protector-release `&mut` activation):** A `conflicted = true` `&mut` witness
   from a read-only call MUST succeed when written *after* that call returns and releases its
   protector (matching Miri `child_write` checking `if protected`).
3. **`B4` (`activateProtectorOne` `ptrInScope` check):** Passing an out-of-scope offset
   `.fieldOnly 1` `&mut` reference to `callMayUnwind` triggers immediate `.error .tbUb`. -/
def aliasedMutUnsafeCellBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [true] }]
  , blocks := [
      { stmts := [
          .takeFieldPtr 0 0 0 .mutRef,
          .takeFieldPtr 1 0 0 .mutRef
        ]
      , term := .callMayUnwind 0 [0, 1] none 1 2 },
      { stmts := [.readField 0 0 0], term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def readArg1WriteArg0Env : CalleeEnv
  | 0 => some { ops := [.readArg 1 none true, .writeArg 0 none 99], exit := .normal 0 }
  | _ => none

def conflictedAfterReleaseBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false] }]
  , blocks := [
      { stmts := [
          .writeField 0 0 (.constU64 10),
          .takeFieldPtr 0 0 0 .mutRef,
          .takeFieldPtr 1 0 0 .shared
        ]
      , term := .callMayUnwind 0 [0, 1] none 1 2 },
      { stmts := [
          .writePtr 0 (.constU64 42),
          .readField 0 0 0
        ]
      , term := .ret (.reg 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def readArg1OnlyEnv : CalleeEnv
  | 0 => some { ops := [.readArg 1 none true], exit := .normal 0 }
  | _ => none

def outOfScopeMutArgBody : MirBody :=
  { allocDecls := [{ fieldUnsafeCell := [false, false] }]
  , blocks := [
      { stmts := [
          .takeFieldPtr 0 0 1 .mutRef,
          .ptrOffset 1 0 0
        ]
      , term := .callMayUnwind 0 [1] none 1 2 },
      { stmts := [], term := .ret (.constU64 0) },
      { stmts := [.landingPad none], term := .resume }
    ] }

def noopCalleeEnv : CalleeEnv
  | 0 => some { ops := [], exit := .normal 0 }
  | _ => none

theorem ce_b2_b3_b4_tree_borrows_faithfulness :
    execMir .unwind aliasedMutUnsafeCellBody readArg1WriteArg0Env [] 10 = .error .tbUb ∧
    execMir .unwind conflictedAfterReleaseBody readArg1OnlyEnv [] 10 =
      .ok ([.calleeRead 10], .ret 42) ∧
    execMir .unwind outOfScopeMutArgBody noopCalleeEnv [] 10 = .error .tbUb :=
  ⟨rfl, rfl, rfl⟩

end VrustcFormal.F1_2
