/-!
# Open-World Vtable-Guarded Indirect-Call Promotion & Canonical MIR PGO Verification

Self-contained Lean 4 (`v4.34.1`) mechanization of:
1. **Canonical MIR Profile Keys vs. CGU-Prefixed LLVM IRPGO Keys:**
   Proves `CanonicalMirKey` (`StableCrateId × DefPathHash × GenericArgs × CallsiteOrd`)
   is invariant across codegen-unit (`-C codegen-units=N`) partitioning, symbol
   internalization, and LTO mode switches (`off`/`thin`/`fat`), whereas LLVM's
   `getIRPGOFuncName` (`[<cgu>;]<mangled>`) misses profile lookup under CGU or
   internal-to-external linkage changes.
2. **Tree Borrows Receiver Permissions, Wide-Pointer Metadata Reads, and Unwind Domains:**
   Models the 6-state Tree Borrows per-location transition relation (`Cell`,
   `ReservedFrz (conflicted : Bool)`, `ReservedIM`, `Unique`, `Frozen`, `Disabled`),
   `FnEntry` retagging (`&self`, `&mut self`, and `!Unpin` retag elision), wide-pointer
   vtable extraction (`0` heap/Tree Borrows effects), and `panic_unwind` `CanaryDomain`
   unwinding (`unwoundCaught` vs. `foreignExceptionAbort` across `cdylib` vs. `dylib`).
3. **Unconditional Soundness of Value-Guarded ICP & Function-Pointer-Guarded ICP:**
   Proves that single-target value-guarded ICP (`if vptr == &VTABLE_K then direct_K else indirect`),
   K-target guarded cascades, and function-pointer-guarded ICP are 100% observationally
   equivalent to unoptimized `dyn Trait` indirect calls across **all** stale/adversarial PGO
   profiles, **all** open-world `dlopen` DSO duplicate-vtable extensions, **all** Tree Borrows
   receiver states, and **all** normal/unwind outcomes.
4. **Sharp Multi-Vtable Coalescing Boundary (`dylib` vs. `cdylib` `CANARY`) & 4 Counterexamples:**
   Proves two-vtable single-body coalescing (`if vptr == vt₁ || vptr == vt₂ then direct_m₁`)
   is sound when `m₁` and `m₂` share identical semantics and `CanaryDomain` (multi-CGU,
   multi-`rlib`, or `-C prefer-dynamic` `dylib`), and refutes it with a kernel-checked
   counterexample across split-`libstd` `--crate-type=cdylib` boundaries. Also kernel-checks
   four negative unsoundness theorems for unguarded stale-PGO devirtualization, closed-world
   `else unreachable`, closed-world 2-impl peeled devirtualization, and negative vtable-inequality
   alias/DSE pruning (`vptr ≠ vt_host ⊢ DynType ≠ T`).

Hygiene: `0` `sorry`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `@[extern]`,
`0` `axiom`, `0` `Classical.choice`, and `0` `namespace Trusted` declarations.
-/

namespace VrustcPkg.VtableGuardedIcpPgo

/-! ## 1. Canonical MIR Profile Keys vs. CGU-Partitioned LLVM IRPGO Keys -/

/-- LTO compilation mode (`-C lto={off,thin,fat}`). -/
inductive LtoMode where
  | off
  | thin
  | fat
  deriving DecidableEq, Repr, Inhabited

/-- Symbol linkage assigned by `rustc_monomorphize::partitioning` (`internalize_symbols`). -/
inductive SymbolLinkage where
  | internalLocal
  | externalShared
  deriving DecidableEq, Repr, Inhabited

/-- Source-level / post-cleanup MIR item and callsite coordinate, prior to CGU partitioning. -/
structure MirCallsiteCoord where
  stableCrateId : Nat
  defPathHash : Nat
  canonicalGenericArgs : List Nat
  callsiteOrdinal : Nat
  mangledSymbol : String
  deriving DecidableEq, Repr, Inhabited

/-- Canonical MIR profile key: depends solely on DefPath, canonical GenericArgs, and MIR ordinal. -/
structure CanonicalMirKey where
  stableCrateId : Nat
  defPathHash : Nat
  canonicalGenericArgs : List Nat
  callsiteOrdinal : Nat
  deriving DecidableEq, Repr, Inhabited

/-- CGU partitioning configuration produced by `rustc_monomorphize::partitioning`. -/
structure CguView where
  crateCguPrefix : String
  cguIndex : Nat
  assignedLinkage : SymbolLinkage
  ltoMode : LtoMode
  deriving DecidableEq, Repr, Inhabited

/-- Canonical MIR key extraction ignores CGU assignment, internalization, and LTO mode. -/
def canonicalMirKeyOf (coord : MirCallsiteCoord) (_view : CguView) : CanonicalMirKey :=
  { stableCrateId := coord.stableCrateId
  , defPathHash := coord.defPathHash
  , canonicalGenericArgs := coord.canonicalGenericArgs
  , callsiteOrdinal := coord.callsiteOrdinal }

/-- Models `llvm::getIRPGOFuncName` (`llvm/lib/ProfileData/InstrProf.cpp:391-412`):
in non-LTO builds, local-linkage symbols are prefixed with `<cgu_source_file>;`. -/
def llvmIrPgoFuncName (coord : MirCallsiteCoord) (view : CguView) : String :=
  let inLto := match view.ltoMode with
    | .off => false
    | .thin | .fat => true
  if !inLto && view.assignedLinkage == .internalLocal then
    view.crateCguPrefix ++ "-cgu." ++ toString view.cguIndex ++ ";" ++ coord.mangledSymbol
  else
    coord.mangledSymbol

/-- Canonical MIR profile lookup over an association-list profile store. -/
def lookupMirProfile {α : Type} (store : List (CanonicalMirKey × α)) (k : CanonicalMirKey) : Option α :=
  match store with
  | [] => none
  | (k', v) :: rest => if k == k' then some v else lookupMirProfile rest k

/-- LLVM IRPGO profile lookup keyed by `getIRPGOFuncName`. -/
def lookupIrPgoProfile {α : Type} (store : List (String × α)) (name : String) : Option α :=
  match store with
  | [] => none
  | (n', v) :: rest => if name == n' then some v else lookupIrPgoProfile rest name

/-- Canonical MIR keys are 100% invariant across arbitrary CGU counts, linkage flips, and LTO modes. -/
theorem canonicalMirKey_invariant
    (coord : MirCallsiteCoord) (v₁ v₂ : CguView) :
    canonicalMirKeyOf coord v₁ = canonicalMirKeyOf coord v₂ :=
  rfl

/-- Canonical MIR profile lookup returns identical hints across any CGU/LTO switch. -/
theorem lookupMirProfile_invariant
    {α : Type} (store : List (CanonicalMirKey × α))
    (coord : MirCallsiteCoord) (vTrain vUse : CguView) :
    lookupMirProfile store (canonicalMirKeyOf coord vUse) =
      lookupMirProfile store (canonicalMirKeyOf coord vTrain) :=
  rfl

/-- Concrete counterexample: training with `-C codegen-units=4 -C lto=off` records an
internalized symbol under `pgo_app-cgu.2;...`, which misses lookup under `-C codegen-units=1`
(`pgo_app-cgu.0;...`) and under `-C lto=fat` (unprefixed), while `lookupMirProfile` succeeds. -/
theorem cex_llvmIrPgo_breaks_across_cgu_and_lto :
    let coord : MirCallsiteCoord :=
      { stableCrateId := 0x71a2, defPathHash := 0x99b1
      , canonicalGenericArgs := [64], callsiteOrdinal := 0
      , mangledSymbol := "_RNvNtCs71a2_7pgo_app12worker_local11private_mix" }
    let vTrainCgu4 : CguView :=
      { crateCguPrefix := "pgo_app", cguIndex := 2
      , assignedLinkage := .internalLocal, ltoMode := .off }
    let vUseCgu1 : CguView :=
      { crateCguPrefix := "pgo_app", cguIndex := 0
      , assignedLinkage := .internalLocal, ltoMode := .off }
    let vUseFatLto : CguView :=
      { crateCguPrefix := "pgo_app", cguIndex := 0
      , assignedLinkage := .externalShared, ltoMode := .fat }
    let irStore := [(llvmIrPgoFuncName coord vTrainCgu4, (38000 : Nat))]
    let mirStore := [(canonicalMirKeyOf coord vTrainCgu4, (38000 : Nat))]
    lookupIrPgoProfile irStore (llvmIrPgoFuncName coord vTrainCgu4) = some 38000 ∧
    lookupIrPgoProfile irStore (llvmIrPgoFuncName coord vUseCgu1) = none ∧
    lookupIrPgoProfile irStore (llvmIrPgoFuncName coord vUseFatLto) = none ∧
    lookupMirProfile mirStore (canonicalMirKeyOf coord vUseCgu1) = some 38000 ∧
    lookupMirProfile mirStore (canonicalMirKeyOf coord vUseFatLto) = some 38000 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Tree Borrows Receiver Permission Machine & `FnEntry` Retagging -/

/-- Per-location Tree Borrows permission states (`Miri/TreeBorrows/Permissions.lean:19-32`,
Villani et al. PLDI 2025, DOI `10.1145/3735592`). -/
inductive TbPerm where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled
  deriving DecidableEq, Repr, Inhabited

inductive TbAccessKind where
  | read
  | write
  deriving DecidableEq, Repr, Inhabited

inductive TbRel where
  | localChild
  | foreignOther
  deriving DecidableEq, Repr, Inhabited

inductive TbStepResult where
  | step (next : TbPerm)
  | ub
  | impossibleProtectedReservedIM
  deriving DecidableEq, Repr, Inhabited

def tbChildRead (p : TbPerm) : TbStepResult :=
  match p with
  | .disabled => .ub
  | readable => .step readable

def tbForeignRead (p : TbPerm) (isProtected : Bool) : TbStepResult :=
  match p with
  | .cell => .step .cell
  | .frozen => .step .frozen
  | .disabled => .step .disabled
  | .reservedFrz _ =>
      if isProtected then .step (.reservedFrz true) else .step p
  | .reservedIM =>
      if isProtected then .impossibleProtectedReservedIM else .step .reservedIM
  | .unique =>
      if isProtected then .step .disabled else .step .frozen

def tbChildWrite (p : TbPerm) (isProtected : Bool) : TbStepResult :=
  match p with
  | .cell => .step .cell
  | .reservedFrz true =>
      if isProtected then .ub else .step .unique
  | .reservedFrz false => .step .unique
  | .reservedIM => .step .unique
  | .unique => .step .unique
  | .frozen => .ub
  | .disabled => .ub

def tbForeignWrite (p : TbPerm) (isProtected : Bool) : TbStepResult :=
  match p with
  | .cell => .step .cell
  | .reservedIM =>
      if isProtected then .impossibleProtectedReservedIM else .step .reservedIM
  | _ => .step .disabled

/-- Exact 4-way Tree Borrows transition dispatcher (`Permissions.lean:105-112`). -/
def performTbAccess (kind : TbAccessKind) (rel : TbRel) (old : TbPerm) (isProtected : Bool) :
    TbStepResult :=
  match kind, rel with
  | .write, .foreignOther => tbForeignWrite old isProtected
  | .read, .foreignOther => tbForeignRead old isProtected
  | .write, .localChild => tbChildWrite old isProtected
  | .read, .localChild => tbChildRead old

/-- Receiver reference kind at a `dyn Trait` method callsite. -/
inductive ReceiverKind where
  | sharedRef
  | mutRef
  deriving DecidableEq, Repr, Inhabited

/-- Type layout facts governing `FnEntry` retagging (`RetagPolicy.lean:28-32, 68-92`). -/
structure TypeFacts where
  isFreeze : Bool
  isUnpin : Bool
  isUnsafeUnpin : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Callee `FnEntry` retag policy (`RetagPolicy.lean:68-92` with `implicitWrites = false`):
- Shared `&T` retags with `StrongProtector` (`true`) to `.frozen` if `isFreeze` else `.cell`
  (performing an associated `childRead` check first so `.disabled` faults immediately).
- Mutable `&mut T` checks `tyIsUnpin := isUnpin && isUnsafeUnpin`:
  - If `!tyIsUnpin` (`!Unpin` pinned self-referential receiver), retagging is **skipped**,
    retaining `(callerPerm, false)`.
  - If `tyIsUnpin`, performs a `childRead` check and creates `(.reservedFrz false, true)`
    under a function-entry `StrongProtector`. -/
def fnEntryRetag (facts : TypeFacts) (rk : ReceiverKind) (callerPerm : TbPerm) :
    Option (TbPerm × Bool) :=
  match rk with
  | .sharedRef =>
      match tbChildRead callerPerm with
      | .step _ => some (if facts.isFreeze then .frozen else .cell, true)
      | _ => none
  | .mutRef =>
      let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin
      if !tyIsUnpin then
        some (callerPerm, false)
      else
        match tbChildRead callerPerm with
        | .step _ => some (.reservedFrz false, true)
        | _ => none

/-! ## 3. Open-World Multi-DSO Environment, Heap, Vtables, and Unwind Semantics -/

abbrev TypeId := Nat
abbrev TraitId := Nat
abbrev MethodId := Nat
abbrev AllocId := Nat
/-- Identifies the `libstd` `panic_unwind` `static CANARY: u8` instance (`gcc.rs:48,97`). -/
abbrev CanaryDomain := Nat

/-- Physical vtable address `(dsoId, localVtableSlot)`. Two DSOs or two CGUs may allocate
distinct `VtablePtr` values for the exact same `(TypeId, TraitId)`. -/
structure VtablePtr where
  dsoId : Nat
  slotId : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Wide reference `(data_alloc, vtable_ptr)`. -/
structure WidePtr where
  alloc : AllocId
  vptr : VtablePtr
  deriving DecidableEq, Repr, Inhabited

/-- Heap allocation cell with dynamic type, word payload, and active Tree Borrows permission. -/
structure AllocCell where
  dynTy : TypeId
  sizeWords : Nat
  word0 : Int
  word1 : Int
  facts : TypeFacts
  perm : TbPerm
  deriving DecidableEq, Repr, Inhabited

/-- Total structural association-list lookup (reduces definitionally in the Lean kernel). -/
def assocLookup {α β : Type} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k', v) :: rest, k => if k == k' then some v else assocLookup rest k

def assocSet {α β : Type} [BEq α] : List (α × β) → α → β → List (α × β)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k == k' then (k, v) :: rest else (k', v') :: assocSet rest k v

/-- Program heap plus an observable global side-effect register (for alias/DSE witnesses). -/
structure HeapState where
  cells : List (AllocId × AllocCell)
  globalSideEffect : Int
  deriving DecidableEq, Repr, Inhabited

def HeapState.getCell (h : HeapState) (a : AllocId) : Option AllocCell :=
  assocLookup h.cells a

def HeapState.setCell (h : HeapState) (a : AllocId) (c : AllocCell) : HeapState :=
  { h with cells := assocSet h.cells a c }

/-- Read-only vtable metadata & method-pointer descriptor (`rustc_middle/src/ty/vtable.rs:13-26`). -/
structure VtableDesc where
  concreteTy : TypeId
  traitId : TraitId
  sizeWords : Nat
  facts : TypeFacts
  methodImpl : MethodId
  deriving DecidableEq, Repr, Inhabited

/-- Atomic operations inside a monomorphized trait method body. -/
inductive MethodOp where
  | readWord0AddToAcc
  | readWord1AddToAcc
  | childWriteWord0 (val : Int)
  | foreignReadReceiver
  | writeGlobalSideEffect (val : Int)
  | panicIfArgNeg (payload : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Monomorphized method body descriptor. Note `expectedTy` and `retagFacts`:
a concrete method `<T as Trait>::m` assumes its `data_ptr` points to a valid `T`
and retags its receiver parameter according to `(T.facts, rk)`. -/
structure MethodBody where
  expectedTy : TypeId
  minWords : Nat
  retagFacts : TypeFacts
  expectedRk : ReceiverKind
  canaryDomain : CanaryDomain
  ops : List MethodOp
  baseRet : Int
  deriving DecidableEq, Repr, Inhabited

/-- Open-world program environment linking arbitrarily many CGUs and `dlopen` DSOs. -/
structure OpenWorldEnv where
  vtables : List (VtablePtr × VtableDesc)
  methods : List (MethodId × MethodBody)
  deriving DecidableEq, Repr, Inhabited

def OpenWorldEnv.lookupVtable (env : OpenWorldEnv) (vp : VtablePtr) : Option VtableDesc :=
  assocLookup env.vtables vp

def OpenWorldEnv.lookupMethod (env : OpenWorldEnv) (mid : MethodId) : Option MethodBody :=
  assocLookup env.methods mid

/-- Undefined behavior categories distinguished by the operational semantics. -/
inductive UbKind where
  | danglingVtable
  | missingMethod
  | danglingDataPtr
  | receiverKindMismatch
  | typeLayoutConfusion
  | outOfBoundsField
  | treeBorrowsUb
  | unreachableExecuted
  deriving DecidableEq, Repr, Inhabited

/-- Observable call outcomes including normal return, caught same-`CANARY` Rust unwind,
foreign-`CANARY` abort (`library/panic_unwind/src/gcc.rs:97-103`), and UB. -/
inductive ExecOutcome where
  | returned (retVal : Int) (heap : HeapState)
  | unwoundCaught (payload : Nat) (callerHeap : HeapState)
  | foreignExceptionAbort (callerHeap : HeapState)
  | ub (reason : UbKind)
  deriving DecidableEq, Repr, Inhabited

/-- Extract wide-pointer vtable metadata (`UnOp::PtrMetadata`): pure register projection! -/
def extractWideVptr (w : WidePtr) : VtablePtr :=
  w.vptr

/-- Extracting `w.vptr` touches zero heap cells and induces zero Tree Borrows transitions. -/
theorem extractWideVptr_zero_heap_and_tb_effect (w : WidePtr) (h : HeapState) :
    (extractWideVptr w, h) = (w.vptr, h) :=
  rfl

/-- Execute a list of `MethodOp`s under active `FnEntry` receiver permission `(curPerm, isProt)`. -/
def execMethodOps
    (ops : List MethodOp) (callerCanary calleeCanary : CanaryDomain)
    (alloc : AllocId) (arg : Int) (acc : Int)
    (curPerm : TbPerm) (isProt : Bool) (heap : HeapState) : ExecOutcome :=
  match ops with
  | [] =>
      -- Normal return (`endCall` releases function-entry protector; write back updated perm)
      match heap.getCell alloc with
      | none => .ub .danglingDataPtr
      | some cell =>
          let heap' := heap.setCell alloc { cell with perm := curPerm }
          .returned acc heap'
  | op :: rest =>
      match op with
      | .readWord0AddToAcc =>
          match performTbAccess .read .localChild curPerm isProt, heap.getCell alloc with
          | .step nextPerm, some cell =>
              if cell.sizeWords >= 1 then
                execMethodOps rest callerCanary calleeCanary alloc arg (acc + cell.word0) nextPerm isProt heap
              else
                .ub .outOfBoundsField
          | _, none => .ub .danglingDataPtr
          | _, _ => .ub .treeBorrowsUb
      | .readWord1AddToAcc =>
          match performTbAccess .read .localChild curPerm isProt, heap.getCell alloc with
          | .step nextPerm, some cell =>
              if cell.sizeWords >= 2 then
                execMethodOps rest callerCanary calleeCanary alloc arg (acc + cell.word1) nextPerm isProt heap
              else
                .ub .outOfBoundsField
          | _, none => .ub .danglingDataPtr
          | _, _ => .ub .treeBorrowsUb
      | .childWriteWord0 v =>
          match performTbAccess .write .localChild curPerm isProt, heap.getCell alloc with
          | .step nextPerm, some cell =>
              if cell.sizeWords >= 1 then
                let heap' := heap.setCell alloc { cell with word0 := v, perm := nextPerm }
                execMethodOps rest callerCanary calleeCanary alloc arg acc nextPerm isProt heap'
              else
                .ub .outOfBoundsField
          | _, none => .ub .danglingDataPtr
          | _, _ => .ub .treeBorrowsUb
      | .foreignReadReceiver =>
          match performTbAccess .read .foreignOther curPerm isProt with
          | .step nextPerm =>
              execMethodOps rest callerCanary calleeCanary alloc arg acc nextPerm isProt heap
          | _ => .ub .treeBorrowsUb
      | .writeGlobalSideEffect v =>
          execMethodOps rest callerCanary calleeCanary alloc arg acc curPerm isProt
            { heap with globalSideEffect := v }
      | .panicIfArgNeg payload =>
          if arg < 0 then
            match heap.getCell alloc with
            | none => .ub .danglingDataPtr
            | some cell =>
                let callerHeap := heap.setCell alloc { cell with perm := curPerm }
                if calleeCanary == callerCanary then
                  .unwoundCaught payload callerHeap
                else
                  .foreignExceptionAbort callerHeap
          else
            execMethodOps rest callerCanary calleeCanary alloc arg acc curPerm isProt heap

/-- Execute a direct call to `methodId` assuming concrete receiver type `assumedTy`.
Notice the safety checks:
1. Callee ABI `expectedRk` must match `rk`.
2. Callee performs `fnEntryRetag mb.retagFacts rk cell.perm` FIRST (modeling `Retag([fn entry] _1)`
   at MIR entry of the monomorphized body!), and THEN executes `mb.ops`.
3. If `cell.dynTy != mb.expectedTy` or `cell.sizeWords < mb.minWords`, we check Tree Borrows
   transitions inside `mb.ops` OR report `.typeLayoutConfusion` if non-`UnsafeCell` layout invariants
   are violated. Specifically, retagging `&FreezeAlpha` (`cell.facts.isFreeze = true`) as `&CellBeta`
   (`mb.retagFacts.isFreeze = false`) is caught either as `.typeLayoutConfusion` (mismatch between
   pointee's actual `dynTy` and callee's `expectedTy`) or `.treeBorrowsUb` when writing a `Frozen`
   allocation! Here we check Tree Borrows against the caller's actual `Freeze` protection when `rk == .sharedRef`
   AND check `cell.dynTy == assumedTy && mb.expectedTy == assumedTy`. -/
def evalDirectConcreteCall
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (methodId : MethodId) (assumedTy : TypeId) (rk : ReceiverKind)
    (dataAlloc : AllocId) (arg : Int) (heap : HeapState) : ExecOutcome :=
  match env.lookupMethod methodId with
  | none => .ub .missingMethod
  | some mb =>
      if mb.expectedRk != rk then
        .ub .receiverKindMismatch
      else
        match heap.getCell dataAlloc with
        | none => .ub .danglingDataPtr
        | some cell =>
            -- Under caller's wide-pointer reborrow `&dyn Trait` / `&mut dyn Trait`, if `rk == .sharedRef`
            -- and the underlying object `cell.facts.isFreeze == true`, the caller's parent borrow tag
            -- freezes the allocation (`.frozen`), so even if a mismatched callee thinks its type has
            -- `UnsafeCell`, writing through a parent `Frozen` tag is immediate Tree Borrows UB!
            let effectiveFacts : TypeFacts :=
              { isFreeze := cell.facts.isFreeze || mb.retagFacts.isFreeze
              , isUnpin := mb.retagFacts.isUnpin
              , isUnsafeUnpin := mb.retagFacts.isUnsafeUnpin }
            match fnEntryRetag effectiveFacts rk cell.perm with
            | none => .ub .treeBorrowsUb
            | some (entryPerm, isProt) =>
                if cell.dynTy != assumedTy || mb.expectedTy != assumedTy || cell.sizeWords < mb.minWords then
                  -- Check whether the first write immediately violates Tree Borrows `Frozen` (matching Miri tb_03/tb_04),
                  -- otherwise report `typeLayoutConfusion`!
                  match execMethodOps mb.ops callerCanary mb.canaryDomain dataAlloc arg mb.baseRet entryPerm isProt heap with
                  | .ub u => .ub u
                  | _ => .ub .typeLayoutConfusion
                else
                  execMethodOps mb.ops callerCanary mb.canaryDomain dataAlloc arg mb.baseRet entryPerm isProt heap

/-- Unoptimized `dyn Trait` indirect call: loads `vd` from `w.vptr` and invokes `vd.methodImpl`. -/
def evalIndirectDynCall
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  match env.lookupVtable (extractWideVptr w) with
  | none => .ub .danglingVtable
  | some vd =>
      evalDirectConcreteCall env callerCanary vd.methodImpl vd.concreteTy rk w.alloc arg heap

/-! ## 4. Guarded ICP Transformations, Certificates, and Soundness Proofs -/

/-- Untrusted PGO value-profile hint (may have stale target, zero count, or adversarial weights). -/
structure UntrustedPgoHint where
  hintedVptr : VtablePtr
  profiledCount : Nat
  totalCount : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Compiler-checked guard certificate linking a concrete `VtablePtr` to `(targetTy, traitId, targetMethod)`. -/
structure VtableGuardCert where
  targetVptr : VtablePtr
  targetTy : TypeId
  traitId : TraitId
  targetMethod : MethodId
  deriving DecidableEq, Repr, Inhabited

/-- Decidable certificate verifier: checks ONLY that `targetVptr` is bound in `env` to a
`VtableDesc` with matching `concreteTy`, `traitId`, and `methodImpl`. -/
def checkVtableGuardCert (env : OpenWorldEnv) (cert : VtableGuardCert) : Bool :=
  match env.lookupVtable cert.targetVptr with
  | none => false
  | some vd =>
      (vd.concreteTy == cert.targetTy) &&
      (vd.traitId == cert.traitId) &&
      (vd.methodImpl == cert.targetMethod)

/-- Single-target value-guarded ICP (`if w.vptr == cert.targetVptr then direct_call else indirect_call`).
Note `_pgoHint` affects only branch-weight metadata / candidate selection, never semantics. -/
def evalValueGuardedIcp
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (cert : VtableGuardCert) (_pgoHint : UntrustedPgoHint)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  if extractWideVptr w == cert.targetVptr then
    evalDirectConcreteCall env callerCanary cert.targetMethod cert.targetTy rk w.alloc arg heap
  else
    evalIndirectDynCall env callerCanary rk w arg heap

/-- Helper inversion lemma for `checkVtableGuardCert env cert = true`. -/
theorem checkVtableGuardCert_inv
    {env : OpenWorldEnv} {cert : VtableGuardCert}
    (hCert : checkVtableGuardCert env cert = true) :
    ∃ vd, env.lookupVtable cert.targetVptr = some vd ∧
          vd.concreteTy = cert.targetTy ∧
          vd.traitId = cert.traitId ∧
          vd.methodImpl = cert.targetMethod := by
  unfold checkVtableGuardCert at hCert
  cases hLookup : env.lookupVtable cert.targetVptr with
  | none =>
      rw [hLookup] at hCert
      contradiction
  | some vd =>
      rw [hLookup] at hCert
      simp only [Bool.and_eq_true, beq_iff_eq] at hCert
      exact ⟨vd, rfl, hCert.1.1, hCert.1.2, hCert.2⟩

/-- **Theorem 1 (Unconditional Soundness of Value-Guarded ICP):**
Whenever `checkVtableGuardCert env cert = true`, value-guarded ICP produces the **exact same**
`ExecOutcome` (including return value, post-heap, Tree Borrows permissions, caught Rust unwinds,
and foreign-`CANARY` `cdylib` aborts) as unoptimized `evalIndirectDynCall`, for **every**
untrusted/adversarial PGO hint and **every** runtime wide pointer (including duplicate vtables
from dynamically loaded DSOs). -/
theorem valueGuardedIcp_exact_equiv
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (cert : VtableGuardCert) (pgoHint : UntrustedPgoHint)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState)
    (hCert : checkVtableGuardCert env cert = true) :
    evalValueGuardedIcp env callerCanary cert pgoHint rk w arg heap =
      evalIndirectDynCall env callerCanary rk w arg heap := by
  unfold evalValueGuardedIcp
  cases hEq : (extractWideVptr w == cert.targetVptr)
  · simp
  · simp only [↓reduceIte]
    have hVptr : extractWideVptr w = cert.targetVptr := beq_iff_eq.mp hEq
    rcases checkVtableGuardCert_inv hCert with ⟨vd, hVd, hTy, _, hMeth⟩
    unfold evalIndirectDynCall
    rw [hVptr, hVd]
    dsimp only
    rw [hTy, hMeth]

/-- Multi-candidate guarded ICP cascade (`if vptr == vt₁ then direct₁ else if vptr == vt₂ ... else indirect`). -/
def evalMultiGuardedIcpCascade
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (certs : List VtableGuardCert)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  match certs with
  | [] => evalIndirectDynCall env callerCanary rk w arg heap
  | c :: rest =>
      if extractWideVptr w == c.targetVptr then
        evalDirectConcreteCall env callerCanary c.targetMethod c.targetTy rk w.alloc arg heap
      else
        evalMultiGuardedIcpCascade env callerCanary rest rk w arg heap

/-- **Theorem 2 (Multi-Target Cascade ICP Soundness):**
Any finite cascade of certified vtable guards (covering both polymorphic inline caches and
multi-DSO vtable lists where each DSO vtable invokes its own method symbol) is 100% equivalent
to `evalIndirectDynCall`. -/
theorem multiGuardedIcpCascade_exact_equiv
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (certs : List VtableGuardCert)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState)
    (hAll : certs.all (checkVtableGuardCert env) = true) :
    evalMultiGuardedIcpCascade env callerCanary certs rk w arg heap =
      evalIndirectDynCall env callerCanary rk w arg heap := by
  induction certs with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hAll
      unfold evalMultiGuardedIcpCascade
      cases hEq : (extractWideVptr w == c.targetVptr)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih hAll.2
      · simp only [↓reduceIte]
        have hVptr : extractWideVptr w = c.targetVptr := beq_iff_eq.mp hEq
        rcases checkVtableGuardCert_inv hAll.1 with ⟨vd, hVd, hTy, _, hMeth⟩
        unfold evalIndirectDynCall
        rw [hVptr, hVd]
        dsimp only
        rw [hTy, hMeth]

/-- Function-pointer-guarded ICP (`llvm::IndirectCallPromoter::tryToPromoteWithFuncCmp`,
`IndirectCallPromotion.cpp:691-735`): loads `vd` from `w.vptr` and compares `vd.methodImpl`
against `targetMethod` (coupled with verifying `vd.concreteTy == targetTy` by Rust vtable
uniqueness of monomorphized method symbols per concrete self type). -/
def checkFuncPtrCert (env : OpenWorldEnv) (targetMethod : MethodId) (targetTy : TypeId) : Bool :=
  env.vtables.all fun (_, vd) =>
    if vd.methodImpl == targetMethod then vd.concreteTy == targetTy else true

def evalFuncPtrGuardedIcp
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (targetMethod : MethodId) (targetTy : TypeId)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  match env.lookupVtable (extractWideVptr w) with
  | none => .ub .danglingVtable
  | some vd =>
      if vd.methodImpl == targetMethod then
        evalDirectConcreteCall env callerCanary targetMethod targetTy rk w.alloc arg heap
      else
        evalDirectConcreteCall env callerCanary vd.methodImpl vd.concreteTy rk w.alloc arg heap

private theorem assocLookup_mem_all
    {vtables : List (VtablePtr × VtableDesc)} {vp : VtablePtr} {vd : VtableDesc}
    {p : VtablePtr × VtableDesc → Bool}
    (hAll : vtables.all p = true)
    (hFind : assocLookup vtables vp = some vd) :
    ∃ vp₀, p (vp₀, vd) = true := by
  induction vtables with
  | nil => contradiction
  | cons hd tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hAll
      unfold assocLookup at hFind
      cases hEq : (vp == hd.1)
      · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hFind
        exact ih hAll.2 hFind
      · simp only [hEq, ↓reduceIte] at hFind
        injection hFind with hVd
        subst hVd
        exact ⟨hd.1, hAll.1⟩

/-- **Theorem 3 (Soundness of Function-Pointer-Guarded ICP):**
When `targetMethod` uniquely identifies `targetTy` across registered vtables, LLVM-style
`tryToPromoteWithFuncCmp` is 100% equivalent to `evalIndirectDynCall` — and takes the fast path
across distinct multi-CGU / multi-`rlib` duplicate vtables (`vt_cgu0 ≠ vt_cgu1`) whenever both
vtables reference the same shared `targetMethod`! -/
theorem funcPtrGuardedIcp_exact_equiv
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (targetMethod : MethodId) (targetTy : TypeId)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState)
    (hFnCert : checkFuncPtrCert env targetMethod targetTy = true) :
    evalFuncPtrGuardedIcp env callerCanary targetMethod targetTy rk w arg heap =
      evalIndirectDynCall env callerCanary rk w arg heap := by
  unfold evalFuncPtrGuardedIcp evalIndirectDynCall
  cases hLookup : env.lookupVtable (extractWideVptr w) with
  | none => rfl
  | some vd =>
      dsimp only
      cases hM : (vd.methodImpl == targetMethod)
      · simp
      · simp only [↓reduceIte]
        have hMethEq : vd.methodImpl = targetMethod := beq_iff_eq.mp hM
        rcases assocLookup_mem_all hFnCert hLookup with ⟨_, hProp⟩
        simp only [hM, ↓reduceIte, beq_iff_eq] at hProp
        rw [hMethEq, hProp]

/-- Two-vtable single-callee coalesced guard (`if vptr == vt₁ || vptr == vt₂ then direct_m₁ else indirect`),
which attempts to redirect a second CGU/DSO's duplicate vtable `vt₂` into `vt₁`'s method body `m₁`. -/
def evalTwoVtableSingleCalleeIcp
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (vt₁ vt₂ : VtablePtr) (m₁ : MethodId) (ty : TypeId)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  if (extractWideVptr w == vt₁) || (extractWideVptr w == vt₂) then
    evalDirectConcreteCall env callerCanary m₁ ty rk w.alloc arg heap
  else
    evalIndirectDynCall env callerCanary rk w arg heap

/-- **Theorem 4a (Multi-CGU / Multi-`rlib` / Shared-`std` `dylib` Coalescing Soundness):**
Coalescing `vt₁` and `vt₂` into a single direct call `m₁` is sound whenever `vt₂`'s method `m₂`
has identical `MethodBody` (including identical `canaryDomain`, i.e., shared `libstd`!). -/
theorem twoVtableSingleCalleeIcp_sound_of_same_body
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (c₁ c₂ : VtableGuardCert)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState)
    (hTy : c₂.targetTy = c₁.targetTy)
    (hCert₁ : checkVtableGuardCert env c₁ = true)
    (hCert₂ : checkVtableGuardCert env c₂ = true)
    (hSameBody : env.lookupMethod c₂.targetMethod = env.lookupMethod c₁.targetMethod) :
    evalTwoVtableSingleCalleeIcp env callerCanary c₁.targetVptr c₂.targetVptr
        c₁.targetMethod c₁.targetTy rk w arg heap =
      evalIndirectDynCall env callerCanary rk w arg heap := by
  unfold evalTwoVtableSingleCalleeIcp
  cases h1 : (extractWideVptr w == c₁.targetVptr)
  · cases h2 : (extractWideVptr w == c₂.targetVptr)
    · simp
    · simp only [Bool.false_or, ↓reduceIte]
      have hVptr : extractWideVptr w = c₂.targetVptr := beq_iff_eq.mp h2
      rcases checkVtableGuardCert_inv hCert₂ with ⟨vd₂, hVd₂, hTy₂, _, hM₂⟩
      unfold evalIndirectDynCall
      rw [hVptr, hVd₂]
      dsimp only
      rw [hTy₂, hTy, hM₂]
      unfold evalDirectConcreteCall
      rw [hSameBody]
  · simp only [Bool.true_or, ↓reduceIte]
    have hVptr : extractWideVptr w = c₁.targetVptr := beq_iff_eq.mp h1
    rcases checkVtableGuardCert_inv hCert₁ with ⟨vd₁, hVd₁, hTy₁, _, hM₁⟩
    unfold evalIndirectDynCall
    rw [hVptr, hVd₁]
    dsimp only
    rw [hTy₁, hM₁]

/-- Open-world dynamic linking monotonicity (`dlopen` adds DSO vtables/methods without mutating existing ones). -/
def LinkExtends (base extended : OpenWorldEnv) : Prop :=
  (∀ vp vd, base.lookupVtable vp = some vd → extended.lookupVtable vp = some vd) ∧
  (∀ mid mb, base.lookupMethod mid = some mb → extended.lookupMethod mid = some mb)

/-- **Theorem 5 (Open-World `dlopen` Monotonicity):**
Any guard certificate verified in `base` remains valid in any dynamically extended `OpenWorldEnv`
(even when `extended` loads new DSOs defining duplicate vtables for `cert.targetTy`!), preserving
exact equivalence with `evalIndirectDynCall` in `extended`. -/
theorem openWorldLink_preserves_guardedIcp
    {base extended : OpenWorldEnv}
    (hExt : LinkExtends base extended)
    {cert : VtableGuardCert}
    (hCert : checkVtableGuardCert base cert = true)
    (callerCanary : CanaryDomain) (pgoHint : UntrustedPgoHint)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) :
    checkVtableGuardCert extended cert = true ∧
    evalValueGuardedIcp extended callerCanary cert pgoHint rk w arg heap =
      evalIndirectDynCall extended callerCanary rk w arg heap := by
  rcases checkVtableGuardCert_inv hCert with ⟨vd, hVd, hTy, hTr, hMeth⟩
  have hVdExt := hExt.1 cert.targetVptr vd hVd
  have hCertExt : checkVtableGuardCert extended cert = true := by
    unfold checkVtableGuardCert
    rw [hVdExt]
    dsimp only
    rw [hTy, hTr, hMeth]
    have h1 : (cert.targetTy == cert.targetTy) = true := beq_self_eq_true cert.targetTy
    have h2 : (cert.traitId == cert.traitId) = true := beq_self_eq_true cert.traitId
    have h3 : (cert.targetMethod == cert.targetMethod) = true := beq_self_eq_true cert.targetMethod
    rw [h1, h2, h3]
    rfl
  exact ⟨hCertExt, valueGuardedIcp_exact_equiv extended callerCanary cert pgoHint rk w arg heap hCertExt⟩

/-! ## 5. Kernel-Checked Negative Counterexamples (`V1` Non-Vacuity & Broken Assumptions) -/

/-- Shared fixture types and IDs for concrete counterexample witnesses. -/
private def tyFreezeAlpha : TypeId := 1
private def tyCellBeta : TypeId := 2
private def traitSharedOp : TraitId := 10
private def methAlphaHost : MethodId := 100
private def methAlphaCdylib : MethodId := 101
private def methBetaHost : MethodId := 200

private def vtAlphaHost : VtablePtr := { dsoId := 0, slotId := 0 }
private def vtAlphaPlugin : VtablePtr := { dsoId := 1, slotId := 0 }
private def vtBetaHost : VtablePtr := { dsoId := 0, slotId := 1 }

private def factsFreeze : TypeFacts := { isFreeze := true, isUnpin := true, isUnsafeUnpin := true }
private def factsCell : TypeFacts := { isFreeze := false, isUnpin := true, isUnsafeUnpin := true }

private def demoOpenWorldEnv : OpenWorldEnv :=
  { vtables :=
      [ (vtAlphaHost, { concreteTy := tyFreezeAlpha, traitId := traitSharedOp, sizeWords := 1
                      , facts := factsFreeze, methodImpl := methAlphaHost })
      , (vtAlphaPlugin, { concreteTy := tyFreezeAlpha, traitId := traitSharedOp, sizeWords := 1
                        , facts := factsFreeze, methodImpl := methAlphaCdylib })
      , (vtBetaHost, { concreteTy := tyCellBeta, traitId := traitSharedOp, sizeWords := 1
                     , facts := factsCell, methodImpl := methBetaHost }) ]
  , methods :=
      [ (methAlphaHost,
          { expectedTy := tyFreezeAlpha, minWords := 1, retagFacts := factsFreeze
          , expectedRk := .sharedRef, canaryDomain := 0
          , ops := [.readWord0AddToAcc, .writeGlobalSideEffect 777, .panicIfArgNeg 9]
          , baseRet := 5 })
      , (methAlphaCdylib,
          { expectedTy := tyFreezeAlpha, minWords := 1, retagFacts := factsFreeze
          , expectedRk := .sharedRef, canaryDomain := 1 -- Separate cdylib `libstd` CANARY!
          , ops := [.readWord0AddToAcc, .writeGlobalSideEffect 777, .panicIfArgNeg 9]
          , baseRet := 5 })
      , (methBetaHost,
          { expectedTy := tyCellBeta, minWords := 1, retagFacts := factsCell
          , expectedRk := .sharedRef, canaryDomain := 0
          , ops := [.childWriteWord0 88, .readWord0AddToAcc] -- Interior `UnsafeCell` write!
          , baseRet := 0 }) ] }

private def demoAlphaHeap : HeapState :=
  { cells := [(0, { dynTy := tyFreezeAlpha, sizeWords := 1, word0 := 32, word1 := 0
                  , facts := factsFreeze, perm := .frozen })]
  , globalSideEffect := 100 }

/-- **Counterexample A (Unguarded Stale-PGO Devirtualization Violates Tree Borrows `Frozen`):**
A stale PGO profile claims callsite target is `CellBeta` (`UnsafeCell` interior mutation);
unguarded devirtualization dispatches a `FreezeAlpha` `&dyn SharedOp` receiver directly into
`methBetaHost`, attempting a write under a `Frozen` receiver permission -> `.ub .treeBorrowsUb`
(matching Miri `-Zmiri-tree-borrows` litmus `tb_03`!), whereas `evalIndirectDynCall` returns `37`. -/
theorem cex_unguardedStalePgo_treeBorrows_ub :
    let wHostAlpha : WidePtr := { alloc := 0, vptr := vtAlphaHost }
    evalDirectConcreteCall demoOpenWorldEnv 0 methBetaHost tyCellBeta .sharedRef wHostAlpha.alloc 1 demoAlphaHeap =
      .ub .treeBorrowsUb ∧
    evalIndirectDynCall demoOpenWorldEnv 0 .sharedRef wHostAlpha 1 demoAlphaHeap =
      .returned 37 { demoAlphaHeap with globalSideEffect := 777 } := by
  exact ⟨rfl, rfl⟩

/-- **Counterexample B (Closed-World `else unreachable` Fails on Duplicate DSO/CGU Vtable):**
Even if `FreezeAlpha` were the ONLY concrete type ever instantiated at runtime, an object arriving
with duplicate vtable `vtAlphaPlugin ≠ vtAlphaHost` triggers `.ub .unreachableExecuted` under
`if vptr == vtAlphaHost then direct else unreachable`, while value-guarded ICP returns `37`. -/
def evalClosedWorldUnreachableIcp
    (env : OpenWorldEnv) (callerCanary : CanaryDomain) (cert : VtableGuardCert)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  if extractWideVptr w == cert.targetVptr then
    evalDirectConcreteCall env callerCanary cert.targetMethod cert.targetTy rk w.alloc arg heap
  else
    .ub .unreachableExecuted

theorem cex_closedWorldUnreachable_dup_vtable_ub :
    let certAlpha : VtableGuardCert :=
      { targetVptr := vtAlphaHost, targetTy := tyFreezeAlpha
      , traitId := traitSharedOp, targetMethod := methAlphaHost }
    let wPluginAlpha : WidePtr := { alloc := 0, vptr := vtAlphaPlugin }
    let staleHint : UntrustedPgoHint := { hintedVptr := vtBetaHost, profiledCount := 999, totalCount := 999 }
    vtAlphaPlugin ≠ vtAlphaHost ∧
    checkVtableGuardCert demoOpenWorldEnv certAlpha = true ∧
    evalClosedWorldUnreachableIcp demoOpenWorldEnv 0 certAlpha .sharedRef wPluginAlpha 1 demoAlphaHeap =
      .ub .unreachableExecuted ∧
    evalValueGuardedIcp demoOpenWorldEnv 0 certAlpha staleHint .sharedRef wPluginAlpha 1 demoAlphaHeap =
      .returned 37 { demoAlphaHeap with globalSideEffect := 777 } := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro hEq
  injection hEq with hDso _
  contradiction

/-- **Counterexample C (Closed-World 2-Impl Peeled Guard Fails on Duplicate Vtable):**
Assuming `{FreezeAlpha, CellBeta}` has unique vtables and omitting the second guard
(`if vptr == vtAlphaHost then Alpha else Beta`) misdispatches `wPluginAlpha` (`FreezeAlpha`
with `vtAlphaPlugin`) into `methBetaHost`, triggering `.ub .treeBorrowsUb` (matching Miri `tb_04`!). -/
def evalClosedWorldPeeledTwoImpl
    (env : OpenWorldEnv) (callerCanary : CanaryDomain)
    (vtA : VtablePtr) (mA : MethodId) (tyA : TypeId)
    (mB : MethodId) (tyB : TypeId)
    (rk : ReceiverKind) (w : WidePtr) (arg : Int) (heap : HeapState) : ExecOutcome :=
  if extractWideVptr w == vtA then
    evalDirectConcreteCall env callerCanary mA tyA rk w.alloc arg heap
  else
    evalDirectConcreteCall env callerCanary mB tyB rk w.alloc arg heap

theorem cex_closedWorldPeeledTwoImpl_dup_vtable_ub :
    let wPluginAlpha : WidePtr := { alloc := 0, vptr := vtAlphaPlugin }
    evalClosedWorldPeeledTwoImpl demoOpenWorldEnv 0
        vtAlphaHost methAlphaHost tyFreezeAlpha methBetaHost tyCellBeta
        .sharedRef wPluginAlpha 1 demoAlphaHeap = .ub .treeBorrowsUb ∧
    evalIndirectDynCall demoOpenWorldEnv 0 .sharedRef wPluginAlpha 1 demoAlphaHeap =
      .returned 37 { demoAlphaHeap with globalSideEffect := 777 } := by
  exact ⟨rfl, rfl⟩

/-- **Counterexample D (Negative Vtable-Inequality Alias / Read-Forwarding in `else` Miscompiles):**
Suppose the compiler keeps the safe `else` indirect call `evalIndirectDynCall`, and afterward
reads `heap.globalSideEffect`. In the `else` branch (`w.vptr != vtAlphaHost`), a naive alias
analysis deduces `DynamicType(w) != FreezeAlpha`, concluding the `else` call cannot execute
`FreezeAlpha`'s `writeGlobalSideEffect 777`, and forwards the pre-call value `heap.globalSideEffect = 100`!
When `w` carries duplicate `vtAlphaPlugin`, the `else` indirect call DOES invoke `FreezeAlpha`
(`globalSideEffect := 777`), so read-forwarding returns `100` instead of `777`! -/
def callerReadGlobalAfterTrueSemantics
    (env : OpenWorldEnv) (w : WidePtr) (heap : HeapState) : Option Int :=
  match evalIndirectDynCall env 0 .sharedRef w 1 heap with
  | .returned _ heap' => some heap'.globalSideEffect
  | _ => none

def callerReadGlobalAfterUnsoundElseForwarding
    (env : OpenWorldEnv) (knownAlphaVt : VtablePtr) (w : WidePtr) (heap : HeapState) : Option Int :=
  let preGlobal := heap.globalSideEffect
  if extractWideVptr w == knownAlphaVt then
    match evalDirectConcreteCall env 0 methAlphaHost tyFreezeAlpha .sharedRef w.alloc 1 heap with
    | .returned _ heap' => some heap'.globalSideEffect
    | _ => none
  else
    -- BUG: Assumes `w.vptr != knownAlphaVt => callee cannot be FreezeAlpha` and forwards `preGlobal`!
    match evalIndirectDynCall env 0 .sharedRef w 1 heap with
    | .returned _ _ => some preGlobal
    | _ => none

theorem cex_negativeVtableInequalityAliasForwarding_unsound :
    let wPluginAlpha : WidePtr := { alloc := 0, vptr := vtAlphaPlugin }
    callerReadGlobalAfterTrueSemantics demoOpenWorldEnv wPluginAlpha demoAlphaHeap = some 777 ∧
    callerReadGlobalAfterUnsoundElseForwarding demoOpenWorldEnv vtAlphaHost wPluginAlpha demoAlphaHeap = some 100 := by
  exact ⟨rfl, rfl⟩

/-- **Counterexample E (Broken Assumption: Cross-`cdylib` Two-Vtable Coalescing Breaks Unwind Equivalence):**
When `vtAlphaPlugin` belongs to a `--crate-type=cdylib` (`canaryDomain = 1 ≠ callerCanary = 0`,
`library/panic_unwind/src/gcc.rs:48,97-103`), unoptimized `evalIndirectDynCall` on panicking input
`arg = -1` invokes `methAlphaCdylib` and aborts with `.foreignExceptionAbort` (`SIGABRT`:
`"Rust cannot catch foreign exceptions"`), whereas single-target `evalValueGuardedIcp` preserves
`.foreignExceptionAbort` identically, **and** coalesced two-vtable `evalTwoVtableSingleCalleeIcp`
redirecting `vtAlphaPlugin` to `methAlphaHost` unsoundly alters the outcome to `.unwoundCaught 9`! -/
theorem cex_crossCdylibTwoVtableSingleCallee_breaks_unwind :
    let certHost : VtableGuardCert :=
      { targetVptr := vtAlphaHost, targetTy := tyFreezeAlpha
      , traitId := traitSharedOp, targetMethod := methAlphaHost }
    let wPluginAlpha : WidePtr := { alloc := 0, vptr := vtAlphaPlugin }
    let hint : UntrustedPgoHint := { hintedVptr := vtAlphaHost, profiledCount := 50, totalCount := 100 }
    -- 1. Unoptimized indirect call aborts on foreign cdylib CANARY:
    evalIndirectDynCall demoOpenWorldEnv 0 .sharedRef wPluginAlpha (-1) demoAlphaHeap =
      .foreignExceptionAbort { demoAlphaHeap with globalSideEffect := 777 } ∧
    -- 2. Single-target value-guarded ICP (`if vptr == vtAlphaHost`) preserves exact abort behavior:
    evalValueGuardedIcp demoOpenWorldEnv 0 certHost hint .sharedRef wPluginAlpha (-1) demoAlphaHeap =
      .foreignExceptionAbort { demoAlphaHeap with globalSideEffect := 777 } ∧
    -- 3. Naive cross-cdylib 2-vtable coalescing (`if vptr == vtHost || vptr == vtPlugin -> methAlphaHost`)
    --    diverges by turning a fatal foreign-CANARY abort into a caught host unwind:
    evalTwoVtableSingleCalleeIcp demoOpenWorldEnv 0 vtAlphaHost vtAlphaPlugin methAlphaHost tyFreezeAlpha
        .sharedRef wPluginAlpha (-1) demoAlphaHeap =
      .unwoundCaught 9 { demoAlphaHeap with globalSideEffect := 777 } := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Protected `&mut self` Unwind & `ReservedFrz` Verification Witness:**
Demonstrates that under `&mut self` (`tyIsUnpin = true`), `FnEntry` retagging installs
`(.reservedFrz false, true)` (`StrongProtector`), and a foreign read followed by a child write
while protected triggers `.ub .treeBorrowsUb` (`Permissions.lean:73,86`) identically in both
`evalValueGuardedIcp` and `evalIndirectDynCall`. -/
theorem mutSelf_protected_reservedFrz_conflict_preserved :
    let tyMut : TypeId := 3
    let methConflict : MethodId := 300
    let vtMut : VtablePtr := { dsoId := 0, slotId := 3 }
    let envMut : OpenWorldEnv :=
      { vtables := [(vtMut, { concreteTy := tyMut, traitId := 20, sizeWords := 1
                            , facts := factsFreeze, methodImpl := methConflict })]
      , methods := [(methConflict,
          { expectedTy := tyMut, minWords := 1, retagFacts := factsFreeze
          , expectedRk := .mutRef, canaryDomain := 0
          , ops := [.foreignReadReceiver, .childWriteWord0 55], baseRet := 0 })] }
    let certMut : VtableGuardCert :=
      { targetVptr := vtMut, targetTy := tyMut, traitId := 20, targetMethod := methConflict }
    let heapMut : HeapState :=
      { cells := [(0, { dynTy := tyMut, sizeWords := 1, word0 := 10, word1 := 0
                      , facts := factsFreeze, perm := .unique })]
      , globalSideEffect := 0 }
    let w : WidePtr := { alloc := 0, vptr := vtMut }
    let hint : UntrustedPgoHint := { hintedVptr := vtMut, profiledCount := 10, totalCount := 10 }
    checkVtableGuardCert envMut certMut = true ∧
    evalValueGuardedIcp envMut 0 certMut hint .mutRef w 0 heapMut = .ub .treeBorrowsUb ∧
    evalIndirectDynCall envMut 0 .mutRef w 0 heapMut = .ub .treeBorrowsUb := by
  exact ⟨rfl, rfl, rfl⟩

end VrustcPkg.VtableGuardedIcpPgo
