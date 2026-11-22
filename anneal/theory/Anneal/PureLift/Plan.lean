-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin

namespace Anneal.PureLift

/-!
# Structured Control-Flow Plans, Diamond Joins, and Function Lifting (`Plan`)

Evaluates imperative control-flow plans (`FlowPlan Val`) over the unified pure
symbolic state (`SymState Val`).

Supported features:
- Sub-place reads and writes (`PlaceExpr.localSub` and `PlaceExpr.derefSub`)
  checked against `PermTree` permissions and `LoanPhase` liveness.
- Shared and mutable borrows (`PrimAction.borrow`) and explicit loan or
  multi-region-group termination (`PrimAction.endLoan` and
  `PrimAction.endRegionGroup`).
- Modular single-region (`PrimAction.call`) and multi-region-group
  (`PrimAction.callMultiRegion`) interprocedural calls using forward/backward
  lens summaries.
- Hybrid functional-spatial pinning (`PrimAction.freezeSpatial`,
  `PrimAction.mutateSpatial`, and `PrimAction.reabsorbSpatial`).
- Symbolic diamond branch joins (`joinSymState`) with anti-aliasing validation
  on explicit join pairs (`validJoinPairs`).
- Nested early return (`FlowPlan.earlyReturn`) with scoped loan and region
  cleanup and short-circuiting through enclosing sequential compositions and
  loops (`ExecFlow`).
- Entry parameter aliasing validation (`initFnState`) and top-level function
  lifting (`evalFnValue` and `evalFnReturningMut`).
-/

def sameBackTargetStepShape {Val : Type} :
    BackTargetStep Val → BackTargetStep Val → Bool
  | .rootParam i, .rootParam j => i == j
  | .direct o1 p1, .direct o2 p2 => OwnerRef.beq o1 o2 && subPathEq p1 p2
  | .regionOut g1 i1, .regionOut g2 i2 => g1 == g2 && i1 == i2
  | _, _ => false

def sameBackTargetShape {Val : Type} (t1 t2 : BackTarget Val) : Bool :=
  match t1.steps, t2.steps with
  | [s1], [s2] => sameBackTargetStepShape s1 s2
  | _, _ => false

def joinBackTarget {Val : Type} (cond : Val)
    (t1 t2 : BackTarget Val) : BackTarget Val :=
  if sameBackTargetShape t1 t2 then t1
  else .choice cond t1 t2

/-- Place expression addressing either a local register sub-path or a
dereferenced borrow handle with an additional sub-path projection. -/
inductive PlaceExpr where
  | localSub (reg : LocalId) (path : SubPath)
  | derefSub (reg : LocalId) (path : SubPath)

/-- Decode the borrow handle stored in local `reg` for read (`reqMut = false`)
or mutable (`reqMut = true`) access. Reading through a handle or ending its
loan requires `reg` to hold a readable value (`getOwnerForRead`); writing or
mutably reborrowing through a handle requires `reg` itself to be writable
(`getOwnerForMut`), so an active shared borrow of a local holding an `&mut`
blocks mutating through that `&mut`. -/
def readLocalHandleForAccess {Val : Type} (alg : ValAlgebra Val)
    (reqMut : Bool) (reg : LocalId) (st : SymState Val) :
    Option (LoanId × SubPath) :=
  let cellOpt :=
    if reqMut then getOwnerForMut alg (.localReg reg) st []
    else getOwnerForRead alg (.localReg reg) st []
  match cellOpt with
  | some ⟨handle, _⟩ => alg.decodeRef handle
  | none => none

/-- Decode the borrow handle stored in local `reg` for read access. -/
def readLocalHandle {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : Option (LoanId × SubPath) :=
  readLocalHandleForAccess alg false reg st

/-- Resolve `PlaceExpr` in `st` to its underlying `(OwnerRef × SubPath)` for
read (`reqMut = false`) or mutable (`reqMut = true`) access. -/
def resolvePlaceForAccess {Val : Type} (alg : ValAlgebra Val)
    (reqMut : Bool) (p : PlaceExpr) (st : SymState Val) :
    Option (OwnerRef × SubPath) :=
  match p with
  | .localSub reg path => some (.localReg reg, path)
  | .derefSub reg extraPath =>
    match readLocalHandleForAccess alg reqMut reg st with
    | some (lid, basePath) => some (.parentLoan lid, basePath ++ extraPath)
    | none => none

/-- Resolve `PlaceExpr` in `st` to its underlying `(OwnerRef × SubPath)` for
read access. -/
def resolvePlace {Val : Type} (alg : ValAlgebra Val) (p : PlaceExpr)
    (st : SymState Val) : Option (OwnerRef × SubPath) :=
  resolvePlaceForAccess alg false p st

/-- Resolve and read a branch-joined choice tree of shared-reference handles
at additional projection `extraPath`. Every leaf must decode to a copyable
(`.activeShared`) loan handle whose target sub-path is readable in `st`, and
every choice guard must be handle-free. -/
def readSharedChoiceDeref {Val : Type} (alg : ValAlgebra Val)
    (extraPath : SubPath) (st : SymState Val) (handle : Val) :
    Option Val :=
  natFold (fun _ => none)
    (fun _ ih w =>
      match alg.decodeRef w with
      | some (lid, basePath) =>
        if !handleCopyable st.loans lid then none
        else
          let fullPath := basePath ++ extraPath
          match getOwnerForRead alg (.parentLoan lid) st fullPath with
          | some ⟨subVal, _⟩ => some subVal
          | none => none
      | none =>
        match alg.branchSplit w with
        | none => none
        | some (cond, vt, vf) =>
          if !handleFreeVal alg cond then none
          else
            match alg.asBool cond with
            | some true => ih vt
            | some false => ih vf
            | none =>
              match ih vt, ih vf with
              | some v1, some v2 =>
                some (zipOrKeepSameRef alg cond v1 v2)
              | _, _ => none)
    (alg.sizeBound handle + 1) handle

/-- Read the value at `PlaceExpr` if `PermTree` permits reading at the resolved
sub-path and the owner is active. When `p = .derefSub reg extraPath` and `reg`
holds a symbolic choice of shared-reference handles produced by a branch join,
resolves the dereference branch-wise (`readSharedChoiceDeref`). -/
def readPlaceVal {Val : Type} (alg : ValAlgebra Val)
    (p : PlaceExpr) (st : SymState Val) : Option Val :=
  match resolvePlaceForAccess alg false p st with
  | some (owner, path) =>
    match getOwnerForRead alg owner st path with
    | some ⟨subVal, _⟩ => some subVal
    | none => none
  | none =>
    match p with
    | .localSub _ _ => none
    | .derefSub reg extraPath =>
      match getOwnerForRead alg (.localReg reg) st [] with
      | some ⟨handle, _⟩ =>
        match alg.decodeRef handle with
        | some _ => none
        | none => readSharedChoiceDeref alg extraPath st handle
      | none => none

/-- Write `vNew` to `PlaceExpr` if `PermTree` permits writing at the resolved
sub-path and the owner (as well as the handle local itself for `.derefSub`) is
mutable and active. -/
def writePlaceVal {Val : Type} (alg : ValAlgebra Val)
    (p : PlaceExpr) (vNew : Val) (st : SymState Val) : Option (SymState Val) :=
  match resolvePlaceForAccess alg true p st with
  | none => none
  | some (owner, path) =>
    match owner, path with
    -- A whole-local write may also create the next fresh local.
    | .localReg reg, [] => setLocalChecked alg reg vNew st
    | _, _ =>
      modifyOwner alg owner true (fun ownerVal ownerPerm =>
        if canWritePath path ownerPerm then
          match putPath alg path ownerVal vNew with
          | some ownerVal' => some (ownerVal', ownerPerm)
          | none => none
        else none) st

/-- Pure right-hand-side expression operator. -/
inductive RvalOp (Val : Type) where
  | constVal (v : Val)
  | use (p : PlaceExpr)
  | unary (f : Val → Option Val) (p : PlaceExpr)
  | binary (f : Val → Val → Option Val) (p1 p2 : PlaceExpr)

/-- Evaluate the right-hand side `op` in `st`: a constant, a read of a place
(`readPlaceVal`), or a pure function of one or two values read from places.
Fails (`none`) if a read fails or the function rejects its arguments.

A read neither moves nor copy-checks the value it reads, so the result may
duplicate a borrow handle that is still stored at its place. A caller that
stores the result in the state must first check that the copy is allowed
(`copyableVal`, as `stepAction`'s `.assign` and `evalRvalList` do); a value
that leaves the function is checked by `handleFreeOut` instead, and a branch
condition is only inspected. -/
def evalRval {Val : Type} (alg : ValAlgebra Val) (op : RvalOp Val)
    (st : SymState Val) : Option Val :=
  match op with
  | .constVal v => some v
  | .use p => readPlaceVal alg p st
  | .unary f p =>
    match readPlaceVal alg p st with
    | some v => f v
    | none => none
  | .binary f p1 p2 =>
    match readPlaceVal alg p1 st, readPlaceVal alg p2 st with
    | some v1, some v2 => f v1 v2
    | _, _ => none

/-- Evaluate the by-value arguments of a call. Each argument is copied into
the callee, so each must satisfy `copyableVal`. -/
def evalRvalList {Val : Type} (alg : ValAlgebra Val)
    (ops : List (RvalOp Val)) (st : SymState Val) : Option (List Val) :=
  listFold (some [])
    (fun r _ ih =>
      match evalRval alg r st, ih with
      | some v, some vs =>
        if copyableVal alg st.loans v then some (v :: vs) else none
      | _, _ => none)
    ops

/-- Modular forward/backward lens summary for a single-region function call. -/
structure CallSummary (Val : Type) where
  returnsMutBorrow : Bool
  fwd : List Val → List Val → Option Val
  back : List Val → List Val → Val → Option (List Val)

/-- Specification of one region group in a multi-region-group call. -/
structure RegionGroupSpec (Val : Type) where
  groupId : RegionGroupId
  requiredChildren : List RegionGroupId
  inputPlaces : List PlaceExpr
  outDsts : List LocalId
  fwdOuts : List Val → List Val → Option (List Val)
  backFn : List Val → List Val → List Val → List Val →
      Option (List Val × List Val)

/-- Lock each mutable argument place for loan `lid` in left-to-right order,
rejecting aliased or overlapping mutable arguments or dereferences through a
non-writable handle local. -/
def acquireMutCallArgs {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (places : List PlaceExpr) (st : SymState Val) :
    Option (List (OwnerRef × SubPath) × List Val × SymState Val) :=
  listFold
    (fun st0 => some ([], [], st0))
    (fun p _ ih st0 =>
      match resolvePlaceForAccess alg true p st0 with
      | none => none
      | some (owner, path) =>
        match modifyOwnerRes alg owner true (fun ownerVal ownerPerm =>
          match getPath alg path ownerVal,
                acquirePerm .mutBorrow lid path ownerPerm with
          | some subVal, some ownerPerm' => some (subVal, ownerVal, ownerPerm')
          | _, _ => none) st0 with
        | some (subVal, st1) =>
          match ih st1 with
          | some (restTargets, restVals, st2) =>
            some ((owner, path) :: restTargets, subVal :: restVals, st2)
          | none => none
        | none => none)
    places st

/-- Replace an existing `RegionGroupEntry` with `entry.groupId` in `rgs`, or
append `entry` if `entry.groupId` does not yet appear in `rgs`, in a single
pass. -/
def upsertRegionGroup {Val : Type} (entry : RegionGroupEntry Val)
    (rgs : List (RegionGroupEntry Val)) : List (RegionGroupEntry Val) :=
  match
    rgs.foldr
      (fun g (acc : Bool × List (RegionGroupEntry Val)) =>
        match acc with
        | (found, rest) =>
          if g.groupId == entry.groupId then
            (true, entry :: rest)
          else
            (found, g :: rest))
      (false, [])
  with
  | (true, updated) => updated
  | (false, updated) => updated ++ [entry]

/-- True iff `xs` contains no repeated element. -/
def allDistinctNat (xs : List Nat) : Bool :=
  listFold true (fun x rest ih => !elemLoanId x rest && ih) xs

/-- Pre-installation record produced by Pass 1 of `installRegionGroups` after
all input places of every region group in the call have been resolved and
mutably locked in the pre-output state. -/
structure PreparedRegionGroup (Val : Type) where
  spec : RegionGroupSpec Val
  lockLid : LoanId
  inTargets : List (OwnerRef × SubPath)
  inMutVals : List Val
  outVals : List Val

/-- Install all region groups of a multi-region-group call into `st`. Rejects
reinstalling an already-active `groupId`, replaces any completed (inactive)
entry with the same `groupId` so repeated calls in a loop do not shadow newer
entries.

Each group locks its input places under `lockLid`, the next free loan ID.
When the group has outputs, its first output loan is allocated at that same
ID, so `lockLid` names that output loan, and the release list
`lockLid :: outputLoans` that `endRegionGroupInState` passes to
`writebackRegionTargets` names it twice. The duplicate is harmless: releasing
a loan's permission twice equals releasing it once, and the output loans are
retired (`.ended`) before the writeback, which requires that no live loan
carries `lockLid`. When a group has no outputs (`outLids.isEmpty`), an ended
lock-sentinel entry is appended to `st.loans` at `lockLid`, so that later
region groups or borrows never reuse `lockLid`.

All input places across every region group of the call are resolved and mutably
locked in Pass 1 before any group's output handles are bound into `outDsts` in
Pass 2, so a later group's `.derefSub` input resolves through the pre-call
handle local rather than an earlier group's newly written output handle.

A completed entry is not replaced while a group that was active before this
call lists its `groupId` in `requiredChildren`. That parent's outlives check
(`allRequiredGroupsEnded`) looks children up by `groupId`, and it consumes the
deposits tagged with that `groupId`, so a replacement would let it observe this
call's child instead of the child it was installed with. Installing a group
also fails while unconsumed deposits tagged with its `groupId` remain: no
active group may consume them (by the rule above), they must not reach a
parent of the new instance, and dropping them would lose a backward result
that `stateCleanAtReturn` would otherwise report.

All output destinations of the call must be distinct. Outputs are bound one
at a time, so a repeated destination would let a later handle overwrite an
earlier one while both output loans stay active.

Every `requiredChildren` entry must name a group of the same call, and no two
groups of the call may require the same child; see `takeChildDeposits`. -/
def installRegionGroups {Val : Type} (alg : ValAlgebra Val)
    (pureVals : List Val) (specs : List (RegionGroupSpec Val))
    (st : SymState Val) : Option (SymState Val) :=
  let allGids : List RegionGroupId := specs.map RegionGroupSpec.groupId
  let allDsts : List LocalId :=
    specs.foldr (fun spec acc => spec.outDsts ++ acc) []
  if !allDistinctNat allGids || !allDistinctNat allDsts then none
  else
    let pass1Opt : Option (List (PreparedRegionGroup Val) × SymState Val) :=
      listFold
        (β := Nat → SymState Val →
          Option (List (PreparedRegionGroup Val) × SymState Val))
        (fun _ st0 => some ([], st0))
        (fun spec _ ih nextLid st0 =>
          let alreadyActive : Bool :=
            match findRegionGroup spec.groupId st0.regionGroups with
            | some existing => existing.active
            | none => false
          let requiredByEarlierGroup : Bool :=
            st.regionGroups.any (fun g =>
              g.active && g.requiredChildren.any (fun c => c == spec.groupId))
          -- A parent's children must be groups of this same call, and no two
          -- groups of the call may share a child: a parent consumes its
          -- children's deposits, so a stale child from an earlier call or a
          -- second parent would observe the wrong deposits (or none).
          let childrenInCall : Bool :=
            spec.requiredChildren.all (fun c =>
              specs.any (fun other => other.groupId == c))
          let childShared : Bool :=
            specs.any (fun other =>
              other.groupId != spec.groupId &&
                other.requiredChildren.any (fun c =>
                  spec.requiredChildren.any (fun c' => c' == c)))
          let leftoverDeposits : Bool :=
            st0.regionDeposits.any (fun d => d.1 == spec.groupId)
          match alreadyActive || requiredByEarlierGroup || !childrenInCall ||
              childShared || leftoverDeposits with
          | true => none
          | false =>
            let lockLid := nextLid
            let span :=
              if spec.outDsts.isEmpty then 1 else spec.outDsts.length
            match acquireMutCallArgs alg lockLid spec.inputPlaces st0 with
            | none => none
            | some (inTargets, inMutVals, stLocked) =>
              match spec.fwdOuts pureVals inMutVals with
              | none => none
              | some outVals =>
                if outVals.length != spec.outDsts.length then none
                else
                  match ih (lockLid + span) stLocked with
                  | some (restPrep, stAllLocked) =>
                    let prep : PreparedRegionGroup Val :=
                      ⟨spec, lockLid, inTargets, inMutVals, outVals⟩
                    some (prep :: restPrep, stAllLocked)
                  | none => none)
        specs st.loans.length st
    match pass1Opt with
    | none => none
    | some (prepared, stAllLocked) =>
      listFold
        (β := SymState Val → Option (SymState Val))
        (fun st0 => some st0)
        (fun prep _ ih st0 =>
          let spec := prep.spec
          if st0.loans.length != prep.lockLid then none
          else
            match installRegionGroupOutputs alg spec.groupId prep.lockLid
                    prep.inTargets spec.outDsts prep.outVals st0 with
            | none => none
            | some (outLids, stWithOuts) =>
              let rgEntry : RegionGroupEntry Val :=
                ⟨spec.groupId, true, prep.lockLid, prep.inTargets, outLids,
                 spec.requiredChildren, spec.backFn pureVals prep.inMutVals⟩
              let stWithRg : SymState Val :=
                match stWithOuts with
                | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                  let loans' :=
                    if outLids.isEmpty then
                      let lockSentinel : LoanEntry Val :=
                        ⟨prep.lockLid, .ended, ⟨alg.defaultVal, .unborrowed⟩,
                         .regionOut spec.groupId 0⟩
                      loans ++ [lockSentinel]
                    else
                      loans
                  ⟨locals, loans', upsertRegionGroup rgEntry rgs, deps, sp, tag⟩
              ih stWithRg)
        prepared stAllLocked

/-- Construct the merged sub-value and `.choice` `BackTarget` for a shared
reborrow `&(*reg).extraPath` when `reg` holds a choice tree of shared-reference
handles `handle`. -/
def buildSharedChoiceBorrow {Val : Type} (alg : ValAlgebra Val)
    (extraPath : SubPath) (st : SymState Val) (handle : Val) :
    Option (Val × BackTarget Val) :=
  natFold (fun _ => none)
    (fun _ ih w =>
      match alg.decodeRef w with
      | some (lid, basePath) =>
        if !handleCopyable st.loans lid then none
        else
          let fullPath := basePath ++ extraPath
          match getOwnerForRead alg (.parentLoan lid) st fullPath with
          | some ⟨subVal, _⟩ =>
            some (subVal, .direct (.parentLoan lid) fullPath)
          | none => none
      | none =>
        match alg.branchSplit w with
        | none => none
        | some (cond, vt, vf) =>
          if !handleFreeVal alg cond then none
          else
            match alg.asBool cond with
            | some true => ih vt
            | some false => ih vf
            | none =>
              match ih vt, ih vf with
              | some (v1, t1), some (v2, t2) =>
                some (zipOrKeepSameRef alg cond v1 v2,
                      joinBackTarget cond t1 t2)
              | _, _ => none)
    (alg.sizeBound handle + 1) handle

/-- Acquire a shared borrow `&(*reg).extraPath` into `dst` when `reg` holds a
symbolic choice tree of shared-reference handles, locking all active parent
loan leaves under the new shared loan ID and installing a `.choice`
`BackTarget`. -/
def acquireSharedChoiceBorrow {Val : Type} (alg : ValAlgebra Val)
    (dst : LocalId) (reg : LocalId) (extraPath : SubPath)
    (st : SymState Val) : Option (SymState Val) :=
  match getOwnerForRead alg (.localReg reg) st [] with
  | none => none
  | some ⟨handle, _⟩ =>
    match alg.decodeRef handle with
    | some _ => none
    | none =>
      match buildSharedChoiceBorrow alg extraPath st handle with
      | none => none
      | some (_, target) =>
        if !validateSharedBackTarget alg target then none
        else
          let newLid := st.loans.length
          let leaves := dedupOwnerPaths (activeTargetLeaves alg target)
          let stLockedOpt : Option (SymState Val) :=
            leaves.foldr
              (fun op ih st0 =>
                match op with
                | (owner, path) =>
                  match modifyOwner alg owner false
                      (fun ownerVal ownerPerm =>
                        match acquirePerm .shared newLid path ownerPerm with
                        | some ownerPerm' => some (ownerVal, ownerPerm')
                        | none => none)
                      st0 with
                  | some st1 => ih st1
                  | none => none)
              (fun st0 => some st0)
              st
          match stLockedOpt with
          | some stLocked =>
            installNewLoanInLocal alg dst .activeShared target stLocked
          | none => none

/-- Primitive atomic action in a `FlowPlan`. -/
inductive PrimAction (Val : Type) where
  | assign (dst : PlaceExpr) (rhs : RvalOp Val)
  | borrow (dst : LocalId) (kind : BorrowKind) (src : PlaceExpr)
  | endLoan (lid : LoanId)
  | endLoanAtLocal (reg : LocalId)
  | call (dst : LocalId) (summary : CallSummary Val)
      (pureArgs : List (RvalOp Val)) (mutArgs : List PlaceExpr)
  | callMultiRegion (pureArgs : List (RvalOp Val))
      (groups : List (RegionGroupSpec Val))
  | endRegionGroup (gid : RegionGroupId)
  | freezeSpatial (lid : LoanId) (codec : SpatialCodec Val)
  | mutateSpatial (bid : BlockId) (tag : Nat) (cells : List (CellVal Val))
  | reabsorbSpatial (lid : LoanId) (codec : SpatialCodec Val)

/-- Execute a single `PrimAction` on `SymState Val`. -/
def stepAction {Val : Type} (alg : ValAlgebra Val)
    (act : PrimAction Val) (st : SymState Val) : EvalOutcome (SymState Val) :=
  match act with
  | .assign dst rhs =>
    match evalRval alg rhs st with
    | some v =>
      if !copyableVal alg st.loans v then .fail
      else
        match writePlaceVal alg dst v st with
        | some st' => .ok st'
        | none => .fail
    | none => .fail
  | .borrow dst kind src =>
    let reqMut : Bool :=
      match kind with
      | .shared => false
      | .mutBorrow => true
    match resolvePlaceForAccess alg reqMut src st with
    | none =>
      match kind, src with
      | .shared, .derefSub reg extraPath =>
        match acquireSharedChoiceBorrow alg dst reg extraPath st with
        | some st' => .ok st'
        | none => .fail
      | _, _ => .fail
    | some (owner, path) =>
      let newLid := st.loans.length
      match modifyOwner alg owner reqMut (fun ownerVal ownerPerm =>
        match acquirePerm kind newLid path ownerPerm with
        | some ownerPerm' => some (ownerVal, ownerPerm')
        | none => none) st with
      | none => .fail
      | some stLocked =>
        let phase : LoanPhase Val :=
          match kind with
          | .shared => .activeShared
          | .mutBorrow => .activeMut
        match installNewLoanInLocal alg dst phase
                (.direct owner path) stLocked with
        | some st' => .ok st'
        | none => .fail
  | .endLoan lid => endLoanInState alg lid st
  | .endLoanAtLocal reg =>
    match readLocalHandle alg reg st with
    | some (lid, _) => endLoanInState alg lid st
    | none => .fail
  | .call dst summary pureArgs mutArgs =>
    match evalRvalList alg pureArgs st with
    | none => .fail
    | some pureVals =>
      let newLid := st.loans.length
      match acquireMutCallArgs alg newLid mutArgs st with
      | none => .fail
      | some (targets, mutVals, stLocked) =>
        if summary.returnsMutBorrow then
          match installLensLoanInLocal alg dst targets
                  (summary.fwd pureVals) (summary.back pureVals)
                  stLocked with
          | some st' => .ok st'
          | none => .fail
        else
          match summary.fwd pureVals mutVals with
          | none => .fail
          | some retVal =>
            match summary.back pureVals mutVals retVal with
            | some updatedMutVals =>
              match writebackLensTargets alg newLid targets
                      updatedMutVals stLocked with
              | some stUnlocked =>
                -- A by-value result is stored like an assigned value.
                if !copyableVal alg stUnlocked.loans retVal then .fail
                else
                  match setLocalChecked alg dst retVal stUnlocked with
                  | some st' => .ok st'
                  | none => .fail
              | none => .fail
            | none => .fail
  | .callMultiRegion pureArgs groups =>
    match evalRvalList alg pureArgs st with
    | none => .fail
    | some pureVals =>
      match installRegionGroups alg pureVals groups st with
      | some st' => .ok st'
      | none => .fail
  | .endRegionGroup gid => endRegionGroupInState alg gid st
  | .freezeSpatial lid codec => freezeToSpatialInState alg lid codec st
  | .mutateSpatial bid tag cells => mutateSpatialInState bid tag cells st
  | .reabsorbSpatial lid codec => reabsorbFromSpatialInState alg lid codec st

/-- Merge two value lists under symbolic branch condition `cond`. -/
def zipValList {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (xs ys : List Val) : List Val :=
  listFold
    (fun bs => bs)
    (fun x _ ih bs =>
      match bs with
      | [] => x :: ih []
      | y :: ys' => zipOrKeepSameRef alg cond x y :: ih ys')
    xs ys

/-- Project a list of branch-joined values to branch `branch` (`true` or
`false`) under condition `cond` (`ValAlgebra.getField_projectBranchVal`
guarantees that `alg.projectBranchVal` commutes with `alg.getField` through
aggregate fields). -/
def projectBranchValList {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (branch : Bool) (xs : List Val) : List Val :=
  listFold []
    (fun v _ ih => alg.projectBranchVal cond branch v :: ih)
    xs

/-- Join two local `PlaceCell` lists across a conditional branch join, merging
the locals that both branches hold. A local written in only one branch may be
uninitialized after the join, so it is dropped (making later reads fail)
instead of being merged with a synthetic `alg.defaultVal`. Dropping is only
sound if nothing borrows that local, so the join fails (`none`) when such a
branch-only local has a non-`.unborrowed` permission. -/
def joinPlaceCells {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (cs1 cs2 : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  let allUnborrowed (cs : List (PlaceCell Val)) : Bool :=
    listFold true (fun c _ ih => isUnborrowed c.perm && ih) cs
  listFold
    (fun bs => if allUnborrowed bs then some [] else none)
    (fun c1 rest ih bs =>
      match bs with
      | [] => if allUnborrowed (c1 :: rest) then some [] else none
      | c2 :: cs2' =>
        match ih cs2' with
        | some tail =>
          some (⟨zipOrKeepSameRef alg cond c1.val c2.val,
                 unionPerm c1.perm c2.perm⟩ :: tail)
        | none => none)
    cs1 cs2

/-- True iff every loan entry in `es` is a fully ended branch-local loan
(with `.ended` phase, `.unborrowed` cell permissions, and not a root
parameter). Ended region-output loans (including lock sentinels) are allowed:
an ended loan is never written back again, and `joinRegionGroups` rejects any
branch-local region group that is still active, so these loans belong to
groups that ended inside the branch. -/
def allEndedBranchLocalLoans {Val : Type}
    (es : List (LoanEntry Val)) : Bool :=
  listFold true
    (fun e _ ih =>
      e.phase.isEnded && isUnborrowed e.cell.perm &&
      !isRootParamTarget e.target && ih)
    es

/-- Join two loan lists across a diamond branch join, synthesizing `.choice`
writeback targets when a loan's target differs between branches and preserving
trailing branch-local loans that were created and ended within one arm. -/
def joinLoanEntries {Val : Type} (alg : ValAlgebra Val)
    (cond : Val) (es1 es2 : List (LoanEntry Val)) :
    Option (List (LoanEntry Val)) :=
  listFold
    (fun bs =>
      if allEndedBranchLocalLoans bs then some bs else none)
    (fun e1 rest1 ih bs =>
      match bs with
      | [] =>
        if allEndedBranchLocalLoans (e1 :: rest1) then
          some (e1 :: rest1)
        else
          none
      | e2 :: es2' =>
        if e1.id == e2.id && e1.phase.samePhase e2.phase then
          match ih es2' with
          | some rest =>
            let mergedEntry : LoanEntry Val :=
              ⟨e1.id, e1.phase,
                ⟨zipOrKeepSameRef alg cond e1.cell.val e2.cell.val,
                 unionPerm e1.cell.perm e2.cell.perm⟩,
                joinBackTarget cond e1.target e2.target⟩
            some (mergedEntry :: rest)
          | none => none
        else none)
    es1 es2

/-- Structural equality on `List (OwnerRef × SubPath)`. -/
def ownerPathListEq (xs ys : List (OwnerRef × SubPath)) : Bool :=
  listFold
    (fun bs =>
      match bs with
      | [] => true
      | _ :: _ => false)
    (fun a _ ih bs =>
      match a, bs with
      | (o1, p1), (o2, p2) :: bs' =>
        OwnerRef.beq o1 o2 && subPathEq p1 p2 && ih bs'
      | _, _ => false)
    xs ys

/-- Join two region-group tables across a diamond branch join. Entries are
paired by position:
- Two active entries must agree on all structural metadata (`groupId`,
  `lockLid`, `inputTargets`, `outputLoans`, `requiredChildren`); their
  `backFn` closures are merged under `cond` after projecting `outVals` and
  `deps` to each branch via `projectBranchValList`.
- Two inactive entries need only agree on `groupId`: a completed group's
  metadata is never consulted again, so a branch that reinstalled and ended the
  group may differ from one that did not.
- Trailing entries present in only one branch are kept if they are inactive
  and no active group requires them. Such a group was installed and ended
  inside that branch; requiring absence of an active parent keeps the join
  from reporting a child as ended that the other branch never ran. Where the
  arms' entries first differ in `groupId`, both arms appended different
  groups, and both tails are kept under the same condition.

Any deposits left by a branch-local group make the deposit lists differ, which
`joinRegionDeposits` rejects. -/
def joinRegionGroups {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (gs1 gs2 : List (RegionGroupEntry Val)) :
    Option (List (RegionGroupEntry Val)) :=
  -- Active entries can only be paired with equal active entries, so the
  -- active groups of `gs1` are those of the joined table.
  let branchLocalOk (g : RegionGroupEntry Val) : Bool :=
    !g.active &&
      !gs1.any (fun a =>
        a.active && a.requiredChildren.any (fun c => c == g.groupId))
  listFold
    (fun bs => if bs.all branchLocalOk then some bs else none)
    (fun g1 rest1 ih bs =>
      match bs with
      | [] =>
        if (g1 :: rest1).all branchLocalOk then some (g1 :: rest1) else none
      | g2 :: gs2' =>
        if g1.groupId == g2.groupId && !g1.active && !g2.active then
          match ih gs2' with
          | some rest => some (g1 :: rest)
          | none => none
        -- Different groups at the same position: the arms appended different
        -- branch-local groups (installs append new IDs), so everything from
        -- here on in both arms is branch-local. Keep both arms' entries.
        else if g1.groupId != g2.groupId &&
                (g1 :: rest1).all branchLocalOk && bs.all branchLocalOk then
          some ((g1 :: rest1) ++
            bs.filter (fun g =>
              !(g1 :: rest1).any (fun h => h.groupId == g.groupId)))
        else if g1.groupId == g2.groupId &&
           g1.active == g2.active &&
           g1.lockLid == g2.lockLid &&
           ownerPathListEq g1.inputTargets g2.inputTargets &&
           loanIdListEq g1.outputLoans g2.outputLoans &&
           loanIdListEq g1.requiredChildren g2.requiredChildren then
          match ih gs2' with
          | some rest =>
            let mergedBack :
                List Val → List Val → Option (List Val × List Val) :=
              fun outVals deps =>
                let outT := projectBranchValList alg cond true outVals
                let depsT := projectBranchValList alg cond true deps
                let outF := projectBranchValList alg cond false outVals
                let depsF := projectBranchValList alg cond false deps
                match alg.asBool cond with
                | some true => g1.backFn outT depsT
                | some false => g2.backFn outF depsF
                | none =>
                  match g1.backFn outT depsT, g2.backFn outF depsF with
                  | some (inUpd1, depUpd1), some (inUpd2, depUpd2) =>
                    if inUpd1.length == inUpd2.length &&
                       depUpd1.length == depUpd2.length then
                      some (zipValList alg cond inUpd1 inUpd2,
                            zipValList alg cond depUpd1 depUpd2)
                    else none
                  | _, _ => none
            let gMerged : RegionGroupEntry Val :=
              ⟨g1.groupId, g1.active, g1.lockLid, g1.inputTargets,
               g1.outputLoans, g1.requiredChildren, mergedBack⟩
            some (gMerged :: rest)
          | none => none
        else none)
    gs1 gs2

/-- Remove the first deposit tagged with `gid` from `ds`, returning its value
and the remaining deposits in their original order. -/
def popFirstDepositForGroup {Val : Type} (gid : RegionGroupId)
    (ds : List (RegionGroupId × Val)) :
    Option (Val × List (RegionGroupId × Val)) :=
  listFold none
    (fun d tail ih =>
      if d.1 == gid then some (d.2, tail)
      else
        match ih with
        | some (v, rest) => some (v, d :: rest)
        | none => none)
    ds

/-- Join two tagged deposit lists across a conditional branch join. Both
branches must hold the same multiset of producer `groupId`s; deposits from the
same producer are paired in FIFO order (matching `takeChildDeposits`) even when
independent child region groups ended in different orders across the two
branches, and their values are merged under `cond`. -/
def joinRegionDeposits {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (ds1 ds2 : List (RegionGroupId × Val)) :
    Option (List (RegionGroupId × Val)) :=
  listFold
    (fun bs =>
      match bs with
      | [] => some []
      | _ :: _ => none)
    (fun d1 _ ih bs =>
      match popFirstDepositForGroup d1.1 bs with
      | some (v2, bs') =>
        match ih bs' with
        | some rest =>
          some ((d1.1, zipOrKeepSameRef alg cond d1.2 v2) :: rest)
        | none => none
      | none => none)
    ds1 ds2

/-- Join two symbolic states across a conditional diamond branch, requiring
matching `regionDeposits` producers (`joinRegionDeposits`) and taking the
maximum of `st1.nextSpatialTag` and `st2.nextSpatialTag` so spatial provenance
tags remain fresh relative to both branch histories. -/
def joinSymState {Val : Type} (alg : ValAlgebra Val) (cond : Val)
    (st1 st2 : SymState Val) : Option (SymState Val) :=
  if !st1.spatial.isEmpty || !st2.spatial.isEmpty then
    none
  else
    match joinLoanEntries alg cond st1.loans st2.loans,
          joinRegionGroups alg cond st1.regionGroups st2.regionGroups,
          joinRegionDeposits alg cond st1.regionDeposits st2.regionDeposits with
    | some loans', some rgs', some deps' =>
      let nextTag :=
        if decide (st1.nextSpatialTag ≤ st2.nextSpatialTag) then
          st2.nextSpatialTag
        else
          st1.nextSpatialTag
      match joinPlaceCells alg cond st1.locals st2.locals with
      | some locals' =>
        some ⟨locals',
              loans',
              rgs',
              deps',
              [],
              nextTag⟩
      | none => none
    | _, _, _ => none

def listContainsLoanId (lid : LoanId) (xs : List LoanId) : Bool :=
  elemLoanId lid xs

/-- Verify that an explicit list of branch join pairs `(trueLid, falseLid)`
does not duplicate any loan identifier across joined outputs, preventing
aliasing of mutable ownership at a branch merge. -/
def validJoinPairs (pairs : List (LoanId × LoanId))
    (seenT seenF : List LoanId) : Bool :=
  listFold
    (fun _ _ => true)
    (fun pair _ ih sT sF =>
      match pair with
      | (tLid, fLid) =>
        if listContainsLoanId tLid sT || listContainsLoanId fLid sF then
          false
        else
          ih (tLid :: sT) (fLid :: sF))
    pairs seenT seenF

/-- Rename parent loan references from `oldLid` to `newLid` inside an
`OwnerRef`. -/
def renameOwnerLoan (oldLid newLid : LoanId) : OwnerRef → OwnerRef
  | .localReg reg => .localReg reg
  | .parentLoan lid => .parentLoan (if lid == oldLid then newLid else lid)

/-- Swap parent loan references `lidA` and `lidB` inside an `OwnerRef`. -/
def swapOwnerLoan (lidA lidB : LoanId) : OwnerRef → OwnerRef
  | .localReg reg => .localReg reg
  | .parentLoan lid =>
    .parentLoan
      (if lid == lidA then lidB else if lid == lidB then lidA else lid)

/-- True iff `v` may contain a handle to loan `lid` (or nests too deeply to
tell; see `collectHandles`). -/
def mayMentionLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (v : Val) : Bool :=
  match collectHandles alg v with
  | some lids => elemLoanId lid lids
  | none => true

/-- The loan and sub-path of every borrow handle in `v`, with multiplicity,
listing every field and both arms of every choice in full; or `none` if `v`
nests more deeply than its traversal budget `alg.sizeBound v + 1`. Unlike
`collectHandles`, it does not merge arms, since it describes the value's
structure rather than one branch. -/
def handleRefs {Val : Type} (alg : ValAlgebra Val) (v : Val) :
    Option (List (LoanId × SubPath)) :=
  natFold (fun _ => none)
    (fun _ ih w =>
      match alg.decodeRef w with
      | some r => some [r]
      | none =>
        let fromFields : Option (List (LoanId × SubPath)) :=
          natFold (some [])
            (fun idx acc =>
              match acc, alg.getField idx w with
              | some ls, some field =>
                match ih field with
                | some ls' => some (ls ++ ls')
                | none => none
              | some ls, none => some ls
              | none, _ => none)
            (alg.sizeBound w)
        let fromArms : Option (List (LoanId × SubPath)) :=
          match alg.branchSplit w with
          | none => some []
          | some (_, vt, vf) =>
            match ih vt, ih vf with
            | some lt, some lf => some (lt ++ lf)
            | _, _ => none
        match fromFields, fromArms with
        | some ls, some ls' => some (ls ++ ls')
        | _, _ => none)
    (alg.sizeBound v + 1) v

/-- `rs` with the first occurrence of `r` removed, or `none` if `r` does not
occur. -/
def removeOneRef (r : LoanId × SubPath) (rs : List (LoanId × SubPath)) :
    Option (List (LoanId × SubPath)) :=
  listFold none
    (fun x rest ih =>
      if x.1 == r.1 && subPathEq x.2 r.2 then some rest
      else
        match ih with
        | some rest' => some (x :: rest')
        | none => none)
    rs

/-- True iff `xs` and `ys` hold the same handles with the same multiplicity. -/
def sameRefMultiset (xs ys : List (LoanId × SubPath)) : Bool :=
  match
    xs.foldr
      (fun x acc =>
        match acc with
        | some rest => removeOneRef x rest
        | none => none)
      (some ys)
  with
  | some [] => true
  | _ => false

/-- Rename handles to loan `fLid` to `tLid` inside `v` (including handles nested
in fields and choice arms) using `alg.remapRefInVal`, or `none` if the result
is not that renaming.

The `ValAlgebra` laws for `remapRefInVal` fix everything about the result that
`decodeRef`, `getField`, and `branchSplit` observe: a handle to `fLid` becomes
a handle to `tLid` with the same sub-path, other handles are kept, fields and
the guards and arms of choices are renamed recursively, and a value with none
of these is unchanged. The check below confirms the part that borrow tracking
depends on at run time: the result's handles (`handleRefs`, loan and sub-path,
with multiplicity) must be exactly those of `v` with `fLid` replaced by
`tLid`, and the check fails closed if either scan exceeds its depth budget.

Neither the laws nor the check constrain data that those three operations do
not expose, such as an aggregate's tag or what a handle records besides its
loan and sub-path (for `mirValAlg`, its mutability, generation, and reborrow
depth). An algebra that changed such data while renaming would make the
renamed state describe a different machine state from the one that the
program reached. That cannot make a verified conclusion false: a conclusion
about a machine follows only from `pure_lift_sound`, whose simulation
hypothesis `hSim` must relate the lifted result to an actual machine run, so an
unfaithful algebra leaves `hSim` unprovable rather than the conclusion
unsound. -/
def remapValLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (v : Val) : Option Val :=
  let v' := alg.remapRefInVal fLid tLid v
  match handleRefs alg v, handleRefs alg v' with
  | some rs, some rs' =>
    if sameRefMultiset
        (rs.map (fun r => (if r.1 == fLid then tLid else r.1, r.2))) rs'
    then some v'
    else none
  | _, _ => none

/-- `remapValLoan` across a list of values, failing if any value fails. -/
def remapValListLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (vals : List Val) : Option (List Val) :=
  vals.foldr
    (fun u acc =>
      match remapValLoan alg fLid tLid u, acc with
      | some u', some rest => some (u' :: rest)
      | _, _ => none)
    (some [])

/-- Wrap a backward function written for the state before renaming loan
`oldLid` to `newLid`, so that it works on values after the renaming: inputs are
renamed back (`newLid` to `oldLid`) and outputs forward.

The renaming swaps the two IDs (`renameLoanInState`), but each direction needs
only one of them. After the renaming, `oldLid` names an ended placeholder that
no value refers to, and before it `newLid` named such an ended loan; so a value
after the renaming should hold no handle to `oldLid`, and an output before it
none to `newLid`. The wrapper rejects such a value rather than mapping it
wrongly. -/
def renameClosureVals {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) (inputs : List Val)
    (run : List Val → Option (List Val)) : Option (List Val) :=
  if inputs.any (mayMentionLoan alg oldLid) then none
  else
    match remapValListLoan alg newLid oldLid inputs with
    | none => none
    | some inputsOld =>
      match run inputsOld with
      | none => none
      | some outs =>
        if outs.any (mayMentionLoan alg newLid) then none
        else remapValListLoan alg oldLid newLid outs

def mapBackTargetStepLoan {Val : Type} (alg : ValAlgebra Val)
    (mapOwner : OwnerRef → OwnerRef) (oldLid newLid : LoanId) :
    BackTargetStep Val → Option (BackTargetStep Val)
  | .rootParam i => some (.rootParam i)
  | .direct o p => some (.direct (mapOwner o) p)
  | .choiceJoin cond =>
    match remapValLoan alg oldLid newLid cond with
    | some cond' => some (.choiceJoin cond')
    | none => none
  | .lensCall targets backFn =>
    let targets' :=
      listFold []
        (fun op _ ih =>
          match op with
          | (o, p) => (mapOwner o, p) :: ih)
        targets
    let backFn' : Val → Option (List Val) :=
      fun v =>
        renameClosureVals alg oldLid newLid [v] (fun vs =>
          match vs with
          | [vOld] => backFn vOld
          | _ => none)
    some (.lensCall targets' backFn')
  | .regionOut gid idx => some (.regionOut gid idx)

def renameBackTargetStepLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) :
    BackTargetStep Val → Option (BackTargetStep Val) :=
  mapBackTargetStepLoan alg (renameOwnerLoan oldLid newLid) oldLid newLid

def mapBackTargetLoan {Val : Type} (alg : ValAlgebra Val)
    (mapOwner : OwnerRef → OwnerRef) (oldLid newLid : LoanId)
    (target : BackTarget Val) : Option (BackTarget Val) :=
  match
    target.steps.foldr
      (fun s acc =>
        match mapBackTargetStepLoan alg mapOwner oldLid newLid s, acc with
        | some s', some rest => some (s' :: rest)
        | _, _ => none)
      (some [])
  with
  | some steps => some ⟨steps⟩
  | none => none

/-- Rename parent loan references and handles from `oldLid` to `newLid` inside
a `BackTarget Val`, or `none` if a condition's renaming fails
(`remapValLoan`). -/
def renameBackTargetLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) (target : BackTarget Val) :
    Option (BackTarget Val) :=
  mapBackTargetLoan alg (renameOwnerLoan oldLid newLid) oldLid newLid target

/-- Swap parent loan references `fLid ↔ tLid` and remap value handles
`fLid → tLid` inside a `BackTarget Val`, or `none` if a condition's renaming
fails (`remapValLoan`). -/
def swapBackTargetLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (target : BackTarget Val) :
    Option (BackTarget Val) :=
  mapBackTargetLoan alg (swapOwnerLoan fLid tLid) fLid tLid target

/-- Remap handles (`remapValLoan`) and `PermTree` loan IDs from `fLid` to
`tLid` across a list of `PlaceCell Val`s, failing if any value fails. -/
def remapPlaceCellsLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (cells : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  cells.foldr
    (fun c acc =>
      match remapValLoan alg fLid tLid c.val, acc with
      | some v', some rest =>
        some (⟨v', renameLoanPerm fLid tLid c.perm⟩ :: rest)
      | _, _ => none)
    (some [])

/-- Rename loan references from `oldLid` to `newLid` inside a
`RegionGroupEntry Val`, wrapping its backward function with the same checks
as `renameClosureVals`: outputs and deposits are renamed back before the
call, and the results forward after it. -/
def renameRegionGroupLoan {Val : Type} (alg : ValAlgebra Val)
    (oldLid newLid : LoanId) (g : RegionGroupEntry Val) :
    RegionGroupEntry Val :=
  let lockLid' := if g.lockLid == oldLid then newLid else g.lockLid
  let targets' :=
    listFold []
      (fun op _ ih =>
        match op with
        | (o, p) => (renameOwnerLoan oldLid newLid o, p) :: ih)
      g.inputTargets
  let outLoans' :=
    listFold []
      (fun lid _ ih => (if lid == oldLid then newLid else lid) :: ih)
      g.outputLoans
  let backFn' : List Val → List Val → Option (List Val × List Val) :=
    fun outs deps =>
      if (outs ++ deps).any (mayMentionLoan alg oldLid) then none
      else
        match remapValListLoan alg newLid oldLid outs,
            remapValListLoan alg newLid oldLid deps with
        | some outsOld, some depsOld =>
          match g.backFn outsOld depsOld with
          | some (inUpd, depUpd) =>
            if (inUpd ++ depUpd).any (mayMentionLoan alg newLid) then none
            else
              match remapValListLoan alg oldLid newLid inUpd,
                  remapValListLoan alg oldLid newLid depUpd with
              | some inUpd', some depUpd' => some (inUpd', depUpd')
              | _, _ => none
          | none => none
        | _, _ => none
  ⟨g.groupId, g.active, lockLid', targets', outLoans',
   g.requiredChildren, backFn'⟩

/-- True iff some local, loan cell, region deposit, or spatial block of `st`
may hold a handle to loan `lid`. -/
def staleHandleTo {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (st : SymState Val) : Bool :=
  st.locals.any (fun c => mayMentionLoan alg lid c.val) ||
    st.loans.any (fun e => mayMentionLoan alg lid e.cell.val) ||
    st.regionDeposits.any (fun d => mayMentionLoan alg lid d.2) ||
    st.spatial.any (fun b =>
      b.cells.any (fun cell =>
        match cell with
        | .init v => mayMentionLoan alg lid v
        | .uninit => false
        | .rawByte _ => true)) ||
    st.loans.any (fun e =>
      match e.phase with
      | .spatialPinned bid pinnedCodec =>
        match findSpatialBlock st.spatial bid with
        | some (blk, _) =>
          match pinnedCodec.decode blk.cells with
          | some vDec => mayMentionLoan alg lid vDec
          | none => true
        | none => true
      | _ => false)

/-- True iff `target` holds an active owner edge to `lid`
(`activeTargetLeaves`) or mentions `lid` in any `.choiceJoin` condition.
Untaken arms of concrete choices are pruned for owner edges (matching
`noActiveChildLoanEdgesIn`), while symbolic or malformed choices still inspect
all branches. -/
def backTargetMentionsLoan {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val) : Bool :=
  hasParentLoanEdge lid (activeTargetLeaves alg target) ||
    target.steps.any (fun s =>
      match s with
      | .choiceJoin cond => mayMentionLoan alg lid cond
      | _ => false)

/-- True iff loan `lid` still carries a value or structural reference in `st`:
a handle in locals/loans/deposits/spatial cells (`staleHandleTo`), a local or
loan `PermTree` entry (`!noResidualLoanPerm`), a non-ended loan's `BackTarget`,
an active `RegionGroupEntry` (`lockLid`, `outputLoans`, or `inputTargets`), or a
`SpatialBlock.originLoan`. -/
def loanIdReferencedInState {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (st : SymState Val) : Bool :=
  staleHandleTo alg lid st ||
    !noResidualLoanPerm lid st ||
    st.loans.any (fun e =>
      !e.phase.isEnded && backTargetMentionsLoan alg lid e.target) ||
    st.regionGroups.any (fun g =>
      g.active &&
        (g.lockLid == lid ||
          elemLoanId lid g.outputLoans ||
          hasParentLoanEdge lid g.inputTargets)) ||
    st.spatial.any (fun b => b.originLoan == lid)

/-- Remap handles to `fLid` to `tLid` inside a spatial cell (`remapValLoan` on
`.init v`). -/
def remapCellValLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (c : CellVal Val) : Option (CellVal Val) :=
  match c with
  | .init v =>
    match remapValLoan alg fLid tLid v with
    | some v' => some (.init v')
    | none => none
  | .uninit => some .uninit
  | .rawByte b => some (.rawByte b)

/-- Remap `originLoan` and `.init` cell values from `fLid` to `tLid` in a
spatial block. -/
def remapSpatialBlockLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (b : SpatialBlock Val) :
    Option (SpatialBlock Val) :=
  let origin' := if b.originLoan == fLid then tLid else b.originLoan
  match
    b.cells.foldr
      (fun c acc =>
        match remapCellValLoan alg fLid tLid c, acc with
        | some c', some rest => some (c' :: rest)
        | _, _ => none)
      (some [])
  with
  | some cells' =>
    some ⟨b.blockId, origin', b.perm, b.provenanceTag,
          b.activeSubSplits, cells'⟩
  | none => none

/-- Remap every spatial block in `blocks` from `fLid` to `tLid`. -/
def remapSpatialBlocksLoan {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (blocks : List (SpatialBlock Val)) :
    Option (List (SpatialBlock Val)) :=
  blocks.foldr
    (fun b acc =>
      match remapSpatialBlockLoan alg fLid tLid b, acc with
      | some b', some rest => some (b' :: rest)
      | _, _ => none)
    (some [])

/-- Verify that after remapping `fLid` to `tLid`, every `.spatialPinned` loan's
spatial block either decodes under its `pinnedCodec` to the exact remapped
handle multiset of its pre-rename decoded value AND preserves the full handle
multiset across every `.init` cell (`collectInitCells (handleRefs alg)`), or
(when the block is partially uninitialized or undecodable) neither the pinned
loan cell nor the block mentions `fLid` or contains `.rawByte` cells. -/
def spatialPinnedRenameConsistent {Val : Type} (alg : ValAlgebra Val)
    (fLid tLid : LoanId) (loans : List (LoanEntry Val))
    (spOld spNew : List (SpatialBlock Val)) : Bool :=
  loans.all (fun e =>
    match e.phase with
    | .spatialPinned bid pinnedCodec =>
      match findSpatialBlock spOld bid, findSpatialBlock spNew bid with
      | some (blkOld, _), some (blkNew, _) =>
        if !hasUninitCell blkOld.cells then
          match pinnedCodec.decode blkOld.cells,
              pinnedCodec.decode blkNew.cells,
              collectInitCells (handleRefs alg) blkOld.cells,
              collectInitCells (handleRefs alg) blkNew.cells with
          | some vOld, some vNew, some csOld, some csNew =>
            match handleRefs alg vOld, handleRefs alg vNew with
            | some rsOld, some rsNew =>
              sameRefMultiset
                (rsOld.map (fun r =>
                  (if r.1 == fLid then tLid else r.1, r.2)))
                rsNew &&
              sameRefMultiset
                (csOld.map (fun r =>
                  (if r.1 == fLid then tLid else r.1, r.2)))
                csNew
            | _, _ => false
          | _, _, _, _ => false
        else
          !mayMentionLoan alg fLid e.cell.val &&
            blkOld.cells.all (fun c =>
              match c with
              | .init v => !mayMentionLoan alg fLid v
              | .uninit => true
              | .rawByte _ => false)
      | _, _ => false
    | _ => true)

/-- Append ended placeholder loans to `st` so that every loan ID up to `upTo`
exists. Loan IDs are allocated as `st.loans.length`, so the placeholders take
the IDs another branch may have used for scratch borrows. An ended loan is
never read, written back, or ended again, so a placeholder carries no
obligation. -/
def padEndedLoans {Val : Type} (alg : ValAlgebra Val) (upTo : LoanId)
    (st : SymState Val) : SymState Val :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    let extra : List (LoanEntry Val) :=
      natFold []
        (fun i acc =>
          acc ++ [⟨loans.length + i, .ended, ⟨alg.defaultVal, .unborrowed⟩,
                   .direct (.localReg 0) []⟩])
        (upTo + 1 - loans.length)
    ⟨locals, loans ++ extra, rgs, deps, sp, tag⟩

/-- Move loan `fLid` (live or ended) of `stIn` to the ID `tLid`, where `tLid`
names an ended loan of `stIn` with no remaining value or structural references
(`loanIdReferencedInState`). If `tLid` lies beyond `stIn`'s loans, `stIn` is
first padded with ended placeholders (`padEndedLoans`). Every reference to
`fLid` (locals, loan cells, permissions, `BackTarget`s, region groups,
deposits, and spatial blocks) is remapped to `tLid`,
the entry at `fLid` moves to `tLid`, and the ended entry formerly at `tLid`
moves to `fLid`, where nothing refers to it any more. Every renamed value is
checked to be exactly that renaming (`remapValLoan`), so the result is a
consistent relabeling of `stIn` and is valid on its own; explicit branch joins
use it to give both arms' loans a common ID (`relabelJoinLoans`). Root
parameter loans are never renamed: their `.rootParam` target records the
caller's parameter, and renaming would drop that writeback obligation. -/
def renameLoanInState {Val : Type} (alg : ValAlgebra Val)
    (tLid fLid : LoanId) (stIn : SymState Val) : Option (SymState Val) :=
  if tLid == fLid then some stIn
  else
    let st : SymState Val :=
      if decide (stIn.loans.length ≤ tLid) then padEndedLoans alg tLid stIn
      else stIn
    match findLoan fLid st.loans, findLoan tLid st.loans with
    | some eF, some eT =>
      if !hasUniqueLoanId fLid st.loans || !hasUniqueLoanId tLid st.loans ||
         isRootTarget eF.target || isRootTarget eT.target ||
         !eT.phase.isEnded then none
      -- Any surviving value handle, permission lock, live backward target,
      -- active region lock/edge, or spatial origin on `tLid` would bind to
      -- the moved entry.
      else if loanIdReferencedInState alg tLid st then none
      else
        match st with
        | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
          let renameEntry (e : LoanEntry Val) (newId : LoanId) :
              Option (LoanEntry Val) :=
            match remapValLoan alg fLid tLid e.cell.val,
                swapBackTargetLoan alg fLid tLid e.target with
            | some v', some t' =>
              some ⟨newId, e.phase, ⟨v', renameLoanPerm fLid tLid e.cell.perm⟩,
                t'⟩
            | _, _ => none
          let clearedEntry : Option (LoanEntry Val) :=
            if handleFreeVal alg alg.defaultVal then
              some ⟨fLid, .ended, ⟨alg.defaultVal, .unborrowed⟩,
                    .direct (.localReg 0) []⟩
            else
              match remapValLoan alg fLid tLid eT.cell.val,
                  swapBackTargetLoan alg fLid tLid eT.target with
              | some vT, some tT =>
                some ⟨fLid, .ended, ⟨vT, .unborrowed⟩, tT⟩
              | _, _ => none
          let loans' : Option (List (LoanEntry Val)) :=
            loans.foldr
              (fun e acc =>
                match acc with
                | none => none
                | some rest =>
                  if e.id == tLid then
                    match renameEntry eF tLid with
                    | some moved => some (moved :: rest)
                    | none => none
                  else if e.id == fLid then
                    match clearedEntry with
                    | some c => some (c :: rest)
                    | none => none
                  else
                    match renameEntry e e.id with
                    | some e' => some (e' :: rest)
                    | none => none)
              (some [])
          let rgs' :=
            listFold []
              (fun g _ ih => renameRegionGroupLoan alg fLid tLid g :: ih)
              rgs
          let deps' : Option (List (RegionGroupId × Val)) :=
            deps.foldr
              (fun d acc =>
                match remapValLoan alg fLid tLid d.2, acc with
                | some v', some rest => some ((d.1, v') :: rest)
                | _, _ => none)
              (some [])
          match remapPlaceCellsLoan alg fLid tLid locals, loans', deps',
              remapSpatialBlocksLoan alg fLid tLid sp with
          | some locals', some loans'', some deps'', some sp' =>
            if !spatialPinnedRenameConsistent alg fLid tLid loans sp sp' then
              none
            else
              some ⟨locals', loans'', rgs', deps'', sp', tag⟩
          | _, _, _, _ => none
    | _, _ => none

/-- The larger of `a` and `b`. -/
def maxLoanId (a b : LoanId) : LoanId :=
  if decide (a ≤ b) then b else a

/-- A loan ID that is at least `floor` and above every ID in `pairs`. -/
def joinPairsFreshBase (pairs : List (LoanId × LoanId)) (floor : LoanId) :
    LoanId :=
  pairs.foldr (fun p acc => maxLoanId (maxLoanId (p.1 + 1) (p.2 + 1)) acc)
    floor

/-- Rename the loans of `st` by the explicit join pairs `pairs`, one pair at a
time: each pair `(tLid, fLid)` gives the live loan that `st` holds at `fLid`
the ID `tLid`, and a pair with `tLid = fLid` changes nothing. The pairs must
not repeat an ID on either side (`validJoinPairs`), and `base` must exceed
every loan ID that `st` or `pairs` uses (`joinPairsFreshBase`).

A pair moves its loan directly (`renameLoanInState`) if `tLid` is free. If
`tLid` is occupied, its loan first moves to the fresh ID `base + i` (for the
`i`-th pair), together with every reference to it, provided that the loan is
- an ended loan that something still refers to, such as a dead handle left in
  a local (as in MIR before `StorageDead`) or the lock sentinel of an active
  output-free region group, or
- a live loan that a later pair moves; that pair then finds it at the fresh
  ID, so the pairs may exchange loans, as in `[(2, 3), (3, 2)]`.
Any other occupant makes the renaming fail. Fresh IDs remain afterwards as
ended loans. -/
def relabelJoinLoans {Val : Type} (alg : ValAlgebra Val)
    (pairs : List (LoanId × LoanId)) (base : LoanId) (st : SymState Val) :
    Option (SymState Val) :=
  -- `moved` maps the original ID of each live loan moved to a fresh ID to
  -- that fresh ID.
  listFold
    (β := Nat → List (LoanId × LoanId) → SymState Val →
      Option (SymState Val))
    (fun _ _ s => some s)
    (fun p rest ih i moved s =>
      match p with
      | (tLid, fLid) =>
        if tLid == fLid then ih (i + 1) moved s
        else
          let src : LoanId :=
            match moved.find? (fun m => m.1 == fLid) with
            | some m => m.2
            | none => fLid
          match findLoan src s.loans with
          | none => none
          | some eF =>
            if !eF.phase.isActive then none
            else
              match renameLoanInState alg tLid src s with
              | some s' => ih (i + 1) moved s'
              | none =>
                -- `tLid` is occupied (or the move is invalid, in which case
                -- the retry below fails the same way).
                match findLoan tLid s.loans with
                | none => none
                | some eT =>
                  let movedLater : Bool :=
                    rest.any (fun q => q.1 != q.2 && q.2 == tLid)
                  if !eT.phase.isEnded && !(eT.phase.isActive && movedLater)
                  then none
                  else
                    match renameLoanInState alg (base + i) tLid s with
                    | none => none
                    | some s1 =>
                      match renameLoanInState alg tLid src s1 with
                      | none => none
                      | some s2 =>
                        let moved' : List (LoanId × LoanId) :=
                          if eT.phase.isActive then (tLid, base + i) :: moved
                          else moved
                        ih (i + 1) moved' s2)
    pairs 0 [] st

/-- True iff the explicit join pair `(tLid, fLid)` fits the arms: the true
arm `st1` has a live loan `tLid`, the false arm `st2` has a loan `fLid` in the
same phase, and a pair that renames (`tLid ≠ fLid`) does not target a root
parameter loan. -/
def joinPairFits {Val : Type} (tLid fLid : LoanId) (st1 st2 : SymState Val) :
    Bool :=
  match findLoan tLid st1.loans, findLoan fLid st2.loans with
  | some e1, some e2 =>
    e1.phase.isActive && e1.phase.samePhase e2.phase &&
      (tLid == fLid || !isRootTarget e1.target)
  | _, _ => false

/-- Rename the false arm's loans in `st2` by the explicit join pairs
(`relabelJoinLoans`), so that they line up with the true arm `st1` before
`joinSymState` joins the arms. Every pair must fit the arms (`joinPairFits`).
The fresh IDs lie beyond both arms' loans, so they remain as ended trailing
loans of `st2`, which `joinLoanEntries` accepts. A false-arm loan that no pair
renames keeps its ID; `joinLoanEntries` then requires the true arm's entry
with that ID to agree with it. -/
def applyJoinPairs {Val : Type} (alg : ValAlgebra Val)
    (joinPairs : List (LoanId × LoanId))
    (st1 st2 : SymState Val) : Option (SymState Val) :=
  if !joinPairs.all (fun p => joinPairFits p.1 p.2 st1 st2) then none
  else
    relabelJoinLoans alg joinPairs
      (joinPairsFreshBase joinPairs
        (maxLoanId st1.loans.length st2.loans.length))
      st2

/-- Apply every explicit join pair's renaming to a single arm's state `st`
(`relabelJoinLoans`). Used when only the false arm continues past an explicit
join, so code after the join can use the canonical loan IDs. -/
def applySelfJoinPairs {Val : Type} (alg : ValAlgebra Val)
    (joinPairs : List (LoanId × LoanId)) (st : SymState Val) :
    Option (SymState Val) :=
  relabelJoinLoans alg joinPairs
    (joinPairsFreshBase joinPairs st.loans.length) st

/-- Forward value and backward writeback closure synthesized for a function
returning a mutable reference. -/
abbrev MutRetSummary (Val : Type) := Val × (Val → Option (List Val))

/-- Merge two `MutRetSummary Val` results under symbolic branch condition
`cVal`, preserving identical encoded references via `zipOrKeepSameRef` and
projecting branch-specialized final values via `alg.projectBranchVal` before
invoking `back1` and `back2`. -/
def mergeMutRet {Val : Type} (alg : ValAlgebra Val) (cVal : Val)
    (tMut fMut : Option (MutRetSummary Val)) : Option (MutRetSummary Val) :=
  match tMut, fMut with
  | some (fwd1, back1), some (fwd2, back2) =>
    some
      (zipOrKeepSameRef alg cVal fwd1 fwd2,
       fun vFinal =>
         let vFinal1 := alg.projectBranchVal cVal true vFinal
         let vFinal2 := alg.projectBranchVal cVal false vFinal
         match back1 vFinal1, back2 vFinal2 with
         | some finals1, some finals2 =>
           some (zipValList alg cVal finals1 finals2)
         | _, _ => none)
  | _, _ => none

/-- True iff the loans `loans` may remain when a function returns a mutable
reference to loan `retLid` (`synthesizeMutReturnFromVal`): every loan ID is
unique; loan `retLid` is `.activeMut`, its cell carries no permission, and no
active loan borrows from it; every root-parameter loan is the only loan for
its parameter, and those other than `retLid` are active; and every other loan
has ended. It does not check that `retLid` exists. -/
def loansCleanExceptReturned {Val : Type} (retLid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  listFold true
    (fun e _ ih =>
      let okHere : Bool :=
        if !hasUniqueLoanId e.id loans then false
        else if e.id == retLid then
          e.phase.isActiveMut && isUnborrowed e.cell.perm &&
          noActiveChildLoanEdges retLid loans &&
          match rootParamIdxOpt e.target with
          | some idx => countRootParamIdx idx loans == 1
          | none => true
        else
          match rootParamIdxOpt e.target with
          | some idx =>
            e.phase.isActive && countRootParamIdx idx loans == 1
          | none =>
            e.phase.isEnded
      okHere && ih)
    loans

/-- True iff every leaf of `target` ultimately writes back to storage that
outlives the current frame: following `.direct (.parentLoan l)` leaves through
`loans` (bounded by `loans.length + 1` steps), no leaf may name a local
register (`.direct (.localReg _)`), which dies at return. Root parameters and
region outputs have no local leaves. -/
def targetOutlivesFrame {Val : Type} (loans : List (LoanEntry Val))
    (target : BackTarget Val) : Bool :=
  @Nat.recCompiled (fun _ => BackTarget Val → Bool)
    (fun _ => false)
    (fun _ ih t =>
      (targetLeaves t).all (fun leaf =>
        match leaf with
        | (.localReg _, _) => false
        | (.parentLoan l, _) =>
          match findLoan l loans with
          | some e => ih e.target
          | none => false))
    (loans.length + 1) target

/-- Synthesize `(fwdVal, backFn)` for a returned mutable reference `retRefVal`
in terminal or early-return state `stF`. -/
def synthesizeMutReturnFromVal {Val : Type} (alg : ValAlgebra Val)
    (retRefVal : Val) (stF : SymState Val) : Option (MutRetSummary Val) :=
  if !allRegionGroupsEnded stF.regionGroups || !stF.spatial.isEmpty ||
     !stF.regionDeposits.isEmpty then
    none
  else
    match alg.decodeRef retRefVal with
    | none => none
    | some (retLid, retPath) =>
      if !loansCleanExceptReturned retLid stF.loans then none
      else
        match findLoan retLid stF.loans with
        | none => none
        | some retEntry =>
          -- A returned `&mut` must not be backed by a local of this frame.
          if !retEntry.phase.isActiveMut ||
             !targetOutlivesFrame stF.loans retEntry.target then none
          else
            match getPath alg retPath retEntry.cell.val with
            | none => none
            | some fwdVal =>
              -- The forward value and the final parameter values reach the
              -- caller, so neither may carry a handle to a loan of this frame.
              if !handleFreeVal alg fwdVal then none
              else
              let handleFreeFinals (finals : List Val) : Option (List Val) :=
                if finals.all (handleFreeVal alg) then some finals else none
              let backFn : Val → Option (List Val) := fun vFinal =>
                match putPath alg retPath retEntry.cell.val vFinal with
                | none => none
                | some entryVal' =>
                  if isRootTarget retEntry.target then
                    let loans' := updateLoan retLid
                      (fun e =>
                        ⟨e.id, e.phase, ⟨entryVal', e.cell.perm⟩,
                         e.target⟩)
                      stF.loans
                    if loansCleanAtReturn loans' then
                      handleFreeFinals (collectRootMutVals loans')
                    else none
                  else
                    let stUpdated : SymState Val :=
                      match stF with
                      | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                        ⟨locals,
                          updateLoan retLid
                            (fun e =>
                              ⟨e.id, e.phase, ⟨entryVal', e.cell.perm⟩,
                               e.target⟩)
                            loans,
                          rgs, deps, sp, tag⟩
                    match endLoanInState alg retLid stUpdated with
                    | .ok stEnded =>
                      if stateCleanAtReturn stEnded then
                        handleFreeFinals (collectRootMutVals stEnded.loans)
                      else none
                    | .fail => none
              some (fwdVal, backFn)

/-- Control-flow status during structured plan evaluation: normal fallthrough
(`.continuing st`), short-circuiting early return (`.returned out valClean
mutOut`), or continuing execution under pending symbolic early-return guards
(`.guardedContinuing wrapOut st valClean wrapMut`), where `wrapOut` and
`wrapMut` fold any pending symbolic early-return outcomes around the eventual
return of the continuing execution path. -/
inductive ExecFlow (Val : Type) where
  | continuing (st : SymState Val)
  | returned (out : FuncOut Val)
      (valClean : Bool := true)
      (mutOut : Option (MutRetSummary Val) := none)
  | guardedContinuing (wrapOut : FuncOut Val → FuncOut Val)
      (st : SymState Val)
      (valClean : Bool := true)
      (wrapMut : Option (MutRetSummary Val) → Option (MutRetSummary Val) :=
        fun m => m)

/-- Merge two `FuncOut Val` results under symbolic branch condition `cVal`. -/
def mergeFuncOut {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (tOut fOut : FuncOut Val) : FuncOut Val :=
  ⟨zipOrKeepSameRef alg cVal tOut.ret fOut.ret,
   zipValList alg cVal tOut.mutFinals fOut.mutFinals⟩

/-- Compose pending symbolic early-return wrappers around a subsequent
`EvalOutcome (ExecFlow Val)`. -/
def prependGuardedWrap {Val : Type}
    (wrap1 : FuncOut Val → FuncOut Val)
    (clean1 : Bool := true)
    (wrapMut1 : Option (MutRetSummary Val) → Option (MutRetSummary Val) :=
      fun m => m)
    (res : EvalOutcome (ExecFlow Val)) : EvalOutcome (ExecFlow Val) :=
  match res with
  | .ok (.continuing st2) =>
    .ok (.guardedContinuing wrap1 st2 clean1 wrapMut1)
  | .ok (.returned out2 clean2 mut2) =>
    .ok (.returned (wrap1 out2) (clean1 && clean2) (wrapMut1 mut2))
  | .ok (.guardedContinuing wrap2 st2 clean2 wrapMut2) =>
    .ok (.guardedContinuing
      (fun out => wrap1 (wrap2 out))
      st2
      (clean1 && clean2)
      (fun m => wrapMut1 (wrapMut2 m)))
  | .fail => .fail

/-- Elementary pre-order operation in a serialized `FlowPlan Val` tree. -/
inductive FlowPlanOp (Val : Type) where
  | skip : FlowPlanOp Val
  | act (a : PrimAction Val) : FlowPlanOp Val
  | seqJoin : FlowPlanOp Val
  | branchJoin (cond : RvalOp Val) : FlowPlanOp Val
  | branchExplicitJoinOp (cond : RvalOp Val)
      (joinPairs : List (LoanId × LoanId)) : FlowPlanOp Val
  | earlyReturn (cleanupLoans : List LoanId)
      (cleanupGroups : List RegionGroupId) (retExpr : RvalOp Val) :
      FlowPlanOp Val
  | whileLoopOp (fuel : Nat) (cond : RvalOp Val) : FlowPlanOp Val

/-- Structured control-flow certificate (`FlowPlan Val`), represented as a
pre-order operation sequence so right-to-left `listFold` (`List.foldr`)
evaluates arbitrarily nested sequential, conditional, and loop plans bottom-up
as a computable Lean 4 definition. -/
structure FlowPlan (Val : Type) where
  ops : List (FlowPlanOp Val)

namespace FlowPlan

def skip {Val : Type} : FlowPlan Val :=
  ⟨[.skip]⟩

def act {Val : Type} (a : PrimAction Val) : FlowPlan Val :=
  ⟨[.act a]⟩

def seq {Val : Type} (p1 p2 : FlowPlan Val) : FlowPlan Val :=
  ⟨.seqJoin :: (p1.ops ++ p2.ops)⟩

def branch {Val : Type} (cond : RvalOp Val) (onTrue onFalse : FlowPlan Val) :
    FlowPlan Val :=
  ⟨.branchJoin cond :: (onTrue.ops ++ onFalse.ops)⟩

def branchExplicitJoin {Val : Type} (cond : RvalOp Val)
    (onTrue onFalse : FlowPlan Val)
    (joinPairs : List (LoanId × LoanId)) : FlowPlan Val :=
  ⟨.branchExplicitJoinOp cond joinPairs :: (onTrue.ops ++ onFalse.ops)⟩

def earlyReturn {Val : Type} (cleanupLoans : List LoanId)
    (cleanupGroups : List RegionGroupId) (retExpr : RvalOp Val) :
    FlowPlan Val :=
  ⟨[.earlyReturn cleanupLoans cleanupGroups retExpr]⟩

def whileLoop {Val : Type} (fuel : Nat) (cond : RvalOp Val)
    (body : FlowPlan Val) : FlowPlan Val :=
  ⟨.whileLoopOp fuel cond :: body.ops⟩

end FlowPlan

/-- Project a fallthrough `FuncOut` under `cVal = branch` before passing it into
a branch-specific wrapper (`ExecFlow.guardedContinuing`), so values synthesized
from a joined continuing state do not leak the opposite branch's `.choice cVal`
values into `wrap1` or `wrap2`. -/
def projectBranchFuncOut {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (branch : Bool) (out : FuncOut Val) : FuncOut Val :=
  ⟨alg.projectBranchVal cVal branch out.ret,
   out.mutFinals.map (alg.projectBranchVal cVal branch)⟩

/-- Project an optional fallthrough mutable-reference return summary under
`cVal = branch` before passing it into a branch-specific wrapper
(`ExecFlow.guardedContinuing`). -/
def projectBranchMutRet {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (branch : Bool)
    (m : Option (Val × (Val → Option (List Val)))) :
    Option (Val × (Val → Option (List Val))) :=
  match m with
  | none => none
  | some (fwdVal, backFn) =>
    some
      (alg.projectBranchVal cVal branch fwdVal,
       fun vFinal =>
         match backFn (alg.projectBranchVal cVal branch vFinal) with
         | some vs => some (vs.map (alg.projectBranchVal cVal branch))
         | none => none)

/-- Join the control-flow results of the two arms of a branch on the symbolic
condition `cVal` (the true arm first). Two continuing states join with
`joinSymState`, which fails if they cannot be joined. Two returns merge their
outputs (`mergeFuncOut` and `mergeMutRet`). A return on one side and a
continuing state on the other become `.guardedContinuing`: execution continues
in the continuing side's state, and the pending return is merged into the
eventual return under `cVal`. Arms that are already `.guardedContinuing`
compose their pending returns the same way. A join is value-clean
(`valClean`) only if every return it merges is. -/
def joinExecFlow {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) : ExecFlow Val → ExecFlow Val → Option (ExecFlow Val)
  | .continuing st1, .continuing st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined => some (.continuing stJoined)
    | none => none
  | .returned out1 c1 m1, .returned out2 c2 m2 =>
    some (.returned
      (mergeFuncOut alg cVal out1 out2)
      (c1 && c2)
      (mergeMutRet alg cVal m1 m2))
  | .returned out1 c1 m1, .continuing st2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 fallOut)
      st2
      c1
      (fun fallMut => mergeMutRet alg cVal m1 fallMut))
  | .continuing st1, .returned out2 c2 m2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal fallOut out2)
      st1
      c2
      (fun fallMut => mergeMutRet alg cVal fallMut m2))
  | .returned out1 c1 m1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal out1 (wrap2 fallOut))
      st2
      (c1 && c2)
      (fun fallMut => mergeMutRet alg cVal m1 (wrapMut2 fallMut)))
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .returned out2 c2 m2 =>
    some (.guardedContinuing
      (fun fallOut => mergeFuncOut alg cVal (wrap1 fallOut) out2)
      st1
      (c1 && c2)
      (fun fallMut => mergeMutRet alg cVal (wrapMut1 fallMut) m2))
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .continuing st2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut =>
          mergeFuncOut alg cVal
            (wrap1 (projectBranchFuncOut alg cVal true fallOut))
            (projectBranchFuncOut alg cVal false fallOut))
        stJoined
        c1
        (fun fallMut =>
          mergeMutRet alg cVal
            (wrapMut1 (projectBranchMutRet alg cVal true fallMut))
            (projectBranchMutRet alg cVal false fallMut)))
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut =>
          mergeFuncOut alg cVal
            (projectBranchFuncOut alg cVal true fallOut)
            (wrap2 (projectBranchFuncOut alg cVal false fallOut)))
        stJoined
        c2
        (fun fallMut =>
          mergeMutRet alg cVal
            (projectBranchMutRet alg cVal true fallMut)
            (wrapMut2 (projectBranchMutRet alg cVal false fallMut))))
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1,
    .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match joinSymState alg cVal st1 st2 with
    | some stJoined =>
      some (.guardedContinuing
        (fun fallOut =>
          mergeFuncOut alg cVal
            (wrap1 (projectBranchFuncOut alg cVal true fallOut))
            (wrap2 (projectBranchFuncOut alg cVal false fallOut)))
        stJoined
        (c1 && c2)
        (fun fallMut =>
          mergeMutRet alg cVal
            (wrapMut1 (projectBranchMutRet alg cVal true fallMut))
            (wrapMut2 (projectBranchMutRet alg cVal false fallMut))))
    | none => none

/-- `applySelfJoinPairs` applied to the continuing state of an `ExecFlow`, if
any. -/
def applySelfJoinPairsFlow {Val : Type} (alg : ValAlgebra Val)
    (joinPairs : List (LoanId × LoanId)) :
    ExecFlow Val → Option (ExecFlow Val)
  | .continuing st =>
    match applySelfJoinPairs alg joinPairs st with
    | some st' => some (.continuing st')
    | none => none
  | .guardedContinuing wrap st c wrapMut =>
    match applySelfJoinPairs alg joinPairs st with
    | some st' => some (.guardedContinuing wrap st' c wrapMut)
    | none => none
  | .returned out c m => some (.returned out c m)

/-- `joinExecFlow` for an explicit join (`FlowPlan.branchExplicitJoin`). Before
the arms join, the pairs `joinPairs` rename the false arm's loans to the true
arm's loan IDs (`applyJoinPairs` when both arms continue, and
`applySelfJoinPairsFlow` when only the false arm does), so that code after the
join can use the true arm's IDs. Fails if a renaming fails; see
`relabelJoinLoans` for what the pairs can express. -/
def joinExecFlowExplicit {Val : Type} (alg : ValAlgebra Val)
    (cVal : Val) (joinPairs : List (LoanId × LoanId)) :
    ExecFlow Val → ExecFlow Val → Option (ExecFlow Val)
  | .continuing st1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal (.continuing st1) (.continuing st2Aligned)
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1, .continuing st2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1 c1 wrapMut1) (.continuing st2Aligned)
    | none => none
  | .continuing st1, .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.continuing st1) (.guardedContinuing wrap2 st2Aligned c2 wrapMut2)
    | none => none
  | .guardedContinuing wrap1 st1 c1 wrapMut1,
    .guardedContinuing wrap2 st2 c2 wrapMut2 =>
    match applyJoinPairs alg joinPairs st1 st2 with
    | some st2Aligned =>
      joinExecFlow alg cVal
        (.guardedContinuing wrap1 st1 c1 wrapMut1)
        (.guardedContinuing wrap2 st2Aligned c2 wrapMut2)
    | none => none
  -- At least one arm returned, so only one state (if any) continues. The
  -- pairs rename the false arm's loans to the true arm's IDs; a continuing
  -- false arm is renamed on its own, and a continuing true arm already uses
  -- the canonical IDs.
  | f1, f2 =>
    match applySelfJoinPairsFlow alg joinPairs f2 with
    | some f2' => joinExecFlow alg cVal f1 f2'
    | none => none

/-- Execute a `while` loop for at most `fuel` iterations, failing if the loop
condition remains true when `fuel` reaches `0`. -/
def runWhileFlowSteps {Val : Type} (alg : ValAlgebra Val)
    (cond : RvalOp Val)
    (evalBody : SymState Val → EvalOutcome (ExecFlow Val))
    (fuel : Nat) (s : SymState Val) : EvalOutcome (ExecFlow Val) :=
  @Nat.recCompiled (fun _ => SymState Val → EvalOutcome (ExecFlow Val))
    (fun s0 =>
      match evalRval alg cond s0 with
      | some cv =>
        match alg.asBool cv with
        | some false => .ok (.continuing s0)
        | _ => .fail
      | none => .fail)
    (fun _ ih s0 =>
      match evalRval alg cond s0 with
      | some cv =>
        match alg.asBool cv with
        | some false => .ok (.continuing s0)
        | some true =>
          match evalBody s0 with
          | .ok (.continuing s') => ih s'
          | .ok (.returned out c m) => .ok (.returned out c m)
          | .ok (.guardedContinuing wrap1 s' c1 wrapMut1) =>
            prependGuardedWrap wrap1 c1 wrapMut1 (ih s')
          | .fail => .fail
        | none => .fail
      | none => .fail)
    fuel s

/-- Push-down stack step for one `FlowPlanOp Val` during bottom-up `listFold`
evaluation of a `FlowPlan Val`. The flag records whether every step so far
found the operands it needs. A malformed plan clears it for good: a cleared
flag cannot be hidden by later steps, even ones (such as `seq` after an early
return) that would never run the failing operand. -/
def stepPlanOp {Val : Type} (alg : ValAlgebra Val) (op : FlowPlanOp Val)
    (acc : Bool × List (SymState Val → EvalOutcome (ExecFlow Val))) :
    Bool × List (SymState Val → EvalOutcome (ExecFlow Val)) :=
  match acc with
  | (ok, stk) =>
  match op with
  | .skip => (ok, (fun s0 => .ok (.continuing s0)) :: stk)
  | .act a =>
    (ok, (fun s0 =>
      match stepAction alg a s0 with
      | .ok st' => .ok (.continuing st')
      | .fail => .fail) :: stk)
  | .seqJoin =>
    match stk with
    | ih1 :: ih2 :: rest =>
      (ok, (fun s0 =>
        match ih1 s0 with
        | .ok (.continuing st1) => ih2 st1
        | .ok (.returned out c m) => .ok (.returned out c m)
        | .ok (.guardedContinuing wrap1 st1 c1 wrapMut1) =>
          prependGuardedWrap wrap1 c1 wrapMut1 (ih2 st1)
        | .fail => .fail) :: rest)
    | _ => (false, [])
  | .branchJoin cond =>
    match stk with
    | ihTrue :: ihFalse :: rest =>
      (ok, (fun s0 =>
        match evalRval alg cond s0 with
        | none => .fail
        | some cVal =>
          match alg.asBool cVal with
          | some true => ihTrue s0
          | some false => ihFalse s0
          | none =>
            match ihTrue s0, ihFalse s0 with
            | .ok flowTrue, .ok flowFalse =>
              match joinExecFlow alg cVal flowTrue flowFalse with
              | some flowJoined => .ok flowJoined
              | none => .fail
            | _, _ => .fail) :: rest)
    | _ => (false, [])
  | .branchExplicitJoinOp cond joinPairs =>
    match stk with
    | ihTrue :: ihFalse :: rest =>
      (ok, (fun s0 =>
        if !validJoinPairs joinPairs [] [] then .fail
        else
          match evalRval alg cond s0 with
          | none => .fail
          | some cVal =>
            match alg.asBool cVal with
            | some true => ihTrue s0
            | some false =>
              -- Code after the join uses the true arm's loan IDs, so the
              -- false arm's loans are renamed even when it alone runs.
              match ihFalse s0 with
              | .ok flowFalse =>
                match applySelfJoinPairsFlow alg joinPairs flowFalse with
                | some flow => .ok flow
                | none => .fail
              | .fail => .fail
            | none =>
              match ihTrue s0, ihFalse s0 with
              | .ok flowTrue, .ok flowFalse =>
                match joinExecFlowExplicit alg cVal joinPairs
                        flowTrue flowFalse with
                | some flowJoined => .ok flowJoined
                | none => .fail
              | _, _ => .fail) :: rest)
    | _ => (false, [])
  | .earlyReturn cleanupLoans cleanupGroups retExpr =>
    (ok, (fun s0 =>
      match evalRval alg retExpr s0 with
      | none => .fail
      | some retVal =>
        match endLoansInState alg cleanupLoans s0 with
        | .fail => .fail
        | .ok st1 =>
          match endRegionGroupsInState alg cleanupGroups st1 with
          | .fail => .fail
          | .ok st2 =>
            let valClean := stateCleanAtReturn st2
            let mutOut := synthesizeMutReturnFromVal alg retVal st2
            let noMutOut :=
              match mutOut with
              | none => true
              | some _ => false
            if !valClean && noMutOut then .fail
            else
              .ok (.returned
                ⟨retVal, collectRootMutVals st2.loans⟩
                valClean
                mutOut)) :: stk)
  | .whileLoopOp fuel cond =>
    match stk with
    | ihBody :: rest =>
      (ok, (fun s0 => runWhileFlowSteps alg cond ihBody fuel s0) :: rest)
    | _ => (false, [])

def evalPlanOps {Val : Type} (alg : ValAlgebra Val)
    (ops : List (FlowPlanOp Val))
    (acc : Bool × List (SymState Val → EvalOutcome (ExecFlow Val))) :
    Bool × List (SymState Val → EvalOutcome (ExecFlow Val)) :=
  ops.foldr (fun op acc' => stepPlanOp alg op acc') acc

/-- Evaluate `FlowPlan Val` on `SymState Val` via total structural recursion
(`List.foldr`). A malformed serialization (an operator missing operands, or
operands left over) fails, whatever the operands would have done. Every plan
evaluator (`evalFnValue`, `evalFnReturningMut`, and `BlockCfg` block bodies)
runs plans through this function. -/
def evalPlan {Val : Type} (alg : ValAlgebra Val)
    (plan : FlowPlan Val) (st : SymState Val) : EvalOutcome (ExecFlow Val) :=
  match evalPlanOps alg plan.ops (true, []) with
  | (true, [evalFn]) => evalFn st
  | _ => .fail

/-- Well-formedness invariant for a serialized `FlowPlan Val`: folding `p.ops`
onto any continuation stack `stk` keeps the flag `ok` and pushes
`evalPlan alg p` onto `stk`. -/
def WfPlan {Val : Type} (alg : ValAlgebra Val) (p : FlowPlan Val) : Prop :=
  ∀ ok stk,
    evalPlanOps alg p.ops (ok, stk) =
      (ok, (fun s0 => evalPlan alg p s0) :: stk)

theorem evalPlanOps_append {Val : Type} (alg : ValAlgebra Val)
    (xs ys : List (FlowPlanOp Val))
    (stk : Bool × List (SymState Val → EvalOutcome (ExecFlow Val))) :
    evalPlanOps alg (xs ++ ys) stk =
      evalPlanOps alg xs (evalPlanOps alg ys stk) := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    change stepPlanOp alg x (evalPlanOps alg (xs' ++ ys) stk) =
      stepPlanOp alg x (evalPlanOps alg xs' (evalPlanOps alg ys stk))
    rw [ih]

theorem evalPlan_seq {Val : Type} (alg : ValAlgebra Val)
    (p1 p2 : FlowPlan Val) (s0 : SymState Val)
    (hWf1 : WfPlan alg p1) (hWf2 : WfPlan alg p2) :
    evalPlan alg (.seq p1 p2) s0 =
      (match evalPlan alg p1 s0 with
       | .ok (.continuing st1) => evalPlan alg p2 st1
       | .ok (.returned out c m) => .ok (.returned out c m)
       | .ok (.guardedContinuing wrap1 st1 c1 wrapMut1) =>
         prependGuardedWrap wrap1 c1 wrapMut1 (evalPlan alg p2 st1)
       | .fail => .fail) := by
  change
    (match stepPlanOp alg .seqJoin
        (evalPlanOps alg (p1.ops ++ p2.ops) (true, [])) with
     | (true, [evalFn]) => evalFn s0
     | _ => .fail) = _
  rw [evalPlanOps_append, hWf2 true [], hWf1]
  rfl

/-- Entry parameter passing mode. -/
inductive ParamMode where
  | byVal
  | sharedRef (rootId : Nat) (path : SubPath)
  | mutRef (rootId : Nat) (path : SubPath)

/-- Entry parameter descriptor pairing a passing mode with an initial value. -/
structure ParamInput (Val : Type) where
  mode : ParamMode
  val : Val

def getRootPerm (rootId : Nat) (ps : List (Nat × PermTree)) : PermTree :=
  listFold .unborrowed
    (fun entry _ ih =>
      match entry with
      | (id, p) => if id == rootId then p else ih)
    ps

def setRootPerm (rootId : Nat) (p : PermTree)
    (ps : List (Nat × PermTree)) : List (Nat × PermTree) :=
  listFold [(rootId, p)]
    (fun entry rest ih =>
      match entry with
      | (id, oldP) =>
        if id == rootId then (id, p) :: rest
        else (id, oldP) :: ih)
    ps

/-- Value of a new shared parameter at `path` within a root whose existing
borrows are `rp`, keeping aliased shared parameters coherent, together with
updated values for earlier shared loans that the new parameter encloses. Each
root-parameter loan stores its own value, and `ValAlgebra` cannot compare
values, so overlapping shared parameters of one root are made to agree:
- An earlier shared loan `l0` at `p0` with `p0` a prefix of `path` supplies the
  new value: `path`'s suffix is projected out of `l0`'s value (`getPath`).
- Otherwise the caller-supplied `supplied` is used.
- Every earlier shared loan at a path that `path` strictly encloses is updated
  to the matching projection of the new value, so the smaller loans agree with
  the larger one.
- An overlapping entry that is not a shared loan, or a projection that does not
  resolve, yields `none`. -/
def aliasedSharedParamVal {Val : Type} (alg : ValAlgebra Val)
    (path : SubPath) (rp : PermTree) (loans : List (LoanEntry Val))
    (supplied : Val) : Option (Val × List (LoanId × Val)) :=
  -- `some none`: no enclosing loan seen yet; `some (some v)`: derived value
  -- `v`; `none`: some overlapping entry cannot supply a coherent value.
  let derived : Option (Option Val) :=
    (toEntries rp).foldr
      (fun entry acc =>
        match acc with
        | none => none
        | some cand =>
          if !subPathOverlaps entry.1 path then some cand
          else
            match stripSubPathPrefix entry.1 path, entry.2 with
            | some rel, .shared (l0 :: _) =>
              match findLoan l0 loans with
              | some e0 =>
                match getPath alg rel e0.cell.val with
                | some v => some (some v)
                | none => none
              | none => none
            | some _, _ => none
            -- `path` strictly encloses this entry; handled below.
            | none, _ => some cand)
      (some none)
  let newVal : Option Val :=
    match derived with
    | none => none
    | some none => some supplied
    | some (some v) => some v
  match newVal with
  | none => none
  | some v =>
    let updates : Option (List (LoanId × Val)) :=
      (toEntries rp).foldr
        (fun entry acc =>
          match acc with
          | none => none
          | some ups =>
            match stripSubPathPrefix entry.1 path with
            | some _ => some ups
            | none =>
              match stripSubPathPrefix path entry.1, entry.2 with
              | none, _ => some ups
              | some rel, .shared ls =>
                match getPath alg rel v with
                | some sub => some (ls.map (fun l => (l, sub)) ++ ups)
                | none => none
              | some _, _ => none)
        (some [])
    match updates with
    | some ups => some (v, ups)
    | none => none

/-- Replace the cell value of each loan named in `updates`. -/
def applyLoanValueUpdates {Val : Type} (updates : List (LoanId × Val))
    (loans : List (LoanEntry Val)) : List (LoanEntry Val) :=
  loans.map (fun e =>
    match updates.find? (fun u => u.1 == e.id) with
    | some u => ⟨e.id, e.phase, ⟨u.2, e.cell.perm⟩, e.target⟩
    | none => e)

/-- Initialize `SymState Val` from function entry parameters, checking for
illegal aliasing across reference parameters via `PermTree`. -/
def buildInitState {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val))
    (rootPerms : List (Nat × PermTree))
    (st : SymState Val) : Option (SymState Val) :=
  listFold
    (β := List (Nat × PermTree) → SymState Val → Option (SymState Val))
    (fun _ s => some s)
    (fun p _ ih rPerms st0 =>
      match st0 with
      | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
        match p.mode with
        | .byVal =>
          -- A by-value parameter carries no borrow: a decodable handle in it
          -- would alias a parameter loan, or a loan allocated later.
          if !handleFreeVal alg p.val then none
          else
            let st' : SymState Val :=
              ⟨locals ++ [⟨p.val, .unborrowed⟩], loans, rgs, deps, sp, tag⟩
            ih rPerms st'
        | .sharedRef rootId path =>
          let lid := loans.length
          let rp := getRootPerm rootId rPerms
          -- Nested references are not modeled: a pointee value carrying a
          -- handle would alias a loan of this frame.
          if !handleFreeVal alg p.val then none
          else
          match aliasedSharedParamVal alg path rp loans p.val,
                acquirePerm .shared lid path rp with
          | none, _ => none
          | _, none => none
          | some (val, updates), some rp' =>
            let entry : LoanEntry Val :=
              ⟨lid, .activeShared, ⟨val, .unborrowed⟩, .rootParam lid⟩
            let st' : SymState Val :=
              ⟨locals ++ [⟨alg.encodeSharedRef lid [], .unborrowed⟩],
               applyLoanValueUpdates updates loans ++ [entry], rgs, deps, sp,
               tag⟩
            ih (setRootPerm rootId rp' rPerms) st'
        | .mutRef rootId path =>
          let lid := loans.length
          let rp := getRootPerm rootId rPerms
          if !handleFreeVal alg p.val then none
          else
          match acquirePerm .mutBorrow lid path rp with
          | none => none
          | some rp' =>
            let entry : LoanEntry Val :=
              ⟨lid, .activeMut, ⟨p.val, .unborrowed⟩, .rootParam lid⟩
            let st' : SymState Val :=
              ⟨locals ++ [⟨alg.encodeRef lid [], .unborrowed⟩],
               loans ++ [entry], rgs, deps, sp, tag⟩
            ih (setRootPerm rootId rp' rPerms) st')
    params rootPerms st

def initFnState {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) : EvalOutcome (SymState Val) :=
  match buildInitState alg params [] ⟨[], [], [], [], [], 0⟩ with
  | some st => .ok st
  | none => .fail

/-- Evaluate a function returning a value, yielding `FuncOut Val`. Neither the
returned value nor any final `&mut` parameter value may contain a borrow
handle (`handleFreeOut`): a handle would name a loan of this frame (or a root
parameter loan the caller still owns). Functions returning `&mut` go through
`evalFnReturningMut`. Functions returning a shared reference (`&T`) are
supported by neither entry point: this one rejects the handle, and
`evalFnReturningMut` requires the returned loan to be `.activeMut`. Canaries'
`value_return_tests` (item 1) and
`plan_whileLoop_initFnState_and_returningMut_tests` (item 4) pin both
rejections. -/
def evalFnValue {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retExpr : RvalOp Val) : EvalOutcome (FuncOut Val) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    match evalPlan alg plan st0 with
    | .fail => .fail
    | .ok (.returned out valClean _) =>
      if !valClean || !handleFreeOut alg out then .fail else .ok out
    | .ok (.continuing stF) =>
      if !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal =>
          let out : FuncOut Val := ⟨retVal, collectRootMutVals stF.loans⟩
          if !handleFreeOut alg out then .fail else .ok out
        | none => .fail
    | .ok (.guardedContinuing wrapOut stF valClean _) =>
      if !valClean || !stateCleanAtReturn stF then .fail
      else
        match evalRval alg retExpr stF with
        | some retVal =>
          let fallthroughOut : FuncOut Val :=
            ⟨retVal, collectRootMutVals stF.loans⟩
          let out := wrapOut fallthroughOut
          if !handleFreeOut alg out then .fail else .ok out
        | none => .fail

/-- Evaluate a function returning a mutable reference in `retReg` (or via
`.earlyReturn`), synthesizing both its forward value `fwdVal` and its backward
lens `backFn : Val → Option (List Val)`.

Limitation: the returned reference must be a single loan whose target reaches
caller storage directly. A reborrow through an intermediate loan that is still
live is rejected, as in `let r = &mut *x; &mut (*r).0` or `&mut g(x).0`
(where `g` returns `&mut`): the returned loan's target is a sub-place of the
intermediate loan `r`, which cannot end while the returned loan borrows from
it, and `synthesizeMutReturnFromVal` requires every other non-root loan to
have ended (`loansCleanExceptReturned`). Supporting such chains would need the
summary to carry the chain of live loans and its backward function to end
them innermost first, writing each one's value back into its parent before
the root parameter's final value is read. -/
def evalFnReturningMut {Val : Type} (alg : ValAlgebra Val)
    (params : List (ParamInput Val)) (plan : FlowPlan Val)
    (retReg : LocalId) : EvalOutcome (Val × (Val → Option (List Val))) :=
  match initFnState alg params with
  | .fail => .fail
  | .ok st0 =>
    match evalPlan alg plan st0 with
    | .fail => .fail
    | .ok (.returned _ _ (some mutRet)) => .ok mutRet
    | .ok (.returned _ _ none) => .fail
    | .ok (.continuing stF) =>
      match readPlaceVal alg (.localSub retReg []) stF with
      | some retRef =>
        match synthesizeMutReturnFromVal alg retRef stF with
        | some mutRet => .ok mutRet
        | none => .fail
      | none => .fail
    | .ok (.guardedContinuing _ stF _ wrapMut) =>
      let fallMut :=
        match readPlaceVal alg (.localSub retReg []) stF with
        | some retRef => synthesizeMutReturnFromVal alg retRef stF
        | none => none
      match wrapMut fallMut with
      | some mutRet => .ok mutRet
      | none => .fail

/-!
## Kernel-Checked Unit Tests for `Plan`
-/

/-- Unit tests for `resolvePlace`, `readPlaceVal`, `writePlaceVal`,
`evalRval`, `evalRvalList`, `validJoinPairs`, `remapValLoan` on nested
aggregates, `renameRegionGroupLoan`, and mixed early-return / continuing
branches (`ExecFlow.guardedContinuing`). -/
theorem plan_core_helpers_and_guardedContinuing_tests :
    let st0 : SymState LensTestVal :=
      { locals :=
          [ ⟨.node (.atom 10) (.atom 20), .unborrowed⟩
          , ⟨.ref 0 [1], .unborrowed⟩ ]
        loans :=
          [⟨0, .activeMut,
            ⟨.node (.atom 30) (.atom 40), .split [([0], .mutLocked 1)]⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 1. `resolvePlace`, `readPlaceVal` (gating parent-loan sub-path `[0]` vs.
    -- `[1]`), and `writePlaceVal`:
    resolvePlace lensTestValAlg (.localSub 0 [0]) st0 =
      some (.localReg 0, [0]) ∧
    resolvePlace lensTestValAlg (.derefSub 1 [0]) st0 =
      some (.parentLoan 0, [1, 0]) ∧
    resolvePlace lensTestValAlg (.derefSub 0 []) st0 = none ∧
    readPlaceVal lensTestValAlg (.localSub 0 [0]) st0 = some (.atom 10) ∧
    readPlaceVal lensTestValAlg (.derefSub 1 []) st0 = some (.atom 40) ∧
    let stRef0 : SymState LensTestVal :=
      { st0 with
        locals :=
          [ ⟨.node (.atom 10) (.atom 20), .unborrowed⟩
          , ⟨.ref 0 [0], .unborrowed⟩ ] }
    (writePlaceVal lensTestValAlg (.localSub 1 []) (.ref 0 [0]) st0 = none ∧
     readPlaceVal lensTestValAlg (.derefSub 1 []) stRef0 = none ∧
     writePlaceVal lensTestValAlg (.derefSub 1 []) (.atom 99) stRef0 = none) ∧
    -- 2. `evalRval` and `evalRvalList`:
    evalRvalList lensTestValAlg
      [ .constVal (.atom 1)
      , .use (.localSub 0 [1])
      , .unary (fun v => some v) (.localSub 0 [0])
      , .binary (fun v1 _ => some v1) (.localSub 0 [0]) (.localSub 0 [1]) ]
      st0 =
      some [.atom 1, .atom 20, .atom 10, .atom 10] ∧
    -- 3. `validJoinPairs` anti-aliasing and `remapValLoan` inside nested
    -- `.node` aggregates:
    validJoinPairs [(1, 2), (3, 4)] [] [] = true ∧
    validJoinPairs [(1, 2), (1, 3)] [] [] = false ∧
    validJoinPairs [(1, 2), (3, 2)] [] [] = false ∧
    remapValLoan lensTestValAlg 2 7 (.node (.ref 2 [0]) (.ref 3 [1])) =
      some (.node (.ref 7 [0]) (.ref 3 [1])) ∧
    -- 4. Mixed `.returned` and `.continuing` symbolic branch via
    -- `ExecFlow.guardedContinuing`:
    let mixedBranchPlan : FlowPlan LensTestVal :=
      .seq
        (.branch (.use (.localSub 0 []))
          (.earlyReturn [] [] (.constVal (.atom 111)))
          (.act (.assign (.derefSub 1 []) (.constVal (.atom 222)))))
        (.act (.assign (.localSub 2 []) (.constVal (.atom 333))))
    evalFnValue lensTestValAlg
      [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 111, [.atom 5]⟩ ∧
    evalFnValue lensTestValAlg
      [⟨.byVal, .atom 0⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.atom 333, [.atom 222]⟩ ∧
    evalFnValue lensTestValAlg
      [⟨.byVal, .node (.atom 1) (.atom 0)⟩, ⟨.mutRef 0 [], .atom 5⟩]
      mixedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.choice (.node (.atom 1) (.atom 0)) (.atom 111) (.atom 333),
           [.choice (.node (.atom 1) (.atom 0)) (.atom 5) (.atom 222)]⟩ ∧
    -- 5. Nested symbolic `.branch` joining `.guardedContinuing` with
    -- `.continuing`, and `.whileLoop` preserving `.guardedContinuing` across
    -- iterations:
    let symBranchCond : LensTestVal := .node (.atom 1) (.atom 0)
    let nestedGuardedBranchPlan : FlowPlan LensTestVal :=
      .seq
        (.branch (.use (.localSub 0 []))
          (.branch (.use (.localSub 0 []))
            (.earlyReturn [] [] (.constVal (.atom 101)))
            (.act (.assign (.localSub 2 []) (.constVal (.atom 202)))))
          (.act (.assign (.localSub 2 []) (.constVal (.atom 303)))))
        (.act (.assign (.localSub 2 []) (.constVal (.atom 404))))
    let guardedWhileLoopPlan : FlowPlan LensTestVal :=
      .whileLoop 2 (.use (.localSub 2 []))
        (.seq
          (.branch (.use (.localSub 0 []))
            (.earlyReturn [] [] (.constVal (.atom 505)))
            .skip)
          (.act (.assign (.localSub 2 []) (.constVal (.atom 0)))))
    let fallMutFinal : LensTestVal := .atom 5
    evalFnValue lensTestValAlg
      [⟨.byVal, symBranchCond⟩, ⟨.mutRef 0 [], .atom 5⟩]
      nestedGuardedBranchPlan
      (.use (.localSub 2 [])) =
      .ok ⟨.choice symBranchCond
             (.choice symBranchCond (.atom 101) (.atom 404))
             (.atom 404),
           [.choice symBranchCond
              (.choice symBranchCond (.atom 5) fallMutFinal)
              fallMutFinal]⟩ ∧
    evalFnValue lensTestValAlg
      [ ⟨.byVal, symBranchCond⟩
      , ⟨.mutRef 0 [], .atom 5⟩
      , ⟨.byVal, .atom 1⟩ ]
      guardedWhileLoopPlan
      (.constVal (.atom 606)) =
      .ok ⟨.choice symBranchCond (.atom 505) (.atom 606),
           [.choice symBranchCond (.atom 5) (.atom 5)]⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl⟩

/-- Tests for:
1. `joinRegionGroups` projecting branch-specific `outVals` and `deps` via
   `alg.projectBranchVal` before invoking `g1.backFn` and `g2.backFn`,
2. `renameBackTargetLoan` and `renameRegionGroupLoan` remapping references
   inside `.lensCall` and `RegionGroupEntry` backward-closure outputs,
3. `evalFnReturningMut` supporting `.earlyReturn` on all paths (`.returned`) and
   mixed early-return / continuing paths (`.guardedContinuing`), with
   `mergeMutRet` projecting branch-specialized `vFinal` values via
   `alg.projectBranchVal` and `zipOrKeepSameRef` preserving identical encoded
   references in `joinLoanEntries` and `mergeMutRet`, while `evalFnValue`
   rejects `.earlyReturn` when an unended child loan remains active. -/
theorem plan_join_projection_rename_and_returningMut_tests :
    -- 1. `joinRegionGroups` projects branch-specialized `outVals` and `deps`:
    (let gTrue : RegionGroupEntry LensTestVal :=
       ⟨0, true, 1, [(.localReg 0, [])], [1], [],
        fun outs deps =>
          match outs, deps with
          | [⟨_, .atom 100⟩], [⟨_, .atom 10⟩] => some ([.atom 110], [.atom 1])
          | _, _ => none⟩
     let gFalse : RegionGroupEntry LensTestVal :=
       ⟨0, true, 1, [(.localReg 0, [])], [1], [],
        fun outs deps =>
          match outs, deps with
          | [⟨_, .atom 200⟩], [⟨_, .atom 20⟩] => some ([.atom 220], [.atom 2])
          | _, _ => none⟩
     let symCond : LensTestVal := .ref 99 []
     let zippedOut := lensTestValAlg.zipVal symCond (.atom 100) (.atom 200)
     let zippedDep := lensTestValAlg.zipVal symCond (.atom 10) (.atom 20)
     match joinRegionGroups lensTestValAlg symCond [gTrue] [gFalse] with
     | some [gJoined] =>
       gJoined.backFn [zippedOut] [zippedDep] =
         some
           ([lensTestValAlg.zipVal symCond (.atom 110) (.atom 220)],
            [lensTestValAlg.zipVal symCond (.atom 1) (.atom 2)])
     | _ => False) ∧
    -- 2. `renameBackTargetLoan` and `renameRegionGroupLoan` remap references
    -- returned by `backFn`:
    (let bt : BackTarget LensTestVal :=
       .lensCall [(.localReg 0, [])] (fun _ => some [.ref 2 [0]])
     match renameBackTargetLoan lensTestValAlg 2 1 bt with
     | some bt' =>
       match bt'.steps with
       | [.lensCall _ backFn'] => backFn' (.atom 0) = some [.ref 1 [0]]
       | _ => False
     | none => False) ∧
    (let rg : RegionGroupEntry LensTestVal :=
       ⟨0, true, 2, [(.localReg 0, [])], [2], [],
        fun _ _ => some ([.ref 2 [0]], [.ref 2 [1]])⟩
     let rg' := renameRegionGroupLoan lensTestValAlg 2 1 rg
     rg'.backFn [] [] = some ([.ref 1 [0]], [.ref 1 [1]])) ∧
    -- 3. `evalFnReturningMut` with `.earlyReturn` (both direct `.returned` and
    -- mixed `.guardedContinuing`), plus `evalFnValue` rejecting unended child
    -- loans at `.earlyReturn`, plus `joinLoanEntries` preserving identical
    -- reference values inside loan cells via `zipOrKeepSameRef`:
    (let symCond : LensTestVal := .node (.atom 1) (.atom 0)
     let earlyMutPlan : FlowPlan LensTestVal :=
       .seq
         (.branch (.use (.localSub 0 []))
           (.seq
             (.act (.borrow 3 .mutBorrow (.derefSub 1 [])))
             (.seq
               (.act (.assign (.derefSub 3 []) (.constVal (.atom 70))))
               (.earlyReturn [] [] (.use (.localSub 3 [])))))
           .skip)
         (.seq
           (.act (.borrow 3 .mutBorrow (.derefSub 2 [])))
           (.act (.assign (.derefSub 3 []) (.constVal (.atom 80)))))
     let eRef : LoanEntry LensTestVal :=
       ⟨0, .activeMut, ⟨.ref 1 [0], .unborrowed⟩, .rootParam 0⟩
     (match joinLoanEntries lensTestValAlg symCond [eRef] [eRef] with
      | some [eJoined] => eJoined.cell.val = .ref 1 [0]
      | _ => False) ∧
     (match evalFnReturningMut lensTestValAlg
         [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩, ⟨.mutRef 1 [], .atom 6⟩]
         earlyMutPlan 3 with
      | .ok (fwdT, backT) =>
        fwdT = .atom 70 ∧ backT (.atom 99) = some [.atom 99, .atom 6]
      | .fail => False) ∧
     (match evalFnReturningMut lensTestValAlg
         [⟨.byVal, symCond⟩,
          ⟨.mutRef 0 [], .atom 5⟩,
          ⟨.mutRef 1 [], .atom 6⟩]
         earlyMutPlan 3 with
      | .ok (fwdSym, backSym) =>
        fwdSym = .choice symCond (.atom 70) (.atom 80) ∧
        backSym (.choice symCond (.atom 91) (.atom 92)) =
          some [.choice symCond (.atom 91) (.atom 5),
                .choice symCond (.atom 6) (.atom 92)]
      | .fail => False) ∧
     evalFnValue lensTestValAlg
       [⟨.byVal, .atom 1⟩, ⟨.mutRef 0 [], .atom 5⟩, ⟨.mutRef 1 [], .atom 6⟩]
       earlyMutPlan (.use (.localSub 3 [])) = .fail) :=
  ⟨rfl, rfl, rfl, ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩⟩

/-- A malformed plan serialization fails even where the operand that is
missing would never run:
1. a trailing `.seqJoin` with one operand, after an early return,
2. a trailing `.branchJoin` with one operand, after an early return, and
3. `[.seqJoin, X, .seqJoin, Y]`, whose inner join is missing an operand and
   which would otherwise drop `Y`.
The well-formed `[.seqJoin, X, .skip]` returns the early-return value. -/
theorem malformed_plan_serializations_fail_tests :
    let ret : FlowPlanOp LensTestVal := .earlyReturn [] [] (.constVal (.atom 7))
    evalFnValue lensTestValAlg [] ⟨[.seqJoin, ret, .seqJoin]⟩
      (.constVal (.atom 0)) = .fail ∧
    evalFnValue lensTestValAlg []
      ⟨[.seqJoin, ret, .branchJoin (.constVal (.atom 1))]⟩
      (.constVal (.atom 0)) = .fail ∧
    evalFnValue lensTestValAlg [] ⟨[.seqJoin, ret, .seqJoin, .skip]⟩
      (.constVal (.atom 0)) = .fail ∧
    evalFnReturningMut lensTestValAlg [] ⟨[.seqJoin, ret, .seqJoin]⟩ 0 =
      .fail ∧
    evalFnValue lensTestValAlg [] ⟨[.seqJoin, ret, .skip]⟩
      (.constVal (.atom 0)) = .ok ⟨.atom 7, []⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Tests for:
1. `writePlaceVal` and `.borrow _ .mutBorrow (.derefSub reg _)` requiring the
   handle local `reg` to be `.unborrowed` (`readLocalHandleForAccess`),
2. `readPlaceVal` and `.borrow _ .shared (.derefSub reg _)` resolving a
   branch-joined choice tree of shared-reference handles (`readSharedChoiceDeref`
   and `acquireSharedChoiceBorrow`),
3. `renameLoanInState` remapping `.init` cells inside pinned spatial blocks and
   rejecting stale references when the pinned codec does not match the remapped
   cells (`remapSpatialBlocksLoan` and `spatialPinnedRenameConsistent`),
4. `zipOrKeepSameRef` deriving recursion fuel from the maximum `sizeBound` of
   both operands so nested identical references beyond the condition's size bound
   stay decodable. -/
theorem plan_handle_access_shared_choice_spatial_rename_and_zip_fuel_tests :
    -- 1. Mutable dereference requires an unborrowed handle local:
    let stSharedHandle : SymState LensTestVal :=
      { locals := [⟨.ref 0 [], .shared [1]⟩, ⟨.atom 0, .unborrowed⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .rootParam 0⟩
          , ⟨1, .activeShared, ⟨.ref 0 [], .unborrowed⟩,
              .direct (.localReg 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    readPlaceVal lensTestValAlg (.derefSub 0 []) stSharedHandle =
      some (.atom 10) ∧
    writePlaceVal lensTestValAlg (.derefSub 0 []) (.atom 20) stSharedHandle =
      none ∧
    stepAction lensTestValAlg
      (.borrow 1 .mutBorrow (.derefSub 0 [])) stSharedHandle = .fail ∧
    -- 2. Branch-joined shared reference handles can be dereferenced and
    -- shared-reborrowed:
    let symCond : LensTestVal := .node (.atom 1) (.atom 0)
    let sRef0 : LensTestVal := lensTestValAlg.encodeSharedRef 0 []
    let sRef1 : LensTestVal := lensTestValAlg.encodeSharedRef 1 []
    let stJoinedShared : SymState LensTestVal :=
      { locals :=
          [ ⟨.choice symCond sRef0 sRef1, .unborrowed⟩
          , ⟨.atom 0, .unborrowed⟩ ]
        loans :=
          [ ⟨0, .activeShared,
              ⟨.node (.atom 10) (.atom 11), .unborrowed⟩, .rootParam 0⟩
          , ⟨1, .activeShared,
              ⟨.node (.atom 20) (.atom 21), .unborrowed⟩, .rootParam 1⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    readPlaceVal lensTestValAlg (.derefSub 0 [1]) stJoinedShared =
      some (.choice symCond (.atom 11) (.atom 21)) ∧
    (match stepAction lensTestValAlg
        (.borrow 1 .shared (.derefSub 0 [0])) stJoinedShared with
     | .ok stReborrowed =>
       readPlaceVal lensTestValAlg (.derefSub 1 []) stReborrowed =
         some (.choice symCond (.atom 10) (.atom 20)) ∧
       match endLoanInState lensTestValAlg 2 stReborrowed with
       | .ok _ => True
       | .fail => False
     | .fail => False) ∧
    -- 3. `renameLoanInState` remaps handles inside pinned spatial blocks:
    let stPinnedRef : SymState LensTestVal :=
      { locals := [⟨.ref 2 [], .mutLocked 0⟩]
        loans :=
          [ ⟨0, .spatialPinned 0 valueCellCodec,
              ⟨.ref 2 [], .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨1, .ended, ⟨.ref 2 [], .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨2, .activeMut, ⟨.atom 55, .unborrowed⟩, .direct (.localReg 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := [⟨0, 0, .readWrite, 0, 0, [.init (.ref 2 [])]⟩]
        nextSpatialTag := 1 }
    (match renameLoanInState lensTestValAlg 1 2 stPinnedRef with
     | some stRenamed =>
       staleHandleTo lensTestValAlg 2 stRenamed = false ∧
       match reabsorbFromSpatialInState lensTestValAlg 0
           valueCellCodec stRenamed with
       | .ok stReabs =>
         match findLoan 0 stReabs.loans with
         | some e0 => e0.cell.val = .ref 1 []
         | none => False
       | .fail => False
     | none => False) ∧
    -- 4. `zipOrKeepSameRef` preserves nested identical references even when
    -- `cVal` has `sizeBound = 1`:
    let deepRef : LensTestVal :=
      .node (.atom 1) (.node (.atom 2) (.ref 4 [0]))
    zipOrKeepSameRef lensTestValAlg (.atom 0) deepRef deepRef = deepRef ∧
    -- 5. `installRegionGroups` locks all groups' inputs before writing any
    -- output handles into `outDsts`:
    let stTwoParams : SymState LensTestVal :=
      { locals := [⟨.ref 0 [], .unborrowed⟩, ⟨.ref 1 [], .unborrowed⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .rootParam 0⟩
          , ⟨1, .activeMut, ⟨.atom 20, .unborrowed⟩, .rootParam 1⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let rg0 : RegionGroupSpec LensTestVal :=
      { groupId := 10
        requiredChildren := []
        inputPlaces := [.derefSub 1 []]
        outDsts := [0]
        fwdOuts := fun _ muts => some muts
        backFn := fun _ _ outs _ => some (outs, []) }
    let rg1 : RegionGroupSpec LensTestVal :=
      { groupId := 20
        requiredChildren := []
        inputPlaces := [.derefSub 0 []]
        outDsts := [1]
        fwdOuts := fun _ muts => some muts
        backFn := fun _ _ outs _ => some (outs, []) }
    (match installRegionGroups lensTestValAlg [] [rg0, rg1] stTwoParams with
     | some stInstalled =>
       readPlaceVal lensTestValAlg (.derefSub 0 []) stInstalled =
         some (.atom 20) ∧
       readPlaceVal lensTestValAlg (.derefSub 1 []) stInstalled =
         some (.atom 10)
     | none => False) ∧
    -- 6. `joinRegionDeposits` aligns deposits by producer `groupId` even when
    -- independent child groups ended in opposite orders:
    joinRegionDeposits lensTestValAlg symCond
      [(10, .atom 1), (20, .atom 2)]
      [(20, .atom 20), (10, .atom 10)] =
      some [(10, .choice symCond (.atom 1) (.atom 10)),
            (20, .choice symCond (.atom 2) (.atom 20))] :=
  ⟨rfl, rfl, rfl, rfl, ⟨rfl, trivial⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl⟩

/-- Tests for:
1. `spatialPinnedRenameConsistent` verifying every `.init` cell (including extra
   cells ignored by `decode`) under loan renaming,
2. `renameLoanInState` rejecting overwriting `tLid` when referenced solely by a
   local/loan `PermTree` entry, a non-ended loan's `BackTarget` (`.direct` or
   `.choiceJoin`), an active `RegionGroupEntry`'s `lockLid`, `outputLoans`, or
   `inputTargets`, or a `SpatialBlock.originLoan`. -/
theorem spatial_pinned_extra_cell_rename_and_loan_ref_tests :
    let ignoredExtraCodec : SpatialCodec LensTestVal :=
      { codecId := 45
        encode := fun v => [.init v, .init (.atom 0)]
        decode := fun cells =>
          match cells with
          | .init v :: _ => some v
          | _ => none
        decode_encode := fun _ => rfl }
    let loansPin : List (LoanEntry LensTestVal) :=
      [⟨0, .spatialPinned 0 ignoredExtraCodec, ⟨.atom 5, .unborrowed⟩,
        .direct (.localReg 0) []⟩]
    let spOld : List (SpatialBlock LensTestVal) :=
      [⟨0, 0, .readWrite, 0, 0, [.init (.atom 5), .init (.ref 2 [])]⟩]
    let spBadNew : List (SpatialBlock LensTestVal) :=
      [⟨0, 0, .readWrite, 0, 0, [.init (.atom 5), .init (.atom 9)]⟩]
    let spGoodNew : List (SpatialBlock LensTestVal) :=
      [⟨0, 0, .readWrite, 0, 0, [.init (.atom 5), .init (.ref 1 [])]⟩]
    let baseLoans : List (LoanEntry LensTestVal) :=
      [ ⟨0, .activeMut, ⟨.atom 1, .unborrowed⟩, .rootParam 0⟩
      , ⟨1, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
      , ⟨2, .activeMut, ⟨.atom 2, .unborrowed⟩, .direct (.localReg 0) []⟩ ]
    let stPermOnly : SymState LensTestVal :=
      ⟨[⟨.atom 1, .mutLocked 1⟩], baseLoans, [], [], [], 0⟩
    let stSharedPermOnly : SymState LensTestVal :=
      ⟨[⟨.atom 1, .shared [1]⟩], baseLoans, [], [], [], 0⟩
    let stTargetDirect : SymState LensTestVal :=
      ⟨[],
       [ ⟨0, .activeMut, ⟨.atom 1, .unborrowed⟩, .rootParam 0⟩
       , ⟨1, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
       , ⟨2, .activeMut, ⟨.atom 2, .unborrowed⟩, .direct (.localReg 0) []⟩
       , ⟨3, .activeMut, ⟨.atom 3, .unborrowed⟩, .direct (.parentLoan 1) []⟩ ],
       [], [], [], 0⟩
    let stTargetCond : SymState LensTestVal :=
      ⟨[],
       [ ⟨0, .activeMut, ⟨.atom 1, .unborrowed⟩, .rootParam 0⟩
       , ⟨1, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
       , ⟨2, .activeMut, ⟨.atom 2, .unborrowed⟩, .direct (.localReg 0) []⟩
       , ⟨3, .activeMut, ⟨.atom 3, .unborrowed⟩,
          ⟨[.direct (.localReg 0) [], .direct (.localReg 0) [],
            .choiceJoin (.ref 1 [])]⟩⟩ ],
       [], [], [], 0⟩
    let stActiveGroupLock : SymState LensTestVal :=
      ⟨[], baseLoans,
       [⟨0, true, 1, [], [], [], fun _ _ => some ([], [])⟩],
       [], [], 0⟩
    let stActiveGroupOut : SymState LensTestVal :=
      ⟨[], baseLoans,
       [⟨0, true, 9, [], [1], [], fun _ _ => some ([], [])⟩], [], [], 0⟩
    let stActiveGroupIn : SymState LensTestVal :=
      ⟨[], baseLoans,
       [⟨0, true, 9, [(.parentLoan 1, [])], [], [], fun _ _ => some ([], [])⟩],
       [], [], 0⟩
    let stSpatialOrigin : SymState LensTestVal :=
      ⟨[], baseLoans, [], [], [⟨0, 1, .readWrite, 0, 0, [.init (.atom 7)]⟩], 1⟩
    spatialPinnedRenameConsistent lensTestValAlg 2 1 loansPin spOld spBadNew =
      false ∧
    spatialPinnedRenameConsistent lensTestValAlg 2 1 loansPin spOld spGoodNew =
      true ∧
    renameLoanInState lensTestValAlg 1 2 stPermOnly = none ∧
    renameLoanInState lensTestValAlg 1 2 stSharedPermOnly = none ∧
    renameLoanInState lensTestValAlg 1 2 stTargetDirect = none ∧
    renameLoanInState lensTestValAlg 1 2 stTargetCond = none ∧
    renameLoanInState lensTestValAlg 1 2 stActiveGroupLock = none ∧
    renameLoanInState lensTestValAlg 1 2 stActiveGroupOut = none ∧
    renameLoanInState lensTestValAlg 1 2 stActiveGroupIn = none ∧
    renameLoanInState lensTestValAlg 1 2 stSpatialOrigin = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete-choice pruning in `backTargetMentionsLoan` and involutive parent
swapping in `swapBackTargetLoan`:
1. When child loan `1` has concrete choice `true` (`trueArm = localReg 0`,
   `falseArm = parentLoan 0`) and `0` is `.ended`, `renameLoanInState alg 0 2`
   succeeds, swaps `falseArm` to `.parentLoan 2`, and allows `endLoanInState` on
   loan `1` afterward.
2. `renameLoanInState alg 0 2` still returns `none` when (i) the taken concrete
   arm points to `.parentLoan 0`, (ii) the condition is symbolic
   (`asBool = none`), or (iii) `.choiceJoin cond` holds a handle to `0`. -/
theorem renameLoanInState_concrete_choice_pruning_tests :
    let mkSt (t1 : BackTarget LensTestVal) : SymState LensTestVal :=
      ⟨[⟨.atom 10, .mutLocked 1⟩, ⟨.atom 20, .mutLocked 2⟩],
       [ ⟨0, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
       , ⟨1, .activeMut, ⟨.atom 77, .unborrowed⟩, t1⟩
       , ⟨2, .activeMut, ⟨.atom 88, .unborrowed⟩, .direct (.localReg 1) []⟩ ],
       [], [], [], 0⟩
    let tPruned : BackTarget LensTestVal :=
      .choice (.atom 1) (.direct (.localReg 0) []) (.direct (.parentLoan 0) [])
    let tTaken : BackTarget LensTestVal :=
      .choice (.atom 0) (.direct (.localReg 0) []) (.direct (.parentLoan 0) [])
    let tSym : BackTarget LensTestVal :=
      .choice (.node (.atom 0) (.atom 1)) (.direct (.localReg 0) [])
        (.direct (.parentLoan 0) [])
    let tCondHandle : BackTarget LensTestVal :=
      .choice (.ref 0 []) (.direct (.localReg 0) []) (.direct (.localReg 1) [])
    (match renameLoanInState lensTestValAlg 0 2 (mkSt tPruned) with
     | some stRenamed =>
       (match findLoan 0 stRenamed.loans, findLoan 1 stRenamed.loans,
            findLoan 2 stRenamed.loans with
        | some e0', some e1', some e2' =>
          e0'.phase.isActiveMut && e2'.phase.isEnded &&
          (match e1'.target.steps with
           | [.choiceJoin c, .direct (.localReg 0) [],
              .direct (.parentLoan 2) []] =>
             lensTestValEq c (.atom 1)
           | _ => false)
        | _, _, _ => false) = true ∧
       (match endLoanInState lensTestValAlg 1 stRenamed with
        | .ok stEnded =>
          (match findLoan 1 stEnded.loans with
           | some e1'' => e1''.phase.isEnded
           | none => false) = true ∧
          getLocal lensTestValAlg 0 stEnded = some (.atom 77)
        | .fail => False)
     | none => False) ∧
    renameLoanInState lensTestValAlg 0 2 (mkSt tTaken) = none ∧
    renameLoanInState lensTestValAlg 0 2 (mkSt tSym) = none ∧
    renameLoanInState lensTestValAlg 0 2 (mkSt tCondHandle) = none :=
  ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl, rfl, rfl⟩

end Anneal.PureLift
