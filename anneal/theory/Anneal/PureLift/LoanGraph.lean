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
import Init.Data.UInt.BasicAux
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree

namespace Anneal.PureLift

/-!
# Unified Loan Graph, Backward Morphisms, and Multi-Region Groups

Models active borrows, nested reborrows, conditional diamond borrow joins, and
multi-region-group call frames as a pure functional directed acyclic graph
(`SymState Val`).

Key design invariants:
- `PlaceCell Val` unifies local variable slots and active loan cells under a
  single `(val, perm)` representation, avoiding duplicated owner dispatch.
- `BackTarget Val` encodes how ending a mutable loan propagates its final value
  back to its parent owner(s), including conditional diamond borrows (`.choice`)
  and interprocedural lenses (`.lensCall` and `.regionOut`).
- `LoanPhase.spatialPinned` represents a mutable loan temporarily exported to
  the spatial memory zone as a loan lifecycle phase rather than a `BackTarget`
  constructor. Consequently, freezing and reabsorbing a loan preserves its
  `BackTarget` intact while automatically blocking pure reads, writes, and
  premature `endLoanInState` calls while pinned.
- `RegionGroupEntry` tracks lifetime outlives dependencies (`requiredChildren`)
  and verifies that all output loans of a region group are unborrowed
  (`isUnborrowed e.cell.perm`) before retiring the group.
-/

/-- Reference to the owner of a borrowed sub-place: either a local variable
register or an enclosing parent loan. -/
inductive OwnerRef where
  | localReg (reg : LocalId)
  | parentLoan (lid : LoanId)

def OwnerRef.beq : OwnerRef → OwnerRef → Bool
  | .localReg r1, .localReg r2 => r1 == r2
  | .parentLoan l1, .parentLoan l2 => l1 == l2
  | _, _ => false

/-- Elementary pre-order step in a serialized `BackTarget Val` tree. -/
inductive BackTargetStep (Val : Type) where
  | rootParam (paramIdx : Nat)
  | direct (owner : OwnerRef) (path : SubPath)
  | choiceJoin (cond : Val)
  | lensCall (targets : List (OwnerRef × SubPath))
      (backFn : Val → Option (List Val))
  | regionOut (groupId : RegionGroupId) (outIdx : Nat)

/-- Compositional backward writeback target for an active loan, represented as a
pre-order step sequence so right-to-left `listFold` (`List.foldr`) evaluates
arbitrarily nested `.choice` trees bottom-up as a computable Lean 4 definition:
- `BackTarget.rootParam paramIdx`: external `&` or `&mut` input parameter of the
  current function.
- `BackTarget.direct owner path`: borrow of `path` inside `owner`.
- `BackTarget.choice cond onTrue onFalse`: diamond conditional borrow merged
  across branches under symbolic condition `cond`.
- `BackTarget.lensCall targets backFn`: single-region interprocedural call
  returning a mutable borrow with backward lens `backFn`.
- `BackTarget.regionOut groupId outIdx`: output borrow `outIdx` of
  multi-region-group call frame `groupId`. -/
structure BackTarget (Val : Type) where
  steps : List (BackTargetStep Val)

namespace BackTarget

def rootParam {Val : Type} (paramIdx : Nat) : BackTarget Val :=
  ⟨[.rootParam paramIdx]⟩

def direct {Val : Type} (owner : OwnerRef) (path : SubPath) : BackTarget Val :=
  ⟨[.direct owner path]⟩

def choice {Val : Type} (cond : Val) (onTrue : BackTarget Val)
    (onFalse : BackTarget Val) : BackTarget Val :=
  ⟨.choiceJoin cond :: (onTrue.steps ++ onFalse.steps)⟩

def lensCall {Val : Type} (targets : List (OwnerRef × SubPath))
    (backFn : Val → Option (List Val)) : BackTarget Val :=
  ⟨[.lensCall targets backFn]⟩

def regionOut {Val : Type} (groupId : RegionGroupId) (outIdx : Nat) :
    BackTarget Val :=
  ⟨[.regionOut groupId outIdx]⟩

end BackTarget

/-- True iff `BackTarget` (or any branch inside a nested `.choice` tree)
contains a `.regionOut` target that must be retired via `endRegionGroupInState`
rather than `endLoanInState`. -/
def isRegionOutTarget {Val : Type} (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun step ih =>
      match step with
      | .regionOut _ _ => true
      | _ => ih)
    false

/-- True iff `BackTarget` (or any branch inside a nested `.choice` tree)
contains a `.rootParam` step, which represents an external caller parameter.
Only a bare `[.rootParam idx]` target is finalized at function return
(`collectRootMutVals`, via `rootParamIdxOpt`). A `.rootParam` nested inside a
larger target can neither be ended (`deactivateLoan` rejects it through
`activeTargetHasSpecial`) nor returned (`loansCleanAtReturn` requires every
non-root loan to have ended), so a run holding such a loan fails. -/
def isRootParamTarget {Val : Type} (t : BackTarget Val) : Bool :=
  t.steps.foldr
    (fun step ih =>
      match step with
      | .rootParam _ => true
      | _ => ih)
    false

/-- True iff the pre-order step sequence of `target` encodes exactly one tree:
every `.choiceJoin` finds two subtrees and one tree remains. The check ignores
conditions, so a malformed subtree is caught even inside an arm that a
concrete condition would discard. Branch-sensitive folds over `target` check
this first and fail closed when it does not hold. -/
def targetWellFormed {Val : Type} (target : BackTarget Val) : Bool :=
  match
    target.steps.foldr
      (fun step (acc : Option Nat) =>
        match acc with
        | none => none
        | some d =>
          match step with
          | .choiceJoin _ =>
            match d with
            | d' + 2 => some (d' + 1)
            | _ => none
          | _ => some (d + 1))
      (some 0)
  with
  | some 1 => true
  | _ => false

/-- Branch-sensitive variant of `isRegionOutTarget || isRootParamTarget`: true
iff an active branch of `target` contains a `.rootParam` or `.regionOut` step.
Untaken branches of a `.choice` whose condition is concrete are ignored; both
branches of a symbolic choice count. A malformed target (`targetWellFormed`)
counts as special. -/
def activeTargetHasSpecial {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
  !targetWellFormed target ||
  let stk : List Bool :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => true :: acc
        | .direct _ _ => false :: acc
        | .choiceJoin cond =>
          match acc with
          | bTrue :: bFalse :: rest =>
            let merged :=
              match alg.asBool cond with
              | some true => bTrue
              | some false => bFalse
              | none => bTrue || bFalse
            merged :: rest
          | _ => [true]
        | .lensCall _ _ => false :: acc
        | .regionOut _ _ => true :: acc)
      []
  match stk with
  | [b] => b
  | _ => true

/-- True iff `target` is `.regionOut gid expectedIdx`. -/
def isMatchingRegionOut {Val : Type} (gid : RegionGroupId)
    (expectedIdx : Nat) (t : BackTarget Val) : Bool :=
  match t.steps with
  | [.regionOut g idx] => g == gid && idx == expectedIdx
  | _ => false

/-- Look up the updated value for `(owner, path)` from a parallel `(targets,
vals)` list produced by a `.lensCall` backward function, returning `none` if
`targets` and `vals` have different lengths, and `some vOld` if `(owner, path)`
does not appear in `targets`. -/
def lookupLensTargetVal {Val : Type} (owner : OwnerRef) (path : SubPath)
    (vOld : Val) (targets : List (OwnerRef × SubPath)) (vals : List Val) :
    Option Val :=
  targets.foldr
    (fun op ih vs =>
      match op, vs with
      | (o, p), vUpd :: restVals =>
        match ih restVals with
        | some tailVal =>
          if OwnerRef.beq owner o && subPathEq path p then
            some vUpd
          else
            some tailVal
        | none => none
      | _, [] => none)
    (fun vs =>
      match vs with
      | [] => some vOld
      | _ :: _ => none)
    vals

/-- True iff `(owner, path)` overlaps with any `(o, p)` entry in `xs`
(`OwnerRef.beq owner o && subPathOverlaps path p`). -/
def overlapsAnyOwnerPath (owner : OwnerRef) (path : SubPath)
    (xs : List (OwnerRef × SubPath)) : Bool :=
  xs.foldr
    (fun op ih =>
      match op with
      | (o, p) =>
        if OwnerRef.beq owner o && subPathOverlaps path p then true else ih)
    false

/-- True iff all `(owner, path)` entries in `xs` are pairwise disjoint (neither
equal nor overlapping sub-paths of the same owner). -/
def ownerPathsDisjoint (xs : List (OwnerRef × SubPath)) : Bool :=
  match
    xs.foldr
      (fun op acc =>
        match op, acc with
        | (o, p), (ok, seen) =>
          (ok && !overlapsAnyOwnerPath o p seen, (o, p) :: seen))
      (true, [])
  with
  | (ok, _) => ok

/-- True iff `(owner, path)` occurs in `xs`. -/
def containsOwnerPath (owner : OwnerRef) (path : SubPath)
    (xs : List (OwnerRef × SubPath)) : Bool :=
  xs.foldr
    (fun op ih =>
      match op with
      | (o, p) =>
        if OwnerRef.beq owner o && subPathEq path p then true else ih)
    false

/-- Deduplicate a list of `(OwnerRef × SubPath)` leaves via total structural
recursion so diamond writeback updates each underlying leaf once without
truncating large leaf sets. -/
def dedupOwnerPaths (xs : List (OwnerRef × SubPath)) :
    List (OwnerRef × SubPath) :=
  xs.foldr
    (fun op tail =>
      match op with
      | (o, p) =>
        if containsOwnerPath o p tail then tail else (o, p) :: tail)
    []

/-- Collect all leaf `(OwnerRef × SubPath)` targets referenced anywhere in
`target` via total structural recursion (`List.foldr`). -/
def targetLeaves {Val : Type} (target : BackTarget Val) :
    List (OwnerRef × SubPath) :=
  target.steps.foldr
    (fun step acc =>
      match step with
      | .rootParam _ => acc
      | .direct o p => (o, p) :: acc
      | .choiceJoin _ => acc
      | .lensCall targets _ => targets ++ acc
      | .regionOut _ _ => acc)
    []

/-- Collect the active leaf `(OwnerRef × SubPath)` targets of `target`, pruning
untaken branches whenever `.choiceJoin cond` has a concrete boolean condition
`alg.asBool cond = some b`. A malformed step sequence (a truncated `.choiceJoin`
or a stack that does not reduce to one tree) conservatively yields every
serialized leaf (`targetLeaves`), so dependency checks such as
`noActiveChildLoanEdgesIn` can never lose an edge through a malformed child
target. -/
def activeTargetLeaves {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : List (OwnerRef × SubPath) :=
  let res : Bool × List (List (OwnerRef × SubPath)) :=
    target.steps.foldr
      (fun step (acc : Bool × List (List (OwnerRef × SubPath))) =>
        match acc with
        | (ok, stk) =>
          match step with
          | .rootParam _ => (ok, [] :: stk)
          | .direct o p => (ok, [(o, p)] :: stk)
          | .choiceJoin cond =>
            match stk with
            | lTrue :: lFalse :: rest =>
              let merged :=
                match alg.asBool cond with
                | some true => lTrue
                | some false => lFalse
                | none => lTrue ++ lFalse
              (ok, merged :: rest)
            | _ => (false, [[]])
          | .lensCall targets _ => (ok, targets :: stk)
          | .regionOut _ _ => (ok, [] :: stk))
      (true, [])
  match res with
  | (true, [leaves]) => leaves
  | _ => targetLeaves target

/-- Verify a shared-loan `BackTarget` step tree. It rejects a malformed step
sequence anywhere in the tree (`targetWellFormed`), even inside an arm that a
concrete condition discards. In the active branches only (both arms of a
symbolic `.choice`, the taken arm of a concrete one), it also rejects
`.rootParam` and `.regionOut` targets and `.choice` trees whose branches
target distinct overlapping sub-paths of the same owner. -/
def validateSharedBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) : Bool :=
  if !targetWellFormed target then false
  else if
    !ownerPathsDisjoint (dedupOwnerPaths (activeTargetLeaves alg target))
  then false
  else
    let stk : List Bool :=
      target.steps.foldr
        (fun step acc =>
          match step with
          | .rootParam _ => false :: acc
          | .direct _ _ => true :: acc
          | .choiceJoin cond =>
            match acc with
            | bTrue :: bFalse :: rest =>
              let ok :=
                match alg.asBool cond with
                | some true => bTrue
                | some false => bFalse
                | none => bTrue && bFalse
              ok :: rest
            | _ => [false]
          | .lensCall targets _ => ownerPathsDisjoint targets :: acc
          | .regionOut _ _ => false :: acc)
        []
    match stk with
    | [true] => true
    | _ => false

/-- Verify that the pre-order step sequence of `target` is well-formed
everywhere (`targetWellFormed`), even inside an arm that a concrete condition
discards, and, in the active branches only, that every `.lensCall` has
pairwise-disjoint `targets` and succeeds on its branch-projected loan value
with a value list matching its `targets` arity, that no `.choice` branches
target distinct overlapping sub-paths of the same owner, and that no
`.rootParam` or `.regionOut` node appears. -/
def validateBackTarget {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) (vNew : Val) : Bool :=
  if !targetWellFormed target then false
  else if
    !ownerPathsDisjoint (dedupOwnerPaths (activeTargetLeaves alg target))
  then false
  else
    let stk : List (Val → Bool) :=
      target.steps.foldr
        (fun step acc =>
          match step with
          | .rootParam _ => (fun _ => false) :: acc
          | .direct _ _ => (fun _ => true) :: acc
          | .choiceJoin cond =>
            match acc with
            | fTrue :: fFalse :: rest =>
              let fBranch : Val → Bool :=
                fun vCur =>
                  match alg.asBool cond with
                  | some true => fTrue vCur
                  | some false => fFalse vCur
                  | none =>
                    fTrue (alg.projectBranchVal cond true vCur) &&
                    fFalse (alg.projectBranchVal cond false vCur)
              fBranch :: rest
            | _ => [fun _ => false]
          | .lensCall targets backFn =>
            let fLeaf : Val → Bool :=
              fun vCur =>
                ownerPathsDisjoint targets &&
                match backFn vCur with
                | some vals => vals.length == targets.length
                | none => false
            fLeaf :: acc
          | .regionOut _ _ => (fun _ => false) :: acc)
        []
    match stk with
    | [fRoot] => fRoot vNew
    | _ => false

/-- Rebuild `v1` with each field present in both `v1` and `v2` replaced by
`ih f1 f2`, visiting every index below `maxFields` (gaps included). Fails if
some index is a field of only one of the two values. Callers pass a bound
above every field index of both values (`getField_lt_sizeBound`), so no field
is skipped. -/
def zipAggregateFields {Val : Type} (alg : ValAlgebra Val)
    (ih : Val → Val → Val) (maxFields : Nat) (v1 v2 : Val) : Option Val :=
  @Nat.recCompiled (fun _ => Nat → Val → Option Val)
    (fun _ acc => some acc)
    (fun _ ihField idx acc =>
      match alg.getField idx v1, alg.getField idx v2 with
      | none, none => ihField (idx + 1) acc
      | some f1, some f2 =>
        match alg.setField idx acc (ih f1 f2) with
        | some acc' => ihField (idx + 1) acc'
        | none => none
      | _, _ => none)
    maxFields 0 v1

/-- True iff `v` has a field at some index (below `alg.sizeBound v`, which
bounds every field index). -/
def hasAnyField {Val : Type} (alg : ValAlgebra Val) (v : Val) : Bool :=
  natFold false
    (fun idx acc =>
      acc ||
        match alg.getField idx v with
        | some _ => true
        | none => false)
    (alg.sizeBound v)

/-- Merge two values under symbolic branch condition `cond`, preserving an
encoded reference handle unchanged when both branches hold a reference to the
exact same `(lid, path)` that `alg.sameRefVal` vouches are equal as full `Val`
values (`sameRefVal_eq`), and recursively merging aggregate fields when both
branches hold aggregates that `sameAggregateShape` relates and whose fields
occupy the same indices, so field projections (`alg.getField`) remain
available after a symbolic branch join. Because `getField_lt_sizeBound`
guarantees `sizeBound c < sizeBound v` for every child field `c`, the outer
budget `max (alg.sizeBound v1) (alg.sizeBound v2) + 1` strictly bounds every
nested aggregate field chain. -/
def zipOrKeepSameRef {Val : Type} (alg : ValAlgebra Val)
    (cond v1 v2 : Val) : Val :=
  @Nat.recCompiled (fun _ => Val → Val → Val)
    (fun a b =>
      match alg.decodeRef a, alg.decodeRef b with
      | some (l1, p1), some (l2, p2) =>
        if l1 == l2 && subPathEq p1 p2 && alg.sameRefVal a b then a
        else alg.zipVal cond a b
      | _, _ => alg.zipVal cond a b)
    (fun _ ih a b =>
      match alg.decodeRef a, alg.decodeRef b with
      | some (l1, p1), some (l2, p2) =>
        if l1 == l2 && subPathEq p1 p2 && alg.sameRefVal a b then a
        else alg.zipVal cond a b
      | _, _ =>
        -- Rebuilding from `a` is exact only when `a` and `b` differ at most
        -- in their fields (`sameAggregateShape_ext`).
        let fieldBound :=
          if decide (alg.sizeBound a ≤ alg.sizeBound b) then alg.sizeBound b
          else alg.sizeBound a
        if hasAnyField alg a && hasAnyField alg b &&
           alg.sameAggregateShape a b then
          match zipAggregateFields alg ih fieldBound a b with
          | some agg => agg
          | none => alg.zipVal cond a b
        else alg.zipVal cond a b)
    ((if decide (alg.sizeBound v1 ≤ alg.sizeBound v2) then alg.sizeBound v2
      else alg.sizeBound v1) + 1) v1 v2

/-- Evaluate the updated sub-value for `(owner, path)` when ending a loan with
`target`, new loan value `vNew`, and prior owner sub-value `vOld`. Supports
`.direct`, `.lensCall`, and arbitrarily nested `.choice` trees with
branch-sensitive evaluation and branch-specific value projection of both `vNew`
and `vOld`. A malformed step sequence (`targetWellFormed`) gives `none`. -/
def evalBackVal {Val : Type} (alg : ValAlgebra Val)
    (owner : OwnerRef) (path : SubPath)
    (target : BackTarget Val) (vNew vOld : Val) : Option Val :=
  if !targetWellFormed target then none
  else
  let stk : List (Val → Val → Option Val) :=
    target.steps.foldr
      (fun step acc =>
        match step with
        | .rootParam _ => (fun _ _ => none) :: acc
        | .direct o p =>
          let fLeaf : Val → Val → Option Val :=
            fun vCur vOldCur =>
              if OwnerRef.beq owner o && subPathEq path p then some vCur
              else some vOldCur
          fLeaf :: acc
        | .choiceJoin cond =>
          match acc with
          | fTrue :: fFalse :: rest =>
            let fBranch : Val → Val → Option Val :=
              fun vCur vOldCur =>
                match alg.asBool cond with
                | some true => fTrue vCur vOldCur
                | some false => fFalse vCur vOldCur
                | none =>
                  -- Both values are projected onto each branch before the
                  -- branch results are recombined with `zipOrKeepSameRef`
                  -- (preserving aggregate field structure and identical
                  -- reference handles across choice writeback joins).
                  match fTrue (alg.projectBranchVal cond true vCur)
                              (alg.projectBranchVal cond true vOldCur),
                        fFalse (alg.projectBranchVal cond false vCur)
                               (alg.projectBranchVal cond false vOldCur) with
                  | some v1, some v2 => some (zipOrKeepSameRef alg cond v1 v2)
                  | _, _ => none
            fBranch :: rest
          | _ => [fun _ _ => none]
        | .lensCall targets backFn =>
          let fLeaf : Val → Val → Option Val :=
            fun vCur vOldCur =>
              if !containsOwnerPath owner path targets then
                some vOldCur
              else
                match backFn vCur with
                | some updatedVals =>
                  lookupLensTargetVal owner path vOldCur targets updatedVals
                | none => none
          fLeaf :: acc
        | .regionOut _ _ => (fun _ _ => none) :: acc)
      []
  match stk with
  | [fRoot] => fRoot vNew vOld
  | _ => none

/-- Low-level spatial memory cell supporting initialized values, uninitialized
storage (`.uninit`), and raw byte views (`.rawByte`). A raw byte is a `UInt8`
so the representation cannot hold values outside Rust's 8-bit byte range. -/
inductive CellVal (Val : Type) where
  | init (v : Val)
  | uninit
  | rawByte (b : UInt8)

/-- True iff any cell in `cells` is `.uninit`. -/
def hasUninitCell {Val : Type} (cells : List (CellVal Val)) : Bool :=
  cells.foldr
    (fun c ih =>
      match c with
      | .uninit => true
      | .init _ => ih
      | .rawByte _ => ih)
    false

/-- Representation codec converting between pure values (`Val`) and spatial
memory cells (`List (CellVal Val)`), carrying a kernel-checked round-trip law
`decode_encode`. -/
structure SpatialCodec (Val : Type) where
  codecId : Nat
  encode : Val → List (CellVal Val)
  decode : List (CellVal Val) → Option Val
  decode_encode : ∀ v : Val, decode (encode v) = some v

/-- Lifecycle phase of a loan in the loan graph. `.spatialPinned` binds the
exact `SpatialCodec Val` used to freeze the loan so reabsorption cannot
substitute an unrelated decoder. -/
inductive LoanPhase (Val : Type) where
  | activeShared : LoanPhase Val
  | activeMut : LoanPhase Val
  | spatialPinned (bid : BlockId) (codec : SpatialCodec Val) : LoanPhase Val
  | ended : LoanPhase Val

def LoanPhase.isActive {Val : Type} : LoanPhase Val → Bool
  | .activeShared => true
  | .activeMut => true
  | .spatialPinned _ _ => false
  | .ended => false

def LoanPhase.isActiveMut {Val : Type} : LoanPhase Val → Bool
  | .activeMut => true
  | _ => false

def LoanPhase.isEnded {Val : Type} : LoanPhase Val → Bool
  | .ended => true
  | _ => false

def LoanPhase.samePhase {Val : Type} : LoanPhase Val → LoanPhase Val → Bool
  | .activeShared, .activeShared => true
  | .activeMut, .activeMut => true
  | .ended, .ended => true
  | _, _ => false

/-- Permissioned value cell shared by local variable slots and loan entries. -/
structure PlaceCell (Val : Type) where
  val : Val
  perm : PermTree

/-- Single node in the unified loan graph. -/
structure LoanEntry (Val : Type) where
  id : LoanId
  phase : LoanPhase Val
  cell : PlaceCell Val
  target : BackTarget Val

/-- Multi-region-group call frame tracking a lifetime group `groupId`, its
locked input places, its output loans, its required shorter-lived child groups,
and its pure backward function `backFn`. -/
structure RegionGroupEntry (Val : Type) where
  groupId : RegionGroupId
  active : Bool
  lockLid : LoanId
  inputTargets : List (OwnerRef × SubPath)
  outputLoans : List LoanId
  requiredChildren : List RegionGroupId
  backFn : List Val → List Val → Option (List Val × List Val)

/-- Spatial memory access permission for hybrid spatial blocks. -/
inductive SpatialPerm where
  | readOnly
  | readWrite

/-- Spatial memory block exported from an active mutable loan. -/
structure SpatialBlock (Val : Type) where
  blockId : BlockId
  originLoan : LoanId
  perm : SpatialPerm
  provenanceTag : Nat
  activeSubSplits : Nat
  cells : List (CellVal Val)

/-- Complete pure symbolic state of a `PureLift` evaluation.

Each entry `(gid, v)` of `regionDeposits` is a value deposited by the backward
function of region group `gid` when it ended. Only a group that lists `gid` in
its `requiredChildren` receives (and consumes) those values; see
`takeChildDeposits`. -/
structure SymState (Val : Type) where
  locals : List (PlaceCell Val)
  loans : List (LoanEntry Val)
  regionGroups : List (RegionGroupEntry Val)
  regionDeposits : List (RegionGroupId × Val)
  spatial : List (SpatialBlock Val)
  nextSpatialTag : Nat

/-- Look up index `idx` in `xs`, returning `defVal` when out of bounds. -/
def listGetVal {α : Type} (defVal : α) (idx : Nat) (xs : List α) : α :=
  natFold
    (fun ys =>
      match ys with
      | [] => defVal
      | x :: _ => x)
    (fun _ ih ys =>
      match ys with
      | [] => defVal
      | _ :: rest => ih rest)
    idx xs

def getLocalCell {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : PlaceCell Val :=
  listGetVal ⟨alg.defaultVal, .unborrowed⟩ reg st.locals

/-- Force a `SubPerm` and its head loan IDs to constructor WHNF. -/
def strictSubPerm (sp : SubPerm) : SubPerm :=
  match sp with
  | .shared [] => .shared []
  | .shared [l1] => .shared [l1]
  | .shared [l1, l2] => .shared [l1, l2]
  | .shared (l1 :: l2 :: l3 :: ls) => .shared (l1 :: l2 :: l3 :: ls)
  | .mutLocked lid => .mutLocked lid
  | .mutJoined m s => .mutJoined m s

/-- Force a `(SubPath × SubPerm)` entry to constructor WHNF. -/
def strictSplitEntry (e : SubPath × SubPerm) : SubPath × SubPerm :=
  match e with
  | ([], sp) => ([], strictSubPerm sp)
  | ([f1], sp) => ([f1], strictSubPerm sp)
  | ([f1, f2], sp) => ([f1, f2], strictSubPerm sp)
  | (f1 :: f2 :: fs, sp) => (f1 :: f2 :: fs, strictSubPerm sp)

/-- Construct a `PlaceCell Val` after forcing `p : PermTree` (including `.split`
entry spines) to weak head normal form so multi-step plans never accumulate
chains of unreduced `PermTree` thunks inside `PlaceCell.perm`. -/
def mkStrictPlaceCell {Val : Type} (v : Val) (p : PermTree) : PlaceCell Val :=
  match p with
  | .unborrowed => ⟨v, .unborrowed⟩
  | .shared [] => ⟨v, .unborrowed⟩
  | .shared [l1] => ⟨v, .shared [l1]⟩
  | .shared (l1 :: l2 :: ls) => ⟨v, .shared (l1 :: l2 :: ls)⟩
  | .mutLocked lid => ⟨v, .mutLocked lid⟩
  | .mutJoined m s => ⟨v, .mutJoined m s⟩
  | .split [] => ⟨v, .unborrowed⟩
  | .split [e1] =>
    match strictSplitEntry e1 with
    | (p1, sp1) => ⟨v, .split [(p1, sp1)]⟩
  | .split [e1, e2] =>
    match strictSplitEntry e1, strictSplitEntry e2 with
    | (p1, sp1), (p2, sp2) => ⟨v, .split [(p1, sp1), (p2, sp2)]⟩
  | .split (e1 :: e2 :: e3 :: rest) =>
    match strictSplitEntry e1, strictSplitEntry e2, strictSplitEntry e3 with
    | (p1, sp1), (p2, sp2), (p3, sp3) =>
      ⟨v, .split ((p1, sp1) :: (p2, sp2) :: (p3, sp3) :: rest)⟩

/-- Single-pass linear modifier for an existing local register `idx`. Fails
when `idx` is not below `xs.length`: a local that no plan step has written has
no value to read, borrow, or update. Only a whole-local write may create the
next fresh local (`setLocalChecked`). -/
def modifyLocalAt {Val : Type}
    (f : Val → PermTree → Option (Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      | [] => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (v', p') => some (mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] => none
      | x :: rest =>
        match ih rest with
        | some rest' => some (x :: rest')
        | none => none)
    idx xs

def getLocalPerm {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : PermTree :=
  (getLocalCell alg reg st).perm

/-- Count occurrences of loan ID `lid` in `loans`. -/
def countLoanId {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Nat :=
  loans.foldr (fun e ih => if e.id == lid then ih + 1 else ih) 0

/-- True iff `lid` occurs exactly once in `loans`. -/
def hasUniqueLoanId {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  countLoanId lid loans == 1

/-- Find loan `lid` in `loans`. -/
def findLoan {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Option (LoanEntry Val) :=
  loans.foldr
    (fun e ih => if e.id == lid then some e else ih)
    none

/-- Update loan `lid` in `loans`. -/
def updateLoan {Val : Type} (lid : LoanId)
    (f : LoanEntry Val → LoanEntry Val)
    (loans : List (LoanEntry Val)) : List (LoanEntry Val) :=
  loans.foldr
    (fun e ih => if e.id == lid then f e :: ih else e :: ih)
    []

/-- `xs` with the first occurrence of `x` removed. -/
def removeOneNat (x : Nat) (xs : List Nat) : List Nat :=
  listFold [] (fun y rest ih => if y == x then rest else y :: ih) xs

/-- Multiset union of `xs` and `ys` in which each element occurs as often as
in whichever of the two lists holds it more often. -/
def maxUnionNat (xs ys : List Nat) : List Nat :=
  xs ++ xs.foldr (fun x acc => removeOneNat x acc) ys

/-- Multiset intersection of `xs` and `ys` in which each element occurs as
often as in whichever of the two lists holds it less often. -/
def minInterNat (xs ys : List Nat) : List Nat :=
  match
    xs.foldr
      (fun x (acc : List Nat × List Nat) =>
        match acc with
        | (out, rest) =>
          if elemLoanId x rest then (x :: out, removeOneNat x rest)
          else (out, rest))
      ([], ys)
  with
  | (out, _) => out

/-- Decoded borrow handle identity `(lid, path, isShared)`, recording the
target loan ID, sub-path, and whether the handle uses the shared-reference
encoding (`alg.decodeRefIsShared`). -/
abbrev HandleRef := LoanId × SubPath × Bool

/-- Structural equality on `(LoanId × SubPath × Bool)` borrow handle identities. -/
def handleRefEq (a b : HandleRef) : Bool :=
  a.1 == b.1 && subPathEq a.2.1 b.2.1 && a.2.2 == b.2.2

/-- True iff `r` occurs in `rs`. -/
def elemHandleRef (r : HandleRef) (rs : List HandleRef) :
    Bool :=
  rs.foldr (fun x ih => if handleRefEq x r then true else ih) false

/-- `rs` with the first occurrence of `r` removed. -/
def removeOneHandleRef (r : HandleRef)
    (rs : List HandleRef) : List HandleRef :=
  listFold [] (fun y rest ih => if handleRefEq y r then rest else y :: ih) rs

/-- Multiset union of handle-reference lists `xs` and `ys` in which each
`HandleRef` occurs as often as in whichever list holds it more
often. -/
def maxUnionHandleRef (xs ys : List HandleRef) :
    List HandleRef :=
  xs ++ xs.foldr (fun x acc => removeOneHandleRef x acc) ys

/-- Multiset intersection of handle-reference lists `xs` and `ys` in which each
`HandleRef` occurs as often as in whichever list holds it less
often. -/
def minInterHandleRef (xs ys : List HandleRef) :
    List HandleRef :=
  match
    xs.foldr
      (fun x (acc : List HandleRef × List HandleRef) =>
        match acc with
        | (out, rest) =>
          if elemHandleRef x rest then
            (x :: out, removeOneHandleRef x rest)
          else (out, rest))
      ([], ys)
  with
  | (out, _) => out

/-- Number of occurrences of handle reference `r` in `rs`. -/
def countHandleRef (r : HandleRef)
    (rs : List HandleRef) : Nat :=
  rs.foldr (fun y n => if handleRefEq y r then n + 1 else n) 0

/-- The truth value that the branch context `ctx` assigns to `cond`, if any.
A branch context lists symbolic conditions with the truth value each takes in
one family of branches; `alg.sameCond` identifies the same condition. -/
def lookupCond {Val : Type} (alg : ValAlgebra Val)
    (ctx : List (Val × Bool)) (cond : Val) : Option Bool :=
  ctx.foldr
    (fun entry ih =>
      match entry with
      | (c, b) => if alg.sameCond c cond then some b else ih)
    none

/-- `(LoanId × SubPath × Bool)` triples named by the borrow handles in `v` in
the branches described by `ctx`, with multiplicity, or `none` if `v` nests more
deeply than its traversal budget `alg.sizeBound v + 1` or contains a choice
whose guard is not handle-free. -/
def collectHandleRefsIn {Val : Type} (alg : ValAlgebra Val) (lower : Bool)
    (ctx : List (Val × Bool)) (v : Val) : Option (List HandleRef) :=
  natFold (fun _ => none)
    (fun _ ih w =>
      match alg.decodeRef w with
      | some (lid, path) => some [(lid, path, alg.decodeRefIsShared w)]
      | none =>
        let fromFields : Option (List HandleRef) :=
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
        let fromArms : Option (List HandleRef) :=
          match alg.branchSplit w with
          | none => some []
          | some (cond, vt, vf) =>
            match ih cond, ih vt, ih vf with
            | some [], some lt, some lf =>
              if lt == lf then some lt
              else
                match lookupCond alg ctx cond with
                | some true => some lt
                | some false => some lf
                | none =>
                  some
                    (if lower then minInterHandleRef lt lf
                     else maxUnionHandleRef lt lf)
            | _, _, _ => none
        match fromFields, fromArms with
        | some ls, some ls' =>
          some (if lower then maxUnionHandleRef ls ls' else ls ++ ls')
        | _, _ => none)
    (alg.sizeBound v + 1) v

/-- `HandleRef` triples named by the borrow handles in `v` in any
branch, with multiplicity. -/
def collectHandleRefs {Val : Type} (alg : ValAlgebra Val) (v : Val) :
    Option (List HandleRef) :=
  collectHandleRefsIn alg false [] v

/-- Concatenated `collectHandleRefsIn` of every value in `vs`. -/
def collectHandleRefsListIn {Val : Type} (alg : ValAlgebra Val) (lower : Bool)
    (ctx : List (Val × Bool)) (vs : List Val) :
    Option (List HandleRef) :=
  vs.foldr
    (fun v acc =>
      match collectHandleRefsIn alg lower ctx v, acc with
      | some ls, some rest => some (ls ++ rest)
      | _, _ => none)
    (some [])

/-- Loan IDs named by the borrow handles in `v` in the branches described by
`ctx`, with multiplicity, or `none` if `v` nests more deeply than its traversal
budget `alg.sizeBound v + 1`. -/
def collectHandlesIn {Val : Type} (alg : ValAlgebra Val) (lower : Bool)
    (ctx : List (Val × Bool)) (v : Val) : Option (List LoanId) :=
  match collectHandleRefsIn alg lower ctx v with
  | some refs => some (refs.map Prod.fst)
  | none => none

/-- Loan IDs named by the borrow handles in `v` in any branch, with
multiplicity: the upper bound of `collectHandlesIn` with no fixed conditions.
An unchanged unique handle in both arms of `zipVal c h h` occurs once. -/
def collectHandles {Val : Type} (alg : ValAlgebra Val) (v : Val) :
    Option (List LoanId) :=
  collectHandlesIn alg false [] v

/-- True iff `v` contains no decodable borrow handle (`collectHandles`). -/
def handleFreeVal {Val : Type} (alg : ValAlgebra Val) (v : Val) : Bool :=
  match collectHandles alg v with
  | some [] => true
  | _ => false

/-- True iff neither the return value nor any final `&mut` parameter value of
`out` contains a borrow handle. -/
def handleFreeOut {Val : Type} (alg : ValAlgebra Val) (out : FuncOut Val) :
    Bool :=
  handleFreeVal alg out.ret && out.mutFinals.all (handleFreeVal alg)

/-- Concatenated `collectHandlesIn` of every value in `vs`. -/
def collectHandlesListIn {Val : Type} (alg : ValAlgebra Val) (lower : Bool)
    (ctx : List (Val × Bool)) (vs : List Val) : Option (List LoanId) :=
  match collectHandleRefsListIn alg lower ctx vs with
  | some refs => some (refs.map Prod.fst)
  | none => none

/-- True iff a handle to loan `lid` may be duplicated: `lid` names exactly one
loan, and that loan is currently `.activeShared`. Handles to `.activeMut`,
`.spatialPinned`, or `.ended` loans are never copyable (ending a loan retires
its entry before writeback runs, so treating `.ended` as copyable would let a
backward lens fabricate a dangling handle to the retiring loan). -/
def handleCopyable {Val : Type} (loans : List (LoanEntry Val))
    (lid : LoanId) : Bool :=
  hasUniqueLoanId lid loans &&
    match findLoan lid loans with
    | some e =>
      match e.phase with
      | .activeShared => true
      | .ended => false
      | .activeMut => false
      | .spatialPinned _ _ => false
    | none => false

/-- True iff the decoded borrow handle `r = (lid, path, isShared)` may be freely
copied or introduced: `path` must be the loan root `[]` (every shared borrow
allocates its own loan entry rooted at `[]`, so a non-empty sub-path on a shared
handle would grant unrecorded sub-place authority), `isShared` must be `true`
(so mutable-form encodings in algebras where `encodeRef` and `encodeSharedRef`
differ cannot be fabricated from an `.activeShared` loan), and `lid` must
satisfy `handleCopyable loans`. -/
def handleRefCopyable {Val : Type} (_alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (r : HandleRef) : Bool :=
  r.2.1.isEmpty && r.2.2 && handleCopyable loans r.1

/-- True iff the decoded handle `r = (lid, path, isShared)` names a unique
active loan in `loans` whose phase matches the handle's encoding flavor `isShared`:
- for `.activeShared`, `isShared` must be `true`,
- for `.activeMut`, `isShared` must equal
  `alg.decodeRefIsShared (alg.encodeRef lid path)`. -/
def handleFlavorMatchesLoan {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (r : HandleRef) : Bool :=
  if !hasUniqueLoanId r.1 loans then false
  else
    match findLoan r.1 loans with
    | some e =>
      match e.phase with
      | .activeShared => r.2.2
      | .activeMut =>
        r.2.2 == alg.decodeRefIsShared (alg.encodeRef r.1 r.2.1)
      | .spatialPinned _ _ => false
      | .ended => false
    | none => false

/-- True iff `v` may be duplicated into the symbolic state: every borrow handle
inside it (`collectHandleRefs`) satisfies `handleRefCopyable`. Reading a value
out of the symbolic state never invalidates its source, so a mutable reference
must be transferred by reborrowing it rather than by copying its handle. -/
def copyableVal {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (v : Val) : Bool :=
  match collectHandleRefs alg v with
  | some refs => refs.all (handleRefCopyable alg loans)
  | none => false

/-- Fallible copy-assignment to a local register: writes `v` to local `reg`
only if `v` satisfies `copyableVal alg st.loans v` (so no active mutable or
spatially pinned borrow handle can be duplicated or fabricated) and either
`reg` already exists with `canWritePath []` permission or `reg` is exactly
one past the end (appending a fresh unborrowed local). -/
def setLocalChecked {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (v : Val) (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    if !copyableVal alg loans v then none
    else if reg == locals.length then
      some ⟨locals ++ [⟨v, .unborrowed⟩], loans, rgs, deps, sp, tag⟩
    else
      match modifyLocalAt
          (fun _ p => if canWritePath [] p then some (v, p) else none)
          reg locals with
      | some locals' => some ⟨locals', loans, rgs, deps, sp, tag⟩
      | none => none

/-- Number of occurrences of `x` in `xs`. -/
def countNat (x : Nat) (xs : List Nat) : Nat :=
  xs.foldr (fun y n => if y == x then n + 1 else n) 0

/-- Symbolic choice guards inside `v` (in fields and in arms, but not inside
other guards), with repetition. A value nested more deeply than its traversal
budget contributes only the guards found within the budget; `collectHandlesIn`
fails on such a value anyway. -/
def collectConds {Val : Type} (alg : ValAlgebra Val) (v : Val) : List Val :=
  natFold (fun _ => [])
    (fun _ ih w =>
      match alg.decodeRef w with
      | some _ => []
      | none =>
        let fromFields : List Val :=
          natFold []
            (fun idx acc =>
              match alg.getField idx w with
              | some field => acc ++ ih field
              | none => acc)
            (alg.sizeBound w)
        let fromArms : List Val :=
          match alg.branchSplit w with
          | none => []
          | some (cond, vt, vf) =>
            let own : List Val :=
              match alg.asBool cond with
              | some _ => []
              | none => [cond]
            own ++ ih vt ++ ih vf
        fromFields ++ fromArms)
    (alg.sizeBound v + 1) v

/-- The distinct guards among `conds` that `alg.sameCond` can identify (those
it reports equal to themselves). A guard it cannot identify can never be
fixed by a branch context, so enumerating it would add no precision. -/
def identifiableConds {Val : Type} (alg : ValAlgebra Val)
    (conds : List Val) : List Val :=
  conds.foldr
    (fun c acc =>
      if !alg.sameCond c c || acc.any (alg.sameCond c) then acc else c :: acc)
    []

/-- Every branch context that assigns a truth value to each of `conds`. -/
def condAssignments {Val : Type} (conds : List Val) :
    List (List (Val × Bool)) :=
  conds.foldr
    (fun c acc =>
      acc.map (fun ctx => (c, true) :: ctx) ++
        acc.map (fun ctx => (c, false) :: ctx))
    [[]]

/-- Handle-accounting core over decoded `(oldRefs newRefs : List HandleRef)`
lists: every handle in `newRefs` must either satisfy `handleRefCopyable` or
match a unique active loan (`handleFlavorMatchesLoan`) and appear no more
often in `newRefs` than in `oldRefs`. -/
def replaceableHandleRefs {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (oldRefs newRefs : List HandleRef) :
    Bool :=
  newRefs.all (fun r =>
    handleRefCopyable alg loans r ||
      (handleFlavorMatchesLoan alg loans r &&
        Nat.ble (countHandleRef r newRefs) (countHandleRef r oldRefs)))

/-- True iff writing the values `news` in place of `olds` (one writeback that
may span several places) introduces, in no branch, a handle `(lid, path)` that
could not be copied: in every branch, every handle `(lid, path)` in `news`
satisfies `replaceableHandleRefs` against the handles in `olds`. Counting
`(LoanId × SubPath)` pairs across the whole writeback admits moving or swapping
unique handles between the written places (as in `mem::swap` of two `&mut`
references) while rejecting handles that callee-supplied functions or spatial
cells fabricate, duplicate, or retarget to a different `SubPath` or to an
`.ended` loan. -/
def replaceableVals {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (olds news : List Val) : Bool :=
  let fitsIn (ctx : List (Val × Bool)) : Bool :=
    match collectHandleRefsListIn alg false ctx news,
        collectHandleRefsListIn alg true ctx olds with
    | some newRefs, some oldRefs =>
      replaceableHandleRefs alg loans oldRefs newRefs
    | _, _ => false
  -- Bounds over every branch at once suffice when they already fit.
  fitsIn [] ||
    (condAssignments
      (identifiableConds alg
        ((olds ++ news).foldr (fun v acc => collectConds alg v ++ acc) []))).all
      fitsIn

/-- `replaceableVals` for a single place: writing `vNew` in place of `vOld`. -/
def replaceableVal {Val : Type} (alg : ValAlgebra Val)
    (loans : List (LoanEntry Val)) (vOld vNew : Val) : Bool :=
  replaceableVals alg loans [vOld] [vNew]

/-- Branch contexts under which `target` selects a place satisfying `hit`: one
context per selecting path through the step tree, listing the symbolic guards
on that path with the arm taken. Concrete `.choice` conditions select their
arm without adding to the context. If no path selects such a place, or the
step tree is malformed, the result is `[[]]`, the context of an unconditional
write, which makes overlap checks as strict as possible. -/
def leafBranchContexts {Val : Type} (alg : ValAlgebra Val)
    (hit : OwnerRef × SubPath → Bool) (target : BackTarget Val) :
    List (List (Val × Bool)) :=
  let res : Bool × List (List (List (Val × Bool))) :=
    target.steps.foldr
      (fun step (acc : Bool × List (List (List (Val × Bool)))) =>
        match acc with
        | (ok, stk) =>
          match step with
          | .rootParam _ => (ok, [] :: stk)
          | .direct o p => (ok, (if hit (o, p) then [[]] else []) :: stk)
          | .choiceJoin cond =>
            match stk with
            | cTrue :: cFalse :: rest =>
              let merged :=
                match alg.asBool cond with
                | some true => cTrue
                | some false => cFalse
                | none =>
                  cTrue.map (fun ctx => (cond, true) :: ctx) ++
                    cFalse.map (fun ctx => (cond, false) :: ctx)
              (ok, merged :: rest)
            | _ => (false, [])
          | .lensCall targets _ =>
            (ok, (if targets.any hit then [[]] else []) :: stk)
          | .regionOut _ _ => (ok, [] :: stk))
      (true, [])
  match res with
  | (true, [ctxs]) =>
    match ctxs with
    | [] => [[]]
    | _ :: _ => ctxs
  | _ => [[]]

/-- True iff `target` may select a place satisfying `hit` in some branch
described by `ctx`: a concrete `.choice` condition selects its arm, a symbolic
one that `ctx` fixes (`lookupCond`) selects the fixed arm, and any other
symbolic one may take either arm. A malformed step tree conservatively answers
whether any serialized leaf hits. With `ctx = []` this asks whether any active
leaf (`activeTargetLeaves`) hits. -/
def targetMayHitIn {Val : Type} (alg : ValAlgebra Val)
    (ctx : List (Val × Bool)) (hit : OwnerRef × SubPath → Bool)
    (target : BackTarget Val) : Bool :=
  let res : Bool × List Bool :=
    target.steps.foldr
      (fun step (acc : Bool × List Bool) =>
        match acc with
        | (ok, stk) =>
          match step with
          | .rootParam _ => (ok, false :: stk)
          | .direct o p => (ok, hit (o, p) :: stk)
          | .choiceJoin cond =>
            match stk with
            | bTrue :: bFalse :: rest =>
              let b :=
                match alg.asBool cond with
                | some true => bTrue
                | some false => bFalse
                | none =>
                  -- Agreeing arms need no branch lookup.
                  if bTrue == bFalse then bTrue
                  else
                    match lookupCond alg ctx cond with
                    | some true => bTrue
                    | some false => bFalse
                    | none => true
              (ok, b :: rest)
            | _ => (false, [])
          | .lensCall targets _ => (ok, targets.any hit :: stk)
          | .regionOut _ _ => (ok, false :: stk))
      (true, [])
  match res with
  | (true, [b]) => b
  | _ => (targetLeaves target).any hit

/-- True iff some live storage observer other than those in `exempt` covers
storage overlapping `(owner, path)`:
- a live (not `.ended`) loan outside `exempt` whose target may overlap it in
  some branch in which the write happens; or
- an active region group whose lock `lockLid` is not in `exempt` and one of
  whose `inputTargets` overlaps.

Writing back into such storage would change a value that a still-live borrow
or region group observes. `writerCtxs` lists the branch contexts in which the
write happens (`leafBranchContexts`); `[[]]` means every branch. A loan's
target is followed in each such context (`targetMayHitIn`), so choices on a
guard that the writer's context fixes take the same arm for both. A branch
join that gives two loans swapped targets (as in `if c { (&mut a, &mut b) }
else { (&mut b, &mut a) }`) therefore lets either loan end while the other is
live, while a loan that overlaps the written place in the same branch blocks
the write. Guards that `sameCond` cannot identify count as independent, which
can only report more overlaps.

This check does not order the ends of such correlated loans. When one loan's
target in one branch lies inside the other loan's target in the other branch,
the outer loan's writeback turns the outer place into a choice value, and
`getPath` cannot see through a choice to the inner place. So the inner loan
must end first; ending the outer one first makes the inner loan's later end
fail. -/
def liveLoanTargetsOverlap {Val : Type} (alg : ValAlgebra Val)
    (writerCtxs : List (List (Val × Bool))) (exempt : List LoanId)
    (owner : OwnerRef) (path : SubPath) (loans : List (LoanEntry Val))
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  let overlaps (t : OwnerRef × SubPath) : Bool :=
    OwnerRef.beq t.1 owner && subPathOverlaps t.2 path
  loans.any (fun e =>
    !elemLoanId e.id exempt && !e.phase.isEnded &&
      writerCtxs.any (fun ctx => targetMayHitIn alg ctx overlaps e.target)) ||
    rgs.any (fun g =>
      g.active && !elemLoanId g.lockLid exempt && g.inputTargets.any overlaps)

/-- Single-pass linear modifier for loan `lid`, enforcing that `lid` occurs
uniquely in `loans` and is active (or `.activeMut` when `reqMut == true`). -/
def modifyLoanAt {Val : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (List (LoanEntry Val)) :=
  if !hasUniqueLoanId lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Bool × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨v, p⟩, target⟩, (found, rest) =>
            if id == lid then
              let okPhase :=
                if reqMut then phase.isActiveMut else phase.isActive
              if okPhase then
                match f v p with
                | some (v', p') =>
                  (true, ⟨id, phase, mkStrictPlaceCell v' p', target⟩ :: rest)
                | none => (false, rest)
              else (false, rest)
            else
              (found, ⟨id, phase, ⟨v, p⟩, target⟩ :: rest))
        (false, [])
    with
    | (true, updated) => some updated
    | (false, _) => none

/-- Modify the `PlaceCell` of `owner` in a single pass. -/
def modifyOwner {Val : Type} (_alg : ValAlgebra Val) (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Val × PermTree))
    (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAt f reg locals with
      | some locals' => some ⟨locals', loans, rgs, deps, sp, tag⟩
      | none => none
    | .parentLoan lid =>
      match modifyLoanAt lid reqMut f loans with
      | some loans' => some ⟨locals, loans', rgs, deps, sp, tag⟩
      | none => none

/-- Single-pass linear modifier for local register `idx` returning an auxiliary
result `Res`. -/
def modifyLocalAtRes {Val Res : Type}
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (idx : Nat) (xs : List (PlaceCell Val)) :
    Option (Res × List (PlaceCell Val)) :=
  natFold
    (fun cells =>
      match cells with
      -- As in `modifyLocalAt`, a missing local cannot be modified.
      | [] => none
      | ⟨v, p⟩ :: rest =>
        match f v p with
        | some (res, v', p') => some (res, mkStrictPlaceCell v' p' :: rest)
        | none => none)
    (fun _ ih cells =>
      match cells with
      | [] => none
      | x :: rest =>
        match ih rest with
        | some (res, rest') => some (res, x :: rest')
        | none => none)
    idx xs

/-- Single-pass linear modifier for loan `lid` returning an auxiliary result
`Res`, requiring `lid` to occur uniquely in `loans`. -/
def modifyLoanAtRes {Val Res : Type} (lid : LoanId) (reqMut : Bool)
    (f : Val → PermTree → Option (Res × Val × PermTree))
    (loans : List (LoanEntry Val)) : Option (Res × List (LoanEntry Val)) :=
  if !hasUniqueLoanId lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Option Res × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨v, p⟩, target⟩, (resOpt, rest) =>
            if id == lid then
              let okPhase :=
                if reqMut then phase.isActiveMut else phase.isActive
              if okPhase then
                match f v p with
                | some (r, v', p') =>
                  (some r,
                   ⟨id, phase, mkStrictPlaceCell v' p', target⟩ :: rest)
                | none => (none, rest)
              else (none, rest)
            else
              (resOpt, ⟨id, phase, ⟨v, p⟩, target⟩ :: rest))
        (none, [])
    with
    | (some r, updated) => some (r, updated)
    | (none, _) => none

/-- Modify `owner` in a single pass and return an auxiliary result `Res`. -/
def modifyOwnerRes {Val Res : Type} (_alg : ValAlgebra Val)
    (owner : OwnerRef)
    (reqMut : Bool) (f : Val → PermTree → Option (Res × Val × PermTree))
    (st : SymState Val) : Option (Res × SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    match owner with
    | .localReg reg =>
      match modifyLocalAtRes f reg locals with
      | some (res, locals') => some (res, ⟨locals', loans, rgs, deps, sp, tag⟩)
      | none => none
    | .parentLoan lid =>
      match modifyLoanAtRes lid reqMut f loans with
      | some (res, loans') => some (res, ⟨locals, loans', rgs, deps, sp, tag⟩)
      | none => none

/-- Look up `owner` for read access at `path` (defaulting to the whole owner
`[]`), rejecting duplicate parent loan IDs, `.spatialPinned` and `.ended`
loans, as well as any cell whose `PermTree` has an active mutable borrow
overlapping `path` (`!canReadPath path cell.perm`), and projecting both the
returned value (`getPath alg path cell.val`) and permission
(`getPathPerm path cell.perm`) to `path` so locked sibling sub-places are never
exposed. -/
def getOwnerForRead {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    -- A local beyond `st.locals` was never written, so `getLocalCell` would
    -- return the synthetic `alg.defaultVal`; reading it must fail.
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, p⟩ =>
        if canReadPath path p then
          match getPath alg path v with
          | some subVal => some ⟨subVal, getPathPerm path p⟩
          | none => none
        else none
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
        if phase.isActive && canReadPath path p then
          match getPath alg path v with
          | some subVal => some ⟨subVal, getPathPerm path p⟩
          | none => none
        else none
      | none => none

/-- Look up the value of local register `reg` for read access (`getOwnerForRead`
at `[]`), returning `none` if `reg` was never written or is behind an active
mutable borrow (`!canReadPath [] perm`). -/
def getLocal {Val : Type} (alg : ValAlgebra Val) (reg : LocalId)
    (st : SymState Val) : Option Val :=
  (getOwnerForRead alg (.localReg reg) st []).map PlaceCell.val

/-- Look up `owner` for mutable access at `path` (defaulting to the whole owner
`[]`), rejecting duplicate parent loan IDs, `.activeShared`, `.spatialPinned`,
and `.ended` loans, as well as any cell whose `PermTree` has an active shared
or mutable borrow overlapping `path` (`!canWritePath path cell.perm`), and
projecting both the returned value (`getPath alg path cell.val`) and permission
(`getPathPerm path cell.perm`) to `path` so locked sibling sub-places are never
exposed. -/
def getOwnerForMut {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (st : SymState Val) (path : SubPath := []) : Option (PlaceCell Val) :=
  match owner with
  | .localReg reg =>
    -- As in `getOwnerForRead`: a local beyond `st.locals` does not exist.
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, p⟩ =>
        if canWritePath path p then
          match getPath alg path v with
          | some subVal => some ⟨subVal, getPathPerm path p⟩
          | none => none
        else none
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some ⟨_, phase, ⟨v, p⟩, _⟩ =>
        if phase.isActiveMut && canWritePath path p then
          match getPath alg path v with
          | some subVal => some ⟨subVal, getPathPerm path p⟩
          | none => none
        else none
      | none => none

/-- True iff `owner` names storage that already exists in `st`: a local
register below `st.locals.length`, or any parent loan (whose presence the loan
modifiers check themselves). Writeback and cleanup check it before modifying
an owner. -/
def ownerExists {Val : Type} (owner : OwnerRef) (st : SymState Val) : Bool :=
  match owner with
  | .localReg reg => decide (reg < st.locals.length)
  | .parentLoan _ => true

/-- Current value at `path` inside `owner`, or `none` if the owner does not
exist (or its loan ID is ambiguous) or the path does not resolve. -/
def ownerPathValue {Val : Type} (alg : ValAlgebra Val) (owner : OwnerRef)
    (path : SubPath) (st : SymState Val) : Option Val :=
  match owner with
  | .localReg reg =>
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, _⟩ => getPath alg path v
  | .parentLoan lid =>
    if !hasUniqueLoanId lid st.loans then none
    else
      match findLoan lid st.loans with
      | some ⟨_, _, ⟨v, _⟩, _⟩ => getPath alg path v
      | none => none

/-- True iff writing `vals` into `targets` (one value per target) introduces no
new non-copyable handle, counting across all targets at once
(`replaceableVals`). -/
def targetsReplaceable {Val : Type} (alg : ValAlgebra Val)
    (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Bool :=
  let olds : Option (List Val) :=
    targets.foldr
      (fun t acc =>
        match ownerPathValue alg t.1 t.2 st, acc with
        | some v, some rest => some (v :: rest)
        | _, _ => none)
      (some [])
  match olds with
  | some vs => replaceableVals alg st.loans vs vals
  | none => false

/-- True iff `v` may contain a handle to loan `lid` (or nests too deeply to
tell; see `collectHandles`). -/
def valMayMentionLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (v : Val) : Bool :=
  match collectHandles alg v with
  | some lids => elemLoanId lid lids
  | none => true

/-- True iff any local, loan cell, region deposit, or spatial block of `st` may
hold a handle to loan `lid`. -/
def stateMayMentionLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (st : SymState Val) : Bool :=
  st.locals.any (fun c => valMayMentionLoan alg lid c.val) ||
    st.loans.any (fun e => valMayMentionLoan alg lid e.cell.val) ||
    st.regionDeposits.any (fun d => valMayMentionLoan alg lid d.2) ||
    st.spatial.any (fun b =>
      b.cells.any (fun cell =>
        match cell with
        | .init v => valMayMentionLoan alg lid v
        | .uninit => false
        | .rawByte _ => true))

/-- True iff `owner` exists in `st` (and is active / `.activeMut` when `owner`
is a parent loan) and holds a borrow lock for `lid` at `path` of the flavor
required by `reqMut` (`hasMutLoanAtPath` without `hasSharedLoanAtPath` for
`reqMut = true`, and the converse for `reqMut = false`). -/
def ownerHasBorrowLock {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (reqMut : Bool) (owner : OwnerRef) (path : SubPath)
    (st : SymState Val) : Bool :=
  match owner with
  | .localReg reg =>
    if !decide (reg < st.locals.length) then false
    else
      match getLocalCell alg reg st with
      | ⟨_, perm⟩ =>
        if reqMut then
          hasMutLoanAtPath lid path perm && !hasSharedLoanAtPath lid path perm
        else
          hasSharedLoanAtPath lid path perm && !hasMutLoanAtPath lid path perm
  | .parentLoan pLid =>
    if !hasUniqueLoanId pLid st.loans then false
    else
      match findLoan pLid st.loans with
      | some ⟨_, phase, ⟨_, perm⟩, _⟩ =>
        let okPhase := if reqMut then phase.isActiveMut else phase.isActive
        let okPerm :=
          if reqMut then
            hasMutLoanAtPath lid path perm &&
              !hasSharedLoanAtPath lid path perm
          else
            hasSharedLoanAtPath lid path perm &&
              !hasMutLoanAtPath lid path perm
        okPhase && okPerm
      | none => false

/-- If `owner` exists in `st`, holds a borrow lock for `lid` at `path` of the
flavor required by `reqMut` (`ownerHasBorrowLock`), and resolves at `path`,
returns `some subVal`; otherwise `none`. Combines `ownerHasBorrowLock` and
`ownerPathValue` in a single lookup of `owner`. -/
def ownerLockedPathValue {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (reqMut : Bool) (owner : OwnerRef) (path : SubPath)
    (st : SymState Val) : Option Val :=
  match owner with
  | .localReg reg =>
    if !decide (reg < st.locals.length) then none
    else
      match getLocalCell alg reg st with
      | ⟨v, perm⟩ =>
        let okPerm :=
          if reqMut then
            hasMutLoanAtPath lid path perm &&
              !hasSharedLoanAtPath lid path perm
          else
            hasSharedLoanAtPath lid path perm &&
              !hasMutLoanAtPath lid path perm
        if okPerm then getPath alg path v else none
  | .parentLoan pLid =>
    if !hasUniqueLoanId pLid st.loans then none
    else
      match findLoan pLid st.loans with
      | some ⟨_, phase, ⟨v, perm⟩, _⟩ =>
        let okPhase := if reqMut then phase.isActiveMut else phase.isActive
        let okPerm :=
          if reqMut then
            hasMutLoanAtPath lid path perm &&
              !hasSharedLoanAtPath lid path perm
          else
            hasSharedLoanAtPath lid path perm &&
              !hasMutLoanAtPath lid path perm
        if okPhase && okPerm then getPath alg path v else none
      | none => none

/-- Derive the sub-value stored at `target` in `st` for a `.direct` or
symbolic `.choice` `BackTarget` whose borrowed source place(s) are locked under
`newLid` with permission flavor `reqMut`, reading each active leaf and merging
symbolic choice arms via `zipOrKeepSameRef` (or selecting the taken arm when
`alg.asBool cond = some b`). Returns `none` when `!targetWellFormed target` or
when any active step is `.rootParam`, `.regionOut`, `.lensCall`, lacks the
required borrow lock on its owner path, or has a choice guard that is not
handle-free. -/
def deriveLockedTargetVal {Val : Type} (alg : ValAlgebra Val)
    (newLid : LoanId) (reqMut : Bool) (target : BackTarget Val)
    (st : SymState Val) : Option Val :=
  match target.steps with
  | [.direct owner path] =>
    ownerLockedPathValue alg newLid reqMut owner path st
  | [] | [_] => none
  | _ =>
    if reqMut || isRootParamTarget target || isRegionOutTarget target ||
       !validateSharedBackTarget alg target then
      none
    else
      let leaves := dedupOwnerPaths (activeTargetLeaves alg target)
      if leaves.isEmpty ||
         !leaves.all (fun t =>
           ownerHasBorrowLock alg newLid false t.1 t.2 st) then
        none
      else
        let stk : List (Option Val) :=
          target.steps.foldr
            (fun step acc =>
              match step with
              | .direct owner path => ownerPathValue alg owner path st :: acc
              | .choiceJoin cond =>
                match acc with
                | optTrue :: optFalse :: rest =>
                  let merged : Option Val :=
                    if !handleFreeVal alg cond then none
                    else
                      match alg.asBool cond with
                      | some true => optTrue
                      | some false => optFalse
                      | none =>
                        match optTrue, optFalse with
                        | some vTrue, some vFalse =>
                          some (zipOrKeepSameRef alg cond vTrue vFalse)
                        | _, _ => none
                  merged :: rest
                | _ => []
              | _ => none :: acc)
            []
        match stk with
        | [some v] =>
          if targetsReplaceable alg leaves [v] st then some v else none
        | _ => none

/-- True iff `target` and `subVal` describe a valid internal loan allocation at
`newLid` in `st`:
- `target` is well-formed and contains neither `.rootParam` nor `.regionOut`
  (root parameter loans are created only at function entry, and region-group
  outputs are allocated together via `installRegionGroupOutputs`);
- neither `subVal` nor any value in `st` mentions `newLid`;
- every borrowed source place of `target` in `st` is locked under `newLid`
  with the permission flavor matching `phase`, and `subVal` introduces no
  non-copyable handle that was not already present in those locked source
  places (`targetsReplaceable`). -/
def validInstalledLoanSource {Val : Type} (alg : ValAlgebra Val)
    (newLid : LoanId) (phase : LoanPhase Val) (subVal : Val)
    (target : BackTarget Val) (st : SymState Val) : Bool :=
  if valMayMentionLoan alg newLid subVal ||
     stateMayMentionLoan alg newLid st then
    false
  else
    match phase with
    | .activeMut =>
      match target.steps with
      | [.direct owner path] =>
        ownerHasBorrowLock alg newLid true owner path st &&
          replaceableVal alg st.loans subVal subVal
      | [.lensCall targets _] =>
        ownerPathsDisjoint targets &&
          validateBackTarget alg target subVal &&
          targets.all (fun t =>
            ownerHasBorrowLock alg newLid true t.1 t.2 st) &&
          targetsReplaceable alg targets [subVal] st
      | _ => false
    | .activeShared =>
      if isRootParamTarget target || isRegionOutTarget target ||
         !validateSharedBackTarget alg target then false
      else
        let leaves := dedupOwnerPaths (activeTargetLeaves alg target)
        !leaves.isEmpty &&
          leaves.all (fun t =>
            ownerHasBorrowLock alg newLid false t.1 t.2 st) &&
          copyableVal alg st.loans subVal &&
          targetsReplaceable alg leaves [subVal] st
    | _ => false

/-- Bind `⟨newLid, phase, ⟨subVal, .unborrowed⟩, target⟩` into `st.loans` and
write its encoded handle into `dst` when `dst` is writable or one past the end.
Callers must already have verified `findLoan newLid st.loans == none`,
`!valMayMentionLoan alg newLid subVal`, `!stateMayMentionLoan alg newLid st`,
and the phase-specific source lock and handle accounting checks. -/
def bindVerifiedLoanInLocal {Val : Type} (alg : ValAlgebra Val)
    (dst : LocalId) (newLid : LoanId) (phase : LoanPhase Val) (subVal : Val)
    (target : BackTarget Val) (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    let encValOpt : Option Val :=
      match phase with
      | .activeMut => some (alg.encodeRef newLid [])
      | .activeShared => some (alg.encodeSharedRef newLid [])
      | _ => none
    match encValOpt with
    | none => none
    | some encVal =>
      let newEntry : LoanEntry Val :=
        ⟨newLid, phase, ⟨subVal, .unborrowed⟩, target⟩
      let loans' := loans ++ [newEntry]
      if dst == locals.length then
        some ⟨locals ++ [⟨encVal, .unborrowed⟩], loans', rgs, deps, sp, tag⟩
      else
        match modifyLocalAt
            (fun _ p => if canWritePath [] p then some (encVal, p) else none)
            dst locals with
        | some locals' => some ⟨locals', loans', rgs, deps, sp, tag⟩
        | none => none

/-- Atomically allocate a fresh `.direct` or `.choice` internal loan entry
`⟨newLid, phase, ⟨subVal, .unborrowed⟩, target⟩` (where `subVal` is derived
directly from the locked source place(s) of `target` in `st` via
`deriveLockedTargetVal`, `newLid := st.loans.length`, `findLoan newLid st.loans
== none`, and `validInstalledLoanSource alg newLid phase subVal target st`
holds) and bind its freshly encoded handle (`alg.encodeRef newLid []` for
`.activeMut`, or `alg.encodeSharedRef newLid []` for `.activeShared`) to local
`dst` when `dst` is writable (`canWritePath []`) or one past the end
(`dst == st.locals.length`). -/
def installNewLoanInLocal {Val : Type} (alg : ValAlgebra Val) (dst : LocalId)
    (phase : LoanPhase Val) (target : BackTarget Val)
    (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    let st0 : SymState Val := ⟨locals, loans, rgs, deps, sp, tag⟩
    let newLid := loans.length
    let lidAlreadyExists : Bool :=
      match findLoan newLid loans with
      | some _ => true
      | none => false
    let reqMutOpt : Option Bool :=
      match phase with
      | .activeMut => some true
      | .activeShared => some false
      | _ => none
    match lidAlreadyExists, reqMutOpt with
    | false, some reqMut =>
      match deriveLockedTargetVal alg newLid reqMut target st0 with
      | none => none
      | some subVal =>
        let okVal : Bool :=
          !valMayMentionLoan alg newLid subVal &&
            !stateMayMentionLoan alg newLid st0 &&
            (if reqMut then replaceableVal alg loans subVal subVal
             else
               copyableVal alg loans subVal &&
                 replaceableVal alg loans subVal subVal)
        if !okVal then none
        else bindVerifiedLoanInLocal alg dst newLid phase subVal target st0
    | _, _ => none

/-- Atomically allocate a fresh `.lensCall` mutable loan entry in `st` and bind
its freshly encoded handle to `dst`: reads `srcVals` from the locked `targets`
in `st` via `ownerPathValue`, derives `subVal ← fwdFn srcVals`, constructs
`target := .lensCall targets (backFn srcVals)`, validates
`validInstalledLoanSource`, and binds the loan via `bindVerifiedLoanInLocal`. -/
def installLensLoanInLocal {Val : Type} (alg : ValAlgebra Val) (dst : LocalId)
    (targets : List (OwnerRef × SubPath))
    (fwdFn : List Val → Option Val)
    (backFn : List Val → Val → Option (List Val))
    (st : SymState Val) : Option (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    let st0 : SymState Val := ⟨locals, loans, rgs, deps, sp, tag⟩
    let newLid := loans.length
    let lidAlreadyExists : Bool :=
      match findLoan newLid loans with
      | some _ => true
      | none => false
    if lidAlreadyExists then none
    else
      let srcValsOpt : Option (List Val) :=
        targets.foldr
          (fun t acc =>
            match ownerPathValue alg t.1 t.2 st0, acc with
            | some v, some vs => some (v :: vs)
            | _, _ => none)
          (some [])
      match srcValsOpt with
      | none => none
      | some srcVals =>
        match fwdFn srcVals with
        | none => none
        | some subVal =>
          let target : BackTarget Val := .lensCall targets (backFn srcVals)
          if !validInstalledLoanSource alg newLid .activeMut subVal target
               st0 then
            none
          else
            bindVerifiedLoanInLocal alg dst newLid .activeMut subVal target st0

/-- Allocate the output loans of region group `gid` (whose input places
`inTargets` are already mutably locked under `lockLid` in `st`) and bind their
encoded handles into the distinct local registers `dsts`. Rejects duplicate
destinations, unlocked or overlapping `inTargets`, any output list `outVals`
that fabricates or duplicates a non-copyable handle (`targetsReplaceable`
across all `outVals` at once), or any output loan ID that already exists or is
mentioned in `st` or `outVals`. -/
def installRegionGroupOutputs {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (lockLid : LoanId)
    (inTargets : List (OwnerRef × SubPath)) (dsts : List LocalId)
    (outVals : List Val) (st : SymState Val) :
    Option (List LoanId × SymState Val) :=
  let allDistinct (xs : List Nat) : Bool :=
    listFold true (fun x rest ih => !elemLoanId x rest && ih) xs
  if !allDistinct dsts || dsts.length != outVals.length ||
     !ownerPathsDisjoint inTargets ||
     !inTargets.all (fun t =>
       ownerHasBorrowLock alg lockLid true t.1 t.2 st) ||
     !targetsReplaceable alg inTargets outVals st then
    none
  else
    listFold
      (β := Nat → List Val → SymState Val →
        Option (List LoanId × SymState Val))
      (fun _ vs st0 =>
        match vs with
        | [] => some ([], st0)
        | _ :: _ => none)
      (fun dst _ ih idx vs st0 =>
        match vs, st0 with
        | vOut :: restVals, ⟨locals, loans, rgs, deps, sp, tag⟩ =>
          let newLid := loans.length
          let lidExists : Bool :=
            match findLoan newLid loans with
            | some _ => true
            | none => false
          if lidExists || valMayMentionLoan alg newLid vOut ||
             restVals.any (valMayMentionLoan alg newLid) ||
             stateMayMentionLoan alg newLid st0 then
            none
          else
            let encVal := alg.encodeRef newLid []
            let newEntry : LoanEntry Val :=
              ⟨newLid, .activeMut, ⟨vOut, .unborrowed⟩, .regionOut gid idx⟩
            let loans' := loans ++ [newEntry]
            let st1Opt : Option (SymState Val) :=
              if dst == locals.length then
                some ⟨locals ++ [⟨encVal, .unborrowed⟩], loans', rgs, deps,
                      sp, tag⟩
              else
                match modifyLocalAt
                    (fun _ p =>
                      if canWritePath [] p then some (encVal, p) else none)
                    dst locals with
                | some locals' =>
                  some ⟨locals', loans', rgs, deps, sp, tag⟩
                | none => none
            match st1Opt with
            | none => none
            | some st1 =>
              match ih (idx + 1) restVals st1 with
              | some (restLids, st2) => some (newLid :: restLids, st2)
              | none => none
        | [], _ => none)
      dsts 0 outVals st

/-- Cleanup decision for an inactive leaf whose owner is a parent loan that the
cleanup cannot modify: one that is no longer active (for example, an untaken
branch's parent that already ended, which `noActiveChildLoanEdgesIn` permits)
or, for mutable cleanup (`reqMut`), an `.activeShared` parent. Such a cell
cannot be modified, but it need not be: the leaf is skipped (`some (some st)`)
if the cell carries no permission overlapping `path` for `lid`, and rejected
(`some none`) if it retains a residual permission. `none` means the owner is
not an inactive parent loan and the caller should proceed normally. -/
def inactiveParentLeafCleanup {Val : Type} (lid : LoanId) (owner : OwnerRef)
    (path : SubPath) (st : SymState Val) (reqMut : Bool) :
    Option (Option (SymState Val)) :=
  match owner with
  | .parentLoan p =>
    match findLoan p st.loans with
    | some e =>
      -- Proceed normally only if the caller could actually modify this parent
      -- (`.activeMut` for mutable cleanup, any active phase for shared
      -- cleanup); otherwise inspect it read-only.
      if (if reqMut then e.phase.isActiveMut else e.phase.isActive) then none
      else if hasAnyLoanOverlappingPath lid path e.cell.perm then some none
      else some (some st)
    | none => none
  | .localReg _ => none

/-- Write back or release one leaf `(owner, path)` of the mutable loan `lid`,
whose target is `target`, when the loan ends with value `vNew`.

An active leaf (one that `target` selects in some branch, `activeLeaves`)
receives the branch-sensitive written-back value (`evalBackVal`), provided the
owner exists, no other live loan or region group observes overlapping storage
in a branch in which the write happens (`liveLoanTargetsOverlap` with
`leafBranchContexts`), and the owner holds `lid` at `path` as a mutable loan
only; `lid`'s permission at `path` is then released. Handle accounting is not
done here: it must count across every active leaf at once, so
`writebackLeaves` checks it for the whole writeback before writing any leaf.

An inactive leaf (one that `target` selects in no branch) is not written:
`lid`'s permission there is released if it holds one, and any other
permission overlapping `path` for `lid` is rejected. Leaves naming a missing
local and parent loans that cannot be modified are handled without a write
(`inactiveParentLeafCleanup`). -/
def writebackLeaf {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val)
    (activeLeaves : List (OwnerRef × SubPath)) (vNew : Val)
    (owner : OwnerRef) (path : SubPath) (st : SymState Val) :
    Option (SymState Val) :=
  if containsOwnerPath owner path activeLeaves then
    if !ownerExists owner st ||
       liveLoanTargetsOverlap alg
         (leafBranchContexts alg
           (fun t => OwnerRef.beq t.1 owner && subPathEq t.2 path) target)
         [lid] owner path st.loans st.regionGroups
    then none
    else
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if !hasMutLoanAtPath lid path ownerPerm ||
         hasSharedLoanAtPath lid path ownerPerm then
        none
      else
        match getPath alg path ownerVal with
        | some vOld =>
          match evalBackVal alg owner path target vNew vOld with
          | some vUpd =>
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal', releaseLoanPermAtPath lid path ownerPerm)
            | none => none
          | none => none
        | none => none) st
  else
    -- An inactive leaf naming a missing local holds no permission: skip it.
    if !ownerExists owner st then some st
    else
    match inactiveParentLeafCleanup lid owner path st true with
    | some decision => decision
    | none =>
    modifyOwner alg owner true (fun ownerVal ownerPerm =>
      if hasMutLoanAtPath lid path ownerPerm &&
         !hasSharedLoanAtPath lid path ownerPerm then
        some (ownerVal, releaseLoanPermAtPath lid path ownerPerm)
      else if hasAnyLoanOverlappingPath lid path ownerPerm then
        none
      else
        some (ownerVal, ownerPerm)) st

/-- Apply `writebackLeaf` to the leaves in `leaves` that are active
(`wantActive = true`) or inactive (`wantActive = false`) with respect to
`activeLeaves`, in order, failing if any leaf fails. -/
def writebackLeavesPass {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val)
    (activeLeaves : List (OwnerRef × SubPath)) (wantActive : Bool)
    (vNew : Val) (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        if containsOwnerPath owner path activeLeaves == wantActive then
          match writebackLeaf alg lid target activeLeaves vNew owner path
              st0 with
          | some st1 => ih st1
          | none => none
        else
          ih st0)
    (fun st0 => some st0)
    st

/-- Old and written-back values of the leaves `written` of the ending mutable
loan's target `target` (with new loan value `vNew`) in `st`, or `none` if some
leaf has no current value or no written-back value. -/
def activeLeafUpdates {Val : Type} (alg : ValAlgebra Val)
    (target : BackTarget Val) (vNew : Val)
    (written : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (List Val × List Val) :=
  written.foldr
    (fun op acc =>
      match acc with
      | none => none
      | some (olds, news) =>
        match op with
        | (owner, path) =>
          match ownerPathValue alg owner path st with
          | none => none
          | some vOld =>
            match evalBackVal alg owner path target vNew vOld with
            | none => none
            | some vUpd => some (vOld :: olds, vUpd :: news))
    (some ([], []))

/-- Write back every leaf of the ending mutable loan `lid`.

Before writing anything, it checks the writeback as a whole: the active leaves
to be written must be pairwise disjoint, and their written-back values must
create no uncopyable handle, counting across all of them at once
(`replaceableVals`). Counting per leaf would reject a callee that swaps two
`&mut` references held in two places, as `writebackLensTargets` and
`writebackRegionTargets` accept. The leaves are disjoint, so writing one
leaves the others' old values unchanged, and the counts taken up front
describe the whole writeback.

It then writes all active leaves, then all inactive ones. The order matters
when an inactive leaf
overlaps an active one (for example, `x[0]` in the untaken arm of a concrete
choice whose taken arm is `x[0, 1]`): cleaning up the inactive leaf must see
the permission state after the active leaf's write released `lid`, or it
would find `lid`'s permission at the overlapping active path and reject the
leaf. -/
def writebackLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (target : BackTarget Val) (vNew : Val)
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  let activeLeaves := activeTargetLeaves alg target
  let written :=
    leaves.filter (fun op => containsOwnerPath op.1 op.2 activeLeaves)
  if !ownerPathsDisjoint written then none
  else
  match activeLeafUpdates alg target vNew written st with
  | none => none
  | some (olds, news) =>
    if !replaceableVals alg st.loans olds news then none
    else
    match writebackLeavesPass alg lid target activeLeaves true vNew leaves
        st with
    | some st1 =>
      writebackLeavesPass alg lid target activeLeaves false vNew leaves st1
    | none => none

/-- Write the values `vals` returned by a callee's backward lens into the
places `targets`, releasing the call's mutable loan `lid` at each. Fails
unless the targets are pairwise disjoint (`ownerPathsDisjoint`), `targets` and
`vals` have the same length, the whole writeback creates no uncopyable handle
(`targetsReplaceable`), and, for each target, the owner exists, no other live
loan or region group observes overlapping storage, and the owner holds `lid`
at the path as a mutable loan only. Overlapping targets would be written in
sequence, so a later write could copy a handle that an earlier one placed
inside it, past the handle count, which reads every old value first. -/
def writebackLensTargets {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val) : Option (SymState Val) :=
  -- Handles may move between the written places, but not multiply.
  if !ownerPathsDisjoint targets || !targetsReplaceable alg targets vals st then
    none
  else
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        if !ownerExists owner st0 ||
           liveLoanTargetsOverlap alg [[]] [lid] owner path st0.loans
             st0.regionGroups then none
        else
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          if !hasMutLoanAtPath lid path ownerPerm ||
             hasSharedLoanAtPath lid path ownerPerm then
            none
          else
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal', releaseLoanPermAtPath lid path ownerPerm)
            | none => none) st0 with
        | some st1 => ih restVals st1
        | none => none
      | _, [] => none)
    (fun vs st0 =>
      match vs with
      | [] => some st0
      | _ :: _ => none)
    vals st

/-- Release the shared loan `lid` at the leaves in `leaves` that are active
(`wantActive = true`) or inactive (`wantActive = false`) with respect to
`activeLeaves`. An active leaf must name an existing place on which the owner
holds `lid` as a shared loan only. An inactive leaf releases a shared
permission for `lid` if present and rejects any other permission overlapping
the path; leaves naming a missing local or an unmodifiable parent loan are
handled without a modification (`inactiveParentLeafCleanup`). -/
def releaseSharedLeavesPass {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (activeLeaves : List (OwnerRef × SubPath))
    (wantActive : Bool) (leaves : List (OwnerRef × SubPath))
    (st : SymState Val) : Option (SymState Val) :=
  leaves.foldr
    (fun op ih st0 =>
      match op with
      | (owner, path) =>
        if containsOwnerPath owner path activeLeaves == wantActive then
          if wantActive then
            if !ownerExists owner st0 then none
            else
            match modifyOwner alg owner false (fun ownerVal ownerPerm =>
              -- The shared loan must name a place that exists in the owner,
              -- not merely carry a (possibly forged) matching permission.
              match getPath alg path ownerVal with
              | none => none
              | some _ =>
                if !hasSharedLoanAtPath lid path ownerPerm ||
                   hasMutLoanAtPath lid path ownerPerm then
                  none
                else
                  some (ownerVal,
                        releaseLoanPermAtPath lid path ownerPerm)) st0 with
            | some st1 => ih st1
            | none => none
          else if !ownerExists owner st0 then ih st0
          else
            match inactiveParentLeafCleanup lid owner path st0 false with
            | some (some st1) => ih st1
            | some none => none
            | none =>
            match modifyOwner alg owner false (fun ownerVal ownerPerm =>
              if hasSharedLoanAtPath lid path ownerPerm &&
                 !hasMutLoanAtPath lid path ownerPerm then
                some (ownerVal,
                      releaseLoanPermAtPath lid path ownerPerm)
              else if hasAnyLoanOverlappingPath lid path ownerPerm then
                none
              else
                some (ownerVal, ownerPerm)) st0 with
            | some st1 => ih st1
            | none => none
        else
          ih st0)
    (fun st0 => some st0)
    st

/-- Release every leaf of the ending shared loan `lid`: first all active
leaves, then all inactive ones, for the same reason as `writebackLeaves`: the
cleanup of an inactive leaf that overlaps an active one must see the
permission that the active leaf released. -/
def releaseSharedLeaves {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (activeLeaves : List (OwnerRef × SubPath))
    (leaves : List (OwnerRef × SubPath)) (st : SymState Val) :
    Option (SymState Val) :=
  match releaseSharedLeavesPass alg lid activeLeaves true leaves st with
  | some st1 =>
    releaseSharedLeavesPass alg lid activeLeaves false leaves st1
  | none => none

/-- True iff no local slot in `st.locals` and no loan cell in `st.loans`
retains any permission (mutable or shared, at any sub-path) for `lid`. -/
def noResidualLoanPerm {Val : Type} (lid : LoanId)
    (st : SymState Val) : Bool :=
  let localsClean :=
    st.locals.foldr
      (fun c ih => !hasAnyLoanOverlappingPath lid [] c.perm && ih)
      true
  let loansClean :=
    st.loans.foldr
      (fun e ih => !hasAnyLoanOverlappingPath lid [] e.cell.perm && ih)
      true
  localsClean && loansClean

/-- True iff no local slot or loan cell in `st` retains any permission for any
loan ID in `lids`. -/
def noResidualLoanListPerm {Val : Type} (lids : List LoanId)
    (st : SymState Val) : Bool :=
  lids.foldr (fun lid ih => noResidualLoanPerm lid st && ih) true

/-- True iff `targets` contains an edge targeting `.parentLoan lid`. -/
def hasParentLoanEdge (lid : LoanId)
    (targets : List (OwnerRef × SubPath)) : Bool :=
  targets.foldr
    (fun op ih => OwnerRef.beq op.1 (.parentLoan lid) || ih)
    false

/-- True iff no non-ended loan in `loans` has an active backward target edge to
`.parentLoan lid`. Untaken branches of `.choice` targets with a concrete
condition are ignored (`activeTargetLeaves`): the child's permission lives only
in the selected owner, so it does not depend on `lid`. Both branches of a
symbolic choice still count. -/
def noActiveChildLoanEdgesIn {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let isNonEnded :=
        match e.phase with
        | .ended => false
        | _ => true
      if isNonEnded && hasParentLoanEdge lid (activeTargetLeaves alg e.target)
      then
        false
      else
        ih)
    true

/-- Conservative variant of `noActiveChildLoanEdgesIn` that counts every
serialized leaf of each non-ended child's target, for callers without a value
algebra. -/
def noActiveChildLoanEdges {Val : Type} (lid : LoanId)
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let isNonEnded :=
        match e.phase with
        | .ended => false
        | _ => true
      if isNonEnded && hasParentLoanEdge lid (targetLeaves e.target) then
        false
      else
        ih)
    true

/-- True iff no active region group in `rgs` has an input target edge to
`.parentLoan lid`. -/
def noActiveChildRegionEdges {Val : Type} (lid : LoanId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  rgs.foldr
    (fun rg ih =>
      if rg.active && hasParentLoanEdge lid rg.inputTargets then
        false
      else
        ih)
    true

/-- Deactivate loan `lid` in a single pass, verifying that `lid` is unique in
`loans`, has no active child borrows (`isUnborrowed cellPerm` and
`noActiveChildLoanEdgesIn alg lid loans`), has no `.regionOut` or `.rootParam`
target in an active branch (`activeTargetHasSpecial`, which also rejects a
malformed target), and is currently active (`phase.isActive`). -/
def deactivateLoan {Val : Type} (alg : ValAlgebra Val) (lid : LoanId)
    (loans : List (LoanEntry Val)) :
    Option (LoanEntry Val × List (LoanEntry Val)) :=
  if !noActiveChildLoanEdgesIn alg lid loans then none
  else
    match
      loans.foldr
        (fun e (acc : Bool × Option (LoanEntry Val) × List (LoanEntry Val)) =>
          match e, acc with
          | ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩, (dup, foundOpt, rest) =>
            if id == lid then
              match foundOpt with
              | some _ => (true, foundOpt, rest)
              | none =>
                if !isUnborrowed cellPerm ||
                   activeTargetHasSpecial alg target || !phase.isActive then
                  (true, none, rest)
                else
                  (dup,
                   some ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩,
                   ⟨id, .ended, ⟨cellVal, cellPerm⟩, target⟩ :: rest)
            else
              (dup, foundOpt,
               ⟨id, phase, ⟨cellVal, cellPerm⟩, target⟩ :: rest))
        (false, none, [])
    with
    | (false, some found, updated) => some (found, updated)
    | _ => none

/-- End active loan `lid` and propagate its backward writeback through the loan
graph, supporting `.direct`, `.lensCall`, and nested `.choice` targets. -/
def endLoanInState {Val : Type} (alg : ValAlgebra Val)
    (lid : LoanId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  match st with
  | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
    if !noActiveChildRegionEdges lid rgs then .fail
    else
      match deactivateLoan alg lid loans with
      | none => .fail
      | some (⟨_, phase, ⟨cellVal, _⟩, target⟩, loansDeact) =>
        let stDeact : SymState Val := ⟨locals, loansDeact, rgs, deps, sp, tag⟩
        match phase with
        | .activeShared =>
          if !validateSharedBackTarget alg target then .fail
          else
            let leaves := dedupOwnerPaths (targetLeaves target)
            let activeLeaves := activeTargetLeaves alg target
            match releaseSharedLeaves alg lid activeLeaves leaves stDeact with
            | some st' =>
              if noResidualLoanPerm lid st' then .ok st' else .fail
            | none => .fail
        | .activeMut =>
          if !validateBackTarget alg target cellVal then .fail
          else
            let leaves := dedupOwnerPaths (targetLeaves target)
            match writebackLeaves alg lid target cellVal leaves stDeact with
            | some st' =>
              if noResidualLoanPerm lid st' then .ok st' else .fail
            | none => .fail
        | .spatialPinned _ _ => .fail
        | .ended => .fail

/-- End a sequence of loans in order. -/
def endLoansInState {Val : Type} (alg : ValAlgebra Val)
    (lids : List LoanId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  lids.foldr
    (fun lid ih st0 =>
      match endLoanInState alg lid st0 with
      | .ok st1 => ih st1
      | .fail => .fail)
    (fun st0 => .ok st0)
    st

/-- Count occurrences of region group ID `gid` in `rgs`. -/
def countRegionGroupId {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Nat :=
  rgs.foldr (fun g ih => if g.groupId == gid then ih + 1 else ih) 0

/-- True iff `gid` occurs exactly once in `rgs`. -/
def hasUniqueRegionGroupId {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  countRegionGroupId gid rgs == 1

/-- Look up region group `gid`. -/
def findRegionGroup {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Option (RegionGroupEntry Val) :=
  rgs.foldr
    (fun g ih => if g.groupId == gid then some g else ih)
    none

/-- Update region group `gid`. -/
def updateRegionGroup {Val : Type} (gid : RegionGroupId)
    (f : RegionGroupEntry Val → RegionGroupEntry Val)
    (rgs : List (RegionGroupEntry Val)) : List (RegionGroupEntry Val) :=
  rgs.foldr
    (fun g ih => if g.groupId == gid then f g :: ih else g :: ih)
    []

def isRegionGroupEnded {Val : Type} (gid : RegionGroupId)
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  if !hasUniqueRegionGroupId gid rgs then false
  else
    match findRegionGroup gid rgs with
    | some g => !g.active
    | none => false

def allRequiredGroupsEnded {Val : Type} (rgs : List (RegionGroupEntry Val))
    (reqIds : List RegionGroupId) : Bool :=
  reqIds.foldr
    (fun gid ih => isRegionGroupEnded gid rgs && ih)
    true

/-- Retire all output loans of region group `gid`, verifying that each output
loan at position `expectedIdx` is unique in `st.loans`, is currently
`.activeMut`, has no active child sub-borrows (`isUnborrowed e.cell.perm`,
`noActiveChildLoanEdgesIn`, and `noActiveChildRegionEdges`), and has target
`.regionOut gid expectedIdx`. -/
def collectAndRetireOutputLoans {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (expectedIdx : Nat) (outLids : List LoanId)
    (st : SymState Val) : Option (List Val × SymState Val) :=
  outLids.foldr
    (β := Nat → SymState Val → Option (List Val × SymState Val))
    (fun olid ih idx st0 =>
      if !hasUniqueLoanId olid st0.loans ||
         !noActiveChildLoanEdgesIn alg olid st0.loans ||
         !noActiveChildRegionEdges olid st0.regionGroups then
        none
      else
        match findLoan olid st0.loans with
        | none => none
        | some e =>
          if !e.phase.isActiveMut || !isUnborrowed e.cell.perm ||
             !isMatchingRegionOut gid idx e.target then
            none
          else
            let st1 : SymState Val :=
              match st0 with
              | ⟨locals, loans, rgs, deps, sp, tag⟩ =>
                ⟨locals,
                  updateLoan olid
                    (fun x => ⟨x.id, .ended, x.cell, x.target⟩) loans,
                  rgs, deps, sp, tag⟩
            match ih (idx + 1) st1 with
            | some (vals, st2) => some (e.cell.val :: vals, st2)
            | none => none)
    (fun _ st0 => some ([], st0))
    expectedIdx st

def releaseLoanListPermAtPath (lids : List LoanId) (path : SubPath)
    (p : PermTree) : PermTree :=
  lids.foldr
    (fun lid ih p0 => ih (releaseLoanPermAtPath lid path p0))
    (fun p0 => p0)
    p

/-- True iff each loan in `lids` appears at `path` of `perm` only in the
permission flavor its phase in `loans` implies: an `.activeMut` loan must not
appear as a shared permission, and an `.activeShared` loan must not appear as a
mutable one. Region writeback releases every such loan at once, so a
contradictory flavor must be rejected first. -/
def releasedPermFlavorsMatch {Val : Type} (loans : List (LoanEntry Val))
    (lids : List LoanId) (path : SubPath) (perm : PermTree) : Bool :=
  lids.all (fun l =>
    match findLoan l loans with
    | some e =>
      match e.phase with
      | .activeMut => !hasSharedLoanAtPath l path perm
      | .activeShared => !hasMutLoanAtPath l path perm
      | _ => true
    | none => true)

/-- Write the values `vals` produced by a region group's backward function into
its input places `targets`, releasing the loans `releaseLids` (the group's
lock `lockLid` and its output loans) at each. Fails unless no live loan has
the ID `lockLid` (a lock normally names an ended sentinel entry, and an
output used as the lock is already retired), the targets are pairwise
disjoint (`ownerPathsDisjoint`, for the reason given at
`writebackLensTargets`), `targets` and `vals` have the same length, the whole
writeback creates no uncopyable handle (`targetsReplaceable`), and, for each
target, the owner exists, no live loan or region group outside `releaseLids`
observes overlapping storage, the owner holds `lockLid` at the path as a
mutable loan only, and every released loan appears there only in the flavor
its phase implies (`releasedPermFlavorsMatch`, using `phaseLoans` when the
output loans were already retired). -/
def writebackRegionTargets {Val : Type} (alg : ValAlgebra Val)
    (lockLid : LoanId) (releaseLids : List LoanId)
    (targets : List (OwnerRef × SubPath)) (vals : List Val)
    (st : SymState Val)
    (phaseLoans : Option (List (LoanEntry Val)) := none) :
    Option (SymState Val) :=
  -- The lock is exempt from the live-loan check below, so it must not name a
  -- live loan: every loan with its ID must have ended (output loans are
  -- retired before this runs).
  if !st.loans.all (fun e => e.id != lockLid || e.phase.isEnded) then none
  -- Handles may move between the written places, but not multiply.
  else if
    !ownerPathsDisjoint targets || !targetsReplaceable alg targets vals st
  then none
  else
  targets.foldr
    (fun op ih vs st0 =>
      match op, vs with
      | (owner, path), vUpd :: restVals =>
        if !ownerExists owner st0 ||
           liveLoanTargetsOverlap alg [[]] releaseLids owner path st0.loans
             st0.regionGroups then none
        else
        match modifyOwner alg owner true (fun ownerVal ownerPerm =>
          -- As in `writebackLeaf`, the lock must be held only as a mutable
          -- loan: a `lockLid` that also appears in the shared half of a
          -- `.mutJoined` permission is a contradictory borrow state. Every
          -- other released loan must likewise appear only in the flavor its
          -- phase implies before its permission is removed.
          if !hasMutLoanAtPath lockLid path ownerPerm ||
             hasSharedLoanAtPath lockLid path ownerPerm ||
             !releasedPermFlavorsMatch
               (match phaseLoans with
                | some ls => ls
                | none => st0.loans)
               releaseLids path ownerPerm then
            none
          else
            match putPath alg path ownerVal vUpd with
            | some ownerVal' =>
              some (ownerVal',
                    releaseLoanListPermAtPath releaseLids path ownerPerm)
            | none => none) st0 with
        | some st1 => ih restVals st1
        | none => none
      | _, [] => none)
    (fun vs st0 =>
      match vs with
      | [] => some st0
      | _ :: _ => none)
    vals st

/-- Split `deps` into the values deposited by the groups in `children` and the
remaining deposits. The values are ordered by their producer's position in
`children` and then by deposit order, so the result does not depend on the
order in which independent groups ended. A child listed twice contributes its
deposits once. Taken deposits are consumed, so if several groups require the
same child, only the first of them to end receives the child's deposits. -/
def takeChildDeposits {Val : Type} (children : List RegionGroupId)
    (deps : List (RegionGroupId × Val)) :
    List Val × List (RegionGroupId × Val) :=
  children.foldl
    (fun (acc : List Val × List (RegionGroupId × Val)) c =>
      match acc with
      | (taken, rest) =>
        (taken ++ (rest.filter (fun d => d.1 == c)).map (fun d => d.2),
         rest.filter (fun d => d.1 != c)))
    ([], deps)

/-- End multi-region group `gid`, enforcing uniqueness of `gid` in
`st.regionGroups`, `requiredChildren` outlives order, pairwise-disjoint
`inputTargets`, unborrowed output loans with matching `.regionOut gid idx`
targets, and backward lens propagation across `inputTargets`. The backward
function receives only the deposits of the group's `requiredChildren`
(`takeChildDeposits`), which are consumed; its own deposits are tagged with
`gid`. -/
def endRegionGroupInState {Val : Type} (alg : ValAlgebra Val)
    (gid : RegionGroupId) (st : SymState Val) : EvalOutcome (SymState Val) :=
  if !hasUniqueRegionGroupId gid st.regionGroups then .fail
  else
    match findRegionGroup gid st.regionGroups with
  | none => .fail
  | some g =>
    -- Deposits are consumed by the first group that ends, so another active
    -- group requiring one of the same children would silently receive none.
    let childShared : Bool :=
      st.regionGroups.any (fun o =>
        o.groupId != gid && o.active &&
          o.requiredChildren.any (fun c =>
            g.requiredChildren.any (fun c' => c' == c)))
    if !g.active || !ownerPathsDisjoint g.inputTargets ||
       !allRequiredGroupsEnded st.regionGroups g.requiredChildren ||
       childShared then
      .fail
    else
      match collectAndRetireOutputLoans alg gid 0 g.outputLoans st with
      | none => .fail
      | some (outVals, stRetired) =>
        let childSplit :=
          takeChildDeposits g.requiredChildren stRetired.regionDeposits
        match g.backFn outVals childSplit.1 with
        | none => .fail
        | some (updatedInputs, newDeposits) =>
          -- Output loans are already `.ended` in `stRetired`, so their
          -- permission flavors are checked against the pre-retirement phases
          -- in `st.loans`.
          match writebackRegionTargets alg g.lockLid
                  (g.lockLid :: g.outputLoans)
                  g.inputTargets updatedInputs stRetired (some st.loans) with
          | none => .fail
          | some stWritten =>
            if !noResidualLoanListPerm (g.lockLid :: g.outputLoans)
                 stWritten then
              .fail
            else
              match stWritten with
              | ⟨locals, loans, rgs, _, sp, tag⟩ =>
                let rgs' := updateRegionGroup gid
                  (fun x => ⟨x.groupId, false, x.lockLid, x.inputTargets,
                             x.outputLoans, x.requiredChildren, x.backFn⟩)
                  rgs
                .ok ⟨locals, loans, rgs',
                     childSplit.2 ++ newDeposits.map (fun v => (gid, v)), sp,
                     tag⟩

/-- End a list of region groups in order. -/
def endRegionGroupsInState {Val : Type} (alg : ValAlgebra Val)
    (gids : List RegionGroupId) (st : SymState Val) :
    EvalOutcome (SymState Val) :=
  gids.foldr
    (fun gid ih st0 =>
      match endRegionGroupInState alg gid st0 with
      | .ok st1 => ih st1
      | .fail => .fail)
    (fun st0 => .ok st0)
    st

/-- Extract `some paramIdx` if `t` is a root parameter backward target
(`.rootParam paramIdx`), or `none` otherwise. -/
def rootParamIdxOpt {Val : Type} (t : BackTarget Val) : Option Nat :=
  match t.steps with
  | [.rootParam idx] => some idx
  | _ => none

/-- True iff `t` is a root parameter backward target (`.rootParam paramIdx`). -/
def isRootTarget {Val : Type} (t : BackTarget Val) : Bool :=
  match rootParamIdxOpt t with
  | some _ => true
  | none => false

/-- Count how many entries in `loans` have backward target `.rootParam idx`. -/
def countRootParamIdx {Val : Type} (idx : Nat)
    (loans : List (LoanEntry Val)) : Nat :=
  loans.foldr
    (fun e ih =>
      match rootParamIdxOpt e.target with
      | some i => if i == idx then ih + 1 else ih
      | none => ih)
    0

/-- Insert `(idx, val)` into an ascending-index-sorted list of `(paramIdx, Val)`
pairs. -/
def insertRootMutByIdx {Val : Type} (idx : Nat) (v : Val)
    (sorted : List (Nat × Val)) : List (Nat × Val) :=
  sorted.foldr
    (fun (curIdx, curVal) ih =>
      match ih with
      | [] => [(curIdx, curVal), (idx, v)]
      | (headIdx, headVal) :: tail =>
        if Nat.ble idx curIdx then
          (idx, v) :: (curIdx, curVal) :: tail
        else
          (curIdx, curVal) :: (headIdx, headVal) :: tail)
    [(idx, v)]

/-- True iff every loan ID in `loans` is unique, every root parameter loan in
`loans` has a unique `.rootParam idx` index and is active with no active child
borrows (`isUnborrowed e.cell.perm`), and every non-root loan has ended. -/
def loansCleanAtReturn {Val : Type}
    (loans : List (LoanEntry Val)) : Bool :=
  loans.foldr
    (fun e ih =>
      let okHere : Bool :=
        if !hasUniqueLoanId e.id loans then false
        else
          match rootParamIdxOpt e.target with
          | some idx =>
            e.phase.isActive && isUnborrowed e.cell.perm &&
            countRootParamIdx idx loans == 1
          | none =>
            e.phase.isEnded
      okHere && ih)
    true

/-- True iff all region groups in `rgs` have ended (`!g.active`). -/
def allRegionGroupsEnded {Val : Type}
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  rgs.foldr
    (fun g ih => !g.active && ih)
    true

/-- True iff every region group in `rgs` has ended and no two share a
`groupId`, checked in a single pass so the return predicate inspects
`regionGroups` once. -/
def allRegionGroupsEndedUnique {Val : Type}
    (rgs : List (RegionGroupEntry Val)) : Bool :=
  (rgs.foldr
    (fun g (acc : Bool × List RegionGroupId) =>
      match acc with
      | (ok, seen) =>
        (ok && !g.active && !seen.contains g.groupId, g.groupId :: seen))
    (true, [])).1

/-- True iff all non-root loans and region groups have ended, root parameter
loans have unique IDs, unique parameter indices, and no active child borrows,
no spatial blocks remain pinned, no local or loan cell retains any borrow
permission, and no region deposit is left unconsumed (a leftover deposit is a
backward result that no parent group received). -/
def stateCleanAtReturn {Val : Type} (st : SymState Val) : Bool :=
  loansCleanAtReturn st.loans &&
  allRegionGroupsEndedUnique st.regionGroups &&
  st.spatial.isEmpty &&
  st.regionDeposits.isEmpty &&
  -- Every non-root loan has ended, so no local and no loan cell may still
  -- carry a borrow permission; a stale permission means an inconsistent
  -- borrow state that must not reach the return boundary.
  st.locals.all (fun c => isUnborrowed c.perm) &&
  st.loans.all (fun e => isUnborrowed e.cell.perm)

/-- Collect the final values of all root `&mut` parameter loans sorted in
ascending parameter index order (`.rootParam paramIdx`). -/
def collectRootMutVals {Val : Type}
    (loans : List (LoanEntry Val)) : List Val :=
  let sortedPairs : List (Nat × Val) :=
    loans.foldr
      (fun e ih =>
        match e.phase, rootParamIdxOpt e.target with
        | .activeMut, some idx => insertRootMutByIdx idx e.cell.val ih
        | _, _ => ih)
      []
  sortedPairs.map Prod.snd

/-- Finalize function return from `st` with direct return value `retVal`,
verifying `stateCleanAtReturn st` and `handleFreeOut alg` on
`⟨retVal, collectRootMutVals st.loans⟩`. -/
def finalizeRootReturn {Val : Type} (alg : ValAlgebra Val) (retVal : Val)
    (st : SymState Val) : EvalOutcome (FuncOut Val) :=
  if !stateCleanAtReturn st then .fail
  else
    let out : FuncOut Val := ⟨retVal, collectRootMutVals st.loans⟩
    if !handleFreeOut alg out then .fail
    else .ok out

/-!
## Kernel-Checked Tests for `LoanGraph`
-/

/-- Local register access (`listGetVal`, `getLocal`, `setLocalChecked`,
`modifyLocalAt`, `modifyLocalAtRes`) is exact for local indices above eight
(`8`, `9`, `12`, `15`) and never aliases local `12` to local `8`. Writes may
overwrite an existing local or append exactly one past the end, but never pad
skipped slots, and reading a slot that was never written fails. -/
theorem loanGraph_locals_above_eight_no_aliasing :
    let set (reg : LocalId) (v : LensTestVal) (st : SymState LensTestVal) :
        SymState LensTestVal :=
      match setLocalChecked lensTestValAlg reg v st with
      | some st' => st'
      | none => st
    let st0 : SymState LensTestVal :=
      ⟨List.replicate 12 ⟨.atom 0, .unborrowed⟩, [], [], [], [], 0⟩
    let st1 := set 8 (.atom 80) st0
    let st2 := set 9 (.atom 90) st1
    let st3 := set 12 (.atom 120) st2
    let st4 := set 13 (.atom 130) st3
    let st5 := set 14 (.atom 140) st4
    let st6 := set 15 (.atom 150) st5
    getLocal lensTestValAlg 0 st6 = some (.atom 0) ∧
    getLocal lensTestValAlg 8 st6 = some (.atom 80) ∧
    getLocal lensTestValAlg 9 st6 = some (.atom 90) ∧
    getLocal lensTestValAlg 12 st6 = some (.atom 120) ∧
    getLocal lensTestValAlg 15 st6 = some (.atom 150) ∧
    getLocal lensTestValAlg 16 st6 = none ∧
    -- No padding: a write two or more slots past the end fails, and the
    -- never-written slot is unreadable.
    setLocalChecked lensTestValAlg 20 (.atom 1) st6 = none ∧
    getOwnerForRead lensTestValAlg (.localReg 20) st6 = none ∧
    getOwnerForRead lensTestValAlg (.localReg 16) st6 = none ∧
    (getOwnerForRead lensTestValAlg (.localReg 15) st6).map PlaceCell.val =
      some (.atom 150) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Balanced `.choice` tree with 16 distinct leaves used to verify that
`targetLeaves` and `dedupOwnerPaths` preserve all 16 leaves without
truncation. -/
def choiceTree16 : BackTarget LensTestVal :=
  let c := LensTestVal.atom 1
  let pair (i : Nat) : BackTarget LensTestVal :=
    .choice c (.direct (.localReg (2 * i)) [])
              (.direct (.localReg (2 * i + 1)) [])
  let quad (j : Nat) : BackTarget LensTestVal :=
    .choice c (pair (2 * j)) (pair (2 * j + 1))
  let oct (k : Nat) : BackTarget LensTestVal :=
    .choice c (quad (2 * k)) (quad (2 * k + 1))
  .choice c (oct 0) (oct 1)

theorem dedupOwnerPaths_preserves_all_sixteen_leaves :
    (targetLeaves choiceTree16).length = 16 ∧
    (dedupOwnerPaths (targetLeaves choiceTree16)).length = 16 :=
  ⟨rfl, rfl⟩

/-- `isRegionOutTarget` detects `.regionOut` targets nested inside `.choice`
trees. `deactivateLoan` rejects ordinary `endLoanInState` when such a target
lies in an active branch (here, under a symbolic condition), but ignores it in
the untaken branch of a concrete choice. -/
theorem nested_regionOut_under_choice_rejected :
    let mkTarget (c : LensTestVal) : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.choice c (.direct (.localReg 1) []) (.regionOut 0 0))
    let mkSt (c : LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, mkTarget c⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let symTarget : BackTarget LensTestVal :=
      .choice (.node (.atom 0) (.atom 1))
        (.direct (.localReg 0) []) (.regionOut 0 0)
    isRegionOutTarget (mkTarget (.atom 0)) = true ∧
    activeTargetHasSpecial lensTestValAlg (mkTarget (.atom 0)) = false ∧
    activeTargetHasSpecial lensTestValAlg symTarget = true ∧
    activeTargetHasSpecial lensTestValAlg
      (.choice (.atom 0) (.direct (.localReg 0) []) (.rootParam 0)) = true ∧
    (match endLoanInState lensTestValAlg 0 (mkSt (.atom 0)) with
     | .ok st' => getLocal lensTestValAlg 0 st' = some (.atom 99)
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0
      { mkSt (.atom 0) with
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, symTarget⟩] } =
      .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `endLoanInState` executes backward lenses when `.lensCall` is nested inside
a `.choice` tree, propagating the branch-selected lens writeback to the owner
locals. -/
theorem nested_lensCall_under_choice_executes_writeback (cond : Bool) :
    let condVal : LensTestVal := .atom (if cond then 1 else 0)
    let tTrue : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, [])]
        (fun v =>
          match v with
          | ⟨_, .atom n⟩ => some [.atom (n + 100)]
          | _ => none)
    let tFalse : BackTarget LensTestVal :=
      .lensCall [(.localReg 1, [])]
        (fun v =>
          match v with
          | ⟨_, .atom n⟩ => some [.atom (n + 200)]
          | _ => none)
    let choiceTarget : BackTarget LensTestVal := .choice condVal tTrue tFalse
    let st : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 0⟩, ⟨.atom 2, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 5, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    match endLoanInState lensTestValAlg 0 st with
    | .ok st' =>
      getLocal lensTestValAlg 0 st' =
        some (if cond then .atom 105 else .atom 1) ∧
      getLocal lensTestValAlg 1 st' =
        some (if cond then .atom 2 else .atom 205) ∧
      getLocalPerm lensTestValAlg 0 st' = .unborrowed ∧
      getLocalPerm lensTestValAlg 1 st' = .unborrowed
    | .fail => False := by
  cases cond <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- `endRegionGroupInState` rejects a region group whose `outputLoans` list
references a loan belonging to a different group ID or wrong output index. -/
theorem regionGroup_rejects_mismatched_output_loan_target :
    let rgWrongGroup : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := [(.localReg 0, [])]
        outputLoans := [0]
        requiredChildren := []
        backFn := fun outs _ => some (outs, []) }
    let stWrongGroup : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .regionOut 1 0⟩]
        regionGroups := [rgWrongGroup]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stWrongIdx : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .regionOut 0 1⟩]
        regionGroups := [rgWrongGroup]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    endRegionGroupInState lensTestValAlg 0 stWrongGroup = .fail ∧
    endRegionGroupInState lensTestValAlg 0 stWrongIdx = .fail :=
  ⟨rfl, rfl⟩

/-- Mutable writeback into an `.activeShared` parent loan is rejected
(`reqMut = true`) by `writebackLeaf` (through `endLoanInState`),
`writebackRegionTargets` (through `endRegionGroupInState`), and
`writebackLensTargets`. Each shared-parent case has an `.activeMut`-parent
twin with the same permissions that succeeds, so the parent's phase alone
decides the outcome. -/
theorem writeback_rejects_activeShared_parent_loan :
    let stDirect (ph : LoanPhase LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩]
        loans :=
          [ ⟨0, ph, ⟨.atom 10, .mutLocked 1⟩, .direct (.localReg 0) []⟩,
            ⟨1, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let rgOnParent : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 1
        inputTargets := [(.parentLoan 0, [])]
        outputLoans := [2]
        requiredChildren := []
        backFn := fun outs _ => some (outs, []) }
    let stRegion (ph : LoanPhase LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩]
        loans :=
          [ ⟨0, ph, ⟨.atom 10, .mutLocked 1⟩, .direct (.localReg 0) []⟩,
            ⟨2, .activeMut, ⟨.atom 77, .unborrowed⟩, .regionOut 0 0⟩ ]
        regionGroups := [rgOnParent]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    let isSome (o : Option (SymState LensTestVal)) : Bool :=
      match o with
      | some _ => true
      | none => false
    isOk (endLoanInState lensTestValAlg 1 (stDirect .activeShared)) = false ∧
    isOk (endLoanInState lensTestValAlg 1 (stDirect .activeMut)) = true ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion .activeShared)) =
      false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion .activeMut)) =
      true ∧
    isSome (writebackLensTargets lensTestValAlg 1 [(.parentLoan 0, [])]
      [.atom 5] (stDirect .activeShared)) = false ∧
    isSome (writebackLensTargets lensTestValAlg 1 [(.parentLoan 0, [])]
      [.atom 5] (stDirect .activeMut)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A malformed step tree in the arm that a concrete condition discards is
still malformed (`targetWellFormed`): `validateBackTarget`,
`validateSharedBackTarget`, and `evalBackVal` reject it,
`activeTargetHasSpecial` treats it as special, and ending a loan with such a
target fails. The well-formed twin, whose discarded arm is a complete
`.choice`, validates. -/
theorem malformed_untaken_arm_rejected_tests :
    let bad : BackTarget LensTestVal :=
      ⟨[.choiceJoin (.atom 1), .direct (.localReg 0) [],
        .choiceJoin (.node (.atom 0) (.atom 1)), .direct (.localReg 1) []]⟩
    let good : BackTarget LensTestVal :=
      .choice (.atom 1) (.direct (.localReg 0) [])
        (.choice (.node (.atom 0) (.atom 1)) (.direct (.localReg 1) [])
          (.direct (.localReg 1) []))
    let st (t : BackTarget LensTestVal) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 0⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, t⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    targetWellFormed bad = false ∧
    validateBackTarget lensTestValAlg bad (.atom 5) = false ∧
    validateSharedBackTarget lensTestValAlg bad = false ∧
    evalBackVal lensTestValAlg (.localReg 0) [] bad (.atom 5) (.atom 10) =
      none ∧
    activeTargetHasSpecial lensTestValAlg bad = true ∧
    isOk (endLoanInState lensTestValAlg 0 (st bad)) = false ∧
    targetWellFormed good = true ∧
    validateBackTarget lensTestValAlg good (.atom 5) = true ∧
    isOk (endLoanInState lensTestValAlg 0 (st good)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unit tests for `OwnerRef.beq`, `LoanPhase` predicates
(`isActive`, `isActiveMut`, `isEnded`, `samePhase`), `hasUninitCell`, and
`validateBackTarget` on root-parameter and region-output targets.
`lookupLensTargetVal_and_evalBackVal_tests` covers those two functions. -/
theorem loanPhase_and_backTarget_helpers_tests :
    let dummyCodec : SpatialCodec LensTestVal :=
      { codecId := 0
        encode := fun v => [.init v]
        decode := fun cs => match cs with | [.init v] => some v | _ => none
        decode_encode := fun _ => rfl }
    let pSh : LoanPhase LensTestVal := .activeShared
    let pMut : LoanPhase LensTestVal := .activeMut
    let pPin : LoanPhase LensTestVal := .spatialPinned 0 dummyCodec
    let pEnd : LoanPhase LensTestVal := .ended
    OwnerRef.beq (.localReg 1) (.localReg 1) = true ∧
    OwnerRef.beq (.localReg 1) (.localReg 2) = false ∧
    OwnerRef.beq (.parentLoan 1) (.parentLoan 1) = true ∧
    OwnerRef.beq (.localReg 1) (.parentLoan 1) = false ∧
    pSh.isActive = true ∧
    pSh.isActiveMut = false ∧
    pSh.isEnded = false ∧
    pMut.isActive = true ∧
    pMut.isActiveMut = true ∧
    pMut.isEnded = false ∧
    pPin.isActive = false ∧
    pPin.isActiveMut = false ∧
    pPin.isEnded = false ∧
    pEnd.isActive = false ∧
    pEnd.isActiveMut = false ∧
    pEnd.isEnded = true ∧
    LoanPhase.samePhase pSh pSh = true ∧
    LoanPhase.samePhase pMut pMut = true ∧
    LoanPhase.samePhase pEnd pEnd = true ∧
    LoanPhase.samePhase pSh pMut = false ∧
    LoanPhase.samePhase pPin pPin = false ∧
    hasUninitCell ([.init (.atom 1), .rawByte 2] :
      List (CellVal LensTestVal)) = false ∧
    hasUninitCell ([.init (.atom 1), .uninit] :
      List (CellVal LensTestVal)) = true ∧
    validateBackTarget lensTestValAlg (.rootParam 0 : BackTarget LensTestVal)
      (.atom 1) = false ∧
    validateBackTarget lensTestValAlg (.regionOut 0 0 : BackTarget LensTestVal)
      (.atom 1) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Unit tests for `getOwnerForRead`, `getOwnerForMut`,
`endLoanInState`, `endLoansInState`, `endRegionGroupInState`, and
`endRegionGroupsInState` across shared, mutable, child-locked, and multi-group
hierarchies. -/
theorem loanGraph_lifecycle_and_regionGroups_tests :
    let stSharedAndChild : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 20, .mutLocked 2⟩,
              .direct (.localReg 1) []⟩
          , ⟨2, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 1) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 1. `.activeShared` owner allows read lookup (`getOwnerForRead`) and
    -- rejects mut lookup (`getOwnerForMut`), while `getLocal` rejects reading
    -- a `.mutLocked` local (`local 1`):
    (match getOwnerForRead lensTestValAlg (.parentLoan 0) stSharedAndChild with
     | some _ => true
     | none => false) = true ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stSharedAndChild = none ∧
    getLocal lensTestValAlg 0 stSharedAndChild = some (.atom 10) ∧
    getLocal lensTestValAlg 1 stSharedAndChild = none ∧
    -- 2. Ending parent loan `1` before child loan `2` fails; ending `[0, 2, 1]`
    -- in child-first order via `endLoansInState` succeeds and writes `.atom 99`
    -- back to local `1`:
    endLoanInState lensTestValAlg 1 stSharedAndChild = .fail ∧
    (match endLoansInState lensTestValAlg [0, 2, 1] stSharedAndChild with
     | .ok stDone =>
       getLocal lensTestValAlg 0 stDone = some (.atom 10) ∧
       getLocal lensTestValAlg 1 stDone = some (.atom 99) ∧
       getLocalPerm lensTestValAlg 0 stDone = .unborrowed ∧
       getLocalPerm lensTestValAlg 1 stDone = .unborrowed ∧
       -- Ending an already-ended loan fails:
       endLoanInState lensTestValAlg 0 stDone = .fail
     | .fail => False) ∧
    -- 3. Multi-region group hierarchy with `requiredChildren = [1]` on group
    -- `0`: ending `[0, 1]` out of order fails, while ending `[1, 0]` via
    -- `endRegionGroupsInState` succeeds; the parent consumes the child's
    -- deposit and leaves its own, tagged with `0`:
    let rgParent : RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := [(.localReg 0, [])]
        outputLoans := [0]
        requiredChildren := [1]
        backFn := fun outs _ =>
          match outs with
          | [⟨_, .atom v⟩] => some ([.atom (v + 1)], [.atom 900])
          | _ => none }
    let rgChild : RegionGroupEntry LensTestVal :=
      { groupId := 1
        active := true
        lockLid := 1
        inputTargets := [(.localReg 1, [])]
        outputLoans := [1]
        requiredChildren := []
        backFn := fun outs _ =>
          match outs with
          | [⟨_, .atom v⟩] => some ([.atom (v + 2)], [.atom 800])
          | _ => none }
    let stRg : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 30, .unborrowed⟩, .regionOut 0 0⟩
          , ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgParent, rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    endRegionGroupsInState lensTestValAlg [0, 1] stRg = .fail ∧
    (match endRegionGroupsInState lensTestValAlg [1, 0] stRg with
     | .ok stRgDone =>
       getLocal lensTestValAlg 0 stRgDone = some (.atom 31) ∧
       getLocal lensTestValAlg 1 stRgDone = some (.atom 42) ∧
       stRgDone.regionDeposits = [(0, .atom 900)] ∧
       endRegionGroupInState lensTestValAlg 0 stRgDone = .fail
     | .fail => False) ∧
    -- 4. `validateBackTarget` rejects `.lensCall` with duplicate or overlapping
    -- `(owner, path)` targets, and `endLoanInState` rejects ending a loan whose
    -- owner `PermTree` does not hold the loan at `path` (the region-group case
    -- is in `region_owner_perm_and_disjoint_writeback_tests`):
    let dupLensTarget : BackTarget LensTestVal :=
      .lensCall [(.localReg 0, []), (.localReg 0, [0])]
        (fun v => some [v, v])
    let stUnownedMut : SymState LensTestVal :=
      { locals := [⟨.atom 10, .unborrowed⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stUnownedShared : SymState LensTestVal :=
      { locals := [⟨.atom 10, .unborrowed⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    validateBackTarget lensTestValAlg dupLensTarget (.atom 1) = false ∧
    endLoanInState lensTestValAlg 0 stUnownedMut = .fail ∧
    endLoanInState lensTestValAlg 0 stUnownedShared = .fail ∧
    -- 5. Multi-leaf `.choice` and `.lensCall` writebacks to disjoint sub-paths
    -- of the same owner (`[0]` and `[1]`) succeed because
    -- `releaseLoanPermAtPath` releases only the target sub-path at each step
    -- (the region-group case is in
    -- `region_owner_perm_and_disjoint_writeback_tests`):
    let stChoiceSplit : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
            .choice (.atom 1)
              (.direct (.localReg 0) [0])
              (.direct (.localReg 0) [1])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stLensSplit : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
            .lensCall [(.localReg 0, [0]), (.localReg 0, [1])]
              (fun _ => some [.atom 11, .atom 22])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupLoanId : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 2, .unborrowed⟩, .direct (.localReg 0) []⟩
          , ⟨0, .activeMut, ⟨.atom 3, .unborrowed⟩, .direct (.localReg 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stBadSharedTarget : SymState LensTestVal :=
      { locals := [⟨.atom 1, .shared [0]⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 1, .unborrowed⟩, dupLensTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stParentSplit : SymState LensTestVal :=
      { locals := [⟨.node (.atom 1) (.atom 2), .mutLocked 0⟩]
        loans :=
          [⟨0, .activeMut,
            ⟨.node (.atom 1) (.atom 2), .split [([0], .mutLocked 1)]⟩,
            .direct (.localReg 0) []⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stRootParamLoan : SymState LensTestVal :=
      { locals := []
        loans :=
          [⟨0, .activeMut, ⟨.atom 42, .unborrowed⟩, .rootParam 0⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stChoicePartialLens : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans :=
          [⟨0, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 1)
              (.lensCall [(.localReg 0, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 77⟩ => some [.atom 88]
                  | _ => none))
              (.lensCall [(.localReg 1, [])]
                (fun _ => none))⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let symCond : LensTestVal := .node (.atom 0) (.atom 0)
    let stChoiceSymbolicLens : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 0⟩]
        loans :=
          [⟨0, .activeMut,
            ⟨lensTestValAlg.zipVal symCond (.atom 70) (.atom 80), .unborrowed⟩,
            .choice symCond
              (.lensCall [(.localReg 0, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 70⟩ => some [.atom 71]
                  | _ => none))
              (.lensCall [(.localReg 1, [])]
                (fun v =>
                  match v with
                  | ⟨_, .atom 80⟩ => some [.atom 81]
                  | _ => none))⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRegionGroup : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 30, .unborrowed⟩, .regionOut 0 0⟩
          , ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgChild, rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRegionOutLoan : SymState LensTestVal :=
      { locals := [⟨.atom 20, .mutLocked 1⟩]
        loans :=
          [ ⟨1, .activeMut, ⟨.atom 40, .unborrowed⟩, .regionOut 1 0⟩
          , ⟨1, .activeMut, ⟨.atom 41, .unborrowed⟩, .regionOut 1 0⟩ ]
        regionGroups := [rgChild]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 0 stChoiceSplit with
     | .ok stC =>
       getLocal lensTestValAlg 0 stC = some (.node (.atom 55) (.atom 2)) ∧
       getLocalPerm lensTestValAlg 0 stC = .unborrowed
     | .fail => False) ∧
    (match endLoanInState lensTestValAlg 0 stLensSplit with
     | .ok stL =>
       getLocal lensTestValAlg 0 stL = some (.node (.atom 11) (.atom 22)) ∧
       getLocalPerm lensTestValAlg 0 stL = .unborrowed
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0 stDupLoanId = .fail ∧
    endLoanInState lensTestValAlg 0 stBadSharedTarget = .fail ∧
    endLoanInState lensTestValAlg 0 stRootParamLoan = .fail ∧
    (match endLoanInState lensTestValAlg 0 stChoicePartialLens with
     | .ok stCP =>
       getLocal lensTestValAlg 0 stCP = some (.atom 88) ∧
       getLocal lensTestValAlg 1 stCP = some (.atom 20) ∧
       getLocalPerm lensTestValAlg 0 stCP = .unborrowed
     | .fail => False) ∧
    (match endLoanInState lensTestValAlg 0 stChoiceSymbolicLens with
     | .ok stCS =>
       getLocal lensTestValAlg 0 stCS =
         some (lensTestValAlg.zipVal symCond (.atom 71) (.atom 10)) ∧
       getLocal lensTestValAlg 1 stCS =
         some (lensTestValAlg.zipVal symCond (.atom 20) (.atom 81)) ∧
       getLocalPerm lensTestValAlg 0 stCS = .unborrowed ∧
       getLocalPerm lensTestValAlg 1 stCS = .unborrowed
     | .fail => False) ∧
    endRegionGroupInState lensTestValAlg 1 stDupRegionGroup = .fail ∧
    endRegionGroupInState lensTestValAlg 1 stDupRegionOutLoan = .fail ∧
    getOwnerForRead lensTestValAlg (.parentLoan 0) stParentSplit [0] = none ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stParentSplit [0] = none ∧
    getOwnerForRead lensTestValAlg (.parentLoan 0) stParentSplit [1] =
      some ⟨.atom 2, .unborrowed⟩ ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stParentSplit [1] =
      some ⟨.atom 2, .unborrowed⟩ ∧
    -- 6. Duplicate parent loan IDs are rejected by `modifyLoanAt`,
    -- `modifyLoanAtRes`, `getOwnerForRead`, and `getOwnerForMut`:
    modifyLoanAt 0 true (fun v p => some (v, p)) stDupLoanId.loans = none ∧
    modifyLoanAtRes 0 true (fun v p => some ((), v, p))
      stDupLoanId.loans = none ∧
    getOwnerForRead lensTestValAlg (.parentLoan 0) stDupLoanId = none ∧
    getOwnerForMut lensTestValAlg (.parentLoan 0) stDupLoanId = none ∧
    -- 7. `.choice` targets whose branches target distinct overlapping sub-paths
    -- of the same owner (`[]` and `[0]`) are rejected by `validateBackTarget`,
    -- `validateSharedBackTarget`, and `endLoanInState`:
    let overlapChoiceTarget : BackTarget LensTestVal :=
      .choice symCond
        (.direct (.localReg 0) [])
        (.direct (.localReg 0) [0])
    let stOverlapChoice : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([], .mutLocked 0), ([0], .mutLocked 0)]⟩]
        loans :=
          [⟨0, .activeMut, ⟨.node (.atom 9) (.atom 9), .unborrowed⟩,
            overlapChoiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    validateBackTarget lensTestValAlg overlapChoiceTarget
      (.node (.atom 9) (.atom 9)) = false ∧
    validateSharedBackTarget lensTestValAlg overlapChoiceTarget = false ∧
    endLoanInState lensTestValAlg 0 stOverlapChoice = .fail ∧
    -- 8. `collectRootMutVals` and `finalizeRootReturn` extract root `&mut`
    -- parameter values sorted by ascending `paramIdx` even when loan entries
    -- appear out of order, and reject duplicate `.rootParam` indices:
    let stOutOfOrderRootParams : SymState LensTestVal :=
      { locals := []
        loans :=
          [ ⟨20, .activeMut, ⟨.atom 200, .unborrowed⟩, .rootParam 2⟩
          , ⟨10, .activeMut, ⟨.atom 100, .unborrowed⟩, .rootParam 0⟩
          , ⟨15, .activeMut, ⟨.atom 150, .unborrowed⟩, .rootParam 1⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stDupRootParamIdx : SymState LensTestVal :=
      { locals := []
        loans :=
          [ ⟨10, .activeMut, ⟨.atom 100, .unborrowed⟩, .rootParam 0⟩
          , ⟨11, .activeMut, ⟨.atom 101, .unborrowed⟩, .rootParam 0⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 9. Concrete `.choice` conditions prune untaken branch leaves before
    -- checking overlap in `validateBackTarget` and `validateSharedBackTarget`:
    let concretePrunedOverlapTarget : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.direct (.localReg 0) [0])
    -- 10. `endLoanInState` rejects retiring a parent loan that still has an
    -- active child loan even if its `cell.perm` is `.unborrowed` (the
    -- region-group and region-edge cases are in `retirement_guard_tests`):
    let stForgedUnborrowedParent : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩]
        loans :=
          [ ⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩,
              .direct (.localReg 0) []⟩
          , ⟨1, .activeMut, ⟨.atom 99, .unborrowed⟩,
              .direct (.parentLoan 0) []⟩ ]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    collectRootMutVals stRootParamLoan.loans = [.atom 42] ∧
    finalizeRootReturn lensTestValAlg (.atom 7) stRootParamLoan =
      .ok ⟨.atom 7, [.atom 42]⟩ ∧
    finalizeRootReturn lensTestValAlg (.ref 0 []) stRootParamLoan = .fail ∧
    finalizeRootReturn lensTestValAlg (.atom 7) stOutOfOrderRootParams =
      .ok ⟨.atom 7, [.atom 100, .atom 150, .atom 200]⟩ ∧
    finalizeRootReturn lensTestValAlg (.atom 7) stDupRootParamIdx = .fail ∧
    validateBackTarget lensTestValAlg concretePrunedOverlapTarget
      (.atom 9) = true ∧
    validateSharedBackTarget lensTestValAlg concretePrunedOverlapTarget = true ∧
    endLoanInState lensTestValAlg 0 stForgedUnborrowedParent = .fail ∧
    finalizeRootReturn lensTestValAlg (.atom 7) stParentSplit = .fail :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
   rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl,
   ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `writebackLeaf` (through `endLoanInState` on a mutable loan) rejects
inactive `.choice` leaves whose owner carries a wrong-kind or overlapping stale
permission for `lid` (`hasAnyLoanOverlappingPath`), while permitting an inactive
leaf whose owner was never locked by `lid` (`.unborrowed`).
`inactive_choice_leaf_shared_release_tests` covers `releaseSharedLeaves`. -/
theorem inactive_choice_leaf_rejects_malformed_owner_perm :
    let choiceTarget : BackTarget LensTestVal :=
      .choice (.atom 1)
        (.direct (.localReg 0) [])
        (.direct (.localReg 1) [])
    -- Valid inactive leaf (`local 1` is `.unborrowed`):
    let stValidInactive : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .unborrowed⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- Malformed inactive leaf (`local 1` has `.shared [0]` on an `.activeMut`
    -- loan `0`):
    let stMalformedInactive : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 0⟩, ⟨.atom 20, .shared [0]⟩]
        loans := [⟨0, .activeMut, ⟨.atom 99, .unborrowed⟩, choiceTarget⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 0 stValidInactive with
     | .ok st' =>
       getLocal lensTestValAlg 0 st' = some (.atom 99) ∧
       getLocal lensTestValAlg 1 st' = some (.atom 20)
     | .fail => False) ∧
    endLoanInState lensTestValAlg 0 stMalformedInactive = .fail ∧
    -- Concrete `.choice (.atom 0) (.direct (.localReg 0) [])
    -- (.direct (.localReg 0) [0])` selects `[0]` and processes the active leaf
    -- `[0]` before the inactive overlapping leaf `[]`:
    (let sameOwnerChoice : BackTarget LensTestVal :=
       .choice (.atom 0)
         (.direct (.localReg 0) [])
         (.direct (.localReg 0) [0])
     let stSameOwnerActive0 : SymState LensTestVal :=
       { locals :=
           [⟨.node (.atom 10) (.atom 20), .split [([0], .mutLocked 0)]⟩]
         loans := [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩, sameOwnerChoice⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     let stUndeclaredSiblingPerm : SymState LensTestVal :=
       { locals :=
           [⟨.node (.atom 10) (.atom 20),
             .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
         loans :=
           [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
             .direct (.localReg 0) [0]⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     (match endLoanInState lensTestValAlg 0 stSameOwnerActive0 with
      | .ok st' =>
        getLocal lensTestValAlg 0 st' = some (.node (.atom 55) (.atom 20)) ∧
        isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
      | .fail => False) ∧
     endLoanInState lensTestValAlg 0 stUndeclaredSiblingPerm = .fail) :=
  ⟨⟨rfl, rfl⟩, rfl, ⟨⟨rfl, rfl⟩, rfl⟩⟩

/-- Tests for `LoanGraph`:
1. `writebackRegionTargets` rejects a region lock ID that also appears in the
   shared half of a `.mutJoined` owner permission, while still accepting an
   exclusive `.mutLocked` lock, and
2. `CellVal.rawByte` stores a `UInt8`, so out-of-range raw bytes are not
   representable (`(256 : UInt8) = 0`). -/
theorem region_lock_flavor_and_raw_byte_tests :
    -- 1. Contradictory `.mutJoined [5] [5]` lock is rejected; `.mutLocked 5`
    -- is accepted and released:
    (let stJoined : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutJoined [5] [5]⟩]
         loans := []
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     writebackRegionTargets lensTestValAlg 5 [5] [(.localReg 0, [])]
       [.atom 7] stJoined = none) ∧
    (let stLocked : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutLocked 5⟩]
         loans := []
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     match writebackRegionTargets lensTestValAlg 5 [5] [(.localReg 0, [])]
         [.atom 7] stLocked with
     | some st' =>
       getLocal lensTestValAlg 0 st' = some (.atom 7) ∧
       isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
     | none => False) ∧
    -- 2. Raw bytes are 8-bit:
    (CellVal.rawByte 256 : CellVal LensTestVal) = .rawByte 0 ∧
    hasUninitCell ([.rawByte 255] : List (CellVal LensTestVal)) = false :=
  ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- Tests for `LoanGraph`:
1. Region writeback rejects a released output loan whose permission flavor
   contradicts its phase (an `.activeMut` loan in the shared half of
   `.mutJoined`), and accepts the consistent `.activeShared` case,
2. Ending a loan whose concrete choice leaves an inactive leaf naming a missing
   local neither fails nor fabricates that local,
3. Ending a shared loan whose target sub-path does not exist in the owner fails,
   even if the owner carries a matching (forged) permission, and
4. A non-ended child whose concrete choice does not select `.parentLoan 0` does
   not block ending loan `0`, while a selected or symbolic edge still does. -/
theorem writeback_flavor_missing_local_and_forged_path_tests :
    -- 1. Released-loan flavor must match its phase:
    (let mkSt (outPhase : LoanPhase LensTestVal) : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutJoined [5] [6]⟩]
         loans := [⟨6, outPhase, ⟨.atom 0, .unborrowed⟩, .rootParam 9⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     writebackRegionTargets lensTestValAlg 5 [5, 6] [(.localReg 0, [])]
       [.atom 7] (mkSt .activeMut) = none ∧
     (match writebackRegionTargets lensTestValAlg 5 [5, 6]
         [(.localReg 0, [])] [.atom 7] (mkSt .activeShared) with
      | some st' => getLocal lensTestValAlg 0 st' = some (.atom 7)
      | none => False)) ∧
    -- 2. Inactive leaf on a missing local is skipped, not allocated:
    (let st : SymState LensTestVal :=
       { locals := [⟨.atom 10, .mutLocked 0⟩]
         loans :=
           [⟨0, .activeMut, ⟨.atom 55, .unborrowed⟩,
             .choice (.atom 0) (.direct (.localReg 1) [])
               (.direct (.localReg 0) [])⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     match endLoanInState lensTestValAlg 0 st with
     | .ok st' =>
       st'.locals.length = 1 ∧ getLocal lensTestValAlg 0 st' = some (.atom 55)
     | .fail => False) ∧
    -- 3. Shared target path must exist in the owner value:
    (let mkSt (ownerVal : LensTestVal) : SymState LensTestVal :=
       { locals := [⟨ownerVal, .split [([0], .shared [0])]⟩]
         loans :=
           [⟨0, .activeShared, ⟨.atom 1, .unborrowed⟩,
             .direct (.localReg 0) [0]⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     endLoanInState lensTestValAlg 0 (mkSt (.atom 10)) = .fail ∧
     (match endLoanInState lensTestValAlg 0
         (mkSt (.node (.atom 1) (.atom 2))) with
      | .ok st' =>
        isUnborrowed (getLocalCell lensTestValAlg 0 st').perm = true
      | .fail => False)) ∧
    -- 4. Branch-sensitive child edges:
    (let child (c : LensTestVal) : LoanEntry LensTestVal :=
       ⟨1, .activeMut, ⟨.atom 0, .unborrowed⟩,
        .choice c (.direct (.parentLoan 0) []) (.direct (.localReg 1) [])⟩
     let parent : LoanEntry LensTestVal :=
       ⟨0, .activeMut, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
     noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child (.atom 0)] =
       true ∧
     noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child (.atom 1)] =
       false ∧
     noActiveChildLoanEdgesIn lensTestValAlg 0
       [parent, child (.node (.atom 0) (.atom 1))] = false ∧
     noActiveChildLoanEdges 0 [parent, child (.atom 0)] = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Tests for `LoanGraph`:
1. `getOwnerForMut` rejects a local beyond `st.locals`, and
2. `stateCleanAtReturn` rejects a state in which a local still carries a
   permission for an ended loan. -/
theorem owner_bounds_and_clean_return_tests :
    -- 1. No mutable access to a missing local:
    getOwnerForMut lensTestValAlg (.localReg 2)
      (⟨[], [], [], [], [], 0⟩ : SymState LensTestVal) = none ∧
    -- 2. Residual permissions block the return boundary:
    (let mkSt (p : PermTree) : SymState LensTestVal :=
       { locals := [⟨.atom 1, p⟩]
         loans :=
           [⟨7, .ended, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩]
         regionGroups := []
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     stateCleanAtReturn (mkSt (.mutLocked 7)) = false ∧
     stateCleanAtReturn (mkSt .unborrowed) = true) :=
  ⟨rfl, ⟨rfl, rfl⟩⟩

/-- Tests for region-group retirement and the return
boundary:
1. `endRegionGroupInState` rejects an `.activeMut` output loan that appears in
   the shared half of an input permission, checking flavors against the phases
   before the outputs are retired, and still ends the consistent group, and
2. `stateCleanAtReturn` rejects duplicate region-group IDs, even when every
   group is inactive. -/
theorem region_retirement_flavor_and_duplicate_group_tests :
    (let rg : RegionGroupEntry LensTestVal :=
       { groupId := 0
         active := true
         lockLid := 5
         inputTargets := [(.localReg 0, [])]
         outputLoans := [6]
         requiredChildren := []
         backFn := fun outs _ => some (outs, []) }
     let mkSt (p : PermTree) : SymState LensTestVal :=
       { locals := [⟨.atom 10, p⟩]
         loans := [⟨6, .activeMut, ⟨.atom 7, .unborrowed⟩, .regionOut 0 0⟩]
         regionGroups := [rg]
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     endRegionGroupInState lensTestValAlg 0 (mkSt (.mutJoined [5] [6])) =
       .fail ∧
     (match endRegionGroupInState lensTestValAlg 0 (mkSt (.mutLocked 5)) with
      | .ok st' => getLocal lensTestValAlg 0 st' = some (.atom 7)
      | .fail => False)) ∧
    (let rgDone : RegionGroupEntry LensTestVal :=
       { groupId := 3
         active := false
         lockLid := 0
         inputTargets := []
         outputLoans := []
         requiredChildren := []
         backFn := fun outs _ => some (outs, []) }
     let mkSt (rgs : List (RegionGroupEntry LensTestVal)) :
         SymState LensTestVal :=
       { locals := []
         loans := []
         regionGroups := rgs
         regionDeposits := []
         spatial := []
         nextSpatialTag := 0 }
     stateCleanAtReturn (mkSt [rgDone, rgDone]) = false ∧
     stateCleanAtReturn (mkSt [rgDone]) = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Tests for `setLocalChecked`: it writes a copyable value to an existing or
fresh local, but rejects a non-copyable active mutable handle, a local behind a
live `&mut` or `&` borrow, and a slot two or more past the end. -/
theorem setLocalChecked_tests :
    let loans : List (LoanEntry LensTestVal) :=
      [⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩, .rootParam 3⟩,
       ⟨5, .activeShared, ⟨.atom 50, .unborrowed⟩, .rootParam 5⟩]
    let mkSt (p : PermTree) : SymState LensTestVal :=
      ⟨[⟨.ref 3 [], p⟩], loans, [], [], [], 0⟩
    (match setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt .unborrowed) with
     | some st' => getLocal lensTestValAlg 0 st' = some (.atom 2)
     | none => False) ∧
    (match setLocalChecked lensTestValAlg 1 (.atom 2) (mkSt .unborrowed) with
     | some st' => st'.locals.length = 2
     | none => False) ∧
    (match setLocalChecked lensTestValAlg 1 (.ref 5 []) (mkSt .unborrowed) with
     | some st' => getLocal lensTestValAlg 1 st' = some (.ref 5 [])
     | none => False) ∧
    setLocalChecked lensTestValAlg 0 (.ref 3 []) (mkSt .unborrowed) = none ∧
    setLocalChecked lensTestValAlg 1 (.ref 3 []) (mkSt .unborrowed) = none ∧
    setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt (.mutLocked 3)) = none ∧
    setLocalChecked lensTestValAlg 0 (.atom 2) (mkSt (.shared [3])) = none ∧
    setLocalChecked lensTestValAlg 2 (.atom 2) (mkSt .unborrowed) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- After an untaken parent loan has ended, ending a
child whose concrete choice did not select that parent succeeds, while a
residual permission for the child on the ended parent still fails. -/
theorem inactive_ended_parent_cleanup_tests :
    let mkSt (parentPerm : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 1⟩]
        loans :=
          [⟨0, .ended, ⟨.atom 5, parentPerm⟩, .direct (.localReg 3) []⟩,
           ⟨1, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 0) (.direct (.parentLoan 0) [])
              (.direct (.localReg 0) [])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 1 (mkSt .unborrowed) with
     | .ok st' => getLocal lensTestValAlg 0 st' = some (.atom 77)
     | .fail => False) ∧
    endLoanInState lensTestValAlg 1 (mkSt (.mutLocked 1)) = .fail :=
  ⟨rfl, rfl⟩

/-- A non-ended child with a truncated choice target
`[.choiceJoin c, .direct (.parentLoan 0) []]` still counts as a dependency of
loan `0` (`activeTargetLeaves` falls back to every serialized leaf), so the
parent cannot be ended underneath it. -/
theorem malformed_child_target_dependency_tests :
    let malformed : BackTarget LensTestVal :=
      ⟨[.choiceJoin (.atom 1), .direct (.parentLoan 0) []]⟩
    let child : LoanEntry LensTestVal :=
      ⟨1, .activeMut, ⟨.atom 0, .unborrowed⟩, malformed⟩
    let parent : LoanEntry LensTestVal :=
      ⟨0, .activeMut, ⟨.atom 0, .unborrowed⟩, .direct (.localReg 0) []⟩
    activeTargetLeaves lensTestValAlg malformed = [(.parentLoan 0, [])] ∧
    noActiveChildLoanEdgesIn lensTestValAlg 0 [parent, child] = false :=
  ⟨rfl, rfl⟩

/-- An untaken leaf naming an `.activeShared` parent
that carries no permission for the child is skipped during mutable cleanup,
while a residual permission on it still fails. -/
theorem inactive_shared_parent_cleanup_tests :
    let mkSt (parentPerm : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .mutLocked 1⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 5, parentPerm⟩, .direct (.localReg 3) []⟩,
           ⟨1, .activeMut, ⟨.atom 77, .unborrowed⟩,
            .choice (.atom 0) (.direct (.parentLoan 0) [])
              (.direct (.localReg 0) [])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    (match endLoanInState lensTestValAlg 1 (mkSt .unborrowed) with
     | .ok st' => getLocal lensTestValAlg 0 st' = some (.atom 77)
     | .fail => False) ∧
    endLoanInState lensTestValAlg 1 (mkSt (.mutLocked 1)) = .fail :=
  ⟨rfl, rfl⟩

/-- Handle accounting:
1. `collectHandles` counts a handle in both arms of `zipVal c h h` once; the
   upper bound of `zipVal c h3 h4` holds both handles, the lower bound
   neither, and a context fixing `c` selects one arm,
2. `maxUnionNat` and `minInterNat` take per-element maxima and minima,
3. only root (`[]`) handles to unique `.activeShared` loans are copyable
   (`.ended`, `.activeMut`, `.spatialPinned`, and non-empty sub-paths are
   rejected),
4. `replaceableVals` accepts a conditional swap, a plain swap, and writing an
   unchanged handle back as `zipVal c h h`; it rejects a fabricated
   duplicate, a write that duplicates a handle under distinct guards, a handle
   retargeted to a different `SubPath` (`.ref 3 [0]` -> `.ref 3 [1]`), or a
   handle to an `.ended` loan, while letting root shared handles be copied,
5. `installNewLoanInLocal` rejects `.rootParam` targets, self-referential
   `subVal = .ref 0 []`, and unlocked or mismatched `subVal` handles, while
   accepting a properly locked `.direct` borrow, and
6. the guard enumeration keeps one entry per identifiable guard and skips
   guards that `sameCond` cannot identify. -/
theorem handle_accounting_tests :
    let c : LensTestVal := .node (.atom 0) (.atom 0)
    let d : LensTestVal := .node (.atom 0) (.atom 1)
    let h (l : LoanId) : LensTestVal := .ref l []
    let z (g a b : LensTestVal) : LensTestVal := lensTestZipVal g a b
    let loans : List (LoanEntry LensTestVal) :=
      [⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩, .rootParam 3⟩,
       ⟨4, .activeMut, ⟨.atom 40, .unborrowed⟩, .rootParam 4⟩,
       ⟨5, .activeShared, ⟨.atom 50, .unborrowed⟩, .rootParam 5⟩,
       ⟨6, .ended, ⟨.atom 60, .unborrowed⟩, .direct (.localReg 0) []⟩]
    let stEmpty : SymState LensTestVal := ⟨[], [], [], [], [], 0⟩
    let stLocked0 : SymState LensTestVal :=
      ⟨[⟨.atom 10, .mutLocked 0⟩], [], [], [], [], 0⟩
    -- 1. Scans:
    collectHandles lensTestValAlg (z c (h 3) (h 3)) = some [3] ∧
    collectHandles lensTestValAlg (.node (h 3) (h 4)) = some [3, 4] ∧
    collectHandles lensTestValAlg (z (h 3) (.atom 1) (.atom 2)) = none ∧
    handleFreeVal lensTestValAlg (z (h 3) (.atom 1) (.atom 2)) = false ∧
    replaceableVal lensTestValAlg loans (h 3)
      (z (h 3) (.atom 1) (.atom 2)) = false ∧
    collectHandlesIn lensTestValAlg false [] (z c (h 3) (h 4)) =
      some [3, 4] ∧
    collectHandlesIn lensTestValAlg true [] (z c (h 3) (h 4)) = some [] ∧
    collectHandlesIn lensTestValAlg false [(c, true)] (z c (h 3) (h 4)) =
      some [3] ∧
    -- 2. Multiset bounds:
    maxUnionNat [1, 1, 2] [1, 3] = [1, 1, 2, 3] ∧
    minInterNat [1, 1, 2] [1, 3, 1] = [1, 1] ∧
    -- 3. Copyability:
    handleCopyable loans 5 = true ∧
    handleCopyable loans 6 = false ∧
    handleCopyable loans 3 = false ∧
    handleCopyable loans 9 = false ∧
    copyableVal lensTestValAlg loans (h 5) = true ∧
    copyableVal lensTestValAlg loans (.ref 5 [0]) = false ∧
    copyableVal lensTestValAlg loans (h 6) = false ∧
    copyableVal lensTestValAlg loans (.node (h 5) (h 3)) = false ∧
    -- 4. Replacement:
    replaceableVals lensTestValAlg loans [z c (h 3) (h 4), z c (h 4) (h 3)]
      [z c (h 4) (h 3), z c (h 3) (h 4)] = true ∧
    replaceableVals lensTestValAlg loans [h 3, h 4] [h 4, h 3] = true ∧
    replaceableVal lensTestValAlg loans (h 3) (z c (h 3) (h 3)) = true ∧
    replaceableVal lensTestValAlg loans (.ref 3 [0]) (.ref 3 [1]) = false ∧
    replaceableVal lensTestValAlg loans (h 6) (h 6) = false ∧
    replaceableVals lensTestValAlg loans [h 3, h 4] [h 3, h 3] = false ∧
    replaceableVals lensTestValAlg loans [h 3, h 4]
      [z c (h 3) (h 4), z d (h 4) (h 3)] = false ∧
    replaceableVals lensTestValAlg loans [h 3, h 4]
      [z c (h 3) (h 4), z c (h 4) (h 3)] = true ∧
    replaceableVals lensTestValAlg loans [h 5] [h 5, h 5] = true ∧
    replaceableVals lensTestValAlg loans [h 5] [.ref 5 [0]] = false ∧
    -- 5. Loan allocation guards:
    installNewLoanInLocal lensTestValAlg 0 .activeMut
      (.rootParam 0) stEmpty = none ∧
    installNewLoanInLocal lensTestValAlg 1 .activeMut
      (.direct (.localReg 0) [])
      ⟨[⟨h 0, .mutLocked 0⟩], [], [], [], [], 0⟩ = none ∧
    installLensLoanInLocal lensTestValAlg 1 [(.localReg 0, [])]
      (fun _ => some (h 3)) (fun _ v => some [v])
      ⟨[⟨.atom 10, .mutLocked 1⟩], [⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩,
        .rootParam 3⟩], [], [], [], 0⟩ = none ∧
    -- Installing an `.activeShared` loan rejects a non-copyable `.activeMut`
    -- handle `h 3` even when the shared-locked source local already holds `h 3`:
    installNewLoanInLocal lensTestValAlg 1 .activeShared
      (.direct (.localReg 0) [])
      ⟨[⟨h 3, .shared [1]⟩], [⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩,
        .rootParam 3⟩], [], [], [], 0⟩ = none ∧
    (match installNewLoanInLocal lensTestValAlg 1 .activeMut
        (.direct (.localReg 0) []) stLocked0 with
     | some st' =>
       getLocal lensTestValAlg 1 st' = some (h 0) ∧
       ownerPathValue lensTestValAlg (.parentLoan 0) [] st' = some (.atom 10)
     | none => False) ∧
    -- 6. Guard enumeration:
    identifiableConds lensTestValAlg [c, c, d] = [c, d] ∧
    identifiableConds lensTestValAlg [.atom 1, h 9] = [] ∧
    (condAssignments [c, d]).length = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Correlated overlap checks:
1. `leafBranchContexts` lists the guards on the path to a written leaf, gives
   `[[]]` for an unconditional leaf, and falls back to `[[]]` when no path
   selects the leaf,
2. `targetMayHitIn` follows a guard that the context fixes, treats other
   guards as independent, and follows concrete conditions,
3. `liveLoanTargetsOverlap` reports a live loan that overlaps in the writer's
   branch, but not one that overlaps only in the other branch or that is
   exempt, and
4. two loans whose targets a branch join swapped can end in either order
   because `evalBackVal` preserves `x0[0]`'s aggregate fields via
   `zipOrKeepSameRef` and `projectBranchOrFields`. -/
theorem correlated_overlap_tests :
    let c : LensTestVal := .node (.atom 0) (.atom 0)
    let d : LensTestVal := .node (.atom 0) (.atom 1)
    let x0 (p : SubPath) : BackTarget LensTestVal := .direct (.localReg 0) p
    let x1 : BackTarget LensTestVal := .direct (.localReg 1) []
    let x2 : BackTarget LensTestVal := .direct (.localReg 2) []
    let hit0 (t : OwnerRef × SubPath) : Bool :=
      OwnerRef.beq t.1 (.localReg 0) && subPathEq t.2 [0]
    let ov (t : OwnerRef × SubPath) : Bool :=
      OwnerRef.beq t.1 (.localReg 0) && subPathOverlaps t.2 [0]
    let live (t : BackTarget LensTestVal) : List (LoanEntry LensTestVal) :=
      [⟨2, .activeMut, ⟨.atom 77, .unborrowed⟩, t⟩]
    let st : SymState LensTestVal :=
      { locals := [⟨.node (.node (.atom 1) (.atom 2)) (.atom 3),
                    .split [([0], .mutLocked 1), ([0, 1], .mutLocked 2)]⟩,
                   ⟨.atom 9, .mutLocked 1⟩, ⟨.atom 8, .mutLocked 2⟩]
        loans :=
          [⟨1, .activeMut, ⟨.node (.atom 50) (.atom 60), .unborrowed⟩,
            .choice c (x0 [0]) x1⟩,
           ⟨2, .activeMut, ⟨.atom 77, .unborrowed⟩, .choice c x2 (x0 [0, 1])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let endBoth (a b : LoanId) : Bool :=
      match endLoanInState lensTestValAlg a st with
      | .ok st1 =>
        match endLoanInState lensTestValAlg b st1 with
        | .ok _ => true
        | .fail => false
      | .fail => false
    -- 1. Writer contexts:
    leafBranchContexts lensTestValAlg hit0 (.choice c (x0 [0]) x1) =
      [[(c, true)]] ∧
    leafBranchContexts lensTestValAlg hit0 (x0 [0]) = [[]] ∧
    leafBranchContexts lensTestValAlg hit0 x1 = [[]] ∧
    -- 2. Following live targets:
    targetMayHitIn lensTestValAlg [(c, true)] ov (.choice c (x0 [0, 1]) x2) =
      true ∧
    targetMayHitIn lensTestValAlg [(c, false)] ov (.choice c (x0 [0, 1]) x2) =
      false ∧
    targetMayHitIn lensTestValAlg [(d, false)] ov (.choice c (x0 [0, 1]) x2) =
      true ∧
    targetMayHitIn lensTestValAlg [] ov (.choice (.atom 0) (x0 [0, 1]) x2) =
      false ∧
    -- 3. Live-loan overlap:
    liveLoanTargetsOverlap lensTestValAlg [[(c, true)]] [1] (.localReg 0) [0]
      (live (.choice c (x0 [0, 1]) x2)) [] = true ∧
    liveLoanTargetsOverlap lensTestValAlg [[(c, false)]] [1] (.localReg 0) [0]
      (live (.choice c (x0 [0, 1]) x2)) [] = false ∧
    liveLoanTargetsOverlap lensTestValAlg [[(c, true)]] [2] (.localReg 0) [0]
      (live (.choice c (x0 [0, 1]) x2)) [] = false ∧
    -- 4. Swapped diamond loans:
    endBoth 2 1 = true ∧
    endBoth 1 2 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Region deposits and shared children:
1. `takeChildDeposits` takes deposits in the order of `children` (then
   deposit order), counts a repeated child once, and leaves other groups'
   deposits, and
2. a group cannot end while another active group requires one of its
   children, since it would consume the deposits that group expects; without
   the second requirement it ends. -/
theorem region_deposit_and_shared_child_tests :
    let deps : List (RegionGroupId × LensTestVal) :=
      [(1, .atom 10), (3, .atom 30), (2, .atom 20), (1, .atom 11)]
    let rg (gid lock reg : Nat) (req : List RegionGroupId) (act : Bool) :
        RegionGroupEntry LensTestVal :=
      { groupId := gid
        active := act
        lockLid := lock
        inputTargets := if act then [(.localReg reg, [])] else []
        outputLoans := []
        requiredChildren := req
        backFn := fun _ _ => some (if act then [.atom 42] else [], []) }
    let st (req1 : List RegionGroupId) : SymState LensTestVal :=
      { locals := [⟨.atom 1, .mutLocked 5⟩, ⟨.atom 2, .mutLocked 6⟩]
        loans :=
          [⟨5, .ended, ⟨.atom 0, .unborrowed⟩, .regionOut 0 0⟩,
           ⟨6, .ended, ⟨.atom 0, .unborrowed⟩, .regionOut 1 0⟩,
           ⟨8, .ended, ⟨.atom 0, .unborrowed⟩, .regionOut 7 0⟩]
        regionGroups :=
          [rg 0 5 0 [7] true, rg 1 6 1 req1 true, rg 7 8 0 [] false]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    -- 1. Deposits:
    takeChildDeposits [2, 1] deps =
      ([.atom 20, .atom 10, .atom 11], [(3, .atom 30)]) ∧
    (takeChildDeposits [2, 1, 2] deps).1 = [.atom 20, .atom 10, .atom 11] ∧
    -- 2. Shared children:
    isOk (endRegionGroupInState lensTestValAlg 0 (st [7])) = false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (st [])) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `releaseSharedLeaves` (through `endLoanInState` on a shared loan) releases
an inactive `.choice` leaf that holds the loan as a shared permission, skips
one that the loan never locked, and rejects one that holds the loan as a
mutable permission. -/
theorem inactive_choice_leaf_shared_release_tests :
    let st (p1 : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 10, .shared [0]⟩, ⟨.atom 20, p1⟩]
        loans :=
          [⟨0, .activeShared, ⟨.atom 10, .unborrowed⟩,
            .choice (.atom 1) (.direct (.localReg 0) [])
              (.direct (.localReg 1) [])⟩]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    isOk (endLoanInState lensTestValAlg 0 (st (.shared [0]))) = true ∧
    isOk (endLoanInState lensTestValAlg 0 (st .unborrowed)) = true ∧
    isOk (endLoanInState lensTestValAlg 0 (st (.mutLocked 0))) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Region-group writeback checks the owner's permission and handles disjoint
sub-paths of one owner:
1. ending a group whose input place does not hold the lock fails, while the
   same group with the lock held ends, and
2. a group whose inputs are the disjoint sub-paths `[0]` and `[1]` of one
   local writes both and leaves the local unborrowed. -/
theorem region_owner_perm_and_disjoint_writeback_tests :
    let rg (inputs : List (OwnerRef × SubPath)) (outs : List LensTestVal) :
        RegionGroupEntry LensTestVal :=
      { groupId := 0
        active := true
        lockLid := 0
        inputTargets := inputs
        outputLoans := []
        requiredChildren := []
        backFn := fun _ _ => some (outs, []) }
    let stOwner (p : PermTree) : SymState LensTestVal :=
      { locals := [⟨.atom 1, p⟩]
        loans := []
        regionGroups := [rg [(.localReg 0, [])] [.atom 2]]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stSplit : SymState LensTestVal :=
      { locals :=
          [⟨.node (.atom 1) (.atom 2),
            .split [([0], .mutLocked 0), ([1], .mutLocked 0)]⟩]
        loans := []
        regionGroups :=
          [rg [(.localReg 0, [0]), (.localReg 0, [1])] [.atom 11, .atom 22]]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    isOk (endRegionGroupInState lensTestValAlg 0 (stOwner .unborrowed)) =
      false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stOwner (.mutLocked 0))) =
      true ∧
    (match endRegionGroupInState lensTestValAlg 0 stSplit with
     | .ok st' =>
       getLocal lensTestValAlg 0 st' = some (.node (.atom 11) (.atom 22)) ∧
       isUnborrowed (getLocalPerm lensTestValAlg 0 st') = true
     | .fail => False) :=
  ⟨rfl, rfl, ⟨rfl, rfl⟩⟩

/-- Every writeback path counts handles across the whole writeback, so a
callee may swap two `&mut` references held in two places but not duplicate
one:
1. ending a loan whose `.lensCall` target writes `[h4, h3]` over `[h3, h4]`
   succeeds, and writing `[h3, h3]` fails (`writebackLeaves`),
2. `writebackLensTargets` accepts the swap and rejects the duplicate,
3. ending a region group whose callback returns the swap succeeds, and the
   duplicate fails (`writebackRegionTargets`), and
4. `writebackLeaves`, `writebackLensTargets`, and `writebackRegionTargets`
   reject overlapping targets (`[0]` and `[]` of one local), through which a
   later write could copy a handle placed by an earlier one, while disjoint
   targets succeed. (`endLoanInState` rejects such a loan target earlier, in
   `validateBackTarget`, so `writebackLeaves` is called directly.) -/
theorem writeback_handle_guard_tests :
    let h (l : LoanId) : LensTestVal := .ref l []
    let rootLoans : List (LoanEntry LensTestVal) :=
      [⟨3, .activeMut, ⟨.atom 30, .unborrowed⟩, .rootParam 3⟩,
       ⟨4, .activeMut, ⟨.atom 40, .unborrowed⟩, .rootParam 4⟩]
    let xs : List (OwnerRef × SubPath) := [(.localReg 0, []), (.localReg 1, [])]
    let stLens (back : LensTestVal → Option (List LensTestVal)) :
        SymState LensTestVal :=
      { locals := [⟨h 3, .mutLocked 0⟩, ⟨h 4, .mutLocked 0⟩]
        loans :=
          ⟨0, .activeMut, ⟨.atom 0, .unborrowed⟩, .lensCall xs back⟩ ::
            rootLoans
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stRegion (outs : List LensTestVal) : SymState LensTestVal :=
      { locals := [⟨h 3, .mutLocked 0⟩, ⟨h 4, .mutLocked 0⟩]
        loans := rootLoans
        regionGroups :=
          [{ groupId := 0
             active := true
             lockLid := 0
             inputTargets := xs
             outputLoans := []
             requiredChildren := []
             backFn := fun _ _ => some (outs, []) }]
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stOne (p : PermTree) : SymState LensTestVal :=
      { locals := [⟨.node (h 3) (.atom 1), p⟩]
        loans := rootLoans
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let overlapPerm : PermTree :=
      .split [([0], .mutLocked 0), ([], .mutLocked 0)]
    let disjointPerm : PermTree :=
      .split [([0], .mutLocked 0), ([1], .mutLocked 0)]
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    let isSome (o : Option (SymState LensTestVal)) : Bool :=
      match o with
      | some _ => true
      | none => false
    -- 1. Loan end through a `.lensCall` target:
    isOk (endLoanInState lensTestValAlg 0 (stLens (fun _ => some [h 4, h 3])))
      = true ∧
    isOk (endLoanInState lensTestValAlg 0 (stLens (fun _ => some [h 3, h 3])))
      = false ∧
    -- 2. Callee lens writeback:
    isSome (writebackLensTargets lensTestValAlg 0 xs [h 4, h 3]
      (stLens (fun _ => none))) = true ∧
    isSome (writebackLensTargets lensTestValAlg 0 xs [h 3, h 3]
      (stLens (fun _ => none))) = false ∧
    -- 3. Region group:
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion [h 4, h 3])) =
      true ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion [h 3, h 3])) =
      false ∧
    -- 4. Overlapping targets:
    isSome (writebackLeaves lensTestValAlg 0
      (.lensCall [(.localReg 0, [0]), (.localReg 0, [])]
        (fun _ => some [.atom 5, .node (h 3) (h 3)]))
      (.atom 0) [(.localReg 0, [0]), (.localReg 0, [])]
      (stOne overlapPerm)) = false ∧
    isSome (writebackLensTargets lensTestValAlg 0
      [(.localReg 0, [0]), (.localReg 0, [])] [.atom 5, .node (h 3) (h 3)]
      (stOne overlapPerm)) = false ∧
    isSome (writebackRegionTargets lensTestValAlg 0 [0]
      [(.localReg 0, [0]), (.localReg 0, [])] [.atom 5, .node (h 3) (h 3)]
      (stOne overlapPerm)) = false ∧
    isSome (writebackLensTargets lensTestValAlg 0
      [(.localReg 0, [0]), (.localReg 0, [1])] [.atom 5, h 3]
      (stOne disjointPerm)) = true ∧
    isSome (writebackRegionTargets lensTestValAlg 0 [0]
      [(.localReg 0, [0]), (.localReg 0, [1])] [.atom 5, h 3]
      (stOne disjointPerm)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `lookupLensTargetVal` selects the value a lens call returns for a target
(or keeps the old value for a place it does not name, and fails on an arity
mismatch); `evalBackVal` writes a loan's new value at a direct leaf, keeps
other places, follows concrete choices, merges symbolic ones with `zipVal`,
and takes `.lensCall` results from the backward function. -/
theorem lookupLensTargetVal_and_evalBackVal_tests :
    let x0 : OwnerRef := .localReg 0
    let x1 : OwnerRef := .localReg 1
    let c : LensTestVal := .node (.atom 0) (.atom 0)
    let lens : BackTarget LensTestVal :=
      .lensCall [(x0, []), (x1, [])] (fun v => some [v, .atom 9])
    let old : LensTestVal := .atom 0
    lookupLensTargetVal x0 [] old [(x0, []), (x1, [])] [.atom 1, .atom 2] =
      some (.atom 1) ∧
    lookupLensTargetVal x1 [] old [(x0, []), (x1, [])] [.atom 1, .atom 2] =
      some (.atom 2) ∧
    lookupLensTargetVal (.localReg 2) [] old [(x0, []), (x1, [])]
      [.atom 1, .atom 2] = some (.atom 0) ∧
    lookupLensTargetVal x0 [] old [(x0, []), (x1, [])] [.atom 1] = none ∧
    evalBackVal lensTestValAlg x0 [] (.direct x0 []) (.atom 5) (.atom 1) =
      some (.atom 5) ∧
    evalBackVal lensTestValAlg x1 [] (.direct x0 []) (.atom 5) (.atom 1) =
      some (.atom 1) ∧
    evalBackVal lensTestValAlg x1 []
      (.choice (.atom 0) (.direct x0 []) (.direct x1 [])) (.atom 5)
      (.atom 1) = some (.atom 5) ∧
    evalBackVal lensTestValAlg x0 []
      (.choice c (.direct x0 []) (.direct x1 [])) (.atom 5) (.atom 1) =
      some (lensTestValAlg.zipVal c (.atom 5) (.atom 1)) ∧
    evalBackVal lensTestValAlg x1 [] lens (.atom 5) (.atom 1) =
      some (.atom 9) ∧
    evalBackVal lensTestValAlg x0 [] (.rootParam 0) (.atom 5) (.atom 1) =
      none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Writebacks refuse to change storage that another live borrow observes,
and a region lock must not name a live loan:
1. ending loan `1` on `x0[0]` fails while a shared loan `2` observes `x0`,
   through `endLoanInState` (`writebackLeaf`) and `writebackLensTargets`,
2. ending a region group over `x0[0]` fails while loan `2` observes `x0`
   (`writebackRegionTargets`), and
3. a region group whose `lockLid` names a live, non-output loan cannot end:
   the loan would stay active while the group releases its permission.
Each case succeeds once loan `2` (or the lock's loan) has ended. -/
theorem live_observer_and_lock_guard_tests :
    let x0 : OwnerRef := .localReg 0
    let mk (locals : List (PlaceCell LensTestVal))
        (loans : List (LoanEntry LensTestVal))
        (rgs : List (RegionGroupEntry LensTestVal)) : SymState LensTestVal :=
      { locals := locals
        loans := loans
        regionGroups := rgs
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let rg (lock : LoanId) (inputs : List (OwnerRef × SubPath)) :
        RegionGroupEntry LensTestVal :=
      ⟨0, true, lock, inputs, [], [], fun _ _ => some ([.atom 7], [])⟩
    let observer (ph : LoanPhase LensTestVal) : LoanEntry LensTestVal :=
      ⟨2, ph, ⟨.atom 1, .unborrowed⟩, .direct x0 []⟩
    let stLoan (ph : LoanPhase LensTestVal) :=
      mk [⟨.node (.atom 1) (.atom 2), .split [([0], .mutLocked 1)]⟩]
        [⟨1, .activeMut, ⟨.atom 9, .unborrowed⟩, .direct x0 [0]⟩, observer ph]
        []
    let stRegion (ph : LoanPhase LensTestVal) :=
      mk [⟨.node (.atom 1) (.atom 2), .split [([0], .mutLocked 9)]⟩]
        [⟨9, .ended, ⟨.atom 0, .unborrowed⟩, .regionOut 0 0⟩, observer ph]
        [rg 9 [(x0, [0])]]
    let stLock (ph : LoanPhase LensTestVal) :=
      mk [⟨.atom 10, .mutLocked 5⟩]
        [⟨5, ph, ⟨.atom 99, .unborrowed⟩, .direct x0 []⟩] [rg 5 [(x0, [])]]
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    let isSome (o : Option (SymState LensTestVal)) : Bool :=
      match o with
      | some _ => true
      | none => false
    -- 1. Loan end and lens writeback:
    isOk (endLoanInState lensTestValAlg 1 (stLoan .activeShared)) = false ∧
    isOk (endLoanInState lensTestValAlg 1 (stLoan .ended)) = true ∧
    isSome (writebackLensTargets lensTestValAlg 1 [(x0, [0])] [.atom 5]
      (stLoan .activeShared)) = false ∧
    isSome (writebackLensTargets lensTestValAlg 1 [(x0, [0])] [.atom 5]
      (stLoan .ended)) = true ∧
    -- 2. Region writeback:
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion .activeShared)) =
      false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stRegion .ended)) = true ∧
    -- 3. Live lock:
    isOk (endRegionGroupInState lensTestValAlg 0 (stLock .activeMut)) = false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stLock .ended)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Retiring loans checks for remaining borrows and leftover permissions:
1. ending a region group fails while its output loan has an active child
   loan, an active region group borrowing from it, or a forged child
   permission in its cell (`collectAndRetireOutputLoans`),
2. ending a loan fails while an active region group borrows from it, or while
   its cell carries a forged child permission (`endLoanInState`,
   `deactivateLoan`), and
3. ending a region group fails if another place still holds the lock's
   permission afterwards (`noResidualLoanListPerm`).
Each case succeeds once the borrow has ended or the permission is gone. -/
theorem retirement_guard_tests :
    let x0 : OwnerRef := .localReg 0
    let mk (locals : List (PlaceCell LensTestVal))
        (loans : List (LoanEntry LensTestVal))
        (rgs : List (RegionGroupEntry LensTestVal)) : SymState LensTestVal :=
      { locals := locals
        loans := loans
        regionGroups := rgs
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let rg (gid lock : Nat) (inputs : List (OwnerRef × SubPath))
        (outs : List LoanId) (act : Bool) (vals : List LensTestVal) :
        RegionGroupEntry LensTestVal :=
      ⟨gid, act, lock, inputs, outs, [], fun _ _ => some (vals, [])⟩
    let sentinel : LoanEntry LensTestVal :=
      ⟨9, .ended, ⟨.atom 0, .unborrowed⟩, .regionOut 0 0⟩
    let stOut (p : PermTree) (extra : List (LoanEntry LensTestVal))
        (rgs : List (RegionGroupEntry LensTestVal)) :=
      mk [⟨.atom 1, .mutLocked 9⟩]
        ([sentinel, ⟨3, .activeMut, ⟨.atom 30, p⟩, .regionOut 0 0⟩] ++ extra)
        (rg 0 9 [(x0, [])] [3] true [.atom 7] :: rgs)
    let child (ph : LoanPhase LensTestVal) : LoanEntry LensTestVal :=
      ⟨4, ph, ⟨.atom 30, .unborrowed⟩, .direct (.parentLoan 3) []⟩
    let stEdge (act : Bool) :=
      mk [⟨.atom 10, .mutLocked 0⟩]
        [⟨0, .activeMut, ⟨.atom 10, .unborrowed⟩, .direct x0 []⟩]
        [rg 0 9 [(.parentLoan 0, [])] [] act [.atom 7]]
    let stCell (p : PermTree) :=
      mk [⟨.atom 10, .mutLocked 0⟩]
        [⟨0, .activeMut, ⟨.atom 10, p⟩, .direct x0 []⟩] []
    let stResidual (p1 : PermTree) :=
      mk [⟨.atom 1, .mutLocked 9⟩, ⟨.atom 2, p1⟩] [sentinel]
        [rg 0 9 [(x0, [])] [] true [.atom 7]]
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    -- 1. Output loans:
    isOk (endRegionGroupInState lensTestValAlg 0
      (stOut .unborrowed [child .activeMut] [])) = false ∧
    isOk (endRegionGroupInState lensTestValAlg 0
      (stOut .unborrowed [child .ended] [])) = true ∧
    isOk (endRegionGroupInState lensTestValAlg 0
      (stOut .unborrowed [] [rg 1 8 [(.parentLoan 3, [])] [] true []])) =
      false ∧
    isOk (endRegionGroupInState lensTestValAlg 0
      (stOut .unborrowed [] [rg 1 8 [(.parentLoan 3, [])] [] false []])) =
      true ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stOut (.mutLocked 4) [] []))
      = false ∧
    -- 2. Loans:
    isOk (endLoanInState lensTestValAlg 0 (stEdge true)) = false ∧
    isOk (endLoanInState lensTestValAlg 0 (stEdge false)) = true ∧
    isOk (endLoanInState lensTestValAlg 0 (stCell (.mutLocked 7))) = false ∧
    isOk (endLoanInState lensTestValAlg 0 (stCell .unborrowed)) = true ∧
    -- 3. Residual lock permission:
    isOk (endRegionGroupInState lensTestValAlg 0 (stResidual (.mutLocked 9)))
      = false ∧
    isOk (endRegionGroupInState lensTestValAlg 0 (stResidual .unborrowed)) =
      true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Permission flavors must match the loan's kind:
1. a mutable writeback fails where the owner holds the loan as both mutable
   and shared (`.mutJoined [0] [0]`), through `endLoanInState`
   (`writebackLeaf`) and `writebackLensTargets`,
2. ending a shared loan fails where the owner holds it mutably as well
   (`releaseSharedLeavesPass`), or where a place outside the target still
   holds it afterwards (`noResidualLoanPerm`), and
3. a handle to a loan ID that names two loans is not copyable, even if the
   first is shared (`handleCopyable`).
Each case has a succeeding twin with a consistent permission. -/
theorem permission_flavor_guard_tests :
    let x0 : OwnerRef := .localReg 0
    let mk (locals : List (PlaceCell LensTestVal))
        (loans : List (LoanEntry LensTestVal)) : SymState LensTestVal :=
      { locals := locals
        loans := loans
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    let stMut (p : PermTree) :=
      mk [⟨.atom 1, p⟩] [⟨0, .activeMut, ⟨.atom 9, .unborrowed⟩, .direct x0 []⟩]
    let stShared (p0 p1 : PermTree) :=
      mk [⟨.atom 1, p0⟩, ⟨.atom 2, p1⟩]
        [⟨0, .activeShared, ⟨.atom 1, .unborrowed⟩, .direct x0 []⟩]
    let shared5 : LoanEntry LensTestVal :=
      ⟨5, .activeShared, ⟨.atom 0, .unborrowed⟩, .rootParam 5⟩
    let mut5 : LoanEntry LensTestVal :=
      ⟨5, .activeMut, ⟨.atom 0, .unborrowed⟩, .rootParam 6⟩
    let isOk (o : EvalOutcome (SymState LensTestVal)) : Bool :=
      match o with
      | .ok _ => true
      | .fail => false
    let isSome (o : Option (SymState LensTestVal)) : Bool :=
      match o with
      | some _ => true
      | none => false
    -- 1. Mutable writebacks:
    isOk (endLoanInState lensTestValAlg 0 (stMut (.mutJoined [0] [0]))) =
      false ∧
    isOk (endLoanInState lensTestValAlg 0 (stMut (.mutLocked 0))) = true ∧
    isSome (writebackLensTargets lensTestValAlg 0 [(x0, [])] [.atom 5]
      (stMut (.mutJoined [0] [0]))) = false ∧
    isSome (writebackLensTargets lensTestValAlg 0 [(x0, [])] [.atom 5]
      (stMut (.mutLocked 0))) = true ∧
    -- 2. Shared releases:
    isOk (endLoanInState lensTestValAlg 0
      (stShared (.mutJoined [0] [0]) .unborrowed)) = false ∧
    isOk (endLoanInState lensTestValAlg 0
      (stShared (.shared [0]) (.shared [0]))) = false ∧
    isOk (endLoanInState lensTestValAlg 0
      (stShared (.shared [0]) .unborrowed)) = true ∧
    -- 3. Duplicate loan IDs:
    handleCopyable [shared5, mut5] 5 = false ∧
    handleCopyable [shared5] 5 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Target validation and the clean-return check:
1. a `.lensCall` naming the same place twice is rejected by both
   `validateBackTarget` and `validateSharedBackTarget` (a whole-target
   deduplication would hide the repeat), and `validateBackTarget` rejects a
   backward function returning the wrong number of values, while the
   single-target lens call validates, and
2. `stateCleanAtReturn` rejects leftover region deposits, a remaining spatial
   block, a loan cell that still carries a permission, and a duplicated loan
   ID, while the same state without them is clean. -/
theorem target_validation_and_clean_return_tests :
    let x0 : OwnerRef := .localReg 0
    let dupLens : BackTarget LensTestVal :=
      .lensCall [(x0, []), (x0, [])] (fun v => some [v, v])
    let oneLens : BackTarget LensTestVal :=
      .lensCall [(x0, [])] (fun v => some [v])
    let arityLens : BackTarget LensTestVal :=
      .lensCall [(x0, [])] (fun v => some [v, v])
    let ended : LoanEntry LensTestVal :=
      ⟨0, .ended, ⟨.atom 0, .unborrowed⟩, .direct x0 []⟩
    let clean : SymState LensTestVal :=
      { locals := [⟨.atom 1, .unborrowed⟩]
        loans := [ended]
        regionGroups := []
        regionDeposits := []
        spatial := []
        nextSpatialTag := 0 }
    -- 1. Lens-call targets:
    validateBackTarget lensTestValAlg dupLens (.atom 1) = false ∧
    validateSharedBackTarget lensTestValAlg dupLens = false ∧
    validateBackTarget lensTestValAlg arityLens (.atom 1) = false ∧
    validateBackTarget lensTestValAlg oneLens (.atom 1) = true ∧
    validateSharedBackTarget lensTestValAlg oneLens = true ∧
    -- 2. Clean return:
    stateCleanAtReturn clean = true ∧
    stateCleanAtReturn { clean with regionDeposits := [(0, .atom 1)] } =
      false ∧
    stateCleanAtReturn
      { clean with spatial := [⟨0, 0, .readWrite, 0, 0, []⟩] } = false ∧
    stateCleanAtReturn
      { clean with
        loans := [⟨0, .ended, ⟨.atom 0, .mutLocked 3⟩, .direct x0 []⟩] } =
      false ∧
    stateCleanAtReturn { clean with loans := [ended, ended] } = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.PureLift
