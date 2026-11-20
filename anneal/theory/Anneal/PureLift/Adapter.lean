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
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg

namespace Anneal.PureLift

/-!
# Operational Machine Adapters and Adequacy Theorem (`Adapter`)

Decouples `PureLift` from any specific operational semantics representation via
two interfaces:
- `SpatialModel`: interprets `PermTree` sub-place ownership and disjointness in
  a concrete memory model (`MachMem` and `Addr`).
- `OperationalAdapter`: connects `evalFnValue` to a concrete machine's
  multi-step reachability relation `ExecutesTo : Mach → Nat → Mach → Prop` via
  the adequacy theorem `pure_lift_sound`. The theorem does not derive the
  machine run: it assumes that the machine simulates the lifted evaluation
  (`hSim`) and that the initial states are related (`hInit`), and each use
  must discharge both for its machine.

Also provides three canonical adapter constructors covering:
1. Total step-function machines (`M1StepResult`, `m1OperationalAdapter`).
2. Relational trace-emitting small-step machines (`M2StepResult`,
   `m2OperationalAdapter`).
3. Allocation/offset heaps with Tree Borrows permission tags (`M3Mach`,
   `m3SpatialModel`, `m3OperationalAdapter`).
-/

/-- Spatial sub-place ownership realization interface over a concrete memory
representation `MachMem` and address type `Addr`.

`ownSubPlace mem addr path owner perm v` states that `mem` holds `v` at
`addr` and `path`, that the sub-place belongs to loan `owner`, and that `perm`
is the borrow state of that sub-place itself, relative to the sub-place (the
bound loan's own permission when no child borrow overrides it, or the child
borrows' permission otherwise). -/
structure SpatialModel (Val MachMem Addr : Type) where
  ownSubPlace : MachMem → Addr → SubPath → LoanId → PermTree → Val → Prop
  frameHolds : (MachMem → Prop) → MachMem → Prop
  disjointSubPlaces : Addr → SubPath → Addr → SubPath → Prop

/-- Constructive finite-step operational adapter connecting `PureLift` symbolic
evaluation to an arbitrary operational machine `Mach`. `ExecutesTo m k m'`
says that `m'` is reachable from `m` in `k` steps; for a nondeterministic
machine it holds for each reachable state, so statements built from it (such
as `pure_lift_sound`) assert that some run is good, not that all runs are. -/
structure OperationalAdapter (Mach Val : Type) where
  ExecutesTo : Mach → Nat → Mach → Prop
  StateRel : SymState Val → Mach → Prop
  FinalLoansRel : FuncOut Val → Mach → Prop
  exec_zero : ∀ m, ExecutesTo m 0 m
  exec_trans : ∀ {m1 m2 m3 k1 k2},
    ExecutesTo m1 k1 m2 → ExecutesTo m2 k2 m3 → ExecutesTo m1 (k1 + k2) m3

/-- Adequacy theorem (`pure_lift_sound`): if `initFnState alg params` produces
an initial symbolic state `st0` related to `m0` via `ad.StateRel st0 m0`
(`hInit`), `evalFnValue alg params plan retExpr` satisfies
`HoldsFnSpec ... post` (`hSpec`), and the machine simulates the evaluation from
`(st0, m0)` (`hSim`), then `m0` reaches a terminal machine state `mFinal` in
`k` steps satisfying `FinalLoansRel out mFinal` and `post out`.

The theorem transfers `post` from the lifted result to the machine; it does
not derive the machine run. `hSim` and `hInit` are assumptions, and each
adapter instance must discharge them for its own machine.

The conclusion is existential: some run from `m0` reaches a good final state.
For a deterministic machine this is the run. For a nondeterministic one, such
as an `M2` machine whose step offers a `.choice`, `hSim` need exhibit only one
run, and the theorem says nothing about the other runs the machine may take.
A claim about every run would need a universal simulation obligation instead.
The `M2` instances in this suite are deterministic. -/
theorem pure_lift_sound {Mach Val : Type}
    (ad : OperationalAdapter Mach Val)
    (alg : ValAlgebra Val)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (m0 : Mach)
    (hInit : Exists fun st0 =>
      initFnState alg params = .ok st0 ∧ ad.StateRel st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue alg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState alg params = .ok st0 →
      ad.StateRel st0 m0 →
      evalFnValue alg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        ad.ExecutesTo m0 k mFinal ∧ ad.FinalLoansRel out mFinal) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      ad.ExecutesTo m0 k mFinal ∧
      ad.FinalLoansRel out mFinal ∧
      post out := by
  cases hInit with
  | intro st0 hInitPair =>
    cases hEval : evalFnValue alg params plan retExpr with
    | fail =>
      rw [hEval] at hSpec
      nomatch hSpec
    | ok out =>
      have hStep := hSim st0 out hInitPair.1 hInitPair.2 hEval
      rw [hEval] at hSpec
      dsimp [HoldsFnSpec] at hSpec
      cases hStep with
      | intro k hk =>
        cases hk with
        | intro mFinal hm =>
          exact ⟨k, ⟨mFinal, ⟨out, hm.1, hm.2, hSpec⟩⟩⟩

/-- Style 1: Total step-function outcome (`.next`, `.ret`, `.fault`). -/
inductive M1StepResult (State Val : Type) where
  | next (s' : State)
  | ret (out : FuncOut Val)
  | fault

inductive M1MachState (State Val : Type) where
  | running (s : State)
  | returned (out : FuncOut Val)
  | faulted

def m1StepMach {State Val : Type}
    (step : State → M1StepResult State Val) :
    M1MachState State Val → M1MachState State Val
  | .running s =>
    match step s with
    | .next s' => .running s'
    | .ret out => .returned out
    | .fault => .faulted
  | .returned out => .returned out
  | .faulted => .faulted

def m1RunN {State Val : Type} (step : State → M1StepResult State Val)
    (k : Nat) (m : M1MachState State Val) : M1MachState State Val :=
  @Nat.recCompiled (fun _ => M1MachState State Val → M1MachState State Val)
    (fun m0 => m0)
    (fun _ ih m0 => ih (m1StepMach step m0))
    k m

theorem m1RunN_succ {State Val : Type}
    (step : State → M1StepResult State Val)
    (k : Nat) (m : M1MachState State Val) :
    m1RunN step (k + 1) m = m1RunN step k (m1StepMach step m) := rfl

theorem m1RunN_add {State Val : Type}
    (step : State → M1StepResult State Val)
    (k1 k2 : Nat) (m : M1MachState State Val) :
    m1RunN step (k1 + k2) m = m1RunN step k2 (m1RunN step k1 m) := by
  induction k1 generalizing m with
  | zero =>
    have hZ : 0 + k2 = k2 := Nat.zero_add k2
    rw [hZ]
    rfl
  | succ k1' ih =>
    have hS : (k1' + 1) + k2 = (k1' + k2) + 1 := Nat.succ_add k1' k2
    rw [hS]
    rw [m1RunN_succ, m1RunN_succ]
    exact ih (m1StepMach step m)

/-- Operational adapter for total step-function machines (`M1StepResult`). -/
def m1OperationalAdapter {State Val : Type}
    (step : State → M1StepResult State Val)
    (stateRel : SymState Val → State → Prop) :
    OperationalAdapter (M1MachState State Val) Val where
  ExecutesTo m1 k m2 := m1RunN step k m1 = m2
  StateRel st m :=
    match m with
    | .running s => stateRel st s
    | _ => False
  FinalLoansRel out m := m = .returned out
  exec_zero _ := rfl
  exec_trans h1 h2 := by
    rw [m1RunN_add]
    rw [h1]
    exact h2

/-- Style 2: Relational small-step transition with observable trace events and
nondeterministic choice (`M2StepResult`). -/
inductive M2StepResult (State Obs Val : Type) where
  | step (ev : List Obs) (s' : State)
  | choice (nexts : State → Prop)
  | terminated (out : FuncOut Val)
  | failed

structure M2Config (State Obs Val : Type) where
  state : State
  trace : List Obs
  terminal : Option (FuncOut Val)

inductive M2ExecutesTo {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val) :
    M2Config State Obs Val → Nat → M2Config State Obs Val → Prop where
  | refl (c : M2Config State Obs Val) :
      M2ExecutesTo step c 0 c
  | trans {c1 c2 c3 : M2Config State Obs Val} {k1 k2 : Nat} :
      M2ExecutesTo step c1 k1 c2 →
      M2ExecutesTo step c2 k2 c3 →
      M2ExecutesTo step c1 (k1 + k2) c3
  | step_emit {s s' : State} {tr ev : List Obs} :
      step s = .step ev s' →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s', tr ++ ev, none⟩
  | step_choice {s s' : State} {tr : List Obs} {nexts : State → Prop} :
      step s = .choice nexts →
      nexts s' →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s', tr, none⟩
  | step_term {s : State} {tr : List Obs} {out : FuncOut Val} :
      step s = .terminated out →
      M2ExecutesTo step ⟨s, tr, none⟩ 1 ⟨s, tr, some out⟩

def M2ProductiveOn {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val) (s : State) : Prop :=
  match step s with
  | .failed => False
  | .choice nexts => Exists fun s' => nexts s'
  | _ => True

/-- Operational adapter for trace-emitting relational small-step machines
(`M2StepResult`). -/
def m2OperationalAdapter {State Obs Val : Type}
    (step : State → M2StepResult State Obs Val)
    (stateRel : SymState Val → State → Prop) :
    OperationalAdapter (M2Config State Obs Val) Val where
  ExecutesTo := M2ExecutesTo step
  StateRel st c :=
    c.terminal = none ∧ stateRel st c.state ∧ M2ProductiveOn step c.state
  FinalLoansRel out c := c.terminal = some out
  exec_zero := M2ExecutesTo.refl
  exec_trans := M2ExecutesTo.trans

/-- Style 3: Allocation/offset heap (`AllocId × Offset`) with Tree Borrows
permission tags (`TbPerm`). -/
abbrev AllocId := Nat
abbrev Offset := Nat
abbrev TbTag := Nat

inductive TbPerm where
  | reserved
  | activeUnique
  | frozen
  | disabled

structure M3Cell (Val : Type) where
  allocId : AllocId
  offset : Offset
  subPath : SubPath := []
  tag : TbTag
  perm : TbPerm
  cellVal : CellVal Val

structure M3Mach (Val : Type) where
  heap : List (M3Cell Val)
  retOut : Option (FuncOut Val)

/-- True iff neither `p1` nor `p2` is a prefix of the other, witnessing
non-overlapping sub-place paths within the same allocation slot. -/
def subPathDisjoint (p1 p2 : SubPath) : Bool :=
  listFold
    (fun _ => false)
    (fun x _ ih ys =>
      match ys with
      | [] => false
      | y :: ys' => if x == y then ih ys' else true)
    p1 p2

/-- Look up the unique `M3Cell` at `(aid, off, path)` in `cells`, returning
`none` if no cell matches, if multiple cells share `(aid, off, path)`, or if
another cell at `(aid, off)` has a prefix-overlapping sub-path
(`!subPathDisjoint c.subPath path`). -/
def m3LookupCell {Val : Type} (aid : AllocId) (off : Offset) (path : SubPath)
    (cells : List (M3Cell Val)) : Option (M3Cell Val) :=
  match
    cells.foldr
      (fun c (acc : Bool × Option (M3Cell Val)) =>
        match acc with
        | (dup, foundOpt) =>
          if c.allocId == aid && c.offset == off then
            if subPathEq c.subPath path then
              match foundOpt with
              | some _ => (true, foundOpt)
              | none => (dup, some c)
            else if !subPathDisjoint c.subPath path then
              (true, foundOpt)
            else
              (dup, foundOpt)
          else
            (dup, foundOpt))
      (false, none)
  with
  | (false, some found) => some found
  | _ => none

/-- Spatial ownership model interpreting `PermTree` permissions as Tree Borrows
`TbPerm` states at `(AllocId × Offset)` locations and sub-paths. The cell at
`(addr, path)` is checked against the root of `perm` (normalized by
`getPathPerm []`), which describes that cell; `path` locates the cell and is
not applied to `perm` again. The cell's tag must match the loan ID(s) that
hold the cell. Where no loan in `perm` names the cell itself (`.unborrowed`,
or `.split` when child borrows cover only strict sub-places), the cell must
carry the tag of the owning loan `owner` with a unique permission. The model
does not see the owner's phase: callers pass a shared owner's place as
`.shared` (`effectiveBoundLoanPerm`), which requires a frozen cell. -/
def m3SpatialModel (Val : Type) :
    SpatialModel Val (List (M3Cell Val)) (AllocId × Offset) where
  ownSubPlace heap addr path owner perm v :=
    match m3LookupCell addr.1 addr.2 path heap with
    | some c =>
      c.cellVal = .init v ∧
      match getPathPerm [] perm with
      | .unborrowed => c.tag = owner ∧ c.perm = .activeUnique
      | .mutLocked lid =>
        c.tag = lid ∧ (c.perm = .activeUnique ∨ c.perm = .reserved)
      | .mutJoined mLids sLids =>
        -- A mutable joined loan witnesses a unique Tree Borrows permission;
        -- a shared joined loan witnesses a frozen one.
        (elemLoanId c.tag mLids = true ∧
          (c.perm = .activeUnique ∨ c.perm = .reserved)) ∨
        (elemLoanId c.tag sLids = true ∧ c.perm = .frozen)
      | .shared lids =>
        elemLoanId c.tag lids = true ∧ c.perm = .frozen
      | .split _ => c.tag = owner ∧ c.perm = .activeUnique
    | none => False
  frameHolds frame heap := frame heap
  disjointSubPlaces a1 p1 a2 p2 := a1 ≠ a2 ∨ subPathDisjoint p1 p2 = true

/-- Pairwise disjointness across a list of `(LoanId × Addr × SubPath)` spatial
loan bindings under `sp.disjointSubPlaces`. -/
def spatialBindingsDisjoint {Val MachMem Addr : Type}
    (sp : SpatialModel Val MachMem Addr)
    (bindings : List (LoanId × Addr × SubPath)) : Prop :=
  listFold True
    (fun head rest ih =>
      match head with
      | (_, addr, path) =>
        (listFold True
          (fun entry _ ihInner =>
            match entry with
            | (_, addr2, path2) =>
              sp.disjointSubPlaces addr path addr2 path2 ∧ ihInner)
          rest) ∧
        ih)
    bindings

/-- Effective `PermTree` of the place bound to active loan `lid` in `phase`,
whose child-borrow permission tree (relative to the loan's own value) is
`cellPerm`. When no child borrow holds the whole place (`getPathPerm []
cellPerm` is `.unborrowed`), the place is owned by `lid` itself (`.mutLocked
lid` for `.activeMut`, `.shared [lid]` for `.activeShared`). A place under an
`.activeShared` loan whose child borrows cover only strict sub-places
(`.split`) is still shared as a whole, so it is also `.shared [lid]`:
`m3SpatialModel` then requires a frozen cell, not the unique one it requires
for `.split`. -/
def effectiveBoundLoanPerm {Val : Type} (lid : LoanId) (phase : LoanPhase Val)
    (cellPerm : PermTree) : PermTree :=
  match getPathPerm [] cellPerm with
  | .unborrowed =>
    match phase with
    | .activeMut => .mutLocked lid
    | .activeShared => .shared [lid]
    | _ => cellPerm
  | .split children =>
    match phase with
    | .activeShared => .shared [lid]
    | _ => .split children
  | _ => cellPerm

/-- Spatial loan-ownership invariant connecting symbolic loans in `st.loans` to
concrete memory `mem` via `sp.ownSubPlace` (using `effectiveBoundLoanPerm` so
unborrowed loan cells remain tied to their own `lid` and `phase`) and
`spatialBindingsDisjoint`. -/
def spatialBindingsHold {Val MachMem Addr : Type}
    (sp : SpatialModel Val MachMem Addr)
    (bindings : List (LoanId × Addr × SubPath))
    (st : SymState Val) (mem : MachMem) : Prop :=
  spatialBindingsDisjoint sp bindings ∧
  listFold True
    (fun entry _ ih =>
      match entry with
      | (lid, addr, path) =>
        (match findLoan lid st.loans with
         | some e =>
           e.phase.isActive = true ∧
           sp.ownSubPlace mem addr path lid
             (effectiveBoundLoanPerm lid e.phase e.cell.perm) e.cell.val
         | none => False) ∧ ih)
    bindings

/-- Final spatial ownership relation pairing each root mutable parameter
`(lid, addr, path)` in `rootAddrs` with the corresponding output value in
`out.mutFinals`. The final cell must still be owned under root loan `lid`
(`.mutLocked lid`, which requires the cell's tag to equal `lid`), matching how
`spatialBindingsHold` ties an unborrowed root loan to its own tag at entry, so
the caller's original mutable reference remains usable after the call. -/
def spatialFinalBindingsHold {Val MachMem Addr : Type}
    (sp : SpatialModel Val MachMem Addr)
    (rootAddrs : List (LoanId × Addr × SubPath))
    (out : FuncOut Val) (mem : MachMem) : Prop :=
  listFold
    (fun vals => vals = [])
    (fun entry _ ih vals =>
      match entry, vals with
      | (lid, addr, path), vFinal :: restVals =>
        sp.ownSubPlace mem addr path lid (.mutLocked lid) vFinal ∧ ih restVals
      | _, [] => False)
    rootAddrs out.mutFinals

inductive M3ExecutesTo {Val : Type}
    (step : List (M3Cell Val) → M1StepResult (List (M3Cell Val)) Val) :
    M3Mach Val → Nat → M3Mach Val → Prop where
  | refl (m : M3Mach Val) : M3ExecutesTo step m 0 m
  | trans {m1 m2 m3 : M3Mach Val} {k1 k2 : Nat} :
      M3ExecutesTo step m1 k1 m2 → M3ExecutesTo step m2 k2 m3 →
      M3ExecutesTo step m1 (k1 + k2) m3
  | step_heap {heap heap' : List (M3Cell Val)} :
      step heap = .next heap' →
      M3ExecutesTo step ⟨heap, none⟩ 1 ⟨heap', none⟩
  | step_ret {heap : List (M3Cell Val)} {out : FuncOut Val} :
      step heap = .ret out →
      M3ExecutesTo step ⟨heap, none⟩ 1 ⟨heap, some out⟩

/-- Operational adapter for allocation/tag-tree machines (`M3Mach`) driven by a
heap step function `step`, spatial loan-address bindings `bindings`, root
mutable output addresses `rootAddrs`, and auxiliary state relation `stateRel`.
-/
def m3OperationalAdapter {Val : Type}
    (step : List (M3Cell Val) → M1StepResult (List (M3Cell Val)) Val)
    (stateRel : SymState Val → List (M3Cell Val) → Prop)
    (bindings : List (LoanId × (AllocId × Offset) × SubPath) := [])
    (rootAddrs : List (LoanId × (AllocId × Offset) × SubPath) := []) :
    OperationalAdapter (M3Mach Val) Val where
  ExecutesTo := M3ExecutesTo step
  StateRel st m :=
    m.retOut = none ∧
    spatialBindingsHold (m3SpatialModel Val) bindings st m.heap ∧
    stateRel st m.heap
  FinalLoansRel out m :=
    m.retOut = some out ∧
    spatialFinalBindingsHold (m3SpatialModel Val) rootAddrs out m.heap
  exec_zero := M3ExecutesTo.refl
  exec_trans := M3ExecutesTo.trans

/-- Spatial adequacy theorem (`pure_lift_spatial_sound`): specializes
`pure_lift_sound` to `m3OperationalAdapter`. The initial `m3SpatialModel`
sub-place ownership (`spatialBindingsHold`) and disjointness are part of the
assumed initial relation `hInit`, and final root mutable sub-place ownership
(`spatialFinalBindingsHold`) in the terminal heap `mFinal.heap` is part of the
assumed simulation `hSim`; the theorem exposes both in its conclusion but
derives neither, and each instance must discharge them. -/
theorem pure_lift_spatial_sound {Val : Type}
    (step : List (M3Cell Val) → M1StepResult (List (M3Cell Val)) Val)
    (stateRel : SymState Val → List (M3Cell Val) → Prop)
    (bindings : List (LoanId × (AllocId × Offset) × SubPath))
    (rootAddrs : List (LoanId × (AllocId × Offset) × SubPath))
    (alg : ValAlgebra Val)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (m0 : M3Mach Val)
    (hInit : Exists fun st0 =>
      initFnState alg params = .ok st0 ∧
      (m3OperationalAdapter step stateRel bindings rootAddrs).StateRel st0 m0)
    (hSpec : HoldsFnSpec (evalFnValue alg params plan retExpr) post)
    (hSim : ∀ st0 out,
      initFnState alg params = .ok st0 →
      (m3OperationalAdapter step stateRel bindings rootAddrs).StateRel st0 m0 →
      evalFnValue alg params plan retExpr = .ok out →
      Exists fun k => Exists fun mFinal =>
        M3ExecutesTo step m0 k mFinal ∧
        (m3OperationalAdapter step stateRel bindings rootAddrs).FinalLoansRel
          out mFinal) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      M3ExecutesTo step m0 k mFinal ∧
      mFinal.retOut = some out ∧
      spatialFinalBindingsHold (m3SpatialModel Val) rootAddrs out mFinal.heap ∧
      post out := by
  have hBase :=
    pure_lift_sound
      (m3OperationalAdapter step stateRel bindings rootAddrs)
      alg params plan retExpr post m0 hInit hSpec hSim
  cases hBase with
  | intro k hk =>
    cases hk with
    | intro mFinal hm =>
      cases hm with
      | intro out hOut =>
        exact ⟨k, ⟨mFinal, ⟨out, hOut.1, hOut.2.1.1, hOut.2.1.2, hOut.2.2⟩⟩⟩

/-!
## Kernel-Checked Unit Tests for `Adapter`
-/

/-- Unit tests for `m1StepMach`, `m1RunN`, `M2ProductiveOn`,
`subPathDisjoint`, `m3LookupCell`, and `m3SpatialModel.ownSubPlace` across all
`PermTree` constructors, including the owning-loan tag check for `.unborrowed`
and `.split` cells. -/
theorem adapter_styles_and_m3SpatialModel_tests :
    let stepM1 (s : Nat) : M1StepResult Nat LensTestVal :=
      match s with
      | 0 => .next 1
      | 1 => .ret ⟨.atom 42, []⟩
      | _ => .fault
    let stepM2 (s : Nat) : M2StepResult Nat Nat LensTestVal :=
      match s with
      | 0 => .step [10] 1
      | 1 => .terminated ⟨.atom 42, []⟩
      | _ => .failed
    let sp := m3SpatialModel LensTestVal
    let heap : List (M3Cell LensTestVal) :=
      [ ⟨0, 0, [], 1, .activeUnique, .init (.atom 10)⟩
      , ⟨0, 1, [0], 2, .reserved, .init (.atom 20)⟩
      , ⟨0, 2, [1], 3, .frozen, .init (.atom 30)⟩ ]
    m1RunN stepM1 0 (.running 0) = .running 0 ∧
    m1RunN stepM1 1 (.running 0) = .running 1 ∧
    m1RunN stepM1 2 (.running 0) = .returned ⟨.atom 42, []⟩ ∧
    m1RunN stepM1 3 (.running 0) = .returned ⟨.atom 42, []⟩ ∧
    m1RunN stepM1 1 (.running 99) = .faulted ∧
    m1RunN stepM1 2 (.running 99) = .faulted ∧
    M2ProductiveOn stepM2 0 ∧
    M2ProductiveOn stepM2 1 ∧
    ¬ M2ProductiveOn stepM2 99 ∧
    subPathDisjoint [] [0] = false ∧
    subPathDisjoint [0, 1] [0, 2] = true ∧
    sp.ownSubPlace heap (0, 0) [] 1 .unborrowed (.atom 10) ∧
    sp.ownSubPlace heap (0, 1) [0] 0 (.mutLocked 2) (.atom 20) ∧
    sp.ownSubPlace heap (0, 1) [0] 0 (.mutJoined [2] [9]) (.atom 20) ∧
    sp.ownSubPlace heap (0, 2) [1] 0 (.shared [3]) (.atom 30) ∧
    -- A shared loan in `.mutJoined` witnesses a frozen cell, not a reserved
    -- (mutable) one:
    sp.ownSubPlace heap (0, 2) [1] 0 (.mutJoined [7] [3]) (.atom 30) ∧
    ¬ sp.ownSubPlace heap (0, 1) [0] 0 (.mutJoined [7] [2]) (.atom 20) ∧
    ¬ sp.ownSubPlace heap (0, 2) [1] 0 (.mutJoined [3] [7]) (.atom 30) ∧
    ¬ sp.ownSubPlace heap (9, 9) [] 1 .unborrowed (.atom 10) ∧
    -- A cell whose child borrows cover only strict sub-places (`.split`) or
    -- that no loan borrows (`.unborrowed`) must carry the owning loan's tag:
    sp.ownSubPlace heap (0, 0) [] 1 (.split [([0], .mutLocked 2)]) (.atom 10) ∧
    ¬ sp.ownSubPlace heap (0, 0) [] 5 (.split [([0], .mutLocked 2)])
      (.atom 10) ∧
    ¬ sp.ownSubPlace heap (0, 0) [] 5 .unborrowed (.atom 10) ∧
    m3LookupCell 0 0 [] (heap ++ heap) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial, trivial,
    fun h => h, rfl, rfl, ⟨rfl, ⟨rfl, rfl⟩⟩, ⟨rfl, ⟨rfl, Or.inr rfl⟩⟩,
    ⟨rfl, Or.inl ⟨rfl, Or.inr rfl⟩⟩, ⟨rfl, ⟨rfl, rfl⟩⟩,
    ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩,
    (by
      intro h
      cases h with
      | intro _ hRest =>
        cases hRest with
        | inl hm => cases hm.1
        | inr hs => cases hs.2),
    (by
      intro h
      cases h with
      | intro _ hRest =>
        cases hRest with
        | inl hm =>
          cases hm.2 with
          | inl hu => cases hu
          | inr hr => cases hr
        | inr hs => cases hs.1),
    fun h => h,
    ⟨rfl, ⟨rfl, rfl⟩⟩,
    (fun h => nomatch h.2.1),
    (fun h => nomatch h.2.1),
    rfl⟩

/-- A place under an `.activeShared` loan whose child borrows cover only strict
sub-places (`.split`) is shared as a whole: `effectiveBoundLoanPerm` maps it to
`.shared [lid]`, so `m3SpatialModel` accepts a frozen cell and rejects a
unique one. Under an `.activeMut` loan the `.split` permission is kept. -/
theorem effectiveBoundLoanPerm_shared_split_tests :
    let split : PermTree := .split [([0], .mutLocked 4)]
    let cell (perm : TbPerm) : List (M3Cell LensTestVal) :=
      [⟨0, 0, [], 3, perm, .init (.atom 1)⟩]
    let sharedPerm :=
      effectiveBoundLoanPerm 3 (LoanPhase.activeShared (Val := LensTestVal))
        split
    effectiveBoundLoanPerm 3 (LoanPhase.activeShared (Val := LensTestVal))
      split = .shared [3] ∧
    effectiveBoundLoanPerm 3 (LoanPhase.activeMut (Val := LensTestVal))
      split = split ∧
    (m3SpatialModel LensTestVal).ownSubPlace (cell .frozen) (0, 0) [] 3
      sharedPerm (.atom 1) ∧
    ¬ (m3SpatialModel LensTestVal).ownSubPlace (cell .activeUnique) (0, 0) []
      3 sharedPerm (.atom 1) :=
  ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, fun h => nomatch h.2.2⟩

end Anneal.PureLift
