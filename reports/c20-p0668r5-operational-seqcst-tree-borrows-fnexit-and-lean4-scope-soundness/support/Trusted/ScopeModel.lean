-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:memory

prelude
import Init.Data.Nat.Basic
import Init.NotationExtra

namespace Trusted

inductive MemOrdering where
  | relaxed
  | release
  | acquire
  | acqRel
  | seqCst

inductive ChildSchedule where
  | child1First
  | child2First

abbrev Tid := Nat
abbrev FuncId := Nat
abbrev MemView := Tid → Nat

def viewBot : MemView :=
  fun _ => 0

def viewJoin (v1 v2 : MemView) : MemView :=
  fun t => if v1 t ≤ v2 t then v2 t else v1 t

def viewBump (v : MemView) (t : Tid) (epoch : Nat) : MemView :=
  fun q => if q == t then (if v q ≤ epoch then epoch else v q) else v q

def viewLe3 (req cur : MemView) : Bool :=
  decide (req 0 ≤ cur 0) && decide (req 1 ≤ cur 1) && decide (req 2 ≤ cur 2)

structure NaCell where
  val : Nat
  writeTid : Tid
  writeEpoch : Nat
  readEpochs : MemView

structure AtomicCount where
  count : Nat
  relView : MemView

structure ScopeMachine where
  clocks : Tid → MemView
  cellA : NaCell
  cellX : NaCell
  running : AtomicCount

def tickThread (m : ScopeMachine) (t : Tid) : ScopeMachine :=
  let c := m.clocks t
  let next := c t + 1
  { m with clocks := fun q => if q == t then viewBump c t next else m.clocks q }

def readCellA (m : ScopeMachine) (t : Tid) : Option (Nat × ScopeMachine) :=
  let tc := m.clocks t
  if decide (m.cellA.writeEpoch ≤ tc m.cellA.writeTid) then
    let c' : NaCell := { m.cellA with readEpochs := viewBump m.cellA.readEpochs t (tc t) }
    some (m.cellA.val, { m with cellA := c' })
  else
    none

def writeCellA (m : ScopeMachine) (t : Tid) (v : Nat) : Option ScopeMachine :=
  let tc := m.clocks t
  if decide (m.cellA.writeEpoch ≤ tc m.cellA.writeTid) && viewLe3 m.cellA.readEpochs tc then
    let c' : NaCell := {
      val := v
      writeTid := t
      writeEpoch := tc t
      readEpochs := viewBot
    }
    some (tickThread { m with cellA := c' } t)
  else
    none

def readCellX (m : ScopeMachine) (t : Tid) : Option (Nat × ScopeMachine) :=
  let tc := m.clocks t
  if decide (m.cellX.writeEpoch ≤ tc m.cellX.writeTid) then
    let c' : NaCell := { m.cellX with readEpochs := viewBump m.cellX.readEpochs t (tc t) }
    some (m.cellX.val, { m with cellX := c' })
  else
    none

def writeCellX (m : ScopeMachine) (t : Tid) (v : Nat) : Option ScopeMachine :=
  let tc := m.clocks t
  if decide (m.cellX.writeEpoch ≤ tc m.cellX.writeTid) && viewLe3 m.cellX.readEpochs tc then
    let c' : NaCell := {
      val := v
      writeTid := t
      writeEpoch := tc t
      readEpochs := viewBot
    }
    some (tickThread { m with cellX := c' } t)
  else
    none

def packetDropFetchSub (m : ScopeMachine) (t : Tid) (dropOrd : MemOrdering) : ScopeMachine :=
  let tc := m.clocks t
  let newRel :=
    match dropOrd with
    | .release | .acqRel | .seqCst => viewJoin m.running.relView tc
    | .relaxed | .acquire => m.running.relView
  let m' := { m with running := { count := m.running.count - 1, relView := newRel } }
  tickThread m' t

def scopeWaitAcquireZero (m : ScopeMachine) (t : Tid) : Option ScopeMachine :=
  if m.running.count == 0 then
    let joined := viewJoin (m.clocks t) m.running.relView
    some (tickThread { m with clocks := fun q => if q == t then joined else m.clocks q } t)
  else
    none

def initScopeMachine : ScopeMachine :=
  let c0 : MemView := fun t => if t == 0 then 2 else 0
  let c1 : MemView := fun t => if t == 0 then 2 else if t == 1 then 1 else 0
  let c2 : MemView := fun t => if t == 0 then 2 else if t == 2 then 1 else 0
  {
    clocks := fun t => if t == 0 then c0 else if t == 1 then c1 else if t == 2 then c2 else viewBot
    cellA := { val := 10, writeTid := 0, writeEpoch := 1, readEpochs := viewBot }
    cellX := { val := 5,  writeTid := 0, writeEpoch := 1, readEpochs := viewBot }
    running := { count := 2, relView := viewBot }
  }

def runChild1 (m : ScopeMachine) (dropOrd : MemOrdering) : Option ScopeMachine :=
  match readCellA m 1 with
  | none => none
  | some (_, m1) => some (packetDropFetchSub m1 1 dropOrd)

def runChild2 (m : ScopeMachine) (dropOrd : MemOrdering) : Option ScopeMachine :=
  match readCellA m 2 with
  | none => none
  | some (aVal, m1) =>
    match readCellX m1 2 with
    | none => none
    | some (xVal, m2) =>
      match writeCellX m2 2 (xVal + aVal) with
      | none => none
      | some m3 => some (packetDropFetchSub m3 2 dropOrd)

def runScopeExecution (dropOrd : MemOrdering) (sched : ChildSchedule) : Option Nat :=
  let m0 := initScopeMachine
  let afterChildren :=
    match sched with
    | .child1First =>
      match runChild1 m0 dropOrd with
      | none => none
      | some m1 => runChild2 m1 dropOrd
    | .child2First =>
      match runChild2 m0 dropOrd with
      | none => none
      | some m1 => runChild1 m1 dropOrd
  match afterChildren with
  | none => none
  | some mJoined =>
    match scopeWaitAcquireZero mJoined 0 with
    | none => none
    | some mParent =>
      match writeCellA mParent 0 31 with
      | none => none
      | some mParent2 =>
        match readCellX mParent2 0 with
        | none => none
        | some (xFinal, _) => some (31 + xFinal)

def ScopeSoundClaim : Prop :=
  ∀ sched : ChildSchedule, runScopeExecution MemOrdering.release sched = some 46

def ScopeRelaxedDropUnsoundClaim : Prop :=
  ∀ sched : ChildSchedule, runScopeExecution MemOrdering.relaxed sched = none

end Trusted
