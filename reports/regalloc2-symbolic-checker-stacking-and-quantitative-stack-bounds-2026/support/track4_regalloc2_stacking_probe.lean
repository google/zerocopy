/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Track 4 Mechanization: `regalloc2` Symbolic Checker, `Stacking`, and Guard-Page Probing

This standalone Lean 4.34.1 module mechanizes the core verification pipeline
studied in Track 4 of Round 1:

1. **Multi-Block Virtual-Register IR (`AnVReg`) and Physical Machine (`AnMach`):**
   Formalizes a multi-block CFG with unbounded virtual registers (`VReg`) and
   abstract local slots (`LocalSlot`), an intermediate register-allocated IR
   (`AnAlloc`) with bounded physical registers (`PReg`), spill slots
   (`SpillSlot`), and `regalloc2`-style `EditMove` sequences, and a concrete
   stack-frame machine (`AnMach`) operating over bounded `PReg`, hardware stack
   pointer `sp`, and a flat stack memory bounded by `[stackLimit, stackBase)`.

2. **`regalloc2`-Style Forward Symbolic Dataflow Checker (`checkRegAlloc`):**
   Implements a computable forward symbolic checker tracking active
   `(Allocation, VReg)` equivalences across `EditMove` spills, reloads, and
   register-to-register moves, instruction definitions/uses, clobbers, and
   multi-predecessor CFG joins. Fixes the untracked-source move bug identified
   in `regalloc2` (`src/checker.rs:554-562`) by unconditionally killing the
   destination allocation before propagating any source `VReg`s. Proves
   `checkRegAlloc_sound`, establishing forward simulation and `Refines` over
   arbitrary multi-block CFGs.

3. **`Stacking` Pass, Frame-Size Certificates (`A-BEH-07`), and `-mno-red-zone`:**
   Lowers `LocalSlot`s, `SpillSlot`s, and callee-saved register slots into
   contiguous, pairwise-disjoint offsets inside `[sp, sp + frameSize)` and
   emits the static Frame-Size Certificate `frameSizeCert`. Proves:
   - `stacking_sound` and `regalloc_and_stacking_sound`: end-to-end refinement
     from `AnVReg` to `AnMach` on flat stack memory.
   - `callChain_no_stackOverflow`: any call chain whose static frame-size
     certificates sum to at most `stackBase - stackLimit` never transitions to
     `.failed .stackOverflow` (`A-BEH-07`).
   - `no_red_zone_writeMachLoc` and `interrupt_preserves_active_frames`: all
     frame writes lie in `[sp, sp + frameSize)`, so asynchronous interrupts
     clobbering memory below `sp` preserve all active stack frames.
   - `probe_step_bounded`: periodic stack probing at stride `guardPageSize`
     never advances the lowest probed address by more than `guardPageSize`.

4. **Four Negative Adequacy Canaries:**
   - **Canary 1:** Two live `VReg`s assigned to the same `PReg` rejected by
     `checkRegAlloc`.
   - **Canary 2:** Cyclic parallel move `x0 := x1; x1 := x0` lowered
     sequentially without a scratch register rejected by `checkRegAlloc` (and
     accepted when lowered with a scratch register `x2`).
   - **Canary 3:** CFG join mismatch where two predecessor blocks leave a live
     `VReg` in different physical registers without an edge move rejected by
     `checkRegAlloc` (and accepted when an edge move reconciles the join).
   - **Canary 4:** A function call whose frame size exceeds the remaining stack
     budget deterministically transitions to `.failed .stackOverflow`.
-/

namespace Anneal.Track4

/-! ## 1. Foundational Execution and Refinement Primitives -/

/-- Machine-level failure conditions relevant to register allocation and stack
lowering. -/
inductive FailureKind where
  | stackOverflow
  | outOfBoundsStackAccess
  | invalidControlFlow
  deriving DecidableEq, Repr

/-- Explicit outcome of a single small-step transition, mirroring
`Trusted.StepResult`. -/
inductive StepResult (State : Type) (Obs : Type) where
  | continue_ (next : State)
  | terminal (obs : Obs)
  | failed (err : FailureKind)
  | stuck
  deriving DecidableEq, Repr

/-- Small-step transition machine mirroring `Trusted.Refinement`. -/
structure Machine (State : Type) (Obs : Type) where
  step : State → StepResult State Obs

/-- Runs a `Machine` for `fuel` steps, returning the terminal observation or
failure if reached. -/
def evalSteps (m : Machine State Obs) : Nat → State → StepResult State Obs
  | 0, s => .continue_ s
  | fuel + 1, s =>
      match m.step s with
      | .continue_ s' => evalSteps m fuel s'
      | .terminal obs => .terminal obs
      | .failed err => .failed err
      | .stuck => .stuck

/-- Forward behavioral refinement: whenever the source machine takes a
non-stuck step, the target machine takes a matching step preserving `rel`. -/
def Refines (src : Machine SState Obs) (tgt : Machine TState Obs)
    (rel : SState → TState → Prop) : Prop :=
  ∀ s t, rel s t →
    match src.step s with
    | .continue_ s' => ∃ t', tgt.step t = .continue_ t' ∧ rel s' t'
    | .terminal obs => tgt.step t = .terminal obs
    | .failed err => tgt.step t = .failed err
    | .stuck => True

/-- Relational composition of two forward refinements (`m1 → m2` and `m2 → m3`). -/
theorem refines_trans {m1 : Machine S1 Obs} {m2 : Machine S2 Obs}
    {m3 : Machine S3 Obs} {r12 : S1 → S2 → Prop} {r23 : S2 → S3 → Prop}
    (h12 : Refines m1 m2 r12) (h23 : Refines m2 m3 r23) :
    Refines m1 m3 (fun s1 s3 => ∃ s2, r12 s1 s2 ∧ r23 s2 s3) := by
  intro s1 s3 ⟨s2, hRel12, hRel23⟩
  have hStep12 := h12 s1 s2 hRel12
  have hStep23 := h23 s2 s3 hRel23
  cases hSrc : m1.step s1 with
  | continue_ s1' =>
      rw [hSrc] at hStep12
      rcases hStep12 with ⟨s2', hM2, hRel12'⟩
      rw [hM2] at hStep23
      rcases hStep23 with ⟨s3', hM3, hRel23'⟩
      exact ⟨s3', hM3, s2', hRel12', hRel23'⟩
  | terminal obs =>
      rw [hSrc] at hStep12
      rw [hStep12] at hStep23
      exact hStep23
  | failed err =>
      rw [hSrc] at hStep12
      rw [hStep12] at hStep23
      exact hStep23
  | stuck =>
      trivial

/-- Single-step lockstep simulation implies multi-step behavioral refinement
across arbitrary fuel bounds. -/
theorem refines_evalSteps {src : Machine SState Obs} {tgt : Machine TState Obs}
    {rel : SState → TState → Prop} (hSim : Refines src tgt rel)
    (fuel : Nat) {s : SState} {t : TState} (hRel : rel s t) :
    match evalSteps src fuel s with
    | .continue_ s' => ∃ t', evalSteps tgt fuel t = .continue_ t' ∧ rel s' t'
    | .terminal obs => evalSteps tgt fuel t = .terminal obs
    | .failed err => evalSteps tgt fuel t = .failed err
    | .stuck => True := by
  induction fuel generalizing s t with
  | zero =>
      exact ⟨t, rfl, hRel⟩
  | succ n ih =>
      simp only [evalSteps]
      have hStep := hSim s t hRel
      cases hSrc : src.step s with
      | continue_ s' =>
          rw [hSrc] at hStep
          rcases hStep with ⟨t', hTgt, hRel'⟩
          rw [hTgt]
          exact ih hRel'
      | terminal obs =>
          rw [hSrc] at hStep
          rw [hStep]
      | failed err =>
          rw [hSrc] at hStep
          rw [hStep]
      | stuck =>
          trivial

/-! ## 2. Source Virtual-Register IR (`AnVReg`) and Allocated IR (`AnAlloc`) -/

/-- Virtual register identifier in `AnVReg`. -/
abbrev VReg := Nat

/-- Abstract function-local stack slot identifier in `AnVReg`. -/
abbrev LocalSlot := Nat

/-- Basic-block identifier in a function CFG. -/
abbrev BlockId := Nat

/-- Function identifier in a call graph. -/
abbrev FnId := Nat

/-- Physical machine register identifier. -/
structure PReg where
  idx : Nat
  deriving DecidableEq, Repr

/-- Spill slot identifier allocated by `regalloc2`. -/
abbrev SpillSlot := Nat

/-- Physical allocation assigned to a virtual register at a program point,
mirroring `regalloc2::Allocation` (`Reg(PReg)` or `Stack(SpillSlot)`). -/
inductive Allocation where
  | preg (r : PReg)
  | spill (s : SpillSlot)
  deriving DecidableEq, Repr

/-- Pure binary arithmetic operations shared across IR levels. -/
inductive BinOp where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Evaluates a binary arithmetic operation. -/
def evalBinOp (op : BinOp) (lhs rhs : Int) : Int :=
  match op with
  | .add => lhs + rhs
  | .sub => lhs - rhs
  | .mul => lhs * rhs

/-- Non-branching instruction in the virtual-register IR (`AnVReg`). -/
inductive VInst where
  | const (dst : VReg) (val : Int)
  | mov (dst src : VReg)
  | binop (op : BinOp) (dst lhs rhs : VReg)
  | loadLocal (dst : VReg) (slot : LocalSlot)
  | storeLocal (slot : LocalSlot) (src : VReg)
  deriving DecidableEq, Repr

/-- Block terminator in `AnVReg`. -/
inductive VTerm where
  | ret (src : VReg)
  | br (target : BlockId)
  | condBr (cond : VReg) (tTarget fTarget : BlockId)
  deriving DecidableEq, Repr

/-- Basic block in `AnVReg`. -/
structure VBlock where
  insts : List VInst
  term : VTerm
  deriving DecidableEq, Repr

/-- Multi-block CFG function in `AnVReg`. -/
structure VFunc where
  numLocals : Nat
  entry : BlockId
  blocks : List VBlock
  deriving DecidableEq, Repr

/-- State of an executing `AnVReg` function. -/
structure VState where
  block : BlockId
  vregs : VReg → Int
  locals : LocalSlot → Int

/-- Functional update of a virtual register map. -/
def updateVReg (vregs : VReg → Int) (v : VReg) (val : Int) : VReg → Int :=
  fun u => if u = v then val else vregs u

/-- Functional update of a local slot map. -/
def updateLocal (locals : LocalSlot → Int) (slot : LocalSlot) (val : Int) :
    LocalSlot → Int :=
  fun s => if s = slot then val else locals s

/-- Executes a single `VInst` on `(vregs, locals)`. -/
def execVInst (vregs : VReg → Int) (locals : LocalSlot → Int) (inst : VInst) :
    (VReg → Int) × (LocalSlot → Int) :=
  match inst with
  | .const dst val => (updateVReg vregs dst val, locals)
  | .mov dst src => (updateVReg vregs dst (vregs src), locals)
  | .binop op dst lhs rhs =>
      (updateVReg vregs dst (evalBinOp op (vregs lhs) (vregs rhs)), locals)
  | .loadLocal dst slot => (updateVReg vregs dst (locals slot), locals)
  | .storeLocal slot src => (vregs, updateLocal locals slot (vregs src))

/-- Executes a straight-line sequence of `VInst`s within a basic block. -/
def execVInsts (vregs : VReg → Int) (locals : LocalSlot → Int) :
    List VInst → (VReg → Int) × (LocalSlot → Int)
  | [] => (vregs, locals)
  | i :: is =>
      let (vregs', locals') := execVInst vregs locals i
      execVInsts vregs' locals' is

/-- Executes one basic-block step of a `VFunc` in `AnVReg`. -/
def stepVFunc (f : VFunc) (s : VState) : StepResult VState Int :=
  match f.blocks[s.block]? with
  | none => .stuck
  | some blk =>
      let (vregs', locals') := execVInsts s.vregs s.locals blk.insts
      match blk.term with
      | .ret src => .terminal (vregs' src)
      | .br target =>
          .continue_ { block := target, vregs := vregs', locals := locals' }
      | .condBr cond tTarget fTarget =>
          let nextBlk := if vregs' cond != 0 then tTarget else fTarget
          .continue_ { block := nextBlk, vregs := vregs', locals := locals' }

/-- Wraps a `VFunc` as a `Machine VState Int`. -/
def anVRegMachine (f : VFunc) : Machine VState Int where
  step := stepVFunc f

/-! ## 3. Register-Allocated IR (`AnAlloc`) with `EditMove` Sequences -/

/-- A single move edit (`into := from_`) inserted by `regalloc2` (`Edit::Move`)
to spill, reload, shuffle registers, or resolve parallel moves. -/
structure EditMove where
  into : Allocation
  from_ : Allocation
  deriving DecidableEq, Repr

/-- An instruction whose register operands have been replaced by physical
`Allocation`s, plus optional clobbered physical registers (`clobbers`). -/
inductive MInstOp where
  | const (dst : Allocation) (val : Int) (clobbers : List PReg := [])
  | mov (dst src : Allocation) (clobbers : List PReg := [])
  | binop (op : BinOp) (dst lhs rhs : Allocation) (clobbers : List PReg := [])
  | loadLocal (dst : Allocation) (slot : LocalSlot) (clobbers : List PReg := [])
  | storeLocal (slot : LocalSlot) (src : Allocation) (clobbers : List PReg := [])
  deriving DecidableEq, Repr

/-- An allocated instruction pairing preceding `regalloc2` `EditMove`s with the
allocated operation. -/
structure AllocatedInst where
  edits : List EditMove
  op : MInstOp
  deriving DecidableEq, Repr

/-- Allocated block terminator, supporting pre-terminator `edits` and per-edge
move lists (`tEdits`, `fEdits`) to reconcile CFG joins. -/
inductive MTermOp where
  | ret (edits : List EditMove) (src : Allocation)
  | br (edits : List EditMove) (target : BlockId)
  | condBr (edits : List EditMove) (cond : Allocation)
      (tEdits : List EditMove) (tTarget : BlockId)
      (fEdits : List EditMove) (fTarget : BlockId)
  deriving DecidableEq, Repr

/-- Basic block in `AnAlloc`. -/
structure AllocatedBlock where
  insts : List AllocatedInst
  term : MTermOp
  deriving DecidableEq, Repr

/-- Register-allocated function in `AnAlloc`. -/
structure AllocFunc where
  numPRegs : Nat
  numSpills : Nat
  numLocals : Nat
  numSavedRegs : Nat
  entry : BlockId
  blocks : List AllocatedBlock
  deriving DecidableEq, Repr

/-- State of an executing `AnAlloc` function prior to `Stacking`. -/
structure AllocState where
  block : BlockId
  pregs : PReg → Int
  spills : SpillSlot → Int
  locals : LocalSlot → Int

/-- Reads an `Allocation` from `(pregs, spills)`. -/
def readAlloc (pregs : PReg → Int) (spills : SpillSlot → Int)
    (a : Allocation) : Int :=
  match a with
  | .preg r => pregs r
  | .spill s => spills s

/-- Functional update of a physical register map. -/
def updatePReg (pregs : PReg → Int) (r : PReg) (val : Int) : PReg → Int :=
  fun r' => if r' = r then val else pregs r'

/-- Functional update of a spill slot map. -/
def updateSpill (spills : SpillSlot → Int) (s : SpillSlot) (val : Int) :
    SpillSlot → Int :=
  fun s' => if s' = s then val else spills s'

/-- Writes `val` to `a : Allocation` in `(pregs, spills)`. -/
def writeAlloc (pregs : PReg → Int) (spills : SpillSlot → Int)
    (a : Allocation) (val : Int) : (PReg → Int) × (SpillSlot → Int) :=
  match a with
  | .preg r => (updatePReg pregs r val, spills)
  | .spill s => (pregs, updateSpill spills s val)

/-- Zeroes clobbered physical registers to model arbitrary clobber effects. -/
def applyClobbers (pregs : PReg → Int) : List PReg → PReg → Int
  | [] => pregs
  | r :: rs => applyClobbers (updatePReg pregs r 0) rs

/-- Executes a single `EditMove` (`into := from_`). -/
def execEditMove (pregs : PReg → Int) (spills : SpillSlot → Int)
    (m : EditMove) : (PReg → Int) × (SpillSlot → Int) :=
  let val := readAlloc pregs spills m.from_
  writeAlloc pregs spills m.into val

/-- Executes a sequence of `EditMove`s sequentially in order. -/
def execEditMoves (pregs : PReg → Int) (spills : SpillSlot → Int) :
    List EditMove → (PReg → Int) × (SpillSlot → Int)
  | [] => (pregs, spills)
  | m :: ms =>
      let (pregs', spills') := execEditMove pregs spills m
      execEditMoves pregs' spills' ms

/-- Executes a single `MInstOp`. -/
def execMInstOp (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (op : MInstOp) :
    (PReg → Int) × (SpillSlot → Int) × (LocalSlot → Int) :=
  match op with
  | .const dst val clobbers =>
      let pregs1 := applyClobbers pregs clobbers
      let (pregs2, spills2) := writeAlloc pregs1 spills dst val
      (pregs2, spills2, locals)
  | .mov dst src clobbers =>
      let v := readAlloc pregs spills src
      let pregs1 := applyClobbers pregs clobbers
      let (pregs2, spills2) := writeAlloc pregs1 spills dst v
      (pregs2, spills2, locals)
  | .binop bop dst lhs rhs clobbers =>
      let vL := readAlloc pregs spills lhs
      let vR := readAlloc pregs spills rhs
      let pregs1 := applyClobbers pregs clobbers
      let (pregs2, spills2) := writeAlloc pregs1 spills dst (evalBinOp bop vL vR)
      (pregs2, spills2, locals)
  | .loadLocal dst slot clobbers =>
      let v := locals slot
      let pregs1 := applyClobbers pregs clobbers
      let (pregs2, spills2) := writeAlloc pregs1 spills dst v
      (pregs2, spills2, locals)
  | .storeLocal slot src clobbers =>
      let v := readAlloc pregs spills src
      let pregs1 := applyClobbers pregs clobbers
      (pregs1, spills, updateLocal locals slot v)

/-- Executes an `AllocatedInst` (`edits` followed by `op`). -/
def execAllocatedInst (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (ai : AllocatedInst) :
    (PReg → Int) × (SpillSlot → Int) × (LocalSlot → Int) :=
  let (pregs1, spills1) := execEditMoves pregs spills ai.edits
  execMInstOp pregs1 spills1 locals ai.op

/-- Executes a sequence of `AllocatedInst`s. -/
def execAllocatedInsts (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) :
    List AllocatedInst → (PReg → Int) × (SpillSlot → Int) × (LocalSlot → Int)
  | [] => (pregs, spills, locals)
  | ai :: ais =>
      let (pregs', spills', locals') := execAllocatedInst pregs spills locals ai
      execAllocatedInsts pregs' spills' locals' ais

/-- Executes one basic-block step of an `AllocFunc`. -/
def stepAllocFunc (af : AllocFunc) (s : AllocState) :
    StepResult AllocState Int :=
  match af.blocks[s.block]? with
  | none => .stuck
  | some ablk =>
      let (pregs1, spills1, locals1) :=
        execAllocatedInsts s.pregs s.spills s.locals ablk.insts
      match ablk.term with
      | .ret edits src =>
          let (pregs2, spills2) := execEditMoves pregs1 spills1 edits
          .terminal (readAlloc pregs2 spills2 src)
      | .br edits target =>
          let (pregs2, spills2) := execEditMoves pregs1 spills1 edits
          .continue_ {
            block := target
            pregs := pregs2
            spills := spills2
            locals := locals1
          }
      | .condBr edits cond tEdits tTarget fEdits fTarget =>
          let (pregs2, spills2) := execEditMoves pregs1 spills1 edits
          if readAlloc pregs2 spills2 cond != 0 then
            let (pregsT, spillsT) := execEditMoves pregs2 spills2 tEdits
            .continue_ {
              block := tTarget
              pregs := pregsT
              spills := spillsT
              locals := locals1
            }
          else
            let (pregsF, spillsF) := execEditMoves pregs2 spills2 fEdits
            .continue_ {
              block := fTarget
              pregs := pregsF
              spills := spillsF
              locals := locals1
            }

/-- Wraps an `AllocFunc` as a `Machine AllocState Int`. -/
def anAllocMachine (af : AllocFunc) : Machine AllocState Int where
  step := stepAllocFunc af

/-! ## 4. `regalloc2`-Style Forward Symbolic Checker and Soundness Proof -/

/-- Symbolic checker state mapping physical `Allocation`s to the `VReg`s whose
current values they hold. Represented as a finite list of `(Allocation × VReg)`
pairs, isomorphic to `regalloc2`'s `FxHashMap<Allocation, FxHashSet<VReg>>`. -/
abbrev CheckerState := List (Allocation × VReg)

/-- Checks whether `Allocation` `a` is guaranteed to hold virtual register `v`
in symbolic state `st`. -/
def hasVReg (st : CheckerState) (a : Allocation) (v : VReg) : Bool :=
  st.contains (a, v)

/-- Checks whether an `Allocation` respects the function's physical register
and spill-slot bounds. -/
def wfAlloc (numPRegs numSpills : Nat) (a : Allocation) : Bool :=
  match a with
  | .preg r => decide (r.idx < numPRegs)
  | .spill s => decide (s < numSpills)

/-- Checks whether a list of clobbered `PReg`s lies within `numPRegs`. -/
def wfClobbers (numPRegs : Nat) (clobbers : List PReg) : Bool :=
  clobbers.all (fun r => decide (r.idx < numPRegs))

/-- Symbolic transfer function for `EditMove { into, from_ }`.
Unconditionally removes all previous bindings for `into` before copying any
`VReg` bindings currently associated with `from_`. This fixes the soundness bug
in `regalloc2`'s `CheckerState::update` (`src/checker.rs:554-562`), where an
untracked `from_` failed to kill stale bindings in `into`. -/
def updateMove (st : CheckerState) (m : EditMove) : CheckerState :=
  let kept := st.filter (fun p => p.1 != m.into)
  let copied := (st.filter (fun p => p.1 == m.from_)).map (fun p => (m.into, p.2))
  kept ++ copied

/-- Symbolic transfer function for a sequential list of `EditMove`s, returning
`none` if any move references an out-of-bounds `Allocation`. -/
def checkEditMoves (numPRegs numSpills : Nat) (st : CheckerState) :
    List EditMove → Option CheckerState
  | [] => some st
  | m :: ms =>
      if wfAlloc numPRegs numSpills m.into &&
         wfAlloc numPRegs numSpills m.from_ then
        checkEditMoves numPRegs numSpills (updateMove st m) ms
      else
        none

/-- Removes all symbolic bindings residing in a clobbered physical register. -/
def killPReg (st : CheckerState) (r : PReg) : CheckerState :=
  st.filter (fun p => p.1 != .preg r)

/-- Removes all symbolic bindings in a list of clobbered physical registers. -/
def killClobbers (st : CheckerState) : List PReg → CheckerState
  | [] => st
  | r :: rs => killClobbers (killPReg st r) rs

/-- Symbolic transfer function for defining virtual register `v` in `dst`:
kills any previous bindings in `dst` and any stale locations holding `v`, then
records `(dst, v)`. -/
def updateDef (st : CheckerState) (dst : Allocation) (v : VReg) : CheckerState :=
  (dst, v) :: st.filter (fun p => p.1 != dst && p.2 != v)

/-- Checks a single instruction `MInstOp` against its source `VInst` and
computes the successor `CheckerState`. Checks all input `Use`s before killing
`clobbers` and updating `Def`s. -/
def checkMInstOp (numPRegs numSpills numLocals : Nat) (st : CheckerState)
    (vi : VInst) (op : MInstOp) : Option CheckerState :=
  match vi, op with
  | .const vDst vVal, .const mDst mVal clobbers =>
      if vVal == mVal &&
         wfAlloc numPRegs numSpills mDst &&
         wfClobbers numPRegs clobbers then
        some (updateDef (killClobbers st clobbers) mDst vDst)
      else
        none
  | .mov vDst vSrc, .mov mDst mSrc clobbers =>
      if hasVReg st mSrc vSrc &&
         wfAlloc numPRegs numSpills mDst &&
         wfAlloc numPRegs numSpills mSrc &&
         wfClobbers numPRegs clobbers then
        some (updateDef (killClobbers st clobbers) mDst vDst)
      else
        none
  | .binop vOp vDst vLhs vRhs, .binop mOp mDst mLhs mRhs clobbers =>
      if vOp == mOp &&
         hasVReg st mLhs vLhs &&
         hasVReg st mRhs vRhs &&
         wfAlloc numPRegs numSpills mDst &&
         wfAlloc numPRegs numSpills mLhs &&
         wfAlloc numPRegs numSpills mRhs &&
         wfClobbers numPRegs clobbers then
        some (updateDef (killClobbers st clobbers) mDst vDst)
      else
        none
  | .loadLocal vDst vSlot, .loadLocal mDst mSlot clobbers =>
      if vSlot == mSlot &&
         decide (vSlot < numLocals) &&
         wfAlloc numPRegs numSpills mDst &&
         wfClobbers numPRegs clobbers then
        some (updateDef (killClobbers st clobbers) mDst vDst)
      else
        none
  | .storeLocal vSlot vSrc, .storeLocal mSlot mSrc clobbers =>
      if vSlot == mSlot &&
         decide (vSlot < numLocals) &&
         hasVReg st mSrc vSrc &&
         wfAlloc numPRegs numSpills mSrc &&
         wfClobbers numPRegs clobbers then
        some (killClobbers st clobbers)
      else
        none
  | _, _ => none

/-- Checks a single `AllocatedInst` (`edits` followed by `op`) against a source
`VInst`. -/
def checkAllocatedInst (numPRegs numSpills numLocals : Nat) (st : CheckerState)
    (vi : VInst) (ai : AllocatedInst) : Option CheckerState :=
  match checkEditMoves numPRegs numSpills st ai.edits with
  | none => none
  | some st1 => checkMInstOp numPRegs numSpills numLocals st1 vi ai.op

/-- Checks a sequence of `AllocatedInst`s against a sequence of `VInst`s. -/
def checkAllocatedInsts (numPRegs numSpills numLocals : Nat) (st : CheckerState) :
    List VInst → List AllocatedInst → Option CheckerState
  | [], [] => some st
  | vi :: vis, ai :: ais =>
      match checkAllocatedInst numPRegs numSpills numLocals st vi ai with
      | none => none
      | some st' => checkAllocatedInsts numPRegs numSpills numLocals st' vis ais
  | _, _ => none

/-- Kildall join / meet operation on `CheckerState`: set intersection of active
`(Allocation, VReg)` bindings across control-flow predecessors. -/
def meetState (s1 s2 : CheckerState) : CheckerState :=
  s1.filter (fun p => s2.contains p)

/-- Checks that every `(Allocation, VReg)` requirement in `required` (the
target block's entry `CheckerState`) is satisfied by the outgoing state
`actual` at a CFG edge. -/
def subState (required actual : CheckerState) : Bool :=
  required.all (fun p => actual.contains p)

/-- Checks an allocated terminator `MTermOp` against a source `VTerm` and the
function's block-entry state certificate `blockIn : List CheckerState`. -/
def checkTerm (numPRegs numSpills : Nat) (blockIn : List CheckerState)
    (st : CheckerState) (vt : VTerm) (mt : MTermOp) : Bool :=
  match vt, mt with
  | .ret vSrc, .ret edits mSrc =>
      match checkEditMoves numPRegs numSpills st edits with
      | none => false
      | some st1 =>
          hasVReg st1 mSrc vSrc && wfAlloc numPRegs numSpills mSrc
  | .br vTarget, .br edits mTarget =>
      if vTarget == mTarget then
        match checkEditMoves numPRegs numSpills st edits, blockIn[mTarget]? with
        | some st1, some stTarget => subState stTarget st1
        | _, _ => false
      else
        false
  | .condBr vCond vT vF, .condBr edits mCond tEdits mT fEdits mF =>
      if vT == mT && vF == mF then
        match checkEditMoves numPRegs numSpills st edits with
        | none => false
        | some st1 =>
            if hasVReg st1 mCond vCond && wfAlloc numPRegs numSpills mCond then
              match checkEditMoves numPRegs numSpills st1 tEdits,
                    checkEditMoves numPRegs numSpills st1 fEdits,
                    blockIn[mT]?, blockIn[mF]? with
              | some stT, some stF, some reqT, some reqF =>
                  subState reqT stT && subState reqF stF
              | _, _, _, _ => false
            else
              false
      else
        false
  | _, _ => false

/-- Checks a single basic block against its entry `CheckerState`. -/
def checkBlock (numPRegs numSpills numLocals : Nat)
    (blockIn : List CheckerState) (stEntry : CheckerState)
    (vblk : VBlock) (ablk : AllocatedBlock) : Bool :=
  match checkAllocatedInsts numPRegs numSpills numLocals stEntry
          vblk.insts ablk.insts with
  | none => false
  | some stEnd =>
      checkTerm numPRegs numSpills blockIn stEnd vblk.term ablk.term

/-- Checks all blocks in lockstep against `blockIn`. -/
def checkBlocks (numPRegs numSpills numLocals : Nat)
    (blockIn : List CheckerState) :
    List CheckerState → List VBlock → List AllocatedBlock → Bool
  | [], [], [] => true
  | st :: sts, vb :: vbs, ab :: abs_ =>
      checkBlock numPRegs numSpills numLocals blockIn st vb ab &&
      checkBlocks numPRegs numSpills numLocals blockIn sts vbs abs_
  | _, _, _ => false

/-- Top-level `regalloc2`-style translation validation checker for a multi-block
function `VFunc` and its `AllocFunc` allocation, given the block-entry state
certificate `blockIn`. -/
def checkRegAlloc (vf : VFunc) (af : AllocFunc)
    (blockIn : List CheckerState) : Bool :=
  vf.numLocals == af.numLocals &&
  vf.entry == af.entry &&
  checkBlocks af.numPRegs af.numSpills af.numLocals
    blockIn blockIn vf.blocks af.blocks

/-! ### Soundness Proof for `checkRegAlloc` -/

/-- Semantic compatibility between `vregs` and `(pregs, spills)` under
symbolic state `st`: every `(a, v) ∈ st` holds `vregs v` in `a`. -/
def StateCompat (st : CheckerState) (vregs : VReg → Int)
    (pregs : PReg → Int) (spills : SpillSlot → Int) : Prop :=
  ∀ a v, (a, v) ∈ st → readAlloc pregs spills a = vregs v

/-- Agreement of local slots between `AnVReg` and `AnAlloc` on all indices
`< numLocals`. -/
def LocalCompat (numLocals : Nat) (vlocals mlocals : LocalSlot → Int) : Prop :=
  ∀ slot, slot < numLocals → mlocals slot = vlocals slot

theorem readAlloc_writeAlloc_eq (pregs : PReg → Int) (spills : SpillSlot → Int)
    (a : Allocation) (val : Int) :
    readAlloc (writeAlloc pregs spills a val).1
      (writeAlloc pregs spills a val).2 a = val := by
  cases a with
  | preg r => simp [writeAlloc, readAlloc, updatePReg]
  | spill s => simp [writeAlloc, readAlloc, updateSpill]

theorem readAlloc_writeAlloc_ne (pregs : PReg → Int) (spills : SpillSlot → Int)
    {a b : Allocation} (hNe : a ≠ b) (val : Int) :
    readAlloc (writeAlloc pregs spills b val).1
      (writeAlloc pregs spills b val).2 a = readAlloc pregs spills a := by
  cases a <;> cases b <;>
    simp [writeAlloc, readAlloc, updatePReg, updateSpill] at hNe ⊢
  · intro hEq; exact False.elim (hNe hEq)
  · intro hEq; exact False.elim (hNe hEq)

theorem hasVReg_sound {st : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hCompat : StateCompat st vregs pregs spills)
    {a : Allocation} {v : VReg} (hHas : hasVReg st a v = true) :
    readAlloc pregs spills a = vregs v := by
  unfold hasVReg at hHas
  rw [List.contains_iff_mem] at hHas
  exact hCompat a v hHas

theorem updateMove_compat {st : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hCompat : StateCompat st vregs pregs spills) (m : EditMove) :
    StateCompat (updateMove st m) vregs
      (execEditMove pregs spills m).1 (execEditMove pregs spills m).2 := by
  intro a v hMem
  unfold updateMove at hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl hKept =>
      rw [List.mem_filter] at hKept
      rcases hKept with ⟨hInSt, hNeB⟩
      have hNe : a ≠ m.into := by
        intro hEq
        subst hEq
        simp at hNeB
      unfold execEditMove
      rw [readAlloc_writeAlloc_ne pregs spills hNe]
      exact hCompat a v hInSt
  | inr hCopied =>
      rw [List.mem_map] at hCopied
      rcases hCopied with ⟨⟨a0, v0⟩, hInFilter, hPairEq⟩
      rw [List.mem_filter] at hInFilter
      rcases hInFilter with ⟨hInSt, hFromB⟩
      injection hPairEq with hA hV
      subst hA; subst hV
      have hFrom : a0 = m.from_ := of_decide_eq_true hFromB
      subst hFrom
      unfold execEditMove
      rw [readAlloc_writeAlloc_eq]
      exact hCompat m.from_ v0 hInSt

theorem checkEditMoves_compat {numPRegs numSpills : Nat}
    {st st' : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    {edits : List EditMove}
    (hCheck : checkEditMoves numPRegs numSpills st edits = some st')
    (hCompat : StateCompat st vregs pregs spills) :
    StateCompat st' vregs
      (execEditMoves pregs spills edits).1
      (execEditMoves pregs spills edits).2 := by
  induction edits generalizing st pregs spills with
  | nil =>
      simp [checkEditMoves] at hCheck
      subst hCheck
      exact hCompat
  | cons m ms ih =>
      simp only [checkEditMoves] at hCheck
      split at hCheck
      · simp only [execEditMoves]
        exact ih hCheck (updateMove_compat hCompat m)
      · contradiction

theorem killPReg_compat {st : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hCompat : StateCompat st vregs pregs spills) (r : PReg) (val : Int) :
    StateCompat (killPReg st r) vregs (updatePReg pregs r val) spills := by
  intro a v hMem
  unfold killPReg at hMem
  rw [List.mem_filter] at hMem
  rcases hMem with ⟨hInSt, hNeB⟩
  cases a with
  | preg r' =>
      have hNe : r' ≠ r := by
        intro hEq
        subst hEq
        simp at hNeB
      simp [readAlloc, updatePReg, hNe]
      exact hCompat (.preg r') v hInSt
  | spill s =>
      simp [readAlloc]
      exact hCompat (.spill s) v hInSt

theorem killClobbers_compat {st : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hCompat : StateCompat st vregs pregs spills) (clobbers : List PReg) :
    StateCompat (killClobbers st clobbers) vregs
      (applyClobbers pregs clobbers) spills := by
  induction clobbers generalizing st pregs with
  | nil => exact hCompat
  | cons r rs ih =>
      simp only [killClobbers, applyClobbers]
      exact ih (killPReg_compat hCompat r 0)

theorem updateDef_compat {st : CheckerState} {vregs : VReg → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hCompat : StateCompat st vregs pregs spills)
    (dst : Allocation) (v : VReg) (val : Int) :
    StateCompat (updateDef st dst v) (updateVReg vregs v val)
      (writeAlloc pregs spills dst val).1
      (writeAlloc pregs spills dst val).2 := by
  intro a u hMem
  unfold updateDef at hMem
  rw [List.mem_cons] at hMem
  cases hMem with
  | inl hHead =>
      injection hHead with hA hU
      subst hA; subst hU
      rw [readAlloc_writeAlloc_eq]
      simp [updateVReg]
  | inr hTail =>
      rw [List.mem_filter] at hTail
      rcases hTail with ⟨hInSt, hCond⟩
      rw [Bool.and_eq_true] at hCond
      rcases hCond with ⟨hNeDstB, hNeVB⟩
      have hNeDst : a ≠ dst := by
        intro hEq; subst hEq; simp at hNeDstB
      have hNeV : u ≠ v := by
        intro hEq; subst hEq; simp at hNeVB
      rw [readAlloc_writeAlloc_ne pregs spills hNeDst val]
      simp [updateVReg, hNeV]
      exact hCompat a u hInSt

theorem checkMInstOp_sound {numPRegs numSpills numLocals : Nat}
    {st st' : CheckerState} {vregs : VReg → Int}
    {vlocals mlocals : LocalSlot → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    {vi : VInst} {op : MInstOp}
    (hCheck : checkMInstOp numPRegs numSpills numLocals st vi op = some st')
    (hCompat : StateCompat st vregs pregs spills)
    (hLoc : LocalCompat numLocals vlocals mlocals) :
    let (vregs', vlocals') := execVInst vregs vlocals vi
    let (pregs', spills', mlocals') := execMInstOp pregs spills mlocals op
    StateCompat st' vregs' pregs' spills' ∧
    LocalCompat numLocals vlocals' mlocals' := by
  cases vi <;> cases op <;> simp only [checkMInstOp] at hCheck
  case const.const vDst vVal mDst mVal clobbers =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt
      subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨hValB, _⟩, _⟩
      have hVal : vVal = mVal := of_decide_eq_true hValB
      subst hVal
      dsimp only [execVInst, execMInstOp]
      exact ⟨updateDef_compat (killClobbers_compat hCompat clobbers) mDst vDst vVal, hLoc⟩
    · contradiction
  case mov.mov vDst vSrc mDst mSrc clobbers =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt
      subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨hHas, _⟩, _⟩, _⟩
      have hSrcEq := hasVReg_sound hCompat hHas
      dsimp only [execVInst, execMInstOp]
      rw [hSrcEq]
      exact ⟨updateDef_compat (killClobbers_compat hCompat clobbers) mDst vDst (vregs vSrc), hLoc⟩
    · contradiction
  case binop.binop vOp vDst vLhs vRhs mOp mDst mLhs mRhs clobbers =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt
      subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨⟨⟨⟨hOpB, hLhs⟩, hRhs⟩, _⟩, _⟩, _⟩, _⟩
      have hOp : vOp = mOp := of_decide_eq_true hOpB
      subst hOp
      have hLhsEq := hasVReg_sound hCompat hLhs
      have hRhsEq := hasVReg_sound hCompat hRhs
      dsimp only [execVInst, execMInstOp]
      rw [hLhsEq, hRhsEq]
      exact ⟨updateDef_compat (killClobbers_compat hCompat clobbers) mDst vDst
              (evalBinOp vOp (vregs vLhs) (vregs vRhs)), hLoc⟩
    · contradiction
  case loadLocal.loadLocal vDst vSlot mDst mSlot clobbers =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt
      subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨hSlotB, hLtB⟩, _⟩, _⟩
      have hSlot : vSlot = mSlot := of_decide_eq_true hSlotB
      subst hSlot
      have hLt : vSlot < numLocals := of_decide_eq_true hLtB
      have hLocEq := hLoc vSlot hLt
      dsimp only [execVInst, execMInstOp]
      rw [hLocEq]
      exact ⟨updateDef_compat (killClobbers_compat hCompat clobbers) mDst vDst (vlocals vSlot), hLoc⟩
    · contradiction
  case storeLocal.storeLocal vSlot vSrc mSlot mSrc clobbers =>
    split at hCheck
    · rename_i hCond
      injection hCheck with hSt
      subst hSt
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨⟨hSlotB, _⟩, hHas⟩, _⟩, _⟩
      have hSlot : vSlot = mSlot := of_decide_eq_true hSlotB
      subst hSlot
      have hSrcEq := hasVReg_sound hCompat hHas
      dsimp only [execVInst, execMInstOp]
      rw [hSrcEq]
      refine ⟨killClobbers_compat hCompat clobbers, ?_⟩
      intro s hs
      unfold updateLocal
      split
      · rfl
      · exact hLoc s hs
    · contradiction
  all_goals contradiction

theorem checkAllocatedInst_sound {numPRegs numSpills numLocals : Nat}
    {st st' : CheckerState} {vregs : VReg → Int}
    {vlocals mlocals : LocalSlot → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    {vi : VInst} {ai : AllocatedInst}
    (hCheck : checkAllocatedInst numPRegs numSpills numLocals st vi ai = some st')
    (hCompat : StateCompat st vregs pregs spills)
    (hLoc : LocalCompat numLocals vlocals mlocals) :
    let (vregs', vlocals') := execVInst vregs vlocals vi
    let (pregs', spills', mlocals') := execAllocatedInst pregs spills mlocals ai
    StateCompat st' vregs' pregs' spills' ∧
    LocalCompat numLocals vlocals' mlocals' := by
  unfold checkAllocatedInst at hCheck
  cases hMoves : checkEditMoves numPRegs numSpills st ai.edits with
  | none =>
      rw [hMoves] at hCheck
      contradiction
  | some st1 =>
      rw [hMoves] at hCheck
      have hMovesCompat := checkEditMoves_compat hMoves hCompat
      dsimp only [execAllocatedInst]
      exact checkMInstOp_sound hCheck hMovesCompat hLoc

theorem checkAllocatedInsts_sound {numPRegs numSpills numLocals : Nat}
    {st st' : CheckerState} {vregs : VReg → Int}
    {vlocals mlocals : LocalSlot → Int}
    {pregs : PReg → Int} {spills : SpillSlot → Int}
    {vis : List VInst} {ais : List AllocatedInst}
    (hCheck : checkAllocatedInsts numPRegs numSpills numLocals st vis ais = some st')
    (hCompat : StateCompat st vregs pregs spills)
    (hLoc : LocalCompat numLocals vlocals mlocals) :
    let (vregs', vlocals') := execVInsts vregs vlocals vis
    let (pregs', spills', mlocals') := execAllocatedInsts pregs spills mlocals ais
    StateCompat st' vregs' pregs' spills' ∧
    LocalCompat numLocals vlocals' mlocals' := by
  induction vis generalizing ais st vregs vlocals mlocals pregs spills with
  | nil =>
      cases ais with
      | nil =>
          simp [checkAllocatedInsts] at hCheck
          subst hCheck
          exact ⟨hCompat, hLoc⟩
      | cons _ _ =>
          simp [checkAllocatedInsts] at hCheck
  | cons vi visTail ih =>
      cases ais with
      | nil =>
          simp [checkAllocatedInsts] at hCheck
      | cons ai aisTail =>
          simp only [checkAllocatedInsts] at hCheck
          cases hInst : checkAllocatedInst numPRegs numSpills numLocals st vi ai with
          | none =>
              rw [hInst] at hCheck
              contradiction
          | some st1 =>
              rw [hInst] at hCheck
              rcases checkAllocatedInst_sound hInst hCompat hLoc with ⟨hC1, hL1⟩
              dsimp only [execVInsts, execAllocatedInsts]
              exact ih hCheck hC1 hL1

theorem subState_compat {req actual : CheckerState}
    {vregs : VReg → Int} {pregs : PReg → Int} {spills : SpillSlot → Int}
    (hSub : subState req actual = true)
    (hCompat : StateCompat actual vregs pregs spills) :
    StateCompat req vregs pregs spills := by
  intro a v hMem
  unfold subState at hSub
  rw [List.all_eq_true] at hSub
  have hInActualB := hSub (a, v) hMem
  rw [List.contains_iff_mem] at hInActualB
  exact hCompat a v hInActualB

/-- Lookups in `checkBlocks` extract the per-block validation fact at index `b`. -/
theorem checkBlocks_get? {numPRegs numSpills numLocals : Nat}
    {blockIn sts : List CheckerState}
    {vbs : List VBlock} {abs_ : List AllocatedBlock}
    (hCheck : checkBlocks numPRegs numSpills numLocals blockIn sts vbs abs_ = true)
    (b : BlockId) {vb : VBlock} (hVb : vbs[b]? = some vb) :
    ∃ st ab, sts[b]? = some st ∧ abs_[b]? = some ab ∧
      checkBlock numPRegs numSpills numLocals blockIn st vb ab = true := by
  induction sts generalizing vbs abs_ b with
  | nil =>
      cases vbs <;> cases abs_ <;> simp [checkBlocks] at hCheck
      simp at hVb
  | cons st stsTail ih =>
      cases vbs with
      | nil => simp at hVb
      | cons vbHead vbsTail =>
          cases abs_ with
          | nil => simp [checkBlocks] at hCheck
          | cons abHead absTail =>
              simp only [checkBlocks, Bool.and_eq_true] at hCheck
              rcases hCheck with ⟨hBlk, hRest⟩
              cases b with
              | zero =>
                  simp at hVb
                  subst hVb
                  exact ⟨st, abHead, rfl, rfl, hBlk⟩
              | succ b' =>
                  simp at hVb
                  exact ih hRest b' hVb

/-- Symmetric lookup in `checkBlocks` starting from `abs_[b]? = some ab`. -/
theorem checkBlocks_get_ab? {numPRegs numSpills numLocals : Nat}
    {blockIn sts : List CheckerState}
    {vbs : List VBlock} {abs_ : List AllocatedBlock}
    (hCheck : checkBlocks numPRegs numSpills numLocals blockIn sts vbs abs_ = true)
    (b : BlockId) {ab : AllocatedBlock} (hAb : abs_[b]? = some ab) :
    ∃ st vb, sts[b]? = some st ∧ vbs[b]? = some vb ∧
      checkBlock numPRegs numSpills numLocals blockIn st vb ab = true := by
  induction sts generalizing vbs abs_ b with
  | nil =>
      cases vbs <;> cases abs_ <;> simp [checkBlocks] at hCheck
      simp at hAb
  | cons st stsTail ih =>
      cases vbs with
      | nil =>
          cases abs_ <;> simp [checkBlocks] at hCheck
      | cons vbHead vbsTail =>
          cases abs_ with
          | nil => simp at hAb
          | cons abHead absTail =>
              simp only [checkBlocks, Bool.and_eq_true] at hCheck
              rcases hCheck with ⟨hBlk, hRest⟩
              cases b with
              | zero =>
                  simp at hAb
                  subst hAb
                  exact ⟨st, vbHead, rfl, rfl, hBlk⟩
              | succ b' =>
                  simp at hAb
                  exact ih hRest b' hAb

/-- Relational invariant connecting `VState` and `AllocState` during multi-block
execution. -/
def AllocRel (numLocals : Nat) (blockIn : List CheckerState)
    (vs : VState) (as_ : AllocState) : Prop :=
  vs.block = as_.block ∧
  LocalCompat numLocals vs.locals as_.locals ∧
  ∃ st, blockIn[vs.block]? = some st ∧
    StateCompat st vs.vregs as_.pregs as_.spills

/-- **Theorem (`checkRegAlloc_sound`):** Any multi-block allocation accepted by
`checkRegAlloc` is a forward behavioral refinement (`Refines`) of the source
`AnVReg` function. -/
theorem checkRegAlloc_sound (vf : VFunc) (af : AllocFunc)
    (blockIn : List CheckerState)
    (hCheck : checkRegAlloc vf af blockIn = true) :
    Refines (anVRegMachine vf) (anAllocMachine af)
      (AllocRel vf.numLocals blockIn) := by
  unfold checkRegAlloc at hCheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hCheck
  rcases hCheck with ⟨⟨hLocB, _⟩, hBlocks⟩
  have hNumLocals : vf.numLocals = af.numLocals := of_decide_eq_true hLocB
  intro vs as_ hRel
  rcases hRel with ⟨hBlkEq, hLocCompat, stEntry, hStEntry, hStCompat⟩
  dsimp only [anVRegMachine, anAllocMachine, stepVFunc, stepAllocFunc]
  cases hVb : vf.blocks[vs.block]? with
  | none =>
      trivial
  | some vblk =>
      rcases checkBlocks_get? hBlocks vs.block hVb with
        ⟨stEntry', ablk, hStEntry', hAb, hCheckBlk⟩
      rw [hStEntry] at hStEntry'
      injection hStEntry' with hStEq
      subst hStEq
      rw [← hBlkEq, hAb]
      dsimp only
      unfold checkBlock at hCheckBlk
      cases hInsts : checkAllocatedInsts af.numPRegs af.numSpills af.numLocals
          stEntry vblk.insts ablk.insts with
      | none =>
          rw [hInsts] at hCheckBlk
          contradiction
      | some stEnd =>
          rw [hInsts] at hCheckBlk
          dsimp only at hCheckBlk
          have hLocCompat' : LocalCompat af.numLocals vs.locals as_.locals := by
            rw [← hNumLocals]; exact hLocCompat
          rcases checkAllocatedInsts_sound hInsts hStCompat hLocCompat' with
            ⟨hEndCompat, hEndLoc⟩
          have hEndLocV : LocalCompat vf.numLocals
              (execVInsts vs.vregs vs.locals vblk.insts).2
              (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2 := by
            rw [hNumLocals]; exact hEndLoc
          cases hVt : vblk.term <;> cases hMt : ablk.term <;>
            rw [hVt, hMt] at hCheckBlk <;> simp only [checkTerm] at hCheckBlk
          case ret.ret vSrc edits mSrc =>
            cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
            | none =>
                rw [hEd] at hCheckBlk
                contradiction
            | some stRet =>
                rw [hEd] at hCheckBlk
                dsimp only at hCheckBlk
                rw [Bool.and_eq_true] at hCheckBlk
                rcases hCheckBlk with ⟨hHas, _⟩
                have hRetCompat := checkEditMoves_compat hEd hEndCompat
                have hValEq := hasVReg_sound hRetCompat hHas
                simp [hValEq]
          case br.br vTarget edits mTarget =>
            split at hCheckBlk
            · rename_i hTargetB
              have hTarget : vTarget = mTarget := of_decide_eq_true hTargetB
              subst hTarget
              cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
              | none =>
                  rw [hEd] at hCheckBlk
                  contradiction
              | some stBr =>
                  rw [hEd] at hCheckBlk
                  cases hReq : blockIn[vTarget]? with
                  | none =>
                      rw [hReq] at hCheckBlk
                      contradiction
                  | some stTarget =>
                      rw [hReq] at hCheckBlk
                      dsimp only at hCheckBlk
                      have hBrCompat := checkEditMoves_compat hEd hEndCompat
                      have hTargetCompat := subState_compat hCheckBlk hBrCompat
                      exact ⟨_, rfl, rfl, hEndLocV, stTarget, hReq, hTargetCompat⟩
            · contradiction
          case condBr.condBr vCond vT vF edits mCond tEdits mT fEdits mF =>
            split at hCheckBlk
            · rename_i hTargetsB
              rw [Bool.and_eq_true] at hTargetsB
              rcases hTargetsB with ⟨hTB, hFB⟩
              have hT : vT = mT := of_decide_eq_true hTB
              have hF : vF = mF := of_decide_eq_true hFB
              subst hT; subst hF
              cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
              | none =>
                  rw [hEd] at hCheckBlk
                  contradiction
              | some stCond =>
                  rw [hEd] at hCheckBlk
                  dsimp only at hCheckBlk
                  split at hCheckBlk
                  · rename_i hCondHasB
                    rw [Bool.and_eq_true] at hCondHasB
                    rcases hCondHasB with ⟨hHasCond, _⟩
                    have hCondCompat := checkEditMoves_compat hEd hEndCompat
                    have hCondEq := hasVReg_sound hCondCompat hHasCond
                    cases hEdT : checkEditMoves af.numPRegs af.numSpills stCond tEdits with
                    | none => rw [hEdT] at hCheckBlk; contradiction
                    | some stT =>
                      cases hEdF : checkEditMoves af.numPRegs af.numSpills stCond fEdits with
                      | none => rw [hEdT, hEdF] at hCheckBlk; contradiction
                      | some stF =>
                        cases hReqT : blockIn[vT]? with
                        | none => rw [hEdT, hEdF, hReqT] at hCheckBlk; contradiction
                        | some reqT =>
                          cases hReqF : blockIn[vF]? with
                          | none =>
                              rw [hEdT, hEdF, hReqT, hReqF] at hCheckBlk
                              contradiction
                          | some reqF =>
                              rw [hEdT, hEdF, hReqT, hReqF] at hCheckBlk
                              dsimp only at hCheckBlk
                              rw [Bool.and_eq_true] at hCheckBlk
                              rcases hCheckBlk with ⟨hSubT, hSubF⟩
                              dsimp only
                              rw [hCondEq]
                              split
                              · have hTCompat :=
                                  subState_compat hSubT
                                    (checkEditMoves_compat hEdT hCondCompat)
                                exact ⟨_, rfl, rfl, hEndLocV, reqT, hReqT, hTCompat⟩
                              · have hFCompat :=
                                  subState_compat hSubF
                                    (checkEditMoves_compat hEdF hCondCompat)
                                exact ⟨_, rfl, rfl, hEndLocV, reqF, hReqF, hFCompat⟩
                  · contradiction
            · contradiction
          all_goals contradiction

/-! ## 5. The `Stacking` Pass, Frame-Size Certificates (`A-BEH-07`), and `AnMach` -/

/-- Concrete frame layout computed by `Stacking` for a function:
- `[0, numLocals)`: local stack slots
- `[numLocals, numLocals + numSpills)`: `regalloc2` spill slots
- `[numLocals + numSpills, frameSize)`: saved callee-save registers & link -/
structure FrameLayout where
  numLocals : Nat
  numSpills : Nat
  numSavedRegs : Nat
  deriving DecidableEq, Repr

/-- Total static frame size $\mathcal{S}(f)$ in words/slots. -/
def FrameLayout.frameSize (fl : FrameLayout) : Nat :=
  fl.numLocals + fl.numSpills + fl.numSavedRegs

/-- Byte/word offset of a local slot from `sp`. -/
def FrameLayout.localOffset (_fl : FrameLayout) (slot : LocalSlot) : Nat :=
  slot

/-- Byte/word offset of a spill slot from `sp`. -/
def FrameLayout.spillOffset (fl : FrameLayout) (s : SpillSlot) : Nat :=
  fl.numLocals + s

/-- Byte/word offset of a saved register slot from `sp`. -/
def FrameLayout.savedRegOffset (fl : FrameLayout) (idx : Nat) : Nat :=
  fl.numLocals + fl.numSpills + idx

theorem localOffset_lt_frameSize (fl : FrameLayout) {slot : Nat}
    (h : slot < fl.numLocals) : fl.localOffset slot < fl.frameSize := by
  unfold FrameLayout.localOffset FrameLayout.frameSize
  omega

theorem spillOffset_lt_frameSize (fl : FrameLayout) {s : Nat}
    (h : s < fl.numSpills) : fl.spillOffset s < fl.frameSize := by
  unfold FrameLayout.spillOffset FrameLayout.frameSize
  omega

theorem savedRegOffset_lt_frameSize (fl : FrameLayout) {idx : Nat}
    (h : idx < fl.numSavedRegs) : fl.savedRegOffset idx < fl.frameSize := by
  unfold FrameLayout.savedRegOffset FrameLayout.frameSize
  omega

theorem local_spill_disjoint (fl : FrameLayout) {slot s : Nat}
    (h : slot < fl.numLocals) :
    fl.localOffset slot ≠ fl.spillOffset s := by
  unfold FrameLayout.localOffset FrameLayout.spillOffset
  omega

theorem local_saved_disjoint (fl : FrameLayout) {slot idx : Nat}
    (h : slot < fl.numLocals) :
    fl.localOffset slot ≠ fl.savedRegOffset idx := by
  unfold FrameLayout.localOffset FrameLayout.savedRegOffset
  omega

theorem spill_saved_disjoint (fl : FrameLayout) {s idx : Nat}
    (h : s < fl.numSpills) :
    fl.spillOffset s ≠ fl.savedRegOffset idx := by
  unfold FrameLayout.spillOffset FrameLayout.savedRegOffset
  omega

/-- Physical location in `AnMach` after `Stacking` folds both local slots and
spill slots into `SP`-relative frame offsets `[sp + offset]`. -/
inductive MachLoc where
  | preg (r : PReg)
  | stackOffset (off : Nat)
  deriving DecidableEq, Repr

/-- Lowers an `Allocation` into a `MachLoc` using `FrameLayout`. -/
def lowerAlloc (fl : FrameLayout) (a : Allocation) : MachLoc :=
  match a with
  | .preg r => .preg r
  | .spill s => .stackOffset (fl.spillOffset s)

/-- A single move instruction in `AnMach` (`into := from_`) over `MachLoc`. -/
structure MachMove where
  into : MachLoc
  from_ : MachLoc
  deriving DecidableEq, Repr

/-- Lowers an `EditMove` into a `MachMove`. -/
def lowerEditMove (fl : FrameLayout) (m : EditMove) : MachMove where
  into := lowerAlloc fl m.into
  from_ := lowerAlloc fl m.from_

/-- Lowers a list of `EditMove`s. -/
def lowerEditMoves (fl : FrameLayout) (ms : List EditMove) : List MachMove :=
  ms.map (lowerEditMove fl)

/-- Non-branching instruction in `AnMach` after `Stacking`. Both local slots
and spill slots have been folded into `SP`-relative stack offsets. -/
inductive MachInstOp where
  | const (dst : MachLoc) (val : Int) (clobbers : List PReg)
  | mov (dst src : MachLoc) (clobbers : List PReg)
  | binop (op : BinOp) (dst lhs rhs : MachLoc) (clobbers : List PReg)
  deriving DecidableEq, Repr

/-- Lowers an `MInstOp` into a `MachInstOp` by folding `loadLocal` and
`storeLocal` into `MachInstOp.mov` with `.stackOffset (fl.localOffset slot)`. -/
def lowerMInstOp (fl : FrameLayout) (op : MInstOp) : MachInstOp :=
  match op with
  | .const dst val clobbers =>
      .const (lowerAlloc fl dst) val clobbers
  | .mov dst src clobbers =>
      .mov (lowerAlloc fl dst) (lowerAlloc fl src) clobbers
  | .binop bop dst lhs rhs clobbers =>
      .binop bop (lowerAlloc fl dst) (lowerAlloc fl lhs)
        (lowerAlloc fl rhs) clobbers
  | .loadLocal dst slot clobbers =>
      .mov (lowerAlloc fl dst) (.stackOffset (fl.localOffset slot)) clobbers
  | .storeLocal slot src clobbers =>
      .mov (.stackOffset (fl.localOffset slot)) (lowerAlloc fl src) clobbers

/-- Stacked instruction pairing lowered `MachMove`s with a `MachInstOp`. -/
structure MachInst where
  moves : List MachMove
  op : MachInstOp
  deriving DecidableEq, Repr

/-- Lowers an `AllocatedInst` into a `MachInst`. -/
def lowerAllocatedInst (fl : FrameLayout) (ai : AllocatedInst) : MachInst where
  moves := lowerEditMoves fl ai.edits
  op := lowerMInstOp fl ai.op

/-- Block terminator in `AnMach`. -/
inductive MachTerm where
  | ret (moves : List MachMove) (src : MachLoc)
  | br (moves : List MachMove) (target : BlockId)
  | condBr (moves : List MachMove) (cond : MachLoc)
      (tMoves : List MachMove) (tTarget : BlockId)
      (fMoves : List MachMove) (fTarget : BlockId)
  deriving DecidableEq, Repr

/-- Lowers an `MTermOp` into a `MachTerm`. -/
def lowerMTermOp (fl : FrameLayout) (mt : MTermOp) : MachTerm :=
  match mt with
  | .ret edits src =>
      .ret (lowerEditMoves fl edits) (lowerAlloc fl src)
  | .br edits target =>
      .br (lowerEditMoves fl edits) target
  | .condBr edits cond tEdits tTarget fEdits fTarget =>
      .condBr (lowerEditMoves fl edits) (lowerAlloc fl cond)
        (lowerEditMoves fl tEdits) tTarget
        (lowerEditMoves fl fEdits) fTarget

/-- Basic block in `AnMach`. -/
structure MachBlock where
  insts : List MachInst
  term : MachTerm
  deriving DecidableEq, Repr

/-- Lowers an `AllocatedBlock` into a `MachBlock`. -/
def lowerAllocatedBlock (fl : FrameLayout) (ablk : AllocatedBlock) :
    MachBlock where
  insts := ablk.insts.map (lowerAllocatedInst fl)
  term := lowerMTermOp fl ablk.term

/-- Complete lowered function in `AnMach`, carrying its static `FrameLayout`. -/
structure MachFunc where
  layout : FrameLayout
  entry : BlockId
  blocks : List MachBlock
  deriving DecidableEq, Repr

/-- The `Stacking` pass: lowers an `AllocFunc` into a `MachFunc` with a unified
`FrameLayout`. -/
def lowerFunc (af : AllocFunc) : MachFunc :=
  let fl : FrameLayout := {
    numLocals := af.numLocals
    numSpills := af.numSpills
    numSavedRegs := af.numSavedRegs
  }
  { layout := fl
    entry := af.entry
    blocks := af.blocks.map (lowerAllocatedBlock fl) }

/-- Static **Frame-Size Certificate** $\mathcal{S}(f)$ emitted by `Stacking`. -/
def frameSizeCert (af : AllocFunc) : Nat :=
  (lowerFunc af).layout.frameSize

/-- Hardware state of `AnMach` with bounded flat stack `[stackLimit, stackBase)`.
Any stack access when `sp < stackLimit` triggers `.failed .stackOverflow`, and
any access at `addr ≥ stackBase` triggers `.failed .outOfBoundsStackAccess`. -/
structure MachState where
  block : BlockId
  pregs : PReg → Int
  sp : Nat
  mem : Nat → Int
  stackLimit : Nat
  stackBase : Nat

/-- Functional update of flat stack memory at address `addr`. -/
def updateMem (mem : Nat → Int) (addr : Nat) (val : Int) : Nat → Int :=
  fun a => if a = addr then val else mem a

/-- Reads a `MachLoc` in `AnMach`, checking hardware stack bounds on
`.stackOffset off`. -/
def readMachLoc (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) (loc : MachLoc) :
    Except FailureKind Int :=
  match loc with
  | .preg r => .ok (pregs r)
  | .stackOffset off =>
      if sp < stackLimit then
        .error .stackOverflow
      else if stackBase ≤ sp + off then
        .error .outOfBoundsStackAccess
      else
        .ok (mem (sp + off))

/-- Writes `val` to a `MachLoc` in `AnMach`, checking hardware stack bounds on
`.stackOffset off`. Notice that `addr = sp + off` with `off : Nat`, so `AnMach`
structurally never writes below `sp` (no red-zone access). -/
def writeMachLoc (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) (loc : MachLoc) (val : Int) :
    Except FailureKind ((PReg → Int) × (Nat → Int)) :=
  match loc with
  | .preg r => .ok (updatePReg pregs r val, mem)
  | .stackOffset off =>
      if sp < stackLimit then
        .error .stackOverflow
      else if stackBase ≤ sp + off then
        .error .outOfBoundsStackAccess
      else
        .ok (pregs, updateMem mem (sp + off) val)

/-- Executes a single `MachMove` in `AnMach`. -/
def execMachMove (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) (m : MachMove) :
    Except FailureKind ((PReg → Int) × (Nat → Int)) := do
  let val ← readMachLoc pregs sp mem stackLimit stackBase m.from_
  writeMachLoc pregs sp mem stackLimit stackBase m.into val

/-- Executes a sequence of `MachMove`s in `AnMach`. -/
def execMachMoves (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) :
    List MachMove → Except FailureKind ((PReg → Int) × (Nat → Int))
  | [] => .ok (pregs, mem)
  | m :: ms => do
      let (pregs', mem') ← execMachMove pregs sp mem stackLimit stackBase m
      execMachMoves pregs' sp mem' stackLimit stackBase ms

/-- Executes a `MachInstOp` in `AnMach`. -/
def execMachInstOp (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) (op : MachInstOp) :
    Except FailureKind ((PReg → Int) × (Nat → Int)) :=
  match op with
  | .const dst val clobbers =>
      let pregs1 := applyClobbers pregs clobbers
      writeMachLoc pregs1 sp mem stackLimit stackBase dst val
  | .mov dst src clobbers => do
      let v ← readMachLoc pregs sp mem stackLimit stackBase src
      let pregs1 := applyClobbers pregs clobbers
      writeMachLoc pregs1 sp mem stackLimit stackBase dst v
  | .binop bop dst lhs rhs clobbers => do
      let vL ← readMachLoc pregs sp mem stackLimit stackBase lhs
      let vR ← readMachLoc pregs sp mem stackLimit stackBase rhs
      let pregs1 := applyClobbers pregs clobbers
      writeMachLoc pregs1 sp mem stackLimit stackBase dst (evalBinOp bop vL vR)

/-- Executes a `MachInst` (`moves` followed by `op`). -/
def execMachInst (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) (mi : MachInst) :
    Except FailureKind ((PReg → Int) × (Nat → Int)) := do
  let (pregs1, mem1) ← execMachMoves pregs sp mem stackLimit stackBase mi.moves
  execMachInstOp pregs1 sp mem1 stackLimit stackBase mi.op

/-- Executes a sequence of `MachInst`s. -/
def execMachInsts (pregs : PReg → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat) :
    List MachInst → Except FailureKind ((PReg → Int) × (Nat → Int))
  | [] => .ok (pregs, mem)
  | mi :: mis => do
      let (pregs', mem') ← execMachInst pregs sp mem stackLimit stackBase mi
      execMachInsts pregs' sp mem' stackLimit stackBase mis

/-- Executes one basic-block step of a `MachFunc` in `AnMach`. -/
def stepMachFunc (mf : MachFunc) (ms : MachState) :
    StepResult MachState Int :=
  match mf.blocks[ms.block]? with
  | none => .stuck
  | some mblk =>
      match execMachInsts ms.pregs ms.sp ms.mem ms.stackLimit ms.stackBase
              mblk.insts with
      | .error err => .failed err
      | .ok (pregs1, mem1) =>
          match mblk.term with
          | .ret moves src =>
              match execMachMoves pregs1 ms.sp mem1 ms.stackLimit ms.stackBase
                      moves with
              | .error err => .failed err
              | .ok (pregs2, mem2) =>
                  match readMachLoc pregs2 ms.sp mem2 ms.stackLimit ms.stackBase
                          src with
                  | .error err => .failed err
                  | .ok val => .terminal val
          | .br moves target =>
              match execMachMoves pregs1 ms.sp mem1 ms.stackLimit ms.stackBase
                      moves with
              | .error err => .failed err
              | .ok (pregs2, mem2) =>
                  .continue_ { ms with
                    block := target
                    pregs := pregs2
                    mem := mem2
                  }
          | .condBr moves cond tMoves tTarget fMoves fTarget =>
              match execMachMoves pregs1 ms.sp mem1 ms.stackLimit ms.stackBase
                      moves with
              | .error err => .failed err
              | .ok (pregs2, mem2) =>
                  match readMachLoc pregs2 ms.sp mem2 ms.stackLimit ms.stackBase
                          cond with
                  | .error err => .failed err
                  | .ok condVal =>
                      if condVal != 0 then
                        match execMachMoves pregs2 ms.sp mem2 ms.stackLimit
                                ms.stackBase tMoves with
                        | .error err => .failed err
                        | .ok (pregsT, memT) =>
                            .continue_ { ms with
                              block := tTarget
                              pregs := pregsT
                              mem := memT
                            }
                      else
                        match execMachMoves pregs2 ms.sp mem2 ms.stackLimit
                                ms.stackBase fMoves with
                        | .error err => .failed err
                        | .ok (pregsF, memF) =>
                            .continue_ { ms with
                              block := fTarget
                              pregs := pregsF
                              mem := memF
                            }

/-- Wraps a `MachFunc` as a `Machine MachState Int`. -/
def anMachMachine (mf : MachFunc) : Machine MachState Int where
  step := stepMachFunc mf

/-! ### Soundness Proof for `Stacking` (`AnAlloc` $\to$ `AnMach`) -/

/-- Agreement between abstract `(locals, spills)` in `AnAlloc` and concrete
flat stack memory `[sp, sp + fl.frameSize)` in `AnMach`. -/
def StackFrameCompat (fl : FrameLayout) (sp : Nat)
    (locals : LocalSlot → Int) (spills : SpillSlot → Int)
    (mem : Nat → Int) : Prop :=
  (∀ slot, slot < fl.numLocals → mem (sp + fl.localOffset slot) = locals slot) ∧
  (∀ s, s < fl.numSpills → mem (sp + fl.spillOffset s) = spills s)

theorem readMachLoc_lowerAlloc (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    (hFrame : StackFrameCompat fl sp locals spills mem)
    {numPRegs : Nat} {a : Allocation}
    (hWf : wfAlloc numPRegs fl.numSpills a = true) :
    readMachLoc pregs sp mem stackLimit stackBase (lowerAlloc fl a) =
      .ok (readAlloc pregs spills a) := by
  cases a with
  | preg r => rfl
  | spill s =>
      simp only [wfAlloc] at hWf
      have hs : s < fl.numSpills := of_decide_eq_true hWf
      have hOffLt := spillOffset_lt_frameSize fl hs
      have hNotLim : ¬ (sp < stackLimit) := by omega
      have hNotBase : ¬ (stackBase ≤ sp + fl.spillOffset s) := by omega
      simp [lowerAlloc, readMachLoc, hNotLim, hNotBase, readAlloc, hFrame.2 s hs]

theorem writeMachLoc_lowerAlloc (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    (hFrame : StackFrameCompat fl sp locals spills mem)
    {numPRegs : Nat} {a : Allocation}
    (hWf : wfAlloc numPRegs fl.numSpills a = true) (val : Int) :
    ∃ mem',
      writeMachLoc pregs sp mem stackLimit stackBase (lowerAlloc fl a) val =
        .ok ((writeAlloc pregs spills a val).1, mem') ∧
      StackFrameCompat fl sp locals (writeAlloc pregs spills a val).2 mem' ∧
      (∀ addr, (addr < sp ∨ sp + fl.frameSize ≤ addr) → mem' addr = mem addr) := by
  cases a with
  | preg r =>
      refine ⟨mem, rfl, hFrame, ?_⟩
      intro addr _; rfl
  | spill s =>
      simp only [wfAlloc] at hWf
      have hs : s < fl.numSpills := of_decide_eq_true hWf
      have hOffLt := spillOffset_lt_frameSize fl hs
      have hNotLim : ¬ (sp < stackLimit) := by omega
      have hNotBase : ¬ (stackBase ≤ sp + fl.spillOffset s) := by omega
      refine ⟨updateMem mem (sp + fl.spillOffset s) val, ?_, ?_, ?_⟩
      · simp [lowerAlloc, writeMachLoc, writeAlloc, hNotLim, hNotBase]
      · constructor
        · intro slot hSlot
          have hDisj := local_spill_disjoint fl (s := s) hSlot
          simp [updateMem, hDisj, hFrame.1 slot hSlot]
        · intro s' hs'
          by_cases hEq : s' = s
          · subst hEq
            simp [updateMem, writeAlloc, updateSpill]
          · have hOffNe : fl.spillOffset s' ≠ fl.spillOffset s := by
              unfold FrameLayout.spillOffset; omega
            simp [updateMem, writeAlloc, updateSpill, hEq, hOffNe, hFrame.2 s' hs']
      · intro addr hOut
        have hAddrNe : addr ≠ sp + fl.spillOffset s := by omega
        simp [updateMem, hAddrNe]

theorem readMachLoc_localOffset (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    (hFrame : StackFrameCompat fl sp locals spills mem)
    {slot : Nat} (hSlot : slot < fl.numLocals) :
    readMachLoc pregs sp mem stackLimit stackBase
      (.stackOffset (fl.localOffset slot)) = .ok (locals slot) := by
  have hOffLt := localOffset_lt_frameSize fl hSlot
  have hNotLim : ¬ (sp < stackLimit) := by omega
  have hNotBase : ¬ (stackBase ≤ sp + fl.localOffset slot) := by omega
  simp [readMachLoc, hNotLim, hNotBase, hFrame.1 slot hSlot]

theorem writeMachLoc_localOffset (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    (hFrame : StackFrameCompat fl sp locals spills mem)
    {slot : Nat} (hSlot : slot < fl.numLocals) (val : Int) :
    let mem' := updateMem mem (sp + fl.localOffset slot) val
    writeMachLoc pregs sp mem stackLimit stackBase
      (.stackOffset (fl.localOffset slot)) val = .ok (pregs, mem') ∧
    StackFrameCompat fl sp (updateLocal locals slot val) spills mem' ∧
    (∀ addr, (addr < sp ∨ sp + fl.frameSize ≤ addr) → mem' addr = mem addr) := by
  have hOffLt := localOffset_lt_frameSize fl hSlot
  have hNotLim : ¬ (sp < stackLimit) := by omega
  have hNotBase : ¬ (stackBase ≤ sp + fl.localOffset slot) := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [writeMachLoc, hNotLim, hNotBase]
  · constructor
    · intro slot' hSlot'
      by_cases hEq : slot' = slot
      · subst hEq
        simp [updateMem, updateLocal]
      · have hOffNe : fl.localOffset slot' ≠ fl.localOffset slot := by
          unfold FrameLayout.localOffset; omega
        simp [updateMem, updateLocal, hEq, hOffNe, hFrame.1 slot' hSlot']
    · intro s hs
      have hDisj : fl.spillOffset s ≠ fl.localOffset slot :=
        Ne.symm (local_spill_disjoint fl (s := s) hSlot)
      simp [updateMem, hDisj, hFrame.2 s hs]
  · intro addr hOut
    have hAddrNe : addr ≠ sp + fl.localOffset slot := by omega
    simp [updateMem, hAddrNe]

theorem execMachMoves_lowerEditMoves (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    {numPRegs : Nat} {st st' : CheckerState} {edits : List EditMove}
    (hCheck : checkEditMoves numPRegs fl.numSpills st edits = some st')
    (hFrame : StackFrameCompat fl sp locals spills mem) :
    ∃ mem',
      execMachMoves pregs sp mem stackLimit stackBase
        (lowerEditMoves fl edits) =
        .ok ((execEditMoves pregs spills edits).1, mem') ∧
      StackFrameCompat fl sp locals (execEditMoves pregs spills edits).2 mem' ∧
      (∀ addr, (addr < sp ∨ sp + fl.frameSize ≤ addr) → mem' addr = mem addr) := by
  induction edits generalizing st pregs spills mem with
  | nil =>
      exact ⟨mem, rfl, hFrame, fun _ _ => rfl⟩
  | cons m ms ih =>
      simp only [checkEditMoves] at hCheck
      split at hCheck
      · rename_i hWfB
        rw [Bool.and_eq_true] at hWfB
        rcases hWfB with ⟨hWfInto, hWfFrom⟩
        have hRead := readMachLoc_lowerAlloc fl pregs spills locals sp mem
          stackLimit stackBase hLim hBase hFrame hWfFrom
        rcases writeMachLoc_lowerAlloc fl pregs spills locals sp mem
          stackLimit stackBase hLim hBase hFrame hWfInto
          (readAlloc pregs spills m.from_) with
          ⟨mem1, hWriteMach, hFrame1, hOut1⟩
        rcases ih (execEditMove pregs spills m).1
          (execEditMove pregs spills m).2 mem1 hCheck hFrame1 with
          ⟨mem2, hRestMach, hFrame2, hOut2⟩
        refine ⟨mem2, ?_, hFrame2, ?_⟩
        · dsimp only [lowerEditMoves, List.map, execMachMoves, execMachMove,
                      lowerEditMove, Bind.bind, Except.bind, execEditMoves]
          rw [hRead]
          dsimp only
          rw [hWriteMach]
          exact hRestMach
        · intro addr hOut
          rw [hOut2 addr hOut, hOut1 addr hOut]
      · contradiction

theorem execMachInstOp_lowerMInstOp (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    {numPRegs : Nat} {st st' : CheckerState} {vi : VInst} {op : MInstOp}
    (hCheck : checkMInstOp numPRegs fl.numSpills fl.numLocals st vi op = some st')
    (hFrame : StackFrameCompat fl sp locals spills mem) :
    ∃ mem',
      execMachInstOp pregs sp mem stackLimit stackBase (lowerMInstOp fl op) =
        .ok ((execMInstOp pregs spills locals op).1, mem') ∧
      StackFrameCompat fl sp
        (execMInstOp pregs spills locals op).2.2
        (execMInstOp pregs spills locals op).2.1 mem' ∧
      (∀ addr, (addr < sp ∨ sp + fl.frameSize ≤ addr) → mem' addr = mem addr) := by
  cases vi <;> cases op <;> simp only [checkMInstOp] at hCheck
  case const.const vDst vVal mDst mVal clobbers =>
    split at hCheck
    · rename_i hCond
      rw [Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨_, hWfDst⟩, _⟩
      rcases writeMachLoc_lowerAlloc fl (applyClobbers pregs clobbers) spills
        locals sp mem stackLimit stackBase hLim hBase hFrame hWfDst mVal with
        ⟨mem', hWM, hFrame', hOut'⟩
      exact ⟨mem', hWM, hFrame', hOut'⟩
    · contradiction
  case mov.mov vDst vSrc mDst mSrc clobbers =>
    split at hCheck
    · rename_i hCond
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨_, hWfDst⟩, hWfSrc⟩, _⟩
      have hRead := readMachLoc_lowerAlloc fl pregs spills locals sp mem
        stackLimit stackBase hLim hBase hFrame hWfSrc
      rcases writeMachLoc_lowerAlloc fl (applyClobbers pregs clobbers) spills
        locals sp mem stackLimit stackBase hLim hBase hFrame hWfDst
        (readAlloc pregs spills mSrc) with
        ⟨mem', hWM, hFrame', hOut'⟩
      refine ⟨mem', ?_, hFrame', hOut'⟩
      dsimp only [lowerMInstOp, execMachInstOp, execMInstOp,
                  Bind.bind, Except.bind]
      rw [hRead]
      exact hWM
    · contradiction
  case binop.binop vOp vDst vLhs vRhs mOp mDst mLhs mRhs clobbers =>
    split at hCheck
    · rename_i hCond
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hWfDst⟩, hWfLhs⟩, hWfRhs⟩, _⟩
      have hRL := readMachLoc_lowerAlloc fl pregs spills locals sp mem
        stackLimit stackBase hLim hBase hFrame hWfLhs
      have hRR := readMachLoc_lowerAlloc fl pregs spills locals sp mem
        stackLimit stackBase hLim hBase hFrame hWfRhs
      rcases writeMachLoc_lowerAlloc fl (applyClobbers pregs clobbers) spills
        locals sp mem stackLimit stackBase hLim hBase hFrame hWfDst
        (evalBinOp mOp (readAlloc pregs spills mLhs)
          (readAlloc pregs spills mRhs)) with
        ⟨mem', hWM, hFrame', hOut'⟩
      refine ⟨mem', ?_, hFrame', hOut'⟩
      dsimp only [lowerMInstOp, execMachInstOp, execMInstOp,
                  Bind.bind, Except.bind]
      rw [hRL]
      dsimp only
      rw [hRR]
      exact hWM
    · contradiction
  case loadLocal.loadLocal vDst vSlot mDst mSlot clobbers =>
    split at hCheck
    · rename_i hCond
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨hSlotB, hLtB⟩, hWfDst⟩, _⟩
      have hSlotEq : vSlot = mSlot := of_decide_eq_true hSlotB
      subst hSlotEq
      have hLt : vSlot < fl.numLocals := of_decide_eq_true hLtB
      have hRead := readMachLoc_localOffset fl pregs spills locals sp mem
        stackLimit stackBase hLim hBase hFrame hLt
      rcases writeMachLoc_lowerAlloc fl (applyClobbers pregs clobbers) spills
        locals sp mem stackLimit stackBase hLim hBase hFrame hWfDst
        (locals vSlot) with
        ⟨mem', hWM, hFrame', hOut'⟩
      refine ⟨mem', ?_, hFrame', hOut'⟩
      dsimp only [lowerMInstOp, execMachInstOp, execMInstOp,
                  Bind.bind, Except.bind]
      rw [hRead]
      exact hWM
    · contradiction
  case storeLocal.storeLocal vSlot vSrc mSlot mSrc clobbers =>
    split at hCheck
    · rename_i hCond
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at hCond
      rcases hCond with ⟨⟨⟨⟨hSlotB, hLtB⟩, _⟩, hWfSrc⟩, _⟩
      have hSlotEq : vSlot = mSlot := of_decide_eq_true hSlotB
      subst hSlotEq
      have hLt : vSlot < fl.numLocals := of_decide_eq_true hLtB
      have hRead := readMachLoc_lowerAlloc fl pregs spills locals sp mem
        stackLimit stackBase hLim hBase hFrame hWfSrc
      rcases writeMachLoc_localOffset fl (applyClobbers pregs clobbers) spills
        locals sp mem stackLimit stackBase hLim hBase hFrame hLt
        (readAlloc pregs spills mSrc) with
        ⟨hWM, hFrame', hOut'⟩
      refine ⟨updateMem mem (sp + fl.localOffset vSlot)
                (readAlloc pregs spills mSrc), ?_, hFrame', hOut'⟩
      dsimp only [lowerMInstOp, execMachInstOp, execMInstOp,
                  Bind.bind, Except.bind]
      rw [hRead]
      exact hWM
    · contradiction
  all_goals contradiction

theorem execMachInsts_lowerAllocatedInsts (fl : FrameLayout)
    (pregs : PReg → Int) (spills : SpillSlot → Int)
    (locals : LocalSlot → Int) (sp : Nat) (mem : Nat → Int)
    (stackLimit stackBase : Nat)
    (hLim : stackLimit ≤ sp) (hBase : sp + fl.frameSize ≤ stackBase)
    {numPRegs : Nat} {st st' : CheckerState}
    {vis : List VInst} {ais : List AllocatedInst}
    (hCheck : checkAllocatedInsts numPRegs fl.numSpills fl.numLocals
                st vis ais = some st')
    (hFrame : StackFrameCompat fl sp locals spills mem) :
    ∃ mem',
      execMachInsts pregs sp mem stackLimit stackBase
        (ais.map (lowerAllocatedInst fl)) =
        .ok ((execAllocatedInsts pregs spills locals ais).1, mem') ∧
      StackFrameCompat fl sp
        (execAllocatedInsts pregs spills locals ais).2.2
        (execAllocatedInsts pregs spills locals ais).2.1 mem' ∧
      (∀ addr, (addr < sp ∨ sp + fl.frameSize ≤ addr) → mem' addr = mem addr) := by
  induction vis generalizing ais st pregs spills locals mem with
  | nil =>
      cases ais with
      | nil =>
          exact ⟨mem, rfl, hFrame, fun _ _ => rfl⟩
      | cons _ _ =>
          simp [checkAllocatedInsts] at hCheck
  | cons vi visTail ih =>
      cases ais with
      | nil =>
          simp [checkAllocatedInsts] at hCheck
      | cons ai aisTail =>
          simp only [checkAllocatedInsts] at hCheck
          cases hInst : checkAllocatedInst numPRegs fl.numSpills fl.numLocals
              st vi ai with
          | none =>
              rw [hInst] at hCheck; contradiction
          | some st1 =>
              rw [hInst] at hCheck
              dsimp only at hCheck
              unfold checkAllocatedInst at hInst
              cases hMoves : checkEditMoves numPRegs fl.numSpills st ai.edits with
              | none =>
                  rw [hMoves] at hInst; contradiction
              | some stMoves =>
                  rw [hMoves] at hInst
                  dsimp only at hInst
                  rcases execMachMoves_lowerEditMoves fl pregs spills locals
                    sp mem stackLimit stackBase hLim hBase hMoves hFrame with
                    ⟨mem1, hMachMoves, hFrame1, hOut1⟩
                  rcases execMachInstOp_lowerMInstOp fl
                    (execEditMoves pregs spills ai.edits).1
                    (execEditMoves pregs spills ai.edits).2
                    locals sp mem1 stackLimit stackBase hLim hBase hInst
                    hFrame1 with
                    ⟨mem2, hMachOp, hFrame2, hOut2⟩
                  rcases ih
                    (execAllocatedInst pregs spills locals ai).1
                    (execAllocatedInst pregs spills locals ai).2.1
                    (execAllocatedInst pregs spills locals ai).2.2
                    mem2 hCheck hFrame2 with
                    ⟨mem3, hMachRest, hFrame3, hOut3⟩
                  refine ⟨mem3, ?_, hFrame3, ?_⟩
                  · dsimp only [List.map, execMachInsts, execMachInst,
                                lowerAllocatedInst, Bind.bind, Except.bind,
                                execAllocatedInsts, execAllocatedInst]
                    rw [hMachMoves]
                    dsimp only
                    rw [hMachOp]
                    exact hMachRest
                  · intro addr hOut
                    rw [hOut3 addr hOut, hOut2 addr hOut, hOut1 addr hOut]

/-- Simulation relation between `AllocState` and `MachState` under `Stacking`. -/
def StackingRel (fl : FrameLayout) (as_ : AllocState) (ms : MachState) : Prop :=
  as_.block = ms.block ∧
  as_.pregs = ms.pregs ∧
  ms.stackLimit ≤ ms.sp ∧
  ms.sp + fl.frameSize ≤ ms.stackBase ∧
  StackFrameCompat fl ms.sp as_.locals as_.spills ms.mem

/-- **Theorem (`stacking_sound`):** For any function validated by
`checkRegAlloc`, the `Stacking`-lowered machine `AnMach` refines `AnAlloc`
whenever the current frame `[sp, sp + frameSize)` fits within
`[stackLimit, stackBase)`. -/
theorem stacking_sound (vf : VFunc) (af : AllocFunc)
    (blockIn : List CheckerState)
    (hCheck : checkRegAlloc vf af blockIn = true) :
    let mf := lowerFunc af
    Refines (anAllocMachine af) (anMachMachine mf)
      (StackingRel mf.layout) := by
  intro mf as_ ms hStackRel
  unfold checkRegAlloc at hCheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hCheck
  rcases hCheck with ⟨⟨_, _⟩, hBlocks⟩
  rcases hStackRel with ⟨hAsBlk, hPregsEq, hLim, hBase, hFrame⟩
  dsimp only [anAllocMachine, anMachMachine, stepAllocFunc, stepMachFunc]
  cases hAb : af.blocks[as_.block]? with
  | none =>
      trivial
  | some ablk =>
      have hMb : mf.blocks[ms.block]? =
          some (lowerAllocatedBlock mf.layout ablk) := by
        simp [mf, lowerFunc, ← hAsBlk, hAb]
      rw [hMb, ← hPregsEq]
      dsimp only
      rcases checkBlocks_get_ab? hBlocks as_.block hAb with
        ⟨stEntry, vblk, _, _, hCheckBlk⟩
      unfold checkBlock at hCheckBlk
      cases hInsts : checkAllocatedInsts af.numPRegs af.numSpills af.numLocals
          stEntry vblk.insts ablk.insts with
      | none =>
          rw [hInsts] at hCheckBlk; contradiction
      | some stEnd =>
          rw [hInsts] at hCheckBlk
          dsimp only at hCheckBlk
          rcases execMachInsts_lowerAllocatedInsts mf.layout
            as_.pregs as_.spills as_.locals ms.sp ms.mem
            ms.stackLimit ms.stackBase hLim hBase hInsts hFrame with
            ⟨mem1, hMachInsts, hFrame1, _⟩
          dsimp only [lowerAllocatedBlock]
          rw [hMachInsts]
          dsimp only
          cases hVt : vblk.term <;> cases hMt : ablk.term <;>
            rw [hVt, hMt] at hCheckBlk <;> simp only [checkTerm] at hCheckBlk
          case ret.ret vSrc edits mSrc =>
            cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
            | none => rw [hEd] at hCheckBlk; contradiction
            | some stRet =>
                rw [hEd] at hCheckBlk
                dsimp only at hCheckBlk
                rw [Bool.and_eq_true] at hCheckBlk
                rcases hCheckBlk with ⟨_, hWfSrc⟩
                rcases execMachMoves_lowerEditMoves mf.layout
                  (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                  (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                  (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                  ms.sp mem1 ms.stackLimit ms.stackBase hLim hBase hEd hFrame1 with
                  ⟨mem2, hMachEd, hFrame2, _⟩
                have hReadSrc := readMachLoc_lowerAlloc mf.layout
                  (execEditMoves
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                    edits).1
                  (execEditMoves
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                    edits).2
                  (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                  ms.sp mem2 ms.stackLimit ms.stackBase hLim hBase hFrame2 hWfSrc
                simp only [lowerMTermOp, hMachEd, hReadSrc]
          case br.br vTarget edits mTarget =>
            split at hCheckBlk
            · cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
              | none => rw [hEd] at hCheckBlk; contradiction
              | some stBr =>
                  rcases execMachMoves_lowerEditMoves mf.layout
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                    (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                    ms.sp mem1 ms.stackLimit ms.stackBase hLim hBase hEd hFrame1 with
                    ⟨mem2, hMachEd, hFrame2, _⟩
                  simp only [lowerMTermOp, hMachEd]
                  exact ⟨_, rfl, rfl, rfl, hLim, hBase, hFrame2⟩
            · contradiction
          case condBr.condBr vCond vT vF edits mCond tEdits mT fEdits mF =>
            split at hCheckBlk
            · cases hEd : checkEditMoves af.numPRegs af.numSpills stEnd edits with
              | none => rw [hEd] at hCheckBlk; contradiction
              | some stCond =>
                  rw [hEd] at hCheckBlk
                  dsimp only at hCheckBlk
                  split at hCheckBlk
                  · rename_i hCondHasB
                    rw [Bool.and_eq_true] at hCondHasB
                    rcases hCondHasB with ⟨_, hWfCond⟩
                    rcases execMachMoves_lowerEditMoves mf.layout
                      (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                      (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                      (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                      ms.sp mem1 ms.stackLimit ms.stackBase hLim hBase hEd hFrame1 with
                      ⟨mem2, hMachEd, hFrame2, _⟩
                    have hReadCond := readMachLoc_lowerAlloc mf.layout
                      (execEditMoves
                        (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                        (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                        edits).1
                      (execEditMoves
                        (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                        (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                        edits).2
                      (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                      ms.sp mem2 ms.stackLimit ms.stackBase hLim hBase hFrame2 hWfCond
                    cases hEdT : checkEditMoves af.numPRegs af.numSpills stCond tEdits with
                    | none => rw [hEdT] at hCheckBlk; contradiction
                    | some stT =>
                      cases hEdF : checkEditMoves af.numPRegs af.numSpills stCond fEdits with
                      | none => rw [hEdT, hEdF] at hCheckBlk; contradiction
                      | some stF =>
                          dsimp only [lowerMTermOp]
                          rw [hMachEd]
                          dsimp only
                          rw [hReadCond]
                          dsimp only
                          by_cases hCondVal :
                            (readAlloc
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).1
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).2
                              mCond != 0) = true
                          · simp only [hCondVal, ↓reduceIte]
                            rcases execMachMoves_lowerEditMoves mf.layout
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).1
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).2
                              (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                              ms.sp mem2 ms.stackLimit ms.stackBase hLim hBase hEdT hFrame2 with
                              ⟨memT, hMachEdT, hFrameT, _⟩
                            rw [hMachEdT]
                            exact ⟨_, rfl, rfl, rfl, hLim, hBase, hFrameT⟩
                          · simp only [hCondVal, Bool.false_eq_true, ↓reduceIte]
                            rcases execMachMoves_lowerEditMoves mf.layout
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).1
                              (execEditMoves
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).1
                                (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.1
                                edits).2
                              (execAllocatedInsts as_.pregs as_.spills as_.locals ablk.insts).2.2
                              ms.sp mem2 ms.stackLimit ms.stackBase hLim hBase hEdF hFrame2 with
                              ⟨memF, hMachEdF, hFrameF, _⟩
                            rw [hMachEdF]
                            exact ⟨_, rfl, rfl, rfl, hLim, hBase, hFrameF⟩
                  · contradiction
            · contradiction
          all_goals contradiction

/-- **End-to-End Composition Theorem (`regalloc_and_stacking_sound`):**
Composes `checkRegAlloc_sound` (`AnVReg` $\to$ `AnAlloc`) and `stacking_sound`
(`AnAlloc` $\to$ `AnMach`) into a single end-to-end forward refinement from the
multi-block virtual-register IR `AnVReg` to the flat-stack physical machine
`AnMach`. -/
theorem regalloc_and_stacking_sound (vf : VFunc) (af : AllocFunc)
    (blockIn : List CheckerState)
    (hCheck : checkRegAlloc vf af blockIn = true) :
    let mf := lowerFunc af
    Refines (anVRegMachine vf) (anMachMachine mf)
      (fun vs ms => ∃ as_,
        AllocRel vf.numLocals blockIn vs as_ ∧
        StackingRel mf.layout as_ ms) :=
  refines_trans
    (checkRegAlloc_sound vf af blockIn hCheck)
    (stacking_sound vf af blockIn hCheck)

/-! ## 6. Frame-Size Certificates (`A-BEH-07`), `-mno-red-zone`, and Guard-Page Probing -/

/-- Allocates a new stack frame of size `frameSize` by decrementing `sp`.
If the remaining stack budget `sp - stackLimit` is strictly less than
`frameSize` (`sp < stackLimit + frameSize`), transitions deterministically to
`.failed .stackOverflow`. -/
def allocFrame (sp frameSize stackLimit : Nat) : StepResult Nat Unit :=
  if sp < stackLimit + frameSize then
    .failed .stackOverflow
  else
    .continue_ (sp - frameSize)

/-- Sum of static Frame-Size Certificates $\sum_{f \in \text{calls}} \mathcal{S}(f)$
along a call chain. -/
def totalFrameSize (cert : FnId → Nat) : List FnId → Nat
  | [] => 0
  | f :: fs => cert f + totalFrameSize cert fs

/-- Allocates stack frames sequentially along a call chain `calls : List FnId`
using the static Frame-Size Certificate `cert : FnId → Nat`. -/
def allocCallChain (cert : FnId → Nat) (stackLimit : Nat) :
    List FnId → Nat → StepResult Nat Unit
  | [], sp => .continue_ sp
  | f :: fs, sp =>
      match allocFrame sp (cert f) stackLimit with
      | .continue_ sp' => allocCallChain cert stackLimit fs sp'
      | .failed err => .failed err
      | .terminal obs => .terminal obs
      | .stuck => .stuck

/-- **Theorem (`callChain_no_stackOverflow`, discharging `A-BEH-07`):**
For any call chain `calls` whose static frame-size certificates sum to at most
the available stack budget `sp - stackLimit` (`stackLimit + totalFrameSize cert calls ≤ sp`),
`allocCallChain` succeeds without triggering `.failed .stackOverflow` and leaves
the hardware stack pointer at `sp - totalFrameSize cert calls ≥ stackLimit`. -/
theorem callChain_no_stackOverflow (cert : FnId → Nat) (stackLimit : Nat)
    (calls : List FnId) (sp : Nat)
    (hBudget : stackLimit + totalFrameSize cert calls ≤ sp) :
    allocCallChain cert stackLimit calls sp =
      .continue_ (sp - totalFrameSize cert calls) ∧
    stackLimit ≤ sp - totalFrameSize cert calls := by
  induction calls generalizing sp with
  | nil =>
      simp [totalFrameSize, allocCallChain] at hBudget ⊢
      omega
  | cons f fs ih =>
      simp only [totalFrameSize] at hBudget
      have hNotOv : ¬ (sp < stackLimit + cert f) := by omega
      have hSubBudget : stackLimit + totalFrameSize cert fs ≤ sp - cert f := by
        omega
      rcases ih (sp - cert f) hSubBudget with ⟨hRest, hLim⟩
      simp only [allocCallChain, allocFrame, hNotOv, ite_false, totalFrameSize]
      rw [hRest]
      have hEq : sp - cert f - totalFrameSize cert fs =
          sp - (cert f + totalFrameSize cert fs) := by omega
      rw [hEq] at hLim ⊢
      exact ⟨rfl, hLim⟩

/-- **Theorem (`no_red_zone_writeMachLoc`):** Every memory write in `AnMach`
occurs at `addr = sp + off ≥ sp`; no instruction ever writes to the red zone
`[0, sp)` below `sp`. -/
theorem no_red_zone_writeMachLoc {pregs pregs' : PReg → Int}
    {sp stackLimit stackBase : Nat} {mem mem' : Nat → Int}
    {loc : MachLoc} {val : Int}
    (hW : writeMachLoc pregs sp mem stackLimit stackBase loc val =
          .ok (pregs', mem')) :
    ∀ addr, addr < sp → mem' addr = mem addr := by
  intro addr hLt
  cases loc with
  | preg r =>
      simp [writeMachLoc] at hW
      rcases hW with ⟨_, rfl⟩
      rfl
  | stackOffset off =>
      simp only [writeMachLoc] at hW
      split at hW
      · contradiction
      · split at hW
        · contradiction
        · injection hW with hPair
          injection hPair with _ hMem
          subst hMem
          have hNe : addr ≠ sp + off := by omega
          simp [updateMem, hNe]

/-- Models an asynchronous interrupt or exception handler that uses the active
hardware stack pointer `sp` to push its trap frame into `[0, sp)`. -/
def asyncInterruptClobberBelowSP (sp : Nat) (intrFrame : Nat → Int)
    (mem : Nat → Int) : Nat → Int :=
  fun addr => if addr < sp then intrFrame addr else mem addr

/-- **Theorem (`interrupt_preserves_active_frames`):** Because `Stacking` with
`-mno-red-zone` places all local slots, spill slots, and saved registers at
offsets `≥ sp`, an asynchronous interrupt clobbering all memory below `sp`
preserves `StackFrameCompat` and every caller stack frame at `≥ sp`. -/
theorem interrupt_preserves_active_frames (fl : FrameLayout) (sp : Nat)
    (locals : LocalSlot → Int) (spills : SpillSlot → Int)
    (mem intrFrame : Nat → Int)
    (hFrame : StackFrameCompat fl sp locals spills mem) :
    StackFrameCompat fl sp locals spills
      (asyncInterruptClobberBelowSP sp intrFrame mem) ∧
    (∀ addr, sp ≤ addr →
      asyncInterruptClobberBelowSP sp intrFrame mem addr = mem addr) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro slot hSlot
    have hNotLt : ¬ (sp + fl.localOffset slot < sp) := by omega
    simp [asyncInterruptClobberBelowSP, hNotLt, hFrame.1 slot hSlot]
  · intro s hs
    have hNotLt : ¬ (sp + fl.spillOffset s < sp) := by omega
    simp [asyncInterruptClobberBelowSP, hNotLt, hFrame.2 s hs]
  · intro addr hGe
    have hNotLt : ¬ (addr < sp) := by omega
    simp [asyncInterruptClobberBelowSP, hNotLt]

/-- One step of periodic guard-page stack probing (`__rust_probestack` /
`Inst::StackProbeLoop`): decreases `sp` by `min remaining guardPageSize` so
that no single adjustment ever skips over an unmapped OS guard page of size
`guardPageSize`. -/
def probeStep (sp remaining guardPageSize : Nat) : Nat × Nat :=
  let step := if remaining ≤ guardPageSize then remaining else guardPageSize
  (sp - step, remaining - step)

/-- **Theorem (`probe_step_bounded`):** A single guard-page probe step never
decreases `sp` by more than `guardPageSize`, preventing Stack Clash guard-page
skipping when `frameSize > guardPageSize`. -/
theorem probe_step_bounded (sp remaining guardPageSize : Nat) :
    sp - (probeStep sp remaining guardPageSize).1 ≤ guardPageSize := by
  unfold probeStep
  dsimp only
  split <;> omega

/-! ## 7. Negative Adequacy Canaries and Positive Counterparts -/

/-! ### Canary 1: Two Live `VReg`s Assigned to the Same `PReg` Rejected -/

/-- Source function defining `v0 := 10`, `v1 := 20`, and `v2 := v0 + v1`. -/
def canary1VFunc : VFunc where
  numLocals := 0
  entry := 0
  blocks := [{
    insts := [
      .const 0 10,
      .const 1 20,
      .binop .add 2 0 1
    ]
    term := .ret 2
  }]

/-- Buggy allocation assigning both live `v0` and `v1` to `PReg 0`. -/
def canary1BadAlloc : AllocFunc where
  numPRegs := 2
  numSpills := 0
  numLocals := 0
  numSavedRegs := 0
  entry := 0
  blocks := [{
    insts := [
      { edits := [], op := .const (.preg ⟨0⟩) 10 },
      { edits := [], op := .const (.preg ⟨0⟩) 20 },
      { edits := [], op := .binop .add (.preg ⟨0⟩) (.preg ⟨0⟩) (.preg ⟨0⟩) }
    ]
    term := .ret [] (.preg ⟨0⟩)
  }]

/-- **Canary 1 (`canary1_aliasing_live_vregs_rejected`):** Assigning two
simultaneously live virtual registers (`v0` and `v1`) to the same physical
register (`PReg 0`) is rejected by `checkRegAlloc`. -/
theorem canary1_aliasing_live_vregs_rejected :
    checkRegAlloc canary1VFunc canary1BadAlloc [[]] = false := rfl

/-! ### Canary 2: Cyclic Parallel Move Without Scratch Register Rejected -/

/-- Source function defining `v0 := 10`, `v1 := 20`, and returning `v0 - v1`. -/
def canary2VFunc : VFunc where
  numLocals := 0
  entry := 0
  blocks := [{
    insts := [
      .const 0 10,
      .const 1 20,
      .binop .sub 2 0 1
    ]
    term := .ret 2
  }]

/-- Buggy sequential lowering of a cyclic parallel swap (`PReg 0 ↔ PReg 1`)
without a temporary scratch register: `PReg 0 := PReg 1; PReg 1 := PReg 0`
clobbers `v0` in `PReg 0` before copying it to `PReg 1`. -/
def canary2BadCyclicMoveAlloc : AllocFunc where
  numPRegs := 3
  numSpills := 0
  numLocals := 0
  numSavedRegs := 0
  entry := 0
  blocks := [{
    insts := [
      { edits := [], op := .const (.preg ⟨0⟩) 10 },
      { edits := [], op := .const (.preg ⟨1⟩) 20 },
      { edits := [
          { into := .preg ⟨0⟩, from_ := .preg ⟨1⟩ },
          { into := .preg ⟨1⟩, from_ := .preg ⟨0⟩ }
        ],
        op := .binop .sub (.preg ⟨0⟩) (.preg ⟨1⟩) (.preg ⟨0⟩) }
    ]
    term := .ret [] (.preg ⟨0⟩)
  }]

/-- Correct 3-move lowering of the cyclic swap (`PReg 0 ↔ PReg 1`) using
scratch register `PReg 2`:
`PReg 2 := PReg 0; PReg 0 := PReg 1; PReg 1 := PReg 2`. -/
def canary2GoodScratchMoveAlloc : AllocFunc where
  numPRegs := 3
  numSpills := 0
  numLocals := 0
  numSavedRegs := 0
  entry := 0
  blocks := [{
    insts := [
      { edits := [], op := .const (.preg ⟨0⟩) 10 },
      { edits := [], op := .const (.preg ⟨1⟩) 20 },
      { edits := [
          { into := .preg ⟨2⟩, from_ := .preg ⟨0⟩ },
          { into := .preg ⟨0⟩, from_ := .preg ⟨1⟩ },
          { into := .preg ⟨1⟩, from_ := .preg ⟨2⟩ }
        ],
        op := .binop .sub (.preg ⟨0⟩) (.preg ⟨1⟩) (.preg ⟨0⟩) }
    ]
    term := .ret [] (.preg ⟨0⟩)
  }]

/-- **Canary 2a (`canary2_cyclic_move_without_scratch_rejected`):** Lowering a
2-cycle parallel move sequentially without a scratch register is rejected by
`checkRegAlloc`. -/
theorem canary2_cyclic_move_without_scratch_rejected :
    checkRegAlloc canary2VFunc canary2BadCyclicMoveAlloc [[]] = false := rfl

/-- **Canary 2b (`canary2_cyclic_move_with_scratch_accepted`):** Breaking the
2-cycle parallel move with scratch register `PReg 2` is accepted by
`checkRegAlloc`. -/
theorem canary2_cyclic_move_with_scratch_accepted :
    checkRegAlloc canary2VFunc canary2GoodScratchMoveAlloc [[]] = true := rfl

/-! ### Canary 3: CFG Join Mismatch Across Predecessors Rejected -/

/-- Diamond CFG: Block 0 branches on `v0` to Block 1 or Block 2; both jump to
Block 3, which returns `v1`. -/
def canary3VFunc : VFunc where
  numLocals := 0
  entry := 0
  blocks := [
    -- Block 0: condBr v0 -> 1, 2
    { insts := [.const 0 1], term := .condBr 0 1 2 },
    -- Block 1: v1 := 100; br 3
    { insts := [.const 1 100], term := .br 3 },
    -- Block 2: v1 := 200; br 3
    { insts := [.const 1 200], term := .br 3 },
    -- Block 3: ret v1
    { insts := [], term := .ret 1 }
  ]

/-- Buggy allocation where Block 1 places `v1` in `PReg 0`, Block 2 places `v1`
in `PReg 1` without an edge move, and Join Block 3 reads `v1` from `PReg 0`. -/
def canary3BadJoinAlloc : AllocFunc where
  numPRegs := 2
  numSpills := 0
  numLocals := 0
  numSavedRegs := 0
  entry := 0
  blocks := [
    { insts := [{ edits := [], op := .const (.preg ⟨0⟩) 1 }],
      term := .condBr [] (.preg ⟨0⟩) [] 1 [] 2 },
    { insts := [{ edits := [], op := .const (.preg ⟨0⟩) 100 }],
      term := .br [] 3 },
    { insts := [{ edits := [], op := .const (.preg ⟨1⟩) 200 }],
      term := .br [] 3 },
    { insts := [],
      term := .ret [] (.preg ⟨0⟩) }
  ]

/-- Correct allocation inserting an edge move `PReg 0 := PReg 1` on Block 2's
jump to Join Block 3 so both predecessors establish `(PReg 0, v1)`. -/
def canary3GoodJoinAlloc : AllocFunc where
  numPRegs := 2
  numSpills := 0
  numLocals := 0
  numSavedRegs := 0
  entry := 0
  blocks := [
    { insts := [{ edits := [], op := .const (.preg ⟨0⟩) 1 }],
      term := .condBr [] (.preg ⟨0⟩) [] 1 [] 2 },
    { insts := [{ edits := [], op := .const (.preg ⟨0⟩) 100 }],
      term := .br [] 3 },
    { insts := [{ edits := [], op := .const (.preg ⟨1⟩) 200 }],
      term := .br [{ into := .preg ⟨0⟩, from_ := .preg ⟨1⟩ }] 3 },
    { insts := [],
      term := .ret [] (.preg ⟨0⟩) }
  ]

/-- Entry state certificate requiring `(PReg 0, v1)` at Join Block 3. -/
def canary3BlockIn : List CheckerState :=
  [[], [], [], [(.preg ⟨0⟩, 1)]]

/-- **Canary 3a (`canary3_cfg_join_mismatch_rejected`):** Leaving `v1` in
`PReg 0` in Block 1 and `PReg 1` in Block 2 without an edge move is rejected by
`checkRegAlloc`. -/
theorem canary3_cfg_join_mismatch_rejected :
    checkRegAlloc canary3VFunc canary3BadJoinAlloc canary3BlockIn = false := rfl

/-- **Canary 3b (`canary3_cfg_join_with_edge_move_accepted`):** Inserting the
edge move `PReg 0 := PReg 1` on Block 2's outgoing edge reconciles the join and
is accepted by `checkRegAlloc`. -/
theorem canary3_cfg_join_with_edge_move_accepted :
    checkRegAlloc canary3VFunc canary3GoodJoinAlloc canary3BlockIn = true := rfl

/-! ### Canary 4: Call Exceeding `StackBudget` Steps to `.failed .stackOverflow` -/

/-- Sample Frame-Size Certificate assigning 64 words to `fn 0` and 64 words to
`fn 1`. -/
def canary4Cert (f : FnId) : Nat :=
  match f with
  | 0 => 64
  | _ => 64

/-- **Canary 4 (`canary4_call_exceeding_stack_budget_overflows`):** Calling
`[0, 1]` (total required stack = 128 words) on a machine with `stackBase = 200`
and `stackLimit = 100` (stack budget = 100 words) deterministically transitions
to `.failed .stackOverflow`. -/
theorem canary4_call_exceeding_stack_budget_overflows :
    allocCallChain canary4Cert 100 [0, 1] 200 = .failed .stackOverflow := rfl

/-! ## 8. Axiom Footprint Verification -/

/--
info: 'Anneal.Track4.checkRegAlloc_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms checkRegAlloc_sound

/--
info: 'Anneal.Track4.stacking_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms stacking_sound

/--
info: 'Anneal.Track4.regalloc_and_stacking_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms regalloc_and_stacking_sound

/--
info: 'Anneal.Track4.callChain_no_stackOverflow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms callChain_no_stackOverflow

/--
info: 'Anneal.Track4.no_red_zone_writeMachLoc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms no_red_zone_writeMachLoc

/--
info: 'Anneal.Track4.interrupt_preserves_active_frames' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms interrupt_preserves_active_frames

/--
info: 'Anneal.Track4.probe_step_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms probe_step_bounded

/--
info: 'Anneal.Track4.canary1_aliasing_live_vregs_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary1_aliasing_live_vregs_rejected

/--
info: 'Anneal.Track4.canary2_cyclic_move_without_scratch_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary2_cyclic_move_without_scratch_rejected

/--
info: 'Anneal.Track4.canary3_cfg_join_mismatch_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canary3_cfg_join_mismatch_rejected

/--
info: 'Anneal.Track4.canary4_call_exceeding_stack_budget_overflows' does not depend on any axioms
-/
#guard_msgs in
#print axioms canary4_call_exceeding_stack_budget_overflows

end Anneal.Track4
