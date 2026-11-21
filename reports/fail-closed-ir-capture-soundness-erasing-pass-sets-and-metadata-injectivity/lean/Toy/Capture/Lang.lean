import Toy.Capture.Basic

/-!
# A concrete source IR, verifier IR, passes and captures

Source IR: a control-flow graph of blocks, each block marked normal or cleanup,
with statements (assignment, place mention, zero-size read, output, and an
`asm` statement that captures do not model) and terminators (goto, integer
switch, return, resume-unwinding, call, drop with a replace flag, terminate with a
reason, an unmodeled `trap`, and `unreachable`). Constants may be erroneous.

Verifier IR: the same shape without `asm`, `trap`, erroneous constants and the
drop replace flag, plus an `opaque` statement whose meaning is a parameter
(`OpaqueSem`): `noop` (no effect) or `havoc` (a run that reaches `opaque` admits
every behaviour for its input, including behaviours whose trace does not extend
the output emitted before `opaque`).

A program runs on one input `x : Nat`, initially stored in local `0`; all other
locals start uninitialized. Pointers are natural numbers; `0` is null. A run is an
input together with the resulting behaviour (output trace and outcome).
-/

namespace Toy.Capture

/-! ## Behaviours and states -/

/-- The reason attached to an abnormal termination while unwinding: `abi`
(unwinding is not permitted here) or `inCleanup` (a second unwind was raised while
running cleanup code for an ongoing unwind). -/
inductive Reason where
  | abi
  | inCleanup
  deriving DecidableEq, Repr

/-- How a run ends. `fuelOut` marks a run that did not finish within the fuel
(the number of blocks plus one, `SProg.fuel`); it is an ordinary outcome, distinct
from `ub` and from `abort`. -/
inductive Outcome where
  | ret
  | unwind
  | abort (r : Reason)
  | trap
  | ub
  | constErr
  | fuelOut
  deriving DecidableEq, Repr

/-- A behaviour: the output trace and the outcome. -/
structure Beh where
  trace : List Nat
  out : Outcome
  deriving DecidableEq, Repr

/-- A run: the input and the behaviour. -/
abbrev Run : Type := Nat × Beh

/-- Machine state: locals (`none` = uninitialized) and the output trace so far. -/
structure St where
  loc : Nat → Option Nat
  tr : List Nat

/-- The initial state on input `x`: local `0` holds `x`, every other local is
uninitialized, and the trace is empty. -/
def St.init (x : Nat) : St := ⟨fun l => if l = 0 then some x else none, []⟩

def St.set (st : St) (l : Nat) (v : Option Nat) : St :=
  { st with loc := fun j => if j = l then v else st.loc j }

def St.emit (st : St) (v : Nat) : St := { st with tr := st.tr ++ [v] }

/-- End the run in `st` with outcome `o`. -/
def St.fin (st : St) (o : Outcome) : Beh := ⟨st.tr, o⟩

/-- `*l` is a valid place: local `l` is initialized and non-null. Evaluating the
place `*l` (by a place mention or a zero-size read) is UB otherwise. -/
def derefOk (st : St) (l : Nat) : Bool :=
  match st.loc l with
  | some (_ + 1) => true
  | _ => false

/-! ## Source IR -/

/-- A constant: a value, or an erroneous constant whose evaluation fails. -/
inductive Const where
  | val (n : Nat)
  | err
  deriving DecidableEq, Repr

inductive SOperand where
  | copy (l : Nat)
  | const (c : Const)
  deriving DecidableEq, Repr

inductive SStmt where
  /-- `d := o` -/
  | assign (d : Nat) (o : SOperand)
  /-- Evaluate the place `*l` and discard it (no load). UB iff `*l` is invalid. -/
  | placeMention (l : Nat)
  /-- Read zero bytes through the pointer in local `l`. UB iff `*l` is invalid. -/
  | zstRead (l : Nat)
  /-- Append the operand's value to the output trace. -/
  | emit (o : SOperand)
  /-- A construct the captures here do not model: it appends `c` to the output
  trace. -/
  | asm (c : Nat)
  deriving DecidableEq, Repr

/-- The unwind action of a call: continue unwinding out of the function, or jump
to a cleanup block. -/
inductive UnwindAct where
  | continueUnwind
  | cleanup (l : Nat)
  deriving DecidableEq, Repr

inductive STerm where
  | goto (t : Nat)
  /-- Read `o`; jump to `targets[v]` if the value `v` is below `targets.length`,
  otherwise to `otherwise`. Reading an uninitialized local is UB. -/
  | switchInt (o : SOperand) (targets : List Nat) (otherwise : Nat)
  | ret
  /-- Continue unwinding out of the function (outcome `unwind`). -/
  | resume
  /-- Call an opaque function that panics iff `panics`. A panic in a cleanup block
  aborts with reason `inCleanup`; in a normal block it follows `unwind`. -/
  | call (panics : Bool) (next : Nat) (unwind : UnwindAct)
  /-- Drop local `l` (deinitialize it) and go to `next`; UB if `l` is
  uninitialized. The `replace` flag has no operational effect. -/
  | drop (replace : Bool) (l : Nat) (next : Nat)
  /-- Abort with the given reason. -/
  | terminate (r : Reason)
  /-- A construct the captures here do not model: it aborts the run (outcome
  `trap`). `next` is a syntactic fall-through label that is never taken. -/
  | trap (next : Nat)
  /-- UB. -/
  | unreachable
  deriving DecidableEq, Repr

structure SBlock where
  stmts : List SStmt
  term : STerm
  cleanup : Bool
  deriving DecidableEq, Repr

/-- A source program; execution starts at block `0`. -/
structure SProg where
  blocks : List SBlock
  deriving DecidableEq, Repr

def SOperand.eval (st : St) : SOperand → Except Outcome Nat
  | .copy l =>
    match st.loc l with
    | some v => .ok v
    | none => .error .ub
  | .const (.val n) => .ok n
  | .const .err => .error .constErr

/-- Execute one source statement: continue in a new state, or end with a
behaviour. -/
def execSStmt (st : St) : SStmt → Except Beh St
  | .assign d o =>
    match o.eval st with
    | .ok v => .ok (st.set d (some v))
    | .error e => .error (st.fin e)
  | .placeMention l => if derefOk st l then .ok st else .error (st.fin .ub)
  | .zstRead l => if derefOk st l then .ok st else .error (st.fin .ub)
  | .emit o =>
    match o.eval st with
    | .ok v => .ok (st.emit v)
    | .error e => .error (st.fin e)
  | .asm c => .ok (st.emit c)

def execSStmts : List SStmt → St → Except Beh St
  | [], st => .ok st
  | s :: ss, st =>
    match execSStmt st s with
    | .ok st' => execSStmts ss st'
    | .error b => .error b

/-- Run the source program from block `pc` with fuel `n` (one unit per block
entered). Jumping to a missing block is UB. -/
def runS (p : SProg) : Nat → Nat → St → Beh
  | 0, _, st => st.fin .fuelOut
  | n + 1, pc, st =>
    match p.blocks[pc]? with
    | none => st.fin .ub
    | some blk =>
      match execSStmts blk.stmts st with
      | .error b => b
      | .ok st' =>
        match blk.term with
        | .goto t => runS p n t st'
        | .switchInt o ts ow =>
          match o.eval st' with
          | .ok v => runS p n (ts.getD v ow) st'
          | .error e => st'.fin e
        | .ret => st'.fin .ret
        | .resume => st'.fin .unwind
        | .call panics next uw =>
          if panics then
            if blk.cleanup then st'.fin (.abort .inCleanup)
            else
              match uw with
              | .continueUnwind => st'.fin .unwind
              | .cleanup c => runS p n c st'
          else runS p n next st'
        | .drop _ l next =>
          match st'.loc l with
          | some _ => runS p n next (st'.set l none)
          | none => st'.fin .ub
        | .terminate r => st'.fin (.abort r)
        | .trap _ => st'.fin .trap
        | .unreachable => st'.fin .ub

/-- Fuel: the number of blocks plus one (one unit per block entered). A run that
enters more blocks ends in `fuelOut`; the bound counts every block, reachable or
not. -/
def SProg.fuel (p : SProg) : Nat := p.blocks.length + 1

/-- Source semantics: the set of runs `(x, b)` such that running `p` on input `x`
yields `b`. Deterministic and total. -/
def semS (p : SProg) : Den Run :=
  fun r => runS p p.fuel 0 (St.init r.1) = r.2

instance (p : SProg) : DecidablePred (semS p) :=
  fun r => inferInstanceAs (Decidable (runS p p.fuel 0 (St.init r.1) = r.2))

/-! ## Verifier IR -/

inductive VOperand where
  | copy (l : Nat)
  | const (n : Nat)
  deriving DecidableEq, Repr

inductive VStmt where
  | assign (d : Nat) (o : VOperand)
  | placeMention (l : Nat)
  | zstRead (l : Nat)
  | emit (o : VOperand)
  /-- A statement the verifier knows only by an opaque tag; its meaning is the
  parameter `OpaqueSem`. -/
  | opaque (tag : Nat)
  deriving DecidableEq, Repr

inductive VTerm where
  | goto (t : Nat)
  | switchInt (o : VOperand) (targets : List Nat) (otherwise : Nat)
  | ret
  | resume
  | call (panics : Bool) (next : Nat) (unwind : UnwindAct)
  | drop (l : Nat) (next : Nat)
  | terminate (r : Reason)
  | unreachable
  deriving DecidableEq, Repr

structure VBlock where
  stmts : List VStmt
  term : VTerm
  cleanup : Bool
  deriving DecidableEq, Repr

structure VProg where
  blocks : List VBlock
  deriving DecidableEq, Repr

/-- The meaning of `opaque` statements: `noop` (no effect) or `havoc` (reaching
`opaque` ends the verifier run with `VRes.top`, which admits every behaviour for
that input, including behaviours whose trace does not extend the output emitted
before `opaque`). -/
inductive OpaqueSem where
  | noop
  | havoc
  deriving DecidableEq, Repr

/-- Result of a verifier run: one determined behaviour, or `top` (every behaviour
is admitted, whatever the run output before the havoc). -/
inductive VRes where
  | det (b : Beh)
  | top
  deriving DecidableEq, Repr

/-- The behaviours a verifier result admits. -/
def VRes.admits : VRes → Beh → Prop
  | .det b', b => b' = b
  | .top, _ => True

def VOperand.eval (st : St) : VOperand → Except Outcome Nat
  | .copy l =>
    match st.loc l with
    | some v => .ok v
    | none => .error .ub
  | .const n => .ok n

def execVStmt (os : OpaqueSem) (st : St) : VStmt → Except VRes St
  | .assign d o =>
    match o.eval st with
    | .ok v => .ok (st.set d (some v))
    | .error e => .error (.det (st.fin e))
  | .placeMention l => if derefOk st l then .ok st else .error (.det (st.fin .ub))
  | .zstRead l => if derefOk st l then .ok st else .error (.det (st.fin .ub))
  | .emit o =>
    match o.eval st with
    | .ok v => .ok (st.emit v)
    | .error e => .error (.det (st.fin e))
  | .opaque _ =>
    match os with
    | .noop => .ok st
    | .havoc => .error .top

def execVStmts (os : OpaqueSem) : List VStmt → St → Except VRes St
  | [], st => .ok st
  | s :: ss, st =>
    match execVStmt os st s with
    | .ok st' => execVStmts os ss st'
    | .error r => .error r

def runV (os : OpaqueSem) (q : VProg) : Nat → Nat → St → VRes
  | 0, _, st => .det (st.fin .fuelOut)
  | n + 1, pc, st =>
    match q.blocks[pc]? with
    | none => .det (st.fin .ub)
    | some blk =>
      match execVStmts os blk.stmts st with
      | .error r => r
      | .ok st' =>
        match blk.term with
        | .goto t => runV os q n t st'
        | .switchInt o ts ow =>
          match o.eval st' with
          | .ok v => runV os q n (ts.getD v ow) st'
          | .error e => .det (st'.fin e)
        | .ret => .det (st'.fin .ret)
        | .resume => .det (st'.fin .unwind)
        | .call panics next uw =>
          if panics then
            if blk.cleanup then .det (st'.fin (.abort .inCleanup))
            else
              match uw with
              | .continueUnwind => .det (st'.fin .unwind)
              | .cleanup c => runV os q n c st'
          else runV os q n next st'
        | .drop l next =>
          match st'.loc l with
          | some _ => runV os q n next (st'.set l none)
          | none => .det (st'.fin .ub)
        | .terminate r => .det (st'.fin (.abort r))
        | .unreachable => .det (st'.fin .ub)

def VProg.fuel (q : VProg) : Nat := q.blocks.length + 1

/-- Verifier semantics: the runs admitted by the verifier result on each input. -/
def semV (os : OpaqueSem) (q : VProg) : Den Run :=
  fun r => (runV os q q.fuel 0 (St.init r.1)).admits r.2

instance (r : VRes) (b : Beh) : Decidable (r.admits b) :=
  match r with
  | .det b' => inferInstanceAs (Decidable (b' = b))
  | .top => inferInstanceAs (Decidable True)

instance (os : OpaqueSem) (q : VProg) : DecidablePred (semV os q) :=
  fun r => inferInstanceAs (Decidable ((runV os q q.fuel 0 (St.init r.1)).admits r.2))

/-! ## Captures -/

/-- Why a capture failed. -/
inductive CapErr where
  | unmodeledStmt
  | unmodeledTerm
  | erroneousConst
  deriving DecidableEq, Repr

/-- Capture configuration. The fail-closed capture `capFC` uses `cfgFC`; each
fail-open or lossy variant changes exactly one field. -/
structure CapCfg where
  /-- default: map `trap next` to `goto next` (a no-op) instead of failing. -/
  defaultTrap : Bool
  /-- stringify: map `asm c` to `opaque c` instead of failing. -/
  stringifyAsm : Bool
  /-- swallow: map an erroneous constant to the value `0` instead of failing. -/
  swallowErrConst : Bool
  /-- keep the cleanup mark of each block (otherwise every block is marked
  normal). -/
  keepCleanup : Bool
  /-- keep the terminate reason (otherwise every reason becomes `abi`). -/
  keepReason : Bool
  deriving DecidableEq, Repr

def capOperand (c : CapCfg) : SOperand → Except CapErr VOperand
  | .copy l => .ok (.copy l)
  | .const (.val n) => .ok (.const n)
  | .const .err => if c.swallowErrConst then .ok (.const 0) else .error .erroneousConst

def capStmt (c : CapCfg) : SStmt → Except CapErr VStmt
  | .assign d o =>
    match capOperand c o with
    | .ok vo => .ok (.assign d vo)
    | .error e => .error e
  | .placeMention l => .ok (.placeMention l)
  | .zstRead l => .ok (.zstRead l)
  | .emit o =>
    match capOperand c o with
    | .ok vo => .ok (.emit vo)
    | .error e => .error e
  | .asm t => if c.stringifyAsm then .ok (.opaque t) else .error .unmodeledStmt

def capStmts (c : CapCfg) : List SStmt → Except CapErr (List VStmt)
  | [] => .ok []
  | s :: ss =>
    match capStmt c s, capStmts c ss with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

/-- Capture a terminator. The drop replace flag is not represented in the verifier
IR and is forgotten. -/
def capTerm (c : CapCfg) : STerm → Except CapErr VTerm
  | .goto t => .ok (.goto t)
  | .switchInt o ts ow =>
    match capOperand c o with
    | .ok vo => .ok (.switchInt vo ts ow)
    | .error e => .error e
  | .ret => .ok .ret
  | .resume => .ok .resume
  | .call pa nx uw => .ok (.call pa nx uw)
  | .drop _ l nx => .ok (.drop l nx)
  | .terminate r => .ok (.terminate (if c.keepReason then r else .abi))
  | .trap nx => if c.defaultTrap then .ok (.goto nx) else .error .unmodeledTerm
  | .unreachable => .ok .unreachable

def capBlock (c : CapCfg) (b : SBlock) : Except CapErr VBlock :=
  match capStmts c b.stmts, capTerm c b.term with
  | .ok ss, .ok t => .ok ⟨ss, t, if c.keepCleanup then b.cleanup else false⟩
  | .error e, _ => .error e
  | .ok _, .error e => .error e

def capBlocks (c : CapCfg) : List SBlock → Except CapErr (List VBlock)
  | [] => .ok []
  | b :: bs =>
    match capBlock c b, capBlocks c bs with
    | .ok v, .ok vs => .ok (v :: vs)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

def capWith (c : CapCfg) (p : SProg) : Except CapErr VProg :=
  match capBlocks c p.blocks with
  | .ok bs => .ok ⟨bs⟩
  | .error e => .error e

/-- The fail-closed configuration: unmodeled constructs and erroneous constants
yield errors; all metadata is kept. -/
def cfgFC : CapCfg :=
  { defaultTrap := false, stringifyAsm := false, swallowErrConst := false,
    keepCleanup := true, keepReason := true }

/-- The fail-closed capture. -/
def capFC : SProg → Except CapErr VProg := capWith cfgFC
/-- Fail-open variant "default": `trap next` becomes `goto next`. -/
def capDefault : SProg → Except CapErr VProg := capWith { cfgFC with defaultTrap := true }
/-- Fail-open variant "stringify": `asm c` becomes `opaque c`. -/
def capStringify : SProg → Except CapErr VProg := capWith { cfgFC with stringifyAsm := true }
/-- Fail-open variant "swallow": an erroneous constant becomes `0`. -/
def capSwallow : SProg → Except CapErr VProg := capWith { cfgFC with swallowErrConst := true }
/-- Lossy variant: every block is marked normal. -/
def capNoCleanup : SProg → Except CapErr VProg := capWith { cfgFC with keepCleanup := false }
/-- Lossy variant: every terminate reason becomes `abi`. -/
def capNoReason : SProg → Except CapErr VProg := capWith { cfgFC with keepReason := false }

/-! ## Passes -/

def SStmt.isPlaceMention : SStmt → Bool
  | .placeMention _ => true
  | _ => false

def SStmt.isZstRead : SStmt → Bool
  | .zstRead _ => true
  | _ => false

/-- Remove every place mention (a UB-erasing pass). -/
def erasePlaceMentions (p : SProg) : SProg :=
  ⟨p.blocks.map fun b => { b with stmts := b.stmts.filter fun s => !s.isPlaceMention }⟩

/-- Remove every zero-size read (a UB-erasing pass). -/
def eraseZstReads (p : SProg) : SProg :=
  ⟨p.blocks.map fun b => { b with stmts := b.stmts.filter fun s => !s.isZstRead }⟩

/-- Replace every switch whose targets all equal its `otherwise` label, and whose
operand is not an erroneous constant, by a goto to that label (a UB-erasing pass:
the operand read disappears). Switches on an erroneous constant are kept, so the
pass never removes a `constErr` outcome. -/
def simplifyTrivialSwitches (p : SProg) : SProg :=
  ⟨p.blocks.map fun b =>
    { b with term :=
        match b.term with
        | .switchInt o ts ow =>
          if o != .const .err && ts.all (· == ow) then .goto ow else .switchInt o ts ow
        | t => t }⟩

/-- Clear the drop replace flag of a block's terminator. -/
def clearReplaceBlock (b : SBlock) : SBlock :=
  { b with term :=
      match b.term with
      | .drop _ l nx => .drop false l nx
      | t => t }

/-- Clear every drop replace flag (an equivalence: the flag has no operational
effect in the toy). -/
def clearReplace (p : SProg) : SProg :=
  ⟨p.blocks.map clearReplaceBlock⟩

/-! ## Specifications -/

/-- The outcome is an abort (with any reason). -/
def Outcome.isAbort : Outcome → Bool
  | .abort _ => true
  | _ => false

/-- No run is UB. -/
def ubFree : Run → Prop := fun r => r.2.out ≠ .ub
/-- The run returns normally. -/
def returnsNormally : Run → Prop := fun r => r.2.out = .ret
/-- The run produces no output. -/
def silent : Run → Prop := fun r => r.2.trace = []
/-- The run does not abort (with any reason). -/
def noAbort : Run → Prop := fun r => r.2.out.isAbort = false
/-- The run does not abort with reason `inCleanup`. -/
def noAbortInCleanup : Run → Prop := fun r => r.2.out ≠ .abort .inCleanup

instance : DecidablePred ubFree := fun r => inferInstanceAs (Decidable (r.2.out ≠ .ub))
instance : DecidablePred returnsNormally := fun r => inferInstanceAs (Decidable (r.2.out = .ret))
instance : DecidablePred silent := fun r => inferInstanceAs (Decidable (r.2.trace = []))
instance : DecidablePred noAbort := fun r => inferInstanceAs (Decidable (r.2.out.isAbort = false))
instance : DecidablePred noAbortInCleanup :=
  fun r => inferInstanceAs (Decidable (r.2.out ≠ .abort .inCleanup))

end Toy.Capture
