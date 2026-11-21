/-!
# A toy frame-stack machine with guaranteed tail calls

Each function has parameters and locals (together: *slots*, parameters first). A slot may
carry a destructor that emits an observable `drop` event when the slot's owned value is
destroyed. Terminators include `call`, `ret`, `tailCall` and `panic`. A pointer
`addrOf s` names a slot of the current frame by the frame's unique identity; a load through
a pointer whose frame is no longer on the stack is undefined behaviour (outcome `ub`).

The same machine is run under four semantics for `tailCall f args` (`Sem`):
* `callReturn` (A): behaves as `y := f(args); return y`;
* `preJump` (A′): evaluate the arguments, drop the frame's remaining owned slots in reverse
  declaration order, then call `f`; the finalized frame stays on the stack and forwards the
  result when `f` returns;
* `frameReuse` (B): as `preJump`, but the current frame is popped before `f` is pushed, so
  `f` returns directly to the current frame's caller;
* `popFirst`: an incorrect variant of `frameReuse` that removes the frame from the stack before
  its pending destructors run. A destructor takes its slot by reference (the toy counterpart of
  `Drop::drop(&mut self)`): it reaches the slot through the frame's identity, exactly as a
  `deref` does, so once the frame is gone the first pending destructor is `ub`.

A stack bound `D : Option Nat` (`none` = unbounded) limits the number of frames; a push
beyond it halts with outcome `stackOverflow`.

Destructors are atomic: running one is a single event inside one `step` (it emits `drop v`, or
emits it and starts a panic). A destructor pushes no frame, executes no instructions and reads
or writes no slot of any frame.

This is a toy model. It is meant to capture the frame discipline of a guaranteed tail call
(a MIR-like `TailCall` terminator); it does not model types, heap memory, stores through
pointers, borrow checking, or any real calling convention.
-/

namespace Toy.TailCall

abbrev FnId := Nat
abbrev Slot := Nat

/-- Runtime values: natural numbers, pointers to a slot of a frame (identified by its unique
frame id), and the content of a never-written slot. -/
inductive Val where
  | int (n : Nat)
  | ptr (fid : Nat) (slot : Slot)
  | undef
  deriving DecidableEq, Repr

/-- The observable content of a value. Events and final results record only this number, so
frame identities (which differ between a program and its inlined version) are not
observable: pointers and `undef` both observe as `0`. -/
def Val.obs : Val → Nat
  | .int n => n
  | _ => 0

/-- Operands, evaluated in the current (top) frame. `move s` reads slot `s` and clears its
drop flag; `addrOf s` yields a pointer to slot `s` of the current frame; `deref s` loads
through the pointer held in slot `s`; `succ s` is `n + 1` for an integer slot. -/
inductive Operand where
  | const (n : Nat)
  | copy (s : Slot)
  | move (s : Slot)
  | addrOf (s : Slot)
  | deref (s : Slot)
  | succ (s : Slot)
  deriving DecidableEq, Repr

/-- Instructions; every non-terminator names its successor `pc` explicitly.
* `reset ss` makes the slots `ss` unowned and `undef` without running destructors (a
  storage-live marker, used by the inliner for the callee's slots);
* `dropSlots ss` runs the destructors of those slots of `ss` that still own a value, in the
  given order (used by the inliner to finalize the callee's slots). -/
inductive Instr where
  | assign (dst : Slot) (op : Operand) (next : Nat)
  | emit (k : Nat) (next : Nat)
  | branchLt (s : Slot) (k : Nat) (thenPc elsePc : Nat)
  | goto (next : Nat)
  | reset (ss : List Slot) (next : Nat)
  | dropSlots (ss : List Slot) (next : Nat)
  | call (f : FnId) (args : List Operand) (dst : Slot) (next : Nat)
  | ret (op : Operand)
  | tailCall (f : FnId) (args : List Operand)
  | panic
  deriving DecidableEq, Repr

/-- What happens when the destructor of a slot runs: nothing to run, run and return, or run
(emitting its event) and then panic. -/
inductive DtorKind where
  | none
  | quiet
  | panics
  deriving DecidableEq, Repr

/-- A function: `nParams` parameters, one destructor kind per slot (parameters first, so
`dtors.length` is the number of slots), and its code (entry `pc` 0). -/
structure Fn where
  nParams : Nat
  dtors : List DtorKind
  code : List Instr
  deriving DecidableEq, Repr

def Fn.nSlots (fn : Fn) : Nat := fn.dtors.length

def Fn.dtor (fn : Fn) (s : Slot) : DtorKind := fn.dtors.getD s .none

/-- A program; function `0` is the entry point and is called with no arguments. -/
structure Prog where
  fns : List Fn
  deriving DecidableEq, Repr

/-- Observable events: `out k` from `emit k`; `drop v` when a destructor runs on a slot whose
value has observable content `v`. -/
inductive Event where
  | out (k : Nat)
  | drop (v : Nat)
  deriving DecidableEq, Repr

/-- How a frame resumes when the frame above it returns a value: store it and continue
(after `call`), or return it in turn (after a `tailCall` under `callReturn`/`preJump`). -/
inductive Cont where
  | store (dst : Slot) (next : Nat)
  | thenReturn
  deriving DecidableEq, Repr

/-- A stack frame. `live s` is the drop flag of slot `s` (it owns a value not yet moved out
or dropped). `pendingRet = some v` means the frame is about to return `v`. -/
structure Frame where
  fid : Nat
  fn : FnId
  pc : Nat
  vals : List Val
  live : List Bool
  cont : Cont
  pendingRet : Option Val
  deriving DecidableEq, Repr

def Frame.get (fr : Frame) (s : Slot) : Val := fr.vals.getD s .undef

def Frame.isLive (fr : Frame) (s : Slot) : Bool := fr.live.getD s false

def Frame.write (fr : Frame) (s : Slot) (v : Val) : Frame :=
  { fr with vals := fr.vals.set s v, live := fr.live.set s true }

def Frame.kill (fr : Frame) (s : Slot) : Frame := { fr with live := fr.live.set s false }

def Frame.clear (fr : Frame) (s : Slot) : Frame :=
  { fr with vals := fr.vals.set s .undef, live := fr.live.set s false }

/-- Machine state. The head of `stack` is the running frame. `maxDepth` is the largest stack
length reached; `tailCalls` counts executed tail-call jumps (callee frame pushed). -/
structure State where
  stack : List Frame
  nextFid : Nat
  events : List Event
  maxDepth : Nat
  tailCalls : Nat
  unwinding : Bool
  deriving DecidableEq, Repr

inductive Outcome where
  | returned (n : Nat)
  | panicked
  | aborted
  | ub
  | stackOverflow
  deriving DecidableEq, Repr

structure Result where
  outcome : Outcome
  events : List Event
  maxDepth : Nat
  tailCalls : Nat
  deriving DecidableEq, Repr

inductive Conf where
  | running (st : State)
  | halted (r : Result)
  deriving DecidableEq, Repr

/-- The four semantics of `tailCall` (see the module docstring). -/
inductive Sem where
  | callReturn
  | preJump
  | frameReuse
  | popFirst
  deriving DecidableEq, Repr

def State.halt (st : State) (o : Outcome) : Conf :=
  .halted ⟨o, st.events, st.maxDepth, st.tailCalls⟩

/-- Find a live frame by identity. -/
def findFrame (stk : List Frame) (fid : Nat) : Option Frame := stk.find? (·.fid == fid)

/-- Evaluate an operand in the top frame `fr` (frames `below` underneath). `none` is UB:
an out-of-range slot, a load through a non-pointer or through a pointer whose frame is not
on the stack, or `succ` of a non-integer. -/
def evalOp (below : List Frame) (fr : Frame) : Operand → Option (Val × Frame)
  | .const n => some (.int n, fr)
  | .copy s => if s < fr.vals.length then some (fr.get s, fr) else none
  | .move s => if s < fr.vals.length then some (fr.get s, fr.kill s) else none
  | .addrOf s => if s < fr.vals.length then some (.ptr fr.fid s, fr) else none
  | .deref s =>
    match fr.get s with
    | .ptr fid j =>
      match findFrame (fr :: below) fid with
      | some g => if j < g.vals.length then some (g.get j, fr) else none
      | none => none
    | _ => none
  | .succ s =>
    match fr.get s with
    | .int n => some (.int (n + 1), fr)
    | _ => none

/-- Evaluate operands left to right, threading the frame (moves clear drop flags). -/
def evalOps (below : List Frame) : Frame → List Operand → Option (List Val × Frame)
  | fr, [] => some ([], fr)
  | fr, o :: os =>
    match evalOp below fr o with
    | none => none
    | some (v, fr') =>
      match evalOps below fr' os with
      | none => none
      | some (vs, fr'') => some (v :: vs, fr'')

/-- Slots of `fr` that still own a value with a destructor, in reverse declaration order
(so locals before parameters, and moved-from slots skipped). -/
def pendingDrops (fn : Fn) (fr : Frame) : List Slot :=
  (List.range fr.vals.length).reverse.filter (fun s => fr.isLive s && fn.dtor s != .none)

inductive DropEnd where
  | ok
  | unwind
  | abort
  deriving DecidableEq, Repr

/-- Run the destructors of `ss` in order. `unw` records whether a panic is propagating. In
normal mode a panicking destructor starts unwinding and the remaining slots are still
dropped (in the same order); a destructor that panics while unwinding aborts. -/
def dropList (fn : Fn) : Frame → List Slot → Bool → Frame × List Event × DropEnd
  | fr, [], unw => (fr, [], if unw then .unwind else .ok)
  | fr, s :: ss, unw =>
    let ev := Event.drop (fr.get s).obs
    let fr1 := fr.kill s
    if fn.dtor s == .panics then
      if unw then (fr1, [ev], .abort)
      else
        let r := dropList fn fr1 ss true
        (r.1, ev :: r.2.1, r.2.2)
    else
      let r := dropList fn fr1 ss unw
      (r.1, ev :: r.2.1, r.2.2)

/-- Whether the bound `D` forbids pushing a frame on a stack of length `n`. -/
def overflows (D : Option Nat) (n : Nat) : Bool :=
  match D with
  | some d => decide (d ≤ n)
  | none => false

/-- Push a fresh frame for `f` with arguments `args` on the stack `stk`. -/
def push (D : Option Nat) (p : Prog) (st : State) (stk : List Frame) (f : FnId)
    (args : List Val) : Conf :=
  match p.fns[f]? with
  | none => st.halt .ub
  | some fn =>
    if args.length != fn.nParams || fn.nSlots < fn.nParams then st.halt .ub
    else if overflows D stk.length then st.halt .stackOverflow
    else
      let k := fn.nSlots - fn.nParams
      let fr : Frame := ⟨st.nextFid, f, 0, args ++ List.replicate k .undef,
        List.replicate fn.nParams true ++ List.replicate k false, .thenReturn, none⟩
      .running { st with stack := fr :: stk, nextFid := st.nextFid + 1,
                         maxDepth := max st.maxDepth (stk.length + 1) }

/-- Deliver the value `v` returned by a popped frame to the stack `stk` below it. -/
def deliver (st : State) (stk : List Frame) (v : Val) : Conf :=
  match stk with
  | [] => st.halt (.returned v.obs)
  | g :: rest =>
    match g.cont with
    | .store dst next => .running { st with stack := { g.write dst v with pc := next } :: rest }
    | .thenReturn => .running { st with stack := { g with pendingRet := some v } :: rest }

/-- Continue unwinding below a frame that has just been popped. -/
def unwindBelow (st : State) (rest : List Frame) : Conf :=
  match rest with
  | [] => st.halt .panicked
  | _ => .running { st with stack := rest, unwinding := true }

/-- Return `v` from the top frame `fr`: drop its owned slots (reverse declaration order),
pop it, and deliver `v`. -/
def doReturn (st : State) (fn : Fn) (fr : Frame) (rest : List Frame) (v : Val) : Conf :=
  let r := dropList fn fr (pendingDrops fn fr) false
  let st1 := { st with events := st.events ++ r.2.1 }
  match r.2.2 with
  | .ok => deliver st1 rest v
  | .unwind => unwindBelow st1 rest
  | .abort => st1.halt .aborted

def bumpTail : Conf → Conf
  | .running st => .running { st with tailCalls := st.tailCalls + 1 }
  | c => c

/-- Execute `tailCall f` with evaluated arguments `vs` from frame `fr` (after argument
evaluation), under semantics `sem`. -/
def doTailCall (sem : Sem) (D : Option Nat) (p : Prog) (st : State) (fn : Fn) (fr : Frame)
    (rest : List Frame) (f : FnId) (vs : List Val) : Conf :=
  match sem with
  | .callReturn => bumpTail (push D p st ({ fr with cont := .thenReturn } :: rest) f vs)
  | .preJump =>
    let r := dropList fn fr (pendingDrops fn fr) false
    let st1 := { st with events := st.events ++ r.2.1 }
    match r.2.2 with
    | .ok => bumpTail (push D p st1 ({ r.1 with cont := .thenReturn } :: rest) f vs)
    | .unwind => unwindBelow st1 rest
    | .abort => st1.halt .aborted
  | .frameReuse =>
    let r := dropList fn fr (pendingDrops fn fr) false
    let st1 := { st with events := st.events ++ r.2.1 }
    match r.2.2 with
    | .ok => bumpTail (push D p st1 rest f vs)
    | .unwind => unwindBelow st1 rest
    | .abort => st1.halt .aborted
  | .popFirst =>
    -- The frame is already off the stack; `rest` remains. A pending destructor reaches
    -- its slot through the frame identity `fr.fid`, which `findFrame` resolves as for `deref`.
    if !(pendingDrops fn fr).isEmpty && (findFrame rest fr.fid).isNone then st.halt .ub
    else
      let r := dropList fn fr (pendingDrops fn fr) false
      let st1 := { st with events := st.events ++ r.2.1 }
      match r.2.2 with
      | .ok => bumpTail (push D p st1 rest f vs)
      | .unwind => unwindBelow st1 rest
      | .abort => st1.halt .aborted

/-- One step of the machine. -/
def step (sem : Sem) (D : Option Nat) (p : Prog) (st : State) : Conf :=
  match st.stack with
  | [] => st.halt .ub
  | fr :: rest =>
    match p.fns[fr.fn]? with
    | none => st.halt .ub
    | some fn =>
      if st.unwinding then
        let r := dropList fn fr (pendingDrops fn fr) true
        let st1 := { st with events := st.events ++ r.2.1 }
        match r.2.2 with
        | .abort => st1.halt .aborted
        | _ =>
          match rest with
          | [] => st1.halt .panicked
          | _ => .running { st1 with stack := rest }
      else
      match fr.pendingRet with
      | some v => doReturn st fn fr rest v
      | none =>
      match fn.code[fr.pc]? with
      | none => st.halt .ub
      | some i =>
      match i with
      | .assign dst op next =>
        match evalOp rest fr op with
        | none => st.halt .ub
        | some (v, fr1) =>
          if dst < fr1.vals.length then
            .running { st with stack := { fr1.write dst v with pc := next } :: rest }
          else st.halt .ub
      | .emit k next =>
        .running { st with stack := { fr with pc := next } :: rest,
                           events := st.events ++ [.out k] }
      | .branchLt s k t e =>
        match fr.get s with
        | .int n => .running { st with stack := { fr with pc := if n < k then t else e } :: rest }
        | _ => st.halt .ub
      | .goto next => .running { st with stack := { fr with pc := next } :: rest }
      | .reset ss next =>
        .running { st with stack := { ss.foldl Frame.clear fr with pc := next } :: rest }
      | .dropSlots ss next =>
        let r := dropList fn fr (ss.filter (fun s => fr.isLive s && fn.dtor s != .none)) false
        let st1 := { st with events := st.events ++ r.2.1 }
        match r.2.2 with
        | .ok => .running { st1 with stack := { r.1 with pc := next } :: rest }
        | .unwind => .running { st1 with stack := r.1 :: rest, unwinding := true }
        | .abort => st1.halt .aborted
      | .call f args dst next =>
        match evalOps rest fr args with
        | none => st.halt .ub
        | some (vs, fr1) =>
          if dst < fr1.vals.length then
            push D p st ({ fr1 with cont := .store dst next } :: rest) f vs
          else st.halt .ub
      | .ret op =>
        match evalOp rest fr op with
        | none => st.halt .ub
        | some (v, fr1) => doReturn st fn fr1 rest v
      | .tailCall f args =>
        match evalOps rest fr args with
        | none => st.halt .ub
        | some (vs, fr1) => doTailCall sem D p st fn fr1 rest f vs
      | .panic => .running { st with unwinding := true }

/-- Run for at most `n` steps. -/
def run (sem : Sem) (D : Option Nat) (p : Prog) : Nat → Conf → Conf
  | 0, c => c
  | n + 1, .running st => run sem D p n (step sem D p st)
  | _ + 1, .halted r => .halted r

def State.empty : State := ⟨[], 0, [], 0, 0, false⟩

/-- The initial configuration: function `0` called with no arguments. -/
def start (D : Option Nat) (p : Prog) : Conf := push D p State.empty [] 0 []

/-- `sem` runs `p` under bound `D` to a halted result `r`. -/
def RunsTo (sem : Sem) (D : Option Nat) (p : Prog) (r : Result) : Prop :=
  ∃ n, run sem D p n (start D p) = .halted r

/-- `sem` runs `p` under bound `D` to outcome `o` with event trace `es` (depth and tail-call
counters ignored). -/
def Observes (sem : Sem) (D : Option Nat) (p : Prog) (o : Outcome) (es : List Event) : Prop :=
  ∃ r, RunsTo sem D p r ∧ r.outcome = o ∧ r.events = es

/-- No function of `p` contains a `call` instruction, so every run of `p` is a single chain of
tail calls starting from the entry function. -/
def CallFree (p : Prog) : Bool :=
  p.fns.all fun fn => fn.code.all fun i =>
    match i with
    | .call .. => false
    | _ => true

/-- The entry function exists and takes no parameters (so `start` pushes one frame). -/
def EntryOk (p : Prog) : Prop := ∃ fn, p.fns[0]? = some fn ∧ fn.nParams = 0

/-- Halted configurations are fixed points of `run`. -/
theorem run_halted (sem : Sem) (D : Option Nat) (p : Prog) (n : Nat) (r : Result) :
    run sem D p n (.halted r) = .halted r := by
  cases n <;> rfl

/-- Once halted within `n` steps, the run stays halted with the same result. -/
theorem run_mono (sem : Sem) (D : Option Nat) (p : Prog) :
    ∀ (n k : Nat) (c : Conf) (r : Result), run sem D p n c = .halted r →
      run sem D p (n + k) c = .halted r := by
  intro n
  induction n with
  | zero =>
    intro k c r h
    simp only [run] at h
    subst h
    rw [Nat.zero_add, run_halted]
  | succ n ih =>
    intro k c r h
    cases c with
    | halted r' => rw [run_halted] at h ⊢; exact h
    | running st =>
      rw [Nat.succ_add]
      exact ih k _ r h

/-- The machine is deterministic: a run halts with at most one result. -/
theorem runsTo_unique {sem : Sem} {D : Option Nat} {p : Prog} {r r' : Result}
    (h : RunsTo sem D p r) (h' : RunsTo sem D p r') : r = r' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := h'
  have a := run_mono sem D p n n' _ _ hn
  have b := run_mono sem D p n' n _ _ hn'
  rw [Nat.add_comm] at b
  rw [a] at b
  exact (Conf.halted.inj b).symm ▸ rfl

/-- If the run is known to halt with `r`, then it observes exactly `r`'s outcome and trace. -/
theorem observes_iff_of_runsTo {sem : Sem} {D : Option Nat} {p : Prog} {r : Result}
    (h : RunsTo sem D p r) (o : Outcome) (es : List Event) :
    Observes sem D p o es ↔ (r.outcome = o ∧ r.events = es) := by
  constructor
  · rintro ⟨r', h', ho, he⟩
    rw [runsTo_unique h h']
    exact ⟨ho, he⟩
  · rintro ⟨ho, he⟩
    exact ⟨r, h, ho, he⟩

/-- The events of a complete pre-jump finalization of frame `fr`: one `drop` per pending slot,
in `pendingDrops` order. -/
def finalizationEvents (fn : Fn) (fr : Frame) : List Event :=
  (pendingDrops fn fr).map fun s => Event.drop (fr.get s).obs

/-- The pending slots of `fr` whose destructor panics. -/
def panickingPending (fn : Fn) (fr : Frame) : List Slot :=
  (pendingDrops fn fr).filter fun s => fn.dtor s == .panics

/-- `st` is about to execute `tailCall f args` in frame `fr` (function `fn`, frames `rest`
below), and the arguments evaluate to `vs`, leaving the frame as `fr1` (moves applied). -/
structure AtTailCall (p : Prog) (st : State) (fn : Fn) (fr : Frame) (rest : List Frame)
    (f : FnId) (args : List Operand) (vs : List Val) (fr1 : Frame) : Prop where
  stack_eq : st.stack = fr :: rest
  not_unwinding : st.unwinding = false
  no_pendingRet : fr.pendingRet = none
  fn_eq : p.fns[fr.fn]? = some fn
  instr_eq : fn.code[fr.pc]? = some (.tailCall f args)
  args_eq : evalOps rest fr args = some (vs, fr1)

end Toy.TailCall
