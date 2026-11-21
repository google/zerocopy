# Explicit tail calls: frame reuse, pre-jump drop order, stack-borrow rejection, argument areas and inlining

## Summary

A Lean 4 formalization of a toy frame-stack machine with guaranteed tail calls, destructors, pointers into frames, a stack bound and inlining. Lean project: `lean/` (library `ToyTailCall`, namespaces `Toy.TailCall` and `Toy.TailCall.Layout`), Lean `v4.34.1`, core Lean without Mathlib. All 22 main theorems in `ToyTailCall/Results.lean` are kernel-checked, as are the definition examples (`Examples.lean`) and the counterexamples, non-vacuity witnesses and positive controls (`Counterexamples.lean`, `Converse.lean`); every declaration depends on at most the axioms `propext`, `Classical.choice` and `Quot.sound` (Evidence).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

* **R1** (theorem) — For every toy program `p` satisfying `NoStackBorrow p` (in the unbounded `preJump` run of `p`, no executed `tailCall` passes an argument value that is a pointer into the current frame), and for every outcome `o` and event trace `es`, the unbounded `frameReuse` run of `p` halts with `o` and `es` if and only if the unbounded `preJump` run of `p` does.
* **R2** (counterexample) — There is a toy program, `dtorProg`, that satisfies `NoStackBorrow` and whose unbounded `callReturn` run returns 0 with trace `[out 1, drop 7]` while its unbounded `frameReuse` run returns 0 with trace `[drop 7, out 1]`; so `frameReuse` does not refine `callReturn` on event traces even when no stack borrow is passed.
* **R3** (theorem) — For every toy program `p` satisfying `NoStackBorrow p` (a property of the unbounded `preJump` run of `p`), every stack bound `D` (including `none`), and every outcome `o` other than `stackOverflow` with trace `es`: if the `D`-bounded `preJump` run of `p` halts with `o` and `es`, then the `D`-bounded `frameReuse` run of `p` halts with `o` and `es`.
* **R4** (theorem) — For every `N`, the self-tail-recursive toy program `countUp N` (the entry calls `rec 0`; `rec n` returns 0 when `n ≥ N`, and otherwise owns a local with value `n` whose destructor emits `drop n` and tail-calls `rec (n + 1)`) returns 0 with exactly `N` tail-call jumps under each of the three unbounded semantics `frameReuse`, `preJump` and `callReturn`, with: `frameReuse` — trace `drop 0, …, drop (N-1)` and maximum depth exactly 2; `preJump` — the same trace and maximum depth exactly `N + 2`; `callReturn` — trace `drop (N-1), …, drop 0` and maximum depth exactly `N + 2` (each trace is `[]` when `N = 0`; the Lean terms use `List.range N`, so no truncated subtraction occurs).
* **R5** (theorem) — For every call-free toy program (`CallFree p`: no `call` instruction in any function of `p`, reachable or not) whose entry function exists and takes no parameters (`EntryOk p`), every halted unbounded `frameReuse` run has maximum depth exactly 1, and every halted unbounded `preJump` run has maximum depth equal to its number of tail-call jumps plus 1.
* **R6** (characterization) — For every function `fn` and frame `fr`, a slot `s` is in `pendingDrops fn fr` exactly when `s < fr.vals.length`, the drop flag of `s` is set (`fr.isLive s = true`), and the destructor kind of `s` is not `none`; and `pendingDrops fn fr` lists slots in strictly decreasing order.
* **R7** (counterexample) — Without `NoStackBorrow` the equivalence of R1 fails: in `borrowProg` (`t` does `become reader(&local)` and `reader` loads through its argument) `NoStackBorrow` does not hold, the unbounded `preJump` run returns 5 with an empty trace, the unbounded `frameReuse` run halts with `ub` and an empty trace, and the two runs do not have the same outcomes and traces.
* **R8** (theorem) — For every toy program `p`, if the flow-insensitive escape check accepts `p` (`EscapeCheckAccepts p = true`: in every function, no `tailCall` argument is an `addrOf` operand or reads a slot that may hold an `addrOf`-derived value, where taint flows through `assign` and through `call` results with a tainted argument), then `p` satisfies `NoStackBorrow`.
* **R9** (counterexample) — The escape check is incomplete: it rejects `deadEscape` (an address is stored in a slot and overwritten with 0 before the tail call passes that slot), although `deadEscape` satisfies `NoStackBorrow`.
* **R10** (characterization) — In the layout toy, at a fixed frame boundary `b` (no return-address relocation and no stack-pointer adjustment before the jump), for all incoming-area sizes `inG` (current function) and `inH` (callee): frame reuse is sound under caller cleanup iff `inH ≤ inG`, and sound under callee cleanup iff `inH = inG` (`ReuseSound`: for every memory, frame base `b` and list of exactly `inH` argument cells, no cell below `b - inG` changes, the callee reads back its arguments from `[b - inH, b)`, and the caller sees stack pointer `b - inG` after the return).
* **R11** (theorem) — In the layout toy, at a fixed frame boundary, for all signatures `g` and `h`: if `sigCheckFull g h = true` (equal explicit parameters and equal hidden caller-location parameter), then frame reuse is sound for their incoming-area sizes under either cleanup convention.
* **R12** (counterexample) — In the layout toy, at a fixed frame boundary, comparing explicit parameters is not enough: for `g = ⟨[1], false⟩` and `h = ⟨[1], true⟩`, `sigCheckExplicit g h = true` and `sigCheckFull g h = false`, and frame reuse is unsound for their area sizes (exactly 1 and exactly 2) under both cleanup conventions (the callee's extra cell overwrites the caller's frame).
* **R13** (counterexample) — In the layout toy, at a fixed frame boundary, when the current function has the hidden caller-location parameter and the callee lacks it (`g = ⟨[1], true⟩`, `h = ⟨[1], false⟩`), `sigCheckExplicit g h = true` and `sigCheckFull g h = false`, and frame reuse is sound under caller cleanup and unsound under callee cleanup.
* **R14** (counterexample) — The naive splice, which keeps the callee's `tailCall`, changes behaviour at a `call` site: in `inlEx` (`main` owns 9, calls `g`, then emits `out 2`; `g` tail-calls `h`, which emits `out 1`) the unbounded `frameReuse` run returns 0 with trace `[out 1, out 2, drop 9]`, while after `inlineCallSite .naive inlEx 0 1` it returns 0 with trace `[drop 9, out 1]`: the kept `tailCall` finalizes and pops `main`'s frame, so `main`'s continuation is lost.
* **R15** (theorem) — For every toy program `p`, call site (function `ci`, pc `k`), stack bound `D` (including `none`), outcome `o` that is neither `ub` nor `stackOverflow`, and trace `es`: if the `D`-bounded `frameReuse` run of `p` halts with `o` and `es`, then so does the `D`-bounded `frameReuse` run of `inlineCallSite .corrected p ci k` (the callee's `tailCall h args` rewritten to: arguments into fresh temporaries, `dropSlots` of the callee's slots in reverse declaration order, then `call h` with the call site's destination slot `dst` and continuation pc `next`).
* **R16** (theorem) — For every `N`, the unbounded `frameReuse` run of `mutualRec N` (mutual tail recursion `c ↔ g`, exactly `N` rounds of the pair, no destructors) returns 0 with empty trace, maximum depth exactly 2 and exactly `2 * N` jumps, while the unbounded `frameReuse` run of `inlineTailSite .corrected (mutualRec N) 1 1` (`g` spliced into `c`'s tail site after rewriting that tail call into its pre-jump reading as code) returns 0 with empty trace, maximum depth exactly `N + 2` and no jumps; and for every `C`, under stack bound `some (2 + C)` the `frameReuse` run of `mutualRec (C + 1)` returns 0 with empty trace while that of its corrected tail-site splice halts with `stackOverflow` and empty trace.
* **R17** (theorem) — (a) For every function `fn` and frame `fr`, if finalizing `fr`'s pending slots does not abort, no pending drop remains in the resulting frame; (b) for every state `st` about to execute `tailCall f args` under `frameReuse` (any bound `D`) — not unwinding, with no pending return, and with the arguments evaluating without `ub` to values `vs` and evaluated frame `fr1` — if no pending destructor of `fr1` panics, the step emits `finalizationEvents fn fr1` (one `drop` per pending slot, in `pendingDrops` order), then performs `push` of `f` with `vs` onto the frames below the current one (the current frame is no longer on the stack), and, if that push succeeds, increments the tail-call counter (`bumpTail`).
* **R18** (theorem) — For every state `st` about to execute `tailCall f args` under `frameReuse` (any bound `D`) — not unwinding, with no pending return, and with the arguments evaluating without `ub` to evaluated frame `fr1` — if exactly one pending destructor of `fr1` panics, the step still emits one `drop` per slot pending in `fr1` (slots moved into the arguments are no longer pending), in `pendingDrops` order, removes the frame, and continues unwinding with the frames below (`unwindBelow`: the original caller's cleanup, or outcome `panicked` if there is none); the already-evaluated argument values are discarded without a `drop` event.
* **R19** (counterexample) — In the toy, where a destructor reaches its slot through the frame's identity (as a `deref` does, the counterpart of `Drop::drop(&mut self)`), removing the frame before its pending destructors run makes running them `ub`: for `dtorProg` the unbounded `frameReuse` run returns 0 with trace `[drop 7, out 1]`, while the `popFirst` run halts with `ub` and an empty trace.
* **R20** (characterization) — In the layout toy with the boundary moved by `δ` cells before the jump (callee area at `[b + δ - inH, b + δ)`), for all `δ`, `inG` and `inH`: `δ = 0` gives exactly the fixed-boundary `ReuseSound`; under callee cleanup frame reuse is sound iff `δ = inH - inG` (integer subtraction), so a suitable relocation exists for all area sizes; under caller cleanup it is sound iff `δ = 0` and `inH ≤ inG`, so relocation does not help.

The non-claims of every result are listed under Boundaries, result by result; each result must be read together with them.

## Applicability

**Model fidelity.** A toy frame-stack machine meant to capture the frame discipline of a guaranteed tail call (a MIR-like `TailCall` terminator: pop the current frame, then call with the current caller's return address), destructors that emit observable events, pointers into frames, a stack bound, and inlining. It does not mirror any compiler's data structures. Known gaps: no heap, no stores through pointers, no types, no borrow checker, no catching of panics; destructors are atomic single-step events (`DtorKind`) that push no frame, execute no instruction and read or write no slot (so they cannot call functions or dereference pointers; the `popFirst` variant models a destructor's access to its own slot and nothing else); assignment over an owned slot does not drop the old value; a load from a dropped slot is not flagged; frame identities are unobservable by design (`Val.obs`); and the argument-area question is answered in a separate layout toy with no proved relation to the machine. Connections to rustc are separate `derived (modeling bridge)` claims (Findings, modeling bridge).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

**Toolchain.** Lean `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std` without Mathlib; the Lake project in `lean/` has no `require` and builds on its own.

**Subjects and their relation.** The Lean toolchain is the checker of every theorem in this package. The rustc, CompCert and LLVM revisions listed under Evidence are sources of documentation and source text quoted verbatim in the modeling bridge (Findings); nothing from them was executed or measured, and no toy definition mirrors their data structures. The papers listed under Evidence are prior art cited by the result cards; none of them is a dependency of any proof.

**Proof-support modules.** `Lemmas.lean`, `CountUpProof.lean`, `MutualRecProof.lean`, `CallFreeProof.lean`, `EscapeProof.lean`, `ReuseProof.lean` and the `Splice*.lean` modules contain proofs; no statement in them is cited here.

## Findings

### The model

The definitions that the results are stated with are quoted verbatim from the Lean sources, each with its file and line range.

#### Syntax and state (`Machine.lean`)

```lean
-- ToyTailCall/Machine.lean:36
abbrev FnId := Nat
-- ToyTailCall/Machine.lean:37
abbrev Slot := Nat
-- ToyTailCall/Machine.lean:41-45
inductive Val where
  | int (n : Nat)
  | ptr (fid : Nat) (slot : Slot)
  | undef
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:50-52
def Val.obs : Val → Nat
  | .int n => n
  | _ => 0
-- ToyTailCall/Machine.lean:57-64
inductive Operand where
  | const (n : Nat)
  | copy (s : Slot)
  | move (s : Slot)
  | addrOf (s : Slot)
  | deref (s : Slot)
  | succ (s : Slot)
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:71-82
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
-- ToyTailCall/Machine.lean:86-90
inductive DtorKind where
  | none
  | quiet
  | panics
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:94-98
structure Fn where
  nParams : Nat
  dtors : List DtorKind
  code : List Instr
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:100
def Fn.nSlots (fn : Fn) : Nat := fn.dtors.length
-- ToyTailCall/Machine.lean:102
def Fn.dtor (fn : Fn) (s : Slot) : DtorKind := fn.dtors.getD s .none
-- ToyTailCall/Machine.lean:105-107
structure Prog where
  fns : List Fn
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:111-114
inductive Event where
  | out (k : Nat)
  | drop (v : Nat)
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:118-121
inductive Cont where
  | store (dst : Slot) (next : Nat)
  | thenReturn
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:125-133
structure Frame where
  fid : Nat
  fn : FnId
  pc : Nat
  vals : List Val
  live : List Bool
  cont : Cont
  pendingRet : Option Val
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:135
def Frame.get (fr : Frame) (s : Slot) : Val := fr.vals.getD s .undef
-- ToyTailCall/Machine.lean:137
def Frame.isLive (fr : Frame) (s : Slot) : Bool := fr.live.getD s false
-- ToyTailCall/Machine.lean:139-140
def Frame.write (fr : Frame) (s : Slot) (v : Val) : Frame :=
  { fr with vals := fr.vals.set s v, live := fr.live.set s true }
-- ToyTailCall/Machine.lean:142
def Frame.kill (fr : Frame) (s : Slot) : Frame := { fr with live := fr.live.set s false }
-- ToyTailCall/Machine.lean:144-145
def Frame.clear (fr : Frame) (s : Slot) : Frame :=
  { fr with vals := fr.vals.set s .undef, live := fr.live.set s false }
-- ToyTailCall/Machine.lean:149-156
structure State where
  stack : List Frame
  nextFid : Nat
  events : List Event
  maxDepth : Nat
  tailCalls : Nat
  unwinding : Bool
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:158-164
inductive Outcome where
  | returned (n : Nat)
  | panicked
  | aborted
  | ub
  | stackOverflow
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:166-171
structure Result where
  outcome : Outcome
  events : List Event
  maxDepth : Nat
  tailCalls : Nat
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:173-176
inductive Conf where
  | running (st : State)
  | halted (r : Result)
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:179-184
inductive Sem where
  | callReturn
  | preJump
  | frameReuse
  | popFirst
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:186-187
def State.halt (st : State) (o : Outcome) : Conf :=
  .halted ⟨o, st.events, st.maxDepth, st.tailCalls⟩
-- ToyTailCall/Machine.lean:190
def findFrame (stk : List Frame) (fid : Nat) : Option Frame := stk.find? (·.fid == fid)
-- ToyTailCall/Machine.lean:195-210
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
-- ToyTailCall/Machine.lean:213-221
def evalOps (below : List Frame) : Frame → List Operand → Option (List Val × Frame)
  | fr, [] => some ([], fr)
  | fr, o :: os =>
    match evalOp below fr o with
    | none => none
    | some (v, fr') =>
      match evalOps below fr' os with
      | none => none
      | some (vs, fr'') => some (v :: vs, fr'')
```

* Slots are parameters first, then locals; `Fn.dtors` gives one destructor kind per slot. Parameters start owned (`live = true`); locals start `undef` and unowned.
* A pointer is `ptr fid slot`; a load through it (`deref`) is `ub` unless a frame with identity `fid` is on the stack and `slot` is in range.
* `Frame.kill` clears a drop flag and keeps the value, so a later load from a dropped slot is not flagged.

#### Finalization and the four semantics of `tailCall`

```lean
-- ToyTailCall/Machine.lean:225-226
def pendingDrops (fn : Fn) (fr : Frame) : List Slot :=
  (List.range fr.vals.length).reverse.filter (fun s => fr.isLive s && fn.dtor s != .none)
-- ToyTailCall/Machine.lean:228-232
inductive DropEnd where
  | ok
  | unwind
  | abort
  deriving DecidableEq, Repr
-- ToyTailCall/Machine.lean:237-249
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
-- ToyTailCall/Machine.lean:252-255
def overflows (D : Option Nat) (n : Nat) : Bool :=
  match D with
  | some d => decide (d ≤ n)
  | none => false
-- ToyTailCall/Machine.lean:258-270
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
-- ToyTailCall/Machine.lean:273-279
def deliver (st : State) (stk : List Frame) (v : Val) : Conf :=
  match stk with
  | [] => st.halt (.returned v.obs)
  | g :: rest =>
    match g.cont with
    | .store dst next => .running { st with stack := { g.write dst v with pc := next } :: rest }
    | .thenReturn => .running { st with stack := { g with pendingRet := some v } :: rest }
-- ToyTailCall/Machine.lean:282-285
def unwindBelow (st : State) (rest : List Frame) : Conf :=
  match rest with
  | [] => st.halt .panicked
  | _ => .running { st with stack := rest, unwinding := true }
-- ToyTailCall/Machine.lean:289-295
def doReturn (st : State) (fn : Fn) (fr : Frame) (rest : List Frame) (v : Val) : Conf :=
  let r := dropList fn fr (pendingDrops fn fr) false
  let st1 := { st with events := st.events ++ r.2.1 }
  match r.2.2 with
  | .ok => deliver st1 rest v
  | .unwind => unwindBelow st1 rest
  | .abort => st1.halt .aborted
-- ToyTailCall/Machine.lean:297-299
def bumpTail : Conf → Conf
  | .running st => .running { st with tailCalls := st.tailCalls + 1 }
  | c => c
-- ToyTailCall/Machine.lean:303-331
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
```

* `callReturn` (A): the frame stays with continuation `thenReturn`; when the callee returns, the frame returns in turn, dropping its owned slots then.
* `preJump` (A′): arguments evaluated (moves applied), then `dropList` over `pendingDrops`, then the callee is pushed on top of the finalized frame, which forwards the result.
* `frameReuse` (B): as `preJump`, but the callee is pushed on `rest` (the current frame is removed).
* `popFirst`: the frame is removed first; if some destructor is pending and the frame's identity is no longer found on the stack (`findFrame rest fr.fid = none`, the lookup a `deref` uses), the step halts with `ub`; otherwise it behaves as `frameReuse`.
* Stack bound: `push` halts with `stackOverflow` when `overflows D stk.length`; `none` is unbounded. With `D = some 0` the initial push already overflows.

```lean
-- ToyTailCall/Machine.lean:334-397
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
-- ToyTailCall/Machine.lean:400-403
def run (sem : Sem) (D : Option Nat) (p : Prog) : Nat → Conf → Conf
  | 0, c => c
  | n + 1, .running st => run sem D p n (step sem D p st)
  | _ + 1, .halted r => .halted r
-- ToyTailCall/Machine.lean:405
def State.empty : State := ⟨[], 0, [], 0, 0, false⟩
-- ToyTailCall/Machine.lean:408
def start (D : Option Nat) (p : Prog) : Conf := push D p State.empty [] 0 []
-- ToyTailCall/Machine.lean:411-412
def RunsTo (sem : Sem) (D : Option Nat) (p : Prog) (r : Result) : Prop :=
  ∃ n, run sem D p n (start D p) = .halted r
-- ToyTailCall/Machine.lean:416-417
def Observes (sem : Sem) (D : Option Nat) (p : Prog) (o : Outcome) (es : List Event) : Prop :=
  ∃ r, RunsTo sem D p r ∧ r.outcome = o ∧ r.events = es
-- ToyTailCall/Machine.lean:431-432
theorem run_halted (sem : Sem) (D : Option Nat) (p : Prog) (n : Nat) (r : Result) :
    run sem D p n (.halted r) = .halted r := by
-- ToyTailCall/Machine.lean:436-438
theorem run_mono (sem : Sem) (D : Option Nat) (p : Prog) :
    ∀ (n k : Nat) (c : Conf) (r : Result), run sem D p n c = .halted r →
      run sem D p (n + k) c = .halted r := by
-- ToyTailCall/Machine.lean:455-456
theorem runsTo_unique {sem : Sem} {D : Option Nat} {p : Prog} {r r' : Result}
    (h : RunsTo sem D p r) (h' : RunsTo sem D p r') : r = r' := by
-- ToyTailCall/Machine.lean:466-468
theorem observes_iff_of_runsTo {sem : Sem} {D : Option Nat} {p : Prog} {r : Result}
    (h : RunsTo sem D p r) (o : Outcome) (es : List Event) :
    Observes sem D p o es ↔ (r.outcome = o ∧ r.events = es) := by
```

Definition examples (`Examples.lean`): the same program under each semantics, and `Observes` rejecting a trace the run does not produce.

```lean
-- ToyTailCall/Examples.lean:131-132
theorem dtorProg_callReturn : RunsTo .callReturn none dtorProg
    ⟨.returned 0, [.out 1, .drop 7], 3, 1⟩ := ⟨20, by decide⟩
-- ToyTailCall/Examples.lean:134-135
theorem dtorProg_preJump : RunsTo .preJump none dtorProg
    ⟨.returned 0, [.drop 7, .out 1], 3, 1⟩ := ⟨20, by decide⟩
-- ToyTailCall/Examples.lean:137-138
theorem dtorProg_frameReuse : RunsTo .frameReuse none dtorProg
    ⟨.returned 0, [.drop 7, .out 1], 2, 1⟩ := ⟨20, by decide⟩
-- ToyTailCall/Examples.lean:142
theorem dtorProg_popFirst : RunsTo .popFirst none dtorProg ⟨.ub, [], 2, 0⟩ := ⟨20, by decide⟩
-- ToyTailCall/Examples.lean:145-146
theorem not_observes_dtorProg_frameReuse_callReturnTrace :
    ¬ Observes .frameReuse none dtorProg (.returned 0) [.out 1, .drop 7] := by
```

`pendingDrops`: positive (reverse declaration order, moved-from slot skipped) and negative (a live slot without a destructor is never pending).

```lean
-- ToyTailCall/Examples.lean:154-157
theorem pendingDrops_orderDemo :
    pendingDrops ⟨2, [.quiet, .quiet, .quiet, .quiet, .quiet], []⟩
      ⟨1, 1, 3, [.int 10, .int 11, .int 12, .int 13, .int 14],
        [true, true, true, false, true], .thenReturn, none⟩ = [4, 2, 1, 0] := by decide
-- ToyTailCall/Examples.lean:160-162
theorem pendingDrops_skips_no_dtor :
    pendingDrops ⟨0, [.none, .quiet], []⟩ ⟨0, 0, 0, [.int 1, .int 2], [true, false], .thenReturn, none⟩
      = [] := by decide
```

#### Stack borrows (`Borrow.lean`)

```lean
-- ToyTailCall/Borrow.lean:11-15
def allRunning (pred : State → Bool) (sem : Sem) (D : Option Nat) (p : Prog) :
    Nat → Conf → Bool
  | _, .halted _ => true
  | 0, .running _ => false
  | n + 1, .running st => pred st && allRunning pred sem D p n (step sem D p st)
-- ToyTailCall/Borrow.lean:19-21
theorem allRunning_sound (pred : State → Bool) (sem : Sem) (D : Option Nat) (p : Prog) :
    ∀ (N : Nat) (c : Conf), allRunning pred sem D p N c = true →
      ∀ n st, run sem D p n c = .running st → pred st = true := by
-- ToyTailCall/Borrow.lean:40-42
def Val.pointsInto (fid : Nat) : Val → Bool
  | .ptr f _ => f == fid
  | _ => false
-- ToyTailCall/Borrow.lean:46-59
def tailCallBorrowsFrame (p : Prog) (st : State) : Bool :=
  match st.stack with
  | [] => false
  | fr :: rest =>
    if st.unwinding || fr.pendingRet.isSome then false else
    match p.fns[fr.fn]? with
    | none => false
    | some fn =>
      match fn.code[fr.pc]? with
      | some (.tailCall _ args) =>
        match evalOps rest fr args with
        | some (vs, _) => vs.any (Val.pointsInto fr.fid)
        | none => false
      | _ => false
-- ToyTailCall/Borrow.lean:68-69
def NoStackBorrow (p : Prog) : Prop :=
  ∀ n st, run .preJump none p n (start none p) = .running st → tailCallBorrowsFrame p st = false
-- ToyTailCall/Borrow.lean:73-75
theorem noStackBorrow_of_allRunning (p : Prog) (N : Nat)
    (h : allRunning (fun st => !tailCallBorrowsFrame p st) .preJump none p N (start none p) = true) :
    NoStackBorrow p := by
-- ToyTailCall/Borrow.lean:84-90
def opTainted (T : List Bool) : Operand → Bool
  | .const _ => false
  | .addrOf _ => true
  | .copy s => T.getD s false
  | .move s => T.getD s false
  | .deref s => T.getD s false
  | .succ s => T.getD s false
-- ToyTailCall/Borrow.lean:98-104
def taintStep (fn : Fn) (T : List Bool) : List Bool :=
  (List.range fn.nSlots).map fun d =>
    T.getD d false || fn.code.any fun i =>
      match i with
      | .assign d' op _ => d' == d && opTainted T op
      | .call _ args d' _ => d' == d && args.any (opTainted T)
      | _ => false
-- ToyTailCall/Borrow.lean:108-109
def taint (fn : Fn) : List Bool :=
  Nat.repeat (taintStep fn) (fn.nSlots + 1) (List.replicate fn.nSlots false)
-- ToyTailCall/Borrow.lean:112-116
def EscapeCheckFn (fn : Fn) : Bool :=
  fn.code.all fun i =>
    match i with
    | .tailCall _ args => !(args.any (opTainted (taint fn)))
    | _ => true
-- ToyTailCall/Borrow.lean:119
def EscapeCheckAccepts (p : Prog) : Bool := p.fns.all EscapeCheckFn
```

* `NoStackBorrow` (semantic property of the unbounded `preJump` run) and `EscapeCheckAccepts` (a static verdict) are distinct names.
* The check is intra-procedural: a `call` taints its destination slot and no other slot; this is adequate in a toy without stores through pointers, heap, globals or compound values.
* `taint` runs `nSlots + 1` rounds of a monotone step from "nothing tainted"; that this reaches the least fixpoint is not proved separately.

Definition examples: `NoStackBorrow` holds for `dtorProg` and `deadEscape` and fails for `borrowProg`; the check accepts `dtorProg` and `countUp 3` and rejects `borrowProg`.

```lean
-- ToyTailCall/Examples.lean:166
theorem noStackBorrow_dtorProg : NoStackBorrow dtorProg :=
-- ToyTailCall/Examples.lean:169
theorem noStackBorrow_deadEscape : NoStackBorrow deadEscape :=
-- ToyTailCall/Examples.lean:172
theorem not_noStackBorrow_borrowProg : ¬ NoStackBorrow borrowProg := fun h => by
-- ToyTailCall/Examples.lean:179
theorem escapeCheck_accepts_dtorProg : EscapeCheckAccepts dtorProg = true := by decide
-- ToyTailCall/Examples.lean:181
theorem escapeCheck_accepts_countUp3 : EscapeCheckAccepts (countUp 3) = true := by decide
-- ToyTailCall/Examples.lean:183
theorem escapeCheck_rejects_borrowProg : EscapeCheckAccepts borrowProg = false := by decide
```

#### Call-free chains

```lean
-- ToyTailCall/Machine.lean:421-425
def CallFree (p : Prog) : Bool :=
  p.fns.all fun fn => fn.code.all fun i =>
    match i with
    | .call .. => false
    | _ => true
-- ToyTailCall/Machine.lean:428
def EntryOk (p : Prog) : Prop := ∃ fn, p.fns[0]? = some fn ∧ fn.nParams = 0
```

Definition examples:

```lean
-- ToyTailCall/Examples.lean:187
theorem callFree_chain3 : CallFree chain3 = true := by decide
-- ToyTailCall/Examples.lean:189
theorem not_callFree_countUp3 : CallFree (countUp 3) = false := by decide
-- ToyTailCall/Examples.lean:191
theorem entryOk_chain3 : EntryOk chain3 := ⟨_, rfl, rfl⟩
-- ToyTailCall/Examples.lean:193
theorem not_entryOk_emptyProg : ¬ EntryOk emptyProg := by
```

#### Inlining (`Inline.lean`)

```lean
-- ToyTailCall/Inline.lean:31-34
inductive SpliceMode where
  | naive
  | corrected
  deriving DecidableEq, Repr
-- ToyTailCall/Inline.lean:36-42
def renOp (off : Nat) : Operand → Operand
  | .const n => .const n
  | .copy s => .copy (s + off)
  | .move s => .move (s + off)
  | .addrOf s => .addrOf (s + off)
  | .deref s => .deref (s + off)
  | .succ s => .succ (s + off)
-- ToyTailCall/Inline.lean:45-48
def maxTailArity : List Instr → Nat
  | [] => 0
  | .tailCall _ args :: is => max args.length (maxTailArity is)
  | _ :: is => maxTailArity is
-- ToyTailCall/Inline.lean:51-53
def assignTemps (off t base : Nat) : Nat → List Operand → List Instr
  | _, [] => []
  | i, a :: as => .assign (t + i) (renOp off a) (base + i + 1) :: assignTemps off t base (i + 1) as
-- ToyTailCall/Inline.lean:58-80
def spliceInstr (mode : SpliceMode) (nC nG gStart K dst next q : Nat) : Instr → List Instr
  | .assign d op n => [.assign (d + nC) (renOp nC op) (gStart + K * n)]
  | .emit k n => [.emit k (gStart + K * n)]
  | .branchLt s k t e => [.branchLt (s + nC) k (gStart + K * t) (gStart + K * e)]
  | .goto n => [.goto (gStart + K * n)]
  | .reset ss n => [.reset (ss.map (· + nC)) (gStart + K * n)]
  | .dropSlots ss n => [.dropSlots (ss.map (· + nC)) (gStart + K * n)]
  | .call f args d n => [.call f (args.map (renOp nC)) (d + nC) (gStart + K * n)]
  | .panic => [.panic]
  | .ret op =>
    let base := gStart + K * q
    [.assign (nC + nG) (renOp nC op) (base + 1),
     .dropSlots ((List.range nG).reverse.map (· + nC)) (base + 2),
     .assign dst (.move (nC + nG)) next]
  | .tailCall h args =>
    match mode with
    | .naive => [.tailCall h (args.map (renOp nC))]
    | .corrected =>
      let base := gStart + K * q
      let t := nC + nG + 1
      assignTemps nC t base 0 args ++
      [.dropSlots ((List.range nG).reverse.map (· + nC)) (base + args.length + 1),
       .call h ((List.range args.length).map fun i => .move (t + i)) dst next]
-- ToyTailCall/Inline.lean:83
def padBlock (K : Nat) (l : List Instr) : List Instr := l ++ List.replicate (K - l.length) .panic
-- ToyTailCall/Inline.lean:85-88
def spliceBody (mode : SpliceMode) (nC nG gStart K dst next : Nat) : Nat → List Instr → List Instr
  | _, [] => []
  | q, i :: is => padBlock K (spliceInstr mode nC nG gStart K dst next q i) ++
      spliceBody mode nC nG gStart K dst next (q + 1) is
-- ToyTailCall/Inline.lean:91-102
def spliceFn (mode : SpliceMode) (c g : Fn) (k : Nat) (args : List Operand) (dst next : Nat) : Fn :=
  let nC := c.nSlots
  let nG := g.nSlots
  let nT := maxTailArity g.code + 1
  let L := c.code.length
  let gStart := L + 1 + args.length
  let K := maxTailArity g.code + 3
  let prologue := .reset ((List.range (nG + nT)).map (· + nC)) (L + 1) ::
    assignTemps 0 nC (L + 1) 0 args
  { c with
    dtors := c.dtors ++ g.dtors ++ List.replicate nT .none
    code := c.code.set k (.goto L) ++ prologue ++ spliceBody mode nC nG gStart K dst next 0 g.code }
-- ToyTailCall/Inline.lean:105-118
def inlineCallSite (mode : SpliceMode) (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.call g args dst next) =>
      if g = ci then p else
      match p.fns[g]? with
      | none => p
      | some gf =>
        if args.length = gf.nParams ∧ gf.nParams ≤ gf.nSlots ∧ dst < c.nSlots then
          ⟨p.fns.set ci (spliceFn mode c gf k args dst next)⟩
        else p
    | _ => p
-- ToyTailCall/Inline.lean:122
def desugaredCallPc (L a : Nat) : Nat := L + a + 1
-- ToyTailCall/Inline.lean:127-143
def desugarTailSite (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.tailCall g args) =>
      let nC := c.nSlots
      let a := args.length
      let y := nC + a
      let L := c.code.length
      let tail := assignTemps 0 nC L 0 args ++
        [.dropSlots ((List.range nC).reverse) (L + a + 1),
         .call g ((List.range a).map fun i => .move (nC + i)) y (L + a + 2),
         .ret (.move y)]
      ⟨p.fns.set ci { c with dtors := c.dtors ++ List.replicate (a + 1) .none,
                             code := c.code.set k (.goto L) ++ tail }⟩
    | _ => p
-- ToyTailCall/Inline.lean:147-154
def inlineTailSite (mode : SpliceMode) (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.tailCall _ args) =>
      inlineCallSite mode (desugarTailSite p ci k) ci (desugaredCallPc c.code.length args.length)
    | _ => p
```

Definition examples: the spliced code of `inlEx`; a site that is not a `call` and a well-formed self-call are left unchanged (the second exercises the test `g = ci`); `inlineTailSite` leaves a site that is not a `tailCall` unchanged; the pre-jump reading of a tail site as code.

```lean
-- ToyTailCall/Examples.lean:200-204
theorem inlineCallSite_corrected_inlEx :
    (inlineCallSite .corrected inlEx 0 1).fns[0]? = some
      ⟨0, [.quiet, .none, .none],
       [.assign 0 (.const 9) 1, .goto 4, .emit 2 3, .ret (.move 1),
        .reset [2] 5, .dropSlots [] 6, .call 2 [] 1 2, .panic]⟩ := by decide
-- ToyTailCall/Examples.lean:207
theorem inlineCallSite_nonCall_unchanged : inlineCallSite .corrected inlEx 0 0 = inlEx := by
-- ToyTailCall/Examples.lean:213-217
theorem inlineCallSite_self_unchanged :
    (selfCallProg.fns[1]?.bind fun fn => fn.code[0]?) = some (.call 1 [.copy 0] 0 1) ∧
      (∃ c, selfCallProg.fns[1]? = some c ∧
        [Operand.copy 0].length = c.nParams ∧ c.nParams ≤ c.nSlots ∧ 0 < c.nSlots) ∧
      inlineCallSite .corrected selfCallProg 1 0 = selfCallProg :=
-- ToyTailCall/Examples.lean:221-222
theorem inlineTailSite_nonTail_unchanged :
    inlineTailSite .corrected (mutualRec 3) 1 0 = mutualRec 3 := by decide
-- ToyTailCall/Examples.lean:225-229
theorem desugarTailSite_mutualRec3 :
    (desugarTailSite (mutualRec 3) 1 1).fns[1]? = some
      ⟨1, [.none, .none, .none],
       [.branchLt 0 3 1 2, .goto 3, .ret (.const 0), .assign 1 (.copy 0) 4, .dropSlots [0] 5,
        .call 2 [.move 1] 2 6, .ret (.move 2)]⟩ := by decide
```

#### Argument-area layout (`Layout.lean`, namespace `Toy.TailCall.Layout`)

The fixed-boundary model (`ReuseSound`) and the model with the boundary moved by `δ` cells (`ReuseSoundAt`).

```lean
-- ToyTailCall/Layout.lean:25-28
inductive Cleanup where
  | callerPops
  | calleePops
  deriving DecidableEq, Repr
-- ToyTailCall/Layout.lean:30
abbrev Mem := Int → Nat
-- ToyTailCall/Layout.lean:33-35
def writeArgs (m : Mem) (a : Int) : List Nat → Mem
  | [] => m
  | v :: vs => writeArgs (fun x => if x = a then v else m x) (a + 1) vs
-- ToyTailCall/Layout.lean:38-40
def readArgs (m : Mem) (a : Int) : Nat → List Nat
  | 0 => []
  | n + 1 => m a :: readArgs m (a + 1) n
-- ToyTailCall/Layout.lean:43-44
theorem writeArgs_eq_of_lt (m : Mem) (a : Int) (args : List Nat) (x : Int) (hx : x < a) :
    writeArgs m a args x = m x := by
-- ToyTailCall/Layout.lean:54-55
theorem readArgs_writeArgs (m : Mem) (a : Int) (args : List Nat) :
    readArgs (writeArgs m a args) a args.length = args := by
-- ToyTailCall/Layout.lean:66-67
def reuseWrite (m : Mem) (b : Int) (inH : Nat) (args : List Nat) : Mem :=
  writeArgs m (b - inH) args
-- ToyTailCall/Layout.lean:70-71
theorem readArgs_reuseWrite (m : Mem) (b : Int) (inH : Nat) (args : List Nat)
    (hlen : args.length = inH) : readArgs (reuseWrite m b inH args) (b - inH) inH = args := by
-- ToyTailCall/Layout.lean:77-80
def spAfterReturn (cl : Cleanup) (b : Int) (inG inH : Nat) : Int :=
  match cl with
  | .callerPops => b - inG
  | .calleePops => b - inH
-- ToyTailCall/Layout.lean:94-98
def ReuseSound (cl : Cleanup) (inG inH : Nat) : Prop :=
  ∀ (m : Mem) (b : Int) (args : List Nat), args.length = inH →
    (∀ x, x < b - inG → reuseWrite m b inH args x = m x) ∧
    readArgs (reuseWrite m b inH args) (b - inH) inH = args ∧
    spAfterReturn cl b inG inH = b - inG
-- ToyTailCall/Layout.lean:110-111
def reuseWriteAt (m : Mem) (b δ : Int) (inH : Nat) (args : List Nat) : Mem :=
  writeArgs m (b + δ - inH) args
-- ToyTailCall/Layout.lean:114-116
theorem readArgs_reuseWriteAt (m : Mem) (b δ : Int) (inH : Nat) (args : List Nat)
    (hlen : args.length = inH) :
    readArgs (reuseWriteAt m b δ inH args) (b + δ - inH) inH = args := by
-- ToyTailCall/Layout.lean:121-124
def spAfterReturnAt (cl : Cleanup) (b δ : Int) (inG inH : Nat) : Int :=
  match cl with
  | .callerPops => b + δ - inG
  | .calleePops => b + δ - inH
-- ToyTailCall/Layout.lean:128-132
def ReuseSoundAt (cl : Cleanup) (δ : Int) (inG inH : Nat) : Prop :=
  ∀ (m : Mem) (b : Int) (args : List Nat), args.length = inH →
    (∀ x, x < b - inG → reuseWriteAt m b δ inH args x = m x) ∧
    readArgs (reuseWriteAt m b δ inH args) (b + δ - inH) inH = args ∧
    spAfterReturnAt cl b δ inG inH = b - inG
-- ToyTailCall/Layout.lean:138-141
structure Sig where
  explicit : List Nat
  callerLoc : Bool
  deriving DecidableEq, Repr
-- ToyTailCall/Layout.lean:144
def Sig.areaSize (s : Sig) : Nat := s.explicit.sum + (if s.callerLoc then 1 else 0)
-- ToyTailCall/Layout.lean:147
def sigCheckFull (g h : Sig) : Bool := g == h
-- ToyTailCall/Layout.lean:150
def sigCheckExplicit (g h : Sig) : Bool := g.explicit == h.explicit
```

* Addresses are integers, so `b - inH` is ordinary integer subtraction (no truncation) even when negative; areas may have size `0`.
* The second condition of `ReuseSound` holds for all sizes (`readArgs_reuseWrite`); the third is fixed by `spAfterReturn`.

Definition examples:

```lean
-- ToyTailCall/Examples.lean:238
theorem reuseSound_callerPops_2_1 : ReuseSound .callerPops 2 1 := by
-- ToyTailCall/Examples.lean:252
theorem reuseSound_calleePops_1_1 : ReuseSound .calleePops 1 1 := by
-- ToyTailCall/Examples.lean:267
theorem not_reuseSound_callerPops_1_2 : ¬ ReuseSound .callerPops 1 2 := by
-- ToyTailCall/Examples.lean:274
theorem not_reuseSound_calleePops_2_1 : ¬ ReuseSound .calleePops 2 1 := by
-- ToyTailCall/Examples.lean:279-280
theorem areaSize_examples :
    Sig.areaSize ⟨[1, 2], false⟩ = 3 ∧ Sig.areaSize ⟨[1, 2], true⟩ = 4 := by decide
-- ToyTailCall/Examples.lean:282-283
theorem sigCheckFull_examples :
    sigCheckFull ⟨[1], true⟩ ⟨[1], true⟩ = true ∧ sigCheckFull ⟨[1], true⟩ ⟨[1], false⟩ = false := by
-- ToyTailCall/Examples.lean:286-288
theorem sigCheckExplicit_examples :
    sigCheckExplicit ⟨[1], true⟩ ⟨[1], false⟩ = true ∧
      sigCheckExplicit ⟨[1], true⟩ ⟨[2], true⟩ = false := by decide
```

#### Example programs (`Examples.lean`)

```lean
-- ToyTailCall/Examples.lean:20-24
def countUp (N : Nat) : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none, .quiet, .none],
       [.branchLt 0 N 1 4, .assign 1 (.copy 0) 2, .assign 2 (.succ 0) 3,
        .tailCall 1 [.move 2], .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:28-31
def dtorProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.quiet], [.assign 0 (.const 7) 1, .tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:35-38
def borrowProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .tailCall 2 [.addrOf 0]]⟩,
     ⟨1, [.none], [.ret (.deref 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:42-46
def deadEscape : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none, .none], [.assign 0 (.const 5) 1, .assign 1 (.addrOf 0) 2,
        .assign 1 (.const 0) 3, .tailCall 2 [.copy 1]]⟩,
     ⟨1, [.none], [.ret (.copy 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:50-55
def orderDemo : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 10, .const 11] 0 1, .ret (.move 0)]⟩,
     ⟨2, [.quiet, .quiet, .quiet, .quiet, .quiet],
       [.assign 2 (.const 12) 1, .assign 3 (.const 13) 2, .assign 4 (.const 14) 3,
        .tailCall 2 [.move 3]]⟩,
     ⟨1, [.quiet], [.emit 99 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:59-63
def panicFin (d0 d1 d2 : DtorKind) : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     ⟨0, [d0, d1, d2], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
        .assign 2 (.const 3) 3, .tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:67-70
def inlEx : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 9) 1, .call 1 [] 1 2, .emit 2 3, .ret (.move 1)]⟩,
     ⟨0, [], [.tailCall 2 []]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:75-79
def inlEx2 : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 9) 1, .call 1 [.const 4] 1 2, .emit 2 3,
        .ret (.move 1)]⟩,
     ⟨1, [.quiet, .quiet], [.assign 1 (.const 5) 1, .emit 3 2, .tailCall 2 [.move 0]]⟩,
     ⟨1, [.none], [.emit 1 1, .ret (.move 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:83-86
def mutualRec (N : Nat) : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none], [.branchLt 0 N 1 2, .tailCall 2 [.copy 0], .ret (.const 0)]⟩,
     ⟨1, [.none, .none], [.assign 1 (.succ 0) 1, .tailCall 1 [.move 1]]⟩ ]⟩
-- ToyTailCall/Examples.lean:89-91
def danglingRet : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.deref 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .ret (.addrOf 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:94-96
def plainCall : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:99-102
def chain3 : Prog :=
  ⟨[ ⟨0, [], [.tailCall 1 []]⟩,
     ⟨0, [], [.emit 1 1, .tailCall 2 []]⟩,
     ⟨0, [], [.ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:105
def emptyProg : Prog := ⟨[]⟩
-- ToyTailCall/Examples.lean:109-111
def selfCallProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [.const 0] 0 1, .ret (.move 0)]⟩,
     ⟨1, [.none], [.call 1 [.copy 0] 0 1, .ret (.move 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:115-118
def ignorePtrProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.move 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .tailCall 2 [.addrOf 0]]⟩,
     ⟨1, [.none], [.ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:122-124
def ptrRetProg : Prog :=
  ⟨[ ⟨0, [.none], [.call 1 [] 0 1, .ret (.copy 0)]⟩,
     ⟨0, [.none], [.assign 0 (.const 5) 1, .ret (.addrOf 0)]⟩ ]⟩
-- ToyTailCall/Examples.lean:127
def paramEntryProg : Prog := ⟨[⟨1, [.none], [.ret (.const 0)]⟩]⟩
```

#### Statement helpers (`Machine.lean`)

```lean
-- ToyTailCall/Machine.lean:478-479
def finalizationEvents (fn : Fn) (fr : Frame) : List Event :=
  (pendingDrops fn fr).map fun s => Event.drop (fr.get s).obs
-- ToyTailCall/Machine.lean:482-483
def panickingPending (fn : Fn) (fr : Frame) : List Slot :=
  (pendingDrops fn fr).filter fun s => fn.dtor s == .panics
-- ToyTailCall/Machine.lean:487-494
structure AtTailCall (p : Prog) (st : State) (fn : Fn) (fr : Frame) (rest : List Frame)
    (f : FnId) (args : List Operand) (vs : List Val) (fr1 : Frame) : Prop where
  stack_eq : st.stack = fr :: rest
  not_unwinding : st.unwinding = false
  no_pendingRet : fr.pendingRet = none
  fn_eq : p.fns[fr.fn]? = some fn
  instr_eq : fn.code[fr.pc]? = some (.tailCall f args)
  args_eq : evalOps rest fr args = some (vs, fr1)
```

Definition examples for `AtTailCall` (positive and negative); `finalizationEvents` and `panickingPending` are evaluated in `panic_drops_rest_nonvacuous` (Findings, auxiliary lemmas and witnesses).

```lean
-- ToyTailCall/Counterexamples.lean:363-365
def panicFinT (d0 d1 d2 : DtorKind) : Fn :=
  ⟨0, [d0, d1, d2], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2, .assign 2 (.const 3) 3,
    .tailCall 2 []]⟩
-- ToyTailCall/Counterexamples.lean:368-369
def panicFinFrame : Frame :=
  ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩
-- ToyTailCall/Counterexamples.lean:372
def panicFinRest : List Frame := [⟨0, 0, 1, [.int 50, .undef], [true, false], .store 1 2, none⟩]
-- ToyTailCall/Counterexamples.lean:375
def panicFinState : State := ⟨panicFinFrame :: panicFinRest, 2, [], 2, 0, false⟩
-- ToyTailCall/Counterexamples.lean:383-385
theorem atTailCall_panicFin (d0 d1 d2 : DtorKind) :
    AtTailCall (panicFin d0 d1 d2) panicFinState (panicFinT d0 d1 d2) panicFinFrame panicFinRest
      2 [] [] panicFinFrame :=
-- ToyTailCall/Counterexamples.lean:390-393
theorem not_atTailCall_wrongInstr :
    ¬ AtTailCall ⟨[⟨0, [], []⟩, ⟨0, [.quiet, .quiet, .quiet], [.panic, .panic, .panic, .panic]⟩]⟩
      panicFinState ⟨0, [.quiet, .quiet, .quiet], [.panic, .panic, .panic, .panic]⟩
      panicFinFrame panicFinRest 2 [] [] panicFinFrame := by
```

### Results

Each card gives the plain claim, kind, tier and depth, the verbatim Lean statement, the hypothesis ledger (every hypothesis with its tightness and a kernel-checked counterexample), the non-vacuity witness, a positive control where the result is an impossibility, prior art and the design question it informs. The non-claims of each card are under Boundaries.

#### R1. `frameReuse_observes_iff_preJump_of_noStackBorrow`

**Plain claim.** For every toy program `p` satisfying `NoStackBorrow p` (in the unbounded `preJump` run of `p`, no executed `tailCall` passes an argument value that is a pointer into the current frame), and for every outcome `o` and event trace `es`, the unbounded `frameReuse` run of `p` halts with `o` and `es` if and only if the unbounded `preJump` run of `p` does.

**Kind / tier / depth.** theorem / T1 (folklore made precise: deallocating a frame before the tail call is known to be safe when no pointer into it reaches the callee (CompCert `Tailcall.v` documentation, LLVM `musttail` documentation), and tail calls without destructors are mechanized in Stack-Aware CompCert and CakeML; a mechanized statement combining pre-jump destructor finalization with this equivalence was not found in a web search) / substantive.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:27-29
theorem frameReuse_observes_iff_preJump_of_noStackBorrow (p : Prog) (hnb : NoStackBorrow p)
    (o : Outcome) (es : List Event) :
    Observes .frameReuse none p o es ↔ Observes .preJump none p o es :=
```

Unfolded (prose): `NoStackBorrow p` ≡ for every `n` and `st`, if `run .preJump none p n (start none p) = .running st` then `tailCallBorrowsFrame p st = false`, i.e. if `st` is about to execute `tailCall f args` in its top frame `fr` (not unwinding, no pending return), the values of `args` (evaluated with `evalOps`) contain no `ptr fr.fid _`. `Observes sem D p o es` ≡ ∃ r, (∃ n, `run sem D p n (start D p) = .halted r`) ∧ `r.outcome = o` ∧ `r.events = es`.

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hnb : NoStackBorrow p` | frame reuse removes the current frame before the callee runs; a callee loading through a pointer into it is `ub` under `frameReuse` but reads a live slot under `preJump` | tight: counterexample `frameReuse_iff_preJump_fails_borrowProg` (witness class: a three-function program with one tail call passing `addrOf` of a local) |

**Non-vacuity witness.** `dtorProg` satisfies `NoStackBorrow` and both semantics return 0 with trace `[drop 7, out 1]`. (`frameReuse_iff_preJump_nonvacuous_dtorProg`)

**Non-claims.** Listed under Boundaries, R1; a reader of this result must read them with it.

**Prior art.**

* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719 (space-efficiency formulation of proper tail calls; no destructors, no inlining)
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825 (documentation of `TailCall`: pop of the current stack frame, then a call with the return address of the current caller) and :829-833 (arguments are owned by the callee) [documentation; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Tailcall.v:17-28 (the documentation says an `Icall` can be turned into an `Itailcall` if the caller's stack block is empty, and explains that otherwise a pointer into it may have been passed to the callee) and :80-98 (`transf_instr`, `transf_function`); backend/Tailcallproof.v:600-601 (`transf_program_correct`: forward simulation RTL -> RTL)
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Cminor.v:468-475 (`step_tailcall` frees the stack block before entering the callee)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]
* Y. Wang, P. Wilke, Z. Shao, "An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code", Proc. ACM Program. Lang. 3 (POPL), Article 62, 2019, doi:10.1145/3290375 (Stack-Aware CompCert: a bounded abstract stack, mechanized through tail-call recognition and inlining; no destructors) [bibliographic record checked; publisher text not fetched]
* J. Clements, M. Felleisen, "A Tail-Recursive Machine with Stack Inspection", ACM TOPLAS 26(6), 2004, pp. 1029-1052, doi:10.1145/1034774.1034778 (an abstract machine combining proper tail calls with frame-attached information; no destructors) [bibliographic record checked; publisher text not fetched]
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "A New Verified Compiler Backend for CakeML", ICFP 2016, pp. 60-73, doi:10.1145/2951913.2951924 (a verified backend with explicit stack frames, tail calls and exception unwinding; no destructors) [bibliographic record checked; publisher text not fetched]
* rust-lang/rfcs#3407 "Explicit Tail Calls" (open, unmerged proposal; cited in prose, not normative) and rust-lang/rust#112788 (open tracking issue; cited in prose)

**Design question.** Q1: relative to what reference semantics is frame reuse a refinement, given that locals and parameters are finalized before the jump?

#### R2. `frameReuse_ne_callReturn_dtorProg`

**Plain claim.** There is a toy program, `dtorProg`, that satisfies `NoStackBorrow` and whose unbounded `callReturn` run returns 0 with trace `[out 1, drop 7]` while its unbounded `frameReuse` run returns 0 with trace `[drop 7, out 1]`; so `frameReuse` does not refine `callReturn` on event traces even when no stack borrow is passed.

**Kind / tier / depth.** counterexample / T1 (folklore made precise: running the caller's destructors before the callee is the documented pre-jump order; the observable difference from call-then-return with a destructor-carrying local was not found mechanized) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:18-22
theorem frameReuse_ne_callReturn_dtorProg :
    NoStackBorrow dtorProg ∧
      Observes .callReturn none dtorProg (.returned 0) [.out 1, .drop 7] ∧
      Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      ¬ Observes .frameReuse none dtorProg (.returned 0) [.out 1, .drop 7] :=
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`frameReuse_ne_callReturn_dtorProg`)

**Non-claims.** Listed under Boundaries, R2; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825 (documentation of `TailCall`: pop of the current stack frame, then a call with the return address of the current caller) and :829-833 (arguments are owned by the callee) [documentation; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/drop-order.rs:7-39 (asserts that `tail_recursive` records 0..128 ascending and `simply_recursive` records it descending) and :41-60 (all locals of the current frame dropped before the callee's) [test; used in the modeling bridge]
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) clang/include/clang/Basic/AttrDocs.td:616-643 (`[[clang::musttail]]`: "Any variables in scope, including all arguments to the function and the return value must be trivially destructible"; matching argument counts and similar types) [documentation; cited in prose]
* T. Ramananandro, G. Dos Reis, X. Leroy, "A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management", POPL 2012, doi:10.1145/2103621.2103718 (mechanized reverse-order destruction; no tail calls) [bibliographic record checked; publisher text not fetched]
* rust-lang/rfcs#3407 "Explicit Tail Calls" (open, unmerged proposal; cited in prose, not normative) and rust-lang/rust#112788 (open tracking issue; cited in prose)

**Design question.** Q1: relative to what reference semantics is frame reuse a refinement, given that locals and parameters are finalized before the jump?

#### R3. `frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow`

**Plain claim.** For every toy program `p` satisfying `NoStackBorrow p` (a property of the unbounded `preJump` run of `p`), every stack bound `D` (including `none`), and every outcome `o` other than `stackOverflow` with trace `es`: if the `D`-bounded `preJump` run of `p` halts with `o` and `es`, then the `D`-bounded `frameReuse` run of `p` halts with `o` and `es`.

**Kind / tier / depth.** theorem / T1 (folklore made precise: deallocating a frame before the tail call is known to be safe when no pointer into it reaches the callee (CompCert `Tailcall.v` documentation, LLVM `musttail` documentation), and tail calls without destructors are mechanized in Stack-Aware CompCert and CakeML; a mechanized statement combining pre-jump destructor finalization with this bounded transfer was not found in a web search) / substantive.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:35-38
theorem frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow (p : Prog)
    (hnb : NoStackBorrow p) (D : Option Nat) (o : Outcome) (es : List Event)
    (hso : o ≠ .stackOverflow) :
    Observes .preJump D p o es → Observes .frameReuse D p o es :=
```

Unfolded (prose): As in R1; the bound enters through `push`, which halts with `stackOverflow` when `D = some d` and the stack already has at least `d` frames.

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hnb : NoStackBorrow p` | as in R1: without it a popped slot can be loaded | tight: counterexample `frameReuse_of_preJump_fails_borrowProg` (witness class: a three-function program, `D = none`) |
| `hso : o ≠ .stackOverflow` | the bounded `preJump` run may overflow where `frameReuse` does not | tight: counterexample `frameReuse_of_preJump_fails_for_overflow_countUp3` (witness class: `countUp 3` with bound `some 4`) |

**Non-vacuity witness.** `countUp 3` satisfies `NoStackBorrow`; with bound `some 5` its `preJump` run returns 0 with trace `[drop 0, drop 1, drop 2]`. (`frameReuse_of_preJump_nonvacuous_countUp3`)

**Non-claims.** Listed under Boundaries, R3; a reader of this result must read them with it.

**Prior art.**

* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719 (space-efficiency formulation of proper tail calls; no destructors, no inlining)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]
* Y. Wang, P. Wilke, Z. Shao, "An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code", Proc. ACM Program. Lang. 3 (POPL), Article 62, 2019, doi:10.1145/3290375 (Stack-Aware CompCert: a bounded abstract stack, mechanized through tail-call recognition and inlining; no destructors) [bibliographic record checked; publisher text not fetched]
* Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao, "End-to-End Verification of Stack-Space Bounds for C Programs", PLDI 2014, pp. 270-281, doi:10.1145/2594291.2594301 (stack-bound preservation through a verified compiler; no explicit tail calls or destructors)

**Design question.** Q1: relative to what reference semantics is frame reuse a refinement, given that locals and parameters are finalized before the jump?

#### R4. `countUp_frameReuse_runsTo` (+2)

**Plain claim.** For every `N`, the self-tail-recursive toy program `countUp N` (the entry calls `rec 0`; `rec n` returns 0 when `n ≥ N`, and otherwise owns a local with value `n` whose destructor emits `drop n` and tail-calls `rec (n + 1)`) returns 0 with exactly `N` tail-call jumps under each of the three unbounded semantics `frameReuse`, `preJump` and `callReturn`, with: `frameReuse` — trace `drop 0, …, drop (N-1)` and maximum depth exactly 2; `preJump` — the same trace and maximum depth exactly `N + 2`; `callReturn` — trace `drop (N-1), …, drop 0` and maximum depth exactly `N + 2` (each trace is `[]` when `N = 0`; the Lean terms use `List.range N`, so no truncated subtraction occurs).

**Kind / tier / depth.** theorem / T1 (folklore made precise: the ascending/descending drop orders are asserted by the rustc UI test `drop-order.rs`; exact depth and trace equations for a self-tail-recursive family were not found mechanized) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:45-47
theorem countUp_frameReuse_runsTo (N : Nat) :
    RunsTo .frameReuse none (countUp N)
      ⟨.returned 0, (List.range N).map Event.drop, 2, N⟩ :=
-- ToyTailCall/Results.lean:52-54
theorem countUp_preJump_runsTo (N : Nat) :
    RunsTo .preJump none (countUp N)
      ⟨.returned 0, (List.range N).map Event.drop, N + 2, N⟩ :=
-- ToyTailCall/Results.lean:59-61
theorem countUp_callReturn_runsTo (N : Nat) :
    RunsTo .callReturn none (countUp N)
      ⟨.returned 0, ((List.range N).reverse).map Event.drop, N + 2, N⟩ :=
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** Instances `N = 3` are kernel-checked: `countUp3_frameReuse`, `countUp3_preJump`, `countUp3_callReturn`. (`countUp3_frameReuse`, `countUp3_preJump`, `countUp3_callReturn`)

**Non-claims.** Listed under Boundaries, R4; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/drop-order.rs:7-39 (asserts that `tail_recursive` records 0..128 ascending and `simply_recursive` records it descending) and :41-60 (all locals of the current frame dropped before the callee's) [test; used in the modeling bridge]
* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719 (space-efficiency formulation of proper tail calls; no destructors, no inlining)

**Design question.** Q1: relative to what reference semantics is frame reuse a refinement, given that locals and parameters are finalized before the jump?

#### R5. `callFree_frameReuse_maxDepth_of_entryOk` (+1)

**Plain claim.** For every call-free toy program (`CallFree p`: no `call` instruction in any function of `p`, reachable or not) whose entry function exists and takes no parameters (`EntryOk p`), every halted unbounded `frameReuse` run has maximum depth exactly 1, and every halted unbounded `preJump` run has maximum depth equal to its number of tail-call jumps plus 1.

**Kind / tier / depth.** theorem / T0 (re-derivation: constant stack for chains of proper tail calls versus linear growth when frames are kept is the classical space property of Steele and Clinger, restated for this machine) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:68-69
theorem callFree_frameReuse_maxDepth_of_entryOk (p : Prog) (hcf : CallFree p = true)
    (hentry : EntryOk p) (r : Result) (hr : RunsTo .frameReuse none p r) : r.maxDepth = 1 :=
-- ToyTailCall/Results.lean:74-76
theorem callFree_preJump_maxDepth_of_entryOk (p : Prog) (hcf : CallFree p = true)
    (hentry : EntryOk p) (r : Result) (hr : RunsTo .preJump none p r) :
    r.maxDepth = r.tailCalls + 1 :=
```

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hcf : CallFree p = true` | a `call` keeps a frame below the chain, adding depth that is not a tail call | tight: counterexample `callFree_needed_frameReuse_countUp3`, `callFree_needed_preJump_countUp3` (witness class: `countUp 3`, whose entry calls `rec`) |
| `hentry : EntryOk p` | without an entry frame the run halts at depth 0 | tight: counterexample `entryOk_needed_emptyProg`, `entryOk_needed_paramEntryProg` (witness class: the empty program (no entry function), and a one-function program whose entry function takes one parameter) |

**Non-vacuity witness.** `chain3` (main → f₁ → f₂, two tail calls) satisfies both hypotheses; `frameReuse` depth 1, `preJump` depth 3 with 2 jumps. (`callFree_nonvacuous_chain3`)

**Non-claims.** Listed under Boundaries, R5; a reader of this result must read them with it.

**Prior art.**

* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719 (space-efficiency formulation of proper tail calls; no destructors, no inlining)
* G. L. Steele Jr., "Debunking the 'Expensive Procedure Call' Myth, or, Procedure Call Implementations Considered Harmful, or, LAMBDA: The Ultimate GOTO", Proceedings of the 1977 annual conference (ACM '77), pp. 153-162, doi:10.1145/800179.810196 (tail calls compiled as jumps)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]
* J. Clements, M. Felleisen, "A Tail-Recursive Machine with Stack Inspection", ACM TOPLAS 26(6), 2004, pp. 1029-1052, doi:10.1145/1034774.1034778 (an abstract machine combining proper tail calls with frame-attached information; no destructors) [bibliographic record checked; publisher text not fetched]

**Design question.** Q1: relative to what reference semantics is frame reuse a refinement, given that locals and parameters are finalized before the jump?

#### R6. `mem_pendingDrops_iff` (+1)

**Plain claim.** For every function `fn` and frame `fr`, a slot `s` is in `pendingDrops fn fr` exactly when `s < fr.vals.length`, the drop flag of `s` is set (`fr.isLive s = true`), and the destructor kind of `s` is not `none`; and `pendingDrops fn fr` lists slots in strictly decreasing order.

**Kind / tier / depth.** characterization / T0 (re-derivation: a definitional characterization of the toy's finalization list; reverse declaration order is the usual destruction order, mechanized for C++ by Ramananandro et al.) / definitional.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:82-83
theorem mem_pendingDrops_iff (fn : Fn) (fr : Frame) (s : Slot) :
    s ∈ pendingDrops fn fr ↔ s < fr.vals.length ∧ fr.isLive s = true ∧ fn.dtor s ≠ .none := by
-- ToyTailCall/Results.lean:87-88
theorem pendingDrops_pairwise_gt (fn : Fn) (fr : Frame) :
    (pendingDrops fn fr).Pairwise (· > ·) := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** `pendingDrops_orderDemo` (slots 4, 2, 1, 0; slot 3 moved) and the full run `orderDemo_frameReuse`. (`pendingDrops_orderDemo`, `orderDemo_frameReuse`)

**Non-claims.** Listed under Boundaries, R6; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/drop-order.rs:7-39 (asserts that `tail_recursive` records 0..128 ascending and `simply_recursive` records it descending) and :41-60 (all locals of the current frame dropped before the callee's) [test; used in the modeling bridge]
* T. Ramananandro, G. Dos Reis, X. Leroy, "A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management", POPL 2012, doi:10.1145/2103621.2103718 (mechanized reverse-order destruction; no tail calls) [bibliographic record checked; publisher text not fetched]

**Design question.** Q5: what does pre-jump finalization guarantee when a destructor panics, and why must the frame stay until finalization ends?

#### R7. `frameReuse_iff_preJump_fails_borrowProg`

**Plain claim.** Without `NoStackBorrow` the equivalence of R1 fails: in `borrowProg` (`t` does `become reader(&local)` and `reader` loads through its argument) `NoStackBorrow` does not hold, the unbounded `preJump` run returns 5 with an empty trace, the unbounded `frameReuse` run halts with `ub` and an empty trace, and the two runs do not have the same outcomes and traces.

**Kind / tier / depth.** counterexample / T0 (re-derivation: the hazard is documented in CompCert's `Tailcall.v` and LLVM's `musttail` rules; this is its instance in the toy) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:34-38
theorem frameReuse_iff_preJump_fails_borrowProg :
    ¬ NoStackBorrow borrowProg ∧
      Observes .preJump none borrowProg (.returned 5) [] ∧
      Observes .frameReuse none borrowProg .ub [] ∧
      ¬ (∀ o es, Observes .frameReuse none borrowProg o es ↔ Observes .preJump none borrowProg o es) := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`frameReuse_iff_preJump_fails_borrowProg`)

**Non-claims.** Listed under Boundaries, R7; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/ctfe-arg-bad-borrow.rs:4-10 and ctfe-arg-bad-borrow.stderr:1-11 (`become takes_borrow(&local)` rejected with E0597, "`local` dropped here while still borrowed") [test; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Tailcall.v:17-28 (the documentation says an `Icall` can be turned into an `Itailcall` if the caller's stack block is empty, and explains that otherwise a pointer into it may have been passed to the callee) and :80-98 (`transf_instr`, `transf_function`); backend/Tailcallproof.v:600-601 (`transf_program_correct`: forward simulation RTL -> RTL)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]

**Design question.** Q2: when must borrows of the current frame be rejected?

#### R8. `noStackBorrow_of_escapeCheckAccepts`

**Plain claim.** For every toy program `p`, if the flow-insensitive escape check accepts `p` (`EscapeCheckAccepts p = true`: in every function, no `tailCall` argument is an `addrOf` operand or reads a slot that may hold an `addrOf`-derived value, where taint flows through `assign` and through `call` results with a tainted argument), then `p` satisfies `NoStackBorrow`.

**Kind / tier / depth.** theorem / T1 (folklore made precise: escape analysis guarding tail calls is standard compiler practice; a soundness proof of such a check against a tail-call semantics with frame identities was not found mechanized) / substantive.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:97-98
theorem noStackBorrow_of_escapeCheckAccepts (p : Prog) (hacc : EscapeCheckAccepts p = true) :
    NoStackBorrow p :=
```

Unfolded (prose): `EscapeCheckAccepts p = true` ≡ every function `fn` of `p` has no `tailCall _ args` with an argument `a` such that `opTainted (taint fn) a = true`; `opTainted T` is true on `addrOf _` and on `copy s`, `move s`, `deref s`, `succ s` with `T[s] = true`.

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hacc : EscapeCheckAccepts p = true` | the verdict whose soundness is claimed | tight: counterexample `escapeCheck_needed_borrowProg` (witness class: `borrowProg`, which the check rejects and which violates `NoStackBorrow`) |

**Non-vacuity witness.** The check accepts `dtorProg` and `countUp 3`. (`escapeCheck_accepts_dtorProg`, `escapeCheck_accepts_countUp3`)

**Non-claims.** Listed under Boundaries, R8; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/ctfe-arg-bad-borrow.rs:4-10 and ctfe-arg-bad-borrow.stderr:1-11 (`become takes_borrow(&local)` rejected with E0597, "`local` dropped here while still borrowed") [test; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Tailcall.v:17-28 (the documentation says an `Icall` can be turned into an `Itailcall` if the caller's stack block is empty, and explains that otherwise a pointer into it may have been passed to the callee) and :80-98 (`transf_instr`, `transf_function`); backend/Tailcallproof.v:600-601 (`transf_program_correct`: forward simulation RTL -> RTL)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]

**Design question.** Q2: when must borrows of the current frame be rejected?

#### R9. `escapeCheck_incomplete_deadEscape`

**Plain claim.** The escape check is incomplete: it rejects `deadEscape` (an address is stored in a slot and overwritten with 0 before the tail call passes that slot), although `deadEscape` satisfies `NoStackBorrow`.

**Kind / tier / depth.** counterexample / T0 (re-derivation: incompleteness of flow-insensitive analyses is textbook; this is its instance for the toy check) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:210-211
theorem escapeCheck_incomplete_deadEscape :
    EscapeCheckAccepts deadEscape = false ∧ NoStackBorrow deadEscape :=
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`escapeCheck_incomplete_deadEscape`)

**Non-claims.** Listed under Boundaries, R9; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/ctfe-arg-bad-borrow.rs:4-10 and ctfe-arg-bad-borrow.stderr:1-11 (`become takes_borrow(&local)` rejected with E0597, "`local` dropped here while still borrowed") [test; used in the modeling bridge]

**Design question.** Q2: when must borrows of the current frame be rejected?

#### R10. `Layout.reuseSound_callerPops_iff` (+1)

**Plain claim.** In the layout toy, at a fixed frame boundary `b` (no return-address relocation and no stack-pointer adjustment before the jump), for all incoming-area sizes `inG` (current function) and `inH` (callee): frame reuse is sound under caller cleanup iff `inH ≤ inG`, and sound under callee cleanup iff `inH = inG` (`ReuseSound`: for every memory, frame base `b` and list of exactly `inH` argument cells, no cell below `b - inG` changes, the callee reads back its arguments from `[b - inH, b)`, and the caller sees stack pointer `b - inG` after the return).

**Kind / tier / depth.** characterization / T0 (re-derivation: textbook calling-convention reasoning about argument areas at a fixed frame boundary, restated in a layout toy) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:199-200
theorem reuseSound_callerPops_iff (inG inH : Nat) :
    ReuseSound .callerPops inG inH ↔ inH ≤ inG := by
-- ToyTailCall/Results.lean:214-215
theorem reuseSound_calleePops_iff (inG inH : Nat) :
    ReuseSound .calleePops inG inH ↔ inH = inG := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** `reuseSound_callerPops_2_1` and `reuseSound_calleePops_1_1`. (`Layout.reuseSound_callerPops_2_1`, `Layout.reuseSound_calleePops_1_1`)

**Non-claims.** Listed under Boundaries, R10; a reader of this result must read them with it.

**Prior art.**

* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Conventions.v:143-155 (`tailcall_possible`: all arguments passed in registers, i.e. no stack-argument area)
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:134-136 (ABI equality check) and :150-163 (signature equality check, skipped when the callee ABI is `RustTail`) [source; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/signature-mismatch.rs:4-14 and signature-mismatch.stderr:1-19 (`become` between `fn(())` and `fn()` rejected: "mismatched signatures") [test; cited in prose]
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:498-501 (`swifttailcc`: "the callee pops the argument area of the stack so that mandatory tail calls are possible as in ``tailcc``") and :12626-12637 (prototype matching is required for `musttail` unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]

**Design question.** Q3: what signature or argument-area compatibility does frame reuse need?

#### R11. `Layout.reuseSound_of_sigCheckFull`

**Plain claim.** In the layout toy, at a fixed frame boundary, for all signatures `g` and `h`: if `sigCheckFull g h = true` (equal explicit parameters and equal hidden caller-location parameter), then frame reuse is sound for their incoming-area sizes under either cleanup convention.

**Kind / tier / depth.** theorem / T0 (re-derivation: a direct corollary of card R10) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:229-230
theorem reuseSound_of_sigCheckFull (g h : Sig) (hchk : sigCheckFull g h = true) (cl : Cleanup) :
    ReuseSound cl g.areaSize h.areaSize := by
```

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hchk : sigCheckFull g h = true` | equal signatures give equal areas | tight: counterexample `Layout.sigCheckExplicit_insufficient_calleeLoc` (witness class: `g = ⟨[1], false⟩`, `h = ⟨[1], true⟩`, under either convention) |

**Non-vacuity witness.** `sigCheckFull ⟨[1, 2], true⟩ ⟨[1, 2], true⟩ = true`. (`Layout.sigCheckFull_nonvacuous`)

**Non-claims.** Listed under Boundaries, R11; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:134-136 (ABI equality check) and :150-163 (signature equality check, skipped when the callee ABI is `RustTail`) [source; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:165-185 (comment: `#[track_caller]` adds a location argument; a `#[track_caller]` caller is rejected because THIR can be polymorphic, so allowing just the resolvable `#[track_caller]` callees would make changing `track_caller`-ness a breaking change; the callee's `track_caller`-ness is not checked, mostly for those reasons and also because the shim generated for coercing the function to an `fn()` pointer can always be tail-called) and :394-405 (the error "a function marked with `#[track_caller]` cannot perform a tail-call") [source; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/caller_is_track_caller.rs:4-14 and caller_is_track_caller.stderr:1-11 (`become` from a `#[track_caller]` function is rejected both when the callee lacks the attribute (`a -> b`) and when it has it (`c -> a`)) [test; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/signature-mismatch.rs:4-14 and signature-mismatch.stderr:1-19 (`become` between `fn(())` and `fn()` rejected: "mismatched signatures") [test; cited in prose]

**Design question.** Q3: what signature or argument-area compatibility does frame reuse need?

#### R12. `Layout.sigCheckExplicit_insufficient_calleeLoc`

**Plain claim.** In the layout toy, at a fixed frame boundary, comparing explicit parameters is not enough: for `g = ⟨[1], false⟩` and `h = ⟨[1], true⟩`, `sigCheckExplicit g h = true` and `sigCheckFull g h = false`, and frame reuse is unsound for their area sizes (exactly 1 and exactly 2) under both cleanup conventions (the callee's extra cell overwrites the caller's frame).

**Kind / tier / depth.** counterexample / T0 (re-derivation: an instance of card R10) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:692-696
theorem sigCheckExplicit_insufficient_calleeLoc :
    sigCheckExplicit ⟨[1], false⟩ ⟨[1], true⟩ = true ∧
      sigCheckFull ⟨[1], false⟩ ⟨[1], true⟩ = false ∧
      ¬ ReuseSound .callerPops (Sig.areaSize ⟨[1], false⟩) (Sig.areaSize ⟨[1], true⟩) ∧
      ¬ ReuseSound .calleePops (Sig.areaSize ⟨[1], false⟩) (Sig.areaSize ⟨[1], true⟩) := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`Layout.sigCheckExplicit_insufficient_calleeLoc`)

**Non-claims.** Listed under Boundaries, R12; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:165-185 (comment: `#[track_caller]` adds a location argument; a `#[track_caller]` caller is rejected because THIR can be polymorphic, so allowing just the resolvable `#[track_caller]` callees would make changing `track_caller`-ness a breaking change; the callee's `track_caller`-ness is not checked, mostly for those reasons and also because the shim generated for coercing the function to an `fn()` pointer can always be tail-called) and :394-405 (the error "a function marked with `#[track_caller]` cannot perform a tail-call") [source; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/caller_is_track_caller.rs:4-14 and caller_is_track_caller.stderr:1-11 (`become` from a `#[track_caller]` function is rejected both when the callee lacks the attribute (`a -> b`) and when it has it (`c -> a`)) [test; used in the modeling bridge]

**Design question.** Q3: what signature or argument-area compatibility does frame reuse need?

#### R13. `Layout.sigCheckExplicit_callerLoc_depends_on_cleanup`

**Plain claim.** In the layout toy, at a fixed frame boundary, when the current function has the hidden caller-location parameter and the callee lacks it (`g = ⟨[1], true⟩`, `h = ⟨[1], false⟩`), `sigCheckExplicit g h = true` and `sigCheckFull g h = false`, and frame reuse is sound under caller cleanup and unsound under callee cleanup.

**Kind / tier / depth.** counterexample / T0 (re-derivation: an instance of card R10) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:705-709
theorem sigCheckExplicit_callerLoc_depends_on_cleanup :
    sigCheckExplicit ⟨[1], true⟩ ⟨[1], false⟩ = true ∧
      sigCheckFull ⟨[1], true⟩ ⟨[1], false⟩ = false ∧
      ReuseSound .callerPops (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) ∧
      ¬ ReuseSound .calleePops (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) :=
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`Layout.sigCheckExplicit_callerLoc_depends_on_cleanup`)

**Non-claims.** Listed under Boundaries, R13; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:165-185 (comment: `#[track_caller]` adds a location argument; a `#[track_caller]` caller is rejected because THIR can be polymorphic, so allowing just the resolvable `#[track_caller]` callees would make changing `track_caller`-ness a breaking change; the callee's `track_caller`-ness is not checked, mostly for those reasons and also because the shim generated for coercing the function to an `fn()` pointer can always be tail-called) and :394-405 (the error "a function marked with `#[track_caller]` cannot perform a tail-call") [source; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/caller_is_track_caller.rs:4-14 and caller_is_track_caller.stderr:1-11 (`become` from a `#[track_caller]` function is rejected both when the callee lacks the attribute (`a -> b`) and when it has it (`c -> a`)) [test; used in the modeling bridge]

**Design question.** Q3: what signature or argument-area compatibility does frame reuse need?

#### R14. `naiveSplice_changes_events_inlEx`

**Plain claim.** The naive splice, which keeps the callee's `tailCall`, changes behaviour at a `call` site: in `inlEx` (`main` owns 9, calls `g`, then emits `out 2`; `g` tail-calls `h`, which emits `out 1`) the unbounded `frameReuse` run returns 0 with trace `[out 1, out 2, drop 9]`, while after `inlineCallSite .naive inlEx 0 1` it returns 0 with trace `[drop 9, out 1]`: the kept `tailCall` finalizes and pops `main`'s frame, so `main`'s continuation is lost.

**Kind / tier / depth.** counterexample / T1 (folklore made precise: CompCert's inliner turns an `Itailcall` in an inlined body into an `Icall` to the return point, and LLVM reduces the strength of inlined tail calls; the toy adds a destructor-carrying caller frame whose finalization the kept tail call would trigger) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:225-229
theorem naiveSplice_changes_events_inlEx :
    Observes .frameReuse none inlEx (.returned 0) [.out 1, .out 2, .drop 9] ∧
      Observes .frameReuse none (inlineCallSite .naive inlEx 0 1) (.returned 0) [.drop 9, .out 1] ∧
      ¬ Observes .frameReuse none (inlineCallSite .naive inlEx 0 1) (.returned 0)
          [.out 1, .out 2, .drop 9] := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`naiveSplice_changes_events_inlEx`)

**Non-claims.** Listed under Boundaries, R14; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/inline.rs:429-432 (the inliner returns Err("can't inline functions with tail calls") with a FIXME) and :539 (FIXME: "figure out if we can inline tail calls") [source; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Inlining.v:352-356 (an `Itailcall` in the body of an inlined function that cannot itself be inlined "must be turned into an [Icall] instruction that branches to the return point of the inlined function"), :385-399 (`expand_instr`: the `Itailcall` case keeps `Itailcall` when `ctx.(retinfo)` is `None`, emits `Icall ... rreg rpc` when it is `Some (rpc, rreg)`, and inlines a tail callee with `inline_tail_function`, :324-333); backend/Inliningproof.v:1321-1322 (`transf_program_correct`: forward simulation); driver/Compiler.v:123-125 (Inlining runs after Tail calls). No destructors; no frame bound.
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/lib/Transforms/Utils/InlineFunction.cpp:2594-2613 (comment and code reducing the strength of inlined tail calls: "f -> musttail g -> musttail f  ==>  f -> musttail f" keeps `musttail` to avoid unbounded stack growth for mutually recursive `f` and `g`, while "f -> g -> musttail f  ==>  f -> f") [source comment; used in the modeling bridge]

**Design question.** Q4: why is call-site inlining of a function containing tail calls not the Call/Return splice?

#### R15. `correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow`

**Plain claim.** For every toy program `p`, call site (function `ci`, pc `k`), stack bound `D` (including `none`), outcome `o` that is neither `ub` nor `stackOverflow`, and trace `es`: if the `D`-bounded `frameReuse` run of `p` halts with `o` and `es`, then so does the `D`-bounded `frameReuse` run of `inlineCallSite .corrected p ci k` (the callee's `tailCall h args` rewritten to: arguments into fresh temporaries, `dropSlots` of the callee's slots in reverse declaration order, then `call h` with the call site's destination slot `dst` and continuation pc `next`).

**Kind / tier / depth.** theorem / T1 (folklore made precise: CompCert mechanizes the `Itailcall`-to-`Icall` conversion inside inlined bodies by forward simulation, without destructors and without a frame bound; a statement with pre-jump destructor finalization and a frame bound was not found mechanized) / substantive.

**Proof status.** kernel-checked. Proof outline: a forward simulation in which a callee frame entered at the splice site, together with its caller's frame, corresponds to one merged frame of the spliced caller (caller slots, then callee slots, then temporaries), with frame identities renamed; every step of the original run is matched by zero or more steps of the spliced run (two original unwinding steps by one spliced step), and the spliced stack is never longer than the original one. The proof-support modules are the `Splice*.lean` files.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:106-110
theorem correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow (p : Prog)
    (ci k : Nat) (D : Option Nat) (o : Outcome) (es : List Event) (hub : o ≠ .ub)
    (hso : o ≠ .stackOverflow) :
    Observes .frameReuse D p o es →
      Observes .frameReuse D (inlineCallSite .corrected p ci k) o es := by
```

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hub : o ≠ .ub` | inlining can turn `ub` into defined behaviour | tight: counterexample `correctedSplice_ub_not_preserved_danglingRet` (witness class: a two-function program whose callee returns the address of its own local) |
| `hso : o ≠ .stackOverflow` | inlining removes a frame push, so an overflow can disappear | tight: counterexample `correctedSplice_overflow_not_preserved_plainCall` (witness class: a two-function program with bound `some 1`) |

**Non-vacuity witness.** `inlEx2` (callee with a moved parameter and a local with a destructor) returns 4 with the same trace before and after the splice, unbounded and with bound `some 2`; the outcome is neither `ub` nor `stackOverflow` and the splice changes the program. (`correctedSplice_nonvacuous_inlEx2`)

**Non-claims.** Listed under Boundaries, R15; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/inline.rs:429-432 (the inliner returns Err("can't inline functions with tail calls") with a FIXME) and :539 (FIXME: "figure out if we can inline tail calls") [source; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Inlining.v:352-356 (an `Itailcall` in the body of an inlined function that cannot itself be inlined "must be turned into an [Icall] instruction that branches to the return point of the inlined function"), :385-399 (`expand_instr`: the `Itailcall` case keeps `Itailcall` when `ctx.(retinfo)` is `None`, emits `Icall ... rreg rpc` when it is `Some (rpc, rreg)`, and inlines a tail callee with `inline_tail_function`, :324-333); backend/Inliningproof.v:1321-1322 (`transf_program_correct`: forward simulation); driver/Compiler.v:123-125 (Inlining runs after Tail calls). No destructors; no frame bound.
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/lib/Transforms/Utils/InlineFunction.cpp:2594-2613 (comment and code reducing the strength of inlined tail calls: "f -> musttail g -> musttail f  ==>  f -> musttail f" keeps `musttail` to avoid unbounded stack growth for mutually recursive `f` and `g`, while "f -> g -> musttail f  ==>  f -> f") [source comment; used in the modeling bridge]
* Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao, "End-to-End Verification of Stack-Space Bounds for C Programs", PLDI 2014, pp. 270-281, doi:10.1145/2594291.2594301 (stack-bound preservation through a verified compiler; no explicit tail calls or destructors)
* Y. Wang, P. Wilke, Z. Shao, "An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code", Proc. ACM Program. Lang. 3 (POPL), Article 62, 2019, doi:10.1145/3290375 (Stack-Aware CompCert: a bounded abstract stack, mechanized through tail-call recognition and inlining; no destructors) [bibliographic record checked; publisher text not fetched]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Tailcall.v:17-28 (the documentation says an `Icall` can be turned into an `Itailcall` if the caller's stack block is empty, and explains that otherwise a pointer into it may have been passed to the callee) and :80-98 (`transf_instr`, `transf_function`); backend/Tailcallproof.v:600-601 (`transf_program_correct`: forward simulation RTL -> RTL)

**Design question.** Q4: why is call-site inlining of a function containing tail calls not the Call/Return splice?

#### R16. `correctedTailSiteSplice_mutualRec_runsTo` (+1)

**Plain claim.** For every `N`, the unbounded `frameReuse` run of `mutualRec N` (mutual tail recursion `c ↔ g`, exactly `N` rounds of the pair, no destructors) returns 0 with empty trace, maximum depth exactly 2 and exactly `2 * N` jumps, while the unbounded `frameReuse` run of `inlineTailSite .corrected (mutualRec N) 1 1` (`g` spliced into `c`'s tail site after rewriting that tail call into its pre-jump reading as code) returns 0 with empty trace, maximum depth exactly `N + 2` and no jumps; and for every `C`, under stack bound `some (2 + C)` the `frameReuse` run of `mutualRec (C + 1)` returns 0 with empty trace while that of its corrected tail-site splice halts with `stackOverflow` and empty trace.

**Kind / tier / depth.** theorem / T0 (re-derivation: LLVM's inliner documents that inlining `g` into `f -> musttail g -> musttail f` must keep `musttail` to avoid unbounded stack growth; this is the toy instance with explicit depth equations) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:115-118
theorem correctedTailSiteSplice_mutualRec_runsTo (N : Nat) :
    RunsTo .frameReuse none (mutualRec N) ⟨.returned 0, [], 2, 2 * N⟩ ∧
      RunsTo .frameReuse none (inlineTailSite .corrected (mutualRec N) 1 1)
        ⟨.returned 0, [], N + 2, 0⟩ :=
-- ToyTailCall/Results.lean:124-127
theorem correctedTailSiteSplice_mutualRec_overflows_any_slack (C : Nat) :
    Observes .frameReuse (some (2 + C)) (mutualRec (C + 1)) (.returned 0) [] ∧
      Observes .frameReuse (some (2 + C)) (inlineTailSite .corrected (mutualRec (C + 1)) 1 1)
        .stackOverflow [] :=
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** Instance `N = 3` (`correctedTailSiteSplice_mutualRec3`) and the bounded instance `correctedTailSiteSplice_overflows_mutualRec3` (bound `some 3`: the original returns, the spliced program overflows). (`correctedTailSiteSplice_mutualRec3`, `correctedTailSiteSplice_overflows_mutualRec3`)

**Positive control.** `naiveTailSiteSplice_within_bound_mutualRec3`.

**Non-claims.** Listed under Boundaries, R16; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/inline.rs:429-432 (the inliner returns Err("can't inline functions with tail calls") with a FIXME) and :539 (FIXME: "figure out if we can inline tail calls") [source; used in the modeling bridge]
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/lib/Transforms/Utils/InlineFunction.cpp:2594-2613 (comment and code reducing the strength of inlined tail calls: "f -> musttail g -> musttail f  ==>  f -> musttail f" keeps `musttail` to avoid unbounded stack growth for mutually recursive `f` and `g`, while "f -> g -> musttail f  ==>  f -> f") [source comment; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Inlining.v:352-356 (an `Itailcall` in the body of an inlined function that cannot itself be inlined "must be turned into an [Icall] instruction that branches to the return point of the inlined function"), :385-399 (`expand_instr`: the `Itailcall` case keeps `Itailcall` when `ctx.(retinfo)` is `None`, emits `Icall ... rreg rpc` when it is `Some (rpc, rreg)`, and inlines a tail callee with `inline_tail_function`, :324-333); backend/Inliningproof.v:1321-1322 (`transf_program_correct`: forward simulation); driver/Compiler.v:123-125 (Inlining runs after Tail calls). No destructors; no frame bound.
* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719 (space-efficiency formulation of proper tail calls; no destructors, no inlining)
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]

**Design question.** Q4: why is call-site inlining of a function containing tail calls not the Call/Return splice?

#### R17. `dropList_clears_pending_of_ne_abort` (+1)

**Plain claim.** (a) For every function `fn` and frame `fr`, if finalizing `fr`'s pending slots does not abort, no pending drop remains in the resulting frame; (b) for every state `st` about to execute `tailCall f args` under `frameReuse` (any bound `D`) — not unwinding, with no pending return, and with the arguments evaluating without `ub` to values `vs` and evaluated frame `fr1` — if no pending destructor of `fr1` panics, the step emits `finalizationEvents fn fr1` (one `drop` per pending slot, in `pendingDrops` order), then performs `push` of `f` with `vs` onto the frames below the current one (the current frame is no longer on the stack), and, if that push succeeds, increments the tail-call counter (`bumpTail`).

**Kind / tier / depth.** theorem / T1 (folklore made precise, as a reference point: the one-step effect of pre-jump finalization stated for the toy; definitional) / definitional.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:135-137
theorem dropList_clears_pending_of_ne_abort (fn : Fn) (fr : Frame)
    (hna : (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort) :
    pendingDrops fn (dropList fn fr (pendingDrops fn fr) false).1 = [] := by
-- ToyTailCall/Results.lean:155-160
theorem frameReuse_tailCall_finalizes_then_push_of_noPanic {p : Prog} {st : State} {fn : Fn}
    {fr : Frame} {rest : List Frame} {f : FnId} {args : List Operand} {vs : List Val}
    {fr1 : Frame} (D : Option Nat) (hat : AtTailCall p st fn fr rest f args vs fr1)
    (hnp : panickingPending fn fr1 = []) :
    step .frameReuse D p st =
      bumpTail (push D p { st with events := st.events ++ finalizationEvents fn fr1 } rest f vs) := by
```

Unfolded (prose): `AtTailCall p st fn fr rest f args vs fr1` bundles: `st.stack = fr :: rest`, `st.unwinding = false`, `fr.pendingRet = none`, `p.fns[fr.fn]? = some fn`, `fn.code[fr.pc]? = some (.tailCall f args)`, `evalOps rest fr args = some (vs, fr1)`.

**Hypothesis ledger.**

| hypothesis | theorem | why | tightness |
| --- | --- | --- | --- |
| `hna : (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort` | (a) | an aborting finalization stops before the remaining slots | tight: counterexample `dropList_abort_leaves_pending` (witness class: a frame with two panicking destructors) |
| `hat.not_unwinding : st.unwinding = false` | (b) | field of `AtTailCall`; while unwinding, the step drops and pops instead of executing the tail call | tight: counterexample `finalizes_then_push_fails_when_unwinding` (witness class: the `panicFin` state with `unwinding := true`) |
| `hat.no_pendingRet : fr.pendingRet = none` | (b) | field of `AtTailCall`; a frame with a pending return returns instead | tight: counterexample `finalizes_then_push_fails_with_pendingRet` (witness class: the `panicFin` frame with a pending return value) |
| `hat.args_eq : evalOps rest fr args = some (vs, fr1)` | (b) | field of `AtTailCall`; if argument evaluation is `ub`, the step halts with `ub` before any drop | tight: counterexample `finalizes_then_push_fails_when_args_ub` (witness class: a two-function program (`badArgTailProg`) whose tail-call argument loads through an integer) |
| `hat.stack_eq, hat.fn_eq, hat.instr_eq` | (b) | fields of `AtTailCall`, taken jointly; they identify the instruction being executed as `tailCall f args` in frame `fr` of function `fn` | tight: counterexample `finalization_fails_at_other_instr` (witness class: the `panicFin` state at a `panic` instruction (`instr_eq` fails, the other fields hold)) |
| `hnp : panickingPending fn fr1 = []` | (b) | a panicking destructor starts unwinding instead of the push | tight: counterexample `finalizes_then_push_fails_with_panic` (witness class: the `panicFin` state with one panicking destructor) |

**Non-vacuity witness.** An all-quiet three-slot frame for (a); the all-quiet `panicFin` state for (b). (`dropList_clears_pending_nonvacuous`, `finalizes_then_push_nonvacuous`)

**Non-claims.** Listed under Boundaries, R17; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825 (documentation of `TailCall`: pop of the current stack frame, then a call with the return address of the current caller) and :829-833 (arguments are owned by the callee) [documentation; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Cminor.v:468-475 (`step_tailcall` frees the stack block before entering the callee)

**Design question.** Q5: what does pre-jump finalization guarantee when a destructor panics, and why must the frame stay until finalization ends?

#### R18. `frameReuse_finalization_unique_panic_drops_rest_then_unwinds`

**Plain claim.** For every state `st` about to execute `tailCall f args` under `frameReuse` (any bound `D`) — not unwinding, with no pending return, and with the arguments evaluating without `ub` to evaluated frame `fr1` — if exactly one pending destructor of `fr1` panics, the step still emits one `drop` per slot pending in `fr1` (slots moved into the arguments are no longer pending), in `pendingDrops` order, removes the frame, and continues unwinding with the frames below (`unwindBelow`: the original caller's cleanup, or outcome `panicked` if there is none); the already-evaluated argument values are discarded without a `drop` event.

**Kind / tier / depth.** theorem / T1 (folklore made precise, as a reference point: unwinding through pre-jump finalization stated for one step; definitional) / definitional.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:170-175
theorem frameReuse_finalization_unique_panic_drops_rest_then_unwinds {p : Prog} {st : State}
    {fn : Fn} {fr : Frame} {rest : List Frame} {f : FnId} {args : List Operand} {vs : List Val}
    {fr1 : Frame} (D : Option Nat) (hat : AtTailCall p st fn fr rest f args vs fr1)
    (hone : (panickingPending fn fr1).length = 1) :
    step .frameReuse D p st =
      unwindBelow { st with events := st.events ++ finalizationEvents fn fr1 } rest := by
```

Unfolded (prose): `AtTailCall` as in R17. `unwindBelow st rest` halts with `panicked` if `rest = []` and otherwise continues with stack `rest` and `unwinding := true`.

**Hypothesis ledger.**

| hypothesis | why | tightness |
| --- | --- | --- |
| `hat.not_unwinding : st.unwinding = false` | field of `AtTailCall`; while unwinding, a panicking destructor aborts | tight: counterexample `panic_drops_rest_fails_when_unwinding` (witness class: the `panicFin` state with `unwinding := true`) |
| `hat.no_pendingRet : fr.pendingRet = none` | field of `AtTailCall`; a frame with a pending return returns, dropping slots moved into the arguments too | tight: counterexample `panic_drops_rest_fails_with_pendingRet` (witness class: a frame with a pending return whose tail call moves a slot) |
| `hat.args_eq : evalOps rest fr args = some (vs, fr1)` | field of `AtTailCall`; if argument evaluation is `ub`, the step halts with `ub` before any drop | tight: counterexample `panic_drops_rest_fails_when_args_ub` (witness class: a two-function program (`badArgTailProg`) whose tail-call argument loads through an integer) |
| `hat.stack_eq, hat.fn_eq, hat.instr_eq` | fields of `AtTailCall`, taken jointly; they identify the instruction being executed | tight: counterexample `panic_drops_rest_fails_at_other_instr` (witness class: the `panicFin` state in the three-function program `panicFinOnePanicNoTail` (its function `t` is `panicFinTOnePanicNoTail`), whose instruction at the frame's `pc` is `panic` and which has exactly one panicking pending destructor (`instr_eq` fails; `hone` and the other fields hold)) |
| `hone : (panickingPending fn fr1).length = 1` | exactly one: with none the step pushes the callee; with two the second panic (while unwinding) aborts | tight: counterexample `panic_drops_rest_fails_with_zero_panics`, `panic_drops_rest_fails_with_two_panics` (witness class: the `panicFin` state with zero, and with two, panicking destructors) |

**Non-vacuity witness.** `panicFin` with one panicking destructor: events `[drop 3, drop 2, drop 1]`. (`panic_drops_rest_nonvacuous`)

**Non-claims.** Listed under Boundaries, R18; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825 (documentation of `TailCall`: pop of the current stack frame, then a call with the return address of the current caller) and :829-833 (arguments are owned by the callee) [documentation; used in the modeling bridge]

**Design question.** Q5: what does pre-jump finalization guarantee when a destructor panics, and why must the frame stay until finalization ends?

#### R19. `popFirst_ub_with_pending_drop_dtorProg`

**Plain claim.** In the toy, where a destructor reaches its slot through the frame's identity (as a `deref` does, the counterpart of `Drop::drop(&mut self)`), removing the frame before its pending destructors run makes running them `ub`: for `dtorProg` the unbounded `frameReuse` run returns 0 with trace `[drop 7, out 1]`, while the `popFirst` run halts with `ub` and an empty trace.

**Kind / tier / depth.** counterexample / T0 (re-derivation: running a destructor on storage that has been deallocated is a use after free; instance in the toy) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Counterexamples.lean:667-670
theorem popFirst_ub_with_pending_drop_dtorProg :
    Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      Observes .popFirst none dtorProg .ub [] ∧
      ¬ Observes .popFirst none dtorProg (.returned 0) [.drop 7, .out 1] := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** (counterexample; the instance is the witness) (`popFirst_ub_with_pending_drop_dtorProg`)

**Positive control.** `popFirst_agrees_without_pending_drops_chain3`.

**Non-claims.** Listed under Boundaries, R19; a reader of this result must read them with it.

**Prior art.**

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825 (documentation of `TailCall`: pop of the current stack frame, then a call with the return address of the current caller) and :829-833 (arguments are owned by the callee) [documentation; used in the modeling bridge]
* AbsInt/CompCert v3.16 (a4ad87b17898cf7b7c8638c32ad694a15f7c0032) backend/Cminor.v:468-475 (`step_tailcall` frees the stack block before entering the callee)

**Design question.** Q5: what does pre-jump finalization guarantee when a destructor panics, and why must the frame stay until finalization ends?

#### R20. `Layout.reuseSoundAt_zero_iff` (+2)

**Plain claim.** In the layout toy with the boundary moved by `δ` cells before the jump (callee area at `[b + δ - inH, b + δ)`), for all `δ`, `inG` and `inH`: `δ = 0` gives exactly the fixed-boundary `ReuseSound`; under callee cleanup frame reuse is sound iff `δ = inH - inG` (integer subtraction), so a suitable relocation exists for all area sizes; under caller cleanup it is sound iff `δ = 0` and `inH ≤ inG`, so relocation does not help.

**Kind / tier / depth.** characterization / T1 (folklore made precise: LLVM documents that the callee popping the argument area makes mandatory tail calls possible and that `musttail` under `swifttailcc`/`tailcc` does not require matching prototypes; a statement relating cleanup convention, boundary relocation and argument areas was not found mechanized) / shallow.

**Proof status.** kernel-checked.

Basis: execution (Lean kernel check).

**Statement.**

```lean
-- ToyTailCall/Results.lean:240-241
theorem reuseSoundAt_zero_iff (cl : Cleanup) (inG inH : Nat) :
    ReuseSoundAt cl 0 inG inH ↔ ReuseSound cl inG inH := by
-- ToyTailCall/Results.lean:259-260
theorem reuseSoundAt_calleePops_iff (δ : Int) (inG inH : Nat) :
    ReuseSoundAt .calleePops δ inG inH ↔ δ = (inH : Int) - inG := by
-- ToyTailCall/Results.lean:272-273
theorem reuseSoundAt_callerPops_iff (δ : Int) (inG inH : Nat) :
    ReuseSoundAt .callerPops δ inG inH ↔ δ = 0 ∧ inH ≤ inG := by
```

**Hypothesis ledger.**

No hypotheses beyond the quantified variables.

**Non-vacuity witness.** Under callee cleanup, `inG = 1`, `inH = 2`: unsound at the fixed boundary, sound with `δ = 1`; under caller cleanup, `δ = 0`, `inG = 2`, `inH = 1`. (`Layout.reuseSoundAt_calleePops_nonvacuous`, `Layout.reuseSoundAt_callerPops_nonvacuous`)

**Non-claims.** Listed under Boundaries, R20; a reader of this result must read them with it.

**Prior art.**

* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:498-501 (`swifttailcc`: "the callee pops the argument area of the stack so that mandatory tail calls are possible as in ``tailcc``") and :12626-12637 (prototype matching is required for `musttail` unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]
* llvm/llvm-project llvmorg-19.1.0 (a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4) llvm/docs/LangRef.rst:12593-12637 (`musttail`: no unbounded stack growth in recursive cycles; "Both markers imply that the callee does not access allocas from the caller"; ABI attributes and caller/callee prototypes must match unless the convention is `swifttailcc` or `tailcc`) [documentation; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/signature-mismatch.rs:28-34 (comment: "tailcc does not need the signatures to match, but only tailcc can tail call tailcc.") [test; used in the modeling bridge]
* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:134-136 (ABI equality check) and :150-163 (signature equality check, skipped when the callee ABI is `RustTail`) [source; used in the modeling bridge]

**Design question.** Q3: what signature or argument-area compatibility does frame reuse need?

### Modeling bridge (`derived (modeling bridge)`; documented behaviour, no measurements)

Each paragraph below is a separate claim labelled `derived (modeling bridge)`: it connects a toy result to documented upstream behaviour by analogy. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, CompCert or LLVM. No upstream behaviour was executed or measured; quotes are verbatim from the pinned files, each with its full line range.

**B1 (frame reuse; cards R1, R3, R4, R17).** The MIR documentation describes `TailCall` as a pop of the current frame followed by a call with the current caller's return address, which is the toy's `frameReuse`.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:810-825`.

```rust
    /// Tail call.
    ///
    /// Roughly speaking this is a chimera of [`Call`] and [`Return`], with some caveats.
    /// Semantically tail calls consists of two actions:
    /// - pop of the current stack frame
    /// - a call to the `func`, with the return address of the **current** caller
    ///   - so that a `return` inside `func` returns to the caller of the caller
    ///     of the function that is currently being executed
    ///
    /// Note that in difference with [`Call`] this is missing
    /// - `destination` (because it's always the return place)
    /// - `target` (because it's always taken from the current stack frame)
    /// - `unwind` (because it's always taken from the current stack frame)
    ///
    /// [`Call`]: TerminatorKind::Call
    /// [`Return`]: TerminatorKind::Return
```

The same terminator documents that the arguments are owned by the callee.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:829-833`.

```rust
        /// Arguments the function is called with.
        /// These are owned by the callee, which is free to modify them.
        /// This allows the memory occupied by "by-value" arguments to be
        /// reused across function calls without duplicating the contents.
        args: Box<[Spanned<Operand<'tcx>>]>,
```

Derived: in the toy, removing the frame before the call is proved observationally equivalent to keeping a finalized frame (`preJump`) under the hypothesis `NoStackBorrow` (R1); without that hypothesis the equivalence fails on `borrowProg` (R7); and frame reuse differs from call-then-return on `dtorProg` (R2).

Basis: derived (modeling bridge): documentation and source quoted verbatim at the pinned revision, related to the kernel-checked toy results by the analogy stated in this paragraph; nothing was executed.

**B2 (drop order; cards R4, R6).** A rustc UI test asserts ascending drop order for the `become` version and descending order for the `return` version, with labels increasing with recursion depth, which is the order of `countUp_frameReuse_runsTo` versus `countUp_callReturn_runsTo`.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/drop-order.rs:7-39`.
The quote is verbatim.
It shows `main` and the two recursive functions,
`tail_recursive` (with `become`) and `simply_recursive` (with `return`):

```rust
fn main() {
    let tail_counter = Default::default();
    tail_recursive(0, &tail_counter);
    assert_eq!(tail_counter.into_inner(), (0..128).collect::<Vec<u8>>());

    let simply_counter = Default::default();
    simply_recursive(0, &simply_counter);
    assert_eq!(simply_counter.into_inner(), (0..128).rev().collect::<Vec<u8>>());

    let scope_counter = Default::default();
    out_of_inner_scope(&scope_counter);
    assert_eq!(scope_counter.into_inner(), (0..8).collect::<Vec<u8>>());
}

fn tail_recursive(n: u8, order: &RefCell<Vec<u8>>) {
    if n >= 128 {
        return;
    }

    let _local = DropCounter(n, order);

    become tail_recursive(n + 1, order)
}

fn simply_recursive(n: u8, order: &RefCell<Vec<u8>>) {
    if n >= 128 {
        return;
    }

    let _local = DropCounter(n, order);

    return simply_recursive(n + 1, order);
}
```

Basis: derived (modeling bridge): documentation and source quoted verbatim at the pinned revision, related to the kernel-checked toy results by the analogy stated in this paragraph; nothing was executed.

**B3 (stack borrows; cards R7, R8, R9).** A rustc UI test rejects passing a borrow of a local to a tail call.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/ctfe-arg-bad-borrow.rs:4-10`.
The quote is verbatim.
The local `local` is borrowed in the argument of `become`;
`Type` (line 12 of the file) has no `Drop` implementation:

```rust
pub const fn test(_: &Type) {
    const fn takes_borrow(_: &Type) {}

    let local = Type;
    become takes_borrow(&local);
    //~^ error: `local` does not live long enough
}
```

The expected compiler output of that test, also quoted in full.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/ctfe-arg-bad-borrow.stderr:1-11`.
The quote is verbatim.
The primary message is E0597;
"`local` dropped here while still borrowed" is a span label:

```text
error[E0597]: `local` does not live long enough
  --> $DIR/ctfe-arg-bad-borrow.rs:8:25
   |
LL |     let local = Type;
   |         ----- binding `local` declared here
LL |     become takes_borrow(&local);
   |                         ^^^^^^- `local` dropped here while still borrowed
   |                         |
   |                         borrowed value does not live long enough

error: aborting due to 1 previous error
```

Derived: the rejected program has the shape of `borrowProg` (R7). The toy escape check (R8) is a different, flow-insensitive check; no claim is made about how rustc decides the rejection. CompCert documents the same hazard for its tail-call recognition.
Source: `AbsInt/CompCert@a4ad87b17898cf7b7c8638c32ad694a15f7c0032 backend/Tailcall.v:17-28`.

```coq
(** An [Icall] instruction that stores its result in register [rreg]
  can be turned into a tail call if:
- its successor is a [Ireturn None] or [Ireturn (Some rreg)] instruction;
- the stack block of the current function is empty: [stacksize = 0].

If the current function had a non-empty stack block, it could be that
the called function accesses it, for instance if a pointer into the
stack block is passed as an argument.  In this case, it would be
semantically incorrect to deallocate the stack block before the call,
as [Itailcall] does.  Therefore, the optimization can only be performed if
the stack block of the current function is empty, in which case it makes
no semantic difference to deallocate it before or after the call.
```

The LLVM LangRef documents the corresponding assumption for `musttail`.
Source: `llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 llvm/docs/LangRef.rst:12611`.

```rst
   Both markers imply that the callee does not access allocas from the caller.
```

Basis: derived (modeling bridge): documentation and source quoted verbatim at the pinned revision, related to the kernel-checked toy results by the analogy stated in this paragraph; nothing was executed.

**B4 (argument areas and hidden parameters; cards R10–R13, R20).** rustc checks ABI equality before accepting `become`.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:134-136`.

```rust
        if caller_sig.abi() != callee_sig.abi() {
            self.report_abi_mismatch(expr.span, caller_sig.abi(), callee_sig.abi());
        }
```

It checks signature equality unless the callee's ABI is `RustTail`.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:150-163`.

```rust
        if caller_sig.inputs_and_output != callee_sig.inputs_and_output
            && !matches!(callee_sig.abi(), ExternAbi::RustTail)
        {
            let caller_ty = self.tcx.type_of(self.caller_def_id).skip_binder();

            self.report_signature_mismatch(
                expr.span,
                self.tcx.liberate_late_bound_regions(
                    CRATE_DEF_ID.to_def_id(),
                    caller_ty.fn_sig(self.tcx),
                ),
                self.tcx.liberate_late_bound_regions(CRATE_DEF_ID.to_def_id(), ty.fn_sig(self.tcx)),
            );
        }
```

Its source comment gives two reasons, both quoted here in full: a `#[track_caller]` caller is rejected because THIR can be polymorphic, so allowing just the resolvable `#[track_caller]` callees would make changing `track_caller`-ness a breaking change; and the callee's `track_caller`-ness is not checked, mostly for those reasons and also because the shim generated for coercing the function to an `fn()` pointer can always be tail-called.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:165-185`.

```rust
        {
            // `#[track_caller]` affects the ABI of a function (by adding a location argument),
            // so a `track_caller` can only tail call other `track_caller` functions.
            //
            // The issue is however that we can't know if a function is `track_caller` or not at
            // this point (THIR can be polymorphic, we may have an unresolved trait function).
            // We could only allow functions that we *can* resolve and *are* `track_caller`,
            // but that would turn changing `track_caller`-ness into a breaking change,
            // which is probably undesirable.
            //
            // Also note that we don't check callee's `track_caller`-ness at all, mostly for the
            // reasons above, but also because we can always tailcall the shim we'd generate for
            // coercing the function to an `fn()` pointer. (although in that case the tailcall is
            // basically useless -- the shim calls the actual function, so tailcalling the shim is
            // equivalent to calling the function)
            let caller_needs_location = self.caller_needs_location();

            if caller_needs_location {
                self.report_track_caller_caller(expr.span);
            }
        }
```

The error it reports.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_build/src/check_tail_calls.rs:394-405`.

```rust
    fn report_track_caller_caller(&mut self, sp: Span) {
        let err = self
            .tcx
            .dcx()
            .struct_span_err(
                sp,
                "a function marked with `#[track_caller]` cannot perform a tail-call",
            )
            .emit();

        self.found_errors = Err(err);
    }
```

A rustc UI test rejects `become` from a `#[track_caller]` function whether or not the callee has the attribute.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/caller_is_track_caller.rs:4-14`.
The quote is verbatim:
`a -> b` (callee without the attribute) and
`c -> a` (callee with the attribute) are both rejected.

```rust
#[track_caller]
fn a() {
    become b(); //~ error: a function marked with `#[track_caller]` cannot perform a tail-call
}

fn b() {}

#[track_caller]
fn c() {
    become a(); //~ error: a function marked with `#[track_caller]` cannot perform a tail-call
}
```

(Lines 16-23 of the same file reject the same tail call from a `#[track_caller]` trait method.) The expected output for the two functions quoted.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/caller_is_track_caller.stderr:1-11`.
The quote is verbatim.
One error per function,
at lines 6 and 13 of the test:

```text
error: a function marked with `#[track_caller]` cannot perform a tail-call
  --> $DIR/caller_is_track_caller.rs:6:5
   |
LL |     become b();
   |     ^^^^^^^^^^

error: a function marked with `#[track_caller]` cannot perform a tail-call
  --> $DIR/caller_is_track_caller.rs:13:5
   |
LL |     become a();
   |     ^^^^^^^^^^
```

The same test directory documents, for the `"tail"` ABI, that signatures need not match.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe tests/ui/explicit-tail-calls/signature-mismatch.rs:28-34`.
The quote is verbatim.
It is the last case of that test;
the `become` is rejected for the ABI mismatch:

```rust
extern "tail" fn _tailcc() {}

fn _f4() {
    // tailcc does not need the signatures to match,
    // but only tailcc can tail call tailcc.
    become _tailcc(); //~ error: mismatched function ABIs
}
```

Derived: in the layout toy at a fixed boundary, equal full signatures suffice (R11), equality of the non-hidden parameters (`sigCheckExplicit`) does not (R12), and the effect of a hidden parameter present in the current function but absent in the callee depends on the cleanup convention (R13). The toy check `sigCheckFull` accepts a caller and callee that both take the hidden parameter, whereas rustc rejects every `become` from a `#[track_caller]` function, including that case; `sigCheckFull` is not a model of rustc's check. With the boundary relocatable, callee cleanup admits all area sizes and caller cleanup does not (R20); the toy says nothing about which convention rustc or LLVM uses. LLVM documents that callee cleanup is what makes mandatory tail calls possible under `swifttailcc`.
Source: `llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 llvm/docs/LangRef.rst:498-501`.

```rst
"``swifttailcc``"
    This calling convention is like ``swiftcc`` in most respects, but also the
    callee pops the argument area of the stack so that mandatory tail calls are
    possible as in ``tailcc``.
```

CompCert's condition is stronger than area fit (no stack arguments at all).
Source: `AbsInt/CompCert@a4ad87b17898cf7b7c8638c32ad694a15f7c0032 backend/Conventions.v:143-155`.

```coq
(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (regs_of_rpairs (loc_arguments s)) ->
  match l with R _ => True | S _ _ _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  List.forallb
    (fun l => match l with R _ => true | S _ _ _ => false end)
    (regs_of_rpairs (loc_arguments sg)).
```

Basis: derived (modeling bridge): documentation and source quoted verbatim at the pinned revision, related to the kernel-checked toy results by the analogy stated in this paragraph; nothing was executed.

**B5 (inlining; cards R14–R16).** The rustc MIR inliner refuses callees that contain tail calls.
Source: `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_mir_transform/src/inline.rs:429-432`.

```rust
            } else if let TerminatorKind::TailCall { .. } = term.kind {
                // FIXME(explicit_tail_calls): figure out how exactly functions containing tail
                // calls can be inlined (and if they even should)
                return Err("can't inline functions with tail calls");
```

CompCert's inliner, which runs after its tail-call recognition, distinguishes the two kinds of site: inside an inlined body an `Itailcall` that is not itself inlined becomes an `Icall` to the return point, and at a tail site (`retinfo = None`) it stays an `Itailcall`.
Source: `AbsInt/CompCert@a4ad87b17898cf7b7c8638c32ad694a15f7c0032 backend/Inlining.v:385-399`.

```coq
  | Itailcall sg ros args =>
      match can_inline ros with
      | Cannot_inline =>
          match ctx.(retinfo) with
          | None =>
              set_instr (spc ctx pc)
                        (Itailcall sg (sros ctx ros) (sregs ctx args))
          | Some(rpc, rreg) =>
              set_instr (spc ctx pc)
                        (Icall sg (sros ctx ros) (sregs ctx args) rreg rpc)
          end
      | Can_inline id f P Q =>
          do n <- inline_tail_function ctx id f Q args;
          set_instr (spc ctx pc) (Inop n)
      end
```

LLVM's inliner documents the mutual-recursion case.
Source: `llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 llvm/lib/Transforms/Utils/InlineFunction.cpp:2594-2613`.

```cpp
        // We need to reduce the strength of any inlined tail calls.  For
        // musttail, we have to avoid introducing potential unbounded stack
        // growth.  For example, if functions 'f' and 'g' are mutually recursive
        // with musttail, we can inline 'g' into 'f' so long as we preserve
        // musttail on the cloned call to 'f'.  If either the inlined call site
        // or the cloned call site is *not* musttail, the program already has
        // one frame of stack growth, so it's safe to remove musttail.  Here is
        // a table of example transformations:
        //
        //    f -> musttail g -> musttail f  ==>  f -> musttail f
        //    f -> musttail g ->     tail f  ==>  f ->     tail f
        //    f ->          g -> musttail f  ==>  f ->          f
        //    f ->          g ->     tail f  ==>  f ->          f
        //
        // Inlined notail calls should remain notail calls.
        CallInst::TailCallKind ChildTCK = CI->getTailCallKind();
        if (ChildTCK != CallInst::TCK_NoTail)
          ChildTCK = std::min(CallSiteTailKind, ChildTCK);
        CI->setTailCallKind(ChildTCK);
        InlinedMustTailCalls |= CI->isMustTailCall();
```

This is documented behaviour; it is not characterized further here. Derived: R14 shows in the toy why keeping the callee's tail call in a `Call`/`Return` splice is wrong at a call site; R15 proves that the corrected splice preserves non-`ub`, non-overflow outcomes and traces under every frame bound at call sites; R16 proves that the same splice applied at a tail site of `mutualRec` loses every additive bound, in line with the `musttail`-preserving rule documented by LLVM and the `Itailcall`-preserving rule of CompCert.

Basis: derived (modeling bridge): documentation and source quoted verbatim at the pinned revision, related to the kernel-checked toy results by the analogy stated in this paragraph; nothing was executed.

**B6 (proposal status).** RFC 3407 (rust-lang/rfcs#3407, "Explicit Tail Calls") is an open, unmerged proposal and rust-lang/rust#112788 is its open tracking issue; neither is used as normative text here.

### Auxiliary lemmas and witnesses cited by name

Every package-local declaration mentioned by name above and not quoted earlier, quoted verbatim.

```lean
-- ToyTailCall/Counterexamples.lean:54-56
theorem noStackBorrow_not_necessary_ignorePtrProg :
    ¬ NoStackBorrow ignorePtrProg ∧
      ∀ o es, Observes .frameReuse none ignorePtrProg o es ↔ Observes .preJump none ignorePtrProg o es := by
-- ToyTailCall/Counterexamples.lean:64-67
theorem frameReuse_of_preJump_fails_borrowProg :
    ¬ NoStackBorrow borrowProg ∧ (.returned 5 : Outcome) ≠ .stackOverflow ∧
      Observes .preJump none borrowProg (.returned 5) [] ∧
      ¬ Observes .frameReuse none borrowProg (.returned 5) [] := by
-- ToyTailCall/Counterexamples.lean:78-79
theorem countUp3_bound4_frameReuse : RunsTo .frameReuse (some 4) (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ := ⟨40, by decide⟩
-- ToyTailCall/Counterexamples.lean:84-87
theorem frameReuse_of_preJump_fails_for_overflow_countUp3 :
    NoStackBorrow (countUp 3) ∧
      Observes .preJump (some 4) (countUp 3) .stackOverflow [.drop 0, .drop 1, .drop 2] ∧
      ¬ Observes .frameReuse (some 4) (countUp 3) .stackOverflow [.drop 0, .drop 1, .drop 2] := by
-- ToyTailCall/Counterexamples.lean:93-95
theorem countUp3_bound0_overflows :
    RunsTo .preJump (some 0) (countUp 3) ⟨.stackOverflow, [], 0, 0⟩ ∧
      RunsTo .frameReuse (some 0) (countUp 3) ⟨.stackOverflow, [], 0, 0⟩ :=
-- ToyTailCall/Counterexamples.lean:102-103
theorem runsTo_bound0_of_entryOk (sem : Sem) (p : Prog) (h : EntryOk p) :
    RunsTo sem (some 0) p ⟨.stackOverflow, [], 0, 0⟩ := by
-- ToyTailCall/Counterexamples.lean:110-112
theorem paramEntryProg_bound0_ub :
    Observes .preJump (some 0) paramEntryProg .ub [] ∧
      Observes .frameReuse (some 0) paramEntryProg .ub [] :=
-- ToyTailCall/Counterexamples.lean:117-119
theorem frameReuse_of_preJump_nonvacuous_countUp3 :
    NoStackBorrow (countUp 3) ∧ (.returned 0 : Outcome) ≠ .stackOverflow ∧
      Observes .preJump (some 5) (countUp 3) (.returned 0) [.drop 0, .drop 1, .drop 2] :=
-- ToyTailCall/Counterexamples.lean:125-128
theorem frameReuse_iff_preJump_nonvacuous_dtorProg :
    NoStackBorrow dtorProg ∧
      Observes .frameReuse none dtorProg (.returned 0) [.drop 7, .out 1] ∧
      Observes .preJump none dtorProg (.returned 0) [.drop 7, .out 1] :=
-- ToyTailCall/Counterexamples.lean:133-134
theorem countUp3_frameReuse : RunsTo .frameReuse none (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ := ⟨16, by decide⟩
-- ToyTailCall/Counterexamples.lean:136-137
theorem countUp3_preJump : RunsTo .preJump none (countUp 3)
    ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 5, 3⟩ := ⟨19, by decide⟩
-- ToyTailCall/Counterexamples.lean:139-140
theorem countUp3_callReturn : RunsTo .callReturn none (countUp 3)
    ⟨.returned 0, [.drop 2, .drop 1, .drop 0], 5, 3⟩ := ⟨19, by decide⟩
-- ToyTailCall/Counterexamples.lean:145-146
theorem orderDemo_frameReuse : RunsTo .frameReuse none orderDemo
    ⟨.returned 0, [.drop 14, .drop 12, .drop 11, .drop 10, .out 99, .drop 13], 2, 1⟩ :=
-- ToyTailCall/Counterexamples.lean:158-161
theorem callFree_nonvacuous_chain3 :
    CallFree chain3 = true ∧ EntryOk chain3 ∧
      RunsTo .frameReuse none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ ∧
      RunsTo .preJump none chain3 ⟨.returned 0, [.out 1], 3, 2⟩ :=
-- ToyTailCall/Counterexamples.lean:166-168
theorem callFree_needed_frameReuse_countUp3 :
    CallFree (countUp 3) = false ∧ EntryOk (countUp 3) ∧ RunsTo .frameReuse none (countUp 3)
      ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 2, 3⟩ ∧ (2 : Nat) ≠ 1 :=
-- ToyTailCall/Counterexamples.lean:173-175
theorem callFree_needed_preJump_countUp3 :
    CallFree (countUp 3) = false ∧ EntryOk (countUp 3) ∧ RunsTo .preJump none (countUp 3)
      ⟨.returned 0, [.drop 0, .drop 1, .drop 2], 5, 3⟩ ∧ (5 : Nat) ≠ 3 + 1 :=
-- ToyTailCall/Counterexamples.lean:180-183
theorem entryOk_needed_emptyProg :
    CallFree emptyProg = true ∧ ¬ EntryOk emptyProg ∧
      RunsTo .frameReuse none emptyProg ⟨.ub, [], 0, 0⟩ ∧
      RunsTo .preJump none emptyProg ⟨.ub, [], 0, 0⟩ ∧ (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 0 + 1 :=
-- ToyTailCall/Counterexamples.lean:189-193
theorem entryOk_needed_paramEntryProg :
    CallFree paramEntryProg = true ∧ (∃ fn, paramEntryProg.fns[0]? = some fn) ∧
      ¬ EntryOk paramEntryProg ∧
      RunsTo .frameReuse none paramEntryProg ⟨.ub, [], 0, 0⟩ ∧
      RunsTo .preJump none paramEntryProg ⟨.ub, [], 0, 0⟩ ∧ (0 : Nat) ≠ 1 ∧ (0 : Nat) ≠ 0 + 1 := by
-- ToyTailCall/Counterexamples.lean:204-205
theorem escapeCheck_needed_borrowProg :
    EscapeCheckAccepts borrowProg = false ∧ ¬ NoStackBorrow borrowProg :=
-- ToyTailCall/Counterexamples.lean:238-247
theorem correctedSplice_nonvacuous_inlEx2 :
    (.returned 4 : Outcome) ≠ .ub ∧ (.returned 4 : Outcome) ≠ .stackOverflow ∧
      inlineCallSite .corrected inlEx2 0 1 ≠ inlEx2 ∧
      Observes .frameReuse none inlEx2 (.returned 4) [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse (some 2) inlEx2 (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse none (inlineCallSite .corrected inlEx2 0 1) (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] ∧
      Observes .frameReuse (some 2) (inlineCallSite .corrected inlEx2 0 1) (.returned 4)
        [.out 3, .drop 5, .out 1, .out 2, .drop 9] :=
-- ToyTailCall/Counterexamples.lean:257-261
theorem correctedSplice_tailCalls_differ_inlEx2 :
    RunsTo .frameReuse none inlEx2
      ⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 1⟩ ∧
      RunsTo .frameReuse none (inlineCallSite .corrected inlEx2 0 1)
        ⟨.returned 4, [.out 3, .drop 5, .out 1, .out 2, .drop 9], 2, 0⟩ :=
-- ToyTailCall/Counterexamples.lean:266-268
theorem correctedSplice_ub_not_preserved_danglingRet :
    Observes .frameReuse none danglingRet .ub [] ∧
      ¬ Observes .frameReuse none (inlineCallSite .corrected danglingRet 0 0) .ub [] := by
-- ToyTailCall/Counterexamples.lean:278-280
theorem correctedSplice_overflow_not_preserved_plainCall :
    Observes .frameReuse (some 1) plainCall .stackOverflow [] ∧
      ¬ Observes .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0) .stackOverflow [] := by
-- ToyTailCall/Counterexamples.lean:291-293
theorem correctedSplice_masks_borrow_ub_borrowProg :
    Observes .frameReuse none borrowProg .ub [] ∧
      Observes .frameReuse none (inlineCallSite .corrected borrowProg 0 0) (.returned 5) [] :=
-- ToyTailCall/Counterexamples.lean:300-309
theorem correctedSplice_raw_values_differ_ptrRetProg :
    (match run .frameReuse none ptrRetProg 3 (start none ptrRetProg) with
     | .running st => st.stack.head?.map (fun fr => fr.get 0)
     | _ => none) = some (.ptr 1 0) ∧
    (match run .frameReuse none (inlineCallSite .corrected ptrRetProg 0 0) 6
        (start none (inlineCallSite .corrected ptrRetProg 0 0)) with
     | .running st => st.stack.head?.map (fun fr => fr.get 0)
     | _ => none) = some (.ptr 0 1) ∧
    Observes .frameReuse none ptrRetProg (.returned 0) [] ∧
    Observes .frameReuse none (inlineCallSite .corrected ptrRetProg 0 0) (.returned 0) [] :=
-- ToyTailCall/Counterexamples.lean:322-325
theorem correctedTailSiteSplice_overflows_mutualRec3 :
    Observes .frameReuse (some 3) (mutualRec 3) (.returned 0) [] ∧
      Observes .frameReuse (some 3) (inlineTailSite .corrected (mutualRec 3) 1 1) .stackOverflow [] ∧
      ¬ Observes .frameReuse (some 3) (inlineTailSite .corrected (mutualRec 3) 1 1) (.returned 0) [] := by
-- ToyTailCall/Counterexamples.lean:332-335
theorem correctedTailSiteSplice_mutualRec3 :
    RunsTo .frameReuse none (mutualRec 3) ⟨.returned 0, [], 2, 6⟩ ∧
      RunsTo .frameReuse none (inlineTailSite .corrected (mutualRec 3) 1 1)
        ⟨.returned 0, [], 5, 0⟩ :=
-- ToyTailCall/Counterexamples.lean:340-342
theorem naiveTailSiteSplice_within_bound_mutualRec3 :
    RunsTo .frameReuse (some 3) (inlineTailSite .naive (mutualRec 3) 1 1)
      ⟨.returned 0, [], 2, 3⟩ := ⟨60, by decide⟩
-- ToyTailCall/Counterexamples.lean:348-351
theorem dropList_clears_pending_nonvacuous :
    let fn : Fn := ⟨0, [.quiet, .quiet, .quiet], []⟩
    let fr : Frame := ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩
    pendingDrops fn fr = [2, 1, 0] ∧ (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort := by
-- ToyTailCall/Counterexamples.lean:356-360
theorem dropList_abort_leaves_pending :
    let fn : Fn := ⟨0, [.quiet, .panics, .panics], []⟩
    let fr : Frame := ⟨1, 1, 3, [.int 1, .int 2, .int 3], [true, true, true], .thenReturn, none⟩
    (dropList fn fr (pendingDrops fn fr) false).2.2 = .abort ∧
      pendingDrops fn (dropList fn fr (pendingDrops fn fr) false).1 = [0] := by decide
-- ToyTailCall/Counterexamples.lean:400-405
theorem finalizes_then_push_nonvacuous :
    AtTailCall (panicFin .quiet .quiet .quiet) panicFinState (panicFinT .quiet .quiet .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame = [] ∧
      finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame =
        [.drop 3, .drop 2, .drop 1] :=
-- ToyTailCall/Counterexamples.lean:410-419
theorem finalizes_then_push_fails_with_panic :
    AtTailCall (panicFin .quiet .panics .quiet) panicFinState (panicFinT .quiet .panics .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame ≠ [] ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) panicFinState ≠
        bumpTail (push none (panicFin .quiet .panics .quiet)
          { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame }
          panicFinRest 2 []) :=
-- ToyTailCall/Counterexamples.lean:425-438
theorem finalizes_then_push_fails_when_unwinding :
    let st : State := { panicFinState with unwinding := true }
    st.stack = panicFinFrame :: panicFinRest ∧ st.unwinding = true ∧
      panicFinFrame.pendingRet = none ∧
      (panicFin .quiet .quiet .quiet).fns[panicFinFrame.fn]? = some (panicFinT .quiet .quiet .quiet) ∧
      (panicFinT .quiet .quiet .quiet).code[panicFinFrame.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame = [] ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) st ≠
        bumpTail (push none (panicFin .quiet .quiet .quiet)
          { st with
              events := st.events ++
                finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame }
          panicFinRest 2 []) := by
-- ToyTailCall/Counterexamples.lean:447-460
theorem finalizes_then_push_fails_with_pendingRet :
    let st : State := ⟨panicFinFrameRet :: panicFinRest, 2, [], 2, 0, false⟩
    st.stack = panicFinFrameRet :: panicFinRest ∧ st.unwinding = false ∧
      panicFinFrameRet.pendingRet ≠ none ∧
      (panicFin .quiet .quiet .quiet).fns[panicFinFrameRet.fn]? = some (panicFinT .quiet .quiet .quiet) ∧
      (panicFinT .quiet .quiet .quiet).code[panicFinFrameRet.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrameRet [] = some ([], panicFinFrameRet) ∧
      panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrameRet = [] ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) st ≠
        bumpTail (push none (panicFin .quiet .quiet .quiet)
          { st with
              events := st.events ++
                finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrameRet }
          panicFinRest 2 []) := by
-- ToyTailCall/Counterexamples.lean:465-467
def badArgTailProg (d : DtorKind) : Prog :=
  ⟨[ ⟨0, [d], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩,
     ⟨1, [.none], [.ret (.copy 0)]⟩ ]⟩
-- ToyTailCall/Counterexamples.lean:479-491
theorem finalizes_then_push_fails_when_args_ub :
    let fn : Fn := ⟨0, [.quiet], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩
    badArgTailState.stack = badArgTailFrame :: [] ∧ badArgTailState.unwinding = false ∧
      badArgTailFrame.pendingRet = none ∧
      (badArgTailProg .quiet).fns[badArgTailFrame.fn]? = some fn ∧
      fn.code[badArgTailFrame.pc]? = some (.tailCall 1 [.deref 0]) ∧
      evalOps [] badArgTailFrame [.deref 0] = none ∧
      panickingPending fn badArgTailFrame = [] ∧
      step .frameReuse none (badArgTailProg .quiet) badArgTailState = .halted ⟨.ub, [], 1, 0⟩ ∧
      step .frameReuse none (badArgTailProg .quiet) badArgTailState ≠
        bumpTail (push none (badArgTailProg .quiet)
          { badArgTailState with
            events := badArgTailState.events ++ finalizationEvents fn badArgTailFrame } [] 1 []) := by
-- ToyTailCall/Counterexamples.lean:509-524
theorem finalization_fails_at_other_instr :
    panicFinState.stack = panicFinFrame :: panicFinRest ∧ panicFinState.unwinding = false ∧
      panicFinFrame.pendingRet = none ∧
      panicFinNoTail.fns[panicFinFrame.fn]? = some panicFinTNoTail ∧
      panicFinTNoTail.code[panicFinFrame.pc]? ≠ some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      panickingPending panicFinTNoTail panicFinFrame = [] ∧
      step .frameReuse none panicFinNoTail panicFinState ≠
        bumpTail (push none panicFinNoTail
          { panicFinState with
              events := panicFinState.events ++
                finalizationEvents panicFinTNoTail panicFinFrame } panicFinRest 2 []) ∧
      step .frameReuse none panicFinNoTail panicFinState ≠
        unwindBelow { panicFinState with
              events := panicFinState.events ++
                finalizationEvents panicFinTNoTail panicFinFrame } panicFinRest := by
-- ToyTailCall/Counterexamples.lean:528-533
theorem panic_drops_rest_nonvacuous :
    AtTailCall (panicFin .quiet .panics .quiet) panicFinState (panicFinT .quiet .panics .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame).length = 1 ∧
      finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame =
        [.drop 3, .drop 2, .drop 1] :=
-- ToyTailCall/Counterexamples.lean:538-548
theorem panic_drops_rest_fails_with_two_panics :
    AtTailCall (panicFin .quiet .panics .panics) panicFinState (panicFinT .quiet .panics .panics)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .panics .panics) panicFinFrame).length = 2 ∧
      step .frameReuse none (panicFin .quiet .panics .panics) panicFinState =
        .halted ⟨.aborted, [.drop 3, .drop 2], 2, 0⟩ ∧
      step .frameReuse none (panicFin .quiet .panics .panics) panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .panics .panics) panicFinFrame }
          panicFinRest :=
-- ToyTailCall/Counterexamples.lean:553-561
theorem panic_drops_rest_fails_with_zero_panics :
    AtTailCall (panicFin .quiet .quiet .quiet) panicFinState (panicFinT .quiet .quiet .quiet)
        panicFinFrame panicFinRest 2 [] [] panicFinFrame ∧
      (panickingPending (panicFinT .quiet .quiet .quiet) panicFinFrame).length = 0 ∧
      step .frameReuse none (panicFin .quiet .quiet .quiet) panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents (panicFinT .quiet .quiet .quiet) panicFinFrame }
          panicFinRest :=
-- ToyTailCall/Counterexamples.lean:567-580
theorem panic_drops_rest_fails_when_unwinding :
    let st : State := { panicFinState with unwinding := true }
    st.stack = panicFinFrame :: panicFinRest ∧ st.unwinding = true ∧
      panicFinFrame.pendingRet = none ∧
      (panicFin .quiet .panics .quiet).fns[panicFinFrame.fn]? = some (panicFinT .quiet .panics .quiet) ∧
      (panicFinT .quiet .panics .quiet).code[panicFinFrame.pc]? = some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      (panickingPending (panicFinT .quiet .panics .quiet) panicFinFrame).length = 1 ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) st =
        .halted ⟨.aborted, [.drop 3, .drop 2], 2, 0⟩ ∧
      step .frameReuse none (panicFin .quiet .panics .quiet) st ≠
        unwindBelow { st with
            events := st.events ++
              finalizationEvents (panicFinT .quiet .panics .quiet) panicFinFrame } panicFinRest := by
-- ToyTailCall/Counterexamples.lean:599-611
theorem panic_drops_rest_fails_with_pendingRet :
    let st : State := ⟨panicFinFrameRet :: panicFinRest, 2, [], 2, 0, false⟩
    st.stack = panicFinFrameRet :: panicFinRest ∧ st.unwinding = false ∧
      panicFinFrameRet.pendingRet ≠ none ∧
      panicMoveProg.fns[panicFinFrameRet.fn]? = some panicMoveT ∧
      panicMoveT.code[panicFinFrameRet.pc]? = some (.tailCall 2 [.move 0]) ∧
      evalOps panicFinRest panicFinFrameRet [.move 0] =
        some ([.int 1], panicFinFrameRet.kill 0) ∧
      (panickingPending panicMoveT (panicFinFrameRet.kill 0)).length = 1 ∧
      step .frameReuse none panicMoveProg st ≠
        unwindBelow { st with
            events := st.events ++ finalizationEvents panicMoveT (panicFinFrameRet.kill 0) }
          panicFinRest := by
-- ToyTailCall/Counterexamples.lean:617-628
theorem panic_drops_rest_fails_when_args_ub :
    let fn : Fn := ⟨0, [.panics], [.assign 0 (.const 7) 1, .tailCall 1 [.deref 0]]⟩
    badArgTailState.stack = badArgTailFrame :: [] ∧ badArgTailState.unwinding = false ∧
      badArgTailFrame.pendingRet = none ∧
      (badArgTailProg .panics).fns[badArgTailFrame.fn]? = some fn ∧
      fn.code[badArgTailFrame.pc]? = some (.tailCall 1 [.deref 0]) ∧
      evalOps [] badArgTailFrame [.deref 0] = none ∧
      (panickingPending fn badArgTailFrame).length = 1 ∧
      step .frameReuse none (badArgTailProg .panics) badArgTailState = .halted ⟨.ub, [], 1, 0⟩ ∧
      step .frameReuse none (badArgTailProg .panics) badArgTailState ≠
        unwindBelow { badArgTailState with
            events := badArgTailState.events ++ finalizationEvents fn badArgTailFrame } [] := by
-- ToyTailCall/Counterexamples.lean:633-635
def panicFinTOnePanicNoTail : Fn :=
  ⟨0, [.quiet, .panics, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .panic]⟩
-- ToyTailCall/Counterexamples.lean:638-641
def panicFinOnePanicNoTail : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicFinTOnePanicNoTail,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Counterexamples.lean:647-657
theorem panic_drops_rest_fails_at_other_instr :
    panicFinState.stack = panicFinFrame :: panicFinRest ∧ panicFinState.unwinding = false ∧
      panicFinFrame.pendingRet = none ∧
      panicFinOnePanicNoTail.fns[panicFinFrame.fn]? = some panicFinTOnePanicNoTail ∧
      panicFinTOnePanicNoTail.code[panicFinFrame.pc]? ≠ some (.tailCall 2 []) ∧
      evalOps panicFinRest panicFinFrame [] = some ([], panicFinFrame) ∧
      (panickingPending panicFinTOnePanicNoTail panicFinFrame).length = 1 ∧
      step .frameReuse none panicFinOnePanicNoTail panicFinState ≠
        unwindBelow { panicFinState with
            events := panicFinState.events ++
              finalizationEvents panicFinTOnePanicNoTail panicFinFrame } panicFinRest := by
-- ToyTailCall/Counterexamples.lean:680-682
theorem popFirst_agrees_without_pending_drops_chain3 :
    RunsTo .popFirst none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ ∧
      RunsTo .frameReuse none chain3 ⟨.returned 0, [.out 1], 1, 2⟩ :=
-- ToyTailCall/Counterexamples.lean:713
theorem sigCheckFull_nonvacuous : sigCheckFull ⟨[1, 2], true⟩ ⟨[1, 2], true⟩ = true := by decide
-- ToyTailCall/Counterexamples.lean:723-726
theorem reuseSound_calleePops_without_sigCheck :
    sigCheckFull ⟨[2], false⟩ ⟨[1], true⟩ = false ∧
      sigCheckExplicit ⟨[2], false⟩ ⟨[1], true⟩ = false ∧
      ReuseSound .calleePops (Sig.areaSize ⟨[2], false⟩) (Sig.areaSize ⟨[1], true⟩) :=
-- ToyTailCall/Counterexamples.lean:732-733
theorem reuseSoundAt_calleePops_nonvacuous :
    ¬ ReuseSound .calleePops 1 2 ∧ ReuseSoundAt .calleePops 1 1 2 := by
-- ToyTailCall/Counterexamples.lean:744
theorem reuseSoundAt_callerPops_nonvacuous : ReuseSoundAt .callerPops 0 2 1 := by
-- ToyTailCall/Counterexamples.lean:754-755
theorem reuseSoundAt_calleePops_callerLoc_relocated :
    ReuseSoundAt .calleePops (-1) (Sig.areaSize ⟨[1], true⟩) (Sig.areaSize ⟨[1], false⟩) := by
-- ToyTailCall/Converse.lean:14-17
theorem correctedSplice_converse_fails_plainCall :
    Observes .frameReuse (some 1) (inlineCallSite .corrected plainCall 0 0) (.returned 0)
        [.out 1] ∧
      ¬ Observes .frameReuse (some 1) plainCall (.returned 0) [.out 1] := by
-- ToyTailCall/Converse.lean:27-29
theorem correctedSplice_converse_fails_borrowProg :
    Observes .frameReuse none (inlineCallSite .corrected borrowProg 0 0) (.returned 5) [] ∧
      ¬ Observes .frameReuse none borrowProg (.returned 5) [] := by
-- ToyTailCall/Converse.lean:36-40
theorem correctedCallSiteSplice_converse_false :
    ¬ ∀ (p : Prog) (ci k : Nat) (D : Option Nat) (o : Outcome) (es : List Event),
        o ≠ .ub → o ≠ .stackOverflow →
        Observes .frameReuse D (inlineCallSite .corrected p ci k) o es →
          Observes .frameReuse D p o es := by
```

Helper definitions that occur in the R17 and R18 counterexample statements above, quoted so that those statements read in place (they are also part of those statements' definition closures, which the recorded hashes cover):

```lean
-- ToyTailCall/Counterexamples.lean:442
def panicFinFrameRet : Frame := { panicFinFrame with pendingRet := some (.int 99) }
-- ToyTailCall/Counterexamples.lean:470
def badArgTailFrame : Frame := ⟨0, 0, 1, [.int 7], [true], .thenReturn, none⟩
-- ToyTailCall/Counterexamples.lean:473
def badArgTailState : State := ⟨[badArgTailFrame], 1, [], 1, 0, false⟩
-- ToyTailCall/Counterexamples.lean:495-497
def panicFinTNoTail : Fn :=
  ⟨0, [.quiet, .quiet, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .panic]⟩
-- ToyTailCall/Counterexamples.lean:500-503
def panicFinNoTail : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicFinTNoTail,
     ⟨0, [], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
-- ToyTailCall/Counterexamples.lean:585-587
def panicMoveT : Fn :=
  ⟨0, [.quiet, .panics, .quiet], [.assign 0 (.const 1) 1, .assign 1 (.const 2) 2,
    .assign 2 (.const 3) 3, .tailCall 2 [.move 0]]⟩
-- ToyTailCall/Counterexamples.lean:590-593
def panicMoveProg : Prog :=
  ⟨[ ⟨0, [.quiet, .none], [.assign 0 (.const 50) 1, .call 1 [] 1 2, .ret (.move 1)]⟩,
     panicMoveT,
     ⟨1, [.none], [.emit 1 1, .ret (.const 0)]⟩ ]⟩
```

## Boundaries

### Non-claims, by result

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R1. `frameReuse_observes_iff_preJump_of_noStackBorrow`

* Compares halted runs (outcome and finite trace). Infinite traces of non-halting runs are not compared, beyond the consequence of the equivalence that one run halts exactly when the other does.
* Unbounded stack (`D = none`). Under a bound the two semantics differ (`frameReuse_of_preJump_fails_for_overflow_countUp3`); the bounded transfer is card R3.
* Does not relate `frameReuse` to `callReturn`: they differ even under the hypothesis (card R2).
* `NoStackBorrow` is sufficient, not necessary: in `ignorePtrProg` a pointer into the current frame is passed but never loaded through, so `NoStackBorrow` fails, yet the two semantics have the same outcomes and traces (`noStackBorrow_not_necessary_ignorePtrProg`).
* `NoStackBorrow` is a dynamic property of the unbounded `preJump` run; it is not a static check. A sound static check is card R8.
* `preJump` keeps finalized frames on the stack, and the machine does not flag a load from a dropped slot (`Frame.kill` clears the drop flag and keeps the value); it imposes no arity or signature relation between a function and the callee of its tail call (a mismatch is `ub` at `push`).
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* The toy has no heap, no stores through pointers, no borrow checker and no catching of panics.
* Frame identities are unobservable by construction: `Val.obs` maps pointers and `undef` to `0`, and events and final results record `Val.obs` values and no frame identities.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R2. `frameReuse_ne_callReturn_dtorProg`

* One concrete program; it shows that the equivalence of card R1 cannot be stated against `callReturn`.
* On programs whose frames own no value with a destructor at their tail calls, `frameReuse` and `callReturn` may agree on traces; that is not proved here.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R3. `frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow`

* One direction: `frameReuse` may halt normally where `preJump` overflows. With bound `some 4`, `countUp 3` overflows under `preJump` while `frameReuse` does not halt with that overflow (`frameReuse_of_preJump_fails_for_overflow_countUp3`); `frameReuse` returns 0 there (`countUp3_bound4_frameReuse`). The converse transfer is not claimed.
* `NoStackBorrow` is evaluated on the unbounded `preJump` run, not on the bounded one.
* Degenerate bound: with `D = some 0`, for a program satisfying `EntryOk p` (whose entry function exists and takes no parameters) the initial push overflows under every semantics (`runsTo_bound0_of_entryOk`; instance `countUp3_bound0_overflows`), so for such a program the statement has no premise with an outcome other than `stackOverflow`. For a program violating `EntryOk` it can have one: `paramEntryProg` (entry function with exactly 1 parameter) halts with `ub` under both semantics at `D = some 0`, because `push` checks the arity before the bound (`paramEntryProg_bound0_ub`).
* Compares halted runs; bounded runs that do not halt are not compared.
* Depth is counted in frames, not bytes; frame sizes are not modelled in this machine.
* The non-claims of card R1 apply here too. In particular, `NoStackBorrow` is sufficient, not necessary: in `ignorePtrProg` a pointer into the current frame is passed but never loaded through, so `NoStackBorrow` fails, yet the unbounded runs of both semantics have the same outcome and trace (`noStackBorrow_not_necessary_ignorePtrProg`; shown for `D = none`, other bounds are not examined). `preJump` keeps finalized frames on the stack and the machine does not flag a load from a dropped slot; the machine imposes no arity or signature relation between a function and the callee of its tail call (a mismatch is `ub` at `push`).
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* The toy has no heap, no stores through pointers, no borrow checker and no catching of panics.
* Frame identities are unobservable by construction: `Val.obs` maps pointers and `undef` to `0`, and events and final results record `Val.obs` values and no frame identities.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R4. `countUp_frameReuse_runsTo` (+2)

* One specific program family; "ascending" and "descending" refer to the labels `n`, which increase with recursion depth (the outermost frame owns `drop 0`). With labels decreasing in depth the words swap.
* Depth counts frames (the entry frame included); the value 2 includes the entry frame that called `rec`.
* The `popFirst` variant is not covered (it is `ub` on this family whenever `N > 0`, by the mechanism of card R19; not proved here).
* General tail-call chains are card R5; programs with both calls and tail calls are not covered beyond this family.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R5. `callFree_frameReuse_maxDepth_of_entryOk` (+1)

* A "jump" is a tail call whose callee frame was pushed (`bumpTail`); tail calls interrupted by a destructor panic, an overflow or `ub` are not counted.
* Unbounded runs (`D = none`) that halt; non-halting chains are not covered.
* `CallFree` is syntactic over all functions, so a program with an unreachable `call` is excluded although its runs may be chains of tail calls.
* Programs mixing `call` and `tailCall` are not bounded by this result (`countUp 3` reaches depth 2 under `frameReuse`).
* `r.tailCalls` is not claimed equal across `frameReuse` and `preJump` runs of the same program.
* Depth in frames, not bytes.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R6. `mem_pendingDrops_iff` (+1)

* In the machine, parameters occupy the lowest slots and `move` clears a slot's drop flag (`evalOp`), so in a run the list puts locals before parameters and omits moved-from slots (instance: `orderDemo_frameReuse`); these operational facts are not part of this result.
* Characterizes the toy's finalization order; it does not state the parameter drop order of any real language.
* Drop flags are set by `assign` and `call` results and cleared by `move`, drops and `reset`; partial moves and nested places are not modelled.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R7. `frameReuse_iff_preJump_fails_borrowProg`

* The local has no destructor, so the difference is the frame's removal alone; with a destructor the `preJump` run would also load a dropped slot, which the toy does not flag.
* Shows that the hypothesis of R1 cannot be dropped; it does not show that every pointer-passing program breaks the equivalence (card R1 non-claims: `noStackBorrow_not_necessary_ignorePtrProg`).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R8. `noStackBorrow_of_escapeCheckAccepts`

* Not complete: card R9.
* The check is intra-procedural: a `call` taints its destination slot and no other slot. Its soundness relies on the toy having no stores through pointers (so no out-parameters), no heap or global state and no compound values; it is not offered as an analysis for a language that has them.
* `taint` runs `nSlots + 1` rounds of an inflationary step; the proof shows that the result is a fixpoint of `taintStep` (in the proof-support module `EscapeProof.lean`, not cited as a result); that it is the least fixpoint is not proved, and the result is about `taint` as defined.
* Not a model of Rust's borrow checker; the toy has no lifetimes or references, just frame-identified pointers.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R9. `escapeCheck_incomplete_deadEscape`

* Says nothing about how often such rejections occur, or about flow-sensitive checks.
* Other sources of incompleteness exist (for instance a borrowing tail call in unreachable code, or `succ`, which taints its result although it never yields a pointer); they are not proved here.
* Whether `NoStackBorrow` is decidable is not addressed here.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R10. `Layout.reuseSound_callerPops_iff` (+1)

* The fixed boundary is a modelling choice. Callee-cleanup conventions that relocate the return address and adjust the stack pointer before the jump escape the `inH = inG` condition: with the boundary moved by `inH - inG` cells, frame reuse is sound under callee cleanup for all sizes, including `inH > inG` (card R20, `reuseSoundAt_calleePops_iff`).
* The second condition of `ReuseSound` holds for all sizes (`readArgs_reuseWrite`): the arguments are already-evaluated numbers, so copying arguments in place out of the current function's own incoming area, where an overlapping write can clobber an argument not yet read, is not modelled.
* The third condition is fixed by `spAfterReturn`, which stipulates each convention's stack pointer after the return; under callee cleanup the `→` direction follows from it alone.
* A separate layout model; no relation to the frame-stack machine is proved.
* Addresses are integers (no wrap-around, no truncated subtraction); area sizes 0 are allowed and covered.
* Register-passed arguments, per-argument types and alignment, the return-address slot itself and variadic functions are not modelled.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R11. `Layout.reuseSound_of_sigCheckFull`

* A shallow corollary of card R10 (equal signatures have equal areas).
* `sigCheckFull` is sufficient, not necessary, under either convention: under caller cleanup a smaller callee area is enough (`sigCheckExplicit_callerLoc_depends_on_cleanup`), and under callee cleanup equal areas are enough even when explicit parameters differ (`reuseSound_calleePops_without_sigCheck`: `⟨[2], false⟩` and `⟨[1], true⟩`).
* The toy check accepts a caller and a callee that both take the hidden parameter; rustc rejects every `become` from a `#[track_caller]` function, including that case (Findings, modeling bridge B4). The toy check is not a model of rustc's check.
* A hidden parameter is modelled as one trailing stack cell; a hidden parameter passed in a register, or one that shifts the positions of explicit parameters, is not modelled.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R12. `Layout.sigCheckExplicit_insufficient_calleeLoc`

* An instance of card R10 at a fixed boundary; under callee cleanup with return-address relocation the same areas are compatible (card R20).
* A hidden parameter is modelled as one trailing stack cell; a hidden parameter passed in a register, or one that shifts the positions of explicit parameters, is not modelled.
* rustc rejects `become` from a `#[track_caller]` function and does not check the callee's `track_caller`-ness; its source comment gives as one reason that the shim generated for coercing the function to an `fn()` pointer can always be tail-called (Findings, modeling bridge B4). This card says nothing about rustc's handling of such callees.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R13. `Layout.sigCheckExplicit_callerLoc_depends_on_cleanup`

* The toy says nothing about which convention rustc uses; rustc rejects this case regardless (a `#[track_caller]` caller cannot perform a tail call; Findings, modeling bridge B4).
* A hidden parameter is modelled as one trailing stack cell; a hidden parameter passed in a register, or one that shifts the positions of explicit parameters, is not modelled.
* The fixed boundary is a modelling choice: under callee cleanup with the return address relocated by `δ = -1` cells, the same pair of areas (exactly 2 cells for `g`, exactly 1 for `h`) is compatible (`reuseSoundAt_calleePops_callerLoc_relocated`; card R20, `reuseSoundAt_calleePops_iff`).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R14. `naiveSplice_changes_events_inlEx`

* About a `call` site. At a tail site keeping the tail call is the appropriate splice (CompCert keeps `Itailcall` when `ctx.(retinfo)` is `None`); in the toy one instance is kernel-checked (`naiveTailSiteSplice_within_bound_mutualRec3`, card R16).
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R15. `correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow`

* One direction: the converse is false (`correctedCallSiteSplice_converse_false`). Unbounded, the corrected splice of `borrowProg` returns 5 with an empty trace while `borrowProg` does not (`correctedSplice_converse_fails_borrowProg`; it halts with `ub`, `correctedSplice_masks_borrow_ub_borrowProg`); with bound `some 1`, the corrected splice of `plainCall` returns 0 with trace `[out 1]` while `plainCall` does not (`correctedSplice_converse_fails_plainCall`; it overflows, `correctedSplice_overflow_not_preserved_plainCall`). The tightness counterexamples `correctedSplice_ub_not_preserved_danglingRet` and `correctedSplice_overflow_not_preserved_plainCall` show that the statement fails without `hub` or without `hso`; their statements do not expose the outcome of the spliced program, so they do not by themselves refute the converse.
* `o ≠ ub` excludes more than dangling returns: a callee whose own tail call passes a pointer into the callee's frame (`ub` under `frameReuse`) returns normally after the splice (`correctedSplice_masks_borrow_ub_borrowProg`).
* Comparisons go through `Val.obs`, which maps pointers to `0`: raw values can differ after inlining (`correctedSplice_raw_values_differ_ptrRetProg`: `ptr 1 0` before, `ptr 0 1` after) while `Observes` agrees. No version of the statement that compares raw values instead of `Val.obs` values is formalized; such a version is expected to fail because frame numbering changes (not proved here).
* A self-call (`g = ci`) or a site that is not a well-formed `call` leaves the program unchanged (`inlineCallSite_self_unchanged`, `inlineCallSite_nonCall_unchanged`); for those the statement is trivial.
* Tail-call counters are not preserved: the unbounded run of `inlEx2` executes exactly 1 tail-call jump and that of its corrected splice none, with the same outcome, trace and maximum depth (`correctedSplice_tailCalls_differ_inlEx2`); `Observes` ignores the counter.
* Stated for `frameReuse`; `callReturn` and `preJump` are not covered.
* Depth is counted in frames: the spliced function has more slots, so on a machine with a fixed byte budget per stack the splice could overflow where the original does not; frame sizes are not modelled.
* Tail sites are card R16.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R16. `correctedTailSiteSplice_mutualRec_runsTo` (+1)

* About the corrected (call-site) splice applied at a tail site. It does not show that tail-site inlining is impossible: a splice that keeps `g`'s tail call stays within bound `some 3` on `mutualRec 3` (`naiveTailSiteSplice_within_bound_mutualRec3`, one instance; no general theorem about a tail-preserving splice is stated). CompCert and LLVM keep the tail call at tail sites (Findings, modeling bridge B5).
* One program family, without destructors: the interaction of tail-site inlining with finalization or unwinding is not tested.
* Depth in frames, not bytes.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R17. `dropList_clears_pending_of_ne_abort` (+1)

* A one-step statement; whole-run exactly-once destruction is not stated.
* Whether the push succeeds (callee exists, arity, bound) is left to `push`; the theorem fixes the step's result, not its success.
* A definitional unfolding of `step`, `doTailCall` and `dropList`, kept as a reference point for the design question.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R18. `frameReuse_finalization_unique_panic_drops_rest_then_unwinds`

* "Each slot once" is about this step; the frame is removed, so no later step can drop its slots, but a whole-run statement is not given.
* Argument values already evaluated when the destructor panics are discarded without a drop event (a leak in the toy); real behaviour for such values is not examined.
* The abort-on-second-panic rule is a modelling choice.
* A definitional unfolding of `step`, `doTailCall` and `dropList`, kept as a reference point for the design question.
* Destructors are atomic events (`DtorKind`): running one pushes no frame, executes no instruction and reads or writes no slot, so destructors that call functions (raising the peak depth during finalization) or that access their own slot through `&mut self` are not modelled (the `popFirst` variant of card R19 models that access and nothing else).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R19. `popFirst_ub_with_pending_drop_dtorProg`

* `popFirst` is a constructed incorrect variant; this is not a claim about any implementation.
* Under `popFirst` the one destructor effect modelled is the access to its own slot; elsewhere destructors are atomic events (`DtorKind`) that read no slot.
* When no destructor is pending at a tail call, `popFirst` and `frameReuse` coincide (positive control `popFirst_agrees_without_pending_drops_chain3`, one instance).
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

#### R20. `Layout.reuseSoundAt_zero_iff` (+2)

* Writing the relocated return address, and the cost of the extra moves, are not modelled.
* The second condition holds for all sizes and relocations (`readArgs_reuseWriteAt`); overlapping in-place argument copies are not modelled.
* Says nothing about which convention rustc or LLVM uses for a given ABI; the LLVM and rustc texts of the modeling bridge (Findings) are quoted as documentation and source text (including test files), not as execution evidence establishing which calling convention either compiler lowers a given ABI to.
* Register-passed arguments, per-argument types and alignment are not modelled.
* The third condition is fixed by `spAfterReturnAt`, which stipulates each convention's stack pointer after the return; under callee cleanup the `→` direction of `reuseSoundAt_calleePops_iff` follows from it alone, and under caller cleanup so does `δ = 0`.
* A separate layout model; no relation to the frame-stack machine is proved.
* Addresses and `δ` are integers (no wrap-around, no truncated subtraction); area sizes 0 are allowed and covered.
* Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or any other compiler.

### Escape hatches

For the results that show a failure, the nearby settings in which the failure goes away, as far as they are proved here:

* R7 (without `NoStackBorrow` the equivalence of R1 fails on `borrowProg`): adding the hypothesis `NoStackBorrow` restores the equivalence (R1, kernel-checked); the hypothesis is sufficient and not necessary: there is a program that violates it and on which the two unbounded semantics have the same outcomes and traces (`noStackBorrow_not_necessary_ignorePtrProg`).
* R12 and R13 (frame reuse unsound at a fixed frame boundary for the given signature pairs): under callee cleanup, moving the boundary by `δ = inH - inG` cells makes frame reuse sound for all area sizes (R20, `Layout.reuseSoundAt_calleePops_iff`); for the pair of R13 with `δ = -1` this is `reuseSoundAt_calleePops_callerLoc_relocated`. Under caller cleanup relocation does not help (R20, `Layout.reuseSoundAt_callerPops_iff`).
* R14 and R16 (the naive splice changes behaviour at a `call` site of `inlEx`; at the tail site of `mutualRec`, the corrected splice loses every additive stack bound): at a tail site, a splice that keeps `g`'s tail call stays within bound `some 3` on `mutualRec 3` (positive control `naiveTailSiteSplice_within_bound_mutualRec3`, one instance; no general theorem about tail-site splicing is proved).
* R19 (`popFirst` makes pending destructors `ub` on `dtorProg`): when no destructor is pending at a tail call, `popFirst` and `frameReuse` coincide on the instance `popFirst_agrees_without_pending_drops_chain3` (positive control, one instance; not proved in general).
* R2 and R9: no escape hatch is proved. For R2, agreement of `frameReuse` and `callReturn` on programs whose frames own no value with a destructor at their tail calls is not proved here; for R9, no flow-sensitive check is defined or proved complete.

### Hypotheses with unknown tightness

None: every hypothesis of every result is `tight`, and its ledger names a kernel-checked counterexample in which all other hypotheses hold and the conclusion fails.

### Disproved or dropped statements

None: every result listed in the Summary is kernel-checked with the statement quoted in its card.

### Not examined

* Destructors that call functions, read or write slots (beyond the single slot access of `popFirst`), or catch panics; heap memory and stores through pointers; types and borrow checking; any real calling convention or frame size in bytes.
* The `callReturn` and `preJump` semantics for the inlining results (R14–R16 are stated for `frameReuse`).
* Any execution or measurement of rustc, CompCert or LLVM.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4` `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean without Mathlib. Basis of every theorem below: execution (Lean kernel check), observed on 2026-11-21. The table lists every declaration that a card names (results, witnesses, counterexamples, positive controls and the auxiliary lemmas and definitions cited by name), with the axioms it depends on (`#print axioms`, computed with Lean's `collectAxioms`), the SHA-256 of its statement (the Lean `repr` of its type) and the SHA-256 of its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded). The same data are in `audit/axioms.json` and `audit/statements.json`.

| declaration | axioms | statement SHA-256 | definition-closure SHA-256 (size) |
| --- | --- | --- | --- |
| `Toy.TailCall.AtTailCall` | `propext` | `279faf142ecb0adbe8b21abeac2b7fe9e97a1badfb8c5a611073c0fee53ce2f0` | `0fd74b0e580f707c0966cb1b27b495fc1f5b89c45d3a0bb02d034ec4b43eb0c5` (42) |
| `Toy.TailCall.CallFree` | `propext` | `3b1db981b3afb614717927d66572954e15c6c049e80767f98059dbf61b63c75a` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.Conf` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Cont` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.DropEnd` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.DtorKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.EntryOk` | `propext` | `f162703c13d5764ab052fccaac9330dd66ef50d12651b862dc031288f82e973c` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.EscapeCheckAccepts` | `propext` | `3b1db981b3afb614717927d66572954e15c6c049e80767f98059dbf61b63c75a` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.EscapeCheckFn` | `propext` | `8ae6a5832c6b61b3b955b9ca262d5ea7d46fcba727ff712e1a023678776ed7d3` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.Event` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Fn` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Fn.dtor` | `propext` | `46c89a2987c286adeaf195bada483e24a2f0821047938e8bdaff7a2d8543e44c` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.Fn.nSlots` | none | `b447054a5eebdb89a4ff045fd2f6f698c6676feb271da304d41e63da10ec9748` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.FnId` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Frame` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Frame.clear` | none | `38508e73e4f14409234bb16280a4ea1c4656cd612acac433a94c633320957241` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.Frame.get` | `propext` | `5244eed2fc890bfdd5c859fdb0bb25e21ff47046871444f3fba61730ec31c9be` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.Frame.isLive` | `propext` | `be34e0ff32b8b721075b9ca841df4d4c2fd8e907ccd1ccd1add109922b69e360` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.Frame.kill` | none | `38508e73e4f14409234bb16280a4ea1c4656cd612acac433a94c633320957241` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.Frame.write` | none | `b32d172b4ece8ad23cc892b628cefb3d95cabff50f313af69fe587fc64d76584` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.Instr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Layout.Cleanup` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Layout.Mem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Layout.ReuseSound` | none | `4ec7a1cb14fc8a18a59987f6971269eec9f786c9307e5d7cb6b1aa053c0be331` | `e871bfa199ed8a3e8e279bba1c6cc59d81407ad982040babe88d2942fcf1684b` (3) |
| `Toy.TailCall.Layout.ReuseSoundAt` | none | `f694078afc4335bc5acfea0e1ebf91c1e7584daa24676d492a194fe64f9c477f` | `e871bfa199ed8a3e8e279bba1c6cc59d81407ad982040babe88d2942fcf1684b` (3) |
| `Toy.TailCall.Layout.Sig` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Layout.Sig.areaSize` | none | `767ebad43284a26d7b8dec38691d4712ae5abfa97e5e285af63f20f291dd5d43` | `333b58a3511e46f34e06e5f110ebf611d4d499acb19f8bd3f3ceb13121b9b1b0` (2) |
| `Toy.TailCall.Layout.areaSize_examples` | none | `fe159a69721022ce1fb21fbbea8c8303b8f4f14b7a00a5be4b625be04f10db0b` | `34d529b45c9b102f3a1f30d9181e1268ce74b3de23e7464d2898e04a047f4b0a` (5) |
| `Toy.TailCall.Layout.not_reuseSound_calleePops_2_1` | `propext` | `86e08592e3d01442dea8d96410c71e4eafd21037323fcdbb58feaa7a9cce1324` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.not_reuseSound_callerPops_1_2` | `propext` | `a8154e29da1fe4f5d0b024ce8e26c79a22e2f20cc74573c7ed0ceb1b05dff3bd` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.readArgs` | none | `326b502596548be82fd444584a592521fde40fc08db67cf60a0c6acd1c0e826e` | `7a41df43349146623e3143d5d8ac8d5232c1750f45f1ece49400a269c9600791` (1) |
| `Toy.TailCall.Layout.readArgs_reuseWrite` | `Quot.sound`, `propext` | `1f4c2cce5ca3e6c8375bbe8f6e91c204254e2cb34fc94e5dfa337d35e04a390d` | `6d7ae4dc93a932ceee7efcf9b2603086f818e19b45683a8888c9e69b1b26b300` (8) |
| `Toy.TailCall.Layout.readArgs_reuseWriteAt` | `Quot.sound`, `propext` | `7434846a6716ad2e6730c8fc414ca33d4ed12d59e3457e927df0923fd9ee81a4` | `d66c08ecbc78b0df35911bf7617b11f33c16f39b3ef398f660b230b0bfd3ebc2` (8) |
| `Toy.TailCall.Layout.readArgs_writeArgs` | `Quot.sound`, `propext` | `036f0b3577301cb479ebcd93fd6de072f3d31dc377f1afcc5baf21fc99dcd45b` | `c7db58ce1fdde7409219b2c0b4ba4d2065d1d6026065539ba430a606b7cfefa3` (7) |
| `Toy.TailCall.Layout.reuseSoundAt_calleePops_callerLoc_relocated` | `Quot.sound`, `propext` | `eaafdd348fe0a25201a16cf3a731c5c3a61c9127022093e9f4860bd1944fd2a9` | `6b49933df06637275c65f1bfb1928ecf547a384f561950daf9da828370391ed7` (21) |
| `Toy.TailCall.Layout.reuseSoundAt_calleePops_iff` | `Quot.sound`, `propext` | `2b3f61e489d1648ccdbbdd05fe9e673e72158dc78a371176a3efc73cc5b90539` | `97848ecc4b7b4ae89c8812621ebaa8e9c86336f24d1f82bfa62f2998e7912db4` (16) |
| `Toy.TailCall.Layout.reuseSoundAt_calleePops_nonvacuous` | `Quot.sound`, `propext` | `a1012add8b18dc76dd2fc2bd2b442c3d26113f663ff2e2e6bd355ecf4f964434` | `2aad216df8ea8259f8b20a2614b31ad80169b6b737d27d8bfd6c795fc9ae7db9` (19) |
| `Toy.TailCall.Layout.reuseSoundAt_callerPops_iff` | `Quot.sound`, `propext` | `f6beba8cf4e713d8090acc7e901a98dd4254f64514413c33471f0a9cdf2a9809` | `97848ecc4b7b4ae89c8812621ebaa8e9c86336f24d1f82bfa62f2998e7912db4` (16) |
| `Toy.TailCall.Layout.reuseSoundAt_callerPops_nonvacuous` | `Quot.sound`, `propext` | `9a1d534c02840d0016a47cbcba451ca72d29581275f3f9502634180c2db15b3a` | `97848ecc4b7b4ae89c8812621ebaa8e9c86336f24d1f82bfa62f2998e7912db4` (16) |
| `Toy.TailCall.Layout.reuseSoundAt_zero_iff` | `propext` | `09b539dcdb84bd6d99d213976cf6804643cf7c4f83c41ea5a00a32ee4aa2e84f` | `2aad216df8ea8259f8b20a2614b31ad80169b6b737d27d8bfd6c795fc9ae7db9` (19) |
| `Toy.TailCall.Layout.reuseSound_calleePops_1_1` | `Quot.sound`, `propext` | `e3a97a5d91cf55576929ee491087ec953bac6d585b7b0a74cc358368b791dc18` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.reuseSound_calleePops_iff` | `Quot.sound`, `propext` | `8f40a117393328e5486e58cfccbc64b1d4d781619f2339a04558cb874c138591` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.reuseSound_calleePops_without_sigCheck` | `Quot.sound`, `propext` | `24f6f3e6ad7cd53875b64e379cd8afee5051570081d457309b00c1766acb1e61` | `fb33921ef1df3009dd8a0a0f423dac211ba883e7f48b0b84a4a620eb29d96cb3` (31) |
| `Toy.TailCall.Layout.reuseSound_callerPops_2_1` | `Quot.sound`, `propext` | `9b4089ce0eb0e6f20efb9ab080649d325fd75b6a203db7007394ea02243ab6c8` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.reuseSound_callerPops_iff` | `Quot.sound`, `propext` | `83ff5f92a109e211a46366cfed9a3aada62222d52bef90ac513fb02413a66e60` | `8c7aa7bd620a18649e1de9d8805062b0a4081b376a314db7bf7ceb3c5ce00cc5` (16) |
| `Toy.TailCall.Layout.reuseSound_of_sigCheckFull` | `Quot.sound`, `propext` | `7c25781ac274e0d40a66987a731f9c8e5bfa3748c1c0b884cbf6073c137dfe61` | `d28d2b98f3ec663619dcbc3564f5badabf4c270dcac2c111f43a0bd3d9ce0f6e` (30) |
| `Toy.TailCall.Layout.reuseWrite` | none | `f1f01b119abd87c90de0acf2efa7b9c9bde10b61175951a711113675d96ae758` | `7a41df43349146623e3143d5d8ac8d5232c1750f45f1ece49400a269c9600791` (1) |
| `Toy.TailCall.Layout.reuseWriteAt` | none | `b038a13515cc6c4c57be5e1a3df481277a53eb1d8307bff2941d6ef2efaea451` | `7a41df43349146623e3143d5d8ac8d5232c1750f45f1ece49400a269c9600791` (1) |
| `Toy.TailCall.Layout.sigCheckExplicit` | none | `9d7abe8314c97d0858f240f306ffa29a360aab11403cecc7dcab0df70884cb6e` | `333b58a3511e46f34e06e5f110ebf611d4d499acb19f8bd3f3ceb13121b9b1b0` (2) |
| `Toy.TailCall.Layout.sigCheckExplicit_callerLoc_depends_on_cleanup` | `Quot.sound`, `propext` | `114386f8c581c02dbdc4160928ae2979baaba08dc23596eda8d4e89bd9746a71` | `fb33921ef1df3009dd8a0a0f423dac211ba883e7f48b0b84a4a620eb29d96cb3` (31) |
| `Toy.TailCall.Layout.sigCheckExplicit_examples` | none | `f4fbae8c038927c74fb27f01a5afbc19c441b72a3cf9b1a8433ffed467422dae` | `9d543a8a2d3297385f5834900427fa91490fd8a78788142cee1b98003fa5526c` (4) |
| `Toy.TailCall.Layout.sigCheckExplicit_insufficient_calleeLoc` | `propext` | `484e90913fc4e44ff38685117ae5c453969295416ff91e38d89e05c9f9bc722d` | `fb33921ef1df3009dd8a0a0f423dac211ba883e7f48b0b84a4a620eb29d96cb3` (31) |
| `Toy.TailCall.Layout.sigCheckFull` | none | `9d7abe8314c97d0858f240f306ffa29a360aab11403cecc7dcab0df70884cb6e` | `333b58a3511e46f34e06e5f110ebf611d4d499acb19f8bd3f3ceb13121b9b1b0` (2) |
| `Toy.TailCall.Layout.sigCheckFull_examples` | none | `b5d7c7e116a22fd1a3483158b2233824b53c1cccb7bab6f5c8957c85096f8225` | `d4a5ad6d60fad1c16c3917dcf6b2afc0ef359ab755020efd9ac3fd531b64dd0a` (11) |
| `Toy.TailCall.Layout.sigCheckFull_nonvacuous` | none | `3da0492db754be377cbb61ceee46b214d7b3cc38753a4f3b2b3e7b1b9711347a` | `d4a5ad6d60fad1c16c3917dcf6b2afc0ef359ab755020efd9ac3fd531b64dd0a` (11) |
| `Toy.TailCall.Layout.spAfterReturn` | none | `2165b5f8c381d7c5798d2f908a4b1667cc928ed4876ec26821fa7d3c669d85d5` | `e871bfa199ed8a3e8e279bba1c6cc59d81407ad982040babe88d2942fcf1684b` (3) |
| `Toy.TailCall.Layout.spAfterReturnAt` | none | `bea837be03ca18755648353be7c2936b093d680c258a75dcec42ce408cf6010b` | `e871bfa199ed8a3e8e279bba1c6cc59d81407ad982040babe88d2942fcf1684b` (3) |
| `Toy.TailCall.Layout.writeArgs` | none | `10d873ebc6c97b6d660ce37f0c10eca88dd0c9bbaf814ea746b421046ef11c72` | `7a41df43349146623e3143d5d8ac8d5232c1750f45f1ece49400a269c9600791` (1) |
| `Toy.TailCall.Layout.writeArgs_eq_of_lt` | `Quot.sound`, `propext` | `1e4200e4c819b94a5bb4231187f1befd3678ee60b90d157153c82c235d217f53` | `5eefcca566f4e3906bebd5ade9310024bf81fb48f6dc8eb16e6a00ef93532818` (4) |
| `Toy.TailCall.NoStackBorrow` | `propext` | `f162703c13d5764ab052fccaac9330dd66ef50d12651b862dc031288f82e973c` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.Observes` | `propext` | `1db47b6e12ea58e2111aae86d15eaa9698d1b10ab31eae32b06bb5c6527d364f` | `c0970b7f556b91b8d8efd6e06f6cd1594e7b416a73d81cb8f15f8103dd7dcad7` (42) |
| `Toy.TailCall.Operand` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Outcome` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Result` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.RunsTo` | `propext` | `62d6e17d8c3963a1c575bf60aa95e3bd8902df31948a00acf74c19f0e30e3117` | `dbbdf1163743fa115fa0f47f656cc82a29a4d5cac26290e5fc99b64978d1ef2e` (44) |
| `Toy.TailCall.Sem` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Slot` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.SpliceMode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.State` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.State.empty` | none | `d99634d5dccdb51b3d6551463fb918c2251a24257be7c863ae5353d111c3c235` | `c59b3adb987a48ddaebbe376d72c0f46da53758551804714248944276d4aba20` (16) |
| `Toy.TailCall.State.halt` | none | `ba789d0305864443af82b6f4a7d21d780971e7157c24203d50132741fef963c2` | `486a38a303f255f97d0fdbe7ef74c301479f1aeed73cea8e9dc3fbaa682fee23` (27) |
| `Toy.TailCall.Val` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.Val.obs` | `propext` | `c66c30acbe03689e510f2f8011fa188ca3c17dfd9723b265c3b169e7bc581187` | `f134b61d966a7f88d22439711a0c461c0d5bd2498d46ef32d8fcba58ccb988ad` (5) |
| `Toy.TailCall.Val.pointsInto` | `propext` | `f42fec0ecc139577c6b63a8a282ea354217c53a1950f4efe6af0b1b08b44b1bb` | `f134b61d966a7f88d22439711a0c461c0d5bd2498d46ef32d8fcba58ccb988ad` (5) |
| `Toy.TailCall.allRunning` | `propext` | `781bd8cc8f6da2e9575bc475e13e3f64b5cab2e26fd55087666eae1005c55991` | `5ac1c042aef89e552869aee2f46bdf8063625e922d1fb3411a7fb6a897ac7d4c` (58) |
| `Toy.TailCall.allRunning_sound` | `propext` | `0133eda37a2bfdf722ba8c75266bdfd0a7aa732ffb38c7dc28a471fb5004b591` | `bdf7ca62db7544a97840007a84214e9edfc4f102436761fcca2b6ae5de73d462` (157) |
| `Toy.TailCall.assignTemps` | none | `aaef244a8f200cbf54ab323c4505161b1557feb650f192544b76d1e8276e1fb2` | `bccad8f7a7e1df32e8e40aad64d9993154632f91d0eeb0d588cc01c29afd0dd8` (20) |
| `Toy.TailCall.atTailCall_panicFin` | `propext` | `b6a686d40d17ba19cdc99e5df5f18b33de85f73bee91b7db89ee763faee3cd62` | `d0bae995d70d55af0080e2b9ffeea0b40048f75a72583eddfb82b1066470cea7` (80) |
| `Toy.TailCall.badArgTailProg` | none | `444544bab219f2567f9d9b13331157852ae4479413200bfb9c291f0080c70dab` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.borrowProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.bumpTail` | `propext` | `7ce6cdb33d41096cb041b662b2de924963ee6c518d0c6a2061617849c16327ef` | `486a38a303f255f97d0fdbe7ef74c301479f1aeed73cea8e9dc3fbaa682fee23` (27) |
| `Toy.TailCall.callFree_chain3` | `propext` | `2fb10ebacda06e784aece53ff8da55035646e913f4e025083015fbd66c692c6a` | `72c36713f65c076b53f816351e29b743cf60e6b206c9f2b7c4c225201c26ffac` (37) |
| `Toy.TailCall.callFree_frameReuse_maxDepth_of_entryOk` | `Quot.sound`, `propext` | `ca353052daed84e59fae59879b11c0e2f0eb8360d21b9493218a47cbe3c6d3aa` | `153c29155a39ad8b71d03cef6b353670e26e749041ce018b9a8ae1e3ce3085e8` (163) |
| `Toy.TailCall.callFree_needed_frameReuse_countUp3` | `propext` | `36ac16f981dccacc0faf7f4d065f466a1262b42d7e6fc8ec28aed051244d08bb` | `ca537a1c1f3b0b0ea632aae791760a512a0672fb7dbe89dd9af8503e181c6ae3` (163) |
| `Toy.TailCall.callFree_needed_preJump_countUp3` | `propext` | `a1f4f30e73984f3aa3e38d64aa2426ea15ea6b0337a9dd0a25416e68c6dc383b` | `ca537a1c1f3b0b0ea632aae791760a512a0672fb7dbe89dd9af8503e181c6ae3` (163) |
| `Toy.TailCall.callFree_nonvacuous_chain3` | `propext` | `04c4c2f6cf5e443fed66b0943d66a50908fd585635bc4da355a3e38cb8d7ba1d` | `4b3d478eb7ece8cd139a14c7b2eb0bb7059409874991a1ac12f7e3ea85c3d95d` (163) |
| `Toy.TailCall.callFree_preJump_maxDepth_of_entryOk` | `Quot.sound`, `propext` | `8c9e53e340c61b04670880260750148b497a0648244fb4b3500ed5ec90016080` | `d539adcda2240578ded9fbc34e226c93ff7f77fa45cf60024723810b405ee30a` (164) |
| `Toy.TailCall.chain3` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.correctedCallSiteSplice_converse_false` | `propext` | `49b61303fec2464a3bfbb307db6ca68253e109aec7565a169bbb3dd27a49c5bd` | `7779f2d760c5dafee5b6b13f27509807d3d9adbb50bae94dca1f64e036596b95` (188) |
| `Toy.TailCall.correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow` | `Classical.choice`, `Quot.sound`, `propext` | `c62d8571e7b9ecb29be78a6b0b4f553afc7bf869d9db2e92638db9725ff2216e` | `7779f2d760c5dafee5b6b13f27509807d3d9adbb50bae94dca1f64e036596b95` (188) |
| `Toy.TailCall.correctedSplice_converse_fails_borrowProg` | `propext` | `3b1c7957dd5bc7aefeb7ea3857faf4282377703f453bba22fae4d82ed1175eaf` | `f05d218ced462492adf4e9bb3abdf18086f371b15a7b1ba20e5349f6cd83a391` (189) |
| `Toy.TailCall.correctedSplice_converse_fails_plainCall` | `propext` | `31603393cf69e712666a73535a1abbd4cda4ce5d86be0ac08c71069dd009a5ab` | `449afc21e4f8fb797b9362783722134ff09f65e014d75ca1eb657b688aeb946e` (189) |
| `Toy.TailCall.correctedSplice_masks_borrow_ub_borrowProg` | `propext` | `60bcab6dc1063273a0834823fcee479f89067a4c723e08c4330e12bf6b85cc8e` | `f05d218ced462492adf4e9bb3abdf18086f371b15a7b1ba20e5349f6cd83a391` (189) |
| `Toy.TailCall.correctedSplice_nonvacuous_inlEx2` | `propext` | `73da7e5751ec2c710e5b5583654c7b5b0844f2add9b570c825d2e60f3c0d2753` | `16c05d7c73d2a89e2cc3c6d3b3a5e18eb33124d5cef12d95a2c1e92290328c70` (189) |
| `Toy.TailCall.correctedSplice_overflow_not_preserved_plainCall` | `propext` | `b7751e6a8721267e00869de2ee111115f7a92fcc9fd691a97ec5fff05ddfc2a9` | `449afc21e4f8fb797b9362783722134ff09f65e014d75ca1eb657b688aeb946e` (189) |
| `Toy.TailCall.correctedSplice_raw_values_differ_ptrRetProg` | `propext` | `84285fc192769098772b578e8fdf0b929b10fd860e64d62ea31f28d2d13d3233` | `2e817bfecace9f57c1638aefcd64af1b2eb87ca1d479b6a3a0a41252ad5726e0` (191) |
| `Toy.TailCall.correctedSplice_tailCalls_differ_inlEx2` | `propext` | `0650809bcf6a6045a0dce984bc545d5f1e81ce7108140d7f73756c60a013fe19` | `76d75880fa6c55c7c566f595daad4451c72a53ace71c2b26ff9850e25b962ce8` (186) |
| `Toy.TailCall.correctedSplice_ub_not_preserved_danglingRet` | `propext` | `e732944db6f383d984f7df7355a3bf44c09ca2f67aba96f6cf062ede80ff3472` | `87f6501356727e95ac312f5627d429059eb0c21ed912a6488ca2dcd428506c39` (189) |
| `Toy.TailCall.correctedTailSiteSplice_mutualRec3` | `propext` | `b9ba4b56c5f7b172f7df664fe6676dca7d2538b1b2617b4e32c867fba4c41f07` | `cff4a4664fb6d47580b99c89e95f8482b01310262dfb3cb1a1c71d13e5b3cfdd` (190) |
| `Toy.TailCall.correctedTailSiteSplice_mutualRec_overflows_any_slack` | `Quot.sound`, `propext` | `4e37a2d7a647aca4b462e7ef496f0ccfc081bdd65171d885ccf80996e0c686b5` | `cbc0b339928b44ac4036549251711de5ce4cf15b9506bb7f5afa6844b92fd40b` (193) |
| `Toy.TailCall.correctedTailSiteSplice_mutualRec_runsTo` | `Quot.sound`, `propext` | `57ad296b4d607a4320172bcbed4b74a02869d5df12ac85243ddd08ac3051bec2` | `cff4a4664fb6d47580b99c89e95f8482b01310262dfb3cb1a1c71d13e5b3cfdd` (190) |
| `Toy.TailCall.correctedTailSiteSplice_overflows_mutualRec3` | `propext` | `c40cb0920e9c47ce9885f3ce2b671efcd439dfa4e802b05ccc436890dd26c173` | `cbc0b339928b44ac4036549251711de5ce4cf15b9506bb7f5afa6844b92fd40b` (193) |
| `Toy.TailCall.countUp` | none | `930ac4aca58800e6cec2d1359ca65e9b8247321928b59d9174c9f10a7fff1b2e` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.countUp3_bound0_overflows` | `propext` | `f20ddd433147debba768734d1fc6292158d890b44495da0cf49d7e059f6b3e1e` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp3_bound4_frameReuse` | `propext` | `5742f35532e4e060822ef7bee056d04a728b7a2ef0a6dfc077eaafaa666b6299` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp3_callReturn` | `propext` | `132bf084f21086ed14cb55622e224d4d7ef23b85b4c744f8718d119fdbb716b4` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp3_frameReuse` | `propext` | `b31be111ad3adccc2a74eded01965d35bc34f99f5e6d245cb031fe4b7a1eb6b1` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp3_preJump` | `propext` | `d5f83852c32d99d706a1a21813d25daa744f844c6c6abdd92fff17d398d1ec16` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp_callReturn_runsTo` | `Quot.sound`, `propext` | `936d54d4cf2922b4f5d0b7a183fa3d48c31c41eb1d9dd47272a4c4f859fe01e7` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp_frameReuse_runsTo` | `Quot.sound`, `propext` | `7bc59cc3e09bd43f88ad511569bf9f9de46b0e71d50b966dcf30be53bec52852` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.countUp_preJump_runsTo` | `Quot.sound`, `propext` | `9d91353b3b642f318fcd103218046e5a77a394a6d9f19932373bae6a5ad5d2a7` | `7bc2b3fbe0b77baccfd415a8aa89228e567d00926bea2084a1dcf01a276fe1fa` (158) |
| `Toy.TailCall.danglingRet` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.deadEscape` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.deliver` | `propext` | `325b08fe7429f877c80aa73129e347024a0c70346827ab9cc6a965a617ff4d9d` | `486a38a303f255f97d0fdbe7ef74c301479f1aeed73cea8e9dc3fbaa682fee23` (27) |
| `Toy.TailCall.desugarTailSite` | `propext` | `38545bde5d9a7d9ce60e0691e821ecf2f2de5d5c02f19d5efab70ae82f4db31c` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.desugarTailSite_mutualRec3` | `propext` | `07de4883e596c4b55263432201baa9f6434842760dc47c8c4386c090d26164e9` | `2339ca9f38a4a58914f1646e42097dc7761041be618801cd87295110b9e77c9d` (49) |
| `Toy.TailCall.desugaredCallPc` | none | `eda2dc74816d062ced4f64350ab7090fdf543bf1d301103d4f9693ed00a799cc` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.doReturn` | `propext` | `a0433aba1a2034249acdf2203747d09fcc59e9a117cf2e4626ed9e5452e0f554` | `e8b05e7f2fb448faae99929471280afced0105ddcd470b1d01871163609798d8` (51) |
| `Toy.TailCall.doTailCall` | `propext` | `fed74e13ab4fc10a219848c50031cd68ca54d4892e5d11c5e9dc7e7df51c35af` | `5ac1c042aef89e552869aee2f46bdf8063625e922d1fb3411a7fb6a897ac7d4c` (58) |
| `Toy.TailCall.dropList` | `propext` | `6537781176a21a1d69e67ba8a81f3cdf4696463a3b6c287a909d7f50ec902b7b` | `11f52b8f764681bd46568874384a7a979f131bbe041aba310dd79c1cd96ac8ff` (42) |
| `Toy.TailCall.dropList_abort_leaves_pending` | `propext` | `60a58d527ab7bfeb1d7651eeaf45ee1a16d8b6516ce7d46f43b5db542fa3ea26` | `3c15930e1e85fa0925d876fbf2b3ebbd13d4fdd8543dc748a46adb144d5f4d7b` (70) |
| `Toy.TailCall.dropList_clears_pending_nonvacuous` | `propext` | `12cef641726c64f7a299b8556f17a239f01cdf606f05c272645c8e084d821178` | `3c15930e1e85fa0925d876fbf2b3ebbd13d4fdd8543dc748a46adb144d5f4d7b` (70) |
| `Toy.TailCall.dropList_clears_pending_of_ne_abort` | `Classical.choice`, `Quot.sound`, `propext` | `730fd969f3824221d577ddd22027642d49349e450a78c48dea886e2a40ba4746` | `3c15930e1e85fa0925d876fbf2b3ebbd13d4fdd8543dc748a46adb144d5f4d7b` (70) |
| `Toy.TailCall.dtorProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.dtorProg_callReturn` | `propext` | `c84053bb24ba8048476878fdc7435491be87c340f2c90af71199d33f93adcd5a` | `ad09cd5674701e3f848cf1c06831b578a4fb1e5e70f4a8d2b2efb034f28147e9` (158) |
| `Toy.TailCall.dtorProg_frameReuse` | `propext` | `607814b641c92e43c6ead8cadb3eb29a41431610b73ee4d37044c019c32c70f7` | `ad09cd5674701e3f848cf1c06831b578a4fb1e5e70f4a8d2b2efb034f28147e9` (158) |
| `Toy.TailCall.dtorProg_popFirst` | `propext` | `a76ce46967fb93c165e91020fd5d466d6989bd73aa1622f1b331ae4c295a5444` | `ad09cd5674701e3f848cf1c06831b578a4fb1e5e70f4a8d2b2efb034f28147e9` (158) |
| `Toy.TailCall.dtorProg_preJump` | `propext` | `6353cbc8796a82758cc80b492d134f6be9177c1803daa581ddb5293e6cf0b0b8` | `ad09cd5674701e3f848cf1c06831b578a4fb1e5e70f4a8d2b2efb034f28147e9` (158) |
| `Toy.TailCall.emptyProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.entryOk_chain3` | `propext` | `75e870f77c6100b09b192dc955cb88bc6d92f07ebaa026f9b8fd538e7d44f579` | `0761939cb7b23e3d018a7767e15020409804180c269b1b0ca779f0ab6d1de8cf` (32) |
| `Toy.TailCall.entryOk_needed_emptyProg` | `propext` | `96231ec11db3997e03225ce70618db5152d91d212006743cb4e84c64fd77d26e` | `c1c28662baf96e7efb73831fb972890286ec64cccffb445c08c7afe54bf9c67a` (163) |
| `Toy.TailCall.entryOk_needed_paramEntryProg` | `propext` | `d7fba79c34dc15c62b2e67d8b90d2facf4dc32c54a36b9391e43c6607fd8a8be` | `6b4f6b7b8dc6b0b4e2f3817782b16d7cf029b5ae169a7ac09bef5845751ee4c5` (163) |
| `Toy.TailCall.escapeCheck_accepts_countUp3` | `propext` | `b01ff5ff1a4fdbe7c7ac8a0cabcc3c8df6191329aac38881d6c3639e4c975fe5` | `2055a2b323e0a4c7b21d935d6f2a0c64687d8e5e80d77e545ca8cb02889b2c31` (48) |
| `Toy.TailCall.escapeCheck_accepts_dtorProg` | `propext` | `be224366d724f14d0284d7cbe9e6a6a5ce30b17503b82a23f291dc11910e7da9` | `e9daa5c0a250b04a402a0609e32195d5a6d07f7785635a2c27db1f2097806284` (48) |
| `Toy.TailCall.escapeCheck_incomplete_deadEscape` | `propext` | `976e1bb99c7c1dd04b02ef4af09d50fc845a9b368a671f60450de7af051c061f` | `725638bd75ca26349b0c5a28608228cc613da474ad4a338629e8c3f82d5c0289` (178) |
| `Toy.TailCall.escapeCheck_needed_borrowProg` | `propext` | `00968f16df7a4f103abf77453b68a747cf8abfdafb3717673722728ed9605e6b` | `afa4b7db535846ca77b63b5e2ad54d43403dfd6621293b7088d75465ac5b2cdc` (178) |
| `Toy.TailCall.escapeCheck_rejects_borrowProg` | `propext` | `98dce4ca20f6a4175c41090edca1b87125f4115dee4c7ac32f15b752f4aa48e3` | `0743024fc71353b4587a541064a7cd4d15065ade97f3b256c0f19f963a3c7846` (48) |
| `Toy.TailCall.evalOp` | `propext` | `82cd77413a1f99dce0b64f97c2a869972682f9e525d5a0593ec4d35732b9d9fe` | `898cea7af2ea8ddb68a06491fcff49b111f7c9ae8d8b4a95f3e6788cb199f3d3` (18) |
| `Toy.TailCall.evalOps` | `propext` | `3c0ed6677d3be8a7f51411d6df1685c66a7630979b228f726d9698c2fb4fa7a9` | `898cea7af2ea8ddb68a06491fcff49b111f7c9ae8d8b4a95f3e6788cb199f3d3` (18) |
| `Toy.TailCall.finalizationEvents` | `propext` | `18d00b84bb8e7490ee3454109bbdfc780ead29c527b0e8dee1b2934a6a67c799` | `81fec6fa6b36321f02d7a6b393881a429cba0ec0f9b7c382fe4237ed2e4a8982` (38) |
| `Toy.TailCall.finalization_fails_at_other_instr` | `propext` | `10666ba9006bc4b5572cfb75fcda75e5a19a2f7ad90f2c9ad6243eedf4fea9f3` | `ab96f0192895fe9de07e93f5a8d1915b0dde2b6c523c26a570d5a5652aa7bcb1` (158) |
| `Toy.TailCall.finalizes_then_push_fails_when_args_ub` | `propext` | `c08409f76d45c87a01fe4421b7c0c3558d7c546659f9f894b73998ddaa3f8d92` | `ba86377726583e193f1becbd90a7447053249811d52355c8f2099c20cfca7259` (156) |
| `Toy.TailCall.finalizes_then_push_fails_when_unwinding` | `propext` | `6462b143d19f355028f5b685abb26c90203057259f52956f47cda283302a7719` | `6d5dfe439410a38a47482b3046fd0f8054d0e1eeccfa30eefa543f6a4d5eaa49` (158) |
| `Toy.TailCall.finalizes_then_push_fails_with_panic` | `propext` | `d11f10e0b539296743f589e290a15640cdc61558dde5673466c57b1274629be7` | `144c8511de85b0ac6200a5263c54c04d199a39a4b1bd203844893c84c226d5d5` (160) |
| `Toy.TailCall.finalizes_then_push_fails_with_pendingRet` | `propext` | `f62a83903c95c95ca4f387cd05f7e385f4910b397c4d0d4dff2593c59b598596` | `3df459924ca2a205e1befa63d4b9821484917b4b48764f75a3cab7c5416b2a1a` (158) |
| `Toy.TailCall.finalizes_then_push_nonvacuous` | `propext` | `8a3aad441aca9c732a82a59b3be8061b20a7c4f8737be689634ea86a0ab0460c` | `da342d7099a8dde6767d5450d57a56b760a9033ff0426bfe9e99dc17e0b93ef8` (93) |
| `Toy.TailCall.findFrame` | none | `24ca5fc8269031c0f88cf38588f8c94590650f9b86a48343b11e8097d051478a` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.frameReuse_finalization_unique_panic_drops_rest_then_unwinds` | `Quot.sound`, `propext` | `f5b2d5302d54188bd4d69e6e42799d89846aed2606f3d12536176919f9e1c260` | `30e5938a2f89615131fa2661ed683b4fec4d4b6f914118f4b9f120013a4b544f` (155) |
| `Toy.TailCall.frameReuse_iff_preJump_fails_borrowProg` | `propext` | `7f13038dd146af11c03c19b275c69bf6b0a71ef8292e6f347fb87c4e5b3c1c01` | `bbb8c4c8e2fd777a60c5e70fdd14e401d4eabc4ebcf5a4547e1582807fa6f65f` (173) |
| `Toy.TailCall.frameReuse_iff_preJump_nonvacuous_dtorProg` | `propext` | `dd591a6911a3fde0a5116eea04049dbaae7417ba9e9f75d2ed522b8c5462a130` | `da7bfbae2e0f9636355fc7a1f97426ffb51a73f26d5309a24aa1a2b66adc3939` (173) |
| `Toy.TailCall.frameReuse_ne_callReturn_dtorProg` | `propext` | `8e349b60e6599401c08f5901ea50f41f20b45e5bb34cc9a9bbe5d8c8bf8ec018` | `da7bfbae2e0f9636355fc7a1f97426ffb51a73f26d5309a24aa1a2b66adc3939` (173) |
| `Toy.TailCall.frameReuse_observes_iff_preJump_of_noStackBorrow` | `Classical.choice`, `Quot.sound`, `propext` | `096d09746c0443ad7c6b935226744434f9ffe689bbe22659d8a7729a0d936192` | `be9c77b76261e0975a60ed1035c670b1f2c8b27372a4b7bdde563d854ad40ed2` (172) |
| `Toy.TailCall.frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow` | `Classical.choice`, `Quot.sound`, `propext` | `e3e8f59242edf8775ef2d49aac97568dc03166b70a64cec757b2057099dee52d` | `be9c77b76261e0975a60ed1035c670b1f2c8b27372a4b7bdde563d854ad40ed2` (172) |
| `Toy.TailCall.frameReuse_of_preJump_fails_borrowProg` | `propext` | `3d5691b084bab0af7a317bc111b71d12fe1630ad613ae148e75acf6285886e24` | `bbb8c4c8e2fd777a60c5e70fdd14e401d4eabc4ebcf5a4547e1582807fa6f65f` (173) |
| `Toy.TailCall.frameReuse_of_preJump_fails_for_overflow_countUp3` | `propext` | `7df0256bd649df1e3708a9ab782907a156265d72d5d4b166d5a8677ee1bcb626` | `7643200314766dc52488453b9c64881444f85edab73d2f538689d0611fc8fc2d` (173) |
| `Toy.TailCall.frameReuse_of_preJump_nonvacuous_countUp3` | `propext` | `2dd0a3a63e5d5943e41707ab61a1d0378ca3f4d0b1a1b4860ffd0e68b80cda28` | `7643200314766dc52488453b9c64881444f85edab73d2f538689d0611fc8fc2d` (173) |
| `Toy.TailCall.frameReuse_tailCall_finalizes_then_push_of_noPanic` | `Quot.sound`, `propext` | `ebf9f311264f25dff814136cb16735c53587a082a042f7f1dc3d443116e9e426` | `30e5938a2f89615131fa2661ed683b4fec4d4b6f914118f4b9f120013a4b544f` (155) |
| `Toy.TailCall.ignorePtrProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.inlEx` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.inlEx2` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.inlineCallSite` | `propext` | `c99e8814f7474647afc671bc32afb81c54abd8f89a73989049e02678fff63299` | `ff1cbe0214c6f042eaa1cb32bb4777d558c358a21719db5cc12ce043bf2e4fa7` (31) |
| `Toy.TailCall.inlineCallSite_corrected_inlEx` | `propext` | `26c042a1ecd9893b7b1ebfe1c55b7de42570b2573e1c8f051b576c00719dd1b4` | `c53eda435206af5a5444d2de0ed8e987728e977e488b53608335d11e037b16d5` (66) |
| `Toy.TailCall.inlineCallSite_nonCall_unchanged` | `propext` | `b4b6ccd9962ab35dbdfe0b01b76d1f3fe430493ed56179d51c4644e529a2bd78` | `c53eda435206af5a5444d2de0ed8e987728e977e488b53608335d11e037b16d5` (66) |
| `Toy.TailCall.inlineCallSite_self_unchanged` | `propext` | `c56c915bc62e4347cf83d194c631d0bf893c0bbd15bb5b684d241d8b455c48ee` | `016539b9b55e47f27ab69bb6b2931bff5f0e6afddd2ec0712e42dff7e3b57a66` (66) |
| `Toy.TailCall.inlineTailSite` | `propext` | `c99e8814f7474647afc671bc32afb81c54abd8f89a73989049e02678fff63299` | `ff1cbe0214c6f042eaa1cb32bb4777d558c358a21719db5cc12ce043bf2e4fa7` (31) |
| `Toy.TailCall.inlineTailSite_nonTail_unchanged` | `propext` | `4f074e60defcb0ab6bd0f1decbeb171eac771c6608fc99e48bd13ac36abae878` | `586def681ee1cf3a4175d9a3a54b86c361c74124ff8ae853b5f145468e7cc1d1` (70) |
| `Toy.TailCall.maxTailArity` | `propext` | `eb4d40f642282eb4e3ff2ce4db7c7a7e4c09e541d6bfe3e58998efa920440a53` | `bccad8f7a7e1df32e8e40aad64d9993154632f91d0eeb0d588cc01c29afd0dd8` (20) |
| `Toy.TailCall.mem_pendingDrops_iff` | `Quot.sound`, `propext` | `ee585552ca533cc79c2e202d6653df03b94b467b9c2d039e5df3e86b47bb7eec` | `7d6a3e876f0be9d9ac8ecacd64f56fef210acc5e1763a1378b0c9a3bbf397d37` (47) |
| `Toy.TailCall.mutualRec` | none | `930ac4aca58800e6cec2d1359ca65e9b8247321928b59d9174c9f10a7fff1b2e` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.naiveSplice_changes_events_inlEx` | `propext` | `1ec5ab8b01e31c9b4567de84222c6f2193e74e3796a61394c696cb2ca5d94757` | `38c06a8b2a727a245afb2d5e21c79de16677d0d88feea223bf970dba072560c5` (189) |
| `Toy.TailCall.naiveTailSiteSplice_within_bound_mutualRec3` | `propext` | `abc6f9a62e5a9586089c19d2bfe8dd672a55eeb6e27a19e57aa3001bba17c59c` | `cff4a4664fb6d47580b99c89e95f8482b01310262dfb3cb1a1c71d13e5b3cfdd` (190) |
| `Toy.TailCall.noStackBorrow_deadEscape` | `propext` | `45c8492333e985c62b49ecf17024b54a9a325b0f163b47391b37537c97d64be1` | `48bca69ab36555b63bd9d1d99eff1a52568d2b8d4466564cef422f0316694d67` (169) |
| `Toy.TailCall.noStackBorrow_dtorProg` | `propext` | `8389328aabb44bb3c8f73011c0d28e21a7767fcdd5de3e5b87b08e759f3c3bfc` | `915d57b8624b348046d01bccd740d3101b820ad192aa8dcf30e2e993bb4f7243` (169) |
| `Toy.TailCall.noStackBorrow_not_necessary_ignorePtrProg` | `propext` | `f7fcba1c4cdea945dc457fa4549a6b521e940f450519def92b284729f94d4c5f` | `e8d25918f04940d105f59d8275a659fb21a2c2467af86685205f5bf6c84908b1` (173) |
| `Toy.TailCall.noStackBorrow_of_allRunning` | `propext` | `afd86a6edc0067345554d5d60e53a135edafe91632894fef4c05df9a397043e6` | `ad330e23401bfd8b432d7a48ddf461d6eb23d1039f24a156bedf5de1de51ebc9` (171) |
| `Toy.TailCall.noStackBorrow_of_escapeCheckAccepts` | `Classical.choice`, `Quot.sound`, `propext` | `c9fe6d178fd03a5eb2c739c1bbd948884a4cd5a05642b2f7bab0fb180ec90fca` | `4824f5a47231d53aa9f02001dabef9ae76ff16db84b64615bc0d0178df0b42b0` (177) |
| `Toy.TailCall.not_atTailCall_wrongInstr` | `propext` | `ac3fecf9ac8110830c7ceae8ff246c3f86f78aa80b7e2c2fac081f6c8d9c99e3` | `b946411a03760d14e772c9d1fff141e7de1ba94aaa5ec72635747317ab803f06` (78) |
| `Toy.TailCall.not_callFree_countUp3` | `propext` | `73e6bd850884434078c009ac8c6394b9f9758f10129ae7114c162dc760da27df` | `5411faa360ffe895ba6c8bdf24d269933ccba537e85ee0064958e50d5315618b` (37) |
| `Toy.TailCall.not_entryOk_emptyProg` | `propext` | `ee9273fa6b9cc7fb88a4929eb1d7f3f83c2943ca5f776ec8d1173d89b93689bd` | `bfb83866293fccc61f18f1d5b869c71360a2816bc5ae0392593429f96241dead` (32) |
| `Toy.TailCall.not_noStackBorrow_borrowProg` | `propext` | `460ff1d8f678f3270fe2c0321c889db47212ae305e9ddb499556d48e78578095` | `260c92d9e3083726b5e4c0737ce67066b3c66fdf69b847f66818bed78725bbde` (169) |
| `Toy.TailCall.not_observes_dtorProg_frameReuse_callReturnTrace` | `propext` | `ce5d31c9bdf1c15f08e4e189e537d83d62a87b5c8e9cae8248b71fca3455b555` | `873f47f2aeb77cb4fdd04e46fe6fbb8cc6c6d6718216e3081332c82beefdedc6` (161) |
| `Toy.TailCall.observes_iff_of_runsTo` | `propext` | `b2b21001824ac41858f9343dcd370491d424d9a57cf9c651ff10037201f198dc` | `e08ada92b84a7f2bc5390fa1fae1587078791f77207704d7310e87dc7d9167ac` (160) |
| `Toy.TailCall.opTainted` | `propext` | `e66fb977338d13c8eef33928a3700095eec9b5e938a15c2190180c803c4541cf` | `fd04a17e881a1597f0f0d68d114841011ef4245d42d145c2b05b7026f25b907a` (8) |
| `Toy.TailCall.orderDemo` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.orderDemo_frameReuse` | `propext` | `5fbd765b7ae70495c85f0bd84c842008bb2ed4b49f4501e7846d969fe4b80d55` | `6378142e7041890620353b825a8aa0e63f08b6cdb74662fb4c0733db9875bcdd` (158) |
| `Toy.TailCall.overflows` | none | `dc9c02b7e2e10803c21e2623fa24ae4615902af65038113975bec713f1ac9201` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.TailCall.padBlock` | none | `bc50d434906b445fa7b0d6512ba772c55aa1f66807e21dc12a360b97743497f3` | `bccad8f7a7e1df32e8e40aad64d9993154632f91d0eeb0d588cc01c29afd0dd8` (20) |
| `Toy.TailCall.panicFin` | none | `934b33add02753bad3417f2adfc6e8dffdd75b471842b790893b2b98fb6bae3e` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.panicFinFrame` | none | `fa4d9b9cb398488a4f7b5cc35afebb698a797894a30fb83292d0e512ba44b30a` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.panicFinOnePanicNoTail` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.panicFinRest` | none | `b66ae47540941be51d602170fa0577e08262ec03f76583533a3365fe1cad7655` | `bb7bd46b4018ec419061196f28b4fa54e7698dd6e48609a1419ed55cf780e374` (11) |
| `Toy.TailCall.panicFinState` | none | `d99634d5dccdb51b3d6551463fb918c2251a24257be7c863ae5353d111c3c235` | `c59b3adb987a48ddaebbe376d72c0f46da53758551804714248944276d4aba20` (16) |
| `Toy.TailCall.panicFinT` | none | `489f148e717ccce748e8ec4cfae0ef735862700e19202f288f0e7bbe0ee4dfb3` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.panicFinTOnePanicNoTail` | none | `75894ca55c508fc3162960f231e4bc0cc45dcbf59bbb91e20e915c5ffa7d88f7` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.panic_drops_rest_fails_at_other_instr` | `propext` | `c3b9dc3eafeae8b488983545b024e308ba3b9d35be52ef170481c046b3e9b5c3` | `c8b501ff0e0dc51078fdfe8feafc57515b423d9fcf920203b21d3e71263c04de` (158) |
| `Toy.TailCall.panic_drops_rest_fails_when_args_ub` | `propext` | `304ecdce8c37343ec471e259130d66dd307bdca545768c378717fe61b492f931` | `ba86377726583e193f1becbd90a7447053249811d52355c8f2099c20cfca7259` (156) |
| `Toy.TailCall.panic_drops_rest_fails_when_unwinding` | `propext` | `b69ebba7ae09925b8fefdace17f792190c36c503443c1193812981819c643fd1` | `6d5dfe439410a38a47482b3046fd0f8054d0e1eeccfa30eefa543f6a4d5eaa49` (158) |
| `Toy.TailCall.panic_drops_rest_fails_with_pendingRet` | `propext` | `167155be8b0f766db1bc9d45861e525f5c3771c600506e077880cd3c5b77eefb` | `a28095ab8500e1ca7a3eb7ed7b539d10f2b38c8baf1df7d98e9405231a69d5b9` (158) |
| `Toy.TailCall.panic_drops_rest_fails_with_two_panics` | `propext` | `0513c29f95a1e46f1d21cd4fd78cb36f454cf5b3dcebab7e85e5103240e3fc23` | `144c8511de85b0ac6200a5263c54c04d199a39a4b1bd203844893c84c226d5d5` (160) |
| `Toy.TailCall.panic_drops_rest_fails_with_zero_panics` | `propext` | `ac313fcc29b689f3c394c72585204fa14d8af8df4164c2c8c134cea38eacdcbc` | `144c8511de85b0ac6200a5263c54c04d199a39a4b1bd203844893c84c226d5d5` (160) |
| `Toy.TailCall.panic_drops_rest_nonvacuous` | `propext` | `31f1234f983ba729467be1dd2f4ae7622ff4179c1ed22862d63917e8ce0981de` | `da342d7099a8dde6767d5450d57a56b760a9033ff0426bfe9e99dc17e0b93ef8` (93) |
| `Toy.TailCall.panickingPending` | `propext` | `5aba3076195f6374e6ffba3cb8a5b4e363ec412c4b433155fb7792167a1250e5` | `56c44c614a1c84ddf3326802fdeb33047be7fc782135869f39faaffb75480126` (35) |
| `Toy.TailCall.paramEntryProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.paramEntryProg_bound0_ub` | `propext` | `481775e71541477fbea8fe81b1821157187a20df49bb09ffba74409de0d8fab5` | `fd322961e532cea9b852f262719ff46633aaf9666d8d892cf6490d6a9b076014` (161) |
| `Toy.TailCall.pendingDrops` | `propext` | `5aba3076195f6374e6ffba3cb8a5b4e363ec412c4b433155fb7792167a1250e5` | `56c44c614a1c84ddf3326802fdeb33047be7fc782135869f39faaffb75480126` (35) |
| `Toy.TailCall.pendingDrops_orderDemo` | `propext` | `d10e47530782e56d776d0bd4d9a92302e2ad7463766dd04579cd5e64d24aa474` | `7d6a3e876f0be9d9ac8ecacd64f56fef210acc5e1763a1378b0c9a3bbf397d37` (47) |
| `Toy.TailCall.pendingDrops_pairwise_gt` | `Classical.choice`, `Quot.sound`, `propext` | `fad3bd58f2c7b291d51ebc1214c1f06ba0063f9336aaa5dbe26505b659c4bac4` | `7d6a3e876f0be9d9ac8ecacd64f56fef210acc5e1763a1378b0c9a3bbf397d37` (47) |
| `Toy.TailCall.pendingDrops_skips_no_dtor` | `propext` | `f2e3fc1d5c3c6010f00a5478a210c74d2f9335de26c36fd326d3301ad15f1485` | `7d6a3e876f0be9d9ac8ecacd64f56fef210acc5e1763a1378b0c9a3bbf397d37` (47) |
| `Toy.TailCall.plainCall` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.popFirst_agrees_without_pending_drops_chain3` | `propext` | `9f9ce69cb4a63c51b58b389cd5757d877ae679e603add1add0d8a070adb5ec58` | `83d9a5c3f6ae34684edb528d063dd334e7b6da172c10e11a0f2afbbecc502aa4` (158) |
| `Toy.TailCall.popFirst_ub_with_pending_drop_dtorProg` | `propext` | `bded2d6f190bc688be17fbbcab6cda0462c0ae33ca5331783d9b260532718ae8` | `873f47f2aeb77cb4fdd04e46fe6fbb8cc6c6d6718216e3081332c82beefdedc6` (161) |
| `Toy.TailCall.ptrRetProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.push` | `propext` | `b2ea4ca69483a1f8b9a7d363c96fdc9b514597b8a9330c72af783185de50b51e` | `0ff568e0c316322cda1665733b71d510dc9fa9d45542b085dfe1f3ec8bef05f4` (53) |
| `Toy.TailCall.renOp` | none | `28e2b475c17ba5d0fc61e9899049345fce8e4fafca9ca93a6976329be3579d58` | `fd04a17e881a1597f0f0d68d114841011ef4245d42d145c2b05b7026f25b907a` (8) |
| `Toy.TailCall.run` | `propext` | `a55d721497a14380616c58615bde5a15a577ff5cde2205c6cd11c4aa1e18c5c4` | `5ac1c042aef89e552869aee2f46bdf8063625e922d1fb3411a7fb6a897ac7d4c` (58) |
| `Toy.TailCall.run_halted` | `propext` | `054bfd9920a0fc76ecfb0556bd28732590ab5fe60c89d772860ed22633ed5696` | `c5d9a566ea34cc3a1fcef4249d740f4b8f4383ac1e36e04ea2896249ec6209c2` (154) |
| `Toy.TailCall.run_mono` | `propext` | `1597dfc66c062a0291fe49a677e3c76c5228c5ed503bce8a6f76dce9d65a4a36` | `c5d9a566ea34cc3a1fcef4249d740f4b8f4383ac1e36e04ea2896249ec6209c2` (154) |
| `Toy.TailCall.runsTo_bound0_of_entryOk` | `Quot.sound`, `propext` | `a7e7138d4463c439c72269bdb5d637414ff4db063d5cb5e70b3b0a2c6c7a23cd` | `9936521ff52370f575fa26d0891cdea5b7f18e844485ee927c4e5cba3adacaa5` (158) |
| `Toy.TailCall.runsTo_unique` | `propext` | `ebb4dd7395c5eb6a0371cdd606807a6e5c7f02db04aa3855eca3a8089ef0cf24` | `b8bf767555f6567ea764cc86ac81b28f6e4774a1260e9d30d1bc58ed685d717e` (157) |
| `Toy.TailCall.selfCallProg` | none | `3b2a9c5a8115fe4caaf98689c07989cce41f2114659940c3cd53ec74128f4fb8` | `64508e93b9a6eebb15fa7295a49f83073847ba0562b72f6b12f259e1c7cbfb66` (28) |
| `Toy.TailCall.spliceBody` | none | `63ba27cdc378c05ef34ae362b308a725ee15d9993dd13e3c934c06325272c8b1` | `957a36c77919bf0234bacd19273be07ac8cb97206fe630170e3b5a2261bb72cb` (23) |
| `Toy.TailCall.spliceFn` | `propext` | `b5b4171683294198624ade42a984019ecbd6fe38b8a6956a8354771e63f6c247` | `d2ed17b92625171fdbc2e4b67683b969837e3217a5156a3bcc873ffe0dca13ed` (29) |
| `Toy.TailCall.spliceInstr` | none | `23def8fefe8e785e9e14425adefaf2480267de8b38f4e5a91cf50309c075f720` | `957a36c77919bf0234bacd19273be07ac8cb97206fe630170e3b5a2261bb72cb` (23) |
| `Toy.TailCall.start` | `propext` | `7f80e76e4f617fc037987c3c73646ad4863f314f5bea17331f22aa6afb3ceb8d` | `0ff568e0c316322cda1665733b71d510dc9fa9d45542b085dfe1f3ec8bef05f4` (53) |
| `Toy.TailCall.step` | `propext` | `3aa9b8f2d710473498a141c0b7c97275c5fc79c12e79c99e16d03199d57c3adf` | `5ac1c042aef89e552869aee2f46bdf8063625e922d1fb3411a7fb6a897ac7d4c` (58) |
| `Toy.TailCall.tailCallBorrowsFrame` | `propext` | `57ea28828f35c7a4d2631b80f10630b927e945b6138f0aeb5933810b4719a021` | `0fd74b0e580f707c0966cb1b27b495fc1f5b89c45d3a0bb02d034ec4b43eb0c5` (42) |
| `Toy.TailCall.taint` | `propext` | `f7aa107c0b3e49d7b92a9145cbe1a8b26c25b883bd502aa744bd6a0bd578678a` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.taintStep` | `propext` | `b064f08718a06e74f31874ab217ac54d2f8ead7420eccb7e6cfb7a3311fb581e` | `2a16caa1088bf958a45dc88beab422b2247183a4bbf68e93f70c2c36b1337fcd` (26) |
| `Toy.TailCall.unwindBelow` | `propext` | `ae786af51b1de320646a89f3d9c12d3cd45bac6c5b233131bfb1802cc617392d` | `486a38a303f255f97d0fdbe7ef74c301479f1aeed73cea8e9dc3fbaa682fee23` (27) |

### Proof status of the main theorems

| card | theorem | status |
| --- | --- | --- |
| R1 | `frameReuse_observes_iff_preJump_of_noStackBorrow` | kernel-checked |
| R3 | `frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow` | kernel-checked |
| R4 | `countUp_frameReuse_runsTo` | kernel-checked |
| R4 | `countUp_preJump_runsTo` | kernel-checked |
| R4 | `countUp_callReturn_runsTo` | kernel-checked |
| R5 | `callFree_frameReuse_maxDepth_of_entryOk` | kernel-checked |
| R5 | `callFree_preJump_maxDepth_of_entryOk` | kernel-checked |
| R6 | `mem_pendingDrops_iff` | kernel-checked |
| R6 | `pendingDrops_pairwise_gt` | kernel-checked |
| R8 | `noStackBorrow_of_escapeCheckAccepts` | kernel-checked |
| R10 | `Layout.reuseSound_callerPops_iff` | kernel-checked |
| R10 | `Layout.reuseSound_calleePops_iff` | kernel-checked |
| R11 | `Layout.reuseSound_of_sigCheckFull` | kernel-checked |
| R15 | `correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow` | kernel-checked |
| R16 | `correctedTailSiteSplice_mutualRec_runsTo` | kernel-checked |
| R16 | `correctedTailSiteSplice_mutualRec_overflows_any_slack` | kernel-checked |
| R17 | `dropList_clears_pending_of_ne_abort` | kernel-checked |
| R17 | `frameReuse_tailCall_finalizes_then_push_of_noPanic` | kernel-checked |
| R18 | `frameReuse_finalization_unique_panic_drops_rest_then_unwinds` | kernel-checked |
| R20 | `Layout.reuseSoundAt_zero_iff` | kernel-checked |
| R20 | `Layout.reuseSoundAt_calleePops_iff` | kernel-checked |
| R20 | `Layout.reuseSoundAt_callerPops_iff` | kernel-checked |

Counterexample cards, non-vacuity witnesses, tightness counterexamples, positive controls and definition examples are all kernel-checked.

### Primary sources

Upstream revisions (verbatim quotes in the modeling bridge and the prior-art entries, each with its full line range):

* `rust-lang/rust` at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`.
* `AbsInt/CompCert` `v3.16`, commit `a4ad87b17898cf7b7c8638c32ad694a15f7c0032`.
* `llvm/llvm-project` `llvmorg-19.1.0`, commit `a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4`.

Tags on prior-art entries: `used in the modeling bridge` means that at least one line range cited in the entry is quoted verbatim, in full or in part, in the modeling bridge (Findings), and the other ranges of the entry are described but not quoted; `cited in prose` means that no range cited in the entry is quoted there.

Papers (bibliographic metadata of each DOI checked against the Crossref record on 2026-11-21):

* G. L. Steele Jr., "Debunking the 'Expensive Procedure Call' Myth, or, Procedure Call Implementations Considered Harmful, or, LAMBDA: The Ultimate GOTO", ACM '77, pp. 153-162, doi:10.1145/800179.810196.
* W. D. Clinger, "Proper Tail Recursion and Space Efficiency", PLDI 1998, pp. 174-185, doi:10.1145/277650.277719.
* J. Clements, M. Felleisen, "A Tail-Recursive Machine with Stack Inspection", ACM TOPLAS 26(6), 2004, pp. 1029-1052, doi:10.1145/1034774.1034778.
* T. Ramananandro, G. Dos Reis, X. Leroy, "A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management", POPL 2012, doi:10.1145/2103621.2103718.
* Q. Carbonneaux, J. Hoffmann, T. Ramananandro, Z. Shao, "End-to-End Verification of Stack-Space Bounds for C Programs", PLDI 2014, pp. 270-281, doi:10.1145/2594291.2594301.
* Y. K. Tan, M. O. Myreen, R. Kumar, A. Fox, S. Owens, M. Norrish, "A New Verified Compiler Backend for CakeML", ICFP 2016, pp. 60-73, doi:10.1145/2951913.2951924.
* Y. Wang, P. Wilke, Z. Shao, "An Abstract Stack Based Approach to Verified Compositional Compilation to Machine Code", Proc. ACM Program. Lang. 3 (POPL), Article 62, 2019, doi:10.1145/3290375.

RFC 3407 (rust-lang/rfcs#3407) is an open, unmerged proposal and is not used as normative text (modeling bridge, B6).

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified) and checks: (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit` or `native_decide`, or declares an `axiom`; (3) every declaration of the `ToyTailCall` library depends on no axiom other than `propext`, `Classical.choice` and `Quot.sound` (Lean's `collectAxioms`); (4) for every Lean name in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and the hypotheses' `counterexample`), the SHA-256 of the statement (Lean `repr` of its type) and of its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded) equals the value recorded in `audit/statements.json`. It exits with status 0 if and only if all four checks pass.

A manual check of the build and of the axioms of the 22 main theorems, without the script:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target) runs `#print axioms` on each of the 22 main theorems; each reported axiom list must contain no axiom other than `propext`, `Classical.choice` and `Quot.sound`. A change to any definition in `Machine.lean`, `Borrow.lean`, `Inline.lean`, `Layout.lean` or `Examples.lean` changes the recorded closure hashes of the results that depend on it, and step (4) of the script reports which ones.
