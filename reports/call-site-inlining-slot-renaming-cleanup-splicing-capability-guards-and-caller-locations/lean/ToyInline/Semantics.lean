import ToyInline.Syntax

/-!
# Reference semantics: a frame stack with per-frame cleanup and unwinding

One deterministic small-step function `step` on a stack of frames, observed through a
fuel-indexed runner `runWith`. The same semantics runs original and inlined programs; a
program obtained by inlining is simply another program whose bodies contain spliced blocks
and inlined scopes.

Caller locations (`#[track_caller]`-style implicit arguments): a frame of a `trackCaller`
function carries `il = some l`, its implicit location. A call to a `trackCaller` callee passes
the caller-location value of the call site (computed by the scope walk at the call's scope and
span). For a function with no inlined scopes this is the caller's own implicit location if
the caller is `trackCaller`, and the call's span otherwise.
-/

namespace Toy.Inline

/-! ## The scope walk -/

/-- Result of walking the `inlinedParent` chain: `stop sp` (stopped inside an inlined callee
that is not `trackCaller`, answer `sp`) or `top sp` (reached the end of the chain with current
span `sp`). -/
inductive WalkRes
  | stop (sp : Span)
  | top (sp : Span)
  deriving DecidableEq, Repr

/-- The scope walk, with explicit fuel. At a scope with `inlined = some (g, csp)`: if `g` is not
tracked, stop with the current span; otherwise replace the span by `csp`. Then follow
`inlinedParent`; at the end of the chain return `top`. Missing scopes end the walk. -/
def walk (tr : FnId → Bool) (scopes : List Scope) : Nat → ScopeId → Span → WalkRes
  | 0, _, sp => .top sp
  | fuel + 1, s, sp =>
    match nth? scopes s with
    | none => .top sp
    | some sc =>
      match sc.inlined with
      | some (g, csp) =>
        if tr g then
          (match sc.inlinedParent with
           | none => .top csp
           | some t => walk tr scopes fuel t csp)
        else .stop sp
      | none =>
        match sc.inlinedParent with
        | none => .top sp
        | some t => walk tr scopes fuel t sp

/-- The caller-location value of a `loc sp` (or of a call with span `sp`) in scope `s` of a body
with scope table `scopes`, in a frame with implicit location `il`: walk the chain with fuel
`scopes.length`; if the walk reaches the top, return `il` if present and the span otherwise. -/
def locValue (tr : FnId → Bool) (scopes : List Scope) (s : ScopeId) (sp : Span)
    (il : Option Span) : Span :=
  match walk tr scopes scopes.length s sp with
  | .stop sp' => sp'
  | .top sp' => il.getD sp'

/-! ## Alternative (naive) caller-location policies, used only in counterexamples -/

/-- The first scope on the `inlinedParent` chain from `s` (including `s`) that carries
`inlined`, if any. -/
def firstInlined (scopes : List Scope) : Nat → ScopeId → Option (FnId × Span)
  | 0, _ => none
  | fuel + 1, s =>
    match nth? scopes s with
    | none => none
    | some sc =>
      match sc.inlined with
      | some x => some x
      | none =>
        match sc.inlinedParent with
        | none => none
        | some t => firstInlined scopes fuel t

/-- The callsite span of the last (outermost) inlined scope on the chain from `s`, if any. -/
def lastInlinedSpan (scopes : List Scope) : Nat → ScopeId → Option Span → Option Span
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
    match nth? scopes s with
    | none => acc
    | some sc =>
      let acc' := match sc.inlined with
        | some (_, csp) => some csp
        | none => acc
      match sc.inlinedParent with
      | none => acc'
      | some t => lastInlinedSpan scopes fuel t acc'

/-- Caller-location policies. `walk` is the scope walk above. `innermost` answers the callsite
span of the innermost inlined scope (if its callee is tracked). `outermost` answers the
callsite span of the outermost inlined scope (if the innermost inlined callee is tracked).
All three agree on bodies without inlined scopes. -/
inductive LocPolicy
  | walk
  | innermost
  | outermost
  deriving DecidableEq, Repr

def locValueWith (pol : LocPolicy) (tr : FnId → Bool) (scopes : List Scope) (s : ScopeId)
    (sp : Span) (il : Option Span) : Span :=
  match pol with
  | .walk => locValue tr scopes s sp il
  | .innermost =>
    match firstInlined scopes scopes.length s with
    | none => il.getD sp
    | some (g, csp) => if tr g then csp else sp
  | .outermost =>
    match firstInlined scopes scopes.length s with
    | none => il.getD sp
    | some (g, csp) =>
      if tr g then (lastInlinedSpan scopes scopes.length s none).getD csp else sp

/-! ## Machine states -/

/-- Observable events. -/
inductive Event
  | out (v : Nat)
  | loc (sp : Span)
  deriving DecidableEq, Repr

/-- Final outcomes: normal return of the entry function with its return value, a panic that
escaped the entry function, abort, undefined behaviour, and executing `needCap c` in a
function that lacks `c`. -/
inductive Outcome
  | returned (v : Nat)
  | unwound
  | aborted
  | ub
  | capFault
  deriving DecidableEq, Repr

/-- A frame: function, current block, index of the next statement (`pc = stmts.length` means
"at the terminator"), the store of locals, and the implicit caller location. -/
structure Frame where
  fn : FnId
  block : BlockId
  pc : Nat
  store : Local → Nat
  il : Option Span

inductive Config
  | running (stack : List Frame)
  | halted (o : Outcome)

def evalOp (st : Local → Nat) : Operand → Nat
  | .const n => n
  | .var x => st x

def evalRv (st : Local → Nat) : Rvalue → Nat
  | .use o => evalOp st o
  | .add a b => evalOp st a + evalOp st b

def upd (st : Local → Nat) (x : Local) (v : Nat) : Local → Nat :=
  fun y => if y = x then v else st y

/-- Initial store of a callee frame: return place `0`, local `i + 1` holds argument `i`, all
other locals `0`. -/
def bindArgs (vals : List Nat) : Local → Nat
  | 0 => 0
  | i + 1 => (nth? vals i).getD 0

/-- The terminator a frame is currently at, if the frame is at its block's end. -/
def curTerm (p : Program) (fr : Frame) : Option Term :=
  match nth? p.fns fr.fn with
  | none => none
  | some F =>
    match nth? F.blocks fr.block with
    | none => none
    | some B => if fr.pc = B.stmts.length then some B.term else none

/-- Unwinding out of a callee into the stack `rest`: the top frame of `rest` must be at a call;
its unwind action decides. -/
def unwindInto (p : Program) : List Frame → Config
  | [] => .halted .unwound
  | c :: rest =>
    match curTerm p c with
    | some (.call ci) =>
      match ci.unwind with
      | .cleanup b => .running ({ c with block := b, pc := 0 } :: rest)
      | .continue => unwindInto p rest
      | .terminate => .halted .aborted
    | _ => .halted .ub

/-- Starting to unwind in frame `fr` with unwind action `u` (a `panic u`). -/
def startUnwind (p : Program) (fr : Frame) (rest : List Frame) : Unwind → Config
  | .cleanup b => .running ({ fr with block := b, pc := 0 } :: rest)
  | .continue => unwindInto p rest
  | .terminate => .halted .aborted

/-- Returning value `v` into the stack `rest`: the top frame of `rest` must be at a call. -/
def returnInto (p : Program) (v : Nat) : List Frame → Config
  | [] => .halted (.returned v)
  | c :: rest =>
    match curTerm p c with
    | some (.call ci) =>
      match ci.target with
      | some t => .running ({ c with block := t, pc := 0, store := upd c.store ci.dest v } :: rest)
      | none => .halted .ub
    | _ => .halted .ub

/-- One step. Returns the next configuration and the events emitted by the step (at most one).
An ABI-sensitive call from host `F` to callee `G` with `abi F.caps ≠ abi G.caps` garbles every
argument (`v ↦ v + 1`). -/
def step (pol : LocPolicy) (p : Program) : List Frame → Config × List Event
  | [] => (.halted .ub, [])
  | fr :: rest =>
    match nth? p.fns fr.fn with
    | none => (.halted .ub, [])
    | some F =>
    match nth? F.blocks fr.block with
    | none => (.halted .ub, [])
    | some B =>
    match nth? B.stmts fr.pc with
    | some s =>
      let fr' := { fr with pc := fr.pc + 1 }
      match s with
      | .assign x rv =>
        (.running ({ fr' with store := upd fr.store x (evalRv fr.store rv) } :: rest), [])
      | .emit o => (.running (fr' :: rest), [.out (evalOp fr.store o)])
      | .needCap c =>
        if F.caps.contains c then (.running (fr' :: rest), []) else (.halted .capFault, [])
      | .loc sp sc =>
        (.running (fr' :: rest), [.loc (locValueWith pol p.tracked F.scopes sc sp fr.il)])
    | none =>
      match B.term with
      | .goto b => (.running ({ fr with block := b, pc := 0 } :: rest), [])
      | .branch o z nz =>
        (.running ({ fr with block := if evalOp fr.store o = 0 then z else nz, pc := 0 } :: rest), [])
      | .call ci =>
        match nth? p.fns ci.callee with
        | none => (.halted .ub, [])
        | some G =>
          let vals0 := ci.args.map (evalOp fr.store)
          let vals := if ci.abiSensitive && (p.abi F.caps != p.abi G.caps)
            then vals0.map (· + 1) else vals0
          let il' := if G.trackCaller
            then some (locValueWith pol p.tracked F.scopes ci.scope ci.span fr.il) else none
          (.running ({ fn := ci.callee, block := 0, pc := 0, store := bindArgs vals, il := il' }
            :: { fr with pc := B.stmts.length } :: rest), [])
      | .ret => (returnInto p (fr.store 0) rest, [])
      | .resume => (unwindInto p rest, [])
      | .panic u => (startUnwind p fr rest u, [])
      | .unreachable => (.halted .ub, [])
      | .abort => (.halted .aborted, [])

/-- A finite observation: the events emitted so far and the outcome, if the run has halted. -/
structure Obs where
  events : List Event
  outcome : Option Outcome
  deriving DecidableEq, Repr

/-- Run for at most `n` steps under caller-location policy `pol`. -/
def runWith (pol : LocPolicy) (p : Program) : Nat → Config → Obs
  | _, .halted o => ⟨[], some o⟩
  | 0, .running _ => ⟨[], none⟩
  | n + 1, .running s =>
    let r := step pol p s
    let o := runWith pol p n r.1
    ⟨r.2 ++ o.events, o.outcome⟩

/-- An entry: the function to run, its argument values, and the implicit location it receives
if it is `trackCaller`. -/
structure Entry where
  fn : FnId
  args : List Nat
  loc : Span
  deriving DecidableEq, Repr

def init (p : Program) (e : Entry) : Config :=
  match nth? p.fns e.fn with
  | none => .halted .ub
  | some F =>
    .running [{ fn := e.fn, block := 0, pc := 0, store := bindArgs e.args,
                il := if F.trackCaller then some e.loc else none }]

/-- Observation prefix order: the events of `o₁` are a prefix of those of `o₂`, and if `o₁` has
halted then `o₂ = o₁`. -/
def Obs.Prefix (o₁ o₂ : Obs) : Prop :=
  o₁.events <+: o₂.events ∧ (o₁.outcome.isSome → o₂ = o₁)

/-- Behavioural equivalence of `p` and `q` from entry `e` under policy `pol`: every finite
observation of either program is a prefix of some observation of the other. For these
deterministic programs this says the maximal event sequences and outcomes coincide; it
ignores step counts (inlining changes them). -/
def BehEquivAtWith (pol : LocPolicy) (p q : Program) (e : Entry) : Prop :=
  (∀ n, ∃ m, (runWith pol p n (init p e)).Prefix (runWith pol q m (init q e))) ∧
  (∀ m, ∃ n, (runWith pol q m (init q e)).Prefix (runWith pol p n (init p e)))

/-- The reference semantics uses the scope walk. -/
abbrev run (p : Program) (n : Nat) (c : Config) : Obs := runWith .walk p n c

abbrev BehEquivAt (p q : Program) (e : Entry) : Prop := BehEquivAtWith .walk p q e

/-- Behavioural equivalence from every entry (every function, argument list and implicit
location). -/
def BehEquiv (p q : Program) : Prop := ∀ e, BehEquivAt p q e

end Toy.Inline
