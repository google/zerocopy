import ToyInline.Semantics

/-!
# The call-site inliner (a parameterised transformation)

`inline p f b cfg` splices the callee of the call terminating block `b` of function `f` into
`f`. The configuration `cfg` fixes the slot renaming and selects, for the purposes of the
counterexamples, deliberately wrong variants of three rewriting rules (unredirected `continue`
edges, `resume` mapped to the normal continuation, and a scope-link rule that ignores the
callsite's `inlinedParent`). The intended rules are `redirectContinue = true`,
`resumeMap = .unwind` and `link = .rustc`.

Layout of the new body of `f` (as in the rustc MIR inliner): the old blocks, with block `b`
now ending in the argument-binding prologue and a `goto` to the callee's entry; then, if the
call had a target, one new return block; then the callee's blocks, shifted. The callee's
scopes are appended after `f`'s scopes and linked by the scope-link rule.
-/

namespace Toy.Inline

/-- Where the callee's return place goes: a fresh temporary `t` (moved into the destination by
the return block) or the call's destination itself. -/
inductive RetMode
  | temp (t : Local)
  | dest
  deriving DecidableEq, Repr

/-- Scope-link rule for the callee's outermost scope. `rustc`: `inlinedParent` is the callsite
scope if that scope carries `inlined`, else the callsite scope's own `inlinedParent`.
`ignoreParent`: the callsite scope if it carries `inlined`, else none. -/
inductive LinkRule
  | rustc
  | ignoreParent
  deriving DecidableEq, Repr

/-- How the callee's `resume` is rewritten: by the call's unwind action (`unwind`, intended),
or as a jump to the normal continuation (`normal`, wrong). -/
inductive ResumeMap
  | unwind
  | normal
  deriving DecidableEq, Repr

/-- Inliner configuration. `slot i` is the host local for callee local `i ≥ 1`. -/
structure InlineCfg where
  slot : Nat → Local
  ret : RetMode
  redirectContinue : Bool
  resumeMap : ResumeMap
  link : LinkRule

/-- The local renaming `ρ` of one inlining step: callee local `0` goes to the temporary or to the
destination `dest`; callee local `i ≥ 1` goes to `slot i`. -/
def InlineCfg.rename (cfg : InlineCfg) (dest : Local) (i : Nat) : Local :=
  if i = 0 then (match cfg.ret with | .temp t => t | .dest => dest) else cfg.slot i

/-- The canonical configuration for a host with `hostN` declared locals: callee local `i`
(including the return place, via the temporary `hostN`) goes to `hostN + i`. -/
def InlineCfg.canonical (hostN : Nat) : InlineCfg where
  slot i := hostN + i
  ret := .temp hostN
  redirectContinue := true
  resumeMap := .unwind
  link := .rustc

/-- The same configuration with the callee's return place mapped to the call's destination. -/
def InlineCfg.withDest (cfg : InlineCfg) : InlineCfg := { cfg with ret := .dest }

def Operand.rename (ρ : Nat → Local) : Operand → Operand
  | .const n => .const n
  | .var x => .var (ρ x)

def Rvalue.rename (ρ : Nat → Local) : Rvalue → Rvalue
  | .use o => .use (o.rename ρ)
  | .add a b => .add (a.rename ρ) (b.rename ρ)

/-- Rename locals by `ρ` and shift scopes by `ns`. -/
def Stmt.rename (ρ : Nat → Local) (ns : Nat) : Stmt → Stmt
  | .assign x rv => .assign (ρ x) (rv.rename ρ)
  | .emit o => .emit (o.rename ρ)
  | .needCap c => .needCap c
  | .loc sp sc => .loc sp (sc + ns)

/-- Everything the splice of one callee body needs to know. -/
structure SpliceCtx where
  ρ : Nat → Local
  base : Nat
  ns : Nat
  retBlk : Option BlockId
  callUnwind : Unwind
  redirectContinue : Bool
  resumeMap : ResumeMap

/-- Unwind actions inside the callee: cleanup targets are shifted; `continue` becomes the call's
own unwind action (if redirected); `terminate` is kept. -/
def SpliceCtx.mapUnwind (c : SpliceCtx) : Unwind → Unwind
  | .cleanup b => .cleanup (b + c.base)
  | .continue => if c.redirectContinue then c.callUnwind else .continue
  | .terminate => .terminate

/-- Terminator rewriting: `ret ↦ goto returnBlock` (or `unreachable` if the call had no target);
`resume ↦ goto b` for `cleanup b`, `resume` for `continue`, `abort` for `terminate`. -/
def SpliceCtx.term (c : SpliceCtx) : Term → Term
  | .goto b => .goto (b + c.base)
  | .branch o z nz => .branch (o.rename c.ρ) (z + c.base) (nz + c.base)
  | .call ci => .call { ci with
      args := ci.args.map (Operand.rename c.ρ),
      dest := c.ρ ci.dest,
      target := ci.target.map (· + c.base),
      unwind := c.mapUnwind ci.unwind,
      scope := ci.scope + c.ns }
  | .ret => match c.retBlk with
    | some r => .goto r
    | none => .unreachable
  | .resume => match c.resumeMap with
    | .unwind => match c.callUnwind with
      | .cleanup b => .goto b
      | .continue => .resume
      | .terminate => .abort
    | .normal => match c.retBlk with
      | some r => .goto r
      | none => .unreachable
  | .panic u => .panic (c.mapUnwind u)
  | .unreachable => .unreachable
  | .abort => .abort

def SpliceCtx.block (c : SpliceCtx) (B : Block) : Block where
  stmts := B.stmts.map (Stmt.rename c.ρ c.ns)
  term := c.term B.term
  isCleanup := B.isCleanup

/-- Argument `i ≥ 1` of the call (or `0` if missing). -/
def argOr (args : List Operand) (i : Nat) : Operand :=
  (nth? args (i - 1)).getD (.const 0)

/-- The argument-binding prologue: assign callee local `i` (for `1 ≤ i < n`) from argument `i`
(or `0`), then zero the callee's return place. Arguments are read before the return place is
written. -/
def prologue (ρ : Nat → Local) (args : List Operand) (n : Nat) : List Stmt :=
  (List.range n).tail.map (fun i => .assign (ρ i) (.use (argOr args i))) ++
    (if n = 0 then [] else [.assign (ρ 0) (.use (.const 0))])

/-- Statements of the return block: move the temporary into the destination (temp mode). -/
def retStmts (cfg : InlineCfg) (ci : CallInfo) : List Stmt :=
  match cfg.ret with
  | .temp t => [.assign ci.dest (.use (.var t))]
  | .dest => []

/-- `1 + max_{i < n} ρ i` (or `0`). -/
def maxSucc (ρ : Nat → Local) (n : Nat) : Nat :=
  (List.range n).foldl (fun m i => max m (ρ i + 1)) 0

/-- `t + 1` for a return temporary `t` (or `0` in destination mode): the return block reads the
temporary even when the callee declares no locals. -/
def retTempSucc (cfg : InlineCfg) : Nat :=
  match cfg.ret with
  | .temp t => t + 1
  | .dest => 0

def mapIdxFrom {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | i, a :: as => f i a :: mapIdxFrom f (i + 1) as

/-- Scope linking for callee scope `j` (`ns` = number of host scopes; `cs` = the callsite scope's
data, at index `csScope`). The outermost callee scope gets `inlined := (callee, span)` and an
`inlinedParent` given by the link rule; an inner scope without `inlinedParent` gets the
(shifted) outermost callee scope; other links are shifted. -/
def linkScope (link : LinkRule) (csScope : ScopeId) (cs : Option Scope) (callee : FnId)
    (span : Span) (ns : Nat) (j : Nat) (sc : Scope) : Scope :=
  if j = 0 then
    { inlined := some (callee, span),
      inlinedParent :=
        match cs with
        | some c =>
          if c.inlined.isSome then some csScope
          else (match link with
                | .rustc => c.inlinedParent
                | .ignoreParent => none)
        | none => none }
  else
    { inlined := sc.inlined,
      inlinedParent := match sc.inlinedParent with
        | none => some ns
        | some t => some (t + ns) }

/-- The linked, shifted callee scopes appended to the host's scope table. -/
def linkScopes (link : LinkRule) (F : Fn) (ci : CallInfo) (G : Fn) : List Scope :=
  mapIdxFrom (linkScope link ci.scope (nth? F.scopes ci.scope) ci.callee ci.span
    F.scopes.length) 0 G.scopes

/-- The new body of the host `F` after inlining callee `G` at the call `ci` ending block `b`
(whose old contents are `B`). The declared-local count covers the host's locals, the images of
the callee's locals and the return temporary. -/
def inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn) (cfg : InlineCfg) :
    Fn :=
  let nb := F.blocks.length
  let ρ := cfg.rename ci.dest
  let base := nb + (match ci.target with | some _ => 1 | none => 0)
  let ctx : SpliceCtx :=
    { ρ := ρ, base := base, ns := F.scopes.length, retBlk := ci.target.map (fun _ => nb),
      callUnwind := ci.unwind, redirectContinue := cfg.redirectContinue,
      resumeMap := cfg.resumeMap }
  let callBlk : Block :=
    { stmts := B.stmts ++ prologue ρ ci.args G.nlocals, term := .goto base,
      isCleanup := B.isCleanup }
  let rb : List Block := match ci.target with
    | some t => [{ stmts := retStmts cfg ci, term := .goto t,
                   isCleanup := ((nth? F.blocks t).map Block.isCleanup).getD false }]
    | none => []
  { nlocals := max (max F.nlocals (maxSucc ρ G.nlocals)) (retTempSucc cfg),
    caps := F.caps,
    trackCaller := F.trackCaller,
    blocks := F.blocks.set b callBlk ++ rb ++ G.blocks.map ctx.block,
    scopes := F.scopes ++ linkScopes cfg.link F ci G }

/-- Inline the call terminating block `b` of function `f`. If there is no such call (or the
callee does not exist) the program is returned unchanged. -/
def inline (p : Program) (f b : Nat) (cfg : InlineCfg) : Program :=
  match nth? p.fns f with
  | none => p
  | some F =>
    match nth? F.blocks b with
    | none => p
    | some B =>
      match B.term with
      | .call ci =>
        match nth? p.fns ci.callee with
        | none => p
        | some G => { p with fns := p.fns.set f (inlineFn F b B ci G cfg) }
      | _ => p

/-- The number of declared locals of function `f` (or `0`). -/
def hostNLocals (p : Program) (f : FnId) : Nat :=
  match nth? p.fns f with
  | some F => F.nlocals
  | none => 0

/-- Inline with the canonical configuration for the current host. -/
def inlineCanon (p : Program) (f b : Nat) : Program :=
  inline p f b (InlineCfg.canonical (hostNLocals p f))

end Toy.Inline
