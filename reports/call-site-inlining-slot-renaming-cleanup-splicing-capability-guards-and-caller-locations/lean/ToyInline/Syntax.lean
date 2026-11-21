/-!
# Syntax of the toy MIR-like language

A deliberately small control-flow-graph language, modelled on the shape of Rust MIR:
functions with numbered locals (local `0` is the return place, locals `1..k` receive the
arguments), basic blocks marked normal or cleanup, calls carrying an unwind action, a
source-scope table with `inlined` / `inlinedParent` links, and per-function capability
lists and a `trackCaller` flag.

This is a toy model. It is meant to capture the bookkeeping a call-site inliner performs;
it is not a mirror of any compiler's data structures.
-/

namespace Toy.Inline

abbrev Local := Nat
abbrev BlockId := Nat
abbrev FnId := Nat
abbrev Cap := Nat
abbrev Span := Nat
abbrev ScopeId := Nat

/-- A capability list (standing for the set of enabled target features of a function).
Membership is list membership; equality of two capability lists is equality of the lists
(order and multiplicity matter), not equality as sets. -/
abbrev CapSet := List Cap

/-- `nth? l i` is the `i`-th element of `l`, if any (structural, so it reduces in the kernel). -/
def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n

/-- Operands: a constant or the current value of a local. -/
inductive Operand
  | const (n : Nat)
  | var (x : Local)
  deriving DecidableEq, Repr

/-- Right-hand sides of assignments. -/
inductive Rvalue
  | use (o : Operand)
  | add (a b : Operand)
  deriving DecidableEq, Repr

/-- Statements.
* `assign x rv` writes local `x`;
* `emit o` produces the observable event `out v` (drop events are `emit`s in cleanup blocks);
* `needCap c` is legal only if the enclosing function holds capability `c`;
* `loc sp sc` produces the observable event `loc v`, where `v` is the caller-location value
  at span `sp` in source scope `sc`. -/
inductive Stmt
  | assign (x : Local) (rv : Rvalue)
  | emit (o : Operand)
  | needCap (c : Cap)
  | loc (sp : Span) (sc : ScopeId)
  deriving DecidableEq, Repr

/-- Unwind actions of calls and panics: continue in a cleanup block of this function,
continue unwinding into the caller, or abort. -/
inductive Unwind
  | cleanup (b : BlockId)
  | «continue»
  | terminate
  deriving DecidableEq, Repr

/-- The data of a call terminator. `span` and `scope` are the call's source information;
`abiSensitive` marks a call whose argument passing depends on the surrounding function's
capabilities. -/
structure CallInfo where
  callee : FnId
  args : List Operand
  dest : Local
  target : Option BlockId
  unwind : Unwind
  span : Span
  scope : ScopeId
  abiSensitive : Bool
  deriving DecidableEq, Repr

/-- Terminators. `branch o z nz` jumps to `z` if `o` evaluates to `0` and to `nz` otherwise;
`panic u` models a call to a panicking function whose unwind action is `u`;
`unreachable` is undefined behaviour; `abort` terminates the program. -/
inductive Term
  | goto (b : BlockId)
  | branch (o : Operand) (ifZero ifNonZero : BlockId)
  | call (ci : CallInfo)
  | ret
  | resume
  | panic (u : Unwind)
  | unreachable
  | abort
  deriving DecidableEq, Repr

/-- A basic block. `isCleanup` is metadata: the semantics does not consult it. -/
structure Block where
  stmts : List Stmt
  term : Term
  isCleanup : Bool
  deriving DecidableEq, Repr

/-- A source scope. `inlined = some (g, sp)` marks the outermost scope of a body of `g` that
was inlined at a call with span `sp`; `inlinedParent` points to the nearest enclosing scope
that carries `inlined` (if any). Scope `0` of a function is its outermost scope. -/
structure Scope where
  inlined : Option (FnId × Span)
  inlinedParent : Option ScopeId
  deriving DecidableEq, Repr

/-- A function: the number of declared locals, its capability list, the `trackCaller` flag,
its blocks (block `0` is the entry) and its scope table. -/
structure Fn where
  nlocals : Nat
  caps : CapSet
  trackCaller : Bool
  blocks : List Block
  scopes : List Scope
  deriving DecidableEq, Repr

/-- A program: a function table and one program-wide map `abi : CapSet → Bool` from capability
lists to a Boolean ABI class. An ABI-sensitive argument is passed correctly iff
`abi (caps host) = abi (caps callee)`; the ABI class does not depend on the call's argument
types or on any implication between capabilities. -/
structure Program where
  fns : List Fn
  abi : CapSet → Bool

/-- The `trackCaller` flag of function `g` in `p` (`false` for a missing function). -/
def Program.tracked (p : Program) (g : FnId) : Bool :=
  match nth? p.fns g with
  | some G => G.trackCaller
  | none => false

/-! ## Locals mentioned by syntax -/

def Operand.locals : Operand → List Local
  | .const _ => []
  | .var x => [x]

def Rvalue.locals : Rvalue → List Local
  | .use o => o.locals
  | .add a b => a.locals ++ b.locals

def Stmt.locals : Stmt → List Local
  | .assign x rv => x :: rv.locals
  | .emit o => o.locals
  | .needCap _ => []
  | .loc _ _ => []

/-- Locals mentioned by a terminator. `ret` reads the return place `0`. -/
def Term.locals : Term → List Local
  | .branch o _ _ => o.locals
  | .call ci => ci.dest :: ci.args.flatMap Operand.locals
  | .ret => [0]
  | _ => []

def Block.locals (B : Block) : List Local :=
  B.stmts.flatMap Stmt.locals ++ B.term.locals

/-! ## Blocks and scopes mentioned by syntax -/

def Unwind.blocks : Unwind → List BlockId
  | .cleanup b => [b]
  | _ => []

/-- Blocks a terminator may transfer control to. -/
def Term.succs : Term → List BlockId
  | .goto b => [b]
  | .branch _ z nz => [z, nz]
  | .call ci => (match ci.target with | some t => [t] | none => []) ++ ci.unwind.blocks
  | .panic u => u.blocks
  | _ => []

def Stmt.scopes : Stmt → List ScopeId
  | .loc _ sc => [sc]
  | _ => []

def Term.scopes : Term → List ScopeId
  | .call ci => [ci.scope]
  | _ => []

def Block.scopeRefs (B : Block) : List ScopeId :=
  B.stmts.flatMap Stmt.scopes ++ B.term.scopes

/-- `true` iff the terminator is an ABI-sensitive call. -/
def Term.abiSensitive : Term → Bool
  | .call ci => ci.abiSensitive
  | _ => false

end Toy.Inline
