/-!
# Unwind capability: classification, call sites, and a toy execution semantics

This file defines the toy model used by every result of the package.

* Crates carry a panic strategy and a panic-in-drop setting (`CrateCfg`).
* Functions carry an ABI, a foreign flag, a never-unwind attribute flag and a drop-glue flag
  (`FnInfo`), plus the crate that defines (or, for a foreign function, declares) them.
* A *precedence function* (`Prec`) decides, from the settings of the crate doing the
  classifying and a function's static facts, whether that function may unwind. It is a
  parameter of every semantic definition so that different rule orders can be compared.
  `stdCanUnwind` is the ordered rule list attribute → abort-and-not-foreign → drop glue under
  panic-in-drop = abort → ABI.
* Function bodies are straight-line lists of statements: a panic point (`raise`) or a call,
  each carrying a landing-pad action (`Action`): none (a plain call), a cleanup pad, a catch
  pad, or a terminate pad.
* `runFn` is a fuel-indexed evaluator returning every finite run (event trace and outcome) of
  a function. Foreign functions are opaque: they may return, and may also unwind when their
  `throws` flag is set. An unwind leaving a function that its own crate classified as
  non-unwinding, or arriving without a stopping pad at a call site whose caller's crate
  classified the callee as non-unwinding, yields the outcome `ub`.

These are statements about a toy model; they neither establish nor refute the corresponding
claims about any real compiler, linker or runtime.
-/

namespace Toy.UnwindCap

/-! ## Settings, ABIs and static facts -/

/-- A crate's panic strategy (`unwind` or `abort`), also used for the per-crate panic-in-drop
setting. -/
inductive Strategy where
  | unwind
  | abort
  deriving DecidableEq, Repr

/-- `true` for the `unwind` strategy. -/
def Strategy.unwinds : Strategy → Bool
  | .unwind => true
  | .abort => false

/-- Function ABIs: the Rust ABI (whose unwinding follows the panic strategy), a non-unwinding
foreign ABI (modelled on `"C"`), and an unwinding foreign ABI (modelled on `"C-unwind"`). -/
inductive Abi where
  | rust
  | c
  | cUnwind
  deriving DecidableEq, Repr

/-- Per-crate compilation settings: the panic strategy and the panic-in-drop setting. -/
structure CrateCfg where
  panic : Strategy
  panicInDrop : Strategy
  deriving DecidableEq, Repr

/-- The static facts about a function that a classification may consult: its ABI, whether it
is a foreign item (declared, not defined, in Rust), whether it carries a never-unwind
attribute, and whether it is drop glue. -/
structure FnInfo where
  abi : Abi
  foreign : Bool
  neverUnwind : Bool
  dropGlue : Bool
  deriving DecidableEq, Repr

/-- A precedence function: from the settings of the crate doing the classifying and a
function's static facts, decide whether that crate treats the function as possibly unwinding
(`true`) or as non-unwinding (`false`). -/
abbrev Prec := CrateCfg → FnInfo → Bool

/-! ## Rules and rule orders -/

/-- The ABI rule: Rust ABIs follow the classifying crate's panic strategy, `c` never unwinds,
`cUnwind` may unwind. -/
def abiCanUnwind (c : CrateCfg) : Abi → Bool
  | .rust => c.panic.unwinds
  | .c => false
  | .cUnwind => true

/-- One precedence rule: `some b` decides `b`; `none` defers to the next rule. -/
abbrev Rule := CrateCfg → FnInfo → Option Bool

/-- A never-unwind attribute decides "non-unwinding". -/
def ruleAttr : Rule := fun _ i => if i.neverUnwind then some false else none

/-- Under the `abort` strategy, a function that is not foreign is non-unwinding. -/
def ruleAbortNonForeign : Rule := fun c i =>
  if !c.panic.unwinds && !i.foreign then some false else none

/-- Under panic-in-drop = `abort`, drop glue is non-unwinding. -/
def ruleDropGlue : Rule := fun c i =>
  if i.dropGlue && !c.panicInDrop.unwinds then some false else none

/-- The ABI rule as a deciding rule. -/
def ruleAbi : Rule := fun c i => some (abiCanUnwind c i.abi)

/-- A mistaken rule: under the `abort` strategy, every function (foreign or not) is
non-unwinding. -/
def ruleAbortAll : Rule := fun c _ => if !c.panic.unwinds then some false else none

/-- Evaluate an ordered rule list: the first deciding rule wins; if none decides, the ABI rule
decides. -/
def evalRules : List Rule → Prec
  | [], c, i => abiCanUnwind c i.abi
  | r :: rs, c, i =>
    match r c i with
    | some b => b
    | none => evalRules rs c i

/-- The standard order: attribute → abort-and-not-foreign → drop glue under panic-in-drop =
abort → ABI. -/
def stdOrder : List Rule := [ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi]

/-- The standard precedence function. -/
def stdCanUnwind : Prec := evalRules stdOrder

/-- An alternative order that consults the ABI before the panic strategy. -/
def abiFirstOrder : List Rule := [ruleAttr, ruleAbi, ruleAbortNonForeign, ruleDropGlue]

/-- The precedence function of `abiFirstOrder`. -/
def abiFirstCanUnwind : Prec := evalRules abiFirstOrder

/-- A mistaken order whose strategy rule omits the foreign check. -/
def abortAllOrder : List Rule := [ruleAttr, ruleAbortAll, ruleDropGlue, ruleAbi]

/-- The precedence function of `abortAllOrder`. -/
def abortAllCanUnwind : Prec := evalRules abortAllOrder

/-! ## Programs -/

/-- The landing-pad action of a call site or panic point: `none` is a plain call (no landing
pad); `cleanup ds` drops the listed live locals and resumes unwinding; `catchPad` stops the unwind
and continues with the next statement (modelled on `catch_unwind`); `terminate` aborts. -/
inductive Action where
  | none
  | cleanup (locals : List Nat)
  | catchPad
  | terminate
  deriving DecidableEq, Repr

/-- `true` for the actions that stop an unwind (`catchPad`, `terminate`). -/
def Action.Stops : Action → Bool
  | .catchPad => true
  | .terminate => true
  | _ => false

/-- `true` for actions that impose an obligation on the frame: a cleanup pad with at least one
local to drop, a catch pad, or a terminate pad. -/
def Action.obligation : Action → Bool
  | .none => false
  | .cleanup ds => !ds.isEmpty
  | .catchPad => true
  | .terminate => true

/-- A statement: a panic point, or a call to function `f`, each with a landing-pad action. -/
inductive Stmt where
  | raise (act : Action)
  | call (f : Nat) (act : Action)
  deriving DecidableEq, Repr

/-- A function: static facts, the index of its defining (or declaring) crate, its body
(ignored for foreign functions), and, for foreign functions, whether the foreign code may
unwind. -/
structure FnDef where
  info : FnInfo
  crate : Nat
  body : List Stmt
  throws : Bool
  deriving DecidableEq, Repr

/-- A linked program: crate settings, functions (indexed by position), and the panic handler
of the final artifact (`abort` makes every panic point abort). -/
structure Prog where
  crates : List CrateCfg
  fns : List FnDef
  handler : Strategy
  deriving DecidableEq, Repr

/-- The function used for indices outside `fns`: a non-foreign Rust function with an empty
body in crate 0. -/
def FnDef.dummy : FnDef :=
  { info := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := false },
    crate := 0, body := [], throws := false }

/-- The settings used for crate indices outside `crates`. -/
def CrateCfg.dflt : CrateCfg := ⟨.unwind, .unwind⟩

/-- Function `f` of `p`. -/
def Prog.fn (p : Prog) (f : Nat) : FnDef := p.fns.getD f FnDef.dummy

/-- Indices at or beyond the end of `fns` denote `FnDef.dummy`. -/
theorem Prog.fn_of_ge (p : Prog) {g : Nat} (h : p.fns.length ≤ g) : p.fn g = FnDef.dummy := by
  simp only [Prog.fn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none h]
  rfl

/-- The settings of the crate of function `f`. -/
def Prog.crateOf (p : Prog) (f : Nat) : CrateCfg := p.crates.getD (p.fn f).crate CrateCfg.dflt

/-- How `f`'s own crate classifies `f` under `cu` (the classification its definition, or
declaration, is compiled with). -/
def Prog.selfMay (p : Prog) (cu : Prec) (f : Nat) : Bool := cu (p.crateOf f) (p.fn f).info

/-- How the crate of caller `g` classifies callee `f` under `cu`. -/
def Prog.viewMay (p : Prog) (cu : Prec) (g f : Nat) : Bool := cu (p.crateOf g) (p.fn f).info

/-! ## Semantics -/

/-- Observable events: a destructor of local `x` of function `g` ran, or function `g` caught
an unwind. -/
inductive Event where
  | drop (fn x : Nat)
  | caught (fn : Nat)
  deriving DecidableEq, Repr

/-- Outcomes of a run: normal return, an unwind leaving the function, abort, or undefined
behaviour. -/
inductive Outcome where
  | ret
  | unwind
  | abort
  | ub
  deriving DecidableEq, Repr

/-- A finite run: its event trace and its outcome. -/
abbrev Run := List Event × Outcome

/-- Prefix an event trace to every run of a list. -/
def prependRuns (t : List Event) (rs : List Run) : List Run := rs.map fun r => (t ++ r.1, r.2)

/-- The fate of an unwind arriving at a statement of function `g` with action `act`. `assumed`
records that `g`'s crate classified the callee as non-unwinding (always `false` for a panic
point). `k` lists the runs of the rest of the body. -/
def onUnwind (g : Nat) (assumed : Bool) (act : Action) (k : List Run) : List Run :=
  match act with
  | .terminate => [([], .abort)]
  | .catchPad => prependRuns [Event.caught g] k
  | .none => if assumed then [([], .ub)] else [([], .unwind)]
  | .cleanup ds => if assumed then [([], .ub)] else [(ds.map (Event.drop g), .unwind)]

/-- Runs of a statement list of function `g`, given the runs of each callee. -/
def execBody (cu : Prec) (p : Prog) (callee : Nat → List Run) (g : Nat) : List Stmt → List Run
  | [] => [([], .ret)]
  | .raise act :: rest =>
    match p.handler with
    | .abort => [([], .abort)]
    | .unwind => onUnwind g false act (execBody cu p callee g rest)
  | .call f act :: rest =>
    (callee f).flatMap fun r =>
      match r.2 with
      | .ret => prependRuns r.1 (execBody cu p callee g rest)
      | .unwind => prependRuns r.1 (onUnwind g (!p.viewMay cu g f) act (execBody cu p callee g rest))
      | .abort => [(r.1, .abort)]
      | .ub => [(r.1, .ub)]

/-- The function boundary: an unwind leaving `f` is undefined behaviour when `f`'s own crate
classified `f` as non-unwinding. -/
def boundary (cu : Prec) (p : Prog) (f : Nat) (r : Run) : Run :=
  match r.2 with
  | .unwind => if p.selfMay cu f then r else (r.1, .ub)
  | _ => r

/-- All runs of function `f` with call depth below `n`. A foreign function may return, and may
also unwind when its `throws` flag is set. -/
def runFn (cu : Prec) (p : Prog) : Nat → Nat → List Run
  | 0, _ => []
  | n + 1, f =>
    if (p.fn f).info.foreign then
      ([], .ret) :: (if (p.fn f).throws then [boundary cu p f ([], .unwind)] else [])
    else (execBody cu p (runFn cu p n) f (p.fn f).body).map (boundary cu p f)

/-- `Exec cu p f t o`: function `f` of `p` has a finite run with trace `t` and outcome `o`
under precedence function `cu`. Diverging executions are not represented. -/
def Exec (cu : Prec) (p : Prog) (f : Nat) (t : List Event) (o : Outcome) : Prop :=
  ∃ n, (t, o) ∈ runFn cu p n f

/-! ## Hypotheses of the soundness results -/

/-- Enforcement at function `g` (the toy codegen's obligation): if `g` is non-foreign and its
own crate classifies it as non-unwinding, then (when the panic handler is `unwind`) every panic
point of `g` carries a stopping pad, and every call of `g` to a callee that `g`'s crate classifies
as possibly unwinding carries a stopping pad. Under the `abort` handler a panic point aborts
without unwinding, so its action is not constrained. -/
def EnforcedAt (cu : Prec) (p : Prog) (g : Nat) : Prop :=
  (p.fn g).info.foreign = false → p.selfMay cu g = false →
    (p.handler = .unwind → ∀ act, Stmt.raise act ∈ (p.fn g).body → act.Stops = true) ∧
    (∀ f act, Stmt.call f act ∈ (p.fn g).body → p.viewMay cu g f = true → act.Stops = true)

/-- Enforcement: `EnforcedAt` holds at every function index, reachable or not. -/
def Enforced (cu : Prec) (p : Prog) : Prop := ∀ g, EnforcedAt cu p g

/-- Every foreign function that may unwind is classified as possibly unwinding by its
declaring crate. -/
def ForeignCovered (cu : Prec) (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).throws = true → p.selfMay cu f = true

/-- Call-site agreement at function `g`: at every call site of `g` without a stopping pad, if `g`
is non-foreign and `g`'s crate classifies the callee as non-unwinding, so does the callee's own
crate. -/
def SiteAgreementAt (cu : Prec) (p : Prog) (g : Nat) : Prop :=
  ∀ f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
    act.Stops = false → p.viewMay cu g f = false → p.selfMay cu f = false

/-- Call-site agreement: `SiteAgreementAt` holds at every function index, reachable or not. -/
def SiteAgreement (cu : Prec) (p : Prog) : Prop := ∀ g, SiteAgreementAt cu p g

/-- Foreign code honours its declaration: a foreign function that may unwind is declared with
the `cUnwind` ABI and without the never-unwind attribute. -/
def ForeignHonest (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).throws = true →
    (p.fn f).info.abi = .cUnwind ∧ (p.fn f).info.neverUnwind = false

/-- Well-formedness: no foreign function is drop glue. -/
def ForeignNotGlue (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).info.dropGlue = false

/-- A precedence function is sound for foreign code when, in every program satisfying
`ForeignHonest` and `ForeignNotGlue`, it classifies every foreign function that may unwind as
possibly unwinding. -/
def PrecForeignSound (cu : Prec) : Prop :=
  ∀ p, ForeignHonest p → ForeignNotGlue p → ForeignCovered cu p

/-! ## Linking restriction (modelled on two of the three clauses of the Reference's
"potentially unwinding" rule) -/

/-- The artifact is potentially unwinding: it uses the `unwind` panic handler, or a non-foreign
function of an `unwind`-strategy crate calls a function with the `cUnwind` ABI. -/
def PotentiallyUnwinding (p : Prog) : Prop :=
  p.handler = .unwind ∨
  ∃ g f act, (p.fn g).info.foreign = false ∧ (p.crateOf g).panic = .unwind ∧
    Stmt.call f act ∈ (p.fn g).body ∧ (p.fn f).info.abi = .cUnwind

/-- The toy linking restriction: if the artifact is potentially unwinding, every crate of the
program uses the `unwind` strategy. -/
def LinkOK (p : Prog) : Prop :=
  PotentiallyUnwinding p → ∀ c ∈ p.crates, c.panic = .unwind

/-- Drop-glue agreement: at every call site without a stopping pad that calls drop glue from a
crate with panic-in-drop = `abort`, the drop-glue instance called was compiled in a crate with
panic-in-drop = `abort`. -/
def GlueAgreement (p : Prog) : Prop :=
  ∀ g f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
    (p.fn f).info.dropGlue = true → act.Stops = false →
    (p.crateOf g).panicInDrop = .abort → (p.crateOf f).panicInDrop = .abort

/-! ## Toy codegen: terminate-pad insertion -/

/-- The toy codegen for one statement of a function classified as non-unwinding. A panic point
whose action is not a stopping pad has its action replaced by `terminate` when the panic handler
is `unwind` (under the `abort` handler it is left unchanged). A call whose action is not a stopping
pad has its action replaced by `terminate` when the caller's crate classifies the callee as
possibly unwinding. A replaced `cleanup ds` action loses its drop list. -/
def padStmt (cu : Prec) (p : Prog) (g : Nat) : Stmt → Stmt
  | .raise act => .raise (if p.handler.unwinds && !act.Stops then .terminate else act)
  | .call f act => .call f (if p.viewMay cu g f && !act.Stops then .terminate else act)

/-- The toy codegen for one function: functions that are non-foreign and classified as
non-unwinding by their own crate get `padStmt` applied to every statement. -/
def padFn (cu : Prec) (p : Prog) (g : Nat) (d : FnDef) : FnDef :=
  if !d.info.foreign && !cu (p.crates.getD d.crate CrateCfg.dflt) d.info then
    { d with body := d.body.map (padStmt cu p g) }
  else d

/-- The toy codegen pass: insert terminate pads in every function classified as
non-unwinding. -/
def insertPads (cu : Prec) (p : Prog) : Prog :=
  { p with fns := p.fns.mapIdx (padFn cu p) }

/-! ## Mixed backends -/

/-- A backend's landing-pad capability: `full` emits cleanup, catch and terminate pads; `none`
emits no landing pads, so every call site and panic point of a function it compiles behaves as
one without a landing pad. A `pads = none` function is still assumed to be unwindable: an
unwind arriving at one of its call sites without a landing pad propagates to its caller (as for
code with frame-unwind tables but no landing pads); code that cannot be unwound through at all
is not modelled. -/
inductive Pads where
  | full
  | none
  deriving DecidableEq, Repr

/-- The statement a `pads = none` backend emits: the same statement without its landing pad. -/
def Stmt.unpadded : Stmt → Stmt
  | .raise _ => .raise .none
  | .call f _ => .call f .none

/-- The program as compiled when function `g` is compiled by a backend with capability
`pads g`: functions compiled with `pads = none` lose every landing pad. -/
def Prog.withPads (p : Prog) (pads : Nat → Pads) : Prog :=
  { p with fns := p.fns.mapIdx fun g d =>
      match pads g with
      | .full => d
      | .none => { d with body := d.body.map Stmt.unpadded } }

end Toy.UnwindCap
