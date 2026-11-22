import ToyContracts.Instr

/-!
# Cross-crate flag scoping and compile-time evaluation (toy parameters)

The crate that holds a check, where the flag test of a callee-side check is resolved, and whether
compile-time evaluation runs checks are parameters of the toy; nothing here asserts which option
any real compiler implements.

A cross-crate call is modelled as a pipeline of three per-crate steps, each of which reads the flag
of its own crate and no other: the defining crate compiles the callee (`compileInDefCrate`), the
instantiating crate instantiates a generic body (`instantiateIn`), and the calling crate performs
the call (`callInCallerCrate`). Which crate's flag decides checking (`governingCrate`) is not used
by these definitions; `callRun_eq_ite_governingFlag_of_lowered` derives it.
-/

namespace Toy.Contracts

/-- Where the checks of a call are placed: in the callee's body (compiled into it by the defining
crate, or, for a generic callee whose flag test is resolved at instantiation, by the crate that
instantiates it), or around the call in the caller. -/
inductive Site where
  | calleeSide
  | callerSide
  deriving DecidableEq, Repr

/-- Where the flag test of a callee-side check is resolved: with the definition, or where a generic
callee body is instantiated. -/
inductive Resolution where
  | atDefinition
  | atInstantiation
  deriving DecidableEq, Repr

/-- A cross-crate call: the calling crate, the defining crate, the crate in which a generic callee
body is instantiated (not used for a non-generic callee), and whether the callee is generic. Crates
are named by natural numbers. -/
structure CallSite where
  callerCrate : Nat
  defCrate : Nat
  instCrate : Nat
  generic : Bool
  deriving DecidableEq, Repr

/-- The crate whose source holds the check: the defining crate for callee-side placement, the
calling crate for caller-side placement. -/
def holder : Site → CallSite → Nat
  | .calleeSide, cs => cs.defCrate
  | .callerSide, cs => cs.callerCrate

/-- The crate whose flag decides whether the call's checks run, as a function of placement,
resolution and call site. -/
def governingCrate : Site → Resolution → CallSite → Nat
  | .callerSide, _, cs => cs.callerCrate
  | .calleeSide, .atDefinition, cs => cs.defCrate
  | .calleeSide, .atInstantiation, cs => if cs.generic then cs.instCrate else cs.defCrate

/-- What the defining crate exports for a callee: a compiled body, or a generic body that the
instantiating crate compiles. -/
inductive Exported where
  | compiled (body : Fn)
  | template (body : Fn)
  deriving DecidableEq, Repr

/-- Compilation of callee `g` (as written) in the defining crate, which reads its own flag
`defFlag`. Under callee-side placement it compiles the all-exits instrumentation of `g` if its flag
is on and `g` itself otherwise, except that a generic callee whose flag test is resolved at
instantiation is exported uncompiled. Under caller-side placement the callee carries no checks. -/
def compileInDefCrate (defFlag : Bool) (s : Site) (res : Resolution) (generic : Bool) (g : Fn) :
    Exported :=
  match s, res, generic with
  | .calleeSide, .atInstantiation, true => .template g
  | .calleeSide, _, _ => .compiled (if defFlag then instr .allExits g else g)
  | .callerSide, _, _ => .compiled g

/-- Instantiation in the instantiating crate, which reads its own flag `instFlag`: a compiled body
is used as is; a generic body is compiled with the all-exits instrumentation if the flag is on. -/
def instantiateIn (instFlag : Bool) : Exported → Fn
  | .compiled body => body
  | .template body => if instFlag then instr .allExits body else body

/-- The call in the calling crate, which reads its own flag `callerFlag`: under caller-side
placement with the flag on, `Req` is checked before the call and `Ens` on the value the call
returns (`instrObs`); otherwise the callee body runs unwrapped. -/
def callInCallerCrate (callerFlag : Bool) (s : Site) (c : Contract) (body : Fn) (x n : Nat) : Obs :=
  match s with
  | .calleeSide => run c body x n
  | .callerSide => if callerFlag then instrObs c x (run c body x n) else run c body x n

/-- Observation of a cross-crate call of callee `g` (as written) under per-crate flags `fl`, at
fuel `n`: the three per-crate steps, each given the flag of its own crate. -/
def callRun (fl : Nat → Bool) (s : Site) (res : Resolution) (cs : CallSite) (c : Contract)
    (g : Fn) (x n : Nat) : Obs :=
  callInCallerCrate (fl cs.callerCrate) s c
    (instantiateIn (fl cs.instCrate) (compileInDefCrate (fl cs.defCrate) s res cs.generic g)) x n

/-- A contract violation at `x`: `Req x` fails, or `Req x` holds and `g` returns (for some fuel) a
value violating `Ens`. -/
def ViolationAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  c.req x = false ∨ (c.req x = true ∧ ∃ tr r, Halts c g x ⟨tr, .ret r⟩ ∧ c.ens x r = false)

/-- The call reports a failed check on `x` for some fuel (a `checkFail` outcome, whether it comes
from an inserted check or from a contract statement already in `g`). -/
def Detects (fl : Nat → Bool) (s : Site) (res : Resolution) (cs : CallSite) (c : Contract)
    (g : Fn) (x : Nat) : Prop :=
  ∃ n tr k, callRun fl s res cs c g x n = ⟨tr, .checkFail k⟩

/-- Compile-time evaluation mode: skip contract statements (run the erasure) or evaluate them. -/
inductive CtfeMode where
  | skipChecks
  | evalChecks
  deriving DecidableEq, Repr

/-- Compile-time evaluation of a (possibly instrumented) function `p`. -/
def ctfeRun : CtfeMode → Contract → Fn → Nat → Nat → Obs
  | .skipChecks, c, p, x, n => run c (erase p) x n
  | .evalChecks, c, p, x, n => run c p x n

/-- Compile-time evaluation in mode `m` of the instrumentation `instr p g` (placement `p`) on `x`
produces the constant `r` (a normal return, for some fuel; events are ignored). -/
def CtfeConst (p : Placement) (m : CtfeMode) (c : Contract) (g : Fn) (x r : Nat) : Prop :=
  ∃ n tr, ctfeRun m c (instr p g) x n = ⟨tr, .ret r⟩

/-- The runtime-checked call with placement `p` (the instrumentation `instr p g`) on `x` returns
`r` for some fuel. -/
def RuntimeValue (p : Placement) (c : Contract) (g : Fn) (x r : Nat) : Prop :=
  ∃ tr, Halts c (instr p g) x ⟨tr, .ret r⟩

end Toy.Contracts
