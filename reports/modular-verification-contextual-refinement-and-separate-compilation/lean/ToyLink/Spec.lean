import ToyLink.Defs

/-!
# Specifications, assume-guarantee rules, spec refinement, and pass preservation

Defines function specifications (`FnSpec`, `SpecEnv`), whole-program partial and total
correctness (`FnPartialCorrect`, `ProgramPartialCorrect`, `FnTotalCorrect`,
`ProgramTotalCorrect`), interface implementation (`SpecsImplemented`), modular
assume-guarantee weakest-precondition judgements for partial correctness (`wpPartial`,
`ModuleVerifiedPartial`) and measure-indexed total correctness (`wpCallDec`,
`ModuleVerifiedTotal`), specification refinement (`WeakensPre`, `StrengthensPostUnderPre`), the mixed assumption
environment for modules with internal calls (`mixEnv`), and separate-compilation pass
properties (`PreservesVerifiedPartial`, `PreservesDefines`, `PassCtxRefines`).
Contracts relate one integer argument to one integer result; there is no state, no
frame, and no auxiliary (logical) variable.
-/

namespace Toy.Link

/-- A function contract assigning a precondition on the input argument and a
two-state postcondition relating input argument and return value.
Captures a behavioral interface specification for a module boundary. -/
structure FnSpec where
  pre : Int → Prop
  post : Int → Int → Prop

/-- A specification environment mapping every function name to its contract.
Captures a shared module interface specification across linked units. -/
abbrev SpecEnv := Fname → FnSpec

/-- Whole-program partial correctness of `fn` in `P` against `spec`: under `spec.pre x`,
every finite-fuel outcome is either `outOfFuel` or a normal return `val v` satisfying
`spec.post x v` (in particular, `undefinedCall` never occurs).
Captures safety / partial correctness: divergence is accepted, since `outOfFuel` is
always allowed. -/
def FnPartialCorrect (P : Module) (fn : Fname) (spec : FnSpec) : Prop :=
  ∀ fuel x out, spec.pre x → HasBehavior fn P fuel x out →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ spec.post x v

/-- Whole-program partial correctness of every function in `P` against `S`.
Captures whole-program safety against a global specification map. -/
def ProgramPartialCorrect (P : Module) (S : SpecEnv) : Prop :=
  ∀ fn, FnPartialCorrect P fn (S fn)

/-- Whole-program total correctness of `fn` in `P` against `spec`: under `spec.pre x`,
there exists a finite fuel bound `fuel` at which every possible outcome is a normal
return `val v` satisfying `spec.post x v`.
Captures guaranteed termination with uniform finite call-depth bound under bounded choice. -/
def FnTotalCorrect (P : Module) (fn : Fname) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → ∃ fuel, ∀ out, HasBehavior fn P fuel x out →
    ∃ v, out = .val v ∧ spec.post x v

/-- Whole-program total correctness of every function in `P` against `S`.
Captures whole-program termination and postcondition satisfaction. -/
def ProgramTotalCorrect (P : Module) (S : SpecEnv) : Prop :=
  ∀ fn, FnTotalCorrect P fn (S fn)

/-- Interface completeness: every function whose precondition is satisfiable is
defined in `P`. Captures the linker obligation that no reachable specified symbol is missing. -/
def SpecsImplemented (P : Module) (S : SpecEnv) : Prop :=
  ∀ fn x, (S fn).pre x → P.Defines fn

/-- Assume-guarantee weakest precondition for an expression `e` under input `x`,
assuming every callee `fn` satisfies `(A fn).pre` and `(A fn).post`, without any
termination measure. Captures Hoare-style modular partial-correctness verification. -/
def wpPartial (A : SpecEnv) (x : Int) : Expr → (Int → Prop) → Prop
  | .lit n, Q => Q n
  | .var, Q => Q x
  | .add e₁ e₂, Q =>
      wpPartial A x e₁ (fun v₁ => wpPartial A x e₂ (fun v₂ => Q (v₁ + v₂)))
  | .sub e₁ e₂, Q =>
      wpPartial A x e₁ (fun v₁ => wpPartial A x e₂ (fun v₂ => Q (v₁ - v₂)))
  | .mul e₁ e₂, Q =>
      wpPartial A x e₁ (fun v₁ => wpPartial A x e₂ (fun v₂ => Q (v₁ * v₂)))
  | .ifLe e₁ e₂ eThen eElse, Q =>
      wpPartial A x e₁ (fun v₁ =>
        wpPartial A x e₂ (fun v₂ =>
          (v₁ ≤ v₂ → wpPartial A x eThen Q) ∧
          (¬ v₁ ≤ v₂ → wpPartial A x eElse Q)))
  | .choose e₁ e₂, Q =>
      wpPartial A x e₁ Q ∧ wpPartial A x e₂ Q
  | .call fn eArg, Q =>
      wpPartial A x eArg (fun vArg =>
        (A fn).pre vArg ∧ ∀ vRes, (A fn).post vArg vRes → Q vRes)

/-- Modular partial-correctness verification of a single body against `spec` under
callee assumptions `A`. Captures per-function Hoare-logic obligation for partial correctness. -/
def BodyVerifiedPartial (A : SpecEnv) (body : Expr) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → wpPartial A x body (spec.post x)

/-- Modular partial-correctness verification of every function defined in `M` against
guarantee `G` under callee assumptions `A`. Captures open assume-guarantee module verification. -/
def ModuleVerifiedPartial (M : Module) (A G : SpecEnv) : Prop :=
  ∀ fn body, M.lookup fn = some body → BodyVerifiedPartial A body (G fn)

/-- Measure-indexed assume-guarantee weakest precondition for total correctness:
every call `fn(vArg)` must strictly decrease the measure `μ fn vArg` relative to
the caller's current measure `cur` under `rel`, in addition to satisfying `(A fn).pre`.
Captures modular termination verification with explicit call-decreasing measures. -/
def wpCallDec {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (A : SpecEnv) (cur : α) (x : Int) : Expr → (Int → Prop) → Prop
  | .lit n, Q => Q n
  | .var, Q => Q x
  | .add e₁ e₂, Q =>
      wpCallDec rel μ A cur x e₁ (fun v₁ =>
        wpCallDec rel μ A cur x e₂ (fun v₂ => Q (v₁ + v₂)))
  | .sub e₁ e₂, Q =>
      wpCallDec rel μ A cur x e₁ (fun v₁ =>
        wpCallDec rel μ A cur x e₂ (fun v₂ => Q (v₁ - v₂)))
  | .mul e₁ e₂, Q =>
      wpCallDec rel μ A cur x e₁ (fun v₁ =>
        wpCallDec rel μ A cur x e₂ (fun v₂ => Q (v₁ * v₂)))
  | .ifLe e₁ e₂ eThen eElse, Q =>
      wpCallDec rel μ A cur x e₁ (fun v₁ =>
        wpCallDec rel μ A cur x e₂ (fun v₂ =>
          (v₁ ≤ v₂ → wpCallDec rel μ A cur x eThen Q) ∧
          (¬ v₁ ≤ v₂ → wpCallDec rel μ A cur x eElse Q)))
  | .choose e₁ e₂, Q =>
      wpCallDec rel μ A cur x e₁ Q ∧ wpCallDec rel μ A cur x e₂ Q
  | .call fn eArg, Q =>
      wpCallDec rel μ A cur x eArg (fun vArg =>
        rel (μ fn vArg) cur ∧ (A fn).pre vArg ∧
          ∀ vRes, (A fn).post vArg vRes → Q vRes)

/-- Modular total-correctness verification of function `fn`'s body against `spec` under
callee assumptions `A` and measure `μ` ordered by `rel`.
Captures per-function Hoare obligation for recursive total correctness. -/
def BodyVerifiedTotal {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (A : SpecEnv) (fn : Fname) (body : Expr) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → wpCallDec rel μ A (μ fn x) x body (spec.post x)

/-- Modular total-correctness verification of every function defined in `M`.
Captures measure-indexed open assume-guarantee verification for total correctness. -/
def ModuleVerifiedTotal {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (M : Module) (A G : SpecEnv) : Prop :=
  ∀ fn body, M.lookup fn = some body → BodyVerifiedTotal rel μ A fn body (G fn)

/-- Contravariant precondition refinement: every input satisfying the assumed contract
`spec` also satisfies the stronger callee contract `spec'`.
Captures interface precondition weakening by a callee implementation. -/
def WeakensPre (spec spec' : FnSpec) : Prop :=
  ∀ x, spec.pre x → spec'.pre x

/-- Covariant postcondition refinement restricted to inputs satisfying the assumed
precondition `spec.pre`: any output allowed by `spec'` satisfies `spec`.
This is the refinement-calculus ordering ("strengthen the postcondition under the
precondition"); behavioural subtyping in the sense of Liskov and Wing requires the
stronger unconditional implication `spec'.post → spec.post`.
Captures behavioral postcondition strengthening under the caller's precondition. -/
def StrengthensPostUnderPre (spec spec' : FnSpec) : Prop :=
  ∀ x v, spec.pre x → spec'.post x v → spec.post x v

/-- Assumption environment for verifying a module `M` that calls both its own functions
and functions of other modules: calls to a function `M` defines are assumed to satisfy
`M`'s own guarantee `G`, and calls to any other function are assumed to satisfy the
external interface `S`.
Captures the usual rule for (mutually) recursive procedures inside one module combined
with interface-only assumptions about imports. -/
def mixEnv (M : Module) (G S : SpecEnv) : SpecEnv :=
  fun g => if M.Defines g then G g else S g

/-- A per-module compiler or optimizer pass `compile` preserves modular assume-guarantee
partial correctness against interface `S`: every module verified against `S` (assuming and
guaranteeing `S`) is mapped to a module that is again verified against `S`.
This mentions only `S`; it relates no behaviour of `compile M` to that of `M`.
Captures verification-preserving (specification-preserving) compilation. -/
def PreservesVerifiedPartial (compile : Module → Module) (S : SpecEnv) : Prop :=
  ∀ M, ModuleVerifiedPartial M S S → ModuleVerifiedPartial (compile M) S S

/-- A per-module compiler or optimizer pass `compile` retains every symbol defined in
its input module. Captures symbol-export preservation under separate compilation. -/
def PreservesDefines (compile : Module → Module) : Prop :=
  ∀ M fn, M.Defines fn → (compile M).Defines fn

/-- A per-module pass `compile` is a contextual refinement on every module:
`CtxRefines M (compile M)` for all `M`.
Captures behaviour-preserving separate compilation with the explicit behaviour relation
`CtxRefines` (lockstep-fuel outcome inclusion under every disjoint context). -/
def PassCtxRefines (compile : Module → Module) : Prop :=
  ∀ M, CtxRefines M (compile M)

end Toy.Link
