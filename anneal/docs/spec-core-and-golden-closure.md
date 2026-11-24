<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Specification Core v2 and Golden Spec-Closure Governance

> **Status: Target architecture, partly implemented.**
>
> **Shipped today:** out-of-line `Spec.lean` modules over the scalar MIR
> profile (`UnitTheorem` and `CrateTheorem`; see [alpha guide](alpha.md),
> [`#4095`](https://github.com/google/zerocopy/issues/4095)); the contract
> core in `Trusted.MirSemantics.Contract` (`EffectMask`, `FnContract`,
> `ContractSignature`, `BodyContractSatisfied`, `ContractPreInhabited`,
> `ContractEntry`, `ContractSpecs`, `scalarAsInt`); and `autoImplicit false` /
> `relaxedAutoImplicit false` for specification modules, enforced by both
> `"spec-preflight"` and Lean compilation.
>
> **Target design, not yet implemented:** everything else below, including
> `EffectMask.le`, the `measure`, `InvariantEnv`, `SpecEval`, and abort-related
> parts of the §1–§2 sketches (which therefore differ from the shipped
> definitions), assumed-contract realizability, the Rust surface syntax, and
> Golden Spec Closure rendering with `CODEOWNERS`/`OWNERS` governance. These are
> tracked under [`#4102`](https://github.com/google/zerocopy/issues/4102) and
> sequenced after Stage 1 audited TCB accounting
> ([`#4012`](https://github.com/google/zerocopy/issues/4012)).

Anneal's design goal is to let Rust programmers write ergonomic inline
specifications (`core::contracts`, `anodized`, or thin `anneal-spec`
attributes) while supporting rich out-of-line Lean 4 mathematical models
(`Spec.lean`) when needed—without duplicating Rust semantics inside
`trusted/lean/` and without fracturing the human review surface defined in
[`THREAT_MODEL.md`](../THREAT_MODEL.md).

Two architectural pillars achieve this together:

1. **Specification Core v2 (`Trusted.MirSemantics.Contract`):** A compact,
   tactic-free, syntax-independent 3-primitive semantic core that every Rust
   and Lean specification frontend lowers into.
2. **Always-Rendered Golden Spec Closure + `CODEOWNERS` / `OWNERS`
   Enforcement:** A mandatory canonical artifact that renders the exact
   transitive definition closure of every stated specification into one
   deterministic, diffable golden file, regardless of whether specs were
   authored inline in Rust or out-of-line in Lean.

## 1. Primitive 1: `FnContract`, `EffectMask`, and soundness rules

### Separating `safetyPre` from `behaviorPre`

Using a single precondition predicate to guard `WellFormed` (UB-freedom) on all
functions is unsound for safe Rust. Safe functions can be called from arbitrary
safe Rust code on any valid Rust value; annotating a safe function
`pub fn f(x: u32)` with `#[requires(x < 10)]` must **never** allow `f` to
exhibit undefined behavior when called with `x = 20`.

`FnContract` enforces this distinction structurally by splitting preconditions
into two fields:

```lean
structure EffectMask where
  terminates : Bool  -- forbids Diverges
  noUnwind   : Bool  -- forbids TerminalOut.unwound
  noAbort    : Bool  -- forbids TerminalOut.aborted (post-M1-Blocker-0)

def EffectMask.le (m1 m2 : EffectMask) : Prop :=
  (m1.terminates = true -> m2.terminates = true) ∧
  (m1.noUnwind = true -> m2.noUnwind = true) ∧
  (m1.noAbort = true -> m2.noAbort = true)

structure FnContract where
  safetyPre   : Query -> Prop := fun _ => True
  behaviorPre : Query -> Prop := fun _ => True
  postReturn  : Query -> Out -> Prop := fun _ _ => True
  postUnwind  : Query -> CallerMemory -> Prop := fun _ _ => True
  postAbort   : Query -> CallerMemory -> Prop := fun _ _ => True
  effects     : EffectMask
  measure     : Option (Query -> Nat) := none
```

`EffectMask` fields and `FnContract.effects` intentionally carry **no struct
defaults** so Lean generates zero `._default` terms and every rendered or
hand-written `Spec.lean` states all effect bits explicitly. Named constructors
`EffectMask.totalNormal` and `EffectMask.partialAnyExit` capture the two
canonical masks, and uniform positive polarity (`true` = stronger guarantee)
gives `EffectMask.le` a clean pointwise Boolean product lattice for call-edge
and trait/impl strengthening.

- **`safetyPre` (active only when `body.isUnsafe = true`):** Defines
  `effectiveSafetyPre := (body.isUnsafe = true -> c.safetyPre q)`. On safe
  functions (`isUnsafe = false`), `effectiveSafetyPre` reduces to `True`, so
  `ContractSatisfied` requires `WellFormed` (UB-freedom) unconditionally over
  all `FullValid` entry states regardless of `behaviorPre`.
- **`behaviorPre` (active on both safe and unsafe functions):** Combined as
  `effectiveBehaviorPre := effectiveSafetyPre ∧ c.behaviorPre`, gating
  `postReturn`, `postUnwind`, `postAbort`, and the `EffectMask` obligations.

### Total-by-default verified specs vs. partial-by-default assumed contracts

Verified specifications and unverified assumptions use intentionally asymmetric
Layer-2 defaults across `EffectMask` so both directions fail safe:

- **Verified functional specifications default to Total Normal Return
  (`EffectMask.totalNormal`: `terminates = true`, `noUnwind = true`, and
  `noAbort = true` post-abort support):** Under partial correctness, a function
  can satisfy any postcondition trivially by diverging (`loop {}`), allowing
  postcondition laundering through non-termination; similarly, omitting panic
  or abort guarantees silently hides panic paths. Verified functional
  specifications therefore require normal termination by default (`95%+` of
  loop-free systems code needs zero effect annotations). Authors opt out
  explicitly on the human-reviewed surface via `may_diverge`
  (`terminates = false`), `may_unwind` (`noUnwind = false`), `may_panic`, or
  staged `may_abort`, making every permitted failure or divergence mode
  visible in golden spec-closure review.
- **Assumed external contracts remain partial by default
  (`EffectMask.partialAnyExit`: `terminates = false`, `noUnwind = false`,
  `noAbort = false`,
  [`#3091`](https://github.com/google/zerocopy/issues/3091)):**
  Anneal never silently assumes progress or panic-freedom from unverified
  `#[anneal::trusted]` or `extern` callees. Leaving assumed contracts partial
  by default `(false, false, false)` (save `extern "C"` `noUnwind = true`
  below) avoids unstated liveness assumptions and prevents callers from
  deriving `False` from diverging or `-> !` stubs; any escalation on an
  assumed contract must appear explicitly in the specification and Receipt v3
  `tcb_shims[]` and discharge `AssumedContractRealizable`.

### Four-way outcomes, `TerminalOut.aborted`, and foreign ABI consistency

To distinguish unwinding panics from process aborts accurately, Specification
Core v2 extends `Trusted.MirModel.TerminalOut` with `.aborted` (alongside
`.returned` and `.unwound`) and adds `TerminatorKind.unwindTerminate` to
`Trusted.MirAst.Terminators` (matching `rustc`'s `UnwindTerminate` terminator,
emitted for `extern "C-unwind"` calls under `-C panic=abort`).

For foreign assumed functions, `AbiKind` distinguishes `rust`, `cNoUnwind`
(`extern "C"`), and `cUnwind` (`extern "C-unwind"`):

- Because `rustc` emits `UnwindAction::Unreachable` on foreign `extern "C"`
  call sites, assuming `noUnwind = false` on an `extern "C"` stub would make
  every caller fault as UB. Therefore, foreign `extern "C"` assumed contracts
  require `noUnwind = true` (`AssumedAbiConsistent`) and record that assumption
  explicitly in Receipt v3 `tcb_shims[]`.
- Foreign `extern "C-unwind"` stubs default to `noUnwind = false`.

### General 8-mask `AssumedContractRealizable` soundness condition

When a caller invokes an assumed contract (`#[anneal::trusted]` or `extern`),
the operational semantics branches demonically over the set of outcomes
permitted by the contract's `EffectMask` and postconditions
(`ValidAssumedChoice`). If that set were empty for some valid entry query `q`,
the caller could derive `False` and prove arbitrary false claims!

Checking `∃ out, postReturn q out` only when all three `EffectMask` bits are
`true` leaves a soundness hole on intermediate masks—for example,
`(terminates = true, noUnwind = false, noAbort = true)` with
`postReturn = False ∧ postUnwind = False`, where no valid demonic branch
exists. `AssumedContractRealizable` closes all 8 combinations of `EffectMask`
with an exact 4-way disjunction equivalent to `ValidAssumedChoice` inhabitation:

```lean
noncomputable def AssumedContractRealizable
    (env : InvariantEnv) (body : Body) (c : FnContract) : Prop :=
  ∀ q : Query, ValidContractQuery env body q ->
    c.effectiveBehaviorPre body.isUnsafe q ->
    (c.effects.terminates = false) ∨
    (∃ out : Out, ValidReturnFullValid env body out ∧ c.postReturn q out) ∨
    (c.effects.noUnwind = false ∧ ∃ mem : CallerMemory, c.postUnwind q mem) ∨
    (c.effects.noAbort  = false ∧ ∃ mem : CallerMemory, c.postAbort  q mem)
```

Under the partial-by-default assumed mask (`terminates = false`), the first
disjunct holds immediately via non-faulting divergence, so `#[trusted]
#[ensures(false)] fn spin() -> !` is sound and cannot let callers derive
`False`. Escalating an assumed contract to `terminates = true` obligates the
proof to witness at least one enabled return, unwind, or abort outcome.

### Two-tier modular mutual-recursion stratification

Modular assume-guarantee verification replaces a concrete callee invocation
with the callee's `FnContract`. Soundness across mutually recursive functions
follows a two-tier rule:

- **Partial contracts (`terminates = false`):** Modular assume-guarantee for
  safety (`WellFormed`), postconditions, `noUnwind`, and `noAbort` is
  unconditionally sound across arbitrary mutual recursion.
- **Total contracts (`terminates = true`):** Naive modular assumption of
  `terminates = true` is unsound—mutually recursive `f() { g() }` and
  `g() { f() }` would prove each other's termination. Therefore, modular
  `terminates = true` calls are admitted only when either:
  1. The call crosses strictly downward between call-graph strongly connected
     components (acyclic stratification), or
  2. Every call edge inside a `terminates = true` SCC supplies a `decreases`
     measure (`Query -> Nat`; surface `decreases(e)` checks an explicit
     non-negativity guard `0 <= e` before converting to `Nat`) and discharges
     `meas q_callee < meas q_caller`.

## 2. Primitive 2: Pure clause evaluation (`SpecEval`) and capture IR

Inline Rust contract frontends—nightly `core::contracts`, `verify-rust-std`
annotations, `anodized`, and thin `anneal-spec` attributes—all lower through a
single syntax-agnostic capture IR (`BodyContract`) and a universal dead-branch
marker ABI (`if false { ... }`) captured under `-Zcontract-checks=no
-Zmir-preserve-ub`. Because contract clauses are ordinary MIR closure bodies
evaluated by `Trusted.MirSemantics`, `trusted/lean/` needs **zero** second Rust
expression interpreter.

Four soundness invariants govern `SpecEval` and contract capture:

1. **Stepwise `callerMem` immutability (`SpecEvalVal`):** A contract clause
   must be `WellFormed`, terminating (`¬ Diverges`), deterministic, and
   read-only at *every* intermediate execution step
   (`∀ s_mid, Reaches s_0 s_mid -> s_mid.callerMem = q_c.callerMem`). Checking
   only endpoint equality would wrongly admit temporary `UnsafeCell`
   write-then-restore side effects.
2. **Pre-state `old!` snapshots without `AllocId` collisions:** Rather than
   placing pre-state and post-state `&mut T` allocations in the same
   `CallerMemory` (which collides on `AllocId`) or remapping pointer IDs (which
   breaks pointer identity), each `old!` closure is evaluated in pre-state via
   `SpecEvalVal` and materialized at fresh disjoint read-only `AllocId`s in
   `out.callerMem`.
3. **Short-circuiting multi-clause conjunction (`&&`):** Dependent clauses must
   evaluate sequentially with short-circuiting so a later clause is only
   evaluated when earlier guards hold. Eager bitwise `&` clause joins are
   rejected fail-closed at capture time.
4. **Fail-closed dead-scaffold erasure:** Capture rejects
   `-Zcontract-checks=yes`, any non-capture side-effecting statement inside the
   dead contract scaffold, any `StorageLive`/`StorageDead` annotation drift on
   surviving runtime locals during scaffold pruning, and any ghost memory
   intrinsic appearing inside a runtime body.

## 3. Primitive 3: Stratified type and `unsafe trait` invariants

`InvariantEnv` pairs language validity (`LangValid`) with library type
invariants (`libValid`) into `FullValid := LangValid ∧ LibValid`, ensuring
validity-sensitive traits (such as `FromBytes` and `IntoBytes`) quantify over
both language and library invariants.

Two structural gates prevent classic Rust soundness traps:

- **`ProductiveUnsafeImpl` (coinductive `unsafe impl` soundness):** Naively
  rejecting any trait-impl dependency cycle touching an `unsafe impl` falsely
  rejects valid recursive types such as
  `struct BoxNode { next: Option<Box<BoxNode>> }: Send` (which cycles through
  `unsafe impl<T: Send> Send for Box<T>`). Instead, capture builds the
  trait-impl dependency graph $G_{\text{impl}}$ and requires every cycle to
  cross an indirection-guarded subterm edge and discharge a depth-indexed
  `UnsafeImplObligation` (`∀ d' < d, whereAt d' -> typeInvAt d binding`). This
  admits `BoxNode: Send` while failing closed on unguarded self-cycles,
  unproductive mutual cycles, and specialized/`default` impls on
  contract-bearing traits. `TraitContract` also binds associated types and
  constants (`ImplBinding`) for traits such as `KnownLayout`.
- **`VisCone` unwind-closed encapsulation:** For any type `S` with a
  non-trivial `LibValid S`, every verified item inside `S`'s visibility cone
  (`VisCone(S)`, narrowed when `unsafe` fields restrict field access) must
  preserve `LibValid S` on **both `.returned` and `.unwound` exits** so
  `catch_unwind` callers cannot observe broken library invariants. Any
  unverified item inside `VisCone(S)` is logged explicitly in Receipt v3
  `tcb_shims[]`.

## 4. Always-rendered golden spec closure + `CODEOWNERS` / `OWNERS` enforcement

### Core architectural requirement

Regardless of whether specifications are authored **inline in Rust
annotations** (`core::contracts`, `anodized`, `anneal-spec`) OR **out-of-line
in dedicated `.lean` files**, Anneal MUST always deterministically render the
**complete, canonical transitive definition closure of all stated
specifications** into an inspectable golden artifact (alongside `Specs/` and
authenticated by digest in Receipt v3).

To prevent silent rebinding or hidden semantic drift, the rendered golden spec
closure MUST include:

- **Resolved canonical Rust item paths:** Every specification binds to its
  resolved canonical Rust item path (for example, `my_crate::module::func`).
  Positional body indexing (such as `entryProgForBody program 0`) is forbidden,
  and unresolved or renamed items fail closed so adding, removing, or
  reordering functions can never silently attach a specification to a different
  body.
- **Safe vs. `unsafe fn` signature, ABI, and types:** Each bound item's safe
  vs. `unsafe fn` qualifier, ABI (`extern "Rust"`, `extern "C"`,
  `extern "C-unwind"`), and concrete parameter and return types—ensuring a
  signature or safety-qualifier change (such as switching `fn` to `unsafe fn`,
  which activates `safetyPre`) surfaces loudly in the golden diff.
- **Referenced Rust helper bodies:** Any Rust helper function body whose
  definition a specification references (such as pure predicate helpers invoked
  from inline contract clauses), closing the seam where editing a Rust helper
  silently alters what the specification means.

```text
  Inline Rust contracts              Out-of-line Lean specs
  (core::contracts / anodized /      (Specs/*.lean checked by
   anneal-spec attributes)            TrapFreeHumanSpecAST)
             │                                  │
             └──────────────┬───────────────────┘
                            ▼
            Deterministic Canonical Spec-Closure Renderer
                            │
                            ▼
       <target>.spec-closure.golden  (checked into VCS under
                                      CODEOWNERS / OWNERS!)
                            │
          ┌─────────────────┴─────────────────┐
          ▼                                   ▼
   CI Golden-Diff Gate                 Receipt v3 Binding
   Any edit altering the               expected_cone_sha256 &
   rendered transitive spec            spec_closure_sha256
   closure fails CI until              bind the exact verified
   golden is updated and               specification closure
   approved by spec owners
```

### Why always-rendered golden spec closures are required

1. **Unbypassable `CODEOWNERS` / `OWNERS` review governance:** Repositories can
   check the rendered golden spec closure into version control under a
   protected path (for example, `specs/CODEOWNERS` or `specs/OWNERS`). Any
   change anywhere in the codebase—including an edit inside an inline Rust
   attribute, a procedural macro expansion, a helper constant, or a transitive
   Lean definition—that alters the kernel-checked specification closure causes
   a loud golden diff and mechanically requires specification-owner approval
   before merge.
2. **Closes the inline-vs-out-of-line audit split:** Inline Rust contracts give
   developers low-friction local authoring, while the always-rendered golden
   closure preserves [`THREAT_MODEL.md`](../THREAT_MODEL.md)'s bounded
   two-surface review boundary: reviewers inspect only the rendered golden spec
   closure and the Receipt v3 TCB audit log, never `Proof/*.lean`.
3. **Neutralizes hasty-reader and macro-expansion surprises:** Rendering the
   exact transitive kernel-checked closure in one deterministic, diffable text
   artifact eliminates hidden ambient definitions, implicit binder surprises
   (`autoImplicit`), notation shadowing, and silent macro drift. Combined with
   closed-allowlist `TrapFreeHumanSpecAST` syntax validation on `Spec.*`
   modules (which bans `autoImplicit true`, unguarded `Nat` subtraction/
   division, macros, and panicking totalized accessors), what a reviewer reads
   in the golden diff is unambiguously what the Lean kernel checks.

### Typical repository workflow

1. A developer or agent writes or updates Rust code and inline contracts (or
   out-of-line `Specs/*.lean`).
2. Running Anneal deterministically regenerates the target's canonical golden
   spec closure (`<target>.spec-closure.golden`).
3. In CI, verification fails closed if the freshly rendered closure differs
   from the checked-in golden file, and Receipt v3 records the exact
   `spec_closure_sha256` and `expected_cone_sha256`.
4. Pure proof changes (`Proof/*.lean`) and implementation refactors that
   preserve the exact specification produce **zero diff** in the golden spec
   closure and require no spec-owner sign-off. Any change that alters a
   precondition, postcondition, invariant, or transitive helper definition
   surfaces directly in the golden file diff under `CODEOWNERS` / `OWNERS`
   protection.
