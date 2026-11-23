-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Boundary

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Effect-Indexed Function Contracts (`Trusted.MirSemantics.Contract`)

Declarative, syntax-independent contract core for $M_{\text{anneal}}$:
1. `EffectMask` and `AbiKind` (`extern "C"` vs. `extern "C-unwind"`),
2. `FnContract` (obligation-side, total-by-default with explicit `mayDiverge`
   opt-out) and `BodyBoundByPath` / `ContractSatisfied`,
3. `AssumedContract` (assumption-side, partial-by-default), general 8-mask
   `AssumedContractRealizable`, and `AssumedAbiConsistent`, and
4. `CallEdgeStratified` for modular mutual-recursion stratification.

**Why obligation-side and assumption-side termination defaults are asymmetric:**
- On the **obligation side** (`FnContract`, proved for verified bodies),
  `mayDiverge := false` requires `¬ Diverges` by default so an implementation
  cannot launder an unprovable `postReturn` via `loop {}` without an explicit,
  human-reviewed `mayDiverge := true` opt-out on the spec surface.
- On the **assumption side** (`AssumedContract`, assumed for unverified
  external or `#[anneal::trusted]` stubs), `EffectMask.terminates := false`
  never silently assumes progress (`#3091`), so diverging stubs (such as `-> !`
  with `postReturn = False`) remain realizable unless termination is explicitly
  assumed and audited.
-/

/-- Explicit 3-bit effect mask separating safety and partial correctness from
termination, unwinding, and process aborts.

All three flags default to `false` (partial correctness) so assumption-side
contracts never silently assume progress, no-unwind, or no-abort. -/
structure EffectMask where
  terminates : Bool := false
  noUnwind : Bool := false
  noAbort : Bool := false

/-- Calling-convention unwind classification for foreign and Rust items.

In the Rust Reference (`src/panic.md`, `r[panic.unwind.ffi.undefined]`,
`rust-lang/reference` `a286e1ecb8ce193d50056e4bb042eea9b23876ef`):

> "Unwinding with the wrong ABI is undefined behavior:
> * Causing an unwind into Rust code from a foreign function that was called
>   via a function declaration or pointer declared with a non-unwinding ABI,
>   such as `\"C\"`, `\"system\"`, etc."

And in `rustc` (`compiler/rustc_abi/src/extern_abi.rs`,
`C { unwind: false } =><= "C"` vs. `C { unwind: true } =><= "C-unwind"`,
and `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`,
`AbortUnwindingCalls::run_pass` rewriting `!call_can_unwind` calls to
`UnwindAction::Unreachable`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

Because `rustc` emits `UnwindAction::Unreachable` on every foreign `extern "C"`
call site, an assumed `cNoUnwind` contract MUST declare `noUnwind := true`;
otherwise the demonic unwind branch faults `.undefined` and makes every caller
unprovable. `cUnwind` (`extern "C-unwind"`) keeps `noUnwind := false`. -/
inductive AbiKind where
  | rust
  | cNoUnwind
  | cUnwind

/-- Obligation-side behavioral contract proved for a verified function body.

**Why `safetyPre` and `behaviorPre` are separate:**
A safe Rust function (`body.isUnsafe = false`) can be called by arbitrary safe
code on all language-valid arguments, so behavioral preconditions
(`#[requires]`) must NEVER waive UB-freedom (`WellFormed`). Only `safetyPre`
gates `WellFormed`, and ONLY when `body.isUnsafe = true`; `behaviorPre` gates
postconditions and effects on both safe and unsafe functions.

**Why `mayDiverge` is a top-level field defaulting to `false`:**
Obligation-side contracts require termination (`¬ Diverges`) by default, even
when `noUnwind` or `noAbort` is set. Partial correctness requires an explicit,
auditable `mayDiverge := true` opt-out. `measure` supplies an optional `Nat`
ranking function required by `CallEdgeStratified` inside cyclic SCCs. -/
structure FnContract where
  safetyPre : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn : Query → Out → Prop := fun _ _ => True
  postUnwind : Query → CallerMemory → Prop := fun _ _ => True
  postAbort : Query → CallerMemory → Prop := fun _ _ => True
  mayDiverge : Bool := false
  noUnwind : Bool := false
  noAbort : Bool := false
  measure : Option (Query → Nat) := none

/-- Effective safety precondition guarding `WellFormed` (always `True` when
`isUnsafe = false`). -/
def FnContract.effectiveSafetyPre (c : FnContract) (isUnsafe : Bool)
    (q : Query) : Prop :=
  isUnsafe = true → c.safetyPre q

/-- Effective combined precondition guarding postconditions and effects. -/
def FnContract.effectiveBehaviorPre (c : FnContract) (isUnsafe : Bool)
    (q : Query) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- Valid entry query for `body` under Profile version 1: arguments match
`body.locals[1..=argumentCount]` and `callerMem` is empty. -/
def ValidContractQuery (body : Body) (q : Query) : Prop :=
  ValidEntryArgs body q.args ∧ q.callerMem = ⟨[]⟩

/-- Well-typed normal return output for `body`: `out.ret` matches
`body.locals[0]`. For `MirTy.never`, `checkVal` is always `false`, making
normal return uninhabited automatically. -/
def ValidReturnVal (body : Body) (out : Out) : Prop :=
  match getElem? body.locals 0 with
  | some retTy => checkVal out.ret retTy = true
  | none => False

/-- Canonical item-path and signature-safety binding for a body in `p`.

Binding by canonical Rust item path (`itemPath`) and `expectedIsUnsafe` (under
`bodiesHaveUniqueIdentities p.bodies = true`) prevents positional `DefId`
reordering from silently aliasing another function or swapping safe/unsafe
signature status. -/
def BodyBoundByPath (p : Program) (itemPath : String)
    (expectedIsUnsafe : Bool) (defId : DefId) (body : Body) : Prop :=
  bodiesHaveUniqueIdentities p.bodies = true ∧
  getElem? p.bodies defId = some body ∧
  body.identity = itemPath ∧
  body.isUnsafe = expectedIsUnsafe

/-- Top-level satisfaction judgment for the body uniquely named `itemPath`
(with signature safety `expectedIsUnsafe`) in `p` against obligation contract
`c`. Enforces unconditional safe `WellFormed`, default termination
(`c.mayDiverge = false → ¬ Diverges`), typed postconditions, and optional
`noUnwind` / `noAbort` guarantees. -/
def ContractSatisfied (p : Program) (itemPath : String)
    (expectedIsUnsafe : Bool) (c : FnContract) : Prop :=
  ∃ (defId : DefId) (body : Body),
    BodyBoundByPath p itemPath expectedIsUnsafe defId body ∧
    BodyStaticAdmitted p body = true ∧
    let ep := entryProgForBody p defId
    (∀ q : Query, ValidContractQuery body q →
      c.effectiveSafetyPre body.isUnsafe q →
      WellFormed ep q) ∧
    (∀ q : Query, ValidContractQuery body q →
      c.effectiveBehaviorPre body.isUnsafe q →
      (∀ out : Out, Behavior ep q (.returned out) →
        ValidReturnVal body out ∧ c.postReturn q out) ∧
      (∀ mem : CallerMemory, Behavior ep q (.unwound mem) →
        c.postUnwind q mem) ∧
      (∀ mem : CallerMemory, Behavior ep q (.aborted mem) →
        c.postAbort q mem) ∧
      (c.mayDiverge = false → ¬ Diverges ep q) ∧
      (c.noUnwind = true →
        ∀ mem : CallerMemory, ¬ Behavior ep q (.unwound mem)) ∧
      (c.noAbort = true →
        ∀ mem : CallerMemory, ¬ Behavior ep q (.aborted mem)))

/-- Assumption-side contract for an unverified external or `#[anneal::trusted]`
stub. Unlike `FnContract`, `effects` defaults to partial (`terminates = false`)
so callers never silently assume progress (`#3091`). -/
structure AssumedContract where
  safetyPre : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn : Query → Out → Prop := fun _ _ => True
  postUnwind : Query → CallerMemory → Prop := fun _ _ => True
  postAbort : Query → CallerMemory → Prop := fun _ _ => True
  effects : EffectMask := ⟨false, false, false⟩

/-- Effective safety precondition on an assumed callee. -/
def AssumedContract.effectiveSafetyPre (c : AssumedContract) (isUnsafe : Bool)
    (q : Query) : Prop :=
  isUnsafe = true → c.safetyPre q

/-- Effective combined behavioral precondition on an assumed callee. -/
def AssumedContract.effectiveBehaviorPre (c : AssumedContract) (isUnsafe : Bool)
    (q : Query) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- General 8-mask realizability obligation for an assumed contract `c`.

**Why all four disjuncts are required across all 8 `EffectMask` combinations:**
Checking `∃ out, postReturn` only when `(terminates, noUnwind, noAbort) =
(true, true, true)` leaves intermediate masks (such as `terminates = true,
noUnwind = false, noAbort = true` with `postReturn = False` and
`postUnwind = False`) with zero admissible demonic call outcomes, allowing
callers to derive `False` vacuously. This 4-disjunct formula is equivalent to
explicit call-choice inhabitation across all 8 masks, while default
`terminates = false` discharges it via `Or.inl rfl`. -/
def AssumedContractRealizable (body : Body) (c : AssumedContract) : Prop :=
  ∀ q : Query, ValidContractQuery body q →
    c.effectiveBehaviorPre body.isUnsafe q →
    (c.effects.terminates = false) ∨
    (∃ out : Out, ValidReturnVal body out ∧ c.postReturn q out) ∨
    (c.effects.noUnwind = false ∧
      ∃ mem : CallerMemory, c.postUnwind q mem) ∨
    (c.effects.noAbort = false ∧
      ∃ mem : CallerMemory, c.postAbort q mem)

/-- ABI consistency gate for foreign assumed contracts: `extern "C"`
(`AbiKind.cNoUnwind`) calls lower to `UnwindAction::Unreachable` in `rustc`, so
their assumed contract must explicitly declare `noUnwind = true`. -/
def AssumedAbiConsistent (abi : AbiKind) (c : AssumedContract) : Prop :=
  match abi with
  | .cNoUnwind => c.effects.noUnwind = true
  | .rust | .cUnwind => True

/-- Modular mutual-recursion stratification gate for a call edge from
`(callerId, qCaller)` to `(calleeId, qCallee)` under SCC rank map `sccRank`.

**Why partial (`mayDiverge = true`) and total (`mayDiverge = false`) calls are
asymmetric:**
Partial correctness and safety hold across arbitrary mutual recursion by step
induction (no measure or SCC acyclicity required). When `cCaller.mayDiverge =
false` (total, the default), circular termination assumptions around a cycle
are unsound unless `cCallee.mayDiverge = false` and every edge either crosses
strictly downward across SCC strata (`sccRank calleeId < sccRank callerId`) or
strictly decreases a `Nat` measure within the same SCC. -/
def CallEdgeStratified (sccRank : DefId → Nat)
    (callerId calleeId : DefId)
    (cCaller cCallee : FnContract)
    (qCaller qCallee : Query) : Prop :=
  cCaller.mayDiverge = false →
    cCallee.mayDiverge = false ∧
    (sccRank calleeId < sccRank callerId ∨
      (sccRank calleeId = sccRank callerId ∧
        match cCaller.measure, cCallee.measure with
        | some mCaller, some mCallee => mCallee qCallee < mCaller qCaller
        | _, _ => False))

end Trusted.MirSemantics

end
