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
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.State
public import Trusted.MirSemantics.Step
public import Trusted.MirSemantics.Boundary

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Function Contracts (`Trusted.MirSemantics.Contract`)

A syntax-independent contract layer that compiles down to the `Specs` /
`UnitTheorem` / `CrateTheorem` boundary in `Trusted.MirSemantics.Boundary`:

- `FnContract` separates the caller's safety obligation `safetyPre` (consulted
  only when `body.isUnsafe = true`) from the behavioral precondition
  `behaviorPre` (which gates postconditions and effects on every body), and
  carries outcome-specific postconditions and an `EffectMask`;
- `BodyContractSatisfied` is the per-body judgment;
- `ContractPreInhabited` is the non-vacuity obligation; and
- `ContractEntry` / `ContractSpecs` package identity-bound contracts as a
  `Specs`.

`ContractSpecs` is the target of a Rust-syntax specification lowering (which
follows in a separate change), whose generated `Spec.lean` also decodes
integer arguments and results through `decodeScalar` / `scalarAsInt`.
-/

/-- Permitted non-normal outcomes of a function contract, with uniform positive
polarity (`true` = stronger guarantee / narrower allowed effect set):
- `terminates = true` forbids `Diverges`; `false` permits divergence.
- `noUnwind = true` forbids `TerminalOut.unwound`; `false` permits unwinding.

Fields intentionally have no defaults so every specification and `Spec.lean`
audit artifact states every effect bit explicitly. The mask has no abort bit
yet: `BodyContractSatisfied` rejects every `TerminalOut.aborted` outcome, so no
contract admits a `--panic abort` termination.
-/
structure EffectMask where
  terminates : Bool
  noUnwind   : Bool

/-- Total normal return: forbids both divergence and unwinding. -/
def EffectMask.totalNormal : EffectMask :=
  { terminates := true, noUnwind := true }

/-- Partial contract permitting divergence and unwinding (but never aborting;
see `BodyContractSatisfied`). Appropriate for unverified assumptions rather
than verified obligations. -/
def EffectMask.partialAnyExit : EffectMask :=
  { terminates := false, noUnwind := false }

/-- Syntax-independent function contract separating the UB-safety obligation
(`safetyPre`, enforced only when `body.isUnsafe = true`) from the functional
precondition (`behaviorPre`, active for both safe and unsafe functions) and
outcome-specific postconditions (`postReturn`, `postUnwind`). -/
structure FnContract where
  safetyPre   : Query → Prop := fun _ => True
  behaviorPre : Query → Prop := fun _ => True
  postReturn  : Query → Out → Prop := fun _ _ => True
  postUnwind  : Query → CallerMemory → Prop := fun _ _ => True
  effects     : EffectMask

/-- Safety precondition active on `body` entry: gated strictly by
`body.isUnsafe = true` so safe functions can never use `safetyPre` to guard UB.
-/
noncomputable def FnContract.effectiveSafetyPre (c : FnContract)
    (isUnsafe : Bool) (q : Query) : Prop :=
  isUnsafe = true → c.safetyPre q

/-- Combined precondition gating functional postconditions and effect
obligations: requires `safetyPre` (when `unsafe`) alongside `behaviorPre`. -/
noncomputable def FnContract.effectiveBehaviorPre (c : FnContract)
    (isUnsafe : Bool) (q : Query) : Prop :=
  c.effectiveSafetyPre isUnsafe q ∧ c.behaviorPre q

/-- Value-entry safety precondition projection matching `BodyVerified` and
`Specs.safety`. -/
noncomputable def FnContract.safetyArgPre (c : FnContract) : List Val → Prop :=
  fun args => c.safetyPre { args := args }

/-- Alias for `Trusted.MirSemantics.decodeScalar` allowing contract
specifications to decode MIR scalar operands and return values as mathematical
`Int`s without width or sign loss. -/
noncomputable abbrev scalarAsInt : ScalarVal → Int := decodeScalar

/-- Contract satisfaction judgment for body `body` at index `defId` in `p`:
1. `body` matches `p.bodies[defId]` and is statically admitted;
2. On all valid entry arguments satisfying `effectiveSafetyPre`, execution is
   `WellFormed` (UB- and fault-free); and
3. Whenever `effectiveBehaviorPre` also holds, every normal return satisfies
   `postReturn`, every unwind requires `effects.noUnwind = false ∧ postUnwind`,
   no execution aborts (`EffectMask` has no abort bit yet, so a contract never
   permits `--panic abort` termination), and `effects.terminates = true`
   forbids `Diverges`. -/
noncomputable def BodyContractSatisfied (p : Program) (defId : DefId)
    (body : Body) (c : FnContract) : Prop :=
  getElem? p.bodies defId = some body ∧
  BodyStaticAdmitted p body = true ∧
  ∀ args : List Val,
    ValidEntryArgs body args →
    let q : Query := { args := args }
    let ep := entryProgForBody p defId
    (c.effectiveSafetyPre body.isUnsafe q → WellFormed ep q) ∧
    (c.effectiveBehaviorPre body.isUnsafe q →
      (∀ out : TerminalOut, Behavior ep q out →
        match out with
        | .returned retOut => c.postReturn q retOut
        | .unwound uwMem =>
          c.effects.noUnwind = false ∧ c.postUnwind q uwMem
        | .aborted _ => False) ∧
      (c.effects.terminates = true → ¬ Diverges ep q))

/-- Non-vacuity witness obligation asserting that a function's combined entry
precondition admits at least one `ValidEntryArgs`-compatible argument tuple. -/
noncomputable def ContractPreInhabited (body : Body) (c : FnContract) : Prop :=
  ∃ args : List Val,
    ValidEntryArgs body args ∧
    c.effectiveBehaviorPre body.isUnsafe { args := args }

/-- Optional expected MIR signature against which `bodySatisfiesContractEntry`
validates a captured `Body` (unsafe qualifier, parameter `MirTy` list, and
return `MirTy`), preventing out-of-band companion declarations from binding to
a body whose actual types or safety disagree. -/
structure ContractSignature where
  isUnsafe : Bool
  params   : List MirTy
  ret      : MirTy

/-- Check that `body` matches `sig` in `isUnsafe`, `argumentCount`, parameter
types (`locals[1..=argumentCount]`), and return type (`locals[0]`). -/
noncomputable def bodyMatchesContractSignature (body : Body)
    (sig : ContractSignature) : Bool :=
  (body.isUnsafe == sig.isUnsafe) &&
    Nat.beq body.argumentCount sig.params.length &&
    MirTy.beqList ((body.locals.drop 1).take body.argumentCount) sig.params &&
    match body.locals with
    | retTy :: _ => MirTy.beq retTy sig.ret
    | [] => false

/-- Named contract entry binding a `FnContract`, optional expected MIR
signature (`signature`), and optional non-vacuity guard (`requireInhabited`) to
a canonical Rust item identity string. -/
structure ContractEntry where
  identity : String
  contract : FnContract
  signature : Option ContractSignature := none
  requireInhabited : Bool := true

/-- Verification obligation for a single `ContractEntry` inside `p`: requires a
matching body in `p.bodies` (forbidding silent omission of missing targets),
signature agreement when `e.signature` is supplied, `BodyContractSatisfied`,
and `ContractPreInhabited` unless waived via `requireInhabited := false`. -/
noncomputable def bodySatisfiesContractEntry (p : Program)
    (e : ContractEntry) : Prop :=
  ∃ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body ∧
    stringBeq body.identity e.identity = true ∧
    (match e.signature with
     | none => True
     | some sig => bodyMatchesContractSignature body sig = true) ∧
    BodyContractSatisfied p defId body e.contract ∧
    (e.requireInhabited = true → ContractPreInhabited body e.contract)

/-- Structural conjunction requiring every `ContractEntry` in `entries` to be
discharged by `p` (unfolding definitionally so empty lists reduce to `True`
for trivial-property linting while non-empty entries inspect `p`). -/
noncomputable def ContractEntriesSatisfied (p : Program) :
    List ContractEntry → Prop
  | [] => True
  | e :: rest =>
    bodySatisfiesContractEntry p e ∧ ContractEntriesSatisfied p rest

/-- Balanced Red-Black tree indexing `ContractEntry` records by
`IdentityKey` for $O(\log N)$ `Specs.safety` lookup. -/
abbrev ContractEntryRbTree := IdentityRbTree ContractEntry

/-- Look up the unique `ContractEntry` for `identity` in `tree` in
$O(\log N)$ comparisons. -/
noncomputable def contractEntryRbLookup (tree : ContractEntryRbTree)
    (identity : String) : Option ContractEntry :=
  identityRbLookup tree identity

/-- Bridge a list of identity-bound `ContractEntry` obligations into a
`Trusted.MirSemantics.Specs` bundle for `UnitTheorem` and `CrateTheorem`.

Entry identities must be non-empty and pairwise distinct. `ContractSpecs`
indexes `entries` once into a balanced `ContractEntryRbTree`
(`IdentityRbTree ContractEntry`) so `safety` looks up per-body preconditions
in $O(\log N)$ steps rather than scanning linearly per body, and fails closed
(`False`) if any identity is empty or duplicated. -/
noncomputable def ContractSpecs (entries : List ContractEntry) : Specs :=
  match identityRbBuildAux
      (fun (e : ContractEntry) => e.identity) id entries .empty with
  | none =>
    { safety := fun _ _ => True
      property := fun p =>
        (false = true) ∧ ContractEntriesSatisfied p entries }
  | some tree =>
    { safety := fun id args =>
        match contractEntryRbLookup tree id with
        | some e => e.contract.safetyArgPre args
        | none => True
      property := fun p =>
        (true = true) ∧ ContractEntriesSatisfied p entries }

end Trusted.MirSemantics

end
