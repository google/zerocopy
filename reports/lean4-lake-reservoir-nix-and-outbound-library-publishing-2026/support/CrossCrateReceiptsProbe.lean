-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module

import Lean.Linter.Extra

/-!
# Standalone Cross-Crate Verification Receipts Probe (`OD-08`, `LIB-01`–`10`)

Synthesizes the multi-module `probe2-cross-crate-receipts` workspace
(`Core.lean`, `UpstreamCrate/Spec.lean`, `UpstreamCrate/MirAndProof.lean`, and
`DownstreamCrate/Consumer.lean`) into a single, zero-`sorry`, zero-warning Lean
`v4.34.1` artifact demonstrating all three cross-crate verification paths:

1. **Path 1 — Abstract specification composition (`LIB-01`, `LIB-02`, `LIB-07`,
   `LIB-08`):** Downstream callers verify interprocedural calls against an
   upstream function's exported `CalleeSatisfiesAbstractSpec` contract and
   encapsulated representation invariants (`BoundedCounter.Valid`) without
   unfolding the upstream `MirBody`.
2. **Path 2 — Direct dependency MIR inspection (`LIB-03`, `LIB-04`, `LIB-05`):**
   When an upstream crate exports only a weak contract (`ret ≤ 2000`), a
   downstream crate proves that the weak contract is insufficient for parity
   reasoning (`weak_contract_insufficient_for_halve_even`), inspects the
   upstream `MirBody` (`addBoundedBody`) directly without modifying or forking
   the upstream crate (`downstream_strengthened_upstream_exact`), and verifies
   its caller (`verify_downstream_halve_even_via_mir_inspection`).
3. **Path 3 — Transitive `VerifiedCrateReceipt` / `SubjectIdentity` checking
   (`OD-08`, `LIB-09`, `LIB-10`):** Receipts bind `SubjectIdentity`
   (`crateName`, `crateVersion`, `rustcCommit`, `targetTriple`, `mirSha256`) and
   merge `up.transitiveTcb ++ downLocalTcb`. Clean DAGs compose under
   `defaultTrustPolicy` (`downstream_clean_dag_verified`), tainted upstream
   crates carrying `.unsafeAxiom` fail closed under `defaultTrustPolicy`
   (`downstream_tainted_upstream_rejected_by_default_policy`) unless explicitly
   permitted (`downstream_tainted_upstream_accepted_with_explicit_policy`), and
   target-triple mismatches fail `CompatibleSubject`
   (`downstream_incompatible_target_rejected`).
-/

set_option linter.missingDocs true
set_option linter.unusedSimpArgs true
set_option linter.extra true

@[expose] public section

namespace CrossCrateProbe

/-!
## 1. Core Cross-Crate Receipt and MIR Evaluation Definitions (`Core`)
-/

/-- All propositions in `xs` hold (`List.foldr And True xs`). -/
def AllHold : List Prop → Prop
  | [] => True
  | p :: ps => p ∧ AllHold ps

/-- `AllHold` distributes over list append (`++`). -/
theorem allHold_append {xs ys : List Prop} :
    AllHold (xs ++ ys) ↔ AllHold xs ∧ AllHold ys := by
  induction xs with
  | nil => simp [AllHold]
  | cons x xs ih =>
    simp only [List.cons_append, AllHold, ih]
    exact ⟨fun ⟨hx, hxs, hys⟩ => ⟨⟨hx, hxs⟩, hys⟩,
           fun ⟨⟨hx, hxs⟩, hys⟩ => ⟨hx, hxs, hys⟩⟩

/-- Map append over `AllHold`. -/
theorem allHold_map_append {α : Type u} (P : α → Prop) (xs ys : List α) :
    AllHold ((xs ++ ys).map P) ↔ AllHold (xs.map P) ∧ AllHold (ys.map P) := by
  rw [List.map_append]
  exact allHold_append

/-- A trust policy over a type `Item` of TCB assumptions. -/
structure TrustPolicy (Item : Type u) where
  /-- Predicate determining whether a TCB item is permitted by this policy. -/
  isAllowed : Item → Prop

/-- A verification receipt asserting that every item in `tcb` is allowed by
`policy` and that `claim` holds whenever `assumptions` hold. -/
def VerificationResult {Item : Type u}
    (policy : TrustPolicy Item)
    (tcb : List Item)
    (assumptions : List Prop)
    (claim : Prop) : Prop :=
  AllHold (tcb.map policy.isAllowed) ∧ (AllHold assumptions → claim)

/-- Trusted Computing Base (TCB) assumption items tracked across crate
boundaries (`LIB-09`). -/
inductive TCBItem where
  /-- Standard vetted `rustc` MIR lowering and ABI semantics. -/
  | rustcLowering
  /-- Candidate-trusted Anneal subsystem feature (`@[candidate <feat>]`). -/
  | candidateFeature (feature : String)
  /-- Unverified `unsafe` or external FFI assumption introduced by a crate. -/
  | unsafeAxiom (name : String)
  deriving DecidableEq, Repr

/-- Default (`VettedOnly`) trust policy: allows only `.rustcLowering` and
rejects all candidate features and unverified `unsafe` axioms. -/
def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering => True
    | .candidateFeature _ => False
    | .unsafeAxiom _ => False

/-- Cryptographic and compiler identity of a captured Rust crate (`LIB-10`). -/
structure SubjectIdentity where
  /-- Cargo package / crate name. -/
  crateName : String
  /-- Cargo package version string. -/
  crateVersion : String
  /-- Pinned `rustc` commit hash used to capture `Runtime(PostCleanup)` MIR. -/
  rustcCommit : String
  /-- Target triple for layout and ABI evaluation. -/
  targetTriple : String
  /-- SHA-256 digest of the canonical `.anneal/Mir.lean` artifact. -/
  mirSha256 : String
  deriving DecidableEq, Repr

/-- Two crates in a verification DAG are ABI- and compiler-compatible (`LIB-10`)
when they were captured under the exact same `rustcCommit` and
`targetTriple`. -/
def CompatibleSubject (up down : SubjectIdentity) : Prop :=
  up.rustcCommit = down.rustcCommit ∧ up.targetTriple = down.targetTriple

/-- Qualified cross-crate function identifier (`crateName :: fnName`). -/
structure QualifiedFnId where
  /-- Defining crate name. -/
  crateName : String
  /-- Function symbol name within the crate. -/
  fnName : String
  deriving DecidableEq, Repr

/-- Deterministic evaluation outcome of a MIR function invocation. -/
inductive MirEvalOutcome where
  /-- Normal return with scalar `Nat` value `val`. -/
  | returns (val : Nat)
  /-- Defined panic / assertion failure / overflow trap. -/
  | traps
  /-- Out-of-fuel or unresolvable external call (`goesWrong`). -/
  | goesWrong
  deriving DecidableEq, Repr

/-- Simplified MIR expression/statement body used in the cross-crate probe to
model both concrete intraprocedural logic and cross-crate `Call` terminators. -/
inductive MirBody where
  /-- Check `arg0 ≤ bound ∧ arg1 ≤ bound`; if so return `arg0 + arg1`, else
  trap. -/
  | boundedAdd2 (bound : Nat)
  /-- Call an external/upstream function `callee` with `(arg0, arg0)` and check
  that its return value is `≤ maxOut`, returning that value or trapping. -/
  | callDupAndCheckBound (callee : QualifiedFnId) (maxOut : Nat)
  /-- Call an external/upstream function `callee` with `(arg0, arg0)` and assert
  that the returned value is even (`val % 2 == 0`), returning `val / 2` or
  trapping if odd. -/
  | callDupAndHalveEven (callee : QualifiedFnId)
  deriving DecidableEq, Repr

/-- External call environment mapping `QualifiedFnId` to its two-argument
operational behavior.

Generalizes `skeleton`'s hardcoded `PureCallee2` enum to an open cross-crate
call table (`OD-08`). -/
abbrev CallEnv := QualifiedFnId → Nat → Nat → MirEvalOutcome

/-- Evaluate a `MirBody` on two `Nat` arguments `(x, y)` under external call
environment `env`. -/
def evalMirBody (env : CallEnv) (body : MirBody) (x y : Nat) : MirEvalOutcome :=
  match body with
  | .boundedAdd2 bound =>
    if x ≤ bound && y ≤ bound then
      .returns (x + y)
    else
      .traps
  | .callDupAndCheckBound callee maxOut =>
    match env callee x x with
    | .returns v =>
      if v ≤ maxOut then .returns v else .traps
    | .traps => .traps
    | .goesWrong => .goesWrong
  | .callDupAndHalveEven callee =>
    match env callee x x with
    | .returns v =>
      if v % 2 == 0 then .returns (v / 2) else .traps
    | .traps => .traps
    | .goesWrong => .goesWrong

/-- A function is well-formed (free of `goesWrong` undefined behavior) under
call environment `env` when for all inputs `(x, y)` it either `.returns` or
`.traps`. -/
def MirFnWellFormed (env : CallEnv) (body : MirBody) : Prop :=
  ∀ x y, evalMirBody env body x y ≠ .goesWrong

/-- Two-argument function contract (`Pre → Post` on `.returns`, and never
`.goesWrong`). -/
structure FnContract where
  /-- Precondition on inputs `(x, y)`. -/
  Pre : Nat → Nat → Prop
  /-- Postcondition on inputs `(x, y)` and return value `ret`. -/
  Post : Nat → Nat → Nat → Prop

/-- A `MirBody` satisfies `contract : FnContract` under `env` when:
1. It never `.goesWrong` for any inputs (`MirFnWellFormed env body`), and
2. Whenever `contract.Pre x y` holds, `evalMirBody env body x y` returns a value
   `ret` satisfying `contract.Post x y ret` (no trap and no UB). -/
def SatisfiesContract
    (env : CallEnv) (body : MirBody) (contract : FnContract) : Prop :=
  MirFnWellFormed env body ∧
  ∀ x y, contract.Pre x y →
    ∃ ret, evalMirBody env body x y = .returns ret ∧ contract.Post x y ret

/-- An abstract specification for an external callee in `env` (`LIB-01`,
`LIB-02`): asserts that `env callee` never `.goesWrong` and satisfies
`contract`, without mentioning or exposing any `MirBody`. -/
def CalleeSatisfiesAbstractSpec
    (env : CallEnv) (callee : QualifiedFnId) (contract : FnContract) : Prop :=
  (∀ x y, env callee x y ≠ .goesWrong) ∧
  (∀ x y, contract.Pre x y →
    ∃ ret, env callee x y = .returns ret ∧ contract.Post x y ret)

/-- Bridge theorem (`LIB-01`, `LIB-02`): if a concrete `MirBody` is bound in
`env` at `callee` and satisfies `contract`, then `CalleeSatisfiesAbstractSpec`
holds for `callee`.

Downstream callers can consume `CalleeSatisfiesAbstractSpec` without ever
unfolding `body`. -/
theorem calleeSatisfiesAbstractSpec_of_body
    (env : CallEnv) (callee : QualifiedFnId)
    (body : MirBody) (contract : FnContract)
    (hBind : ∀ x y, env callee x y = evalMirBody env body x y)
    (hSat : SatisfiesContract env body contract) :
    CalleeSatisfiesAbstractSpec env callee contract := by
  rcases hSat with ⟨hWF, hPost⟩
  refine ⟨fun x y => ?_, fun x y hPre => ?_⟩
  · rw [hBind x y]
    exact hWF x y
  · rw [hBind x y]
    exact hPost x y hPre

/-- A cross-crate verification receipt (`OD-08`, `LIB-09`, `LIB-10`). -/
structure CrateReceipt where
  /-- Compiler, target, and artifact digest identity of this crate
  (`LIB-10`). -/
  subject : SubjectIdentity
  /-- Direct crate-local TCB items used by this crate. -/
  localTcb : List TCBItem
  /-- Transitive TCB items accumulated from this crate and all upstream
  dependencies (`LIB-09`). -/
  transitiveTcb : List TCBItem
  /-- Semantic verification claim established for this crate. -/
  claim : Prop

/-- Alias for `CrateReceipt` matching the `VerifiedCrateReceipt` nomenclature in
`OD-08`. -/
abbrev VerifiedCrateReceipt := CrateReceipt

/-- Compose an upstream crate's `VerificationResult` with a downstream crate's
verification obligation across the crate DAG (`LIB-09`, `LIB-10`).

Requires `CompatibleSubject up.subject downSubject` and merges the transitive
TCB `up.transitiveTcb ++ downLocalTcb`. -/
theorem composeCrateVerification
    (policy : TrustPolicy TCBItem)
    (up : CrateReceipt)
    (downSubject : SubjectIdentity)
    (downLocalTcb : List TCBItem)
    (upAssumptions downAssumptions : List Prop)
    (downClaim : Prop)
    (hCompat : CompatibleSubject up.subject downSubject)
    (hUpVer : VerificationResult policy up.transitiveTcb upAssumptions up.claim)
    (hDownLocalPolicy : AllHold (downLocalTcb.map policy.isAllowed))
    (hDownStep :
      CompatibleSubject up.subject downSubject →
        up.claim → AllHold downAssumptions → downClaim) :
    VerificationResult
      policy
      (up.transitiveTcb ++ downLocalTcb)
      (upAssumptions ++ downAssumptions)
      (CompatibleSubject up.subject downSubject ∧ downClaim) := by
  rcases hUpVer with ⟨hUpPol, hUpImp⟩
  refine ⟨?_, ?_⟩
  · rw [allHold_map_append]
    exact ⟨hUpPol, hDownLocalPolicy⟩
  · intro hBothAssump
    rw [allHold_append] at hBothAssump
    rcases hBothAssump with ⟨hUpA, hDownA⟩
    have hUpClaim := hUpImp hUpA
    exact ⟨hCompat, hDownStep hCompat hUpClaim hDownA⟩

/-!
## 2. Upstream Crate Specification and MIR/Proof Artifacts (`UpstreamCrate`)
-/

namespace UpstreamCrate

/-- Captured compiler and artifact identity for `upstream_math` (`LIB-10`). -/
def upstreamSubject : SubjectIdentity where
  crateName := "upstream_math"
  crateVersion := "0.1.0"
  rustcCommit := "rustc-1.88.0-nightly-2026-04-01"
  targetTriple := "x86_64-unknown-linux-gnu"
  mirSha256 :=
    "sha256:9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08"

/-- Qualified symbol identifier for `upstream_math::add_bounded`. -/
def addBoundedId : QualifiedFnId where
  crateName := "upstream_math"
  fnName := "add_bounded"

/-- Concrete captured `Runtime(PostCleanup)` MIR body for
`upstream_math::add_bounded` (`LIB-03`). -/
def addBoundedBody : MirBody :=
  .boundedAdd2 1000

/-- Upstream's published abstract contract for `add_bounded`: guarantees only
that when `x ≤ 1000 ∧ y ≤ 1000`, the return value `ret` satisfies `ret ≤ 2000`.

This contract intentionally omits `ret = x + y` to test `LIB-03`–`LIB-05`. -/
def upstreamWeakContract : FnContract where
  Pre x y := x ≤ 1000 ∧ y ≤ 1000
  Post _ _ ret := ret ≤ 2000

/-- Proof that `addBoundedBody` satisfies `upstreamWeakContract` under any call
environment `env`. -/
theorem addBoundedBody_satisfies_weak (env : CallEnv) :
    SatisfiesContract env addBoundedBody upstreamWeakContract := by
  refine ⟨fun x y => ?_, fun x y hPre => ?_⟩
  · simp only [evalMirBody, addBoundedBody]
    by_cases h : (x ≤ 1000 && y ≤ 1000) = true <;> simp [h]
  · rcases hPre with ⟨hx, hy⟩
    refine ⟨x + y, ?_, Nat.add_le_add hx hy⟩
    simp [evalMirBody, addBoundedBody, hx, hy]

/-- Exported abstract specification theorem (`LIB-01`, `LIB-02`): for any call
environment `env` that binds `addBoundedId` to `addBoundedBody`,
`CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract` holds. -/
theorem upstream_add_bounded_abstract_spec (env : CallEnv)
    (hBind : ∀ x y, env addBoundedId x y = evalMirBody env addBoundedBody x y) :
    CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract :=
  calleeSatisfiesAbstractSpec_of_body env addBoundedId addBoundedBody
    upstreamWeakContract hBind (addBoundedBody_satisfies_weak env)

/-- Representation-hiding container (`LIB-07`, `LIB-08`) whose private field
invariant (`val ≤ 1000`) is encapsulated via an abstract predicate `Valid`. -/
structure BoundedCounter where
  /-- Underlying counter value. -/
  val : Nat
  deriving DecidableEq, Repr

/-- Abstract validity predicate exported to downstream crates (`LIB-07`). -/
def BoundedCounter.Valid (c : BoundedCounter) : Prop :=
  c.val ≤ 1000

/-- Construct a valid zero counter (`LIB-07`). -/
def BoundedCounter.zero : BoundedCounter := ⟨0⟩

/-- `BoundedCounter.zero` satisfies the abstract validity invariant
(`LIB-07`). -/
theorem BoundedCounter.zero_valid : BoundedCounter.zero.Valid :=
  Nat.zero_le 1000

/-- Extract the bounded value from a `Valid` counter as a precondition witness
for `upstreamWeakContract` (`LIB-08`). -/
theorem BoundedCounter.valid_le_1000 {c : BoundedCounter} (h : c.Valid) :
    c.val ≤ 1000 := h

/-- Clean verification receipt for `upstream_math` using only vetted
`TCBItem.rustcLowering` (`LIB-09`). -/
def upstreamCleanReceipt (env : CallEnv) : CrateReceipt where
  subject := upstreamSubject
  localTcb := [.rustcLowering]
  transitiveTcb := [.rustcLowering]
  claim := SatisfiesContract env addBoundedBody upstreamWeakContract

/-- Proof of `VerificationResult` for `upstreamCleanReceipt` under
`defaultTrustPolicy`. -/
theorem verify_upstreamCleanReceipt (env : CallEnv) :
    VerificationResult
      defaultTrustPolicy
      (upstreamCleanReceipt env).transitiveTcb
      []
      (upstreamCleanReceipt env).claim := by
  refine ⟨⟨trivial, trivial⟩, fun _ => addBoundedBody_satisfies_weak env⟩

/-- Tainted verification receipt for an upstream crate that relies on an
unverified `unsafe` axiom (`TCBItem.unsafeAxiom "upstream_raw_ptr_sound"`). -/
def taintedUpstreamReceipt (env : CallEnv) : CrateReceipt where
  subject := upstreamSubject
  localTcb := [.rustcLowering, .unsafeAxiom "upstream_raw_ptr_sound"]
  transitiveTcb := [.rustcLowering, .unsafeAxiom "upstream_raw_ptr_sound"]
  claim := SatisfiesContract env addBoundedBody upstreamWeakContract

end UpstreamCrate

/-!
## 3. Downstream Crate Verification (`DownstreamCrate`)
-/

namespace DownstreamCrate

open UpstreamCrate

/-!
### Path 1: Abstract Specification Composition (`LIB-01`, `02`, `07`, `08`)
-/

/-- Downstream function body that calls `upstream_math::add_bounded(x, x)` and
checks that the result is `≤ 2000`. -/
def downstreamCheckBoundBody : MirBody :=
  .callDupAndCheckBound addBoundedId 2000

/-- Downstream contract for `downstreamCheckBoundBody`. -/
def downstreamCheckBoundContract : FnContract where
  Pre x _ := x ≤ 1000
  Post _ _ ret := ret ≤ 2000

/-- Abstract specification composition (`LIB-01`, `LIB-02`): verifies
`downstreamCheckBoundBody` using only the abstract specification
`CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract`.

`UpstreamCrate.addBoundedBody` does not appear anywhere in the theorem statement
or proof. -/
theorem verify_downstream_via_abstract_spec (env : CallEnv)
    (hAbs : CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract) :
    SatisfiesContract
      env downstreamCheckBoundBody downstreamCheckBoundContract := by
  rcases hAbs with ⟨hNoUB, hWeakPost⟩
  refine ⟨fun x y => ?_, fun x y hx => ?_⟩
  · simp only [evalMirBody, downstreamCheckBoundBody]
    have hCall := hNoUB x x
    cases hOut : env addBoundedId x x with
    | returns v =>
      by_cases hv : v ≤ 2000 <;> simp [hv]
    | traps => simp
    | goesWrong => exact False.elim (hCall hOut)
  · have hPre : upstreamWeakContract.Pre x x := ⟨hx, hx⟩
    rcases hWeakPost x x hPre with ⟨ret, hCallRet, hRetLe⟩
    have hRetLe' : ret ≤ 2000 := hRetLe
    refine ⟨ret, ?_, hRetLe⟩
    simp [evalMirBody, downstreamCheckBoundBody, hCallRet, hRetLe']

/-- Module-invariant composition (`LIB-07`, `LIB-08`): using
`BoundedCounter.Valid` from `UpstreamCrate`, `downstreamCheckBoundBody` is
guaranteed to return a value `≤ 2000` without exposing `BoundedCounter`'s
internal representation invariant directly at the call site. -/
theorem verify_downstream_counter_double (env : CallEnv)
    (hAbs : CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract)
    (c : BoundedCounter) (hc : c.Valid) :
    ∃ ret,
      evalMirBody env downstreamCheckBoundBody c.val c.val = .returns ret ∧
      ret ≤ 2000 := by
  have hSat := verify_downstream_via_abstract_spec env hAbs
  exact hSat.2 c.val c.val (BoundedCounter.valid_le_1000 hc)

/-!
### Path 2: Direct Dependency MIR Inspection (`LIB-03`, `LIB-04`, `LIB-05`)
-/

/-- Downstream function body that calls `upstream_math::add_bounded(x, x)`,
asserts that the returned sum is even (`v % 2 == 0`), and returns `v / 2`. -/
def downstreamHalveEvenBody : MirBody :=
  .callDupAndHalveEven addBoundedId

/-- Downstream contract for `downstreamHalveEvenBody`: for `x ≤ 1000`, returns
`ret = x` without trapping. -/
def downstreamHalveEvenContract : FnContract where
  Pre x _ := x ≤ 1000
  Post x _ ret := ret = x

/-- Counterexample environment that satisfies
`UpstreamCrate.upstreamWeakContract` (`ret ≤ 2000`) by always returning the odd
number `1`. -/
def oddMockEnv : CallEnv :=
  fun _ _ _ => .returns 1

/-- Proof that `oddMockEnv` satisfies `UpstreamCrate`'s published abstract
specification (`upstreamWeakContract`), yet causes `downstreamHalveEvenBody` to
trap on `x = 1`.

This establishes that `upstreamWeakContract` is mathematically insufficient to
verify `downstreamHalveEvenBody`. -/
theorem weak_contract_insufficient_for_halve_even :
    CalleeSatisfiesAbstractSpec oddMockEnv addBoundedId upstreamWeakContract ∧
    evalMirBody oddMockEnv downstreamHalveEvenBody 1 1 = .traps := by
  refine ⟨⟨fun _ _ => by simp [oddMockEnv],
           fun _ _ _ => ⟨1, rfl, show 1 ≤ 2000 by decide⟩⟩,
          rfl⟩

/-- Stronger contract formulated locally by `DownstreamCrate` (`LIB-04`):
specifies the exact sum `ret = x + y` when `x ≤ 1000 ∧ y ≤ 1000`. -/
def downstreamExactAddContract : FnContract where
  Pre x y := x ≤ 1000 ∧ y ≤ 1000
  Post x y ret := ret = x + y

/-- Direct dependency MIR inspection (`LIB-03`, `LIB-04`, `LIB-05`):
`DownstreamCrate` inspects `UpstreamCrate.addBoundedBody` directly—without
modifying or forking `UpstreamCrate`—to prove that `addBoundedBody` satisfies
the stronger `downstreamExactAddContract`. -/
theorem downstream_strengthened_upstream_exact (env : CallEnv) :
    SatisfiesContract env addBoundedBody downstreamExactAddContract := by
  refine ⟨(addBoundedBody_satisfies_weak env).1, fun x y ⟨hx, hy⟩ => ?_⟩
  refine ⟨x + y, ?_, rfl⟩
  simp [evalMirBody, addBoundedBody, hx, hy]

/-- Downstream verification via direct MIR inspection (`LIB-03`, `LIB-05`):
using `downstream_strengthened_upstream_exact`, `DownstreamCrate` verifies
`downstreamHalveEvenBody` (`ret = x` when `x ≤ 1000`). -/
theorem verify_downstream_halve_even_via_mir_inspection (env : CallEnv)
    (hBind : ∀ x y, env addBoundedId x y = evalMirBody env addBoundedBody x y) :
    SatisfiesContract
      env downstreamHalveEvenBody downstreamHalveEvenContract := by
  have hExact := downstream_strengthened_upstream_exact env
  refine ⟨fun x y => ?_, fun x y hx => ?_⟩
  · simp only [evalMirBody, downstreamHalveEvenBody]
    have hNoUB := hExact.1 x x
    rw [← hBind x x] at hNoUB
    cases hOut : env addBoundedId x x with
    | returns v =>
      by_cases hv : (v % 2 == 0) = true <;> simp [hv]
    | traps => simp
    | goesWrong => exact False.elim (hNoUB hOut)
  · have hPre : downstreamExactAddContract.Pre x x := ⟨hx, hx⟩
    rcases hExact.2 x x hPre with ⟨ret, hBodyRet, hRetEq⟩
    have hCallRet : env addBoundedId x x = .returns (x + x) := by
      rw [hBind x x, hBodyRet, hRetEq]
    refine ⟨x, ?_, rfl⟩
    have hEven : ((x + x) % 2 == 0) = true := by
      simp [Nat.add_mod]
      omega
    have hHalf : (x + x) / 2 = x := by omega
    simp [evalMirBody, downstreamHalveEvenBody, hCallRet, hEven, hHalf]

/-!
### Path 3: Transitive TCB and Subject Propagation (`OD-08`, `LIB-09`, `LIB-10`)
-/

/-- Captured compiler and artifact identity for `downstream_app` (`LIB-10`),
compiled with the same `rustcCommit` and `targetTriple` as `upstream_math`. -/
def downstreamSubject : SubjectIdentity where
  crateName := "downstream_app"
  crateVersion := "0.1.0"
  rustcCommit := "rustc-1.88.0-nightly-2026-04-01"
  targetTriple := "x86_64-unknown-linux-gnu"
  mirSha256 :=
    "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

/-- Proof that `upstreamSubject` and `downstreamSubject` satisfy
`CompatibleSubject` (`LIB-10`). -/
theorem upstream_downstream_compatible :
    CompatibleSubject upstreamSubject downstreamSubject :=
  ⟨rfl, rfl⟩

/-- Clean DAG composition (`LIB-09`, `LIB-10`): composing `upstreamCleanReceipt`
with `downstream_app`'s local `[.rustcLowering]` TCB produces a valid
`VerificationResult` under `defaultTrustPolicy` (`VettedOnly`). -/
theorem downstream_clean_dag_verified (env : CallEnv)
    (hBind : ∀ x y, env addBoundedId x y = evalMirBody env addBoundedBody x y) :
    VerificationResult
      defaultTrustPolicy
      ((upstreamCleanReceipt env).transitiveTcb ++ [.rustcLowering])
      []
      (CompatibleSubject (upstreamCleanReceipt env).subject downstreamSubject ∧
       SatisfiesContract
         env downstreamCheckBoundBody downstreamCheckBoundContract) := by
  exact composeCrateVerification
    defaultTrustPolicy
    (upstreamCleanReceipt env)
    downstreamSubject
    [.rustcLowering]
    []
    []
    (SatisfiesContract
      env downstreamCheckBoundBody downstreamCheckBoundContract)
    upstream_downstream_compatible
    (verify_upstreamCleanReceipt env)
    ⟨trivial, trivial⟩
    (fun _ hUpSat _ =>
      verify_downstream_via_abstract_spec env
        (calleeSatisfiesAbstractSpec_of_body env addBoundedId addBoundedBody
          upstreamWeakContract hBind hUpSat))

/-- Fail-closed rejection of tainted upstream TCB (`LIB-09`): when an upstream
dependency's receipt includes `.unsafeAxiom "upstream_raw_ptr_sound"`, the
merged transitive TCB `(taintedUpstreamReceipt env).transitiveTcb ++
[.rustcLowering]` is mechanically rejected by `defaultTrustPolicy`. -/
theorem downstream_tainted_upstream_rejected_by_default_policy (env : CallEnv) :
    ¬ AllHold
        (((taintedUpstreamReceipt env).transitiveTcb ++
          [TCBItem.rustcLowering]).map defaultTrustPolicy.isAllowed) := by
  intro hAll
  rcases hAll with ⟨_, hUnsafeAllowed, _⟩
  exact hUnsafeAllowed

/-- Explicit downstream trust policy opting into `"upstream_raw_ptr_sound"`
(`LIB-09`). -/
def allowUpstreamUnsafePolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering => True
    | .candidateFeature _ => False
    | .unsafeAxiom name => name = "upstream_raw_ptr_sound"

/-- Explicit opt-in acceptance of tainted upstream TCB (`LIB-09`): when the
downstream verification target explicitly adopts `allowUpstreamUnsafePolicy` and
lists the upstream soundness assumption in `assumptions`, composition
succeeds. -/
theorem downstream_tainted_upstream_accepted_with_explicit_policy
    (env : CallEnv)
    (UpstreamRawPtrSound : Prop)
    (hBind : ∀ x y, env addBoundedId x y = evalMirBody env addBoundedBody x y) :
    VerificationResult
      allowUpstreamUnsafePolicy
      ((taintedUpstreamReceipt env).transitiveTcb ++ [.rustcLowering])
      [UpstreamRawPtrSound]
      (CompatibleSubject
        (taintedUpstreamReceipt env).subject downstreamSubject ∧
       SatisfiesContract
         env downstreamCheckBoundBody downstreamCheckBoundContract) := by
  have hTaintedUpVer :
      VerificationResult
        allowUpstreamUnsafePolicy
        (taintedUpstreamReceipt env).transitiveTcb
        [UpstreamRawPtrSound]
        (taintedUpstreamReceipt env).claim :=
    ⟨⟨trivial, rfl, trivial⟩, fun _ => addBoundedBody_satisfies_weak env⟩
  exact composeCrateVerification
    allowUpstreamUnsafePolicy
    (taintedUpstreamReceipt env)
    downstreamSubject
    [.rustcLowering]
    [UpstreamRawPtrSound]
    []
    (SatisfiesContract
      env downstreamCheckBoundBody downstreamCheckBoundContract)
    upstream_downstream_compatible
    hTaintedUpVer
    ⟨trivial, trivial⟩
    (fun _ hUpSat _ =>
      verify_downstream_via_abstract_spec env
        (calleeSatisfiesAbstractSpec_of_body env addBoundedId addBoundedBody
          upstreamWeakContract hBind hUpSat))

/-- Subject identity with a mismatched target triple
(`aarch64-unknown-linux-gnu` instead of `x86_64-unknown-linux-gnu`). -/
def incompatibleArm64Subject : SubjectIdentity where
  crateName := "downstream_arm64"
  crateVersion := "0.1.0"
  rustcCommit := "rustc-1.88.0-nightly-2026-04-01"
  targetTriple := "aarch64-unknown-linux-gnu"
  mirSha256 :=
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"

/-- Fail-closed rejection of incompatible target triple (`LIB-10`): receipts
captured for different target triples fail `CompatibleSubject`. -/
theorem downstream_incompatible_target_rejected :
    ¬ CompatibleSubject upstreamSubject incompatibleArm64Subject := by
  intro ⟨_, hTarget⟩
  revert hTarget
  decide

end DownstreamCrate

/-!
## 4. `#guard_msgs` Signature and Kernel Axiom Verification Suite
-/

namespace Tests

open UpstreamCrate
open DownstreamCrate

/--
info: CrossCrateProbe.DownstreamCrate.verify_downstream_via_abstract_spec (env : CallEnv)
  (hAbs : CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract) :
  SatisfiesContract env downstreamCheckBoundBody downstreamCheckBoundContract
-/
#guard_msgs in
#check verify_downstream_via_abstract_spec

/--
info: CrossCrateProbe.DownstreamCrate.verify_downstream_halve_even_via_mir_inspection (env : CallEnv)
  (hBind : ∀ (x y : Nat), env addBoundedId x y = evalMirBody env addBoundedBody x y) :
  SatisfiesContract env downstreamHalveEvenBody downstreamHalveEvenContract
-/
#guard_msgs in
#check verify_downstream_halve_even_via_mir_inspection

/--
info: CrossCrateProbe.DownstreamCrate.downstream_tainted_upstream_rejected_by_default_policy (env : CallEnv) :
  ¬AllHold
      (List.map defaultTrustPolicy.isAllowed ((taintedUpstreamReceipt env).transitiveTcb ++ [TCBItem.rustcLowering]))
-/
#guard_msgs in
#check downstream_tainted_upstream_rejected_by_default_policy

/--
info: CrossCrateProbe.DownstreamCrate.downstream_incompatible_target_rejected :
  ¬CompatibleSubject upstreamSubject incompatibleArm64Subject
-/
#guard_msgs in
#check downstream_incompatible_target_rejected

/--
info: 'CrossCrateProbe.DownstreamCrate.verify_downstream_via_abstract_spec' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms verify_downstream_via_abstract_spec

/--
info: 'CrossCrateProbe.DownstreamCrate.verify_downstream_halve_even_via_mir_inspection' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms verify_downstream_halve_even_via_mir_inspection

/--
info: 'CrossCrateProbe.DownstreamCrate.downstream_clean_dag_verified' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms downstream_clean_dag_verified

/--
info: 'CrossCrateProbe.DownstreamCrate.downstream_tainted_upstream_rejected_by_default_policy' does not depend on any axioms
-/
#guard_msgs in
#print axioms downstream_tainted_upstream_rejected_by_default_policy

/--
info: 'CrossCrateProbe.DownstreamCrate.downstream_incompatible_target_rejected' does not depend on any axioms
-/
#guard_msgs in
#print axioms downstream_incompatible_target_rejected

end Tests

end CrossCrateProbe

end
