# Substitution-Stable Checks: Definition-Site Verification vs. Post-Monomorphization Assertions and Generic IR Capture

## Summary

Namespace `Toy.SubstStable`; Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only (no Mathlib). Every declaration in the package—all 17 main theorems in `lean/Toy/SubstStable/Main.lean` together with all supporting definitions, characterization lemmas, definition examples, canonical tightness counterexamples, non-vacuity witnesses, and positive controls (`819` declarations total)—is kernel-checked with zero `sorry` and depends at most on `{propext, Classical.choice, Quot.sound}`; Lean statement blocks below are verbatim `-- path.lean:A-B` source quotes with proof bodies omitted (`:= by …`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

- **R1 (`R1-subst-stability-characterization`):** For every semantic bound B and closed-type property Φ: (1) a Boolean definition-site check C over open types that is both sound (DefCheckSound B Φ C) and instance-complete (DefCheckComplete B Φ C) exists if and only if Φ is substitution-stable relative to B (SubstStable B Φ); and (2) for any instantiation-witness map w satisfying HasInstWitness B w, the witness-evaluating check witnessDefCheck Φ w (defined without Classical.choice, and executable whenever Φ and w are computable) is both sound and instance-complete relative to B if and only if SubstStable B Φ holds.
- **R2 (`R2-instability-forces-incompleteness`):** If C is sound relative to B for Φ (DefCheckSound B Φ C) and an open type t admits two B-conforming closed instances τ1 (with Φ τ1 = true) and τ2 (with Φ τ2 = false), then C rejects t (C t = false) and fails instance-completeness (¬ DefCheckComplete B Φ C); under unbounded parameters, SubstStable unbounded Φ holds if and only if Φ is constant across all closed types, so for every byte threshold k, sizeLe k is not substitution-stable under unbounded and every unbounded-sound definition-site check C for sizeLe k fails DefCheckComplete unbounded (sizeLe k) C.
- **R3 (`R3-packed-align-empty-bounds-unsound`):** Under emptyBounds (where every substituted parameter and associated type is itself packedNoAlignWf, with no noAlign restrictions), the syntactic check naiveDefPackedCheck accepts both Packed<T0> (.packed 1 (.tparam 0)) and Packed<<T0 as Trait0>::Assoc> (.packed 1 (.proj 0 (.tparam 0))), yet emptyBounds-conforming instantiations (substAlign16 and sampleAssoc with substU8) normalize both to .packed 1 align16U8, which violates packedNoAlignWf; hence naiveDefPackedCheck is not DefCheckSound and packedNoAlignWf is not SubstStable under emptyBounds.
- **R4 (`R4-packed-align-post-mono-and-bounded-sound`):** For every associated-type environment A, substitution σ, and open type t, the definitional unfolding of PmeCheck.packedWf t after instantiation (evalPmeCheck A σ (.packedWf t) = true) holds if and only if instTy A σ t produces a closed type τ with packedNoAlignWf τ = true; at the definition site, for every declared bound d, open type t, environment A, substitution σ, and closed type τ, if boundedDefPackedCheck d t = true, DeclBounds.sat d A σ holds, and instTy A σ t = some τ, then packedNoAlignWf τ = true.
- **R5 (`R5-ctor-const-indices-total-and-decidable`):** For every const-index expression e satisfying isCtorIdx e = true (acyclic constructor and parameter terms over canonical natural scalars, with no add, sub, or div nodes), instantiation-time evaluation in evalIdx never fails (IdxTotal e); and for any two index expressions e1 and e2 with isCtorIdx e1 = true and isCtorIdx e2 = true, semantic equality across all natural parameter valuations (IdxSemEq e1 e2) holds if and only if rigid syntactic AST equality e1 = e2 holds, which is decidable via DecidableEq IdxTerm.
- **R6 (`R6-const-index-rigid-eq-and-partial-op-cex`):** (1) The total index expressions idxAddN1 (N + 1) and idxAdd1N (1 + N) satisfy IdxSemEq yet fail rigid syntactic AST equality (decide (idxAddN1 = idxAdd1N) = false); (2) under checked natural subtraction, idxSub1 (N - 1) evaluates to some (.nat 0), instantiates [u8; N - 1] to [u8; 0], and passes collectAndCheck true progSub1 [⟨0, [], [1]⟩] 2 at N = 1, yet evaluates to none, fails instTy, and fails collectAndCheck true progSub1 [⟨0, [], [0]⟩] 2 with .pmeError ⟨0, [], [0]⟩ at N = 0; and (3) under checked floor division, idxDiv0 (16 / N) evaluates to some (.nat 8) and passes collectAndCheck true progDiv0 [⟨0, [], [2]⟩] 2 at N = 2, yet evaluates to none and fails collectAndCheck true progDiv0 [⟨0, [], [0]⟩] 2 with .pmeError ⟨0, [], [0]⟩ at N = 0.
- **R7 (`R7-pme-collection-soundness`):** For every mode includeMentioned, crate program P, root list roots, fuel, and output list T: (1) if collectAndCheck includeMentioned P roots fuel = .ok T, then T contains an instance k if and only if k is collector-reachable via monoEdges (Reachable includeMentioned P roots k, which truncates outgoing call edges at localMir = false items), T includes every used-reachable instance (Reachable false P roots k), and every k in T satisfies passesLocalPme P k = true; and (2) if in addition every key in T has locally available MIR (AllLocalMir P T), then IntrinsicReachable includeMentioned P roots k (full fn.body call-graph reachability via intrinsicEdges) coincides with Reachable includeMentioned P roots k for every k, and every intrinsically reachable instance k satisfies passesIntrinsicPme P k = true.
- **R8 (`R8-pme-collection-dead-branch-unreached-and-external-cex`):** (1) On progDeadBranch (where fn 0 mentions fn 1::<u8> inside deadBranch), used-only collection (includeMentioned = false) returns .ok [⟨0, [], []⟩] while mentioned-mode collection (includeMentioned = true) reports .pmeError ⟨1, [tyU8], []⟩; (2) on progUnreachedLib, mentioned-mode collection from ⟨0, [], []⟩ returns .ok [⟨0, [], []⟩] with AllLocalMir, yet the unreached instance ⟨1, [tyU8], []⟩ is neither IntrinsicReachable nor Reachable and violates passesIntrinsicPme; (3) on progExtHole (where fn 1 has localMir = false), mentioned-mode collection returns .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] with passesLocalPme = true while passesIntrinsicPme is false on ⟨1, [tyU8], []⟩; and (4) on progExtCallbackHole (where local fn 0 calls external fn 1 which calls back into local fn 2), mentioned-mode collection returns .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] while local instance ⟨2, [tyU8], []⟩ (isLocalFn = true) is IntrinsicReachable, not Reachable, and violates passesIntrinsicPme.
- **R9 (`R9-generic-capture-invariance-and-pme-gap`):** (1) As an elementary corollary of DefCheckSound and R1, for every bound B, property Φ, and check C satisfying DefCheckSound B Φ C, Φ evaluates to true (and hence Φ τ1 = Φ τ2) across all B-conforming closed instances of every C-accepted open type t, and if C also satisfies DefCheckComplete B Φ C then SubstStable B Φ holds globally; (2) for every B_src, B_assumed, Φ, C, generic function fn, and openTarget, BoundEntails B_src B_assumed transfers DefCheckSound B_assumed Φ C to DefCheckSound B_src Φ C, and when BoundEntails (DeclBounds.sat fn.bounds) B_assumed and C openTarget = true hold, GenericBodySafeUnconditional fn openTarget Φ holds; (3) assuming an unstated bound (FullNoAlignBound when source declares emptyBounds) makes naiveDefPackedCheck on Packed<T0> violate both DefCheckSound and GenericBodySafeUnconditional for packedNoAlignWf at substAlign16; and (4) PME-guarded fnTransmuteLike on (.prod (.tparam 0) (.tparam 1)) satisfies GenericBodySafeUnderPme for eqProdByteSize yet violates GenericBodySafeUnconditional without a PME-admission precondition.
- **R10 (`R10-monomorphic-capture-post-mono-soundness`):** (1) As a definitional List.all equivalence for verifier-executed post-capture checking, for every associated-type environment A, closed-type property Φ (whether substitution-stable or not), target map targetOf, and captured monomorphic instance list T, checkMonoTarget A Φ targetOf T = true holds if and only if MonoCaptureCertifiedOn A Φ targetOf T holds; and (2) for every mode includeMentioned, crate program P, root list roots, fuel, output list T, and target map targetOf, when collectAndCheck includeMentioned P roots fuel = .ok T, AllLocalMir P T holds, and HasPackedPmeGuard P targetOf T holds, MonoCaptureCertifiedOn P.assoc packedNoAlignWf targetOf T holds.

See **Boundaries** below for package-wide non-claims and escape hatches.

## Applicability

**Scope and model–system relation.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier. Among the subjects recorded in `REPORT.json`, the Lean 4 toolchain (`leanprover/lean4` `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, core Lean without Mathlib) is the proof-assistant kernel checking `Toy.SubstStable`; the pinned revisions of `rust-lang/rust`, `rust-lang/reference`, `rust-lang/rfcs`, and `google/zerocopy` supply documented real-system behavior compared in separate `derived (modeling bridge)` paragraphs; and the academic publications and Isabelle/HOL formalizations supply prior-art foundations and verification-architecture comparisons.

**Model fidelity and degenerate edges.**
- **Const indices and arithmetic conventions.** Const parameters range over unbounded natural numbers (`γ : Nat → Nat`), and canonical values (`CVal`) are natural scalars or finite acyclic constructor trees. Function-call const arguments (`evalNatArgs` in `GenStmt.call`) accept `CVal.nat` scalars and reject `CVal.ctor` values with `none` (`evalNatArgs_neg_ctor`, triggering `CollectRes.pmeError`). `evalIdx` implements **checked natural subtraction** (`sub` returns `some (.nat (x - y))` when `y ≤ x` and `none` when `x < y`, rather than Lean's total truncating subtraction `0 - 1 = 0`) and **checked floor division** (`div` returns `some (.nat (x / y))` when `0 < y` and `none` when `y = 0`, rather than Lean's `x / 0 = 0`). Fixed-width integer overflow on `add` (such as `usize::MAX + 1`) is not modeled.
- **Layouts, unpadded `byteSize`, and degenerate parameters.** `ClosedTy.byteSize` and `ClosedTy.effAlign` operate on arbitrary naturals (`sz = 0`, `al = 0`, `k = 0`, `n = 0` are permitted without guards: `min 0 al = 0`, `max 0 al = al`, and `.arr elem (.nat 0)` has `byteSize = 0`, `byteSize_neg_arr_zero`). `ClosedTy.byteSize` models **unpadded payload sums**—omitting inter-field alignment padding (`(ClosedTy.prod tyU8 tyU32).byteSize = 5`) and `align(n)` size rounding (`align16U8.byteSize = 1` despite `align16U8.effAlign = 16`, `byteSize_ignores_align_and_padding`)—and assigns unit count `1` to constructor-indexed arrays (`.arr elem (.ctor _ _)` has `byteSize = elem.byteSize`, `byteSize_pos_arr_ctor`, ignoring constructor arguments). `packedNoAlignWf` is purely structural over `packed` and `align` representation wrappers: `.packed 1 (.arr align16U8 (.nat 0))` has `packedNoAlignWf = false` even at array length `0` (`packedNoAlignWf_neg_zero_len_arr`), `.packed 1 tyU64` has `packedNoAlignWf = true` because `tyU64` is naturally aligned (`packedNoAlignWf_pos_natural_u64`), and associated-type projections `.proj tr arg` erase `arg` after `AssocEnv` lookup without checking source-level well-formedness of `arg` (`boundedDefPackedCheck_pos_erased_proj_arg`).
- **Collection and IR capture.** `CrateProg` models per-crate generic functions with `localMir : Bool`, header-level `pmeAsserts : List PmeCheck`, and bodies built from `skip`, `seq`, `call`, and `deadBranch`. Collector-visible reachability (`Reachable`) steps along `monoEdges` (which returns `some []` when `localMir = false`), whereas `IntrinsicReachable` steps along `intrinsicEdges` (`fn.body` regardless of `localMir`); the two coincide under `AllLocalMir P T` (`intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir`) and diverge when an external function calls back into a local function (`cex_external_callback_local_pme_hole`). Out-of-range parameter indices in `substOfKey` default to `tyU8` (`.base 1 1`) and `0` (`substOfKey_neg_out_of_bounds_default`). Polymorphic recursion, drop/clone shim synthesis, and runtime operational traces are omitted here and treated in the sibling corpus packages cited in **Boundaries** and the result cards below (`monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets` and `packed-field-projections-aligned-staging-and-alignment-check-completeness-across-shims`).

### Definitions

Every package-local `def` or `abbrev` value/predicate appearing directly in any card's verbatim `lean` theorem statement is accounted for below:

- `isCtorIdx` — tests: isCtorIdx_pos_nested_ctor, isCtorIdx_neg_add — admits only .lit, .cparam, and .ctor trees while rejecting even total .add nodes
- `evalIdx` — tests: evalIdx_pos_checked_sub, evalIdx_neg_underflow_sub — checked natural subtraction (none when x < y) and checked floor division (none when y = 0), rather than truncating arithmetic
- `IdxSemEq` — tests: idxSemEq_pos_comm_add, idxSemEq_neg_partial_sub — requires identical Option CVal outcomes (including none vs. some agreement) across every valuation γ : Nat → Nat
- `IdxTotal` — characterized: idxTotal_iff_exists_cval
- `sizeLe` — characterized: sizeLe_iff_byteSize_le
- `eqProdByteSize` — characterized: eqProdByteSize_iff_exists_prod
- `packedNoAlignWf` — tests: packedNoAlignWf_pos_outer_align, packedNoAlignWf_neg_inner_align — forbids transitive align(n) wrappers inside packed(k) while permitting align(n) outside packed(k) and naturally aligned scalars
- `instTy` — tests: instTy_pos_proj_and_arr, instTy_neg_failed_idx — substitutes parameters, normalizes projections via AssocEnv, and propagates none from unresolved projections or failed const-index evaluations
- `unbounded` — transparent
- `BoundEntails` — tests: boundEntails_pos_full_to_empty, boundEntails_neg_empty_to_full — pointwise implication ∀ A σ, B1 A σ → B2 A σ from source bound to assumed bound
- `DefCheckSound` — characterized: defCheckSound_iff_allInstSat
- `DefCheckComplete` — characterized: defCheckComplete_iff_exists_inst
- `SubstStable` — characterized: substStable_iff_allInst_const
- `HasInstWitness` — characterized: hasInstWitness_iff_forall_inst
- `witnessDefCheck` — characterized: witnessDefCheck_eq_true_iff
- `emptyBounds` — transparent
- `DeclBounds.sat` — tests: declBoundsSat_pos_selective, declBoundsSat_neg_param_has_align — requires packedNoAlignWf on all substituted and associated types plus hasAlignWrapper = false on listed paramNoAlign parameters and globally across all AssocEnv entries of listed projNoAlign traits
- `FullNoAlignBound` — tests: fullNoAlignBound_pos_scalars, fullNoAlignBound_neg_align_subst — requires packedNoAlignWf = true and hasAlignWrapper = false across every type parameter and associated-type entry
- `naiveDefPackedCheck` — tests: naiveDefPackedCheck_pos_tparam, naiveDefPackedCheck_neg_literal_align — inspects only literal .align nodes in the open AST and optimistically accepts .tparam and .proj inside .packed without inspecting .proj self-arguments
- `boundedDefPackedCheck` — tests: boundedDefPackedCheck_pos_bounded_param, boundedDefPackedCheck_neg_unbounded_param — rejects .tparam and .proj inside .packed unless listed in paramNoAlign/projNoAlign, without inspecting .proj self-arguments at any AST position
- `evalPmeCheck` — tests: evalPmeCheck_pos_sizeEq, evalPmeCheck_neg_sizeMismatch — evaluates post-monomorphization assertions on (A, σ), returning false whenever instTy or evalIdx returns none
- `isLocalFn` — tests: isLocalFn_pos, isLocalFn_neg_external — returns fn.localMir for in-range function ids and false for undefined fnId
- `AllLocalMir` — characterized: allLocalMir_iff_list_all
- `passesLocalPme` — tests: passesLocalPme_pos_external_mir, passesLocalPme_neg_local_fail — returns true for external items with localMir = false (modeling skipped local codegen/PME inspection) and false for undefined fnId
- `passesIntrinsicPme` — tests: passesIntrinsicPme_pos_valid, passesIntrinsicPme_neg_external_fail — evaluates fn.pmeAsserts regardless of localMir, returning false for undefined fnId
- `collectAndCheck` — tests: collectAndCheck_pos_valid, cex_pme_collection_not_ok — runs fuel-bounded worklist collection from empty visited set, aborting with pmeError on local PME or edge-evaluation failure
- `GenericBodySafeUnconditional` — tests: genericBodySafeUnconditional_pos_bounded, genericBodySafeUnconditional_neg_emptyBounds — quantifies over all DeclBounds.sat instantiations without assuming fn.pmeAsserts hold
- `GenericBodySafeUnderPme` — tests: genericBodySafeUnderPme_pos_sizeEq, genericBodySafeUnderPme_neg_unguarded — restricts instantiations to those satisfying both DeclBounds.sat and fn.pmeAsserts
- `checkMonoTarget` — tests: checkMonoTarget_pos_pair, checkMonoTarget_neg_bad_inst — evaluates Φ on instTy of targetOf k.fnId for each k ∈ T, returning false on missing targets or failed instantiations
- `MonoCaptureCertifiedOn` — tests: monoCaptureCertifiedOn_pos_pair, monoCaptureCertifiedOn_neg_missing_target — requires each k ∈ T to resolve targetOf and instTy to some τ with Φ τ = true
- `HasPackedPmeGuard` — characterized: hasPackedPmeGuard_iff_list_all
- `tyU8` — transparent
- `align16U8` — transparent
- `emptyAssoc` — transparent
- `sampleAssoc` — transparent
- `substU8` — transparent
- `substAlign16` — transparent
- `idxAddN1` — transparent
- `idxAdd1N` — transparent
- `idxSub1` — transparent
- `idxDiv0` — transparent
- `progSub1` — transparent
- `progDiv0` — transparent
- `progDeadBranch` — transparent
- `progUnreachedLib` — transparent
- `progExtHole` — transparent
- `progExtCallbackHole` — transparent
- `fnTransmuteLike` — transparent

## Findings

### 1. Core syntax and semantic definitions (`Basic.lean`)

```lean
-- lean/Toy/SubstStable/Basic.lean:14-16
inductive CVal where
  | nat (n : Nat)
  | ctor (tag : Nat) (args : List CVal)

-- lean/Toy/SubstStable/Basic.lean:48-54
inductive IdxTerm where
  | lit (n : Nat)
  | cparam (i : Nat)
  | ctor (tag : Nat) (args : List IdxTerm)
  | add (a b : IdxTerm)
  | sub (a b : IdxTerm)
  | div (a b : IdxTerm)

-- lean/Toy/SubstStable/Basic.lean:109-115
def isCtorIdx : IdxTerm → Bool
  | .lit _ => true
  | .cparam _ => true
  | .ctor _ args => isCtorIdxList args
  | .add _ _ => false
  | .sub _ _ => false
  | .div _ _ => false

-- lean/Toy/SubstStable/Basic.lean:118-120
def isCtorIdxList : List IdxTerm → Bool
  | [] => true
  | e :: es => isCtorIdx e && isCtorIdxList es

-- lean/Toy/SubstStable/Basic.lean:128-143
def evalIdx (γ : Nat → Nat) : IdxTerm → Option CVal
  | .lit n => some (.nat n)
  | .cparam i => some (.nat (γ i))
  | .ctor tag args => (evalIdxList γ args).map (.ctor tag)
  | .add a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => some (.nat (x + y))
      | _, _ => none
  | .sub a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => if y ≤ x then some (.nat (x - y)) else none
      | _, _ => none
  | .div a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => if 0 < y then some (.nat (x / y)) else none
      | _, _ => none

-- lean/Toy/SubstStable/Basic.lean:146-151
def evalIdxList (γ : Nat → Nat) : List IdxTerm → Option (List CVal)
  | [] => some []
  | e :: es =>
      match evalIdx γ e, evalIdxList γ es with
      | some v, some vs => some (v :: vs)
      | _, _ => none

-- lean/Toy/SubstStable/Basic.lean:156-157
def IdxSemEq (e1 e2 : IdxTerm) : Prop :=
  ∀ γ : Nat → Nat, evalIdx γ e1 = evalIdx γ e2

-- lean/Toy/SubstStable/Basic.lean:160-161
def IdxTotal (e : IdxTerm) : Prop :=
  ∀ γ : Nat → Nat, (evalIdx γ e).isSome = true

-- lean/Toy/SubstStable/Basic.lean:167-173
inductive ClosedTy where
  | base (sz al : Nat)
  | prod (a b : ClosedTy)
  | packed (k : Nat) (inner : ClosedTy)
  | align (n : Nat) (inner : ClosedTy)
  | arr (elem : ClosedTy) (idx : CVal)
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:177-185
inductive OpenTy where
  | base (sz al : Nat)
  | tparam (i : Nat)
  | prod (a b : OpenTy)
  | packed (k : Nat) (inner : OpenTy)
  | align (n : Nat) (inner : OpenTy)
  | arr (elem : OpenTy) (idx : IdxTerm)
  | proj (tr : Nat) (arg : OpenTy)
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:191-197
def ClosedTy.byteSize : ClosedTy → Nat
  | .base sz _ => sz
  | .prod a b => a.byteSize + b.byteSize
  | .packed _ inner => inner.byteSize
  | .align _ inner => inner.byteSize
  | .arr elem (.nat n) => elem.byteSize * n
  | .arr elem (.ctor _ _) => elem.byteSize

-- lean/Toy/SubstStable/Basic.lean:201-206
def ClosedTy.effAlign : ClosedTy → Nat
  | .base _ al => al
  | .prod a b => max a.effAlign b.effAlign
  | .packed k inner => min k inner.effAlign
  | .align n inner => max n inner.effAlign
  | .arr elem _ => elem.effAlign

-- lean/Toy/SubstStable/Basic.lean:209-210
def sizeLe (k : Nat) (τ : ClosedTy) : Bool :=
  decide (τ.byteSize ≤ k)

-- lean/Toy/SubstStable/Basic.lean:213-215
def eqProdByteSize : ClosedTy → Bool
  | .prod a b => decide (a.byteSize = b.byteSize)
  | _ => false

-- lean/Toy/SubstStable/Basic.lean:218-223
def hasAlignWrapper : ClosedTy → Bool
  | .base _ _ => false
  | .prod a b => hasAlignWrapper a || hasAlignWrapper b
  | .packed _ inner => hasAlignWrapper inner
  | .align _ _ => true
  | .arr elem _ => hasAlignWrapper elem

-- lean/Toy/SubstStable/Basic.lean:227-232
def packedNoAlignWf : ClosedTy → Bool
  | .base _ _ => true
  | .prod a b => packedNoAlignWf a && packedNoAlignWf b
  | .packed _ inner => (!hasAlignWrapper inner) && packedNoAlignWf inner
  | .align _ inner => packedNoAlignWf inner
  | .arr elem _ => packedNoAlignWf elem

-- lean/Toy/SubstStable/Basic.lean:238
abbrev AssocEnv : Type := Nat → ClosedTy → Option ClosedTy

-- lean/Toy/SubstStable/Basic.lean:241-243
structure Subst where
  ty : Nat → ClosedTy
  cnst : Nat → Nat

-- lean/Toy/SubstStable/Basic.lean:248-264
def instTy (A : AssocEnv) (σ : Subst) : OpenTy → Option ClosedTy
  | .base sz al => some (.base sz al)
  | .tparam i => some (σ.ty i)
  | .prod a b =>
      match instTy A σ a, instTy A σ b with
      | some a', some b' => some (.prod a' b')
      | _, _ => none
  | .packed k inner => (instTy A σ inner).map (.packed k)
  | .align n inner => (instTy A σ inner).map (.align n)
  | .arr elem idx =>
      match instTy A σ elem, evalIdx σ.cnst idx with
      | some elem', some v => some (.arr elem' v)
      | _, _ => none
  | .proj tr arg =>
      match instTy A σ arg with
      | some arg' => A tr arg'
      | none => none

-- lean/Toy/SubstStable/Basic.lean:267
abbrev BoundPred : Type := AssocEnv → Subst → Prop

-- lean/Toy/SubstStable/Basic.lean:270
def unbounded : BoundPred := fun _ _ => True

-- lean/Toy/SubstStable/Basic.lean:273-274
def BoundEntails (B1 B2 : BoundPred) : Prop :=
  ∀ A σ, B1 A σ → B2 A σ

-- lean/Toy/SubstStable/Basic.lean:278-279
def DefCheckSound (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) : Prop :=
  ∀ t A σ τ, C t = true → B A σ → instTy A σ t = some τ → Φ τ = true

-- lean/Toy/SubstStable/Basic.lean:284-285
def DefCheckComplete (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) : Prop :=
  ∀ t A σ τ, B A σ → instTy A σ t = some τ → Φ τ = true → C t = true

-- lean/Toy/SubstStable/Basic.lean:288-289
def AllInstSat (B : BoundPred) (Φ : ClosedTy → Bool) (t : OpenTy) : Prop :=
  ∀ A σ τ, B A σ → instTy A σ t = some τ → Φ τ = true

-- lean/Toy/SubstStable/Basic.lean:293-297
def SubstStable (B : BoundPred) (Φ : ClosedTy → Bool) : Prop :=
  ∀ t A1 σ1 τ1 A2 σ2 τ2,
    B A1 σ1 → instTy A1 σ1 t = some τ1 →
    B A2 σ2 → instTy A2 σ2 t = some τ2 →
    Φ τ1 = Φ τ2

-- lean/Toy/SubstStable/Basic.lean:301-303
def HasInstWitness (B : BoundPred) (w : OpenTy → AssocEnv × Subst) : Prop :=
  ∀ t, (∃ A σ τ, B A σ ∧ instTy A σ t = some τ) →
    B (w t).1 (w t).2 ∧ (instTy (w t).1 (w t).2 t).isSome = true

-- lean/Toy/SubstStable/Basic.lean:307-310
def witnessDefCheck (Φ : ClosedTy → Bool) (w : OpenTy → AssocEnv × Subst) (t : OpenTy) : Bool :=
  match instTy (w t).1 (w t).2 t with
  | some τ => Φ τ
  | none => true

-- lean/Toy/SubstStable/Basic.lean:317-320
structure DeclBounds where
  paramNoAlign : List Nat
  projNoAlign : List Nat
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:324
def emptyBounds : DeclBounds := ⟨[], []⟩

-- lean/Toy/SubstStable/Basic.lean:330-334
def DeclBounds.sat (d : DeclBounds) (A : AssocEnv) (σ : Subst) : Prop :=
  (∀ i, packedNoAlignWf (σ.ty i) = true) ∧
  (∀ tr src rhs, A tr src = some rhs → packedNoAlignWf rhs = true) ∧
  (∀ i, i ∈ d.paramNoAlign → hasAlignWrapper (σ.ty i) = false) ∧
  (∀ tr, tr ∈ d.projNoAlign → ∀ τ rhs, A tr τ = some rhs → hasAlignWrapper rhs = false)

-- lean/Toy/SubstStable/Basic.lean:338-340
def FullNoAlignBound (A : AssocEnv) (σ : Subst) : Prop :=
  (∀ i, packedNoAlignWf (σ.ty i) = true ∧ hasAlignWrapper (σ.ty i) = false) ∧
  (∀ tr src rhs, A tr src = some rhs → packedNoAlignWf rhs = true ∧ hasAlignWrapper rhs = false)

-- lean/Toy/SubstStable/Basic.lean:344-345
def FixedConstNoAlignBound (A : AssocEnv) (σ : Subst) : Prop :=
  FullNoAlignBound A σ ∧ σ.cnst = fun _ => 0

-- lean/Toy/SubstStable/Basic.lean:348-349
def constZeroNoAlignWitness (_ : OpenTy) : AssocEnv × Subst :=
  (fun _ _ => some (.base 1 1), ⟨fun _ => .base 1 1, fun _ => 0⟩)

-- lean/Toy/SubstStable/Basic.lean:353-360
def naiveOpenHasAlign : OpenTy → Bool
  | .base _ _ => false
  | .tparam _ => false
  | .prod a b => naiveOpenHasAlign a || naiveOpenHasAlign b
  | .packed _ inner => naiveOpenHasAlign inner
  | .align _ _ => true
  | .arr elem _ => naiveOpenHasAlign elem
  | .proj _ _ => false

-- lean/Toy/SubstStable/Basic.lean:365-372
def naiveDefPackedCheck : OpenTy → Bool
  | .base _ _ => true
  | .tparam _ => true
  | .prod a b => naiveDefPackedCheck a && naiveDefPackedCheck b
  | .packed _ inner => (!naiveOpenHasAlign inner) && naiveDefPackedCheck inner
  | .align _ inner => naiveDefPackedCheck inner
  | .arr elem _ => naiveDefPackedCheck elem
  | .proj _ _ => true

-- lean/Toy/SubstStable/Basic.lean:378-385
def mayHaveAlignUnder (d : DeclBounds) : OpenTy → Bool
  | .base _ _ => false
  | .tparam i => !decide (i ∈ d.paramNoAlign)
  | .prod a b => mayHaveAlignUnder d a || mayHaveAlignUnder d b
  | .packed _ inner => mayHaveAlignUnder d inner
  | .align _ _ => true
  | .arr elem _ => mayHaveAlignUnder d elem
  | .proj tr _ => !decide (tr ∈ d.projNoAlign)

-- lean/Toy/SubstStable/Basic.lean:391-398
def boundedDefPackedCheck (d : DeclBounds) : OpenTy → Bool
  | .base _ _ => true
  | .tparam _ => true
  | .prod a b => boundedDefPackedCheck d a && boundedDefPackedCheck d b
  | .packed _ inner => (!mayHaveAlignUnder d inner) && boundedDefPackedCheck d inner
  | .align _ inner => boundedDefPackedCheck d inner
  | .arr elem _ => boundedDefPackedCheck d elem
  | .proj _ _ => true

-- lean/Toy/SubstStable/Basic.lean:403-407
structure MonoKey where
  fnId : Nat
  tyArgs : List ClosedTy
  cnstArgs : List Nat
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:410-415
inductive PmeCheck where
  | packedWf (target : OpenTy)
  | sizeEq (lhs rhs : OpenTy)
  | alignLe (lhs rhs : OpenTy)
  | idxValid (idx : IdxTerm)
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:418-431
def evalPmeCheck (A : AssocEnv) (σ : Subst) : PmeCheck → Bool
  | .packedWf t =>
      match instTy A σ t with
      | some τ => packedNoAlignWf τ
      | none => false
  | .sizeEq l r =>
      match instTy A σ l, instTy A σ r with
      | some τ1, some τ2 => decide (τ1.byteSize = τ2.byteSize)
      | _, _ => false
  | .alignLe l r =>
      match instTy A σ l, instTy A σ r with
      | some τ1, some τ2 => decide (τ1.effAlign ≤ τ2.effAlign)
      | _, _ => false
  | .idxValid idx => (evalIdx σ.cnst idx).isSome

-- lean/Toy/SubstStable/Basic.lean:435-440
inductive GenStmt where
  | skip
  | seq (a b : GenStmt)
  | call (callee : Nat) (tyArgs : List OpenTy) (cnstArgs : List IdxTerm)
  | deadBranch (body : GenStmt)
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:444-449
structure GenFn where
  bounds : DeclBounds
  pmeAsserts : List PmeCheck
  localMir : Bool
  body : GenStmt
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:452-454
structure CrateProg where
  fns : List GenFn
  assoc : AssocEnv

-- lean/Toy/SubstStable/Basic.lean:458-460
def substOfKey (k : MonoKey) : Subst where
  ty i := k.tyArgs.getD i (.base 1 1)
  cnst i := k.cnstArgs.getD i 0

-- lean/Toy/SubstStable/Basic.lean:463-466
def isLocalFn (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | some fn => fn.localMir
  | none => false

-- lean/Toy/SubstStable/Basic.lean:469-470
def AllLocalMir (P : CrateProg) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, isLocalFn P k = true

-- lean/Toy/SubstStable/Basic.lean:475-482
def passesLocalPme (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | none => false
  | some fn =>
      if fn.localMir then
        fn.pmeAsserts.all (evalPmeCheck P.assoc (substOfKey k))
      else
        true

-- lean/Toy/SubstStable/Basic.lean:486-489
def passesIntrinsicPme (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | none => false
  | some fn => fn.pmeAsserts.all (evalPmeCheck P.assoc (substOfKey k))

-- lean/Toy/SubstStable/Basic.lean:492-497
def instTyList (A : AssocEnv) (σ : Subst) : List OpenTy → Option (List ClosedTy)
  | [] => some []
  | t :: ts =>
      match instTy A σ t, instTyList A σ ts with
      | some τ, some τs => some (τ :: τs)
      | _, _ => none

-- lean/Toy/SubstStable/Basic.lean:500-505
def evalNatArgs (γ : Nat → Nat) : List IdxTerm → Option (List Nat)
  | [] => some []
  | e :: es =>
      match evalIdx γ e, evalNatArgs γ es with
      | some (.nat n), some ns => some (n :: ns)
      | _, _ => none

-- lean/Toy/SubstStable/Basic.lean:509-519
def usedStmtRefs (A : AssocEnv) (σ : Subst) : GenStmt → Option (List MonoKey)
  | .skip => some []
  | .seq a b =>
      match usedStmtRefs A σ a, usedStmtRefs A σ b with
      | some r1, some r2 => some (r1 ++ r2)
      | _, _ => none
  | .call callee tys cnsts =>
      match instTyList A σ tys, evalNatArgs σ.cnst cnsts with
      | some τs, some ns => some [⟨callee, τs, ns⟩]
      | _, _ => none
  | .deadBranch _ => some []

-- lean/Toy/SubstStable/Basic.lean:522-532
def mentionedStmtRefs (A : AssocEnv) (σ : Subst) : GenStmt → Option (List MonoKey)
  | .skip => some []
  | .seq a b =>
      match mentionedStmtRefs A σ a, mentionedStmtRefs A σ b with
      | some r1, some r2 => some (r1 ++ r2)
      | _, _ => none
  | .call callee tys cnsts =>
      match instTyList A σ tys, evalNatArgs σ.cnst cnsts with
      | some τs, some ns => some [⟨callee, τs, ns⟩]
      | _, _ => none
  | .deadBranch body => mentionedStmtRefs A σ body

-- lean/Toy/SubstStable/Basic.lean:535-545
def monoEdges (includeMentioned : Bool) (P : CrateProg) (k : MonoKey) : Option (List MonoKey) :=
  match P.fns[k.fnId]? with
  | none => none
  | some fn =>
      if fn.localMir then
        if includeMentioned then
          mentionedStmtRefs P.assoc (substOfKey k) fn.body
        else
          usedStmtRefs P.assoc (substOfKey k) fn.body
      else
        some []

-- lean/Toy/SubstStable/Basic.lean:550-554
inductive CollectRes where
  | ok (items : List MonoKey)
  | pmeError (culprit : MonoKey)
  | outOfFuel
  deriving DecidableEq

-- lean/Toy/SubstStable/Basic.lean:557-572
def collectLoop (includeMentioned : Bool) (P : CrateProg) :
    Nat → List MonoKey → List MonoKey → CollectRes
  | 0, [], done => .ok done
  | 0, _ :: _, _ => .outOfFuel
  | _ + 1, [], done => .ok done
  | fuel + 1, k :: rest, done =>
      if k ∈ done then
        collectLoop includeMentioned P fuel rest done
      else if !passesLocalPme P k then
        .pmeError k
      else
        match monoEdges includeMentioned P k with
        | none => .pmeError k
        | some nexts =>
            let fresh := nexts.filter (fun k' => !decide (k' ∈ done))
            collectLoop includeMentioned P fuel (rest ++ fresh) (done ++ [k])

-- lean/Toy/SubstStable/Basic.lean:575-577
def collectAndCheck (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) : CollectRes :=
  collectLoop includeMentioned P fuel roots []

-- lean/Toy/SubstStable/Basic.lean:581-588
inductive Reachable (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey) :
    MonoKey → Prop where
  | root {k} : k ∈ roots → Reachable includeMentioned P roots k
  | step {k k' ks} :
      Reachable includeMentioned P roots k →
      monoEdges includeMentioned P k = some ks →
      k' ∈ ks →
      Reachable includeMentioned P roots k'

-- lean/Toy/SubstStable/Basic.lean:591-599
def intrinsicEdges (includeMentioned : Bool) (P : CrateProg) (k : MonoKey) :
    Option (List MonoKey) :=
  match P.fns[k.fnId]? with
  | none => none
  | some fn =>
      if includeMentioned then
        mentionedStmtRefs P.assoc (substOfKey k) fn.body
      else
        usedStmtRefs P.assoc (substOfKey k) fn.body

-- lean/Toy/SubstStable/Basic.lean:603-610
inductive IntrinsicReachable (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey) :
    MonoKey → Prop where
  | root {k} : k ∈ roots → IntrinsicReachable includeMentioned P roots k
  | step {k k' ks} :
      IntrinsicReachable includeMentioned P roots k →
      intrinsicEdges includeMentioned P k = some ks →
      k' ∈ ks →
      IntrinsicReachable includeMentioned P roots k'

-- lean/Toy/SubstStable/Basic.lean:616-617
def GenericBodySafeUnconditional (fn : GenFn) (openTarget : OpenTy) (Φ : ClosedTy → Bool) : Prop :=
  ∀ A σ τ, DeclBounds.sat fn.bounds A σ → instTy A σ openTarget = some τ → Φ τ = true

-- lean/Toy/SubstStable/Basic.lean:621-626
def GenericBodySafeUnderPme (fn : GenFn) (openTarget : OpenTy) (Φ : ClosedTy → Bool) : Prop :=
  ∀ A σ τ,
    DeclBounds.sat fn.bounds A σ →
    fn.pmeAsserts.all (evalPmeCheck A σ) = true →
    instTy A σ openTarget = some τ →
    Φ τ = true

-- lean/Toy/SubstStable/Basic.lean:630-638
def checkMonoTarget (A : AssocEnv) (Φ : ClosedTy → Bool) (targetOf : Nat → Option OpenTy)
    (T : List MonoKey) : Bool :=
  T.all fun k =>
    match targetOf k.fnId with
    | none => false
    | some openTarget =>
        match instTy A (substOfKey k) openTarget with
        | some τ => Φ τ
        | none => false

-- lean/Toy/SubstStable/Basic.lean:642-647
def MonoCaptureCertifiedOn (A : AssocEnv) (Φ : ClosedTy → Bool)
    (targetOf : Nat → Option OpenTy) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, ∃ openTarget τ,
    targetOf k.fnId = some openTarget ∧
    instTy A (substOfKey k) openTarget = some τ ∧
    Φ τ = true

-- lean/Toy/SubstStable/Basic.lean:651-654
def keyHasPackedGuard (P : CrateProg) (targetOf : Nat → Option OpenTy) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]?, targetOf k.fnId with
  | some fn, some openTarget => decide (PmeCheck.packedWf openTarget ∈ fn.pmeAsserts)
  | _, _ => false

-- lean/Toy/SubstStable/Basic.lean:657-658
def HasPackedPmeGuard (P : CrateProg) (targetOf : Nat → Option OpenTy) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, keyHasPackedGuard P targetOf k = true
```

---

### 2. Result cards

### Card R1 (`R1-subst-stability-characterization`): Substitution stability characterization

```lean
-- lean/Toy/SubstStable/Main.lean:18-21
theorem exists_sound_complete_defCheck_iff_substStable
    (B : BoundPred) (Φ : ClosedTy → Bool) :
    (∃ C : OpenTy → Bool, DefCheckSound B Φ C ∧ DefCheckComplete B Φ C) ↔
      SubstStable B Φ := by …

-- lean/Toy/SubstStable/Main.lean:51-56
theorem witnessDefCheck_sound_and_complete_iff_substStable
    (B : BoundPred) (Φ : ClosedTy → Bool)
    (w : OpenTy → AssocEnv × Subst) (hw : HasInstWitness B w) :
    (DefCheckSound B Φ (witnessDefCheck Φ w) ∧
      DefCheckComplete B Φ (witnessDefCheck Φ w)) ↔
      SubstStable B Φ := by …
```

Unfolded rendering of `exists_sound_complete_defCheck_iff_substStable` (elaborated in `Toy.SubstStable`):

```lean
(∃ C : OpenTy → Bool,
    (∀ t A σ τ, C t = true → B A σ → instTy A σ t = some τ → Φ τ = true) ∧
    (∀ t A σ τ, B A σ → instTy A σ t = some τ → Φ τ = true → C t = true)) ↔
  (∀ t A1 σ1 τ1 A2 σ2 τ2,
    B A1 σ1 → instTy A1 σ1 t = some τ1 →
    B A2 σ2 → instTy A2 σ2 t = some τ2 →
    Φ τ1 = Φ τ2)
```

- **Basis:** `execution (Lean kernel check)`.
- **Kind / Tier / Depth:** `characterization` | `T1` | `shallow`.
- **Plain claim:** For every semantic bound B and closed-type property Φ: (1) a Boolean definition-site check C over open types that is both sound (DefCheckSound B Φ C) and instance-complete (DefCheckComplete B Φ C) exists if and only if Φ is substitution-stable relative to B (SubstStable B Φ); and (2) for any instantiation-witness map w satisfying HasInstWitness B w, the witness-evaluating check witnessDefCheck Φ w (defined without Classical.choice, and executable whenever Φ and w are computable) is both sound and instance-complete relative to B if and only if SubstStable B Φ holds.
- **Hypothesis ledger:**
  - `hw : HasInstWitness B w (in witnessDefCheck_sound_and_complete_iff_substStable)` — ensures w t supplies a B-conforming instantiation whenever t admits at least one B-conforming closed instance. Tight (in the class of constant witness maps over 1-type-parameter open types under FullNoAlignBound): `cex_witnessDefCheck_without_hasInstWitness` (lean/Toy/SubstStable/Counterexamples.lean:124-130).
- **Non-vacuity witness:** `nonvacuity_substStable_witness` (lean/Toy/SubstStable/Counterexamples.lean:139-144) — FixedConstNoAlignBound with constZeroNoAlignWitness and packedNoAlignWf, realizing both true and false verdicts.
- **Non-claims:**
  - The existential right-to-left construction in exists_sound_complete_defCheck_iff_substStable uses classical decidability over arbitrary Prop-valued bounds B; witnessDefCheck_sound_and_complete_iff_substStable gives one constructive route avoiding Classical.choice when an explicit witness map w satisfying HasInstWitness B w is supplied (specific bounds and properties can also admit direct syntax-directed checks such as naiveDefPackedCheck under FullNoAlignBound even when partial const indices rule out any t-independent constant witness map, hasInstWitness_neg_const_map_fullNoAlign).
  - DefCheckSound B Φ C and SubstStable B Φ quantify over environments (A, σ) where instTy A σ t = some τ succeeds; even when SubstStable B Φ holds and a sound, instance-complete check accepts t (C t = true), instantiating t at a B-conforming (A, σ) can still fail with instTy A σ t = none (and CollectRes.pmeError) due to partial const arithmetic (such as N - 1 at N = 0, cex_partial_sub_post_mono_error) or unresolved associated-type projections (instTy_neg_unresolved_proj).
  - DefCheckComplete requires C t = true whenever at least one B-conforming closed instance satisfies Φ; a sound conservative check sufficient for universal validity AllInstSat B Φ t (DefCheckSound B Φ C without DefCheckComplete B Φ C, rejecting mixed open types while accepting a sound class of universally valid ones) does not require SubstStable B Φ (for example, boundedDefPackedCheck in R4; see cex_defCheckSound_without_complete_not_substStable).
  - Open types that admit no B-conforming closed instance (for example, due to an always-failing const index 0 - 1) satisfy AllInstSat B Φ t and SubstStable B Φ vacuously, and witnessDefCheck Φ w accepts them when w t fails to instantiate t.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** Siek and Lumsdaine, 'Essential Language Support for Generic Programming', Proc. ACM SIGPLAN 2005 Conf. on Programming Language Design and Implementation (PLDI '05), pp. 73-84, doi:10.1145/1065010.1065021 (establishes modular concept-bounded type safety of System F^G rather than DefCheckComplete or the iff characterization); Siek and Taha, 'A Semantic Analysis of C++ Templates', ECOOP 2006, LNCS vol. 4067, Springer, pp. 304-327, doi:10.1007/11785477_19 (Isabelle/HOL mechanization of instantiation-time template checking and post-instantiation errors); Gregor, Järvi, Siek, Stroustrup, Dos Reis, and Lumsdaine, 'Concepts: Linguistic Support for Generic Programming in C++', Proc. 21st Annual ACM SIGPLAN Conf. on Object-Oriented Programming, Systems, Languages, and Applications (OOPSLA '06), pp. 291-310, doi:10.1145/1167473.1167499.
- **Design question:** For which closed-type properties does a sound and instance-complete definition-site check over open types exist relative to declared parameter bounds?

---

### Card R2 (`R2-instability-forces-incompleteness`): Instability forces incompleteness of every sound definition-site check

```lean
-- lean/Toy/SubstStable/Main.lean:94-100
theorem not_defCheckComplete_of_defCheckSound_of_unstable_witness
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (t : OpenTy) (A1 A2 : AssocEnv) (σ1 σ2 : Subst) (τ1 τ2 : ClosedTy)
    (hS : DefCheckSound B Φ C)
    (hB1 : B A1 σ1) (hi1 : instTy A1 σ1 t = some τ1) (hΦ1 : Φ τ1 = true)
    (hB2 : B A2 σ2) (hi2 : instTy A2 σ2 t = some τ2) (hΦ2 : Φ τ2 = false) :
    C t = false ∧ ¬ DefCheckComplete B Φ C := by …

-- lean/Toy/SubstStable/Main.lean:110-111
theorem unbounded_substStable_iff_const (Φ : ClosedTy → Bool) :
    SubstStable unbounded Φ ↔ ∀ τ1 τ2 : ClosedTy, Φ τ1 = Φ τ2 := by …

-- lean/Toy/SubstStable/Main.lean:124-127
theorem sizeLe_not_substStable_and_incomplete_of_defCheckSound (k : Nat) :
    ¬ SubstStable unbounded (sizeLe k) ∧
      ∀ C : OpenTy → Bool, DefCheckSound unbounded (sizeLe k) C →
        ¬ DefCheckComplete unbounded (sizeLe k) C := by …
```

Unfolded rendering of `unbounded_substStable_iff_const` (elaborated in `Toy.SubstStable`):

```lean
(∀ t A1 σ1 τ1 A2 σ2 τ2,
    unbounded A1 σ1 → instTy A1 σ1 t = some τ1 →
    unbounded A2 σ2 → instTy A2 σ2 t = some τ2 →
    Φ τ1 = Φ τ2) ↔
  (∀ τ1 τ2 : ClosedTy, Φ τ1 = Φ τ2)
```

- **Basis:** `execution (Lean kernel check)`.
- **Kind / Tier / Depth:** `impossibility` | `T1` | `shallow`.
- **Plain claim:** If C is sound relative to B for Φ (DefCheckSound B Φ C) and an open type t admits two B-conforming closed instances τ1 (with Φ τ1 = true) and τ2 (with Φ τ2 = false), then C rejects t (C t = false) and fails instance-completeness (¬ DefCheckComplete B Φ C); under unbounded parameters, SubstStable unbounded Φ holds if and only if Φ is constant across all closed types, so for every byte threshold k, sizeLe k is not substitution-stable under unbounded and every unbounded-sound definition-site check C for sizeLe k fails DefCheckComplete unbounded (sizeLe k) C.
- **Hypothesis ledger:**
  - `hS : DefCheckSound B Φ C (in not_defCheckComplete_of_defCheckSound_of_unstable_witness and sizeLe_not_substStable_and_incomplete_of_defCheckSound)` — forces C to reject any open type admitting a B-conforming falsifying instance; without soundness, there is an unsound constant-true check (fun _ => true) at threshold k = 4 on 1-parameter open types that accepts .tparam 0 and satisfies DefCheckComplete. Tight (in the class of unsound constant-true check at byte threshold k = 4 on 1-type-parameter open types): `cex_incompleteness_without_soundness` (lean/Toy/SubstStable/Counterexamples.lean:175-186).
  - `hB1 : B A1 σ1 (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — the Φ-satisfying instance τ1 must satisfy B; otherwise under FullNoAlignBound there is an out-of-bound substitution substAlign16 on Packed<T0> while notNaiveDefPackedCheck satisfies DefCheckComplete. Tight (in the class of 1-type-parameter packed open types under FullNoAlignBound): `cex_incompleteness_without_pos_bound` (lean/Toy/SubstStable/Counterexamples.lean:193-204).
  - `hi1 : instTy A1 σ1 t = some τ1 (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — τ1 must arise from instantiating t at (A1, σ1); otherwise on Packed<T0> under FullNoAlignBound there is an unproduced closed type .packed 1 align16U8 while notNaiveDefPackedCheck satisfies DefCheckComplete. Tight (in the class of 1-type-parameter packed open types under FullNoAlignBound): `cex_incompleteness_without_pos_inst` (lean/Toy/SubstStable/Counterexamples.lean:212-224).
  - `hΦ1 : Φ τ1 = true (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — without a B-conforming positive instance of t, rejecting t does not violate DefCheckComplete; for constant-false Φ on .tparam 0, fun _ => false satisfies DefCheckComplete. Tight (in the class of constant-false predicate over 1-type-parameter open types): `cex_incompleteness_without_pos_prop` (lean/Toy/SubstStable/Counterexamples.lean:232-242).
  - `hB2 : B A2 σ2 (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — the Φ-falsifying instance τ2 must satisfy B; otherwise under FullNoAlignBound there is an out-of-bound substitution substAlign16 while naiveDefPackedCheck accepts Packed<T0> and satisfies DefCheckComplete. Tight (in the class of 1-type-parameter packed open types under FullNoAlignBound): `cex_incompleteness_without_neg_bound` (lean/Toy/SubstStable/Counterexamples.lean:251-263).
  - `hi2 : instTy A2 σ2 t = some τ2 (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — τ2 must arise from instantiating t at (A2, σ2); otherwise defaultNoAlignEnv does not produce .packed 1 align16U8 while naiveDefPackedCheck accepts Packed<T0> and satisfies DefCheckComplete. Tight (in the class of 1-type-parameter packed open types under FullNoAlignBound): `cex_incompleteness_without_neg_inst` (lean/Toy/SubstStable/Counterexamples.lean:271-284).
  - `hΦ2 : Φ τ2 = false (in not_defCheckComplete_of_defCheckSound_of_unstable_witness)` — without a B-conforming falsifying instance, C t = true remains sound; for constant-true Φ on .tparam 0, fun _ => true accepts .tparam 0 and satisfies DefCheckComplete. Tight (in the class of constant-true predicate over 1-type-parameter open types): `cex_incompleteness_without_neg_prop` (lean/Toy/SubstStable/Counterexamples.lean:292-303).
- **Non-vacuity witness:** `nonvacuity_unstable_sizeLe` (lean/Toy/SubstStable/Counterexamples.lean:156-165) — unbounded with sizeLe 4, conservative check cClosedBaseLe4 (accepting u8 and rejecting T0), tyU8 (1 byte), and tyU64 (8 bytes).
- **Positive control:** `pc_fullNoAlign_naiveCheck_sound_and_complete` (lean/Toy/SubstStable/Counterexamples.lean:91-94) (adding `FullNoAlignBound` makes `packedNoAlignWf` substitution-stable and makes `naiveDefPackedCheck` both sound and instance-complete).
- **Non-claims:**
  - Failure of DefCheckComplete unbounded (sizeLe k) C forces a sound check C to reject mixed open types such as .tparam 0, not every open type mentioning a type parameter: for example, .arr (.tparam 0) (.lit 0) instantiates to byteSize = 0 ≤ k at every substitution and can be soundly accepted without parameter bounds (allInstSat_pos_zero_len_arr_sizeLe).
  - Does not rule out sound conservative definition-site checks that reject open types with mixed instances while still accepting closed or suitably bounded open types (for example, cClosedBaseLe4 here and boundedDefPackedCheck in R4). Also note that C t = false in not_defCheckComplete_of_defCheckSound_of_unstable_witness follows from the falsifying instance (hS, hB2, hi2, hΦ2) alone (defCheckSound_eq_false_of_falsifying_inst).
  - unbounded_substStable_iff_const relies on OpenTy containing unrestricted type parameters (.tparam 0) ranging over every ClosedTy; a sub-grammar without type parameters or with restricted parameter sorts could admit non-constant unbounded-stable properties (not examined).
  - Escape hatch: strengthening the parameter bound from unbounded to a bound that excludes either all positive or all negative instances of mixed open types restores SubstStable and admits a sound, instance-complete check (pc_fullNoAlign_naiveCheck_sound_and_complete).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** Siek and Lumsdaine, 'Essential Language Support for Generic Programming', Proc. ACM SIGPLAN 2005 Conf. on Programming Language Design and Implementation (PLDI '05), pp. 73-84, doi:10.1145/1065010.1065021 (modular concept-bounded soundness of System F^G; does not state the DefCheckComplete ↔ SubstStable converse); Siek and Taha, 'A Semantic Analysis of C++ Templates', ECOOP 2006, LNCS vol. 4067, Springer, pp. 304-327, doi:10.1007/11785477_19 (Isabelle/HOL mechanization of instantiation-time template checking and post-instantiation errors); Gregor, Järvi, Siek, Stroustrup, Dos Reis, and Lumsdaine, 'Concepts: Linguistic Support for Generic Programming in C++', Proc. 21st Annual ACM SIGPLAN Conf. on Object-Oriented Programming, Systems, Languages, and Applications (OOPSLA '06), pp. 291-310, doi:10.1145/1167473.1167499; Corpus package repr-c-layout-algebra-dst-tails-and-enum-tags (closed layout-size arithmetic background only; does not treat open types, parameter bounds, or substitution stability).
- **Design question:** What goes wrong for completeness when a non-constant structural property (such as size ≤ k) must be checked soundly at the definition site without parameter bounds?

---

### Card R3 (`R3-packed-align-empty-bounds-unsound`): Unconstrained-parameter (`emptyBounds`) `packed`/`align` check counterexample (`Packed<T>` and `Packed<T::Assoc>`)

```lean
-- lean/Toy/SubstStable/Counterexamples.lean:327-336
theorem cex_naiveDefPackedCheck_tparam_and_proj :
    naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      naiveDefPackedCheck (.packed 1 (.proj 0 (.tparam 0))) = true ∧
      DeclBounds.sat emptyBounds sampleAssoc substU8 ∧
      instTy sampleAssoc substU8 (.packed 1 (.proj 0 (.tparam 0))) =
        some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck := by …

-- lean/Toy/SubstStable/Counterexamples.lean:345-346
theorem packedNoAlignWf_not_substStable_emptyBounds :
    ¬ SubstStable (DeclBounds.sat emptyBounds) packedNoAlignWf := by …
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** The Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/type-layout.md:653-654`, `r[layout.repr.alignment.constraint-exclusive]`) specifies: *"The `align` and `packed` modifiers cannot be applied on the same type and a `packed` type cannot transitively contain another `align`ed type."* Error index entry `E0588` (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_error_codes/src/error_codes/E0588.md:1-24`) illustrates that `#[repr(packed)] struct Packed(Aligned)` over `#[repr(align(16))] struct Aligned(i32)` is rejected whereas `#[repr(align(16))] struct Aligned(Packed)` is accepted (distinct from `E0587` on combining `packed` and `align` on one declaration at `E0587.md:1-16`, and from `E0793` on unaligned field references at `E0793.md:1-32`). In the toy model, `packedNoAlignWf` mirrors this containment direction (`packedNoAlignWf_neg_inner_align` vs. `packedNoAlignWf_pos_outer_align`), and `cex_naiveDefPackedCheck_tparam_and_proj` shows why checking only literal `align` attributes visible before parameter substitution and associated-type normalization misses `Packed<T>` and `Packed<T::Assoc>` under `emptyBounds`.
- **Kind / Tier / Depth:** `counterexample` | `T1` | `definitional`.
- **Plain claim:** Under emptyBounds (where every substituted parameter and associated type is itself packedNoAlignWf, with no noAlign restrictions), the syntactic check naiveDefPackedCheck accepts both Packed<T0> (.packed 1 (.tparam 0)) and Packed<<T0 as Trait0>::Assoc> (.packed 1 (.proj 0 (.tparam 0))), yet emptyBounds-conforming instantiations (substAlign16 and sampleAssoc with substU8) normalize both to .packed 1 align16U8, which violates packedNoAlignWf; hence naiveDefPackedCheck is not DefCheckSound and packedNoAlignWf is not SubstStable under emptyBounds.
- **Hypothesis ledger:** None (concrete counterexamples and refutations).
- **Non-vacuity witness:** `cex_naiveDefPackedCheck_tparam_and_proj` (lean/Toy/SubstStable/Counterexamples.lean:327-336) — concrete instantiations substAlign16 on Packed<T0> and (sampleAssoc, substU8) on Packed<<T0 as Trait0>::Assoc>.
- **Positive control:** `pc_fullNoAlign_naiveCheck_sound_and_complete` (lean/Toy/SubstStable/Counterexamples.lean:91-94).
- **Non-claims:**
  - packedNoAlignWf models only transitive containment of an explicit align(n) wrapper inside a packed(k) wrapper; it does not model natural alignment of scalars (packed(1) over u64 has packedNoAlignWf = true, matching E0588 vs. E0793 at compiler/rustc_error_codes/src/error_codes/E0793.md:1-32) or align(n) combined with packed(k) on the same struct declaration (E0587 at compiler/rustc_error_codes/src/error_codes/E0587.md:1-16).
  - Even a zero-length array .packed 1 (.arr align16U8 (.nat 0)) fails packedNoAlignWf because containment is structural in the element type rather than byte-footprint-based (packedNoAlignWf_neg_zero_len_arr).
  - Does not claim that rustc omits post-substitution checks.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_error_codes/src/error_codes/E0588.md:1-24, E0587.md:1-16, and E0793.md:1-32 (documentation); The Rust Reference, rust-lang/reference at commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/type-layout.md:632-658 (specifically r[layout.repr.alignment.constraint-exclusive] at src/type-layout.md:653-654) (normative); Corpus package packed-field-projections-aligned-staging-and-alignment-check-completeness-across-shims.
- **Design question:** Why is 'no explicitly aligned type inside a packed type' not checkable by a purely syntactic open-AST inspection under unconstrained parameters (emptyBounds)?

---

### Card R4 (`R4-packed-align-post-mono-and-bounded-sound`): Post-monomorphization re-checking and bounded definition-site soundness for `packed`/`align`

```lean
-- lean/Toy/SubstStable/Main.lean:150-153
theorem evalPmeCheck_packedWf_iff
    (A : AssocEnv) (σ : Subst) (t : OpenTy) :
    (evalPmeCheck A σ (.packedWf t) = true) ↔
      ∃ τ : ClosedTy, instTy A σ t = some τ ∧ packedNoAlignWf τ = true := by …

-- lean/Toy/SubstStable/Main.lean:198-203
theorem boundedDefPackedCheck_sound
    (d : DeclBounds) (t : OpenTy) (A : AssocEnv) (σ : Subst) (τ : ClosedTy)
    (hchk : boundedDefPackedCheck d t = true)
    (hsat : DeclBounds.sat d A σ)
    (hinst : instTy A σ t = some τ) :
    packedNoAlignWf τ = true := by …
```

Unfolded rendering of `evalPmeCheck_packedWf_iff` (elaborated in `Toy.SubstStable`):

```lean
((match instTy A σ t with
  | some τ => packedNoAlignWf τ
  | none => false) = true) ↔
  ∃ τ : ClosedTy, instTy A σ t = some τ ∧ packedNoAlignWf τ = true
```

- **Basis:** `execution (Lean kernel check)`.
- **Kind / Tier / Depth:** `theorem` | `T1` | `shallow`.
- **Plain claim:** For every associated-type environment A, substitution σ, and open type t, the definitional unfolding of PmeCheck.packedWf t after instantiation (evalPmeCheck A σ (.packedWf t) = true) holds if and only if instTy A σ t produces a closed type τ with packedNoAlignWf τ = true; at the definition site, for every declared bound d, open type t, environment A, substitution σ, and closed type τ, if boundedDefPackedCheck d t = true, DeclBounds.sat d A σ holds, and instTy A σ t = some τ, then packedNoAlignWf τ = true.
- **Hypothesis ledger:**
  - `hchk : boundedDefPackedCheck d t = true (in boundedDefPackedCheck_sound)` — forbids literal align wrappers and unlisted parameters or projections under packed; in the class of 1-parameter open types under emptyBounds, there is Packed<T0> instantiated at substAlign16 where boundedDefPackedCheck = false and packedNoAlignWf = false. Tight (in the class of 1-type-parameter packed open types under emptyBounds): `cex_boundedDefPackedCheck_without_check` (lean/Toy/SubstStable/Counterexamples.lean:358-362).
  - `hsat : DeclBounds.sat d A σ (in boundedDefPackedCheck_sound)` — ensures substituted arguments and associated types obey packedNoAlignWf and declared paramNoAlign/projNoAlign exclusions; in the class of 1-parameter open types under d = ⟨[0], []⟩, there is substAlign16 violating DeclBounds.sat and producing .packed 1 align16U8. Tight (in the class of 1-type-parameter packed open types under DeclBounds ⟨[0], []⟩): `cex_boundedDefPackedCheck_without_boundsSat` (lean/Toy/SubstStable/Counterexamples.lean:366-370).
  - `hinst : instTy A σ t = some τ (in boundedDefPackedCheck_sound)` — ties τ to the normalized result of instantiating t at (A, σ); in the class of closed packed types paired with d = ⟨[0], []⟩, there is .packed 1 align16U8 not produced by instTy on Packed<T0> that violates packedNoAlignWf. Tight (in the class of 1-type-parameter packed open types paired with an unrelated closed type): `cex_boundedDefPackedCheck_without_inst` (lean/Toy/SubstStable/Counterexamples.lean:374-380).
- **Non-vacuity witness:** `nonvacuity_boundedDefPackedCheck_selective` (lean/Toy/SubstStable/Counterexamples.lean:385-393) — selective bound ⟨[0], []⟩ on (Packed<T0>, T1) instantiated with T0 := u8 and T1 := align16U8.
- **Non-claims:**
  - evalPmeCheck_packedWf_iff is a definitional unfolding of evalPmeCheck on PmeCheck.packedWf t; the substantive content of Card R4 is the inductive definition-site soundness theorem boundedDefPackedCheck_sound.
  - Rust has no surface marker trait corresponding to paramNoAlign or projNoAlign; DeclBounds models a counterfactual bound discipline explaining what a sound definition-site check would require.
  - Neither mayHaveAlignUnder nor boundedDefPackedCheck inspects the self-argument arg of .proj tr arg at any AST position (whether inside or outside .packed, boundedDefPackedCheck_pos_erased_proj_arg), because instTy normalizes .proj tr arg to its AssocEnv output rhs and discards arg' without checking packedNoAlignWf arg'; source-level well-formedness of projection arguments (enforced by rustc wfcheck) is not modeled.
  - In DeclBounds.sat, membership tr ∈ d.projNoAlign constrains A tr τ across every closed self-type τ : ClosedTy in AssocEnv (modeling a global trait-definition bound on Trait_tr rather than a per-parameter where-clause bound on <T as Trait_tr>::Assoc), and boundedDefPackedCheck d fails DefCheckComplete whenever d leaves a type parameter i : Nat unlisted (witnessed by Packed<T_i> at substU8, not proved for general d here; proved for d = ⟨[0], []⟩ in cex_defCheckSound_without_complete_not_substStable, cf. boundedDefPackedCheck_neg_unbounded_param for emptyBounds), in addition to rejecting uninstantiable open types such as Packed<[Align16<u8>; 0 - 1]> that satisfy AllInstSat vacuously (not proved here).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_error_codes/src/error_codes/E0588.md:1-24 (documentation); The Rust Reference, rust-lang/reference at commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/type-layout.md:632-658 (r[layout.repr.alignment.constraint-exclusive] at src/type-layout.md:653-654) (normative); Siek and Lumsdaine, 'Essential Language Support for Generic Programming', Proc. ACM SIGPLAN 2005 Conf. on Programming Language Design and Implementation (PLDI '05), pp. 73-84, doi:10.1145/1065010.1065021; Corpus package packed-field-projections-aligned-staging-and-alignment-check-completeness-across-shims.
- **Design question:** Does re-checking packed/align containment after substitution and normalization restore soundness, and what parameter bound makes a definition-site check sound?

---

### Card R5 (`R5-ctor-const-indices-total-and-decidable`): Constructor const indices — total evaluation and decidable rigid syntactic equality

```lean
-- lean/Toy/SubstStable/Main.lean:263-265
theorem idxTotal_of_isCtorIdx
    (e : IdxTerm) (hCtor : isCtorIdx e = true) :
    IdxTotal e := by …

-- lean/Toy/SubstStable/Main.lean:362-366
theorem idxSemEq_iff_eq_of_isCtorIdx
    (e1 e2 : IdxTerm)
    (h1 : isCtorIdx e1 = true)
    (h2 : isCtorIdx e2 = true) :
    IdxSemEq e1 e2 ↔ e1 = e2 := by …
```

Unfolded rendering of `idxSemEq_iff_eq_of_isCtorIdx` (elaborated in `Toy.SubstStable`):

```lean
(∀ γ : Nat → Nat, evalIdx γ e1 = evalIdx γ e2) ↔ e1 = e2
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** Rust RFC 2000 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2000-const-generics.md:178-197, 199-240`) specifies structural equality on const arguments and explains why abstract const expressions containing unevaluated operations cannot be compared by value prior to monomorphization (treating each occurrence as a distinct anonymous projection). In `rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, closed type-system constants normalize to canonical value trees `ValTreeKind` / `ValTree` (`compiler/rustc_type_ir/src/const_kind.rs:191-223` and `compiler/rustc_middle/src/ty/consts/valtree.rs:23-43`), stripping CTFE `AllocId` pointer identities and struct padding bytes (`const_kind.rs:196-202`; see also `ConstKind`/`AliasConstKind` stratification in `const-generics-ctfe-packed-provenance-extern-types-and-array-init-cursors`). Restricting open array indices to `isCtorIdx` over canonical values eliminates partial arithmetic and reduces `IdxSemEq` to rigid syntactic AST equality `e1 = e2` (an instance of free constructor-term injectivity, Baader and Nipkow 1998 Ch. 3).
- **Kind / Tier / Depth:** `characterization` | `T0` | `shallow`.
- **Plain claim:** For every const-index expression e satisfying isCtorIdx e = true (acyclic constructor and parameter terms over canonical natural scalars, with no add, sub, or div nodes), instantiation-time evaluation in evalIdx never fails (IdxTotal e); and for any two index expressions e1 and e2 with isCtorIdx e1 = true and isCtorIdx e2 = true, semantic equality across all natural parameter valuations (IdxSemEq e1 e2) holds if and only if rigid syntactic AST equality e1 = e2 holds, which is decidable via DecidableEq IdxTerm.
- **Hypothesis ledger:**
  - `hCtor : isCtorIdx e = true (in idxTotal_of_isCtorIdx)` — excludes partial checked subtraction and floor division nodes; in the class of 1-const-parameter arithmetic index expressions, there is idxSub1 (N - 1) with isCtorIdx = false that fails evaluation at γ 0 = 0. Tight (in the class of 1-const-parameter checked-subtraction index expressions): `cex_partial_sub_post_mono_error` (lean/Toy/SubstStable/Counterexamples.lean:409-418).
  - `h1 : isCtorIdx e1 = true (in idxSemEq_iff_eq_of_isCtorIdx)` — excludes left-hand arithmetic expressions; in the class of 1-const-parameter total addition expressions, there is 0 + N paired with N that satisfies IdxSemEq while .add (.lit 0) (.cparam 0) ≠ .cparam 0. Tight (in the class of 1-const-parameter total addition index expressions): `cex_idxSemEq_drop_left_isCtorIdx` (lean/Toy/SubstStable/Counterexamples.lean:437-442).
  - `h2 : isCtorIdx e2 = true (in idxSemEq_iff_eq_of_isCtorIdx)` — excludes right-hand arithmetic expressions; in the class of 1-const-parameter total addition expressions, there is N paired with N + 0 that satisfies IdxSemEq while .cparam 0 ≠ .add (.cparam 0) (.lit 0). Tight (in the class of 1-const-parameter total addition index expressions): `cex_idxSemEq_drop_right_isCtorIdx` (lean/Toy/SubstStable/Counterexamples.lean:453-458).
- **Non-vacuity witness:** `nonvacuity_ctor_indices` (lean/Toy/SubstStable/Counterexamples.lean:469-477) — nested constructor terms .ctor 2 [.cparam 0, .ctor 1 [.lit 4]] and .ctor 2 [.cparam 1, .ctor 1 [.lit 4]].
- **Non-claims:**
  - Const parameters (.cparam i) range only over Nat scalars (γ : Nat → Nat, MonoKey.cnstArgs : List Nat), never over CVal.ctor trees, and function-call const argument evaluation (evalNatArgs in GenStmt.call) rejects every .ctor value with none (evalNatArgs_neg_ctor, triggering CollectRes.pmeError during collectAndCheck); IdxTotal guarantees non-failure of evalIdx inside OpenTy.arr, not admission of constructor terms as GenStmt.call const arguments.
  - DecidableEq IdxTerm tests rigid syntactic AST equality (treating .cparam i as universally quantified constants rather than unifiable metavariables). Unlike RFC 2000 (where each abstract const expression occurrence creates a distinct anonymous projection so even two separate AST occurrences of N + 1 do not unify) and stable Rust (where ADT const arguments and open const arithmetic require nightly feature gates), IdxTerm compares AST structure directly.
  - isCtorIdx is sufficient but not necessary for IdxTotal: total addition N + 1 satisfies IdxTotal while isCtorIdx (N + 1) = false (add_idxTotal_yet_not_isCtorIdx).
  - idxSemEq_iff_eq_of_isCtorIdx quantifies over all unconstrained valuations γ : Nat → Nat in IdxSemEq; under a where-clause fixing γ 0 = 4, .cparam 0 and .lit 4 agree on constrained valuations despite syntactic inequality (not modeled in IdxSemEq).
  - CVal models canonical pointer-free, padding-free, union-free value trees directly as an inductive tree; raw pointers with provenance, unions, and floating-point NaN non-reflexivity are outside the grammar.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** Baader and Nipkow, Term Rewriting and All That, Cambridge University Press, 1998, Chapter 3 ('Universal Algebra', §3.2-3.4), doi:10.1017/CBO9781139172752 (freeness and injectivity of constructor-term evaluation over infinite domains); Sternagel and Thiemann, 'First-Order Terms', Archive of Formal Proofs (Isabelle/HOL AFP), Feb. 2018, ISSN 2150-914X, https://isa-afp.org/entries/First_Order_Terms.html (mechanization of first-order constructor terms, matching, and unification); rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_type_ir/src/const_kind.rs:191-223 (ValTreeKind) and compiler/rustc_middle/src/ty/consts/valtree.rs:23-43 (ValTree) (source); rust-lang/rfcs at commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2000-const-generics.md:176-248 (documentation); Corpus report const-generics-ctfe-packed-provenance-extern-types-and-array-init-cursors (ConstKind/AliasConstKind stratification and CtfeProvenance background).
- **Design question:** Under what restriction on const-generic index expressions is instantiation-time evaluation in evalIdx guaranteed never to fail and definitional equality decidable by rigid syntactic AST equality?

---

### Card R6 (`R6-const-index-rigid-eq-and-partial-op-cex`): Incompleteness of rigid syntactic AST equality (`N + 1` vs. `1 + N`) and partial-operation PMEs (`N - 1`, `16 / N`)

```lean
-- lean/Toy/SubstStable/Counterexamples.lean:401-403
theorem cex_rigid_ast_eq_incomplete_comm_add :
    IdxSemEq idxAddN1 idxAdd1N ∧
      decide (idxAddN1 = idxAdd1N) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:409-418
theorem cex_partial_sub_post_mono_error :
    isCtorIdx idxSub1 = false ∧
      ¬ IdxTotal idxSub1 ∧
      evalIdx (fun _ => 1) idxSub1 = some (.nat 0) ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 1⟩ (.arr (.base 1 1) idxSub1) =
        some (.arr tyU8 (.nat 0)) ∧
      collectAndCheck true progSub1 [⟨0, [], [1]⟩] 2 = .ok [⟨0, [], [1]⟩] ∧
      evalIdx (fun _ => 0) idxSub1 = none ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 0⟩ (.arr (.base 1 1) idxSub1) = none ∧
      collectAndCheck true progSub1 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ := by …

-- lean/Toy/SubstStable/Counterexamples.lean:423-429
theorem cex_partial_div_zero_post_mono_error :
    isCtorIdx idxDiv0 = false ∧
      ¬ IdxTotal idxDiv0 ∧
      evalIdx (fun _ => 2) idxDiv0 = some (.nat 8) ∧
      collectAndCheck true progDiv0 [⟨0, [], [2]⟩] 2 = .ok [⟨0, [], [2]⟩] ∧
      evalIdx (fun _ => 0) idxDiv0 = none ∧
      collectAndCheck true progDiv0 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ := by …
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** RFC 2000 (`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2000-const-generics.md:213-229, 242-248`) notes both that distinct AST occurrences of an abstract const expression generate distinct anonymous projections and that commutativity of addition is not built into const comparison, while `E0080` (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_error_codes/src/error_codes/E0080.md:12-15`) documents that *"Attempting to divide by 0 or causing an integer overflow are two ways to induce this error"* during constant evaluation. `cex_partial_sub_post_mono_error` and `cex_partial_div_zero_post_mono_error` witness the resulting post-monomorphization failure at `N = 0`.
- **Kind / Tier / Depth:** `counterexample` | `T0` | `definitional`.
- **Plain claim:** (1) The total index expressions idxAddN1 (N + 1) and idxAdd1N (1 + N) satisfy IdxSemEq yet fail rigid syntactic AST equality (decide (idxAddN1 = idxAdd1N) = false); (2) under checked natural subtraction, idxSub1 (N - 1) evaluates to some (.nat 0), instantiates [u8; N - 1] to [u8; 0], and passes collectAndCheck true progSub1 [⟨0, [], [1]⟩] 2 at N = 1, yet evaluates to none, fails instTy, and fails collectAndCheck true progSub1 [⟨0, [], [0]⟩] 2 with .pmeError ⟨0, [], [0]⟩ at N = 0; and (3) under checked floor division, idxDiv0 (16 / N) evaluates to some (.nat 8) and passes collectAndCheck true progDiv0 [⟨0, [], [2]⟩] 2 at N = 2, yet evaluates to none and fails collectAndCheck true progDiv0 [⟨0, [], [0]⟩] 2 with .pmeError ⟨0, [], [0]⟩ at N = 0.
- **Hypothesis ledger:** None (concrete counterexamples and refutations).
- **Non-vacuity witness:** `cex_partial_sub_post_mono_error` (lean/Toy/SubstStable/Counterexamples.lean:409-418) — concrete expressions idxAddN1, idxAdd1N, idxSub1, and idxDiv0 on progSub1 and progDiv0.
- **Positive control:** `nonvacuity_ctor_indices` (lean/Toy/SubstStable/Counterexamples.lean:469-477).
- **Non-claims:**
  - decide (idxAddN1 = idxAdd1N) = false tests rigid syntactic inequality of ASTs; under RFC 2000's anonymous const projections (text/2000-const-generics.md:213-229), even two separate occurrences of the syntactically identical expression N + 1 fail to unify unless bound to a single declaration.
  - evalIdx models checked natural subtraction (failing with none when x < y) and checked floor division (failing with none when y = 0), matching compile-time const evaluation errors rather than Lean's total truncating Nat.sub (0 - 1 = 0) or Nat.div (16 / 0 = 0).
  - Fixed-width integer overflow (such as usize::MAX + 1 failing E0080, compiler/rustc_error_codes/src/error_codes/E0080.md:12-15) is not modeled in evalIdx's unbounded Nat addition.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** rust-lang/rfcs at commit f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07, text/2000-const-generics.md:176-248 (documentation); rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_error_codes/src/error_codes/E0080.md:1-23 (documentation); Corpus report anneal-pme-mir-semantics-and-polar-ctfe-admission (prose and PME admission semantics); Corpus report const-generics-ctfe-packed-provenance-extern-types-and-array-init-cursors (ConstKind/AliasConstKind stratification referencing RFC 2000).
- **Design question:** How do unevaluated commutative arithmetic and partial arithmetic operations in const indices break rigid syntactic AST equality and defer evaluation errors past generic checking?

---

### Card R7 (`R7-pme-collection-soundness`): Soundness of post-monomorphization assertion collection and `IntrinsicReachable` adequacy

```lean
-- lean/Toy/SubstStable/Main.lean:513-519
theorem collectAndCheck_ok_mem_and_localPme
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T) :
    (∀ k, k ∈ T ↔ Reachable includeMentioned P roots k) ∧
      (∀ k, Reachable false P roots k → k ∈ T) ∧
      (∀ k ∈ T, passesLocalPme P k = true) := by …

-- lean/Toy/SubstStable/Main.lean:565-570
theorem intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T) (k : MonoKey) :
    IntrinsicReachable includeMentioned P roots k ↔ Reachable includeMentioned P roots k := by …

-- lean/Toy/SubstStable/Main.lean:612-618
theorem collectAndCheck_ok_intrinsicPme_of_allLocalMir
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey) (k : MonoKey)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T)
    (hReach : IntrinsicReachable includeMentioned P roots k) :
    passesIntrinsicPme P k = true := by …
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** The module documentation of `rustc_monomorphize::collector` (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_monomorphize/src/collector.rs:159-175`) states: *"One important role of collection is to evaluate all constants that are used by all the items which are being collected"* and *"For every used item, the collector ensures that all mentioned items, recursively, do not use a failing constant,"* while `compiler/rustc_middle/src/mir/mod.rs:265-285` contrasts soundness-critical `Body::required_consts` (`L265-271`) with optimization-level `Body::mentioned_items` (`L273-285`, documented at `L279` as *"not soundness-critical and the contents of this list are not a stable guarantee"*). The Rust Reference (`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/expressions/block-expr.md:252-276`, `r[expr.block.const.evaluation]` and `r[expr.block.const.not-executed]`) guarantees evaluation of executed `const` blocks while leaving unexecuted `if false` `const` blocks unspecified (*"may or may not be evaluated"*). In `google/zerocopy` (`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, `zerocopy/src/macros.rs:239-278`), `transmute_ref!` documents that *"Violations of the alignment and size compatibility checks are detected after the compiler performs monomorphization."* `collectAndCheck` models collection-time PME gating in `used`-only (`false`) vs. `mentioned`-inclusive (`true`) modes, and `intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir` proves when collector-visible `monoEdges` traversal matches full `fn.body` reachability.
- **Kind / Tier / Depth:** `theorem` | `T1` | `substantive`.
- **Plain claim:** For every mode includeMentioned, crate program P, root list roots, fuel, and output list T: (1) if collectAndCheck includeMentioned P roots fuel = .ok T, then T contains an instance k if and only if k is collector-reachable via monoEdges (Reachable includeMentioned P roots k, which truncates outgoing call edges at localMir = false items), T includes every used-reachable instance (Reachable false P roots k), and every k in T satisfies passesLocalPme P k = true; and (2) if in addition every key in T has locally available MIR (AllLocalMir P T), then IntrinsicReachable includeMentioned P roots k (full fn.body call-graph reachability via intrinsicEdges) coincides with Reachable includeMentioned P roots k for every k, and every intrinsically reachable instance k satisfies passesIntrinsicPme P k = true.
- **Hypothesis ledger:**
  - `hOk : collectAndCheck includeMentioned P roots fuel = .ok T` — requires worklist collection to finish within fuel without pmeError or outOfFuel; in the class of 2- and 3-function crates (progLiveLocal and progExtCallbackHole), when collectAndCheck fails to return .ok [], AllLocalMir P [] holds vacuously while membership, IntrinsicReachable ↔ Reachable adequacy, and passesIntrinsicPme all fail. Tight (in the class of 2- and 3-function crates failing with pmeError or outOfFuel): `cex_pme_collection_not_ok` (lean/Toy/SubstStable/Counterexamples.lean:611-620).
  - `hLoc : AllLocalMir P T (in intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir and collectAndCheck_ok_intrinsicPme_of_allLocalMir)` — prevents external items (localMir = false) from skipping PME checks or truncating callbacks; in the class of 3-function crates, there is progExtCallbackHole where external fn 1 calls back into local fn 2 (isLocalFn = true) at ⟨2, [tyU8], []⟩, violating both IntrinsicReachable ↔ Reachable and passesIntrinsicPme despite collectAndCheck = .ok. Tight (in the class of 3-function crates with external-to-local callback edges (and 2-function external-callee crates via cex_external_mir_pme_hole)): `cex_external_callback_local_pme_hole` (lean/Toy/SubstStable/Counterexamples.lean:560-569).
  - `hReach : IntrinsicReachable includeMentioned P roots k (in collectAndCheck_ok_intrinsicPme_of_allLocalMir)` — restricts the intrinsic PME guarantee to call-reachable instances; in the class of 2-function all-local crates, there is progUnreachedLib where collectAndCheck = .ok [⟨0, [], []⟩] and AllLocalMir hold while the unreached instance ⟨1, [tyU8], []⟩ violates passesIntrinsicPme. Tight (in the class of 2-function all-local crates with an unreached generic function): `cex_uncollected_instance_violates_pme` (lean/Toy/SubstStable/Counterexamples.lean:495-500).
- **Non-vacuity witness:** `nonvacuity_pme_collection_mentioned` (lean/Toy/SubstStable/Counterexamples.lean:629-641) — 2-function all-local crate exercising both live and dead-branch calls to fnSizeEqU16 under includeMentioned = true.
- **Non-claims:**
  - collectAndCheck evaluates only explicit assertions in fn.pmeAsserts and Option-totality of monoEdges; it does not enforce DeclBounds.sat fn.bounds on MonoKey arguments or check packedNoAlignWf on closed types lacking an explicit PmeCheck.packedWf assertion, and when roots = [] (an uninstantiated generic library crate) it returns .ok [] while certifying zero instances.
  - In Toy.SubstStable, GenFn.pmeAsserts is attached to the function declaration rather than to GenStmt, so inline assertions on a reached function run in both includeMentioned = false and includeMentioned = true modes; GenStmt.deadBranch affects only callee traversal. In Rust, dead-branch const evaluation is left unspecified by the Reference (r[expr.block.const.not-executed]) and rustc marks Body::mentioned_items (compiler/rustc_middle/src/mir/mod.rs:273-285) as an optimization-independence mechanism rather than a stable soundness guarantee.
  - For an instance k already known to be collector-reachable via Reachable (rather than IntrinsicReachable), pointwise isLocalFn P k = true suffices to transfer passesLocalPme to passesIntrinsicPme without crate-wide AllLocalMir (passesIntrinsicPme_of_passesLocalPme_of_isLocalFn); crate-wide AllLocalMir P T is needed once reachability is stated over intrinsic fn.body edges (cex_external_callback_local_pme_hole).
  - Says nothing when collectAndCheck returns .outOfFuel (for example, under polymorphic recursion; see monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets R8 and R9).
  - In our simplified collector, includeMentioned = true traverses mentionedStmtRefs recursively at every hop, matching collector.rs L173-175 without modeling separate LLVM codegen suppression for mentioned-only nodes.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_monomorphize/src/collector.rs:130-196 and compiler/rustc_middle/src/mir/mod.rs:265-285 (documentation); The Rust Reference, rust-lang/reference at commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/expressions/block-expr.md:230-276 (r[expr.block.const.evaluation]; note r[expr.block.const.not-executed] leaves unexecuted const blocks unspecified) (normative); google/zerocopy at commit 8fb35253fbc703cb2cd0997f4efcda76cf9062b6, zerocopy/src/macros.rs:239-278 and zerocopy/src/doctests.rs:15-17 (documentation); Corpus package monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets; Corpus report anneal-pme-mir-semantics-and-polar-ctfe-admission (prose and PME admission semantics).
- **Design question:** Which monomorphic instances are certified to satisfy post-monomorphization assertions when crate collection succeeds under used-only versus mentioned-items traversal, and when does collector reachability match intrinsic call-graph reachability?

---

### Card R8 (`R8-pme-collection-dead-branch-unreached-and-external-cex`): Dead-branch `used`-vs.-`mentioned` contrast, uncollected instances, and external-MIR callback holes

```lean
-- lean/Toy/SubstStable/Counterexamples.lean:485-488
theorem cex_deadBranch_pme_caught_by_mentioned_missed_by_used :
    collectAndCheck false progDeadBranch [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      collectAndCheck true progDeadBranch [⟨0, [], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progDeadBranch ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:495-500
theorem cex_uncollected_instance_violates_pme :
    collectAndCheck true progUnreachedLib [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      AllLocalMir progUnreachedLib [⟨0, [], []⟩] ∧
      ¬ IntrinsicReachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      ¬ Reachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progUnreachedLib ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:535-542
theorem cex_external_mir_pme_hole :
    collectAndCheck true progExtHole [⟨0, [], []⟩] 4 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      IntrinsicReachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      Reachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesLocalPme progExtHole ⟨1, [tyU8], []⟩ = true ∧
      passesIntrinsicPme progExtHole ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:560-569
theorem cex_external_callback_local_pme_hole :
    collectAndCheck true progExtCallbackHole [⟨0, [], []⟩] 6 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtCallbackHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      isLocalFn progExtCallbackHole ⟨2, [tyU8], []⟩ = true ∧
      IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ (IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ↔
          Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩) ∧
      passesIntrinsicPme progExtCallbackHole ⟨2, [tyU8], []⟩ = false := by …
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** `collector.rs` (`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `L159-175`) documents why `used`-only collection would let dead-code elimination change whether a failing constant errors, motivating `mentioned` items (`cex_deadBranch_pme_caught_by_mentioned_missed_by_used`). For external items, `collector.rs:130-139` notes that when MIR is unavailable for an already-compiled external symbol, `rustc` creates no collector node (whereas `rustc` exports generic MIR in `.rmeta` for cross-crate generic functions); by contrast, `progExtHole` and `progExtCallbackHole` insert `⟨1, [tyU8], []⟩` into `T` with `passesLocalPme = true` and `monoEdges = some []`, modeling a per-crate verifier or modular check that treats external generic calls as uninterpreted stubs—missing both the external callee's own PMEs (`cex_external_mir_pme_hole`) and callbacks from external generic bodies back into local PME-guarded functions (`cex_external_callback_local_pme_hole`; compare `per_crate_collection_has_holes`, Card R14 of `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets`). `zerocopy/src/macros.rs:245-277` (`google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`) likewise documents that uninstantiated generic definitions using post-monomorphization assertions do not fail under `cargo check` (`cex_uncollected_instance_violates_pme`).
- **Kind / Tier / Depth:** `counterexample` | `T1` | `definitional`.
- **Plain claim:** (1) On progDeadBranch (where fn 0 mentions fn 1::<u8> inside deadBranch), used-only collection (includeMentioned = false) returns .ok [⟨0, [], []⟩] while mentioned-mode collection (includeMentioned = true) reports .pmeError ⟨1, [tyU8], []⟩; (2) on progUnreachedLib, mentioned-mode collection from ⟨0, [], []⟩ returns .ok [⟨0, [], []⟩] with AllLocalMir, yet the unreached instance ⟨1, [tyU8], []⟩ is neither IntrinsicReachable nor Reachable and violates passesIntrinsicPme; (3) on progExtHole (where fn 1 has localMir = false), mentioned-mode collection returns .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] with passesLocalPme = true while passesIntrinsicPme is false on ⟨1, [tyU8], []⟩; and (4) on progExtCallbackHole (where local fn 0 calls external fn 1 which calls back into local fn 2), mentioned-mode collection returns .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] while local instance ⟨2, [tyU8], []⟩ (isLocalFn = true) is IntrinsicReachable, not Reachable, and violates passesIntrinsicPme.
- **Hypothesis ledger:** None (concrete counterexamples and refutations).
- **Non-vacuity witness:** `cex_deadBranch_pme_caught_by_mentioned_missed_by_used` (lean/Toy/SubstStable/Counterexamples.lean:485-488) — concrete crate programs progDeadBranch, progUnreachedLib, progExtHole, and progExtCallbackHole.
- **Positive control:** `nonvacuity_pme_collection_mentioned` (lean/Toy/SubstStable/Counterexamples.lean:629-641).
- **Non-claims:**
  - In progExtHole, collectAndCheck inserts the external key ⟨1, [tyU8], []⟩ into the output list T with passesLocalPme = true (and in progExtCallbackHole truncates monoEdges at fn 1), whereas rustc_monomorphize::collector (collector.rs:137-139) creates no collector node when an external non-generic item's MIR is unavailable (and rustc exports generic MIR in .rmeta for cross-crate generic functions); progExtHole and progExtCallbackHole model a per-crate verifier or summary check that treats external generic calls as uninterpreted stubs without discharging their PME obligations or traversing their callbacks.
  - Statements after unconditional divergence (such as return or loop {}) that lower to unreachable zero-predecessor blocks before mentioned-items gathering are not modeled by deadBranch, and the Rust Reference (r[expr.block.const.not-executed]) leaves dead-branch const evaluation unspecified.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_monomorphize/src/collector.rs:130-196 and compiler/rustc_middle/src/mir/mod.rs:265-285 (documentation); The Rust Reference, rust-lang/reference at commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, src/expressions/block-expr.md:230-276 (r[expr.block.const.evaluation], r[expr.block.const.not-executed]) (normative); google/zerocopy at commit 8fb35253fbc703cb2cd0997f4efcda76cf9062b6, zerocopy/src/macros.rs:239-278 and zerocopy/src/doctests.rs:15-17 (documentation); Corpus package monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets; Corpus report anneal-pme-mir-semantics-and-polar-ctfe-admission (prose and PME admission semantics).
- **Design question:** What is the modularity and cross-crate price of enforcing safety invariants via post-monomorphization assertions instead of definition-site trait bounds?

---

### Card R9 (`R9-generic-capture-invariance-and-pme-gap`): Generic IR capture — accepted-type invariance, bound entailment, and PME-assumption gap

```lean
-- lean/Toy/SubstStable/Main.lean:632-640
theorem defCheckSound_accepted_true_and_substStable_of_complete
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (hSound : DefCheckSound B Φ C) :
    (∀ t A1 σ1 τ1 A2 σ2 τ2,
      C t = true →
      B A1 σ1 → instTy A1 σ1 t = some τ1 →
      B A2 σ2 → instTy A2 σ2 t = some τ2 →
      Φ τ1 = true ∧ Φ τ1 = Φ τ2) ∧
    (DefCheckComplete B Φ C → SubstStable B Φ) := by …

-- lean/Toy/SubstStable/Main.lean:652-656
theorem defCheckSound_of_boundEntails
    (B_src B_assumed : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (hEntails : BoundEntails B_src B_assumed)
    (hSound : DefCheckSound B_assumed Φ C) :
    DefCheckSound B_src Φ C := by …

-- lean/Toy/SubstStable/Main.lean:663-669
theorem genericBodySafeUnconditional_of_defCheckSound_of_boundEntails
    (fn : GenFn) (B_assumed : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (openTarget : OpenTy)
    (hEntails : BoundEntails (DeclBounds.sat fn.bounds) B_assumed)
    (hSound : DefCheckSound B_assumed Φ C)
    (hAccept : C openTarget = true) :
    GenericBodySafeUnconditional fn openTarget Φ := by …

-- lean/Toy/SubstStable/Counterexamples.lean:734-744
theorem cex_generic_capture_unstated_bound_unsound :
    SubstStable FullNoAlignBound packedNoAlignWf ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ BoundEntails (DeclBounds.sat emptyBounds) FullNoAlignBound ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck ∧
      ¬ GenericBodySafeUnconditional ⟨emptyBounds, [], true, .skip⟩
          (.packed 1 (.tparam 0)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:761-764
theorem cex_pme_guarded_fn_unsound_without_pme_assumption :
    GenericBodySafeUnderPme fnTransmuteLike (.prod (.tparam 0) (.tparam 1)) eqProdByteSize ∧
      ¬ GenericBodySafeUnconditional fnTransmuteLike
          (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by …
```

Unfolded rendering of `defCheckSound_of_boundEntails` (elaborated in `Toy.SubstStable`):

```lean
∀ t A σ τ, C t = true → B_src A σ → instTy A σ t = some τ → Φ τ = true
```

- **Basis:** `execution (Lean kernel check)`.
- **Modeling bridge (`Basis: derived (modeling bridge)`):** Deductive Rust verifiers that translate or verify polymorphic definitions once against declared trait bounds and contracts (such as Aeneas, Ho and Protzenko 2022; Creusot, Denis et al. 2022; and Verus, Lattuada et al. 2023) reason over symbolic parameters constrained by the function's `where`-clauses. `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails` and `cex_generic_capture_unstated_bound_unsound` isolate why unconditional generic verification may rely on conservative or complete definition-site checks entailed by source bounds, while properties enforced only via post-monomorphization `const` assertions (`Body::required_consts` at `compiler/rustc_middle/src/mir/mod.rs:265-271`, as in `zerocopy`'s `transmute_ref!`) hold only conditionally on PME admission (`GenericBodySafeUnderPme`, matching `PolymorphicConditionalVerification` in `anneal-pme-mir-semantics-and-polar-ctfe-admission`).
- **Kind / Tier / Depth:** `theorem` | `T1` | `definitional`.
- **Plain claim:** (1) As an elementary corollary of DefCheckSound and R1, for every bound B, property Φ, and check C satisfying DefCheckSound B Φ C, Φ evaluates to true (and hence Φ τ1 = Φ τ2) across all B-conforming closed instances of every C-accepted open type t, and if C also satisfies DefCheckComplete B Φ C then SubstStable B Φ holds globally; (2) for every B_src, B_assumed, Φ, C, generic function fn, and openTarget, BoundEntails B_src B_assumed transfers DefCheckSound B_assumed Φ C to DefCheckSound B_src Φ C, and when BoundEntails (DeclBounds.sat fn.bounds) B_assumed and C openTarget = true hold, GenericBodySafeUnconditional fn openTarget Φ holds; (3) assuming an unstated bound (FullNoAlignBound when source declares emptyBounds) makes naiveDefPackedCheck on Packed<T0> violate both DefCheckSound and GenericBodySafeUnconditional for packedNoAlignWf at substAlign16; and (4) PME-guarded fnTransmuteLike on (.prod (.tparam 0) (.tparam 1)) satisfies GenericBodySafeUnderPme for eqProdByteSize yet violates GenericBodySafeUnconditional without a PME-admission precondition.
- **Hypothesis ledger:**
  - `hSound : DefCheckSound B Φ C / DefCheckSound B_assumed Φ C` — the check C must be sound under the assumed bound; in the class of 1-parameter packed open types under emptyBounds, there is naiveDefPackedCheck accepting Packed<T0> while violating DefCheckSound, accepted-type invariance, and GenericBodySafeUnconditional. Tight (in the class of 1-type-parameter packed open types under emptyBounds): `cex_boundEntails_without_soundness` (lean/Toy/SubstStable/Counterexamples.lean:783-793).
  - `hComp : DefCheckComplete B Φ C (in second conjunct of defCheckSound_accepted_true_and_substStable_of_complete)` — conservative sound checks need not imply global SubstStable; in the class of 2-type-parameter packed open types under DeclBounds ⟨[0], []⟩, there is boundedDefPackedCheck ⟨[0], []⟩ which is DefCheckSound and accepts Packed<T0>, yet fails DefCheckComplete while packedNoAlignWf fails SubstStable. Tight (in the class of 2-type-parameter packed open types under DeclBounds ⟨[0], []⟩): `cex_defCheckSound_without_complete_not_substStable` (lean/Toy/SubstStable/Counterexamples.lean:811-817).
  - `hEntails : BoundEntails B_src B_assumed / BoundEntails (DeclBounds.sat fn.bounds) B_assumed` — call sites enforce only the source-declared bound; in the class of 1-parameter generic functions with emptyBounds vs. FullNoAlignBound, there is naiveDefPackedCheck on Packed<T0> at substAlign16 violating both DefCheckSound and GenericBodySafeUnconditional. Tight (in the class of 1-type-parameter generic functions with emptyBounds vs. FullNoAlignBound): `cex_generic_capture_unstated_bound_unsound` (lean/Toy/SubstStable/Counterexamples.lean:734-744).
  - `hAccept : C openTarget = true (in genericBodySafeUnconditional_of_defCheckSound_of_boundEntails)` — C must actually accept openTarget; in the class of 2-type-parameter generic functions with bounds ⟨[0], []⟩, there is openTarget = Packed<T1> rejected by boundedDefPackedCheck ⟨[0], []⟩ that violates GenericBodySafeUnconditional. Tight (in the class of 2-type-parameter generic functions under DeclBounds ⟨[0], []⟩): `cex_genericBodySafeUnconditional_without_accept` (lean/Toy/SubstStable/Counterexamples.lean:837-843).
- **Non-vacuity witness:** `nonvacuity_defCheckSound_boundEntails` (lean/Toy/SubstStable/Counterexamples.lean:857-868) — source bound DeclBounds.sat ⟨[0, 1], []⟩ entailing assumed bound DeclBounds.sat ⟨[0], []⟩ with sound check boundedDefPackedCheck ⟨[0], []⟩ accepting Packed<T0> (and rejecting Packed<T1>), paired with (FullNoAlignBound, naiveDefPackedCheck) witnessing DefCheckSound and DefCheckComplete.
- **Non-claims:**
  - defCheckSound_accepted_true_and_substStable_of_complete, defCheckSound_of_boundEntails, and genericBodySafeUnconditional_of_defCheckSound_of_boundEntails are elementary definitional corollaries of DefCheckSound, BoundEntails, and R1 (GenericBodySafeUnconditional fn openTarget Φ unfolds directly to AllInstSat (DeclBounds.sat fn.bounds) Φ openTarget and does not inspect fn.body).
  - Sound generic-IR reliance on a definition-site check (DefCheckSound B Φ C) does not require SubstStable B Φ when C is conservative rather than instance-complete (¬ DefCheckComplete B Φ C): for example, boundedDefPackedCheck ⟨[0], []⟩ is DefCheckSound under DeclBounds.sat ⟨[0], []⟩ while failing DefCheckComplete and SubstStable (cex_defCheckSound_without_complete_not_substStable; likewise under emptyBounds via boundedDefPackedCheck_sound and packedNoAlignWf_not_substStable_emptyBounds).
  - ClosedTy.byteSize omits inter-field and trailing alignment padding (.align 16 tyU8 has byteSize = 1, byteSize_ignores_align_and_padding), and fnTransmuteLike paired with eqProdByteSize isolates the equal-byte-size PME obligation only—omitting alignment compatibility (PmeCheck.alignLe), alignment-rounded size, bit-validity (FromBytes/IntoBytes), and immutability required for sound reference transmutation.
  - Does not prevent a generic-IR verifier from verifying PME-guarded generic functions conditionally under an explicit PME-admission premise (GenericBodySafeUnderPme, matching PolymorphicConditionalVerification in anneal-pme-mir-semantics-and-polar-ctfe-admission); cex_pme_guarded_fn_unsound_without_pme_assumption refutes only unconditional generic safety (GenericBodySafeUnconditional) that omits PME admission.
  - Does not claim any defect in Aeneas, Charon, Creusot, Verus, or any existing generic-IR verifier.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** Ho and Protzenko, 'Aeneas: Rust verification by functional translation', Proc. ACM Program. Lang. 6 (ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647; Denis, Jourdan, and Marché, 'Creusot: A Foundry for the Deductive Verification of Rust Programs', Proc. 23rd Int. Conf. on Formal Engineering Methods (ICFEM 2022), LNCS vol. 13478, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6; Lattuada, Hance, Cho, Brun, Subasinghe, Zhou, Howell, Parno, and Hawblitzel, 'Verus: Verifying Rust Programs using Linear Ghost Types', Proc. ACM Program. Lang. 7 (OOPSLA1), Article 85, pp. 286-315, 2023, doi:10.1145/3586037; Siek and Lumsdaine, 'Essential Language Support for Generic Programming', Proc. ACM SIGPLAN 2005 Conf. on Programming Language Design and Implementation (PLDI '05), pp. 73-84, doi:10.1145/1065010.1065021; rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_middle/src/mir/mod.rs:265-271 (Body::required_consts) (source); google/zerocopy at commit 8fb35253fbc703cb2cd0997f4efcda76cf9062b6, zerocopy/src/macros.rs:239-278 and zerocopy/src/doctests.rs:15-17 (documentation); Corpus report anneal-pme-mir-semantics-and-polar-ctfe-admission (prose and PME admission semantics).
- **Design question:** Which compiler or verifier checks may a verifier capturing generic IR soundly rely on, and what happens if it assumes unstated bounds or ignores post-monomorphization assertions?

---

### Card R10 (`R10-monomorphic-capture-post-mono-soundness`): Monomorphic IR capture — reliance on post-monomorphization checks for captured instances

```lean
-- lean/Toy/SubstStable/Main.lean:675-679
theorem checkMonoTarget_iff_monoCaptureCertifiedOn
    (A : AssocEnv) (Φ : ClosedTy → Bool)
    (targetOf : Nat → Option OpenTy) (T : List MonoKey) :
    (checkMonoTarget A Φ targetOf T = true) ↔
      MonoCaptureCertifiedOn A Φ targetOf T := by …

-- lean/Toy/SubstStable/Main.lean:702-708
theorem monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard
    (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) (T : List MonoKey) (targetOf : Nat → Option OpenTy)
    (hOk : collectAndCheck includeMentioned P roots fuel = .ok T)
    (hLoc : AllLocalMir P T)
    (hGuard : HasPackedPmeGuard P targetOf T) :
    MonoCaptureCertifiedOn P.assoc packedNoAlignWf targetOf T := by …
```

Unfolded rendering of `checkMonoTarget_iff_monoCaptureCertifiedOn` (elaborated in `Toy.SubstStable`):

```lean
(T.all (fun k =>
    match targetOf k.fnId with
    | none => false
    | some openTarget =>
        match instTy A (substOfKey k) openTarget with
        | some τ => Φ τ
        | none => false) = true) ↔
  (∀ k ∈ T, ∃ openTarget τ,
    targetOf k.fnId = some openTarget ∧
    instTy A (substOfKey k) openTarget = some τ ∧
    Φ τ = true)
```

- **Basis:** `execution (Lean kernel check)`.
- **Kind / Tier / Depth:** `theorem` | `T1` | `shallow`.
- **Plain claim:** (1) As a definitional List.all equivalence for verifier-executed post-capture checking, for every associated-type environment A, closed-type property Φ (whether substitution-stable or not), target map targetOf, and captured monomorphic instance list T, checkMonoTarget A Φ targetOf T = true holds if and only if MonoCaptureCertifiedOn A Φ targetOf T holds; and (2) for every mode includeMentioned, crate program P, root list roots, fuel, output list T, and target map targetOf, when collectAndCheck includeMentioned P roots fuel = .ok T, AllLocalMir P T holds, and HasPackedPmeGuard P targetOf T holds, MonoCaptureCertifiedOn P.assoc packedNoAlignWf targetOf T holds.
- **Hypothesis ledger:**
  - `hOk : collectAndCheck includeMentioned P roots fuel = .ok T (in monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard)` — collection must succeed without pmeError; in the class of 1-function local packedWf-guarded crates, there is progMonoPacked at root ⟨0, [align16U8], []⟩ where AllLocalMir and HasPackedPmeGuard hold, collection fails with pmeError, and MonoCaptureCertifiedOn fails. Tight (in the class of 1-function local packedWf-guarded crates instantiated at an over-aligned argument): `cex_monoCapture_without_collectOk` (lean/Toy/SubstStable/Counterexamples.lean:891-896).
  - `hLoc : AllLocalMir P T (in monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard)` — external items with localMir = false skip local PME evaluation; in the class of 1-function external crates, there is Pext at root ⟨0, [align16U8], []⟩ where collectAndCheck returns .ok and HasPackedPmeGuard holds, yet MonoCaptureCertifiedOn fails. Tight (in the class of 1-function external-MIR crates instantiated at an over-aligned argument): `cex_monoCapture_without_allLocalMir` (lean/Toy/SubstStable/Counterexamples.lean:910-917).
  - `hGuard : HasPackedPmeGuard P targetOf T (in monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard)` — each captured function must declare PmeCheck.packedWf for targetOf; in the class of 1-function unguarded local crates, there is Punguarded at root ⟨0, [align16U8], []⟩ where collectAndCheck returns .ok with AllLocalMir, yet MonoCaptureCertifiedOn fails. Tight (in the class of 1-function local crates omitting the PmeCheck.packedWf guard): `cex_monoCapture_without_packedGuard` (lean/Toy/SubstStable/Counterexamples.lean:933-939).
- **Non-vacuity witness:** `nonvacuity_monoCapture_packed` (lean/Toy/SubstStable/Counterexamples.lean:957-963) — progMonoPacked under emptyBounds (where packedNoAlignWf is unstable) captured at [⟨0, [tyU8], []⟩, ⟨0, [tyU64], []⟩].
- **Non-claims:**
  - checkMonoTarget_iff_monoCaptureCertifiedOn characterizes a direct verifier-side check over T (requiring no compiler PME), whereas monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard transfers compiler PME collection solely for PmeCheck.packedWf / packedNoAlignWf (not .sizeEq, .alignLe, or .idxValid); when roots = [] (an uninstantiated library crate), collectAndCheck returns .ok [] and MonoCaptureCertifiedOn holds vacuously over T = [].
  - MonoCaptureCertifiedOn certifies only the captured instance list T; uncaptured instantiations k ∉ T (such as ⟨0, [align16U8], []⟩ on progMonoPacked) are not certified and can violate Φ (cex_monoCapture_without_collectOk).
  - Does not by itself prove that T is closed under runtime calls unless paired with a closed-target collector theorem (see monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets R1 and R2).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Prior art:** Siek and Taha, 'A Semantic Analysis of C++ Templates', ECOOP 2006, LNCS vol. 4067, Springer, pp. 304-327, doi:10.1007/11785477_19 (mechanized post-instantiation checking of unconstrained generic definitions); VanHattum, Schwartz-Narbonne, Chong, and Sampson, 'Verifying Dynamic Trait Objects in Rust', Proc. 44th IEEE/ACM Int. Conf. on Software Engineering: Software Engineering in Practice (ICSE-SEIP '22), pp. 321-330, 2022, doi:10.1145/3510457.3513031 (per-monomorphization Rust MIR verification in Kani); Griesemer, Hu, Kokke, Lange, Taylor, Toninho, Wadler, and Yoshida, 'Featherweight Go', Proc. ACM Program. Lang. 4 (OOPSLA), Article 149, pp. 149:1-149:29, 2020, doi:10.1145/3428217 (reachable-instance monomorphization collection background only; FGG guarantees post-monomorphization well-typedness from definition-site interface checks with zero post-monomorphization errors); rust-lang/rust at commit 26bfbf28f5f79dff333ce5a232f131b496ec9cfe, compiler/rustc_monomorphize/src/collector.rs:130-196 (documentation); google/zerocopy at commit 8fb35253fbc703cb2cd0997f4efcda76cf9062b6, zerocopy/src/macros.rs:239-278 and zerocopy/src/doctests.rs:15-17 (documentation); Corpus package monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets; Corpus report anneal-pme-mir-semantics-and-polar-ctfe-admission (prose and PME admission semantics).
- **Design question:** Why may a verifier capturing monomorphic IR soundly rely on post-monomorphization checks even for substitution-unstable properties, and to which instances is that guarantee scoped?


---

### 3. Auxiliary characterization lemmas, tightness counterexamples, and definition examples cited by name

#### 3.1 Characterization and structural lemmas (`Lemmas.lean`)

```lean
-- lean/Toy/SubstStable/Lemmas.lean:12-14
theorem defCheckSound_iff_allInstSat
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) :
    DefCheckSound B Φ C ↔ ∀ t, C t = true → AllInstSat B Φ t := by …

-- lean/Toy/SubstStable/Lemmas.lean:23-26
theorem defCheckComplete_iff_exists_inst
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) :
    DefCheckComplete B Φ C ↔
      ∀ t, (∃ A σ τ, B A σ ∧ instTy A σ t = some τ ∧ Φ τ = true) → C t = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:35-38
theorem substStable_iff_allInst_const
    (B : BoundPred) (Φ : ClosedTy → Bool) :
    SubstStable B Φ ↔
      ∀ t, AllInstSat B Φ t ∨ AllInstSat B (fun τ => !Φ τ) t := by …

-- lean/Toy/SubstStable/Lemmas.lean:60-64
theorem hasInstWitness_iff_forall_inst
    (B : BoundPred) (w : OpenTy → AssocEnv × Subst) :
    HasInstWitness B w ↔
      ∀ t A σ τ, B A σ → instTy A σ t = some τ →
        B (w t).1 (w t).2 ∧ (instTy (w t).1 (w t).2 t).isSome = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:72-75
theorem witnessDefCheck_eq_true_iff
    (Φ : ClosedTy → Bool) (w : OpenTy → AssocEnv × Subst) (t : OpenTy) :
    (witnessDefCheck Φ w t = true) ↔
      ∀ τ, instTy (w t).1 (w t).2 t = some τ → Φ τ = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:90-91
theorem idxTotal_iff_exists_cval (e : IdxTerm) :
    IdxTotal e ↔ ∀ γ : Nat → Nat, ∃ v : CVal, evalIdx γ e = some v := by …

-- lean/Toy/SubstStable/Lemmas.lean:104-105
theorem sizeLe_iff_byteSize_le (k : Nat) (τ : ClosedTy) :
    (sizeLe k τ = true) ↔ τ.byteSize ≤ k := by …

-- lean/Toy/SubstStable/Lemmas.lean:110-112
theorem eqProdByteSize_iff_exists_prod (τ : ClosedTy) :
    (eqProdByteSize τ = true) ↔
      ∃ a b : ClosedTy, τ = .prod a b ∧ a.byteSize = b.byteSize := by …

-- lean/Toy/SubstStable/Lemmas.lean:127-128
theorem allLocalMir_iff_list_all (P : CrateProg) (T : List MonoKey) :
    AllLocalMir P T ↔ T.all (isLocalFn P) = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:133-135
theorem hasPackedPmeGuard_iff_list_all
    (P : CrateProg) (targetOf : Nat → Option OpenTy) (T : List MonoKey) :
    HasPackedPmeGuard P targetOf T ↔ T.all (keyHasPackedGuard P targetOf) = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:141-146
theorem defCheckSound_eq_false_of_falsifying_inst
    (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool)
    (t : OpenTy) (A2 : AssocEnv) (σ2 : Subst) (τ2 : ClosedTy)
    (hS : DefCheckSound B Φ C)
    (hB2 : B A2 σ2) (hi2 : instTy A2 σ2 t = some τ2) (hΦ2 : Φ τ2 = false) :
    C t = false := by …

-- lean/Toy/SubstStable/Lemmas.lean:156-159
theorem passesIntrinsicPme_of_passesLocalPme_of_isLocalFn
    {P : CrateProg} {k : MonoKey}
    (hp : passesLocalPme P k = true) (hl : isLocalFn P k = true) :
    passesIntrinsicPme P k = true := by …

-- lean/Toy/SubstStable/Lemmas.lean:171-175
theorem instTy_constZeroNoAlignWitness_isSome
    {A : AssocEnv} {σ : Subst} (hc : σ.cnst = fun _ => 0) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ →
      (instTy (constZeroNoAlignWitness t).1 (constZeroNoAlignWitness t).2 t).isSome = true

-- lean/Toy/SubstStable/Lemmas.lean:226-229
theorem hasAlignWrapper_eq_naiveOpenHasAlign_of_fullNoAlign
    {A : AssocEnv} {σ : Subst} (hB : FullNoAlignBound A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ → hasAlignWrapper τ = naiveOpenHasAlign t

-- lean/Toy/SubstStable/Lemmas.lean:266-269
theorem packedNoAlignWf_eq_naiveDefPackedCheck_of_fullNoAlign
    {A : AssocEnv} {σ : Subst} (hB : FullNoAlignBound A σ) :
    ∀ {t : OpenTy} {τ : ClosedTy},
      instTy A σ t = some τ → packedNoAlignWf τ = naiveDefPackedCheck t
```

#### 3.2 Concrete fixtures, tightness counterexamples, non-vacuity witnesses, and positive controls (`Counterexamples.lean`)

```lean
-- lean/Toy/SubstStable/Counterexamples.lean:15
def idxAddN1 : IdxTerm := .add (.cparam 0) (.lit 1)

-- lean/Toy/SubstStable/Counterexamples.lean:18
def idxAdd1N : IdxTerm := .add (.lit 1) (.cparam 0)

-- lean/Toy/SubstStable/Counterexamples.lean:21
def idxSub1 : IdxTerm := .sub (.cparam 0) (.lit 1)

-- lean/Toy/SubstStable/Counterexamples.lean:24
def idxDiv0 : IdxTerm := .div (.lit 16) (.cparam 0)

-- lean/Toy/SubstStable/Counterexamples.lean:27-28
def progSub1 : CrateProg :=
  ⟨[⟨emptyBounds, [.idxValid idxSub1], true, .skip⟩], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:31-32
def progDiv0 : CrateProg :=
  ⟨[⟨emptyBounds, [.idxValid idxDiv0], true, .skip⟩], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:35-36
def fnSizeEqU16 : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩

-- lean/Toy/SubstStable/Counterexamples.lean:39-40
def fnExtSizeEqU16 : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], false, .skip⟩

-- lean/Toy/SubstStable/Counterexamples.lean:43-44
def fnDeadCaller : GenFn :=
  ⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩

-- lean/Toy/SubstStable/Counterexamples.lean:47-48
def fnLiveCaller : GenFn :=
  ⟨emptyBounds, [], true, .call 1 [.base 1 1] []⟩

-- lean/Toy/SubstStable/Counterexamples.lean:51
def progDeadBranch : CrateProg := ⟨[fnDeadCaller, fnSizeEqU16], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:54
def progLiveLocal : CrateProg := ⟨[fnLiveCaller, fnSizeEqU16], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:57-58
def progUnreachedLib : CrateProg :=
  ⟨[⟨emptyBounds, [], true, .skip⟩, fnSizeEqU16], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:61
def progExtHole : CrateProg := ⟨[fnLiveCaller, fnExtSizeEqU16], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:65-66
def progExtCallbackHole : CrateProg :=
  ⟨[fnLiveCaller, ⟨emptyBounds, [], false, .call 2 [.base 1 1] []⟩, fnSizeEqU16], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:69-71
def cClosedBaseLe4 : OpenTy → Bool
  | .base sz _ => decide (sz ≤ 4)
  | _ => false

-- lean/Toy/SubstStable/Counterexamples.lean:74-75
def fnTransmuteLike : GenFn :=
  ⟨emptyBounds, [.sizeEq (.tparam 0) (.tparam 1)], true, .skip⟩

-- lean/Toy/SubstStable/Counterexamples.lean:78-79
def badAlign16Witness (_ : OpenTy) : AssocEnv × Subst :=
  (emptyAssoc, substAlign16)

-- lean/Toy/SubstStable/Counterexamples.lean:82
def notPackedNoAlignWf (τ : ClosedTy) : Bool := !packedNoAlignWf τ

-- lean/Toy/SubstStable/Counterexamples.lean:85
def notNaiveDefPackedCheck (t : OpenTy) : Bool := !naiveDefPackedCheck t

-- lean/Toy/SubstStable/Counterexamples.lean:883-884
def progMonoPacked : CrateProg :=
  ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩

-- lean/Toy/SubstStable/Counterexamples.lean:887-888
def targetPacked0 (id : Nat) : Option OpenTy :=
  if id = 0 then some (.packed 1 (.tparam 0)) else none

-- lean/Toy/SubstStable/Counterexamples.lean:91-94
theorem pc_fullNoAlign_naiveCheck_sound_and_complete :
    SubstStable FullNoAlignBound packedNoAlignWf ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck := by …

-- lean/Toy/SubstStable/Counterexamples.lean:108-110
theorem notNaiveCheck_sound_and_complete_of_fullNoAlign :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck := by …

-- lean/Toy/SubstStable/Counterexamples.lean:124-130
theorem cex_witnessDefCheck_without_hasInstWitness :
    ¬ HasInstWitness FullNoAlignBound badAlign16Witness ∧
      SubstStable FullNoAlignBound packedNoAlignWf ∧
      ¬ (DefCheckSound FullNoAlignBound packedNoAlignWf
            (witnessDefCheck packedNoAlignWf badAlign16Witness) ∧
          DefCheckComplete FullNoAlignBound packedNoAlignWf
            (witnessDefCheck packedNoAlignWf badAlign16Witness)) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:139-144
theorem nonvacuity_substStable_witness :
    HasInstWitness FixedConstNoAlignBound constZeroNoAlignWitness ∧
      SubstStable FixedConstNoAlignBound packedNoAlignWf ∧
      witnessDefCheck packedNoAlignWf constZeroNoAlignWitness (.packed 1 (.tparam 0)) = true ∧
      witnessDefCheck packedNoAlignWf constZeroNoAlignWitness
        (.packed 1 (.align 16 (.tparam 0))) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:156-165
theorem nonvacuity_unstable_sizeLe :
    DefCheckSound unbounded (sizeLe 4) cClosedBaseLe4 ∧
      cClosedBaseLe4 (.base 1 1) = true ∧
      cClosedBaseLe4 (.tparam 0) = false ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      sizeLe 4 tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      sizeLe 4 tyU64 = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:175-186
theorem cex_incompleteness_without_soundness :
    ¬ DefCheckSound unbounded (sizeLe 4) (fun _ => true) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      sizeLe 4 tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      sizeLe 4 tyU64 = false ∧
      (fun _ : OpenTy => true) (.tparam 0) = true ∧
      DefCheckComplete unbounded (sizeLe 4) (fun _ => true) ∧
      ¬ ((fun _ : OpenTy => true) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (sizeLe 4) (fun _ => true)) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:193-204
theorem cex_incompleteness_without_pos_bound :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ FullNoAlignBound emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      notPackedNoAlignWf (.packed 1 align16U8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      notPackedNoAlignWf (.packed 1 tyU8) = false ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ (notNaiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:212-224
theorem cex_incompleteness_without_pos_inst :
    DefCheckSound FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) ≠
        some (.packed 1 align16U8) ∧
      notPackedNoAlignWf (.packed 1 align16U8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      notPackedNoAlignWf (.packed 1 tyU8) = false ∧
      DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck ∧
      ¬ (notNaiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound notPackedNoAlignWf notNaiveDefPackedCheck) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:232-242
theorem cex_incompleteness_without_pos_prop :
    DefCheckSound unbounded (fun _ => false) (fun _ => false) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      (fun _ : ClosedTy => false) tyU8 ≠ true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      (fun _ : ClosedTy => false) tyU64 = false ∧
      DefCheckComplete unbounded (fun _ => false) (fun _ => false) ∧
      ¬ ((fun _ : OpenTy => false) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (fun _ => false) (fun _ => false)) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:251-263
theorem cex_incompleteness_without_neg_bound :
    DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      packedNoAlignWf (.packed 1 tyU8) = true ∧
      ¬ FullNoAlignBound emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ (naiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:271-284
theorem cex_incompleteness_without_neg_inst :
    DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) =
        some (.packed 1 tyU8) ∧
      packedNoAlignWf (.packed 1 tyU8) = true ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      instTy defaultNoAlignEnv.1 defaultNoAlignEnv.2 (.packed 1 (.tparam 0)) ≠
        some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ (naiveDefPackedCheck (.packed 1 (.tparam 0)) = false ∧
          ¬ DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:292-303
theorem cex_incompleteness_without_neg_prop :
    DefCheckSound unbounded (fun _ => true) (fun _ => true) ∧
      unbounded emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.tparam 0) = some tyU8 ∧
      (fun _ : ClosedTy => true) tyU8 = true ∧
      unbounded emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun _ => tyU64, fun _ => 0⟩ (.tparam 0) = some tyU64 ∧
      (fun _ : ClosedTy => true) tyU64 ≠ false ∧
      (fun _ : OpenTy => true) (.tparam 0) = true ∧
      DefCheckComplete unbounded (fun _ => true) (fun _ => true) ∧
      ¬ ((fun _ : OpenTy => true) (.tparam 0) = false ∧
          ¬ DefCheckComplete unbounded (fun _ => true) (fun _ => true)) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:313-314
theorem sampleAssoc_substU8_sat_emptyBounds :
    DeclBounds.sat emptyBounds sampleAssoc substU8 := by …

-- lean/Toy/SubstStable/Counterexamples.lean:327-336
theorem cex_naiveDefPackedCheck_tparam_and_proj :
    naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      naiveDefPackedCheck (.packed 1 (.proj 0 (.tparam 0))) = true ∧
      DeclBounds.sat emptyBounds sampleAssoc substU8 ∧
      instTy sampleAssoc substU8 (.packed 1 (.proj 0 (.tparam 0))) =
        some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck := by …

-- lean/Toy/SubstStable/Counterexamples.lean:345-346
theorem packedNoAlignWf_not_substStable_emptyBounds :
    ¬ SubstStable (DeclBounds.sat emptyBounds) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:358-362
theorem cex_boundedDefPackedCheck_without_check :
    boundedDefPackedCheck emptyBounds (.packed 1 (.tparam 0)) = false ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:366-370
theorem cex_boundedDefPackedCheck_without_boundsSat :
    boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      ¬ DeclBounds.sat ⟨[0], []⟩ emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:374-380
theorem cex_boundedDefPackedCheck_without_inst :
    boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat ⟨[0], []⟩ emptyAssoc
        ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.packed 1 (.tparam 0)) ≠ some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:385-393
theorem nonvacuity_boundedDefPackedCheck_selective :
    boundedDefPackedCheck ⟨[0], []⟩ (.prod (.packed 1 (.tparam 0)) (.tparam 1)) = true ∧
      DeclBounds.sat ⟨[0], []⟩ emptyAssoc
        ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ ∧
      instTy emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.prod (.packed 1 (.tparam 0)) (.tparam 1)) =
        some (.prod (.packed 1 tyU8) align16U8) ∧
      evalPmeCheck emptyAssoc ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩
        (.packedWf (.prod (.packed 1 (.tparam 0)) (.tparam 1))) = true := by …

-- lean/Toy/SubstStable/Counterexamples.lean:401-403
theorem cex_rigid_ast_eq_incomplete_comm_add :
    IdxSemEq idxAddN1 idxAdd1N ∧
      decide (idxAddN1 = idxAdd1N) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:409-418
theorem cex_partial_sub_post_mono_error :
    isCtorIdx idxSub1 = false ∧
      ¬ IdxTotal idxSub1 ∧
      evalIdx (fun _ => 1) idxSub1 = some (.nat 0) ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 1⟩ (.arr (.base 1 1) idxSub1) =
        some (.arr tyU8 (.nat 0)) ∧
      collectAndCheck true progSub1 [⟨0, [], [1]⟩] 2 = .ok [⟨0, [], [1]⟩] ∧
      evalIdx (fun _ => 0) idxSub1 = none ∧
      instTy emptyAssoc ⟨fun _ => tyU8, fun _ => 0⟩ (.arr (.base 1 1) idxSub1) = none ∧
      collectAndCheck true progSub1 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ := by …

-- lean/Toy/SubstStable/Counterexamples.lean:423-429
theorem cex_partial_div_zero_post_mono_error :
    isCtorIdx idxDiv0 = false ∧
      ¬ IdxTotal idxDiv0 ∧
      evalIdx (fun _ => 2) idxDiv0 = some (.nat 8) ∧
      collectAndCheck true progDiv0 [⟨0, [], [2]⟩] 2 = .ok [⟨0, [], [2]⟩] ∧
      evalIdx (fun _ => 0) idxDiv0 = none ∧
      collectAndCheck true progDiv0 [⟨0, [], [0]⟩] 2 = .pmeError ⟨0, [], [0]⟩ := by …

-- lean/Toy/SubstStable/Counterexamples.lean:437-442
theorem cex_idxSemEq_drop_left_isCtorIdx :
    isCtorIdx (.add (.lit 0) (.cparam 0)) = false ∧
      isCtorIdx (.cparam 0) = true ∧
      IdxSemEq (.add (.lit 0) (.cparam 0)) (.cparam 0) ∧
      ¬ (IdxSemEq (.add (.lit 0) (.cparam 0)) (.cparam 0) ↔
          (.add (.lit 0) (.cparam 0) : IdxTerm) = .cparam 0) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:453-458
theorem cex_idxSemEq_drop_right_isCtorIdx :
    isCtorIdx (.cparam 0) = true ∧
      isCtorIdx (.add (.cparam 0) (.lit 0)) = false ∧
      IdxSemEq (.cparam 0) (.add (.cparam 0) (.lit 0)) ∧
      ¬ (IdxSemEq (.cparam 0) (.add (.cparam 0) (.lit 0)) ↔
          (.cparam 0 : IdxTerm) = .add (.cparam 0) (.lit 0)) := by …

-- lean/Toy/SubstStable/Counterexamples.lean:469-477
theorem nonvacuity_ctor_indices :
    isCtorIdx (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true ∧
      isCtorIdx (.ctor 2 [.cparam 1, .ctor 1 [.lit 4]]) = true ∧
      evalIdx (fun i => i + 10) (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) =
        some (.ctor 2 [.nat 10, .ctor 1 [.nat 4]]) ∧
      decide ((.ctor 2 [.cparam 0, .ctor 1 [.lit 4]] : IdxTerm) =
        .ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true ∧
      decide ((.ctor 2 [.cparam 0, .ctor 1 [.lit 4]] : IdxTerm) =
        .ctor 2 [.cparam 1, .ctor 1 [.lit 4]]) = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:485-488
theorem cex_deadBranch_pme_caught_by_mentioned_missed_by_used :
    collectAndCheck false progDeadBranch [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      collectAndCheck true progDeadBranch [⟨0, [], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progDeadBranch ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:495-500
theorem cex_uncollected_instance_violates_pme :
    collectAndCheck true progUnreachedLib [⟨0, [], []⟩] 4 = .ok [⟨0, [], []⟩] ∧
      AllLocalMir progUnreachedLib [⟨0, [], []⟩] ∧
      ¬ IntrinsicReachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      ¬ Reachable true progUnreachedLib [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesIntrinsicPme progUnreachedLib ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:535-542
theorem cex_external_mir_pme_hole :
    collectAndCheck true progExtHole [⟨0, [], []⟩] 4 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      IntrinsicReachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      Reachable true progExtHole [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ ∧
      passesLocalPme progExtHole ⟨1, [tyU8], []⟩ = true ∧
      passesIntrinsicPme progExtHole ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:560-569
theorem cex_external_callback_local_pme_hole :
    collectAndCheck true progExtCallbackHole [⟨0, [], []⟩] 6 =
        .ok [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      ¬ AllLocalMir progExtCallbackHole [⟨0, [], []⟩, ⟨1, [tyU8], []⟩] ∧
      isLocalFn progExtCallbackHole ⟨2, [tyU8], []⟩ = true ∧
      IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ (IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ↔
          Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩) ∧
      passesIntrinsicPme progExtCallbackHole ⟨2, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:611-620
theorem cex_pme_collection_not_ok :
    collectAndCheck true progLiveLocal [⟨1, [tyU8], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ ∧
      collectAndCheck true progExtCallbackHole [⟨0, [], []⟩] 0 ≠ .ok [] ∧
      AllLocalMir progExtCallbackHole [] ∧
      (⟨0, [], []⟩ : MonoKey) ∉ ([] : List MonoKey) ∧
      Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨0, [], []⟩ ∧
      IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ∧
      ¬ (IntrinsicReachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩ ↔
          Reachable true progExtCallbackHole [⟨0, [], []⟩] ⟨2, [tyU8], []⟩) ∧
      passesIntrinsicPme progExtCallbackHole ⟨2, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Counterexamples.lean:629-641
theorem nonvacuity_pme_collection_mentioned :
    let Pvalid : CrateProg :=
      ⟨[⟨emptyBounds, [], true,
          .seq (.call 1 [.base 2 2] []) (.deadBranch (.call 1 [.arr (.base 1 1) (.lit 2)] []))⟩,
        fnSizeEqU16], emptyAssoc⟩
    let Tvalid : List MonoKey :=
      [⟨0, [], []⟩, ⟨1, [tyU16], []⟩, ⟨1, [.arr tyU8 (.nat 2)], []⟩]
    collectAndCheck true Pvalid [⟨0, [], []⟩] 6 = .ok Tvalid ∧
      AllLocalMir Pvalid Tvalid ∧
      IntrinsicReachable true Pvalid [⟨0, [], []⟩] ⟨1, [.arr tyU8 (.nat 2)], []⟩ ∧
      Reachable true Pvalid [⟨0, [], []⟩] ⟨1, [.arr tyU8 (.nat 2)], []⟩ ∧
      passesIntrinsicPme Pvalid ⟨1, [.arr tyU8 (.nat 2)], []⟩ = true ∧
      collectAndCheck true progLiveLocal [⟨0, [], []⟩] 4 = .pmeError ⟨1, [tyU8], []⟩ := by …

-- lean/Toy/SubstStable/Counterexamples.lean:734-744
theorem cex_generic_capture_unstated_bound_unsound :
    SubstStable FullNoAlignBound packedNoAlignWf ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      ¬ BoundEntails (DeclBounds.sat emptyBounds) FullNoAlignBound ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      DeclBounds.sat emptyBounds emptyAssoc substAlign16 ∧
      instTy emptyAssoc substAlign16 (.packed 1 (.tparam 0)) = some (.packed 1 align16U8) ∧
      packedNoAlignWf (.packed 1 align16U8) = false ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck ∧
      ¬ GenericBodySafeUnconditional ⟨emptyBounds, [], true, .skip⟩
          (.packed 1 (.tparam 0)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:761-764
theorem cex_pme_guarded_fn_unsound_without_pme_assumption :
    GenericBodySafeUnderPme fnTransmuteLike (.prod (.tparam 0) (.tparam 1)) eqProdByteSize ∧
      ¬ GenericBodySafeUnconditional fnTransmuteLike
          (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by …

-- lean/Toy/SubstStable/Counterexamples.lean:783-793
theorem cex_boundEntails_without_soundness :
    BoundEntails (DeclBounds.sat emptyBounds) (DeclBounds.sat emptyBounds) ∧
      ¬ DefCheckSound (DeclBounds.sat emptyBounds) packedNoAlignWf naiveDefPackedCheck ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true ∧
      ¬ (∀ t A1 σ1 τ1 A2 σ2 τ2,
          naiveDefPackedCheck t = true →
          DeclBounds.sat emptyBounds A1 σ1 → instTy A1 σ1 t = some τ1 →
          DeclBounds.sat emptyBounds A2 σ2 → instTy A2 σ2 t = some τ2 →
          packedNoAlignWf τ1 = true ∧ packedNoAlignWf τ1 = packedNoAlignWf τ2) ∧
      ¬ GenericBodySafeUnconditional ⟨emptyBounds, [], true, .skip⟩
          (.packed 1 (.tparam 0)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:811-817
theorem cex_defCheckSound_without_complete_not_substStable :
    DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      ¬ DefCheckComplete (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
          (boundedDefPackedCheck ⟨[0], []⟩) ∧
      ¬ SubstStable (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:837-843
theorem cex_genericBodySafeUnconditional_without_accept :
    BoundEntails (DeclBounds.sat ⟨[0], []⟩) (DeclBounds.sat ⟨[0], []⟩) ∧
      DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 1)) = false ∧
      ¬ GenericBodySafeUnconditional ⟨⟨[0], []⟩, [], true, .skip⟩
          (.packed 1 (.tparam 1)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Counterexamples.lean:857-868
theorem nonvacuity_defCheckSound_boundEntails :
    BoundEntails (DeclBounds.sat ⟨[0, 1], []⟩) (DeclBounds.sat ⟨[0], []⟩) ∧
      DefCheckSound (DeclBounds.sat ⟨[0], []⟩) packedNoAlignWf
        (boundedDefPackedCheck ⟨[0], []⟩) ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 0)) = true ∧
      boundedDefPackedCheck ⟨[0], []⟩ (.packed 1 (.tparam 1)) = false ∧
      DeclBounds.sat ⟨[0, 1], []⟩ emptyAssoc substU8 ∧
      instTy emptyAssoc substU8 (.packed 1 (.tparam 0)) = some (.packed 1 tyU8) ∧
      DefCheckSound FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      DefCheckComplete FullNoAlignBound packedNoAlignWf naiveDefPackedCheck ∧
      FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 ∧
      naiveDefPackedCheck (.packed 1 (.tparam 0)) = true := by …

-- lean/Toy/SubstStable/Counterexamples.lean:891-896
theorem cex_monoCapture_without_collectOk :
    collectAndCheck true progMonoPacked [⟨0, [align16U8], []⟩] 2 ≠ .ok [⟨0, [align16U8], []⟩] ∧
      AllLocalMir progMonoPacked [⟨0, [align16U8], []⟩] ∧
      HasPackedPmeGuard progMonoPacked targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn progMonoPacked.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by …

-- lean/Toy/SubstStable/Counterexamples.lean:910-917
theorem cex_monoCapture_without_allLocalMir :
    let Pext : CrateProg :=
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], false, .skip⟩], emptyAssoc⟩
    collectAndCheck true Pext [⟨0, [align16U8], []⟩] 2 = .ok [⟨0, [align16U8], []⟩] ∧
      ¬ AllLocalMir Pext [⟨0, [align16U8], []⟩] ∧
      HasPackedPmeGuard Pext targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn Pext.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by …

-- lean/Toy/SubstStable/Counterexamples.lean:933-939
theorem cex_monoCapture_without_packedGuard :
    let Punguarded : CrateProg := ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
    collectAndCheck true Punguarded [⟨0, [align16U8], []⟩] 2 = .ok [⟨0, [align16U8], []⟩] ∧
      AllLocalMir Punguarded [⟨0, [align16U8], []⟩] ∧
      ¬ HasPackedPmeGuard Punguarded targetPacked0 [⟨0, [align16U8], []⟩] ∧
      ¬ MonoCaptureCertifiedOn Punguarded.assoc packedNoAlignWf targetPacked0
          [⟨0, [align16U8], []⟩] := by …

-- lean/Toy/SubstStable/Counterexamples.lean:957-963
theorem nonvacuity_monoCapture_packed :
    let roots : List MonoKey := [⟨0, [tyU8], []⟩, ⟨0, [tyU64], []⟩]
    ¬ SubstStable (DeclBounds.sat emptyBounds) packedNoAlignWf ∧
      collectAndCheck true progMonoPacked roots 4 = .ok roots ∧
      AllLocalMir progMonoPacked roots ∧
      HasPackedPmeGuard progMonoPacked targetPacked0 roots ∧
      checkMonoTarget progMonoPacked.assoc packedNoAlignWf targetPacked0 roots = true := by …
```

#### 3.3 Shared fixtures and positive/negative definition examples (`Examples.lean`)

```lean
-- lean/Toy/SubstStable/Examples.lean:13
def tyU8 : ClosedTy := .base 1 1

-- lean/Toy/SubstStable/Examples.lean:16
def tyU16 : ClosedTy := .base 2 2

-- lean/Toy/SubstStable/Examples.lean:19
def tyU32 : ClosedTy := .base 4 4

-- lean/Toy/SubstStable/Examples.lean:22
def tyU64 : ClosedTy := .base 8 8

-- lean/Toy/SubstStable/Examples.lean:25
def align16U8 : ClosedTy := .align 16 tyU8

-- lean/Toy/SubstStable/Examples.lean:28
def emptyAssoc : AssocEnv := fun _ _ => none

-- lean/Toy/SubstStable/Examples.lean:31-34
def sampleAssoc : AssocEnv
  | 0, .base 1 1 => some align16U8
  | 1, .base 1 1 => some tyU32
  | _, _ => none

-- lean/Toy/SubstStable/Examples.lean:37-39
def substU8 : Subst where
  ty _ := tyU8
  cnst _ := 2

-- lean/Toy/SubstStable/Examples.lean:42-44
def substAlign16 : Subst where
  ty i := if i = 0 then align16U8 else tyU8
  cnst _ := 0

-- lean/Toy/SubstStable/Examples.lean:47-48
def defaultNoAlignEnv : AssocEnv × Subst :=
  (fun _ _ => some tyU8, substU8)

-- lean/Toy/SubstStable/Examples.lean:411-416
def sampleMixedCrate : CrateProg where
  fns := [
    ⟨emptyBounds, [], true, .call 1 [.tparam 0] []⟩,
    ⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], false, .skip⟩
  ]
  assoc := emptyAssoc

-- lean/Toy/SubstStable/Examples.lean:52-53
theorem isCtorIdx_pos_nested_ctor :
    isCtorIdx (.ctor 2 [.cparam 0, .ctor 1 [.lit 4]]) = true := by …

-- lean/Toy/SubstStable/Examples.lean:55-56
theorem isCtorIdx_neg_add :
    isCtorIdx (.add (.cparam 0) (.lit 1)) = false := by …

-- lean/Toy/SubstStable/Examples.lean:58-59
theorem isCtorIdxList_pos :
    isCtorIdxList [.lit 0, .cparam 1] = true := by …

-- lean/Toy/SubstStable/Examples.lean:61-62
theorem isCtorIdxList_neg :
    isCtorIdxList [.lit 0, .sub (.cparam 0) (.lit 1)] = false := by …

-- lean/Toy/SubstStable/Examples.lean:64-65
theorem evalIdx_pos_checked_sub :
    evalIdx (fun _ => 5) (.sub (.cparam 0) (.lit 2)) = some (.nat 3) := by …

-- lean/Toy/SubstStable/Examples.lean:67-68
theorem evalIdx_neg_underflow_sub :
    evalIdx (fun _ => 0) (.sub (.cparam 0) (.lit 1)) = none := by …

-- lean/Toy/SubstStable/Examples.lean:70-71
theorem evalIdx_neg_div_zero :
    evalIdx (fun _ => 0) (.div (.lit 16) (.cparam 0)) = none := by …

-- lean/Toy/SubstStable/Examples.lean:73-74
theorem evalIdxList_pos :
    evalIdxList (fun _ => 3) [.cparam 0, .lit 7] = some [.nat 3, .nat 7] := by …

-- lean/Toy/SubstStable/Examples.lean:76-77
theorem evalIdxList_neg :
    evalIdxList (fun _ => 0) [.lit 7, .sub (.cparam 0) (.lit 1)] = none := by …

-- lean/Toy/SubstStable/Examples.lean:79-80
theorem idxSemEq_pos_comm_add :
    IdxSemEq (.add (.cparam 0) (.lit 1)) (.add (.lit 1) (.cparam 0)) := by …

-- lean/Toy/SubstStable/Examples.lean:84-85
theorem idxSemEq_neg_partial_sub :
    ¬ IdxSemEq (.sub (.cparam 0) (.lit 1)) (.lit 0) := by …

-- lean/Toy/SubstStable/Examples.lean:90-91
theorem idxTotal_pos_add :
    IdxTotal (.add (.cparam 0) (.lit 1)) := by …

-- lean/Toy/SubstStable/Examples.lean:95-96
theorem idxTotal_neg_sub :
    ¬ IdxTotal (.sub (.cparam 0) (.lit 1)) := by …

-- lean/Toy/SubstStable/Examples.lean:102-104
theorem add_idxTotal_yet_not_isCtorIdx :
    IdxTotal (.add (.cparam 0) (.lit 1)) ∧
      isCtorIdx (.add (.cparam 0) (.lit 1)) = false := by …

-- lean/Toy/SubstStable/Examples.lean:109-110
theorem byteSize_pos_arr_nat :
    (ClosedTy.arr tyU32 (.nat 3)).byteSize = 12 := by …

-- lean/Toy/SubstStable/Examples.lean:112-113
theorem byteSize_pos_arr_ctor :
    (ClosedTy.arr tyU32 (.ctor 0 [.nat 9])).byteSize = 4 := by …

-- lean/Toy/SubstStable/Examples.lean:115-117
theorem byteSize_neg_arr_zero :
    (ClosedTy.arr tyU32 (.nat 0)).byteSize = 0 ∧
      (ClosedTy.arr tyU32 (.nat 0)).byteSize ≠ 4 := by …

-- lean/Toy/SubstStable/Examples.lean:120-123
theorem byteSize_ignores_align_and_padding :
    align16U8.byteSize = 1 ∧
      align16U8.effAlign = 16 ∧
      (ClosedTy.prod tyU8 tyU32).byteSize = 5 := by …

-- lean/Toy/SubstStable/Examples.lean:126-127
theorem effAlign_pos_align_raises :
    (ClosedTy.align 16 tyU8).effAlign = 16 := by …

-- lean/Toy/SubstStable/Examples.lean:129-131
theorem effAlign_neg_packed_caps :
    (ClosedTy.packed 1 tyU64).effAlign = 1 ∧
      (ClosedTy.packed 1 tyU64).effAlign ≠ 8 := by …

-- lean/Toy/SubstStable/Examples.lean:134-135
theorem sizeLe_pos_u32 :
    sizeLe 4 tyU32 = true := by …

-- lean/Toy/SubstStable/Examples.lean:137-138
theorem sizeLe_neg_u64 :
    sizeLe 4 tyU64 = false := by …

-- lean/Toy/SubstStable/Examples.lean:140-141
theorem eqProdByteSize_pos_same :
    eqProdByteSize (.prod tyU16 (.arr tyU8 (.nat 2))) = true := by …

-- lean/Toy/SubstStable/Examples.lean:143-144
theorem eqProdByteSize_neg_mismatch :
    eqProdByteSize (.prod tyU16 tyU8) = false := by …

-- lean/Toy/SubstStable/Examples.lean:146-147
theorem eqProdByteSize_neg_nonprod :
    eqProdByteSize tyU16 = false := by …

-- lean/Toy/SubstStable/Examples.lean:149-150
theorem hasAlignWrapper_pos_nested :
    hasAlignWrapper (.prod tyU8 align16U8) = true := by …

-- lean/Toy/SubstStable/Examples.lean:152-153
theorem hasAlignWrapper_neg_natural_u64 :
    hasAlignWrapper tyU64 = false := by …

-- lean/Toy/SubstStable/Examples.lean:155-156
theorem packedNoAlignWf_pos_outer_align :
    packedNoAlignWf (.align 16 (.packed 1 tyU64)) = true := by …

-- lean/Toy/SubstStable/Examples.lean:158-159
theorem packedNoAlignWf_pos_natural_u64 :
    packedNoAlignWf (.packed 1 tyU64) = true := by …

-- lean/Toy/SubstStable/Examples.lean:161-162
theorem packedNoAlignWf_neg_inner_align :
    packedNoAlignWf (.packed 1 align16U8) = false := by …

-- lean/Toy/SubstStable/Examples.lean:164-165
theorem packedNoAlignWf_neg_zero_len_arr :
    packedNoAlignWf (.packed 1 (.arr align16U8 (.nat 0))) = false := by …

-- lean/Toy/SubstStable/Examples.lean:169-171
theorem instTy_pos_proj_and_arr :
    instTy sampleAssoc substU8 (.arr (.proj 1 (.tparam 0)) (.cparam 0)) =
      some (.arr tyU32 (.nat 2)) := by …

-- lean/Toy/SubstStable/Examples.lean:173-174
theorem instTy_neg_unresolved_proj :
    instTy emptyAssoc substU8 (.proj 0 (.tparam 0)) = none := by …

-- lean/Toy/SubstStable/Examples.lean:176-177
theorem instTy_neg_failed_idx :
    instTy emptyAssoc substAlign16 (.arr (.tparam 0) (.sub (.cparam 0) (.lit 1))) = none := by …

-- lean/Toy/SubstStable/Examples.lean:179-180
theorem boundEntails_pos_full_to_empty :
    BoundEntails FullNoAlignBound (DeclBounds.sat emptyBounds) := by …

-- lean/Toy/SubstStable/Examples.lean:187-188
theorem substAlign16_sat_emptyBounds :
    DeclBounds.sat emptyBounds emptyAssoc substAlign16 := by …

-- lean/Toy/SubstStable/Examples.lean:200-201
theorem boundEntails_neg_empty_to_full :
    ¬ BoundEntails (DeclBounds.sat emptyBounds) FullNoAlignBound := by …

-- lean/Toy/SubstStable/Examples.lean:207-208
theorem defCheckSound_pos_const_false :
    DefCheckSound unbounded (sizeLe 4) (fun _ => false) := by …

-- lean/Toy/SubstStable/Examples.lean:212-213
theorem defCheckSound_neg_const_true :
    ¬ DefCheckSound unbounded (sizeLe 4) (fun _ => true) := by …

-- lean/Toy/SubstStable/Examples.lean:218-219
theorem defCheckComplete_pos_const_true :
    DefCheckComplete unbounded (sizeLe 4) (fun _ => true) := by …

-- lean/Toy/SubstStable/Examples.lean:223-224
theorem defCheckComplete_neg_const_false :
    ¬ DefCheckComplete unbounded (sizeLe 4) (fun _ => false) := by …

-- lean/Toy/SubstStable/Examples.lean:229-230
theorem allInstSat_pos_packed_under_full :
    AllInstSat FullNoAlignBound packedNoAlignWf (.packed 1 (.tparam 0)) := by …

-- lean/Toy/SubstStable/Examples.lean:235-236
theorem allInstSat_neg_packed_under_empty :
    ¬ AllInstSat (DeclBounds.sat emptyBounds) packedNoAlignWf (.packed 1 (.tparam 0)) := by …

-- lean/Toy/SubstStable/Examples.lean:241-242
theorem allInstSat_pos_zero_len_arr_sizeLe (k : Nat) :
    AllInstSat unbounded (sizeLe k) (.arr (.tparam 0) (.lit 0)) := by …

-- lean/Toy/SubstStable/Examples.lean:249-250
theorem substStable_pos_const_true :
    SubstStable unbounded (fun _ => true) := by …

-- lean/Toy/SubstStable/Examples.lean:254-255
theorem substStable_neg_sizeLe_unbounded :
    ¬ SubstStable unbounded (sizeLe 4) := by …

-- lean/Toy/SubstStable/Examples.lean:263-264
theorem hasInstWitness_pos_fixed_const :
    HasInstWitness FixedConstNoAlignBound constZeroNoAlignWitness := by …

-- lean/Toy/SubstStable/Examples.lean:272-273
theorem hasInstWitness_neg_const_map_fullNoAlign (env : AssocEnv × Subst) :
    ¬ HasInstWitness FullNoAlignBound (fun _ => env) := by …

-- lean/Toy/SubstStable/Examples.lean:302-303
theorem hasInstWitness_pos_singleton_bound :
    HasInstWitness (fun A σ => A = emptyAssoc ∧ σ = substU8) (fun _ => (emptyAssoc, substU8)) := by …

-- lean/Toy/SubstStable/Examples.lean:309-310
theorem hasInstWitness_neg_bad_subst :
    ¬ HasInstWitness FullNoAlignBound (fun _ => (emptyAssoc, substAlign16)) := by …

-- lean/Toy/SubstStable/Examples.lean:320-321
theorem witnessDefCheck_pos_u8 :
    witnessDefCheck (sizeLe 4) (fun _ => (emptyAssoc, substU8)) (.tparam 0) = true := by …

-- lean/Toy/SubstStable/Examples.lean:323-325
theorem witnessDefCheck_neg_over_size :
    witnessDefCheck (sizeLe 4) (fun _ => (emptyAssoc, ⟨fun _ => tyU64, fun _ => 0⟩)) (.tparam 0) =
      false := by …

-- lean/Toy/SubstStable/Examples.lean:329-331
theorem declBoundsSat_pos_selective :
    DeclBounds.sat ⟨[0], []⟩ emptyAssoc
      ⟨fun i => if i = 0 then tyU8 else align16U8, fun _ => 0⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:345-346
theorem declBoundsSat_neg_param_has_align :
    ¬ DeclBounds.sat ⟨[0], []⟩ emptyAssoc substAlign16 := by …

-- lean/Toy/SubstStable/Examples.lean:351-352
theorem fullNoAlignBound_pos_scalars :
    FullNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by …

-- lean/Toy/SubstStable/Examples.lean:357-358
theorem fullNoAlignBound_neg_align_subst :
    ¬ FullNoAlignBound emptyAssoc substAlign16 := by …

-- lean/Toy/SubstStable/Examples.lean:363-364
theorem naiveOpenHasAlign_pos_literal :
    naiveOpenHasAlign (.align 8 (.tparam 0)) = true := by …

-- lean/Toy/SubstStable/Examples.lean:366-367
theorem naiveOpenHasAlign_neg_tparam :
    naiveOpenHasAlign (.tparam 0) = false := by …

-- lean/Toy/SubstStable/Examples.lean:369-370
theorem naiveDefPackedCheck_pos_tparam :
    naiveDefPackedCheck (.packed 1 (.tparam 0)) = true := by …

-- lean/Toy/SubstStable/Examples.lean:372-373
theorem naiveDefPackedCheck_neg_literal_align :
    naiveDefPackedCheck (.packed 1 (.align 16 (.base 1 1))) = false := by …

-- lean/Toy/SubstStable/Examples.lean:375-376
theorem mayHaveAlignUnder_pos_unbounded_param :
    mayHaveAlignUnder emptyBounds (.tparam 0) = true := by …

-- lean/Toy/SubstStable/Examples.lean:378-379
theorem mayHaveAlignUnder_neg_bounded_param :
    mayHaveAlignUnder ⟨[0], []⟩ (.tparam 0) = false := by …

-- lean/Toy/SubstStable/Examples.lean:381-382
theorem boundedDefPackedCheck_pos_bounded_param :
    boundedDefPackedCheck ⟨[0], []⟩ (.prod (.packed 1 (.tparam 0)) (.tparam 1)) = true := by …

-- lean/Toy/SubstStable/Examples.lean:384-385
theorem boundedDefPackedCheck_neg_unbounded_param :
    boundedDefPackedCheck emptyBounds (.packed 1 (.tparam 0)) = false := by …

-- lean/Toy/SubstStable/Examples.lean:387-389
theorem boundedDefPackedCheck_pos_erased_proj_arg :
    boundedDefPackedCheck ⟨[], [0]⟩
      (.packed 1 (.proj 0 (.packed 1 (.align 16 (.base 1 1))))) = true := by …

-- lean/Toy/SubstStable/Examples.lean:393-394
theorem evalPmeCheck_pos_sizeEq :
    evalPmeCheck emptyAssoc substU8 (.sizeEq (.tparam 0) (.base 1 1)) = true := by …

-- lean/Toy/SubstStable/Examples.lean:396-397
theorem evalPmeCheck_neg_sizeMismatch :
    evalPmeCheck emptyAssoc substU8 (.sizeEq (.tparam 0) (.base 2 2)) = false := by …

-- lean/Toy/SubstStable/Examples.lean:399-401
theorem substOfKey_pos_in_bounds :
    (substOfKey ⟨0, [tyU32], [7]⟩).ty 0 = tyU32 ∧
      (substOfKey ⟨0, [tyU32], [7]⟩).cnst 0 = 7 := by …

-- lean/Toy/SubstStable/Examples.lean:404-406
theorem substOfKey_neg_out_of_bounds_default :
    (substOfKey ⟨0, [tyU32], [7]⟩).ty 3 = tyU8 ∧
      (substOfKey ⟨0, [tyU32], [7]⟩).ty 3 ≠ tyU32 := by …

-- lean/Toy/SubstStable/Examples.lean:418-419
theorem isLocalFn_pos :
    isLocalFn sampleMixedCrate ⟨0, [tyU8], []⟩ = true := by …

-- lean/Toy/SubstStable/Examples.lean:421-422
theorem isLocalFn_neg_external :
    isLocalFn sampleMixedCrate ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Examples.lean:424-425
theorem allLocalMir_pos :
    AllLocalMir sampleMixedCrate [⟨0, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:431-432
theorem allLocalMir_neg :
    ¬ AllLocalMir sampleMixedCrate [⟨0, [tyU8], []⟩, ⟨1, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:437-438
theorem passesLocalPme_pos_external_mir :
    passesLocalPme sampleMixedCrate ⟨1, [tyU8], []⟩ = true := by …

-- lean/Toy/SubstStable/Examples.lean:440-443
theorem passesLocalPme_neg_local_fail :
    passesLocalPme
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      ⟨0, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Examples.lean:445-446
theorem passesIntrinsicPme_pos_valid :
    passesIntrinsicPme sampleMixedCrate ⟨1, [tyU16], []⟩ = true := by …

-- lean/Toy/SubstStable/Examples.lean:448-449
theorem passesIntrinsicPme_neg_external_fail :
    passesIntrinsicPme sampleMixedCrate ⟨1, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Examples.lean:451-452
theorem instTyList_pos :
    instTyList emptyAssoc substU8 [.tparam 0, .base 4 4] = some [tyU8, tyU32] := by …

-- lean/Toy/SubstStable/Examples.lean:454-455
theorem instTyList_neg :
    instTyList emptyAssoc substU8 [.proj 0 (.tparam 0)] = none := by …

-- lean/Toy/SubstStable/Examples.lean:457-458
theorem evalNatArgs_pos :
    evalNatArgs (fun _ => 3) [.cparam 0, .add (.cparam 0) (.lit 1)] = some [3, 4] := by …

-- lean/Toy/SubstStable/Examples.lean:460-461
theorem evalNatArgs_neg_ctor :
    evalNatArgs (fun _ => 3) [.ctor 0 [.lit 1]] = none := by …

-- lean/Toy/SubstStable/Examples.lean:463-465
theorem usedStmtRefs_pos_call :
    usedStmtRefs emptyAssoc substU8 (.call 1 [.tparam 0] [.lit 5]) =
      some [⟨1, [tyU8], [5]⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:467-470
theorem usedStmtRefs_neg_erases_deadBranch :
    usedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) = some [] ∧
      usedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) ≠
        some [⟨1, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:473-475
theorem mentionedStmtRefs_pos_keeps_deadBranch :
    mentionedStmtRefs emptyAssoc substU8 (.deadBranch (.call 1 [.tparam 0] [])) =
      some [⟨1, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:477-479
theorem mentionedStmtRefs_neg_bad_idx :
    mentionedStmtRefs emptyAssoc substAlign16
      (.deadBranch (.call 1 [] [.sub (.cparam 0) (.lit 1)])) = none := by …

-- lean/Toy/SubstStable/Examples.lean:481-482
theorem monoEdges_pos_local :
    monoEdges false sampleMixedCrate ⟨0, [tyU16], []⟩ = some [⟨1, [tyU16], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:484-485
theorem monoEdges_neg_undef :
    monoEdges false sampleMixedCrate ⟨9, [], []⟩ = none := by …

-- lean/Toy/SubstStable/Examples.lean:487-490
theorem collectAndCheck_pos_valid :
    collectAndCheck true
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      [⟨0, [tyU16], []⟩] 2 = .ok [⟨0, [tyU16], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:492-495
theorem collectAndCheck_neg_pmeError :
    collectAndCheck true
      ⟨[⟨emptyBounds, [.sizeEq (.tparam 0) (.base 2 2)], true, .skip⟩], emptyAssoc⟩
      [⟨0, [tyU8], []⟩] 2 = .pmeError ⟨0, [tyU8], []⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:497-498
theorem collectAndCheck_neg_outOfFuel :
    collectAndCheck true sampleMixedCrate [⟨0, [tyU16], []⟩] 0 = .outOfFuel := by …

-- lean/Toy/SubstStable/Examples.lean:500-501
theorem reachable_pos_step :
    Reachable false sampleMixedCrate [⟨0, [tyU16], []⟩] ⟨1, [tyU16], []⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:506-510
theorem reachable_neg_deadBranch_in_used :
    ¬ Reachable false
      ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
        ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:528-531
theorem intrinsicEdges_pos_external_body :
    intrinsicEdges true
      ⟨[⟨emptyBounds, [], false, .call 0 [.base 1 1] []⟩], emptyAssoc⟩
      ⟨0, [], []⟩ = some [⟨0, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:533-534
theorem intrinsicEdges_neg_undef :
    intrinsicEdges false sampleMixedCrate ⟨9, [], []⟩ = none := by …

-- lean/Toy/SubstStable/Examples.lean:536-537
theorem intrinsicReachable_pos_step :
    IntrinsicReachable false sampleMixedCrate [⟨0, [tyU16], []⟩] ⟨1, [tyU16], []⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:542-546
theorem intrinsicReachable_neg_deadBranch_in_used :
    ¬ IntrinsicReachable false
      ⟨[⟨emptyBounds, [], true, .deadBranch (.call 1 [.base 1 1] [])⟩,
        ⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      [⟨0, [], []⟩] ⟨1, [tyU8], []⟩ := by …

-- lean/Toy/SubstStable/Examples.lean:564-566
theorem genericBodySafeUnconditional_pos_bounded :
    GenericBodySafeUnconditional
      ⟨⟨[0], []⟩, [], true, .skip⟩ (.packed 1 (.tparam 0)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Examples.lean:573-576
theorem genericBodySafeUnconditional_neg_emptyBounds :
    ¬ GenericBodySafeUnconditional
      ⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩
      (.packed 1 (.tparam 0)) packedNoAlignWf := by …

-- lean/Toy/SubstStable/Examples.lean:581-584
theorem genericBodySafeUnderPme_pos_sizeEq :
    GenericBodySafeUnderPme
      ⟨emptyBounds, [.sizeEq (.tparam 0) (.tparam 1)], true, .skip⟩
      (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by …

-- lean/Toy/SubstStable/Examples.lean:591-593
theorem genericBodySafeUnderPme_neg_unguarded :
    ¬ GenericBodySafeUnderPme
      ⟨emptyBounds, [], true, .skip⟩ (.prod (.tparam 0) (.tparam 1)) eqProdByteSize := by …

-- lean/Toy/SubstStable/Examples.lean:611-614
theorem checkMonoTarget_pos_pair :
    checkMonoTarget emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU16], []⟩] = true := by …

-- lean/Toy/SubstStable/Examples.lean:616-619
theorem checkMonoTarget_neg_bad_inst :
    checkMonoTarget emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU8], []⟩] = false := by …

-- lean/Toy/SubstStable/Examples.lean:621-624
theorem monoCaptureCertifiedOn_pos_pair :
    MonoCaptureCertifiedOn emptyAssoc eqProdByteSize
      (fun id => if id = 0 then some (.prod (.tparam 0) (.tparam 1)) else none)
      [⟨0, [tyU16, tyU16], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:630-632
theorem monoCaptureCertifiedOn_neg_missing_target :
    ¬ MonoCaptureCertifiedOn emptyAssoc eqProdByteSize
      (fun _ => none) [⟨0, [tyU16, tyU16], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:637-639
theorem fixedConstNoAlignBound_pos :
    FixedConstNoAlignBound (constZeroNoAlignWitness (.base 1 1)).1
      (constZeroNoAlignWitness (.base 1 1)).2 := by …

-- lean/Toy/SubstStable/Examples.lean:644-645
theorem fixedConstNoAlignBound_neg_nonzero_cnst :
    ¬ FixedConstNoAlignBound defaultNoAlignEnv.1 defaultNoAlignEnv.2 := by …

-- lean/Toy/SubstStable/Examples.lean:650-654
theorem keyHasPackedGuard_pos :
    keyHasPackedGuard
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      ⟨0, [tyU8], []⟩ = true := by …

-- lean/Toy/SubstStable/Examples.lean:656-660
theorem keyHasPackedGuard_neg_missing_pme :
    keyHasPackedGuard
      ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      ⟨0, [tyU8], []⟩ = false := by …

-- lean/Toy/SubstStable/Examples.lean:662-666
theorem hasPackedPmeGuard_pos :
    HasPackedPmeGuard
      ⟨[⟨emptyBounds, [.packedWf (.packed 1 (.tparam 0))], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      [⟨0, [tyU8], []⟩] := by …

-- lean/Toy/SubstStable/Examples.lean:672-676
theorem hasPackedPmeGuard_neg :
    ¬ HasPackedPmeGuard
      ⟨[⟨emptyBounds, [], true, .skip⟩], emptyAssoc⟩
      (fun id => if id = 0 then some (.packed 1 (.tparam 0)) else none)
      [⟨0, [tyU8], []⟩] := by …
```

## Boundaries

**Non-claims first.**
- **Model–system relation: none proved.** These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, the Rust language, zerocopy, or any program verifier.
- **Instance-completeness vs. conservative sound checking, and partial instantiation.** `DefCheckComplete B Φ C` requires `C` to accept every open type admitting at least one `Φ`-valid `B`-instance. When `SubstStable B Φ` fails, R2 rules out checks that are simultaneously sound and instance-complete; it does **not** rule out sound *conservative* definition-site checks (`cClosedBaseLe4`, `boundedDefPackedCheck`), open types mentioning parameters whose closed property is invariant (`allInstSat_pos_zero_len_arr_sizeLe`), or conditional PME-gated generic verification (`GenericBodySafeUnderPme`). Conversely, even when `SubstStable B Φ` holds and `C t = true`, `instTy A σ t` may still return `none` (`CollectRes.pmeError`) on partially instantiable open types (`[u8; N - 1]` at `N = 0`, `cex_partial_sub_post_mono_error`) or unresolved associated-type projections (`instTy_neg_unresolved_proj`).
- **Scope of monomorphic capture and PME assertions.** Post-monomorphization checks (`collectAndCheck` and `checkMonoTarget`) certify only collected local-MIR instances (`Reachable` / `IntrinsicReachable` under `AllLocalMir`). Uninstantiated library crates (`roots = []`), unreached generic functions (`cex_uncollected_instance_violates_pme`), external callees without local MIR (`cex_external_mir_pme_hole`), and local callbacks reached only through external callees (`cex_external_callback_local_pme_hole`) are **known not to apply** without whole-program MIR availability.
- **Not examined:**
  - Polymorphic-recursion non-termination (`outOfFuel` outcomes of `collectAndCheck`, covered in `monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets` R8 and R9).
  - Equational constraint solving over `where`-clauses restricting const valuations `γ : Nat → Nat` (such as nightly `feature(generic_const_exprs)`), per-AST-occurrence anonymous const projections in RFC 2000 (`text/2000-const-generics.md:213-229`), and nightly `feature(adt_const_params)`.
  - Fixed-width `usize` addition overflow (`usize::MAX + 1`, `compiler/rustc_error_codes/src/error_codes/E0080.md:12-15`), raw-pointer provenance in CTFE (`const-generics-ctfe-packed-provenance-extern-types-and-array-init-cursors`), and CTFE `AllocId`/struct-padding erasure during lowering to `ValTreeKind` (`compiler/rustc_type_ir/src/const_kind.rs:191-223`).
- **Escape hatches:**
  - Strengthening `B` so every `B`-admissible instantiation agrees on `Φ` defeats the incompleteness impossibility of R2 (`pc_fullNoAlign_naiveCheck_sound_and_complete`).
  - Encoding PME assertions as explicit preconditions of generic verification (`GenericBodySafeUnderPme`) allows generic IR verification of PME-guarded functions (`genericBodySafeUnderPme_pos_sizeEq`), shifting the obligation to proving PME admission at each call site.

## Evidence

- **Toolchain:** `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, core Lean and `Std`, zero `[[require]]` dependencies in `lean/lakefile.toml`, no Mathlib), verified on `2026-11-22`.
- **Kernel-check record (`execution`):** All `819` non-internal declarations in `Toy.SubstStable` (`lean/Toy/SubstStable/{Basic,Lemmas,Examples,Counterexamples,Main}.lean`) compile cleanly with zero `sorry`, `admit`, `native_decide`, `axiom`, or `opaque` tokens and depend solely on subsets of `{propext, Classical.choice, Quot.sound}` (`audit/axioms.json`). Statement and definition-closure SHA-256 digests for all `282` declarations referenced across `results.json` (main theorems, characterization lemmas, definition examples, tightness counterexamples, non-vacuity witnesses, positive controls, and core definitions) are recorded in `audit/statements.json`. Note in particular that both `witnessDefCheck` and `witnessDefCheck_sound_and_complete_iff_substStable` (Card R1) use `[propext]` without `Classical.choice`.

### Per-result kernel-check digests

| Theorem | Card | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 | Closure size |
| :--- | :---: | :--- | :--- | :--- | ---: |
| `exists_sound_complete_defCheck_iff_substStable` | R1 | `Classical.choice`, `Quot.sound`, `propext` | `9468d83100c38c0db4f3733bfd60f343b4421e5667c245e0db592ea5cd0509ac` | `7c6fb46a141a8d0ca70e9d17cd4cda9136f4dd40e15bbfbda2210a31027858dc` | 63 |
| `witnessDefCheck_sound_and_complete_iff_substStable` | R1 | `propext` | `daf4c2081433b2218c6fab50d6e467427a1515004065db51649beab2b9214253` | `adc8820bf774866ca6d98285340b0f8c43850853f1502df4c30dfa742bb8c2d3` | 65 |
| `not_defCheckComplete_of_defCheckSound_of_unstable_witness` | R2 | `propext` | `fa19cd8971f764170abf6932dc050f80643c8625f80d45fc896782103d9550f0` | `f90bd06376560672dc4383c0d3b2afc3327edc21828d94d08fbf048f183a6336` | 62 |
| `unbounded_substStable_iff_const` | R2 | `propext` | `0313042e0bef01ae80bb73e6ad5ad03d5cb1d2b718165089cec5876083b04de6` | `eb529b3bf5d7d09eae12228c5af33575ea41f5559e471338f2b85526e0f03609` | 62 |
| `sizeLe_not_substStable_and_incomplete_of_defCheckSound` | R2 | `propext` | `a4bcea299778905e807d286b4c0bf50fe02d85dace11a876897f32ee5a13a8cb` | `73db9c810d60499784b940f9956f2bf37a8d3901ba84d4eb7262ea18e372f467` | 73 |
| `cex_naiveDefPackedCheck_tparam_and_proj` | R3 | `propext` | `368935237f8152e3c9f33d67148e70fd53270385416cc89f6844f55d29de866a` | `54b34754724e8666d1486386c98f43e3ef3b3b427cdc7a7825bf7d3b31ad92a5` | 91 |
| `packedNoAlignWf_not_substStable_emptyBounds` | R3 | `propext` | `d9e1df8f9f2235fbd5a656f0e31275337bd40f3afdf51026f3b209f8d9aeb02f` | `852f0d1d8cbf1e89b66e7bcfcfe6f7b58e0d42563b7d9c1bf42dd1fcb9c7e1b3` | 77 |
| `evalPmeCheck_packedWf_iff` | R4 | `Quot.sound`, `propext` | `c18e6b6c109161366b799527633b3f3cd864bd3267f30a19f03d27c1f56d8c3a` | `197a3a4f5ffaa053eaf4ffd7e4ecb946b41ea292f57ebcfab2ebccd15e5d191d` | 83 |
| `boundedDefPackedCheck_sound` | R4 | `Quot.sound`, `propext` | `5e1747aaed9968a4b18382f37af09a133ec5bc1795d919466736176a0776e98a` | `ef55e4d2d123b1aa44435690dbc519a0c0bc89a0b6434c5f78ae9cfaa9029f9b` | 78 |
| `idxTotal_of_isCtorIdx` | R5 | `propext` | `275211f1788d26602c9573e570e6074ea03e0ad6cb0f7828043ef4832e02dcb4` | `9c7d8cbb0674cb88d54d8f186890b1b71d9614fd26086491bd634a6315b1531e` | 33 |
| `idxSemEq_iff_eq_of_isCtorIdx` | R5 | `Classical.choice`, `Quot.sound`, `propext` | `a0e9b905368385f41e7e2b0eaf8b617d10664949f07f511b604b3be238ecdc65` | `1ad3940fc24ab6748192f0b45c317e6d3781c12d98aee6b8f1cb8d66e91346bb` | 33 |
| `cex_rigid_ast_eq_incomplete_comm_add` | R6 | `propext` | `02a04366b5892ed919ab61654d1fa1cc18cf109aa72849594ac46d94363a2d31` | `cd5256e8b032079215228bff1bbede731aba2ea7cd456a3ed3d0eff0c5effcf2` | 58 |
| `cex_partial_sub_post_mono_error` | R6 | `propext` | `ba317919a8cea92ebd13bec2a46262f5d71a1f570ca3796f1ff1a1beec2c8fe9` | `52cc3a6cebb0ad5ff6734b40190b32be3f7fb5856e064a5311c5694b18bb3753` | 190 |
| `cex_partial_div_zero_post_mono_error` | R6 | `propext` | `286b1bae2ded7778307f73533bf9dee95522e119766adeaf4da55ba313ac3eda` | `fb45ec04fdad9e84f5bae2e31ff60e3ec779c70bdab4f864936ac4ea9445a280` | 189 |
| `collectAndCheck_ok_mem_and_localPme` | R7 | `propext` | `fadf51dd086f61c266271482abb13d2f9017e04de6c34c66bf238a448556083f` | `dd130f2b23200a895cfefe282abd677e86e8aec13e76f399feeb72504dbba75c` | 184 |
| `intrinsicReachable_iff_reachable_of_collectAndCheck_ok_of_allLocalMir` | R7 | `propext` | `4545f9de4dff2e15fbb1de4b5ea41202c9d5e651072b59fc29212ba6e1d85888` | `c1235d38e570771b9e7c5a2acb811809e682b9e6bea595e1b2d41d2a0de83ff7` | 191 |
| `collectAndCheck_ok_intrinsicPme_of_allLocalMir` | R7 | `Quot.sound`, `propext` | `fd2003e5820c40711ffdf5165644953cf4edf0a5d1a8530000696690a7233d85` | `eaecae0774d49f8d8e12a62b8146d8e275dccf473eba5b46a0c4e78e5fed2087` | 189 |
| `cex_deadBranch_pme_caught_by_mentioned_missed_by_used` | R8 | `propext` | `78ec519dd57312812203f2f48da46d6756019346769e2efc26b1dcba51b1eb85` | `444cbcd32cc94913ff87434c6b73adbe4ecd499ecedb5981beac90c4e4f53b0b` | 188 |
| `cex_uncollected_instance_violates_pme` | R8 | `propext` | `b8dc9730a456eddcce5fb695ae01de4e18522bff2562c04d2f23191d06095bcc` | `e3aff903fd14f4655b2e1cfad456bcfa27f4150714b828b7a32fe67791f20ee1` | 197 |
| `cex_external_mir_pme_hole` | R8 | `propext` | `c6655e3b112a39b1a552bbfd4b97469a9cc23f94b6d69e71790ba05b4c224922` | `1ee797d92e884d5aa35a4cca993563b9949750b17b3005992fd380ebc9348301` | 198 |
| `cex_external_callback_local_pme_hole` | R8 | `propext` | `293d7ce98c240953834788e7b4e68c37d44736c11e9f07347e943c0fbf110520` | `02c101333274b9f834241beb78052c3121e6afada9aa8aa2fa76181f02227663` | 198 |
| `defCheckSound_accepted_true_and_substStable_of_complete` | R9 | `Classical.choice`, `Quot.sound`, `propext` | `64b06336c127615bb15cf4d3417bf41cc2f861694222ea15d511961ceb0e05d7` | `7c6fb46a141a8d0ca70e9d17cd4cda9136f4dd40e15bbfbda2210a31027858dc` | 63 |
| `defCheckSound_of_boundEntails` | R9 | `propext` | `7453fc6d42c78067f5ef905d325385861c7eda4d7e53944149b0de218e21702a` | `7c0ae6d73f3cd59c9e8c3e03ffe05cb77e2d33d63f888b61a379ba4e001cbc59` | 62 |
| `genericBodySafeUnconditional_of_defCheckSound_of_boundEntails` | R9 | `propext` | `d9f8839fbf31c636e568f35ed428b2b14edcb1084fa2e9c90a8fb323d3dbe9d8` | `6d4107d85dc45e8be278e51bb2987f7a72fdc8520ce3aa509ecdea2898ac8708` | 91 |
| `cex_generic_capture_unstated_bound_unsound` | R9 | `propext` | `5aee6f201c1e247ced7a45b2120e682d3050d43830007c3c7e0054ede3ad02fe` | `e2bacc6082fc452f2c6266a01fb45ef2718cedc683103d74bad68bf9e5092ac1` | 102 |
| `cex_pme_guarded_fn_unsound_without_pme_assumption` | R9 | `propext` | `0fec2280c945c69516c2a5e87eb1c1b9a0dc599e3a68857ea1bc4c21c8973ddf` | `de99df86fe821fbcc29e124a6daa44457ed1a2dd0d651a5885fe1cf766914149` | 105 |
| `checkMonoTarget_iff_monoCaptureCertifiedOn` | R10 | `Quot.sound`, `propext` | `64c4ce8714a0fa6692892b72c8473ff9c38e0f056e9d47c2dc1f5909f50ade72` | `cfe8d7cd65ce218ce766a389baa89b60ea86209ecadcefeb92a4d346b5bfefb8` | 68 |
| `monoCaptureCertifiedOn_of_collectAndCheck_ok_of_packedGuard` | R10 | `Quot.sound`, `propext` | `d118798fad4d8eb582ddf74d5c128f72054cce79d86e25eb8340b7103d22bef8` | `65103e56ab450238c60b770782fb321faee4b0be005516467e37fb8c13221814` | 262 |

### Pinned primary sources

- **`rust-lang/rust` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`:** `compiler/rustc_error_codes/src/error_codes/E0588.md:1-24`, `compiler/rustc_error_codes/src/error_codes/E0587.md:1-16`, `compiler/rustc_error_codes/src/error_codes/E0793.md:1-32`, `compiler/rustc_error_codes/src/error_codes/E0080.md:1-23`, `compiler/rustc_monomorphize/src/collector.rs:130-196`, `compiler/rustc_middle/src/mir/mod.rs:265-285` (`Body::required_consts` at `L265-271`, `Body::mentioned_items` at `L273-285`), `compiler/rustc_type_ir/src/const_kind.rs:191-223` (`ValTreeKind`), and `compiler/rustc_middle/src/ty/consts/valtree.rs:23-43` (`ValTree`).
- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** `src/type-layout.md:632-658` (specifically `r[layout.repr.alignment.constraint-exclusive]` at `src/type-layout.md:653-654`) and `src/expressions/block-expr.md:230-276` (`r[expr.block.const.evaluation]` and `r[expr.block.const.not-executed]`).
- **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:** `text/2000-const-generics.md:176-248`.
- **`google/zerocopy` at `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`:** `zerocopy/src/macros.rs:239-278` and `zerocopy/src/doctests.rs:15-17`.
- **Academic references:** Baader and Nipkow (*Term Rewriting and All That*, Cambridge Univ. Press, 1998, Ch. 3, ISBN `978-0-521-45520-6`, `doi:10.1017/CBO9781139172752`); Sternagel and Thiemann (*"First-Order Terms"*, *Archive of Formal Proofs*, Feb. 2018, ISSN `2150-914X`, `https://isa-afp.org/entries/First_Order_Terms.html`); Siek and Lumsdaine (*PLDI '05*, pp. 73–84, `doi:10.1145/1065010.1065021`); Siek and Taha (*ECOOP 2006*, LNCS vol. 4067, pp. 304–327, `doi:10.1007/11785477_19`); Gregor, Järvi, Siek, Stroustrup, Dos Reis, and Lumsdaine (*OOPSLA '06*, pp. 291–310, `doi:10.1145/1167473.1167499`); Griesemer, Hu, Kokke, Lange, Taylor, Toninho, Wadler, and Yoshida (*OOPSLA 2020*, Art. 149, pp. 149:1–149:29, `doi:10.1145/3428217`); VanHattum, Schwartz-Narbonne, Chong, and Sampson (*ICSE-SEIP '22*, pp. 321–330, `doi:10.1145/3510457.3513031`); Ho and Protzenko (*ICFP 2022*, Art. 116, pp. 711–741, `doi:10.1145/3547647`); Denis, Jourdan, and Marché (*ICFEM 2022*, LNCS vol. 13478, pp. 90–105, `doi:10.1007/978-3-031-17244-1_6`); Lattuada, Hance, Cho, Brun, Subasinghe, Zhou, Howell, Parno, and Hawblitzel (*OOPSLA 2023*, Art. 85, pp. 286–315, `doi:10.1145/3586037`).

## Revalidation

Requirements: `elan` (which selects the pinned toolchain `leanprover/lean4:v4.34.1` declared in `lean/lean-toolchain`) and `python3`.

### Primary one-command revalidation (`support/revalidate.py`)

Run from the package directory:

```bash
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` into a fresh temporary directory (leaving the package directory unmodified) and checks four properties:
1. `lake build` succeeds under `leanprover/lean4:v4.34.1`.
2. Comment-stripped Lean sources contain no `sorry`, `admit`, `native_decide`, or `axiom` declarations.
3. Every non-internal declaration in `Toy` depends solely on subsets of `{propext, Classical.choice, Quot.sound}` via `Lean.collectAxioms`.
4. For every declaration recorded in `audit/statements.json` (and every Lean name referenced in `results.json`), the SHA-256 of `toString (repr ci.type)` (`statement_sha256`) and the SHA-256 of the sorted newline-joined `"<name> : <repr type>[ := <repr value>]"` entries across all package-local constants reachable from `ci.type`—including inductive constructors and excluding theorem proof terms—(`closure_sha256` and `closure_size`) match `audit/statements.json`, exiting `0` and printing `REVALIDATED`.

### Direct `elan` / `lake` / `python3` build and audit recipe

To reproduce the build, axiom audit, and hash comparison directly without helper scripts, run from the package directory:

```bash
python3 - <<'PY'
import hashlib, json, os, re, shutil, subprocess, tempfile

pkg = os.path.abspath(".")
recorded_stmts = json.load(open(os.path.join(pkg, "audit/statements.json")))["statements"]
recorded_axioms = json.load(open(os.path.join(pkg, "audit/axioms.json")))["declarations"]
allowed = {"propext", "Classical.choice", "Quot.sound"}

def lit(n):
    return "`" + ".".join(
        p if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", p) else f"«{p}»"
        for p in n.split(".")
    )

audit_lean = f"""import Lean
import Toy
open Lean Elab Command

private def roots : List Name := [`Toy]
private def wanted : List Name := [{", ".join(lit(n) for n in sorted(recorded_stmts))}]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with | .inductInfo iv => iv.ctors | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in wanted do
    let some ci := env.find? n | throwError s!"missing {{n}}"
    let cl := closure env (ci.type.getUsedConstants.toList) {{}}
    let clTxt := cl.toList.map (fun c =>
      match env.find? c with
      | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
          (match cc.value? (allowOpaque := true) with
           | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
           | none => "")
      | none => c.toString)
    stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
      ("type_repr", toJson (toString (repr ci.type))),
      ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
"""

with tempfile.TemporaryDirectory(prefix="reval_r19_") as tmp:
    work = os.path.join(tmp, "lean")
    shutil.copytree(os.path.join(pkg, "lean"), work, ignore=shutil.ignore_patterns(".lake", "build"))
    subprocess.run(["lake", "build"], cwd=work, check=True)
    open(os.path.join(work, "RevalidationAudit.lean"), "w").write(audit_lean)
    out = subprocess.run(
        ["lake", "env", "lean", "RevalidationAudit.lean"],
        cwd=work, check=True, capture_output=True, text=True
    ).stdout
    data = json.loads(re.search(r"AUDIT_JSON (\{.*\})", out).group(1))
    got_ax = {d["name"]: sorted(d["axioms"]) for d in data["decls"]}
    assert all(set(v) <= allowed for v in got_ax.values()), "disallowed axiom"
    assert got_ax == recorded_axioms, "axioms.json mismatch"
    for s in data["stmts"]:
        got = {
            "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
            "closure_size": len(s["closure"]),
        }
        assert got == recorded_stmts[s["name"]], f"hash mismatch on {s['name']}"
    print(f"OK: {len(got_ax)} declarations audited; {len(data['stmts'])} statement/closure hashes verified.")
PY
```
