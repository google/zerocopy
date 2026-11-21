# Finite Test Suites, Teaching Sets, and Bounded-State Completeness in Lean 4

## Summary

This package is a kernel-checked Lean 4 toy model (`Toy.Witness`) settling **when passing a finite labeled test or conformance suite uniquely determines an implementation's total behavior (`impl = h`)**. Over any hypothesis class closed under single-point lookup-table overrides on an infinite domain with at least two distinct outputs (`ClosedUnderPointPatches H`, `InfiniteDomain X`, `HasTwoDistinct Y`) — whether unrestricted or strictly restricted (such as `EventuallyFalse : HypothesisClass Nat Bool`) — no finite labeled suite teaches any function. On an infinite domain with at least two distinct outputs, a finite suite can therefore be complete only for a class that breaks single-point patch closure; for example, deterministic Moore machines bounded to `≤ k` states over a finite input alphabet are taught by words up to length `n₁ + k₂ - 2` (target-specific) or `2k - 2` (class-universal). On a finite domain, an exhaustive suite can be complete even for a patch-closed class (proved for `id` in the unrestricted class on `Bool → Bool`); there, breaking the closure is what permits complete suites that leave some input untested: monotone Boolean conjunctions over `m` features (positive literals only, including constant `true` and excluding constant `false`) attain exact per-concept minimum teaching-set size `min (r + 1) m` and teaching dimension `m`. Over an infinite input alphabet, finite teachability of `≤ k`-state Moore behaviors holds at `k = 1` and, whenever outputs take at least two distinct values, fails for every `k ≥ 2`; without any state bound (`FiniteStateMooreBehaviors`), finite teachability fails for every nonempty input alphabet and every output type with at least two distinct values. Operationally, passing a teaching suite certifies `impl = h` across candidate class `C` if and only if every passing member of `C` lies in `H` (`PassingInClass C H S`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers `R1`–`R18` match the cards in **Findings**):

- **R1 (`teaches_iff_hits_disagreement_sets_of_mem_of_consistent`)** — Given `H h` and `Consistent S h`, `S` teaches `h` within `H` if and only if `S.map Prod.fst` hits `{x | g x ≠ h x}` for every rival `g ∈ H` distinct from `h`.
- **R2 (`patchClosed_untested_input_patch_witness`)** — Given `ClosedUnderPointPatches H`, `H h`, `Consistent S h`, untested `x₀ ∉ S.map Prod.fst`, and `y' ≠ h x₀`, `patchAt h x₀ y'` lies in `H`, passes `S`, differs from `h`, and refutes `Teaches H h S`.
- **R3 (`patchClosed_hasUntestedInput_no_teaching`)** — Given `ClosedUnderPointPatches H`, `HasTwoDistinct Y`, and `HasUntestedInput S`, no `h` is taught by `S` within `H`.
- **R4 (`patchClosed_infinite_no_finite_teaching_set`)** — Given `ClosedUnderPointPatches H`, `HasTwoDistinct Y`, and `InfiniteDomain X`, no finite sample `S` teaches any `h : X → Y` within `H`.
- **R5 (`monotone_conj_teaching_set_exact`)** — Unconditionally for all `m : Nat` and `V : Fin m → Bool` with `r = relevantCount V`, `monotoneConjTeachingSet V` teaches `evalMonotoneConj V` within `MonotoneConjunctions m`, has length `min (r + 1) m`, and attains `HasMinTeachingSize` at `min (r + 1) m`.
- **R6 (`monotone_conjunctions_teaching_dimension`)** — Unconditionally for all `m : Nat` (including `m = 0`), `HasTeachingDimension (MonotoneConjunctions m) m`.
- **R7 (`moore_state_equiv_iff_agree_up_to`)** — Unconditionally for every `n`-state Moore machine `M` over arbitrary alphabets `I` and `O`, two states are behaviorally equivalent iff they agree on all words of length `≤ n - 2` (equivalently `< n`).
- **R8 (`moore_two_machine_equiv_iff_agree_up_to`)** — Unconditionally for initialized Moore machines `M₁` (`n₁` states) and `M₂` (`n₂` states), `M₁.behavior = M₂.behavior` iff they agree on all words of length `≤ n₁ + n₂ - 2`.
- **R9 (`moore_bound_sharp`)** — For every `n ≥ 2`, states `0` and `1` of `delayChain n` over `Unit → Bool` agree on words of length `< n - 2` and first disagree at length `n - 2`.
- **R10 (`finite_alphabet_bounded_moore_spec_suite_teaches`)** — Given `CoversAll alphabet` and `BoundedMooreBehaviors I O k₂ M.behavior`, `mooreSpecTestSuite alphabet M k₂` (words up to length `n₁ + k₂ - 2`) teaches `M.behavior` within `BoundedMooreBehaviors I O k₂` (and certifies all `≤ k₂`-state machines even without `hMem` via `finite_alphabet_bounded_moore_spec_suite_certifies`).
- **R11 (`finite_alphabet_bounded_moore_class_suite_teaches`)** — Given `CoversAll alphabet` and `BoundedMooreBehaviors I O k h`, `mooreClassTestSuite alphabet k h` (words up to length `2 * k - 2`) teaches `h` within `BoundedMooreBehaviors I O k`.
- **R12 (`moore_two_machine_bound_sharp`)** — Unconditionally for all `m₁, m₂ : Nat` (`n₁ = m₁ + 1, n₂ = m₂ + 1`), `modCycleMachine m₁ m₂` and `mimicSaturateMachine m₁ m₂` agree on lengths `< m₁ + m₂` and disagree at length `m₁ + m₂ = n₁ + n₂ - 2`.
- **R13 (`bounded_moore_class_suite_depth_sharp`)** — For every `k ≥ 2`, with target `M₁.behavior` for `M₁ = modCycleMachine (k - 1) (k - 1)`, the rival `mimicSaturateMachine (k - 1) (k - 1)` witnesses that neither `labelSample M₁.behavior (wordsUpTo [()] (2 * k - 3))` nor `labelSample M₁.behavior (wordsUpTo [()] (k - 1))` teaches `M₁.behavior` within `BoundedMooreBehaviors Unit Bool k`, so the class-universal depth `2k - 2` of R11 cannot be lowered to `2k - 3` (or to `k - 1`). Other targets can have shorter complete suites.
- **R14 (`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`)** — Given `2 ≤ k`, `InfiniteDomain I`, and `HasTwoDistinct O`, no finite sample teaches any behavior within `BoundedMooreBehaviors I O k` (whereas at `k = 1`, `[([], c)]` teaches every constant behavior over every `I`).
- **R15 (`deviateAfter_agrees_before_and_differs_at`)** — Given `y' ≠ M.behavior (replicate k a)`, `deviateAfter M k y'` (`n * (k + 1)` states) agrees with `M` on words of length `< k` and outputs `y'` on `replicate k a`.
- **R16 (`unbounded_moore_no_finite_teaching_set`)** — Given `Nonempty I` and `HasTwoDistinct O`, no finite sample teaches any behavior within `FiniteStateMooreBehaviors I O`.
- **R17 (`passed_suite_certifies_iff_passingInClass`)** — Given `H h` and `UniqueConsistent H h S`, passing `S` certifies `impl = h` for all `impl ∈ C` iff `PassingInClass C H S` (which is strictly weaker than `SubClass C H`).
- **R18 (`splice_consistent_escapes_class_of_unique`)** — Given `Consistent S h`, `UniqueConsistent H h S`, untested `x₀`, and `outside x₀ ≠ h x₀`, `spliceOutside h outside S` passes `S`, matches `outside` on all untested inputs, differs from `h`, and lies outside `H`.

All non-claims and escape hatches are listed first under **Boundaries**; consult them before relying on any result.

## Applicability

**Model fidelity: this is a toy model.** All definitions live in namespace `Toy.Witness` and are written from scratch for this package; no production software interfaces or codebases are mirrored. They model finite black-box conformance suites for pure total functions `X → Y` (such as decoders, encoders, or classifiers) and deterministic reactive components modeled as Moore machines `MooreMachine I O S`. Connecting any theorem here to a real software artifact requires a separate modeling bridge justifying:

1. **Determinism, purity, and equality.** Outputs depend only on the input (or finite input word from initial state `init`), and behavioral equality corresponds to Lean propositional equality `=` (ignoring non-functional properties such as latency, memory usage, side channels, or observational equivalences over uncanonical representations).
2. **State-output (Moore) vs. transition-output (Mealy) semantics.** In `MooreMachine`, `M.behavior s [] = M.out s` already observes the initial output before applying any input symbol, giving worst-case word lengths `n - 2` (single machine) and `n₁ + n₂ - 2` (two machines). Converting a `k`-state Mealy machine (outputs on transitions) to a Moore machine can multiply the state count by up to `|O|`, and Mealy machines have single-machine bound `n - 1`, so state-count formulas do not transfer verbatim to Mealy state counts.
3. **Reliable reset and full alphabet coverage.** `InitMooreMachine.behavior` evaluates each test word from `M.init`, assuming a reliable reset between words, and R10–R11 require `CoversAll alphabet` (every symbol of `I` appears in `alphabet`).
4. **Independent discharge of class containment (`PassingInClass C H S`).** Passing a finite suite certifies `impl = h` across candidate class `C` only if every `S`-passing candidate in `C` satisfies `H` (e.g., an explicit numeric bound `≤ k` on reachable states, not merely "finite-state").

Every theorem card states `Basis: execution (Lean kernel check)` for the formal Lean theorem and a separate `Basis: derived (modeling bridge)` paragraph explaining when and why the bridge to real systems holds or fails.

**Toolchain and dependencies.** Built with Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`). Core Lean and `Std` only — **no Mathlib** and no external `[[require]]` dependencies (`lean/lakefile.toml` declares a single `[[lean_lib]]`, `Toy`).

**Relationship among subjects in `REPORT.json`.** The Lean 4 toolchain (`leanprover/lean4` `v4.34.1`) elaborates and kernel-checks every theorem and witness in `lean/`. The 11 published papers and 2 Archive of Formal Proofs entries listed in `REPORT.json` are primary prior-art sources (`T0` results restate known theorems in this vocabulary; `T1` results formalize folklore boundaries or minimal-hypothesis converses); the two AFP entries are identified by their Isabelle2026 releases of 2026-10-26, the most recent releases when their entry pages were read. Exact bibliographic records and what portions of each source were inspected appear in **Evidence**. Works cited only for context in non-claims or attributions (Angluin 1987 and 1988, Gold 1967, Goldman and Sloan 1994, Zilles et al. 2011) are recorded in **Evidence** but are not subjects, because none was examined beyond bibliographic metadata or secondary descriptions.

**Proof status.** All 18 main results (`R1`–`R18`), their companions (such as `moore_state_equiv_iff_agree_lt_n` and `finite_alphabet_bounded_moore_spec_suite_certifies`), and all supporting lemmas, definition examples, tightness counterexamples, non-vacuity witnesses, and positive controls are fully proved (`0` `sorry`, `0` warnings) using only subsets of `{propext, Classical.choice, Quot.sound}`.

## Findings

### How to read this section

- Every Lean definition and theorem statement block is printed directly from Lean 4's pretty-printer (`#print` / `#check` with `set_option pp.fieldNotation.generalized false`) on the compiled library. Two entries, `moore_bound_sharp` (R9) and `monotone_conj_m2_r1_exact` (1.6), are printed with `pp.funBinderTypes true` and `pp.numericTypes true` in addition, so that the printed text elaborates to the theorem's statement; the line before each of their blocks says so. Universe parameters print as `u_1`, `u_2` in `#check` output.
- "Unfolded" blocks expand package predicates to elementary quantifiers and equations for direct reading.
- Hypothesis ledgers classify each hypothesis as either `tight` (with a proved counterexample theorem where all other hypotheses hold and the conclusion fails) or `harmless` (with an explanation). No hypothesis has tightness `unknown`.
- Every result carries `Basis: execution (Lean kernel check)` for the mechanized theorem and a separate `Basis: derived (modeling bridge)` claim connecting it to conformance testing.

### Definitions

#### 1.1 Teaching-set framework (`Toy.Witness.Core`)

##### `HypothesisClass`

```lean
@[reducible] def Toy.Witness.HypothesisClass.{u, v} : Type u → Type v → Type (max u v) :=
fun X Y => (X → Y) → Prop
```

*Meant to capture.* A class of admissible candidate implementations `X → Y`.

*Positive examples (proved).* `fun _ => True`, `ConstBoolClass`

*Negative examples (proved).* — (type alias)

##### `Consistent`

```lean
def Toy.Witness.Consistent.{u, v} : {X : Type u} → {Y : Type v} → List (X × Y) → (X → Y) → Prop :=
fun {X} {Y} S h => ∀ (p : X × Y), p ∈ S → h p.fst = p.snd
```

*Meant to capture.* A candidate `h : X → Y` produces the expected output on every input-output pair in `S`.

*Positive examples (proved).* `consistent_pos_example`

*Negative examples (proved).* `consistent_neg_example`

##### `labelSample`

```lean
def Toy.Witness.labelSample.{u, v} : {X : Type u} → {Y : Type v} → (X → Y) → List X → List (X × Y) :=
fun {X} {Y} h inputs => List.map (fun x => (x, h x)) inputs
```

*Meant to capture.* Attaches target `h`'s outputs to a finite list of test inputs `inputs : List X`.

*Positive examples (proved).* `consistent_labelSample`, `map_fst_labelSample`, `length_labelSample`

*Negative examples (proved).* — (total constructor)

##### `UniqueConsistent`

```lean
def Toy.Witness.UniqueConsistent.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → (X → Y) → List (X × Y) → Prop :=
fun {X} {Y} H h S => ∀ (g : X → Y), H g → Toy.Witness.Consistent S g → g = h
```

*Meant to capture.* Every member of `H` that passes `S` is extensionally equal to `h` (isolates the uniqueness/certification half of `Teaches` from `H h` and `Consistent S h`).

*Positive examples (proved).* `uniqueConsistent_pos_example`

*Negative examples (proved).* `uniqueConsistent_neg_example`

##### `Teaches`

```lean
def Toy.Witness.Teaches.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → (X → Y) → List (X × Y) → Prop :=
fun {X} {Y} H h S => H h ∧ Toy.Witness.Consistent S h ∧ Toy.Witness.UniqueConsistent H h S
```

*Meant to capture.* Finite sample `S` uniquely identifies `h ∈ H` against all rivals in `H` (`H h ∧ Consistent S h ∧ UniqueConsistent H h S`).

*Positive examples (proved).* `teaches_pos_example`

*Negative examples (proved).* `teaches_neg_example`

##### `DisagreementSet`

```lean
def Toy.Witness.DisagreementSet.{u, v} : {X : Type u} → {Y : Type v} → (X → Y) → (X → Y) → X → Prop :=
fun {X} {Y} g h x => g x ≠ h x
```

*Meant to capture.* Inputs `x : X` where two candidate functions `g` and `h` differ.

*Positive examples (proved).* `disagreementSet_pos_example`

*Negative examples (proved).* `disagreementSet_neg_example`

##### `HitsAllDisagreements`

```lean
def Toy.Witness.HitsAllDisagreements.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → (X → Y) → List X → Prop :=
fun {X} {Y} H h inputs => ∀ (g : X → Y), H g → g ≠ h → ∃ x, x ∈ inputs ∧ Toy.Witness.DisagreementSet g h x
```

*Meant to capture.* Test-input list `inputs` intersects the disagreement set of every rival `g ∈ H` distinct from `h`.

*Positive examples (proved).* `hitsAllDisagreements_pos_example`

*Negative examples (proved).* `hitsAllDisagreements_neg_example`

##### `HasMinTeachingSize`

```lean
def Toy.Witness.HasMinTeachingSize.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → (X → Y) → Nat → Prop :=
fun {X} {Y} H h k =>
  (∃ S, List.length S = k ∧ Toy.Witness.Teaches H h S) ∧
    ∀ (S : List (X × Y)), Toy.Witness.Teaches H h S → k ≤ List.length S
```

*Meant to capture.* Exact minimum length `k` among all labeled samples teaching `h` within `H` (unique when it exists via `hasMinTeachingSize_unique`).

*Positive examples (proved).* `hasMinTeachingSize_pos_example`

*Negative examples (proved).* `hasMinTeachingSize_neg_example`

##### `HasTeachingDimension`

```lean
def Toy.Witness.HasTeachingDimension.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → Nat → Prop :=
fun {X} {Y} H d =>
  (∀ (h : X → Y), H h → ∃ S, List.length S ≤ d ∧ Toy.Witness.Teaches H h S) ∧
    ∃ h, H h ∧ ∀ (S : List (X × Y)), Toy.Witness.Teaches H h S → d ≤ List.length S
```

*Meant to capture.* Exact worst-case minimum teaching-set size `d` across `H` (unique when it exists via `hasTeachingDimension_unique`). **Edge cases:** holds for no `d` when `H` is empty (the second conjunct requires a witness `h ∈ H`, whereas some conventions define `TD(∅) = 0`) and holds for no `d` when minimum sizes are infinite or unbounded across `H`; holds at `d = 0` for singleton classes such as `MonotoneConjunctions 0`, matching Doliwa et al. (2014).

*Positive examples (proved).* `hasTeachingDimension_pos_example` (`ConstBoolClass`, `d = 1`)

*Negative examples (proved).* `hasTeachingDimension_neg_example_constBool_0`, `hasTeachingDimension_neg_example_constBool_2`, `hasTeachingDimension_neg_example_empty`

##### `ConstBoolClass`

```lean
def Toy.Witness.ConstBoolClass : Toy.Witness.HypothesisClass Bool Bool :=
fun f => (f = fun x => false) ∨ f = fun x => true
```

*Meant to capture.* Two-element benchmark class `{const false, const true}` over `Bool → Bool`.

*Positive examples (proved).* `teaches_pos_example`

*Negative examples (proved).* `isUnrestricted_neg_example`

#### 1.2 Patch-closed and unrestricted classes (`Toy.Witness.Unrestricted`)

##### `IsUnrestricted`

```lean
def Toy.Witness.IsUnrestricted.{u, v} : {X : Type u} → {Y : Type v} → Toy.Witness.HypothesisClass X Y → Prop :=
fun {X} {Y} H => ∀ (f : X → Y), H f
```

*Meant to capture.* Every total function `X → Y` belongs to `H`.

*Positive examples (proved).* `isUnrestricted_pos_example`

*Negative examples (proved).* `isUnrestricted_neg_example`

##### `HasTwoDistinct`

```lean
def Toy.Witness.HasTwoDistinct.{v} : Type v → Prop :=
fun Y => ∃ y₁ y₂, y₁ ≠ y₂
```

*Meant to capture.* Codomain `Y` has at least two distinct observable outputs.

*Positive examples (proved).* `hasTwoDistinct_pos_example` (`Bool`)

*Negative examples (proved).* `hasTwoDistinct_neg_example` (`Unit`)

##### `InfiniteDomain`

```lean
def Toy.Witness.InfiniteDomain.{u} : Type u → Prop :=
fun X => ∀ (L : List X), ∃ x, ¬x ∈ L
```

*Meant to capture.* No finite list enumerates every element of `X`.

*Positive examples (proved).* `infiniteDomain_pos_example` (`Nat`)

*Negative examples (proved).* `infiniteDomain_neg_example` (`Bool`)

##### `HasUntestedInput`

```lean
def Toy.Witness.HasUntestedInput.{u, v} : {X : Type u} → {Y : Type v} → List (X × Y) → Prop :=
fun {X} {Y} S => ∃ x, ¬x ∈ List.map Prod.fst S
```

*Meant to capture.* Finite labeled sample `S` omits at least one input in `X`.

*Positive examples (proved).* `hasUntestedInput_pos_example`

*Negative examples (proved).* `hasUntestedInput_neg_example`

##### `patchAt`

```lean
def Toy.Witness.patchAt.{u, v} : {X : Type u} → {Y : Type v} → (X → Y) → X → Y → X → Y :=
fun {X} {Y} h x₀ y' x => if x = x₀ then y' else h x
```

*Meant to capture.* Single-point lookup-table override of `h` at `x₀` with value `y'` (`if x = x₀ then y' else h x`).

*Positive examples (proved).* `patchAt_self`, `patchAt_of_ne`

*Negative examples (proved).* — (total constructor)

##### `ClosedUnderPointPatches`

```lean
def Toy.Witness.ClosedUnderPointPatches.{u, v} : {X : Type u} → {Y : Type v} → Toy.Witness.HypothesisClass X Y → Prop :=
fun {X} {Y} H => ∀ (h : X → Y) (x₀ : X) (y' : Y), H h → H (Toy.Witness.patchAt h x₀ y')
```

*Meant to capture.* Modifying any member `h ∈ H` at one input `x₀` to any `y'` remains in `H`; strictly weaker than `IsUnrestricted` (`isUnrestricted_implies_closedUnderPointPatches`).

*Positive examples (proved).* `closedUnderPointPatches_pos_example` (`EventuallyFalse`)

*Negative examples (proved).* `closedUnderPointPatches_neg_example` (`ConstBoolClass`)

##### `EventuallyFalse`

```lean
def Toy.Witness.EventuallyFalse : Toy.Witness.HypothesisClass Nat Bool :=
fun f => ∃ N, ∀ (x : Nat), N ≤ x → f x = false
```

*Meant to capture.* Functions `Nat → Bool` that equal `false` for all sufficiently large inputs; strictly restricted yet closed under point patches.

*Positive examples (proved).* `eventuallyFalse_closedUnderPointPatches`

*Negative examples (proved).* `eventuallyFalse_not_unrestricted`

#### 1.3 Monotone Boolean conjunctions (`Toy.Witness.Conjunctions`)

##### `BoolAssignment`

```lean
@[reducible] def Toy.Witness.BoolAssignment : Nat → Type :=
fun m => Fin m → Bool
```

*Meant to capture.* Boolean feature vector `Fin m → Bool` over `m` variables.

*Positive examples (proved).* `evalMonotoneConj_all_true`

*Negative examples (proved).* — (type alias)

##### `evalMonotoneConj`

```lean
def Toy.Witness.evalMonotoneConj : {m : Nat} → (Fin m → Bool) → Toy.Witness.BoolAssignment m → Bool :=
fun {m} V x => List.all (List.finRange m) fun i => !V i || x i
```

*Meant to capture.* Evaluates positive-literal conjunction `⋀_{i ∈ V} x_i`; empty conjunction (`V = const false`) evaluates to constant `true`.

*Positive examples (proved).* `monotoneConjunctions_pos_example`

*Negative examples (proved).* `monotoneConjunctions_neg_example_const_false`

##### `relevantCount`

```lean
def Toy.Witness.relevantCount : {m : Nat} → (Fin m → Bool) → Nat :=
fun {m} V => List.length (List.filter (fun i => V i) (List.finRange m))
```

*Meant to capture.* Number of relevant variables (`V i = true`) in `V`.

*Positive examples (proved).* `relevantCount_le`

*Negative examples (proved).* — (total function)

##### `MonotoneConjunctions`

```lean
def Toy.Witness.MonotoneConjunctions : (m : Nat) → Toy.Witness.HypothesisClass (Toy.Witness.BoolAssignment m) Bool :=
fun m f => ∃ V, Toy.Witness.evalMonotoneConj V = f
```

*Meant to capture.* Class of positive-literal conjunctions over `m` Boolean features (excludes `const false` and disjunctions such as `x 0 || x 1`).

*Positive examples (proved).* `monotoneConjunctions_pos_example` (`x 0 && x 1`)

*Negative examples (proved).* `monotoneConjunctions_neg_example_or` (`x 0 || x 1`), `monotoneConjunctions_neg_example_const_false` (`const false`)

##### `flipBit`

```lean
def Toy.Witness.flipBit : {m : Nat} → Fin m → Toy.Witness.BoolAssignment m :=
fun {m} i k => decide (k ≠ i)
```

*Meant to capture.* Assignment setting coordinate `i` to `false` and all other coordinates to `true`.

*Positive examples (proved).* `monotone_conj_m2_all_teaches`

*Negative examples (proved).* — (total constructor)

##### `monotoneConjNegExamples`

```lean
def Toy.Witness.monotoneConjNegExamples : {m : Nat} → (Fin m → Bool) → List (Toy.Witness.BoolAssignment m × Bool) :=
fun {m} V => List.map (fun i => (Toy.Witness.flipBit i, false)) (List.filter (fun i => V i) (List.finRange m))
```

*Meant to capture.* One negative example `(flipBit i, false)` for each relevant feature `i`.

*Positive examples (proved).* `monotoneConjNegExamples_length`

*Negative examples (proved).* — (total constructor)

##### `monotoneConjTeachingSet`

```lean
def Toy.Witness.monotoneConjTeachingSet : {m : Nat} → (Fin m → Bool) → List (Toy.Witness.BoolAssignment m × Bool) :=
fun {m} V =>
  if Toy.Witness.relevantCount V < m then (V, true) :: Toy.Witness.monotoneConjNegExamples V
  else Toy.Witness.monotoneConjNegExamples V
```

*Meant to capture.* Explicit canonical teaching set of length `min (relevantCount V + 1) m` (`(V, true)` prepended iff `relevantCount V < m`).

*Positive examples (proved).* `monotoneConjTeachingSet_length`, `monotoneConjTeachingSet_nodup`

*Negative examples (proved).* — (total constructor)

#### 1.4 Deterministic Moore machines and witness constructions (`Toy.Witness.Moore`)

##### `MooreMachine`

```lean
structure Toy.Witness.MooreMachine.{u, v, w} (I : Type u) (O : Type v) (S : Type w) : Type (max (max u v) w)
number of parameters: 3
fields:
  Toy.Witness.MooreMachine.step : S → I → S
  Toy.Witness.MooreMachine.out : S → O
constructor:
  Toy.Witness.MooreMachine.mk.{u, v, w} {I : Type u} {O : Type v} {S : Type w} (step : S → I → S) (out : S → O) :
    Toy.Witness.MooreMachine I O S
```

*Meant to capture.* Deterministic transition system `(step : S → I → S, out : S → O)` over input alphabet `I`, output alphabet `O`, and state space `S`.

*Positive examples (proved).* `stateEquiv_pos_example`

*Negative examples (proved).* — (record type)

##### `MooreMachine.run`

```lean
def Toy.Witness.MooreMachine.run.{u, v, w} : {I : Type u} →
  {O : Type v} → {S : Type w} → Toy.Witness.MooreMachine I O S → S → List I → S :=
fun {I} {O} {S} M x x_1 => List.brecOn (motive := fun x => S → S) x_1 (Toy.Witness.MooreMachine.run._f M) x
```

*Meant to capture.* Executes input word `w : List I` from state `s` (`run_append`).

*Positive examples (proved).* `MooreMachine.run_append`

*Negative examples (proved).* — (total function)

##### `MooreMachine.behavior`

```lean
def Toy.Witness.MooreMachine.behavior.{u, v, w} : {I : Type u} →
  {O : Type v} → {S : Type w} → Toy.Witness.MooreMachine I O S → S → List I → O :=
fun {I} {O} {S} M s w => M.out (Toy.Witness.MooreMachine.run M s w)
```

*Meant to capture.* Output observed after executing `w` from state `s` (`[]` observes `M.out s`).

*Positive examples (proved).* `moore_state_equiv_iff_agree_up_to_nonvacuity`

*Negative examples (proved).* — (total function)

##### `StateEquiv`

```lean
def Toy.Witness.StateEquiv.{u, v, w} : {I : Type u} →
  {O : Type v} → {S : Type w} → Toy.Witness.MooreMachine I O S → S → S → Prop :=
fun {I} {O} {S} M s t => Toy.Witness.MooreMachine.behavior M s = Toy.Witness.MooreMachine.behavior M t
```

*Meant to capture.* Two states of `M` produce identical outputs on all finite input words.

*Positive examples (proved).* `stateEquiv_pos_example`

*Negative examples (proved).* `stateEquiv_neg_example`

##### `AgreeUpTo`

```lean
def Toy.Witness.AgreeUpTo.{u, v, w} : {I : Type u} →
  {O : Type v} → {S : Type w} → Toy.Witness.MooreMachine I O S → S → S → Nat → Prop :=
fun {I} {O} {S} M s t k =>
  ∀ (w : List I), List.length w ≤ k → Toy.Witness.MooreMachine.behavior M s w = Toy.Witness.MooreMachine.behavior M t w
```

*Meant to capture.* Two states of `M` agree on all input words of length at most `k`.

*Positive examples (proved).* `agreeUpTo_pos_example`

*Negative examples (proved).* `agreeUpTo_neg_example`

##### `InitMooreMachine`

```lean
structure Toy.Witness.InitMooreMachine.{u, v} (I : Type u) (O : Type v) (n : Nat) : Type (max u v)
number of parameters: 3
parents:
  Toy.Witness.InitMooreMachine.toMooreMachine : Toy.Witness.MooreMachine I O (Fin n)
fields:
  Toy.Witness.MooreMachine.step : Fin n → I → Fin n
  Toy.Witness.MooreMachine.out : Fin n → O
  Toy.Witness.InitMooreMachine.init : Fin n
constructor:
  Toy.Witness.InitMooreMachine.mk.{u, v} {I : Type u} {O : Type v} {n : Nat}
    (toMooreMachine : Toy.Witness.MooreMachine I O (Fin n)) (init : Fin n) : Toy.Witness.InitMooreMachine I O n
field notation resolution order:
  Toy.Witness.InitMooreMachine, Toy.Witness.MooreMachine
```

*Meant to capture.* Deterministic Moore machine over `Fin n` states with designated initial state `init`.

*Positive examples (proved).* `constMoore`, `altMachine2`, `latchMachine2`

*Negative examples (proved).* — (record type)

##### `InitMooreMachine.behavior`

```lean
def Toy.Witness.InitMooreMachine.behavior.{u, v} : {I : Type u} →
  {O : Type v} → {n : Nat} → Toy.Witness.InitMooreMachine I O n → List I → O :=
fun {I} {O} {n} M => Toy.Witness.MooreMachine.behavior M.toMooreMachine M.init
```

*Meant to capture.* Input-output behavior `List I → O` starting from `M.init`.

*Positive examples (proved).* `altMachine2_behavior`

*Negative examples (proved).* — (total function)

##### `BoundedMooreBehaviors`

```lean
def Toy.Witness.BoundedMooreBehaviors.{u, v} : (I : Type u) →
  (O : Type v) → Nat → Toy.Witness.HypothesisClass (List I) O :=
fun I O k f => ∃ m, m ≤ k ∧ ∃ M, Toy.Witness.InitMooreMachine.behavior M = f
```

*Meant to capture.* Behaviors `List I → O` realizable by an initialized Moore machine with at most `k` states.

*Positive examples (proved).* `boundedMooreBehaviors_pos_example`

*Negative examples (proved).* `boundedMooreBehaviors_neg_example`

##### `FiniteStateMooreBehaviors`

```lean
def Toy.Witness.FiniteStateMooreBehaviors.{u, v} : (I : Type u) →
  (O : Type v) → Toy.Witness.HypothesisClass (List I) O :=
fun I O f => ∃ n M, Toy.Witness.InitMooreMachine.behavior M = f
```

*Meant to capture.* Behaviors realizable by some finite-state Moore machine without an a priori numeric state ceiling.

*Positive examples (proved).* `finiteStateMooreBehaviors_pos_example`

*Negative examples (proved).* `finiteStateMooreBehaviors_neg_example` (equal `false`/`true` count via Myhill–Nerode pigeonhole)

##### `CoversAll`

```lean
def Toy.Witness.CoversAll.{u} : {α : Type u} → List α → Prop :=
fun {α} L => ∀ (a : α), a ∈ L
```

*Meant to capture.* Finite list `L` enumerating every symbol of input alphabet `α`.

*Positive examples (proved).* `coversAll_pos_example` (`[false, true]`)

*Negative examples (proved).* `coversAll_neg_example` (`[false]`)

##### `wordsOfLength`

```lean
def Toy.Witness.wordsOfLength.{u} : {I : Type u} → List I → Nat → List (List I) :=
fun {I} alphabet x => Nat.brecOn x (Toy.Witness.wordsOfLength._f alphabet)
```

*Meant to capture.* All words of exact length `k` formed from `alphabet`.

*Positive examples (proved).* `mem_wordsOfLength_iff`

*Negative examples (proved).* — (total constructor)

##### `wordsUpTo`

```lean
def Toy.Witness.wordsUpTo.{u} : {I : Type u} → List I → Nat → List (List I) :=
fun {I} alphabet x => Nat.brecOn x (Toy.Witness.wordsUpTo._f alphabet)
```

*Meant to capture.* All words of length at most `L` formed from `alphabet`.

*Positive examples (proved).* `mem_wordsUpTo_iff`

*Negative examples (proved).* — (total constructor)

##### `mooreSpecTestSuite`

```lean
def Toy.Witness.mooreSpecTestSuite.{u, v} : {I : Type u} →
  {O : Type v} → {n₁ : Nat} → List I → Toy.Witness.InitMooreMachine I O n₁ → Nat → List (List I × O) :=
fun {I} {O} {n₁} alphabet M k₂ =>
  Toy.Witness.labelSample (Toy.Witness.InitMooreMachine.behavior M) (Toy.Witness.wordsUpTo alphabet (n₁ + k₂ - 2))
```

*Meant to capture.* Words up to length `n₁ + k₂ - 2` over `alphabet` labeled by `n₁`-state specification `M`.

*Positive examples (proved).* `finite_alphabet_bounded_moore_spec_suite_teaches`

*Negative examples (proved).* — (total constructor)

##### `mooreClassTestSuite`

```lean
def Toy.Witness.mooreClassTestSuite.{u, v} : {I : Type u} →
  {O : Type v} → List I → Nat → (List I → O) → List (List I × O) :=
fun {I} {O} alphabet k h => Toy.Witness.labelSample h (Toy.Witness.wordsUpTo alphabet (2 * k - 2))
```

*Meant to capture.* Universal `k`-state suite: words up to length `2 * k - 2` over `alphabet` labeled by `h`.

*Positive examples (proved).* `finite_alphabet_bounded_moore_class_suite_teaches`

*Negative examples (proved).* — (total constructor)

##### `disjointUnion`

```lean
def Toy.Witness.disjointUnion.{u, v} : {I : Type u} →
  {O : Type v} →
    {n₁ n₂ : Nat} →
      Toy.Witness.InitMooreMachine I O n₁ →
        Toy.Witness.InitMooreMachine I O n₂ → Toy.Witness.MooreMachine I O (Fin (n₁ + n₂)) :=
fun {I} {O} {n₁ n₂} M₁ M₂ =>
  {
    step := fun s a =>
      if h : ↑s < n₁ then Toy.Witness.inlFin (M₁.step ⟨↑s, h⟩ a) else Toy.Witness.inrFin (M₂.step ⟨↑s - n₁, ⋯⟩ a),
    out := fun s => if h : ↑s < n₁ then M₁.out ⟨↑s, h⟩ else M₂.out ⟨↑s - n₁, ⋯⟩ }
```

*Meant to capture.* Disjoint union of `n₁`-state `M₁` and `n₂`-state `M₂` into an `(n₁ + n₂)`-state Moore machine via `inlFin` and `inrFin`.

*Positive examples (proved).* `behavior_disjointUnion_inl`, `behavior_disjointUnion_inr`

*Negative examples (proved).* — (total constructor)

##### `delayChain`

```lean
def Toy.Witness.delayChain : (n : Nat) → Toy.Witness.MooreMachine Unit Bool (Fin n) :=
fun n => { step := fun i x => if h : ↑i + 1 < n then ⟨↑i + 1, h⟩ else i, out := fun i => decide (↑i + 1 = n) }
```

*Meant to capture.* Unary `n`-state saturating chain `0 → 1 → … → n - 1 → n - 1` accepting only at state `n - 1`.

*Positive examples (proved).* `moore_bound_sharp`

*Negative examples (proved).* — (witness family)

##### `modCycleMachine`

```lean
def Toy.Witness.modCycleMachine : (m₁ : Nat) → Nat → Toy.Witness.InitMooreMachine Unit Bool (m₁ + 1) :=
fun m₁ m₂ =>
  { step := fun s x => ⟨(↑s + 1) % (m₁ + 1), ⋯⟩, out := fun s => decide (↑s = (m₁ + m₂) % (m₁ + 1)), init := ⟨0, ⋯⟩ }
```

*Meant to capture.* Unary `(m₁ + 1)`-state cycle outputting `true` only at residue `(m₁ + m₂) % (m₁ + 1)`.

*Positive examples (proved).* `moore_two_machine_bound_sharp`

*Negative examples (proved).* — (witness family)

##### `mimicSaturateMachine`

```lean
def Toy.Witness.mimicSaturateMachine : Nat → (m₂ : Nat) → Toy.Witness.InitMooreMachine Unit Bool (m₂ + 1) :=
fun m₁ m₂ =>
  { step := fun s x => if h : ↑s + 1 < m₂ + 1 then ⟨↑s + 1, h⟩ else s,
    out := fun s => if ↑s < m₂ then decide (↑s % (m₁ + 1) = (m₁ + m₂) % (m₁ + 1)) else false, init := ⟨0, ⋯⟩ }
```

*Meant to capture.* Unary `(m₂ + 1)`-state saturating chain mimicking `modCycleMachine m₁ m₂` on steps `< m₂` and outputting `false` at absorbing state `m₂`.

*Positive examples (proved).* `moore_two_machine_bound_sharp`

*Negative examples (proved).* — (witness family)

##### `constMoore`

```lean
def Toy.Witness.constMoore.{u, v} : {I : Type u} → {O : Type v} → O → Toy.Witness.InitMooreMachine I O 1 :=
fun {I} {O} y => { step := fun s x => s, out := fun x => y, init := ⟨0, Toy.Witness.constMoore._proof_1⟩ }
```

*Meant to capture.* 1-state constant Moore machine always outputting `y`.

*Positive examples (proved).* `constMoore_behavior`

*Negative examples (proved).* — (witness family)

##### `altMachine2`

```lean
def Toy.Witness.altMachine2 : Toy.Witness.InitMooreMachine Unit Bool 2 :=
{ step := fun s x => if ↑s = 0 then ⟨1, Toy.Witness.altMachine2._proof_1⟩ else ⟨0, Toy.Witness.altMachine2._proof_2⟩,
  out := fun s => decide (↑s = 1), init := ⟨0, Toy.Witness.altMachine2._proof_2⟩ }
```

*Meant to capture.* 2-state unary machine alternating `false, true, false, …`.

*Positive examples (proved).* `two_state_moore_length_lt_k_insufficient`

*Negative examples (proved).* — (witness)

##### `latchMachine2`

```lean
def Toy.Witness.latchMachine2 : Toy.Witness.InitMooreMachine Unit Bool 2 :=
{ step := fun x x_1 => ⟨1, Toy.Witness.altMachine2._proof_1⟩, out := fun s => decide (↑s = 1),
  init := ⟨0, Toy.Witness.altMachine2._proof_2⟩ }
```

*Meant to capture.* 2-state unary machine outputting `false, true, true, …`.

*Positive examples (proved).* `two_state_moore_length_lt_k_insufficient`

*Negative examples (proved).* — (witness)

##### `deviateAfter`

```lean
def Toy.Witness.deviateAfter.{u, v} : {I : Type u} →
  {O : Type v} →
    {n : Nat} → Toy.Witness.InitMooreMachine I O n → (k : Nat) → O → Toy.Witness.InitMooreMachine I O (n * (k + 1)) :=
fun {I} {O} {n} M k y' =>
  {
    step := fun idx a =>
      have s := Toy.Witness.decodeState✝ idx;
      let c := Toy.Witness.decodeCount✝ idx;
      Toy.Witness.encodePair✝ (M.step s a) ⟨min (↑c + 1) k, ⋯⟩,
    out := fun idx =>
      have s := Toy.Witness.decodeState✝ idx;
      have c := Toy.Witness.decodeCount✝ idx;
      if ↑c < k then M.out s else y',
    init := Toy.Witness.encodePair✝ M.init ⟨0, ⋯⟩ }
```

*Meant to capture.* Product of `n`-state `M` with a `(k + 1)`-state saturating step counter, encoded in `Fin (n * (k + 1))` as `idx = s * (k + 1) + c` for machine state `s` and counter `c` (the inaccessible names marked `✝` in the printed definition are internal encoders: `encodePair✝ s c = s * (k + 1) + c`, `decodeState✝ idx = idx / (k + 1)`, `decodeCount✝ idx = idx % (k + 1)`): agrees with `M` for `< k` steps and switches permanently to `y'` at step `k`.

*Positive examples (proved).* `deviateAfter_agrees_before_and_differs_at`

*Negative examples (proved).* — (witness family)

#### 1.5 Class membership and off-suite splicing (`Toy.Witness.Soundness`)

##### `SubClass`

```lean
def Toy.Witness.SubClass.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → Toy.Witness.HypothesisClass X Y → Prop :=
fun {X} {Y} C H => ∀ (f : X → Y), C f → H f
```

*Meant to capture.* Every candidate implementation in `C` belongs to `H` (`∀ f, C f → H f`).

*Positive examples (proved).* `subClass_pos_example`

*Negative examples (proved).* `subClass_neg_example`

##### `PassingInClass`

```lean
def Toy.Witness.PassingInClass.{u, v} : {X : Type u} →
  {Y : Type v} → Toy.Witness.HypothesisClass X Y → Toy.Witness.HypothesisClass X Y → List (X × Y) → Prop :=
fun {X} {Y} C H S => ∀ (f : X → Y), C f → Toy.Witness.Consistent S f → H f
```

*Meant to capture.* Every `S`-passing candidate in `C` belongs to `H`; strictly weaker than `SubClass` (`subClass_implies_passingInClass`, `passingInClass_pos_example`).

*Positive examples (proved).* `passingInClass_pos_example`

*Negative examples (proved).* `passingInClass_neg_example`

##### `spliceOutside`

```lean
def Toy.Witness.spliceOutside.{u, v} : {X : Type u} → {Y : Type v} → (X → Y) → (X → Y) → List (X × Y) → X → Y :=
fun {X} {Y} h outside S x => if x ∈ List.map Prod.fst S then h x else outside x
```

*Meant to capture.* Splices target `h` on tested inputs `S.map Prod.fst` with arbitrary function `outside` on untested inputs.

*Positive examples (proved).* `spliceOutside_of_mem`, `spliceOutside_of_not_mem`, `spliceOutside_consistent`

*Negative examples (proved).* — (total constructor)


#### 1.6 Supporting structural lemmas and concrete checks (proved)

`monotone_conj_m2_r1_exact` is printed with `pp.funBinderTypes true` and `pp.numericTypes true` in addition, which show that `i` ranges over `Fin 2` and that `↑i = 0` compares natural numbers.

```lean
@Toy.Witness.isUnrestricted_implies_closedUnderPointPatches : ∀ {X : Type u_1} {Y : Type u_2}
  {H : Toy.Witness.HypothesisClass X Y}, Toy.Witness.IsUnrestricted H → Toy.Witness.ClosedUnderPointPatches H
Toy.Witness.eventuallyFalse_closedUnderPointPatches : Toy.Witness.ClosedUnderPointPatches Toy.Witness.EventuallyFalse
Toy.Witness.eventuallyFalse_not_unrestricted : ¬Toy.Witness.IsUnrestricted Toy.Witness.EventuallyFalse
@Toy.Witness.hasMinTeachingSize_unique : ∀ {X : Type u_1} {Y : Type u_2} {H : Toy.Witness.HypothesisClass X Y}
  {h : X → Y} {k₁ k₂ : Nat}, Toy.Witness.HasMinTeachingSize H h k₁ → Toy.Witness.HasMinTeachingSize H h k₂ → k₁ = k₂
@Toy.Witness.hasTeachingDimension_unique : ∀ {X : Type u_1} {Y : Type u_2} {H : Toy.Witness.HypothesisClass X Y}
  {d₁ d₂ : Nat}, Toy.Witness.HasTeachingDimension H d₁ → Toy.Witness.HasTeachingDimension H d₂ → d₁ = d₂
@Toy.Witness.monotoneConjTeachingSet_length : ∀ {m : Nat} (V : Fin m → Bool),
  List.length (Toy.Witness.monotoneConjTeachingSet V) = min (Toy.Witness.relevantCount V + 1) m
@Toy.Witness.monotoneConjTeachingSet_nodup : ∀ {m : Nat} (V : Fin m → Bool),
  List.Nodup (Toy.Witness.monotoneConjTeachingSet V)
Toy.Witness.monotone_conj_m2_r0_exact : have V := fun x => false;
Toy.Witness.Teaches (Toy.Witness.MonotoneConjunctions 2) (Toy.Witness.evalMonotoneConj V)
    (Toy.Witness.monotoneConjTeachingSet V) ∧
  List.length (Toy.Witness.monotoneConjTeachingSet V) = min (Toy.Witness.relevantCount V + 1) 2 ∧
    Toy.Witness.HasMinTeachingSize (Toy.Witness.MonotoneConjunctions 2) (Toy.Witness.evalMonotoneConj V)
      (min (Toy.Witness.relevantCount V + 1) 2)
Toy.Witness.monotone_conj_m2_r1_exact : have V := fun (i : Fin (2 : Nat)) => decide (↑i = (0 : Nat));
Toy.Witness.Teaches (Toy.Witness.MonotoneConjunctions (2 : Nat)) (Toy.Witness.evalMonotoneConj V)
    (Toy.Witness.monotoneConjTeachingSet V) ∧
  List.length (Toy.Witness.monotoneConjTeachingSet V) = min (Toy.Witness.relevantCount V + (1 : Nat)) (2 : Nat) ∧
    Toy.Witness.HasMinTeachingSize (Toy.Witness.MonotoneConjunctions (2 : Nat)) (Toy.Witness.evalMonotoneConj V)
      (min (Toy.Witness.relevantCount V + (1 : Nat)) (2 : Nat))
Toy.Witness.monotone_conj_m2_r2_exact : have V := fun x => true;
Toy.Witness.Teaches (Toy.Witness.MonotoneConjunctions 2) (Toy.Witness.evalMonotoneConj V)
    (Toy.Witness.monotoneConjTeachingSet V) ∧
  List.length (Toy.Witness.monotoneConjTeachingSet V) = min (Toy.Witness.relevantCount V + 1) 2 ∧
    Toy.Witness.HasMinTeachingSize (Toy.Witness.MonotoneConjunctions 2) (Toy.Witness.evalMonotoneConj V)
      (min (Toy.Witness.relevantCount V + 1) 2)
Toy.Witness.monotone_conjunctions_m0_td : Toy.Witness.HasTeachingDimension (Toy.Witness.MonotoneConjunctions 0) 0
@Toy.Witness.bounded_one_state_moore_single_example_teaches : ∀ {I : Type u_1} {O : Type u_2} (c : O),
  Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors I O 1) (fun x => c) [([], c)]
Toy.Witness.two_state_moore_length_lt_k_insufficient : Toy.Witness.BoundedMooreBehaviors Unit Bool 2
    (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2) ∧
  Toy.Witness.BoundedMooreBehaviors Unit Bool 2 (Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2) ∧
    (∀ (w : List Unit),
        List.length w < 2 →
          Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2 w =
            Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2 w) ∧
      Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2 [(), ()] ≠
          Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2 [(), ()] ∧
        ¬Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors Unit Bool 2)
            (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2)
            (Toy.Witness.labelSample (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2)
              (Toy.Witness.wordsUpTo [()] 1))
@Toy.Witness.subClass_implies_passingInClass : ∀ {X : Type u_1} {Y : Type u_2} {C H : Toy.Witness.HypothesisClass X Y}
  {S : List (X × Y)}, Toy.Witness.SubClass C H → Toy.Witness.PassingInClass C H S
Toy.Witness.passingInClass_pos_example : have C := fun f => Toy.Witness.ConstBoolClass f ∨ f = id;
have S := [(false, true)];
Toy.Witness.PassingInClass C Toy.Witness.ConstBoolClass S ∧ ¬Toy.Witness.SubClass C Toy.Witness.ConstBoolClass
Toy.Witness.certification_holds_although_C_escapes_H : have C := fun f => Toy.Witness.ConstBoolClass f ∨ f = id;
have h := fun x => true;
have S := [(false, true)];
¬Toy.Witness.SubClass C Toy.Witness.ConstBoolClass ∧
  Toy.Witness.Teaches Toy.Witness.ConstBoolClass h S ∧
    ∀ (impl : Bool → Bool), C impl → Toy.Witness.Consistent S impl → impl = h
Toy.Witness.passed_teaching_suite_ce_not_subclass : have C := fun x => True;
have H := Toy.Witness.MonotoneConjunctions 2;
have V := fun x => true;
have h := Toy.Witness.evalMonotoneConj V;
have S := Toy.Witness.monotoneConjTeachingSet V;
¬Toy.Witness.SubClass C H ∧
  Toy.Witness.Teaches H h S ∧
    ¬∀ (impl : Toy.Witness.BoolAssignment 2 → Bool), C impl → Toy.Witness.Consistent S impl → impl = h
```

### Result cards

#### R1 — Hitting-set characterization of teaching sets

- **Kind:** characterization. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Core.lean`.
- **Lean:** `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent`

**Plain claim.** For any hypothesis class H over X -> Y, target function h in H, and finite labeled sample S consistent with h, S teaches h within H if and only if the input coordinates of S hit the disagreement set {x | g x != h x} of every rival g in H distinct from h.

```lean
@Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  H h →
    Toy.Witness.Consistent S h →
      (Toy.Witness.Teaches H h S ↔ Toy.Witness.HitsAllDisagreements H h (List.map Prod.fst S))
```

Unfolded (prose):

```text
for all types X, Y, class H : (X → Y) → Prop, target h : X → Y, sample S : List (X × Y):
  H h
→ (∀ p ∈ S, h p.1 = p.2)
→ ( (H h ∧ (∀ p ∈ S, h p.1 = p.2) ∧ ∀ g, H g → (∀ p ∈ S, g p.1 = p.2) → g = h)
    ↔ (∀ g, H g → g ≠ h → ∃ x ∈ S.map Prod.fst, g x ≠ h x) )
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hh : H h` | Ensures the target function belongs to H; Teaches H h S requires H h, whereas HitsAllDisagreements H h does not. | `tight` | `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_not_in_H` |
| `hcon : Consistent S h` | Ensures S carries the true outputs of h; an inconsistent sample can still cover every disagreement input without teaching h. | `tight` | `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_inconsistent` |
| `X : Type u, Y : Type v` | Arbitrary domain and codomain types across any universes; no finiteness or decidability is required. | `harmless` | — |
| `H : HypothesisClass X Y, h : X → Y, S : List (X × Y)` | Universally quantified hypothesis class, target, and labeled sample. | `harmless` | — |

**Depth: shallow.** Equivalence follows by unpacking `Teaches` and `HitsAllDisagreements` using classical contradiction on extensional equality.

**Non-vacuity witness.** H = ConstBoolClass = {const false, const true} over Bool -> Bool, h = const true, and S = [(false, true)], where both H h and Consistent S h hold. (`Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_nonvacuity`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003 (Section 5 set-cover equivalence in WUCS-92-28).
- Ayumi Shinohara and Satoru Miyano, "Teachability in Computational Learning", New Generation Computing 8(4):337-347, 1991, DOI 10.1007/BF03037091.
- Martin Anthony, Graham Brightwell, and John Shawe-Taylor, "On specifying Boolean functions by labelled examples", Discrete Applied Mathematics 61(1):1-25, 1995, DOI 10.1016/0166-218X(94)00007-Z.
- Timothy A. Budd and Dana Angluin, "Two notions of correctness and their relation to testing", Acta Informatica 18(1):31-45, 1982, DOI 10.1007/BF00625279 (two notions of test-data correctness, automatic detection/generation, and relation to program equivalence).
- Kathleen Romanik and Carl Smith, "Testing geometric objects", Computational Geometry 4(3):157-176, 1994, DOI 10.1016/0925-7721(94)90005-1 (testing sets determining equivalence to a target concept).

**Design question.** Reduces checking whether a finite conformance suite uniquely pins down a target implementation within a class H (given h in H and Consistent S h) to verifying that every distinct rival in H is separated by at least one input in the suite.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Checking whether a conformance suite `S` pins down a pure deterministic specification `h` within a modeled candidate class `H` reduces to checking that every rival `g ∈ H` differs from `h` on at least one tested input in `S`, provided `h ∈ H` and `S` carries `h`'s true outputs. Does not establish either `H h` or `Consistent S h`, and does not supply an algorithm for finding minimal hitting sets.

#### R2 — Untested-input lookup-table obstruction for patch-closed classes

- **Kind:** impossibility. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Unrestricted.lean`.
- **Lean:** `Toy.Witness.patchClosed_untested_input_patch_witness`

**Plain claim.** If H is closed under single-point patches (in particular if H is unrestricted; see corollary unrestricted_untested_input_patch_witness), h belongs to H, S is consistent with h, x0 does not appear among the inputs of S, and y' != h x0, then the explicit point-patch lookup table patchAt h x0 y' belongs to H, passes S, and differs from h, so S does not teach h within H.

```lean
@Toy.Witness.patchClosed_untested_input_patch_witness : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)) (x₀ : X) (y' : Y),
  Toy.Witness.ClosedUnderPointPatches H →
    H h →
      Toy.Witness.Consistent S h →
        ¬x₀ ∈ List.map Prod.fst S →
          y' ≠ h x₀ →
            H (Toy.Witness.patchAt h x₀ y') ∧
              Toy.Witness.Consistent S (Toy.Witness.patchAt h x₀ y') ∧
                Toy.Witness.patchAt h x₀ y' ≠ h ∧ ¬Toy.Witness.Teaches H h S

@Toy.Witness.unrestricted_untested_input_patch_witness : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)) (x₀ : X) (y' : Y),
  Toy.Witness.IsUnrestricted H →
    Toy.Witness.Consistent S h →
      ¬x₀ ∈ List.map Prod.fst S →
        y' ≠ h x₀ →
          H (Toy.Witness.patchAt h x₀ y') ∧
            Toy.Witness.Consistent S (Toy.Witness.patchAt h x₀ y') ∧
              Toy.Witness.patchAt h x₀ y' ≠ h ∧ ¬Toy.Witness.Teaches H h S
```

Unfolded (prose):

```text
for all types X, Y, class H, target h, sample S, input x₀ : X, output y' : Y:
  (∀ f x y, H f → H (fun z => if z = x then y else f z))
→ H h
→ (∀ p ∈ S, h p.1 = p.2)
→ x₀ ∉ S.map Prod.fst
→ y' ≠ h x₀
→ let g := fun z => if z = x₀ then y' else h z;
  H g ∧ (∀ p ∈ S, g p.1 = p.2) ∧ g ≠ h ∧ ¬ Teaches H h S
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hClosed : ClosedUnderPointPatches H` | Guarantees that modifying h at a single input x0 stays inside H; some restrictions that break patch-closure (e.g. ConstBoolClass or MonotoneConjunctions 2) admit finite teaching sets with untested inputs. | `tight` | `Toy.Witness.patchClosed_untested_input_ce_not_patchClosed` |
| `hh : H h` | Guarantees the base function h lies in H so that patch-closure places patchAt h x0 y' in H. | `tight` | `Toy.Witness.patchClosed_untested_input_ce_not_in_H` |
| `hcon : Consistent S h` | Guarantees that matching h on every tested input implies patchAt h x0 y' passes S. | `tight` | `Toy.Witness.patchClosed_untested_input_ce_inconsistent` |
| `hUntested : x0 not in S.map Prod.fst` | Guarantees that modifying the output at x0 leaves all outputs on S unchanged. | `tight` | `Toy.Witness.patchClosed_untested_input_ce_tested` |
| `hDiff : y' != h x0` | Guarantees that patchAt h x0 y' differs from h at x0. | `tight` | `Toy.Witness.patchClosed_untested_input_ce_same_val` |
| `X : Type u, Y : Type v` | Arbitrary domain and codomain types across any universes. | `harmless` | — |
| `H, h, S, x₀, y'` | Universally quantified over any class, target, sample, untested input, and alternative output meeting the five hypotheses. | `harmless` | — |

**Depth: shallow.** Constructive point perturbation `patchAt h x₀ y'` evaluated at `x₀` and at tested coordinates in `S`.

**Non-vacuity witness.** The strictly restricted patch-closed class EventuallyFalse on Nat -> Bool, h = const false, S = [(0, false)], x0 = 1, y' = true. (`Toy.Witness.patchClosed_untested_input_patch_witness_nonvacuity`).

**Positive control.** Restricting `H` to `MonotoneConjunctions 2` breaks `ClosedUnderPointPatches` while keeping `H h`, `Consistent S h`, untested input `x₀ = (false, false)`, and `true ≠ h x₀`, allowing the 2-example suite `monotoneConjTeachingSet (fun _ => true)` to teach `x₀ ∧ x₁` (`Toy.Witness.patchClosed_untested_input_positive_control_monotone_conj`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003.
- Timothy A. Budd and Dana Angluin, "Two notions of correctness and their relation to testing", Acta Informatica 18(1):31-45, 1982, DOI 10.1007/BF00625279 (two notions of test-data correctness, automatic detection/generation, and relation to program equivalence).

**Design question.** Pinpoints the exact constructive obstruction to finite conformance testing: any class closed under single-point lookup-table overrides (including unrestricted functions and restricted classes like EventuallyFalse) admits, for every target h in H and every suite S consistent with h, a passing disagreeing rival whenever some input x0 goes untested and some output y' != h x0 exists.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Whenever a class of deterministic implementations permits single-input lookup-table overrides (`if x = x₀ then y' else h x`), any finite test suite omitting an input `x₀` fails to pin down `h` whenever a second output exists (`y' ≠ h x₀`). Mere syntactic restriction of `H` avoids this obstruction only when the restriction breaks single-point patch closure; the model omits computability/resource constraints, though `patchAt` preserves computability when equality on `X` is decidable (not formalized here).

#### R3 — Untested-input impossibility for patch-closed classes

- **Kind:** impossibility. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Unrestricted.lean`.
- **Lean:** `Toy.Witness.patchClosed_hasUntestedInput_no_teaching`

**Plain claim.** Corollary of patchClosed_untested_input_patch_witness: whenever H is closed under single-point patches over X -> Y (including unrestricted H via unrestricted_hasUntestedInput_no_teaching), Y has at least two distinct values, and finite sample S leaves at least one input in X untested, S does not teach any h within H.

```lean
@Toy.Witness.patchClosed_hasUntestedInput_no_teaching : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  Toy.Witness.ClosedUnderPointPatches H →
    Toy.Witness.HasTwoDistinct Y → Toy.Witness.HasUntestedInput S → ¬Toy.Witness.Teaches H h S

@Toy.Witness.unrestricted_hasUntestedInput_no_teaching : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  Toy.Witness.IsUnrestricted H →
    Toy.Witness.HasTwoDistinct Y → Toy.Witness.HasUntestedInput S → ¬Toy.Witness.Teaches H h S
```

Unfolded (prose):

```text
for all types X, Y, class H, target h, sample S:
  (∀ f x y, H f → H (fun z => if z = x then y else f z))
→ (∃ y₁ y₂ : Y, y₁ ≠ y₂)
→ (∃ x₀ : X, x₀ ∉ S.map Prod.fst)
→ ¬ (H h ∧ Consistent S h ∧ ∀ g, H g → Consistent S g → g = h)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hClosed : ClosedUnderPointPatches H` | Allows single-point perturbed rivals in H; some restrictions that break patch-closure (e.g. ConstBoolClass or MonotoneConjunctions 2) admit finite teaching sets with untested inputs. | `tight` | `Toy.Witness.patchClosed_hasUntestedInput_ce_not_patchClosed` |
| `hTwo : HasTwoDistinct Y` | Provides an alternative output value distinct from h x0 at an untested input x0. | `tight` | `Toy.Witness.patchClosed_hasUntestedInput_ce_trivial_codomain` |
| `hUntested : HasUntestedInput S` | Ensures X contains at least one input omitted from S (in particular whenever |X| > S.length). | `tight` | `Toy.Witness.patchClosed_hasUntestedInput_ce_exhaustive` |
| `X : Type u, Y : Type v` | Arbitrary domain and codomain types across any universes. | `harmless` | — |
| `H, h, S` | Universally quantified; if `¬ H h` or `¬ Consistent S h`, `¬ Teaches H h S` already holds trivially. | `harmless` | — |

**Depth: shallow.** Direct corollary of R2 (`patchClosed_untested_input_patch_witness`), picking `y' ∈ {y₁, y₂}` distinct from `h x₀`.

**Non-vacuity witness.** H = all functions Bool -> Bool (patch-closed), Y = Bool, S = [(false, false)] leaving true untested. (`Toy.Witness.patchClosed_hasUntestedInput_no_teaching_nonvacuity`).

**Positive control.** Restricting `H` to `MonotoneConjunctions 2` breaks `ClosedUnderPointPatches` while retaining `HasTwoDistinct Bool` and untested input `(false, false)`, allowing a 2-example suite on a 4-element domain to teach `x₀ ∧ x₁` (`Toy.Witness.patchClosed_untested_input_positive_control_monotone_conj`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003.
- Martin Anthony, Graham Brightwell, and John Shawe-Taylor, "On specifying Boolean functions by labelled examples", Discrete Applied Mathematics 61(1):1-25, 1995, DOI 10.1016/0166-218X(94)00007-Z.

**Design question.** Corollary giving the exact finite-domain threshold: for any patch-closed class (in particular an unrestricted class) whose codomain has at least two distinct values, a complete conformance suite must test every single input in the domain.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Over any finite or infinite input domain where candidate implementations are closed under single-point lookup-table patches and at least two outputs exist, a finite test suite cannot teach any target unless it covers every input in `X`. On finite domains this yields the exhaustive-testing threshold `|S.map Prod.fst| ≥ |X|`.

#### R4 — Infinite-domain impossibility for patch-closed classes

- **Kind:** impossibility. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Unrestricted.lean`.
- **Lean:** `Toy.Witness.patchClosed_infinite_no_finite_teaching_set`

**Plain claim.** Corollary of patchClosed_hasUntestedInput_no_teaching: if H is closed under single-point patches over X -> Y (including unrestricted H via unrestricted_infinite_no_finite_teaching_set and strictly restricted classes such as EventuallyFalse via eventuallyFalse_no_finite_teaching_set), Y has at least two distinct elements, and X is infinite, then no finite labeled sample teaches any function h within H.

```lean
@Toy.Witness.patchClosed_infinite_no_finite_teaching_set : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y),
  Toy.Witness.ClosedUnderPointPatches H →
    Toy.Witness.HasTwoDistinct Y →
      Toy.Witness.InfiniteDomain X → ∀ (h : X → Y) (S : List (X × Y)), ¬Toy.Witness.Teaches H h S

@Toy.Witness.unrestricted_infinite_no_finite_teaching_set : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y),
  Toy.Witness.IsUnrestricted H →
    Toy.Witness.HasTwoDistinct Y →
      Toy.Witness.InfiniteDomain X → ∀ (h : X → Y) (S : List (X × Y)), ¬Toy.Witness.Teaches H h S

Toy.Witness.eventuallyFalse_no_finite_teaching_set : ∀ (h : Nat → Bool) (S : List (Nat × Bool)),
  ¬Toy.Witness.Teaches Toy.Witness.EventuallyFalse h S
```

Unfolded (prose):

```text
for all types X, Y, class H:
  (∀ f x y, H f → H (fun z => if z = x then y else f z))
→ (∃ y₁ y₂ : Y, y₁ ≠ y₂)
→ (∀ L : List X, ∃ x : X, x ∉ L)
→ ∀ (h : X → Y) (S : List (X × Y)), ¬ Teaches H h S
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hClosed : ClosedUnderPointPatches H` | Retains single-point lookup-table overrides inside H; some restrictions that break patch-closure (e.g. constant functions or bounded-state Moore machines over a finite alphabet) allow finite teaching sets even on infinite domains. | `tight` | `Toy.Witness.patchClosed_infinite_ce_not_patchClosed` |
| `hTwo : HasTwoDistinct Y` | Rules out subsingleton codomains where every pair of functions X -> Y is automatically equal. | `tight` | `Toy.Witness.patchClosed_infinite_ce_trivial_codomain` |
| `hInf : InfiniteDomain X` | Guarantees that every finite sample leaves at least one input in X untested. | `tight` | `Toy.Witness.patchClosed_infinite_ce_finite_domain` |
| `X : Type u, Y : Type v, H : HypothesisClass X Y` | Arbitrary infinite domain type, nontrivial codomain type, and patch-closed hypothesis class. | `harmless` | — |

**Depth: shallow.** Immediate specialization of R3 (`patchClosed_hasUntestedInput_no_teaching`) using `hInf (S.map Prod.fst)` to witness an untested input.

**Non-vacuity witness.** H = EventuallyFalse on Nat -> Bool (strictly restricted yet patch-closed), Y = Bool (false != true), X = Nat (infinite). (`Toy.Witness.patchClosed_infinite_no_finite_teaching_set_nonvacuity`).

**Positive control.** Over the infinite domain `List Unit` and nontrivial output `Bool`, restricting `H` to `BoundedMooreBehaviors Unit Bool 2` breaks single-point patch closure and lets the 3-word suite `[([], false), ([()], true), ([(), ()], false)]` teach `altMachine2.behavior` (`Toy.Witness.bounded_two_state_moore_unit_positive_control`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003.
- Ayumi Shinohara and Satoru Miyano, "Teachability in Computational Learning", New Generation Computing 8(4):337-347, 1991, DOI 10.1007/BF03037091.
- Martin Anthony, Graham Brightwell, and John Shawe-Taylor, "On specifying Boolean functions by labelled examples", Discrete Applied Mathematics 61(1):1-25, 1995, DOI 10.1016/0166-218X(94)00007-Z.

**Design question.** Corollary isolating three individually necessary hypotheses (patch-closure, nontrivial codomain, infinite domain) under which finite teaching is impossible, showing that, on an infinite domain with at least two distinct outputs, mere restriction of H fails unless it breaks single-point patch closure.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — When at least two output values are possible, no finite test suite can uniquely specify a total function on an infinite input domain unless the candidate class violates single-point patch closure (for example, by fixing a syntactic normal form or a bounded-state machine over a finite alphabet). Crucially, restricting `H` is not sufficient on its own: restricted patch-closed classes such as `EventuallyFalse` remain unteachable by finite samples, though `EventuallyFalse` is identifiable in the limit from positive text and learnable with unboundedly many equivalence queries (different protocols outside this static teaching-set model).

#### R5 — Exact minimum teaching-set size for monotone Boolean conjunctions

- **Kind:** theorem. **Tier:** T0. **Depth:** substantive. **Module:** `lean/Toy/Witness/Conjunctions.lean`.
- **Lean:** `Toy.Witness.monotone_conj_teaching_set_exact`

**Plain claim.** For any m Boolean features and any monotone conjunction V : Fin m -> Bool with r = relevantCount V relevant variables, the explicit sample monotoneConjTeachingSet V teaches evalMonotoneConj V within MonotoneConjunctions m, has length min (r + 1) m, and attains the exact minimum teaching-set size min (r + 1) m (covering r = 0, 0 < r < m, r = m, and m = 0).

```lean
Toy.Witness.monotone_conj_teaching_set_exact : ∀ (m : Nat) (V : Fin m → Bool),
  Toy.Witness.Teaches (Toy.Witness.MonotoneConjunctions m) (Toy.Witness.evalMonotoneConj V)
      (Toy.Witness.monotoneConjTeachingSet V) ∧
    List.length (Toy.Witness.monotoneConjTeachingSet V) = min (Toy.Witness.relevantCount V + 1) m ∧
      Toy.Witness.HasMinTeachingSize (Toy.Witness.MonotoneConjunctions m) (Toy.Witness.evalMonotoneConj V)
        (min (Toy.Witness.relevantCount V + 1) m)
```

Unfolded (prose):

```text
for all m : Nat and V : Fin m → Bool:
  let r := ((List.finRange m).filter V).length;
  let S := if r < m then (V, true) :: ((List.finRange m).filter V).map (fun i => (flipBit i, false))
                    else ((List.finRange m).filter V).map (fun i => (flipBit i, false));
  Teaches (MonotoneConjunctions m) (evalMonotoneConj V) S
  ∧ S.length = min (r + 1) m
  ∧ ( (∃ S', S'.length = min (r + 1) m ∧ Teaches (MonotoneConjunctions m) (evalMonotoneConj V) S')
      ∧ ∀ S', Teaches (MonotoneConjunctions m) (evalMonotoneConj V) S' → min (r + 1) m ≤ S'.length )
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `m : Nat, V : Fin m → Bool` | Unconditional over all feature counts `m` (including `m = 0`) and all indicator vectors `V` (covering `r = 0`, `0 < r < m`, and `r = m`). | `harmless` | — |

**Depth: substantive.** Proves both directions cleanly: consistency and `UniqueConsistent` of `monotoneConjTeachingSet V` by coordinate-wise case analysis (`V i = true` via `flipBit i`, `V i = false` via `(V, true)`), and the `min (r + 1) m` lower bound via the hitting-set characterization (R1), extracting, for each relevant feature `i`, a negative example that separates the target from the rival conjunction with feature `i` removed (`r` pairwise distinct examples in total) and, when `r < m`, an additional positive example that separates it from the rival conjunction with one irrelevant feature `j₀` added.

**Non-vacuity witness.** Direct self-contained proof of the full conclusion (teaching, length, and HasMinTeachingSize lower bound) at m = 2, r = 1 (monotone_conj_m2_r1_exact), with r = 0 (monotone_conj_m2_r0_exact), r = 2 (monotone_conj_m2_r2_exact), and m = 0 (monotone_conjunctions_m0_td) also directly verified. (`Toy.Witness.monotone_conj_teaching_set_exact_nonvacuity`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003 (section on monotone monomials; Theorem 11 in technical report WUCS-92-28).
- Ayumi Shinohara and Satoru Miyano, "Teachability in Computational Learning", New Generation Computing 8(4):337-347, 1991, DOI 10.1007/BF03037091.
- Thorsten Doliwa, Gaojian Fan, Hans Ulrich Simon, and Sandra Zilles, "Recursive Teaching Dimension, VC-Dimension and Sample Compression", Journal of Machine Learning Research 15(89):3107-3131, 2014, https://jmlr.org/papers/v15/doliwa14a.html (Corollary 9(2), which Doliwa et al. attribute in part to Sally A. Goldman and Robert H. Sloan, "The power of self-directed learning", Machine Learning 14(3):271-294, 1994, DOI 10.1007/BF00993977, and to Zilles et al. 2011, Journal of Machine Learning Research 12(11):349-384; neither attributed source was consulted directly).

**Design question.** Computes the exact per-concept conformance-suite size min (r + 1) m for monotone Boolean conjunctions over m features and exposes the explicit computable suite attaining that optimum.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — When a specification is a monotone conjunction of `r` out of `m` Boolean flags (positive literals only, excluding constant `false`), an explicit computable suite of size `min (r + 1) m` uniquely identifies it among all `2^m` monotone conjunctions—exponentially smaller than the `2^m` domain—provided candidate implementations are already guaranteed to lie in `MonotoneConjunctions m`.

#### R6 — Teaching dimension of monotone Boolean conjunctions

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Conjunctions.lean`.
- **Lean:** `Toy.Witness.monotone_conjunctions_teaching_dimension`

**Plain claim.** Corollary derived from monotone_conj_teaching_set_exact: for every m : Nat (including m = 0), the exact teaching dimension of MonotoneConjunctions m is m.

```lean
Toy.Witness.monotone_conjunctions_teaching_dimension : ∀ (m : Nat),
  Toy.Witness.HasTeachingDimension (Toy.Witness.MonotoneConjunctions m) m
```

Unfolded (prose):

```text
for all m : Nat:
  (∀ h, (∃ V : Fin m → Bool, evalMonotoneConj V = h) →
      ∃ S : List (BoolAssignment m × Bool), S.length ≤ m ∧ Teaches (MonotoneConjunctions m) h S)
  ∧ (∃ h, (∃ V : Fin m → Bool, evalMonotoneConj V = h) ∧
      ∀ S : List (BoolAssignment m × Bool), Teaches (MonotoneConjunctions m) h S → m ≤ S.length)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `m : Nat` | Unconditional for all `m : Nat`, including `m = 0` (`TD = 0`, matching singleton class convention). | `harmless` | — |

**Depth: shallow.** Derived in 10 lines directly from R5 (`monotone_conj_teaching_set_exact`): upper bound uses `min (r + 1) m ≤ m`, and lower bound specializes R5 to `V = fun _ => true` (`relevantCount = m`).

**Non-vacuity witness.** Direct self-contained proof of HasTeachingDimension (MonotoneConjunctions 2) 2 without invoking monotone_conj_teaching_set_exact (with m = 0 also directly checked in monotone_conjunctions_m0_td). (`Toy.Witness.monotone_conjunctions_teaching_dimension_nonvacuity`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003 (section on monotone monomials; Theorem 11 in WUCS-92-28).
- Ayumi Shinohara and Satoru Miyano, "Teachability in Computational Learning", New Generation Computing 8(4):337-347, 1991, DOI 10.1007/BF03037091.
- Thorsten Doliwa, Gaojian Fan, Hans Ulrich Simon, and Sandra Zilles, "Recursive Teaching Dimension, VC-Dimension and Sample Compression", Journal of Machine Learning Research 15(89):3107-3131, 2014, https://jmlr.org/papers/v15/doliwa14a.html (Corollary 9(2)).

**Design question.** Corollary of monotone_conj_teaching_set_exact giving the exact worst-case finite test-suite size m across the monotone-conjunction class over m features.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Worst-case minimum teaching-suite size across all monotone conjunctions over `m` features equals `m`, attained by the full conjunction `⋀_{i < m} x_i` (when `m ≥ 1`) or vacuously at `m = 0`. Applies only when negative literals and constant `false` are excluded.

#### R7 — Moore's single-machine state-distinguishability bound (≤ n - 2)

- **Kind:** characterization. **Tier:** T0. **Depth:** substantive. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.moore_state_equiv_iff_agree_up_to`, `Toy.Witness.moore_state_equiv_iff_agree_lt_n`

**Plain claim.** For any deterministic Moore machine M with n states (Fin n) over arbitrary input alphabet I and output alphabet O, two states s and t are behaviorally equivalent if and only if they agree on all input words of length at most n - 2 (equivalently, agreement on all words of length < n suffices, recorded in moore_state_equiv_iff_agree_lt_n).

```lean
@Toy.Witness.moore_state_equiv_iff_agree_up_to : ∀ {I : Type u_1} {O : Type u_2} {n : Nat}
  (M : Toy.Witness.MooreMachine I O (Fin n)) (s t : Fin n),
  Toy.Witness.StateEquiv M s t ↔ Toy.Witness.AgreeUpTo M s t (n - 2)

@Toy.Witness.moore_state_equiv_iff_agree_lt_n : ∀ {I : Type u_1} {O : Type u_2} {n : Nat}
  (M : Toy.Witness.MooreMachine I O (Fin n)) (s t : Fin n),
  Toy.Witness.StateEquiv M s t ↔
    ∀ (w : List I),
      List.length w < n → Toy.Witness.MooreMachine.behavior M s w = Toy.Witness.MooreMachine.behavior M t w
```

Unfolded (prose):

```text
for all types I, O, state count n : Nat, machine M : MooreMachine I O (Fin n), states s, t : Fin n:
  (∀ w : List I, M.out (M.run s w) = M.out (M.run t w))
  ↔ (∀ w : List I, w.length ≤ n - 2 → M.out (M.run s w) = M.out (M.run t w))

-- Companion (moore_state_equiv_iff_agree_lt_n):
-- StateEquiv M s t ↔ ∀ w : List I, w.length < n → M.behavior s w = M.behavior t w
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `I : Type u, O : Type v, n : Nat, M : MooreMachine I O (Fin n), s t : Fin n` | Unconditional across arbitrary (possibly infinite) alphabets `I, O` and all `n : Nat` (including `n = 0, 1`), without assuming pairwise-distinguishable states or finite `I`. | `harmless` | — |

**Depth: substantive.** Constructs an ascending sequence of pairwise-inequivalent state lists `P_j` under `AgreeUpTo M · · j` via partition-splitting stabilization (two internal lemmas: if agreement up to depth `j` implies agreement up to depth `j + 1` for every pair of states, then it implies agreement up to every larger depth; and a pair agreeing up to depth `j` but not `j + 1` extends a pairwise-inequivalent list at depth `j` by one element at depth `j + 1`), showing `P_j.length = j + 2`, so any minimal first-disagreement length `K` forces `K + 2 ≤ n`, i.e., `K ≤ n - 2`.

**Non-vacuity witness.** Direct verification on two non-constant 3-state machines: a 3-state alternating machine where distinct states 0 and 1 satisfy both StateEquiv and AgreeUpTo at length 3 - 2 = 1, and delayChain 3 where states 0 and 1 satisfy neither (companion general sharpness in moore_bound_sharp). (`Toy.Witness.moore_state_equiv_iff_agree_up_to_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), C. E. Shannon and J. McCarthy (eds.), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 6, p. 145).
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.

**Design question.** Establishes the exact finite horizon (n - 2 input symbols) after which no behavioral divergence can first appear between states of an n-state deterministic Moore machine.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Within a deterministic Moore machine with `n` states and state-labeled outputs (where `[]` already observes the initial output), any two states that can be distinguished by *any* finite input sequence are already separated by a sequence of length at most `n - 2`. Transfer requires deterministic state transitions, state-attached outputs (Mealy machines have bound `n - 1`), and an accurate upper bound `n` on state count.

#### R8 — Two-machine form of Moore's bound (≤ n₁ + n₂ - 2)

- **Kind:** characterization. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.moore_two_machine_equiv_iff_agree_up_to`

**Plain claim.** Derived from moore_state_equiv_iff_agree_up_to via disjoint union: two initialized deterministic Moore machines M1 (n1 states) and M2 (n2 states) over arbitrary alphabets I and O have identical input-output behavior if and only if they agree on all input words of length at most n1 + n2 - 2.

```lean
@Toy.Witness.moore_two_machine_equiv_iff_agree_up_to : ∀ {I : Type u_1} {O : Type u_2} {n₁ n₂ : Nat}
  (M₁ : Toy.Witness.InitMooreMachine I O n₁) (M₂ : Toy.Witness.InitMooreMachine I O n₂),
  Toy.Witness.InitMooreMachine.behavior M₁ = Toy.Witness.InitMooreMachine.behavior M₂ ↔
    ∀ (w : List I),
      List.length w ≤ n₁ + n₂ - 2 →
        Toy.Witness.InitMooreMachine.behavior M₁ w = Toy.Witness.InitMooreMachine.behavior M₂ w
```

Unfolded (prose):

```text
for all types I, O, counts n₁ n₂ : Nat, initialized machines M₁ : InitMooreMachine I O n₁, M₂ : InitMooreMachine I O n₂:
  M₁.behavior = M₂.behavior
  ↔ (∀ w : List I, w.length ≤ n₁ + n₂ - 2 → M₁.behavior w = M₂.behavior w)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `I : Type u, O : Type v, n₁ n₂ : Nat, M₁, M₂` | Unconditional; `M₁.init : Fin n₁` and `M₂.init : Fin n₂` implicitly enforce `n₁ ≥ 1, n₂ ≥ 1`. | `harmless` | — |

**Depth: shallow.** Derived from R7 (`moore_state_equiv_iff_agree_up_to`) applied to `disjointUnion M₁ M₂` (which has `n₁ + n₂` states) at `inlFin M₁.init` and `inrFin M₂.init`.

**Non-vacuity witness.** A 1-state and a 2-state all-false Moore machine over Unit -> Bool whose behaviors agree globally and on all words of length <= 1 + 2 - 2 = 1. (`Toy.Witness.moore_two_machine_equiv_iff_agree_up_to_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies, Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 7, pp. 146-147, states the symmetric form for two machines with a common state bound n, an experiment of length 2n - 1, i.e. words of length <= 2n - 2 here; the asymmetric n1 + n2 - 2 form proved here follows from the same direct-sum argument but is not stated by Moore).
- M. P. Vasilevskii, "Failure Diagnosis of Automata", Cybernetics 9(4):653-665, 1973, DOI 10.1007/BF01068590.
- Tsun S. Chow, "Testing Software Design Modeled by Finite-State Machines", IEEE Transactions on Software Engineering SE-4(3):178-187, 1978, DOI 10.1109/TSE.1978.231496.

**Design question.** Derived from moore_state_equiv_iff_agree_up_to; shows exactly how the required test-word depth grows as the sum n1 + n2 - 2 of specification and implementation state budgets.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Comparing an `n₁`-state deterministic Moore specification against an `n₂`-state deterministic Moore implementation requires checking words up to the *sum* `n₁ + n₂ - 2` (not `max n₁ n₂ - 2`). Over an infinite alphabet this remains semantically true, though infinitely many words of length `≤ n₁ + n₂ - 2` exist.

#### R9 — Sharpness of the n - 2 single-machine bound (delayChain n)

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.moore_bound_sharp`

**Plain claim.** For every n >= 2, states 0 and 1 of the explicit n-state delay chain delayChain n over Unit -> Bool agree on every input word of length < n - 2 yet disagree on the word of length n - 2, showing Moore's n - 2 input-word bound cannot be tightened.

Printed with `pp.funBinderTypes true` and `pp.numericTypes true` in addition, which show that `s₀` and `s₁` range over `Fin n` and that `↑s₀ = 0` and `↑s₁ = 1` compare natural numbers:

```lean
Toy.Witness.moore_bound_sharp : ∀ (n : Nat),
  (2 : Nat) ≤ n →
    ∃ (s₀ : Fin n),
      ∃ (s₁ : Fin n),
        ↑s₀ = (0 : Nat) ∧
          ↑s₁ = (1 : Nat) ∧
            (∀ (w : List Unit),
                List.length w < n - (2 : Nat) →
                  Toy.Witness.MooreMachine.behavior (Toy.Witness.delayChain n) s₀ w =
                    Toy.Witness.MooreMachine.behavior (Toy.Witness.delayChain n) s₁ w) ∧
              Toy.Witness.MooreMachine.behavior (Toy.Witness.delayChain n) s₀ (List.replicate (n - (2 : Nat)) ()) ≠
                  Toy.Witness.MooreMachine.behavior (Toy.Witness.delayChain n) s₁ (List.replicate (n - (2 : Nat)) ()) ∧
                ¬Toy.Witness.StateEquiv (Toy.Witness.delayChain n) s₀ s₁
```

Unfolded (prose):

```text
for all n : Nat:
  2 ≤ n →
  ∃ s₀ s₁ : Fin n, s₀.val = 0 ∧ s₁.val = 1 ∧
    (∀ w : List Unit, w.length < n - 2 →
      (delayChain n).behavior s₀ w = (delayChain n).behavior s₁ w) ∧
    (delayChain n).behavior s₀ (List.replicate (n - 2) ()) ≠
      (delayChain n).behavior s₁ (List.replicate (n - 2) ()) ∧
    ¬ StateEquiv (delayChain n) s₀ s₁
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hn : 2 <= n` | Ensures Fin n contains two distinct states; for n <= 1 all states are equal and no two states of delayChain n can disagree. | `tight` | `Toy.Witness.moore_bound_sharp_ce_small_n` |
| `n : Nat` | Universally quantified over all `n ≥ 2`. | `harmless` | — |

**Depth: shallow.** Closed-form tracking of `delayChain n`'s run index (`min (s.val + w.length) (n - 1)`).

**Non-vacuity witness.** n = 3 satisfies 2 <= 3, where states 0 and 1 of delayChain 3 agree on length 0 and disagree on [()] (length 1 = 3 - 2). (`Toy.Witness.moore_bound_sharp_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 6, p. 145, and sharpness examples D_n for n > 3 over two inputs, p. 146; the unary witness delayChain n covering every n >= 2 is this package's construction).

**Design question.** Establishes that n - 2 (not a smaller horizon) is the sharp worst-case word depth needed to distinguish states of an n-state deterministic Moore machine.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — The worst-case distinguishing word length `n - 2` in R7 cannot be lowered for any `n ≥ 2` (even over a 1-letter alphabet). Many individual machines distinguish states earlier, so `n - 2` is a worst-case horizon rather than a per-machine minimum.

#### R10 — Finite-alphabet bounded-state specification test-suite completeness

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_teaches`, `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_certifies`

**Plain claim.** Derived from moore_two_machine_equiv_iff_agree_up_to: over a finite input alphabet enumerated by alphabet, for any n1-state specification machine M whose behavior lies in BoundedMooreBehaviors I O k2, the explicit finite labeled suite mooreSpecTestSuite alphabet M k2 (all words of length <= n1 + k2 - 2) teaches M.behavior within BoundedMooreBehaviors I O k2 (and certifies all <= k2-state implementations even without hMem; see finite_alphabet_bounded_moore_spec_suite_certifies).

```lean
@Toy.Witness.finite_alphabet_bounded_moore_spec_suite_teaches : ∀ {I : Type u_1} {O : Type u_2} {n₁ : Nat}
  (alphabet : List I) (M : Toy.Witness.InitMooreMachine I O n₁) (k₂ : Nat),
  Toy.Witness.CoversAll alphabet →
    Toy.Witness.BoundedMooreBehaviors I O k₂ (Toy.Witness.InitMooreMachine.behavior M) →
      Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors I O k₂) (Toy.Witness.InitMooreMachine.behavior M)
        (Toy.Witness.mooreSpecTestSuite alphabet M k₂)

@Toy.Witness.finite_alphabet_bounded_moore_spec_suite_certifies : ∀ {I : Type u_1} {O : Type u_2} {n₁ : Nat}
  (alphabet : List I) (M : Toy.Witness.InitMooreMachine I O n₁) (k₂ : Nat),
  Toy.Witness.CoversAll alphabet →
    Toy.Witness.Consistent (Toy.Witness.mooreSpecTestSuite alphabet M k₂) (Toy.Witness.InitMooreMachine.behavior M) ∧
      Toy.Witness.UniqueConsistent (Toy.Witness.BoundedMooreBehaviors I O k₂) (Toy.Witness.InitMooreMachine.behavior M)
        (Toy.Witness.mooreSpecTestSuite alphabet M k₂)
```

Unfolded (prose):

```text
for all types I, O, n₁ k₂ : Nat, alphabet : List I, M : InitMooreMachine I O n₁:
  (∀ a : I, a ∈ alphabet) →
  (∃ m ≤ k₂, ∃ M' : InitMooreMachine I O m, M'.behavior = M.behavior) →
  Teaches (BoundedMooreBehaviors I O k₂) M.behavior
    (labelSample M.behavior (wordsUpTo alphabet (n₁ + k₂ - 2)))

-- Companion without hMem (finite_alphabet_bounded_moore_spec_suite_certifies):
-- CoversAll alphabet →
-- Consistent (mooreSpecTestSuite alphabet M k₂) M.behavior ∧
-- UniqueConsistent (BoundedMooreBehaviors I O k₂) M.behavior (mooreSpecTestSuite alphabet M k₂)
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hCover : CoversAll alphabet` | Guarantees that wordsUpTo enumerates every input word over I up to length n1 + k2 - 2. | `tight` | `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_ce_incomplete_alphabet` |
| `hMem : BoundedMooreBehaviors I O k2 M.behavior` | Needed only for the membership conjunct H h of Teaches; consistency and uniqueness (certification of every <= k2-state implementation against M.behavior) hold without hMem, proved in Toy.Witness.finite_alphabet_bounded_moore_spec_suite_certifies. | `tight` | `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound` |
| `I : Type u, O : Type v, n₁ k₂ : Nat, M : InitMooreMachine I O n₁` | Arbitrary finite alphabet `I`, arbitrary codomain `O`, arbitrary state counts `n₁, k₂`. | `harmless` | — |

**Depth: shallow.** Derived directly from R8 (`moore_two_machine_equiv_iff_agree_up_to`) and `mem_wordsUpTo_iff` (`hMem` is needed only for the `H h` conjunct of `Teaches`; certification holds without `hMem` via `finite_alphabet_bounded_moore_spec_suite_certifies`).

**Non-vacuity witness.** I = Unit with alphabet = [()], O = Bool, k2 = 2, and M = altMachine2 (2 states). (`Toy.Witness.finite_alphabet_bounded_moore_spec_suite_teaches_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies, Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorems 6-7; Theorem 7 is the symmetric form with a common state bound n, and the asymmetric n1 + k2 - 2 depth used here follows from the same direct-sum argument but is not stated by Moore).
- M. P. Vasilevskii, "Failure Diagnosis of Automata", Cybernetics 9(4):653-665, 1973, DOI 10.1007/BF01068590.
- Tsun S. Chow, "Testing Software Design Modeled by Finite-State Machines", IEEE Transactions on Software Engineering SE-4(3):178-187, 1978, DOI 10.1109/TSE.1978.231496.
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.
- Rita Dorofeeva, Khaled El-Fakih, Stephane Maag, Ana R. Cavalli, and Nina Yevtushenko, "FSM-based conformance testing methods: A survey annotated with experimental evaluation", Information and Software Technology 52(12):1286-1297, 2010, DOI 10.1016/j.infsof.2010.07.001.
- Robert Sachtleben, "Verified Complete Test Strategies for Finite State Machines", Archive of Formal Proofs, 9 Aug 2022 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/FSM_Tests.html (Isabelle mechanization of complete FSM test strategies: W, Wp, HSI, H, SPY, SPYH, and adaptive state counting).
- Robert Sachtleben, "Formalisation of an Adaptive State Counting Algorithm", Archive of Formal Proofs, 16 Aug 2019 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/Adaptive_State_Counting.html.

**Design question.** Derived from moore_two_machine_equiv_iff_agree_up_to; provides an explicit, complete finite conformance suite over an infinite input-word domain once both the input alphabet is finite and the implementation's state count is bounded by k2.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Given a known `n₁`-state deterministic Moore specification `M`, an exhaustive list of the finite input alphabet `alphabet`, reliable reset between runs, and an upper bound `k₂` on candidate implementation states, running `M` on all words up to length `n₁ + k₂ - 2` yields a finite complete conformance suite over the infinite word domain `List I`. Even if `M` has more than `k₂` states, `finite_alphabet_bounded_moore_spec_suite_certifies` guarantees that no ≤ `k₂`-state implementation differing from `M` passes this suite.

#### R11 — Finite-alphabet bounded-state class-universal test-suite completeness

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.finite_alphabet_bounded_moore_class_suite_teaches`

**Plain claim.** Corollary of moore_two_machine_equiv_iff_agree_up_to: over a finite input alphabet enumerated by alphabet, every behavior h in BoundedMooreBehaviors I O k is taught within BoundedMooreBehaviors I O k by the universal finite suite mooreClassTestSuite alphabet k h consisting of all words of length at most 2 * k - 2.

```lean
@Toy.Witness.finite_alphabet_bounded_moore_class_suite_teaches : ∀ {I : Type u_1} {O : Type u_2} (alphabet : List I)
  (k : Nat) (h : List I → O),
  Toy.Witness.CoversAll alphabet →
    Toy.Witness.BoundedMooreBehaviors I O k h →
      Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors I O k) h (Toy.Witness.mooreClassTestSuite alphabet k h)
```

Unfolded (prose):

```text
for all types I, O, alphabet : List I, k : Nat, h : List I → O:
  (∀ a : I, a ∈ alphabet) →
  BoundedMooreBehaviors I O k h →
  Teaches (BoundedMooreBehaviors I O k) h (labelSample h (wordsUpTo alphabet (2 * k - 2)))
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hCover : CoversAll alphabet` | Ensures every input symbol of I is included when enumerating words up to length 2 * k - 2. | `tight` | `Toy.Witness.finite_alphabet_bounded_moore_class_suite_ce_incomplete_alphabet` |
| `hMem : BoundedMooreBehaviors I O k h` | Ensures the target behavior h is realizable by some Moore machine with at most k states (needed both to bound the target's state count and for the membership conjunct of Teaches). | `tight` | `Toy.Witness.finite_alphabet_bounded_moore_class_suite_ce_target_outside_bound` |
| `I : Type u, O : Type v, k : Nat, h : List I → O` | Arbitrary finite alphabet `I`, output `O`, state bound `k`, and target behavior `h ∈ BoundedMooreBehaviors I O k`. | `harmless` | — |

**Depth: shallow.** Derived directly from R8 (`moore_two_machine_equiv_iff_agree_up_to`) with `n₁ ≤ k` and `n₂ ≤ k`, giving `n₁ + n₂ - 2 ≤ 2 * k - 2`.

**Non-vacuity witness.** I = Unit with alphabet = [()], O = Bool, k = 2, and h = altMachine2.behavior. (`Toy.Witness.finite_alphabet_bounded_moore_class_suite_teaches_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies, Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 7).
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.
- Rita Dorofeeva, Khaled El-Fakih, Stephane Maag, Ana R. Cavalli, and Nina Yevtushenko, "FSM-based conformance testing methods: A survey annotated with experimental evaluation", Information and Software Technology 52(12):1286-1297, 2010, DOI 10.1016/j.infsof.2010.07.001.
- Robert Sachtleben, "Verified Complete Test Strategies for Finite State Machines", Archive of Formal Proofs, 9 Aug 2022 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/FSM_Tests.html.
- Robert Sachtleben, "Formalisation of an Adaptive State Counting Algorithm", Archive of Formal Proofs, 16 Aug 2019 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/Adaptive_State_Counting.html.

**Design question.** Corollary giving a single target-independent input suite (length <= 2k - 2) that is complete for every <= k-state Moore machine over a finite alphabet, even over the infinite domain List I.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — A single target-independent input set (`wordsUpTo alphabet (2 * k - 2)`) suffices to certify every `≤ k`-state deterministic Moore behavior over a finite alphabet against all `≤ k`-state rivals, provided reset, alphabet coverage, and the state ceiling `k` hold.

#### R12 — Sharpness of the two-machine bound (n₁ + n₂ - 2)

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.moore_two_machine_bound_sharp`

**Plain claim.** For all m1, m2 : Nat (giving n1 = m1 + 1 and n2 = m2 + 1 states, so n1 + n2 - 2 = m1 + m2), the explicit unary Moore machines modCycleMachine m1 m2 and mimicSaturateMachine m1 m2 agree on every input word of length < m1 + m2 yet disagree on the word of length m1 + m2, showing Moore's two-machine horizon n1 + n2 - 2 is sharp for every pair of state counts.

```lean
Toy.Witness.moore_two_machine_bound_sharp : ∀ (m₁ m₂ : Nat),
  have M₁ := Toy.Witness.modCycleMachine m₁ m₂;
  have M₂ := Toy.Witness.mimicSaturateMachine m₁ m₂;
  (∀ (w : List Unit),
      List.length w < m₁ + m₂ →
        Toy.Witness.InitMooreMachine.behavior M₁ w = Toy.Witness.InitMooreMachine.behavior M₂ w) ∧
    Toy.Witness.InitMooreMachine.behavior M₁ (List.replicate (m₁ + m₂) ()) ≠
        Toy.Witness.InitMooreMachine.behavior M₂ (List.replicate (m₁ + m₂) ()) ∧
      Toy.Witness.InitMooreMachine.behavior M₁ ≠ Toy.Witness.InitMooreMachine.behavior M₂
```

Unfolded (prose):

```text
for all m₁ m₂ : Nat:
  let M₁ := modCycleMachine m₁ m₂;
  let M₂ := mimicSaturateMachine m₁ m₂;
  (∀ w : List Unit, w.length < m₁ + m₂ → M₁.behavior w = M₂.behavior w)
  ∧ M₁.behavior (List.replicate (m₁ + m₂) ()) ≠ M₂.behavior (List.replicate (m₁ + m₂) ())
  ∧ M₁.behavior ≠ M₂.behavior
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `m₁ m₂ : Nat` | Unconditional over all `m₁, m₂ : Nat`, realizing `n₁ = m₁ + 1`, `n₂ = m₂ + 1`, and `n₁ + n₂ - 2 = m₁ + m₂`. | `harmless` | — |

**Depth: shallow.** Closed-form residue computation on `modCycleMachine m₁ m₂` and `mimicSaturateMachine m₁ m₂` using the elementary residue fact that `t < T` and `T - t < n` imply `t % n ≠ T % n`.

**Non-vacuity witness.** m1 = 1, m2 = 2 (2-state and 3-state unary Moore machines agreeing on lengths 0, 1, 2 and differing at length 3 = 2 + 3 - 2). (`Toy.Witness.moore_two_machine_bound_sharp_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 7, pp. 146-147, and symmetric sharpness examples D_n vs E_n for n > 3 over two inputs, p. 147; the unary asymmetric pair modCycleMachine m1 m2 and mimicSaturateMachine m1 m2 covering all m1, m2 : Nat is this package's construction).

**Design question.** Proves that the additive horizon n1 + n2 - 2 (not max n1 n2 - 2 or < max n1 n2) is tight for every specification/implementation state-budget pair (n1, n2).

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For *every* pair of specification and implementation state budgets `(n₁, n₂)` (`n₁, n₂ ≥ 1`), the additive horizon `n₁ + n₂ - 2` in R8 and R10 is sharp and cannot be replaced by `max n₁ n₂ - 2` or `< max n₁ n₂`.

#### R13 — Sharpness of the 2k - 2 class-suite depth for k ≥ 2

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.bounded_moore_class_suite_depth_sharp`

**Plain claim.** For every state bound k >= 2 over Unit -> Bool, the explicit k-state machines modCycleMachine (k - 1) (k - 1) and mimicSaturateMachine (k - 1) (k - 1) agree on every word of length < 2 * k - 2 yet disagree at length 2 * k - 2, so neither wordsUpTo [()] (2 * k - 3) nor wordsUpTo [()] (k - 1) teaches modCycleMachine (k - 1) (k - 1) within BoundedMooreBehaviors Unit Bool k (with concrete k = 2 check in two_state_moore_length_lt_k_insufficient).

```lean
Toy.Witness.bounded_moore_class_suite_depth_sharp : ∀ (k : Nat),
  2 ≤ k →
    have M₁ := Toy.Witness.modCycleMachine (k - 1) (k - 1);
    have M₂ := Toy.Witness.mimicSaturateMachine (k - 1) (k - 1);
    Toy.Witness.BoundedMooreBehaviors Unit Bool k (Toy.Witness.InitMooreMachine.behavior M₁) ∧
      Toy.Witness.BoundedMooreBehaviors Unit Bool k (Toy.Witness.InitMooreMachine.behavior M₂) ∧
        (∀ (w : List Unit),
            List.length w < 2 * k - 2 →
              Toy.Witness.InitMooreMachine.behavior M₁ w = Toy.Witness.InitMooreMachine.behavior M₂ w) ∧
          Toy.Witness.InitMooreMachine.behavior M₁ (List.replicate (2 * k - 2) ()) ≠
              Toy.Witness.InitMooreMachine.behavior M₂ (List.replicate (2 * k - 2) ()) ∧
            ¬Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors Unit Bool k)
                  (Toy.Witness.InitMooreMachine.behavior M₁)
                  (Toy.Witness.labelSample (Toy.Witness.InitMooreMachine.behavior M₁)
                    (Toy.Witness.wordsUpTo [()] (2 * k - 3))) ∧
              ¬Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors Unit Bool k)
                  (Toy.Witness.InitMooreMachine.behavior M₁)
                  (Toy.Witness.labelSample (Toy.Witness.InitMooreMachine.behavior M₁)
                    (Toy.Witness.wordsUpTo [()] (k - 1)))

Toy.Witness.two_state_moore_length_lt_k_insufficient : Toy.Witness.BoundedMooreBehaviors Unit Bool 2
    (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2) ∧
  Toy.Witness.BoundedMooreBehaviors Unit Bool 2 (Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2) ∧
    (∀ (w : List Unit),
        List.length w < 2 →
          Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2 w =
            Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2 w) ∧
      Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2 [(), ()] ≠
          Toy.Witness.InitMooreMachine.behavior Toy.Witness.latchMachine2 [(), ()] ∧
        ¬Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors Unit Bool 2)
            (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2)
            (Toy.Witness.labelSample (Toy.Witness.InitMooreMachine.behavior Toy.Witness.altMachine2)
              (Toy.Witness.wordsUpTo [()] 1))
```

Unfolded (prose):

```text
for all k : Nat:
  2 ≤ k →
  let M₁ := modCycleMachine (k - 1) (k - 1);
  let M₂ := mimicSaturateMachine (k - 1) (k - 1);
  BoundedMooreBehaviors Unit Bool k M₁.behavior ∧
  BoundedMooreBehaviors Unit Bool k M₂.behavior ∧
  (∀ w : List Unit, w.length < 2 * k - 2 → M₁.behavior w = M₂.behavior w) ∧
  M₁.behavior (List.replicate (2 * k - 2) ()) ≠ M₂.behavior (List.replicate (2 * k - 2) ()) ∧
  ¬ Teaches (BoundedMooreBehaviors Unit Bool k) M₁.behavior
      (labelSample M₁.behavior (wordsUpTo [()] (2 * k - 3))) ∧
  ¬ Teaches (BoundedMooreBehaviors Unit Bool k) M₁.behavior
      (labelSample M₁.behavior (wordsUpTo [()] (k - 1)))
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hk : 2 <= k` | Rules out k = 1 (where 2 * 1 - 3 = 0 and wordsUpTo [()] 0 = [[]] already teaches every 1-state machine) and k = 0 (empty class). | `tight` | `Toy.Witness.bounded_moore_class_suite_depth_sharp_ce_one_state` |
| `k : Nat` | Universally quantified for all `k ≥ 2`. | `harmless` | — |

**Depth: shallow.** Instantiates R12 (`moore_two_machine_bound_sharp`) at `m₁ = m₂ = k - 1` and refutes teaching for `wordsUpTo [()] L` whenever `L < 2 * k - 2`.

**Non-vacuity witness.** k = 3 satisfies 2 <= 3, giving two 3-state unary machines agreeing up to length 3 and differing at length 4 = 2 * 3 - 2 (concrete k = 2 check via altMachine2 and latchMachine2 in two_state_moore_length_lt_k_insufficient). (`Toy.Witness.bounded_moore_class_suite_depth_sharp_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 7 and sharpness examples D_n vs E_n for n > 3 over two inputs, p. 147; the unary pair modCycleMachine (k - 1) (k - 1) and mimicSaturateMachine (k - 1) (k - 1) covering every k >= 2 is this package's construction).

**Design question.** Refutes under-sizing a bounded-state class conformance suite to depth < k or 2k - 3 for every k >= 2: comparing a k-state spec against <= k-state implementations requires worst-case depth 2k - 2.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Testing only words of length `< k` or `≤ 2k - 3` is unsound for certifying `≤ k`-state Moore implementations whenever `k ≥ 2`: two separate `k`-state machines yield up to `2k` combined states and can agree through length `2k - 3` before diverging at `2k - 2`. At `k = 1`, depth `0` (`[[]]`) already suffices (`bounded_moore_class_suite_depth_sharp_ce_one_state`).

#### R14 — Infinite-alphabet impossibility for state bounds k ≥ 2 (and k = 1 boundary)

- **Kind:** impossibility. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.two_le_state_bound_infinite_alphabet_no_finite_teaching_set`

**Plain claim.** For every state bound k >= 2, every infinite input alphabet I, and every output alphabet O with at least two distinct values, no finite labeled sample teaches any behavior h within BoundedMooreBehaviors I O k.

```lean
@Toy.Witness.two_le_state_bound_infinite_alphabet_no_finite_teaching_set : ∀ {I : Type u_1} {O : Type u_2} (k : Nat),
  2 ≤ k →
    Toy.Witness.InfiniteDomain I →
      Toy.Witness.HasTwoDistinct O →
        ∀ (h : List I → O) (S : List (List I × O)), ¬Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors I O k) h S

@Toy.Witness.bounded_one_state_moore_single_example_teaches : ∀ {I : Type u_1} {O : Type u_2} (c : O),
  Toy.Witness.Teaches (Toy.Witness.BoundedMooreBehaviors I O 1) (fun x => c) [([], c)]
```

Unfolded (prose):

```text
for all types I, O, k : Nat:
  2 ≤ k →
  InfiniteDomain I →
  HasTwoDistinct O →
  ∀ (h : List I → O) (S : List (List I × O)),
    ¬ Teaches (BoundedMooreBehaviors I O k) h S

-- Exact k = 1 threshold companion (bounded_one_state_moore_single_example_teaches):
-- ∀ {I : Type u} {O : Type v} (c : O),
--   Teaches (BoundedMooreBehaviors I O 1) (fun _ => c) [([], c)]
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hk : 2 <= k` | Exact threshold: at k = 1 every behavior in BoundedMooreBehaviors I O 1 is constant and is taught by [([], c)] over every alphabet I, including infinite Nat. | `tight` | `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_one_state` |
| `hInf : InfiniteDomain I` | Guarantees every finite sample leaves some input symbol a0 completely unseen, allowing an unseen-symbol transition perturbation within <= k states. | `tight` | `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_finite_alphabet` |
| `hTwo : HasTwoDistinct O` | Rules out subsingleton output alphabets where every two behaviors List I -> O are identical. | `tight` | `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_trivial_output` |
| `I : Type u, O : Type v, k : Nat` | Arbitrary infinite input alphabet `I`, nontrivial output `O`, and state bound `k ≥ 2`. | `harmless` | — |

**Depth: shallow.** Constructs an unseen-symbol `a₀`-transition perturbation: if `M.out` is non-constant on `Fin m`, redirects `a₀` from `M.init` to a state with output `≠ M.out (M.step M.init a₀)` inside `m ≤ k` states; if `M` is constant, builds a 2-state `a₀`-detector (`2 ≤ k`) matching `M` on `S` and differing on `[a₀]`.

**Non-vacuity witness.** k = 2, infinite input alphabet I = Nat, and nontrivial output alphabet O = Bool. (`Toy.Witness.two_le_state_bound_infinite_alphabet_no_finite_teaching_set_nonvacuity`).

**Positive control.** Keeping `k = 2` and `HasTwoDistinct Bool` while switching to the finite alphabet `Unit` makes `[([], false), ([()], true), ([(), ()], false)]` teach `altMachine2.behavior` (`Toy.Witness.bounded_two_state_moore_unit_positive_control`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies, Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (p. 140 restriction to (n, m, p) machines with 'm input symbols or fewer').
- Mechanization search note (T1): checked Lean Mathlib Computability/DFA.lean and Computability/MyhillNerode.lean, Isabelle AFP entries FSM_Tests (Sachtleben 2022) and Adaptive_State_Counting (Sachtleben 2019) as of their Isabelle2026 releases (2026-10-26), and literature searches across Lean/Coq/Isabelle/Agda; existing FSM testing formalizations fix a finite input alphabet and no prior mechanization of this k >= 2 infinite-alphabet impossibility was found.

**Design question.** Shows that for every nontrivial state bound k >= 2 and every output alphabet with at least two distinct values, bounding internal state count alone never yields a finite conformance suite unless the input alphabet (or transition-distinguishing input partition) is also finite, while pinpointing k = 1 as the exact threshold where one example suffices over any alphabet.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — When outputs can take at least two distinct values, imposing an explicit state ceiling `k ≥ 2` never suffices for finite conformance testing unless the observable input alphabet (or the finite set of input equivalence classes distinguishable by transitions) is also finite. Conversely, at `k = 1` every machine is output-only and is taught by a single test `[([], c)]` regardless of alphabet cardinality.

#### R15 — Step-counting delayed-deviation machine (deviateAfter, Moore 1956 Thm. 2)

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.deviateAfter_agrees_before_and_differs_at`

**Plain claim.** For any n-state initialized Moore machine M, step threshold k, input symbol a, and output y' != M.behavior (replicate k a), the explicit (n * (k + 1))-state machine deviateAfter M k y' (Moore 1956, Theorem 2) agrees with M on all words of length < k and outputs y' != M.behavior (replicate k a) on replicate k a.

```lean
@Toy.Witness.deviateAfter_agrees_before_and_differs_at : ∀ {I : Type u_1} {O : Type u_2} {n : Nat}
  (M : Toy.Witness.InitMooreMachine I O n) (k : Nat) (a : I) (y' : O),
  y' ≠ Toy.Witness.InitMooreMachine.behavior M (List.replicate k a) →
    (∀ (w : List I),
        List.length w < k →
          Toy.Witness.InitMooreMachine.behavior (Toy.Witness.deviateAfter M k y') w =
            Toy.Witness.InitMooreMachine.behavior M w) ∧
      Toy.Witness.InitMooreMachine.behavior (Toy.Witness.deviateAfter M k y') (List.replicate k a) = y' ∧
        Toy.Witness.InitMooreMachine.behavior (Toy.Witness.deviateAfter M k y') ≠
          Toy.Witness.InitMooreMachine.behavior M
```

Unfolded (prose):

```text
for all types I, O, n : Nat, M : InitMooreMachine I O n, k : Nat, a : I, y' : O:
  y' ≠ M.behavior (List.replicate k a) →
  (∀ w : List I, w.length < k → (deviateAfter M k y').behavior w = M.behavior w) ∧
  (deviateAfter M k y').behavior (List.replicate k a) = y' ∧
  (deviateAfter M k y').behavior ≠ M.behavior
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hDiff : y' != M.behavior (List.replicate k a)` | Ensures the forced output y' at step k actually differs from M's output on replicate k a. | `tight` | `Toy.Witness.deviateAfter_ce_same_output` |
| `I : Type u, O : Type v, n : Nat, M, k : Nat, a : I, y' : O` | Unconditional over all alphabets, state counts `n ≥ 1`, step thresholds `k`, and symbols `a`. | `harmless` | — |

**Depth: shallow.** Tracks the product state, the pair of underlying state `M.run s w` and saturated counter `min (c + w.length) k`, by induction on `w`.

**Non-vacuity witness.** M = constMoore false over Unit -> Bool, k = 3, a = (), y' = true != false. (`Toy.Witness.deviateAfter_agrees_before_and_differs_at_nonvacuity`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 2 and the remark following it, p. 140).
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.

**Design question.** Mechanizes Moore's n(k+1)-state delayed-deviation construction showing why any finite conformance suite can be defeated if no upper bound on implementation states is enforced.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Given any finite test budget of words of length `< k`, a deterministic finite-state machine with `n * (k + 1)` states can mimic the `n`-state specification on every short word and output an arbitrary wrong value `y'` once `k` steps are reached. This defeats any conformance suite that lacks a state bound `k_max < n * (k + 1)`.

#### R16 — Unbounded-state Moore impossibility (Moore 1956 Thm. 2)

- **Kind:** impossibility. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Witness/Moore.lean`.
- **Lean:** `Toy.Witness.unbounded_moore_no_finite_teaching_set`

**Plain claim.** Over any nonempty input alphabet I and output alphabet O with at least two distinct values, no finite labeled sample teaches any behavior within the class FiniteStateMooreBehaviors I O of all finite-state deterministic Moore machines without a state bound (Moore 1956, Theorem 2).

```lean
@Toy.Witness.unbounded_moore_no_finite_teaching_set : ∀ {I : Type u_1} {O : Type u_2},
  Nonempty I →
    Toy.Witness.HasTwoDistinct O →
      ∀ (h : List I → O) (S : List (List I × O)), ¬Toy.Witness.Teaches (Toy.Witness.FiniteStateMooreBehaviors I O) h S
```

Unfolded (prose):

```text
for all types I, O:
  Nonempty I →
  HasTwoDistinct O →
  ∀ (h : List I → O) (S : List (List I × O)),
    ¬ Teaches (FiniteStateMooreBehaviors I O) h S
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hI : Nonempty I` | Provides an input symbol a to form arbitrarily long words replicate k a exceeding the longest word in S. | `tight` | `Toy.Witness.unbounded_moore_ce_empty_alphabet` |
| `hTwo : HasTwoDistinct O` | Provides an output value y' distinct from the target machine's output at step k. | `tight` | `Toy.Witness.unbounded_moore_ce_trivial_output` |
| `I : Type u, O : Type v` | Arbitrary nonempty input type and nontrivial output type across any universes. | `harmless` | — |

**Depth: shallow.** Sets `k := max_{p ∈ S} p.1.length + 1` and invokes R15 (`deviateAfter_agrees_before_and_differs_at`) with a symbol `a : I` and output `y' ≠ M.behavior (replicate k a)`.

**Non-vacuity witness.** I = Unit (Nonempty) and O = Bool (false != true). (`Toy.Witness.unbounded_moore_no_finite_teaching_set_nonvacuity`).

**Positive control.** Keeping `Nonempty Unit` and `HasTwoDistinct Bool` while adding the concrete numeric ceiling `k = 2` (`BoundedMooreBehaviors Unit Bool 2`) lets `[([], false), ([()], true), ([(), ()], false)]` teach `altMachine2.behavior` (`Toy.Witness.bounded_two_state_moore_unit_positive_control`).

**Prior art.**

- Edward F. Moore, "Gedanken-Experiments on Sequential Machines", in Automata Studies (Annals of Mathematics Studies, No. 34), Princeton University Press, pp. 129-153, 1956, DOI 10.1515/9781400882618-006 (Theorem 2 and the remark following it, p. 140).
- Tsun S. Chow, "Testing Software Design Modeled by Finite-State Machines", IEEE Transactions on Software Engineering SE-4(3):178-187, 1978, DOI 10.1109/TSE.1978.231496.
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.

**Design question.** Separates 'known to be finite-state' (insufficient for finite-suite completeness) from 'known to have at most k states over a finite alphabet, deterministic, and resettable' (sufficient for finite-suite completeness).

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Knowing only that an implementation is 'finite-state' (without a concrete numeric upper bound `k`) never allows a finite conformance suite to certify behavioral equivalence when the input alphabet is nonempty and outputs can take at least two distinct values, even over a 1-letter finite alphabet `Unit`.

#### R17 — Exact operational meaning of a passed conformance suite (Reference Point)

- **Kind:** characterization. **Tier:** T0. **Depth:** definitional. **Module:** `lean/Toy/Witness/Soundness.lean`.
- **Lean:** `Toy.Witness.passed_suite_certifies_iff_passingInClass`

**Plain claim.** Reference point: whenever h in H is the unique member of H consistent with labeled suite S (in particular whenever Teaches H h S, corollary passed_teaching_suite_certifies_iff_passingInClass), every candidate implementation impl in C passing S is extensionally equal to h if and only if every S-passing member of C belongs to H (PassingInClass C H S, which is strictly weaker than SubClass C H; see corollary passed_teaching_suite_certifies_subclass).

```lean
@Toy.Witness.passed_suite_certifies_iff_passingInClass : ∀ {X : Type u_1} {Y : Type u_2}
  (C H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  H h →
    Toy.Witness.UniqueConsistent H h S →
      ((∀ (impl : X → Y), C impl → Toy.Witness.Consistent S impl → impl = h) ↔ Toy.Witness.PassingInClass C H S)

@Toy.Witness.passed_teaching_suite_certifies_iff_passingInClass : ∀ {X : Type u_1} {Y : Type u_2}
  (C H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  Toy.Witness.Teaches H h S →
    ((∀ (impl : X → Y), C impl → Toy.Witness.Consistent S impl → impl = h) ↔ Toy.Witness.PassingInClass C H S)

@Toy.Witness.passed_teaching_suite_certifies_subclass : ∀ {X : Type u_1} {Y : Type u_2}
  (C H : Toy.Witness.HypothesisClass X Y) (h : X → Y) (S : List (X × Y)),
  Toy.Witness.SubClass C H →
    Toy.Witness.Teaches H h S → ∀ (impl : X → Y), C impl → Toy.Witness.Consistent S impl → impl = h
```

Unfolded (prose):

```text
for all types X, Y, classes C H : HypothesisClass X Y, target h : X → Y, sample S : List (X × Y):
  H h →
  UniqueConsistent H h S →
  ((∀ impl : X → Y, C impl → Consistent S impl → impl = h) ↔ PassingInClass C H S)

-- Corollaries:
-- passed_teaching_suite_certifies_iff_passingInClass :
--   Teaches H h S → ((∀ impl, C impl → Consistent S impl → impl = h) ↔ PassingInClass C H S)
-- passed_teaching_suite_certifies_subclass :
--   SubClass C H → Teaches H h S → ∀ impl, C impl → Consistent S impl → impl = h
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hh : H h` | Used for the forward direction: if every S-passing member of C equals h, then every S-passing member of C lies in H because h lies in H. | `tight` | `Toy.Witness.passed_suite_certifies_iff_ce_not_in_H` |
| `huniq : UniqueConsistent H h S` | Used for the backward direction: guarantees that any member of H passing S must equal h. | `tight` | `Toy.Witness.passed_suite_certifies_iff_ce_not_unique` |
| `X : Type u, Y : Type v, C : HypothesisClass X Y` | Arbitrary domain, codomain, and external implementation class `C`. | `harmless` | — |

**Depth: definitional.** Definitional unfolding of `UniqueConsistent` and `PassingInClass`.

**Non-vacuity witness.** H = ConstBoolClass, h = const true, S = [(false, true)] (satisfying both H h and UniqueConsistent H h S; passingInClass_pos_example and certification_holds_although_C_escapes_H show PassingInClass C H S can hold when SubClass C H fails). (`Toy.Witness.passed_suite_certifies_iff_passingInClass_nonvacuity`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003.
- Timothy A. Budd and Dana Angluin, "Two notions of correctness and their relation to testing", Acta Informatica 18(1):31-45, 1982, DOI 10.1007/BF00625279 (two notions of test-data correctness, automatic detection/generation, and relation to program equivalence).
- Kathleen Romanik and Carl Smith, "Testing geometric objects", Computational Geometry 4(3):157-176, 1994, DOI 10.1016/0925-7721(94)90005-1.
- Tsun S. Chow, "Testing Software Design Modeled by Finite-State Machines", IEEE Transactions on Software Engineering SE-4(3):178-187, 1978, DOI 10.1109/TSE.1978.231496.
- Rita Dorofeeva, Khaled El-Fakih, Stephane Maag, Ana R. Cavalli, and Nina Yevtushenko, "FSM-based conformance testing methods: A survey annotated with experimental evaluation", Information and Software Technology 52(12):1286-1297, 2010, DOI 10.1016/j.infsof.2010.07.001 (fault-domain / m-complete test suite contract).
- Robert Sachtleben, "Verified Complete Test Strategies for Finite State Machines", Archive of Formal Proofs, 9 Aug 2022 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/FSM_Tests.html.
- Robert Sachtleben, "Formalisation of an Adaptive State Counting Algorithm", Archive of Formal Proofs, 16 Aug 2019 (release for Isabelle2026, 2026-10-26), https://www.isa-afp.org/entries/Adaptive_State_Counting.html.

**Design question.** Reference point stating the exact epistemic contract of a passed conformance suite: given h in H and UniqueConsistent H h S (in particular Teaches H h S), 'passed S' certifies 'equals h' across C if and only if every S-passing member of C belongs to H (PassingInClass C H S), which holds in particular provided SubClass C H.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — In practice, passing a complete conformance suite `S` (where `h ∈ H` and `UniqueConsistent H h S`) certifies that an implementation `impl ∈ C` matches `h` *if and only if* every `S`-passing implementation in `C` satisfies the structural assumption `H` (`PassingInClass C H S`, implied in particular by `SubClass C H`). Thus a passed test suite never stands alone: it must be paired with an independent static, linguistic, or resource-bound argument placing passing candidates inside `H`.

#### R18 — Off-suite splicing converse (minimal hypotheses)

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Witness/Soundness.lean`.
- **Lean:** `Toy.Witness.splice_consistent_escapes_class_of_unique`

**Plain claim.** Whenever S is consistent with h and h is the unique member of H consistent with S (in particular whenever Teaches H h S; corollary passed_teaching_suite_without_class_bound_escapes_class), for any off-suite function outside differing from h at an untested input x0, the explicit splice spliceOutside h outside S passes S, equals outside on every untested input, differs from h, and lies outside H.

```lean
@Toy.Witness.splice_consistent_escapes_class_of_unique : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h outside : X → Y) (S : List (X × Y)) (x₀ : X),
  Toy.Witness.Consistent S h →
    Toy.Witness.UniqueConsistent H h S →
      ¬x₀ ∈ List.map Prod.fst S →
        outside x₀ ≠ h x₀ →
          have impl := Toy.Witness.spliceOutside h outside S;
          Toy.Witness.Consistent S impl ∧
            (∀ (x : X), ¬x ∈ List.map Prod.fst S → impl x = outside x) ∧ impl ≠ h ∧ ¬H impl

@Toy.Witness.passed_teaching_suite_without_class_bound_escapes_class : ∀ {X : Type u_1} {Y : Type u_2}
  (H : Toy.Witness.HypothesisClass X Y) (h outside : X → Y) (S : List (X × Y)) (x₀ : X),
  Toy.Witness.Teaches H h S →
    ¬x₀ ∈ List.map Prod.fst S →
      outside x₀ ≠ h x₀ →
        have impl := Toy.Witness.spliceOutside h outside S;
        Toy.Witness.Consistent S impl ∧ (∀ (x : X), ¬x ∈ List.map Prod.fst S → impl x = outside x) ∧ impl ≠ h ∧ ¬H impl
```

Unfolded (prose):

```text
for all types X, Y, class H, functions h outside : X → Y, sample S : List (X × Y), input x₀ : X:
  Consistent S h →
  UniqueConsistent H h S →
  x₀ ∉ S.map Prod.fst →
  outside x₀ ≠ h x₀ →
  let impl := spliceOutside h outside S;
  Consistent S impl ∧
  (∀ x : X, x ∉ S.map Prod.fst → impl x = outside x) ∧
  impl ≠ h ∧
  ¬ H impl

-- Corollary taking Teaches H h S (passed_teaching_suite_without_class_bound_escapes_class):
--   Teaches H h S → x₀ ∉ S.map Prod.fst → outside x₀ ≠ h x₀ → ...
```

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness | Counterexample (other hypotheses hold, conclusion fails) |
| :--- | :--- | :--- | :--- |
| `hcon : Consistent S h` | Ensures agreeing with h on the inputs of S makes spliceOutside h outside S consistent with S. | `tight` | `Toy.Witness.splice_consistent_escapes_class_ce_inconsistent` |
| `huniq : UniqueConsistent H h S` | Forces any distinct S-consistent splice to lie outside H (note: H h itself is not needed). | `tight` | `Toy.Witness.splice_consistent_escapes_class_ce_not_unique` |
| `hUntested : x0 not in S.map Prod.fst` | Ensures there exists at least one input not covered by S where off-suite behavior can diverge. | `tight` | `Toy.Witness.splice_consistent_escapes_class_ce_tested` |
| `hDiff : outside x0 != h x0` | Ensures the chosen off-suite behavior actually disagrees with h at x0. | `tight` | `Toy.Witness.splice_consistent_escapes_class_ce_agrees` |
| `X : Type u, Y : Type v, H : HypothesisClass X Y` | Arbitrary domain, codomain, and hypothesis class (does not even require `H h`). | `harmless` | — |

**Depth: shallow.** Evaluates `spliceOutside h outside S` on tested vs. untested inputs and applies `huniq` to rule out `H impl`.

**Non-vacuity witness.** H = ConstBoolClass, h = const true, outside = const false, S = [(false, true)], x0 = true. (`Toy.Witness.splice_consistent_escapes_class_of_unique_nonvacuity`).

**Prior art.**

- Sally A. Goldman and Michael J. Kearns, "On the Complexity of Teaching", Journal of Computer and System Sciences 50(1):20-31, 1995, DOI 10.1006/jcss.1995.1003.
- Timothy A. Budd and Dana Angluin, "Two notions of correctness and their relation to testing", Acta Informatica 18(1):31-45, 1982, DOI 10.1007/BF00625279 (two notions of test-data correctness, automatic detection/generation, and relation to program equivalence).
- Kathleen Romanik and Carl Smith, "Testing geometric objects", Computational Geometry 4(3):157-176, 1994, DOI 10.1016/0925-7721(94)90005-1.
- Rita Dorofeeva, Khaled El-Fakih, Stephane Maag, Ana R. Cavalli, and Nina Yevtushenko, "FSM-based conformance testing methods: A survey annotated with experimental evaluation", Information and Software Technology 52(12):1286-1297, 2010, DOI 10.1016/j.infsof.2010.07.001.
- David Lee and Mihalis Yannakakis, "Principles and Methods of Testing Finite State Machines—A Survey", Proceedings of the IEEE 84(8):1090-1123, 1996, DOI 10.1109/5.533956.
- Mechanization search note (T1): checked Lean Mathlib Computability/, Isabelle AFP entries FSM_Tests (Sachtleben 2022) and Adaptive_State_Counting (Sachtleben 2019) as of their Isabelle2026 releases (2026-10-26), and literature searches across Lean/Coq/Isabelle/Agda; no prior mechanization of this explicit off-suite splicing converse for teaching sets was found.

**Design question.** Shows that every off-suite behavior that differs from h at some untested input is realized by an S-passing function outside H; whether any such function lies in a concrete implementation class C is a separate question.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Whenever a suite leaves an input `x₀` untested, *any* off-suite behavior `outside` disagreeing with `h` at `x₀` can be spliced onto `h`'s suite behavior so that it passes every test in `S`; uniqueness in `H` guarantees only that such a passing divergent implementation must violate `H` (`¬ H impl`). Whether any implementation in a real candidate pool `C` realizes such a splice is a separate question about `C`.


## Boundaries

### Non-claims I: cross-cutting misreadings refuted in Lean

- **Class restriction is not automatically an escape hatch.** R2–R4 depend on `ClosedUnderPointPatches H`, not `IsUnrestricted H`. The strictly restricted class `EventuallyFalse : HypothesisClass Nat Bool` satisfies `ClosedUnderPointPatches` (`eventuallyFalse_closedUnderPointPatches`) while violating `IsUnrestricted` (`eventuallyFalse_not_unrestricted`), and still admits no finite teaching set (`eventuallyFalse_no_finite_teaching_set`). On an infinite domain with at least two distinct outputs, escape requires breaking single-point patch closure, as `BoundedMooreBehaviors Unit Bool 2` does over `List Unit` (`bounded_two_state_moore_unit_positive_control`). On a finite domain, an exhaustive suite can teach even in the unrestricted class (`patchClosed_hasUntestedInput_ce_exhaustive`, for `id` on `Bool → Bool`); there, breaking the closure is what permits a complete suite that leaves some input untested, as in `MonotoneConjunctions 2` (`patchClosed_untested_input_positive_control_monotone_conj`).
- **A state bound alone does not yield a finite suite.** Even with an explicit ceiling `k ≥ 2`, `BoundedMooreBehaviors I O k` admits no finite teaching set whenever `I` is infinite and `O` has two values (R14). Only `k = 1` escapes over infinite alphabets (`bounded_one_state_moore_single_example_teaches`). Conversely, a finite alphabet alone without a numeric state ceiling still fails (`FiniteStateMooreBehaviors`, R16).
- **Single-machine depth `n - 2` does not suffice for two `k`-state machines.** Testing words of length `≤ k - 2`, `< k`, or `≤ 2k - 3` fails for every `k ≥ 2` (`bounded_moore_class_suite_depth_sharp`; concrete `k = 2` witness `two_state_moore_length_lt_k_insufficient`); two separate `k`-state machines form a `2k`-state disjoint union, making `2k - 2` sharp.
- **Passing a teaching suite does not self-certify `SubClass C H` and does not need `SubClass C H`.** Certification across `C` holds iff `PassingInClass C H S` (R17), which is strictly weaker than `SubClass C H` (`certification_holds_although_C_escapes_H`). Conversely, off-suite splicing (R18) only guarantees `¬ H impl`; whether any candidate in `C` realizes `impl` depends on `C`.

### Non-claims II: by result

**R1 (`teaches_iff_hits_disagreement_sets_of_mem_of_consistent`).**

- Does not say that hitting all disagreement sets suffices when S has wrong or contradictory labels (hcon is tight) or when h lies outside H (hh is tight).
- Does not imply that a finite teaching set exists for every (H, h) or provide an algorithm to compute a minimum-size hitting set.
- Does not address randomized, PAC, or probabilistic testing guarantees; equality holds only against deterministic rivals in H.
- Does not cover cooperative or order-dependent teaching models such as recursive teaching dimension, where the learner may infer information from the absence of examples.

**R2 (`patchClosed_untested_input_patch_witness`).**

- Restricting the hypothesis class is not by itself an escape hatch. The operative property is closure under changing a function's value at one untested input: every class with that property — for example all computable functions on a type with decidable equality (not formalized here), or all eventually-false functions ℕ → Bool — also admits no finite teaching set on an infinite domain when outputs take at least two distinct values. On an infinite domain with at least two distinct outputs, only restrictions that break this closure (such as bounded-state Moore machines over a finite alphabet) can make a finite suite complete. On a finite domain, an exhaustive suite can be complete even for a patch-closed class (proved for id in the unrestricted class on Bool -> Bool by patchClosed_hasUntestedInput_ce_exhaustive); there, breaking the closure is what permits complete suites that leave some input untested (as for MonotoneConjunctions 2 in patchClosed_untested_input_positive_control_monotone_conj).
- The patched function patchAt h x₀ y' is computable whenever h is and equality on X is decidable (computability is not formalized here); the obstruction is not an artifact of non-computable lookup tables.
- Does not show that finite tests fail once patch-closure is broken (the positive control restricts H to MonotoneConjunctions 2 while keeping an untested input and nontrivial codomain).
- Does not apply when S exhausts a finite input domain X (hUntested is tight).

**R3 (`patchClosed_hasUntestedInput_no_teaching`).**

- Restricting the hypothesis class is not by itself an escape hatch. The operative property is closure under changing a function's value at one untested input: every class with that property — for example all computable functions on a type with decidable equality (not formalized here), or all eventually-false functions ℕ → Bool — also admits no finite teaching set on an infinite domain when outputs take at least two distinct values. On an infinite domain with at least two distinct outputs, only restrictions that break this closure (such as bounded-state Moore machines over a finite alphabet) can make a finite suite complete. On a finite domain, an exhaustive suite can be complete even for a patch-closed class (proved for id in the unrestricted class on Bool -> Bool by patchClosed_hasUntestedInput_ce_exhaustive); there, breaking the closure is what permits complete suites that leave some input untested (as for MonotoneConjunctions 2 in patchClosed_untested_input_positive_control_monotone_conj).
- Does not rule out finite teaching sets on finite domains when S tests every input in X (exhaustive testing).
- Does not rule out sub-exhaustive finite teaching sets once patch-closure is broken (as shown by MonotoneConjunctions 2, where 2 examples suffice on a 4-element domain).
- Does not quantify statistical generalization error on unseen inputs under a distribution.

**R4 (`patchClosed_infinite_no_finite_teaching_set`).**

- Restricting the hypothesis class is not by itself an escape hatch. The operative property is closure under changing a function's value at one untested input: every class with that property — for example all computable functions on a type with decidable equality (not formalized here), or all eventually-false functions ℕ → Bool — also admits no finite teaching set on an infinite domain when outputs take at least two distinct values. On an infinite domain with at least two distinct outputs, only restrictions that break this closure (such as bounded-state Moore machines over a finite alphabet) can make a finite suite complete. On a finite domain, an exhaustive suite can be complete even for a patch-closed class (proved for id in the unrestricted class on Bool -> Bool by patchClosed_hasUntestedInput_ce_exhaustive); there, breaking the closure is what permits complete suites that leave some input untested (as for MonotoneConjunctions 2 in patchClosed_untested_input_positive_control_monotone_conj).
- Does not support the slogan 'finite tests can never pin down behavior on an infinite domain': the positive control pins down a 2-state Moore machine over the infinite domain List Unit with 3 examples by breaking patch-closure.
- Identification in the limit (Gold 1967, DOI 10.1016/S0019-9958(67)91165-5) and exact learning from equivalence queries (Angluin 1988, DOI 10.1007/BF00116828) are different protocols and are outside this statement: they fail for the class of all functions on a countably infinite domain (not formalized here), but succeed for some restricted patch-closed classes such as EventuallyFalse (finite-support functions Nat -> Bool, which are identifiable in the limit from positive text and learnable with at most |support| + 1 equivalence queries with no uniform bound); the impossibility here concerns finite teaching sets only.
- Does not apply to finite domains (where exhaustive suites are finite) or subsingleton codomains.

**R5 (`monotone_conj_teaching_set_exact`).**

- The 2^m suite size for unrestricted Boolean functions is not a theorem of this package; the gap reflects that the class has only 2^m members and does not imply that structural restrictions generally yield exponential savings (patch-closed restricted classes yield none).
- Does not include the constant-false function or conjunctions with negated literals (general monomials have a different minimum teaching-set formula).
- Does not describe cooperative or recursive teaching dimension (Doliwa et al. 2014, Corollary 9(2), show RTD(Monotone Monomials) = 1, strictly smaller than min (r + 1) m when r >= 1 and m >= 2).
- Does not give an upper bound on adaptive membership-query complexity: teaching dimension provides only a lower bound on the number of membership queries needed for exact identification (Goldman and Kearns 1995).

**R6 (`monotone_conjunctions_teaching_dimension`).**

- Does not mean every monotone conjunction requires m examples: the empty conjunction (r = 0) needs only 1 example when m >= 1, and in general a conjunction of r variables needs min (r + 1) m.
- Does not extend to non-monotone monomials, k-DNF formulas, or arbitrary monotone Boolean functions.
- Does not measure recursive teaching dimension (RTD = 1 for monotone monomials for all m >= 1; Doliwa et al. 2014, Corollary 9(2)).

**R7 (`moore_state_equiv_iff_agree_up_to`).**

- Moore's Theorem 6 assumes pairwise-distinguishable states and a finite alphabet and counts an experiment of length L as L input symbols whose outputs are read before each symbol is applied; 'length n − 1' there equals 'words of length ≤ n − 2' here. This statement drops both hypotheses (a standard generalization).
- Does not say that words of length <= k - 2 or < k suffice when comparing two separate k-state machines: two k-state machines have 2k states in total and require words up to length 2k - 2 (refuted for all k >= 2 by bounded_moore_class_suite_depth_sharp and concretely at k = 2 by two_state_moore_length_lt_k_insufficient).
- Does not guarantee a finite test suite when the input alphabet I is infinite (refuted for all k >= 2 and every O with at least two distinct values by two_le_state_bound_infinite_alphabet_no_finite_teaching_set).
- Does not apply to nondeterministic, probabilistic, or non-resettable (homing/checking-sequence) machines without a reliable reset to the initial state.
- Does not give the word-length bound for Mealy machines (whose outputs live on transitions, shifting the sharp input-word bound from n - 2 to n - 1).

**R8 (`moore_two_machine_equiv_iff_agree_up_to`).**

- Does not imply that words of length <= max n1 n2 - 2 or < max n1 n2 suffice: the worst-case horizon is the exact sum n1 + n2 - 2 (proved sharp for all n1 >= 1, n2 >= 1 in moore_two_machine_bound_sharp).
- Does not by itself yield a finite test suite when I is infinite (refuted for all k >= 2 and every O with at least two distinct values by two_le_state_bound_infinite_alphabet_no_finite_teaching_set).
- Does not bound the size of an optimal checking sequence (e.g. Chow's W-method reduces the number of tests using state covers and characterization sets, whereas naive enumeration tests all words up to length n1 + n2 - 2).

**R9 (`moore_bound_sharp`).**

- Does not claim that every n-state machine has states requiring length n - 2 to separate (many machines have much shorter distinguishing words).
- Does not claim that all words of length <= n - 2 must be tested: only that the worst-case maximum word length cannot be reduced below n - 2.

**R10 (`finite_alphabet_bounded_moore_spec_suite_teaches`).**

- State counts are for Moore machines (outputs attached to states, the empty word observing the initial output). A k-state Mealy implementation (outputs on transitions) can need more Moore states, so the depth formula does not transfer verbatim.
- Does not certify implementations that exceed k2 states (unbounded_moore_no_finite_teaching_set shows no finite suite works without a state bound).
- Does not yield a finite suite over an infinite input alphabet when k2 >= 2 and O has at least two distinct values (two_le_state_bound_infinite_alphabet_no_finite_teaching_set).
- Does not claim that mooreSpecTestSuite is minimum-size: for |I| >= 2 and k2 >= n1, naive enumeration up to length n1 + k2 - 2 has total input-symbol length O((n1 + k2) * |I|^(n1 + k2 - 2)) (for |I| = 1, O((n1 + k2)^2) symbols), whereas structured methods such as Vasilevskii (1973) and Chow's W-method (1978) achieve total input-symbol length O(|I|^(k2 - n1 + 1) * n1^2 * k2) when k2 >= n1 and the specification is minimal, completely specified, and initially connected with reliable reset (strong connectivity is not required).
- Does not apply without a reliable reset between test words (single-sequence checking experiments require additional homing/synchronizing assumptions).

**R11 (`finite_alphabet_bounded_moore_class_suite_teaches`).**

- State counts are for Moore machines (outputs attached to states, the empty word observing the initial output). A k-state Mealy implementation (outputs on transitions) can need more Moore states, so the depth formula does not transfer verbatim.
- Does not work with words of length <= 2 * k - 3 or < k for any k >= 2 (refuted for all k >= 2 by bounded_moore_class_suite_depth_sharp and concretely at k = 2 by two_state_moore_length_lt_k_insufficient).
- Does not provide minimum-size teaching sets (the universal suite does not exploit the specific target's minimal state count).
- Does not apply when the input alphabet I is infinite, k >= 2, and O has at least two distinct values (two_le_state_bound_infinite_alphabet_no_finite_teaching_set) or when candidate implementations can exceed k states.

**R12 (`moore_two_machine_bound_sharp`).**

- Does not claim that every pair of (n1, n2)-state machines requires depth n1 + n2 - 2 to separate (many pairs disagree on much shorter words).
- Does not claim that every word of length <= n1 + n2 - 2 must be tested: only that the worst-case horizon cannot drop below n1 + n2 - 2.

**R13 (`bounded_moore_class_suite_depth_sharp`).**

- Does not contradict Moore's single-machine bound: two k-state machines together have 2k states, so Moore's bound gives 2k - 2, matching the deviation length.
- Does not claim that length 2k - 2 is insufficient (finite_alphabet_bounded_moore_class_suite_teaches proves 2k - 2 is always sufficient over any finite alphabet).
- Does not imply every individual k-state specification requires a teaching word of length 2k - 2 (for instance, at k = 1 depth 0 suffices, and many targets at k >= 2 have shorter target-specific suites).

**R14 (`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`).**

- It does not show that every state bound fails over an infinite alphabet: at state bound 1 every behavior is constant and is taught by one example over any alphabet (proved in bounded_one_state_moore_single_example_teaches and two_le_state_bound_infinite_alphabet_ce_one_state).
- Does not contradict moore_two_machine_equiv_iff_agree_up_to: two k-state machines over an infinite alphabet are still equivalent iff they agree on all words of length <= 2k - 2, but there are infinitely many such words.
- Does not rule out symbolic or input-equivalence-class testing when transitions are restricted to finitely many input predicates.

**R15 (`deviateAfter_agrees_before_and_differs_at`).**

- The construction (n(k+1) states) and the impossibility are Moore's (1956, Theorem 2 and the remark following it); the contribution here is the mechanization only.
- Does not produce a rival within a fixed state bound k_max when n * (k + 1) > k_max.
- Does not imply that finite-state machines are unlearnable with equivalence queries (Angluin's L* algorithm learns regular sets / minimal DFAs using membership plus equivalence queries; Dana Angluin, "Learning regular sets from queries and counterexamples", Information and Computation 75(2):87-106, 1987, DOI 10.1016/0890-5401(87)90052-6).

**R16 (`unbounded_moore_no_finite_teaching_set`).**

- The construction (n(k+1) states) and the impossibility are Moore's (1956, Theorem 2 and the remark following it); the contribution here is the mechanization only.
- A state bound alone is not sufficient: finite completeness also needs a finite input alphabet (two_le_state_bound_infinite_alphabet_no_finite_teaching_set, for k >= 2 and outputs with at least two distinct values), deterministic behavior, and reliable reset between test words.
- Does not apply once an explicit state upper bound k is imposed and the input alphabet is finite (positive control at k = 2 over Unit -> Bool).
- Does not rule out interactive learning of unbounded-state DFAs/Moore machines with membership plus equivalence queries (Angluin's L*, Information and Computation 75(2):87-106, 1987, DOI 10.1016/0890-5401(87)90052-6; general query model in Angluin 1988, DOI 10.1007/BF00116828) or identification in the limit from informant (labeled positive and negative examples; Gold 1967, DOI 10.1016/S0019-9958(67)91165-5).
- Does not apply to an empty input alphabet (hI is tight) or a subsingleton output alphabet (hTwo is tight).

**R17 (`passed_suite_certifies_iff_passingInClass`).**

- SubClass C H is sufficient, not necessary: the conclusion also holds whenever every member of C that passes S lies in H, and it can hold when C is not contained in H. Failure of SubClass C H does not by itself produce a member of C that passes S and differs from h.
- Does not establish PassingInClass C H S or SubClass C H: class membership of S-passing implementations must be discharged independently (e.g. by static analysis, grammar/type constraints, or formal proof).
- Does not guarantee anything about non-functional properties (timing, memory, side channels) not modeled in X -> Y.

**R18 (`splice_consistent_escapes_class_of_unique`).**

- The statement does not mention the implementation class C. The spliced function lies outside H; whether any member of C realizes it, or any other passing behavior different from h, depends on C.
- Does not mean a passed teaching suite is useless: it forces any disagreeing passing function to violate the structural hypothesis H (not H impl).
- Does not apply when S tests every input in a finite domain X (hUntested is tight).


### Escape hatches of the impossibility results

- **R2 (`patchClosed_untested_input_patch_witness`)** fails if `H` breaks `ClosedUnderPointPatches` (`patchClosed_untested_input_positive_control_monotone_conj`), if `h ∉ H` (`patchClosed_untested_input_ce_not_in_H`), if `¬ Consistent S h` (`patchClosed_untested_input_ce_inconsistent`), if `x₀` is tested (`patchClosed_untested_input_ce_tested`), or if `y' = h x₀` (`patchClosed_untested_input_ce_same_val`).
- **R3 (`patchClosed_hasUntestedInput_no_teaching`)** fails if `H` breaks `ClosedUnderPointPatches` (`patchClosed_hasUntestedInput_ce_not_patchClosed`, `patchClosed_untested_input_positive_control_monotone_conj`), if `Y` is a subsingleton (`patchClosed_hasUntestedInput_ce_trivial_codomain`), or if `S` tests every input in a finite domain (`patchClosed_hasUntestedInput_ce_exhaustive`).
- **R4 (`patchClosed_infinite_no_finite_teaching_set`)** fails if `H` breaks `ClosedUnderPointPatches` (`patchClosed_infinite_ce_not_patchClosed`, `bounded_two_state_moore_unit_positive_control`), if `Y` is a subsingleton (`patchClosed_infinite_ce_trivial_codomain`), or if `X` is finite (`patchClosed_infinite_ce_finite_domain`).
- **R14 (`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`)** fails at `k = 1` (`two_le_state_bound_infinite_alphabet_ce_one_state`, `bounded_one_state_moore_single_example_teaches`), over a finite alphabet (`two_le_state_bound_infinite_alphabet_ce_finite_alphabet`, `bounded_two_state_moore_unit_positive_control`), or over a subsingleton output (`two_le_state_bound_infinite_alphabet_ce_trivial_output`).
- **R16 (`unbounded_moore_no_finite_teaching_set`)** fails when an explicit numeric state ceiling `k` is paired with a finite alphabet (`bounded_two_state_moore_unit_positive_control`), over an empty input alphabet (`unbounded_moore_ce_empty_alphabet`), or over a subsingleton output (`unbounded_moore_ce_trivial_output`).
- **Sharpness bounds R9 and R13** have exact lower thresholds: R9 fails at `n = 1` (`moore_bound_sharp_ce_small_n`) and R13 fails at `k = 1` (`bounded_moore_class_suite_depth_sharp_ce_one_state`).

### Hypotheses with unknown tightness

None. Every side-condition hypothesis across all 18 results is proved `tight` via a canonical counterexample theorem (`all other hypotheses hold and the conclusion fails`), and unconstrained universe/type parameters are `harmless`.

### Disproved or withdrawn statements

None; every listed statement is proved as stated.

### Not examined, unsupported, and known not to apply

- **Known not to apply:** `BoundedMooreBehaviors` bounds and `n - 2` / `n₁ + n₂ - 2` / `2k - 2` formulas do not transfer directly to Mealy machines (transition-output bound is `n - 1` and Moore conversion can multiply state counts by up to `|O|`), nor to non-resettable checking experiments or infinite input alphabets when `k ≥ 2`; `MonotoneConjunctions` excludes `const false` and negated-literal conjunctions; `HasTeachingDimension` does not model recursive/cooperative teaching (`RTD = 1` for monotone monomials).
- **Not examined:** Computable functions and decidable equality variants as formalized classes (R2–R4 non-claims note computability informally without formalizing a computability model); structured state-cover/characterization-set minimization (e.g. Vasilevskii / Chow W-method); probabilistic/PAC testing; nondeterministic or probabilistic automata; non-functional execution properties (timing, memory, side effects).
- **Unsupported:** Dependent or dynamically keyed record schemas (`BoolAssignment m` fixes `m` features; `MooreMachine` fixes a single input type `I` and output type `O`).

## Evidence

**Kernel check.** Built with Lean `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) on 2026-11-20: `lake build` in `lean/` succeeds with 0 errors and 0 warnings across all 10 build jobs. Source scans confirm zero occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `#exit`, `ofReduceBool`, or `ofReduceNat`. `Lean.collectAxioms` across all 296 non-internal declarations under `Toy` reports only subsets of `{propext, Classical.choice, Quot.sound}` (`134` with none, `42` with `propext`, `2` with `Quot.sound`, `41` with `Quot.sound, propext`, and `77` with `Classical.choice, Quot.sound, propext`); full per-declaration records are stored in `audit/axioms.json`.

**Statement and definition-closure hashes.** For all 156 declarations referenced by `results.json` (results; the companions, supporting lemmas, and definition examples listed in each card's `lean_names`; non-vacuity witnesses; positive controls; and hypothesis counterexamples), `audit/statements.json` records the SHA-256 of `toString (repr ci.type)` and the SHA-256 of the sorted, newline-joined definition closure (all `Toy.*` constants reachable through `ci.type` and non-theorem definition bodies; theorem proof bodies are excluded). Every public theorem named in this report is among these 156 declarations, and every public definition named in this report lies in the definition closure of at least one of them, so a change to any printed statement or definition changes a recorded hash.

| Lean name | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Witness.MooreMachine.run_append` | R7 supporting lemma | none | `34cfe2207957f91bf2234c1aa9a37f9b53c94d5e4f9dbf0b11471abc6611a107` | `541e4f19011fe534f4c054cd98113b9e4e5f787a8f55d69d52e7701e6a6beb58` (6) |
| `Toy.Witness.agreeUpTo_neg_example` | R7 definition example | none | `73f0cf358d0c788410c3622bb574c0a5ce41d3fef2ceefee44c91d564dd7854f` | `93d7517f0fe5c1862319b15d97eef31df92ac6f8143d7acad2430e7bdb25f95b` (10) |
| `Toy.Witness.agreeUpTo_pos_example` | R7 definition example | propext | `b01b80090b4bddcdc7ff678aefa5722290b263abdafbb950dd1babdd72fce12d` | `93d7517f0fe5c1862319b15d97eef31df92ac6f8143d7acad2430e7bdb25f95b` (10) |
| `Toy.Witness.altMachine2_behavior` | R13 definition example | Quot.sound, propext | `d9608c56fa4715d4e70d417399a9f7ee9539d8c95c1ebe5afd683419ddb89698` | `31e862e619a0a30cff402793ee3ead0f51382f9ff1d329f447094f60d6c2d4f2` (16) |
| `Toy.Witness.behavior_disjointUnion_inl` | R8 supporting lemma | Quot.sound, propext | `b1af7c5005587d83cebef85e2c3162a5274adca4e445fe92b36c2e50681cba59` | `ea2008aa767321c53130c9b1085f91f4b2059a087fbb6dbf0d49a3e608e7dbc9` (17) |
| `Toy.Witness.behavior_disjointUnion_inr` | R8 supporting lemma | Quot.sound, propext | `ddd344503d073caebc38482077ba0e782c13a85188096dbbaadf6d4cf1e76fd1` | `ea2008aa767321c53130c9b1085f91f4b2059a087fbb6dbf0d49a3e608e7dbc9` (17) |
| `Toy.Witness.boundedMooreBehaviors_neg_example` | R10 definition example | Quot.sound, propext | `c0b023983ff2b914445c5c9933125417bc47acc7d5c177f6da9a9399aa189d18` | `f6dce048336622742f418c6fff61c582e03889755aab44bade1ad17e26d5da02` (15) |
| `Toy.Witness.boundedMooreBehaviors_pos_example` | R10 definition example | Quot.sound, propext | `fd8812432f571f9dedb084e46f7fa30c5bd6420adfffe56570017478bc9af3c9` | `f6dce048336622742f418c6fff61c582e03889755aab44bade1ad17e26d5da02` (15) |
| `Toy.Witness.bounded_moore_class_suite_depth_sharp` | R13 result | Classical.choice, Quot.sound, propext | `e6f6b13858ab101d8700d5a66a767434126303eec30b1df0a878c25b6d60ec9e` | `2457282c972f2ded559b670a1bc59aa816d5c806b209ed827e440534284d6902` (27) |
| `Toy.Witness.bounded_moore_class_suite_depth_sharp_ce_one_state` | R13 counterexample (`hk`) | Quot.sound, propext | `b3ca8f1339cad11e23b31a347fb40c192c1a2b2255e7380f157c7df892859a98` | `2457282c972f2ded559b670a1bc59aa816d5c806b209ed827e440534284d6902` (27) |
| `Toy.Witness.bounded_moore_class_suite_depth_sharp_nonvacuity` | R13 non-vacuity | none | `83c63b85bfd7fc34e785e31a2c73d94851f7686031f49a7859461a152ac84266` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Witness.bounded_one_state_moore_single_example_teaches` | R14 companion | Quot.sound, propext | `392221962f5c98ea504a12e135ae59c207bfd2ef1256c6e80b41537ed0cbe8c6` | `5d9b5d431630d5f1cc404c37ccc817b70d5bcb5c84b31439f62bc9be7024eea1` (18) |
| `Toy.Witness.bounded_two_state_moore_unit_positive_control` | R4 positive control; R14 positive control; R16 positive control | Classical.choice, Quot.sound, propext | `29db6efb03338233be06875ea9e8513bd42b052a67c094b76ac3130a35b0648c` | `93df7a6fd32a5404d92a03c6739b9b661d3cf0a39934bfabf0db450ad6c16d18` (25) |
| `Toy.Witness.certification_holds_although_C_escapes_H` | R17 companion | propext | `e34ee05c31dcb14c5e63053abefaf52284d975b8734494619ab2001ffd729bb1` | `f8de2b5cdcedab118d6579d8c94b5257ebea787283abc861a6da555bf68c1fe6` (6) |
| `Toy.Witness.closedUnderPointPatches_neg_example` | R2 definition example | Classical.choice, Quot.sound, propext | `1c48fedba848e4fefae7627898410e61bb01b5394337d9a7bf28ce83d5a8cb23` | `1211b0084463c2fe1177b763d4f93a8f253aa5cef7629be2b7c536f22ccdfd59` (4) |
| `Toy.Witness.closedUnderPointPatches_pos_example` | R2 definition example | Classical.choice, Quot.sound, propext | `c61c4c351c23302b1df583c92f9b8f83321247eb46067b6ad6b9ed39611ba8a9` | `02324748e3df492ac93a13c11b0bf3670284b1d9601d28476e734ef746353156` (5) |
| `Toy.Witness.consistent_labelSample` | R1 supporting lemma | Quot.sound, propext | `2a76cad02d242b6584234ca330aa49dd9ef8ccd5a5e2f2d0c9c852109af6f3cb` | `487c9a8acff314746b149c0b55646d46340a2b91a291d3fd5e9f7b21ccc91197` (2) |
| `Toy.Witness.consistent_neg_example` | R1 definition example | propext | `c53b8d688c2902181823c0c28fc92c325c19c9c34811114b138433dbdc52338d` | `ae2883f122dc2ca862c46947a1f28285ba454f74fa71ae65a0aae67536e78e47` (1) |
| `Toy.Witness.consistent_pos_example` | R1 definition example | propext | `a37866d479efc0e50bf77aa61169e23155baf77d355d888dcc83b15de1f139b6` | `ae2883f122dc2ca862c46947a1f28285ba454f74fa71ae65a0aae67536e78e47` (1) |
| `Toy.Witness.constMoore_behavior` | R14 definition example | propext | `21b4702217cb3f913c2797bbe429ad7d1784986511cb4787f02a9b9a4c23aeae` | `b7dca28481947b81c950f9d7343989b41438935800fb2ebe063e0869f842bdcd` (15) |
| `Toy.Witness.coversAll_neg_example` | R10 definition example | propext | `8c49850681bc540853acbe5e88fe7438db21ca57279b56df86c4851fa26d546f` | `7cf2d5da291ee1ccaa30b712ccd97b2cf404114e6d73e175195dd06a3bce5cba` (1) |
| `Toy.Witness.coversAll_pos_example` | R10 definition example | propext | `64c259c0d2e809232844814f16da60287fd0c3c83e61f5643ae075701c563a6e` | `7cf2d5da291ee1ccaa30b712ccd97b2cf404114e6d73e175195dd06a3bce5cba` (1) |
| `Toy.Witness.deviateAfter_agrees_before_and_differs_at` | R15 result | Classical.choice, Quot.sound, propext | `a5653bcb246b32cc9e464bf13a45a353b64748874deba7b30178f6db4caaa371` | `27224a2ebaadef557bb45413fba9514fa5d19c81aab3cbdb83d869b910499898` (21) |
| `Toy.Witness.deviateAfter_agrees_before_and_differs_at_nonvacuity` | R15 non-vacuity | propext | `549f743a0e71d19e5e6baf18f71161a0177d870d34bd19b75281a1397166297f` | `b7dca28481947b81c950f9d7343989b41438935800fb2ebe063e0869f842bdcd` (15) |
| `Toy.Witness.deviateAfter_ce_same_output` | R15 counterexample (`hDiff`) | Classical.choice, Quot.sound, propext | `2a90093211afa8eba0f75367d2bca7ebed7e4c3cb16da7e0a68cc79c4593e99e` | `540b1b442a9baa75a1ecfae67b56880cf1a28078c1c583428e443abcb18a11b2` (23) |
| `Toy.Witness.disagreementSet_neg_example` | R1 definition example | none | `daec493861e44c16687a254151b683968cf06d6ba2040dce6d7c79f3bbda6bb0` | `22f164d12df8457d1ec5cd80e19535962d8d53b33f2ae68c2cfa4de9291eaded` (1) |
| `Toy.Witness.disagreementSet_pos_example` | R1 definition example | none | `221de96fe94dc9f8218f23405ec1a014ac932a099cc33a68f236d98007a02f5f` | `22f164d12df8457d1ec5cd80e19535962d8d53b33f2ae68c2cfa4de9291eaded` (1) |
| `Toy.Witness.evalMonotoneConj_all_true` | R5 definition example | Quot.sound, propext | `48255dd57a6fcbe51aefea895522c9aeb67f894e029aa96c840400ac187aae41` | `790f2f2330ba33e6545d88b9a612a82606e9068af7e0663882aaab501ec491c0` (2) |
| `Toy.Witness.eventuallyFalse_closedUnderPointPatches` | R4 supporting lemma | Classical.choice, Quot.sound, propext | `b63fe8484807d54e7e0aff8fab5a4803f6f30878a83048cc213c5602af70509b` | `21c0b5f26ccb1de62703a83df48d682a3fab646bd3353b4d584ee320ff376896` (4) |
| `Toy.Witness.eventuallyFalse_no_finite_teaching_set` | R4 companion | Classical.choice, Quot.sound, propext | `4f2089b06d05ccfd053564bd5b46accbdcdbab68aad686778c5718a3440e3254` | `095eb1e7e3f5f38af8576aa44f4b82c293df17015f1e226848825dbf7c470d2c` (5) |
| `Toy.Witness.eventuallyFalse_not_unrestricted` | R4 supporting lemma | none | `85e3fed1d05aafe523b02cb6f30aaff5f40b7b145d12b1d6da9dfe04a7793e27` | `5a3c3d08f7c7ebfe70edf245ec080f52d4cdfb6e74e886354b6476ea51eaf81a` (3) |
| `Toy.Witness.finiteStateMooreBehaviors_neg_example` | R16 definition example | Quot.sound, propext | `5711c0d92fbfd54a0ba99d435c2b2c140229df3a5ba4e2786d35a21b210f735e` | `4b726b055c42e304c9afb6c2a06a7e21ff696c2e8261f464379a2acd53a41dc7` (15) |
| `Toy.Witness.finiteStateMooreBehaviors_pos_example` | R16 definition example | Quot.sound, propext | `288ef97f6925e1b2c639874fe93083cc6a51986b44c47e89069a70e56a7827b0` | `4b726b055c42e304c9afb6c2a06a7e21ff696c2e8261f464379a2acd53a41dc7` (15) |
| `Toy.Witness.finite_alphabet_bounded_moore_class_suite_ce_incomplete_alphabet` | R11 counterexample (`hCover`) | Quot.sound, propext | `ad1ffbd7d3fccc912d433e6392572804ac55bb7de0cbf1eebf4a5803eff80b78` | `0be217526da28220f628887d5f1cabf325d39cbfd9e2ba77fa445328eecc49a5` (26) |
| `Toy.Witness.finite_alphabet_bounded_moore_class_suite_ce_target_outside_bound` | R11 counterexample (`hMem`) | Quot.sound, propext | `483d1c7f73666d81eb498380fe7d2c94be5cab4d3a04b81a173eb6f0b08766e9` | `24dc4cdd987dc060e0a55189823d7639709ecef92600efbfc1a5ac266e2e71cd` (29) |
| `Toy.Witness.finite_alphabet_bounded_moore_class_suite_teaches` | R11 result | Classical.choice, Quot.sound, propext | `a4cb1110f3ea77cc81d61975452b7ba3b24b34f8b6ee615b0f44ea299c5cfe9f` | `0be217526da28220f628887d5f1cabf325d39cbfd9e2ba77fa445328eecc49a5` (26) |
| `Toy.Witness.finite_alphabet_bounded_moore_class_suite_teaches_nonvacuity` | R11 non-vacuity | propext | `92aed58b319a8e6aa10e6434a5f23ff37bf53ec95dd49c228622ca7b011ba0f2` | `afbb6857c39543023a116fce0dbe9278604c7ae9578cee7801576964cb5cfd9f` (19) |
| `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_ce_incomplete_alphabet` | R10 counterexample (`hCover`) | Quot.sound, propext | `d988063606a2c27c3e591ce55eb025477b9e9595f1634f17ab2ef27fa2ccd0dc` | `e4b1e76ef7f8f81c21663517675eac648818e0ecec82a93238e2dba6c72a7ff5` (28) |
| `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound` | R10 counterexample (`hMem`) | Quot.sound, propext | `79e2e670db8db969f7485e3c084e8e44c7cc05d1d203475e6d4d757ba04e65e0` | `1a93aa543639628f2dbd1b43400eda9cb043123ce5e576a77cf032a849ecaad7` (29) |
| `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_certifies` | R10 companion | Classical.choice, Quot.sound, propext | `ce231ec19e0cc68cb8039a16b329f8a96b50e0f01d439d542252c5383d9ec9e5` | `80dea2710397e251779bb7ef04781de0f77ccae4513846000edb7b7b1ec44997` (25) |
| `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_teaches` | R10 result | Classical.choice, Quot.sound, propext | `4c7b0c8c0eaf6b6a0334c921332fbfe6c8340f0869014fd7b8dfc49ef21ef0ab` | `536125ea1a9e2a6ff7558a9696b84501308665545e5b1663910dd7c72d21d536` (26) |
| `Toy.Witness.finite_alphabet_bounded_moore_spec_suite_teaches_nonvacuity` | R10 non-vacuity | propext | `92aed58b319a8e6aa10e6434a5f23ff37bf53ec95dd49c228622ca7b011ba0f2` | `afbb6857c39543023a116fce0dbe9278604c7ae9578cee7801576964cb5cfd9f` (19) |
| `Toy.Witness.hasMinTeachingSize_neg_example` | R5 definition example | propext | `19a5e853f0af4ca9c1ca86f0d70a5af91276d4615a69773a09c39026eb2af57e` | `54774f8ad038aaa6680a81c18a2c57abf3d3b2598c5a0c173e05d526451856c1` (6) |
| `Toy.Witness.hasMinTeachingSize_pos_example` | R5 definition example | propext | `0edb0d1a937fdf5413846f20cc2005b1bc9a66e91d5687da8e03751425ba5e9d` | `54774f8ad038aaa6680a81c18a2c57abf3d3b2598c5a0c173e05d526451856c1` (6) |
| `Toy.Witness.hasMinTeachingSize_unique` | R5 supporting lemma | none | `bcba7e1251434e1f092d223b9995a983e3a6900964687aa5e7f44cf459144ae8` | `45d1200ee627909c4763b56e7d09bef293f8a51fe431c1c67dc5b39866b83c38` (5) |
| `Toy.Witness.hasTeachingDimension_neg_example_constBool_0` | R6 definition example | propext | `449b881ee5eaa24bb1d68858c5eb9148d50b9f2659ec8cf084da7de3bdcbf24a` | `d7743bcca1d7128f30e13fbe9584a8e3ca732869e409285b161adeb7a6e41021` (6) |
| `Toy.Witness.hasTeachingDimension_neg_example_constBool_2` | R6 definition example | propext | `cf715fac2b9cbca0205e5809366df8a4cfd638f7dbc66f9ffb0937a0173f08e6` | `d7743bcca1d7128f30e13fbe9584a8e3ca732869e409285b161adeb7a6e41021` (6) |
| `Toy.Witness.hasTeachingDimension_neg_example_empty` | R6 definition example | none | `1888b6dccaff4f8bfc16c47d903d35264ede7277d15b4f8ab8c80b10a6b95e9c` | `790f89dd3164d12b50aa92a18bc096f9b7f510b09cc9cb73e3c36ccf007dfc20` (5) |
| `Toy.Witness.hasTeachingDimension_pos_example` | R6 definition example | propext | `ce051d7603e01179710d1b6b1713da8f2fa31d38286d7ce093ab010fd0e3cbb8` | `d7743bcca1d7128f30e13fbe9584a8e3ca732869e409285b161adeb7a6e41021` (6) |
| `Toy.Witness.hasTeachingDimension_unique` | R6 supporting lemma | none | `10d88690f56381d51317eb296803ca3d301cad56ee189c9e97e2b20d88e030bf` | `790f89dd3164d12b50aa92a18bc096f9b7f510b09cc9cb73e3c36ccf007dfc20` (5) |
| `Toy.Witness.hasTwoDistinct_neg_example` | R3 definition example | none | `31e799a384be69422a8d666b8447cbec20e152255c5d0eae30f3839b361c3c13` | `cbdbf1ee9c2bfeccf050a23cef1aea0b704822df9ff8ce28d3fc6c2b9d772571` (1) |
| `Toy.Witness.hasTwoDistinct_pos_example` | R3 definition example | none | `132f1ffabbac69ff84dd6c919c8bc414561bcf19ff498eb5421a6c3340561c33` | `cbdbf1ee9c2bfeccf050a23cef1aea0b704822df9ff8ce28d3fc6c2b9d772571` (1) |
| `Toy.Witness.hasUntestedInput_neg_example` | R3 definition example | propext | `e52e15e9add603ee30a383f4d753d28225281ad2b235f419fe1557b3a503fc86` | `779d3965b7f91acceec0b7847a7861a0665184278f16924176b04fff51fd2c2e` (1) |
| `Toy.Witness.hasUntestedInput_pos_example` | R3 definition example | propext | `d4bfbe4dae313500929392516174150806c585fdc7630127fbd2835aa97fb38e` | `779d3965b7f91acceec0b7847a7861a0665184278f16924176b04fff51fd2c2e` (1) |
| `Toy.Witness.hitsAllDisagreements_neg_example` | R1 definition example | propext | `e0761dd2f3d91529dd5f757c6ad2efde75066fb8501dfcd182fb9b36764bba89` | `c7c73aff170db9b5a48042af9be033e3630ae74ebbce6ef9fb8d6fd55ee91e10` (3) |
| `Toy.Witness.hitsAllDisagreements_pos_example` | R1 definition example | propext | `d54b86390ee425cb48de76c62187eb9d2fde01fccc61cb06cfc4da1c7c25b6eb` | `3107b83541dfcba3458de47d5ccaa3893abe5ee6acca50a0d653ddc8ac88ed5c` (4) |
| `Toy.Witness.infiniteDomain_neg_example` | R4 definition example | propext | `a36d35cd74fd31ca6190aee40d1e8a83d1acd432109178078b9a781d7bd95527` | `6eb3a2c0aac97f2fc1e991292e7b65012ffbea3d20d1ea733aaae77038ff9276` (1) |
| `Toy.Witness.infiniteDomain_pos_example` | R4 definition example | Quot.sound, propext | `d302204dbf8c2d71f7520cfab770ffda9458fde18c5a0e3655978280cacd2162` | `6eb3a2c0aac97f2fc1e991292e7b65012ffbea3d20d1ea733aaae77038ff9276` (1) |
| `Toy.Witness.isUnrestricted_implies_closedUnderPointPatches` | R2 supporting lemma | Classical.choice, Quot.sound, propext | `caf3325946562535f39099f17e176190669eb64637d88a864c9e10220577e313` | `172b8a1d79d072ff7c8bd7697b5d1fb971b00ffaa412dd1a7b313bca9bf5b8b5` (4) |
| `Toy.Witness.isUnrestricted_neg_example` | R2 definition example | none | `662564a32d82a460a82cda83ecb73c1bec1ad56dfea0062ab5573a947fe0b75a` | `30afb9d698a92b5cb03dddf3bc925df86add24ff21a904b2ec49e57353bcdf27` (3) |
| `Toy.Witness.isUnrestricted_pos_example` | R2 definition example | none | `ffa7a304e355b33e7cf22baae14856910a1b4682a676ae5d84b40bfe5e67c4c2` | `b8346fece2f21ba5cadf23031bf496e3aa7bba3bbe9c67c695212b99c34b6362` (2) |
| `Toy.Witness.length_labelSample` | R1 supporting lemma | propext | `9a00f1db0083e33da4bdd47989d1211ee6557f4c6900792ed06ff334acc34676` | `35f49745ee45e4b78e6009970e27f47ed22eacf0c9284d2eef4b4e37b57b1c84` (1) |
| `Toy.Witness.map_fst_labelSample` | R1 supporting lemma | none | `701e8076efe5f5e66d95aea73471746a62503dc21f5e4eded93e6eea3329bae6` | `35f49745ee45e4b78e6009970e27f47ed22eacf0c9284d2eef4b4e37b57b1c84` (1) |
| `Toy.Witness.mem_wordsOfLength_iff` | R10 supporting lemma | Quot.sound, propext | `4f93ebbad53291daa886ed435c5b74495e72baf40c38a783748435bbf1f70061` | `07f3c75b7357bee7b8114ecb823311e4fd45be4eccbb0dff429426eaba955bb3` (4) |
| `Toy.Witness.mem_wordsUpTo_iff` | R10 supporting lemma | Classical.choice, Quot.sound, propext | `a7c19fd3c2b42a06ed90195f7e2f39d50db4b62a64c07be46a816e45787c794f` | `6ccbdf8674d6b2b2206b8797835e07f049ce20d6d50b7c71d6970635123f35ce` (6) |
| `Toy.Witness.monotoneConjNegExamples_length` | R5 supporting lemma | propext | `3a70ce109050ec42870d59646dce42e8ff8627b3f3e81cc0c1c338002bc98309` | `4189e37e6e255bdc6ff39107ce123ccf40210bf353e2f6a801a782292ef66a15` (4) |
| `Toy.Witness.monotoneConjTeachingSet_length` | R5 supporting lemma | Quot.sound, propext | `2b3f9890aeb4f787e7ae7ad9ddc80cbccd87fa3b51058c5ebd852d90913d558d` | `527c8bfd615265165bce765484cc4e36de88d207b37c70a372741a5f9915b7ea` (5) |
| `Toy.Witness.monotoneConjTeachingSet_nodup` | R5 supporting lemma | Quot.sound, propext | `0c06e170c17dd4c74abc6b234bf7b08b877ebd10f4ea0ac4e49f20ef75b6ae1d` | `527c8bfd615265165bce765484cc4e36de88d207b37c70a372741a5f9915b7ea` (5) |
| `Toy.Witness.monotoneConjunctions_neg_example_const_false` | R5 definition example | Quot.sound, propext | `abc53c93e068d30f5da8c417f8c33776ff2e82311d1f250ccf485096ee4fbbb2` | `bb265572962e8fef5e598614e1228ce6c675a492c03e2adb13edc10cb1c13325` (4) |
| `Toy.Witness.monotoneConjunctions_neg_example_or` | R5 definition example | Quot.sound, propext | `b51665dbbdd1635db1b93f27dcfe574246fb40b7da3ae2774e2efc285c08cf38` | `bb265572962e8fef5e598614e1228ce6c675a492c03e2adb13edc10cb1c13325` (4) |
| `Toy.Witness.monotoneConjunctions_pos_example` | R5 definition example | Quot.sound, propext | `3d37076a71cfd0e1c682c0dd6920fa55013e47d3ba8ac88b9c4ee994c4a3e786` | `bb265572962e8fef5e598614e1228ce6c675a492c03e2adb13edc10cb1c13325` (4) |
| `Toy.Witness.monotone_conj_m2_all_teaches` | R5 definition example | Quot.sound, propext | `db60b319b38498d9052763cd7ae24a68ca6c030f6e0f68f1c1cb4a67cec39ec0` | `1790863208f78245720bffc18941e78ca452026a44fe12fe70783e73ad47abcf` (11) |
| `Toy.Witness.monotone_conj_m2_r0_exact` | R5 supporting lemma | Quot.sound, propext | `0b48ad1435a08acefbc1fc3b07938ae3d1c7841df2cdc3d41baa157b838938cd` | `ee1c0a9087d1c1658cff69e44d902c13485b2964c0ea23fac4f3febf0f0b0c2f` (12) |
| `Toy.Witness.monotone_conj_m2_r1_exact` | R5 supporting lemma | Classical.choice, Quot.sound, propext | `13885e1dc0518b7cb0cdcfed8cf5aff5aebdac10c9c162262238780105079f76` | `ee1c0a9087d1c1658cff69e44d902c13485b2964c0ea23fac4f3febf0f0b0c2f` (12) |
| `Toy.Witness.monotone_conj_m2_r2_exact` | R5 supporting lemma | Classical.choice, Quot.sound, propext | `b9dddba3407e57e35f5fd7d15325c39550ff7d5a4e1253d01b4e71b51a42747b` | `ee1c0a9087d1c1658cff69e44d902c13485b2964c0ea23fac4f3febf0f0b0c2f` (12) |
| `Toy.Witness.monotone_conj_teaching_set_exact` | R5 result | Classical.choice, Quot.sound, propext | `7f4c95bb0ab7a576cfed0f4dce522aa92244aff7fe8bc4b929d0ed346a5fa7c2` | `ee1c0a9087d1c1658cff69e44d902c13485b2964c0ea23fac4f3febf0f0b0c2f` (12) |
| `Toy.Witness.monotone_conj_teaching_set_exact_nonvacuity` | R5 non-vacuity | Classical.choice, Quot.sound, propext | `13885e1dc0518b7cb0cdcfed8cf5aff5aebdac10c9c162262238780105079f76` | `ee1c0a9087d1c1658cff69e44d902c13485b2964c0ea23fac4f3febf0f0b0c2f` (12) |
| `Toy.Witness.monotone_conjunctions_m0_td` | R6 supporting lemma | Quot.sound | `70ef672bf0c0e7fb3c453bdf928f2a2fc547a583314a4c0bb97c20670f409be2` | `95377a9bf1d9770a937e536764d79aa5037761450353475b91563ff7c306b209` (8) |
| `Toy.Witness.monotone_conjunctions_teaching_dimension` | R6 result | Classical.choice, Quot.sound, propext | `f13ebd5a81718c2eb590c2c2fd188cd3a2c07580fe8ad76652651184aaafa52c` | `95377a9bf1d9770a937e536764d79aa5037761450353475b91563ff7c306b209` (8) |
| `Toy.Witness.monotone_conjunctions_teaching_dimension_nonvacuity` | R6 non-vacuity | Classical.choice, Quot.sound, propext | `2e89de89ba6f7d1b2eff5f4d4b7d3183a8632efee854c4a415603c79012f1aa6` | `95377a9bf1d9770a937e536764d79aa5037761450353475b91563ff7c306b209` (8) |
| `Toy.Witness.moore_bound_sharp` | R9 result | Quot.sound, propext | `5ce8f41119bdf90da6e1f463a5c3b7e6470fc81862936d48a2920426e52af0b5` | `d448cf35dc394f8c31337585012773c186ec38321c78b8491768a3366f59a432` (10) |
| `Toy.Witness.moore_bound_sharp_ce_small_n` | R9 counterexample (`hn`) | Quot.sound, propext | `3c55df49c8c0907ed8aafc965918efa1feefa006f8959662bfde81559b067e14` | `d448cf35dc394f8c31337585012773c186ec38321c78b8491768a3366f59a432` (10) |
| `Toy.Witness.moore_bound_sharp_nonvacuity` | R9 non-vacuity | none | `83c63b85bfd7fc34e785e31a2c73d94851f7686031f49a7859461a152ac84266` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Witness.moore_state_equiv_iff_agree_lt_n` | R7 companion | Classical.choice, Quot.sound, propext | `981ec341277233ee67585b1ddf66a90f293d74c9ff7124df7fec9728c94ec685` | `581834fe34eceef90dda3c64d62bec2e5333bb4b811abd7718ce7b6f1aaabc3f` (9) |
| `Toy.Witness.moore_state_equiv_iff_agree_up_to` | R7 result | Classical.choice, Quot.sound, propext | `52fbc7258d69a9c624fd97b7268572318164411ecdc965ac58654a3468e77b7c` | `27edbfc54d95e1f837a340b356e1a9075d2aa6ec717de46051dd3d5d1968f5e8` (10) |
| `Toy.Witness.moore_state_equiv_iff_agree_up_to_nonvacuity` | R7 non-vacuity | Quot.sound | `42258bc597c1c754148427d4a403b12ecce0542ffee57d359d06e37d2ad2023d` | `23ff15ffa3513e2417b35ddb2843b37252d0625c83f13fee1abe06bfb58c08a8` (11) |
| `Toy.Witness.moore_two_machine_bound_sharp` | R12 result | Quot.sound, propext | `8a6e7b8a88290af0ae63cc77f0363d83c5e6ca31812999404e6bbf88f17ec14d` | `f20615ff370c151d65299f01847a1353f373005c54f1a9f481b14bbadf4f1d0f` (16) |
| `Toy.Witness.moore_two_machine_bound_sharp_nonvacuity` | R12 non-vacuity | Quot.sound, propext | `3e4d759b76088ee6fdd23644fac1ee8453b7b500a8510f0230be26d5e3986042` | `f20615ff370c151d65299f01847a1353f373005c54f1a9f481b14bbadf4f1d0f` (16) |
| `Toy.Witness.moore_two_machine_equiv_iff_agree_up_to` | R8 result | Classical.choice, Quot.sound, propext | `8724e35163434f456df13000e6fb1a048d1da72c60fa59ffc5f730600a1137ac` | `f55a24756f8bfc34aaf6e84cdb4055db9c2f1fbac5f1d209c15c30fd70fce132` (13) |
| `Toy.Witness.moore_two_machine_equiv_iff_agree_up_to_nonvacuity` | R8 non-vacuity | Quot.sound, propext | `484e3cae1a7aa437b387615e2f5839a1566388537a47e0051010c46b3b978fe0` | `b7dca28481947b81c950f9d7343989b41438935800fb2ebe063e0869f842bdcd` (15) |
| `Toy.Witness.passed_suite_certifies_iff_ce_not_in_H` | R17 counterexample (`hh`) | propext | `8eccf8b2eec6b82a8a9f5069f2653556f35ef1e4157976a6870cbacf7cff9702` | `f40d14847c9b8ab095c98ee40b18dee5cf964fc65c27a1be576b66df885963ac` (4) |
| `Toy.Witness.passed_suite_certifies_iff_ce_not_unique` | R17 counterexample (`huniq`) | propext | `cb7bee945cff4a7ddccbcc751d89cb1192bf7ade00acca0469902a912c8da16b` | `f40d14847c9b8ab095c98ee40b18dee5cf964fc65c27a1be576b66df885963ac` (4) |
| `Toy.Witness.passed_suite_certifies_iff_passingInClass` | R17 result | none | `eb142d0c568e354b0cfe19e2e65294a2f61ca0730ce1bca7e3989f4ad9ec482b` | `f40d14847c9b8ab095c98ee40b18dee5cf964fc65c27a1be576b66df885963ac` (4) |
| `Toy.Witness.passed_suite_certifies_iff_passingInClass_nonvacuity` | R17 non-vacuity | propext | `41e64bfea10778803843737b9aa290286cea96c18337cf0b5e7f73ed911cde2c` | `29f70a5dc9a71d21038f1675af34d4394b5df65cfe9c77b969f3704618386237` (4) |
| `Toy.Witness.passed_teaching_suite_ce_not_subclass` | R17 companion | Classical.choice, Quot.sound, propext | `6ea8a2e0268a91f6caf7d87a5590298270a8c0de3995a18a3e50549ba742239f` | `51f51d24b7c22db0e48731087da5e60d037fa10361ef4c4687ce1968bad724c2` (12) |
| `Toy.Witness.passed_teaching_suite_certifies_iff_passingInClass` | R17 companion | none | `8b3d0342386ff5674de6ea5e861c080a6ebdfff8881c4aa3bb072a6a4c0984d5` | `f7158109033459c7d159766ba668c2436e4eb95f23312c812ddceaa6e51897a4` (5) |
| `Toy.Witness.passed_teaching_suite_certifies_subclass` | R17 companion | none | `be6c9fddfd50ee9a4e4172d1cee7eb53af4fc2e0d5def202004ab0f7eb9f5b77` | `da04a4489ee9a34694b8d18dff04ae59730dcf8c896628ab635b2fc5d8b768c1` (5) |
| `Toy.Witness.passed_teaching_suite_without_class_bound_escapes_class` | R18 companion | Classical.choice, Quot.sound, propext | `fe0646c9a0c0f2b982ef0a7bbfd003c610e4f77b2e3e096323aada9f3180b2ae` | `d5b3e102c53c29a9e30bb1ca3aae7a0dbe8a0aeaa537e55a9e7fd49f00548a2d` (6) |
| `Toy.Witness.passingInClass_neg_example` | R17 definition example | propext | `f8d51e73a68af5a5edfeadc786a66ce11d7c45178cd9222baacb6d78d567f4da` | `0c005b01a5bdefd94976581d8d4d0526b996132371f6517e839f724d4bc06b14` (4) |
| `Toy.Witness.passingInClass_pos_example` | R17 definition example | propext | `b74a722bba48e0d76dc3d0fa7a3e1c19e58a2f30c5af2781f05509e19e51375b` | `8e6201a0cd49d620124f216b4306b8a640902c2851fcacb6ec94b99985ac38f3` (5) |
| `Toy.Witness.patchAt_of_ne` | R2 supporting lemma | Classical.choice, Quot.sound, propext | `37f15120ae2a9f7340a70adab3f343be125dafe4f4c4c854ef273481c9ed8fec` | `540dd6c83a6c13f98abb08c8254786d75775aa0803560129f177933ed01fef64` (1) |
| `Toy.Witness.patchAt_self` | R2 supporting lemma | Classical.choice, Quot.sound, propext | `1df3d1aeea19af942f18fda80e296443cda272360f57922d2d3a1f464b49c831` | `540dd6c83a6c13f98abb08c8254786d75775aa0803560129f177933ed01fef64` (1) |
| `Toy.Witness.patchClosed_hasUntestedInput_ce_exhaustive` | R3 counterexample (`hUntested`) | Classical.choice, Quot.sound, propext | `509f7a40d98f6738516b3fce30da4f9e3cc35e558d29720c420648a8c1982050` | `3c53e4b8eb50bf28d72b754215e0a1ee5734ce2770b4f62add3513041c33377c` (8) |
| `Toy.Witness.patchClosed_hasUntestedInput_ce_not_patchClosed` | R3 counterexample (`hClosed`) | Classical.choice, Quot.sound, propext | `89b491de5c47f4abd693893685469056b6dfb70b6255e920415df4161ff9f727` | `6b0bc23a9d30c328fda5d91cee4a34ba3b2b401f3ce57c06e61a2c3db2b593ab` (9) |
| `Toy.Witness.patchClosed_hasUntestedInput_ce_trivial_codomain` | R3 counterexample (`hTwo`) | Classical.choice, Quot.sound, propext | `993de0f6e6ae988a8a08f851babdffbcf9934e166a798eea82db4589d883ecee` | `3c53e4b8eb50bf28d72b754215e0a1ee5734ce2770b4f62add3513041c33377c` (8) |
| `Toy.Witness.patchClosed_hasUntestedInput_no_teaching` | R3 result | Classical.choice, Quot.sound, propext | `296425a8045fad46c9d7c458f41397f1b7d104408166d42470732ad5bc119135` | `3c53e4b8eb50bf28d72b754215e0a1ee5734ce2770b4f62add3513041c33377c` (8) |
| `Toy.Witness.patchClosed_hasUntestedInput_no_teaching_nonvacuity` | R3 non-vacuity | Classical.choice, Quot.sound, propext | `1a41ee1df1229be4340a29ddc2cec69215958b19c16bcf68aa196eaf60d5cb12` | `ff305e14707e87709454c5d4fbf677b48988c8c9c7f10eeee296dda28174c97a` (5) |
| `Toy.Witness.patchClosed_infinite_ce_finite_domain` | R4 counterexample (`hInf`) | Classical.choice, Quot.sound, propext | `076315320cfd7feec20e07918184c8059c098bad18b230c92b12291d3df19fd5` | `9f75dc02d9801ad8fabd49a3527e47ba04331f68d6709c1116f34e833ff38fe9` (8) |
| `Toy.Witness.patchClosed_infinite_ce_not_patchClosed` | R4 counterexample (`hClosed`) | Classical.choice, Quot.sound, propext | `6c6939be45d4f8fa748e2a5d64ace18201ef85604cd6cb9b57be51a8ab1a36de` | `9f75dc02d9801ad8fabd49a3527e47ba04331f68d6709c1116f34e833ff38fe9` (8) |
| `Toy.Witness.patchClosed_infinite_ce_trivial_codomain` | R4 counterexample (`hTwo`) | Classical.choice, Quot.sound, propext | `e5c79efdeb0fc5e9eb4c7775a72c6dfc118cfeac5055e2bb745c9a37ee93e8f6` | `9f75dc02d9801ad8fabd49a3527e47ba04331f68d6709c1116f34e833ff38fe9` (8) |
| `Toy.Witness.patchClosed_infinite_no_finite_teaching_set` | R4 result | Classical.choice, Quot.sound, propext | `6e4aeebdf219d805c4a74d944c02df5dadb90042c2b68dd38055628a0fe29034` | `9f75dc02d9801ad8fabd49a3527e47ba04331f68d6709c1116f34e833ff38fe9` (8) |
| `Toy.Witness.patchClosed_infinite_no_finite_teaching_set_nonvacuity` | R4 non-vacuity | Classical.choice, Quot.sound, propext | `9b1179ccc0b59c0b13a9023b2114d072a8036230a4f2ee7342696c2010c0f5a4` | `702a8c51e59efcb4751d105754f435fbd019be7273a6f7d65880a0c75dd9c875` (6) |
| `Toy.Witness.patchClosed_untested_input_ce_inconsistent` | R2 counterexample (`hcon`) | Classical.choice, Quot.sound, propext | `2afaf374ce05886517558d3e7fe08adb2a6ce060fbf790d2ee7ddfbbee84e3b7` | `e16ed5c4f6b8bfd9c5db2ea6912037635b0d92833352c43bd9edd06ec3a68ee3` (6) |
| `Toy.Witness.patchClosed_untested_input_ce_not_in_H` | R2 counterexample (`hh`) | Classical.choice, Quot.sound, propext | `040abb6ec8308cc65c6e406264ea24c9294d2a21bb1085768737556baeab2918` | `4ac974d39ed4151babb15b4d16cbb17feda0edb8633a386e79c4265c1b4bcffd` (7) |
| `Toy.Witness.patchClosed_untested_input_ce_not_patchClosed` | R2 counterexample (`hClosed`) | Classical.choice, Quot.sound, propext | `a0e46f6dcca7b6015512ed433525b04af34980b60986428236397c011d6000a1` | `274632d2cd4e2cf503a730ffb03d4df65dcac0235097ffca99ebb89b96ff2b39` (7) |
| `Toy.Witness.patchClosed_untested_input_ce_same_val` | R2 counterexample (`hDiff`) | Classical.choice, Quot.sound, propext | `42fadf206dd9b1a84650386affb2ada0154555b42d526604125711d008aa1bc6` | `e16ed5c4f6b8bfd9c5db2ea6912037635b0d92833352c43bd9edd06ec3a68ee3` (6) |
| `Toy.Witness.patchClosed_untested_input_ce_tested` | R2 counterexample (`hUntested`) | Classical.choice, Quot.sound, propext | `ad87bc0c45e90df6b6a8e3a122a142ae9943405f14a9bd269e24c4b87e7d1105` | `e16ed5c4f6b8bfd9c5db2ea6912037635b0d92833352c43bd9edd06ec3a68ee3` (6) |
| `Toy.Witness.patchClosed_untested_input_patch_witness` | R2 result | Classical.choice, Quot.sound, propext | `017ef0445bbc847b0c26c24133fc3aadd853fc1cb85f68b1b208279b01b1ee9d` | `e16ed5c4f6b8bfd9c5db2ea6912037635b0d92833352c43bd9edd06ec3a68ee3` (6) |
| `Toy.Witness.patchClosed_untested_input_patch_witness_nonvacuity` | R2 non-vacuity | Classical.choice, Quot.sound, propext | `b09b20b9447ec5e0342d51e6956cffa7326d826e620215edc2dc4bb614106865` | `198dbb45dd7926d1c20e75702f4cdf8129882f0850ecba23697b3e3eab677749` (5) |
| `Toy.Witness.patchClosed_untested_input_positive_control_monotone_conj` | R2 positive control; R3 positive control | Classical.choice, Quot.sound, propext | `57d1e119097f7d344cc650fe20a3a76c0b56fd44021b4be761f137c3c1d3ce2a` | `cc4594d78340fd3a4bbe7836943acad489474dcef79bdae982436e63931c6721` (14) |
| `Toy.Witness.relevantCount_le` | R5 supporting lemma | propext | `7cb33d335bd889c153ac213cf6f4a81eb7fed3ef613da6b5d0393750c9ccff22` | `25aa85516a4e712376555b9eec850a1afad534a59561c66a41295b4663448603` (1) |
| `Toy.Witness.spliceOutside_consistent` | R18 supporting lemma | Classical.choice, Quot.sound, propext | `775d0f6105bc0123a515c1a4e2347154d93751d40f0928c358e09070668fba7c` | `38acf147a66e1aeb53f61d467930dea012f9c7a7fc27b4abf224bd6bc8906aef` (3) |
| `Toy.Witness.spliceOutside_of_mem` | R18 supporting lemma | Classical.choice, Quot.sound, propext | `78592299515b2d07d4b65701c4b65c8a299ec6fd9d1d86d315c85aacff78fccb` | `bf7429eb311a20c2c15c3e1e1f3132d244b0824725b40ee8b9bdb98c3abab88a` (2) |
| `Toy.Witness.spliceOutside_of_not_mem` | R18 supporting lemma | Classical.choice, Quot.sound, propext | `2852160673d6a2ba156f916e04ba4e867ed5c6e6084bb3bb27c763774643daa8` | `bf7429eb311a20c2c15c3e1e1f3132d244b0824725b40ee8b9bdb98c3abab88a` (2) |
| `Toy.Witness.splice_consistent_escapes_class_ce_agrees` | R18 counterexample (`hDiff`) | Classical.choice, Quot.sound, propext | `5a9d85899be31696fc7467b3e7b694bedb31584186bd5158308acd0c58bb220b` | `d5dc186a95c48da8a2b4b0f5be70942032624ad1094cf850c66991b314b1f491` (6) |
| `Toy.Witness.splice_consistent_escapes_class_ce_inconsistent` | R18 counterexample (`hcon`) | Classical.choice, Quot.sound, propext | `42d1895ad9e0225cb0fcfef15e4e377f3cb9bb0ea1390e38a1fc6e7257209fab` | `03eb7858b93b8417ae75869ec2241838661e22e8dad57e34828ed879368906e5` (5) |
| `Toy.Witness.splice_consistent_escapes_class_ce_not_unique` | R18 counterexample (`huniq`) | Classical.choice, Quot.sound, propext | `66d3a6b9a14aef32aedbda9be53c7e6cc8fa3f8f995deee00426912f66131424` | `03eb7858b93b8417ae75869ec2241838661e22e8dad57e34828ed879368906e5` (5) |
| `Toy.Witness.splice_consistent_escapes_class_ce_tested` | R18 counterexample (`hUntested`) | Classical.choice, Quot.sound, propext | `f5b724eead238dbe51fe669f045c78b841b220ac94c40adf3fc267799f8fb9c5` | `d5dc186a95c48da8a2b4b0f5be70942032624ad1094cf850c66991b314b1f491` (6) |
| `Toy.Witness.splice_consistent_escapes_class_of_unique` | R18 result | Classical.choice, Quot.sound, propext | `6d06a5fe63497552e3253799588e3d06c43461a5b9827fe0bdab3e3a9fc387d4` | `03eb7858b93b8417ae75869ec2241838661e22e8dad57e34828ed879368906e5` (5) |
| `Toy.Witness.splice_consistent_escapes_class_of_unique_nonvacuity` | R18 non-vacuity | propext | `2a2534e05ec1e8d7cb14aa691215de8c29817644e63fb1c9cacfdc90524ea23f` | `29f70a5dc9a71d21038f1675af34d4394b5df65cfe9c77b969f3704618386237` (4) |
| `Toy.Witness.stateEquiv_neg_example` | R7 definition example | none | `c93d68328f3d10d589c0d13dc6864e8a4b8f9cb9b76199bbf345d829e88d32f7` | `581834fe34eceef90dda3c64d62bec2e5333bb4b811abd7718ce7b6f1aaabc3f` (9) |
| `Toy.Witness.stateEquiv_pos_example` | R7 definition example | Quot.sound, propext | `e2ae2e022b48df3b7e504a0c01bcb025202827599629c70c6e9363fafb42d9ed` | `581834fe34eceef90dda3c64d62bec2e5333bb4b811abd7718ce7b6f1aaabc3f` (9) |
| `Toy.Witness.subClass_implies_passingInClass` | R17 supporting lemma | none | `89db7e5dfb1b7da01ec491816b6d696da9665243d7a3a1d5b1073f0f7620f585` | `db640dd599ed05c0e60a26c466a1d005e6f2fc7906fd17a0785535732fe5a5c6` (4) |
| `Toy.Witness.subClass_neg_example` | R17 definition example | none | `321ba55a6294c3a6e44fe60bea30eef95d881556e58e4a4cf465a2932150cf86` | `5e5a3038bee2a5ebb990831228496abc01d86575456ece24fc857646916c89ba` (3) |
| `Toy.Witness.subClass_pos_example` | R17 definition example | none | `1d57178e08fcda1cb707ddf9028675ebb21a70b69058b7d88de9e79d09679842` | `5e5a3038bee2a5ebb990831228496abc01d86575456ece24fc857646916c89ba` (3) |
| `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent` | R1 result | Classical.choice, Quot.sound, propext | `27a62cb315b5e1de6feff63d762af2dfdfb19784959d4f51954e03fa57b8686a` | `2bd413c7f3711e34d53ae2f2c25b39ddabbebb89248dfdba6b309508acd4ddcf` (6) |
| `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_inconsistent` | R1 counterexample (`hcon`) | propext | `1777e1495c794aa3d8852bff0747ce5cae3a910945633424739f9c7d962d752e` | `f3f6ad6ba4d29576c9188d8f2a530f1ec8b70d791a5672b83e69a1a69d7da142` (7) |
| `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_not_in_H` | R1 counterexample (`hh`) | propext | `bba203e538c86fe25302002f826c94849cc515159ac5467031e40b461be0666e` | `2bd413c7f3711e34d53ae2f2c25b39ddabbebb89248dfdba6b309508acd4ddcf` (6) |
| `Toy.Witness.teaches_iff_hits_disagreement_sets_of_mem_of_consistent_nonvacuity` | R1 non-vacuity | propext | `e100f9e5bf45cbe61de7669d5628b9851694ed7ded2793c03e7e3fcf5f3ab5ee` | `2b1621fe7c850b2c6e298bf41e9f284aa847b7fd2626ddd92c9c3cd8038b8cb9` (3) |
| `Toy.Witness.teaches_neg_example` | R1 definition example | propext | `407764b7d0980b1ba9db39e44bcccbb66bd955e42fbdff68e7dfeb6533b4fb52` | `8e0bdd6d5c4ebdd3af69653b37d92d774d6b51e7de4b5e9caf48db506c84dd17` (4) |
| `Toy.Witness.teaches_pos_example` | R1 definition example | propext | `5e4ad1d0d547e4520e4d60f0f6e810264df4b3b91c566c090e117625db52039a` | `b831e6fb6642d3309ce3a077b637267faa8b88337919d95e4cfd134502a187d3` (5) |
| `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_finite_alphabet` | R14 counterexample (`hInf`) | Classical.choice, Quot.sound, propext | `2adcdd260445dfe4d657ffeb584db934960d85b34532010a7ba0b4a5505808bb` | `41acbbf3e762dc393ee2cf3457e6a7e9590193e6be97a7f595ba6a75348e5d93` (20) |
| `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_one_state` | R14 counterexample (`hk`) | Quot.sound, propext | `6277fedc0056cd6fcb49abfcda2ec006ed071f3f21b5d16e1d5ba569e5d87b3c` | `41acbbf3e762dc393ee2cf3457e6a7e9590193e6be97a7f595ba6a75348e5d93` (20) |
| `Toy.Witness.two_le_state_bound_infinite_alphabet_ce_trivial_output` | R14 counterexample (`hTwo`) | Quot.sound, propext | `947ea7e422c0b2664f5fe8c92a57c7a42184460aec77ec6ccd1a7e99c3e9348e` | `41acbbf3e762dc393ee2cf3457e6a7e9590193e6be97a7f595ba6a75348e5d93` (20) |
| `Toy.Witness.two_le_state_bound_infinite_alphabet_no_finite_teaching_set` | R14 result | Classical.choice, Quot.sound, propext | `92d15824a70f68e3dbf766e960ec927185e9325de6391e4e22a1017309100bce` | `41acbbf3e762dc393ee2cf3457e6a7e9590193e6be97a7f595ba6a75348e5d93` (20) |
| `Toy.Witness.two_le_state_bound_infinite_alphabet_no_finite_teaching_set_nonvacuity` | R14 non-vacuity | Quot.sound, propext | `9bd246e795146420870dd58a3cc64f262dac62e68d8bbd8167b6bd74c21c5503` | `544fb3579f21fb65ff6b6c68f85aeaefb5593e72aca2b7cef0a00521bf0d192b` (2) |
| `Toy.Witness.two_state_moore_length_lt_k_insufficient` | R13 companion | Classical.choice, Quot.sound, propext | `213c6c525537227b3092e088162499eb52c6ad0b929ba05c3f4ab5053ab94801` | `fbf2c68f9918aa33ddca92e637bb5e93461391aad8fd663325737c500711e8e5` (28) |
| `Toy.Witness.unbounded_moore_ce_empty_alphabet` | R16 counterexample (`hI`) | Quot.sound, propext | `c6371b4ea6a1562c6c9dca04dce4817d83868c0953f167cb67ebfd7ce77d95ed` | `c3f5a8f8e1572af48a5fcfb89e3424b9c1eaaa06cd551115916f554c953cb156` (19) |
| `Toy.Witness.unbounded_moore_ce_trivial_output` | R16 counterexample (`hTwo`) | Quot.sound, propext | `94e5c1cee259001fb4aa2f3f30ba198640d89afee8725cc4c11e34f951b5dcaa` | `c3f5a8f8e1572af48a5fcfb89e3424b9c1eaaa06cd551115916f554c953cb156` (19) |
| `Toy.Witness.unbounded_moore_no_finite_teaching_set` | R16 result | Classical.choice, Quot.sound, propext | `085a42e8348b78a6218f77c7e6d4589a62ee727cb6516edea7793fb8bb8aca0f` | `c3f5a8f8e1572af48a5fcfb89e3424b9c1eaaa06cd551115916f554c953cb156` (19) |
| `Toy.Witness.unbounded_moore_no_finite_teaching_set_nonvacuity` | R16 non-vacuity | none | `fe8e9aaca57d141ec7f00896fb5291e08efb82965f3ff491c44d46ce5f3e928c` | `cbdbf1ee9c2bfeccf050a23cef1aea0b704822df9ff8ce28d3fc6c2b9d772571` (1) |
| `Toy.Witness.uniqueConsistent_neg_example` | R1 definition example | propext | `98af83a8d9e5672605f54d5b3f1c7b4247897a04f21fd96b372d1119acf2aaf8` | `fcb91957c72ab19d53c8cf509dd6ad4285fa7c1b56cbeb510e6ee0d01b8502b3` (3) |
| `Toy.Witness.uniqueConsistent_pos_example` | R1 definition example | propext | `3cdf18a4abc27a253e926002d00efb1afea4fe220b093460b69e9b393b5e1eb3` | `29f70a5dc9a71d21038f1675af34d4394b5df65cfe9c77b969f3704618386237` (4) |
| `Toy.Witness.unrestricted_hasUntestedInput_no_teaching` | R3 companion | Classical.choice, Quot.sound, propext | `4c918d3112a37f509c08bbbe6ebb28ecc513fe195fff527895913bb957384dd3` | `5e1c57bd55873826291ca9d93abe97d79c693ebe398f8b3acb13be478cc88c26` (7) |
| `Toy.Witness.unrestricted_infinite_no_finite_teaching_set` | R4 companion | Classical.choice, Quot.sound, propext | `81341a4d2deeaceb295de73905afb161a023dbe0bd052414f59ab067344019f9` | `c25140e541e9775d91ff3996ef7b1483fa68efa76138598acc596bec5dee92df` (7) |
| `Toy.Witness.unrestricted_untested_input_patch_witness` | R2 companion | Classical.choice, Quot.sound, propext | `c940bcb8355f93f91fdfda32fd9b43476c1f0be4fd14057954d1d97af2aee3d2` | `6d62b40bdc0f7465da0331ead50b1e1e93aa10158ef4ec449bac2507d8c0830e` (6) |

**Primary sources.** Bibliographic metadata for DOI-identified sources was checked against Crossref records and JMLR and AFP pages on 2026-11-20. Exact consultation scope per source:

- **[Ang87]** D. Angluin. *Learning regular sets from queries and counterexamples*. Information and Computation 75(2):87–106, 1987. DOI `10.1016/0890-5401(87)90052-6`. *(Context reference, not a subject. Metadata matched Crossref; the L\* membership-plus-equivalence-query result is stated from secondary descriptions; full text not consulted.)*
- **[Ang88]** D. Angluin. *Queries and concept learning*. Machine Learning 2(4):319–342, 1988. DOI `10.1007/BF00116828`. *(Context reference, not a subject. Metadata matched Crossref; full text not consulted.)*
- **[ABST95]** M. Anthony, G. Brightwell, J. Shawe-Taylor. *On specifying Boolean functions by labelled examples*. Discrete Applied Mathematics 61(1):1–25, 1995. DOI `10.1016/0166-218X(94)00007-Z`. *(Metadata matched Crossref; COLT 1992 precursor summarized in Goldman and Kearns; full text not consulted.)*
- **[BA82]** T. A. Budd, D. Angluin. *Two notions of correctness and their relation to testing*. Acta Informatica 18(1):31–45, 1982. DOI `10.1007/BF00625279`. *(Metadata matched Crossref; abstract read; full text not consulted.)*
- **[Chow78]** T. S. Chow. *Testing Software Design Modeled by Finite-State Machines*. IEEE Transactions on Software Engineering SE-4(3):178–187, 1978. DOI `10.1109/TSE.1978.231496`. *(Metadata matched Crossref; full text not consulted.)*
- **[DFSZ14]** T. Doliwa, G. Fan, H. U. Simon, S. Zilles. *Recursive Teaching Dimension, VC-Dimension and Sample Compression*. Journal of Machine Learning Research 15(89):3107–3131, 2014. `https://jmlr.org/papers/v15/doliwa14a.html`. *(Full text read; Corollary 9(2) `RTD(Monotone Monomials) = 1` and singleton `TD = 0`.)*
- **[DEMCY10]** R. Dorofeeva, K. El-Fakih, S. Maag, A. R. Cavalli, N. Yevtushenko. *FSM-based conformance testing methods: A survey annotated with experimental evaluation*. Information and Software Technology 52(12):1286–1297, 2010. DOI `10.1016/j.infsof.2010.07.001`. *(Metadata matched Crossref; full text not consulted.)*
- **[Gold67]** E. M. Gold. *Language identification in the limit*. Information and Control 10(5):447–474, 1967. DOI `10.1016/S0019-9958(67)91165-5`. *(Context reference, not a subject. Metadata matched Crossref; full text not consulted.)*
- **[GK95]** S. A. Goldman, M. J. Kearns. *On the Complexity of Teaching*. Journal of Computer and System Sciences 50(1):20–31, 1995. DOI `10.1006/jcss.1995.1003`. *(Metadata matched Crossref; full text read in technical report WUCS-92-28: Sec. 2, Sec. 5 set-cover equivalence, and Theorem 11 `min(r + 1, n)` for monotone monomials; JCSS theorem numbering not separately verified.)*
- **[GS94]** S. A. Goldman, R. H. Sloan. *The power of self-directed learning*. Machine Learning 14(3):271–294, 1994. DOI `10.1007/BF00993977`. *(Context reference, not a subject: cited only as one of the sources to which [DFSZ14] attributes Corollary 9(2). Title, venue, volume, pages, and DOI matched a bibliographic search on 2026-11-20; full text not consulted.)*
- **[LY96]** D. Lee, M. Yannakakis. *Principles and Methods of Testing Finite State Machines—A Survey*. Proceedings of the IEEE 84(8):1090–1123, 1996. DOI `10.1109/5.533956`. *(Metadata matched Crossref; full text not consulted.)*
- **[Moore56]** E. F. Moore. *Gedanken-Experiments on Sequential Machines*. In *Automata Studies* (Annals of Mathematics Studies 34), C. E. Shannon and J. McCarthy (eds.), Princeton University Press, pp. 129–153, 1956. DOI `10.1515/9781400882618-006`. *(Full text read via `https://www.jstor.org/stable/j.ctt1bgzb3s.8`: length convention p. 136, Theorem 2 & `(n, m, p)` remark p. 140, Theorem 6 p. 145 & `D_n` p. 146, Theorem 7 pp. 146–147 (symmetric form: two machines with a common state bound `n` and an experiment of length `2n − 1`; the asymmetric `n₁ + n₂ − 2` form used in R8 and R10 follows from the same direct-sum argument but is not stated there) & `D_n`/`E_n` p. 147.)*
- **[RS94]** K. Romanik, C. Smith. *Testing geometric objects*. Computational Geometry 4(3):157–176, 1994. DOI `10.1016/0925-7721(94)90005-1`. *(Metadata checked against Crossref; summarized in Goldman and Kearns; full text not consulted.)*
- **[Sach19]** R. Sachtleben. *Formalisation of an Adaptive State Counting Algorithm*. Archive of Formal Proofs, 16 Aug 2019. Release for Isabelle2026, 2026-10-26. `https://www.isa-afp.org/entries/Adaptive_State_Counting.html`. *(Entry page (abstract, session theory list, dependencies, release list) read on 2026-11-20, when the most recent listed release was the Isabelle2026 release of 2026-10-26; statements about the entry's content refer to that release. No archive hash recorded.)*
- **[Sach22]** R. Sachtleben. *Verified Complete Test Strategies for Finite State Machines*. Archive of Formal Proofs, 9 Aug 2022. Release for Isabelle2026, 2026-10-26. `https://www.isa-afp.org/entries/FSM_Tests.html`. *(Entry page (abstract, session theory list, dependencies, release list) read on 2026-11-20, when the most recent listed release was the Isabelle2026 release of 2026-10-26; statements about the entry's content refer to that release. No archive hash recorded.)*
- **[SM91]** A. Shinohara, S. Miyano. *Teachability in Computational Learning*. New Generation Computing 8(4):337–347, 1991. DOI `10.1007/BF03037091`. *(Metadata matched Crossref; full text not consulted.)*
- **[Vas73]** M. P. Vasilevskii. *Failure diagnosis of automata*. Cybernetics 9(4):653–665, 1973. DOI `10.1007/BF01068590`. *(SpringerLink publication date July 1973; full text not consulted.)*
- **[ZLHZ11]** S. Zilles, S. Lange, R. Holte, M. Zinkevich. *Models of Cooperative Teaching and Learning*. Journal of Machine Learning Research 12(11):349–384, 2011. `https://jmlr.org/papers/v12/zilles11a.html`. *(Context reference, not a subject: cited only as one of the sources to which [DFSZ14] attributes Corollary 9(2). JMLR record checked; full text not consulted.)*

Observation date: 2026-11-20 (build, axiom audit, hashes, and primary-source verification).

## Revalidation

Revalidation requires `elan` (to install and select the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`.

From the package root directory, run the bundled self-contained revalidation script:

```sh
python3 support/revalidate.py .
```

This script copies `lean/` to a temporary directory, runs `lake build`, verifies no Lean source contains `sorry`, `admit`, `native_decide`, or an `axiom` declaration, collects axioms via `Lean.collectAxioms` for every declaration under `Toy` (checking only subsets of `{propext, Classical.choice, Quot.sound}`), and recomputes the SHA-256 of each card-referenced declaration's type `repr` and sorted definition-closure text (types and non-theorem definition bodies of all reachable `Toy.*` constants), comparing every hash and `closure_size` against `audit/statements.json`. It prints `REVALIDATED` and exits with status `0` if every check passes.

To run the build and audit manually using only `lake`, `lean`, and `python3` (against the included standalone program `lean/RevalidationAudit.lean`, which sits outside the `Toy` library target in `lean/lakefile.toml`):

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/witness_audit.out
python3 - <<'PY'
import hashlib, json, re

raw = open("/tmp/witness_audit.out", encoding="utf-8").read()
m = re.search(r"REVALIDATION_AUDIT_JSON (\{.*\})", raw)
assert m, "missing REVALIDATION_AUDIT_JSON output"
audit = json.loads(m.group(1))

allowed = {"propext", "Classical.choice", "Quot.sound"}
bad_ax = [d["name"] for d in audit["decls"] if set(d["axioms"]) - allowed]
assert not bad_ax, f"unexpected axioms: {bad_ax}"

got_ax = {d["name"]: sorted(d["axioms"]) for d in audit["decls"]}
rec_ax = json.load(open("../audit/axioms.json", encoding="utf-8"))["declarations"]
assert got_ax == rec_ax, "axiom drift detected"

got_st = {
    s["name"]: {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
        "closure_size": len(s["closure"]),
    }
    for s in audit["stmts"]
}
rec_st = json.load(open("../audit/statements.json", encoding="utf-8"))["statements"]
drift = [k for k in set(got_st) | set(rec_st) if got_st.get(k) != rec_st.get(k)]
assert not drift, f"statement/closure hash drift: {drift}"
print(f"OK: {len(got_ax)} declarations audited; {len(got_st)} statement/closure hashes verified.")
PY
```

To spot-check a single theorem's axioms interactively from `lean/`:

```sh
printf 'import Toy\n#print axioms Toy.Witness.moore_state_equiv_iff_agree_up_to\n' > /tmp/SpotCheck.lean
lake env lean /tmp/SpotCheck.lean
```

On a Lean release other than `leanprover/lean4:v4.34.1`, `repr` formatting of internal expressions can differ even when mathematical statements are unchanged; in that case compare `#check` output against the Lean statements recorded in **Findings** instead of comparing `audit/statements.json` hashes.
