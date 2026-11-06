# Lean 4 Partial Definitions, Termination Checking, Weakest-Precondition Encodings, and Release Upgrade Boundaries

## Summary

Across Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), and Lean `v4.35.0` (`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), recursive and potentially diverging definitions in Lean 4 are governed by four distinct architectural mechanisms that must remain separated during verification and trusted-computing-base (TCB) auditing:

1. **Explicit `partial def` declarations split an opaque logical constant from recursive executable code**: `addAndCompilePartial` does not install a nonterminating recursive body as the logical value of the user-visible declaration. Instead, Lean synthesizes an arbitrary inhabitant of the result type via `mkInhabitantFor`, installs the user-visible constant as an `opaque` declaration, and separately compiles a `DefinitionSafety.partial` recursive companion named `<decl>._unsafe_rec`. Consequently, ordinary kernel weak-head normalization (`Kernel.whnf`) and definitional equality leave applications of a `partial def` stuck (`c3 =?= v1 := false`), while native execution and `native_decide` invoke `<decl>._unsafe_rec` across the compiled-execution trust boundary (`Lean.Meta.Native.nativeEqTrue`).
2. **Ordinary recursive `def`/`theorem` termination checking translates recursion into non-recursive kernel terms**: `Lean.Elab.addPreDefinitions` (`PreDefinition/Main.lean:288` in `v4.34.1`) partitions mutually dependent definitions into strongly connected call-graph cliques and dispatches safe recursive definitions either through **structural recursion** (`structuralRecursion` at `Structural/Main.lean:183` in `v4.34.1`, eliminating recursion via inductive `brecOn` recursors while using temporary local axioms under `withoutModifyingEnv`) or **well-founded recursion** (`wfRecursion` at `WF/Main.lean:23` in `v4.34.1`, translating recursive calls through `WellFounded.Nat.fix` or `WellFounded.fix` guarded by decrease proof obligations solved by `decreasing_by` or `decreasing_tactic` over explicit `termination_by` measures or `GuessLex` search bounded to 32 combinations). The kernel checks the resulting non-recursive term directly rather than trusting an elaborator termination bit.
3. **Weakest-precondition (`Std.WP`), order-theoretic `partial_fixpoint`, and Aeneas `ITree` encodings separate assertion transformers from operational adequacy**: In newer Lean releases (`v4.34.1` and `v4.35.0`), `Std.WP.Basic`, `Std.WP.Monad.Sound` (`LawfulWPMonadAttach`), and `Std.WP.Frame` provide generic assertion-transformer, verification-condition (`vcgen`), and spatial-framing interfaces, while `partial_fixpoint` constructs lattice-theoretic fixed points that expose unfolding equations as theorems. In `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`v4.35.0-rc4`), `Result` is an irreducible wrapper around an interaction tree (`ITree RustEffect`), where total correctness (`spec`, defined via least-fixed-point `DWP`) forbids divergence (`div ↦ False`) and partial correctness (`dspec`, defined via greatest-fixed-point `DWLP`) permits divergence (`div ↦ True`).
4. **Twelve-gate release upgrade boundary across `v4.30.0-rc2` → `v4.34.1`**: Upgrading Anneal's Lean toolchain from `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, paired with `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` and Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`) to `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, paired with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`) spans twelve independent verification gates documented in [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json): revision and archive digest pinning, Aeneas toolchain alignment, Lake manifest closure, logical trust/axiom boundary auditing, generated-Lean elaboration acceptance, tactic replay (`simp`/`simp_all`, `grind`, `omega`, `linter.unusedSimpArgs`), recursion/termination/partiality verification, `.olean`/`.ilean`/trace invalidation, LSP/RPC server protocol compatibility, host-native artifact verification, build/cache determinism, and end-to-end generated-code-to-proof composition.

## Applicability

This report applies to the exact pinned revisions recorded in `REPORT.json`, [`support/lean-wp-partiality-and-aeneas-integration/source-reading.json`](support/lean-wp-partiality-and-aeneas-integration/source-reading.json), [`support/lean-release-upgrade-checklist/source-map.json`](support/lean-release-upgrade-checklist/source-map.json), and [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json):

- **Lean 4 / Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (paired with Mathlib `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`).
- **Lean 4 / Lake `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`, paired with Mathlib `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`).
- **Lean 4 `v4.35.0` and reconnaissance comparison**: `leanprover/lean4` revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`) and `leanprover/lean4` revision `88539871b4133140b0d5e9beb4cd446bcc0d2f40` (used for interface comparison of `Std.WP` and `Lake.CLI.Check`).
- **Aeneas Lean backend revisions**:
  - `AeneasVerif/aeneas` revision `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`release: nightly-2026.06.03`, selecting `leanprover/lean4:v4.30.0-rc2`);
  - `AeneasVerif/aeneas` revision `21345f80fa212c596f6437378d7d57984fa2ea77` (`lean_toolchain: v4.35.0-rc4`, introducing the `ITree RustEffect`-backed `Result` and `DWP`/`DWLP` specification predicates).
- **Anneal workspace baseline**: `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

When connecting Lean's partial/total recursion and weakest-precondition semantics to Anneal's small-step operational refinement core without external branch dependencies, the self-contained semantic domain types are:

```lean
inductive StepResult (State : Type) where
  | step (next : State)
  | done
  | trapped
  | stuck

inductive Behavior (Obs : Type) where
  | terminates (trace : List Obs)
  | traps      (trace : List Obs)
  | diverges   (trace : Nat → Obs)
  | goesWrong

inductive ChoiceKind where
  | demonic
  | angelic
```

## Findings

### 1. Explicit `partial def` Elaboration: Opaque Logical Constant vs. `<decl>._unsafe_rec` Executable Companion (`v4.30.0-rc2` & `v4.34.1`)

Basis: **source** + checked-in **execution** output (`src/Lean/Elab/PreDefinition/Main.lean`, `MkInhabitant.lean`, `Basic.lean`, `src/Lean/Compiler/LCNF/ToDecl.lean`, `tests/elab/partial1.lean`, `tests/elab/kernel2.lean`, `tests/elab/reduce1.lean`).

#### 1.1 `partial def` Bypasses Ordinary Termination Elaborators
In both `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), the recursive-definition dispatcher `addPreDefinitions` in `Lean/Elab/PreDefinition/Main.lean` (362 lines in `v4.34.1`, `addPreDefinitions` at line 288) handles explicit `partial` declarations before structural or well-founded recursion. When a recursive clique contains a `partial` modifier, Lean requires each partial declaration to have a function type, invokes `addAndCompilePartial`, and reports any `termination_by` or `decreasing_by` hints as unused. Thus `partial def` is not "well-founded recursion with an omitted proof"; it selects a separate elaboration path in which neither structural recursors nor `WellFounded.fix` justify the source body.

#### 1.2 The User-Visible Logical Declaration Is `opaque` with an Arbitrary Inhabitant
`addAndCompilePartial` does not install the recursive source body as the logical value of the user-visible declaration. For each partial predefinition, it telescopes the declared type, calls `mkInhabitantFor` (`Lean/Elab/PreDefinition/MkInhabitant.lean`), changes the declaration kind to `opaque`, and passes that replacement value to `addNonRec`.
- `mkInhabitantFor` attempts to synthesize an arbitrary inhabitant of the result type using `Inhabited`, `Nonempty`, function parameters, and result-type unfolding. If nonemptiness cannot be established, elaboration fails because Lean refuses to introduce an uninhabited opaque constant that could falsify `False`.
- The logical value therefore has no semantic connection to the recursive body written in source.

#### 1.3 The Recursive Body Is Retained Under `<decl>._unsafe_rec` with `DefinitionSafety.partial`
After creating the `opaque` logical declarations, `addAndCompilePartial` invokes `addAndCompilePartialRec` (`Lean/Elab/PreDefinition/Basic.lean`), which rewrites each declaration in the clique to `Compiler.mkUnsafeRecName preDef.declName` (appending `._unsafe_rec`), replaces recursive calls with those renamed declarations, and installs the mutual definition with `DefinitionSafety.partial`.
- In `Lean/Declaration.lean`, `DefinitionSafety` has three states (`unsafe`, `safe`, `partial`), and `ConstantInfo.isPartial` holds only for `defnInfo` entries whose safety is `.partial` (namely the `._unsafe_rec` auxiliary). By contrast, `OpaqueVal` carries only `isUnsafe : Bool`. Across module boundaries (`Lean/AddDecl.lean`), the exported logical interface remains the `opaque` user-facing constant.
- Checked-in output in `tests/elab/partial1.lean.out.expected` confirms this split for a local recursive loop inside `partial def reverse`:
  - `opaque reverse.loop ...`
  - `partial def reverse.loop._unsafe_rec ... :=` followed by the recursive implementation.
- In `Lean/Compiler/LCNF/ToDecl.lean`, `getDeclInfo?` looks up `mkUnsafeRecName declName` first and falls back to the ordinary declaration only when no `._unsafe_rec` companion exists; `toDecl` normalizes `._unsafe_rec` names back to the user-facing name for code generation.

#### 1.4 Kernel WHNF vs. Compiled Execution (`native_decide`)
- **Kernel reduction**: In `tests/elab/kernel2.lean`, defining `partial def fact` and evaluating `c3 := fact 10` directly through `Kernel.whnf` and kernel definitional equality produces `c3 ==> fact ...` (stuck) and `c3 =?= v1 := false` (where `v1` is `3628800`). Because the user-facing declaration is `opaque` and its recursion equations live only in `fact._unsafe_rec`, no tactic can unfold a `partial def` via kernel conversion.
- **Native execution**: In `tests/elab/reduce1.lean`, `#guard` evaluations (`fact 100`) and `by native_decide` proofs succeed on `partial def fact` because `Lean.Meta.Native.nativeEqTrue` compiles and executes native code (which selects `fact._unsafe_rec`) and emits a fresh axiom asserting the observed Boolean result.
- **Error-recovery placeholder boundary**: When an ordinary recursive definition fails termination checking, `PreDefinition/Main.lean` may call `addAndCompilePartial` with `useSorry := true` for error recovery, installing a labeled synthetic `sorryAx` as the opaque value so downstream elaboration can continue. An external verifier must reject both logged elaboration errors and `sorryAx` dependencies.

---

### 2. Ordinary Termination Checking: Structural and Well-Founded Elaboration (`v4.30.0-rc2` & `v4.34.1`)

Basis: **source** + checked-in **execution** fixtures (`src/Lean/Elab/PreDefinition/Main.lean`, `TerminationHint.lean`, `TerminationMeasure.lean`, `Structural/Main.lean`, `Structural/FindRecArg.lean`, `WF/Main.lean`, `WF/Fix.lean`, `WF/Rel.lean`, `WF/GuessLex.lean`, `src/Init/WF.lean`, `tests/elab_fail/decreasing_by.lean`).

#### 2.1 Strongly Connected Call-Graph Clique Dispatch (`addPreDefinitions`)
In both `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, `PreDefinition/Main.lean:288`), `Lean.Elab.addPreDefinitions` cleans elaborated predefinitions, beta-reduces local-recursive applications, and partitions mutually dependent definitions into strongly connected components (cliques). Non-self-referential singletons use `addNonRec`. For safe recursive cliques, `addPreDefinitions` validates termination-hint consistency across the clique:
- `termination_by structural <param>` (`TerminationMeasure.elab` in `TerminationMeasure.lean`) explicitly selects structural recursion (`structuralRecursion` at `Structural/Main.lean:183` in `v4.34.1`) and requires the measure to elaborate to one of the function parameters.
- Non-structural `termination_by <term>` or any `decreasing_by` clause forces well-founded recursion (`wfRecursion` at `WF/Main.lean:23` in `v4.34.1`). A clique cannot mix structural and non-structural `termination_by` clauses, and `decreasing_by` is rejected when combined with `termination_by structural`.
- `termination_by?` requests the elaborator to report the inferred structural parameter or `GuessLex` measure.
- When neither hint forces a path, `addPreDefinitions` attempts `structuralRecursion` first and falls back to `wfRecursion`, combining diagnostics if both fail.

#### 2.2 Structural Recursion Elimination (`Structural/Main.lean`, `Structural/FindRecArg.lean`)
1. `FindRecArg` searches for non-fixed inductive parameters whose inductive group and index dependencies permit structural recursion.
2. During the transformation, `withRecFunsAsAxioms` temporarily adds the recursive functions as local axioms inside `withoutModifyingEnv` so type inference and definitional equality can operate on expressions referencing the not-yet-defined constants; the environment is restored before final declaration installation.
3. `Structural.elimMutualRecursion` rewrites the recursive clique into a non-recursive term built from the inductive group's `brecOn` functional induction primitives, and `structuralRecursion` (`Structural/Main.lean:183` in `v4.34.1`) passes the resulting non-recursive definition to `addNonRec` for full kernel typechecking.

#### 2.3 Well-Founded Recursion and `GuessLex` (`WF/Main.lean`, `WF/Fix.lean`, `WF/Rel.lean`, `WF/GuessLex.lean`, `Init/WF.lean`)
1. `wfRecursion` (`WF/Main.lean:23` in `v4.34.1`) packs mutual recursion into a unary representation, elaborates or infers a termination measure, synthesizes a `WellFoundedRelation` (`Init/WF.lean`) for the measure codomain via `WF.elabWFRel`, and lifts it via `invImage`.
2. `WF.mkFix` (`WF/Fix.lean`) constructs the non-recursive fixpoint term using `WellFounded.Nat.fix` (when the relation is natural-number `<` via `Nat.lt_wfRel`) or `WellFounded.fix`, replacing every recursive call with a proof obligation that the callee measure is strictly smaller than the caller measure.
3. `solveDecreasingGoals` runs the user's `decreasing_by` script or the default `decreasing_tactic`. Unsolved goals fail elaboration (`tests/elab_fail/decreasing_by.lean`).
4. When no explicit `termination_by` is given, `WF.guessLex` (`WF/GuessLex.lean`) generates candidate measures from eligible parameters, `sizeOf` measures, context-derived natural-number differences `e₂ - e₁`, and mutual-function ordering components, testing combinations up to a default cap of **32 combinations** (`generateCombinations?`) and formatting the candidate matrix on failure (`Could not find a decreasing measure` in `tests/elab_fail/decreasing_by.lean.out.expected`).
5. **Logical vs. compiled realization**: After installing the kernel-checked structural or well-founded definition via `addNonRec`, both `structuralRecursion` and `wfRecursion` invoke `addAndCompilePartialRec` to generate the `._unsafe_rec` (`DefinitionSafety.partial`) compiler realization used for native code generation.

---

### 3. Weakest-Precondition Interfaces (`Std.WP`), Partiality Encodings, and Aeneas `ITree` Integration

Basis: **source** + **documentation** (`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, `leanprover/lean4@88539871b4133140b0d5e9beb4cd446bcc0d2f40`, `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`; [`support/lean-wp-partiality-and-aeneas-integration/source-reading.json`](support/lean-wp-partiality-and-aeneas-integration/source-reading.json)).

#### 3.1 Three Distinct Proof Roles in Weakest-Precondition Verification
1. **Assertion-transformer interpretation**: `Std.WP.Basic` defines `WP` parameterized by program type, return value type, assertion lattice, and exception assertion type, supplying `wpTrans` and monotonicity (`WP.mono`).
2. **Verification-condition generation and framing**: `vcgen` (which deprecates `mvcgen` in `v4.35.0`) and `Std.WP.Frame` (guarded framing and frame-closure under spatial resource operators, demonstrated in `tests/elab/vcgenImp.lean` and `tests/elab/vcgenSepLogic.lean`) decompose goals into proof terms.
3. **Operational adequacy and source correspondence**: `Std.WP.Monad.Sound` (`LawfulWPMonadAttach`, `of_run_eq_wp`) relates WP-provable postconditions to values satisfying `MonadAttach.CanReturn`, but monotonicity alone does not establish termination or Rust-to-Lean semantic adequacy (since a constant `True` transformer is monotone). Similarly, `vcgenSepLogic.lean` demonstrates spatial framing over a toy total map (`Addr → Option Nat`) with fuel-bounded loops, which does not model Rust pointer provenance, lifetimes, or Tree/Stacked Borrows.

#### 3.2 Aeneas `ITree RustEffect` (`Result`) and `spec` (`DWP`) vs. `dspec` (`DWLP`)
In `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`backends/lean/Aeneas/Std/Primitives.lean` and `backends/lean/Aeneas/Std/WP.lean`, targeting `v4.35.0-rc4`), `Result` is no longer a simple 3-constructor inductive datatype; it is defined as an irreducible interaction tree `ITree RustEffect` (`RustEffect.Input` has constructor `fail : Error → Input` with empty response type `PEmpty`), exposing `Result.ok`, `vis`, `fail`, `div`, `bind` (`ITree.bind`), and a `MatchResult` case-analysis view.

In `Aeneas/Std/WP.lean` and `Data/Coinductive/ITreeWP/{DWP,DWLP,Taxonomy}.lean`, `spec` is defined as the least fixed point `DWP` (total correctness, mapping `Behavior.diverges` to `False`) and `dspec` is defined as the greatest fixed point `DWLP` (partial correctness, mapping `Behavior.diverges` to `True`):

| Current `Result` (`ITree RustEffect`) Outcome | `spec` (`DWP`, Least Fixed Point / Total Correctness) | `dspec` (`DWLP`, Greatest Fixed Point / Partial Correctness) |
| :--- | :--- | :--- |
| `ok a` (`StepResult.done` / `Behavior.terminates`) | Postcondition holds at `a` | Postcondition holds at `a` |
| `fail e` (`StepResult.trapped` / `Behavior.traps`) | `False` (`effectWP` maps failure to `False`) | `False` (`effectWP` maps failure to `False`) |
| `div` (`Behavior.diverges`) | `False` (divergence forbidden) | `True` (divergence permitted) |

In the `Std.Do` bridge at the end of `Aeneas/Std/WP.lean` (`Result.instWP`, `Result.instWPMonad`, `Result.of_wp`), `spec_to_mvcgen` lifts a total `spec` directly to a `Std.Do` triple, whereas `dspec_to_mvcgen` requires an explicit side condition ruling out `div`—proving why partial (`dspec`) and total (`spec`) specifications cannot be conflated.

#### 3.3 Comparison of Partiality and Recursion Mechanisms in Lean 4
Across `v4.30.0-rc2`, `v4.34.1`, and `v4.35.0`, six distinct recursion/partiality mechanisms exist with different logical and TCB obligations:

| Mechanism | Logical Representation in Kernel | TCB & Adequacy Obligation to Retain |
| :--- | :--- | :--- |
| **Structural / well-founded recursion** (`structuralRecursion`, `wfRecursion`) | Total non-recursive function built from `brecOn`, `WellFounded.Nat.fix`, or `WellFounded.fix` with justified unfolding equations | Discharge decreasing argument (`decreasing_by`); audit compiled `._unsafe_rec` realization separately if using `native_decide`. |
| **Explicit `partial def`** (`addAndCompilePartial`) | `opaque` constant inhabited via `mkInhabitantFor`; recursive body placed in `<decl>._unsafe_rec` (`DefinitionSafety.partial`) | Zero unfolding equations in kernel WHNF; cannot prove behavioral specs without an external relational model or `native_decide` axiom. |
| **Order-theoretic `partial_fixpoint`** | Monotone fixed point in a complete partial order (`CCPO` / `PartialOrder`); unfolding equations exported as theorems | Identify the domain order and meaning of bottom/unconstrained return values; note that tail-recursive equations like `f n = f (n + 1)` on an inhabited type have multiple total solutions on diverging inputs. |
| **Explicit fuel / step relation** (`StepResult`, `Behavior`) | Total function indexed by `fuel : Nat` or inductive small-step relation | Prove step determinism/adequacy (`ChoiceKind.demonic` vs. `ChoiceKind.angelic`) and quantify over all `fuel : Nat`. |
| **Interaction-tree semantics** (`ITree RustEffect` in Aeneas) | Coinductive/inductive tree distinguishing `ok`, `vis`/`fail`, and `div` | Choose total (`spec` / `DWP`) vs. liberal (`dspec` / `DWLP`) WP and prove correspondence to source Rust semantics. |
| **Coinductive predicates** (`coinductive_fixpoint` / greatest fixed points) | Greatest fixed point in `Prop` or complete lattice | Ensure selected order and coinduction rule match the intended trace/divergence property; in `tests/elab/vcgenCoinductiveFixpoint.lean`, importing `Std.WP` order instances affects elaboration of mixed inductive/coinductive mutual blocks. |

#### 3.4 Native Evaluation (`nativeEqTrue`) and Independent Kernel Checking (`Lake.CLI.Check`)
- In `Lean/Meta/Native.lean`, `nativeEqTrue` requires a closed Boolean expression without free or metavariables, compiles an auxiliary declaration, executes it natively, and—if `true`—adds a fresh axiom asserting the equality (used by `native_decide` in `Lean/Elab/Tactic/Decide.lean` and by `bv_decide` when reflection is bypassed).
- In `Lake/CLI/Check.lean` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), `Check.standardAxioms` permits only `propext`, `Classical.choice`, and `Quot.sound`; `checkUsedAxioms` rejects any theorem reaching a fresh `native_decide` axiom or `sorryAx`. `Lake.CLI.Check` also supports independent kernel replay (`bundledKernels`: `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

---

### 4. Twelve-Gate Lean Release Upgrade Checklist and `v4.30.0-rc2` → `v4.34.1` Deltas

Basis: **source** + **execution** (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`; [`support/lean-release-upgrade-checklist/source-map.json`](support/lean-release-upgrade-checklist/source-map.json), [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json)).

The twelve revalidation gates defined in [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json) govern any Lean toolchain migration in Anneal, and specifically quantify the transition from `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) to `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):

| Gate ID (`upgrade-checklist.json`) | Verification Boundary | `v4.30.0-rc2` (`3dc1a088b6d2`) Baseline | `v4.34.1` (`5045d0056413`) Verified State & Delta |
| :--- | :--- | :--- | :--- |
| **1. `toolchain-and-archive-identity`** | Exact Lean commit and per-platform archive SHA-256 digests (`anneal/flake.nix`) | Commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; `lean-4.30.0-rc2-linux_aarch64.tar.zst` bundled a non-native `leantar`. | Commit `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`); `lean-4.34.1-linux_aarch64.tar.zst` (SHA-256 `fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37`) ships a valid native AArch64 `bin/leantar`. |
| **2. `aeneas-lean-toolchain-alignment`** | Alignment between Anneal's Lean version and Aeneas `backends/lean/lean-toolchain` | `AeneasVerif/aeneas@ac9f1bc5262a` (`nightly-2026.06.03`) pins `leanprover/lean4:v4.30.0-rc2` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`). | Running Aeneas-generated Lean under `v4.34.1` is an explicit cross-toolchain compatibility edge requiring direct generated-corpus elaboration; `AeneasVerif/aeneas@21345f80fa21` targets `v4.35.0-rc4`. |
| **3. `lake-manifest-and-package-closure`** | Locked `lake-manifest.json` package graph and dependency config loading | Mathlib pinned at `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (blob `1a5af703163d8b39f4311aafe22ae171788179ee`); `importConfigFile` wrote `.lake/config/<pkgName>/lakefile.olean` inside each dependency's own directory. | Mathlib `v4.34.1` is `d13f23b723b8a846827a245b89c10fc7d3f11612`. In `v4.34.1`, `LoadConfig.configDir` (`Lake/Load/Config.lean:83`) and `importConfigFile` (`Lake/Load/Lean/Elab.lean:180-185`) hoist compiled dependency config artifacts into the consumer workspace's `.lake/config/<pkgIdx>/`, keeping read-only path dependencies free of writes. |
| **4. `logical-trust-and-admissions`** | Kernel checking, axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`), `sorryAx`, `unsafe`, `debug.skipKernelTC` | `Environment.lean` / `AddDecl.lean` enforce declaration safety and `ReplayFn`. | Preserved in `v4.34.1` (`Lean/Environment.lean`, 2,903 lines, SHA-256 `ee364e4788ce0560...`, `ReplayFn` at line 1307, `markQuotInit` at line 288). |
| **5. `generated-lean-acceptance`** | Parser, elaborator, module/import header processing, and name resolution on generated Lean | `Import.lean`, `Hygiene.lean`, `ResolveName.lean`. | Preserved in `v4.34.1` (`Lean/Elab/Import.lean`, 206 lines, SHA-256 `5d46fc36944ed3cb...`, `processHeaderCore` at line 141, `importModules` at line 159; `Lean/Hygiene.lean:95` `eraseMacroScopes`; `Lean/ResolveName.lean:194` `resolveGlobalName`). |
| **6. `proof-automation-replay`** | Tactic behavior across `simp`/`simp_all`, `grind`, `omega`, and `linter.unusedSimpArgs` | `v4.30.0-rc2` `linter.unusedSimpArgs` emits plain warning text; `omega` omits dark/grey shadows; `grind` performs bounded E-matching/tableaux search. | In `v4.34.1` (`Elab/Tactic/Simp.lean:675, 797, 815`), `linter.unusedSimpArgs` appends an interactive code-action hint (`Hint: Omit it from the simp argument list. [apply] simp`) to the warning message; `omega` (`Omega/Frontend.lean:672`) and `Grind.main` (`Grind/Main.lean:396`) preserve core semantics. |
| **7. `recursion-termination-and-partiality`** | `addPreDefinitions`, `structuralRecursion`, `wfRecursion`, `partial def`, and Aeneas `decreases` clauses | `PreDefinition/Main.lean` (`3d2169aeae3d4d29e04ba9421ec3b7f95ee799e7`), `Structural/Main.lean` (`d3c72b3eb9b0d0d89d70294bf33ee0927ed9159f`), `WF/Main.lean` (`b066ac285ee76cf41a76275750f26810af9ece78`). | Preserved in `v4.34.1` (`PreDefinition/Main.lean:288` `addPreDefinitions`, `Structural/Main.lean:183` `structuralRecursion`, `WF/Main.lean:23` `wfRecursion`), maintaining the exact `opaque` + `._unsafe_rec` split for `partial def` and recursor/`WellFounded.fix` translation for total recursion. |
| **8. `olean-ilean-and-lake-trace-state`** | `.olean`/`.ilean` binary format, Git-hash header validation, and Lake `.trace`/`.hash` files | Module facets `.olean`, `.ilean`, `.c`; `CacheOutput.schemaVersion := "2025-09-10"`; Mathlib `rootHashGeneration := 4`. | In `v4.34.1`, `Lake/Build/Module.lean` (lines 266, 468-471, 630) adds module-system facets `.olean.server`, `.olean.private`, and `.ir.sig`; `Lake/Config/Cache.lean:339` updates `CacheOutput.schemaVersion := "2026-02-25"`; Mathlib `Cache/IO.lean:150` bumps `rootHashGeneration` from `4` to `5`. Prepared `.olean` caches must be rebuilt across versions. |
| **9. `interactive-lsp-and-diagnostics`** | `lean --server` (`Watchdog`, `FileWorker`, `RequestHandling`), `plainGoal`, `waitForDiagnostics`, `lean --json` | `SerialMessage` JSON output; `PlainGoalParams` unversioned; `WaitForDiagnosticsParams` checks `p.version ≤ doc.meta.version`. | Preserved in `v4.34.1` (`Lean/Message.lean` SHA-256 `09277320b843288e...`; `Watchdog.lean:229`, `FileWorker.lean:568, 583`, `RequestHandling.lean:213, 244, 467`), including intermediate per-command snapshot `publishDiagnostics` notifications. |
| **10. `host-native-artifacts`** | `.c`, `.o`, static/shared libraries, precompiled plugins, and `leantar` | `Lake/Build/Actions.lean` (`compileLeanModule`, `compileO`, `compileStaticLib`, `compileSharedLib`). | Preserved in `v4.34.1` (`Lake/Build/Actions.lean`, 212 lines, SHA-256 `9c7d7101f89eb1d0...`, lines 29, 111, 137, 149). |
| **11. `determinism-and-cache-equivalence`** | Repeat-build `.olean`/`.ilean` byte determinism and clean vs. cache-seeded build equivalence | Requires empirical execution verification whenever cache keys rely on artifact byte hashes. | In `v4.34.1`, `Lake/Config/Cache.lean:434, 449` adds `overwrite : Bool := true` to `writeOutputsCore`/`writeOutputs`, and `readOutputs?` (line 463) throws on malformed JSON, caught by `getArtifactsUsingCache?` (`Lake/Build/Common.lean:521`) and converted to a verbose-logged cache miss. |
| **12. `end-to-end-generated-corpus`** | Integrated generated-Rust-to-Lean build, tactic proof check, and `#print axioms` audit | Must exercise functions, borrows, loops/recursion, trait models, expected diagnostics, and final theorem axiom sets. | Must be executed against the locked package closure (`v4.34.1` + Mathlib `d13f23b723b8`) in the relocated/read-only layout before promoting a toolchain upgrade. |

## Boundaries

- **Compiler backend correctness for `partial def` (`not examined`)**: This report characterizes the elaboration and kernel boundary of `partial def` (`opaque` logical constant vs. `<decl>._unsafe_rec` executable definition); it does not prove that every compiler backend compiles every `partial def` correctly or characterize the runtime behavior of diverging partial functions.
- **Incompleteness of automatic termination search (`known not to apply` as a disproof of termination)**: Failure of structural argument search (`FindRecArg`) or `GuessLex` (which is bounded to 32 argument-measure combinations by default) does not establish mathematical nontermination; users or generators can supply explicit `termination_by` and `decreasing_by` proofs.
- **Logical vs. compiled realization equivalence (`not examined` / `unknown` without proof)**: Both `structuralRecursion` and `wfRecursion` emit a kernel-checked logical term via `addNonRec` and a separate `._unsafe_rec` (`DefinitionSafety.partial`) compiler realization via `addAndCompilePartialRec`. Source inspection establishes the split representation but does not prove semantic equivalence between the logical recursor/fixpoint term and native compiled code.
- **Aeneas `v4.35.0-rc4` compatibility with released `v4.35.0` or `v4.34.1` (`not examined` by execution / `unknown`)**: No live build of `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` against `v4.34.1` or released `v4.35.0` was executed in the constituent `Std.WP` study; source comparison already shows API evolution (`mvcgen` deprecation in favor of `vcgen`, and `WP.wpTrans` naming differences on `master@88539871b413`).
- **Promoting `Std.WP` toy separation logic or generic `ITree` effects to Rust semantics (`known not to apply`)**: The `tests/elab/vcgenSepLogic.lean` heap (`Addr → Option Nat`) and generic `ITree` effects in Aeneas do not model Rust pointer provenance, lifetime borrowing, unsafe memory, concurrency, or I/O (`RustEffect` in `Primitives.lean` models only `fail : Error → Input` with `PEmpty` return).
- **Passing the 12-gate upgrade checklist vs. Rust-to-Lean semantic soundness (`known not to apply`)**: Passing [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json) establishes toolchain compatibility, build reproducibility, and axiom-allowlist hygiene, not the mathematical soundness of the Rust-to-Lean translation itself.

## Evidence

### 1. Support Artifacts in This Package
- [`support/lean-wp-partiality-and-aeneas-integration/source-reading.json`](support/lean-wp-partiality-and-aeneas-integration/source-reading.json): Exact upstream blob SHA-1s and inspected declarations across `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), and `leanprover/lean4@88539871b4133140b0d5e9beb4cd446bcc0d2f40`.
- [`support/lean-release-upgrade-checklist/source-map.json`](support/lean-release-upgrade-checklist/source-map.json): Exact blob SHA-1s for Anneal packaging (`anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`), Aeneas toolchain pins (`backends/lean/lean-toolchain` blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26` and `backends/lean/lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`), and constituent reference reports.
- [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json): Machine-readable 12-gate Lean release upgrade checklist.

### 2. Primary Upstream Source Files and Blob Identities Examined
- **`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) & `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`)**:
  - `src/Lean/Parser/Term.lean` (`v4.30.0-rc2` blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559`): syntax and docstrings for `termination_by`, `termination_by?`, `decreasing_by`, and `partial_fixpoint`.
  - `src/Lean/Elab/PreDefinition/Main.lean` (`v4.30.0-rc2` blob `3d2169aeae3d4d29e04ba9421ec3b7f95ee799e7`; `v4.34.1` 362 lines, `addPreDefinitions` at line 288): recursive-clique SCC partitioning, `addAndCompilePartial`, structural/partial-fixpoint/WF dispatch, and `useSorry := true` error recovery.
  - `src/Lean/Elab/PreDefinition/MkInhabitant.lean`: `mkInhabitantFor` arbitrary inhabitant synthesis for `opaque` partial declarations.
  - `src/Lean/Elab/PreDefinition/Basic.lean` (`v4.30.0-rc2` blob `885df3685fdee44bf095924d951eb345dc8eb1f2`): `addNonRec`, `addAndCompilePartialRec`, and `Compiler.mkUnsafeRecName` (`._unsafe_rec`) with `DefinitionSafety.partial`.
  - `src/Lean/Elab/PreDefinition/TerminationHint.lean` (`v4.30.0-rc2` blob `5448856c9a227fb37367aac1eedeafe220c11ef5`) & `TerminationMeasure.lean` (`v4.30.0-rc2` blob `bd9b520513d877501adeae20d62fcc4f3cea7498`): termination-hint validation and structural parameter enforcement.
  - `src/Lean/Elab/PreDefinition/Structural/Main.lean` (`v4.30.0-rc2` blob `d3c72b3eb9b0d0d89d70294bf33ee0927ed9159f`; `v4.34.1` `structuralRecursion` at line 183) & `Structural/FindRecArg.lean` (`v4.30.0-rc2` blob `92802d16417547323bf279e1163ba27d7e43eaf9`): `withRecFunsAsAxioms` under `withoutModifyingEnv`, `elimMutualRecursion` via `brecOn`.
  - `src/Lean/Elab/PreDefinition/WF/Main.lean` (`v4.30.0-rc2` blob `b066ac285ee76cf41a76275750f26810af9ece78`; `v4.34.1` `wfRecursion` at line 23), `WF/Fix.lean` (`v4.30.0-rc2` blob `0fef8a9aac176ae7941d8928d61df69b96dfa6a1`), `WF/Rel.lean` (`v4.30.0-rc2` blob `f544ddbecffcecee378ff9284fe6270ee34d028b`), & `WF/GuessLex.lean` (`v4.30.0-rc2` blob `84e988dd16e89196f29a4f8f4c3cbafdb9700739`): unary packing, `elabWFRel`, `mkFix`, `solveDecreasingGoals`, and `guessLex` (32-combination bound).
  - `src/Init/WF.lean` (`v4.30.0-rc2` blob `6225c703fef3bc62ded4f2e74c0df452ab5c977a`): `WellFoundedRelation`, `invImage`, `Nat.lt_wfRel`, `sizeOfWFRel`, `WellFounded.Nat.fix`.
  - `src/Lean/Declaration.lean`, `src/Lean/AddDecl.lean`, `src/Lean/Compiler/LCNF/ToDecl.lean`: `DefinitionSafety`, `OpaqueVal`, `ConstantInfo.isPartial`, and `getDeclInfo?` preference for `._unsafe_rec`.
  - Checked-in test fixtures: `tests/elab/partial1.lean` & `.out.expected`, `tests/elab/kernel2.lean`, `tests/elab/reduce1.lean`, and `tests/elab_fail/decreasing_by.lean` (blob `1a58fc6f17db7064f8ccaf953d70a5915b883a68`) & `.out.expected` (blob `474a642aa87c8a7db571c293c870fcf035f3d50b`).
- **`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` & `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`)**:
  - `backends/lean/Aeneas/Std/Primitives.lean`, `backends/lean/Aeneas/Std/WP.lean`, `Data/Coinductive/ITreeWP/{DWP,DWLP,Taxonomy}.lean`.
  - `src/Std/WP/Basic.lean`, `src/Std/WP/Monad/Sound.lean`, `src/Std/WP/Frame.lean`, `src/Lean/Meta/Native.lean` (`nativeEqTrue`), `src/Lean/Elab/Tactic/Decide.lean`, `src/lake/Lake/CLI/Check.lean` (`standardAxioms`, `checkUsedAxioms`, `bundledKernels`), and `tests/elab/{vcgenImp,vcgenSepLogic,vcgenCoinductiveFixpoint}.lean`.

## Revalidation

To revalidate partial definitions, termination elaboration, WP encodings, and toolchain upgrade gates on a new Lean or Aeneas revision:

1. **Diff the `PreDefinition` elaborator and compiler hook**:
   Inspect `Lean/Elab/PreDefinition/Main.lean` (`addPreDefinitions`, `addAndCompilePartial`), `MkInhabitant.lean` (`mkInhabitantFor`), `Basic.lean` (`addAndCompilePartialRec`, `mkUnsafeRecName`), `Structural/Main.lean` (`structuralRecursion`, `withRecFunsAsAxioms`), `WF/Main.lean` (`wfRecursion`), `WF/Fix.lean` (`mkFix`, `solveDecreasingGoals`), `WF/GuessLex.lean` (`guessLex`), and `Lean/Compiler/LCNF/ToDecl.lean` (`getDeclInfo?`) to verify whether `partial def` still splits an `opaque` logical constant from `<decl>._unsafe_rec` and whether total recursion still lowers to kernel-checked `brecOn` / `WellFounded.fix` terms.
2. **Run the behavioral partial-definition and termination probes**:
   - Define `partial def fact (n : Nat) : Nat := if n == 0 then 1 else n * fact (n - 1)`, confirm that `Kernel.whnf` leaves `fact 10` stuck and non-definitionally-equal to `3628800` (`tests/elab/kernel2.lean`), while `#eval fact 10` and `by native_decide` succeed and `#print axioms` on the `native_decide` theorem exposes the generated native-evaluation axiom (`tests/elab/reduce1.lean`).
   - Run a termination fixture covering inferred structural recursion, `termination_by structural`, explicit `Nat` well-founded measure, inferred `GuessLex` measure (`termination_by?`), custom `decreasing_by`, unsolved decrease goals (`tests/elab_fail/decreasing_by.lean`), and `#print axioms` on the resulting theorems.
3. **Execute the 12-gate checklist in [`support/lean-release-upgrade-checklist/upgrade-checklist.json`](support/lean-release-upgrade-checklist/upgrade-checklist.json)**:
   Record exact toolchain commit and archive SHA-256 digests, verify `lake-manifest.json` closure, rebuild all `.olean`/`.ilean` caches (accounting for `.olean.server`, `.olean.private`, `.ir.sig`, and `CacheOutput.schemaVersion`), replay batch and LSP/RPC diagnostics, and verify that `#print axioms` on all exported verification theorems lies strictly within `[propext, Classical.choice, Quot.sound]`.
