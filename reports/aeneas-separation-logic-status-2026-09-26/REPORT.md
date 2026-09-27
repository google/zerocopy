# Aeneas separation-logic status: selected release, current main, and draft implementation

## Summary

Anneal's selected Aeneas release, `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, does not contain the separation-logic backend now under development. It is the functional safe-Rust model already characterized by `aeneas-resource-semantics-nightly-2026-06-03`: raw-pointer types can appear in signatures, but the symbolic interpreter rejects raw-pointer dereference.

Aeneas `main` has moved materially since that release. At `b86120db3183b0107eb5f2637b11c424cd06ef1c`, it contains generic interaction-tree/effect machinery and a specification-registration interface that lets `step` work with user-defined Hoare-style judgments. Those pieces are real, merged prerequisites for a spatial logic. They are not, by themselves, the separation-logic implementation: current `Aeneas.lean` does not import `Aeneas.SepLogic`, current `main` has no `backends/lean/Aeneas/SepLogic/` tree, and raw-pointer dereference is still rejected by the OCaml symbolic interpreter.

The concrete first-order sequential separation logic is in open draft PR `AeneasVerif/aeneas#1352`. At the observed head `75fb1479040d32d43d31b74510167ee3b873d28a`, the draft adds an affine heap predicate `IProp`, disjoint-heap composition, total and partial separation-logic specifications, heap-aware `Result` effects, raw-pointer and buffer models, `iframe`/`iintro`/`irewrite` proof-mode tactics, and regression examples. Its memory model is slot-granular: an address is an allocation identifier plus a natural-number slot offset, and a heap cell stores a Lean type together with a value. Pointer permissions are carried by assertions such as `q ↦ v`, not by the pointer value.

That draft is not an end-to-end semantics for arbitrary unsafe Rust. At the same exact PR head, `src/interp/InterpPaths.ml` still raises “Aeneas does not yet support dereferencing raw pointers.” The PR's extractor-side changes are narrow, while the new raw-pointer operations are Lean library models implemented using `Result.guardedModify`. The checked-in separation-logic tests therefore demonstrate the Lean model and proof interface; they do not establish that Aeneas can translate a Rust raw-pointer dereference into that model.

The draft should also be treated as a moving research branch rather than a consumable release. As observed on 2026-09-26, PR #1352 was open and marked draft; its exact head had failing `lean` and `nix` check runs. Its `tests/lean/SepLogic/README.md` is internally stale relative to the same tree: it says `SepLogic` is not a default Lake target even though the exact-head `lakefile.lean` marks it `@[default_target]`, and it describes several files and directories that are absent from the exact-head tree. The implementation source is therefore stronger evidence than that README for current status.

For Anneal, the immediate conclusion is simple. The Aeneas version Anneal currently downloads cannot provide this separation logic. A future integration can reuse important merged architecture from current Aeneas, and PR #1352 is a concrete prototype worth tracking, but consuming it would require at least a new Aeneas dependency decision and a separate justification for how Rust/Charon/LLBC unsafe-memory operations enter the modeled heap semantics.

No fresh Aeneas, Charon, Lean, Lake, or Rust execution was performed for this report. It uses exact source revisions, repository history, PR metadata, checked-in tests, and upstream CI status.

## Applicability

Primary subjects:

- Anneal-selected Aeneas release:
  - repository: `AeneasVerif/aeneas`
  - revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
  - release: `nightly-2026.06.03`
  - relationship: current Anneal downloads this named release.
- Current Aeneas main as observed:
  - repository: `AeneasVerif/aeneas`
  - revision: `b86120db3183b0107eb5f2637b11c424cd06ef1c`
  - branch: `main`
  - observation date: 2026-09-26.
- Draft first-order sequential separation logic:
  - repository: `AeneasVerif/aeneas`
  - pull request: `#1352`
  - revision: `75fb1479040d32d43d31b74510167ee3b873d28a`
  - state as observed: open, draft
  - observation date: 2026-09-26.

The report answers the inventory question “what separation-logic machinery exists, at which exact revisions, and what is consumable now?” It does not treat current `main` or PR #1352 as part of Anneal merely because they are newer than Anneal's selected release.

“Consumable” is used in three different senses and kept explicit:

1. **selected by Anneal** — code in Anneal's actual Aeneas release;
2. **merged upstream** — code on current Aeneas `main` that a future Aeneas pin can depend on;
3. **prototype-available** — code present only at an exact open-PR head, usable for experiments if pinned deliberately but not an upstream release commitment.

The report concerns the Lean backend because the separation-logic implementation is in Aeneas's Lean library. It does not claim equivalent F*, Coq, or HOL4 support.

## Findings

### Anneal's selected Aeneas release has no separation-logic backend

Anneal's current Nix configuration names Aeneas release `nightly-2026.06.03`. The Aeneas tag resolves to `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

At that revision, the Lean tree contains the ordinary `Std/WP.lean` and raw-pointer type support but none of the later `Aeneas/SepLogic`, coinductive `Effect`/`ITree`, generic `Std/Spec`, or heap-model files used by the draft implementation.

The existing corpus report `aeneas-resource-semantics-nightly-2026-06-03` establishes the semantic boundary in more detail: the functional backend is advertised for a subset of safe Rust, does not expose a proof-facing heap/resource model, and rejects raw-pointer dereference.

Thus no amount of Lean-side proof scripting inside Anneal can obtain the new separation logic from the dependency it currently selects; the relevant library is not in that release.

Basis: **source**, **release identity**, and existing corpus synthesis.

### Current Aeneas main contains merged prerequisites, not the full spatial logic

Several architectural changes have landed on Aeneas `main` since the Anneal-selected release.

PR #1180, merged on 2026-09-08, added generic coinductive interaction-tree infrastructure. At current `main`:

- `Aeneas.Data.Coinductive.Effect` defines an effect signature with an input type and input-indexed output type, effect sums, and subeffect mappings.
- `Aeneas.Data.Coinductive.ITree` defines trees with `ret`, `div`, and visible-effect nodes and supplies monadic/partial-fixpoint structure.
- `Aeneas.Std.Spec` defines `SpecInfo` and `#register_spec_info`, allowing `step` to learn the program position, postcondition position, monotonicity rule, bind rule, and proof tactics for an arbitrary registered specification predicate.
- `Aeneas.Tactic.Step.Tests.Triple` demonstrates that registration mechanism with a separate state monad and a custom triple, including sequencing and branch splitting.

PR #1267 generalized `step` specifically so it would no longer assume the ordinary `Std.WP.spec` shape. Later small changes generalized supporting proof infrastructure, including `uncurry'` for use with `IProp`.

These are meaningful integration seams. A future separation logic does not need an entirely separate proof driver; it can register its own Hoare judgments with the existing `step` machinery.

But current `main` does not expose the actual first-order separation-logic library. `backends/lean/Aeneas.lean` imports `Command`, `Data`, `Do`, `Extract`, `Std`, and `Tactic` but not `Aeneas.SepLogic`. The current main tree has no `backends/lean/Aeneas/SepLogic/` directory. Its root README still describes separation logic as ongoing work intended to lift the current unsafe-code and concurrency limitations.

Basis: **source**, **repository history**, and **documentation**.

### Current main still rejects Rust raw-pointer dereference

The merged generic effect/specification infrastructure has not removed the existing source-language boundary.

At current main revision `b86120db3183b0107eb5f2637b11c424cd06ef1c`, `src/interp/InterpPaths.ml` still handles `Deref` of `TRawPtr` by raising:

> Aeneas does not yet support dereferencing raw pointers.

The exact same source blob appears at the observed PR #1352 head.

This matters because a Lean heap model and a Rust-to-Lean translator are separate parts of an end-to-end claim. The former can model a raw-pointer read; the latter must still translate or otherwise justify the Rust operation that is supposed to denote that read.

Basis: **source**.

### PR #1352 is the concrete first-order sequential separation-logic implementation

PR #1352 is titled “Extending Aeneas with first-order sequential separation logic.” At exact head `75fb1479040d32d43d31b74510167ee3b873d28a`, it adds the missing spatial layer rather than only infrastructure.

The core assertion type is `Aeneas.SepLogic.IProp`. An `IProp` is a heap predicate paired with a proof that it is closed under heap extension. This makes the model affine: resources may be discarded, `emp` holds of every heap, and `H ⊢ emp` is valid. Separation remains exclusive, however; `P ∗ Q` requires a split into compatible disjoint heap fragments, and two points-to assertions for the same slot entail false.

The surface deliberately resembles Iris-style notation: `IProp`, `iprop(...)`, `∗`, `-∗`, `⊢`, `⊣⊢`, and `↦`. The implementation is standalone rather than an instantiation of Iris-Lean.

Basis: **source**.

### The draft heap is typed and slot-granular

`Aeneas.Std.Heap` models an address as an allocation identifier plus a natural-number offset. A heap is a finite map from such locations to dependent heap cells carrying both a Lean type and a value.

Heap composition is disjoint union under a `PartialCommMonoid` compatibility relation. A contiguous range is a union of one-slot heaps; range ownership can split and join at slot boundaries.

Fresh allocation chooses a new allocation identifier deterministically. Reads require a proof that the addressed slot exists with the expected type. Writes replace a typed slot, and free removes it.

This is a useful first-order memory model for ownership proofs. It is not a byte-level Rust abstract machine. In particular, the model shown here does not itself encode Rust pointer provenance, allocation layouts in bytes, padding, partial initialization within an object, or concurrent atomic behavior.

Basis: **source** + **derived** model boundary.

### Pointer values are addresses; permissions live in `IProp`

The draft `Aeneas.Std.RawPtr` represents a raw pointer by:

- an allocation identifier; and
- a natural-number slot offset.

The mutability index distinguishes mutable from const raw pointers, but ownership and access permission are not fields of the pointer. They are propositions such as `q ↦ value` and `q ↦* values`.

The draft implements allocation, read, write, and free as `Result` computations over the abstract heap. Their specifications use separation-logic triples. Examples include:

- allocation from `emp` returning ownership of fresh storage;
- read preserving the points-to assertion while returning the stored value;
- write consuming ownership of the old value and returning ownership of the new value;
- free consuming the points-to assertion and returning `emp`.

The separation between pointer value and permission is exactly what makes aliasing representable: two pointer values may identify the same slot, while two simultaneous exclusive points-to resources for that slot cannot be composed.

Basis: **source**.

### The program logic is frame-preserving by construction

At the draft head, `Result` is an interaction tree over a `RustEffect`. The effect signature contains a heap `guardedModify` event plus failure. A guarded modification carries:

- a heap precondition; and
- a state transformer whose type requires a proof of that precondition.

`Std.WP.handler` interprets those effects over `Heap`.

The generic coinductive `TotalSpec` and `PartialSpec` provide total and partial correctness for interaction trees. The separation-logic layer defines `iwp` by quantifying over an arbitrary frame and requiring the postcondition to return that frame unchanged. `ispec P m Q` is total correctness and `dispec P m Q` is partial correctness.

This design puts the frame condition in the judgment rather than treating the frame rule as an unverified tactic convention. `ispec_frame`, `ispec_mono`, `ispec_bind`, and their partial-correctness counterparts are then proved from the semantics and registered for proof automation.

Total and partial correctness differ on divergence: `TotalSpec` is the least fixed point and rejects `ITree.div`; `PartialSpec` is the greatest fixed point and accepts divergence.

Basis: **source**.

### The draft reuses `step` and adds a spatial proof mode

PR #1352 connects its `ispec`/`dispec` judgments to the generalized specification machinery already present on main.

The draft extends `step` with separation-logic-specific handling for spatial ghost arguments and ramified frames. It adds proof-mode tactics including:

- `iframe` for resource cancellation/framing;
- `iintro` for spatial/pure introductions;
- `irewrite` for entailment-aware rewriting; and
- supporting simplification infrastructure.

Checked-in tests use these tactics together with ordinary `step`/`step*`, which is an important usability property for Anneal: spatial reasoning is being integrated into the existing Aeneas proof workflow rather than exposed as a disconnected second proof engine.

Basis: **source**.

### The checked-in examples exercise the Lean memory model, not Rust raw-pointer translation

The draft contains concrete proofs over the new memory model. For example, `tests/lean/SepLogic/Fixtures.lean` defines a program that reads and writes a `MutRawPtr` and proves a points-to triple. `Buffer.lean` covers allocation, indexed reads and writes, free, copy, compare, and bridges between functional arrays/slices and raw buffers.

These are meaningful regression examples for the Lean library. But the same exact PR head still rejects raw-pointer dereference in the OCaml symbolic interpreter. The PR's file changes are overwhelmingly in the Lean backend; the only `src/` change in the PR file list is a two-line update to `ExtractBuiltinLean.ml`, while `InterpPaths.ml` is unchanged.

Therefore these examples do not establish an end-to-end pipeline from a Rust function containing arbitrary raw-pointer dereference through Charon and Aeneas into a heap-aware Lean term. They establish that the modeled Lean operations and their proof rules exist.

For Anneal's Rust-level UB-freedom goals, that missing bridge is a separate semantic obligation, not an implementation detail that can be inferred from the presence of `RawPtr.read.spec`.

Basis: **source**, **PR diff**, and **derived** pipeline distinction.

### The prototype contains a bridge between functional values and modeled raw storage

Although general Rust raw-pointer dereference is not translated, the draft is not isolated from Aeneas's existing functional model.

The checked-in `Buffer` tests include `mut_to_raw`/`end_mut_to_raw` examples that start from functional Aeneas arrays or slices, materialize a buffer in the abstract heap, perform raw-style updates, and convert the result back to the functional representation. The proof establishes how ownership moves across that explicit modeled boundary.

This is likely relevant to a future Anneal architecture: safe functionalized values can remain values until a proof deliberately enters the explicit-memory model.

It is not evidence that arbitrary source-level unsafe code is already routed through that boundary automatically.

Basis: **source**.

### The draft's own README is not authoritative for its exact-head contents

`tests/lean/SepLogic/README.md` at the PR head describes a broader architecture than the same exact tree contains. It refers to files such as `StateMachine.lean`, `SepLogic/Semantics.lean`, and a `MutableData/` hierarchy that are absent from the observed PR tree.

It also says the `SepLogic` Lake target is “not part of the default test build.” At the exact same revision, `tests/lean/lakefile.lean` contains `@[default_target] lean_lib SepLogic`.

Because the PR is a moving draft, checked-in prose has evidently drifted relative to code. This report therefore uses exact tree contents and source as primary evidence and treats the README as design intent only where the tree corroborates it.

This discrepancy is also a revalidation warning: future researchers should not infer exact implementation status from the README without checking the same revision's tree and build configuration.

Basis: **source** and **derived** consistency check.

### The exact draft head was not green when observed

GitHub check runs for `75fb1479040d32d43d31b74510167ee3b873d28a` completed with failures in both the `lean` and `nix` jobs on 2026-09-25. Other checks, including generated-Lean diff and Charon-pin checks, succeeded.

This report did not inspect enough job-log detail to attribute those failures to a particular source change, so it does not claim that the separation-logic code itself is the direct cause. The narrower consumability conclusion is sufficient: the exact observed draft head was not a green upstream integration point.

Basis: upstream **execution/status** metadata.

### Concurrency is not implemented by this reported prototype

The PR title scopes the implementation to first-order **sequential** separation logic. The current main README continues to list concurrency, together with unsafe code, as a limitation intended to be addressed by separation-logic work.

The effect signature at the draft head models heap modifications and failure; the report found no concurrent operational model in the claimed implementation.

Anneal should therefore not infer support for atomics, thread interference, relaxed memory ordering, or concurrent separation logic from the existence of `IProp`.

Basis: **source**, **documentation**, and PR scope.

### What Anneal can consume today is revision-dependent

There are three practical levels:

**From Anneal's current Aeneas dependency:** no spatial logic. Anneal receives the June 3 functional backend described by the existing resource-semantics report.

**From current Aeneas main:** reusable prerequisites are available — interaction trees/effects, generic registered specifications, and generalized `step`. A future Aeneas update could rely on these without taking the open separation-logic PR.

**From PR #1352 at an exact head:** a substantial first-order sequential spatial-logic prototype is available for experiments, including heap-aware raw-pointer models and proof automation. But it is draft-only, not green at the observed head, has stale internal documentation, and does not remove the source translator's rejection of raw-pointer dereference.

A future Anneal design that wants this work should therefore pin and evaluate an exact revision rather than treating “Aeneas supports separation logic” as a single Boolean capability.

Basis: synthesis of the exact subjects above.

## Boundaries

- No fresh build, Lean elaboration, Aeneas translation, Charon extraction, Lake test, or Rust execution was performed.
- Upstream GitHub check-run conclusions are reported as observed external execution metadata; this report did not reproduce or diagnose those runs.
- The report does not prove soundness of the draft separation logic.
- The report does not prove that every checked-in separation-logic theorem is axiom-free or that the complete Lean trusted base is appropriate for Anneal.
- The report does not characterize every file on the PR branch. It focuses on the semantic model, proof interface, translator boundary, and integration status relevant to Anneal.
- The report does not treat a hand-written Lean model of a Rust-like operation as proof that arbitrary source Rust using that operation is translated to the model.
- The abstract heap is not claimed to match Rust's byte/provenance/validity model. A separate abstraction theorem or correspondence argument would be needed for Rust-level UB-freedom claims.
- “Raw pointer” in the draft Lean library names the model's pointer value. It should not be assumed to carry all semantics of `rustc`/LLVM raw pointers.
- The report does not establish concurrent reasoning, atomics, relaxed memory order, I/O, or nondeterminism.
- Current `main` and open PR state are observations dated 2026-09-26. They can change independently of Anneal's still-pinned release.
- The stale/inconsistent draft README is recorded as evidence about the exact observed head, not as a permanent defect in the project.
- Existing reports remain authoritative for the June 3 functional backend's lifetime, resource, and Rust-to-Lean translation details; this report does not duplicate their full analysis.

## Evidence

**Anneal source — current dependency selection.**

- `google/zerocopy` `anneal/flake.nix` on current main: selects Aeneas release `nightly-2026.06.03`.
- Aeneas tag `nightly-2026.06.03`: resolves to commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`.

**Selected Aeneas release — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.**

- Root `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: functional subset of safe Rust; unsafe and concurrency described as ongoing separation-logic work.
- `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: raw-pointer dereference rejected.
- Existing corpus package `reports/aeneas-resource-semantics-nightly-2026-06-03/`: detailed proof-facing resource boundary.

**Current Aeneas main — `AeneasVerif/aeneas@b86120db3183b0107eb5f2637b11c424cd06ef1c`.**

- `README.md`, blob `7326e8ea5223171dec810a0cb669b8683c48eddc`: current support statement still describes unsafe/concurrency support as ongoing separation-logic work.
- `backends/lean/Aeneas/Data/Coinductive/Effect.lean`, blob `0015e858c1ebd2a923435be811082fa655bf531f`: generic effects and subeffects.
- `backends/lean/Aeneas/Data/Coinductive/ITree.lean`, blob `0674c6ffafa146f91f7f1b8ced10428d2f148a25`: interaction trees with return/divergence/visible effects.
- `backends/lean/Aeneas/Std/Spec.lean`, blob `84f7f99e38b530629bbd2cd0e0fa486d57918211`: `SpecInfo` and `#register_spec_info`.
- `backends/lean/Aeneas/Tactic/Step/Tests/Triple.lean`, blob `af674153793bf4a15c79499e419230c978c94786`: custom-state-monad triple registered with and discharged by `step`.
- `backends/lean/Aeneas.lean`, blob `45ba4ca89d0e056a52e6b7920d390718b5d253b4`: no `Aeneas.SepLogic` import.
- `backends/lean/Aeneas/Std.lean`, blob `19e5d842450d4ed2df711a83b3b3c5a863f1f2a8`: no heap/separation-logic import.
- `src/interp/InterpPaths.ml`, blob `3197a7b0367f2037611f20456d781b2ebb0739e0`: raw-pointer dereference still rejected.
- PR #1180, merged 2026-09-08 as `df7059b918e91cd1ac37c6814f642a935948025e`: interaction-tree/effect groundwork.
- PR #1267, merged 2026-08-24 as `089704f2476812da48a0c027840c9619b8d546f9`: generalized `step` to registered specifications.

**Draft first-order sequential separation logic — PR #1352 head `75fb1479040d32d43d31b74510167ee3b873d28a`.**

- PR #1352 metadata: open and draft as observed 2026-09-26.
- `backends/lean/Aeneas/SepLogic/Basic.lean`, blob `5b50eb4a1532251386955d754bb5d711600d384b`: affine `IProp`, separating conjunction, points-to, entailment, exclusivity.
- `backends/lean/Aeneas/Std/Heap.lean`, blob `d635192c03e4b49ab57f6581e4f93a2a17ed265c`: typed slot heap, disjoint-union PCM, range heaps, allocation, read/write/free, heap extension.
- `backends/lean/Aeneas/Std/Primitives.lean`, blob `915ff412447fd47ccbb3f4bbf34d84628e13a77e`: `RustEffect`, `guardedModify`, failure, and `Result = ITree RustEffect`.
- `backends/lean/Aeneas/Data/Coinductive/Spec.lean`, blob `b494834d2aab861331255738ab291c52e767e833`: generic handler semantics, least-fixed-point total correctness, greatest-fixed-point partial correctness.
- `backends/lean/Aeneas/Std/WP.lean`, blob `134d8b9f7dfb24e8afdefd730cae547ba540d2ce`: heap handler; `iwp`, `ispec`, `dispec`; frame/mono/bind rules and proof integration.
- `backends/lean/Aeneas/Std/RawPtr.lean`, blob `33e3dc4b7c06c9b7c46703ec19199d991d023ed1`: abstract raw pointers, points-to/range ownership, allocation/read/write/free and specifications.
- `backends/lean/Aeneas/SepLogic.lean`, blob `99f53b5889fde9a05e0056a65edcc063b0176da8`: separation-logic library root.
- `backends/lean/Aeneas/Tactic/SepLogic.lean`, blob `acda33446e1affbe56abcea888218c04a78d5e2e`: proof-mode tactic root.
- `backends/lean/Aeneas.lean`, blob `a6e11f94c356814ec1b5e3c1881d4c46cd1acdce`: draft root now imports `Aeneas.SepLogic`.
- `backends/lean/Aeneas/Std.lean`, blob `66c388bdf6960f41b0c92cfd586891be0718f9ae`: draft root imports `Std.Buffer` and `Std.Heap`.
- `tests/lean/SepLogic/Fixtures.lean`, blob `2cabc1995755db0114bc55dbfd940ff1ba788c8f`: small raw-pointer-model programs and triples.
- `tests/lean/SepLogic/Buffer.lean`, blob `8e3ba96449781dd5ea4ddf787731f4940bc9b8c8`: allocation/read/write/free/copy/compare proofs and functional-to-raw bridges.
- `tests/lean/SepLogic/Run.lean`, blob `72b77a126443528dc5bd0b790bf2c259c0e38235`: closed/frame examples; explicitly says interpreter/operational adequacy belongs on another branch.
- `tests/lean/SepLogic.lean`, blob `39b8a26c80327cf0ad07b80d358483c9ec3b33e2`: actual exact-head separation-logic test root.
- `src/interp/InterpPaths.ml`, blob `3197a7b0367f2037611f20456d781b2ebb0739e0`: unchanged raw-pointer-dereference rejection.
- `tests/lean/SepLogic/README.md`, blob `b80a670f32e8a4d7e8bba0219013763279b3dbdf`, versus `tests/lean/lakefile.lean`, blob `57668f29144358eca20b1f58ea239fafd2406dd5`: exact-head documentation/tree/build-configuration discrepancies described above.

**Upstream execution/status — exact PR #1352 head.**

- GitHub check runs observed for `75fb1479040d32d43d31b74510167ee3b873d28a`: `lean` failure and `nix` failure completed 2026-09-25; generated-Lean diff, userdocs, and Charon-pin checks succeeded.
- This report did not reproduce those checks or diagnose their failures.

No fresh **execution** evidence was produced by this report.

## Revalidation

For Anneal, begin with dependency identity rather than upstream project marketing:

1. inspect current `anneal/flake.nix` and resolve the selected Aeneas release/tag to a commit;
2. if it still resolves to `ac9f1bc5262a5e4ff1e24ca78617121382202727`, the separation-logic status for Anneal has not changed;
3. if Anneal updates Aeneas, compare the new revision against the exact current-main and PR-head source discriminators below.

For Aeneas upstream, check these high-signal discriminators:

1. root `Aeneas.lean`: whether `Aeneas.SepLogic` is imported on a released/merged revision;
2. `backends/lean/Aeneas/SepLogic/` and `Std/Heap.lean`: whether the spatial model is present on that revision;
3. `src/interp/InterpPaths.ml`: whether `Deref` of `TRawPtr` still raises the unsupported diagnostic;
4. `Std/Primitives.lean`: whether `Result` still carries heap effects and what event signature it uses;
5. `Std/WP.lean`: whether `ispec`/`dispec` still quantify over frames and which semantics justify them;
6. `Std/RawPtr.lean`: the exact pointer/heap model, especially whether it remains slot-based;
7. PR/release metadata and CI: whether #1352 or a successor has merged into a green released revision;
8. `tests/lean/SepLogic/README.md` versus the exact tree and `lakefile.lean`: do not trust prose that disagrees with source.

On an execution-capable surface, use an exact candidate Aeneas revision and preserve artifacts for four tests:

- build the Aeneas Lean library and the complete separation-logic target from a clean Lake state;
- translate a Rust function that merely carries raw pointers without dereferencing them;
- translate a Rust function that dereferences, writes through, and frees/invalidates raw-pointer-modeled storage;
- prove and run, where the implementation supports execution, a small allocation/read/write/free example while retaining the generated LLBC and Lean.

The decisive integration test is not whether a hand-written Lean `RawPtr.read` theorem exists. It is whether the Rust/Charon/Aeneas pipeline maps the relevant source unsafe operation into a semantics whose heap/pointer model is strong enough for Anneal's Rust-level claim, with the correspondence and trust boundary stated explicitly.

If the separation-logic work merges but raw-pointer source translation remains unsupported, record those as two separate facts rather than treating the merge as end-to-end unsafe-Rust support.