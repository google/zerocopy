# Aeneas semantic omissions relevant to unsafe Rust at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the ordinary functional backend selected by Anneal deliberately omits several operational dimensions that unsafe-Rust proofs can depend on. The most important are not hidden implementation details: Aeneas documents this backend as a translation of a subset of safe Rust and says unsafe and concurrent Rust require the developing separation-logic path.

The current reference corpus already establishes the memory-resource side of that boundary. Ordinary references and `Box<T>` are functionalized into pure values and backward functions; the final proof-facing model does not retain allocation identity, ordinary reference identity, a Rust pointer-provenance relation, or a general heap with byte-level initialization and arbitrary aliasing state. Raw-pointer types can cross signatures, but raw-pointer dereference is rejected at this pin. This report does not duplicate those reports. It completes the broader unsafe-Rust omission inventory by connecting that resource boundary to effects, concurrency, I/O, and nondeterminism.

The pure function effect summary is intentionally small: generated functions are classified for failure, divergence, and recursion. Earlier LLBC analysis also computes a coarse `stateful` bit, but the final `Pure.fun_effect_info` contains no general event trace, I/O state, scheduler, atomic memory-order state, allocation map, or nondeterministic-choice structure. Concrete standard-library models confirm that this is a semantic abstraction, not only an absent API: `std::io::stdio::_print` is modeled as `ok ()`, erasing its output effect; selected atomic types are axiomatic Lean types with TODO markers rather than a concurrent atomic semantics; unchecked slice operations over raw pointers fail until the model becomes “more stateful”; and Rust `Drop` statements are no-ops by default unless the separate drop-evaluation option is enabled.

Aeneas does contain one explicit environment-dependent pure primitive, `GetTarget`. It is documented as fallible and axiomatized so that nothing can be deduced from its returned compilation-target string. That is a useful example of conservative abstraction, but it is not a generic nondeterminism or external-effect model. Similarly, an external model can deliberately choose a semantics for an opaque Rust item; name matching to such a model does not establish that the model preserves all Rust observable behavior.

For Anneal, the practical rule is claim-specific. A proof over ordinary Aeneas output can establish properties in the modeled pure semantics. It cannot, without an additional correspondence argument or stronger backend, justify a Rust-level claim whose truth depends on erased allocation/provenance/initialization facts, destructor side effects, concurrent interleavings or memory ordering, I/O traces, environmental interaction, or other nondeterministic behavior. These omissions should be treated as explicit proof obligations or unsupported scope, not silently inherited from a successful Lean proof.

No fresh Aeneas, Charon, Lean, or Rust execution was performed. Evidence is exact pinned source plus current exact-revision reference reports whose underlying source/artifact evidence is independently identified below.

## Applicability

Primary subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- relationship: the Aeneas release selected by current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

This report concerns the **ordinary functional translation** and Lean model library used by that release. It does not describe the developing separation-logic backend as though it were already the semantics of the selected release. The current corpus report `aeneas-separation-logic-status-2026-09-26` owns that implementation-status question.

The issue item uses “semantic omissions” broadly. Here, an omission means that the selected proof-facing semantics either erases a Rust distinction, replaces an operation with a deliberately simpler model, rejects the relevant operation, or leaves the behavior to an external/axiomatic model. An omission is not by itself an Aeneas bug. Many are intentional abstractions that are appropriate for the safe functional subset. They become proof-critical when Anneal wants a theorem whose Rust interpretation depends on the erased distinction.

This report also distinguishes **unsupported** from **abstracted** behavior. Raw-pointer dereference is explicitly unsupported by the ordinary functional interpreter. Printing, by contrast, has a concrete Lean model that succeeds while discarding the output effect. Both are outside a proof of faithful Rust I/O/memory behavior, but for different reasons.

## Findings

### The advertised semantic domain excludes general unsafe and concurrent Rust

The root README states that Aeneas “currently functionalizes a subset of safe Rust” and that the project is extending the model with separation logic to support unsafe and concurrent code. The same section lists unsafe code and concurrency as current limitations of the ordinary functional path.

This is the governing applicability statement for the selected release. Individual representable types or accepted fixtures do not widen it to a general unsafe/concurrent semantics.

Basis: pinned upstream **documentation**.

### Allocation identity and ordinary reference identity are intentionally absent from the pure model

The current exact-revision resource-semantics report already establishes this boundary from pinned source. Ordinary Rust references become their referent values in forward types; mutable effects are represented by backward functions. `Box<T>` becomes the translated `T`. The final pure language therefore does not expose an ordinary reference object or heap allocation identity for those values.

This abstraction supports functional reasoning about safe ownership-disciplined code. It cannot distinguish two source executions solely by which allocation holds an otherwise equal value, nor can it express a Rust-level theorem whose premise is “these two pointer-like values designate this same allocation” unless some stronger model supplies that relation.

Basis: current exact-revision **corpus source synthesis**, grounded in `SymbolicToPureTypes.ml` and `Pure.ml`.

### Rust pointer provenance is not represented by Aeneas `mplace` provenance metadata

The current resource-semantics report also records a terminology trap. Aeneas has `mplace` metadata described as provenance information for generated names and symbolic/source origin. It is not a Rust pointer-provenance relation governing which allocation a pointer may access or how provenance changes across casts and exposure.

Raw-pointer types survive as `TRawPtr`, but `Pure.ml` explicitly says they do not make sense in the pure world at this pin and are retained so signatures can be represented while preventing unsupported uses. Raw-pointer dereference is rejected by the interpreter.

A Rust proof that depends on strict/exposed provenance, pointer-to-allocation association, or provenance-preserving transformations therefore needs semantics outside this ordinary pure representation.

Basis: pinned **source** plus current exact-revision resource/raw-pointer reports.

### Partial initialization is not a proof-facing heap property in the ordinary backend

The ordinary pure model has no general byte-addressed heap whose cells carry allocation and initialization state. Safe values are translated as mathematical/pure values, while unsupported raw-pointer memory operations do not acquire a hidden byte-level semantics merely because their types are representable.

Consequently, properties such as “these bytes are allocated but not initialized,” “this typed value has not yet become valid,” or “this write initializes exactly this region of an allocation” are not facts a later Lean proof can recover from the ordinary functional output alone. This statement does not assert that every source use of an initialization-related standard-library type is rejected; an external or specialized model may abstract a particular API. The narrower point is that the selected backend does not expose general Rust initialization state as a proof resource.

Basis: **derived** from the pinned pure/resource model and its absence of a general heap; this report makes no exhaustive `MaybeUninit` API claim.

### The final pure effect summary is not a general operational-effect algebra

`Pure.fun_effect_info` contains three booleans: `can_fail`, `can_diverge`, and `is_rec`. These control result wrapping and recursive/partial-function extraction. They do not encode I/O traces, allocation/deallocation events, destructor events, thread creation, atomic ordering, scheduler choices, randomness, clocks, filesystem state, or other external effects.

Earlier `FunsAnalysis.ml` also computes a coarse `stateful` bit while analyzing LLBC. That analysis is used by translation machinery, but it likewise does not define a Rust operational event semantics. The source comments explicitly note that not all analyzed information is used to adjust extraction.

Thus “Aeneas knows this function can fail/diverge/is stateful” must not be promoted into “Aeneas models every Rust effect relevant to this function.”

Basis: pinned **source** in `Pure.ml` and `FunsAnalysis.ml`.

### Destructor behavior is abstracted away by default

`Config.ml` initializes `drop_as_no_op = true`. `InterpStatements.ml` implements a Rust `Drop` statement as immediate `Unit` when that option is set. The alternate path calls `drop_value`, which updates the symbolic place/borrow state; it still must not be conflated with arbitrary Rust destructor side effects without a separate correspondence argument.

The current support/failure report already calls out this configuration boundary. For Anneal, a theorem whose source-level meaning depends on a `Drop` implementation performing I/O, mutating global state, releasing an external resource, or otherwise producing observable behavior cannot rely on the default no-op translation as faithful evidence of that effect.

Basis: pinned **source** in `Config.ml` and `InterpStatements.ml`, plus current corpus synthesis.

### The pinned model for standard output deliberately erases output

The Lean standard-library model contains:

```lean
@[rust_fun "std::io::stdio::_print"]
def std.io.stdio._print (_ : core.fmt.Arguments) : Result Unit := .ok ()
```

The model ignores the formatted arguments and returns success. A proof using this model can reason that the modeled call succeeds; it cannot infer the bytes emitted to stdout, ordering relative to other output, failure behavior of a real output device, or any external observer's trace.

This is a concrete witness that some source effects are intentionally abstracted rather than merely absent from the implementation. It should not be generalized to every Rust I/O API: the standard-model inventory is finite and revision-specific, and unmatched APIs may be opaque or require user models.

Basis: pinned Lean model **source** in `Aeneas/Std/Std/Io.lean` and current external-model inventory.

### Concurrency and atomic memory ordering are outside the ordinary functional semantics

The root README explicitly excludes concurrent code from the current functional model. The selected Lean standard library registers `AtomicBool` and `AtomicU32` as axiomatic types with TODO markers. Type registration alone supplies no operational semantics for inter-thread communication or Rust atomic memory ordering.

`FunsAnalysis.ml` also treats trait-method calls conservatively for failure but not as divergent or stateful; this is a translation-analysis heuristic, not a scheduler or memory model. Nothing in the ordinary pure effect summary records thread identities, interleavings, happens-before edges, or atomic orderings.

Therefore an Anneal theorem about races, synchronization, relaxed/acquire/release/SeqCst behavior, or concurrent linearization cannot be justified by the ordinary selected backend merely because an atomic type name is representable.

Basis: pinned **documentation** and Lean model **source**; the operational consequence is **derived**.

### Raw-pointer library models expose the same missing-state boundary

In the selected Lean `Slice` model, `get_unchecked` and `get_unchecked_mut` over raw pointers both return `fail .undef`. The comments say they should be updated once the computation model becomes “more stateful.”

That is direct upstream evidence that the ordinary computation model lacks state needed for these unsafe pointer operations. The current raw-pointer report separately establishes that general raw-pointer dereference is rejected by the symbolic interpreter.

This is a stronger boundary than “the proof library has not been polished.” At this pin, the selected semantics intentionally refuses to pretend that a pure pointer token plus current result monad is enough to model the operation.

Basis: pinned Lean model **source** plus current exact-revision raw-pointer report.

### `GetTarget` is an explicit unknown environment value, not a generic nondeterminism semantics

`Pure.GetTarget` exists for multi-target dispatch. Its source comment says the function is fallible and axiomatized and that “nothing can be deduced from its output.” This is a conservative way to expose one environment-dependent source of variation without inventing a particular target.

That special primitive should not be generalized into a model of all Rust nondeterminism. The ordinary pure effect metadata has no random-choice, scheduler, clock, I/O-event, or environment-transition constructor. When an external function is opaque or modeled, its model supplies whatever semantics the proof sees.

For Anneal, nondeterministic/environmental source behavior is therefore a per-operation/model question unless and until a stronger operational semantics is selected.

Basis: pinned **source** in `Pure.ml` plus **derived** scope distinction.

### External models are semantic assumptions, not automatic preservation theorems

The current external-model report establishes that the selected Lean registry contains hundreds of name-pattern registrations and that matched Rust items are redirected to corresponding Lean definitions. It also emphasizes the trust boundary: matching an item by Rust name does not prove that the Lean model implements every relevant Rust behavior.

The `_print` no-op and atomic-type axioms are concrete examples. A model can intentionally forget effects or representation. Anneal therefore needs to include model adequacy in the Rust-to-Lean correspondence argument for any model whose behavior matters to the theorem.

Basis: current exact-revision **corpus source synthesis** plus the pinned model witnesses above.

### The omission boundary is claim-specific rather than all-or-nothing

These facts do not imply that the ordinary Aeneas backend is unsuitable for every unsafe-adjacent theorem. If a property is insensitive to an erased distinction, a separate abstraction argument may establish that the pure theorem is sufficient. Conversely, even safe-looking code can call a model whose erased effect matters to the desired source claim.

A useful Anneal proof ledger should therefore state, for each theorem:

- which Rust/LLBC operations are in scope;
- which information the selected Aeneas path preserves, erases, abstracts, or rejects;
- which external models are used and what semantics they supply;
- whether the theorem depends on allocation/provenance/initialization, destruction, concurrency, I/O, or nondeterminism; and
- what correspondence theorem or explicit assumption bridges any such gap.

This turns the semantic omissions into reviewable proof obligations instead of an implicit global trust assumption.

Basis: **derived** synthesis from the pinned semantics and current Anneal reference principles.

## Boundaries

- No fresh Charon, Aeneas, Lean, Rust, or OS execution was performed.
- This report does not claim that Aeneas is unsound for its advertised safe functional subset.
- It does not claim every source API involving allocation, initialization, I/O, atomics, or unsafe code is rejected. External and specialized models can abstract particular APIs.
- The absence of a general heap/resource model is not the same as absence of internal borrow/loan machinery. Aeneas uses richer symbolic state while translating safe borrows; that state is not emitted as a general proof-facing Rust heap semantics.
- `mplace` provenance/source-origin metadata is not treated as Rust pointer provenance.
- `AtomicBool` and `AtomicU32` being registered as axiomatic types does not establish whether every atomic operation is absent, modeled, or opaque. The claim here is only that this type registration does not provide concurrent memory-order semantics and that concurrency is explicitly outside the ordinary functional support statement.
- `_print := ok ()` is a concrete I/O witness, not an exhaustive I/O inventory.
- `GetTarget` is a concrete unknown-environment witness, not evidence of a generic nondeterministic transition system.
- Default no-op `Drop` establishes an abstraction in the selected default configuration. Behavior under `-eval-drops` is a separate mode and is not claimed here to reproduce arbitrary destructor effects.
- The developing separation-logic path may add resource semantics. Its current status is a separate report and must be revalidated if Anneal selects it in the future.
- Formal Aeneas papers and mechanized models are not treated as blanket proofs that this exact executable/model-library revision preserves every omitted Rust behavior.

## Evidence

Evidence was revalidated or incorporated on 2026-09-27.

**Primary source — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.**

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: selected functional model is a subset of safe Rust; unsafe and concurrency are limitations intended for separation-logic work.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: pure builtins; `TRawPtr` boundary; `GetTarget`; final `fun_effect_info` with failure/divergence/recursion rather than a general operational-effect trace.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: reference/Box functionalization and pure signature construction used by the current resource-semantics report.
- `src/llbc/FunsAnalysis.ml`, blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`: coarse LLBC failure/stateful/divergence analysis and its documented limitations.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: default `drop_as_no_op = true`.
- `src/interp/InterpStatements.ml`, blob `97452f658bbd773c16386592d31b0bf61da8891f`: Drop no-op branch under the default and alternate symbolic drop path.
- `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: raw-pointer-dereference rejection and internal path/borrow machinery, as indexed by current resource/raw-pointer reports.
- `backends/lean/Aeneas/Std/Std/Io.lean`, blob `c32f89b32297e472aa0128509b572e76cf72a523`: `_print` model ignores arguments and returns `ok ()`.
- `backends/lean/Aeneas/Std/Core/Atomic.lean`, blob `d686f3154fe6da9c2b4c1d6694764a1005332958`: TODO axioms for selected atomic types.
- `backends/lean/Aeneas/Std/Slice.lean`, blob `cab42e4f6ab768e97df8f5d3d9a5de73079a785c`: raw-pointer `get_unchecked` models fail with `.undef` pending a more stateful computation model.

**Current exact-revision reference reports used to avoid duplicating narrower inventories.**

- `reports/aeneas-resource-semantics-nightly-2026-06-03/REPORT.md`, blob `95614a518815fdba251e948aca90cce7dca0d154`: allocation/reference identity, pointer-provenance distinction, initialization/heap-resource boundary, internal borrow state versus proof-facing pure semantics.
- `reports/aeneas-raw-pointers-nightly-2026-06-03/REPORT.md`, blob `62e9779e7c7d206ae648386286efd1e776c112c8`: representable raw-pointer types versus unsupported raw-pointer execution.
- `reports/aeneas-rust-support-failure-matrix-nightly-2026-06-03/REPORT.md`, blob `615717924f2a503c0ca0b5f37ff0ef38d3a032e5`: advertised support boundary, default drop abstraction, warning/error/failure classes.
- `reports/aeneas-external-models-nightly-2026-06-03/REPORT.md`, blob `cfc981a9430447e51cefb2fc57dbe30738ec5def`: name-matched external-model mechanism and semantic trust boundary.
- `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03/REPORT.md`, blob `ca377b8322f33f2ded9c23b0cfbaacdba28ebd`: reference/Box functionalization and backward-function value flow.
- `reports/aeneas-separation-logic-status-2026-09-26/`: current status of the stronger resource-oriented path; this report deliberately does not project that work into the selected functional release.

Evidence roles are **documentation**, **source**, **current corpus synthesis**, and **derived** consequences. There is no fresh **execution** evidence.

## Revalidation

For a later Aeneas pin, first resolve which backend Anneal actually selects. If it is still the ordinary functional backend, recheck these discriminators:

1. root support statement for unsafe/concurrent code;
2. `Pure.fun_effect_info` and pure AST constructors for newly represented effects/resources;
3. `SymbolicToPureTypes.ml` for reference, Box, region, and raw-pointer translation;
4. `InterpPaths.ml` for raw-pointer execution support;
5. `Config.ml` and `InterpStatements.ml` for Drop semantics and defaults;
6. exact Lean models for output, atomics, allocation/pointers, and any other source effects Anneal depends on;
7. the external-model registry and each theorem-relevant model's implementation;
8. the separation-logic backend status if Anneal begins selecting it.

On a capable execution surface, add an end-to-end omission probe suite whose acceptance criteria are semantic rather than “translation succeeded”:

- **allocation/provenance:** two equal-valued allocations plus raw-pointer identity/provenance-sensitive operations;
- **initialization:** an initialization-sensitive unsafe pattern with a matched safe control;
- **Drop/effects:** a destructor that changes an observable modeled state or emits output, tested under default and `-eval-drops` modes;
- **I/O:** a tiny `_print` call, preserving Rust behavior and generated Lean/model call so the intentional no-op abstraction is explicit;
- **concurrency/atomics:** a minimal atomic ordering example, expected to remain outside the ordinary backend until a real concurrent semantics exists;
- **environment/nondeterminism:** a multi-target-dispatch example exercising `GetTarget` and one genuinely external/nondeterministic API under an explicit model.

Preserve Rust, LLBC, generated Lean, model identities, diagnostics, commands, exit statuses, and proof assumptions. The objective is not to force unsupported programs through the translator. It is to maintain a machine-checkable boundary between source properties proved by the selected semantics and source properties that still require a stronger model or explicit assumption.
