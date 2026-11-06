# Open Rust Library Certificate Closure and Consumer Acceptance Protocols

## Summary

Verifying an open Rust library and enforcing sound certificate acceptance require separating six distinct boundaries across theorem shape, entry-domain coverage, callable/generic dependency closure, finite-prefix safety reflection, consumer-owned assumption gating, and concurrent atomic publication:

1. **Library verification versus closed-program verification:** A closed-program theorem fixes the components inside a semantic boundary and proves a property of their whole composition (as in standard CompCert 3.18 `driver/Compiler.v`), whereas an open-module or library theorem universally quantifies over unknown clients or peer modules under an explicit semantic contract (as in RustBelt POPL 2018, Compositional CompCert POPL 2015, and direct open-module refinements `arXiv:2302.12990`). Neither shape dominates the other: open verification requires adequate interface specifications and linking theorems, while closed verification can exploit global invariants that do not factor across module boundaries.
2. **Open Rust library closure and source-bound certificate obligations:** Proving a function over values admitted by a partial mathematical decoder (`decode : Raw -> Option Model`) does not establish safety for arbitrary safe Rust callers. An open-library certificate must establish native entry-domain coverage (`ty_own` / `ty_shr` in RustBelt; `typed_function` in RefinedRust), preserve invariants across all reachable public access paths (illustrated by a 71-function lexical inventory of `zerocopy` `Ptr`/`PtrInner` in `ptr-lexical-inventory.json`), discharge unsafe trait laws (`Project`, `Cast`, `CastExact`, `TryWithError`), and account for callback error recovery (`try_with`), trait objects, and non-guaranteed destructor execution (`core::mem::forget` in `client_domain_probe.rs`).
3. **Functions, generics, and environment certificate closure:** A sound callable certificate must bind `Domain_f`, `StateRel_f`, `StepMatch_f`, `BadReflect_f`, `ReturnRel_f`/`OutcomeRel_f`, `Frame_f`/`Effects_f`, `Dependencies_f`/`EnvironmentRel_f`, and `SpecMeaning_f`. Execution closure must traverse direct calls, monomorphized and default trait methods, associated-type clauses, vtable dispatches, closures, initializers, and implicit `Drop`/unwind paths to a fixed point rather than trusting a producer-supplied callee list or Aeneas's default `can_fail`/`stateful`/`can_diverge` analysis flags (`Interp.ml`, `FunsAnalysis.ml`). Recursive call cycles (`SCC`s) cannot assume all group members safe; they require simultaneous finite-prefix or fuel-indexed induction.
4. **Prefix safety, outcomes, and property transfer (`PrefixCertificate.lean`):** A kernel-checked Lean 4.31.0 development (SHA-256 `70953b0168c85d511a8481f37576a89807a6a84a075cba5c7d1e71e0f748d03c`, five theorems with zero axioms) proves that `stepMatch` and `badReflect` reflect model safety back to source safety (`Certificate.reflectSafety`), enforce initial-domain coverage (`Certificate.coverAllInputs`), and compose heterogeneously across intermediate transition systems (`Certificate.compose`) without assuming complete source safety. A checked counterexample (`stutteringCertificate`, `sourceHasInfiniteChain`, `targetHasNoStep`) proves that finite-prefix safety reflection allows infinite source stuttering (`n → n + 1` mapped to zero `Unit` steps) and therefore transfers neither termination nor liveness without an additional well-founded rank or fairness relation.
5. **Consumer binding, assumption policy, and failure protocol prototype (`support/checker.py`):** A standalone consumer-owned wrapper (SHA-256 `4bf4f2111b72a2ac0c1caaa1754b5edde9f00d8edf1ab97727b6cb0c4bf397db`) binds certificate data to a caller-selected challenge (`support/experiments/challenge.json`), original source hash, model snapshot hash, Lean 4.31.0 binary hash, and an explicit axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`, forbidding `sorryAx` and `native_decide`). Across 38 protocol cases (`support/experiments/mutation-results.json`), it produces the expected 4 acceptances and 34 rejections, plus 5 real Lean assumption/proof controls that reject direct hidden axioms, transitive imported axioms (`HiddenHelper.assumedFalse`), `native_decide`, malformed proofs, and missing theorem declarations.
6. **Concurrent acceptance and publication controls (`support/protocol.py`):** Across 25 multi-process scenarios (`support/results.json`), a cooperative commit-locked consumer protocol verifies that competing producer and consumer generations reject stale epochs before atomic rename publication, that a consumer crashing mid-write (`exit 13` after writing `accepted.partial`) leaves the prior committed `accepted.json` byte-for-byte intact, and that post-commit or same-user tampering is detected on semantic readback while remaining distinct from OS-level sandboxing.

## Applicability

The findings in this package apply to the exact publications, source revisions, and executable prototypes recorded in `REPORT.json`:

- **Open vs closed verification authorities (`support/library-versus-closed-program-verification/`):**
  - RustBelt: Ralf Jung et al., *RustBelt: Securing the Foundations of the Rust Programming Language*, POPL 2018, DOI `10.1145/3158154`, and the `lambda-rust-popl18.tar.gz` archive (SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`).
  - RefinedRust: Zenodo record `21636474` source archive `artifact.tar.gz` (SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`, observed 2026-07-28).
  - Standard CompCert 3.18: `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`VERSION` blob `5fd2882f6f042e89ce617586ce5041f5762c1766`, `driver/Compiler.v` blob `60fc74fec1411216425004f6d63567354e146e9c`).
  - Compositional CompCert: Gordon Stewart et al., POPL 2015, DOI `10.1145/2676726.2676985`.
  - Direct open-module refinements: Ling Zhang et al., *Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules*, `arXiv:2302.12990` (2023).
- **Rust, Charon, and Aeneas source seams:**
  - Rust Reference at `rust-lang/reference@2dafab96d919d6ab2884488e970bf95610ff83eb` (`src/visibility-and-privacy.md`, `src/unsafe-keyword.md`, `src/types/trait-object.md`, `src/destructors.md` blob `0103093cf98bb69825cf840fa04878f6ad545805`, `src/behavior-considered-undefined.md` blob `ff34d0af28ca3ec42f548abf6cd3bce5840a6798`).
  - Charon at `AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`.
  - Aeneas at `AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`.
- **Lean, Rust, and Python execution environments:**
  - Lean `4.31.0` at `leanprover/lean4@68218e876d2a38b1985b8590fff244a83c321783` (`lean` binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`), qualified by the nested-inductive validation fix at `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808`.
  - Native safe-client control compiler: `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `aarch64-apple-darwin`, LLVM 23.1.1).
  - Python `3.9.6` on `macOS-27.0.1-arm64-arm-64bit` (`support/environment.json`).

## Findings

### Library Verification versus Closed-Program Verification

#### Relative semantic closure and open-interface assumptions

Basis: **source** + **documentation** + **derived** (`comparison-matrix.json`, `source-map.json`).

- **Closure is relative to the theorem's semantic boundary:** A closed-program theorem fixes the program components that the semantics treats as the whole program, even when the semantics includes external I/O or nondeterminism. In CompCert 3.18 (`AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `driver/Compiler.v` blob `60fc74fec1411216425004f6d63567354e146e9c`), `Compiler.v` composes translation passes over whole-program values (`transf_c_program`), and the CompCert manual states that while emitted `.o` files can be linked with external libraries, formal semantic-preservation guarantees apply only to whole programs compiled as a whole by CompCert C.
- **Open theorems trade fixed callers for interface contracts and linking theorems:** Compositional CompCert (DOI `10.1145/2676726.2676985`) showed that ordinary whole-program simulations are too weak for separate compilation when modules hold private state (such as stack frames) while exposing pointers across calls; it added language-independent linking semantics and structured simulations carrying module-local invariants. Direct open-module refinement (`arXiv:2302.12990`) relates open source and target modules directly so horizontal and vertical composition do not expose compiler-internal intermediate passes.
- **Proof isolation vs trust isolation in RustBelt (`10.1145/3158154`):** RustBelt separates the fundamental theorem for syntactically typed safe $\lambda_{\text{Rust}}$ code from the semantic verification condition required of every `unsafe` library implementation. Wrapping `unsafe` code in a safe API does not make it trusted by theorem; once the implementation proves its semantic type contract, safe clients compose without reopening the library proof.
- **Three-stage verification pattern and independent modularity axes:** Source modularity and compiler modularity are independent axes. End-to-end verification combines (1) open component proofs against adequate semantic contracts, (2) sound linking/composition theorems, and (3) closing remaining environment assumptions at the final system boundary.

---

### Open Rust Library Closure and Source-Bound Certificate Obligations

#### Native entry domain vs semantic abstraction (`RustBelt` and `RefinedRust`)

Basis: **source** + **normative** + **execution** + **derived** (`source-evidence.json`, `client-probe-results.json`).

- In `lambda-rust-popl18.tar.gz`, RustBelt's semantic type interface distinguishes owned `ty_own(thread, values)` and persistent shared `ty_shr(lifetime, thread, location)`, with `ty_share` converting a full borrow and live lifetime token under a namespace mask into shared ownership, and `ty_shr_mono` providing lifetime contravariance. `typed_body` and `type_soundness` require that syntactically well-typed client entry points inhabit their semantic types before adequacy guarantees thread-safe progress and memory safety.
- In RefinedRust (`artifact.tar.gz`, `functions.v:136–164`), `typed_function` universally quantifies lifetimes, semantic types, specification parameters, call duration, and stack frame, but explicitly requires matching concrete argument layouts (`layout_of`), arbitrary argument locations, initialized owned resources, and precondition/side-condition satisfaction before yielding postcondition resources.
- Consequently, a partial decoder `decode : Raw -> Option Model` that admits only byte sequences with a validity witness cannot by itself justify an `unsafe` operation inside a safe public function: an entry-coverage lemma must prove that every concrete input permitted by the safe Rust signature maps to an admitted semantic state.

#### Bounded pointer access-path inventory and visibility boundaries

Basis: **source** + **normative** (`ptr-lexical-inventory.json`).

The 71-function lexical inventory of `zerocopy` `Ptr`/`PtrInner` (`ptr-lexical-inventory.json`) partitions reachable operations and their required invariant relations:

| Access Class | Examined Source Paths | Required Invariant and Resource Relation |
| --- | --- | --- |
| Ordinary reference entry | `Ptr`/`PtrInner` `from_ref`, `from_mut` | Derive lifetime, allocation liveness, alignment, and semantic validity from a valid incoming Rust reference. |
| Raw/external entry | `PtrInner::new`, `Ptr::from_inner`, assumed alignment/validity, unchecked casts | Caller discharges documented `unsafe` preconditions; private fields prevent arbitrary safe construction. |
| Duplication and reborrow | Shared-only `Copy`/`Clone`, `as_inner`, `reborrow`, shared reborrow | Track shared vs exclusive aliasing; raw `PtrInner` extraction (`as_inner`) does not grant safe dereference authority. |
| Typed observation/transfer | `as_ref`, `as_mut`, `read`, byte/slice conversions, `get_mut` | Establish `Read`, `Immutable`, validity, and alignment invariants for each observed representation. |
| Projection and cast | `transmute`, `recall`/`unify`/`forget` invariants, `cast`/`project`/`tag` | Preserve address, provenance, bounds, and mutation-compatible validity; bind the exact selected trait implementation. |
| DST and slice iteration | Metadata updates, `split_at`/`slice`, trailing slice, cast with leftovers, `iter`/`len` | Preserve wide metadata, bounds, non-overlapping padding-free split preconditions, and error restoration. |
| Callback and error recovery | `try_with`, unchecked exclusive variant, `TryWithError::map` | Enforce callback frame contract and single-inner non-escape law so error recovery restores the unique owning `Ptr`. |
| Layout and projection dictionaries | `KnownLayout`, `HasField`/`HasTag`/`ProjectField`, `Project`/`Cast`/`CastExact` | Bind associated types/constants, const field IDs, and per-implementation unsafe semantic laws. |

Under the [Rust visibility and privacy rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/visibility-and-privacy.md), `#[doc(hidden)]` on a `pub mod` re-export hides documentation without restricting language-level access by downstream safe code; an open-library certificate must cover all `pub`-reachable paths across configured features.

#### Unsafe trait laws, callback restoration, indirect calls, and safe native controls

Basis: **source** + **normative** + **execution** + **derived** (`client_domain_probe.rs`, `client-probe-results.json`).

- **Unsafe traits and callback recovery:** Under [Rust's `unsafe trait` rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/unsafe-keyword.md), `Project` requires the projected byte range to remain within the source allocation with unchanged provenance, `Cast` preserves address, and `CastExact` preserves exact byte extent. In `Ptr::try_with`, the exclusive variant saves the raw inner pointer, invokes the callback, maps any error via `TryWithError` (which requires the error payload to hold at most one copy of the inner pointer and no other non-ZST fields, as in `ValidityError` and `CastError`), and reconstructs the owner; ordinary `FnOnce` typing does not enforce non-escape on the error path.
- **Polymorphism and indirect calls:** In RefinedRust (`generics.v:65, 173–177, 240–284`), `spec_with` indexes specifications by lifetime and semantic-type vectors, `function_ptr` owns a concrete function-table entry and argument layouts, and `type_call_fnptr` verifies thread mask, argument ownership/subtyping, precondition, and live lifetime tokens. Under the [Rust trait-object specification](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/types/trait-object.md), dynamic dispatch requires either the concrete vtable entry set or a universally quantified law over all admissible implementations.
- **Safe native control (`client_domain_probe.rs`):** Compiled and run under `rustc 1.99.0` (`client-probe-results.json`), the probe exercises two safe trait implementations returning `1` and `0` under generic and `dyn` dispatch, const-generic array lengths `0` and `3`, direct mutation of a public struct field to `0`, callback state mutation to `2`, normal `Drop` (`drops=1`), and `core::mem::forget` (`forget=1`), printing `generic=1,0; dynamic=0; const_lengths=0,3; callback=2; drops=1; forget=1` with exit `0`. Because `core::mem::forget` is safe ([`src/destructors.md`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/destructors.md)), soundness can never rely on a value's destructor eventually running unless the value is pinned (`core::pin` drop guarantee) or inaccessible to `forget`.

| Proposed Certificate Record | Minimum Required Content | Composition Gate |
| --- | --- | --- |
| Source domain | Repository/tree, compiler/dependencies, target, feature/cfg/panic settings, roots, expanded public access paths | Every accessible native entry point belongs to the declared domain. |
| Type abstraction | Ownership/shared predicate, decoder identity, lifetime/layout parameters, constructor and mutation laws | Establish native entry coverage and preserve abstraction across all safe paths. |
| Dictionary | Compiler-selected impl/body/associated items, original substitutions, parent laws, const values, checked law proof | Match the actual call dictionary and instantiated source owner. |
| Function | Operational/model relation, pre/normal/unwind/abort effects, footprint/frame, safety-prefix preservation | Callee contract follows from native implementation under stated premises. |
| Indirect call | Function table/vtable or quantified callback set, ABI, ownership, and effect contract | Every selected target satisfies the required call relation. |
| Recursive component | Dependency SCC, guarded/inductive proof rule, invariant resources, all component obligations | No law or safety conclusion is admitted by circular mutual assumption. |
| Link composition | Exact object/source bindings, imported symbol contracts, transformation preservation theorem | Reuse only when dictionary, target, layout, and source meanings match. |

---

### Functions, Generics, and Environment Certificate Closure

#### Callable certificate interface and fixed-point execution closure

Basis: **source** + **normative** + **derived**.

A local callable certificate for function $f$ must bind:

```text
Domain_f(σ, args, instance, env)        -- admissible concrete call states
StateRel_f(σ, μ, instance, env)         -- source-to-model state relation
StepMatch_f                             -- every source call/body prefix is matched
BadReflect_f                            -- every forbidden source prefix is exposed in the model
ReturnRel_f / OutcomeRel_f              -- returned values and accepted defined outcomes
Frame_f / Effects_f                     -- permitted mutations and preserved frame resources
Dependencies_f / EnvironmentRel_f       -- complete set of reachable executable dependencies
SpecMeaning_f                           -- independently required consumer property
```

In Aeneas (`AeneasVerif/aeneas@ca282ec2312a96f6a985a4d23a663690816d3f3e`), [`src/interp/Interp.ml` (lines 52–167, blob `6b6f110c9d38f892fe77685bb2c2fb4c9ab60e3d`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/Interp.ml#L52) computes a declaration dependency graph for extraction, while [`src/llbc/FunsAnalysis.ml` (lines 69–73, blob `7bf693caa8eb8c4dd58cf37b678f792a79dfe3e2`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/llbc/FunsAnalysis.ml#L69) initializes trait-method analysis flags with `can_fail = true`, `stateful = false`, and `can_diverge = false`. Those heuristic translator flags are not sound summaries of arbitrary Rust trait implementations. A sound closure algorithm must traverse from public/selected roots to a fixed point across direct calls, trait/vtable methods, closures, intrinsics, globals/initializers, promoted constants, allocators, FFI calls, and implicit scope-exit/overwrite `Drop` destructors ([`src/destructors.md` line 5, blob `0103093cf98bb69825cf840fa04878f6ad545805`](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/destructors.md#L5)).

#### Charon/Aeneas generic transformations and recursive SCC induction

Basis: **source** + **derived**.

In Charon (`AeneasVerif/charon@cf02e3f228f97ee7be3a415be56989053063326d`):

- [`duplicate_defaulted_methods.rs` (lines 31–39, 82–84, blob `f06bd22f00bd7e735ce7df2f2099e9b7e1948bd1`)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/simplify_output/duplicate_defaulted_methods.rs#L31) copies default trait method bodies into impls and substitutes flattened impl/method binders.
- [`remove_adt_clauses.rs` (lines 1–7, 159–162, blob `3cb85042107304e4513d41a550fd558e05f532ae`)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/simplify_output/remove_adt_clauses.rs#L1) removes ADT trait clauses while preserving associated-type information.
- [`partial_monomorphization.rs` (lines 531–556, blob `08e2c56382579af48ac2db33c808bc3885fc784b`)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/normalize/partial_monomorphization.rs#L531) generates concrete instantiations on demand.
- [`transform_dyn_trait_calls.rs` (lines 1–18, blob `818e87a0ecce4b01ca9056f684dc2a203702bbf5`)](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/transform/normalize/transform_dyn_trait_calls.rs#L1) lowers trait-object calls through vtable function pointers, while Aeneas [`src/PrePasses.ml` (`remove_vtables`, lines 1749–1805, blob `55e8bc208029e6194b038b77d407244447c97557`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/PrePasses.ml#L1749) strips vtable declarations from declaration groups.

| Generic or Dispatch Obligation | Sufficient Derived Closure Rule |
| --- | --- |
| Parametric generic certificate | For all admissible source types, lifetimes, consts, and dictionaries, instantiate the state/prefix/outcome theorem via a proved substitution lemma and semantic trait laws. |
| Per-instance certificate | Bind exact Rust type arguments, selected impl/methods, target layout, and body configuration; never reuse across distinct layouts merely because erased Lean types coincide. |
| Unsafe trait law | Verify the law for the concrete selected implementation or record it as an explicit residual assumption linked to every consuming operation. |
| Default method / associated type | Relate the copied/substituted body and dictionary environment to original trait resolution, preserving recursive calls and cleanup. |
| Specialization / linking | Prove that linked concrete targets satisfy the universally assumed interface and preserve layout and ABI. |
| Dictionary / closure capture | Bind captured environment values/resources and separate closure construction effects from invocation effects. |
| Dynamic dispatch | Cover every permitted vtable target and slot/receiver relation, or reject unresolved dynamic dispatch at admission. |

For a recursive strongly connected component $G$, assuming every member of $G$ is already safe is circular. Sound closure establishes the initial state relation and a single-step preservation and bad-reflection lemma across all constructors (including intra-group recursive calls), then inducts on finite prefix length (or big-step fuel) to discharge the entire group simultaneously without requiring termination for safety.

---

### Prefix Safety, Outcomes, and Property Transfer

#### Checked finite-prefix safety reflection and composition (`PrefixCertificate.lean`)

Basis: **source** + **execution** (`PrefixCertificate.lean`, `lean-check.json`, `lean.stdout`, `lean.stderr`).

Checked directly by Lean `4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) with exit `0`, empty `stderr`, and zero axioms (`lean-check.json`), `PrefixCertificate.lean` defines finite reflexive-transitive reachability `Reach(step, a, b)`, safety `Safe(step, bad, a) := ∀ b, Reach(step, a, b) → ¬bad(b)`, and `Certificate(sourceStep, modelStep, sourceBad, modelBad, R)`:

```text
stepMatch : ∀ s m s', R s m → sourceStep s s' → ∃ m', Reach modelStep m m' ∧ R s' m'
badReflect : ∀ s m, R s m → sourceBad s → ∃ m', Reach modelStep m m' ∧ modelBad m'
```

- `Certificate.mapReach` lifts `stepMatch` by induction to any finite source prefix `Reach sourceStep s s'`.
- `Certificate.reflectSafety` (`no axioms`) proves `Certificate(...) → R sourceInitial modelInitial → Safe modelStep modelBad modelInitial → Safe sourceStep sourceBad sourceInitial` without assuming source safety.
- `Certificate.coverAllInputs` (`no axioms`) proves that if `∀ s, sourceInitial s → ∃ m, modelInitial m ∧ R s m` and `∀ m, modelInitial m → Safe modelStep modelBad m`, then every `sourceInitial` state is safe.
- `Certificate.compose` (`no axioms`) composes `Certificate(stepS, stepM, badS, badM, R_SM)` and `Certificate(stepM, stepT, badM, badT, R_MT)` over the relational product $R_{ST}(s, t) \iff \exists m,\; R_{SM}(s, m) \wedge R_{MT}(m, t)$.

| Relation Form | Condition Required to Reflect Model Safety to Source Safety |
| --- | --- |
| Source-to-model simulation | Universal over all source transitions (`stepMatch`) plus bad-state reflection (`badReflect`); matching only successful runs is insufficient. |
| Model-to-source simulation | Alone can omit a failing source branch; requires an additional source-coverage and bad-reflection direction. |
| Bisimulation | Must include compatible bad-state observations and full initial-input coverage, not merely successful return values. |
| Logical relation | Semantic type membership must entail exclusion of every forbidden finite prefix, not only well-typed terminal values. |
| Contextual refinement | Treating source undefined behavior as arbitrary refinement permission does not reflect target safety back to source safety unless UB is explicitly monitored as `bad`. |

#### Stuttering counterexample, outcome discrimination, and `Atomic.lean` boundary

Basis: **source** + **execution** + **derived**.

- **Checked stuttering witness (`PrefixCertificate.lean`):** `stutteringCertificate` relates `sourceStep(n, n + 1)` on `Nat` to `modelStep := False` on `Unit` with `R n () := True` and `bad := False`. `sourceHasInfiniteChain` (`no axioms`) and `targetHasNoStep` (`no axioms`) prove that a valid finite-prefix safety certificate can map an infinite source execution to zero model steps, demonstrating that safety certificates do not transfer termination or liveness without a well-founded rank on silent steps.
- **Aeneas outcomes vs Rust source outcomes:** Aeneas [`backends/lean/Aeneas/Std/Primitives.lean` (lines 65–110, blob `b5cb07e5f19b9a5e1b39d373ca157ce5ae3627b3`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Primitives.lean#L65) defines `Result` with `ok`, `fail` (`Error.panic`, `Error.undef`, etc.), and `div`, while [`src/interp/InterpStatements.ml` (lines 783–807, blob `e921d3e1411ead14784c1136d104f9aadab18d25`)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/interp/InterpStatements.ml#L783) treats ordinary drops as no-ops, maps `Abort` to `Panic`, and rejects `UnwindResume`. A certificate that permits safe panics while forbidding undefined behavior must keep `panic` and `undef` distinct so `badReflect` rejects `undef` while allowing defined panics.
- **Axiomatic atomics boundary:** Aeneas [`backends/lean/Aeneas/Std/Core/Atomic.lean` (lines 7–13)](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Core/Atomic.lean#L7) declares `AtomicBool` and `AtomicU32` as `axiom` types with `TODO` comments rather than providing a mechanized weak-memory model.

---

### Consumer Binding, Assumption Policy, and Failure Protocol Prototype

#### Consumer-selected challenge, 38 mutation gates, and 5 Lean assumption controls

Basis: **source** + **execution** (`support/checker.py`, `support/run_mutations.py`, `support/experiments/mutation-results.json`).

`support/checker.py` (protocol `arithmetic-consumer-protocol-v1`) validates candidate certificates against an externally hashed consumer challenge (`support/experiments/challenge.json`, SHA-256 `a2d5d3b679bf594afbcdc7838243ebe60de6029e743b87e2d22585b28aff4c5c`). The wrapper hashes `support/experiments/subject.rs`, performs whole-file AST capture, verifies the hash of `support/experiments/ArithmeticModel.lean` and the Lean `4.31.0` binary, and injects only validated integer/opcode data into a consumer-owned proof template before checking that `#print axioms consumerAccepted` contains only `propext`, `Classical.choice`, or `Quot.sound`.

Across 38 protocol test cases (`support/experiments/mutation-results.json`), the suite records **4 acceptances** (the 3 correspondence routes plus re-verified generation-002 cache rebinding) and **34 rejections**:

- **Metadata, domain, and stage rejections (32 cases):** Altered challenge bytes; unsupported profile; modified source/program hash; trivialized property `True`; narrowed, empty, or even-only caller domains; altered semantics tag; mismatched target, flags, generation (`gen-001` vs `gen-002`), instance, callee inventory, toolchain revision, model hash, binary hash, or assumption policy; corrupted model snapshot paired with a weakened goal; invalid opcode or out-of-range byte literal (`256`); conflicting or truncated exports; missing or duplicate trace rows; producer subprocess exit `7`; producer subprocess `0.02 s` timeout cancellation; missing or pending stage status; and attempts to inject raw Lean code or pre-accepted records.
- **Semantic kernel rejections (2 cases):** Changing the multiplier from `5` to `6` or corrupting a single native trace row passes schema/binding gates and is rejected by the Lean 4.31.0 kernel with exit `1`.
- **Five real Lean assumption/proof controls (`support/experiments/assumption-controls/`):**

| Assumption Control Fixture | Lean Kernel Exit | Printed Axiom / Error Observation | Consumer Policy Verdict |
| --- | ---: | --- | --- |
| Direct hidden correspondence `axiom` | `0` | Prints custom `hidden` axiom in `#print axioms` | **Reject** (disallowed axiom) |
| Imported `HiddenHelper.assumedFalse` | `0` | Prints transitive `HiddenHelper.assumedFalse` in `#print axioms` | **Reject** (disallowed transitive axiom) |
| `native_decide` on valid certificate | `0` | Prints `acceptance._native.native_decide.ax_1_1` | **Reject** (native evaluation axiom forbidden) |
| Malformed proof term | `1` | Kernel elaboration error | **Reject** (non-zero kernel exit) |
| Omitted `consumerAccepted` declaration | `1` | Unknown identifier error at `#print axioms consumerAccepted` | **Reject** (missing target theorem) |

---

### Controlled Concurrent Acceptance and Publication Failures

#### Commit-locked generation fencing, partial-write survival, and tampering controls

Basis: **source** + **execution** + **derived** (`support/protocol.py`, `support/results.json`, `support/concurrent-acceptance-publication-controls/results.json`).

`support/protocol.py` (SHA-256 `9acc3831cfcdc1b6b6a49410a7fc3128fb945dd8c70966b2231be46a50ceb82c`) runs real producer, capture, and consumer subprocesses over a 16-entry arithmetic table (`table[i] = i + 1` for `i ∈ 0..15`). Before publishing, the consumer verifies the managed producer process status, the capture subprocess receipt, fixed policy, and input hashes, then acquires an exclusive `commit.lock`, re-reads `challenge.json` to confirm the candidate's generation is still current, writes and `fsync`s `accepted.partial`, atomically replaces `accepted.json`, and `fsync`s the parent directory.

Across 25 executed scenarios (`support/results.json`, `support/runs/run-9168cea43413450ea0c7ffc8db8de38d/`):

- **Process failure and partial-write controls:** Malformed JSON, scalar schemas, boolean table elements (`True` vs `1` rejected by strict type checks), boolean epochs, producer exits `7` and `9`, producer timeout, `SIGTERM` cancellation, partial candidates, and omitted capture steps all fail closed with no `accepted.json` update. When a consumer subprocess writes `accepted.partial` and crashes with exit `13` before `os.replace`, the previous committed `accepted.json` remains byte-for-byte intact and passes `read_accepted`.
- **Concurrent generation and consumer race:** Two producers run in parallel for an older generation and a newer generation; the newer generation commits while the slower older generation is rejected as `stale-generation` under `commit.lock` despite having a valid table. Two concurrent consumers racing on those artifacts likewise accept the current generation and reject the stale one.
- **Metadata and same-user file tampering controls:**

| Mutation or Tampering Control | Observed Protocol Outcome |
| --- | --- |
| Incorrect table entry | Rejected by `semantic_check`; no valid `accepted.json` published. |
| Omitted cleanup effect tag | Rejected by mandatory effect-inventory gate. |
| Mismatched generic, associated-type, dispatch, or callee tag | Rejected by canonical JSON subject-equality gate. |
| Producer overwrites `challenge.json` | Write succeeds on disk (same UID); current-generation check denies publication. |
| Producer overwrites `policy.json` | Write succeeds on disk; fixed-policy digest check denies publication. |
| Producer overwrites checker input | Write succeeds on disk; input-binding hash check denies publication. |
| Producer directly writes forged `accepted.json` | Forged record fails `read_accepted` validation; legitimate consumer atomically replaces it. |
| Post-commit same-user tampering with `accepted.json` table | Write succeeds on disk; subsequent `read_accepted` re-verification rejects the corrupted table. |

## Boundaries

- **Lean 4.31.0 nested-inductive kernel boundary:** As in the companion borrow/pointer prototypes, Lean `4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) predates `leanprover/lean4@a39eab69e1eee9ad38f4efe507907b1026a77808` (PR `14577`), so accepting untrusted producer Lean terms requires a patched checker and full `.olean`/runtime hash verification in addition to `#print axioms` checks.
- **No OS sandboxing in Python wrapper prototypes:** `support/checker.py` and `support/protocol.py` run producer and consumer processes under the same OS user without container/namespace sandboxing. The positive tampering controls in `support/protocol.py` explicitly demonstrate that a same-UID producer can overwrite workspace files unless isolated by an OS-level sandbox.
- **Abstract vs concrete Rust semantics:** `PrefixCertificate.lean` proves generic transition-system theorems (`reflectSafety`, `coverAllInputs`, `compose`, `stutteringCertificate`); it does not formalize a concrete Rust operational semantics or verify Charon/Aeneas translation passes.
- **Incomplete language-feature coverage in bounded inventories:** The 71-function `Ptr`/`PtrInner` lexical inventory (`ptr-lexical-inventory.json`) and basic dictionary controls do not cover arbitrary procedural-macro expansions, generic associated types (GATs), trait specialization, coinductive trait resolution, or weak-memory concurrency (`Atomic.lean` remains axiomatic).

## Evidence

- **Library vs closed-program comparison (`support/library-versus-closed-program-verification/`):**
  - `comparison-matrix.json`, `source-map.json`, `support/library-versus-closed-program-verification/comparison-matrix.json`, `support/library-versus-closed-program-verification/source-map.json`.
- **Open Rust library obligations (`support/open-rust-library-certificate-obligations-8fb35253fbc703cb2cd0997f4efcda76cf9062b6/`):**
  - `ptr-lexical-inventory.json`, `client_domain_probe.rs`, `client-probe-results.json`, `source-evidence.json`, `coverage.json`, `observation-path-normalization.json`, and their copies under `support/open-rust-library-certificate-obligations-8fb35253fbc703cb2cd0997f4efcda76cf9062b6/`.
- **Prefix safety and property transfer (`PrefixCertificate.lean` and `support/prefix-safety-outcomes-and-property-transfer/`):**
  - `PrefixCertificate.lean`, `lean-check.json`, `lean.stdout`, `lean.stderr`, and their copies under `support/prefix-safety-outcomes-and-property-transfer/`.
- **Consumer binding and failure protocol (`support/consumer-binding-and-failure-protocol-prototype/` and `support/experiments/`):**
  - `support/checker.py`, `support/run_mutations.py`, `support/artifact-index.json`, `support/experiments/ArithmeticModel.lean`, `support/experiments/Arithmetic-posthoc.lean`, `support/experiments/subject.rs`, `support/experiments/challenge.json`, `support/experiments/baseline-candidate.json`, `support/experiments/mutation-results.json`, `support/experiments/toolchain-identities.json`.
- **Concurrent acceptance and publication controls (`support/concurrent-acceptance-publication-controls/`):**
  - `support/protocol.py`, `support/results.json`, `support/environment.json`, `support/evidence.json`, `publication-normalization.json`, and the 25 per-scenario run directories under `support/runs/run-9168cea43413450ea0c7ffc8db8de38d/` (and `support/concurrent-acceptance-publication-controls/runs/run-9168cea43413450ea0c7ffc8db8de38d/`).

## Revalidation

1. **Prefix safety theorems (`PrefixCertificate.lean`):** Run `lean PrefixCertificate.lean` using Lean `4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) or a newer release containing `a39eab69e1eee9ad38f4efe507907b1026a77808`. Confirm exit `0`, empty `stderr`, and five `'...' does not depend on any axioms` lines for `Certificate.reflectSafety`, `Certificate.coverAllInputs`, `Certificate.compose`, `sourceHasInfiniteChain`, and `targetHasNoStep`.
2. **Safe client domain probe (`client_domain_probe.rs`):** Compile and execute `client_domain_probe.rs` with `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`) and verify exit `0` and output `generic=1,0; dynamic=0; const_lengths=0,3; callback=2; drops=1; forget=1`.
3. **Consumer binding and assumption mutation suite (`support/run_mutations.py`):** Run `LEAN_BINARY=/path/to/lean-4.31.0/bin/lean python3 -B support/run_mutations.py` in a scratch copy and verify all 38 protocol verdicts (4 acceptances, 34 rejections) and all 5 assumption/proof control rejections in `support/experiments/mutation-results.json`.
4. **Concurrent acceptance and publication suite (`support/protocol.py`):** Run `python3 -B support/protocol.py experiment --root <scratch-runs>` and verify all 25 scenario outcomes, confirming that stale generations and crashed partial writes (`exit 13`) never overwrite a committed `accepted.json` and that `read_accepted` rejects post-commit tampering.
