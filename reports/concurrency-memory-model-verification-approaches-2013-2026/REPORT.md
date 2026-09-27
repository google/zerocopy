# Concurrency and memory-model verification approaches

## Summary

Concurrent verification has at least four separate layers that must not be collapsed into one claim:

1. a **language memory model** defines which executions are allowed and which executions are undefined;
2. a **deductive program logic** proves properties of all executions admitted by a chosen model or fragment;
3. an **automatic model checker** explores executions of a concrete analysis instance under a chosen model; and
4. a **source-to-model correspondence** justifies applying the proof or model-checking result to the source program that matters.

The examined systems make these boundaries explicit. Rust's pinned atomic documentation says that its atomics currently follow C++20's rules, translated from C++'s object-based model to Rust's access-based model, and that data races are undefined behavior. Relaxed Separation Logic (RSL) extends concurrent separation logic with weak-memory-aware proof rules and transfers ownership through release/acquire synchronization. Strong Logic for Weak Memory supplies an operational characterization of a C11 release-acquire fragment so that higher-order Iris reasoning can be applied to that weak-memory semantics. GenMC instead performs stateless model checking under explicit memory models such as RC11, IMM, and LKMM. RustMC carries the model-checking approach to Rust by compiling Rust to LLVM IR and adapting GenMC to Rust-specific lowering behavior.

These techniques are complementary, not interchangeable. A proof in an interleaving logic does not establish weak-memory correctness unless the logic is sound for the relevant weak-memory model. A model checker does not establish an unbounded source-level theorem merely because it explores executions exhaustively within its configured analysis. A source-level Rust claim does not follow automatically from an LLVM-level result unless the lowering and memory-model correspondence needed by that claim is justified.

For Anneal, the reusable rule is simple: future concurrency support must name the memory model and fragment, preserve the concurrency-relevant source operations in translation, and make any proof/model-checking boundary explicit. If those obligations cannot be established, the verifier should reject the unsupported construct rather than silently reason in a stronger sequential model.

## Applicability

The Rust-specific baseline is `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler revision behind the Anneal-era `nightly-2026-05-31` toolchain. Its `library/core/src/sync/atomic.rs` documentation is the direct source for the Rust atomic-model statements in this report. It says that Rust atomics **currently** follow C++20 atomic rules, excluding consume ordering, after translating C++'s object-based terminology to Rust's access-based memory model.

The verification approaches are historical technique references rather than one mutually compatible stack:

- RSL is the OOPSLA 2013 logic described by DOI `10.1145/2509136.2509532`. Its official project page describes a C11 relaxed-memory logic and records an erratum tied to the then-current C11 formalization.
- Strong Logic for Weak Memory is the ECOOP 2017 result at DOI `10.4230/LIPIcs.ECOOP.2017.17`. It targets the RA+NA fragment: release/acquire atomics plus ordinary non-atomic accesses.
- GenMC is represented by its CAV 2021 tool paper, DOI `10.1007/978-3-030-81685-8_20`, together with the current project page that states support for RC11, IMM, and LKMM.
- RustMC is represented by its peer-reviewed FORTE 2026 paper, DOI `10.1007/978-3-032-28187-6_14`. It extends the GenMC approach to Rust programs through LLVM IR.

The report uses these systems to identify verification patterns and proof obligations. It does not claim that C11, RC11, C++20, Rust, IMM, LKMM, or a hardware memory model are equivalent. It also does not claim that the original RSL or Strong Logic theorems directly cover current Rust.

## Findings

### The memory model is part of the theorem, not an implementation detail

The pinned Rust atomic documentation makes the semantic boundary explicit. Rust atomics currently use C++20 rules with a Rust-specific translation from objects to accesses. A data race is a pair of conflicting, non-synchronized accesses when at least one access is non-atomic; Rust treats such a race as undefined behavior. Rust also inherits a mixed-size restriction for non-synchronized conflicting atomic accesses: overlapping atomic accesses must either be disjoint, cover exactly the same bytes with the same size, or both be reads.

These rules determine the execution set to which a verification result can apply. A proof that assumes sequential consistency may rule out behaviors that a weaker model admits. Conversely, a proof against a weak model can rely only on order and visibility guaranteed by that model.

This separates two questions that are easy to conflate:

- **atomic API semantics:** what an `Acquire`, `Release`, `Relaxed`, `AcqRel`, or `SeqCst` operation means; and
- **verification method:** how a proof or analysis establishes a property over executions admitted by those semantics.

A verification technique does not repair a mismatched memory model. Its soundness theorem must already connect it to the relevant execution semantics.

Basis: **source** — `rust-lang/rust@14210df...`, `library/core/src/sync/atomic.rs`; **derived** — theorem-boundary consequence.

### RSL turns synchronization into controlled resource transfer

RSL is a deductive program logic for C11 relaxed memory. Its official project page describes it as an extension of concurrent separation logic with proof rules for C11 atomic accesses. Threads may access non-atomic memory only when they own the corresponding resource. Atomic synchronization can transfer ownership between threads.

The direction of transfer mirrors release/acquire synchronization:

- a release access can transfer ownership away;
- an acquire access can obtain transferred ownership; and
- a relaxed access does not transfer ownership in RSL.

This is a useful proof pattern because it connects a low-level memory-ordering event to a local resource invariant. Instead of globally enumerating interleavings, a thread proves that it owns the non-atomic state it touches and that synchronization publishes or acquires the resources required by the protocol.

The pattern does not imply that RSL's 2013 C11 model is the current Rust memory model. The RSL project itself records an erratum where a behavior attributed to a 2011 C11 formalization did not match the relevant C standard paragraphs. That is direct evidence that memory-model version and formalization identity matter.

Basis: **documentation/source** — official RSL project page and paper identity; **derived** — portability boundary to current Rust.

### An interleaving logic needs a weak-memory semantics before it can prove weak-memory programs

Iris is a higher-order concurrent separation-logic framework. The Strong Logic for Weak Memory project explains the obstacle to applying it directly to C11: Iris is built for an operational interleaving semantics, while C11 weak memory was specified declaratively/axiomatically.

Strong Logic addresses this mismatch by giving an operational characterization of the C11 RA+NA fragment and instantiating Iris with that semantics. The authors then derive higher-order variants of GPS and RSL and report mechanized Coq proofs of RA+NA examples.

The reusable point is not that every weak-memory model should be converted to an interleaving model. It is that the logic and the memory model need an explicit bridge. A powerful concurrent separation logic does not, by itself, establish that its primitive steps represent all behaviors permitted by a weak language model.

This suggests three independent proof obligations for a future verifier:

1. define the concurrent source semantics to be preserved;
2. establish that the proof logic is sound for those semantics, directly or through a proved characterization; and
3. prove the program property inside that logic.

Skipping the second step silently replaces the source memory model with the logic's execution model.

Basis: **documentation/source** — Strong Logic for Weak Memory project page and ECOOP 2017 paper identity; **derived** — three-obligation decomposition.

### Deductive weak-memory logics buy compositionality, but only inside their supported fragment

RSL and the Iris-based RA+NA work illustrate why deductive logics remain attractive for concurrency. Separation logic supports local reasoning: a thread can prove facts about resources it owns while invariants or synchronization protocols control shared state. Higher-order frameworks such as Iris add reusable abstractions, ghost state, and invariant mechanisms that can support proofs of concurrent libraries and their clients.

The corresponding cost is semantic specificity. A program logic is sound for some language/model fragment under some rule set. Strong Logic's project page names RA+NA rather than all of C11. RSL distinguishes release/acquire from relaxed accesses. The proof cannot silently grow to cover fences, atomics, mixed-size accesses, thread primitives, progress properties, or memory-model behaviors that its soundness result did not include.

For verification architecture, “we use separation logic” is therefore not a concurrency specification. The durable specification is the pair **(memory-model fragment, logic soundness theorem)** plus the program proof performed under that theorem.

Basis: **source/documentation** — RSL and Strong Logic project pages; **derived** — architectural consequence.

### GenMC represents a different assurance mode: systematic execution exploration under an explicit model

GenMC is a stateless model checker rather than a deductive program logic. Its project page says that it verifies concurrent C/C++ programs under RC11, IMM, and LKMM and that its exploration algorithm is parametric in the memory model. Subject to stated basic model conditions, the project describes the algorithm as sound, complete, and optimal for the executions in its analysis: it explores every consistent execution exactly once and avoids inconsistent executions.

This assurance mode has different strengths:

- it can automatically search difficult interleaving/weak-memory behavior;
- an error comes with a concrete offending execution rather than only a failed proof obligation; and
- the selected memory model is an explicit analysis parameter.

It also has a different boundary. Exhaustiveness is with respect to the analyzed program and the tool's exploration/configuration, not a blanket theorem about every input, every loop count, every environment, or every source program. GenMC's own project page describes optimizations such as automatic spin-loop bounding, which is another reason to record the concrete analysis configuration when using a tool result as evidence.

Model checking and deductive verification therefore answer different questions. A model checker can be excellent for finding weak-memory counterexamples or validating a bounded client; a compositional proof can establish a reusable theorem for a whole input class. Neither subsumes the other without an additional argument.

Basis: **documentation/source** — GenMC project page and CAV 2021 paper identity; **derived** — comparison with deductive proof.

### RustMC moves model checking toward Rust, but the source-to-LLVM bridge remains part of the trust story

RustMC extends GenMC to concurrent Rust. The FORTE 2026 publication describes a workflow that targets unmodified Rust programs, uses the common LLVM IR layer shared by Rust and C/C++, and handles Rust-specific lowering issues such as threading operations, memory intrinsics, and uninitialized accesses. Its reported case studies include unsafe Rust, C/C++ FFI dependencies, and incorrect atomic use, and it evaluates behavior against Loom tests and production-level concurrent data structures.

That is directly relevant to a future Rust verifier because it demonstrates a practical automatic-analysis path that spans Rust plus foreign C/C++ dependencies. But LLVM-level exploration creates a distinct correspondence obligation. A result about the lowered program establishes the source-level property only to the extent that:

- the Rust compiler lowering preserves the concurrency semantics relevant to the property;
- the model checker interprets the resulting IR operations under a memory model appropriate for that lowering; and
- source behaviors that disappear, are transformed, or are represented by intrinsics are handled soundly by the front-end/instrumentation layer.

RustMC explicitly reports engineering work in those translation boundaries; they are not bookkeeping details. For Anneal, the analogous lesson is that concurrency correctness cannot be recovered after a translation erases or misrepresents atomics, thread operations, fences, mixed-size accesses, or the distinction between atomic and non-atomic memory.

Basis: **documentation/source** — FORTE 2026 RustMC publication record; **derived** — source-to-IR trust decomposition.

### Concurrency proof obligations should remain factored instead of becoming one “thread safety” bit

The examined evidence supports a useful factorization for a verifier or audit:

- **access validity and aliasing:** whether each access is otherwise legal;
- **atomicity and access size:** which accesses are atomic and which byte ranges they cover;
- **memory ordering:** how operations contribute to happens-before or another model relation;
- **race freedom:** whether conflicting non-atomic/atomic accesses are permitted;
- **shared-state protocol:** which thread owns or may mutate which logical resource;
- **functional refinement:** whether the concurrent object has the intended abstract behavior;
- **progress:** lock-freedom, wait-freedom, starvation, fairness, or termination as separately specified properties; and
- **translation adequacy:** whether the analyzed model preserves the source operations and behaviors relevant to the above claims.

Rust's own atomic documentation illustrates why the factors differ. Available Rust atomics are documented as lock-free, but not necessarily wait-free. `Relaxed` operations provide atomicity without release/acquire synchronization. Mixed-size overlap can be invalid even when each individual access is atomic. None of these facts alone establishes that a concurrent data structure implements its intended abstract operation.

Collapsing the factors into one boolean obscures which theorem failed and makes unsupported semantics easier to miss.

Basis: **source** — pinned Rust atomic documentation; **derived** — verification-factor decomposition.

### A future Anneal concurrency path should fail closed at the translation boundary

Anneal's current principles require verification to fail closed and require Rust claims to be justified by Rust semantics. If concurrency becomes in scope, the translation must therefore preserve or reject every source construct that can change the execution set relevant to the theorem.

At minimum, an adequacy review should account for:

- thread creation/join and their synchronization effects;
- atomic versus non-atomic access identity;
- access width and overlap;
- every supported atomic ordering and fence;
- compare-exchange success/failure semantics;
- shared mutable state and ownership/resource invariants;
- external/FFI synchronization effects;
- panic/unwind/destruction interactions that cross thread boundaries when material; and
- any compiler or target model assumed between source Rust and the verified semantics.

A sequential functional model can still be useful for code that is proved not to exercise concurrent behavior. It is not a conservative model of arbitrary concurrent Rust merely because the translated functions return the same values on one schedule. If the translator cannot establish that the source program lies inside its supported concurrency-free fragment, rejection is safer than silently selecting one interleaving.

Basis: **derived** from the examined memory-model/proof-method boundaries and current Anneal fail-closed principles.

## Boundaries

- **Known not to apply:** RSL's 2013 C11 result is not a theorem about current Rust. Its project page records a memory-model-related erratum, and Rust uses a C++20-derived, access-based model.
- **Known not to apply:** Strong Logic for Weak Memory is scoped to RA+NA; it should not be cited as coverage of every C11/C++/Rust atomic feature.
- **Known not to apply:** ordinary Iris reasoning over an interleaving semantics does not automatically prove correctness under an unrelated weak-memory semantics. The Strong Logic work exists precisely to provide such a bridge for its fragment.
- **Known not to apply:** a GenMC or RustMC run is not, merely by being exhaustive over its explored execution set, an unbounded theorem for arbitrary inputs or arbitrary source programs.
- **Not examined:** this report does not establish the exact current correspondence between Rust's documented C++20-derived atomic model, LLVM's concurrency model, RC11, IMM, or any hardware memory model.
- **Not examined:** no GenMC, RustMC, Loom, Miri, Herd, litmus suite, Rocq/Coq proof, or weak-memory executable experiment was run in this investigation.
- **Not examined:** the report does not survey all weak-memory proof systems. It uses RSL, the Iris RA+NA result, GenMC, and RustMC as representative approaches that expose different assurance boundaries.
- **Not examined:** this report does not prove linearizability, functional correctness, deadlock freedom, starvation freedom, fairness, lock-freedom, or wait-freedom for any Anneal or zerocopy code.
- **Unknown:** which concurrency constructs a future Anneal translation should support. The present result only records the obligations that support would create.
- **Unknown:** what exact compiler/memory-model correspondence theorem would be sufficient if Anneal ever reused an LLVM-level concurrency analysis.
- Rust's source says atomics **currently** follow C++20 rules. Revalidation must treat that wording as version-sensitive rather than a timeless language guarantee.

## Evidence

**Pinned Rust atomic semantics.**

Repository: `rust-lang/rust`  
Revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`  
Path: `library/core/src/sync/atomic.rs`  
Blob: `4f2faa7e5fbd6bd7aa7377118b2e2dc1849243c5`

High-signal source regions are the module-level sections “Memory model for atomic accesses,” “Portability,” and the `Ordering` enum documentation. They state the C++20-derived model, access-based translation, data-race and mixed-size rules, lock-free/not-necessarily-wait-free distinction, and ordering semantics.

Evidence role: **source**.

**Relaxed Separation Logic.**

Viktor Vafeiadis and Chinmay Narayan. “Relaxed Separation Logic: A Program Logic for C11 Concurrency.” OOPSLA 2013. DOI `10.1145/2509136.2509532`.

Official project page: `https://people.mpi-sws.org/~viktor/rsl/`

The project page states the ownership-transfer interpretation of release/acquire/relaxed accesses and records the Figure 13 erratum concerning the older C11 formalization.

Evidence role: **source/documentation**.

**Strong Logic for Weak Memory.**

Jan-Oliver Kaiser, Hoang-Hai Dang, Derek Dreyer, Ori Lahav, and Viktor Vafeiadis. “Strong Logic for Weak Memory: Reasoning About Release-Acquire Consistency in Iris.” ECOOP 2017. DOI `10.4230/LIPIcs.ECOOP.2017.17`.

Official project page: `https://plv.mpi-sws.org/igps/`

The project page identifies the declarative-versus-operational mismatch, the RA+NA operational characterization, the Iris instantiation, and the mechanized higher-order GPS/RSL case studies.

Evidence role: **source/documentation**.

**Iris framework context.**

Official project page: `https://iris-project.org/`

The project describes Iris as a higher-order concurrent separation-logic framework implemented and verified in the Rocq Prover. This report uses that description only to characterize Iris's role; the weak-memory claims come from the Strong Logic work above.

Evidence role: **documentation**.

**GenMC.**

Michalis Kokologiannakis and Viktor Vafeiadis. “GenMC: A Model Checker for Weak Memory Models.” CAV 2021, pp. 427–440. DOI `10.1007/978-3-030-81685-8_20`.

Official project page: `https://plv.mpi-sws.org/genmc/`

The project page states the supported RC11/IMM/LKMM models, the parametric stateless exploration algorithm, its stated sound/complete/optimal execution-enumeration property under model conditions, and the use of partial-order/spin-loop optimizations.

Evidence role: **source/documentation**.

**RustMC.**

Ollie Pearce, Julien Lange, and Dan O'Keeffe. “RustMC: Automated Verification of Real-World Concurrent Rust.” FORTE 2026, pp. 235–255. DOI `10.1007/978-3-032-28187-6_14`.

Publication record: `https://pure.royalholloway.ac.uk/en/publications/rustmc-automated-verification-of-real-world-concurrent-rust/`

The publication record states the LLVM-based GenMC extension, Rust-specific lowering challenges, unsafe/FFI/atomic case studies, Loom-suite evaluation, and production-level concurrent-data-structure evaluation.

Evidence role: **documentation/source** for the published tool description.

No fresh **execution** evidence was produced.

## Revalidation

For another Rust revision, first inspect that revision's `library/core/src/sync/atomic.rs`. Revalidate the model source, data-race definition, mixed-size rule, ordering semantics, and lock-free/progress statements before carrying this report's Rust-specific claims forward.

For a deductive concurrency proof, record the exact pair **(memory model or fragment, logic soundness result)**. Check whether the program uses any feature outside the proved fragment: relaxed/SC atomics, fences, mixed-size accesses, non-atomic sharing, thread primitives, FFI effects, progress assumptions, or target-specific operations. Do not infer coverage from the logic's name alone.

For a GenMC- or RustMC-style result, preserve the analyzed program/IR, selected memory model, tool version, bounds/loop handling, environment assumptions, and the concrete property checked. If a source-level claim is required, separately establish why the compiler/front-end lowering preserves the source behaviors relevant to that property.

For a future Anneal concurrency implementation, the cheapest discriminating review is a translation matrix rather than a broad proof rerun. For every supported concurrent Rust construct, record:

1. its source semantic rule;
2. its translated representation;
3. the target proof/model rule that covers it;
4. the correspondence argument between source and target behavior; and
5. the fail-closed behavior when the construct or ordering is unsupported.

Then exercise small litmus-style cases that distinguish relaxed, acquire/release, and sequentially consistent behavior, plus data-race and mixed-size invalid cases. Passing those probes would not prove the full translation correct, but failure would cheaply expose a broken semantic mapping.