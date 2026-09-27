# FFI specification and trust patterns across Rust, CompCert, and CakeML

## Summary

A foreign-function interface is not one proof boundary. It is a stack of boundaries that must line up: the source-language declaration, the native symbol and calling convention, the abstract semantic contract, the resources the call may affect, the concrete foreign implementation, and the execution environment that binds and runs that implementation.

The exact Rust Reference behind Anneal's Rust pin makes the first distinction directly. An item in an `extern` block is a declaration of an item defined elsewhere—effectively an unchecked import. Rust specifies the Rust-visible signature, safety requirements, ABI, unwind boundary, and native-link metadata such as `link_name`; those facts do not establish the behavior of the absent implementation.

CompCert and CakeML show two reusable ways to make the missing semantic layer explicit. CompCert models an external function by a relation over the global environment, argument values, pre-call memory, observable trace, return value, and post-call memory, then requires structural properties that support compiler simulations. CakeML uses an FFI oracle carrying explicit world state and I/O history. Its PLDI 2019 verified-processor development goes one step further: it proves that concrete system-call machine code implements the abstract FFI behavior, thereby discharging a substantial execution-environment assumption rather than leaving that assumption permanently inside the top-level theorem.

For Anneal, the practical rule is to review each foreign edge as a layered contract. ABI compatibility is necessary but not sufficient. A proof is end-to-end only to the extent that it also establishes or explicitly trusts the foreign behavior, its frame/resource effects, the concrete implementation, and the environment that connects the verified caller to that implementation.

## Applicability

This report is a reusable verification-method reference for issue #3720's **FFI specification/trust patterns** item. It is not a replacement for the corpus's exact Rust/Charon foreign-item inventory. In particular, `reports/rust-extern-foreign-items-nightly-2026-05-31` remains the detailed source-level authority on the Anneal-era Rust declaration surface and pinned Charon representation.

The Rust language observations apply to `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, paired in the corpus with `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`nightly-2026-05-31`). The CompCert observations apply to version 3.18 at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`. The CakeML source observations apply to `CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec`; the concrete assumption-discharge example is the 2019 PLDI paper *Verified Compilation on a Verified Processor*.

The report concentrates on sequential external-call specification and trust accounting. It does not supply a C or C++ semantics, a complete dynamic-linker model, a weak-memory/concurrency FFI model, or a verified implementation of any zerocopy foreign dependency.

## Findings

### FFI correctness has several independent layers

A durable FFI proof should answer at least six questions.

First, **what does the verified-language program declare?** The declaration fixes the types and source-level permission boundary that the verified caller sees.

Second, **which native definition is actually invoked, and under which calling convention?** Source identity, native symbol identity, ABI, variadicness, and unwind convention are not interchangeable.

Third, **what semantic behavior may the foreign operation exhibit?** This layer describes return values, state updates, observable events, failure, and divergence rather than merely byte transfer at the ABI boundary.

Fourth, **which resources must it preserve?** A call can return the expected value while corrupting unrelated memory or violating an ownership/frame invariant.

Fifth, **why does the concrete foreign implementation satisfy that semantic contract?** The answer may be a proof, a validator, an audited shim, or an explicit trust premise. Omitting the answer does not make the obligation disappear.

Sixth, **what environment connects the verified call site to that implementation?** Link/load resolution, operating-system behavior, device state, filesystem state, and deployment assumptions can remain outside the proved code even when the foreign routine itself has been verified.

These layers can be discharged by different mechanisms. They should therefore remain separate in the theorem and in trust accounting.

**Evidence:** Rust Reference **normative** text; CompCert/CakeML **formal source**; CakeML PLDI 2019 **published proof architecture**; cross-system layering is **derived**.

### Rust's `extern` declaration proves no foreign implementation

The pinned Rust Reference says that external blocks provide declarations of items not defined in the current crate and describes them as unchecked imports. Functions in an external block have no Rust body. Rust can therefore type-check and compile a call while possessing no implementation whose functional behavior could be proved from the declaration alone.

The declaration still carries important proof-relevant information. The Reference specifies whether using the item requires an unsafe context. It assigns a foreign ABI that controls the low-level call interface. `C-unwind`-style ABIs change the boundary behavior for unwinding. `#[link_name]` and, on relevant Windows configurations, an ordinal can choose a native import identity different from the Rust source name.

Those facts establish a boundary contract, not the foreign implementation's semantics. A verifier that imports an `extern "C" fn f(x: i32) -> i32` as an arbitrary mathematical `i32 -> i32`, for example, still needs to say what state, memory, I/O, failure, divergence, and callback behavior the real `f` may have. The ABI signature alone cannot supply those facts.

The existing native reference report also records a concrete Anneal-era representation concern: pinned Charon preserves some foreign signature information but does not preserve every linker/variadic detail. That issue strengthens the need to keep source declaration identity, effective native binding, and semantic contract separate.

**Evidence:** Rust Reference **normative**; existing corpus report **source-grounded derived context**.

### CompCert makes foreign effects an explicit semantic relation

CompCert 3.18's `extcall_sem` is a relation, not a pure mathematical function. It relates the global symbol environment, argument values, pre-call memory, observable trace, result value, and post-call memory. That shape is useful because it gives the verifier places to state nondeterminism and effects instead of silently pretending that an external call is a pure deterministic expression.

CompCert also requires `extcall_properties`. The inspected record constrains result typing, preservation under equivalent symbol environments, memory evolution and framing, injections/extensions used by compiler simulations, trace length, receptiveness to matching traces, and determinism up to matching traces.

The reusable pattern is not CompCert's exact axiom set. It is the separation between **the abstract relation describing allowed foreign behavior** and **the proof rules needed to compose that relation with the rest of the verified system**. Anneal need not copy CompCert's memory model to benefit from the distinction.

A compiler theorem relative to this external-call relation still does not prove that a particular operating-system routine, C library, device, or hand-written assembly implementation realizes the relation. That is a separate adequacy obligation.

**Evidence:** CompCert 3.18 **formal source** + **derived** methodology.

### CakeML records the external world as state, behavior, and an oracle

CakeML's inspected FFI semantics stores an oracle, an explicit FFI state, and accumulated I/O events. `call_FFI` passes the call name, configuration bytes, current FFI state, and input bytes to the oracle. The oracle may return a new FFI state and output bytes or produce a final outcome. Program behaviors retain I/O events for both terminating and diverging executions.

The basis-library instantiation makes the parameterization visible. `basis_ffi_oracle` supplies formal behavior for standard calls such as read, write, command-line access, and exit. Calls outside that basis set fall through to an `ext` oracle supplied by the environment. The model therefore does not confuse “the verified language knows how to issue a foreign call” with “all foreign calls have been internally proved.”

This is a useful pattern for a verifier whose environment can vary. The semantic model can quantify over, parameterize, or constrain the environment while keeping the dependency explicit in the theorem.

**Evidence:** CakeML **formal source**.

### A foreign specification can be turned from an assumption into a proved refinement

The 2019 CakeML verified-processor development is particularly useful because it shows the next step after abstract FFI modeling. The compiler theorem initially assumes an installed execution environment in which external calls behave according to the modeled filesystem, command line, and CakeML calling convention. The paper identifies the external-call portion as the most complicated part of that assumption.

The development then introduces a relation between concrete machine state and FFI-oracle state and proves that machine execution of the system-call code implements the abstract interference/FFI step. For each relevant system call, the proof connects the abstract `call_FFI` result to a concrete sequence of machine steps and preserves the state relation. This proof work discharges the substantial FFI assumption for the verified Silver deployment; the residual theorem retains only the assumptions that remain genuinely external.

That example exposes an important trust-accounting rule: **a modeled FFI contract and a proof that the concrete foreign implementation realizes that contract are distinct artifacts**. The former lets higher-level proofs proceed. The latter removes the implementation from the unproved environment assumption.

**Evidence:** *Verified Compilation on a Verified Processor* **published proof architecture** + matching CakeML **formal source**.

### ABI correctness and semantic correctness are orthogonal

An ABI governs how a call crosses a machine boundary: register and stack use, argument/result representation, cleanup conventions, and related target details. Rust's Reference also makes unwind behavior depend on the ABI choice. A mismatch at this layer can invalidate a call even if both parties intend the same mathematical function.

The converse is equally important. Perfect ABI agreement says nothing about whether a callee returns the promised value, preserves caller-owned memory, performs unexpected I/O, invokes callbacks, blocks, diverges, or mutates external state. Those are semantic-contract questions.

A verification architecture should therefore avoid a single overloaded label such as “FFI supported.” At minimum it should distinguish **representable/callable**, **semantically modeled**, and **implementation-validated or trusted**. A foreign edge can be green at one layer and red at another.

**Evidence:** Rust Reference + CompCert/CakeML **derived comparison**.

### Frame/resource conditions belong in the FFI contract

Foreign code often receives pointers or handles that expose only part of a caller's state. Functional pre/postconditions on return values are not enough to express the resulting obligation. The proof also needs a frame statement: which memory, ownership tokens, capabilities, file descriptors, or other resources may change and which must remain valid.

CompCert's external-call properties make this explicit in its own memory model. They constrain valid-block evolution, permissions, memory injections, and unchanged regions. The CakeML verified-processor development likewise constrains foreign interference so that private CakeML machine state is preserved while designated shared state carries call inputs and outputs.

For Anneal, the concrete resources will differ because Rust's aliasing, provenance, initialization, and ownership obligations differ. The reusable lesson is structural: a foreign contract should identify both the resources transferred to the callee and the frame the callee must preserve.

**Evidence:** CompCert/CakeML **formal source** + **derived** Anneal implication.

### Linking and deployment are proof-relevant when identity can drift

Rust permits native link identity to differ from Rust item identity, for example through `#[link_name]` or target-specific import mechanisms. More generally, a deployment environment chooses which binary definition satisfies a foreign reference. This creates a separate identity obligation even after a logical contract has been written.

A theorem about “the implementation of `f`” is only connected to execution if the loader/linker actually binds the verified caller to that implementation under the ABI and environment assumed by the proof. If Anneal eventually supports verified or audited FFI models, durable evidence should therefore identify the native implementation by a reproducible artifact identity where practical, not merely by a source-level function name.

This does not require Anneal to model every dynamic loader. It requires the residual assumption to be visible when loader/binding behavior is outside the proof.

**Evidence:** Rust Reference **normative** + **derived** trust accounting.

### Unsafe call syntax is not a proof of the foreign contract

Rust's `unsafe` boundary requires the caller to uphold conditions that the compiler cannot check. Conversely, declaring a foreign function `safe` shifts responsibility toward the declaration author: safe Rust may invoke it without an unsafe block.

Neither syntax proves the foreign implementation. A verification system should not translate “safe to call from Rust” into “verified to satisfy an arbitrary functional specification,” nor should it treat `unsafe` as a complete semantic description of the risk. The contract still needs the layers above.

**Evidence:** Rust Reference **normative** + **derived** verification consequence.

### FFI assumptions should be theorem-visible and reducible over time

The CakeML example also illustrates a process rule. Start with an explicit environment assumption when that is necessary to make progress; then reduce it by verifying more of the boundary. The paper reports that moving assumptions into proved system-call refinement both reduced the trusted boundary and exposed an inconsistency in a prior assumption set.

For Anneal, this favors named assumptions over implicit trust. A future proof package could, for example, state that a particular foreign call satisfies contract `C` under native binding `B`. Later work could replace that premise with a proof about a concrete shim or library without changing unrelated source-level proofs.

An assumption that is explicit can be audited and discharged. An assumption hidden inside an uninterpreted pure function, a hard-coded return value, or a generic “extern supported” flag is much harder to reason about safely.

**Evidence:** CakeML PLDI 2019 **published evidence** + **derived** process guidance.

### Anneal should inventory foreign edges as layered obligations

For each foreign edge that Anneal wants to reason about, durable evidence should record:

1. the source declaration identity and source-level safety contract;
2. the effective native symbol/binding identity;
3. ABI details that affect the call, including unwind and variadic behavior when relevant;
4. the abstract semantic contract, including state, memory, I/O, failure, and divergence as applicable;
5. frame/resource obligations;
6. whether a concrete foreign implementation has been proved/validated against that contract or remains trusted;
7. residual link/load/environment assumptions.

Unsupported layers should fail closed or remain explicit assumptions. They should not be inferred from successful type checking, linkability, or the existence of a Charon external declaration.

This decomposition also prevents one foreign model from accidentally claiming more than it proves. A pure model for a well-understood mathematical intrinsic, for example, does not establish a general mechanism for stateful C APIs.

**Evidence:** **derived synthesis** from the sources above.

## Boundaries

- No Rust, Charon, C/C++, linker, loader, CompCert, CakeML, HOL, or machine-code execution was performed in this run.
- The report does not provide a formal C or C++ semantics, a dynamic-linker semantics, or a platform-complete ABI model.
- CompCert's `extcall_properties` are examples tied to CompCert's memory model; they are not proposed verbatim as Anneal's FFI axiom set.
- CakeML's basis FFI and Silver system-call proof concern CakeML's environment and target. They demonstrate a proof pattern, not a ready-made Rust FFI model.
- The report does not prove any particular foreign library used by zerocopy or Anneal correct.
- The report does not establish a concurrency, signal, cancellation, callback, thread-local-state, or weak-memory FFI model.
- The existing `rust-extern-foreign-items` corpus report remains authoritative for exact Anneal-era Rust/Charon representation details; this report uses those facts only to motivate the general trust decomposition.
- The existing current-profile unsupported/opaque-operation candidate remains the dedicated treatment of fail-closed translation, conservative opaque semantics, and erasure/underapproximation. This report avoids replacing that scope.

## Evidence

**Normative Rust language source:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/items/external-blocks.md`, blob `e1704556b5f000c019cd04df63e7e04692454c42`: external blocks as declarations/unchecked imports; safety; ABI; `link_name` and ordinal behavior.
- `src/items/functions.md`, blob `362b39b5733c385a18e20a928d75f960f1cd427e`: foreign-call definitions and unwind behavior across ABI boundaries.

**Formal CompCert source:** `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (3.18).

- `common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`: `extcall_sem` and `extcall_properties`, including memory/frame, trace receptiveness, and determinism-up-to-matching-traces obligations.

**Formal CakeML source:** `CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec`.

- `semantics/ffi/ffiScript.sml`, blob `b40698d34360646ffb56e098e15571f99b99d9f4`: FFI state, oracle-driven calls, final outcomes, and I/O-carrying terminating/diverging behaviors.
- `basis/basis_ffiScript.sml`, blob `4b98525f4f628392a0ec8710a1d4d1394acbffe9`: basis-library FFI oracle plus parameterized extension oracle.

**Published proof architecture:** Andreas Lööw et al., *Verified Compilation on a Verified Processor*, PLDI 2019, DOI `10.1145/3314221.3314622`. Sections 5–6 describe the execution-environment/FFI assumption and the refinement proof that concrete system-call code implements the modeled FFI behavior.

**Adjacent corpus evidence:** `google/zerocopy@reference` report `rust-extern-foreign-items-nightly-2026-05-31` identifies exact source/native-binding representation boundaries at Anneal's pinned Rust/Charon revisions. Current-profile Library work record `8e5525f7-b5c0-458a-94da-3159ba703c77` separately treats unsupported/opaque-operation semantic preservation.

## Revalidation

When the Rust/Charon/Aeneas pin changes, first revalidate the exact foreign declaration and representation surfaces already identified by the dedicated `rust-extern-foreign-items` report. In particular, check safety, ABI, unwind semantics, effective native identity, variadicness, and what Charon preserves.

For any concrete Anneal FFI model, construct a boundary table matching `trust-layer-matrix.json`. Require an explicit entry for every layer rather than treating omission as success. Tie the abstract semantic contract to the exact source item and, where the proof claims a concrete implementation, to a reproducible native artifact or verified source/build identity.

On an execution-capable surface, use deliberately discriminating fixtures rather than only happy-path calls: mutate caller-visible and caller-private memory separately; return multiple allowed results if the model is nondeterministic; exercise I/O/error paths; test unwind behavior when relevant; and verify effective symbol binding. Preserve the foreign artifact hash, linker/load evidence, target triple, invocation, and resulting trace.

If a foreign implementation is intended to be removed from the trust boundary, prove or validate a refinement from its concrete execution to the abstract contract. Keep any remaining OS/loader/device/environment premise explicit in the final theorem or report.