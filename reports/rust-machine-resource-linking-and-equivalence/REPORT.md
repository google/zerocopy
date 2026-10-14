# Linking machine proofs to Rust resources and behavioral equivalence

## Summary

The missing interface between an assembly proof and unsafe Rust soundness is a relation over values **and resources**, together with execution and context-preservation theorems. Equal return bits are insufficient: they can coexist with a dead allocation, invalidated borrow, uninitialized output, forbidden access or incompatible exit. Equality through a shared specification establishes equivalence only when that specification determines all observations included in the claim.

This report factors the required claims, compares a concrete multi-language methodology, and checks small composition and counterexample theorems. It does not supply the missing complete MiniRust↔Kraken or Rust-source↔machine relation. The factorization gives those future theorems explicit consumers and identifies what a smaller Anneal checker would need to validate.

## Applicability

The comparison uses the POPL2023 DimSum paper (DOI10.1145/3571220), the already-reviewed RustBelt/RefinedRust and FFI corpus, and the exact MiniRust/Kraken subjects of the companion reports. `support/ContextBridge.lean` is an owned abstract model checked with Lean4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`. Its variables range over explicitly supplied relations; the generic theorems do not instantiate Rust, a platform ABI or an ISA.

Research coverage: MR23 and AS07/AS14/AS15, plus the callback/resource portion of AS13. This is a theorem-architecture and bounded-counterexample investigation rather than a completed language integration.

## Findings

### The relation must retain information that machine bytes omit

Basis: source + derived.

MiniRust's byte state carries distinctions such as initialization and provenance fragments, and its memory parameter may add alias permissions. Kraken's base memory is a partial map from numeric addresses to concrete bytes. A relation between the two cannot generally be a total function that simply strips all additional information and later reconstructs it from addresses.

A useful relation `R` needs at least the following components for the supported fragment:

| Component | Why a byte-only relation loses it | Required bridge fact |
|---|---|---|
| Allocation/liveness | Equal addresses can denote successive allocations | Allocated-region map and liveness preservation |
| Provenance/authority | Integer equality is not access permission | Admitted pointer derivation or explicit exposed-provenance policy |
| Aliasing/borrows | Same bytes can coexist with different borrow permissions | Access and reborrow rules preserving caller resources |
| Initialization/validity | A concrete byte pattern may not encode a valid Rust value | Representation and validity at every typed exposure |
| Layout/metadata | Raw words do not determine a DST or calling convention | Bound layout, metadata and ABI witnesses |
| Environment/continuation | Return bits omit the caller's stack, callback and unwind obligations | Entry/exit relation and context invariant |

Not every numeric register needs a Rust pointer interpretation. An adapter should track which values are ordinary integers and which are carried as access capabilities or pointer representations. Inventing provenance for arbitrary output bits would require a separately justified operation; it cannot follow from successful address arithmetic.

The owned `value_equivalence_is_not_context_safety` witness has identical scalar value7 before and after, but a changed live-borrow flag. `same_address_is_not_resource_authority` in the inline-contract package similarly separates liveness, alias allowance and initialization. These simple witnesses expose information loss; they are not a new Rust memory model.

### Separate four semantic obligations

Basis: derived.

1. **Entry adequacy.** Every supported Rust call satisfying the public precondition can produce a machine entry related by `R`. The precondition may require valid inputs, live resources and target/environment configuration. It must not assume the implementation's safety or desired result.
2. **Machine safety and resource preservation.** All admitted execution prefixes satisfy access, fault and resource rules. A terminating postcondition or unchanged final memory does not establish this obligation.
3. **Behavioral correspondence.** Machine executions map to allowed Rust/specification observations and exits, preserving `R`. If equivalence is requested, establish the reverse direction as needed under the same observation/domain choices.
4. **Context closure.** The surrounding supported Rust context can resume or handle the specified exit with its invariants intact. This includes retained aliases, reentrancy and callbacks where admitted.

`context_replacement` checks the logical composition of a supplied execution-reflection relation and observation agreement. It concludes that a machine transition has a corresponding Rust transition with the same observation. Its assumptions are deliberately theorem-visible. It does **not** prove that those relations hold for real Rust/Kraken, exclude machine faults, cover divergence or imply arbitrary-context equivalence. Prefix safety and context closure remain separate hypotheses/results in a real instantiation.

This factorization permits different proof-producing tools to discharge different arrows. A kernel proof of machine arithmetic can be reused without trusting its tactic, while source import, the ABI map and resource interpretation are either checked separately or remain declared assumptions. Moving those assumptions into an opaque “assembly supported” primitive would enlarge the hidden internal TCB.

### Equivalence requires a sufficiently precise common contract

Basis: checked owned theorem + derived.

`exact_spec_equivalence` proves pointwise equality when both deterministic implementations equal the same exact function. `loose_spec_is_not_equivalence` shows that two different outputs can satisfy the same permissive predicate. For an effectful implementation, replace scalar results with the selected behavior: returned values, writes, permitted accesses, externally visible events, errors, panic and divergence as applicable.

The checked overflow witness distinguishes an 8-bit wrapping outcome from a checked-overflow panic at256. Thus comparing assembly with a Rust `+` implementation requires its overflow policy and compilation context; choosing Rust `wrapping_add` makes the intended arithmetic contract explicit. Similarly, oversized shifts, trapping instructions, allocation failure and callbacks can distinguish implementations with equal ordinary-case output.

Refinement is often a useful weaker endpoint, but direction matters. A target allowed to exhibit fewer behaviors than a nondeterministic source may be a valid implementation; that does not justify claiming both have identical behavior. An implication premised on source UB-freedom also cannot independently certify source UB-freedom. The prior source-import report and open P127 retain that foundational distinction.

### A context need not be expressible entirely in one source language

Basis: primary paper + derived application.

DimSum supplies a mechanized methodology based on independently defined modules and event interfaces. Its Rec/Asm examples connect abstract and concrete memory models, including assembly-supported pointer comparison and coroutines; it also verifies a compatible compiler. This is useful evidence that a linking framework can make language and memory differences explicit rather than first forcing every assembly component into a source-language implementation.

For Anneal, the transferable question is how to design the event/resource boundary: call, return, memory/resource transfer and exceptional/control exits should have explicit interpretations. The cited paper's examples are idealized languages, not a ready Rust ABI adapter or modern Rust aliasing theorem. A proposed MiniRust/Kraken application would need its own correspondence and coverage proof, including concurrency if that scope is admitted.

The older CompCert/CakeML FFI corpus offers complementary patterns: external behavior as a relation, explicit world state, and proving a concrete foreign implementation refines that relation. Reuse the decomposition, not a foreign memory model's assumptions verbatim. A scalar external function declaration does not itself establish a frame, callback policy or deployed implementation identity.

### Open clients and callback resources constrain the interface

Basis: prior primary-grounded corpus + derived.

A Rust library's safe clients may retain aliases, invoke safe methods through interior mutability, instantiate generics differently or call back into the library. A closed executable with one initial state does not quantify over those contexts. Assembly contracts should therefore expose public semantic types/resources and identify which invariant is temporarily opened during the call.

The contract must say whether a callback is permitted, what it may access and what must be re-established before invoking it. A caller-owned invariant cannot remain silently broken while control returns to arbitrary safe Rust. On exceptional exits, resource restoration and stack/unwind behavior must agree with the actual ABI and inline restrictions. The memory-logic reports separately examine MiniRust protector and unwind-lowering boundaries.

An unsafe caller violating the public precondition is a different case from a safe caller triggering a bad state through an ostensibly safe abstraction. Do not repair an invalid API theorem by shrinking the public domain to clients that happen not to expose its defect.

### A practical first domain and its extension points

Basis: derived from performed pilot and surveyed interfaces.

The first actual pilot uses scalar integers, a C ABI leaf and register-only modular arithmetic. It avoids pointer reconstruction and complex resource transfers while exercising a real Rust signature, exact Kraken program, return state and object/link binding. A second stage can transfer one live read-only or exclusive byte region and interpret every access with its width. Pointer-returning functions then require a relation that preserves or explicitly reconstructs valid provenance and metadata.

Callbacks, lifetime-parametric APIs, relaxed atomics and privileged code each add a distinct environment/resource obligation. The decomposition permits a restricted but honest supported domain now, while identifying the theorem needed to extend it. It does not require trusting all of Anneal's proof search, but does require either checking or declaring every semantic bridge used by the final claim.

## Boundaries

No full Rust/MiniRust/Kraken mixed-language semantics or contextual adequacy theorem was implemented. No existing RustBelt library proof was automatically ported by this report. The owned generic theorem and negative witnesses have no axioms in their reported Lean closure, but that does not prove the correctness of the kernel implementation, supplied semantic relations or compiler.

The performed native pilot covers selected inputs; its universal Kraken theorem covers the modeled program under its actual semantics. Neither alone connects every safe Rust client to physical hardware. Constant-time, crash behavior and privileged environment interference need additional observations and are covered as separate research scopes.

## Evidence

- [DimSum project and primary artifacts](https://plv.mpi-sws.org/dimsum/), [paper](https://plv.mpi-sws.org/dimsum/paper.pdf), POPL2023 DOI10.1145/3571220, especially language/memory/linking distinctions and case studies.
- Existing corpus `ffi-specification-trust-patterns-2019-2026` and the new RustBelt/RefinedRust/MiniRust bridge reports; their exact subject/version limits remain in force.
- [MiniRust pointer/representation source](https://github.com/minirust/minirust/tree/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec) and [Kraken memory](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/Mem.lean).
- `support/ContextBridge.lean`, exact source identity and successful checker log: composition, exact-spec equality, loose-contract, borrow-liveness, overflow and observation witnesses; all seven reported closures have no axioms.

## Revalidation

Check the owned theorems with the selected Lean kernel and inspect the complete statements and dependencies. For a concrete integration, instantiate entry, prefix safety, execution correspondence and context closure separately; run the same-value/dead-resource, wrong-overflow-policy and loose-contract controls against that integration.

If either language model changes its provenance, aliasing, initialization, unwind or nondeterminism rules, re-examine `R` and all operation-specific preservation lemmas. Passing unchanged scalar arithmetic is not a revalidation of a changed memory bridge.

*Authored by an AI agent acting on joshlf's behalf.*
