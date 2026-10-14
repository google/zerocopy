# PCC, TAL, and foundational policy certificates

## Summary

Proof-carrying code certifies the consumer's chosen property of target code. Typed assembly language certifies its type-safety discipline. TWAM demonstrates that a richer chosen property—soundness of successful logic-program search—can be carried by dependent typing. These certificates can make the producer untrusted while leaving specification choice, semantic models, checking infrastructure, and artifact binding essential. They do not automatically establish equivalence to an original source program.

## Applicability

The primary observations are Necula's 1998 dissertation, Morrisett et al.'s TOPLAS1999 TAL paper, Bohrer/Crary's 2018 TWAM paper, and Appel's primary FPCC project account plus the complete primary LICS 2001 PDF. No historical executable artifact or fresh checker run was acquired. The full FPCC PDF was acquired from the author site after the web fetch failed; its SHA-256 is `03078cc39e2b94460e2e7b48a7ef112754bcacbf4bf108986ed108c69b922bf9`. An access failure was not interpreted as a system limitation.

This report addresses P001–P003, T029, and partial T030/T043/T048. It does not cover all staged runtime generation, JVM verification, eBPF admission policies, or deployed PCC loaders.

## Findings

### The consumer chooses the proposition

**Basis: documentation from Necula, Chapter2 §2.1.3, Theorem2.1, printed pp.20–21/PDF pp.36–37.** The consumer's policy includes logic, specification, and VC generation; provability of the generated VC implies that executed actions meet policy preconditions. Producer annotations supply invariants and specifications, but those claims must be checked. Touchstone's typing and bounds-checking annotations certify a target safety property; Chapter2 explicitly distinguishes this from complete compiler correctness. The historical prototype also records incorrect arithmetic-overflow handling in a footnote on printed p.19/PDF p.35. This limitation is about the stated prototype and infrastructure, not a current-system verdict. [Dissertation](https://people.eecs.berkeley.edu/~necula/Papers/thesis.pdf).

**Basis: derived.** A policy forbidding out-of-bounds writes can accept code returning an incorrect numerical answer. A policy asserting that answer requires an additional functional proposition. Consequently, the consumer must choose an acceptance theorem that matches the intended engineering objective. Certificates are not interchangeable merely because both are called safety proofs.

### TAL: preservation of typing supports a target safety theorem

**Basis: documentation from TOPLAS1999 §7.3, printed p.23, plus §1.** Subject reduction preserves TAL well-formedness across a step; progress says a well-formed program steps or is a designated halt; their type-safety corollary excludes reachable stuck states. The presented translation preserves typing from SystemF through intermediate languages to a conventional RISC-style TAL. It protects the abstractions expressed by those types, without implying termination or arbitrary functional correctness. The basic TAL excludes some advanced optimizations and runtime-generation features, discussed separately as extensions. [Author paper](https://www.cs.cmu.edu/~dpw/papers/tal-toplas.pdf).

The proof directions matter: source typing and a type-preserving compiler help produce an acceptable target; the consumer can independently type-check the target. A malicious compiler may emit a different well-typed target and still pass that target policy. To recover source functional correctness, a source-target semantic certificate must also be supplied or proved.

### Foundational checking reduces assumptions about typing rules

**Basis: primary documentation.** Appel's 1999–2005 project account describes ML-to-SPARC output with machine-checkable Twelf memory-safety proofs and a mechanically justified TAL checker. The LICS2001 paper's inspected abstract/introduction frames FPCC as using foundational logic and a simpler verifier, contrasting it with trusting a large type system or VC generator without a foundational soundness proof. The inspected material does not justify a numerical present-day TCB-size claim. [Project account](https://www.cs.princeton.edu/~appel/fpcc.html), [Primary paper](https://www.cs.princeton.edu/~appel/papers/fpcc.pdf).

The full LICS paper §§2 and 5 makes the mechanism explicit: object HOL with arithmetic axioms is represented in LF/Twelf; type-safety rules become proved semantic lemmas carried to the consumer. Types are interpreted over memory, allocation sets and root values. Its first set model excludes mutable fields and negative recursion; the step-indexed extension handles contravariant recursion. These are historical model boundaries, not present-day limits on every FPCC design. The foundational layer still fixes instruction meaning and policy. Basis: **documentation**, PDF pp.2 and 5–7; no Twelf artifact replay.

**Basis: derived.** Moving typing rules into proved lemmas changes where trust is placed: accepted evidence can derive from a smaller logic rather than assuming an entire language-specific policy checker is sound. The ISA model, chosen policy, foundational axioms, proof checker implementation and binary, parser, loader, and execution environment still need a stated relationship to the theorem. Foundational proofs do not eliminate specification error or hardware-model mismatch.

### TWAM: successful search, failure, and divergence are different

**Basis: documentation from TWAM §3.5, PDF p.15, and introductory Theorem1.** Progress allows a done state, exhausted search failure, or a next step; preservation maintains typing. Search Soundness says a well-typed execution reaching a done state produces a substitution under which the query is derivable in first-order minimal logic. Exhausted search is not machine stuckness. The paper deliberately does not certify completeness. Its T-Prolog includes the occurs check and excludes cut and negation-as-failure. This endpoint is a dependently typed abstract machine, not native machine bytes. [Author paper](https://www.cs.cmu.edu/~crary/papers/2018/twam.pdf).

The property is consequential precisely because it is stronger than ordinary memory safety and narrower than full operational equivalence. Successful answers must have proofs; failure need not prove that no answer exists. Termination and a fair or complete search strategy remain outside that stated guarantee.

### Derived Anneal policy and authority lessons

**Basis: derived.** A consumer-facing Anneal checker should state the certificate proposition before selecting its format. Candidate propositions include target-policy compliance, preservation of safe source executions, source-failure reflection, full state correspondence, and correctness relative to an independently justified mathematical specification. The producer/checker split alone selects none of them.

For unsafe code admission, a typed or policy-safe model is insufficient unless bad concrete executions are connected to bad model executions or ruled out by independently proved concrete premises. A policy that ignores provenance or authority can still correctly certify its own weaker byte-shape property. Extending that policy needs new semantic rules and proofs about authority changes, rather than adding annotations with no acceptance obligation.

Operational containment belongs alongside the proof contract. Isolation can prevent a producer from modifying the checker or certified bytes, but cannot strengthen a weak proposition. Maintain code/certificate identity across loading and runtime generation. Each newly emitted code fragment needs either a fresh policy check bound to its bytes or a proved generator theorem with the corresponding installation premises.

Maintenance costs arise in policy formalization, semantic models, proof compression or annotation reconstruction, checker implementation, and safe loader integration. Consumer-selected policy makes extensions possible, but every extension changes the theorem the consumer is relying on. Reject unsupported constructs and incomplete evidence explicitly.

## Boundaries

No PCC, TAL, Twelf, or TWAM checker was built or run. The reports do not establish source-specification meaning, full compiler semantic preservation, proof of a present-day checker binary, loader correctness, garbage-collector correctness, concurrency, hardware behavior, or exact runtime generation coverage. FPCC primary-paper inspection includes the full10-page author PDF, with §§2/5 checked for logic and semantic-type interfaces; no executable FPCC artifact was rechecked. TAL and TWAM paper metatheory was read, not independently mechanized or replayed.

## Evidence

- Necula, *Compiling with Proofs*, CMU-CS-98-154, 1998-09-18, 277-page author dissertation; Chapter2 Theorem2.1 and narrow coordinates above.
- Morrisett/Walker/Crary/Glew, *From System F to Typed Assembly Language*, TOPLAS21(3),1999, DOI `10.1145/319301.319345`, 41-page author PDF; §7.3 type-safety results.
- Appel, *Foundational Proof-Carrying Code*, LICS2001, DOI `10.1109/LICS.2001.932501`; primary project account1999–2005; full10-page author PDF acquired; exact hash above.
- Bohrer/Crary, *TWAM: A Certifying Abstract Machine for Logic Programs*, 2018 author PDF, 23 pages; introductory Theorem1 and §3.5 metatheory.
- Evidence acquired2026-10-14 via primary web sources and direct author-PDF retrieval with native PDFKit text extraction. No immutable implementation pin was claimed where no concrete executable artifact was inspected; publication identities are retained instead.

## Revalidation

Recover complete primary artifacts before making executable-path claims. Identify the consumer's exact property, its soundness theorem, all axioms and semantic dependencies, and the bytes authorized for execution. For a policy discrimination test, submit a safe target with an intentionally wrong functional answer; an acceptance should demonstrate policy scope, not be misreported as compiler correctness. The adjacent package's finite witness illustrates this distinction without running any upstream checker.

*Authored by an AI agent acting on joshlf's behalf.*
