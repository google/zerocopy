# LCF abstract theorem values: what a small kernel does and does not buy Anneal

## Summary

LCF's important architectural move was not merely to put a small checker at the bottom of a prover. It made theorem values an abstract type in the proof-programming language and allowed ordinary proof code to obtain values of that type only through trusted axioms and primitive inference rules. Tactics could search, fail, backtrack, or decompose a goal incorrectly, but they could not manufacture a theorem value unless their validations ultimately reconstructed one through those trusted constructors. Later LCF-family systems preserved this producer-versus-checker boundary in different forms.

That mechanism gives Anneal a useful design principle: **make successful acceptance a capability that only checked paths can construct**. A live proof result can be represented by an opaque handle tied to an exact proof context or worker generation; publication APIs can require such a checked handle instead of accepting arbitrary "success" data from search code, plugins, or orchestration. Where a portable proof term or certificate exists, Anneal can recheck it before granting current acceptance and thereby remove the producer from the logical acceptance boundary for the fragment the checker covers.

The analogy stops at that boundary. An in-process theorem value says how a logical result was allowed to come into existence in one trusted runtime. It does not identify the Rust program the theorem is supposed to describe, prove that a cached or serialized artifact is fresh, prove that the current translator preserved Rust semantics, or prove that bytes loaded in a later process were produced by the same trusted path. Those are separate obligations about source/model correspondence, environment and tool identity, artifact provenance, compatibility, and freshness.

Anneal should therefore borrow LCF's *authority structure*, not treat "small kernel" as a substitute for end-to-end provenance. Logical acceptance should be difficult to forge by construction. Rust-level acceptance should additionally require the exact source/build/tool/model identity and correspondence evidence that make the checked theorem relevant to the requested Rust claim.

## Applicability

This report addresses `google/zerocopy#3732` J024. It asks why LCF made theorem construction abstract, how later systems extended that idea, how an in-process theorem value differs from a serialized or cached result, and where Anneal can use construction boundaries without confusing them with source/model correspondence.

The historical core comes from the original LCF literature: Gordon, Milner, Wadsworth, Newey, and Morris, *A Metalanguage for Interactive Proof in LCF* (POPL 1978, DOI `10.1145/512760.512773`); Gordon, Milner, and Wadsworth, *Edinburgh LCF: A Mechanised Logic of Computation* (LNCS 78, 1979, DOI `10.1007/3-540-09724-4`); Milner, *LCF: A Way of Doing Proofs with a Machine* (MFCS 1979, DOI `10.1007/3-540-09526-8_11`); and Paulson's later Cambridge LCF exposition in *Logic and Computation* (1987, chapter DOI `10.1017/CBO9780511526602.008`). These sources establish the abstract-theorem-value architecture and the role of trusted inference constructors and validations.

The Anneal comparison is bound to `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require precise verification scope, justified Rust semantics, explicit and shrinkable trust, fail-closed acceptance, and Rust-oriented results while deliberately leaving the exact proof/result representation open.

The report also reuses three current `reference` packages as bounded evidence about the layer that LCF does not solve:

- `lean-olean-format-identity-v4-30-0-rc2` shows that a Lean `.olean` is a serialized module artifact rather than a self-authenticating source-freshness certificate.
- `lean-module-import-semantics-v4-30-0-rc2` shows that the imported environment depends on module resolution and exact compiled artifacts, including transitive imports.
- `tcb-accounting-patterns-verification-systems-2026-09-27` separates logical checking from source/model and deployed-execution correspondence.

Those reports are used only for their stated subjects. This report does not generalize them into a complete Lean or Anneal artifact model.

## Findings

### LCF moved theorem authority into an abstract type

The classic LCF architecture gives proof programs a type of theorem values whose representation ordinary ML code cannot construct directly. Trusted primitive inference rules consume already accepted theorems and return new theorems when their rule-specific preconditions hold. Axioms and other trusted roots introduce the initial authority. The rest of the prover can be large, heuristic, and failure-prone without receiving an unrestricted constructor for theorem values.

This arrangement changes the failure mode of automation. A buggy tactic can choose the wrong subgoals, loop, fail to solve a solvable goal, or produce a validation that later fails. What it cannot do through the ordinary interface is simply assert that an arbitrary proposition is a theorem. The final validation must produce a theorem value, and that value can arise only through the trusted theorem-producing operations.

Paulson's later exposition makes the same separation particularly clear: backward tactics return subgoals together with validations; after the subgoals are proved, the validation combines their theorem values into a theorem for the original goal. Search and proof construction are therefore distinct responsibilities. The search layer may be complicated while logical acceptance remains concentrated in the abstract theorem constructors.

For Anneal, the direct transfer is an authority rule: code that decides *what to try* need not also have authority to say *the claim is established*. An agent, tactic, scheduler, plugin, or external solver can propose work. The final success object should come from a narrower checked path whose contract Anneal can state precisely.

**Evidence role:** primary historical publications; Anneal transfer is derived.

### Opaque checked handles can prevent accidental acceptance inside one live context

Anneal can use the same idea even if its internal implementation is not literally an ML abstract type. A successful verification result can be represented by an opaque value that ordinary orchestration cannot fabricate. Construction can require the exact proof checker, result classifier, trust accounting, and source/model context that define success.

The handle should also be context-bound. A theorem checked in one Lean environment or against one generated model should not remain silently usable after the worker, environment, model, or source generation changes. A live handle can therefore carry or be scoped by an unforgeable session/generation identity. APIs that publish, cache as current, or answer "verified" can require a checked handle for the exact generation they are about to represent.

This is deliberately stronger than tagging a plain result record with a generation number. A tag can be copied or combined incorrectly by code that already has unrestricted constructors. An opaque checked handle makes the authority relation visible in the type/API boundary: code without the checker cannot invent a value that the publication path accepts as checked.

The handle does not need to be durable. It may be useful precisely because it is process- or session-scoped. If a process dies, the handle dies with it, and durable state must be reconstructed from stronger artifacts or recomputed.

**Evidence role:** LCF mechanism plus derived Anneal design.

### Serialization turns an in-process construction invariant into a provenance problem

The theorem abstraction is easiest to reason about while theorem values live only inside the trusted runtime. Persistence changes the question. Once a theorem, environment, or result is serialized, a later process sees bytes rather than the original construction history.

Those bytes can be accepted in several ways:

1. **Recheck a portable proof or certificate.** The new process reconstructs a checked theorem/result through its current checker.
2. **Trust a compiled/serialized environment artifact.** The new process assumes the build and artifact pipeline preserved the trusted invariants.
3. **Recompute from authoritative source.** The process discards the old logical authority and constructs a new one.
4. **Treat the serialized object as an opaque capability minted by a trusted storage service.** This shifts trust into that service's integrity, identity, compatibility, and freshness protocol.

These are different trust models. LCF's abstract type does not select among them.

The current Lean reference evidence gives a concrete reason to preserve the distinction. A `.olean` stores serialized module data and is consumed as part of a compiled environment. The loader's ability to read that artifact is not, by itself, proof that current source and dependencies still correspond to it. Lake and surrounding build machinery carry much of the invalidation responsibility. A module import also depends on how a module name resolves and which compiled transitive artifacts are selected. Even if every theorem inside such an environment was originally kernel-checked, "this is the environment for the source and build I am verifying now" remains an external identity/freshness claim.

Anneal should therefore never infer durable currentness solely from the fact that a value was once checker-produced.

**Evidence role:** existing pinned `reference` reports plus derived comparison.

### Rechecking can remove producer trust without removing correspondence trust

Portable proof terms or certificates offer the cleanest extension of the LCF boundary across process restarts. An untrusted or less-trusted producer can search for evidence; a small checker validates the evidence before acceptance. If the evidence format and checker cover the relevant proof obligation, the producer's implementation no longer needs logical acceptance authority.

That does not make the complete verification pipeline small or self-justifying. The checker proves only the claim represented in its input language under its assumptions. Anneal still needs to justify why that claim corresponds to the requested Rust program and property.

For example, a Lean kernel may establish a theorem about generated Lean definitions. The kernel does not establish that Charon represented every relevant Rust behavior, that Aeneas translated the selected LLBC faithfully for the promised property, that the generated theorem statement describes the intended Rust item, or that the source/build inputs have not changed since generation. Those propositions live outside the logical kernel unless separately encoded and checked.

This yields a useful trust decomposition:

| Question | Small logical checker can answer? | Additional Anneal obligation |
| --- | --- | --- |
| Is this proof valid for this theorem in this logical environment? | Yes, for the checker's supported logic and assumptions | Pin checker/environment identity and trust |
| Is this theorem the one Anneal intended to prove? | Not by theorem checking alone | Obligation identity and provenance |
| Does the theorem/model faithfully represent the selected Rust semantics? | Not by target-level checking alone | Source/model correspondence |
| Are cached/generated artifacts current for this source/build/tool state? | Not by target-level checking alone | Freshness and input closure |
| Is this successful result authorized to replace the current published result? | No | Generation/fencing/publication authority |

The architectural value of a small checker is still substantial: it can shrink one important trust boundary. The mistake is to project that shrinkage onto unrelated boundaries.

**Evidence role:** LCF authority structure + current Anneal principles + derived decomposition.

### "Small kernel" can describe logical trust while hiding a large operational TCB

The LCF story is sometimes summarized as "all soundness rests on a small kernel." That statement is useful only when the claim and failure model are explicit.

For pure logical derivability, a small set of theorem constructors can be the decisive acceptance boundary. Real systems also rely on the implementation language/runtime, unsafe/native extensions, parser and elaborator behavior where those affect the theorem being checked, imported axioms, plugin escape hatches, and the integrity of loaded environments. When the user-facing claim is about Rust rather than an already formed theorem, translators and correspondence arguments add another layer.

Anneal should therefore report trust claim-relatively. A result can say, for example, that a target theorem was accepted by a pinned Lean kernel while separately recording which source/model translation, imported assumptions, generated artifacts, native extensions, or other trusted components were involved. It should not collapse these into the slogan "kernel checked."

This distinction also helps evaluate plugins and agents. A plugin that only proposes tactics or terms that the same checker validates may be outside logical acceptance authority but still inside the process-security/resource boundary. A native extension that can mutate trusted prover state or bypass checks belongs in a different trust class even if it is marketed as proof automation.

**Evidence role:** LCF literature, existing TCB-accounting report, and derived Anneal application.

### Durable acceptance needs identity and compatibility in addition to proof validity

A durable proof artifact can be perfectly valid and still be the wrong artifact.

Anneal therefore needs to bind accepted durable evidence to at least:

- the semantic obligation or theorem identity;
- the exact source/build/model generation to which that obligation belongs;
- the checker/prover and logical-environment compatibility needed to interpret the evidence;
- the trust assumptions under which the check was performed; and
- any dependency closure whose change would alter the theorem or its applicability.

A content hash is useful for byte identity but cannot prove that the hashed object is the current object Anneal needs. A source position is useful for presentation but is not stable semantic identity across edits. A worker epoch is useful for preventing cross-session reuse but intentionally invalidates after restart. These mechanisms solve different parts of the durable-acceptance problem.

The LCF lesson is therefore not "choose the right ID." It is "make authority explicit, then make the evidence that justifies transferring authority across boundaries explicit as well."

**Evidence role:** derived from LCF + current artifact-identity evidence.

### The lowest-risk Anneal design is layered acceptance authority

A practical Anneal design can keep four layers distinct.

**1. Proposal/search.** Agents, tactics, solvers, heuristics, and plugins propose proof work or candidate evidence. They have no direct authority to publish verification success.

**2. Logical checking.** A pinned checker validates the theorem/proof/certificate under a known logical environment and produces an opaque checked result.

**3. Correspondence/currentness.** Anneal establishes that the checked theorem is the right theorem for the exact Rust source/build/model generation and that every promise-relevant artifact is current or intentionally trusted.

**4. Publication.** A generation-fenced authority transition makes that fully justified result current. Stale successful computations remain historical evidence but cannot overwrite newer state.

This architecture preserves the strongest LCF insight while fitting Anneal's broader problem. It also leaves implementation choices open. The checked result might be a Lean environment handle, a proof term, a certificate, a verified-result record backed by a worker session, or another representation. What matters is that each boundary states what it proves and cannot be bypassed accidentally by code from another layer.

The serious simpler alternative is to avoid durable checked handles and re-run the authoritative proof path on every request. That reduces persistence complexity at a potentially large latency cost. Anneal should prefer that simpler model until measured workloads justify durable proof authority, but it should preserve the layer boundaries so later caching does not require redefining what "verified" means.

**Evidence role:** derived architectural judgment under current Anneal authority.

## Boundaries

No LCF, HOL, Lean, Lake, Charon, Aeneas, or Anneal executable was run for this report.

The historical mechanism is reconstructed from primary LCF publications and later system exposition. The report does not claim that every prover commonly called "LCF-style" preserves the same trust boundary or uses the same theorem representation.

The Lean artifact discussion reuses exact-pinned reports already present in `reference`; it does not independently reproduce those experiments here. It does not claim `.olean` artifacts are unsound. It uses their identity and freshness boundary to show that serialized-environment acceptance differs from in-process theorem construction.

The report does not measure the latency, storage, or compatibility costs of proof-term replay, certificate checking, trusted compiled environments, or full recomputation. Those costs could change which persistence design is practical without changing the logical distinctions above.

A small checker does not automatically establish source semantics, translator correctness, currentness, or operational containment. Conversely, these additional obligations do not diminish the value of concentrating logical acceptance authority in a small checked path.

Anneal implications are derived analysis, not adopted project policy.

## Evidence

**Primary historical evidence.** Gordon et al., *A Metalanguage for Interactive Proof in LCF* (POPL 1978, DOI `10.1145/512760.512773`) establishes ML as the proof-programming metalanguage and the abstract-theorem-value architecture. Gordon, Milner, and Wadsworth, *Edinburgh LCF: A Mechanised Logic of Computation* (1979, DOI `10.1007/3-540-09724-4`) documents the mechanized logic and trusted inference machinery. Milner, *LCF: A Way of Doing Proofs with a Machine* (MFCS 1979, DOI `10.1007/3-540-09526-8_11`) gives a contemporary rationale for the architecture. Paulson, *Logic and Computation: Interactive Proof with Cambridge LCF* (1987, chapter DOI `10.1017/CBO9780511526602.008`) gives the later theorem/tactic/validation exposition used above.

**Later LCF-family continuity.** The official HOL theorem-prover reference for `Thm.thm` retains an abstract theorem type whose values arise through primitive inference rules and explicitly situates that mechanism in the Milner/LCF lineage. This report uses that only as continuity evidence, not as a claim that HOL and LCF have identical TCBs.

**Current reference evidence.** `lean-olean-format-identity-v4-30-0-rc2` supplies the bounded observation that `.olean` is serialized module data and that loader acceptance is not itself a source-freshness proof. `lean-module-import-semantics-v4-30-0-rc2` supplies the module-resolution and transitive-artifact identity boundary. `tcb-accounting-patterns-verification-systems-2026-09-27` supplies the broader distinction among logical checking, source/model correspondence, and other trust layers.

**Anneal authority.** `anneal/PRINCIPLES.md` and `anneal/DESIGN.md` at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` define the project-level constraints applied here: precise success scope, justified Rust semantics, fail-closed behavior, explicit trust, and preservation of promise-relevant effects. The proposed acceptance layers are derived from those constraints and the historical evidence; they are not themselves normative Anneal design.

## Revalidation

Revalidate the historical portion if a later review finds that the cited LCF sources do not support the abstract-theorem-constructor/validation account used here or identifies an important contemporary mechanism that materially changes that account.

Revalidate the artifact-boundary comparison when Lean's compiled-module/load contract changes, when `reference` supersedes either cited Lean identity/freshness report, or when Anneal adopts a portable proof/certificate representation with a documented checking and compatibility contract.

For an implementation decision about persistent checked results, the cheapest decisive experiment is not another literature survey. Prototype two paths for one representative Anneal workload:

1. a fresh-process path that rebuilds/rechecks from authoritative inputs; and
2. a persistent/cached path whose checked handle or proof artifact is bound to explicit source/model/environment generations.

Measure latency and storage, then deliberately change source, translation inputs, imported proof dependencies, checker/tool versions, and worker generations. The cached design is acceptable only if every promise-relevant change either causes rechecking/reconstruction or becomes an explicit trust assumption, and stale checked results cannot acquire current publication authority.