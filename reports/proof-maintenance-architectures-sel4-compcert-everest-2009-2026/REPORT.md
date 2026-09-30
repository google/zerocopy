# Proof maintenance architectures: seL4, CompCert, and Project Everest, 2009–2026

## Summary

Mature verification systems reduce proof-maintenance cost by stabilizing the *semantic interfaces that proofs depend on*, not by freezing implementations and not by verifying every tool in the development path. The three systems examined here reach that result through different architectures.

seL4 places several specifications and refinement proofs between the abstract kernel contract and generated representations of the C implementation. It also records exact known-working combinations of kernel, proofs, and theorem prover in a verification manifest. Recent maintenance history shows both sides of that design. A three-line strengthening of a configuration bound required no downstream proof repair because existing obligations already implied the new fact. Reserving a hardware address-space identifier, by contrast, introduced a new invariant and changed many architecture-specific proof files. A library cleanup that made two functions extensionally equivalent was deliberately *not* substituted because different simplifier behavior was expected to break proofs. Stable semantic layers limit propagation, but the effective proof interface also includes normal forms, theorem names, automation behavior, and tool versions.

CompCert makes the semantic boundary more explicit. Individual passes export simulation theorems, and generic composition machinery builds the whole-compiler result from those theorems. A pass can therefore change internally without forcing unrelated proofs to change while its semantic relation remains stable. CompCert also illustrates the opposite case: changes to shared memory-injection machinery touched many pass proofs, and a later compatibility shim deliberately retained an old theorem for downstream users such as VST. The architecture gives maintainers a concrete place to spend compatibility effort: shared proof interfaces rather than every implementation detail. It also supports a serious alternative to verifying a transformation implementation: an unverified transformation can sit behind a proved validator that rejects outputs whose required relation cannot be established.

Project Everest and HACL* attack a different source of maintenance cost. Their Low* work uses high-level, reusable specifications and verification abstractions, then specializes and extracts low-level code. The ICFP 2023 authors report that these techniques were critical to scaling HACL* beyond 100,000 lines of verified source and materially improved proof-engineer productivity; one generic streaming development was reused across more than a dozen cases. At the same time, current repositories pin F*, KaRaMeL, solver, and proof-hint state, keep generated C/assembly under version control, and contain explicit maintenance commits for proof instability and generated artifacts. This is evidence that modular proofs and generated production artifacts can coexist, but the generator, solver behavior, platform glue, and artifact provenance remain real boundaries rather than disappearing behind the verified source.

The conditional implication for Anneal is to stabilize a small set of proof-facing contracts and make everything else replaceable. Strong candidates are: source-to-model correspondence, canonical proof-obligation schemas, assumption/trust declarations, artifact identities, and fail-closed acceptance relations. Anneal should not require every preparatory tool, normalizer, generator, or agent to be verified before use if a narrow checked interface can establish the property that later stages need. It should also avoid making incidental prover terms, generated syntax, or RPC object identities durable APIs when those details can be reconstructed. However, the seL4 history warns that semantic abstraction alone does not eliminate proof churn: if automation depends on a representation's simplifier behavior or theorem vocabulary, that representation has become a de facto interface and should be versioned, normalized, or deliberately hidden.

This is a comparative engineering judgment, not an adopted Anneal design policy. No proof development was executed for this report. The evidence is exact repository history, current project documentation, published proof results, and existing reference reports used as supporting evidence rather than as substitutes for this J025 judgment.

## Applicability

This report addresses #3732 J025: **seL4, CompCert, and Project Everest: architecture under proof maintenance**. It asks how module contracts, abstraction layers, generated code, and trusted components affected repair in mature verified systems; it also separates proof-development artifacts from production paths.

The report uses three kinds of subject.

**seL4.** The current proof-corpus snapshot is `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, paired for configuration-control evidence with `seL4/verification-manifest@f1f7a4289585e9610733ea041c1849e46af9701b`. Selected 2025–2026 commits are examined as maintenance cases. Earlier seL4 publications and current project documentation provide the proof-architecture and trust-boundary context. The report does not claim that every proof layer or configuration has the same maintenance behavior.

**CompCert.** The semantic-composition discussion uses the 3.18 development at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, matching existing reference coverage of the pass-composition machinery. Selected nearby 2026 commits show how maintainers changed shared memory relations and preserved compatibility for external proof clients. Those commits are maintenance evidence; they do not make this report a complete history of CompCert.

**Project Everest.** The current concrete subjects are `hacl-star/hacl-star@504c2987452f87fe44bce9b9f12e19d6e051761f`, `FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, and `project-everest/everest@2a3f67dab56be02d1793b2801ef08f368423a3ac`. The ICFP 2023 HACL* proof-engineering paper provides the strongest reported-outcome evidence about modularity and productivity. Repository history supplies more recent evidence about pins, proof hints, generated artifacts, and CI stability.

The comparison is about *maintenance architecture*, not theorem strength. seL4's refinement stack, CompCert's pass simulations, and HACL*'s Low* abstractions prove different properties about different systems. Their mechanisms should not be ranked by a single “amount of verification” scale.

The historical period in the title begins with seL4's original functional-correctness work and ends at the exact source revisions observed on 2026-09-30. Not every year is sampled. The selected changes were chosen because they expose a maintenance mechanism or boundary clearly, not because they form a statistically representative sample.

## Findings

### Maintenance cost enters through at least five distinct interfaces

Across these systems, “a code change broke the proof” is too coarse to guide architecture. The evidence separates at least five ways maintenance can propagate.

1. **Semantic-contract change.** A changed invariant, memory relation, or externally visible behavior invalidates statements that genuinely depend on it.
2. **Representation change.** The semantics may remain equivalent while proof terms, normal forms, generated syntax, or lemma shapes change.
3. **Automation/toolchain change.** A theorem prover, SMT solver, simplifier, compiler, or proof-hint format changes how the same obligations are discharged.
4. **Generated-artifact change.** Source and proof can remain conceptually aligned while generated C, assembly, manifests, or derived proof inputs need regeneration and identity control.
5. **Trusted-boundary change.** Moving a transformation into or out of the proved path changes what the final assurance statement assumes even if the implementation behavior stays the same.

A stable architecture can isolate some of these axes, but no single abstraction boundary isolates all five. The useful question is which axis a proposed interface is meant to stabilize.

Basis: **derived** from the seL4, CompCert, and Project Everest cases below.

### seL4 separates abstract behavior, implementation correspondence, and proof configuration

The current `l4v` repository preserves several semantic layers instead of proving every property directly over the C syntax.

The repository identifies an abstract functional specification, a Haskell model, a machine interface, automatically imported C semantics, and additional domain-specific specifications such as capDL. Its proof tree then contains separate refinement layers and security developments: abstract invariants, abstract-to-design refinement, design-to-C refinement, access control, information flow, and binary-refinement components. Generated inputs connect the proof tree to the Haskell model and the kernel C source.

That decomposition makes the proof graph explicit. A change can be local to one architecture or one refinement edge if it preserves the contracts above and below that edge. It can also propagate widely when it changes an invariant used by several later developments.

The current build guidance reinforces the distinction between source and generated proof input. Sessions that depend on generated specifications should be built through `run_tests` or the supplied Makefiles so those inputs are regenerated before checking. Thus generated specs are not an informal convenience. They are part of the reproducible path by which concrete kernel state enters the proof.

Basis: **source/documentation** — `seL4/l4v@6b4076a...`, `README.md` and `docs/setup.md`.

### A behavior-preserving change can be almost free when it stays behind an existing obligation

Commit `bce918b83bd9deaf91c3b9e7c3678929c4ad5799` changed the permitted `numDomains` configuration bound so 256 domains are allowed. The patch changed only three lines in `spec/machine/Kernel_Config_Lemmas.thy`.

The commit message records the notable maintenance result: no existing proof broke. Existing obligations already had the form needed to establish the stronger boundary fact, so the local configuration correction did not require downstream repair.

This is the best small example in the sampled history of a stable proof interface doing its job. The implementation/specification fact changed, but the propositions consumed downstream did not need to change.

Basis: **source/history** — exact `l4v` commit `bce918b83bd9deaf91c3b9e7c3678929c4ad5799`; 2 insertions, 1 deletion, one file.

### A new invariant crosses layers even when the implementation edit is conceptually small

The reserved-VMID and reserved-ASID changes show the opposite case.

For AArch64, commit `589b63f232d3c042cc7fc41f5fd304f2e7114e7a` updated proofs after reserving VMID 0. The proof change added the invariant that the “next VMID” is never the reserved value and an explicit sanity lemma that allocation never returns that value. It changed nine proof files across invariant, refinement, C-refinement, and information-flow material, with 171 additions and 93 deletions.

The analogous ARM/ARM_HYP proof update, `411e76099fff81c09cd4eb6619cef13d8d9bb6cf`, introduced a reserved-ASID invariant and repaired or reorganized proofs across 36 files, with 891 additions and 589 deletions. The commit also reused proof setup from the AArch64 work.

The important point is not the raw line count. The new fact was globally relevant. The proof architecture localized the *kind* of obligation—state invariants and the refinements that preserve them—but it could not make the obligation disappear. Reusing the AArch64 setup reduced duplication after the concept became shared.

For Anneal, this argues against judging a boundary only by how many files a change touches. If a Rust-level guarantee gains a genuinely new invariant, several proofs may correctly need revision. The architectural goal is to make those dependencies explicit and reusable, not to suppress necessary repair.

Basis: **source/history** — exact `l4v` commits `589b63f...` and `411e760...`; **derived** application to Anneal.

### Proof-facing representation is an interface even when the functions are extensionally equivalent

Commit `9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f` adjusted the `HaskellLib` `init` function so it became equivalent to Isabelle's `butlast`, then proved the equivalence. The maintainer explicitly did *not* replace `init` with `butlast`: the formulations had different simplifier behavior, and proofs were expected to break.

This is a direct counterexample to a tempting architecture rule: “If the semantic contract is unchanged, proof clients will not care.” Interactive and automated proof scripts consume representations, rewrite rules, theorem names, and normal forms in addition to denotational meaning.

A stable semantic interface still helps, but the system needs one of three additional strategies when proof automation is representation-sensitive:

- preserve a compatibility-facing proof API;
- normalize both representations to a deliberately stable proof form; or
- accept and budget for proof migration when the proof API changes.

For Anneal, this argues for separating durable semantic artifacts from prover-specific surface syntax. If generated Lean terms or Aeneas output shapes become direct long-lived dependencies of many proofs, those shapes are effectively public APIs whether or not the architecture document calls them APIs.

Basis: **source/history** — exact `l4v` commit `9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f`; **derived** application to Anneal.

### seL4 treats the toolchain combination as configuration-controlled proof state

The `verification-manifest` repository records the repository collection needed to replay proofs. Its current README says `default.xml` and `mcs.xml` contain latest tested-as-working combinations and point to exact revision hashes. Development manifests combine moving proof branches with fixed kernel revisions; successful CI updates the tested manifests. Release manifests preserve the proof/kernel/tool combinations for official releases.

The current seL4 release documentation goes further: each release has a proof manifest recording the matching proof revision and the Isabelle/HOL version that can check it.

The 2025–2026 `l4v` history makes the reason visible. A series of commits migrated distinct proof sessions and libraries to Isabelle2025-2. These are proof-maintenance changes even when the kernel behavior they establish has not changed.

The manifest therefore stabilizes a *replay boundary*, not a semantic theorem boundary. It answers “which exact moving components are known to work together?” rather than trying to prove that arbitrary versions are interchangeable.

Anneal should preserve the same distinction. A theorem can be semantically version-independent while the procedure that reconstructs it is not. Pins and environment identities belong in provenance and replay state even when they do not belong in the theorem statement.

Basis: **source/documentation/history** — `seL4/verification-manifest@f1f7a428...`, `README.md`; `seL4/l4v` Isabelle2025-2 migration commits; current seL4 release documentation.

### seL4 keeps proof coverage and trusted exclusions explicit instead of making the pipeline look fully verified

Current seL4 documentation says a changed kernel is not formally verified until the proofs are changed or the change is shown not to affect them. The FAQ also distinguishes proof input from explicit assumptions: C reached by verified kernel entry points must be proved, explicitly assumed, or unreachable. Machine-interface functions and boot code are named examples of assumed regions.

The project's binary-correctness work closes additional compilation/linking gaps for supported configurations, but it does not turn every hardware-facing operation into proved code. Current documentation continues to list assumptions and configuration-specific coverage.

This separation matters for maintenance. A trusted component can change without triggering a proof repair precisely because it is outside a theorem—yet the final assurance statement must then continue to name the assumption. “No proof broke” is not evidence that a trusted-boundary change preserved the proved property.

Basis: **documentation/publication** — current seL4 proof/FAQ pages; PLDI 2013 binary-validation result; **derived** trust-boundary interpretation.

### CompCert puts pass implementations behind semantic-preservation relations

CompCert 3.18's proof architecture makes a different interface choice. Individual compiler transformations establish simulations between formal languages. Generic theorems in `common/Smallstep.v` compose those relations; `driver/Compiler.v` applies the pass-level theorems to obtain the whole-compiler result.

A later stage therefore depends on the semantic relation exported by an earlier stage, not on the earlier stage's algorithm. Optional passes are handled explicitly: an enabled pass supplies its proof, while a disabled pass contributes an identity simulation. Failure to compile is also explicit; successful output is a premise of the final correctness theorem.

This is a strong maintenance boundary because it gives pass authors room to rewrite an optimizer or lowering algorithm without rewriting the proof architecture around it, provided they can re-establish the same relation.

Existing reference report `verified-compiler-pass-composition-compcert-3-18-popl-2008` preserves the detailed theorem structure. This report uses that result as evidence and asks the J025 maintenance question instead of duplicating the pass-composition analysis.

Basis: **source** — `AbsInt/CompCert@74cbdbf...`, `common/Smallstep.v`, `driver/Compiler.v`; **existing reference evidence** — `verified-compiler-pass-composition-compcert-3-18-popl-2008`.

### Shared semantic relations are high-leverage—and high-blast-radius—interfaces

CompCert's 2026 memory-injection changes show the cost of changing a shared proof interface.

Commit `2f5e3204c48510f94c91699c64dee8bd18cd2b75` strengthened memory injections so metadata stored at negative block offsets could not become normally accessible after injection. The change repaired the semantic foundation for `free`; it touched the common memory model and several proof users.

Commit `59b473374b23660f587230969b48ff407241dc19` then introduced `Senv.inject`, `Genv.inject`, and `Val.inject_ptr_flat`, replacing older event/global-preservation machinery and factoring shared code used by pass proofs. The change affected 16 files, including inlining, stacking, unused-global, Cminor-generation, local-simplification, global-environment, value, and target-operation developments.

This is exactly where a mature verified system should experience broad proof repair: the changed relation is intentionally a shared semantic hinge. The repair cost is evidence of dependency, not necessarily bad modularity.

The architectural implication is to keep such relations few, explicit, and semantically meaningful. Hiding them behind a large “compiler internals” module would not remove their logical reach; it would only make the reach harder to audit.

Basis: **source/history** — exact CompCert commits `2f5e320...` and `59b473...`; **derived** maintenance judgment.

### Compatibility shims can protect downstream proofs while a shared interface evolves

After the injection refactor, commit `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` restored `Events.meminj_preserve_globals` for backward compatibility. Its commit message names VST and other downstream projects and says the compatibility theorem can be removed after a few releases.

This is a small but important maintenance mechanism. Proof libraries can offer migration windows just as ordinary software libraries do. The shim does not freeze the new internal organization. It preserves an old theorem-level interface long enough for dependent developments to move.

For Anneal, the analogous interfaces may be obligation schemas, result records, provenance formats, or named semantic adapters. A bounded compatibility layer can be cheaper than forcing every proof artifact and external integration to migrate atomically.

The cost is also familiar from software engineering: every compatibility surface must be maintained and eventually retired. The lesson is not “never break proof APIs.” It is to identify them as APIs and choose migration policy deliberately.

Basis: **source/history** — exact CompCert commit `74cbdbf...`; **derived** application to Anneal.

### A verified validator can replace a verified transformation implementation at a maintenance boundary

Tristan and Leroy's verified-validator pattern, also instantiated inside the broader CompCert tradition, provides a serious alternative to proving a transformation implementation.

An optimizer may remain unverified if a proved validator checks the concrete source/output pair and the wrapper returns success only when the validator establishes the required semantic relation. The unverified algorithm can then evolve without entering the correctness proof. The validator and its relation become the stable verified boundary.

This is especially relevant to Anneal because several useful components may be expensive to verify: extraction tools, normalizers, code generators, search procedures, or agent-produced transformations. If the result can be checked cheaply, verifying the checker can move proof maintenance from an implementation with many design changes to a smaller relation with fewer changes.

The tradeoff is completeness and per-artifact work. A validator can reject a correct output that it cannot establish, and every changed output must be checked. If the relation is too weak, later proof stages still cannot compose the result.

Basis: **publication** — Tristan and Leroy, POPL 2008, DOI `10.1145/1328438.1328444`; **derived** Anneal application.

### Project Everest puts reusable proof abstractions above generated low-level artifacts

HACL* verifies low-level cryptographic implementations in Low*, a subset of F*, and extracts them to C through KaRaMeL. The current HACL* repository describes memory safety, functional correctness, and secret-independence properties on the Low* source. It keeps generated C for current algorithms in `dist/`. Project Everest's integration repository can fetch “known good” tool revisions, replay verification, build generated artifacts, and test them.

This architecture deliberately separates proof-development language from production language. Production consumers can use the generated C/assembly without importing the whole proof toolchain, while proof engineers work against higher-level types and abstractions.

The ICFP 2023 HACL* engineering paper provides direct reported-outcome evidence for the approach. Its authors say their modularity and specialization techniques were critical to scaling HACL* past 100,000 lines of verified source and brought significant proof-engineer productivity gains. Their streaming case study captures one semantic pattern generically and applies it to more than a dozen use cases, with several instances integrated into CPython.

This is stronger evidence than merely observing a modular repository layout: the maintainers explicitly evaluated the architecture as a proof-engineering technique.

Basis: **source/documentation** — `hacl-star/hacl-star@504c298...`; **publication** — Ho, Fromherz, Protzenko, ICFP 2023, DOI `10.1145/3607844`.

### Zero-cost specialization reduces duplicate proof work, but it does not make extraction or deployment disappear from the trust model

KaRaMeL's current design document describes a long transformation pipeline: typed AST conversion, monomorphization, tuple and data-type elimination, simplification, inlining, statement conversion, translation to C*, translation to a C AST, and pretty-printing.

The document also labels a key internal condition an “unverified invariant”: after several transformations, the program is expected to fit the Low* subset used for the later translation. KaRaMeL's README points to a paper formalization relating Low* to CompCert Clight, but the current implementation is not thereby turned into a fully mechanically verified compiler.

This does not negate the value of HACL*'s source proofs. It fixes the boundary of the claim. Verification can live at a reusable high level while the system separately controls generation, tests generated artifacts, pins tool versions, or uses additional validation where required.

For Anneal, the corresponding design is attractive when proof objects or kernel checking can validate the final result. An unverified producer is acceptable only if the acceptance boundary establishes the property Anneal reports. If the producer's correctness itself is part of the claim, the producer or its output relation needs stronger evidence.

Basis: **source/documentation** — `FStarLang/karamel@9abbb865...`, `README.md` and `DESIGN.md`; **derived** trust-boundary analysis.

### Pinned tool versions and proof hints are maintenance state, not incidental build trivia

Current HACL* history contains a concrete proof-stability episode. Commit `bfb6db8ecc67f36754d257500c2a0f1e2f6be609` says a Vale proof passed locally but failed in the Everest build and `check-world`; the proof was adjusted to make it more stable. The merged change `ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa` combined proof stabilization with F* and KaRaMeL dependency pins and regenerated a large set of proof hints.

Nearby history also reverted to Z3 4.8.5 because newer behavior caused performance regressions. This is not a semantic change to the cryptographic function. It is a change in the automation environment used to establish the same kind of fact.

Project Everest addresses this class of maintenance by recording known-good revisions and using CI to exercise the combination. HACL* versions proof hints and generated artifacts. These mechanisms trade some repository churn for replayability.

Anneal should treat solver/prover versions, elaboration options, generated-hint formats, and environment fingerprints as explicit provenance when they affect proof replay. They should not automatically become part of the *semantic* identity of a Rust-level claim, but they do belong to the reconstruction path.

Basis: **source/history** — exact HACL* commits `bfb6db8...`, `ecbf1aaa...`, and `43ffda45...`; **source/documentation** — Project Everest integration repository.

### Generated artifacts need synchronized provenance even when the high-level proof is the source of authority

HACL* repeatedly regenerates proof hints and `dist` artifacts in CI/history. Commit `ee6ac4d2b58fb3da421086e778132800fb3f0e37` is a small example whose message is simply “Fix generated and source file both”; it updates both a generated/distribution-side Makefile and its corresponding source-side file. Project Everest documentation emphasizes that generated C/assembly is kept under version control so users can build the artifacts without rebuilding every verification tool.

This creates two maintenance obligations:

- the verified source and generation recipe must remain reproducible; and
- the checked-in/generated production artifact must be demonstrably the one produced from the intended source/tool configuration.

Version control makes the artifact durable but does not itself prove correspondence. CI regeneration, hashes, validators, or reproducible-build checks are the mechanisms that can close that gap.

For Anneal, this maps directly to generated Lean, normalized IR, or cached proof obligations. Keeping derived artifacts can reduce latency and make debugging easier. They should carry source identity and generator identity, and ordinary success should fail closed if the artifact cannot be shown to correspond to the source state under which its proof is claimed.

Basis: **source/history/documentation** — HACL* and Project Everest; **derived** Anneal application.

### The strongest reusable architecture is a stable checked contract plus replaceable producers

The three systems converge on a pattern even though their mechanisms differ.

- seL4 protects high-level claims with refinement layers and exact configuration control.
- CompCert protects pass composition with semantic simulation interfaces and can place unverified computation behind a verified validator.
- Project Everest protects proof reuse with high-level verified abstractions, then manages a versioned extraction and integration path to low-level artifacts.

The common unit is not “a verified tool.” It is a *contract that later reasoning can rely on and an explicit story for how evidence crosses that contract*.

A tool behind the boundary may be:
- proved correct;
- checked per output;
- restricted to a trusted computing base;
- tested and pinned while the final claim names the assumption; or
- rejected for ordinary verified results.

These choices have different assurance and maintenance costs. The architecture should make the choice visible instead of forcing every component into the same proof strategy.

Basis: **derived** comparative judgment.

### Stable interfaces have four recurring failure modes

The evidence also shows when “add an interface” does not solve proof maintenance.

**The invariant really changed.** The seL4 ASID/VMID cases needed new global facts. No wrapper could soundly preserve the old theorem without changing the claim.

**Proof automation consumed representation details.** The `init`/`butlast` case shows equivalent semantics can still produce different simplifier behavior.

**The shared relation itself changed.** CompCert's memory-injection repair legitimately affected many proof clients.

**The environment changed.** Isabelle, F*, Z3, hints, and generated inputs can invalidate replay without changing the theorem's intended mathematics.

Anneal should therefore record separately:
- semantic version of the obligation/claim;
- proof-facing representation version;
- toolchain/replay identity; and
- concrete generated artifact identity.

Collapsing those into one “version” either causes needless invalidation or hides a real dependency.

Basis: **derived** from the sampled cases.

### Serious alternatives trade recurring proof repair against trust and up-front verification work

The systems suggest several defensible placements for an Anneal boundary.

**Prove the transformation implementation.** This gives a reusable correctness theorem for every successful run. It can reduce per-output validation cost, but changes to the implementation or its semantic model may require proof repair. This is attractive for small, stable, security-critical transformations.

**Validate each output.** A smaller checker can keep a fast-changing producer out of the trusted proof path. This shifts cost to validator completeness and per-artifact checking. It works best when the required relation is cheap to decide or produce a certificate for.

**Use a high-level verified DSL plus extraction.** Project Everest shows that reusable specifications and specialization can improve proof productivity and retain low-level performance. The extraction path must still have an explicit trust/correspondence story.

**Trust and pin a component.** This is the cheapest engineering option when the component cannot yet be verified or validated. It is acceptable only if the final result reports the assumption rather than presenting it as proved. Pins improve reproducibility; they do not improve theorem strength.

**Preserve compatibility adapters.** CompCert's compatibility lemma lets downstream developments migrate gradually. This lowers coordinated-upgrade cost but accumulates interface debt.

**Freeze the whole toolchain.** This maximizes reproducibility in the short term but eventually accumulates ecosystem, security, and maintenance debt. seL4 and HACL* instead record exact working sets while still performing explicit migrations.

No one alternative dominates. The maintenance question is which interface is most stable relative to the expected change rate and which trust boundary is acceptable for the claim Anneal wants to make.

Basis: **derived** from the examined mechanisms.

### Conditional judgment for Anneal

If Anneal adopts lessons from these systems, the first interfaces worth stabilizing are semantic and evidentiary rather than tool-shaped.

A plausible set is:

1. **Source-to-model correspondence.** Every translated subject should identify the Rust source state and the semantic relation the model is meant to preserve.
2. **Canonical obligation schema.** Proof obligations should expose stable logical inputs and assumptions even if Charon, Aeneas, Lean elaboration, or an agent changes internally.
3. **Assumption and trust declaration.** The result should name every unproved edge that matters to the reported Rust-level claim.
4. **Artifact identity and provenance.** Generated model/proof artifacts should bind to source, generator/tool revisions, relevant options, and environment facts needed for replay.
5. **Fail-closed acceptance.** An unverified or heuristic producer should not yield an ordinary verified result unless a trusted or proved boundary validates the property the later proof requires.
6. **Compatibility/migration policy.** When obligation or provenance schemas change, Anneal should know whether to provide adapters, invalidate old derived state, or require proof migration.

This architecture would let Anneal use unverified tooling early without pretending that tooling is proved. It would also let later verification replace trust with proof or validation one edge at a time.

Two cautions follow from the maintenance evidence.

First, do not treat raw generated syntax as the durable semantic contract unless there is no cheaper normal form. The seL4 `init`/`butlast` case shows how quickly proof automation can become coupled to presentation. A small canonicalization layer may be more valuable than forcing every downstream proof to absorb generator churn.

Second, do not confuse a stable checker with a stable reconstruction path. Tool versions, generated hints, environment preparation, and cache identities may remain essential to replay even if they are outside the theorem. Provenance should preserve them without elevating them into theorem semantics.

These are derived design implications, not adopted Anneal policy.

## Boundaries

- **No fresh proof execution.** This report did not rebuild seL4, CompCert, HACL*, KaRaMeL, Vale, F*, or Project Everest. Repository state and published/documented results are evidence; successful replay is not newly observed here.
- **Selected changes, not a statistical study.** Commit cases were selected because they expose a maintenance mechanism. Their line counts measure patch size, not person-hours, cognitive difficulty, or causal maintenance cost.
- **Author intent is labeled as such.** Commit messages and project documentation report maintainer rationale. The report distinguishes those statements from the cross-system conclusions derived here.
- **Reported outcomes are strongest for HACL*.** The ICFP 2023 authors report proof-engineer productivity and reuse outcomes. Comparable quantitative maintenance studies were not found for the selected seL4 and CompCert cases.
- **Current HACL* is not the 2017 code base.** Its README explicitly discourages citing the old HACL* paper for the current incarnation because that code no longer exists. Historical continuity here is architectural and methodological, not a claim of unchanged code ancestry.
- **KaRaMeL is not treated as fully mechanically verified.** Its current design document describes an unverified internal invariant. Paper formalization and source-level verification therefore do not justify silently removing extraction from the trust/correspondence discussion.
- **seL4 proof coverage varies by configuration and property.** A proof architecture example from one architecture does not establish identical coverage or repair cost on another.
- **CompCert's verified compiler core is not the whole deployment toolchain.** Existing reference evidence records ordinary assembler/linker and hardware correspondence boundaries separately.
- **No causal claim from absence of proof breakage.** A change that does not break current scripts may still alter an unmodeled property. The `numDomains` case is useful because the commit explicitly explains why the existing proof obligation remained sufficient.
- **Anneal implications are derived.** This report does not establish that Charon, Aeneas, Lean, or any current Anneal component already provides the recommended interfaces or that a specific validator is feasible.
- **Adjacent reference reports are evidence, not J025 disposition.** Reports on TCB accounting, assembly/ISA boundaries, and CompCert pass composition answer neighboring questions. They do not by themselves adjudicate proof-maintenance architecture.

## Evidence

### seL4 proof corpus and configuration control

Repository: `seL4/l4v`  
Revision: `6b4076aeb35f7803b7c232963e5f996545e3acb5`

- `README.md`, blob `03421c4b7db4e9756efde5f46f19e60970fc7288`
  - lists specification layers, generated C/design specifications, refinement/security proof directories, proof tools, and generated-session build requirements.
- `docs/setup.md`, blob `c20d7ba4fb16845977b4d205d725cb6c52a64eb9`
  - explains that the proof checkout is a coordinated repository collection and points to `verification-manifest` for known-working combinations.

Repository: `seL4/verification-manifest`  
Revision: `f1f7a4289585e9610733ea041c1849e46af9701b`

- `README.md`, blob `2b3f4a193bbb3012f9b7711f06bbb3dc2c98e352`
  - defines latest-tested, development, MCS, and release manifest roles.

Selected maintenance commits in `seL4/l4v`:

- `bce918b83bd9deaf91c3b9e7c3678929c4ad5799` — configuration-bound correction with no proof breakage.
- `589b63f232d3c042cc7fc41f5fd304f2e7114e7a` — AArch64 reserved-VMID proof update; new invariant across nine proof files.
- `411e76099fff81c09cd4eb6619cef13d8d9bb6cf` — ARM/ARM_HYP reserved-ASID proof update; broad repair and reuse of AArch64 proof setup.
- `9ae6b8106f5ef4dd14cb0e9543d9fe14101bbc4f` — proves `init`/`butlast` equivalence but deliberately avoids replacement because simplifier behavior would break proofs.
- `910c9762d46f097632851c5c92626e2b1915f7c0`, `d115a952c9bcf8e7912e29956cdb208a529187ec`, `d4a975e3a0ac41619f363ca9a073011f15117383`, `21de89eeb255427106d4426d2a8e89579f0fb041`, `d78df302c558e58a6f27933b0516bcd5955053db`, `02a52e2e775e3b71f2168a05bdb0392bd76e8abe`, `55070e5fb87604ff5855bc736b2bdd2bb83709fb`, `44badcfc889e852dcb8f395acd0d5d0ea83ef745`, `bfe148f0687398efa270d289b4c7a904ec103dbd`, `9b7b14847dbf2e9c4a0a99615951f2810e330d6d` — separate Isabelle2025-2 migration commits across tools and proof layers.

Current project documentation consulted on 2026-09-30:

- `https://docs.sel4.systems/projects/sel4/kernel-contribution.html`
- `https://docs.sel4.systems/releases.html`
- `https://sel4.systems/Verification/proofs.html`
- `https://sel4.systems/About/FAQ.html`

Published historical context:

- Gerwin Klein et al., “seL4: Formal Verification of an OS Kernel,” SOSP 2009.
- Thomas Sewell, Magnus Myreen, Gerwin Klein, “Translation Validation for a Verified OS Kernel,” PLDI 2013.

Evidence roles: **source**, **documentation**, **publication**.

### CompCert semantic interfaces and compatibility history

Repository: `AbsInt/CompCert`  
3.18 analysis revision: `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`

- `VERSION`, blob `5fd2882f6f042e89ce617586ce5041f5762c1766`
- `common/Smallstep.v`, blob `cefab134fdce4f3ea2f970db49a99d987c05d3a1`
- `driver/Compiler.v`, blob `60fc74fec1411216425004f6d63567354e146e9c`

Selected 2026 maintenance commits:

- `2f5e3204c48510f94c91699c64dee8bd18cd2b75` — strengthens memory injections to preserve hidden metadata assumptions; 374 changed lines across common memory and proof clients.
- `59b473374b23660f587230969b48ff407241dc19` — introduces shared `Senv.inject`, `Genv.inject`, and `Val.inject_ptr_flat` interfaces and refactors multiple pass proofs; 625 changed lines across 16 files.
- `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` — restores an old global-preservation theorem specifically for VST/other downstream compatibility.

Published validator pattern:

- Jean-Baptiste Tristan and Xavier Leroy, “Formal verification of translation validators: a case study on instruction scheduling optimizations,” POPL 2008, DOI `10.1145/1328438.1328444`.

Existing reference support used:

- `reports/verified-compiler-pass-composition-compcert-3-18-popl-2008`
- `reports/tcb-accounting-patterns-verification-systems-2026-09-27`
- `reports/assembly-isa-proof-boundaries-2013-2026`

Evidence roles: **source**, **publication**, **existing derived reference**. The current report's maintenance judgment is new derived synthesis rather than inherited coverage.

### Project Everest, HACL*, and KaRaMeL

Repository: `hacl-star/hacl-star`  
Revision: `504c2987452f87fe44bce9b9f12e19d6e051761f`

- `README.md`, blob `8815628e9cea88ca1cbb777e5f30cab98b66e012`
  - identifies the current verified-source properties, Low*→C workflow, `dist` artifacts, ValeCrypt, EverCrypt, and current publication guidance.

Selected maintenance commits:

- `bfb6db8ecc67f36754d257500c2a0f1e2f6be609` — stabilizes a Vale proof that behaved differently locally and in Everest/`check-world`.
- `ecbf1aaa83016c0b3e67c49c0f962afcdd3986fa` — merges proof stabilization with F*/KaRaMeL pins and regenerated proof hints.
- `43ffda45c9eb03ef2661f6b89c47f1d5a735a502` — returns to Z3 4.8.5 because of performance regressions.
- `ee6ac4d2b58fb3da421086e778132800fb3f0e37` — synchronizes source and generated/distribution files.
- `504c2987452f87fe44bce9b9f12e19d6e051761f` — CI regeneration of hints and `dist`.

Repository: `FStarLang/karamel`  
Revision: `9abbb865b10a0cd5c557da81c024c3965cb6ff53`

- `README.md`, blob `3c0396bb78ad3b8c252da3a0518eba029b2e7cc9`
- `DESIGN.md`, blob `1c61b9572744fa0fbb8f602129ea15aadaac6a36`

Repository: `project-everest/everest`  
Revision: `2a3f67dab56be02d1793b2801ef08f368423a3ac`

- `README.md`, blob `ce627659804164d6250a5ec1397c403c14af4418`
  - records known-good multi-repository revisions and proof-replay/build orchestration.

Current Project Everest documentation consulted on 2026-09-30:

- `https://project-everest.github.io/`
  - describes fetching blessed compatible revisions and building version-controlled generated C/ASM without first rebuilding all verification tools.

Published proof-engineering evaluation:

- Son Ho, Aymeric Fromherz, Jonathan Protzenko, “Modularity, Code Specialization, and Zero-Cost Abstractions for Program Verification,” PACMPL 7 (ICFP 2023), DOI `10.1145/3607844`.
  - authors report that the techniques were critical to scaling HACL* past 100,000 lines of verified source and improved proof-engineer productivity; the generic streaming development was reused across more than a dozen cases.

Evidence roles: **source**, **documentation**, **publication**.

### Evidence-role discipline

Commit messages are used for maintainer-reported rationale and observed patch scope. They are not treated as controlled measurements of proof cost.

Project documentation is used for intended architecture, workflow, and trust boundaries. Published papers are used for theorem claims and reported engineering outcomes. Cross-system maintenance rules and Anneal implications are labeled **derived** because none of the upstream sources adopts them as Anneal policy.

No **execution** evidence was added in this investigation.

## Revalidation

For a future J025 revalidation, broad re-research should not be necessary.

**seL4**

1. Read the current `l4v` README and current `verification-manifest` README.
2. Check whether the exact selected maintenance commits remain representative of the current proof architecture; they are immutable historical evidence even if the architecture evolves.
3. Inspect the newest kernel-change/proof-update pairs for a case that changes an invariant and a case that does not. Compare which proof layers move.
4. Check current release/FAQ documentation for changes to proof coverage, generated-input handling, and explicit assumptions.
5. If quantitative maintenance cost is needed, collect review/author-time data separately; patch size is not a substitute.

**CompCert**

1. Inspect the current generic simulation/semantic-preservation interfaces and the whole-compiler composition point.
2. Check whether `Events.meminj_preserve_globals` has been removed and what migration path external proof clients used.
3. Diff shared semantic relations such as memory injections before interpreting broad proof changes as implementation churn.
4. Check whether the assembler/linker and other downstream trust boundaries changed; do not infer that from pass-proof architecture.

**Project Everest / HACL***

1. Record the current exact HACL*, F*, KaRaMeL, Vale, solver, and integration pins.
2. Check whether generated `dist` artifacts and proof hints remain versioned and how CI establishes correspondence.
3. Search recent history for proof-stability, solver-version, regeneration, and source/generated synchronization commits.
4. Re-read the current extraction/compiler assurance statement before strengthening any claim about generated C.
5. If execution is available, replay the project's canonical verification command at the pinned revisions and preserve the result separately as **execution** evidence.

**Anneal application**

For any proposed stable interface, classify the dependency it is meant to isolate: semantic contract, proof-facing representation, toolchain behavior, generated artifact, or trusted boundary. Then test one realistic change from each relevant class. An interface is a useful maintenance boundary only if those tests show that irrelevant changes stay behind it while relevant assumption changes remain visible.

If Anneal later adds a validator or proof-producing boundary, revalidate the exact relation it establishes and its reject/failure semantics. Do not infer end-to-end adequacy merely because the checker itself is small or verified.