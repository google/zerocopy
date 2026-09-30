# Extensible proof automation without silently changing the claim

## Summary

Extensible provers need two properties that are easy to conflate: **freedom to search for proofs** and **authority to decide what counts as a proof**. F*'s Meta-F* architecture makes that distinction unusually visible, but it also shows where the distinction stops. Meta-F* gives user metaprograms an abstract proof state and a collection of primitive goal transformations. The intent is LCF-like: a tactic can diverge, fail, or search badly without thereby proving a false proposition, because the tactic cannot mutate proof state except through the provided primitives. This lets F* move application-specific proof search out of the core typechecker while keeping the proof-state mutation interface narrow.

That design does **not** mean that all of F*'s automation is outside its trusted computing base. F* normally discharges many verification conditions by encoding them for Z3 and accepting Z3's validity result without constructing a proof term. F*'s current book states the trust consequence directly: the verifier trusts its SMT encoding and the correctness of Z3. Meta-F* therefore separates *tactic implementation* from *proof-state authority*, but an SMT-discharge step still crosses an oracle-style acceptance boundary. A tactic that massages a verification condition into a form Z3 accepts has not converted F* into a small-kernel proof-term system.

F* also exposes an important engineering tradeoff between an extensibility boundary and an execution boundary. Meta-F* code can be interpreted, but it can also be compiled to OCaml and dynamically linked into the F* process. The 2019 Meta-F* work introduced native plugins to make large metaprograms practical, and the current source still supports generated and dynamically loaded tactic plugins. That improves performance substantially, but it changes the operational risk surface: arbitrary native code shares the verifier process. The logical argument about an abstract proof state and sound primitive transformations should therefore be kept separate from reproducibility, process integrity, crashes, resource exhaustion, and malicious-plugin concerns.

Lean and Rocq illustrate a different point in this design space. In their ordinary proof-term paths, tactics construct terms that a comparatively small trusted checker rechecks. Anneal's current Lean-specific reference material at the selected `v4.30.0-rc2` pin confirms both sides of that statement: ordinary tactic extensions manipulate goals and construct expressions that remain subject to Lean's normal declaration checking, while explicit mechanisms such as axioms, `sorry`, native-evaluation machinery, and `debug.skipKernelTC` have different trust consequences. The boundary is therefore not “tactics are safe”; it is “a producer is outside the logical acceptance authority only to the extent that its output is revalidated by the ordinary checker and it cannot invoke a separate trusted bypass.”

A third design point is proof-producing or certificate-checking integration of external automation. SMTCoq, for example, accepts witnesses from external SAT/SMT solvers and checks them with a certified checker in Rocq. This can remove the external solver from the logical TCB for the supported proof fragment, at the cost of a proof/certificate format, checker engineering, coverage limits, and potentially large certificates or reconstruction work. The contrast matters because the same user-visible command — “ask an SMT solver” — can have very different trust semantics depending on whether the solver's answer is accepted as an oracle or converted into evidence checked by the target prover.

For Anneal, the strongest reusable conclusion is to make extensibility authority explicit. A specialist tool may be very powerful without changing the meaning of an ordinary successful result if it is confined to a **proposal/search tier**: it may choose tactics, synthesize proof terms, propose certificates, or suggest edits, but acceptance still passes through the same pinned checker and the same claim-relative trust accounting as ordinary proofs. A mechanism that can add assumptions, bypass checking, replace source/model semantics, or cause an external oracle result to be accepted without independently checked evidence is a **trust or claim-mode extension**, not merely “automation.” That distinction should be visible in result identity and TCB accounting.

This is a conditional architectural judgment, not adopted Anneal policy. It follows from the current Anneal design contract's requirements that trust remain explicit, ordinary users retain a Rust-oriented interface, specialist proof machinery can coexist with that interface, and successful results never silently claim more than their evidence supports.

## Applicability

This report addresses issue #3732 question J023: **“F* and extensible provers: automation without changing the claim.”** It asks what happens when a prover lets specialists extend proof automation, how such extensions interact with the trusted boundary, and which parts of those designs Anneal can reuse without making ordinary Rust users reason about prover internals.

The primary F* source baseline is `FStarLang/FStar@78bb239b54cc113be68fb1dc0cbdfeb19378766a`, the `master` tip observed on 2026-09-30. Its `version.txt` is `2026.09.27`. The historical design anchor is Martínez et al., *Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms*, ESOP 2019, DOI `10.1007/978-3-030-17184-1_2`, together with the corresponding Microsoft Research technical-report/publication pages.

The Anneal baseline is `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`. In particular, `anneal/PRINCIPLES.md` states Anneal's claim-relative TCB promise and its requirement that ordinary Rust programmers not need to learn Lean, while `anneal/DESIGN.md` requires explicit, shrinkable trust and permits specialist access to lower-level proof machinery so long as all users operate against the same program contracts, trust model, and success semantics.

Lean-specific comparisons use Anneal's selected Lean baseline `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) as already characterized by the current `reference` reports `lean-tactic-extension-apis-v4-30-0-rc2` and `lean-trust-admissions-v4-30-0-rc2`. Current Lean documentation is useful as continuity evidence but is not substituted for the exact Anneal pin, because trust and native-evaluation mechanisms can change across releases.

SMTCoq is used as a design contrast, not as a proposal to adopt Rocq. The current repository baseline observed for that contrast is `smtcoq/smtcoq@3187cf12412a244859d7396e8088e6f9de0568d1`. The current repository describes SMTCoq as checking proof witnesses from external SAT/SMT solvers with a certified checker and exposing tactics that use those integrations.

## Findings

### 1. The key boundary is authority, not where the automation code runs

An extensible prover can execute a large amount of user-supplied automation without giving that automation authority to redefine truth. The architectural question is therefore not “can users write plugins?” but “what artifacts and state transitions may those plugins cause the verifier to accept without an independent check?”

Meta-F* makes this explicit in its public programming model. The current F* book describes tactics and metaprograms as F* terms in the `Tac` effect. Internally, that effect carries a proof state, exceptions, and possible divergence. The proof state is abstract to ordinary metaprograms, and metaprograms act through a set of primitives intended to make small, correct goal transformations. The book states the intended soundness argument directly: if the primitives preserve validity, arbitrary compositions of them cannot manufacture a false proof state merely by using unrestricted user-level tactic code.

This is an LCF-style *authority boundary*. It does not require the tactic language itself to be tiny. The tactic author can write loops, heuristics, reflection code, stateful search, and domain-specific automation. Those mechanisms determine *which valid transition to attempt*, while the primitive interface determines *which transitions the verifier will accept*.

The distinction matters for Anneal because specialist automation will likely grow faster than any stable user-facing proof language. A narrow acceptance boundary can let that automation evolve without forcing every tactic implementation, agent heuristic, or search strategy into the logical TCB. Conversely, merely putting code in a “plugin” package does not remove it from the TCB if the plugin can directly install unchecked facts or mutate the semantic environment with unchecked authority.

### 2. Divergence and failure are compatible with logical soundness, but not with availability

Meta-F* deliberately includes divergence in its tactic effect. Its documentation explains the reasoning: if a tactic loops, the verifier waits forever; it does not conclude the pending proposition. This is a useful separation between **soundness** and **liveness**. A tactic can be logically non-authoritative while still making the tool unusable through nontermination, excessive memory use, solver explosions, or poor search.

That separation should be preserved in Anneal's terminology. “Outside the logical TCB” must not be translated into “safe to run without limits.” Agent-generated or third-party proof automation can be soundness-neutral under a checking boundary and still require cancellation, CPU/memory limits, process isolation, deterministic inputs, or restartability. Those are orchestration and security properties rather than theorem-validity properties.

The same point applies to bad heuristics. A weak tactic may leave goals unsolved or make them harder for later automation. That is a completeness or productivity failure. A powerful but unstable tactic may create large proof terms or solver contexts. That is a performance and robustness failure. Neither failure should silently become evidence for a successful Anneal result.

### 3. Meta-F* was designed to complement SMT, not replace it with proof terms

The motivation for Meta-F* was not simply that F* lacked a tactic language. The 2018 technical report and 2019 ESOP paper describe a two-sided scalability problem. SMT automation handles many routine obligations with little user effort, but its behavior becomes brittle on difficult theories or large verification conditions. Traditional tactic systems give users more control, but asking tactic authors to solve every routine step themselves wastes the strength of automated solvers.

Meta-F* therefore lets tactics target the difficult parts of a proof and leave the “skeleton” to F*'s ordinary verification-condition machinery. The current F* book presents this as the normal style: a tactic may simplify, split, normalize, or selectively solve one assertion, while remaining obligations flow to Z3. The 2019 paper reports that this hybrid style improved robustness and performance in case studies, including nonlinear arithmetic and generated verified code.

The important architectural lesson is not “hybrid proof is always better.” It is that extensibility can be valuable when it operates at **semantic choke points** where generic automation is known to struggle. Anneal does not need one universal tactic subsystem to justify specialist hooks. It can expose a stable obligation boundary and let specialized automation act there, provided the resulting evidence remains interpretable under the same success semantics.

### 4. F*'s tactics are constrained, but F*'s SMT acceptance remains trusted

A common overgeneralization would be: “Meta-F* uses sound primitives, therefore user automation is untrusted and all accepted proofs reduce to a small checker.” That is not F*'s architecture.

The current F* book's SMT chapter states that F* encodes propositions into SMT logic and, when Z3 reports validity, accepts the fact without constructing an explicit proof term for that SMT result. It then names the trust consequence: F* trusts both its SMT encoding and Z3's correctness. The tactic framework narrows how a metaprogram itself transforms proof state, but a tactic can still ultimately hand a residual obligation to an oracle-style solver whose answer is trusted by the F* verifier.

That gives two independent trust questions:

1. **Can the tactic itself corrupt the proof state?** Meta-F*'s abstract proof state and primitives are intended to prevent this for ordinary tactic code.
2. **What evidence closes the remaining goals?** If the goal is discharged by F*'s ordinary SMT path, solver and encoding correctness remain part of the acceptance boundary.

For Anneal, these questions should be represented independently. A specialist extension can be outside the tactic-manipulation TCB while still selecting a proof route whose solver, model, or evaluator expands the final result's TCB. “Untrusted plugin” should never be used as shorthand for “no new trusted dependency.”

### 5. Proof-producing external automation is a real alternative, not just a theoretical ideal

SMTCoq demonstrates another architecture. Its current project description says external SAT/SMT solvers produce proof witnesses that a certified checker validates in Rocq. The external solver can still be buggy, time out, or emit an unsupported certificate, but an accepted theorem depends on the checker and the modeled proof format rather than on trusting the solver's yes/no answer for the supported fragment.

This pattern moves cost rather than eliminating it. The integration must define a certificate format, translate the original goal faithfully, cover the solver rules it intends to use, check potentially large witnesses efficiently, and report unsupported reasoning cleanly. A solver can gain features faster than the checker, so certificate coverage can lag solver capability. Proof reconstruction can also be more expensive than receiving a bare validity result.

The benefit is a sharper authority boundary. The search engine may be huge and aggressively optimized because it proposes evidence rather than final truth. That is especially attractive for automation generated or selected by agents: the agent can be wrong in arbitrary ways without a persuasive explanation becoming formal evidence.

For Anneal, this suggests a preference order rather than an absolute rule. Where Lean already has a compact proof term, reflection procedure, or certificate checker for a domain, specialist automation should preferentially emit what Lean can check. Where proof-producing integration would be disproportionately expensive, a trusted external solver or evaluator can still be used, but it should appear as an explicit trust-mode choice rather than being mislabeled as a merely heuristic plugin.

### 6. Native tactic compilation changes the operational boundary even when the logical interface is unchanged

Meta-F*'s performance story includes compiled metaprograms. The 2019 paper describes tactics as either interpreted or compiled to native code and dynamically loaded into the F* typechecker. The current repository preserves this capability. `examples/native_tactics/README` documents `--gen_native_tactics` and `--use_native_tactics`; the latter dynamically links `.cmxs` plugins and executes tactics natively. Current `FStarC_Tactics_Native.ml` maintains registered native tactic steps, and `--no_plugins` disables native plugin execution in favor of ordinary interpretation.

The paper frames the native-plugin mechanism as a way to execute verified source metaprograms efficiently. That helps the *logical* story if the same abstract primitive interface governs the metaprogram's intended proof-state effects. It does not make dynamic native code harmless as a process-level actor. Once arbitrary native code is loaded into the verifier process, memory corruption or malicious behavior in that code, the compiler/runtime, or foreign libraries can in principle affect the process outside the abstract interface that the source-level model describes.

The practical Anneal lesson is to record two boundaries separately:

- **logical authority:** which proof-state transitions or proof artifacts are accepted;
- **execution authority:** what code is permitted to execute in the verifier process and what it can do to files, memory, environment state, or other jobs.

For trusted first-party automation, in-process native execution may be a reasonable performance choice. For third-party or agent-generated extensions, a process boundary, capability restriction, or proof-producing protocol can provide much stronger operational containment without changing the proof model.

### 7. F*'s current tactic effect shows how a small interface can survive a changing implementation

The current F* source still exposes `FStar.Tactics.Effect.Tac` as the public effect for metaprograms. Its representation is a proof-state reference to a potentially divergent result, but the source comment explicitly says that representation exists for extraction and reification and “plays no role in typechecking.” The public abstraction therefore does not require clients to own the implementation representation of the tactic engine.

The same file exposes proof-oriented hooks such as `synth_by_tactic`, `assert_by_tactic`, preprocessing, and postprocessing interfaces. Some hooks synthesize terms or transform definitions; postprocessing is required to establish equality with the original definition, while preprocessing occurs before typechecking and changes what is subsequently checked. Those are materially different authorities even though they all use the same metaprogramming substrate.

This is a useful warning for Anneal API design. An API named “tactic” or “plugin” is too coarse to communicate trust. A hook that chooses among already-defined lemmas, a hook that synthesizes a proof term, a hook that rewrites generated Lean before checking, and a hook that rewrites the Rust-to-Lean model have different claim consequences. The interface should classify the *stage and accepted artifact*, not merely the implementation technology.

### 8. Lean's ordinary tactic extensions give Anneal a strong proposal/checker split at its current pin

Anneal already depends on Lean, so the most immediately relevant comparison is not hypothetical. The current `reference` report for Lean tactic extension APIs at `v4.30.0-rc2` records that a tactic elaborator is `Syntax → TacticM Unit`; it manipulates metavariable goals and constructs or assigns expressions. Ordinary resulting declarations still pass through Lean's normal declaration checking. Custom tactic modules can therefore centralize recurring proof search or stabilize generated proof syntax without becoming new kernel rules.

That is the architecture Anneal should exploit by default for specialist proof automation. A generated tactic invocation can be much shorter and more stable than a long low-level proof script while remaining merely a producer of material that Lean checks.

However, the adjacent trust report also records explicit exceptions to the simple story. Lean supports axioms and `sorry`; compiled implementation substitution and native evaluation have distinct trust consequences; and `debug.skipKernelTC` bypasses normal kernel checking. In addition, tactic metaprograms are executable code and may have operational side effects even when the final declaration remains kernel checked.

The useful rule is therefore precise: **a tactic is outside the logical TCB only for the claim that is independently rechecked after the tactic runs, and only if the tactic does not invoke a separate accepted bypass.** This rule composes naturally with Anneal's existing TCB-audit requirement.

### 9. Extension mechanisms should preserve claim identity across different proof routes

Suppose two Anneal runs establish the same Rust-level contract. One uses a short Lean proof term; the other invokes a custom tactic, which invokes an SMT solver, which produces a checked certificate. If both routes end in evidence accepted by the same checker under the same semantic assumptions, the *claim* can be identical even though the provenance and performance differ.

By contrast, if the second route adds an axiom, trusts an external solver result without checked evidence, uses a native evaluator whose behavior is accepted as truth, or changes the Rust-to-Lean translation rules, the trust assumptions differ. The result may still be useful, but it is not interchangeable with the first result merely because both print “verified.”

Anneal's result identity should therefore distinguish at least:

- the Rust subject and property being claimed;
- source/model and translation identities;
- the final checker and theorem identity;
- theorem-specific assumptions/admissions;
- trusted solver/evaluator or bypass mechanisms, when any;
- proof-producing automation provenance when useful for reproducibility, even if it is not itself trusted.

This follows directly from the existing `reference` report on claim-relative TCB accounting. J023 adds one refinement: an extension should be classified by whether it changes **search provenance**, **checked evidence**, or **accepted assumptions**.

### 10. The most useful Anneal abstraction is three tiers of extension authority

The comparative evidence supports a three-tier model.

**Tier 1: proposal/search extensions.** These can inspect goals, choose lemmas, synthesize proof terms, generate certificates, or propose source/proof edits. Their output is accepted only after ordinary checking. Bugs can cause failures, timeouts, bad suggestions, or resource waste, but not a stronger successful claim. Most custom Lean tactics and external proof-search agents should fit here.

**Tier 2: checked semantic transformations.** These can transform obligations, terms, or generated artifacts, but must provide evidence that a checker validates against a specified relation. Examples include a proof-producing simplifier, reflection with a proved checker, or an external solver whose certificate is validated. The transformation algorithm itself can remain outside the logical TCB, but the transformation relation and checker become part of the evidence boundary.

**Tier 3: trust/claim extensions.** These add axioms, admissions, trusted evaluators, unchecked native primitives, source-model assumptions, or oracle results that the final checker cannot independently justify. They are legitimate engineering tools, especially during development, but they change the TCB or success class and must be visible as such.

The tiers are about authority, not user interface. The same `anneal prove` command could invoke all three internally. What matters is that the resulting record does not erase which tier supplied the final evidence.

### 11. Ordinary users need stable obligations and diagnostics, not exposure to the extension machinery

Anneal's principles require a Rust-oriented ordinary interface. Extensibility does not conflict with that requirement if specialist mechanisms sit behind stable obligation and result contracts.

A Rust developer should see an obligation in source terms: what operation created it, what must hold, and why Anneal could not establish it. A specialist or agent may then use Lean tactics, proof search, reflection, or an external solver to discharge the same obligation. The specialist route should not change the obligation's source-level meaning merely because it uses a lower-level language.

This suggests separating the **obligation schema** from the **proof strategy**. If an obligation has a stable identity and semantics, Anneal can add new proof strategies without redesigning the Rust annotation surface. Conversely, if a new proof strategy requires changing what the obligation means, that is a semantic extension and should be reviewed at the claim layer rather than hidden inside plugin infrastructure.

This separation also helps agent tooling. An agent can query a goal, try several strategies, and discard failed attempts. Only the accepted theorem/evidence and its trust metadata need to become durable verification state.

### 12. Extensibility should not imply global plugin state

F*'s native plugins are loaded into the typechecker process, while Lean tactic registrations live in imported module/environment state. Both models are workable, but long-lived interactive Anneal sessions make global mutable plugin state especially risky.

A proof result should identify the extension environment that was active when the theorem was checked. At minimum, that means module/tool identities and configuration. Ideally, the environment is reconstructible from the subject's dependency closure rather than from mutable process history. This is consistent with Anneal's current interactive-architecture reference work, which already emphasizes immutable/versioned proof contexts and explicit input identity.

The reason is correctness, not merely reproducibility. If a query is answered against a prover process whose plugin set has changed since the source snapshot was created, “same file position” no longer identifies the same proof environment. A specialist extension should therefore participate in proof-context identity just as imported Lean modules and generated models do.

### 13. Sandboxing is orthogonal to logical checking and remains valuable

A kernel or certificate checker protects a proposition from being accepted on invalid evidence. It does not protect the host machine from arbitrary code executed during proof search. Native tactic plugins, elaborator metaprograms, external solvers, and coding agents can read files, consume resources, crash processes, or manipulate mutable state if the runtime permits it.

Anneal should therefore avoid deriving an execution-security conclusion from a proof-theoretic one. For untrusted or rapidly changing specialist automation, running the producer in a separate process with narrow capabilities can reduce operational risk even when the producer's logical output is independently checked. This is especially attractive when the interface is already “goal in, candidate proof/certificate out.”

The reverse is also true: a sandboxed solver whose boolean answer is trusted remains in the logical TCB. Process isolation does not create proof evidence. The two controls address different failure classes and should be documented independently.

### 14. The serious alternatives form a spectrum rather than one winner

Four architectures are defensible for different obligations.

**SMT-oracle acceptance.** The verifier encodes the obligation, asks a solver, and trusts a valid/unsat result. This maximizes automation and can keep proof artifacts small, but the solver and encoding remain trusted. F* uses this model for ordinary SMT discharge.

**Kernel-checked proof terms.** Automation constructs a proof term that the target kernel checks. This minimizes trust in the search procedure and naturally composes with theorem-specific assumption auditing, but generating and checking proof terms can be expensive or difficult for strong automation. Lean and Rocq use this model for their ordinary tactic paths.

**Proof witnesses with a certified or verified checker.** An external solver produces a certificate that a smaller checker validates. This can keep industrial solver performance while removing the solver from the logical TCB for covered rules. It adds certificate-format, reconstruction, coverage, and checker-maintenance costs. SMTCoq is an existence proof for this pattern.

**Trusted domain accelerators.** A system may deliberately accept a trusted evaluator, native reduction mechanism, axiom, or domain-specific oracle because the engineering cost of reconstruction is too high. This can be a reasonable tradeoff, but it should be named as trust rather than hidden behind the generic word “tactic.”

Anneal should support more than one point on this spectrum. Its design contract already anticipates trust that can later be replaced by evidence. The durable requirement is that the result says which point was used.

### 15. A defensible conditional judgment for Anneal

If Anneal wants specialist extensibility without weakening the ordinary success meaning, it should make **proposal/checking separation** the default extension contract.

Concretely, a specialist extension should normally receive a versioned obligation/proof context and return one of:

- a Lean proof term or declaration that ordinary Lean checks;
- a sequence of tactic/proof edits whose resulting declaration ordinary Lean checks;
- a certificate or witness accepted by a pinned checker whose soundness relation is part of Anneal's evidence;
- a failure, timeout, or “unsupported” result.

The extension may choose arbitrary heuristics inside that boundary. Anneal should treat its bugs as completeness, performance, or operational failures unless the extension is also granted a trust-changing capability.

Any extension that instead introduces assumptions, bypasses the checker, modifies source/model correspondence, or relies on an unverified oracle should cross an explicit boundary in result semantics. Anneal can still support such mechanisms, especially for development or for properties whose proof-producing automation does not yet exist, but the TCB audit log should identify them and the UI should not silently collapse them into the same assurance class.

This model preserves the ordinary Rust-facing promise while leaving substantial room for expert Lean code, agents, solver integrations, and future domain-specific automation. It also matches the design principle that trust should be shrinkable: a trusted solver today can later be replaced by a certificate checker without forcing the Rust contract or user annotation syntax to change.

## Historical development and rationale

Meta-F* emerged from a verifier that already relied heavily on SMT. Early F* users could guide Z3 with lemmas, assertions, fuel controls, and solver hints, but difficult goals could become brittle because the whole verification condition still flowed through solver heuristics. The Meta-F* work, developed publicly by 2017 and published in 2019, introduced programmable proof-state access specifically to combine the controllability of tactics with SMT's broad automation.

The 2019 design made two moves at once. First, it embedded metaprogramming as an F* effect rather than inventing a separate tactic language. That reused F*'s type/effect machinery and let metaprograms themselves be structured and, to a degree, verified. Second, it supported compiled native metaprograms because interpreting large tactics inside the normalizer was too slow. The paper reports that the hybrid approach improved robustness and performance on realistic examples compared with SMT-only proofs.

The current repository shows continuity rather than a frozen implementation. The public book still explains the same abstract-proof-state/sound-primitives argument. Current source still defines the tactic effect, supports tactic synthesis and preprocessing/postprocessing hooks, and preserves native tactic loading. At the same time, the exact implementation has evolved enough that this report deliberately anchors current claims to the 2026-09-30 revision instead of assuming that all 2019 internals remain unchanged.

The competing small-kernel tradition is older. LCF-style systems and descendants make proof-producing automation non-authoritative by validating its output in a small checker. Rocq explicitly describes this as the de Bruijn criterion. Lean uses the same broad strategy for ordinary declarations, although both systems also expose explicit trusted or unsafe facilities outside the simplest story. Meta-F* borrows the LCF idea for its tactic proof-state API but combines it with F*'s oracle-style SMT acceptance. The result is a hybrid trust architecture rather than a direct substitute for proof-term checking.

Certificate-checking systems such as SMTCoq address the hybrid's main logical-trust cost by reconstructing or checking external-solver evidence inside a proof assistant. They show that solver trust is an engineering choice rather than a necessary consequence of using SMT. They also explain why many verifiers still choose oracle-style SMT integration: supporting the full solver proof language and keeping certificate checking fast is significant work.

## Costs and failure modes

An extensible proposal/checker split has costs that should be planned rather than treated as free safety.

**Proof-artifact size and checker cost.** A certificate or proof term may be much larger than a boolean solver answer. Rechecking it can dominate verification time for some domains.

**Coverage lag.** A solver may learn a new theory rule before a certificate checker supports it. A proof-producing path can therefore be less complete than an oracle path even when it uses the same solver.

**Interface design pressure.** A proof-state API that is too weak forces tactics to emulate internals inefficiently; one that is too powerful can accidentally grant semantic authority. Meta-F*'s abstract proof state and primitive operations are one answer, but every added primitive deserves trust-boundary review.

**State/version complexity.** Interactive proof tooling must know which extension modules, imported environments, solver versions, and generated artifacts define a goal. Global process state creates stale-result hazards unless it is included in context identity.

**Operational security.** Native plugins and external tools can be logically non-authoritative while still having ambient process or filesystem capabilities. Sandboxing and resource control remain separate requirements.

**Diagnostics.** When a certificate checker rejects external evidence, the user needs to know whether the source property is false, the solver produced unsupported evidence, translation failed, or the checker lacks coverage. Collapsing these cases into “proof failed” undermines the usability advantage of automation.

**Trust-mode proliferation.** Supporting multiple accelerators can create an incomprehensible matrix unless Anneal presents a small result taxonomy. The user should not need to understand every plugin implementation, but the audit record must preserve the exact assumptions for later review.

## Boundaries

This report does not claim that F*'s current typechecker or Meta-F* implementation is formally verified end to end. It reports the design's stated soundness boundary and current source mechanisms. In particular, source-level restrictions on proof-state manipulation do not establish process isolation for native plugins.

It also does not claim that Z3 is unsound or that oracle-style SMT use is inappropriate. The point is accounting: F* explicitly trusts its encoding and Z3 for SMT-discharged facts, whereas a certificate-checking integration can place different components inside the logical TCB.

No F* executable, Z3 process, Lean process, Rocq process, or SMTCoq checker was run for this report. Current F* findings come from exact source and project documentation at the named revision; historical rationale and reported performance come from the Meta-F* paper/project pages. Lean findings are reused from exact-pin packages already present on the current Anneal `reference` branch.

The report does not attempt a security audit of F* native plugins, Lean metaprograms, OCaml dynlink, Z3, or agent execution. Statements about operational containment are derived architectural implications, not vulnerability findings.

The report does not recommend that Anneal adopt F*'s tactic API, effect system, native-plugin mechanism, SMT trust model, Rocq, or SMTCoq. Those systems are evidence about separable design choices. The Anneal judgment is conditional on the current principles and design contract.

Finally, “ordinary checker” is claim-relative. Lean checking can establish a target theorem while source/model correspondence remains separately trusted. A kernel-checked Lean term does not by itself prove that Anneal translated Rust correctly. J023's proposal/checker distinction composes with, rather than replaces, the source/model trust layers already documented elsewhere in the reference corpus.

## Evidence

Observed 2026-09-30 unless otherwise noted.

### F* current source baseline

**Repository revision.** `FStarLang/FStar@78bb239b54cc113be68fb1dc0cbdfeb19378766a`, `master` tip observed 2026-09-30; commit timestamp 2026-09-29T23:36:07Z. `version.txt` is `2026.09.27` (blob `26d3ef1f3dde934155c65eb455d39923012eb2cf`).

**Current tactics overview.** `doc/book/PoP-in-FStar/book/part5/part5_meta.rst`, blob `aa5c1b8571621697654136829ff8d1550d0cfe4f`. It documents verification-condition generation, the normal use of Z3, tactic-decorated assertions, the hybrid tactic/SMT “skeleton” style, `Tac`, abstract proof-state manipulation through primitives, and the argument that tactic divergence stalls verification rather than proving false. Source: `https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/doc/book/PoP-in-FStar/book/part5/part5_meta.rst`.

**Current SMT trust statement.** `doc/book/PoP-in-FStar/book/part1/part1_prop_assertions.rst`, blob `c3061a5a126bd40856f912f6b771e6b75af74cb0`. The document explains that F* may accept Z3 validity without an explicit proof term and explicitly states that F* trusts its SMT encoding and Z3 correctness. Source: `https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/doc/book/PoP-in-FStar/book/part1/part1_prop_assertions.rst`.

**Current tactic-effect interface.** `ulib/FStar.Tactics.Effect.fsti`, blob `a2ad85ec6aa5835ed00d5e011631ea8f02bf3f68`. It defines the `Tac` family, notes that its extracted representation is for reification/extraction rather than typechecking, and exposes tactic synthesis, assertion, preprocessing, and postprocessing hooks. Source: `https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/ulib/FStar.Tactics.Effect.fsti`.

**Current native-tactic loading.** `examples/native_tactics/README`, blob `f8f85265593325cc22dd4f9cec468346f82e7103`, documents generating OCaml tactic plugins and dynamically loading `.cmxs` files. `src/ml/FStarC_Tactics_Native.ml`, blob `352f61d9c41b0315467d934052875af0d55cd498`, registers native tactic/plugin steps and honors the `--no_plugins` mode. Sources: `https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/examples/native_tactics/README` and `https://github.com/FStarLang/FStar/blob/78bb239b54cc113be68fb1dc0cbdfeb19378766a/src/ml/FStarC_Tactics_Native.ml`.

### Meta-F* historical design

**Publication.** Guido Martínez et al., “Meta-F*: Proof Automation with SMT, Tactics, and Metaprograms,” ESOP 2019, pp. 30–59, first online 2019-04-06, DOI `10.1007/978-3-030-17184-1_2`. Springer record: `https://link.springer.com/chapter/10.1007/978-3-030-17184-1_2`.

**Microsoft Research publication record.** The ESOP publication page describes Meta-F* as using tactics/metaprogramming to discharge obligations not solvable by SMT or simplify them into SMT-friendly fragments; it says metaprograms may be interpreted or compiled to native code dynamically loaded into the F* typechecker and reports gains in proof development, efficiency, and robustness. Source: `https://www.microsoft.com/en-us/research/publication/meta-f-proof-automation-with-smt-tactics-and-metaprograms-3/`.

**Earlier technical-report framing.** Microsoft Research's 2018 report page motivates the design by contrasting brittle SMT-only proofs with the effort required for application-specific tactics, and describes safely manipulating typechecker state plus binary plugins compiled from verified source metaprograms. Source: `https://www.microsoft.com/en-us/research/publication/meta-f-proof-automation-with-smt-tactics-and-metaprograms/`.

### Lean and claim-relative trust

**Lean tactic extension behavior at Anneal's exact pin.** Current `reference` package `reports/lean-tactic-extension-apis-v4-30-0-rc2` characterizes `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`: ordinary tactic extensions manipulate goal/metavariable state and produce expressions that remain subject to the normal declaration/checking path, while metaprogram execution has separate operational concerns.

**Lean trust mechanisms at Anneal's exact pin.** Current `reference` package `reports/lean-trust-admissions-v4-30-0-rc2` records axioms, `sorryAx`, theorem-specific `#print axioms`, unsafe-code fences, native/executable trust mechanisms, and `debug.skipKernelTC` as a direct bypass of normal kernel checking.

**Cross-system TCB accounting.** Current `reference` package `reports/tcb-accounting-patterns-verification-systems-2026-09-27` compares Rocq, CompCert, seL4, and CakeML and derives the claim-relative distinction among proof search, checker trust, translation validation, execution correspondence, and artifact identity. J023 relies on that accounting rather than restating a full cross-system TCB survey.

### Certificate-checking alternative

**SMTCoq current repository.** `smtcoq/smtcoq@3187cf12412a244859d7396e8088e6f9de0568d1`. Its repository description states that SMTCoq checks proof witnesses from external SAT/SMT solvers using a certified checker and exposes decision-procedure tactics over those integrations. Source: `https://github.com/smtcoq/smtcoq`.

**Historical publication.** Ekici et al., “SMTCoq: A Plug-In for Integrating SMT Solvers into Coq,” CAV 2017. The project repository lists this as the tool paper and also cites the earlier modular proof-witness integration work.

### Anneal authority

**Principles.** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md`. The document defines Anneal's TCB-conditional promise, UB-freedom requirement, Rust-oriented usability goal, and principles to avoid breaking promises or foreclosing later expressive power.

**Design contract.** Same revision, `anneal/DESIGN.md`. The document requires precise success semantics, explicit and shrinkable trust, faithful source/model correspondence, Rust-oriented ordinary use, and compatibility between specialist low-level proof interfaces and the same underlying program contracts/trust model.

## Revalidation

Revalidate this report when any boundary below changes materially.

1. **F* tactics.** At a new F* revision, re-read the public Meta-F* book chapter, `FStar.Tactics.Effect`, the proof-state primitive layer, and native-tactic loading. Confirm that proof state remains abstract to ordinary user tactics and identify any primitive or plugin hook that can install unchecked facts or bypass ordinary verification.
2. **F* SMT trust.** Re-read the SMT interface documentation. If F* adopts solver proof reconstruction, certificate checking, or a new trusted-solver path, update the oracle-versus-checked-evidence judgment rather than assuming the 2026 design persists.
3. **Native plugins.** Revalidate how plugins are generated, loaded, cached, and disabled. If native execution moves behind a process boundary or gains a verified compilation/loader story, separate that new operational evidence from the source-level tactic soundness argument.
4. **Lean pin.** When Anneal changes its Lean version, rerun the existing tactic-extension and trust/admission revalidation plans. In particular, verify the ordinary declaration-check path, theorem-specific assumption auditing, native evaluation, unsafe mechanisms, and any kernel-check bypass.
5. **External automation.** If Anneal adopts an SMT or specialized solver, classify the integration explicitly as oracle, proof term, checked certificate, verified reflection, or another evidence type. Record exact solver/checker versions and what relation the checker establishes.
6. **Interactive contexts.** Include specialist extension modules and solver/checker configuration in proof-context identity. Test that editing or replacing an extension cannot make an old goal/result appear current under a new environment.
7. **Agent execution.** For agent-authored or third-party automation, test operational isolation separately from logical acceptance. A sandboxed oracle is still trusted for truth; a kernel-checked proof producer may still be dangerous to execute with ambient capabilities.
8. **Result semantics.** Add regression fixtures in which two proof strategies establish the same contract with different producer provenance, and fixtures in which an axiom/oracle/bypass changes the TCB. Confirm that the former can share claim semantics while the latter is visibly distinguished in result/audit metadata.

The report should be reconsidered, not merely mechanically refreshed, if Anneal chooses a proof architecture where Lean is no longer the final acceptance boundary, where source/model transformations become independently verified, or where ordinary successful results intentionally permit trusted domain oracles without separate trust-mode identity.