# Optimistic edits are semantic transactions, not text merges

## Summary

A query-derived edit has two separate correctness questions: whether the text still applies to the bytes the agent saw, and whether the reasoning that justified the edit still applies to the current proposition, model, dependencies, and authorized scope. Optimistic concurrency control, HTTP `If-Match`, Git's expected-old ref update, and versioned LSP edits all provide the same useful shape: perform expensive work without holding a long-lived lock, then validate a recorded basis immediately before making the mutation visible. None of those mechanisms can validate a dependency that the application failed to include in the basis.

The distinction matters for Anneal because a proof-oriented edit can be textually conflict-free while semantically stale. The published Anneal identity probes already exhibit content recurrence and stale-generation cases, and the real generation-publication experiment shows that a Lean check can accept an old proof while the surrounding generated family is mixed. Historical semantics-based program integration reached the same general warning from another direction: successful textual merging does not establish preservation of program behavior.

The conditional design judgment is therefore to treat a query-derived Anneal mutation as an **optimistic semantic transaction**. The observation should carry an operation-specific semantic basis. The apply boundary should atomically compare that basis with current state and re-check write authority. A single project-generation token is sufficient only if it transitively names every semantic input relevant to the operation; otherwise the precondition needs a coherent dependency vector or equivalent manifest. A text version, content hash, or successful rebase remains useful, but it is only one component of that validation.

If the semantic precondition fails, Anneal should normally reject the mutation, recompute it from current state when that operation has a well-defined cheap recomputation, or preserve the work as an explicit non-current fork/scratch attempt. Automatic textual rebasing may construct a new candidate, but the rebased candidate must not inherit the old query's semantic authority. It must be interpreted and, where applicable, verified against the current proposition, model, assumptions, and scope before acceptance.

## Applicability

This report addresses **J051** from issue #3732: operations in which an agent first observes proof or program state and later asks Anneal to mutate authoritative state based on that observation. Examples include applying a suggested proof edit, accepting a source edit derived from a goal, changing generated proof text, or committing a multi-file transformation whose justification depended on a particular source/model generation.

The report compares four protocol families and one program-integration history. Kung and Robinson provide the classic optimistic read/validate/write structure. HTTP `If-Match` and Git `update-ref <new> <old>` provide concrete compare-before-mutate protocols. LSP 3.18 provides a text-document analogue: a `TextDocumentEdit` can name an expected document version so that the client can check the version before applying the edit. Horwitz, Prins, and Reps provide a deliberately stronger integration criterion showing why text-level compatibility and semantic compatibility are different questions.

The Anneal application is **derived** from those sources plus current Anneal design authority and published Anneal experiments. None of the external protocols is a proof-editing specification, and none determines Anneal's exact identity tuple. The report does not require a database, global transaction manager, or one scalar revision for all state. It requires only that each authority-changing operation validate enough state to preserve the invariant it claims to preserve.

Current Anneal design at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92` requires successful verification results to identify the program or behavior, the established promises, and their trusted assumptions closely enough for the success claim to remain meaningful. That makes proposition/model/scope identity material to proof-derived mutations even when a generic editor protocol would regard the same edit as merely a change to one document.

The two published Anneal reports used here are bounded evidence, not adopted architecture. `anneal-interactive-model-probes-2026-09-29` is a finite Python/filesystem model of identity, stale patches, request supersession, and generation pinning. `anneal-3731-real-generation-publication-v4-30-0-rc2` uses retained real Charon/Aeneas/Lean artifacts to demonstrate coherent versus mixed generated families. Their lessons transfer only through the specific relationships described below.

## Findings

### Optimistic concurrency is validation of a remembered basis

Kung and Robinson's optimistic method separates a transaction into a read phase, a validation phase, and a write phase. Work can proceed without holding pessimistic locks during the read phase because tentative writes remain private. Publication is conditional on validation establishing that the concurrent history is acceptable. Their algorithm tracks the transaction's read and write sets; validation can only reason about conflicts represented in those sets.

The reusable architectural point is not the database implementation. It is the placement of the check. Expensive work may be speculative, but the mutation is admitted only after comparing the world that justified the work with the world in which the result would become authoritative. If validation fails, the speculative result is not silently promoted; the transaction aborts or retries. **Basis: primary literature; derived Anneal application.**

That immediately exposes a boundary relevant to Anneal. A validator is only as complete as the basis it names. If a proof edit depends on Rust source, generated Lean, imported artifacts, an obligation statement, trusted assumptions, or permission to edit a region, then checking only the proof document's text version cannot establish that those other dependencies stayed valid. Stronger concurrency machinery cannot repair an incomplete semantic dependency model.

### Compare-and-swap protocols protect the named object, not an unnamed invariant

HTTP conditional requests and Git reference updates make this principle concrete without requiring a database.

RFC 9110 defines `If-Match` so that a state-changing request can be conditioned on the currently selected representation matching the entity tag observed earlier. If the condition is false, the origin server normally refuses the method with `412 Precondition Failed`. The RFC explicitly frames these preconditions as protection against lost updates. The guarantee is intentionally scoped to the target representation and its validator.

Git's `update-ref` similarly accepts an expected old object ID. The ref is changed only if its current value still matches that old ID. Its transactional stdin mode can verify several old values while locking them together before committing the queued ref changes. The documentation also warns that even when individual ref updates are atomic, concurrent readers can observe only a subset of several modifications. **Basis: normative protocol documentation.**

For Anneal, these mechanisms support a fail-closed mutation boundary: "apply this result only if the state I based it on is still current." They do not by themselves identify what "the state" must contain. An expected document hash protects that document. An expected project-generation ID protects the semantic closure only if the ID actually names that closure. An expected obligation ID protects the proposition only if obligation identity includes every distinction needed to interpret it. The comparison primitive and the identity model are separate design obligations.

### LSP version checks solve a text problem, not the proof-context problem

LSP 3.18's `VersionedTextDocumentIdentifier` names a specific version of one text document; the specification says the number increases after every change, including undo and redo. A `TextDocumentEdit` may carry an `OptionalVersionedTextDocumentIdentifier` specifically so that the client can check the document version before applying the edits.

This is exactly the right guard for a class of stale textual operations. It prevents a server response based on document version `Si` from being blindly applied as though the document were still `Si`. It also makes a useful separation explicit: producing an edit and admitting the edit are different steps. **Basis: normative LSP 3.18 specification.**

But an Anneal proof mutation can remain semantically stale even when the target text is unchanged. Imported generated modules may have changed. The same proof bytes may have been closed and reopened in a new document/server incarnation. A Rust obligation at the same apparent location may have been regenerated from a different model. Authorization may have narrowed since the query. Therefore LSP document version should be treated as one possible precondition, not as a universal proof-context identity.

### Textual non-conflict is weaker than semantic noninterference

Horwitz, Prins, and Reps developed a semantics-based method for integrating noninterfering program variants in response to concrete limitations of line-oriented merging. Their paper's negative case is the point that transfers here: text-oriented integration can produce an unacceptable program even when variants are semantically noninterfering, because textual operations do not account for program semantics. Conversely, textual overlap is not a complete characterization of semantic interference.

Anneal should not import that paper's specific dependence-graph algorithm as a general proof-edit merger. Its language, assumptions, and semantic criterion are much narrower than Rust plus Charon/Aeneas/Lean. The historical lesson is instead about evidence: a merge tool proving that hunks apply cleanly, or an automatic rebase finding a conflict-free location, is evidence about text structure. It is not evidence that the proposition the edit was intended to prove remains the same. **Basis: primary program-integration literature; derived limitation.**

This distinction also explains why an automatic rebase should create a **new candidate** rather than silently carrying forward the old semantic warrant. The rebased text can be useful work. It just needs a fresh semantic interpretation and verification against current state.

### Published Anneal probes already contain the stale-semantic shape

The published `anneal-interactive-model-probes-2026-09-29` report separates content identity from causal/currentness identity. Its finite identity model includes an `A -> B -> A` recurrence in which content returns to the earlier value while causal tags differ. The same report's stale-patch model rejects a patch when the host digest, projection digest, or document version changes even if the stored coordinate still maps to a plausible location. Its publication model shows that repeatedly resolving a mutable `current` pointer can mix files from two generations, while pinning one immutable generation yields a coherent old snapshot.

Those results make two J051 points concrete. First, equality of the final text does not imply equality of the observation context. Second, coordinate applicability is weaker than semantic-currentness. A patch that still lands at a valid offset can still be stale relative to the source/model generation that produced it. **Basis: published Anneal execution/model evidence; derived J051 interpretation.**

The published real-generation experiment is a stronger negative control for proof acceptance. During controlled in-place replacement, the generated family passed through mixed A/B inventories. Fresh Lean still accepted the **old** proof during several mixed states because an old compiled function artifact remained in place. The old language server, deliberately pinned to generation A, also continued to answer successfully after B became current; the report correctly labels that answer A-generation guidance rather than a current-B result.

A successful Lean response therefore cannot, by itself, validate that a query-derived edit is current for the intended Anneal generation. The acceptance result must be associated with the semantic generation on which it ran. This is not a claim that Lean is faulty; it is a consequence of asking a perfectly valid checker a question about a stale or mixed context. **Basis: published bounded execution evidence; derived J051 interpretation.**

### The precondition should name the semantic closure needed by the operation

A universal "semantic transaction ID" is unnecessary if Anneal already has a root identity that transitively commits to the relevant immutable state. For example, a project/model generation could be enough when it commits to the Rust snapshot, generated Lean family, imported artifacts, configuration, and obligation identities that matter to the operation. Then the mutation can use one expected-generation compare-and-swap.

If no such root exists, the equivalent design is an atomically checked dependency vector or manifest. The essential property is coherence, not scalarity. Checking source version and model generation in two uncoordinated reads is insufficient if they can move between checks. Likewise, hashing every possible input is unnecessary if one immutable manifest already authenticates them transitively.

The operation also needs a **write-authority precondition**. A patch that remains semantically valid can still be unauthorized if the allowed target files, regions, or operation class changed after the query. Semantic freshness and authorization are distinct. The apply boundary should validate both before mutation. **Basis: derived analysis from the concurrency protocols and Anneal's scope-sensitive success semantics.**

An operation-specific basis is preferable to a maximally broad global revision. A local formatting edit whose computation never inspected model state may need only the authoritative document identity and write scope. A proof edit derived from a Lean goal needs the source/projection/model/import/obligation context that gives the goal meaning. A multi-file transformation may need one coherent project generation plus all affected write targets. The validator should be no broader than needed, because unnecessary dependencies turn harmless concurrent changes into false conflicts.

### Rejection, recomputation, and fork are different recovery policies

A failed semantic precondition means only that the old derivation is no longer authorized for direct application. It does not imply that the work has no value.

**Reject** is the safe default when the system cannot establish that the old reasoning still applies. This is appropriate for authority-changing operations whose semantic dependencies changed and where silent application could make a stale proof look current.

**Recompute** is preferable when the operation has a defined, bounded, cheap way to rerun the observation or derivation against current state. For example, a mechanical edit suggestion can be regenerated after a new goal query. The recomputation creates a new basis; it is not a special exemption from freshness checks.

**Fork** is appropriate when speculative work is expensive or exploratory and should be preserved even though it no longer targets current authoritative state. The fork should be explicitly labeled with its old generation and must not be mistaken for current proof state. It can later be ported or revalidated deliberately.

**Rebase** is a transformation on the candidate text. It may be a useful implementation technique inside either recompute or fork, but successful textual rebasing is not an acceptance rule. After rebasing, the candidate must be reinterpreted under the current semantic basis and pass whatever verification/authorization boundary the operation requires. **Basis: derived decision rule.**

### Optimistic admission and formal verification have different jobs

Even a perfect semantic compare-and-swap only establishes that the mutation is being applied to the context against which it was derived, under current authority. It does not prove the theorem, the Rust property, or the semantic correctness of the edit. Formal verification still has to run at the accepted checking boundary and its result still needs precise identity and scope.

The converse is also important: a proof checker accepting a theorem in some context does not establish that this context is the current one intended by the mutation. Concurrency validation and proof validation therefore compose rather than substitute for each other:

1. identify the observation context;
2. derive a candidate;
3. at apply time, atomically validate semantic basis and authority;
4. perform the mutation;
5. associate subsequent verification evidence with the resulting current generation.

Some systems may combine steps 3 through 5 into one atomic publication/verification protocol. This report does not require that shape. It requires that no successful text operation or proof result silently bridge a failed semantic precondition.

### Conditional Anneal decision matrix

The following matrix is a design aid, not adopted policy:

| Operation | Minimum useful optimistic basis | On mismatch | Why text-only validation is insufficient |
| --- | --- | --- | --- |
| Pure text transform independent of semantic query | authoritative document identity/version plus write scope | reject or recompute transform | Usually sufficient if independence is real; no proof-context claim should be attached |
| Proof/source edit derived from a goal or diagnostic | document/source identity plus model/import/obligation context and write scope, or one root generation committing to them | reject, recompute from fresh query, or fork | Same text/offset can denote a different proposition or generated model |
| Multi-file semantic refactor | one coherent project/model generation or atomically checked dependency vector, plus all target authorities | reject or recompute; explicit fork for expensive work | Per-file conflict checks can admit a cross-file semantic mixture |
| Scratch proof exploration | pinned immutable semantic generation, explicitly non-current | keep fork; rebase only as candidate construction | Exploration can remain useful without current authority |
| Acceptance/publication of a verified result | current semantic generation plus exact verification-result identity and accepted scope | reject stale result; rerun verification on current basis | A successful checker result can be valid for an old or mixed context |

This table intentionally leaves the exact identity fields open. J052 separately asks how epochs, fencing tokens, and process reincarnation should be represented. J050 separately analyzes snapshot isolation and serializability. J051 only requires that the apply decision be tied to a coherent semantic basis rather than to textual applicability alone.

## Boundaries

- **Not examined:** a production Anneal V2 edit API, actual MCP edit transport, editor-specific workspace-edit behavior, a concrete obligation-ID scheme, or a complete source/model identity tuple.
- **Not established:** that one scalar global generation is necessary or optimal. An atomically validated dependency vector or immutable manifest can provide the same relevant guarantee.
- **Not established:** that every edit must serialize globally. Unrelated edits should be able to proceed concurrently when their semantic and authority dependencies do not conflict.
- **Not established:** that database serializability is the implementation Anneal should use. The OCC literature supplies a correctness pattern and terminology; a small compare-and-swap over immutable generations can realize the needed invariant without a database.
- **Known not to follow:** a document version, range check, successful textual merge, or successful rebase does not establish preservation of a proof proposition or imported-model context unless those semantics are themselves part of the validated identity.
- **Known not to follow:** a proof checker success in one generation does not establish current-generation applicability. The published real-generation control retained successful old-proof observations under stale/mixed state.
- **Not established:** that content identity alone is enough for response freshness. Published Anneal finite-model evidence contains an A -> B -> A recurrence with equal content but different causal tags. J052 owns the deeper question of epochs and reincarnation.
- **Unknown:** the smallest sufficient semantic dependency closure for each future Anneal operation. That depends on the eventual source/model/obligation representation and on which hidden or ambient inputs are admitted by the execution backend.
- **Unsupported inference:** semantics-based program integration literature does not provide a ready-made Rust/Lean merge algorithm. It supplies a counterexample to treating text compatibility as behavioral compatibility.
- **Not examined:** user-experience costs of repeated rejection, long-running agent workflows, or whether particular false-conflict rates justify finer-grained dependency tracking. Those costs should be measured against real workloads before choosing a broad or narrow basis.
- Anneal implications in this report are **derived conditional analysis**, not adopted project policy.

## Evidence

### Primary concurrency and integration literature

- H. T. Kung and John T. Robinson, *On Optimistic Methods for Concurrency Control*, ACM Transactions on Database Systems 6(2), 1981, pp. 213-226, DOI `10.1145/319566.319567`. Primary PDF consulted through Carnegie Mellon. The paper supplies the read/validation/write decomposition, read/write-set validation, abort/retry structure, and discussion of read-only queries. Historical claims in this report are limited to those mechanisms.
- Susan Horwitz, Jan Prins, and Thomas Reps, *Integrating Noninterfering Versions of Programs*, ACM Transactions on Programming Languages and Systems 11(3), 1989, pp. 345-387, DOI `10.1145/65979.65980`. Primary PDF consulted through Purdue/Wisconsin mirrors. The paper explicitly contrasts line-oriented textual integration with a semantic noninterference criterion and gives cases in which textual merging is unacceptable. This report uses the negative distinction, not its algorithm as an Anneal design.

### Normative protocol sources

- RFC 9110, *HTTP Semantics*, June 2022, especially sections 13.1.1 and 13.2. The `If-Match` precondition uses entity tags on the selected representation and normally prevents a state-changing method when the condition is false. This report uses it as a concrete lost-update/CAS example, not as a semantic-proof protocol.
- `git/git@a018953688f1b10bddf91bff8747068f5f4746a4`, `Documentation/git-update-ref.adoc`, blob `37a5019a8bc75e29f23decb8b1b70c28c9412771`. The three-argument form checks the current ref against the expected old OID before storing the new OID; the stdin transaction can lock and verify multiple refs before committing queued modifications. This report does not infer cross-ref reader atomicity beyond the documentation's stated guarantees.
- `microsoft/language-server-protocol@9a247101dc088557ae56adef8fecbdc86c9a93ca`, LSP 3.18. `_specifications/lsp/3.18/types/versionedTextDocumentIdentifier.md` is blob `2eef90f025383db3f0bfd1a33579333c796a5221`; `_specifications/lsp/3.18/types/textDocumentEdit.md` is blob `433259b148f8ce8a6b09684174521954e786d574`. The former defines monotonically increasing document versions across changes including undo/redo; the latter says the optional version lets a client check the document before applying the edit.

### Anneal authority and published component evidence

- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md` blob `d5339a95254eae14ac201139d07d9d36d48a19fb` and `anneal/DESIGN.md` blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`. These are the current design constraints used to decide why proposition/model/scope identity matters to a successful result.
- `reports/anneal-interactive-model-probes-2026-09-29/REPORT.md`, observed on `refs/heads/reference` with blob `b8a3bcfe788a8c18b873caa540824b69d79c58f0`. Its retained finite models/execution provide the A -> B -> A content recurrence, stale-patch controls, request/stage supersession counterexample, and generation-pinning filesystem control used here.
- `reports/anneal-3731-real-generation-publication-v4-30-0-rc2/REPORT.md`, observed on `refs/heads/reference` with blob `41015b04602e083e1266c2281d49918317d022d8`. Its retained real Charon/Aeneas/Lean families provide the mixed-generation old-proof acceptance and pinned-old-server observations used here.

`support/evidence-map.json` records the claim-to-source relationships and evidence limits. `support/decision-matrix.json` preserves the operation-specific conditional judgment in machine-readable support form. No new compiler, prover, editor, database, or Anneal execution was performed for this report.

## Revalidation

For literature claims, revalidation is bibliographic rather than version-sensitive: reread the cited Kung-Robinson and Horwitz-Prins-Reps papers if a stronger interpretation is proposed. Their historical mechanisms do not become false because newer concurrency or merge systems exist.

For protocol examples, inspect the exact Git and LSP revisions recorded above and RFC 9110 sections 13.1-13.2. A newer protocol revision should receive a separate comparison if its precondition semantics materially change; do not silently transplant newer behavior onto the identified subjects.

For Anneal applicability, first reread the current `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Then check whether current `reference` still contains the two cited component reports or newer reports that materially revise their bounded findings. The cheapest discriminating implementation check for a future Anneal edit API is a stale-semantic matrix with at least these cells:

1. same text coordinate, changed source/model generation;
2. text A -> B -> A with a new document/worker incarnation;
3. unchanged target document, changed imported model or obligation;
4. semantically unchanged but unrelated concurrent edit, to measure false conflicts;
5. authorization narrowed after query;
6. stale patch that rebases textually without conflict;
7. explicit fork of stale work, followed by deliberate revalidation against current state.

For each cell, record the observation basis, the apply-time precondition, whether the mutation is rejected/recomputed/forked, and the generation against which any subsequent proof was checked. A useful implementation satisfies the fail-closed cases without rejecting unrelated edits solely because a coarse global token changed. If later evidence demonstrates that a smaller transitive root identity is sufficient, prefer it; if hidden semantic inputs escape the root, expand the identity model rather than adding stronger transaction machinery around an incomplete basis.