# Why3 proof sessions: durable repair state without stale-proof authority

## Summary

Why3 separates two questions that are easy to conflate in a long-lived verification workflow: **which old work can help repair a changed proof**, and **which proof results are current enough to count**. Its proof sessions preserve goal hierarchy, transformations, prover identity and resource limits, results, and interactive proof scripts. When Why3 reloads changed source, however, it reconstructs the current proof tasks and merges the old session into that new tree. Matching can use stable names and goal shapes. A matched old attempt may therefore survive as useful work while becoming **obsolete**; an unmatched old subtree may survive as **detached**. Neither state means that the old result is accepted as a proof of the current task.

That separation is the central architectural result for Anneal. Durable work does not need to be identical to current proof state. Anneal can retain prior proof attempts, agent analyses, transformation recipes, transcripts, and expensive intermediate artifacts as repair evidence while rebuilding authoritative obligations from current source, tool, and environment state. A match between old and new obligations can justify reusing the old work as a starting point. It should not by itself justify accepting the old result.

Why3 has reinforced this split for more than a decade. In 2011 it added goal-shape matching for old and new subgoals and recorded prover versions so version changes could make proofs obsolete. In 2014 it split checksums and goal shapes into a `why3shapes` sidecar that the changelog describes as unnecessary for replay itself and useful specifically for tracking obsolete goals after input changes. Current Why3 1.8.2 still rebuilds proof tasks on reload, retains unmatched old nodes without current tasks, and requires replay to update obsolete attempts. Prover upgrades similarly preserve or copy old attempts but mark attempts assigned to a new prover version obsolete so replay is mandatory.

The useful Anneal design is therefore a two-level identity model. **Acceptance identity** should be conservative and tied to the exact current obligation and the evidence that discharged it. **Repair identity** may be weaker and heuristic: source anchors, normalized obligation fingerprints, semantic scope, transformation lineage, or agent-maintained correspondences can suggest which old work to try again. A false repair match should waste work or fail replay; it must not silently turn stale evidence into current acceptance.

This model also argues against making every live RPC or editor object durable. Why3's API loads a saved session with current task fields absent and reconstructs them from source and environment. The durable record carries enough information to recover workflow and prior results; current executable objects are re-created. Anneal can use the same boundary: persist source/tool identities, semantic scope, recipes, artifacts, results, and salvage links, while treating process-local handles, server objects, and mutable RPC state as replaceable.

## Applicability

This report addresses #3732 **J021 — Why3: durable proof sessions without pretending old proofs are current**.

The evidence covers three related layers:

- **Current behavior:** Why3 1.8.2 documentation and public OCaml API, observed on 2026-09-30. The project site identifies 1.8.2 as the current release, and its changelog dates that release to 2025-09-16.
- **Historical evolution:** Why3's 1.8.2 changelog records session changes back to 0.70 in 2011, including goal-shape matching, prover-version obsolescence, prover upgrade support, session-format changes, the `why3shapes` sidecar, and newer session-management commands.
- **Design rationale and reported experience:** Bobot et al., “Preserving User Proofs Across Specification Changes,” VSTTE 2013, describes Why3's session-maintenance technique and reports use across more than one hundred verified programs while Why3 and its standard library evolved.

The report uses Why3 as an architectural case study, not as a direct implementation template. Why3's proof tasks and external-prover calls differ from Anneal's Rust-to-Lean translation pipeline, long-running agents, RPC surfaces, native publication, and coordination requirements. The transferable point is the separation between durable **repair state** and current **acceptance evidence**.

## Findings

### 1. Why3 persists the proof workflow, then reconstructs current tasks

Current Why3 sessions store more than a yes/no proof cache. The 1.8.2 manual says a session records the transformations applied to verification conditions and the provers run. Each proof attempt records the prover's complete identity, including name, version, and optional attribute, plus resource limits and the prover result. The session file format also records goal names, optional goal checksums and shapes, transformation names and arguments, proof-script paths, result status, timing, and whether an attempt is obsolete.

The API makes the reconstruction boundary explicit. `Session_itp.load_session` loads a session with all task fields initialized to `None`. The controller then reparses current files and rebuilds theories and goals. `Controller_itp.reload_files` merges the reconstructed tree with the old session. This is stronger evidence than a file-format convention: the API deliberately represents a loaded durable session before it has current proof-task objects.

This architecture avoids serializing the entire live prover/compiler object graph. Why3 saves a durable description of prior work and enough matching information to relate it to newly reconstructed tasks. Current tasks remain products of the current source and current Why3 environment.

**Anneal implication.** Persisting a live RPC object is unnecessary when the durable record can instead say what the object represented, how it was produced, what source/tool versions governed it, and how to reconstruct or re-run it. A regenerated object should become authoritative only through current execution, not because an old process handle was serialized successfully.

### 2. Goal matching is a migration mechanism, not a proof rule

On reload, Why3 first matches theories by exact name. Within a matched theory it tries to associate each new goal with an old goal, first by exact goal name and otherwise by goal shape. Old transformations attached to a matched goal are re-applied to the new task, and the resulting subgoals are recursively matched against old subgoals. The API also exposes `ignore_shapes`, which disables shape-based matching.

This is intentionally weaker than logical equivalence. A goal shape is useful because generated obligations can move or change identifiers even when much of the old proof strategy remains applicable. Its purpose is to recover work across edits.

Why3's treatment of the result shows the intended trust level. If a matched task changed, its old proof attempts are attached but marked obsolete. Matching therefore authorizes **reuse**, not **acceptance**. Why3 does not infer “these goals look related, therefore the old proof proves the new one.”

The 2013 paper frames the same problem from the user's perspective: changes to code or specification invalidate related proof obligations, even though old transformations and prover calls often remain directly reusable or easy to adjust. The session mechanism exists to preserve that investment.

**Anneal implication.** Anneal should distinguish a strong evidence key from a weaker repair key. Exact artifact/tool/source identities or a regenerated obligation digest can govern whether evidence is current. A semantic label, source span, normalized shape, dependency path, or agent judgment can govern which prior work to attempt. The second should never silently stand in for the first.

### 3. “Obsolete” preserves useful work while explicitly revoking currency

Why3's current manual defines an obsolete proof attempt as one whose prover ran on an earlier version of the task rather than the current task. It says replay is required to run the prover on the current task, update the answer, and remove the obsolete attribute. The IDE offers both “Replay valid obsolete proofs” and “Replay all obsolete proofs.”

This is a useful state because it retains three facts simultaneously:

1. a particular proof attempt existed and had a prior outcome;
2. Why3 found enough correspondence to attach it to the current goal;
3. the prior outcome is not current evidence.

A binary cache typically loses one of those facts. If it treats a cache hit as valid, it risks stale acceptance. If it invalidates the entry completely, it loses repair information. Why3 instead makes staleness first-class.

The `replay` command preserves that distinction at the regression-test boundary. It reruns proofs from a saved session and compares new results with the stored results. When obsolete attempts exist, replay still runs them. By default it updates the session only when the replayed attempts have the same results and all goals are proved; `--force` relaxes the latter condition but still requires the replayed attempts to complete correctly. The command returns a nonzero difference status when results changed.

**Anneal implication.** A durable record can remain valuable after its acceptance predicate expires. Anneal can record a result as stale-for-acceptance while preserving it as a replay candidate. That permits aggressive salvage without weakening current-proof requirements.

### 4. “Detached” preserves unmatched history without claiming that it belongs to the current proof

Why3 uses a second state for old work that no longer has a current task. A proof attempt can become detached because its goal disappeared, or because a parse/type error temporarily prevents Why3 from reconstructing the corresponding current tree. Detached nodes remain in the session until explicitly removed and can be copied and reused.

`reload_files` documents the same behavior structurally. An unmatched old theory remains with its former goals, proof attempts, and transformations, but those goals have no tasks. An unmatched old goal under a matched theory is likewise retained with its old work but no current task. Parse or type errors can temporarily detach an entire file's old tree.

This is an important alternative to deletion. A changed source tree can make correspondence temporarily unknowable without proving that the old work is worthless. By retaining detached work but withholding a current task, Why3 makes salvage reversible without confusing it with proof state.

**Anneal implication.** Candidate-only checkpoints, superseded agent attempts, or reports whose native target disappeared can remain durable salvage. They should be explicitly outside current coverage and should not block new work merely because they exist. If later source or coordination state makes them relevant again, a new authoritative reconciliation can attach or adopt them.

### 5. Prover identity is part of the result's freshness boundary

Why3 has treated prover versions as relevant session identity since at least 0.71 in 2011. That release stored prover versions in the session and marked a proof obsolete when a different prover version had produced it. Version 0.72 added multiple versions of the same prover and IDE support for prover upgrade.

The current 1.8.2 installation manual gives four policies when an old session refers to a prover version that is no longer installed:

- keep the old proof attempt under the old prover identity and do not replay it;
- remove it;
- upgrade it to an installed prover, marking it obsolete so replay becomes mandatory;
- copy it, retaining the old attempt and adding a new-version attempt marked obsolete.

For interactive provers, copying also duplicates edited proof scripts; upgrading without copying can reuse the existing script.

This policy is conservative in exactly the right place. A solver upgrade may improve performance, change heuristics, fix soundness bugs, or alter unsupported behavior. Why3 retains the old result as history but does not silently relabel it as a result of the new prover.

**Anneal implication.** Tool identity belongs in acceptance evidence. A change in Lean, Aeneas, Charon, a solver, an agent model, an environment-normalization rule, or a validator may invalidate current-result status even when the old artifact is still an excellent repair seed. “Same recipe under a new tool” is a replay plan, not a completed replay.

### 6. Why3 historically separated matching metadata from the proof replay itself

The session model evolved in ways that sharpen the distinction between durable repair metadata and proof evidence.

Why3 0.70, released 2011-07-06, introduced a batch session replayer. Version 0.71, released 2011-10-13, added a new old/new subgoal pairing method based on goal shapes stored in the session database and began storing prover versions for obsolescence decisions. Version 0.73, released 2012-07-19, changed the session format while retaining backward readability and added replay restricted to obsolete proofs.

Version 0.84, released 2014-09-01, split session storage into `why3session.xml` and `why3shapes`. The changelog says the shape file contains checksums and goal shapes and is **not strictly needed to replay a proof session**; it is useful when input programs change because it helps track obsolete goals. That is a particularly clear architectural signal. Goal-shape metadata supports correspondence and migration. Replay authority comes from running the proof attempts on reconstructed tasks.

Later releases continued to expand session maintenance rather than collapsing it into a cache. Why3 1.7.0, released 2023-11-24, added command-line operations for marking attempts obsolete, removing proofs, adding provers, creating sessions, running pending/obsolete attempts with `bench`, and ignoring shapes during replay.

**Anneal implication.** Matching metadata should be designed as replaceable support for salvage. It can evolve independently from the acceptance relation. Anneal should be able to improve a work-matching heuristic without thereby changing what evidence counts as a current proof.

### 7. Why3's session tree preserves procedure, not only results

A proof session includes the transformation tree that produced subgoals. On reload, Why3 can reattach an old transformation to a matched current goal, apply that transformation again to the current task, and recursively match the new subgoals to the old subgoals. For interactive provers it also retains edited proof scripts.

This matters because verification work is often procedural. A final “valid” bit cannot explain how a large goal was decomposed or which human intervention made an interactive proof tractable. The durable unit worth preserving may be a sequence of transformations and local proof attempts rather than one terminal proof object.

The 2013 paper's abstract emphasizes exactly this kind of reuse: previous goal transformations and calls to interactive or automated provers can remain useful after obligations change.

**Anneal implication.** Agent work should preserve replayable structure where possible: transformation recipes, source-to-obligation lineage, selected lemmas, subproblem decomposition, tool invocations, input/output artifact identities, and compact rationale. Persisting only a prose conclusion loses the most reusable part of expensive work. Persisting every live runtime object, however, is unnecessary if the procedure can be reconstructed.

### 8. Current replay is stronger than historical matching, but it is still scoped evidence

Why3 replay reruns the stored proof attempts in the current session and compares outcomes. This is materially stronger than merely finding an old matching node. It supplies fresh execution evidence for the reconstructed task under the selected prover configuration.

That does not make replay universal proof of semantic continuity across every possible change. Replay can be affected by resource limits, prover nondeterminism, environment differences, driver changes, or a changed Why3 transformation. A replayed `Valid` result means the current Why3 task was accepted by the current prover path under the current invocation. Interpreting that task as the intended source property still depends on Why3's VC generation, parser, transformations, source version, and any external correspondence assumptions.

The Why3 manual itself treats replay mainly as a non-regression tool and reports differences from the stored session. The report should therefore not elevate replay from “fresh evidence for this current generated task” to “proof that every layer of the system remained semantically identical.”

**Anneal implication.** Current replay should refresh only the layer it actually checks. A Lean theorem replay can refresh target-level validity. It does not on its own refresh Rust-to-Lean correspondence if the translator or source mapping changed. Anneal needs layered provenance so each replay result updates the right boundary.

### 9. A strict exact-match-only cache would be safer than heuristic acceptance but too destructive for repair

One alternative is to reuse old work only when an obligation's serialized bytes or cryptographic digest match exactly. This has a clean acceptance story: if all semantic inputs to the digest are complete and canonical, exact identity can justify reusing an existing result without another search.

As a repair mechanism, however, exact matching is brittle. Harmless renaming, reordered hypotheses, changed generated identifiers, a transformation implementation change, or a source edit that leaves the proof strategy mostly applicable can destroy the match. Why3's long history of goal shapes and recursive session merging exists because users benefit from preserving proof work across those changes.

The useful boundary is therefore not “heuristic matching versus exact matching.” It is **which question each match answers**. Exact identity can participate in acceptance. Heuristic identity can propose salvage.

**Anneal implication.** Prefer strong content/provenance identity when deciding whether evidence is already current, and permit weaker similarity or agent judgment only when choosing what to replay or repair.

### 10. Discarding all stale work is simple but makes regeneration unnecessarily expensive

A second alternative is to delete any work whose exact obligation changed. This avoids confusing stale work with current proof state, but it converts every source/tool evolution into a cold start. It also destroys interactive proof scripts, transformation choices, counterexample investigations, failed approaches, and explanations of prior decisions.

Why3's obsolete and detached states demonstrate a better failure mode. Old work can stay durable while contributing zero current-proof authority.

For Anneal this is particularly important because agent work may be expensive even when it does not publish a final proof. Research reports, minimized counterexamples, theorem-shape investigations, source-correspondence analyses, or failed proof traces can reduce later search substantially. A durable system should retain those assets with explicit status rather than delete them for the sake of a simpler “current/not-current” model.

### 11. Serializing the full live execution graph couples durability to implementation details

A third alternative is to persist entire in-process objects: RPC sessions, server handles, solver contexts, task objects, editor buffers, and scheduler state. This can make same-version resume convenient, but it increases coupling to implementation versions and process topology. It also creates difficult questions about handles that name external processes, mutable services, temporary files, credentials, sockets, or in-memory caches.

Why3 takes the opposite route for proof tasks: `load_session` initializes task fields to `None`, then reload reconstructs them. The session keeps durable workflow data but not authority over a task that no longer exists.

**Anneal implication.** Persist live objects only when they have a stable, deliberately specified serialization contract and when resuming them changes the economics enough to justify that contract. Otherwise persist a reconstructible descriptor plus artifacts. Treat any resumed runtime handle as an optimization that must still reconcile against authoritative current state.

### 12. Proof scripts alone are insufficient as the durable unit

A fourth alternative is to treat the user or agent script as the sole durable artifact and rerun it from scratch. This is attractive because scripts are inspectable and versionable. For some proof assistants it is close to the normal source model.

Why3 still stores a richer session tree because proof maintenance needs more context: which goal a script belonged to, which transformations produced that goal, which prover/version ran, what the prior result was, and how subgoals correspond after changes. A detached script without those relationships may be hard to reattach automatically.

**Anneal implication.** Durable agent transcripts or scripts should carry semantic scope and provenance rather than standing alone. The minimum useful record is usually “procedure plus the obligation and environment it was intended for,” not only procedure bytes.

### 13. Why3's reported experience supports the repair model, but it is not a controlled benchmark

Bobot et al. report that the session-preservation technique was successfully used while developing more than one hundred verified programs and keeping them current as Why3 and its standard library evolved. The paper also says the mechanism helps with environmental changes such as prover upgrades.

This supports the practical relevance of preserving old work across evolution, but it does not quantify the repair savings against a no-session baseline, characterize false matches statistically, or establish that Why3's matching heuristics transfer unchanged to other systems. The evidence is an engineering experience report plus a mature implementation history, not a controlled performance study.

**Anneal implication.** Use Why3 to justify the architectural separation between salvage and acceptance. Tune Anneal's matching keys, retention policy, and replay cost model from Anneal-specific measurements rather than assuming Why3's heuristics are optimal.

### 14. The strongest Anneal design is a durable work graph with explicit freshness states

A practical Anneal record can separate at least four states:

**Current.** The evidence was produced or revalidated against the exact current obligation and all acceptance-relevant tool/source/environment identities required by that evidence layer.

**Obsolete/stale.** The system has a plausible correspondence to a current obligation, but some acceptance-relevant input changed. The old result can seed replay or repair but contributes no current acceptance until revalidated.

**Detached.** No current obligation is authoritatively associated with the work. Retain it as salvage if its cost or rationale is valuable; do not count it as current coverage or let it block replacement work.

**Superseded/terminal history.** Newer authoritative work makes the old path unnecessary for ordinary repair, but provenance or audit requirements justify retaining it.

The correspondence edge should record **why** the system linked old and new work: exact digest, stable source identity, generated-goal name, normalized shape, transformation lineage, or explicit agent/human judgment. That makes the strength of the link inspectable.

The current-evidence edge should separately record what refreshed acceptance: exact replay, proof-kernel check, translation validator, source-correspondence check, or another bounded verifier. This prevents a strong-looking repair link from being mistaken for a proof.

### 15. Publication and external effects need a stricter layer than Why3 sessions provide

Why3's session problem is primarily local proof maintenance. Anneal also has external effects: publication to a repository branch, issue projections, durable coordinator state, and possibly other native outputs. Retaining an old proof attempt is safe because it does not by itself repeat an external effect.

Anneal therefore needs an additional effect-reconciliation layer that Why3 does not solve. A stale work record may say that publication was once intended or attempted, but a later run must reconcile native state and durable effect receipts before acting. A heuristic match to an old publication plan cannot authorize a second push or establish that a prior ambiguous push succeeded.

**Anneal implication.** Borrow Why3's stale/detached work semantics for reasoning artifacts, but keep publication authority behind fenced coordination, exact native reconciliation, attempt receipts, and idempotent effect rules. Durable repair state and durable effect state should remain distinct.

### 16. Conditional judgment for Anneal

Anneal should adopt Why3's architectural distinction, not its exact file format or matching algorithm.

Use **strong identity for acceptance**: current source revision, generated obligation or theorem identity, translator/prover/kernel versions as relevant, configuration, and exact artifact digests. If any acceptance-relevant identity changes, old evidence becomes stale unless an independent validator proves the change irrelevant.

Use **weak identity for salvage**: stable names, source locations, normalized shapes, semantic scopes, dependency structure, transformation lineage, or agent judgment. These links may propose prior work to replay, but they should not satisfy a proof predicate.

Persist **reconstructible workflow**: transformations, invocation recipes, proof scripts, artifacts, prior results, and rationale. Avoid requiring persistence of live RPC/server objects unless a stable resume protocol exists and materially improves cost.

Retain **unmatched expensive work** as detached salvage rather than deleting it. Detached work should neither count as current coverage nor block fresh work.

Treat **tool upgrades as new evidence contexts**. Copy or migrate prior procedures if useful, but require replay or validation before the new tool identity can inherit a current result.

Finally, keep **native effects outside the proof-session abstraction**. Replaying proof work can recover reasoning; publishing or reconciling a branch still requires its own fenced, read-before-write effect protocol.

## Boundaries

This report does not claim that Why3's goal-shape matching establishes logical equivalence. The current API describes it as a way to associate new goals with former goals during session merge. The fact that matched changed tasks become obsolete is evidence that Why3 itself does not treat the match as sufficient proof currency.

The report does not reconstruct the exact implementation of Why3's goal-shape algorithm at every historical release. It uses the current documented merge behavior and the release history to establish the role of shapes in repair. A separate algorithmic study would be needed to compare collision resistance, normalization details, or performance across versions.

The report does not independently run Why3 1.8.2, external provers, or historical Why3 releases. Current behavior comes from versioned documentation/API pages; historical behavior comes from the 1.8.2 distribution changelog and the 2013 paper.

The report uses the 2013 paper's “more than one hundred verified programs” statement as a reported outcome from the authors. It is not treated as a controlled measurement of maintenance cost, match quality, or replay success rate.

Why3 replay refreshes the proof attempt against a current Why3 task, but this report does not claim that replay alone revalidates every upstream source-to-task correspondence or every downstream execution assumption. Anneal should attach replay evidence to the layer that the replay actually checks.

Why3's session model does not address distributed work claims, concurrent workers, ambiguous network writes, or externally visible publication effects. The Anneal conclusions about coordinator fencing and effect reconciliation derive from Anneal's problem, not from Why3.

Current documentation is versioned as Why3 1.8.2, but the public site does not expose a commit hash in the pages used here. The release version and 2025-09-16 release date are therefore the strongest primary identity used for current behavior. Historical release dates and features are anchored in the 1.8.2 source distribution's `CHANGES.md`.

## Evidence

**Why3 1.8.2 project identity.** The Why3 project site lists 1.8.2 as the current release. Source: `https://why3.org/`.

**Current session semantics.** Why3 1.8.2 manual, “The Why3 Tools,” documents stored transformations and prover attempts; complete prover identity and resource limits; obsolete and detached attempts; replay of obsolete attempts; and the `replay`, `session`, and `bench` commands. Source: `https://why3.org/doc/manpages.html`.

**Current merge semantics.** Why3 1.8.2 `Controller_itp` API documents `reload_files`: files are reparsed, theories match by exact name, goals match by exact name or shape, matched old attempts become obsolete when tasks change, transformations are re-applied and subgoals recursively matched, and unmatched old nodes remain detached without current tasks. Source: `https://why3.org/api/Controller_itp.html`.

**Current durable/runtime boundary.** Why3 1.8.2 API index documents `Session_itp.load_session` as loading a session with all tasks initialized to `None`, and documents `merge_files`, `graft_proof_attempt`, `graft_transf`, and `change_prover`. Source: `https://why3.org/api/index_values.html`.

**Current on-disk structure.** Why3 1.8.2 technical documentation gives the `why3session.xml` DTD, including prover/version/resource identities, goal name/checksum/shape, proof result and obsolete flag, transformation names/arguments, and proof-script paths. Source: `https://why3.org/doc/technical.html`.

**Prover-upgrade semantics.** Why3 1.8.2 installation documentation says sessions continue to refer to old prover versions after an upgrade. Users may keep, remove, upgrade, or copy attempts; upgraded/new-version attempts are marked obsolete so replay is mandatory, and interactive proof scripts can be reused or copied. Source: `https://why3.org/doc/install.html`.

**Historical session evolution.** Why3 1.8.2 `CHANGES.md`, distributed with Debian source package `why3 1.8.2-3`, records: the 0.70 batch replayer (2011-07-06); 0.71 goal-shape matching and prover-version obsolescence (2011-10-13); 0.72 multiple prover versions and prover upgrades (2012-05-11); 0.73 backward-readable session-format change and obsolete-only replay (2012-07-19); 0.84 split `why3session.xml`/`why3shapes`, with shapes/checksums described as unnecessary for replay but useful for tracking obsolete goals after input changes (2014-09-01); and 1.7.0 expanded session update/create/bench and `--ignore-shapes` support (2023-11-24). Source: `https://sources.debian.org/src/why3/1.8.2-3/CHANGES.md`.

**Design rationale and reported use.** François Bobot, Jean-Christophe Filliâtre, Claude Marché, Guillaume Melquiond, and Andrei Paskevich, “Preserving User Proofs Across Specification Changes,” VSTTE 2013, pp. 191–201, DOI `10.1007/978-3-642-54108-7_10`, HAL `hal-00875395`. The authors describe preserving proof sessions across modified verification conditions and report successful use for more than one hundred verified programs and for Why3/standard-library and prover evolution. Project bibliography: `https://why3.org/`; publication record: `https://toccata.gitlabpages.inria.fr/toccata/publications/bobot.en.html`.

## Revalidation

Revalidate this report when Why3 changes the semantics of session reload, goal matching, obsolete/detached nodes, prover upgrade, or replay acceptance. In particular:

1. Check the current Why3 release and re-read the session, replay, installation, and `Controller_itp`/`Session_itp` documentation.
2. Confirm whether loaded sessions still reconstruct current tasks rather than treating serialized tasks as authoritative.
3. Confirm the old/new goal matching order and whether shapes, checksums, or another identity scheme now carry stronger or weaker semantics.
4. Confirm that a changed matched task makes old proof attempts stale/obsolete and that replay remains the mechanism that refreshes them.
5. Confirm how prover upgrades migrate or copy old attempts and whether a new prover identity still requires fresh replay.
6. If Anneal adopts a similar model, revalidate Anneal's own acceptance keys separately from its repair keys. A change to repair matching must not silently widen the current-proof predicate.
7. Revalidate native-effect semantics independently. Why3 session persistence is evidence for reasoning-work durability, not for repository publication or distributed-effect reconciliation.