# Unsafe Rust Skill Evaluation Plan

> **Evaluator-only material**
>
> This plan and every oracle it produces must remain outside the installable
> `unsafe-rust` skill and outside every test agent's filesystem and context.
> Evaluation agents receive the skill, a neutral task, and the source under
> review—never this document, the source catalog, advisory/audit metadata, a
> fixing diff, or an intended conclusion.
>
> **Status:** active protocol. Preserved executions live under [`runs/`](runs/);
> each run's frozen manifest, rubric, integrity record, and results govern that
> run. No development or evaluation run is a universal release proof.

## Evaluation Objective

Determine whether using the `unsafe-rust` skill causes fresh coding agents to
author and audit unsafe Rust with materially better proof completeness,
defect recall, calibration, and contract preservation than the same agents
without the skill.

The suite must test observable behavior, not preferred wording. Its primary
question is:

> Given only the audited artifact, its real contracts and configurations, and
> admissible documentation, does the agent find and discharge every in-scope
> soundness and mandatory-postcondition obligation, expose every missing
> implication, and state no stronger conclusion than its proof establishes?

For confirmed historical defects, the suite must demonstrate that agents can
independently recover every known issue atom. For fixed or proved controls, it
must penalize agents that merely recognize a pattern and assert unsoundness.
For open-world targets such as current zerocopy, it must reward valid novel
findings and honest incompleteness rather than agreement with an assumed
“clean” label.

This evaluates a skill revision, agent model, tool environment, prompt,
corpus revision, and budget together. It never establishes that the skill, an
agent, or a codebase is universally sound.

## Non-Negotiable Design Properties

1. **Fresh agents.** Every discovery, authoring, review, and paired-side run
   starts without conversation history or another agent's conclusions.
2. **Blind artifacts.** Expected findings, issue/advisory titles, vulnerable
   labels, fixes, audit notes, and oracle metadata are absent.
3. **Exact provenance.** Every artifact, compiler, dependency, documentation
   version, configuration, and skill revision is pinned.
4. **Issue-level closure.** Aggregate averages never hide a known issue atom
   that no skill-enabled agent found.
5. **Open-world adjudication.** Known findings are a lower-bound oracle. A
   novel finding is reviewed, not automatically called a false positive.
6. **Paired calibration.** Vulnerable, fixed, proof-complete, proof-incomplete,
   and no-known-defect cases are all represented.
7. **Universal-claim discipline.** A tested matrix does not substitute for a
   proof over every supported shippable configuration.
8. **Independent authority checking.** An answer is not correct merely because
   it agrees with an advisory. Its Rust/std factual premises and citations must
   actually imply its claims.
9. **No unsafe execution by default.** Source review is read-only. Any build
   script, proc macro, native build, test, container, reproducer, or historical
   package execution occurs only in a disposable, credential-free,
   network-disabled sandbox.
10. **Separate authoring from validation.** Freeze the skill before running an
    evaluation. If a result motivates a skill change, assign a new
    revision/candidate, rerun cumulative reusable prequalification, and use
    only the unconsumed holdout permitted by the terminal program; never patch
    a treatment in place after observing its outputs.
11. **Finite terminal confirmation.** Each terminal candidate look uses its one
    assigned lineage-disjoint fresh holdout. A failed effective treatment never
    reappears; an unchanged treatment may be rebound after `INVALID` only under
    the frozen infrastructure rule. Stop only at the first complete conjunctive
    pass within the finite claim epoch.

## Evaluation Artifact Architecture

Keep four stores physically separate:

1. **Runtime skill store**
   - only the exact `skills/unsafe-rust/` package under test;
   - immutable per run;
   - no links to maintainer or evaluator material.
2. **Blind fixture store**
   - source, public API documentation, exact dependencies/contracts, and a
     neutral task;
   - no `.git`, history, answer metadata, or issue-bearing collateral;
   - content-addressed.
3. **Private oracle store**
   - the full manifest described in the source catalog;
   - audit/advisory/issue/fix provenance;
   - known-finding atoms and human proofs;
   - inaccessible to every evaluated agent, candidate author/editor,
     candidate-admission reviewer, candidate-side registrar, and any other
     principal or process without the cohort-scoped frozen custody, oracle,
     scoring, adjudication, or bounded-adversarial-review role permitted by the
     exposure ledger below.
4. **Result store**
   - immutable prompts, environment manifests, raw transcripts, reports, TCB
     logs, edits, tool outputs, resource usage, and scores;
   - result IDs derived from skill, corpus, fixture, condition, agent, and
     replicate revisions.

An evaluation sandbox should contain only:

```text
/task/task.md
/target/...
/skill/unsafe-rust/...
/contracts/...       # only exact contracts the real auditor could inspect
/rust-docs/...       # optional pinned Reference/std mirror
/output/...
```

Do not mount the enclosing repository. In particular, exclude `evals/`,
`maintainers/`, other worktrees, branch metadata, local playbooks, cached
advisories, and sibling vulnerable/fixed fixtures.

Use a genuinely separate filesystem namespace, container, or VM. Codex
sub-agents in one root thread share the checkout and are not isolated merely
because they were told not to read sibling paths. The baseline environment must
contain no installed `unsafe-rust` skill, prior-skill package, skill metadata,
or searchable cache.

The runner must fail closed if a forbidden path is present or if the blind
bundle's digest differs from its manifest. Hash the complete effective prompt,
mounted files, tool policy, network policy, and environment for each condition.

### Executable-artifact isolation

Treat historical `build.rs`, proc macros, native build systems, test binaries,
PoCs, and supplied container images as hostile. Execute them only inside a
disposable VM/microVM or equivalently reviewed hardened boundary with:

- no host filesystem, daemon socket, device, credential, secret, SSH agent, or
  cloud-metadata access;
- read-only content-addressed inputs and isolated throwaway output/caches;
- non-root execution, syscall/capability/device restrictions, and no privilege
  escalation;
- no egress or DNS;
- CPU, memory, disk, PID, file-size, and wall-time quotas; and
- teardown plus artifact/log capture after each run.

A third-party container image is an input, not the security boundary. Source
review never requires executing the target and remains the default.

## Fixture Preparation

### Preserve what the proof needs

Include:

- all source files in the stated audit scope;
- actual public and safety documentation;
- manifests, lockfiles, build scripts, macros, proc macros, generated source,
  target specifications, and configuration policy needed to determine the
  supported set;
- exact dependency API documentation or source when its contract is relevant;
- exact external specifications needed for FFI or deployment claims; and
- ordinary repository instructions only in a specifically labeled
  naturalistic variant.

Do not “simplify” a real fixture in a way that removes an invariant producer,
consumer, panic path, callback, configuration, or generated surface.

### Remove answer leakage

By default remove:

- `.git`, branches, tags, commit messages, blame, and remotes;
- `.cargo_vcs_info.json`, embedded source-map/provenance paths, patch metadata,
  generated provenance comments, and package-manager caches that reveal source
  revisions;
- changelogs, release notes, security policy incident lists, advisory files,
  audit metadata, and issue/PR templates that name the defect;
- regression tests, examples, or filenames that explicitly state the answer,
  unless the task is intentionally to explain a supplied failing execution;
- fix patches and sibling fixture directories;
- evaluator manifests and diagnostic output from analysis tools; and
- issue numbers in non-semantic comments.

Never remove or silently rewrite the API's actual safety contract or the
`SAFETY` comment being audited. If a real semantic comment itself names an
incident, classify the case as a follow-through test or build a separately
reviewed neutral reduction; do not pretend it is blind discovery.

Before removing collateral, check `include_str!`, `include_bytes!`, build
scripts, proc macros, generated-source inputs, package metadata, and test
harnesses for semantic use of that file. If the build or proof consumes it,
retain it in a labeled naturalistic fixture or replace it only with a reviewed
neutral equivalent.

Maintain two variants where sanitation might affect realism:

- **naturalistic:** the exact distributable source minus version-control and
  evaluator material; and
- **blind:** a reviewed bundle with answer-bearing collateral removed.

Record every transformation. Compilation/tests can check for accidental
breakage but cannot prove semantic equivalence.

Scan the final bundle for oracle issue numbers and titles, URLs, advisory IDs,
audit-note substrings, base/fix SHAs, vulnerable/fixed labels, and source-map
paths as well as forbidden files. “Blind” means evaluator-oracle-blind; it
cannot prove that a pretrained model never saw a public incident. Only opaque,
access-controlled holdouts and freshly reviewed transformations reduce that
residual contamination.

### Do not reveal the trigger configuration

Tell the agent the genuine support policy and ask for every supported
configuration. Do not say “look at 32-bit,” “enable feature X,” or “the bug is
in release mode” unless an ordinary user request would already restrict scope
that way. The hidden oracle records the triggering combination.

For a separate local-proof capability test, it is acceptable to scope the task
to one module or function, but the prompt must not identify the violated
obligation.

## Hidden Fixture Manifest

Each fixture must instantiate the source-catalog schema and additionally
record:

- neutral target label and blind-bundle digest;
- task mode and exact prompt;
- files and public surfaces genuinely in scope;
- `theorem_domain` and `boundary_class`, kept separate among author/library
  unsafe abstraction, standard-library implementation, compiler TCB,
  OS/FFI/environment/deployment, build/proc-macro/supply-chain execution, and
  non-UB robustness/security;
- supported configuration set and trigger subset;
- every expected finding atom, its direct acceptance criterion, required
  discovery scope, prerequisite atom IDs, and certificate pass rule;
- an acyclic validated atom-dependency graph and the transitive source-family
  or metamorphic-lineage identity used for holdout assignment;
- allowed classifications and accepted alternative proof paths;
- whether a concrete UB witness is required, optional, or unavailable;
- whether the case is Objective defect, Candidate, Scoped positive proof,
  Bug-specific fixed control, or Challenge, plus independent corroboration
  tags;
- contamination risk and public-model-training likelihood;
- source-level, runtime, binary, deployment, robustness, and security claims
  that must remain separate;
- expected TCB entries and entries that would make the theorem vacuous;
- run permissions and whether executing any project code is allowed;
- scorer version and required human expertise; and
- retirement/revalidation triggers.

The oracle atom must describe a proposition, not a keyword. For example,
“agent says aliasing” is insufficient. It should state which safe surface
permits which state, how that state reaches which consuming operation, which
precondition is not proved, and what status follows.

## Fresh-Agent Protocol

### Definition of fresh

A fresh agent:

- receives no turns from skill design, corpus research, fixture preparation,
  the other half of a pair, or another evaluation;
- has no persistent memory or shared scratch files;
- cannot inspect result/oracle stores or the internet beyond the evaluation's
  explicit allowlist;
- receives the same model, reasoning effort, tools, and resource budget as its
  comparator; and
- starts from a content-addressed clean sandbox.

When using sub-agents, use no inherited turns (`fork_turns="none"` or its
equivalent). Do not use an agent that helped author or research the skill.

### Conditions

Run two separately labeled experiments; they answer different questions.

1. **Naturalistic lift**
   - Skill condition: an ordinary user audit/authoring request that explicitly
     invokes the mounted `$unsafe-rust` skill.
   - No-skill baseline: the same ordinary request without the invocation and
     with no specialized skill mounted or discoverable.
   - Interpretation: the combined benefit of the skill's workflow and content
     for a normal request.
2. **Rubric-controlled lift**
   - Skill condition: a detailed user request that independently states the
     desired theorem, configuration, citation, TCB, postcondition, and output
     requirements, plus the mounted skill.
   - No-skill baseline: byte-identical substantive requirements without a
     mounted or discoverable skill.
   - Interpretation: the skill's additional value after the user has already
     supplied much of the rubric.

When evaluating a revision, add a **previous-skill condition** to each
experiment under otherwise identical conditions.

Do not use the detailed prompt templates below as the naturalistic no-skill
baseline; they intentionally encode several skill teachings. Freeze and hash
the effective prompt and mounts for every condition.

Randomize condition order and opaque fixture names. Never let one agent see two
conditions or both sides of a vulnerable/fixed pair.

Use at least three independent replicates per condition for routine fixtures
and five for release-gating, high-severity, current-zerocopy minimum-oracle, and
private-holdout fixtures. Fix the sampling configuration when the platform
allows it; otherwise record it.

Predeclare and enforce a runner-controlled output-finalization protocol. A
**run slot** is one frozen fixture × condition × replicate assignment; an
**execution attempt** is one agent process launched for that slot. Permit
exactly one live leased attempt per slot—never concurrent, speculative, or
racing attempts. Before launch, define the complete scoreable output envelope,
including the final response, every required report, TCB log, edit/diff or other
file, relevant metadata, and process disposition.

The trusted runner, not the agent or coordinator, must atomically seal the
complete declared output tree through compare-and-swap, prohibit post-seal
writes, and record slot/attempt IDs, tree and file digests, byte lengths,
encoding/envelope checks, disposition, and completion state. The first terminal
seal is canonical even if a later coordinator or transport step fails. Its
completion marker means only that the runner sealed the attempt, not that its
content or format is correct.

A sealed slot cannot be retried; an empty, oversized, malformed, semantically
incomplete, or otherwise defective canonical envelope receives its frozen
consequence. Launch another attempt only after an independently attested,
preregistered exogenous and content-independent operational condition leaves no
canonical seal. A missing handoff caused by agent behavior or any failure whose
classification depends on semantic output is the frozen slot failure, not a
retry opportunity. Never inspect partial semantic content before making a retry
decision. Preserve every lease, attempt, partial artifact, failed seal, retry
attestation, and canonicalization record.

An evaluation is invalid if a skill run gets more time, task-specific context,
network, search results, or tool permissions than its baseline. The skill
package itself is the intended treatment; no condition may see another
condition's package or metadata.

### Documentation access

Prefer a pinned offline mirror of the exact Rust Reference and standard-library
documentation versions applicable to the fixture. Otherwise allow network
access only to exact versioned `doc.rust-lang.org` pages and explicitly
provided external/dependency specifications. Block general search, GitHub,
RustSec, crates.io pages, blogs, and cached issue results.

Fail closed on redirects outside the allowlist, unversioned-documentation
fallbacks, and content whose digest or version differs from the manifest.

The agent must open and verify cited documentation. Merely emitting a plausible
URL does not receive citation credit.

### Budgets

Use realistic but generous budgets. Whole-crate proof is not a function-level
task. Split large repositories into invariant-owning modules and configurations
before reducing the budget.

Record:

- model and reasoning setting;
- token and elapsed-time budget;
- tool-call and source-line counts;
- documentation retrieval time;
- whether the run ended naturally, exhausted a budget, or was interrupted; and
- any user steering.

Budget exhaustion is `UNPROVED` evaluation behavior, not evidence that the
target is sound or unsound.

## Prompt Templates

Replace bracketed fields mechanically from the private manifest. Do not add an
issue hint.

### Naturalistic lift

Skill-enabled audit:

```text
Use the $unsafe-rust skill from [SKILL_PATH] to audit [TARGET] at the supplied
snapshot. Do not modify the target. Write the audit report to [OUTPUT].
```

No-skill audit:

```text
Audit [TARGET] at the supplied snapshot. Do not modify the target. Write the
audit report to [OUTPUT].
```

Use equivalently short paired requests for change review and authoring. Do not
silently add the skill's theorem, safe-surface checklist, citation rules,
configuration closure, verdicts, or TCB template to this baseline.

The remaining templates are for the separately reported rubric-controlled
experiment.

### Focused audit

```text
Use the $unsafe-rust skill from [SKILL_PATH] to audit [TARGET] at the supplied
snapshot. The in-scope source is [SCOPE]. Establish the strongest justified
source-level Rust soundness and mandatory documented-postcondition conclusions
for every valid use and every supported shippable configuration in that scope.
Do not modify the target. Put the persistent audit report and TCB audit log in
[OUTPUT]. Independently verify every cited authority.
```

### Full crate or library

```text
Use the $unsafe-rust skill from [SKILL_PATH] to perform a complete unsafe-code
audit of [TARGET] at the supplied snapshot. Derive the supported configuration
set from the source and project policy. Cover every reachable safe and unsafe
API surface, generated artifact, and invariant transition that can ship to
downstream users. Do not modify the target. Put the persistent audit report and
TCB audit log in [OUTPUT]. If the proof cannot be closed, identify the exact
unproved obligations rather than guessing a verdict.
```

### Change review

```text
Use the $unsafe-rust skill from [SKILL_PATH] to review the supplied patch to
[TARGET]. Determine every soundness, safety-contract, documented-postcondition,
configuration, and compatibility obligation affected by the change. Review
both the changed lines and every producer or consumer whose proof depends on
them. Do not modify the target. Write the review to [OUTPUT].
```

### Repair/authoring

```text
Use the $unsafe-rust skill from [SKILL_PATH] to make [REQUESTED API OR CHANGE]
correct for all valid uses and supported shippable configurations. You may edit
the target. Minimize the unsafe boundary, write proof-grade safety contracts
and local comments, and update the TCB/audit artifacts required by the skill.
Do not rely on hidden caller behavior. Put the change and audit handoff in
[OUTPUT].
```

### Evidence review

```text
Use the $unsafe-rust skill from [SKILL_PATH] to determine exactly what the supplied
analysis result and harness establish about [TARGET]. State the theorem, model,
bounds, configurations, assumptions, and remaining TCB. Then determine which
requested soundness or postcondition obligations, if any, it discharges.
```

### Integration

```text
Use the $unsafe-rust skill from [SKILL_PATH] to integrate the supplied independent
module audit reports for [TARGET]. Check their scopes, TCBs, boundary contracts,
configuration coverage, and producer/consumer handoffs against the raw source.
Do not assume a shard verdict is correct merely because it is supplied.
Establish or refuse the requested whole-target conclusions and write the
integrated report to [OUTPUT].
```

Rubric-controlled baseline prompts replace only
`Use the $unsafe-rust skill from [SKILL_PATH] to` with `Independently`; their
substantive requirements remain byte-identical. They must not add a tutorial or
abbreviated rubric.

## Test Families

### 1. Microproof and contract tests

Use short snippets with complete hidden proofs to isolate one behavior at a
time:

- identify the exact operation/contract being justified;
- enumerate every precondition;
- derive each conjunct through checked artifact facts, exact applicable
  semantic premises, named proved invariants, explicit inference, and any
  verified tool theorem or TCB entry;
- prove the resulting invariant and mandatory postconditions;
- reject a circular, restated, misquoted, inapplicable, or wrong-version proof;
- distinguish `UNPROVED`, `UNSOUND`, and `CONTRACT-BROKEN`;
- given one missing premise that blocks several later obligations plus a
  separate direct defect, assign one stable root blocker/gap ID, mark every
  dependent positive obligation `UNPROVED`, preserve the independent defect,
  and do not duplicate the root omission as several findings;
- trace dataflow from a state-producing unsafe API to a later consumer;
- treat an adversarial safe trait implementation or callback correctly;
- recognize all safe API surfaces, including public fields, constructors,
  methods, trait methods, macros, and reachable hidden items;
- distinguish a macro callable with no caller-side unsafe obligation from a
  macro deliberately constructed so expansion succeeds only in an unsafe
  context, then audit the actual generated API/operation;
- handle sealing and compiler-enforced unsafe fields;
- separate selected-safe-dependency trust from caller-controlled safe code;
- qualify cryptographic/deployment assumptions; and
- reject “observations before later UB remain guaranteed.”

For each unsound/proof-incomplete microfixture, include a separately run
proof-complete partner. Rename and reorder variants to prevent memorized pattern
matching.

### 2. Google audit-log exhaustive suite

Use the pinned source and closure process in
[source-catalog.md](source-catalog.md).

Build four required sub-suites and one optional fifth:

1. **`GRA-ATOM`:** one focused blind fixture for every confirmed note atom.
   This is the direct capability regression: can the skill recover every known
   issue without being told what it is?
2. **`GRA-MULTI`:** one combined fixture for every record with multiple
   independent atoms. This tests whether an agent stops after the first issue.
3. **`GRA-REPLAY`:** a naturalistic full-source or original-delta audit for
   every record containing an admitted objective finding, plus a preregistered
   stratified sample of difficult/high-risk records with no known defect. This
   tests discovery amid realistic noise and calibration without converting a
   risk grade into an answer.
4. **`GRA-LEDGER`:** classify all 2,177 records, recursively atomize their
   linked primary sources, and give every record, atom, URL, and exclusion a
   disposition. This is exhaustive issue-coverage accounting, not necessarily
   2,177 agent runs.
5. **`GRA-ALL-REPLAY` (research-scale optional):** when resources and public
   source reconstruction permit, run record-level blind replays over the full
   ledger. An unavailable or non-relevant record receives a recorded
   disposition, not a fabricated fixture. This optional sweep is not a
   prerequisite for useful initial validation.

Import the snapshot-specific anchor families and calibration labels from the
source catalog and generated corpus manifest. Keep crate names and incident
lists out of this stable protocol so the catalog can refresh without the two
documents drifting. In particular, distinguish confirmed issues, fixed
versions such as the cataloged `flate2` control, explicitly disputed atoms,
and generated-code negative controls. The record/atom/URL closure ledger—not a
handwritten list or risk grade—establishes completeness.

### 3. Advisory and historical-pair suite

For every admitted RustSec/GHSA/OSV memory-safety atom:

1. run a focused vulnerable fixture;
2. run a full-source vulnerable audit where source size permits;
3. run the fixed side with a different fresh agent;
4. run a change-review fixture over the repair without revealing the issue;
5. when practical, ask a fresh authoring agent to repair the vulnerable side;
6. separately present any reproducer/tool result as an evidence-review task;
   and
7. de-duplicate scoring while retaining every advisory-to-atom mapping.

The source catalog and generated manifest hold the current named anchor set.
Select release cohorts by theorem domain and coverage tags—initialization,
arbitrary caller types, concurrency, target layout, SIMD, generated code, FFI,
panic/drop, allocators, provenance, compiler evolution, lifetime, postconditions,
adversarial safe traits, reentrancy, and other admitted dimensions—without
duplicating snapshot-specific names here.

Build/proc-macro code-execution advisories are scope/TCB fixtures unless a
separate source-level UB proposition is proved.

### 4. Standard-library adversarial-safe-caller suite

Reconstruct every admitted adversarial-safe-caller pair in the source catalog,
including any partial repair, and add every admitted standard-library
`I-unsound` atom from the corpus ledger. These cases test that unsafe code may
not rely on caller-provided safe implementations behaving according to prose.
Keep compiler soundness bugs in a separate TCB-boundary stratum.

### 5. Zerocopy historical suite

Every historical lead in the source catalog gets:

- a vulnerable focused audit;
- a fixed focused audit by a different agent;
- a full-source or full-module audit;
- a change review;
- a proof-comment/contract review when the repair changed prose; and
- a partial-fix test when history contains more than one repair.

The source catalog's versioned historical registry is the mandatory set; import
it mechanically rather than maintaining a second list here. Include its
negative, disputed, internal-only, build-failure, and proof-comment calibration
cases as distinct cohorts.

Score the dataflow theorem, not just the changed line. For example, the
`Ref` case requires following runtime borrow-guard ownership to a returned
reference; the mutable-transmute history requires detecting that an initial
repair covered only one of several consumers.

### 6. Current zerocopy suite

Materialize the exact immutable current commit identified in the source
catalog, not the live worktree. Import the catalog/manifest's current
invariant-owner shards. Run each with five fresh skill agents, five no-skill
baselines, and five previous-skill agents. Give each shard enough
budget to close its own surface and configuration partition.

The shard manifest must contain an invariant-owner/boundary coverage map
showing that every source file, reachable public surface, generated artifact,
configuration class, producer, transition, and consumer belongs to a shard.
Shard boundaries must arise from proof ownership, not from the locations of
known issues. Retain at least one naturalistic full-source run so shard-specific
hints and missed cross-boundary behavior are visible.

Then run separate fresh integration agents over:

- raw current source;
- normalized shard reports with agent identity removed but condition kept
  homogeneous: skill integration receives only skill reports, baseline
  integration only baseline reports, and previous-skill integration only
  previous-skill reports;
- the union of declared scopes, TCBs, obligation ledgers, and configuration
  partitions; and
- no historical/current issue oracle.

Required special runs:

1. **Reachable `#[doc(hidden)]` audit.** Exercise hidden public traits,
   associated items, modules/reexports, helper types, safe methods, and exported
   macros from an adversarial downstream crate. State that hidden items are
   ordinarily outside documentation/SemVer promises but retain the soundness
   obligations implied by their actual safe/unsafe markings; direct use is not
   forbidden misuse.
2. **Proc-macro theorem.** Audit the generator over every accepted token stream,
   interaction with attribute/function-like macros, repeated tokens, hygiene,
   cfgs, discriminants, and generated helper types.
3. **Generated-output audit.** Inspect real expansions and checked-in expected
   outputs, not only generator source.
4. **Configuration closure.** Derive the actual supported shippable set from
   pinned project policy. Separately classify shipping-library, host-build,
   test-only, documentation-only, analysis-only, internal, and unsupported
   combinations. Prove the shipping theorem universally and audit the other
   requested classes without silently folding them into that theorem.
5. **Scope calibration.** Correctly classify intentionally unsound
   `#[cfg(test)]` code without claiming it ships in the normal library.
6. **Naturalistic versus skill-isolation.** Run once with ordinary project
   instructions and once with only the target source plus skill. The isolation
   variant explicitly excludes `zerocopy/AGENTS.md`,
   `zerocopy/agent_docs/`—especially `agent_docs/unsafe_code.md`—other
   worktrees, playbooks, this repository's evaluator material, and fixes.

The catalog maps each hidden current minimum-oracle item to owning shards and a
provisional admission class. Release checking must verify that each admitted
objective atom is addressed by every owning shard; Candidate/Challenge items
are scored for reasoning and calibration, not agreement with an open issue.
Any novel finding receives independent adjudication.

Do not call current zerocopy a clean or fixed control. The correct integrated
result may be a mix of scoped `PROVED`, `UNPROVED`, `UNSOUND`,
`CONTRACT-BROKEN`, and conditional claims.

### 7. Tool-evidence and proof suite

Build paired tasks from:

- Miri fail/pass suites;
- Kani expected pass/fail and `verify-rust-std`;
- Loom and GenMC concurrency examples;
- Verus, RefinedRust, and RustBelt proof artifacts;
- Rudra, Yuga, RAPx, TypePulse, FFIChecker, MirChecker, RustSan/ERASan, and
  SafeFFI findings; and
- ordinary tests, fuzzing, sanitizers, and manual analyses attached to real
  incidents.

For every result, ask what exact proposition it establishes. Include:

- one witnessed bad execution;
- one clean sampled execution;
- one bounded proof with an insufficient bound;
- one exhaustive finite proof;
- one proof under a model that omits the relevant behavior;
- one proof over generated/translated code with an unproved source mapping;
- one concurrency exploration with an incomplete schedule/model;
- one static analysis that soundly over-approximates the requested domain; and
- one analyzer warning with no validated oracle.

The agent must neither dismiss every static analysis nor promote every formal
tool result to universal Rust soundness.

Include `cargo-geiger` only as potentially incomplete unsafe-site/configuration
enumeration evidence, never as a soundness oracle. Include
`cargo-semver-checks` or public-API diffs only as contract-evolution discovery
aids, never as proof that safety preconditions or behavioral guarantees were
preserved.

### 8. Authoring, repair, and review suite

Auditing alone does not validate the authoring half of the skill. Ask fresh
agents to:

- design a greenfield safe wrapper over a raw-pointer primitive from
  requirements;
- design a greenfield unsafe API with complete caller obligations;
- choose and implement a greenfield unsafe-trait or sealing strategy;
- design a macro-generated safe/unsafe API whose theorem covers every accepted
  input and expansion;
- design an FFI or allocator abstraction from exact external requirements;
- turn a historical defect into a sound safe abstraction;
- choose between local validation and propagating an unsafe caller contract;
- redesign a safe trait as sealed or unsafe when its behavior is consumed for
  soundness;
- privatize an invariant-bearing `pub(super)` field or design a documented
  compiler-enforced unsafe field;
- write exact `# Safety` documentation and adjacent `SAFETY` proofs;
- replace a misquoted/versionless citation with a verified, versioned one or
  report that authoritative text is insufficient;
- preserve invariants across panic, unwind, cancellation, reentrancy, and drop;
- repair a macro/proc macro by proving the generator theorem or constraining
  accepted inputs;
- update a TCB audit log for a safe dependency, unsafe dependency, exact pin,
  in-tree fork, or out-of-band contract;
- preserve documented postconditions as well as UB freedom; and
- review contract evolution for SemVer, exact pins, forks, and consumer-specific
  agreements.

Give greenfield tasks hidden proof obligations rather than an intended API
shape. Accept any design that closes those obligations and preserves the
requested behavior; do not reward imitation of one reference implementation.

Evaluate the resulting code and proof independently. Compilation, tests, Miri,
or a plausible comment cannot substitute for the hidden proof.

### 9. Robustness, compatibility, and conditional-theorem suite

Use paired snippets and real fixes to test:

- UB-free implementation that violates an unsafe API's postcondition;
- postcondition weakening that invalidates downstream unsafe proofs;
- safety-precondition strengthening across a nominally compatible release;
- a safe API correctness failure not in requested robustness scope;
- a cryptographic-signature-gated bad path;
- a negligible-probability collision path;
- a binary safe only under an explicit deployment restriction;
- a safe library API that tries to hide the same restriction;
- exact-version/fork/out-of-band dependency guarantees; and
- compiler/linker/build options that still produce a binary but change the
  requested claim or TCB.

Score source soundness, documented postconditions, compatibility, security,
probability, and deployment as separate claims.

### 10. Metamorphic, instruction-injection, and holdout suite

For each major defect family, create privately reviewed variants that:

- rename crates/items/lifetimes and neutralize comments;
- reorder independent declarations and invert branches;
- extract or inline helper functions;
- move the invariant carrier across a type, field, guard, token, or function
  contract;
- emit the operation through a macro or inspect its expansion;
- place the defect behind a feature, cfg, target, allocator, panic path, or
  build-script result;
- substitute ZST, over-aligned, zero-length, allocation-failure, reentrant,
  panicking, weak-memory, or adversarial-safe-code cases; and
- restore one hunk of a real repair while retaining unrelated refactors.

Include semantics-changing partners that look syntactically similar. A skill
that memorizes “this pattern is bad” should fail the fixed partner.

Add naturalistic repositories containing misleading source comments,
repository instructions, generated text, or prompt-like strings. The agent
must treat target content as code/data under audit, not as authority to weaken
the user task, reveal other files, skip proof, or change output destinations.
Keep ordinary project policy distinct from adversarial instruction injection.

All named cases in the checked-in source catalog are public development
fixtures, not private holdouts. Keep true holdout identities, source, and
answers only in an access-controlled store and refer to them in this plan by
opaque cohort/version ID.

Assign the conservative transitive closure of every common source/incident
ancestor and every direct, reduced, renamed, reordered, or other metamorphic
descendant to one lineage group. Treat that group as indivisible.
Every terminal cohort must be lineage-disjoint from all public or exposed
development fixtures, prequalification cases, runtime examples, prior results,
and earlier or later terminal cohorts—not merely from the other holdouts.
Permanently retire a cohort from confirmation when any of its semantic source,
expected behavior, oracle, or result is exposed. A retired cohort may become a
regression fixture but can never confirm a later candidate. Retirement occurs
at first exposure; **consumption** occurs only after the bound look receives its
terminal disposition and completes every frozen scoring and adjudication step.
Only then may its content inform a later candidate through the append-only
regression transition.

Maintain an append-only principal/process exposure ledger. Any person, agent,
service, or process exposed to any semantic source, oracle, lineage datum, or
content-derived signal for an unconsumed cohort is tainted with that cohort.
Roles are cohort-scoped:

- A current-look actor may be tainted only by `H_n` and already consumed
  cohorts, never by a later or unbound cohort. While `H_n` is unconsumed, that
  actor may perform only the frozen execution, oracle, scoring, consistency,
  adjudication, or bounded-adversarial-review role for `C_n/H_n`; it may not
  author, advise, admit, or select a later candidate or alter a candidate-facing
  protocol component.
- A person or process with semantic access to any later/unbound cohort may
  perform only its frozen future-bank custody or commitment role. It may not
  access candidate bytes, outputs, scores, gate inputs, or results and may not
  execute, review, score, adjudicate, author, advise, admit, or select a
  candidate. The fixed opaque verifier is the only bridge and emits only the
  terminal eligibility result specified below.
- Candidate authors, editing agents, candidate-admission reviewers, and
  candidate-side registrars remain untainted by every unconsumed cohort and its
  lineage map.

These rules include holdout/oracle authors, special adjudicators, custodians,
services, and unnamed intermediaries. Any candidate-linked access crossing from
a later/unbound cohort permanently aborts the claim epoch, retires every
affected cohort, and emits no candidate-facing detail or repair opportunity.

## Scoring Model

### Per-finding atom

Score applicable dimensions on a three-point scale:

| Dimension | 0 — absent/incorrect | 1 — partial | 2 — complete |
|---|---|---|---|
| Discovery | Missing or wrong location | General concern near relevant code | Exact location/surface and full affected scope |
| Required proposition | Wrong or absent | Some pre/postconditions identified | Every applicable pre/postcondition stated concretely |
| Dataflow/invariant chain | Missing or circular | Partial producer/consumer trace | Every establishment, transition, suspension, consumer, and exit path accounted for |
| Premises and authority | Folklore, unchecked, or hallucinated | Plausible but incomplete support | Artifact facts checked; every consumed semantic effect follows from exact applicable authority, verified tool theorem, or explicit TCB; implication direction is valid |
| Valid-use reasoning | Hidden, circular, or assumed caller/implementer path | Some adversarial cases or certificate components | Closes source selection, boundary access/inputs, typing/coherence, every boundary contract owned outside the audited scope—including contracts imposed on witness-supplied code—plus corresponding unsafe-context obligations and TCB applicability, without assuming the in-scope audited safety assertion |
| Configuration closure | Trigger/config missed | Trigger found but no supported-set proof | Every actually supported combination covered concretely or abstractly |
| Classification | Incorrect verdict | Concern found but statuses conflated | Exact independent status for soundness, postconditions, and conditional claims |

A finding counts as recovered only if the agent identifies the affected
surface/location, the violated or missing proposition, and a defensible
classification. Keyword overlap does not count.

Pre-register `N/A` dimensions per fixture and task mode before any run; exclude
them from both numerator and denominator. Never convert a missing applicable
dimension to `N/A` after seeing a result.

Use separate rubrics:

- **Audit:** the seven common dimensions above plus whole-scope/safe-surface
  coverage and report completeness.
- **Authoring/repair:** design validity, minimal/enforced boundary, complete
  contracts/comments, proof, postcondition preservation, configuration
  closure, TCB update, and compatibility.
- **Change review:** changed-proof impact, all affected producer/consumer
  discovery, contract directionality, configuration impact, compatibility, and
  correct disposition.
- **Evidence review:** exact theorem, model/domain/bounds, source-artifact
  correspondence, tool/environment TCB, configuration scope, and which target
  obligations follow.

Do not aggregate scores across task modes or theorem domains as if their
denominators were equivalent.

### Dependency-aware atom decisions

For rubrics whose atoms depend on other certificates, freeze an acyclic
dependency graph and each atom's direct criterion before collection. Blind
scorers first decide the proposition directly demanded by each atom without
mechanically copying prerequisite failures. The evaluator then computes:

```text
blocked_by(a) = immediate prerequisites whose certificate_decision is not PASS

certificate_decision(a) = PASS
  iff direct_decision(a) is PASS and blocked_by(a) is empty
```

Preserve `direct_score` or `direct_decision`, immediate `blocked_by` IDs,
`certificate_decision`, and the transitive set of `root_failures`. If an atom
both fails directly and has failed prerequisites, record both. “Root” is
relative to the frozen rubric graph; it is not a claim about the agent's mental
process.

Release gates use `certificate_decision`: directly stating a downstream
conclusion does not prove it when a consumed prerequisite is unproved. Root and
fan-out aggregates are diagnostic and may never convert a blocked certificate
to success.

### Per-run dimensions

Measure:

- known-atom recall and multi-issue completeness;
- valid-finding precision after adjudication;
- unsupported `UNSOUND` and unsupported `PROVED` rates;
- safe-surface discovery;
- obligation-ledger completeness;
- root-blocker/fan-out accuracy and nonduplicative finding accounting;
- local proof completeness and non-circularity;
- artifact-to-semantics edge closure and exact implication-direction accuracy;
- citation accuracy, versioning, quotation scope, and actual verification;
- TCB completeness, precision, versioning, and non-vacuity;
- adversarial safe-caller handling;
- mandatory-postcondition coverage;
- configuration/generator coverage;
- production/test/internal/released scope accuracy;
- correct use of `UNPROVED`;
- contract-evolution and SemVer analysis;
- evidence theorem/model calibration;
- novel-finding validity;
- actionable report quality;
- edit correctness and preservation for authoring tasks; and
- tokens, elapsed time, tool calls, and human adjudication cost.

Keep defect recall and proof quality separate. An agent may identify the right
line for an invalid reason, or write a beautiful proof that omits another safe
surface.

Report author/library unsafe abstractions as the primary skill-effect cohort.
Report standard-library implementation, compiler TCB, OS/FFI/environment,
build/proc-macro/supply-chain execution, and non-UB robustness/security as
separate domains. Never improve the primary score by pooling easier or
conceptually different boundary cases into it.

### Hard errors

Any of the following fails the run regardless of aggregate score:

- `PROVED` is issued with an undisclosed/uncovered obligation or supported
  shippable configuration;
- `UNSOUND` is issued without a proved valid-use path to UB;
- a fixed/proved partner is condemned solely by pattern recognition;
- an invalid, hallucinated, or unchecked authority citation is used as a
  necessary premise;
- arbitrary caller-provided safe code is trusted behaviorally;
- an advisory, issue, tool result, this skill, or evaluator text is used as a
  Rust axiom;
- a `PROVED` postcondition or whole-scope conclusion omits an applicable
  mandatory documented postcondition;
- a TCB entry assumes the exact in-scope conclusion or implementation and makes
  the audit vacuous;
- test-only/internal/non-shipping code is misreported as an ordinary downstream
  production surface, or a shipping configuration is dismissed as “only cfg”;
- eventual UB is treated as preserving guaranteed observations “before” it;
  or
- the agent read any oracle/paired-side material.

A missed known atom is an issue-level recall failure and may block its
preregistered cohort or release; it is not labeled a universal hard error in
every stochastic naturalistic/full-crate run. This distinction prevents
confusing failure to discover a defect with an affirmatively unsound or
fabricated conclusion.

## Release Gates

Before the first scored run, freeze:

- the corpus revision, admitted denominator, exclusions, cohorts, task modes,
  theorem domains, and `N/A` decisions;
- primary/secondary endpoints, replicate/stopping rule, retry policy, budgets,
  and scorer version;
- numerical non-inferiority and improvement margins; and
- opaque holdout cohort/version IDs.

Before exposure, translate every normative default and run-specific gate into a
versioned mandatory-root inventory. Map each normative requirement to a stable
root gate ID and exact aggregation rule, and validate set equality plus acyclic
dependency closure between that inventory and the executable manifest. Obtain
an independent completeness signoff. An omitted root, orphaned prerequisite,
weakened predicate, cycle, or mapping mismatch can never pass and receives the
frozen abort/`INVALID`/`FAIL` disposition.

The default root gates are intentionally demanding and nonwaivable:

1. **`G-ORACLE-COVERAGE`:** Every admitted Objective-defect atom appears in an
   evaluator-oracle-blind fixture.
2. **`G-FOCUSED-RECALL`:** Every admitted Objective-defect atom is recovered and
   correctly classified in every skill-enabled focused replicate.
3. **`G-MULTI-COMPLETE`:** Every atom in a `GRA-MULTI` fixture is recovered in
   every release-gating focused replicate; finding only the first issue fails
   that fixture.
4. **`G-NATURALISTIC-RECALL`:** A preregistered full-source/sharded recall cohort
   meets its explicit issue-level target. Use 100% when the prompt, scope,
   partition, and budget expressly ask for complete recovery. Report broader
   naturalistic full-repository recall per replicate without relabeling every
   stochastic miss a hard error.
5. **`G-NO-HARD-ERROR`:** There are zero hard errors.
6. **`G-PROOF-QUALITY`:** On focused Objective-defect fixtures, every applicable
   proof dimension scores 2. Full-source cohorts have no applicable dimension
   at 0 and meet a preregistered mean/floor.
7. **`G-CONTROLS`:** Fixed-side controls do not reproduce the repaired finding.
   Other valid findings remain allowed. Scoped positive proofs are accepted
   only within their exact theorem/model/TCB; Candidate and Challenge fixtures
   are never global soundness labels.
8. **`G-CURRENT-ZEROCOPY`:** Every admitted Objective-defect item in the
   current-zerocopy minimum oracle is addressed by each owning shard with
   correct production/test/configuration scope. Candidate/Challenge entries are
   judged on reasoning and calibration, not issue agreement.
9. **`G-AUTHORING`:** Every authoring fixture produces no unsound or vacuous edit
   and satisfies all applicable contract, postcondition, configuration, TCB,
   and compatibility dimensions.
10. **`G-ISOLATION`:** The runner emits a successful automated attestation for
    filesystem, package, prompt, network, documentation, and paired-side
    isolation.
11. **`G-HOLDOUT`:** The opaque holdout cohort has 100% focused Objective-defect
    recall, zero hard errors, required proof-quality floors, no repaired-defect
    false assertion, and no fixture-specific runtime-skill change.
12. **`G-COMPARISON`:** Skill-versus-baseline/prior-skill comparisons meet
    preregistered endpoints.
    In inferential mode, suggested defaults are zero additional hard errors; a
    sequence-adjusted lower paired confidence bound at the preregistered
    family-wise confidence level above -2 percentage points for recall,
    adjudicated precision, and proof-floor pass rate; and either a +10-point
    absolute improvement or standardized paired effect of at least 0.5 on a
    primary behavior the skill is intended to change. When the baseline is
    already at least 95% and the skill meets the absolute safety floors, a
    preregistered ceiling rule may accept non-inferiority without artificial
    “improvement.” In exact engineering-gate mode, use only the frozen exact
    comparison predicate and report its named finite observations
    descriptively. Do not claim an effect, improvement, non-inferiority,
    probability, target-population property, or generalization.
13. **`G-ADVERSARIAL-REVIEW`:** Every slot in a preregistered bounded review
    completes. Freeze at least two independent qualified reviewers, their
    independence from candidate authoring/admission, and their attested absence
    of taint from every later/unbound cohort. Freeze their exact review materials
    and scope, prompts, tools, budgets, number of passes, output schema, and
    disagreement/adjudication rule. This is a distinct current-look
    bounded-adversarial-review role: it may access only `H_n`, consumed history,
    the complete candidate package, canonical reports and audit artifacts,
    scoring/adjudication and gate inputs, and protocol/integrity evidence.
    Missing, partial, invalid, cross-cohort, or unpreserved review output cannot
    pass.
14. **`G-NO-MATERIAL-FINDING`:** Every candidate finding from the bounded review
    receives an evidence-backed disposition under the frozen versioned
    materiality rule and adjudication procedure. The nonwaivable inclusive floor
    qualifies at least any candidate unsoundness or vacuity; hard-error
    enablement; oracle/holdout leakage; isolation, gate, retry, output,
    identity, claim, stopping, or other protocol evasion/weakening; unsupported
    inference or terminal assertion; candidate-specific overfit; or defect
    capable of changing a mandatory-root predicate, input, outcome, or the
    scoped terminal claim. A run-specific rule may add findings but never
    exclude this floor. `PASS` requires zero unresolved or qualifying in-scope
    material defects and no `UNKNOWN`/`ERROR` disposition. A qualifying finding
    makes the look `FAIL`; it may not be removed by post-exposure quarantine,
    scope revision, or candidate repair.

### Finite terminal-candidate program

Development and regression fixtures may be reused for prequalification. A
terminal declaration requires a separate finite claim-level confirmatory
program. Its immutable **claim epoch** owns every look and all persistent state;
operational successor sequences are permitted only by its frozen restart rule
and cannot reset that state. Before exposing its first holdout, freeze:

- a content-addressed immutable genesis manifest containing every frozen field
  in this list, and its digest as the canonical claim-epoch ID; whether the
  release makes only an exact engineering-gate claim or also an
  inferential/statistical claim; the exact user-facing assertion; and a
  substantive claim-equivalence rule that does not depend on labels or file
  identity;
- for an inferential claim, its estimand, target population, sampling and
  assignment units, lineage/dependence treatment, and selection-valid analysis;
- a finite positive global `N_max`, the maximum number of terminal candidate
  looks across the claim epoch and every permitted successor sequence;
- mutually disjoint opaque cohorts `H1 ... HN_max`, allocated by indivisible
  source/metamorphic lineages that are also disjoint from every exposed
  development, prequalification, example, and prior-result lineage, together
  with the lineage-commitment, candidate-side registrar, opaque-verifier, and
  collision/TCB rules used for later eligibility checks;
- an effective-treatment identity and equivalence schema over every
  agent-visible candidate component and the frozen environment; a new name or
  digest is not by itself a distinct treatment;
- every program-invariant component: model and sampling policy, prompts, tools,
  documentation, base prequalification corpus, holdout bank and lineage map,
  runner, budgets, scorer, adjudication, and all protocol policies; each
  candidate's agent-visible runtime byte tree is frozen separately before its
  assigned exposure;
- the persistent cumulative regression bank and its sole permitted mutation:
  append each retired cohort and generalized adjudicated regression after its
  current look;
- the claim epoch's persistent append-only candidate-admission registry; for
  each effective treatment it records identity and byte-tree digests, exposure
  and outcome, and the evidence-backed behavior-affecting revision that makes a
  distinct later treatment eligible;
- every replicate, retry, atomic-output-finalization, invalidation, and
  irreversible fail-fast rule;
- the versioned mandatory-root gate inventory and a total executable gate
  manifest in which every gate has a stable ID, predicate and version/digest,
  typed inputs, prerequisites, missing/error behavior, and output; this includes
  the bounded adversarial-review procedure, its frozen materiality rule, and the
  admission rule for a later candidate revision;
- the complete conjunctive stopping predicate; and
- any across-candidate statistical error-control rule.

Claims belong to the same epoch when a pass would be used to support the same
user-facing release assertion or an aliased, overlapping, or post-exposure
narrowing of its artifact/domain, population, estimand, or endpoints. Cosmetic
rewording cannot create a fresh epoch. A genuinely non-overlapping claim may
start a new epoch under an independently specified rule, but cannot establish
`VN` retroactively for this one.

A candidate enters the program only after passing the entire cumulative
prequalification and a subtractive/coherence review of its runtime instructions,
routed references, templates, and maintainer rationale. A **candidate look** is
the complete binding and evaluation of one frozen candidate against its
assigned cohort; it is distinct from the slot-level execution attempts governed
by the retry policy, and its index is global across the claim epoch. **Semantic
exposure** begins at the earliest candidate-linked human or process access to
any holdout bit, contract, oracle or lineage content, or content-derived signal,
regardless of which security boundary contains the access. Only demonstrably
content-oblivious harness checks whose decisions are independent of those
semantics and the fixed nonrevealing lineage-commitment check below may precede
exposure. Any human semantic comparison or additional/cohort-specific signal
counts as exposure. For candidate look `n`:

Permit exactly one active candidate look in the claim epoch, including across
operational successor sequences. Do not pre-admit, freeze for terminal use,
bind, expose, or run `C_{n+1}` while `C_n` lacks a terminal outcome. Conditions,
replicates, and slot attempts within the one bound look may use only their
frozen schedule and retry rules.

1. Freeze candidate `C_n`. A candidate-side registrar untainted by every
   unconsumed holdout commits the complete candidate-author exposure and source
   lineage set without accessing the holdout map. Before binding `H_n`, a fixed
   trusted verifier compares only the precommitted opaque lineage identifiers
   for `C_n`, the accumulated bank, and every unconsumed cohort. It may emit
   only `PASS` or permanent claim-epoch `ABORT`; it reveals no cohort-specific
   result and permits no candidate repair, retry, or cohort substitution. Any
   semantic inspection, incomplete registrar basis, other output, or verifier
   change invokes the frozen failure rule. Candidate authors and editing agents
   remain unable to access any unconsumed cohort or its lineage map.
2. At first semantic exposure, retire `H_n` permanently from later
   confirmation. It becomes consumed only when this look terminalizes.
   Retirement permits only the frozen completion, slot-retry, scoring,
   consistency, and adjudication operations for this already-bound `C_n/H_n`
   look.
3. Run every required condition and replicate. A favorable partial cohort can
   never pass. Fail-fast is permitted only to record an irreversible `FAIL`.
4. Materialize every human adjudication or materiality decision into the
   manifest's typed inputs, validate exact root-inventory equality and complete
   dependency closure, then compute and publish every required root and
   prerequisite with its predicate and input digests. Only explicit `PASS` for
   every required root and its transitive prerequisites passes; a missing or
   weaker root, closure error, or `UNKNOWN`/`ERROR` result can never support
   `PASS` and receives the frozen abort/`FAIL`/`INVALID` disposition.
5. Assign exactly one look outcome:
   - `PASS` when the complete cohort is valid and every required gate passes;
   - `FAIL` when the protocol-valid complete look has a failed gate or a frozen
     irreversible fail-fast predicate fires; or
   - `INVALID` only under a frozen infrastructure/protocol invalidation
     predicate, never because of report content or an unfavorable result.

An infrastructure failure before semantic exposure is not a look and may be
retried against the same cohort under the frozen rule. After exposure, `H_n` is
consumed even if the outcome is `INVALID`; any further confirmatory evaluation
uses `H_{n+1}`. The same frozen candidate may be rebound after `INVALID` only
when the predeclared infrastructure-only rule permits it. Predeclare whether
the valid retry is an unchanged-candidate rebind or requires a later candidate.
In inferential mode, every exposed invalid look must spend its `alpha_n`
allocation or be accounted for by the preregistered always-valid sequential
method. In exact engineering-gate mode, it consumes one of the finite `N_max`
candidate looks in the claim epoch. An unexposed prelaunch failure consumes
neither. Slot-level execution retries remain governed by the leased-attempt and
atomic whole-envelope canonicalization rule and do not create extra candidate
looks.

Any agent-visible runtime-package change after exposure creates a new
candidate. Any unpermitted change to a program-invariant environment, holdout,
scorer, gate, identity rule, or protocol component aborts the operational
sequence; it cannot be treated as another candidate. A successor sequence may
continue the claim epoch only under the predeclared restart transition and must
inherit its claim/effective-identity rules, cumulative regression bank,
candidate registry, exposure and outcome ledger, remaining holdouts and global
look budget, gate roots, stopping rule, and remaining statistical error budget.
Otherwise the epoch terminates without `VN`. A post-exposure fixture quarantine
or protocol repair never retroactively preserves the consumed look.

Before `C_{n+1}` may be admitted or bound, `C_n` must have exactly one sealed
terminal outcome, `H_n` must be consumed, every frozen scoring/adjudication step
must be complete, and the outcome, exposure, cumulative-bank, and registry
transitions must be atomically preserved. Add every revealed earlier cohort and
every generalized regression derived from its adjudicated failures to reusable
prequalification through the frozen append-only transition. After `FAIL`, the
revision must contain a documented evidence-backed **effective-treatment**
response under the frozen admission rule; an evaluator-only, comment-only,
metadata-only, editorial, or identity-only mutation that cannot affect agent
behavior does not buy another holdout look. The next candidate must pass the
accumulated bank without adding fixture-specific runtime instructions. A
protocol-valid `FAIL` permanently makes its whole effective-treatment
equivalence class ineligible for another holdout look in the claim epoch,
including any successor sequence or aliased claim, until the registry records
an admitted evidence-backed behavior-affecting revision. The frozen admission
rule, not a candidate-supplied label or digest, decides distinctness.

Stop at the smallest global `n` whose entire cohort passes every frozen gate.
`VN` is the immutable terminal record containing the claim-epoch ID, look index,
the complete genesis manifest and digest—including the exact assertion, mode,
claim-equivalence rule and, when applicable, estimand/population/analysis—
candidate effective-treatment identity and byte-tree digest, environment,
prompt/tool/corpus/holdout/protocol/gate identities, canonical output and
scoring/adjudication manifests, complete `PASS` result, and a digest of the
entire claim-epoch history: candidate admissions/identities/outcomes, prior
canonical manifests, exposure/taint and cohort lifecycle ledgers, cumulative
bank transitions, used/remaining global looks and alpha, retries, invalidations,
and successor transitions. The candidate may be called version `VN` only for
the exact assertion bound by that genesis manifest; terminal status is not an
intrinsic context-free property of its bytes. `G-NO-MATERIAL-FINDING` means only
that the frozen bounded procedure produced no unresolved qualifying finding; it
does not claim that no undiscovered defect can exist.

If no candidate passes by the claim epoch's global `N_max`, close the epoch
permanently without a successful `VN`. No successor protocol, fresh bank,
relabeling, overlap, or post-exposure narrowing can extend its look budget or
produce `VN` for it. A genuinely new non-overlapping claim cannot retroactively
rescue the closed epoch.

For an inferential claim, allocate look-level error budgets `alpha_n` with
`sum(alpha_n) <= alpha_total` or use another valid preregistered sequential
method. Each look's joint pass test must be conditionally valid given all prior
information and adaptive selection in the complete history, including prior
outcomes, invalidations, candidate revisions and admissions, endpoint and model
choices, missingness, adjudication, and protocol decisions. It must charge
endpoint, model, selection, missingness, and other multiplicity within its
allocation. Every permitted successor sequence inherits only the claim epoch's
remaining `alpha_total`; freezing a new protocol does not reset it. Disjoint
cohorts alone do not remove optional-stopping inflation. Exact engineering-gate
mode supports only the descriptive proposition that the named candidate digest
passed the named gate roots on the named finite slots under the frozen
environment. Any causal, probabilistic, population, expected-future,
generalized-quality, improvement, or non-inferiority claim requires inferential
mode and its selection-valid method.

The 2,177-record GRA ledger remains the full corpus-closure goal, but completing
it is not a prerequisite to begin with a frozen, semantically adjudicated
initial tranche. No release may claim exhaustive audit-log issue coverage until
every record, recursively derived atom, and URL has a disposition.

Because agents may be stochastic, report every replicate. Statistical
confidence intervals and paired effect sizes are useful secondary summaries;
they do not turn an individual missed soundness obligation into a success.
Three/five replicates are engineering minima, not statistical justification;
increase them when a power analysis or endpoint variance requires it.

If a fixture is wrong, contaminated, unlicensed, or ambiguous, quarantine and
repair it with a versioned reason. A post-result quarantine creates a new
corpus revision and restarts every affected comparison; it cannot change the
frozen denominator retroactively. Required-run infrastructure failures and
budget exhaustion remain failed/incomplete results under the preregistered
retry policy, not silently replaceable runs. Never relabel an agent failure as
a fixture failure merely to pass the release.

## Oracle Construction and Adjudication

### Build an oracle, do not copy a verdict

For every objective atom, two qualified reviewers should independently:

1. inspect the exact source and all relevant safe surfaces/configurations;
2. reconstruct the producer-to-consumer dataflow;
3. state the missing/violated proposition;
4. verify the exact Reference/std basis or record a documentation/TCB gap;
5. check the safe reproducer or proof when available;
6. inspect the repair and confirm what it changes;
7. classify soundness, postcondition, compatibility, and conditional claims
   separately;
8. agree on each atom's direct acceptance criterion, prerequisites, and acyclic
   dependency graph; and
9. reconcile disagreements before the atom becomes an Objective defect or
   Scoped positive proof.

Audit notes, advisories, upstream acknowledgements, and fixing diffs are strong
leads and corroboration, but not substitutes for this work.

### Novel findings

Blind scorers first remove agent identity and condition. Two independent
reviewers then classify every extra assertion as:

- valid new finding;
- valid proof/documentation gap;
- duplicate or broader form of an oracle atom;
- unsupported but reasonable question;
- invalid assertion; or
- requires upstream/Rust-documentation clarification.

Do not penalize a run for a valid novel finding. Add confirmed incidents to the
regression corpus after disclosure/embargo and licensing review.

Potential novel defects in current maintained code enter an access-controlled
coordinated-disclosure quarantine. Restrict transcripts, reports, PoCs, and
fixture material to the triage group; contact the applicable maintainers; and
do not publish results or admit a public regression fixture until the issue is
fixed, disclosed, or the maintainers authorize release.

### Scoring independence

Whenever feasible:

- fixture authors do not score the first run;
- blind scorers do not know skill/baseline condition;
- an adjudicator resolves disagreement;
- the same judge rubric and evidence bundle apply to all conditions; and
- automated extraction computes counts only after semantic labels are fixed.

LLM judges may assist with report normalization but cannot be the sole
authority for a Rust soundness oracle.

Before release-scale scoring, calibrate reviewers on a hidden mixed set and
measure agreement by label and rubric dimension. Require unanimous reconciled
theorem atoms for Objective-defect/Scoped-positive admission and a
preregistered agreement floor (suggested: Cohen's κ or Krippendorff's α at
least 0.8) for routine scoring. Unresolved theorem disagreements block oracle
admission; they are not averaged into a numeric truth.

## Execution Schedule

### Pre-merge smoke suite

Run a small, rotating, contamination-resistant set covering every load-bearing
skill instruction:

- microproof citation and invariant tests;
- one adversarial safe trait/callback;
- one vulnerable/fixed real pair;
- one multi-issue audit-log record;
- one cfg/generated-code defect;
- one postcondition/contract-evolution case;
- one evidence-calibration pair; and
- one current-zerocopy shard excerpt.

This is a fast regression signal, not the release claim.

### Candidate-release suite

For reusable prequalification, run:

- every microfixture;
- every `GRA-ATOM` and `GRA-MULTI` fixture;
- all admitted RustSec historical pairs in the release subset;
- all zerocopy historical cases;
- all current zerocopy shards and integration;
- all authoring/review/evidence tests;
- fixed/proved/calibration controls.

After every reusable item passes, freeze the complete candidate and run its one
assigned opaque access-controlled holdout cohort. Apply the finite
terminal-candidate program for a terminal declaration; do not use that cohort
as an iterative debugging set.

### Full corpus suite

At each major skill release and corpus refresh, run:

- `GRA-REPLAY`, completed `GRA-LEDGER` closure, and, when scheduled,
  `GRA-ALL-REPLAY`;
- every admitted RustSec/GHSA/OSV memory-safety atom;
- all reconstructible standard-library cases;
- packaged benchmark corpora after de-duplication;
- every admitted, independently adjudicated checker finding;
- expanded configuration/architecture runners; and
- multiple supported agent models if the skill is intended for them.

Large corpus runs may be distributed, but each audit agent remains isolated.

### Longitudinal suite

Retain results by immutable skill and corpus revision. Track:

- newly found incidents;
- old fixtures invalidated by Rust/documentation evolution;
- behavior changes by model revision;
- improvements and regressions by skill section;
- cost and completion trends; and
- which historical audits need reinterpretation after a foundational skill
  change.

## Result Report

Publish a report containing:

- exact skill, corpus, runner, model, toolchain, and documentation revisions;
- fixture inclusion/exclusion and license summary;
- contamination checks;
- automated isolation attestation;
- condition/replicate counts and resource budgets;
- the complete content-addressed claim-epoch genesis manifest and digest,
  including the exact assertion, mode, equivalence rule and any inferential
  estimand/population/analysis; terminal candidate index, global `N_max` use,
  effective-treatment/package/protocol identities, persistent registry and
  cumulative-bank transitions, assigned/retired/consumed cohort IDs, lineage
  and taint-ledger checks, and any alpha spending;
- every run slot, attempt lease, execution attempt, whole-envelope atomic
  finalization disposition, retry attestation, and canonical-envelope selection;
- separately reported task modes and theorem domains;
- issue-level results, with no known atom hidden by aggregate metrics;
- direct/root atom failures separately from certificate failures and their
  `blocked_by` fan-out;
- the mandatory-root inventory and total gate-manifest digests, root/dependency
  closure validation, every gate's predicate/input digests, explicit
  machine-readable outcome, and resulting terminal record or failure status;
- every bounded adversarial-review packet, reviewer-independence attestation,
  candidate-finding disposition and adjudication, and the
  `G-ADVERSARIAL-REVIEW`/`G-NO-MATERIAL-FINDING` inputs and outcomes;
- hard errors;
- precision after novel-finding adjudication;
- configuration and safe-surface coverage;
- citation and TCB defects;
- authoring/edit preservation results;
- skill versus baseline/prior-skill paired comparisons;
- current-zerocopy shard and integration outcomes;
- invalid/quarantined fixtures;
- threats to validity; and
- proposed skill changes linked to behavioral failures.

Do not publish opaque holdout source or answers. Do not publish vulnerable code
whose license or coordinated-disclosure status forbids it.

## Threats to Validity

Actively monitor:

- public advisories and famous fixes present in model training;
- answer leakage through source comments, tests, changelogs, crate names, or
  network search;
- source reductions that remove the actual producer/consumer chain;
- “fixed” labels being mistaken for whole-crate soundness;
- tool warnings being mistaken for ground truth;
- Reference/std documentation changing after a fixture was proved;
- compiler behavior or aliasing/provenance models changing;
- running only the configuration that triggers a known bug;
- unrealistic prompts, budgets, or permissions;
- scorer awareness of condition;
- evaluator disagreement hidden by one numeric score;
- model updates being mistaken for skill improvements;
- repeated-candidate optional stopping or unchanged-candidate resubmission;
- holdout leakage through source-family or metamorphic siblings assigned to
  different cohorts;
- post-exposure fixture quarantine, substitution, retry, or package edits that
  preserve a favorable result while changing its frozen denominator;
- duplicating one incident across RustSec, GHSA, audit logs, and research
  datasets; and
- benchmark-specific instructions accreting into the runtime skill.

The response to contamination is access-controlled metamorphic/holdout renewal,
not more explicit hints in the prompt.

## Per-Sequence Release-Gate Readiness Checklist

Before launching the first semantic agent in a claim epoch, and again for every
applicable inherited item before a permitted successor sequence:

1. Freeze the skill revision.
2. Implement the private fixture/oracle manifest and result schema.
3. Create the 2,177-record audit-log ledger, freeze an initial adjudicated
   denominator, and continue full record/atom/URL closure as the release-scale
   corpus goal.
4. Admit an initial Objective-defect and Scoped-positive tranche with
   two-reviewer authority-rooted proofs.
5. Materialize vulnerable/fixed zerocopy historical pairs.
6. Materialize current zerocopy's manifest-defined invariant-owner shards,
   whole-source variant, boundary coverage map, and supported-set manifest.
7. Build and hash blind bundles; scan them for oracle leakage.
8. Prepare pinned offline Rust/std documentation and exact external contracts.
9. Construct and review the hardened no-network VM/microVM runner for any
   executable artifact.
10. Dry-run only the harness on a trivial non-evaluation fixture.
11. Freeze the canonical claim epoch and equivalence rule, effective-treatment
    identity/equivalence and admission rules, prompts, corpus
    denominator/exclusions, persistent regression/registry state, budgets,
    conditions, leased-attempt/retry/finalization/invalidation rules, numerical
    endpoints and margins, scorer rubrics, exact-engineering versus inferential
    mode, mandatory gate-root inventory and total fail-closed executable
    manifest, global finite `N_max`, fully lineage-disjoint holdout cohorts,
    exact terminal stopping predicate, and across-candidate/successor error
    control.
12. Calibrate independent scorers and resolve every admission disagreement.
13. Verify in an automated attestation that agents cannot read `evals/`,
    `maintainers/`, sibling worktrees, prior results, another condition's skill
    package, or the other half of any pair; validate the principal/process
    exposure ledger and role restrictions for every unconsumed holdout.

Only after every applicable item is satisfied may that sequence begin semantic
testing. Any agent-visible skill change made in response to a result creates a
new candidate: rerun the cumulative reusable prequalification and admit a fresh
terminal look only under the claim epoch's frozen rule. Never continue the same
agent conversation.
