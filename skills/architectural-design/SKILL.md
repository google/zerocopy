---
name: architectural-design
description: >-
  Orchestrate end-to-end architectural design from target grounding and
  empirical research through divergent 4-dial brainstorming, multi-agent
  swarm-model-refinement, post-refinement feature-weight pruning, and a
  self-contained design specification. Use when designing or redesigning a
  system, subsystem, semantic model, protocol, or framework with open design
  trade-offs or empirical unknowns. Not for routine implementation of a settled
  design, standalone conceptual minimization without end-to-end design framing,
  or pure empirical investigation without a target design deliverable.
---

# End-to-End Architectural Design

Turn an open architectural problem into a verified, conceptually minimal, and
self-contained design specification. Keep four layers distinct throughout the
workflow:

1. **The two-sided governing contract $C = (C^+, C^-)$** (what positive
   outcomes, cross-axis invariants, and caller-mandated constraints $C^+$ must
   hold in the target system, what fixed scope boundaries, out-of-scope threats,
   and retired prototype assumptions $C^-$ are excluded, and why);
2. **Empirical system facts** (what the compiler, language specification,
   kernel, runtime, or workload actually does at the pinned revision);
3. **Candidate mechanisms and models** (how a candidate model $M$ proposes to
   satisfy $M \models C$—meeting every positive obligation in $C^+$ while
   violating no constraint in $C^-$—explored in the `Candidate Idea Pool` and
   minimized via `swarm-model-refinement` and `model-refinement`); and
4. **The delivered design specification and its lifecycle disposition** (a
   reader-oriented specification of the confirmed design at `local convergence`—
   or an explicitly qualified specification on a `bounded stop`—with rejected
   alternatives isolated in `Appendix A` and open policy choices surfaced).

Scale the workflow to the task and enter at the first unresolved state boundary
rather than replaying settled phases or manufacturing ceremony:

- **Unified entry rule across cold-start, warm-calibrated, post-review, and
  incremental PR/spec tasks:** Before launching experiments or brainstorming,
  establish the **Phase 1 Calibrated Baseline** (§1.1–1.3) against the target
  workspace: the Authoritative Target Baseline (including all controlling
  normative authorities), the two-sided governing contract $C = (C^+, C^-)$,
  and any falsifiable empirical unknowns.
  - **Cold or partially calibrated entry:** Pause at **Checkpoint 1** (§1.4) to
    confirm uncalibrated goals, newly discovered normative-authority conflicts,
    or Phase 2 `reference-research` authorization before advancing.
  - **Warm or mid-stream entry (no redundant Checkpoint 1):** When the caller
    has already calibrated the target baseline and $C = (C^+, C^-)$ in context
    and no new `reference-research` authorization or normative-authority
    conflict remains, record the complete Calibrated Baseline (including $C^-$)
    in the phase checkpoint and skip the Checkpoint 1 pause, advancing directly
    to the first unresolved stage—Phase 2 (if empirical reproducers remain),
    Stage 3.1–3.2 (if open design exploration is needed), or Stage 3.1 followed
    by Stage 3.3–3.4 (when the caller already supplies candidate architectures,
    an existing PR/spec, or post-review/red-team findings, seeding those
    candidates into the `Candidate Idea Pool` or incumbent `Architect γ` after
    completing Stage 3.1).
- **Proportional phase and worker scaling:** If no unresolved empirical unknowns
  exist, skip Phase 2. If worker slots are constrained or a bounded problem
  lacks coupled multi-axis trade-offs warranting multi-agent fan-out, scale
  Stage 3.2 and Stage 3.3 down to fewer workers or single-agent
  `model-refinement` (with an unanchored fresh critic when independent review
  adds value) rather than spawning a full swarm.

## Composition, dependencies, and authority boundaries

Obtain peer skills through the host's supported mechanism or an explicitly
supplied package (reusing any already loaded in context); do not assume a
hardcoded sibling path or universal import facility:

- **`tech-lead`:** Requirement recovery, risk prioritization, and context
  persistence across compaction.
- **`reference-research`:** Multi-round empirical investigation, minimal
  reproducers, and (when separately authorized) reference corpus publication.
- **`swarm-model-refinement` and `model-refinement`:** Multi-agent and
  single-agent conceptual model minimization, generalization, counterexample
  search, comparative adjudication (including the incumbent), and
  completion-boundary rereads.
- **`robust-code` and repository trust/domain skills (such as `trust-review`):**
  Invariant-preserving representations, explicit effects, and trust-boundary
  compliance.
- **`reader-oriented-explanation` and `williams-style`:** Organizing and
  drafting calibration summaries, repository documentation, and the final design
  specification for readers who did not witness the design session.

If a required peer skill is unavailable and not supplied in context, continue
only the work supported without it, explicitly name the unavailable skill and
its unperformed responsibilities, and report a **bounded stop** (or request the
missing package); never invent its rules from memory or claim it was applied.

Invoking this skill grants no authority to modify canonical source files outside
authorized design or scratch paths, commit or push changes, launch
`reference-research` or publish to reference-corpus branches without explicit
user approval, spend unapproved compute, or create standing background
automation. When an authorized scratch directory or detached worktree is
available, keep intermediate exploration, reproducers, and swarm artifacts
inside it.

## Persistence, sub-agent isolation, and recovery

Multi-stage architectural design can span multi-depth sub-agent trees (`depth-0`
root to `depth-1` stage coordinator to `depth-2` workers) and encounter context
compaction, timeouts, or mid-run premise changes:

1. **Persist phase checkpoints and propagate premise invalidations:** On
   multi-wave or interruption-prone tasks where an authorized scratch or
   artifact directory is available, write each phase's state—the confirmed
   two-sided governing contract $C = (C^+, C^-)$, Phase 2 empirical findings,
   Stage 3.1 discovery set and non-revealing holdout metadata (keeping concrete
   blind holdout bodies out of shared checkpoint directories readable by
   candidate contexts; see Stage 3.1), Stage 3.2 candidate pool, and Stage
   3.3/3.4 pass records—to durable files before advancing, and reconstruct state
   from those files after compaction. On short in-conversation tasks or when no
   writable scratch path is authorized, keep checkpoint summaries in context
   rather than writing to unauthorized paths. If a Phase 2 empirical finding,
   Stage 3.4 codebase check, or user redirect invalidates an earlier premise,
   mark dependent downstream artifacts **superseded**, preserve still-valid
   evidence, and re-run only the affected stages.
2. **Read live state before retrying interrupted work:** A sub-agent or command
   timeout does not prove failure. Inspect any authorized scratch directory or
   worktree output on disk before re-running an experiment or sub-agent pass.
3. **Verify sub-agent input paths, propagate coordinator rules across depths,
   and enforce depth-safe write boundaries:**
   - **Propagate target-baseline, $C = (C^+, C^-)$, and coordinator rules:**
     Every sub-agent brief across Phases 1–3 must supply the exact path and
     revision of the Authoritative Target Baseline (and any controlling
     normative documents) plus both $C^+$ and $C^-$—inline or in a single
     verified contract file on disk—so isolated workers never consult stale
     branches or read $C^+$ without $C^-$. Whenever `depth-0` delegates Phase 2
     or Stage 3.3 to a `depth-1` sub-agent coordinator, the `depth-0` brief must
     also pass this `SKILL.md` (or inline the pre-spawn input-path check,
     `depth-2` `<self-id>/scratch/` write-boundary rule, ~10-minute heartbeat
     rule, and Stage 3.3.2 adjudication and stopping rules) so the `depth-1`
     coordinator enforces them when spawning `depth-2` grandchildren.
   - **Pre-spawn input-path check:** Before spawning any sub-agent at any depth
     (especially under strict input-isolation rules that forbid directory
     listing), verify on disk that every file path referenced in its brief
     exists and is readable.
   - **Depth-safe output paths and bounded single-turn writes:** Host
     `write_file` controls typically permit writing only to a conversation's own
     artifact directory or its direct (`depth-1`) parent's artifact directory,
     rejecting writes by `depth-2` grandchildren to a grandparent (`depth-0`)
     artifact directory. Instruct delegated sub-agents (especially `depth-2`
     grandchildren spawned by a `depth-1` coordinator) to write scratch outputs
     to their **own** conversation scratch directory
     (`<appDataDir>/brain/<self-id>/scratch/...`, omitting `ArtifactMetadata`)
     or an authorized `/tmp/...` directory and return the written absolute path
     via `send_message`. Keep single-turn `write_file` payloads bounded within
     output-token limits (splitting large reports or appendices across
     sequential writes when needed).
4. **Bound progress heartbeats to the active phase:** When delegating a
   long-running phase (`reference-research` or `swarm-model-refinement`)
   expected to run for more than 10 minutes, instruct the sub-agent coordinator
   upfront to emit progress updates every ~10 minutes using a task-scoped,
   non-daemon timer (`IsDaemon: false` where supported) summarizing completed
   checks, active workers, and remaining blockers, and cancel any active timer
   as soon as the phase finishes. Never create daemon schedules or fabricate
   progress telemetry when a worker is silent.

## Phase 1: Target grounding, contract calibration, and research discovery

Establish the Phase 1 Calibrated Baseline before proposing mechanisms or
launching experiments, pausing at **Checkpoint 1** whenever human confirmation
or research authorization is needed.

### 1.1 Partition Authoritative Target Baseline from Historical/Prototype Foils

When surveying the workspace, explicitly separate sources by their epistemic
authority:

- **Authoritative Target Baseline:** The exact target branch or worktree where
  the design will live, its live code and tests, and **all controlling normative
  authorities**—including governing principles, threat models, and companion
  design specifications or interface contracts across linked branches,
  worktrees, or sibling repositories that constrain the target subsystem. These
  define the actual interfaces, invariants, and workloads the design must
  satisfy.
- **Historical / Prototype Foils:** Older branches (including `main` when
  designing against an active refactoring branch), prior pull requests,
  superseded prototypes, or sibling implementations. These supply **failure
  modes, edge cases, and empirical lessons only**—never default features, file
  formats, directive syntaxes, CLI flags, or contract requirements.

Apply the **Assumption-Survival Test** to every mechanism, feature, or
workaround encountered in a historical prototype or earlier codebase version:

1. **Identify the generating problem and the prototype's generating
   assumption:** Record *what underlying failure mode* the historical mechanism
   addressed and *what architectural assumption in that older system* made the
   mechanism necessary (for example, per-target-crate hand-edited proof files or
   intermediate transpiled snapshot files).
2. **Test whether the generating assumption still holds in the Authoritative
   Target Baseline:**
   - If the target baseline eliminated that assumption, classify the historical
     mechanism—and every directive, flag, or test mode that existed only to
     exercise or configure it—under **Retired Prototype Assumptions
     (Non-Goals)** in $C^-$.
   - If the underlying problem still exists in the target baseline, carry
     forward **only the required outcome or failure mode** into $C^+$ (for
     example, attributing verification failures to a specific function or
     keeping parallel test runs from dirtying tracked lockfiles), recording in
     $C^-$ that the prototype's mechanism is not required.

### 1.2 Formulate the Two-Sided Governing Contract $C = (C^+, C^-)$

Separate *what must hold, what is excluded, and why* ($C$) from *how to build
it* (candidate models $M$):

1. **Positive Obligations and Caller-Mandated Constraints ($C^+$, clauses
   `C1`–`Ck`):**
   - **Orthogonal guarantee axes and cross-axis interactions:** When a problem
     entangles distinct failure modes or guarantee tiers, factor them into
     orthogonal axes with explicit consequences and rationale (for example,
     runtime UB-freedom vs. compile-time verification stability, or
     unconditional safe-function UB-freedom vs. conditional functional
     postconditions). Whenever a single mechanism, attribute, syntax, or
     semantic predicate participates in more than one guarantee axis—or bridges
     compile-time obligations (such as post-monomorphization layout and `const`
     evaluation checks) and runtime preconditions—test the **cross-product of
     those axes** rather than evaluating each axis in isolation. Ask: *if a
     caller or user exercises Axis B on an item, does it weaken, bypass, or
     render vacuously true an unconditional obligation on Axis A?* Record every
     required cross-axis invariant in $C^+$.
   - **Caller-mandated boundary constraints:** Explicitly preserve any
     representation, wire format, public trait or API signature, CLI flag,
     platform boundary, or interoperability requirement mandated by the caller's
     request or a controlling normative authority, while distinguishing true
     caller requirements from historical prototype holdovers or speculative
     candidate mechanisms.
2. **Explicit Negative and Scope Constraints ($C^-$, clauses `NC1`–`NCn`):**
   - **Fixed scope boundaries and out-of-scope threats:** State what is held
     fixed for a single design or verification instance (for example, a single
     configured compilation with fixed target primitive layout and resolved
     conditional-compilation predicates, or the boundary between target-crate
     pipeline tests and host CLI containment tests) and which threats or failure
     modes are out of scope under the governing threat model.
   - **Retired Prototype Assumptions and Non-Goals:** Explicitly list all
     mechanisms, directives, and assumptions retired by the Assumption-Survival
     Test or excluded as non-goals so downstream agents and holdout authors do
     not re-invent them.

### 1.3 Discover falsifiable empirical research questions

Identify every non-obvious technical question where an unverified assumption
about a compiler, language specification, kernel/elaborator, runtime, or
workload could invalidate the architecture or force defensive over-engineering:

1. **Check existing reference knowledge first:** When a technical reference
   corpus (such as `CATALOG.json` and `reports/<package>/`) is accessible in the
   workspace, filter it programmatically and verify each report's pinned
   revisions, applicability, and boundaries before proposing new experiments.
2. **State concrete, falsifiable questions:** Frame each remaining unknown so it
   can be resolved by primary source inspection and minimal executable
   reproducers at the repository's pinned toolchain revision.

### 1.4 Pause at Checkpoint 1 (when uncalibrated or awaiting approval)

When any element of the Phase 1 Calibrated Baseline requires human confirmation
or `reference-research` approval, present a concise calibration summary (or
artifact) covering:

1. **Authoritative Target Baseline vs. Retired Prototype Assumptions ($C^-$):**
   Which branch, worktree, and companion normative contracts are authoritative,
   and which legacy mechanisms from prior iterations are retired as non-goals.
2. **Governing Goals, Orthogonal Axes, Cross-Axis Invariants, and Scope
   Boundaries ($C^+, C^-$):** What outcomes, cross-axis interactions, and caller
   constraints the design must guarantee and what lies outside scope.
3. **Proposed Empirical Research Plan and `reference-research` Authorization:**
   The exact empirical questions to investigate in Phase 2. Whenever Phase 2
   would invoke `reference-research` (or harvest findings into a reference
   corpus), explicitly ask the human at Checkpoint 1 whether to launch
   `reference-research` and whether to stop after **brainstorm / plan only** or
   run **end-to-end execution and publication**.
4. **High-Leverage Goal Clarifications:** Any genuine ambiguity in user goals,
   scope, or risk tolerance.

Wait for human confirmation at Checkpoint 1 before launching Phase 2 or Phase 3
(when already calibrated by the caller, record the baseline including $C^-$ in
the phase checkpoint and advance under the warm-entry rule above).

## Phase 2: Synchronous empirical research and goal-consistency gate

When Phase 1 identifies unresolved empirical questions, execute the approved
empirical investigation synchronously before design brainstorming:

1. **Run approved empirical research synchronously:** Execute the Phase 1
   research plan (confirmed at Checkpoint 1 when required, and running
   `reference-research` at the approved stopping boundary only when explicitly
   authorized by the user, with task-scoped ~10-minute progress heartbeats if
   long-running). Running research synchronously as a sequential stage avoids
   cross-track coordination overhead and ensures Phase 3 builds on verified
   facts rather than speculation. If the approved boundary is **brainstorm /
   plan only**, return that research plan as requested and stop until execution
   is authorized.
2. **Evaluate the Goal-Consistency Gate (Default: Auto-Advance):** When Phase 2
   execution completes, record the empirical findings and compare them against
   the Phase 1 two-sided governing contract $C = (C^+, C^-)$:
   - **Auto-advance (default):** If the empirical findings are consistent with
     the calibrated contract $C$—even if they refute specific candidate
     mechanisms—advance immediately to Phase 3 without pausing for human input.
   - **Contradiction pause (exception):** Pause and consult the human *only* if
     an empirical finding directly contradicts or invalidates a confirmed goal,
     cross-axis invariant, scope boundary, or soundness premise in $C$.

## Phase 3: Two-stage divergence-to-convergence funnel

Once goals and empirical facts are established, seal the two-sided governing
contract $C = (C^+, C^-)$ and holdout boundary, explore the design space
broadly, and converge on a verified minimal model before drafting the
specification.

### Stage 3.1: Seal the two-sided contract $C = (C^+, C^-)$ and holdouts

Before generating or inspecting candidate designs, freeze $C = (C^+, C^-)$ and
the Discovery vs. Holdout partition:

1. **Freeze the Two-Sided Governing Contract $C = (C^+, C^-)$ in one artifact:**
   - **Keep $C^+$ (`C1`–`Ck`) outcome- and caller-boundary-only:** Because
     `model-refinement` forbids dropping any required clause of $C$, writing a
     historical prototype feature or an unconfirmed candidate mechanism (such as
     a legacy archive format, directive syntax, or auxiliary subsystem) into
     $C^+$ locks it into every candidate model and prevents refinement from
     deleting it. State `C1`–`Ck` strictly in terms of confirmed target
     outcomes, cross-axis interaction invariants, concrete workloads, and
     caller-mandated boundary constraints (§1.2), grounded in Checkpoint 1 and
     Phase 2 empirical facts.
   - **Embed $C^-$ (`NC1`–`NCn`) directly alongside $C^+$:** Include Phase 1's
     negative and scope constraints ($C^-$: fixed scope boundaries, out-of-scope
     threats, and retired prototype assumptions/non-goals from §1.2) inside the
     same Stage 3 contract artifact passed to every Phase 3 role (`Steward`,
     `Brainstorm Dials`, `Architects`, `Challengers`, `Holdout Stitcher`, and
     `Fresh Critics`) so isolated workers and holdout authors never read $C^+$
     without $C^-$ or re-invent retired mechanisms.
2. **Isolated, scope-compliant holdout construction and storage:** Construct and
   scope-check the confirmation cases against *both* $C^+$ and $C^-$ *before*
   candidate brainstorming or synthesis begins:
   - **Multi-agent blind holdouts (`H1`–`Hm`):** Delegate construction and scope
     verification of `H1`–`Hm` to an isolated `Steward` or `Holdout Stitcher`
     context that receives only the Authoritative Target Baseline and the full
     Two-Sided Contract $C = (C^+, C^-)$—explicitly forbidding holdouts that
     demand retired prototype mechanisms or out-of-scope threats in $C^-$, and
     withholding any caller-supplied candidate architectures on warm entry—while
     keeping concrete holdout premises uninspected by the coordinating context
     and candidate explorers. On hosts where sub-agents share a readable
     filesystem (`swarm-model-refinement` Core Invariant 5), **never write
     concrete bodies of unexposed blind holdouts into shared checkpoint
     directories or Coordinator-read summaries while candidate synthesis or
     repair remains open**: keep unexposed `H1`–`Hm` premises inside a
     host-enforced read-isolated `Steward` / `Holdout Stitcher` context,
     recording only non-revealing metadata (such as counts, scope-compliance
     status, and violated contract clause IDs) in shared checkpoints alongside
     any holdouts explicitly disclosed and reclassified as exposed design
     witnesses under Invariant 3. If a host lacks read-isolated storage and
     unexposed holdout bodies are written to a shared filesystem while synthesis
     or repair remains open, forbid candidate and synthesizing contexts from
     reading outside their briefed input paths and qualify those checks in Phase
     4 as exposed to that host filesystem-isolation limit (treating any holdout
     read by a candidate or synthesizing context as an exposed design witness).
   - **Single-agent or Coordinator-authored scenarios (exposed design
     witnesses):** Whenever single-agent execution or worker limits cause the
     coordinating context to prepare or inspect scenarios and that same context
     also develops, synthesizes, or revises the candidate, those scenarios
     cannot serve as held-out or Architect-blind confirmation
     (`model-refinement` treats any case known while developing or revising the
     candidate as a design witness). Classify all Coordinator-known scenarios
     strictly as **exposed design witnesses**; use an isolated unanchored `Fresh
     Critic` when independent confirmation is needed and a sub-agent slot is
     available, or report the single-context isolation limit in Phase 4
     (applying `model-refinement`'s single-agent convergence criteria when
     appropriate, or reporting a `bounded stop` if the task requires independent
     or held-out confirmation).

### Stage 3.2: Divergent 4-dial creativity brainstorm

Explore the design space across four creativity priors (`Dial 1`–`Dial 4`),
supplying the Authoritative Target Baseline, the full two-sided governing
contract $C = (C^+, C^-)$, the Exposed Discovery Set (never Blind Holdouts), and
Phase 2 empirical findings. Require concrete data structures, state/data-flow
boundaries, and trade-off accounting from each perspective:

- **Dial 1 (Conservative / Textbook):** Proven, minimal-surprise mechanisms and
  standard idioms that satisfy $C$ with zero novel abstractions.
- **Dial 2 (Moderately Conservative / Pragmatic Synthesis):** High-leverage
  structural unifications and clean boundary separations within the existing
  system architecture.
- **Dial 3 (Moderately Creative / Structural Redesign):** Rethinking internal
  representations, data flow, or stage boundaries to eliminate entire classes
  of plumbing, boilerplate, or failure modes.
- **Dial 4 (Extremely Creative / Radical Zero-Base Rethink):** Challenging
  every non-mandatory boundary to find radical theoretical or operational
  collapses, even if only individual component insights survive into the final
  model.

Scale execution of the four dials to the host's available worker slots and task
complexity: spawn up to four parallel sub-agents when worker capacity permits;
on hosts with fewer available worker slots (for example, when the coordinator
occupies one of four total slots), run the dials in waves or consolidate
adjacent dials across 1–3 sub-agents; on bounded single-agent runs, evaluate
the four priors sequentially in context.

Coalesce the distinct component mechanisms, representations, and architectural
candidates into the mutable `Candidate Idea Pool`. **Do not pause to ask the
human to choose from this unrefined brainstorm menu, and do not promote
candidate mechanisms from the `Candidate Idea Pool` into $C^+$.**

### Stage 3.3: Disciplined multi-agent `swarm-model-refinement`

Run `swarm-model-refinement` (or single-agent `model-refinement` when scaled
down for a bounded task) over the `Candidate Idea Pool` and the two-sided
governing contract $C = (C^+, C^-)$:

1. **Adversarial exploration, holdout stitching, and fresh criticism:** On the
   multi-agent path, follow `swarm-model-refinement`'s epistemic barrier and
   role-scaling rules—competing Architects (`α` minimization, `β`
   generalization, `γ` incumbent/surgical baseline), targeted `Challengers`,
   isolated `Holdout Stitcher` with cross-pass exposure accounting (verifying
   that each `H1`–`Hm` complies with $C^-$ and disqualifying any holdout premise
   that contradicts $C^-$), and per-pass newly spawned unanchored `Fresh
   Critics`—under the persistence, sub-agent isolation, `depth-1`
   delegation-brief propagation, and ~10-minute heartbeat rules above. On the
   scaled-down single-agent path, apply `model-refinement`'s candidate
   comparison (including the incumbent), whole-model burden accounting, and
   counterexample search directly over the `Candidate Idea Pool` and exposed
   scenarios, spawning an unanchored `Fresh Critic` when a sub-agent slot is
   available.
2. **Coordinator adjudication, literal-definition verification, and pass-cap
   discipline:** During iterative passes, the Stage 3.3 Coordinator owns
   comparative evaluation against $C = (C^+, C^-)$ and whole-model burden and
   must actively adjudicate findings rather than uncritically accreting patches:
   - **Enforce $C^-$ (reject retired-assumption and out-of-scope creep):**
     Evaluate every Challenger, Holdout, and Fresh Critic finding against both
     $C^+$ and $C^-$. Refute and discard any demand that resurrects a Retired
     Prototype Assumption, introduces an unconfirmed policy feature, or enforces
     an out-of-scope threat excluded by $C^-$.
   - **Detect and resolve critic-vs.-critic oscillations:** Maintain a
     cross-pass decision ledger. When Pass $k+1$'s critic flags a regression or
     burden shift caused by a change adopted in Pass $k$, do not oscillate or
     stack a compensating patch; compare the pre-patch and post-patch models
     directly against $C = (C^+, C^-)$ and whole-model burden, retain the
     supported winner, and close that oscillation axis against repeats of the
     same already-weighed argument. If a later critic or check supplies
     **materially new falsifiable evidence** on a closed axis—such as a new
     concrete counterexample, a formal or type defect, or a previously
     unexamined violation of $C = (C^+, C^-)$ that changes which candidate is
     supported—**reopen and re-adjudicate that axis** rather than suppressing
     the finding.
   - **Keep formal candidates focused on load-bearing semantics and trace
     literal definitions:** Whenever candidates include formal definitions,
     equations, code/type signatures, or state machines, keep Stage 3.3
     candidates focused on the core semantic definitions and boundary types
     (verifying them with available typecheckers or LSP tools when within task
     authority) rather than hand-editing hundreds of lines of un-typechecked
     boilerplate across passes. Instruct `Holdout Stitcher`, `Challengers`, and
     `Fresh Critics` to trace the **literal written formal definitions**—
     quantifier scopes, operator precedence (for example, `∃ x, A ∧ B → C` vs.
     `(∃ x, A ∧ B) → C`), parameter and index spaces, and state/type-argument
     threading—rather than relying on prose intent summaries. A prose-level
     `Holdout Stitcher` `PASS` never overrides a concrete formal or mechanical
     counterexample.
   - **Enforce a bounded pass budget and route dispositions cleanly:**
     - **Local convergence (multi-agent `swarm-model-refinement` path):** Stop
       iterating and declare **local convergence** on $M^*$ once a complete pass
       on the unmutated candidate $M^*$ accepts no conceptual-model change—with
       `Holdout Stitcher` and `Challengers` reporting zero contract ($C^+, C^-$)
       or formal defects and that pass's newly spawned unanchored `Fresh Critic`
       identifying no remaining defect or supportable improvement whose
       whole-model benefit justifies another pass (after discarding $C^-$
       violations, unsubstantiated stylistic preferences, and repeats of
       already-adjudicated oscillation arguments that introduce no new
       counterexample or contract defect)—and the required **completion-boundary
       reread** of the refinement guidance identifies no further change. Proceed
       to Stage 3.4.
     - **Local convergence (scaled-down single-agent `model-refinement` path):**
       When running the single-agent `model-refinement` branch (without separate
       `Holdout Stitcher` or `Challenger` sub-agents), apply
       `model-refinement`'s convergence criteria directly rather than
       fabricating multi-agent role reports: declare **local convergence** on
       $M^*$ once a complete verification pass over the unmutated candidate
       (checking all clauses of $C = (C^+, C^-)$, whole-model burden, literal
       formal definitions, counterexample search, applicable mechanical checks,
       and an unanchored fresh-critic sub-agent when one was spawned) followed
       by the required **completion-boundary reread** of `model-refinement` and
       this skill accepts no conceptual-model change, identifies no further
       supportable improvement justifying another pass, and leaves no unresolved
       required check (explicitly calibrating Phase 4 claims to single-agent
       verification and reporting the single-context isolation limit if no
       isolated critic was run). Proceed to Stage 3.4.
     - **Bounded stop:** Declare a **bounded stop** when passes hit the pass
       budget, resource/authority limits, missing evidence/tools, or an
       unresolved oscillation either while a genuine contract or formal defect
       remains open or before a mutated candidate has completed an unchanged
       confirmation pass and completion-boundary reread. When refinement ends in
       a **bounded stop**, **skip convergence-dependent pruning in Stage 3.4**
       and proceed directly to Phase 4's bounded-stop delivery path.

### Stage 3.4: Post-refinement audit, plumbing check, and re-confirmation gate

Phase 3 treats $\min_{M \models C} \text{complexity}(M)$ as its **directional
optimization objective**: per `model-refinement`, reaching `local convergence`
on $M^*$ is relative to the evaluated candidates, checks, and evidence and does
**not** prove that $M^*$ is a unique or global minimum over all $M \models C$.
Once $M^*$ reaches local convergence in Stage 3.3, evaluate its structural
footprint and estimated realization burden (distinguishing measured properties
from unmeasured engineering estimates) against the concrete Authoritative Target
Baseline in three steps:

1. **Zero-base mechanism-weight audit against the concrete target codebase:**
   Inspect every surviving mechanism, directive, state parameter, and subsystem
   in $M^*$ against the actual files, types, and existing tests of the
   Authoritative Target Baseline:
   - **Unconfirmed mechanisms and prototype holdovers in $M^*$:** Ask whether
     existing primitives in the target repository (such as ordinary unit or
     integration tests, existing compiler checks, or existing kernel
     obligations) already satisfy the confirmed contract $C = (C^+, C^-)$
     without bespoke framework machinery. Prune any unconfirmed mechanism or
     prototype carry-over in $M^*$ that is dominated by existing target
     primitives (while preserving every confirmed clause in $C^+$ and $C^-$),
     and record the eliminated mechanism in `Appendix A`.
   - **Confirmed obligations and boundaries in $C = (C^+, C^-)$:** Never
     unilaterally drop or weaken any positive obligation $c \in C^+$ or
     negative/scope boundary in $C^-$ confirmed by the human (even if originally
     proposed by the agent during Phase 1 calibration). If refinement reveals
     that a confirmed clause $c \in C^+$ imposes disproportionate structural or
     implementation burden relative to its target-system benefit, either pause
     to obtain explicit human approval before relaxing $C^+ \to C^{+\prime}$, or
     retain $c$ in the specification while surfacing the exact cost-vs.-value
     trade-off and simplified $C^{+\prime}$ alternative prominently in Phase 4
     for human decision.
2. **Plumbing-equivalence check on remaining open decisions:** For every open
   question or policy choice surfaced during refinement, check:
   - *Is one branch already entailed by the confirmed contract
     $C = (C^+, C^-)$?* If so, resolve it to match $C$.
   - *Do the competing options require different architectural machinery, or do
     they share identical underlying plumbing with a different configuration
     table or default boolean?* If the plumbing is identical, unify the
     architectural mechanism in the specification so it is not misframed as a
     structural fork, while **retaining the user-visible semantic or policy
     default as an explicit open human decision in Phase 4** (with a
     recommended default and trade-offs) unless the confirmed contract $C^+$
     already determines that default.
3. **Mandatory post-pruning `model-refinement` and re-confirmation gate:**
   - If Steps 1 and 2 make **no semantic, structural, or formal edits** to
     $M^*$, $M^*$ retains its Stage 3.3 `local convergence` status.
   - Whenever Stage 3.4 **modifies $M^*$ in any way** after Stage 3.3—whether
     by replacing a bespoke mechanism in $M^*$ with existing target primitives
     (Step 1), obtaining human approval to relax $C^+ \to C^{+\prime}$ (Step 1),
     unifying plumbing across a pseudo-fork (Step 2), or editing any formal
     definition, quantifier, or signature—the modified model $M^{*\prime}$ is a
     new candidate state:
     1. Run a dedicated `model-refinement` pass over $M^{*\prime}$ against the
        concrete target codebase to collapse any supporting scaffolding whose
        sole justification was a removed mechanism or retired clause; **and**
     2. **Re-verify and re-confirm the post-collapse $M^{*\prime}$ through the
        active Stage 3.3 convergence gate** (`multi-agent
        swarm-model-refinement` or `scaled-down single-agent model-refinement`
        branch in §3.3.2, tracing literal formal definitions where present and
        completing the required **completion-boundary reread** with zero further
        conceptual-model changes): on the multi-agent path, re-verify
        $M^{*\prime}$ against the Exposed Discovery Set, the Held-Out
        Confirmation Set (`H1`–`Hm`, with cross-pass exposure accounting under
        `swarm-model-refinement` Invariant 3), warm `Challengers`, the `Holdout
        Stitcher`, and a newly spawned unanchored `Fresh Critic` (plus
        mechanical checks where applicable); on the scaled-down single-agent
        path, complete the full §3.3.2 `model-refinement` verification pass (and
        an unanchored fresh-critic sub-agent when available) and calibrate Phase
        4 claims to single-agent verification without claiming independent
        multi-agent confirmation. **Self-review by the context that authored
        $M^{*\prime}$ never qualifies as independent confirmation**, and any
        scenario whose premise was known to the context that edited
        $M^* \to M^{*\prime}$ is an exposed design witness for $M^{*\prime}$.
     If re-confirmation exposes a defect in a Stage 3.4 modification, either
     **revert an optional Stage 3.4 pruning/simplification back to the
     already-confirmed Stage 3.3 model $M^*$**, or **repair $M^{*\prime}$**
     (reclassifying any holdout whose failure guided the repair to the Exposed
     Discovery Set under Invariant 3) and repeat sub-steps 1–2 on the repaired
     model. If post-mutation re-confirmation is not performed or a defect
     remains unresolved, report a **bounded stop** in Phase 4—never claim `local
     convergence` for an unconfirmed post-Stage-3.3 mutation.

## Phase 4: Reader-oriented design specification and lifecycle boundary

Draft the design specification as a standalone artifact (or update target
repository documentation when requested), applying `reader-oriented-explanation`
and `williams-style`.

### 4.1 Structure the main body and enforce zero process/history leakage

Partition design content cleanly across output surfaces so readers never have to
replay session chronology or filter out superseded history:

- **When refinement (and any Stage 3.4 re-confirmation) reached `local
  convergence`:** Present only the final, weight-checked, re-confirmed design in
  the main body.
- **When refinement or Stage 3.4 ended in a `bounded stop`:** Explicitly qualify
  the document at the top as a partial or conditional specification under a
  bounded stop, state which obligations, checks, or re-confirmation steps remain
  unresolved, and do not present unverified or unconverged parts as settled or
  minimal.
- **Enforce zero historical or process leakage across standalone specifications
  and target repository files:** Never leak design-session narrative (`"In Stage
  3.3"`, `"Candidate α/β/γ"`, `"Fresh Critic 002"`, `"Holdout H8"`) into the
  specification or repository files. When creating or updating tracked target
  repository documentation (`docs/*.md`, `DESIGN.md`, `README.md`) or code
  comments, write in the timeless present tense of the target architecture and
  state enduring scope boundaries and non-goals without historical diff or
  prototype-replacement framing (`"Previously we considered"`, `"Replaced
  prototype X"`, `"Retired feature Y"`), verifying via `git diff` that zero
  session or prototype-comparison narrative leaked into tracked files. Keep
  retired-prototype comparisons, `Appendix A: Alternatives Considered`, and
  branch/migration evolution in the standalone or scratch design specification
  and in PR descriptions or commit messages.

Organize the design specification main body into five sections:

1. **Purpose, Scope, and Governing Guarantees:** State the problem the design
   solves, the fixed scope boundaries, the orthogonal guarantee or stability
   axes and cross-axis invariants ($C^+$), caller-mandated constraints ($C^+$),
   and explicit non-goals ($C^-$; in a standalone design specification, include
   retired prototype assumptions here or in `Appendix A`, while in tracked
   repository documentation state timeless scope boundaries without prototype-
   diff framing).
2. **Architecture and System / Trust Boundaries:** Present a clear architectural
   overview showing how responsibilities are partitioned across components and
   how safety or trust-boundary invariants are enforced.
3. **Concrete Component and Semantic Specifications:** Specify the exact data
   structures, AST/state definitions, formal predicates, algorithms, file
   layouts, grammars, or CLI interfaces per component, grounded in the concrete
   files and types of the Authoritative Target Baseline.
4. **End-to-End Workflows, Verification Strategy, and Migration Plan:** Show how
   representative workloads and edge cases flow through the architecture end to
   end, how existing code or tests migrate, and how regressions are caught.
5. **Epistemic Calibration and Open Product-Policy Decisions:** Distinguish
   verified empirical facts (citing pinned toolchain/repository revisions and
   reproducers), formal or type-checked properties, conceptual
   `model-refinement` arguments (calibrated as local convergence relative to
   tested candidates and evidence rather than a global minimum), unmeasured
   implementation-cost estimates, and any remaining unverified assumptions or
   Bounded-Stop limits. List all open human product-policy or semantic-default
   decisions (including defaults over unified plumbing from Stage 3.4 Step 2 and
   any proposed contract relaxations from Stage 3.4 Step 1) concisely with their
   trade-offs and recommended default.

### 4.2 Record rejected mechanisms in `Appendix A: Alternatives Considered`

In a standalone design specification, place all rejected architectures,
candidate mechanisms falsified during `swarm-model-refinement`, and unconfirmed
mechanisms or prototype holdovers pruned during Stage 3.4 in a dedicated
`## Appendix A: Alternatives Considered` section at the end of the document,
grouped by thematic cluster (when updating tracked repository documentation
directly, record rejected alternatives in the standalone/scratch design
specification or in the PR/commit description rather than appending session
rejections to timeless repository docs):

- For each entry, state **the alternative mechanism or feature** and **the
  concrete dominance argument, counterexample, holdout failure, cross-layer
  burden shift, or target-primitive replacement** that eliminated it.
- Frame each entry by *what the alternative was* and *why it is inferior,
  unsound, or unnecessary in the target system*, without session narrative.

### 4.3 Separate design delivery from downstream implementation or publication

Delivering a design specification does not itself authorize modifying canonical
production code (outside authorized design or documentation files when
requested), committing or pushing to canonical branches, or publishing external
reports. Conclude by presenting the design specification, stating the refinement
disposition (`local convergence` or `bounded stop` with any qualifications), and
highlighting the open product-policy decisions or next implementation steps
that require human direction.
