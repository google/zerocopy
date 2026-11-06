---
name: reference-research
description: >-
  Plan and execute iterative, multi-round technical research and experimentation
  to a fixed point, then coalesce findings into validated report packages and
  publish them to the `reference` branch. Use when investigating open-ended
  technical questions, harvesting retrospective research from engineering work,
  or upstreaming research findings into the `reference` corpus. Not for
  mechanical catalog regeneration, validator maintenance, or single-line typo
  fixes in existing reports.
---

# Reference corpus research

Turn a technical prompt, engineering retrospective, or body of preliminary
findings into durable, self-contained report packages on the `reference` branch.

Before starting, read [`AGENTS.md`](../../AGENTS.md) and
[`FORMAT.md`](../../FORMAT.md) on `reference`. Those documents own corpus
authority, report package structure, evidence roles, `tools/reference.py`
validation, and atomic fast-forward publication. This skill governs the
research, experimentation, convergence, and synthesis process that feeds those
contracts.

## Establish scope, stopping boundary, and orchestration topology

- **Stopping boundary:** Determine whether the caller wants:
  - **Brainstorm / plan only:** Produce the initial set of research and
    experimental questions and proposed investigation tracks, then stop for
    review.
  - **End-to-end execution and publication:** Brainstorm, iterate through
    research rounds to a fixed point, coalesce all findings into report
    packages, validate, and push to `reference` without pausing between rounds
    unless a genuine ambiguity in user intent arises.

  If the request leaves this stopping boundary ambiguous, ask the user to
  clarify **before** beginning the brainstorming process.

- **Coordinator delegation:** When this workflow is invoked during ongoing
  engineering work (for example, to harvest retrospective research or run a
  parallel investigation while coding continues) and the host supports nested
  subagents, delegate the research program to a single coordinator subagent.
  The coordinator owns the multi-round loop, scratch state, synthesis, and
  final publication so the parent conversation remains unblocked.

- **Workspace isolation:** Keep discovery and round artifacts in local scratch
  space outside the `reference` candidate tree. Only final report packages
  (`reports/<package>/`) and regenerated `CATALOG.json` belong in the
  `reference` worktree.

## Derive and refine open questions

At the start of the program—and again after each round completes—compare what is
already established against the governing scope and `FORMAT.md`'s evidentiary
requirements:

- **Check the existing corpus first:** Query `CATALOG.json` programmatically
  (filtering by package name, `topics`, or `subjects` with Python or `jq` rather
  than reading the full file into context) and read the relevant existing
  packages under `reports/`. Reuse established findings instead of rediscovering
  them; schedule new work on a covered topic only when targeting an unexamined
  boundary, a newer upstream revision, or a revalidation probe, and note any
  existing topic package that the new findings or version coverage should update
  and coalesce into.

- **Brainstorm and update open questions:** Derive concrete research and
  experimental questions from four sources:
  - **Unverified premises:** Claims or design choices that depend on upstream
    specifications, source code, compiler passes, kernel checks, or tool
    behavior not yet verified at an immutable revision.
  - **Cross-component seams and discrepancies:** Interfaces between subsystems
    or passes whose producer/consumer invariants have not been checked
    together, or disagreements between documentation, source, and execution.
  - **Missing empirical discriminators:** Questions where static source reading
    leaves runtime, elaboration, corner-case, or performance behavior ambiguous
    and a concrete reproducer, benchmark, or mechanized probe can decide it.
  - **Retrospective friction:** When seeded from prior design, implementation,
    or debugging work, identify anything that was ambiguous, surprising, or
    required trial-and-error and formulate the questions and probes that would
    have resolved that friction upfront.

Separate durable technical questions from task-local context. If the prompt,
retrospective, or preliminary findings refer to local worktrees, unmerged
branches, throwaway experiment commits, pull request stacks, issue or audit
checklist IDs, or undefined project-internal symbols, do not carry those
ephemeral references forward as if future readers will recognize them. Treat
claims that already satisfy `FORMAT.md` (durable upstream subject identities,
self-contained definitions, primary-source citations, and reproducible probes)
as established, and turn any unpinned, context-dependent, or incomplete claims
into open questions or self-contained probes for the next round.

If the authorized stopping boundary is **brainstorm / plan only**, present the
resulting question set and proposed investigation tracks and stop.

## Execute rounds to a fixed point

Repeat the following round loop until the open question set reaches a fixed
point:

- **Partition and fan out:** Group the current open questions into independent
  investigation tracks. When subagent parallelism reduces wall-clock latency or
  isolates noisy exploration, spawn parallel subagents—one per track. Give each
  subagent a self-contained brief containing:
  - Its assigned questions and scope boundaries;
  - The exact durable upstream subjects and revisions to inspect or execute;
  - The required `FORMAT.md` evidence roles (`normative`, `documentation`,
    `source`, `execution`, `derived`) and instructions to build standalone,
    reproducible probes or minimal reproducers and to record self-contained
    definitions of any experimental types, predicates, or harnesses rather than
    citing local branch names, throwaway commits, or undefined internal symbols;
  - An isolated scratch directory for its working files and round report;
  - Explicit instructions to list any newly discovered premises, edge cases,
    cross-track seams, or unresolved questions at the end of its round report.

- **Evaluate and cross-check the round:** When all tracks in the round
  complete, inspect their reports and probes against primary sources:
  - A question is **resolved** only when backed by `FORMAT.md`-grade primary
    source or execution evidence—never by unverified model recollection—or when
    direct investigation establishes the case as `unknown` or `unsupported`.
  - A newly surfaced question **enters the next round** if and only if it is
    within the governing scope, not already answered in `CATALOG.json` or prior
    rounds, and load-bearing for the accuracy, completeness, or soundness of an
    in-scope finding or cross-track seam.
  - Worthwhile questions **outside** the governing scope do not trigger new
    rounds; record them for the final reports' `Boundaries` sections as
    `not examined`.

- **Fixed-point and bounded-stop conditions:**
  - **Fixed point:** Stop iterating when every in-scope question is resolved
    and no new load-bearing in-scope questions remain.
  - **Bounded stop:** If an external constraint (unavailable credentials,
    hardware, toolchain, or caller resource limit) prevents resolving a
    remaining in-scope question, stop iterating on that question and record the
    exact limitation under `Boundaries` (`unknown` or `not examined`) rather
    than guessing or looping.

## Coalesce across rounds and publish to `reference`

Once the research loop reaches its fixed point, synthesize the accumulated
evidence across all rounds into corpus report packages:

- **Group by durable subject and topic, not discovery history:**
  - Partition the findings into a natural set of self-contained report packages
    (`reports/<package>/REPORT.json`, `REPORT.md`, and optional `support/`
    material) according to `FORMAT.md`, using only the canonical top-level
    `topics` namespaces and the six required H2 sections (`## Summary`,
    `## Applicability`, `## Findings`, `## Boundaries`, `## Evidence`,
    `## Revalidation`) enforced by `tools/reference.py check`. When findings
    extend or revalidate a topic already covered in the corpus, prefer updating
    and coalescing into that report package—listing all covered versions in
    `REPORT.json` `subjects` and stating clearly under `Applicability` and
    `Findings` which behaviors are shared and which differ across
    versions—rather than creating separate per-version packages.
  - Make every report self-contained for a cold reader. It is fine if the
    *reason* a report was written is not apparent, but its *meaning* must be
    unambiguous without assuming shared context. Pin `REPORT.json` `subjects`
    only to durable, externally resolvable upstream revisions or release
    artifacts (never local worktrees, unmerged branches, throwaway experiment
    commits, or prior commits of `reference`). When a finding comes from a
    throwaway experiment, local prototype, or counterfactual design variant,
    define the mechanism or model inline in `REPORT.md` and preserve the
    standalone probe in `support/` rather than citing an ephemeral commit,
    branch name, local workstation path, or undefined symbol as if a reader
    could look it up externally (whereas concrete paths whose role is
    self-explanatory in place, such as `/tmp/...` in a reproduction command or
    an embedded build-host path like `/Users/runner/...` inside a binary
    relocation finding, are fine). Even for durable upstream subjects, include
    the relevant signature, definition, or invariant in `REPORT.md` whenever a
    bare symbol name or line range would be opaque without checking out that
    tree.
  - Fold refinements, corrections, and follow-up probes from later rounds
    directly into the claims they qualify. Do not organize `REPORT.md`
    chronologically by round (`Round 1`, `Round 2`) or expose internal track
    identifiers (`WS1`, `Track 3`), issue or audit checklist IDs, subagent
    conversation links, or temporary scratch paths.
  - Preserve high-value executable artifacts (mechanized proofs, compiler or
    toolchain probes, minimal reproducers, verification scripts, and golden
    specimens) in `reports/<package>/support/` so future agents can rerun cheap
    revalidation checks.

- **Single-writer validation and atomic publication:**
  - Fetch the latest `origin/reference` tip and prepare a clean candidate
    worktree from it.
  - If spawning parallel authoring subagents to write the coalesced packages,
    assign each subagent a strictly disjoint `reports/<package>/` directory.
    Authoring subagents must not edit `CATALOG.json` or run `git commit` or
    `git push`.
  - After all package directories are written, the coordinator alone runs:

    ```console
    python3 tools/reference.py catalog
    python3 tools/reference.py check
    ```

  - Verify that every package satisfies `FORMAT.md`'s semantic and structural
    requirements and that no scratch files or untracked state remain in the
    worktree.
  - Commit and fast-forward push to `reference` following the atomic
    publication protocol in `AGENTS.md`. If another writer advanced
    `origin/reference` while the research program was running, fetch the new
    tip, replay the candidate packages onto it, rerun `catalog` and `check`,
    and retry the fast-forward push.
