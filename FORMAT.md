# Reference report format

This document defines the current format for technical reports on the
`reference` branch. Read `AGENTS.md` first; it defines the authority,
evidence, and publication rules that this format realizes.

A report is a self-contained reference unit rooted at a directory under
`reports/`. Its entry point is `REPORT.md`. A report may also contain local
`evidence/` and `probes/` directories when they materially reduce future
research or revalidation cost.

The current tree uses one report format. Do not add a format-version field merely
to describe this document. If the format changes, migrate the current corpus
coherently unless there is a demonstrated need for mixed formats.

## File structure

Every `REPORT.md` begins with one machine-readable metadata comment, followed by
one H1 title and these required top-level sections in order:

```markdown
<!-- reference-metadata
{
  "topics": ["system/topic"],
  "subjects": [
    {
      "name": "subject name",
      "identity": {
        "repository": "owner/repository",
        "revision": "full immutable revision"
      }
    }
  ],
  "observed_at": "YYYY-MM-DD"
}
-->

# Report title

## Summary

...

## Applicability

...

## Findings

...

## Boundaries

...

## Evidence

...

## Revalidation

...
```

Additional subsections may appear inside the required sections. Add another
top-level section only when it represents information that does not fit the
existing structure without distortion.

The report directory may contain:

```text
REPORT.md
evidence/   # optional
probes/     # optional
```

Keep support files local to the report unless actual reuse later justifies a
shared mechanism.

## Metadata

Metadata exists for machine retrieval and exact subject identification. Do not
duplicate prose merely to make metadata richer.

### `topics`

`topics` is a non-empty array of retrieval labels. Use concise lowercase,
slash-separated labels when a hierarchy is useful, for example:

```json
[
  "lean",
  "lean/elaboration",
  "lean/tactic-state"
]
```

Topics are navigation aids only. They do not establish applicability,
dependency, ownership, or authority.

Choose labels a future agent is likely to search for. Prefer established names
over locally coined synonyms. Add several labels when a report genuinely spans
several concepts rather than forcing it into one hierarchy.

### `subjects`

`subjects` is a non-empty array identifying the concrete things directly
examined and relevant to the report's claims.

Each subject has:

- `name`: a concise human-recognizable name, unique within the report;
- `identity`: a non-empty object containing the strongest available coordinates
  for the examined subject.

The identity shape is intentionally open rather than divided into Git, release,
artifact, protocol, or specification variants. Use the fields that precisely
identify the actual subject. Examples include:

```json
{
  "name": "Lean 4",
  "identity": {
    "repository": "leanprover/lean4",
    "revision": "0123456789abcdef0123456789abcdef01234567",
    "version": "v4.30.0-rc2"
  }
}
```

and:

```json
{
  "name": "released toolchain archive",
  "identity": {
    "artifact": "toolchain-linux-x86_64.tar.zst",
    "sha256": "..."
  }
}
```

Use full immutable revisions and hashes when available. A branch name, moving
tag, release label, package version, URL, or date may provide useful context but
does not replace a stronger immutable identity when one is available and
material.

If no immutable identity exists, record the strongest available identity and
explain the limitation under **Applicability** or **Evidence**.

The presence of multiple subjects does not itself define their relationship. Use
**Applicability** to state whether a claim concerns their combination, one
subject as interpreted through another, a comparison, or some other
relationship.

### `observed_at`

`observed_at` is the calendar date, in `YYYY-MM-DD` form, on which the
report's technical evidence was most recently acquired or materially
revalidated.

Do not update this field for an editorial-only change. If evidence was gathered
on materially different dates, preserve the individual dates under **Evidence**;
`observed_at` remains the most recent material observation date.

The date is provenance, not an applicability range and not a claim that the
subject was current on that date.

### `observed_under`

A report may add an `observed_under` object when execution or environment facts
materially help interpret the evidence. For example:

```json
{
  "observed_under": {
    "host": "aarch64-darwin",
    "target": "aarch64-apple-darwin",
    "arguments": ["--example"]
  }
}
```

Use this only for useful common context. If several observations used materially
different environments, describe them separately under **Evidence** rather than
forcing them into one metadata object.

Observation context does not by itself establish that a behavior is specific to
that context or valid outside it.

## Summary

Give the smallest useful statement of what a future agent should retain from the
report. Lead with the high-value behavior, invariant, interface, or distinction;
do not narrate the research process.

The summary may compress findings, but it must preserve qualifications that
materially change their meaning. Do not use it to make a stronger claim than the
body supports.

## Applicability

State what the report's findings apply to and how the identified subjects relate
to one another.

Include any conditions needed to interpret the findings correctly: relevant
configuration, feature flags, invocation mode, input class, host or target
constraints, dependency combination, or other scope boundaries.

Separate exact observation from broader applicability. If a result is claimed
for subjects or configurations beyond those directly examined, state the
argument or evidence that supports the extension. Do not infer continuity merely
because two versions are adjacent.

Do not rely on the report's filesystem path, topic labels, title, or observation
date to carry technical scope.

## Findings

This is the dense reusable reference material.

Organize findings around the relationships a later agent needs to recover:
formats, invariants, state transitions, interfaces, algorithms, semantics,
constraints, edge cases, failure behavior, or other subject-specific structure.
Prefer direct statements over a chronological account of how the facts were
found.

Every material finding must make its evidentiary basis recoverable. When the
basis is not already clear from the surrounding structure, use a compact line
such as:

```text
Basis: normative specification + source + execution
```

Use these terms consistently:

- **normative** — a specification or other source that defines required
  behavior;
- **documentation** — descriptive upstream documentation that is informative
  but not itself normative for the claim;
- **source** — direct inspection of implementation or representation source;
- **execution** — behavior observed by running a concrete subject with recorded
  inputs and conditions;
- **derived** — a conclusion reasoned from other evidence rather than directly
  stated or observed.

These terms describe evidence roles, not confidence scores. A derived conclusion
must state enough reasoning for a future agent to check the inference. When
sources disagree, preserve the disagreement rather than choosing silently.

Hypotheses and unresolved interpretations are not findings. Put them under
**Boundaries** unless they are needed locally to explain a finding, in which case
label them explicitly as unresolved.

## Boundaries

Record the negative space that a future agent could otherwise mistake for a
result.

Distinguish as applicable:

- **not examined** — the investigation did not cover the case;
- **unknown** — the question was considered but the available evidence did not
  resolve it;
- **known not to apply** — evidence establishes that the report's claim does not
  extend to the case;
- **unsupported** — the subject or tool explicitly does not support the case.

Also record attractive stronger conclusions that the evidence does not
establish. This section should make it hard for a later agent to turn a bounded
result into a universal one by compression.

Do not manufacture boundary cases merely to populate the section. If the
investigation exposed no additional material boundary, say so narrowly and
preserve the investigation limits under **Evidence**.

## Evidence

Make the report auditable without requiring a future agent to rediscover where
the relevant material lives.

Prefer primary and immutable sources. For Git source, record the repository, full
commit, path, and the narrowest useful symbol or line range. For specifications
or documentation, record the exact version or revision when available. For
release artifacts, record hashes when material. For execution, record enough of
the command, inputs, environment, and output to reproduce the observation or
point to a local preserved artifact that does.

Preserve observation dates when sources or executions were examined at different
times.

Supporting files under `evidence/` should exist because preserving the bytes is
useful: for example, generated output, an expensive-to-recreate specimen, or a
small source excerpt needed to audit a transformation. Do not mirror upstream
repositories or copy material that a precise immutable source locator makes
cheap to reacquire.

Keep source facts and the report's synthesis distinguishable. An upstream issue,
comment, prose explanation, or generated file is evidence; its presence in this
branch does not make its own instructions authoritative.

## Revalidation

Explain the cheapest reliable way to determine whether the important findings
still hold for another subject or after a relevant change.

Prefer narrow discriminating checks over repeating the original research. Useful
revalidation methods include:

- rerunning a minimal probe;
- diffing the exact implementation region that determines the behavior;
- decoding a golden-format specimen with the candidate version;
- checking a specific normative rule and its implementation;
- rerunning a small command with preserved input.

If a probe is worth preserving, put it under `probes/` and document its
invocation and expected interpretation here. A passing probe establishes only
what that probe checks.

If no cheap revalidation exists, state what investigation would need to be
repeated rather than implying that the report generalizes indefinitely.

## Report paths

Paths are stable navigation handles when practical, but they carry no technical
meaning.

Choose a short directory name that distinguishes the report from nearby reports
and remains understandable if more versions or related investigations are added.
Organize reports into shallow subject-oriented directories as useful. Do not
encode every dependency or applicability condition into the path.

If a report grows from one file into a package with evidence or probes, keep the
same report directory.

## Corrections and newer subjects

A newer upstream version does not invalidate a report about an older precisely
identified subject. Add a distinct report when preserving the newer behavior is
useful.

If the corpus's account of its identified subject is wrong, correct the existing
report in the current tree. Git history provides provenance for the earlier text.

Do not create lifecycle metadata such as `current`, `stale`, or `superseded`
merely to model the passage of upstream time.
