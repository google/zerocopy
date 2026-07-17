<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal V2 agent corpus

This page defines how a context-free agent should locate and ingest the Anneal
V2 documentation. Its purpose is to prevent a worktree mix-up, partial read, or
accidental substitution of the historical V1 corpus. It is a reading manifest,
not a source of new design authority; the authority of each document is defined
by the [documentation taxonomy](README.md#document-classes).

## Establish the V2 root

The canonical corpus root is the `anneal/` directory in the current zerocopy
worktree: the directory containing all of the following markers:

- `Cargo.toml` for the V2 crate;
- `AGENTS.md` whose first Markdown heading is `# Anneal V2 agent guide`;
- `README.md` whose first Markdown heading is `# Anneal V2`; and
- `docs/README.md` whose first Markdown heading is
  `# Anneal V2 documentation`.

Resolve that directory from the current worktree rather than copying an
absolute path from another session. Before relying on the corpus, check all
four markers. A missing or different heading is a failed preflight, not
permission to substitute a similarly named directory.

For example, from anywhere inside the zerocopy worktree:

```bash
repo_root="$(git rev-parse --show-toplevel)"
v2_root="$repo_root/anneal"

test -f "$v2_root/Cargo.toml"
test "$(sed -n '/^# /{p;q;}' "$v2_root/AGENTS.md")" = \
  '# Anneal V2 agent guide'
test "$(sed -n '/^# /{p;q;}' "$v2_root/README.md")" = '# Anneal V2'
test "$(sed -n '/^# /{p;q;}' "$v2_root/docs/README.md")" = \
  '# Anneal V2 documentation'
```

These semantic markers deliberately replace file hashes or an exact byte
count. Normal documentation edits should not require updating an unrelated
digest, while a reader should still detect the common failure modes of opening
the worktree container, the repository root, or V1 instead of V2.

## Exclude V1

`anneal/v1/` is the historical prototype and is **not part of the V2 corpus**.
Do not recursively ingest it, follow its `AGENTS.md` as V2 instructions, or use
its README to fill a missing V2 file. Read selected V1 documentation or source
only when the V2 guide explicitly calls for historical evidence. In that case,
classify what you learn as history rather than V2 authority; see
[Lessons from Anneal V1](history/v1-lessons.md).

The `AGENTS.md` above `anneal/` may impose repository or worktree procedures.
Those instructions still apply to operations in the repository, but they are
not a substitute for Anneal V2's project and design canon.

## Minimum required reading

Before making or reviewing a V2 design change, read these files completely, in
order:

1. [`AGENTS.md`](../AGENTS.md), for the mission, judgment rules, and working
   protocol.
2. [Documentation map](README.md) and [glossary](glossary.md), for document
   authority, conflict handling, and stable vocabulary.
3. [Design principles](design/principles.md), for the project's value
   function.
4. [Settled requirements](design/settled-requirements.md), for constraints an
   acceptable design must satisfy.
5. The [accepted-decision index](design/decisions/README.md) and every accepted
   decision relevant to the change.
6. [Verification model](design/verification-model.md),
   [verification subject and result identity](design/verification-artifact.md),
   and
   [trust model](design/trust-model.md), for the claims Anneal intends to make
   and their conditions.
7. The [worked example](design/worked-example.md), as a schematic application
   whose concrete choices are illustrative rather than decided.
8. [Open-question index](design/open-questions/README.md) and every open-question
   page relevant to the task. Candidate approaches are not decisions.
9. [Current architecture](reference/current-architecture.md),
   [current limitations](reference/current-limitations.md), and non-normative
   [current priorities](reference/current-priorities.md), for what exists in
   the checked-in tree and the present engineering frontier rather than plans
   or open pull requests.

Also read [Aeneas and Charon](reference/aeneas-and-charon.md) for translation,
semantics, or proof-infrastructure work, and read
[V1 lessons](history/v1-lessons.md) before borrowing from V1. A task may require
additional source, upstream documentation, decision records, or history; this
list is a minimum, not a claim that those sources are irrelevant.

## Exhaustive V2 documentation corpus

For a context-free comprehension test or a full documentation audit, ingest:

- `anneal/AGENTS.md`;
- `anneal/README.md`; and
- every Markdown file under `anneal/docs/`, recursively.

Discover the final category from the filesystem rather than maintaining a
second hand-written enumeration here. This automatically includes accepted
decision records, new open questions, references, history, and this ingestion
guide as they are added:

```bash
find "$v2_root/docs" -type f -name '*.md' -print | sort
```

Do not add `anneal/v1/**/*.md` to that command. Source code, issues, pull
requests, and upstream Aeneas or Charon documentation may be necessary evidence
for a particular task, but they are not members of the V2 documentation corpus
and do not acquire authority by being read alongside it.

## Completion check

After reading, a context-free agent should be able to state, without relying on
V1 or an open pull request:

- Anneal's mission and why soundness is special;
- the difference between principles, settled requirements, accepted decisions,
  open questions, current-state references, and history;
- the intended local-to-global verification argument and its unresolved
  source-model adequacy problem;
- the difference between the Rust compilation subject and the identity of the
  verification evidence and claim;
- why simple functional reasoning and resource-sensitive reasoning are both
  required;
- what the checked-in V2 executable actually implements today; and
- which proposed choice it must not silently ratify while completing its task.

If the documents do not support one of those answers, report the gap rather
than importing an answer from V1, an issue, or a PR.
