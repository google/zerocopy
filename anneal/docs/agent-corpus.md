<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal agent corpus

This page helps a context-free agent find and ingest the current Anneal
documentation without confusing a worktree container, another checkout, or the
historical V1 prototype for the intended corpus. The
[documentation map](README.md) is the sole owner of reading order and document
authority.

## Establish the Anneal root

Resolve the repository root from the current checkout; never copy an absolute
path from another session. The corpus root is its `anneal/` directory, which
must contain the crate and the documentation entrypoints:

```bash
repo_root="$(git rev-parse --show-toplevel)"
anneal_root="$repo_root/anneal"

test -f "$anneal_root/Cargo.toml"
test -f "$anneal_root/AGENTS.md"
test -f "$anneal_root/README.md"
test -f "$anneal_root/docs/README.md"
test -f "$anneal_root/docs/agent-corpus.md"
```

These structural checks deliberately avoid exact headings, hashes, and byte
counts. Routine documentation edits should not break discovery. If a marker is
missing, stop and locate the correct worktree instead of substituting a
similarly named directory.

## Exclude V1

`anneal/v1/` is the historical prototype and is **not part of the current
corpus**. Do not recursively ingest it, follow its `AGENTS.md` as current
instructions, or use its README to replace a missing current file. Read
selected V1 documentation or source only when current documentation calls for
historical evidence, and treat it as history rather than authority. The
[V1 lessons](history/v1-lessons.md) page is the normal starting point.

An `AGENTS.md` above `anneal/` may still impose repository or worktree
procedures. Those instructions apply to repository operations, but do not
replace Anneal's project and design canon.

## Discover the complete corpus

For a full documentation audit or a context-free comprehension test, read:

- `anneal/AGENTS.md`;
- `anneal/README.md`; and
- every Markdown file under `anneal/docs/`, recursively.

Discover the last category from the filesystem instead of maintaining another
hand-written enumeration:

```bash
find "$anneal_root/docs" -type f -name '*.md' \
  ! -path '*/design/decisions/0000-template.md' -print | sort
```

Follow the order in the [documentation map](README.md). Do not add
`anneal/v1/**/*.md` to the corpus. Source code, issues, pull requests, and
upstream documentation may be necessary evidence for a task, but reading them
alongside the corpus does not give them design authority.

`design/decisions/0000-template.md` is authoring scaffolding rather than a
decision, so it is deliberately excluded from a comprehension corpus.

## Completion check

After reading, a context-free agent should be able to explain, without relying
on V1 or an open pull request:

- Anneal's product goal, intended users, and why soundness is foundational;
- the principles used to compare designs and the constraints every acceptable
  design must satisfy;
- which documents are normative, accepted, open, factual, or historical;
- how an identified Rust subject, a precise claim, checked evidence, and
  classified residual dependencies form a reported result;
- how local proofs compose into a global claim and why the source model must be
  adequate for that argument;
- what the checked-in executable actually implements today; and
- which unresolved choice the current task must not settle silently.

If the corpus does not support one of those answers, report the gap rather than
importing an answer from V1, an issue, or a pull request.
