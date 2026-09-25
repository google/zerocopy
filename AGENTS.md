# Reference branch agent guide

This orphan branch is a self-contained technical reference corpus. Its purpose is
to preserve expensive-to-recover technical knowledge so future agents can reuse
precise results without repeating broad source crawls, experiments, or synthesis.
The corpus is general-purpose and is not limited to Anneal or zerocopy.

## Authority

The current tip of `refs/heads/reference` is the canonical corpus state. Git
history preserves provenance; historical trees are not competing current
documentation.

This branch is authoritative about its own organization, interpretation, and
maintenance. It is not authoritative about the systems it documents. Upstream
source code, specifications, release artifacts, and other primary sources retain
their own authority.

All documentation needed to interpret or maintain the corpus must live on this
branch. Files elsewhere may point here, but must not be required to determine
what the corpus means or how it is maintained.

`AGENTS.md` governs branch-wide behavior. `FORMAT.md` governs report semantics and
format. `tools/reference.py` mechanically enforces only a subset of those written
contracts. If the tool rejects something the written contract permits, or accepts
something it forbids, treat that as a tooling defect rather than inferring a new
corpus rule from the implementation.

Do not merge, rebase, or otherwise graft another branch's history into
`reference`. Copy particular material when justified, preserving its provenance,
rather than joining histories.

This repository is public. Do not commit credentials, private data, proprietary
material, or unnecessary large source mirrors.

## Reports

Each immediate child directory of `reports/` is one report package. A package
contains `REPORT.json`, `REPORT.md`, and any additional report-owned files or
directories. Package contents are otherwise ordinary files: names such as
`evidence/`, `probes/`, `fixtures/`, or `scripts/` are conventions, not special
corpus object types. Symlinks are not allowed anywhere under `reports/`.

Before writing or revising a report, read `FORMAT.md`. Reports must identify the
subjects actually examined, bound claims to the evidence supporting them, and
preserve important investigation limits. Package paths are navigation handles and
do not carry technical applicability semantics.

When upstream software changes, an older report remains a report about the subject
it identifies. Add another report when preserving the newer behavior is useful.
When the corpus's account of its identified subject is wrong, correct the current
report; Git history preserves the earlier text as provenance.

Prefer reports that avoid future research cost: results that required substantial
synthesis, are easy to misunderstand, control later engineering decisions, depend
on fragmented sources, are expensive to reproduce, or admit a cheap probe that
can replace future rediscovery.

## Generated state and validation

`CATALOG.json` is generated from report package names and `REPORT.json` metadata.
It is navigation only. Do not edit it manually or treat it as independent
technical evidence.

Before publication, run:

```console
python3 tools/reference.py check
```

After changing reports, regenerate the catalog first:

```console
python3 tools/reference.py catalog
python3 tools/reference.py check
```

When changing `tools/reference.py` or its tests, also run:

```console
python3 -m unittest discover -s tests -v
```

The validator and its tests use only the Python standard library. The validator
checks machine-representable corpus invariants; passing it does not establish that
a report's prose or technical claims satisfy `FORMAT.md`.

## Publication

Direct publication to `reference` is the normal workflow; a pull request is not
required unless the user explicitly requests one.

Treat publication as an atomic transition between coherent corpus trees:

1. Read the current remote `reference` tip before writing.
2. Construct the complete candidate from that tip.
3. Regenerate derived state and run the applicable validation.
4. Publish commits descending from the observed tip.
5. Advance `refs/heads/reference` only by fast-forward to the validated candidate.
6. If another writer advanced the branch, fetch the new tip, reconcile the
   candidate, validate again, and retry.
7. Read back the resulting remote state and verify the intended change.

For a multi-file change, do not publish files one at a time to the canonical ref.
Create the complete candidate tree or commit first, then move the branch ref once.
A sequential per-file API is unsuitable when it exposes intermediate trees.

Do not force-push, rewrite published history, or delete the branch during normal
operation. Keep commits coherent, but readers should not need to replay history
to understand the current tree.

Do not add GitHub Actions or make routine corpus publication depend on repository
CI without explicit user direction. The intended maintenance path is lightweight,
deterministic local validation followed by direct fast-forward publication.
