# Technical reference corpus

This orphan branch preserves precise technical knowledge that would otherwise be
expensive to recover through source crawls, experiments, or synthesis. The corpus
is general-purpose and may cover Lean, Rust, Charon, Aeneas, Anneal, zerocopy, or
other systems.

## Start here

Read [`AGENTS.md`](AGENTS.md) before using or changing the corpus. It defines
branch authority, candidate-tree validation, maintenance, and publication.

Before authoring or revising a report, also read [`FORMAT.md`](FORMAT.md). It
defines report package structure, metadata, evidence roles, applicability,
investigation boundaries, and revalidation expectations.

[`CATALOG.json`](CATALOG.json) is the generated machine-readable report index.
Each immediate child directory of `reports/` is one report package containing
`REPORT.json`, `REPORT.md`, and optional report-owned support material.

Validate an exact candidate tree with Python 3.10 or newer:

```console
python3 tools/reference.py check
```

After changing a package name or `REPORT.json`, regenerate the catalog first:

```console
python3 tools/reference.py catalog
python3 tools/reference.py check
```

After changing the validation tool or tests, run:

```console
python3 -m unittest discover -s tests -v
```

The validator and tests otherwise use only the Python standard library.
