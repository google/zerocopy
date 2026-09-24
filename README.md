# Technical reference corpus

This orphan branch preserves precise technical knowledge that would otherwise be
expensive to recover through source crawls, experiments, or synthesis. The corpus
is general-purpose and may cover Lean, Rust, Charon, Aeneas, Anneal, zerocopy, or
other systems.

## Start here

Agents must read [`AGENTS.md`](AGENTS.md) before using or changing the corpus. It
defines branch authority, maintenance, validation, and publication.

Before authoring or revising a report, also read [`FORMAT.md`](FORMAT.md). It
defines report metadata, evidence roles, applicability, investigation boundaries,
and revalidation expectations.

[`CATALOG.json`](CATALOG.json) is the generated machine-readable report index.
Technical reports themselves live under `reports/`.

Validate the current tree with:

```console
python3 tools/reference.py check
```

After editing reports, regenerate the catalog and validate:

```console
python3 tools/reference.py catalog
python3 tools/reference.py check
```

After changing the validation tool or tests, run:

```console
python3 -m unittest discover -s tests -v
```

The validator and tests use only the Python standard library.
