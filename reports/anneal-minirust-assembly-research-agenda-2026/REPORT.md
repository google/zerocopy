# MiniRust and assembly research agenda and question identities

## Summary

This agenda preserves the52 candidate research bundles tracked in [MiniRust issue3873](https://github.com/google/zerocopy/issues/3873) and [assembly issue3874](https://github.com/google/zerocopy/issues/3874). MR01–MR24 and AS01–AS28 are stable question handles; report grouping is a revisable many-to-many relationship. A report count or topic mention does not establish question coverage, a performed experiment or a production soundness theorem.

The first publication adds three foundation investigations: the RustBelt/RefinedRust/MiniRust bridge, Specr/import/nondeterminism/source-safety boundaries, and representation/copy/provenance laws. They provide primary-source findings, scoped checked fragments and executed controls while retaining the unproved general bridges. Further packages are being researched for memory logic, compiler/static inputs, assembly foundations, Rust ABI, concrete pilots and internal trust.

## Applicability

`questions.json` preserves the exact checklist text and source issue-body SHA256s observed2026-10-14 before progress updates. These are agent-authored research proposals, not normative system specifications. `report-map.json` records the presently published report/question associations with bounded scope; it is navigation, not proof of semantic completion.

The earlier364-question research initiative remains at its own final publication9968d4e448f4311a3f4e93b648cc10d2915ef572, with89 reports and an agenda. Its R095/P127/P131 stronger outcomes remain separately unestablished. This new agenda adds questions and does not retroactively claim those outcomes or reopen all prior research.

## Findings

### Provisional grouping

| Research family | Question bundles | Main relationship |
|---|---|---|
| Model/import foundations | MR01–MR05, MR18–MR19 | Concrete safety reflection, semantic import, proof-component reuse |
| Representation and resources | MR06–MR17 | Bytes, layout, provenance, borrows, concurrency and cleanup |
| Coverage and adoption | MR20–MR24 | Evidence, static/open-client boundaries and architecture comparison |
| Assembly/ISA foundations | AS01–AS05, AS17–AS23 | Actual modeled operations, proof closure and bytes/ISA correspondence |
| Rust/assembly interface | AS06–AS16 | Validity, resources, inline contracts, ABI, equivalence and deployment |
| Trust and extended domains | AS24–AS28 | Checkers, weak memory, security, platform scope and shared pilots |

These families overlap. For example, byte/provenance representation is both a MiniRust question and part of the Rust↔machine entry/return relation. The concrete pilot should consume the foundation and contract reports rather than re-survey every system. An alternative compiler foundation should be evaluated against a missing arrow, not integrated merely because it exists.

### Evidence and completion discipline

Each report retains immutable subject identities, source/paper facts versus deductions, exact theorem direction/domain, actual command outcomes, unsupported or unknown cases, and narrow revalidation. Owned fragment models are labeled as such; they do not become mechanizations of the named upstream system merely by using matching terminology.

A negative result can answer a question. A failed toolchain build is an operational result, not a semantic verdict. An inaccessible artifact remains unknown. A proposed future theorem is not checked proof evidence, and a current-source implementation observation is not a normative Rust guarantee.

The final coverage synthesis will assess every exact MR/AS question against report sections and evidence, distinguish genuine unexamined research from stronger design/implementation goals, and update the tracking issues only after that assessment. Crosswalk/metadata validation supplements rather than replaces full prose and semantic review.

## Boundaries

This publication is a progress snapshot. It does not complete all52 investigations, freeze the grouping, adopt an Anneal architecture or establish an end-to-end unsafe Rust/assembly theorem. Experimental and proof scopes remain in each report's own applicability and boundaries.

## Evidence

- `questions.json`:24 MR and28 AS original checklist entries, exact source issue-body digests, titles and public URLs.
- `report-map.json`: first published foundation reports and the bundles they address.
- The reports' own source-evidence, executed probes, proof statements, logs and scoped coverage files.

## Revalidation

Reconcile future issue edits against the preserved text before changing question identities. Regroup by updating the map while retaining exact questions and section-level scope. Validate a complete candidate using its own reference validator, then verify the published Git tree and issue readbacks. Navigation-only completeness must never authorize blanket checkbox completion.

*Authored by an AI agent acting on joshlf's behalf.*
