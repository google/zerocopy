# Bounded final coverage audit for Anneal issues #3730 and #3731

## Summary

This audit reconciles all 159 unique #3731 investigations (I001–I159) and all 174 #3730 suggestions against the research corpus available at **2026-09-29 08:18 UTC**. It includes 15 completed report packages created after the interim audit. A manifest records all 470 files in those packages (19,969,913 bytes), their hashes, format checks and each package's validator result. The report methods, findings and boundaries were read for scope judgments; the manifest is not a claim that every raw transcript line was independently reinterpreted.

The 159-row disposition is **1 complete, 145 partial, 10 not run and 3 conditional**. The 174-suggestion crosswalk is **2 complete, 135 partial, 33 not run and 4 conditional**. “Complete” is a narrow item-level claim: I046 is the requested direct Lean partial-file elaboration fixture at the pinned version; #3730 C13 maps to it. #3730 N11 is complete only for falsifying the Lean-level “no goals means success” claim. Neither establishes full Rust-to-proof or Anneal acceptance. The remaining issue agenda is not 100% complete.

## Applicability and method

The issue scope is the preserved #3730 body/closure comment and #3731 body/scope-extension comment identified by SHA-256 in `report.json`. #3730 was closed as a duplicate backlog, not as completed research. The starting item ledger and crosswalk are the interim audit's `support/investigation-gap-matrix.csv` and `support/3730-crosswalk-disposition.csv`; their hashes are in `support/validation.json`. This audit preserves the original item wording, destination mapping and row count.

For each new package, `support/build_audit.py` explicitly records which investigation IDs its actual experiment or source review can inform and the boundary that prevents overclaiming. It validates each package using `tools/reference.py::_load_report`, inventories every file, parses JSON/CSV where applicable and hashes bytes. It then combines that bounded evidence with the interim residual and applies row-specific residual corrections. The 174 crosswalk rows receive suggestion-specific status corrections where a destination's broad partial state would obscure a narrower completed or unexecuted suggestion. This is a research-evidence audit, not an implementation test or issue-checkbox decision.

Status meanings:

- **Complete:** the precisely scoped row or suggestion was executed at its recorded pin, with no remaining method within that scope. Product integration may remain under other IDs.
- **Partial:** at least some relevant experiment or source review exists, but the exact residual in the row is still open.
- **Not run:** no experiment matching the requested distinguishing method was found, even if background reports are relevant.
- **Conditional:** the distinguishing work depends on an explicit toolchain, human participant, or remote-target decision. A component may still have partial evidence.

## New evidence and its limits

The 15 completed packages are listed with their direct observations, exact reviewed IDs, and boundaries in `support/package-review.csv`; `support/file-inventory.csv` lists the inspected files. Their results advance several clusters:

- **Architecture and source identity:** one-shot/project/broker toy topologies, real Charon root-closure scaling and failed partial output, Aeneas one-shot identity/declaration manifests, and byte-accurate projection/CAS controls. These do not select an Anneal topology or prove a real overlay/in-process worker.
- **Lean and Lake:** module-layout approximations, RPC worker/session lifetime, partial-file elaboration, small relocated prepared Lake consumers, and clean/prepared and native-cache controls. The outstanding launch/refresh, imported-artifact-family and actual generated-workspace matrices remain explicit in the ledger.
- **Concurrency and recovery:** synthetic direct filesystem/process crash-stage publication, local two-client broker contracts, guarded resource measurements, and APFS plus cached OrbStack overlayfs rename/open/unlink/flock trials. They do not establish Anneal's scheduler, real MCP transport, or other native filesystems.
- **Acceptance:** a direct Lean negative-control oracle matrix distinguishes goals from trusted acceptance, and a second GPT-6 Sol High worker reproduced a small vertical prototype on the same host. Neither is a human study, blind independent environment, or full Rust model-change vertical slice.

The only completed I-row is **I046**. The direct Lean fixture exercised unfinished proof, unknown tactic, heartbeat timeout and recoverable syntax error, with before/after goal positions, diagnostics and failing batch checks at Lean 4.30.0-rc2. I129 and I137 continue to require product-level status and Rust obligation coverage. C13 inherits the narrow I046 completion; N11 is supported by weak/admitted/axiom/missing-obligation negative controls and remains Lean-level only.

## Remaining executable work

`support/remaining-local-experiments.csv` gives **18 concrete, bounded suites** that can be attempted with the source, runtimes and scratch environment already available. Each row names the exact I IDs, experiment, evidence boundary and resource guard. Its two in-progress lines are **out of this snapshot**: the Lean launch/refresh matrix and Charon warm-target controls began after 08:18 UTC. They must be reviewed as completed packages in a later audit; this report does not pre-credit their results. The other locally feasible work clusters are parser/projection fixtures, direct Lean RPC lifetimes, actual component-process failure and cache controls, guarded resource/soak measures, cross-version acceptance controls and further source/API comparison.

`support/gated-work.csv` separates seven gate groups from local experiments: same-process Aeneas requires an OCaml/Dune/opam or prebuilt API decision; I141 requires humans; I143 remote durability is conditional on measured need; additional filesystem/platform claims require selected targets; and many end-to-end editor/MCP/Anneal rows require an actual implementation. Some runnable editor/precedent comparisons would need additional client installations. The architecture adoption decision is also distinct from source review. The 18 local suites plus these gates cover every non-complete I ID as a planning route, although one row can have both a local component experiment and an integration residual. No new dependency was installed by this audit.

## Boundaries

- The statuses are based on packages completed by 08:18 UTC. Two newer suites were still in progress. Reports published or modified later require a fresh review, not an automatic promotion.
- Component and model results are not claims that the Anneal product implements the contract. The checkout lacks a complete Anneal editor/MCP bridge and generated Rust-to-Lean service.
- The second-worker reproduction is independent in operator script but shared the host, toolchains and prior procedural description. It is not blind or cross-machine reproduction.
- The Linux trial used an existing OrbStack Ubuntu container over overlayfs; it is not native ext4/XFS, Windows or a network filesystem. The host trial used APFS.
- The corpus review is a coverage judgment, not a rerun of all prior probes. Each cited report's own version, fixture and source restrictions govern its technical conclusion.

## Evidence and revalidation

- `support/investigation-final.csv` — exact requested method/scope, prior and new package pointers, bounded evidence, status and residual for I001–I159.
- `support/3730-crosswalk-final.csv` — all 174 source suggestions, destination IDs, suggestion-level status and residual.
- `support/package-review.csv` and `support/file-inventory.csv` — the 15 post-interim packages, direct scope and file inventory.
- `support/remaining-local-experiments.csv` and `support/gated-work.csv` — execution routes and unresolved gates.
- `support/build_audit.py` and `support/validation.json` — deterministic rebuild of the ledgers and audit counts from the interim source and reviewed packages.

Re-run `python3 support/build_audit.py` from this package to reproduce the data files and counts, then validate this package with `python3 -c 'import sys; sys.path.insert(0, "tools"); import reference; from pathlib import Path; p=Path("reports/anneal-3730-3731-final-coverage-audit-2026-09-29"); print(reference._load_report(p)[1])'` at the repository root. A later audit should first compare the issue/comment hashes, inspect every newly completed package's actual methods and boundaries, and update each affected I and #3730 row explicitly.
