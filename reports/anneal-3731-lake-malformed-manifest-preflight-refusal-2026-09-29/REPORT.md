# Malformed Lake manifest probe refused at the resource gate

## Decision

The selected follow-up cell was **not run**. At the 2026-09-29 20:12:58 EDT preflight, the required estimated free-memory fraction was 25.09%, below the 30% minimum. No Lake or Lean command, fixture mutation, batch control, or live first-goal request was started. This report adds **no Lake behavior evidence** and changes no #3731 I092 or #3730 F07/F08 checklist status.

## Intended bounded cell

The published [fresh-cache consumer matrix](../anneal-3731-lake-fresh-cache-consumer-matrix-2026-09-29/REPORT.md) already covers intact state and missing producer source, traces, hash sidecars, setup JSON, and compiled configuration in its tiny two-package fixture. The [v30 coverage audit](../anneal-3730-3731-final-coverage-audit-2026-09-29-v30/REPORT.md) still identifies malformed manifests as a missing component control.

The proposed single cell was a fresh, private copy of that prepared fixture. Its only intended mutation was to replace the consumer's `lake-manifest.json` contents with invalid JSON (`{\n`), leaving the producer, source, compiled artifacts, and seeded cache intact. A bounded `lake --no-build --no-cache serve` first-goal request and a matched no-build batch control would have been run sequentially, offline, each with a 30-second timeout. Producer and cache inventories would have been captured before and after, with write visibility limited to net file bytes in those trees. None of these steps occurred.

The fixture uses `lake-manifest.json`; there is no generated `lean-manifest.json` in the published fixture. This spelling is material to the planned mutation.

## Refusal evidence

The local `vm_stat` reported 16,384-byte pages: 6,125 free, 120,024 inactive, 4,199 speculative, and 1,185 purgeable. Their sum is 131,533 pages, or 2,155,036,672 bytes. `sysctl -n hw.memsize` reported 8,589,934,592 bytes, yielding 25.09% under the published probe's free-memory estimate. `df -g .` reported 42 GiB available, above the 10 GiB disk gate. A process listing matched no running `lake`, `lean`, or `probe.py` process. Process-tree RSS for a new probe was inapplicable because none was launched. The measured values and command outputs are retained in [support/preflight.json](support/preflight.json).

The existing pinned Lake executable was identified by SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; no Lake invocation was made. The intended original fixture script has SHA-256 `0b5dc8abace2ac483cf64f7cf783ce3bc878eabcf7b142c8d2c8b4e6b9e5d491`.

## Limits and revalidation

There are no before/after producer or cache inventories, Lake outputs, diagnostics, first goal, or write observations for this proposed cell. The resource gate prevented fixture creation. The planned malformed input alone says nothing about Lake's actual response. A later run would require a fresh >=30% memory reading, >=10 GiB disk, process-tree RSS <=2.5 GiB, a 30-second timeout for each Lake phase, no network/dependency setup, and strictly one Lake process at a time. A file inventory would not establish absence of transient or external writes.

Run `python3 support/check.py` to validate the retained refusal evidence; it does not start Lake.
