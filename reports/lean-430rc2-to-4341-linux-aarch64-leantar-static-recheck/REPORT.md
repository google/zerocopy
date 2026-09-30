# Lean Linux AArch64 bundled leantar: v4.30.0-rc2 to v4.34.1 static recheck

## Summary

The exact frozen inventory row is **R443** at reference parent `71f4f352ccaf10afde6fea5a1f1c459c6a36c19e`. Its [predecessor report](../lean-430-rc2-linux-aarch64-leantar-anomaly/REPORT.md) found an x86-64 `bin/leantar` (`ELF e_machine=62`) in the official Lean `v4.30.0-rc2` `linux_aarch64` archive. In this review, the official Lean **v4.34.1** `linux_aarch64` archive contains an **AArch64** `bin/leantar` (`e_machine=183`). The earlier architecture mismatch is absent in this one newer archive. This is a static artifact finding; neither foreign binary was executed.

The old archive was **not downloaded again**. Its whole-archive digest and helper identity come from the exact frozen R443 report and its [archive identities](support/frozen-archive-identities.json). The new archive was downloaded once, matched the digest in [official v4.34.1 release metadata](support/v4.34.1-release.json), and only its `bin/leantar` member was extracted. The [evidence manifest](support/evidence.json), [frozen inventory row](support/frozen-inventory-row.json), [official tag refs](support/tag-refs.txt), raw transcripts, and [offline checker](support/check_evidence.py) preserve the comparison.

## Scope and procedure

The frozen row title and claim come from the 581-row version inventory at `ebcdcadb63fefd1e6c0f46cb2030270ae3232837`. Its exact predecessor path, `REPORT.json`, and archive-identity JSON were read from reference parent `71f4f352ccaf10afde6fea5a1f1c459c6a36c19e`; their bytes and SHA-256 values are preserved under `support/`. Official `git ls-remote` tag refs identify Lean `v4.30.0-rc2` as `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and `v4.34.1` as `5045d0056413266e57c625dcd7c365b10e377c52`. The release metadata snapshots retain the exact archive URLs, sizes, and published digests.

The [preflight sample](support/preflight.txt) at 2026-09-30 23:22:20 UTC recorded 17 GiB available disk space and 61% system-wide memory free. Metadata lookup followed, then the bounded `curl` download. No second resource sample was taken between metadata lookup and download launch. The compressed asset's published size, **581,946,052 bytes**, was below the 600,000,000-byte curl cap and the roughly 1 GiB scratch budget. The [post-download sample](support/postdownload.txt) at 23:23:45 UTC recorded 16 GiB available and 61% memory free; it does not replace the preflight sample. The compressed archive occupied 561 MiB as reported by `du`. The download command and exit status are in [budget-and-download.txt](support/budget-and-download.txt).

After matching the archive's whole-file SHA-256, a `zstd -dc | tar -tf -` pipeline found `lean-4.34.1-linux_aarch64/bin/leantar` and `bin/lean`; the [member list](support/member-list.txt) is retained. A second `zstd -dc | tar -xOf -` pipeline extracted **only** the exact `bin/leantar` member. Both pipelines used `set -o pipefail`. The [tar member entry](support/member-details.txt), [`file`/hash/ELF transcript](support/helper-inspection.txt), and first [64 ELF header bytes](support/new-bundled-leantar-elf-header.bin) are retained. The 581,946,052-byte compressed archive and the 2,563,160-byte extracted helper are preserved under the conversation Data `raw/` directory, outside the report package; no full Lean tree was unpacked.

## Direct comparison

| Artifact | Official compressed archive | Bundled `bin/leantar` | ELF identity |
| --- | --- | --- | --- |
| Lean `v4.30.0-rc2` `linux_aarch64`, frozen R443 observation | 529,196,053 bytes; SHA-256 `b196f41da23960e842fc0fc04749d1639d44839feafc0414e53cb2db6b16790f` | SHA-256 `89ef0c3bd2c40e727191bcd406ef3dac95e0b9000ac93cb7f8c681031ad486be` | x86-64, `e_machine=62` |
| [Lean `v4.34.1` `linux_aarch64` official asset](https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux_aarch64.tar.zst), inspected here | 581,946,052 bytes; SHA-256 `fdb974c2cdb4627e090d5d4007b913e09d13c4868720fb5594e22808b3de9e37` | 2,563,160 bytes; SHA-256 `5a7aaf4a60170490640a4463d31f12515f8de00aa9b66a124b1716768fbd62bc` | ELF64 little-endian AArch64, `e_machine=183` |

The new helper's tar entry is executable and dated 2026-06-27; those are archive metadata, not an execution result. The old bundled helper was x86-64 despite the AArch64 archive name. The exact newer asset inspected here bundles an AArch64 helper, so that specific packaging anomaly does not persist in the v4.34.1 archive. This does not establish why the old archive was wrong, whether every helper in either archive is native, or whether any installer chooses or replaces this helper differently.

## Boundaries and follow-up

No Lean, Lake, leantar, Nix, compiler, or foreign binary was run or installed. Static ELF architecture and digest checks do not establish functional leantar behavior, cache format compatibility, Archive/Mathlib runtime behavior, or Anneal's product behavior. The v4.30.0-rc2 standalone native `leantar` workaround remains historical context; this review does **not** recommend removing it from the pinned setup. A future upgrade can inspect its selected release artifact and packaging path before revisiting that workaround.

For setup and research prompts, retain a version-paired archive digest and a member-level ELF `e_machine` check for any target architecture. State whether the old side was newly inspected or inherited from frozen evidence, and require actual product validation before changing its tool selection. This review adds no issue or audit crosswalk update.

## Revalidation

Run `python3 support/check_evidence.py` for the frozen report/metadata/header checks. With the preserved conversation Data directory available, run `python3 support/check_evidence.py --raw-dir /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/lean-4341-linux-aarch64-leantar-20260930/raw` to rehash the whole downloaded archive and extracted helper offline. The checker never executes either binary.
