# Staggered Charon writers and reads at one LLBC path

## Scope and controls

This is a bounded follow-up to the [single concurrent Charon pair](../anneal-3731-i076-concurrent-shared-destination-2026-09-30/REPORT.md) for [#3731](https://github.com/google/zerocopy/issues/3731) **I020/I076**, with [#3730](https://github.com/google/zerocopy/issues/3730) **D07** as context. The previous pair inspected the shared LLBC only after both Charon processes settled. Here a read-only poller also sampled it during two differently staggered pairs. The fixture source SHA-256 `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d`, pinned tool hashes, and separate release/cfg control LLBC hashes match the prior packages exactly. The controls distinguish release selected U32 literals `11/23` from debug `--cfg probe_alt` literals `7/29`.

For each pair, the destination was initially absent, each writer had a different private `CARGO_TARGET_DIR`, both used offline one-job Charon `--preset aeneas --lib`, and the second process launched about 35–41 ms after the first. The poller repeatedly opened the same destination twice, retaining existence/read-error status, both lengths and SHA-256s, inode values, timestamps and exact bytes for each distinct observed hash. A matching double read is one sampled equality, not proof of an atomic write. [results.json](results.json), [raw/](raw/), [artifacts/](artifacts/) and [work/](work/) retain the record; [check.py](check.py) validates the raw evidence without rerunning Charon.

## Observed results

| Launch order | Both exits | Reader observations | Final shared LLBC |
| --- | --- | --- | --- |
| release, then cfg | 0, 0 | 370 absent/disappeared; four identical 5,520-byte reads | SHA-256 `a3142ee67648b21c8b1703c3ee135bdff03d97116ff1413806332c239473b099`; **full JSON parse fails** |
| cfg, then release | 0, 0 | 123 absent/disappeared; 42 reads of two complete byte states | SHA-256 `15757df7f92055ccb8b41b7c7bcc806dd83de8b566f4719ec15f13c4b01d062a`; parseable release model (`11/23`) |

The release-first final file is exactly 5,520 bytes. A JSON decoder consumes a complete 5,518-byte prefix with `has_errors: false` and cfg literals `7/29`, then finds the literal two-byte suffix `e}`. `json.loads` rejects the full file as extra data at byte 5518. Four captured double reads agree with that same malformed final hash. Both Charon commands nevertheless exited 0, and the final output was copied only after both had settled. This establishes a successful-process pair whose shared destination failed a strict LLBC JSON parse in this run; it does **not** identify the filesystem write order or syscall that produced the suffix.

In the cfg-first pair, the poller first captured a complete 5,514-byte cfg model (`7/29`, SHA-256 `4183b22754037b1ccc355d7f498ed09e3aed036740ada3140928f5ef91f48932`), then a complete 5,516-byte release model (`11/23`), whose bytes remained as the final output. Every captured double read in both pairs matched in bytes, length and hash; the first-open inode matched a subsequent path stat. The poller did not record the second open's inode. These are sampled byte states; they do not prove what a hypothetical reader would see at unsampled instants or under another schedule.

The command collection intervals overlap in both pairs. The process-group RSS sampler observed both groups resident simultaneously in all 16 release-first samples and five of seven cfg-first samples. This establishes overlapping process lifetimes at sampled instants; command end timestamps are collection times rather than exact writer exit/write timestamps. The poller was active over the runs, but its timestamps and nearby RSS samples cannot establish that any particular file read coincided with two active write syscalls.

## Resource and applicability limits

Fresh admissions before each pair measured 30.6007% and 31.2572% estimated reclaimable RAM with over 18.6 GB disk free, above the 25%/10 GiB launch thresholds. The lowest sampled reclaimable estimate was 30.3524%; minimum free disk 18,624,823,296 bytes; maximum summed process-group RSS **254,656 KiB**, below the 256 MiB stop threshold; maximum private scratch 128 KiB. Both pairs completed under 15 seconds without a guard abort, but RSS samples can miss shorter peaks. No dependency was installed or downloaded; exact command/environment and binary hashes are retained.

For **I020**, the two distinct compilation subjects again targeted one path and one observed final was malformed despite successful processes. For **I076**, the new direct evidence is the in-run byte sequence and a nonparseable final shared output; producer ownership, atomic publication and collision rejection remain unimplemented in this direct Charon call. D07 gains bounded component context, with its product-level residual unchanged. No Anneal V2 publisher, generated proof consumer, read-only archive, cross-platform filesystem or repeated statistical schedule sweep was exercised. Neither two successful exits nor a pair of equal reads is an artifact-validity guarantee in the observed release-first cell.

Run `python3 -B check.py` from this package to reconstruct the exact byte classifications, selected literals, command controls, overlap samples and resource limits. `probe.py` is the acquisition runner and should be launched only with fresh resource admission in a fresh package path.
