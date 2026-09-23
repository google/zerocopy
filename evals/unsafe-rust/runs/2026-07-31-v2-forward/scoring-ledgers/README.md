# Blind-scoring orchestration reconciliation

The three shard ledgers in this directory are byte-for-byte copies of the
temporary orchestration ledgers. They record each orchestrator's local view at
the time it stopped; statuses such as `owned_by_other_orchestrator` and the
Shard 3 count of 19 present scores are therefore intermediate ownership
snapshots, not final missing-data findings.

## Shard contributions

| Ledger | Valid scores produced by that orchestrator | Ledger SHA-256 |
|---|---|---|
| [`shard-1.tsv`](shard-1.tsv) | P-s2, H-s1 | `bc6840381dcdc6a7228f4142d7e31fc41724f24061d4914f1db8b233426f6c0e` |
| [`shard-2.md`](shard-2.md) | C-s1, V-s1, U-s2, D-s1, U-s1, P-s1 | `760225868e5a36380c634802055065da4541de136718aad33d2dbe18f992c4f0` |
| [`shard-3.jsonl`](shard-3.jsonl) | C-s2, D-s2, H-s2, I-s2, A-s1, T-s1 | `9b3d78629dd5e76180f8904137b386eca23a5bae79d29e428efe237e715ad2ca` |

All fourteen score digests and word counts recorded by these ledgers match the
corresponding files in [`../blind-scores/raw/`](../blind-scores/raw/). The
remaining six schedule tasks—N-s1, I-s1, A-s2, V-s2, N-s2, and T-s2—were
atomically owned elsewhere and are also present in that final archive.

## T-s2 chronology

Shard 3 completed while T-s2 was owned by another orchestrator and before its
output existed, producing its accurate intermediate count of 19. The first
T-s2 attempt later consulted a Rust release-blog page outside the frozen
allowed-source set. It was excluded and preserved as
[`../blind-scores/invalid/T-s2-attempt-1.md`](../blind-scores/invalid/T-s2-attempt-1.md).
A fresh retry produced the valid
[`../blind-scores/raw/T-s2.md`](../blind-scores/raw/T-s2.md). The invalid and
valid score SHA-256 values are respectively
`47fdd0495848b4d4a2c5447673819fee629eb2482e39328a014d5a06edd0adab`
and `ed792bc0b5c714992401b342396dd24b89fade7cb112684fd9c991f40284937f`.

After that retry, all 20 runtime valid-score files were compared byte-for-byte
with the 20 archived raw scores and matched. The shard reports therefore add
operational provenance but change no score, adjudication, aggregate, or gate.
