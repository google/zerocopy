# Frozen Randomization Specification

`prepare.py` is the executable specification. It uses six independently
generated 256-bit seeds, stored under evaluator-only `sealed/seeds.json`, and
domain-separated SHA-256 hash sorting. No language PRNG or iteration-order
behavior determines an order.

For tag `T`, seed `S`, and canonical UTF-8 value `V`, the sort key is:

```text
SHA256(T || NUL || bytes_from_hex(S) || NUL || V)
```

The canonical tuple breaks the cryptographically negligible event of a key
collision.

The procedure is:

1. Hash-sort real condition roles and assign opaque labels `c0` and `c1`.
2. Hash-sort mode names and assign opaque target labels `m0` through `m4`.
3. Treat each replicate as a balanced wave containing all five modes and both
   conditions. Hash-sort the five waves, then the ten cells within each
   wave. Assign sequential operational run IDs only after sorting.
4. Derive each neutral 128-bit runtime cell ID from a separately tagged hash of
   its canonical `(mode, role, replicate)` tuple. Assert all 50 are unique.
5. Independently hash-sort each mode's ten run IDs and assign blind labels A–J.
6. Independently hash-sort A–J for each scorer's presentation order.
7. Independently hash-sort the ten scorer claims for the scoring launch
   order.
8. Independently hash-sort the five mode claims for the consistency-review
   launch order.

The sealed maps are frozen before collection but never enter a report-agent or
blind-scorer packet. Because the shared repository and host are not hardened
against deliberate out-of-scope reads, secrecy is procedural. Commitments are
recorded in `commitments.json`; the seed and generated-map bytes are covered by
the freeze lock.

Collection processes one complete balanced wave before the next. Within a
wave, starts follow `launch-schedule.tsv`; up to three report agents may be
active concurrently. A later service limitation may reduce concurrency but may
not reorder starts or cross the wave barrier. Every actual start/completion is
recorded in the append-only event ledger.
