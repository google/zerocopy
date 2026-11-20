# Support material

Text-only probes and recorded outputs for `../REPORT.md`. Observed 2026-11-20 on an
x86-64 Linux workstation, with Lean 4 v4.35.0 (release build, commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc). All runs were single-threaded.

| File | Purpose | Reproduce |
|---|---|---|
| `ReelabProbe.lean` | Print, re-parse, re-elaborate and compare every `Init` theorem; writes one TSV row per theorem and `#` summary lines | `lean --run ReelabProbe.lean Init 0 <mode> > out_<mode>.tsv`, where `<mode>` is `default`, `proofs`, `targeted` or `explicit`; a non-zero second argument limits the count |
| `summarize.py` | Status counts, the status × text-round-trip table, timing quantiles and coarse first-difference classes | `python3 summarize.py out_default.tsv out_proofs.tsv out_targeted.tsv out_explicit.tsv` |
| `classify_differ.py` | The finer classification of `differ` and `defeq` rows used in the report's change-class table | `python3 classify_differ.py out_default.tsv` |
| `summary_all_modes.txt`, `classify_all_modes.txt` | Outputs of the two scripts for the four modes | |
| `resource_usage.txt` | GNU `time -v` elapsed time, user time and peak RSS per mode | `/usr/bin/time -v lean --run ...` |
| `differ_rows_default_mode.tsv` | All 474 `differ` rows from the default mode, with `detail` truncated to 600 characters | |
| `SpotCheck.lean`, `SpotCheck.out.txt` | `UInt64.neg_one_eq` and `Int.one_ne_zero` rendered with and without `pp.numericTypes`, and the `Int` reading shown false | `lean SpotCheck.lean` |
| `DefEqStage.lean`, `DefEqStage.out.txt` | The definitional-equality input shape used by the BEq reference implementation, a bidirectional `exact` proof, and `sorry` severity | `lean DefEqStage.lean`; exits 1 because Case2 is meant to fail |

The `detail` column format is `DIFF[<subterm of re-elaborated type> ~~ <subterm of stored type>] || <printed text> ==> <re-printed text>`.

The full per-theorem TSVs are not kept: default 4,902,113 bytes, proofs 4,536,418, targeted 4,386,928, explicit 3,405,649. Regenerate them with the probe.
