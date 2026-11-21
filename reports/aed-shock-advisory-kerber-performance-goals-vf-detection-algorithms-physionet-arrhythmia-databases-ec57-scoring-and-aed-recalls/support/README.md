# Support material

Probes and their recorded outputs for `REPORT.md`. All inputs are synthetic or
are published numbers; no ECG signal data and no device were used. Observed
2026-11-21 on an x86-64 Linux VM (Intel Xeon @ 2.60 GHz, 96 logical CPUs),
GCC 15.2.0, Python 3.13.15, numpy 2.3.5.

| File | Kind | What it shows |
| --- | --- | --- |
| `build_wfdb.sh`, `build_wfdb.out.txt` | build | builds WFDB 10.7.0 (`bemoody/wfdb@de6b1d3981d69060e6a4d1b4e86375fb0d3ed2d1`) library plus `bxb`, `epicmp`, `wrann`, `rdann`, `sumstats` with `-std=gnu89`; build times and binary sizes |
| `make_annotations.py` | input generator | synthetic WFDB headers (zero signals, 360 Hz) and rdann-style text annotations for records `win`, `vfx`, `lrn`, `agA`, `agB`, `epi` |
| `annotation_scoring_probe.sh`, `annotation_scoring_probe.out.txt` | execution of real upstream tools | `bxb` match window and inclusivity, reference-VF exclusion, learning period, `sumstats` gross vs average, `epicmp` VF episode overlap rule |
| `comparitor_probe.py`, `comparitor_probe.out.txt` | execution of unmodified upstream file | wfdb-python `evaluate.py` (`MIT-LCP/wfdb-python@cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e`) strict `<` window; per-record mean vs pooled |
| `make_big_record.py`, `timing_probe.sh`, `timing_probe.out.txt` | execution / timing | 110,000-beat synthetic record: `bxb` vs `Comparitor` agreement, wall time, peak RSS |
| `kerber_lcl.py`, `kerber_lcl.out.txt` | statistical recomputation | which interval constructions reproduce the published one-sided 90% LCLs |
| `interval_label_check.py`, `interval_label_check.out.txt` | statistical recomputation | whether Ruiz de Gauna et al. 2014 Table 1 intervals are Wald intervals as captioned |
| `tci_toy.py`, `tci_toy.out.txt` | toy model (Python port) | behavior of the TCI formula from `FelipeURJC/ohca-vs-public-dbs@4d799e936fea095db4aba3d08bfdc0aabffc29be` `calculate_TCI.m` on sinusoids and pulse trains |

Reproduce (paths are examples):

```sh
WORK=/tmp/aed-probe sh build_wfdb.sh
WFDB_BIN=/tmp/aed-probe/wfdb-10.7.0/app WORK=/tmp/aed-probe/run sh annotation_scoring_probe.sh
curl -sSfL https://raw.githubusercontent.com/MIT-LCP/wfdb-python/cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e/src/wfdb/processing/evaluate.py -o /tmp/aed-probe/evaluate.py
python3 comparitor_probe.py /tmp/aed-probe/evaluate.py /tmp/aed-probe/run/beats.json
WFDB_BIN=/tmp/aed-probe/wfdb-10.7.0/app EVALUATE_PY=/tmp/aed-probe/evaluate.py WORK=/tmp/aed-probe/big sh timing_probe.sh
python3 kerber_lcl.py; python3 interval_label_check.py; python3 tci_toy.py
```
