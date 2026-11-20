# Support material

Text-only probes and their recorded outputs for the parent `REPORT.md`.
Paths in recorded outputs are rewritten as `$WORK` (probe working directory),
`$RTG_DIR` (unzipped `rtg-tools-3.13-linux-x64.zip`), `$VT` (vt binary built
by `scripts/build_vt.sh`) and `$OUT` (build directory).

| Path | What it is |
| --- | --- |
| `scripts/repr_probe.py` | Builds a 921-bp synthetic reference and truth/query VCFs that encode identical haplotypes in different VCF representations; compares them with a toy exact-record matcher, with RTG Tools vcfeval (default, `--squash-ploidy`, `--output-mode ga4gh`), and after `vt normalize`. |
| `repr_probe/*.vcf`, `ref.fa`, `conf.bed` | Exact probe inputs (the evaluation-region BED excludes case J). |
| `repr_probe/*.summary.txt` | vcfeval `summary.txt` for each mode. |
| `repr_probe/*.output.vcf` | vcfeval GA4GH intermediate VCF (decompressed), with per-record `BD`/`BK`/`BI`. |
| `repr_probe/results.json` | All per-run exit codes, wall times, peak RSS, toy-matcher counts and vt output records. |
| `scripts/complexity_probe.py`, `complexity/complexity_results.json` | vcfeval with the path cap lowered through `--XXcom.rtg.vcf.eval.max-paths=N` on 10-vs-10 equivalent heterozygous deletions in an 80-bp poly-A run. |
| `scripts/complexity_sweep.py`, `complexity/sweep_results.json` | Default-cap vcfeval on k-vs-k equivalent heterozygous deletions in a 200-bp poly-A run, k = 4..32. |
| `scripts/acmg_probe.py`, `acmg/acmg_out.json` | Four ACMG/AMP combination formalisations over a bounded box of criterion counts; InterVar's `classfy` is extracted from the pinned `Intervar.py` and executed. |
| `scripts/acmg_breakdown.py`, `acmg/acmg_breakdown.txt` | Category-transition counts between the Table-5 re-encoding and the 2020 point system. |
| `scripts/build_vt.sh`, `build/build_vt_timing.txt` | From-source vt build recipe at the pinned revision and its measured cost. |

Reproduce (Linux x86-64, Python 3.10+, `curl`, `gcc`, `autoconf`):

```bash
bash scripts/build_vt.sh /tmp/vtbuild            # prints vt path
curl -sSLO https://github.com/RealTimeGenomics/rtg-tools/releases/download/3.13/rtg-tools-3.13-linux-x64.zip
sha256sum rtg-tools-3.13-linux-x64.zip           # b00b6c80bad520f446b1ee2a5070aced45496fd4771bb31f3c63dfa128215d26
unzip -q rtg-tools-3.13-linux-x64.zip
python3 scripts/repr_probe.py --rtg-dir rtg-tools-3.13 --vt /tmp/vtbuild/vt-*/vt --work /tmp/repr
python3 scripts/complexity_probe.py --rtg-dir rtg-tools-3.13 --work /tmp/cx
python3 scripts/complexity_sweep.py --rtg-dir rtg-tools-3.13 --work /tmp/sweep
curl -sSLO https://raw.githubusercontent.com/WGLab/InterVar/4801682d37982bb3e99b50392790878a568b42cd/Intervar.py
python3 scripts/acmg_probe.py Intervar.py
```

The probes invoke `RTG.jar` directly with `-Dtalkback=false -Dusage=false` so
no crash-report or usage telemetry is attempted. vcfeval writes a log containing
host and user details; those logs are intentionally not preserved here.
