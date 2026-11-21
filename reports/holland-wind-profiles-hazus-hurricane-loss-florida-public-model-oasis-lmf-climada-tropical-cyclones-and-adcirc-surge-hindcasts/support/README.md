# Support material

Text-only probes and recorded outputs cited by `../REPORT.md`. Every upstream file is
fetched at its pinned revision from raw.githubusercontent.com at run time; no upstream
source is stored here.

| File | What it does | Kind |
|---|---|---|
| `climada_profile_probe.py` | Extracts nine CLIMADA wind-profile functions from the pinned source with `ast` and executes the unmodified bodies under numpy with a dict stand-in for xarray; checks `holland_toy.py` against them; times `_stat_holland_1980`. | execution of upstream function bodies |
| `holland_toy.py` | Hand transliterations of the CLIMADA, ADCIRC (NWS=8, NWS=19 rescale) and GeoClaw (holland80, holland2008) recipes for one reference storm; B-clamp, air-density and drag-elasticity side calculations. | toy model |
| `geoclaw_b2008_probe.sh` | Extracts GeoClaw `get_holland_b_2008` (12 lines) at the pinned revision, compiles it with gfortran and evaluates it with hPa and with Pa arguments. | execution of upstream function |
| `adcirc_uvp_probe.sh` | Compiles ADCIRC `vortex.F` lines 704-709 verbatim (fixed form) to show how the split `* *` is parsed. | execution of upstream expression |
| `ktools_probe.sh` | Times the ktools example pipeline and re-runs `gulcalc` with damage-bin interpolation points moved to 10% of each bin. Needs a built ktools tree. | execution of real binaries |
| `gul_mean_check.py`, `gul_paired_shift.py` | Compare Monte Carlo sample means with the analytic mean (sidx -1) in `gultocsv` output; paired comparison of two runs. | analysis of real outputs |
| `gul_interp_toy.py` | numpy transliteration of the in-bin quadratic interpolation in ktools and OasisLMF. | toy model |
| `outputs.txt` | Recorded outputs of all of the above, plus ktools build and test timings. | recorded output |
