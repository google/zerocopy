# Differential probe: BCRA (R) versus bcra (JavaScript)

Support material for the report in the parent directory. All files are plain text.
The inputs are synthetic and describe no real person.

## Files

- `gen_profiles.py <bcra-js checkout> <profiles.csv>`: writes 2,374 shared input
  profiles. It reads the R-reference fixtures from the JavaScript port's checkout and adds
  edge rows and seeded random rows (seed 20261121).
- `run_bcra.R <profiles.csv> <out_r.csv> [<R library dir>]`: runs `recode.check`,
  `relative.risk` and `absolute.risk` (individual and `Avg_White = 1`) on all rows
  together. It also runs every `Solo = 1` row as a one-row data frame and captures any R error.
- `run_bcrajs.mjs <path to packages/bcra/src/index.js> <profiles.csv> <out_js.csv>`:
  runs `calculateRisk(profile, {calculateAverage: true})` on every row.
- `compare.py <bcra-js checkout> <profiles.csv> <out_r.csv> <out_js.csv>`: prints
  (1) the current R output against the port's recorded R values, (2) the R/JS disagreement
  classes, (3) every edge row and disagreement, and (4) the one-row-frame R results.
- `results/`: the logs of the run reported in `REPORT.md`.

## Reproduce

```sh
git clone https://github.com/cran/BCRA && git -C BCRA checkout 05bfdea1a18c78f411afa9c8c0fbcdf0ccae7499
git clone https://github.com/epiverse/bcra-js && git -C bcra-js checkout 4a38d20753fc28e1e0416818cef698b28415da18
mkdir -p rlib && R CMD INSTALL -l rlib BCRA
python3 gen_profiles.py bcra-js /tmp/profiles.csv
Rscript run_bcra.R /tmp/profiles.csv /tmp/out_r.csv rlib
node run_bcrajs.mjs bcra-js/packages/bcra/src/index.js /tmp/profiles.csv /tmp/out_js.csv
python3 compare.py bcra-js /tmp/profiles.csv /tmp/out_r.csv /tmp/out_js.csv
```

The reported run used R 4.4.1 (`r-base:4.4.1` container) and Node.js 22.11.0
(`node:22.11.0-slim` container), both with networking disabled.
