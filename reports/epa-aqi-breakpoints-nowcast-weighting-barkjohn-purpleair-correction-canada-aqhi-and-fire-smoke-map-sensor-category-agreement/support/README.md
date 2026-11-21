# Support material for the AQI report

These are text-only probe scripts and their raw outputs. Paths are examples; set `OUT` to any scratch directory.

## Inputs (all from pinned upstream revisions; see REPORT.md, Evidence)

| File | SHA-256 |
|---|---|
| `hrbonz/python-aqi` `docs/standards/epa-tad-2018-09_EPA-454-B-18-007.pdf` | `173f8d8668e37bc477290b84d13b905f07235815aca4875cfa78cff712646449` |
| `hrbonz/python-aqi` `docs/standards/epa-tad-2024-05_EPA-454-B-24-002.pdf` | `2c5bd330b956ca8cdbd1c92dbd62ecfb77052ee0794efbd4604b3d2c190ae290` |
| `hrbonz/python-aqi` `docs/standards/epa-tad-2026-05_EPA-403-B-26-003.pdf` | `b69de26a0f3d4603572595fc8b49be8fd157fd0faaaab023410bb13b4b6e5e0c` |
| `USEPA/O3-Nowcast` `WhitePaper.pdf` | `40e192b8d6df4df5219efef429880a7598183b48f80582fce75ae9103de2943d` |
| `USEPA/O3-Nowcast` `ExampleData.csv` | `a65d9181a800a061cefceb220a54fa9f57cbecd588e83226a16e5f53ef9394f1` |
| `USEPA/FASM-sensor-AQI-analysis` `data/purpleair_data.csv` | `e8544e195be73ba429e9a5b891e8806b3ddc294da7335c43939f37fc5126efa2` |

## aqi_diff/ — boundary-grid differential test

```sh
OUT=/tmp/aqi-probe; mkdir -p $OUT
pip install https://codeload.github.com/hrbonz/python-aqi/tar.gz/<python-aqi revision>
python3 aqi_reference_and_grid.py $OUT      # grid.csv (29,956 inputs) + exact reference ref.csv
python3 run_python_aqi.py $OUT              # pyaqi.csv
Rscript run_con2aqi.R <con2aqi checkout>/R/con2aqi.R $OUT   # con2aqi.csv
python3 compare.py $OUT > out_compare.txt
python3 refine.py $OUT > out_refine.txt
python3 ties.py $OUT > out_ties.txt
Rscript edge_con2aqi.R <con2aqi checkout>/R/con2aqi.R > out_edge_con2aqi.txt
```

`out_table_shift.txt` holds the pre-2024 versus 2024 PM2.5 category and index changes, computed from `ref.csv`.

## o3_nowcast/ — USEPA/O3-Nowcast

- `out_upstream_Example_r.txt`: `Rscript Example.r`, run unmodified in a checkout of the pinned revision.
- `o3_harness.R <checkout> upd|orig`: calls `GetNowcast()` directly on `ExampleData.csv` after parsing ISO timestamps. `upd` sources `NowcastFun_Upd.r`, as `Example.r` does; `orig` sources `NowcastFun.r`. The `orig` run also compares `pls::mvr` (default ncomp) with `lm()` and lists predictions for ncomp = 1…20. Its output is in `out_o3_harness.txt`.
- Requires R with the packages zoo, plyr, pls and imputeTS (versions used: R 4.4.3, zoo 1.9.0, plyr 1.8.9, pls 2.9.0, imputeTS 3.4).

## fasm_category/ — sensor side of the Fire and Smoke Map category-agreement code

```sh
Rscript fasm_sensor_nowcast.R <AirMonitor checkout>/R/monitor_nowcast.R <FASM checkout>/data/purpleair_data.csv 300 $OUT
python3 fasm_port.py <FASM checkout>/data/purpleair_data.csv $OUT/r_nowcast_subset.csv 300
```

The R script sources only AirMonitor's internal `.nowcast()` and `.weightFactor()`, so it needs no other packages. The Python port reproduces the R output exactly on the 300-sensor subset before it is applied to all 7,809 sensors. `out_python_aqi_nowcast_check.txt` cross-checks `python-aqi`'s NowCast against the forum example documented in AirMonitor and shows how it handles negative readings.

## correction/ — arithmetic on the published PurpleAir correction coefficients

`python3 barkjohn_piecewise.py` evaluates the 2021 US-wide equation and the 2022 extended piecewise equation exactly as printed. It reports the blend weights and the jumps at raw cf_1 = 570 and 611.
