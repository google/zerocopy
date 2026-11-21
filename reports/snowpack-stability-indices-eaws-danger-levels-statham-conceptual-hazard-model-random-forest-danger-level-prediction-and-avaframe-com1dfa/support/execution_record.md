# Execution record (observed 2026-11-21 UTC)

Host class: x86-64 Linux (Debian-based userland), Intel Xeon CPU @ 2.60 GHz, 96 logical
CPUs, 236 GiB RAM, GCC 15.2.0, CMake 4.4.4 (PyPI wheel). `$WORK` stands for a scratch
directory. Times are wall-clock from `/usr/bin/time -v`; "peak RSS" is that tool's
"Maximum resident set size", i.e. the largest single process in the measured tree.

## SNOWPACK (snowpack-model/snowpack @ b324cbdd1b7f4da4db8ff8a5b408274e88ac1945)

```console
curl -sSL -o snowpack.tar.gz https://codeload.github.com/snowpack-model/snowpack/tar.gz/b324cbdd1b7f4da4db8ff8a5b408274e88ac1945
# sha256 91f7c189676519408b8f19eae3d2fc26a253b0c06249077789f88a85252d9bae (54,229,300 bytes)
cd Source/meteoio  && cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_POLICY_VERSION_MINIMUM=3.5 . && make -j8
cd ../snowpack     && cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_POLICY_VERSION_MINIMUM=3.5 . && make -j8
cd tests/res1exp && mkdir -p output && ../../bin/snowpack -c io_res1exp.ini -e 1996-06-17T00:00
```

| step | wall | peak RSS | artifact sizes |
|---|---|---|---|
| MeteoIO configure+build (`make -j8`) | 46.15 s | 335,204 kB | `libmeteoio.so.2.11.0` 67,882,560 B |
| SNOWPACK configure+build (`make -j8`) | 23.74 s | 762,056 kB | `bin/snowpack` 2,417,320 B; `libsnowpack.so.3.7.1` 35,709,072 B |
| `res1exp` season run (1995-10-30 to 1996-06-17, 15 min steps) | 31.16 s (user 29.26 s) | 39,792 kB | `.pro` 59,559,366 B; `.met` 1,192,274 B |

SNOWPACK's own log line for the run: `Runtime for station MST96: 29.482095 s`;
`Total time to read meteo data : 0.661332 s`.

Season summary of the `.met` stability columns for the 1782 three-hourly records with
modelled snow depth > 0 (flat field, defaults of `io_res1exp.ini`):

| quantity | value |
|---|---|
| records with HS > 0 / all records | 1782 / 1833 |
| maximum modelled HS | 141.58 cm |
| `Stability class` counts | -1: 177, 1: 506, 3: 838, 5: 261 |
| Sk38 (n = 1750 non-nodata) | min 0.05, median 0.505, max 6.0 (145 records at the 6.0 cap) |
| SSI (n = 1750) | min 0.05, median 2.05, max 6.0 (145 at cap) |
| Sn38 (n = 1630) | min 1.11, median 2.34, max 6.0 (304 at cap) |
| Sdef (n = 1630) | min 0.1, median 0.47, max 3.67 |
| `Profile type` | -1 in all 1782 records |

Reference-output comparison (`snowpack_ref_compare.py output output_ref MST96_res`):

```text
.haz {'tokens_out': 773, 'tokens_ref': 753, 'numeric_compared': 567, 'numeric_over_tol': 10, 'text_mismatch': 167, 'max_rel_diff': 1.4930898321816386}
.sno {'tokens_out': 130, 'tokens_ref': 86, 'numeric_compared': 8, 'numeric_over_tol': 1, 'text_mismatch': 56, 'max_rel_diff': 1.0}
.met {'tokens_out': 138027, 'tokens_ref': 128831, 'numeric_compared': 121431, 'numeric_over_tol': 111421, 'text_mismatch': 7369, 'max_rel_diff': 2.0}
.pro {'tokens_out': 10699945, 'tokens_ref': 3691759, 'numeric_compared': 3686204, 'numeric_over_tol': 3574205, 'text_mismatch': 5515, 'max_rel_diff': 2.0}
```

The `.met` reference header reads `#2017-06-21T14:44:26, Snowpack DEFAULT version 3.41 ...`
and has 100 numbered columns; the freshly built binary writes 103. First data row,
column "Sensible heat": reference 0.507748, new run 2.001995 W m-2.

CTest with the repository's own test definition (numdiff not installed on the host; absolute
scratch paths in the log lines below are elided):

```console
cmake -DBUILD_TESTING=ON -DCMAKE_POLICY_VERSION_MINIMUM=3.5 . && make -j8   # exits 2, see below
ctest -R res1exp.smoke -V
```

```text
run_res1exp.sh: line 13: numdiff: command not found
run_res1exp.sh: line 16: numdiff: command not found
run_res1exp.sh: line 22: numdiff: command not found
run_res1exp.sh: line 28: numdiff: command not found
1/1 Test #1: res1exp.smoke ....................   Passed   30.40 sec
100% tests passed out of 1
```

The `BUILD_TESTING=ON` build stops in a different test target:

```text
tests/albedo/albedoTest.cc:584:51: error: could not convert 'slope.Slope::snow_erosion' from 'std::string' {aka 'std::__cxx11::basic_string<char>'} to 'bool'
```

## AvaFrame (OpenNHM/AvaFrame @ 61f1bb90f5aee0e10b81a46d15aca1ed8663fb7a)

Python 3.12.16 (python-build-standalone 20261110), numpy 1.26.4, Cython 3.3.1. The
standalone interpreter's sysconfig names `clang` as compiler; with no clang on the host
the first build failed, so `CC=gcc LDSHARED="gcc -pthread -shared"` was set.

```console
curl -sSL -o avaframe.tar.gz https://codeload.github.com/OpenNHM/AvaFrame/tar.gz/61f1bb90f5aee0e10b81a46d15aca1ed8663fb7a
# sha256 14603bb7d9058bc89eec17a8ac6cccc4f927ed5ddbe3e2015132d80f6515e541
CC=gcc LDSHARED="gcc -pthread -shared" SETUPTOOLS_SCM_PRETEND_VERSION=0.0.0+g61f1bb9 pip install .
cd avaframe   # run scripts use paths relative to the package directory
MPLBACKEND=Agg python runScripts/runSimilaritySol.py
MPLBACKEND=Agg python avaframe_similarity_solution_table.py similarity_errors.csv
MPLBACKEND=Agg python runScripts/runEnergyLineTest.py
MPLBACKEND=Agg python runScripts/runDamBreak.py
```

| step | wall | peak RSS | result |
|---|---|---|---|
| `pip install .` (downloads + Cython build) | 3:29.82 | 438,652 kB | installed |
| `runSimilaritySol.py` (24 simulations, default `nCPU = auto`, `CPUPercent = 50`) | 1:41.72 | 470,092 kB | exit 0 |
| similarity-solution post-processing (this package's script) | 48.70 s | 542,192 kB | `avaframe_similarity_solution_errors.csv` |
| `runEnergyLineTest.py` (`data/avaParabola`) | 1:01.23 | 433,268 kB | exit 0, see below |
| `runDamBreak.py` | 2.88 s | 231,636 kB | exit 1: `NotImplementedError: iniStep=True is currently not supported due to recent refactoring of thickness handling. ...` |

Energy-line test log lines:

```text
Runout s diff : -6.2784e-03 m
Runout z diff : 8.9606e-04 m
Runout angle diff : 6.6068e-05°
velocity height rmse : 8.9900e-04 m
```

`samosATAuto` boundary probe (`python avaframe_samosat_auto_boundary.py`, same environment):

```text
relVolume=   24999  frictModel -> samosATSmall   indexable=True  volumeIndicator=S
relVolume=   25000  frictModel -> samosATMedium  indexable=True  volumeIndicator=M
relVolume=   59999  frictModel -> samosATMedium  indexable=True  volumeIndicator=M
relVolume=   60000  frictModel -> samosATAuto    indexable=False  volumeIndicator=M
relVolume=   60001  frictModel -> samosAT        indexable=True  volumeIndicator=L
```
