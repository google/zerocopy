# Support material: slope-stability probes

Text-only probe scripts and raw outputs cited by `REPORT.md`. All runs were made on
2026-11-21 (UTC) on a Linux x86-64 virtual machine (Intel Xeon CPU @ 2.60 GHz,
96 vCPUs), CPython 3.13.15, NumPy 2.3.5, GNU Fortran 15.2.0. Timings are single
runs, not averaged, and include process start-up.

## `probes/`

| file | what it runs | what it is |
|---|---|---|
| `p64_driver.f90` | 7-line Fortran main program calling `SUBROUTINE p64(input_file, output_file)` | build glue for the upstream textbook program 6.4 |
| `p64_sweep.py` | runs the program-6.4 binary over meshes x tolerances x iteration ceilings | sweep harness |
| `pyslope_shims.py` | stubs `tqdm`, `plotly.graph_objects`, `colour.Color` so the unmodified PySlope analysis core imports without plotting packages | import shim; plotting is never exercised |
| `pyslope_probe.py` | executes upstream PySlope (P1 doc example, P2 automatic search, P3 iteration policy, P4 cross-check against the toy Bishop) | probe of the real upstream code |
| `toy_lem.py` | OMS, Bishop simplified, Spencer and Morgenstern-Price (half-sine) via a GLE force recursion, plus a grid search over circles | **toy model written for this report, not upstream code** |
| `reliability_recompute.py` | recomputes reliability indices from the variance components tabulated by Christian, Ladd & Baecher (1994) | derived arithmetic on published numbers |
| `pybimstab_expr_probe.py` | evaluates, in CPython, two Boolean expressions copied verbatim from pyBIMstab | expression semantics only, not pyBIMstab |

## Reproduction

```sh
# 1. Textbook strength-reduction program (Smith & Griffiths program 6.4, community port)
mkdir -p /tmp/slope-probe && cd /tmp/slope-probe
curl -sSL -o pfem.tar.gz \
  https://codeload.github.com/cunyizju/Programming-FEM-5th-Fortran/tar.gz/bf19e8a773c2a9f0a9a10f304540efdf586955f1
sha256sum pfem.tar.gz   # 923a2c82bdd66c7a1004283221739aa581694b8085c5ee6ae0524d4fe3d4a901
tar xzf pfem.tar.gz && mkdir build && cd build
cp ../Programming-FEM-5th-Fortran-*/main/*.f90 ../Programming-FEM-5th-Fortran-*/geom/*.f90 .
rm getname.f90                       # does not compile with gfortran 15 and is not used by p64
cp ../Programming-FEM-5th-Fortran-*/subordinates/Material-Non-linearity/p64.f90 p64_orig.f90
# Probe patch: p64.f90 passes the uninitialised locals argv/nlen to mesh(); give them values.
awk 'NR==32{print " argv='"'"'p64'"'"'; nlen=3"} {print}' p64_orig.f90 > p64_patched.f90
cp <support>/probes/p64_driver.f90 driver.f90
gfortran -O2 -c main_int.f90 geom_int.f90
for f in *.f90; do case $f in main_int.f90|geom_int.f90|driver.f90|p64_orig.f90) ;; *) gfortran -O2 -c $f;; esac; done
gfortran -O2 -o run_p64 driver.f90 *.o
cp ../Programming-FEM-5th-Fortran-*/subordinates/Material-Non-linearity/p64.dat .
./run_p64 p64.dat p64.res && cat p64.res      # must equal the repository's p64.res
python3 <support>/probes/p64_sweep.py ./run_p64 ./sweep

# 2. PySlope (unmodified analysis core)
mkdir -p /tmp/slope-probe/pyslope && cd /tmp/slope-probe/pyslope
for f in pyslope.py utilities.py data_validation.py; do
  curl -sSLO https://raw.githubusercontent.com/JesseBonanno/PySlope/d6167796769743e069ec540588193216753b678f/pyslope/$f
done
cp <support>/probes/{pyslope_shims.py,pyslope_probe.py,toy_lem.py} .
PYTHONPATH=. python3 pyslope_probe.py p1 p2 p3 p4

# 3. Toy limit-equilibrium grid search, reliability arithmetic, expression semantics
python3 <support>/probes/toy_lem.py 50
python3 <support>/probes/reliability_recompute.py
python3 <support>/probes/pybimstab_expr_probe.py
```

Importing `pyslope.py` as a top-level module (directory on `PYTHONPATH`, not the
package) selects its absolute-import branch (`if __name__ in ("__main__",
"pyslope", "__mp_main__")`), which avoids the package `__init__.py` and its
generated `_version.py`.

## `outputs/`

| file | content |
|---|---|
| `ssrm_p64_published_example.txt` | reproduction of the repository's stored `p64.res`, plus wall time / peak RSS for the published and a 4x-refined mesh |
| `ssrm_p64_sweep.txt` | first non-converging trial factor vs mesh, tolerance and iteration ceiling; per-trial iteration counts. The `maxrss_kB` column is `getrusage(RUSAGE_CHILDREN).ru_maxrss`, i.e. the running maximum over all child processes so far, not a per-run value |
| `ssrm_p64_false_convergence.txt` | trials up to SRF 4.0 with tolerance 1e-3 and 1e-4 at large ceilings: iteration counts saturate near 1/tolerance while displacement grows by orders of magnitude |
| `pyslope_probe.txt` | P1-P4 outputs |
| `toy_lem_grid_search.txt` | toy grid search and four-method comparison on the toy critical circle |
| `reliability_recompute.txt` | recomputed reliability indices |
| `pybimstab_expr_probe.txt` | expression-semantics output |
