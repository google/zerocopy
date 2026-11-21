# Execution record

All execution evidence in the report was gathered on 2026-11-21 (UTC) on an x86-64 Linux
workstation (96 logical CPUs, Intel Xeon @ 2.60 GHz, 236 GiB RAM), CPython 3.13.15.

## Subjects as installed

Source tarballs were downloaded from GitHub's codeload endpoint at the pinned commits and
installed into a fresh virtual environment:

| Repository | Commit | Tarball SHA-256 | Installed as |
|---|---|---|---|
| pythermalcomfort/pythermalcomfort | a0e7ae2a9a0178f24b33fdd75f06f27e9f00ba76 | fe7731e6dd7f2cc96896e5f30b4d0f386991954bfae64fbfae206858d27e9173 | pythermalcomfort 4.8.1 |
| ecmwf/thermofeel | 53437e0e47fb428c452d0f418b68fb46ba802a22 | 1dec31422b820c0468581be908f5c6fecedcc0c7317ea3c12ae2e748cf9de8ee | thermofeel 2.3.0 |
| Unidata/MetPy | 5edfa0186fb0d01ef6d29319c6c2a496a888fb28 | 20b87737a976942e0adb462ee21b10558f5f170a9fc5f2ea99ecb73e2f2fb7fc | MetPy (version forced to 0.0.0, see below) |
| geanders/weathermetrics | 429ee9a4410c6c0c00d209a32ae8e52a0edfa4cc | f4030577474fe9d9f2dacb794245cc249c81ed628117463a4ac14b6ef522b91d | not installed (R not available); transliterated |

Resolved dependencies: numpy 2.5.4, numba 0.68.1, llvmlite 0.50.0, scipy 1.18.1, Pint 0.26.2,
pandas 3.1.1, xarray 2026.9.0.

```sh
python3 -m venv /tmp/heatprobe/venv
for r in pythermalcomfort/pythermalcomfort@a0e7ae2a9a0178f24b33fdd75f06f27e9f00ba76 \
         ecmwf/thermofeel@53437e0e47fb428c452d0f418b68fb46ba802a22 \
         Unidata/MetPy@5edfa0186fb0d01ef6d29319c6c2a496a888fb28; do
  repo=${r%@*}; sha=${r#*@}; name=$(basename $repo)
  mkdir -p /tmp/heatprobe/src/$name
  curl -sSL https://codeload.github.com/$repo/tar.gz/$sha | tar -xz -C /tmp/heatprobe/src/$name --strip-components=1
done
# setuptools-scm cannot read a version from a tarball without VCS metadata:
SETUPTOOLS_SCM_PRETEND_VERSION=0.0.0 /tmp/heatprobe/venv/bin/pip install \
  /tmp/heatprobe/src/pythermalcomfort /tmp/heatprobe/src/thermofeel /tmp/heatprobe/src/MetPy
# The MetPy wheel built from a VCS-less tarball omits a data manifest that its import
# requires; copy it from the source tree (packaging artefact of this install route only):
cp /tmp/heatprobe/src/MetPy/src/metpy/static-data-manifest.txt \
   /tmp/heatprobe/venv/lib/python3.13/site-packages/metpy/
```

## Probe commands

```sh
cd /tmp/heatprobe
NUMBA_CACHE_DIR=/tmp/heatprobe/numba_cache venv/bin/python probe_hi.py > probe_hi_output.txt
NUMBA_CACHE_DIR=/tmp/heatprobe/numba_cache venv/bin/python probe_wbgt_utci.py \
  src/pythermalcomfort/pythermalcomfort/models/utci.py src/thermofeel/thermofeel/thermofeel.py \
  > probe_wbgt_utci_output.txt
rm -rf /tmp/heatprobe/numba_cold && mkdir /tmp/heatprobe/numba_cold
NUMBA_CACHE_DIR=/tmp/heatprobe/numba_cold /usr/bin/time -v venv/bin/python perf_probe.py > perf_probe_output.txt 2>&1
```

Additional one-off measurements reported in the report:

* Import of `pythermalcomfort.models` with an empty numba cache: 12.12 s; with a populated
  cache: 1.63 s and 1.43 s (two runs); `thermofeel` < 0.01 s; `metpy.calc` 0.92–0.94 s.
* Numba on-disk cache after importing `pythermalcomfort.models` once: 2.1 MB (`du -sh`).
* Installed package sizes (`du -sh site-packages/<pkg>`): pythermalcomfort 2.1 MB,
  thermofeel 196 KB, metpy 3.3 MB, numba 33 MB, llvmlite 173 MB.
* Port check of `heat_index_lu` against the 54 reference values embedded in
  `tests/test_heat_index_lu.py::test_extended_heat_index` (T = 200..370 K by 10 K,
  RH = 0, 0.5, 1): maximum absolute deviation 2.22e-06 K (at T = 330 K, RH = 0); the
  upstream test itself only asserts `atol=1` K.

## Transcriptions used as references (not upstream software)

* `nws_literal` in `probe_hi.py` transcribes the NWS Weather Prediction Center
  "Heat Index Equation" page text (accessed 2026-11-21), reading "the simple formula is
  computed first and the result averaged with the temperature" as the switch criterion
  `(A + T)/2 >= 80 F`, returning the simple formula value `A` below the switch.
* `wm_translit` in `probe_hi.py` is a line-by-line Python transliteration of
  `heat.index.algorithm` in weathermetrics `R/heat_index.R` lines 156-186 at the pinned
  commit. R was not executed; the R wrapper's default `round = 0` (line 78, applied at
  line 108) is not reproduced by the transliteration.
