# Support material for the bridge load-rating report

These are text-only probe scripts and their raw outputs. They require Python 3 with numpy, plus pycba installed from the pinned revision:

```sh
pip install https://codeload.github.com/ccaprani/pycba/tar.gz/<pycba revision>
```

| Script | What it checks | Output |
|---|---|---|
| `pycba_il_check.py` | Moment and reaction influence lines of a 20 m simple span and a 2×20 m continuous beam against closed forms (simple-span IL; three-moment equation for the interior-support moment). Also the HL-93 truck's absolute maximum moment on 20 m (resultant theorem and fine-grid brute force) against `BridgeAnalysis.run_vehicle` envelopes at several steps, with wall time and traced allocation | `out_il_check.txt` |
| `pycba_continuous_check.py` | Envelope extremes on 2×20 m (interior-support minimum, 0.4L maximum) against the sum of axle loads times closed-form ILs over 200,001 grid positions plus the exact kink positions | `out_continuous_check.txt` |
| `pycba_state_probe.py` | `InfluenceLines` state reuse (`create_ils` twice), a step that does not divide L, and POI snapping for `npts` = 10, 20, 100 and 1000 | `out_state_probe.txt` |
| `hl93_si_vs_customary.py` | Statics only, independent of pycba: absolute maximum truck moment for the SI-edition HL-93 truck (35/145/145 kN at 4.3 m) against 8/32/32 kip at 14 ft | `out_hl93_si_vs_customary.txt` |

Each script runs in under 10 s with less than 200 MiB RSS on a current x86-64 workstation; the measured values are recorded in the outputs. The closed-form reference code inside these scripts was written for this report. It is a checking oracle, not part of pycba.
