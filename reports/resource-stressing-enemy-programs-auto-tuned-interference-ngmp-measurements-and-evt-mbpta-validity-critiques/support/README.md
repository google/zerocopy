# Support material

Text-only probes and outputs referenced by `REPORT.md`. Nothing here is a
hardware measurement; all inputs are synthetic.

| File | Purpose |
| --- | --- |
| `mbpta_driver.cpp` | Runs chronovise's sample tests, block-maxima + PWM GEV fit and post-EVT tests on a text column of values |
| `gen_samples.py` | Generates the three synthetic datasets (`gen`) and computes exceedance under the deployed mixture (`exceed <w>`) |
| `mbpta_driver.out` | Driver output for the three n = 20000 datasets |
| `mbpta_driver_bds_small.out` | Driver output and timing for n = 250, 500, 1000 (includes the BDS test) |
| `exceed.out` | Monte Carlo exceedance of the "campaign" pWCET under the deployed mixture |
| `bds_size.cpp` | Empirical size / translation-invariance study of chronovise's `TestBDS` |
| `bds_patch_coefficient_only.diff`, `bds_patch.diff` | Local patches used only to localize the BDS defects (not upstream changes) |
| `bds_size.out` | Output of the size study for the upstream library and both patched variants |

Build instructions are in `REPORT.md` under **Evidence**. The chronovise
library must be built from `federeghe/chronovise` at
`4b332f10669af73f33e00f8749040eed9601bfb2` without `ceres-solver`, adding
`-include cstdint` for current GCC.
