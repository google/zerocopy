Support material for the kidney-function equations report (text only).

egfr_probe.R       Differential and edge-case probe. Sources the R/ files of kidney.epi 1.4.0 and nephro 1.5
                   (extracted from GitHub codeload tarballs of cran/kidney.epi and cran/nephro at the commits pinned
                   in REPORT.json) and runs both on shared synthetic inputs.
                   Run: KIDNEY_EPI_DIR=<kidney.epi tree> NEPHRO_DIR=<nephro tree> Rscript egfr_probe.R
                   Observed with R 4.4.2 in the docker.io/library/r-base:4.4.2 image, network disabled.
egfr_probe.out     Output of the above (two runs were byte-identical).
egfr_timing.R      Throughput / memory probe (n = 1e4, 1e5, 1e6 synthetic inputs). Output: egfr_timing.out.
egfr_reference.py  Python transcription of the published formulas; identities, calibration propagation, cap/floor,
                   indexing, formula properties, and comparison with egfr_probe.out.
                   Run: python3 egfr_reference.py egfr_probe.out   (stdlib only). Output: egfr_reference.out.
All inputs are synthetic. Nothing here is clinical or dosing guidance.
