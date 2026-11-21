#!/bin/sh
# Sweep driver for ppg_probe (synthetic inputs only).
# Columns: R PI noise_sd_counts drift_amp_over_AC hr_bpm dc_ir batches seed
B="$(dirname "$0")/ppg_probe"
while read R PI SD DR HR DC N S; do
  "$B" "$R" "$PI" "$SD" "$DR" "$HR" "$DC" "$N" "$S" | tail -1
done <<'CONDS'
0.5 0.02 0 0 72 131500 20 1
0.7 0.02 0 0 72 131500 20 1
1.0 0.02 0 0 72 131500 20 1
1.3 0.02 0 0 72 131500 20 1
0.7 0.005 0 0 72 131500 20 1
0.7 0.001 0 0 72 131500 20 1
0.7 0.0003 0 0 72 131500 20 1
0.7 0.02 20 0 72 131500 50 2
0.7 0.02 100 0 72 131500 50 3
0.7 0.005 20 0 72 131500 50 4
0.7 0.005 100 0 72 131500 50 5
0.7 0.001 20 0 72 131500 50 6
0.7 0.02 0 2 72 131500 50 7
0.7 0.02 0 10 72 131500 50 8
0.7 0.02 0 0 150 131500 20 9
0.7 0.02 0 0 45 131500 20 10
0.7 0.10 0 0 72 230000 20 11
1.0 0.10 0 0 72 230000 20 12
1.83 0.02 0 0 72 131500 20 13
0.2 0.02 0 0 72 131500 20 14
CONDS
# Edge cases (out/ppg_sweep2.txt) were run individually, e.g.:
#   ./ppg_probe 0.7 0.07 0 0 72 230000 5 23
#   ./ppg_probe 1.82 0.02 0 0 72 131500 5 27
