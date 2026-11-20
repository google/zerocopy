#!/bin/bash
# Build CovidSim at the pinned revision under several compiler flag sets and
# rerun the upstream US-based integration test (1 and 2 threads) for each.
set -u
R=/tmp/covidsim-check/covid-sim-b719de9df5909f8fc47753dd1d2baf89fc415943
B=/tmp/covidsim-check
SRCS="src/CovidSim.cpp src/Rand.cpp src/Error.cpp src/Dist.cpp src/Kernels.cpp src/Bitmap.cpp src/SetupModel.cpp src/CalcInfSusc.cpp src/Sweep.cpp src/Update.cpp src/Param.cpp src/Person.cpp src/Direction.cpp src/InverseCdf.cpp src/Memory.cpp src/CLI.cpp src/Files.cpp src/ReadParams.cpp src/Geometry/Vector2.cpp"
declare -A FLAGS
FLAGS[O2_contract_off]="-O2 -ffp-contract=off"
FLAGS[O3]="-O3"
FLAGS[O2_march_native_fma]="-O2 -march=native -ffp-contract=fast"
FLAGS[O2_fastmath]="-O2 -ffast-math"
FLAGS[O0]="-O0"
cd $R
for v in O2_contract_off O3 O2_march_native_fma O2_fastmath O0; do
  echo "=== variant $v: ${FLAGS[$v]}"
  g++ -std=c++14 ${FLAGS[$v]} -fopenmp -DUNIX -Iinclude -Isrc $SRCS -o $B/bin/CovidSim_$v 2> $B/compile_$v.log || { echo "compile failed"; continue; }
  for j in 1 2; do
    python3 $R/tests/integration-test.py --input $R/tests/us-input --output $B/us-out-$v-j$j \
      --checksums $R/tests/us-input/results-j$j.cksum --covidsim $B/bin/CovidSim_$v \
      --popfile $R/data/populations/wpop_usacan.txt.gz --r 1.5 -j $j > $B/us-$v-j$j.log 2>&1
    echo "  j$j exit=$? $(grep -E 'SUCCESS|FAILURE: checksums' $B/us-$v-j$j.log | head -1)"
  done
done
