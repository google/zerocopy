#!/bin/sh
# Fetch the four unmodified upstream algorithm files at the pinned revision into this directory
# and verify their SHA-256 digests (as observed when the report was written).
set -e
cd "$(dirname "$0")"
REV=553ba61952012ad6e895532bb2bfda0e790a3beb
for f in algorithm.cpp algorithm.h algorithm_by_RF.cpp algorithm_by_RF.h; do
  curl -sSL "https://raw.githubusercontent.com/aromring/MAX30102_by_RF/$REV/$f" -o "$f"
done
sha256sum -c <<'SUMS'
f3d09974014b1a3eef4c5dd027cc02d9ec162313b63180f722d65cbd14431e4b  algorithm.cpp
1b3bae1a1036477980bf429397fbb163861eadd9ea6473f6d6083151d31ac3f0  algorithm.h
72ba4792c2062d7366b611c5ae49a9507dc86b1f0817fc81ecc38090b3a8feb4  algorithm_by_RF.cpp
f6c80be33ce6569966336ba2ccb681c79224de4cc75fa0615467f4f25c35070b  algorithm_by_RF.h
SUMS
g++ -O2 -fwrapv -Ishim -o ppg_probe ppg_probe.cpp algorithm.cpp algorithm_by_RF.cpp
