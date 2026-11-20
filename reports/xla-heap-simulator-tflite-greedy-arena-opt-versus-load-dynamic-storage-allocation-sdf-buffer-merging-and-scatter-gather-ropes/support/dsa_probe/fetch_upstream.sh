#!/bin/sh
# Fetches the two upstream planner files at the pinned revision into ./upstream.
set -eu
REV=38a8f0f87302817ddfa99e6a995c7b71ef7118fe
BASE=https://raw.githubusercontent.com/tensorflow/tflite-micro/$REV/tensorflow/lite/micro/memory_planner
D=upstream/tensorflow/lite/micro/memory_planner
mkdir -p "$D"
for f in greedy_memory_planner.cc greedy_memory_planner.h micro_memory_planner.h; do
  curl -sSL -o "$D/$f" "$BASE/$f"
done
sha256sum "$D"/*
