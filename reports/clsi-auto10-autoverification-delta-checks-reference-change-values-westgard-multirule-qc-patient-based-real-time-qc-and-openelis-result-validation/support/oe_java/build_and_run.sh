#!/usr/bin/env bash
# Compile selected OpenELIS Global 2 classes (unmodified, fetched at a pinned commit) against minimal
# stubs of their framework/valueholder dependencies, then run Probe.java.
# Usage: WORK=<scratch dir> bash build_and_run.sh   (needs curl, javac/java >= 17)
set -euo pipefail
SHA=2865b4cfec53a0334d3f5a33e14e350e8ee64e55
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="${WORK:-$HERE/work}"
rm -rf "$WORK"; mkdir -p "$WORK/src" "$WORK/classes"
B=src/main/java/org/openelisglobal
UPSTREAM="qc/service/evaluator/AbstractWestgardRuleEvaluator.java qc/service/evaluator/WestgardRuleEvaluator.java
qc/service/evaluator/RuleEvaluationResult.java qc/service/evaluator/Rule1_2sEvaluator.java qc/service/evaluator/Rule1_3sEvaluator.java
qc/service/evaluator/Rule2_2sEvaluator.java qc/service/evaluator/RuleR_4sEvaluator.java qc/service/evaluator/Rule4_1sEvaluator.java
qc/service/evaluator/Rule10_xEvaluator.java resultvalidation/util/ValidationSignals.java resultlimits/valueholder/ResultLimit.java"
for p in $UPSTREAM; do
  mkdir -p "$WORK/src/org/openelisglobal/$(dirname "$p")"
  curl -fsSL -H "User-Agent: research-bot" -o "$WORK/src/org/openelisglobal/$p" \
    "https://raw.githubusercontent.com/DIGI-UW/OpenELIS-Global-2/$SHA/$B/$p"
  sha256sum "$WORK/src/org/openelisglobal/$p" | sed "s#$WORK/src/##"
done
cp -r "$HERE/stubs/." "$WORK/src/"
cp "$HERE/Probe.java" "$WORK/src/"
javac -encoding UTF-8 -d "$WORK/classes" $(find "$WORK/src" -name '*.java')
java -cp "$WORK/classes" Probe
