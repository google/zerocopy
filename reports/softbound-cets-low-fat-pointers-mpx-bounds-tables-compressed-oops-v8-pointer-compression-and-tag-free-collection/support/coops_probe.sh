#!/usr/bin/env bash
# HotSpot compressed-oops / compressed-class-pointer mode and footprint probe.
# Requires: a Linux x86-64 host with >= 8 GiB RAM, curl, tar, sha256sum.
# Uses Eclipse Temurin 25.0.5+8 (OpenJDK 25.0.5) from the adoptium/temurin25-binaries GitHub release.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${WORK:-/tmp/coops_probe}"; mkdir -p "$WORK"; cd "$WORK"
URL="https://github.com/adoptium/temurin25-binaries/releases/download/jdk-25.0.5%2B8/OpenJDK25U-jdk_x64_linux_hotspot_25.0.5_8.tar.gz"
EXPECT=68982529869257d0ee6b824ec5aa270ff8b118bb438670da0b97ebdab178d7fb
[ -f jdk.tar.gz ] || curl -sSL -o jdk.tar.gz "$URL"
echo "$EXPECT  jdk.tar.gz" | sha256sum -c -
[ -d jdk-25.0.5+8 ] || tar xzf jdk.tar.gz
J="$WORK/jdk-25.0.5+8/bin"
unset _JAVA_OPTIONS JAVA_TOOL_OPTIONS JDK_JAVA_OPTIONS
"$J/java" -version 2>&1

echo "== Encoding mode chosen for each maximum heap size (G1, default alignment 8) =="
for x in 1g 3g 4g 16g 31g 32g 33g; do
  printf -- "-Xmx%-4s " "$x"
  "$J/java" -Xmx$x -Xlog:gc+heap+coops=debug -XX:+PrintFlagsFinal -version 2>/dev/null \
    | grep -E "Compressed Oops mode| UseCompressedOops " | sed -E 's/^\[[^]]*\]\[[^]]*\]\[[^]]*\] *//; s/ +/ /g' | tr '\n' ' '
  echo
done
echo "== ObjectAlignmentInBytes=16 widens the zero-based range =="
for x in 33g 60g 64g; do
  printf -- "-Xmx%-4s align16 " "$x"
  "$J/java" -Xmx$x -XX:ObjectAlignmentInBytes=16 -Xlog:gc+heap+coops=debug -XX:+PrintFlagsFinal -version 2>/dev/null \
    | grep -E "Compressed Oops mode| UseCompressedOops " | sed -E 's/^\[[^]]*\]\[[^]]*\]\[[^]]*\] *//; s/ +/ /g' | tr '\n' ' '
  echo
done
echo "== Narrow klass encoding (default vs compact object headers) =="
"$J/java" -Xlog:gc+metaspace=info -version 2>&1 | grep -iE "narrow klass|encoding range" | sed -E 's/^\[[^]]*\]\[[^]]*\]\[[^]]*\] *//' | head -5
"$J/java" -XX:+UseCompactObjectHeaders -Xlog:gc+metaspace=info -version 2>&1 | grep -iE "narrow klass|encoding range" | sed -E 's/^\[[^]]*\]\[[^]]*\]\[[^]]*\] *//' | head -5

echo "== Footprint / traversal (N=4000000 nodes, -Xms2g -Xmx2g, -XX:+UseSerialGC, JIT enabled) =="
cp "$HERE/CoopsFootprint.java" .
"$J/javac" -d . CoopsFootprint.java
for flags in "" "-XX:-UseCompressedOops" "-XX:+UseCompactObjectHeaders" "-XX:-UseCompressedOops -XX:+UseCompactObjectHeaders"; do
  for rep in 1 2 3; do
    echo "flags=[${flags:-default}] rep=$rep $("$J/java" -Xms2g -Xmx2g -XX:+UseSerialGC $flags -cp . CoopsFootprint 4000000 2>&1 | tr '\n' ' ')"
  done
done
