#!/usr/bin/env bash
# Re-run every execution probe of this report and regenerate support/outputs/*.txt.
# Usage: run_probes.sh <spotbugs-4.10.5-dir> [workdir]
#   <spotbugs-4.10.5-dir>: extracted GitHub release asset spotbugs-4.10.5.tgz
#     (sha256 cce3244900cc215ccd9f5a8db29ed9468fc47824faf662f4fad005343d96007e)
# Requires gcc, javac/java (any JDK that can target --release 17), rustup with cargo-clippy.
set -u
SB="${1:?path to spotbugs-4.10.5}"
HERE="$(cd "$(dirname "$0")" && pwd)"
W="${2:-/tmp/precedence-probe-work}"
OUT="$HERE/outputs"
mkdir -p "$W" "$OUT"
cp "$HERE"/probes/* "$W"/
cd "$W"

{
  echo '$ gcc --version | head -1'; gcc --version | head -1
  for flags in "" "-Wall" "-Wall -Wextra" "-Wparentheses" "-Wall -Wextra -Wconversion"; do
    echo; echo "\$ gcc -std=c17 -fsyntax-only $flags probe.c"
    gcc -std=c17 -fsyntax-only $flags probe.c 2>&1 | grep -E "warning|error|note"
    echo "[exit ${PIPESTATUS[0]}]"
  done
} > "$OUT/gcc.txt" 2>&1

rm -rf jcls jrej && mkdir -p jcls jrej
{
  echo '$ javac -version'; javac -version 2>&1 | grep -v _JAVA_OPTIONS
  echo '$ javac --release 17 -Xlint:all -g -d jcls Probe.java'
  javac --release 17 -Xlint:all -g -d jcls Probe.java 2>&1 | grep -v _JAVA_OPTIONS; echo "[exit ${PIPESTATUS[0]}]"
  echo '$ javac --release 17 -d jrej ProbeReject.java'
  javac --release 17 -d jrej ProbeReject.java 2>&1 | grep -v _JAVA_OPTIONS; echo "[exit ${PIPESTATUS[0]}]"
} > "$OUT/javac.txt" 2>&1

for mode in "" "-low"; do
  /usr/bin/time -f "WALL %e s MAXRSS %M KB" -o "time$mode.txt" \
    java -jar "$SB/lib/spotbugs.jar" -textui -effort:max $mode -xml:withMessages -output "sb$mode.xml" jcls 2>/dev/null
done
python3 - "$W" > "$OUT/spotbugs.txt" <<'EOF'
import sys, xml.etree.ElementTree as ET
w = sys.argv[1]
print("SpotBugs 4.10.5; classes compiled with: javac --release 17 -Xlint:all -g -d jcls Probe.java")
for f in ['sb.xml', 'sb-low.xml']:
    r = ET.parse(f"{w}/{f}").getroot()
    low = '-low ' if 'low' in f else ''
    print(f"\n$ java -jar spotbugs-4.10.5/lib/spotbugs.jar -textui -effort:max {low}-xml:withMessages -output {f} jcls")
    s = r.find('FindBugsSummary')
    print("FindBugsSummary:", {k: s.get(k) for k in ['total_classes', 'total_bugs', 'cpu_seconds', 'clock_seconds', 'peak_mbytes', 'priority_1', 'priority_2', 'priority_3']})
    print(open(f"{w}/time{'-low' if low else ''}.txt").read().strip())
    print("type | priority | rank | category | method | source line")
    for b in r.iter('BugInstance'):
        m = b.find('Method'); sl = b.find('SourceLine')
        print(' | '.join([b.get('type'), b.get('priority'), b.get('rank'), b.get('category'),
                          (m.get('name') if m is not None else '(field)'), (sl.get('start') if sl is not None else '')]))
EOF

rm -rf rprobe && cargo new --lib --edition 2024 rprobe -q --vcs none && cp probe_lints.rs rprobe/src/lib.rs
{
  echo '$ rustc -V; cargo clippy -V'; rustc -V; (cd rprobe && cargo clippy -V)
  echo; echo '$ cargo clippy -q (defaults)'; (cd rprobe && cargo clippy -q --color never 2>&1); echo "[exit $?]"
  echo; echo '$ cargo clippy -q -- -W clippy::precedence_bits -W clippy::integer_division -W clippy::pedantic'
  (cd rprobe && touch src/lib.rs && cargo clippy -q --color never -- -W clippy::precedence_bits -W clippy::integer_division -W clippy::pedantic 2>&1); echo "[exit $?]"
} > "$OUT/clippy.txt" 2>&1
{
  echo '$ rustc -V'; rustc -V
  echo '$ rustc --edition 2024 --crate-type lib --emit=metadata -o reject.rmeta probe_reject.rs'
  rustc --edition 2024 --crate-type lib --emit=metadata -o "$W/reject.rmeta" probe_reject.rs 2>&1; echo "[exit $?]"
} > "$OUT/rustc_reject.txt" 2>&1
# Strip home-directory prefixes from rustc's standard-library paths.
sed -i "s#$HOME/\.rustup#\$RUSTUP_HOME#g; s#$HOME#\$HOME#g" "$OUT"/*.txt
echo "outputs regenerated in $OUT"
