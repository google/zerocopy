#!/bin/sh
# Probe of OasisLMF/ktools at 4a7506c74a22593b1fd7aa32b32b91c44509be01.
# Usage: sh ktools_probe.sh /path/to/built/ktools-source-tree /tmp/scratchdir
# The ktools tree must already be built (autoreconf -fi; ./configure --disable-parquet; make).
# Steps:
#   (1) timed example pipeline eve|getmodel|gulcalc|fmcalc at several sample sizes;
#   (2) quadratic-interpolation stress: damage-bin "interpolation" moved to 10% of each
#       bin width (still inside [bin_from, bin_to], so validatedamagebin only WARNS),
#       then count non-finite ground-up losses written by the real gulcalc binary.
set -e
K="$1"; W="$2"
[ -x "$K/src/gulcalc/gulcalc" ] || { echo "build ktools first"; exit 2; }
rm -rf "$W"; mkdir -p "$W"; cp -r "$K/examples/static" "$K/examples/input" "$W/"
cd "$W"
B="$K/src"
echo "== (1) timing: eve -n 1 1 | getmodel | gulcalc -S<n> -L0 -a0 -i - | fmcalc"
for S in 10 100 1000; do
  /usr/bin/time -f "S=$S wall_s=%e maxrss_kB=%M" sh -c \
    "$B/eve/eve -n 1 1 | $B/getmodel/getmodel | $B/gulcalc/gulcalc -S$S -L0 -a0 -i - | $B/fmcalc/fmcalc > fm_S$S.bin" 2>&1 | tail -1
  /usr/bin/time -f "S=$S gul-only wall_s=%e maxrss_kB=%M" sh -c \
    "$B/eve/eve -n 1 1 | $B/getmodel/getmodel | $B/gulcalc/gulcalc -S$S -L0 -a0 -i - > gul_S$S.bin" 2>&1 | tail -1
  ls -l gul_S$S.bin fm_S$S.bin | awk '{print $5, $9}'
done
echo "== (2) baseline: count non-finite losses with shipped damage bins (interpolation at bin centre)"
$B/eve/eve -n 1 1 | $B/getmodel/getmodel | $B/gulcalc/gulcalc -S100 -L0 -a0 -i - | $B/gultocsv/gultocsv > gul_base.csv
echo "rows: $(wc -l < gul_base.csv)  nonfinite: $(grep -ci 'nan\|inf' gul_base.csv || true)"
echo "== (2) stressed bins: interpolation = bin_from + 0.1*(bin_to-bin_from)"
$B/damagebintocsv/damagebintocsv < static/damage_bin_dict.bin > dbd_orig.csv
python3 - <<'EOF'
rows = open('dbd_orig.csv').read().splitlines()
out = [rows[0]]
for r in rows[1:]:
    i, a, b, m = [s.strip() for s in r.split(',')]
    a, b = float(a), float(b)
    m = a + 0.1 * (b - a) if b > a else b
    out.append(f"{i}, {a:.6f}, {b:.6f}, {m:.6f}")
open('dbd_stress.csv', 'w').write('\n'.join(out) + '\n')
EOF
$B/validatedamagebin/validatedamagebin < dbd_stress.csv > val_out.txt 2>&1 || true
echo "validatedamagebin: ERROR lines=$(grep -c ERROR val_out.txt || true) WARNING lines=$(grep -c WARNING val_out.txt || true)"
$B/damagebintobin/damagebintobin < dbd_stress.csv > static/damage_bin_dict.bin
$B/eve/eve -n 1 1 | $B/getmodel/getmodel | $B/gulcalc/gulcalc -S100 -L0 -a0 -i - | $B/gultocsv/gultocsv > gul_stress.csv
echo "rows: $(wc -l < gul_stress.csv)  nonfinite: $(grep -ci 'nan\|inf' gul_stress.csv || true)"
echo "first non-finite rows (if any):"; grep -i 'nan\|inf' gul_stress.csv | head -5 || true
