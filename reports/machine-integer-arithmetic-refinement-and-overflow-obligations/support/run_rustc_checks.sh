#!/bin/bash
# Compile and run rustc_semantics_checks.rs under four rustc profiles, then check
# compile-time rejections. Needs a nightly rustc (the program uses the unstable
# `exact_bitshifts` feature for one line). Build products go to a temporary directory.
set -u
SRC="$(cd "$(dirname "$0")" && pwd)/rustc_semantics_checks.rs"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cd "$WORK"
rustc --version --verbose | head -3
run() { local name=$1; shift; rustc --edition 2021 "$@" -o "bin_$name" "$SRC" 2>"err_$name.txt" && { echo "=== profile: $name ($*)"; "./bin_$name"; } || { echo "=== profile $name FAILED to compile"; cat "err_$name.txt"; }; }
run debug -C opt-level=0 -C debug-assertions=yes
run release -C opt-level=3
run release_oc -C opt-level=3 -C overflow-checks=yes
run debug_nooc -C opt-level=0 -C debug-assertions=yes -C overflow-checks=no
echo "=== compile-time checks"
printf 'fn main(){ let x: i8 = 128_i8; println!("{}", x); }\n' > ce1.rs
printf 'fn main(){ let x: u8 = 256; println!("{}", x); }\n' > ce2.rs
printf 'fn main(){ let x = -1u8; println!("{}", x); }\n' > ce3.rs
printf 'fn main(){ let x: i8 = -129_i8; println!("{}", x); }\n' > ce4.rs
printf 'fn main(){ let x: i8 = -(-128_i8); println!("{}", x); }\n' > ce5.rs
for f in ce1 ce2 ce3 ce4 ce5; do echo "--- $f: $(cat $f.rs)"; rustc --edition 2021 -o bin_$f $f.rs 2>&1 | grep -E "^error|overflowing_literals|E0600|arithmetic_overflow" | head -4; [ -x bin_$f ] && echo "compiled; runs -> $(./bin_$f 2>&1 | head -1)"; done
exit 0
