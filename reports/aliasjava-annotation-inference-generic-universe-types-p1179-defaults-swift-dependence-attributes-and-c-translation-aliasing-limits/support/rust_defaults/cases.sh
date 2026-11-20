#!/usr/bin/env bash
# Each case is compiled as a library with the installed rustc; prints ACCEPT or the error codes.
# Usage: bash cases.sh   (requires rustc on PATH)
set -u
run() { # name edition source
  printf '%s\n' "$3" > "/tmp/rd_$1.rs"
  out=$(rustc --edition "$2" --crate-type lib --emit=metadata -o "/tmp/rd_$1.rmeta" "/tmp/rd_$1.rs" 2>&1)
  if [ $? -eq 0 ]; then res=ACCEPT; else codes=$(printf '%s' "$out" | grep -oE 'error\[E[0-9]+\]' | sort -u | tr '\n' ' '); res="REJECT ${codes:-(no-code)}"; fi
  first=$(printf '%s' "$out" | grep -m1 -E '^error' | cut -c1-110)
  printf '%-34s ed%s  %s  %s\n' "$1" "$2" "$res" "$first"
}
run A1_elided_self_returns_other   2021 'pub struct S(String); impl S { pub fn pick(&self, o: &str) -> &str { o } }'
run A2_annotated_returns_other     2021 "pub struct S(String); impl S { pub fn pick<'a>(&self, o: &'a str) -> &'a str { o } }"
run B1_two_inputs_elided_output    2021 'pub fn longest(x: &str, y: &str) -> &str { if x.len() > y.len() { x } else { y } }'
run B2_two_inputs_annotated        2021 "pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { if x.len() > y.len() { x } else { y } }"
run C1_box_dyn_default_static      2021 "pub fn mk<'a>(x: &'a u8) -> Box<dyn Fn() -> u8> { Box::new(move || *x) }"
run C2_box_dyn_explicit_bound      2021 "pub fn mk<'a>(x: &'a u8) -> Box<dyn Fn() -> u8 + 'a> { Box::new(move || *x) }"
run D1_rpit_capture_2021           2021 'pub fn it(v: &Vec<u8>) -> impl Iterator<Item = u8> { v.iter().copied() }'
run D2_rpit_capture_2024           2024 'pub fn it(v: &Vec<u8>) -> impl Iterator<Item = u8> { v.iter().copied() }'
run D3_rpit_use_bound_2021         2021 "pub fn it<'a>(v: &'a Vec<u8>) -> impl Iterator<Item = u8> + use<'a> { v.iter().copied() }"
run E1_closure_ref_return          2021 'pub fn g() { let f = |x: &u8| -> &u8 { x }; let a = 1u8; let _ = f(&a); }'
run E2_fn_ref_return               2021 'pub fn f(x: &u8) -> &u8 { x }'
run F1_impl_header_elided          2021 'pub trait R { fn r(&self) -> u8; } pub struct B<T>(T); impl R for B<&u8> { fn r(&self) -> u8 { *self.0 } }'
run G1_static_elided_const         2021 'pub const S: &str = "x"; pub static T: &[u8] = b"y";'
