#![feature(test)]

extern crate test;

use psl::{List, Psl};
use test::Bencher;

const DOMAIN: &[u8] = b"www.example.com";

#[bench]
fn bench_find(b: &mut Bencher) {
    b.iter(|| List.find(DOMAIN.rsplit(|x| *x == b'.')));
}

#[bench]
fn bench_suffix(b: &mut Bencher) {
    b.iter(|| List.suffix(DOMAIN).unwrap());
}

#[bench]
fn bench_domain(b: &mut Bencher) {
    b.iter(|| List.domain(DOMAIN).unwrap());
}
