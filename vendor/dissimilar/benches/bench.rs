#![feature(test)]

extern crate test;

use dissimilar::diff;
use std::{fs, io};
use test::Bencher;

#[bench]
fn bench(b: &mut Bencher) -> io::Result<()> {
    let document1 = fs::read_to_string("benches/document1.txt")?;
    let document2 = fs::read_to_string("benches/document2.txt")?;
    b.iter(|| diff(&document1, &document2));
    Ok(())
}
