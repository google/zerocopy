#![feature(test)]

extern crate nested;
extern crate test;

use nested::Nested;
use test::Bencher;

/// A function which reads src/lib.rs and return a String.
///
/// Note:
/// It is for benchmarking purpose where we want to remove IO.
/// In general, you don't want to return a whole String but you prefer
/// working with a Read or BufRead directly.
fn src_lib() -> String {
    use std::io::{BufReader, Read};
    let mut file = BufReader::new(::std::fs::File::open("src/lib.rs").unwrap());
    let mut res = String::new();
    file.read_to_string(&mut res).unwrap();
    res
}

#[bench]
fn bench_vec_string(b: &mut Bencher) {
    let src = src_lib();
    b.iter(|| {
        let words = src
            .split_whitespace()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        assert!(words.len() > 1000)
    });
}

#[bench]
fn bench_nested_string(b: &mut Bencher) {
    let src = src_lib();
    b.iter(|| {
        let words = src.split_whitespace().collect::<Nested<String>>();
        assert!(words.len() > 1000)
    });
}

#[bench]
fn bench_vec_string_iter(b: &mut Bencher) {
    let src = src_lib();
    b.iter(|| {
        let words = src
            .split_whitespace()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        assert!(words.len() > 1000);
        let words_with_a = words.iter().filter(|w| w.contains('a')).count();
        assert!(words_with_a > 100)
    });
}

#[bench]
fn bench_nested_string_iter(b: &mut Bencher) {
    let src = src_lib();
    b.iter(|| {
        let words = src.split_whitespace().collect::<Nested<String>>();
        assert!(words.len() > 1000);
        let words_with_a = words.iter().filter(|w| w.contains('a')).count();
        assert!(words_with_a > 100)
    });
}
