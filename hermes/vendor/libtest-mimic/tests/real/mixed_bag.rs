#![feature(test)]

extern crate test;


#[test]
fn cat() {}

#[test]
fn dog() {
    panic!("was not a good boy");
}

#[test]
#[ignore]
fn frog() {}

#[test]
#[ignore]
fn owl() {
    panic!("broke neck");
}


#[bench]
fn red(b: &mut test::Bencher) {
    b.iter(|| std::thread::sleep(std::time::Duration::from_millis(50)));
}

#[bench]
fn blue(_: &mut test::Bencher) {
    panic!("sky fell down");
}

#[bench]
#[ignore]
fn purple(b: &mut test::Bencher) {
    b.iter(|| {});
}

#[bench]
#[ignore]
fn cyan(_: &mut test::Bencher) {
    panic!("not creative enough");
}
