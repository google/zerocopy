mod subject { include!("lib.rs"); }
fn main() {
    let start = std::time::Instant::now();
    for byte in 0..256 {
        let expected = if byte <= 1 { 1 + byte } else { 0 };
        assert_eq!(subject::validate_bool(byte), expected);
    }
    for first in 0..256 {
        for second in 0..256 {
            let expected = if first <= 1 && second <= 1 { 1 + 4 * first + 8 * second } else { 0 };
            assert_eq!(subject::validate_pair(first, second), expected);
        }
    }
    assert_eq!(subject::validate_bool(256), 99);
    assert_eq!(subject::validate_pair(256, 0), 99);
    assert_eq!(subject::byte_controls(), 18);
    let layout: Vec<_> = (0..7).map(|field| subject::layout(field)).collect();
    println!("bool=256;pair=65536;controls=18;out_of_domain=2;all_match=true");
    println!("layout={layout:?}");
    println!("case_runtime_ns={}", start.elapsed().as_nanos());
}
