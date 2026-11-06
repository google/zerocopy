mod api;
fn main() {
    for byte in 0..=u8::MAX {
        let result = api::checked_bool(std::hint::black_box(byte));
        let expected = match byte { 0 => Some(false), 1 => Some(true), _ => None };
        assert_eq!(result, expected);
    }
    println!("all_native_u8_inputs=256; accepted=2; rejected=254");
}
