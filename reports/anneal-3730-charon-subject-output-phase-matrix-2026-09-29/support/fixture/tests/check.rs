fn local_alpha(x: u32) -> u32 { x.wrapping_add(1) }
#[test]
fn check_alpha() { assert_eq!(local_alpha(3), 4); }
