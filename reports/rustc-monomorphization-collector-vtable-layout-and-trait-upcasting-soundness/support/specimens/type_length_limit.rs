//! Specimen 5b: Exponential type growth demonstrating `#![type_length_limit]`
//! behavior with default flags (hits `recursion_limit`) vs `-Z enforce-type-length-limit=yes`.
#![type_length_limit = "1024"]

fn exp_blowup<T>(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        exp_blowup::<(T, T)>(n - 1)
    }
}

fn main() {
    println!("{}", exp_blowup::<u8>(3));
}
