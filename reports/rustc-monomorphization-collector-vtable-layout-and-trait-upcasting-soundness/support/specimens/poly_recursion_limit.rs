//! Specimen 5a: Polymorphic recursion halted by `check_recursion_limit`.
#![recursion_limit = "16"]

fn poly_rec<T>(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        poly_rec::<(T, u8)>(n - 1)
    }
}

fn main() {
    println!("{}", poly_rec::<u8>(3));
}
