#![allow(dead_code)]
macro_rules! annotated {
    ($item:ident, $contract:literal, $limit:literal) => {
        #[doc = $contract]
        pub fn $item(x: u8) -> bool { x < $limit }
        pub const ID: &str = concat!(module_path!(), "::", stringify!($item));
        pub const CONTRACT: &str = $contract;
    };
}
mod intended { annotated!(validate, "anneal:bool-valid-v1", 2); }
// Same basename, different module/expansion and mathematical predicate.
mod decoy { annotated!(validate, "anneal:trit-valid-v1", 3); }
pub use intended::validate as exported_alias;
#[cfg(rename)] mod renamed { annotated!(check, "anneal:bool-valid-v1", 2); }
fn main() {
    let good=(0..=255).filter(|&x| intended::validate(x)).count();
    let bad=(0..=255).filter(|&x| decoy::validate(x)).count();
    let alias=(0..=255).all(|x| exported_alias(x)==intended::validate(x));
    println!("{}|{}|{}|{}", intended::ID,intended::CONTRACT,good,alias);
    println!("{}|{}|{}|{}", decoy::ID,decoy::CONTRACT,bad,decoy::validate(2));
    #[cfg(rename)] println!("{}|{}|{}",renamed::ID,renamed::CONTRACT,renamed::check(2));
}
