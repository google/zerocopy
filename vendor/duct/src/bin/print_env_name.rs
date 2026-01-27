#![deny(warnings)]

fn main() {
    let var_value = std::env::args().nth(1).unwrap();

    for (name, value) in std::env::vars() {
        if value == var_value {
            println!("{name}");
        }
    }
}
