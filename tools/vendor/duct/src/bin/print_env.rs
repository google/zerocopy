#![deny(warnings)]

fn main() {
    let var_name = std::env::args().nth(1).unwrap();

    if let Some(value) = std::env::var_os(var_name) {
        println!("{}", value.to_string_lossy());
    }
}
