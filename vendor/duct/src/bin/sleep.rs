#![deny(warnings)]

fn main() {
    let secs: f32 = std::env::args().nth(1).unwrap().parse().unwrap();
    let millis = (1000f32 * secs) as u64;
    std::thread::sleep(std::time::Duration::from_millis(millis));
}
