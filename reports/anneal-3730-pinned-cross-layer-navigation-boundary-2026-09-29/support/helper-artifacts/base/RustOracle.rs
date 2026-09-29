#[path = "source.rs"] mod subject;
fn main() { assert_eq!(subject::sum_to(4), 6); }
