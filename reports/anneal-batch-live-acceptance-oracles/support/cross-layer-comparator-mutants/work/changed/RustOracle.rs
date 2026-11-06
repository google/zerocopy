#[path = "source.rs"] mod subject;
fn main() {
  assert_eq!(subject::inc(0), 2);
  assert_eq!(subject::twice(0), 4);
  assert_eq!(subject::choose(0), 5);
}
