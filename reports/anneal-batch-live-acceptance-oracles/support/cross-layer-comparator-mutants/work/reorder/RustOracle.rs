#[path = "source.rs"] mod subject;
fn main() {
  assert_eq!(subject::inc(0), 1);
  assert_eq!(subject::twice(0), 2);
  assert_eq!(subject::choose(0), 3);
}
