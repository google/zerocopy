use golden_vertical::{inc, twice, choose};
#[test] fn selected_values() {
    assert_eq!(inc(0), 1);
    assert_eq!(twice(0), 2);
    assert_eq!(choose(0), 3);
}
