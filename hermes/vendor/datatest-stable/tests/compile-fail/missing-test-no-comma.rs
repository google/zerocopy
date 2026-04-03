datatest_stable::harness! {
    { root = "tests/files", test = my_test, pattern = r"^.*(?<!\.skip)\.txt$" }
}
