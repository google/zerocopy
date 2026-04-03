datatest_stable::harness! {
    { root = "tests/files", pattern = r"^.*(?<!\.skip)\.txt$" }
}
