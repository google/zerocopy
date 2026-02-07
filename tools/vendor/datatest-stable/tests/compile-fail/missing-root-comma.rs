datatest_stable::harness! {
    {
        test = my_test,
        pattern = r"^.*(?<!\.skip)\.txt$",
    },
}
