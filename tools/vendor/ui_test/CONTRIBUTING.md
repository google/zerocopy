## Running the test suite

The test suite is confusing because it itself runs ui-test, and then also uses ui-test to
check that ui-test produces the right results.

Running `cargo test` will automatically update the "inner" `.stderr` and `.stdout` files.

If you only want to check that the output files match and not
update them, use `cargo test -- -- --check`

To bless the "outer" `.stderr` and `.stdout` files, use `cargo test -- -- --bless`.
