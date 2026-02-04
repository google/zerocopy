## Running the test suite

Running `cargo test` will automatically update the `.stderr`
and `.stdout` files.

If you only want to check that the output files match and not
update them, use `cargo test -- -- --check`
