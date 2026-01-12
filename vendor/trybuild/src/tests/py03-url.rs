test_normalize! {
    DIR="/pyo3"
    WORKSPACE="/pyo3"
"
error: `async fn` is not yet supported for Python functions.

Additional crates such as `pyo3-asyncio` can be used to integrate async Rust and Python. For more information, see https://github.com/PyO3/pyo3/issues/1632
  --> tests/ui/invalid_pyfunctions.rs:10:1
   |
10 | async fn async_function() {}
   | ^^^^^
" "
error: `async fn` is not yet supported for Python functions.

Additional crates such as `pyo3-asyncio` can be used to integrate async Rust and Python. For more information, see https://github.com/PyO3/pyo3/issues/1632
  --> tests/ui/invalid_pyfunctions.rs:10:1
   |
10 | async fn async_function() {}
   | ^^^^^
"}
