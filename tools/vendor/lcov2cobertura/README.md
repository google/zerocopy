# lcov2cobertura

Library for converting lcov info files to cobertura XML format.

Main intention to be a library for [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov). There is also a more performant standalone application replacing the Python based [lcov-to-cobertura-xml](https://github.com/eriwen/lcov-to-cobertura-xml) see [lcov2xml](https://crates.io/crates/lcov2xml).

## Features

- can demangle C++ names
- can demangle rustc names
- merges multiple lcov reports into one
- optionally writes many cobertura XML files
