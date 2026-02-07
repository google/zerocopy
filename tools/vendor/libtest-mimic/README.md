# libtest-mimic

[<img alt="CI status of master" src="https://img.shields.io/github/actions/workflow/status/LukasKalbertodt/libtest-mimic/ci.yml?branch=master&label=CI&logo=github&logoColor=white&style=for-the-badge" height="23">](https://github.com/LukasKalbertodt/libtest-mimic/actions?query=workflow%3ACI+branch%3Amaster)
[<img alt="Crates.io Version" src="https://img.shields.io/crates/v/libtest-mimic?logo=rust&style=for-the-badge" height="23">](https://crates.io/crates/libtest-mimic)
[<img alt="docs.rs" src="https://img.shields.io/crates/v/libtest-mimic?color=blue&label=docs&style=for-the-badge" height="23">](https://docs.rs/libtest-mimic)

Write your own test harness that looks and behaves like the built-in test harness (used by `rustc --test`)!

This is a simple and small testing framework that mimics the original `libtest`.
That means: all output looks pretty much like `cargo test` and most CLI arguments are understood and used.
With that plumbing work out of the way, your test runner can focus on the actual testing.

See [**the documentation**](https://docs.rs/libtest-mimic) or [the `examples/` folder](/examples) for more information.


<p align="center">
    <img src=".github/readme.png" width="95%"></img>
</p>


---

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
