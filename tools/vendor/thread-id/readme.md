Thread-ID
=========
Get a unique ID for the current thread in Rust.

[![Crates.io version][crate-img]][crate]
[![Documentation][docs-img]][docs]

For diagnostics and debugging it can often be useful to get an ID that is
different for every thread. [Until Rust 1.14][stdlib-pr], the standard library
did not expose a way to do that, hence this crate.

Example
-------

```rust
use std::thread;
use thread_id;

let handle = thread::spawn(move || {
    println!("spawned thread has id {}", thread_id::get());
});

println!("main thread has id {}", thread_id::get());

handle.join().unwrap();
```

This will print two different numbers.

License
-------
Thread-ID is licensed under either the [Apache 2.0 license][apache2], or the
[MIT license][mit], at your option. It may be used in free software as well as
closed-source applications, both for commercial and non-commercial use under the
conditions given in the license.

Contributing
------------
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache 2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[crate-img]: https://img.shields.io/crates/v/thread-id.svg
[crate]:     https://crates.io/crates/thread-id
[docs-img]:  https://img.shields.io/badge/docs-online-blue.svg
[docs]:      https://docs.rs/thread-id
[stdlib-pr]: https://github.com/rust-lang/rust/pull/36341
[apache2]:   https://www.apache.org/licenses/LICENSE-2.0
[mit]:       https://opensource.org/licenses/MIT
