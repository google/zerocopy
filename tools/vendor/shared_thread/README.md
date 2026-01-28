# shared_thread.rs [![Actions Status](https://github.com/oconnor663/shared_thread.rs/workflows/tests/badge.svg)](https://github.com/oconnor663/shared_thread.rs/actions) [![crates.io](https://img.shields.io/crates/v/shared_thread.svg)](https://crates.io/crates/shared_thread) [![docs.rs](https://docs.rs/shared_thread/badge.svg)](https://docs.rs/shared_thread)

This crate provides `SharedThread`, a wrapper around
[`std::thread::JoinHandle`](https://doc.rust-lang.org/std/thread/struct.JoinHandle.html)
that lets multiple threads wait on a shared thread and read its output.
