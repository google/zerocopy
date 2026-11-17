// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone `-C opt-level=0` vs `-O` `thread_local!` stack-overflow probe.
//! Demonstrates how a non-`const` 1.8 MB array initializer inside
//! `thread_local!` materializes an eager stack temporary at `-C opt-level=0`
//! that overflows Linux's 2 MiB thread stack (SIGABRT, exit 134), whereas
//! `const { ... }` zero-initialized inline TLS and heap-boxed `Box<[u8; N]>`
//! pass on a 2 MiB stack under both `-O0` and `-O3`.

use std::cell::RefCell;

thread_local! {
    static TLS_BIG_INLINE: RefCell<[u8; 1_800_000]> = const { RefCell::new([0u8; 1_800_000]) };
}
thread_local! {
    static TLS_BIG_EAGER_FN: RefCell<[u8; 1_800_000]> = RefCell::new([1u8; 1_800_000]);
}
thread_local! {
    static TLS_BIG_BOX: RefCell<Option<Box<[u8; 1_800_000]>>> = const { RefCell::new(None) };
}

fn run_on_2mib(name: &str, f: fn() -> u8) -> u8 {
    let val = std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
    println!("{name}: {val}");
    val
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "safe".into());
    if mode == "safe" || mode == "all" {
        assert_eq!(
            run_on_2mib("inline_const_1.8MB", || {
                TLS_BIG_INLINE.with(|c| {
                    c.borrow_mut()[1_700_000] = 42;
                    c.borrow()[1_700_000]
                })
            }),
            42
        );
        assert_eq!(
            run_on_2mib("box_1.8MB", || {
                TLS_BIG_BOX.with(|c| {
                    let mut b = c.borrow_mut();
                    let arr = b.get_or_insert_with(|| {
                        vec![0u8; 1_800_000].into_boxed_slice().try_into().unwrap()
                    });
                    arr[1_700_000] = 42;
                    arr[1_700_000]
                })
            }),
            42
        );
        let default_h = std::thread::spawn(|| {
            TLS_BIG_INLINE.with(|c| {
                c.borrow_mut()[1_700_000] = 42;
                c.borrow()[1_700_000]
            })
        });
        assert_eq!(default_h.join().unwrap(), 42);
        println!("default_2MB_thread_inline: 42");
    }
    if mode == "eager" {
        run_on_2mib("eager_fn_1.8MB", || TLS_BIG_EAGER_FN.with(|c| c.borrow()[1_700_000]));
    }
}
