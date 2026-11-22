// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![forbid(unsafe_code)]
use std::sync::{Arc, Barrier, Mutex, Once, RwLock};
use std::thread;
use std::time::Duration;

fn main() {
    let mode = std::env::args().nth(1).expect("expected probe mode argument");
    match mode.as_str() {
        "forget_deadlock" => {
            let m = Arc::new(Mutex::new(0u32));
            let m1 = Arc::clone(&m);
            thread::spawn(move || {
                let g = m1.lock().unwrap();
                core::mem::forget(g);
            })
            .join()
            .unwrap();
            let _g2 = m.lock().unwrap();
            println!("TERMINATED");
        }
        "drop_control" => {
            let m = Arc::new(Mutex::new(0u32));
            let m1 = Arc::clone(&m);
            thread::spawn(move || {
                let g = m1.lock().unwrap();
                drop(g);
            })
            .join()
            .unwrap();
            let _g2 = m.lock().unwrap();
            println!("TERMINATED");
        }
        "panic_unlock_control" => {
            let m = Arc::new(Mutex::new(0u32));
            let m1 = Arc::clone(&m);
            let _ = thread::spawn(move || {
                let _g = m1.lock().unwrap();
                panic!("boom");
            })
            .join();
            let res = m.lock();
            assert!(res.is_err());
            println!("TERMINATED_POISONED");
        }
        "once_reentrant" => {
            static ONCE: Once = Once::new();
            ONCE.call_once(|| {
                ONCE.call_once(|| {});
            });
            println!("TERMINATED");
        }
        "once_control" => {
            static ONCE: Once = Once::new();
            ONCE.call_once(|| {});
            ONCE.call_once(|| {});
            println!("TERMINATED");
        }
        "rwlock_recursive_read_deadlock" => {
            let rw = Arc::new(RwLock::new(0u32));
            let b = Arc::new(Barrier::new(2));
            let rw_w = Arc::clone(&rw);
            let b_w = Arc::clone(&b);
            let r1 = rw.read().unwrap();
            let writer = thread::spawn(move || {
                b_w.wait();
                let _w = rw_w.write().unwrap();
            });
            b.wait();
            thread::sleep(Duration::from_millis(50));
            let _r2 = rw.read().unwrap();
            drop(r1);
            writer.join().unwrap();
            println!("TERMINATED");
        }
        "rwlock_control" => {
            let rw = Arc::new(RwLock::new(0u32));
            let b = Arc::new(Barrier::new(2));
            let rw_w = Arc::clone(&rw);
            let b_w = Arc::clone(&b);
            let r1 = rw.read().unwrap();
            let writer = thread::spawn(move || {
                b_w.wait();
                let _w = rw_w.write().unwrap();
            });
            b.wait();
            thread::sleep(Duration::from_millis(50));
            drop(r1);
            writer.join().unwrap();
            let _r2 = rw.read().unwrap();
            println!("TERMINATED");
        }
        _ => panic!("unknown mode: {mode}"),
    }
}
