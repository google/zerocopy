#![feature(thread_local)]
#![allow(dead_code)]

use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex};
use std::thread;

#[thread_local]
static FAST_TDATA: Cell<u64> = Cell::new(0x1000);

#[thread_local]
static FAST_TBSS: Cell<u64> = Cell::new(0);

struct DropRecorder {
    id: &'static str,
    log: Arc<Mutex<Vec<String>>>,
    late_trigger: bool,
}

impl Drop for DropRecorder {
    fn drop(&mut self) {
        self.log.lock().unwrap().push(format!("drop:{}", self.id));
        if self.id == "T3" {
            let reentrant = TLS_EAGER_DROP.try_with(|opt| opt.borrow().is_some());
            self.log.lock().unwrap().push(format!("reentrant_t3_ok:{}", reentrant.is_ok()));
        }
        if self.late_trigger {
            let log_clone = self.log.clone();
            TLS_LATE_LAZY.with(|cell| {
                *cell.borrow_mut() = Some(DropRecorder {
                    id: "T_LATE",
                    log: log_clone,
                    late_trigger: false,
                });
            });
        }
    }
}

thread_local! {
    static TLS_CONST_NODROP: Cell<u64> = const { Cell::new(7) };
    static TLS_LAZY_NODROP: Cell<Vec<u8>> = Cell::new(Vec::new());
    static TLS_EAGER_DROP: RefCell<Option<DropRecorder>> = const { RefCell::new(None) };
    static TLS_LAZY_T1: RefCell<Option<DropRecorder>> = RefCell::new(None);
    static TLS_LAZY_T2: RefCell<Option<DropRecorder>> = RefCell::new(None);
    static TLS_LATE_LAZY: RefCell<Option<DropRecorder>> = RefCell::new(None);
}

fn main() {
    let mut handles = Vec::new();
    for tid in 0..4u64 {
        handles.push(thread::spawn(move || {
            assert_eq!(FAST_TDATA.get(), 0x1000);
            assert_eq!(FAST_TBSS.get(), 0);
            FAST_TDATA.set(0x1000 + tid + 1);
            FAST_TBSS.set(0x2000 + tid + 1);
            TLS_CONST_NODROP.with(|c| {
                assert_eq!(c.get(), 7);
                c.set(70 + tid);
            });
            TLS_LAZY_NODROP.with(|c| {
                let mut v = c.take();
                assert!(v.is_empty());
                v.push(tid as u8);
                c.set(v);
            });
            (FAST_TDATA.get(), FAST_TBSS.get(), TLS_CONST_NODROP.with(|c| c.get()))
        }));
    }
    let thread_vals: Vec<(u64, u64, u64)> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    assert_eq!(FAST_TDATA.get(), 0x1000);
    assert_eq!(FAST_TBSS.get(), 0);

    let log_a = Arc::new(Mutex::new(Vec::new()));
    let log_a_ref = log_a.clone();
    thread::spawn(move || {
        TLS_LAZY_T1.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T1", log: log_a_ref.clone(), late_trigger: true });
        });
        TLS_LAZY_T2.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T2", log: log_a_ref.clone(), late_trigger: false });
        });
        TLS_EAGER_DROP.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T3", log: log_a_ref.clone(), late_trigger: false });
        });
    })
    .join()
    .unwrap();

    let log_b = Arc::new(Mutex::new(Vec::new()));
    let log_b_ref = log_b.clone();
    thread::spawn(move || {
        TLS_EAGER_DROP.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T3", log: log_b_ref.clone(), late_trigger: false });
        });
        TLS_LAZY_T1.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T1", log: log_b_ref.clone(), late_trigger: false });
        });
        TLS_LAZY_T2.with(|c| {
            *c.borrow_mut() = Some(DropRecorder { id: "T2", log: log_b_ref.clone(), late_trigger: false });
        });
    })
    .join()
    .unwrap();

    let log_unused = Arc::new(Mutex::new(Vec::<String>::new()));
    thread::spawn(|| {
        // Never touches TLS_EAGER_DROP, TLS_LAZY_T1, or TLS_LAZY_T2.
        assert_eq!(TLS_CONST_NODROP.with(|c| c.get()), 7);
    })
    .join()
    .unwrap();

    let events_a = log_a.lock().unwrap().clone();
    let events_b = log_b.lock().unwrap().clone();
    let events_unused = log_unused.lock().unwrap().clone();

    println!(
        "TLS_MT_OK threads={:?} events_a={:?} events_b={:?} events_unused={:?}",
        thread_vals, events_a, events_b, events_unused
    );
    assert_eq!(
        events_a,
        vec![
            "drop:T3",
            "reentrant_t3_ok:false",
            "drop:T2",
            "drop:T1",
            "drop:T_LATE"
        ]
    );
    assert_eq!(
        events_b,
        vec![
            "drop:T2",
            "drop:T1",
            "drop:T3",
            "reentrant_t3_ok:false"
        ]
    );
    assert!(events_unused.is_empty());
}
