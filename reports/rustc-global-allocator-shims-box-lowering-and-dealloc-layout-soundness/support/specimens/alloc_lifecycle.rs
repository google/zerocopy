//! Allocation-accounting specimen for `Box` and `Vec` lifecycles.
//!
//! A `#[global_allocator]` wraps `std::alloc::System`, records every call it receives in a
//! fixed-size static event log (so the recorder itself never allocates), and keeps a table of live
//! blocks so that every `dealloc` can be checked against the `(size, align)` of the matching
//! `alloc`. Each scenario below runs inside a recording window and prints one JSON object.
//!
//! Build (the probe script does this at several optimization levels):
//!
//!     rustc --edition 2021 -C opt-level=0 -C panic=unwind alloc_lifecycle.rs
//!
//! Types with alignment 64 are used for the measured values so that their layouts cannot be
//! confused with allocations made by the panic runtime (which uses alignments of at most 16).

#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::ptr::addr_of_mut;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};

// ---------------------------------------------------------------------------------------------
// The recording allocator.
// ---------------------------------------------------------------------------------------------

const KIND_ALLOC: usize = 1;
const KIND_DEALLOC: usize = 2;
const KIND_REALLOC: usize = 3;
const KIND_ALLOC_ZEROED: usize = 4;

const LOG_CAP: usize = 2048;
const LIVE_CAP: usize = 4096;

/// Requests of at least this many bytes are refused (a null pointer is returned) without being
/// forwarded to the system allocator. This gives a deterministic allocation failure.
const REFUSE_FROM: usize = 1 << 40;

#[allow(clippy::declare_interior_mutable_const)]
const ZERO: AtomicUsize = AtomicUsize::new(0);

static RECORDING: AtomicBool = AtomicBool::new(false);
static LOG_LEN: AtomicUsize = AtomicUsize::new(0);
static LOG_KIND: [AtomicUsize; LOG_CAP] = [ZERO; LOG_CAP];
static LOG_SIZE: [AtomicUsize; LOG_CAP] = [ZERO; LOG_CAP];
static LOG_ALIGN: [AtomicUsize; LOG_CAP] = [ZERO; LOG_CAP];
static LOG_ADDR: [AtomicUsize; LOG_CAP] = [ZERO; LOG_CAP];
/// For `realloc`: the new size. For a refused request: `usize::MAX`.
static LOG_EXTRA: [AtomicUsize; LOG_CAP] = [ZERO; LOG_CAP];

static LIVE_ADDR: [AtomicUsize; LIVE_CAP] = [ZERO; LIVE_CAP];
static LIVE_SIZE: [AtomicUsize; LIVE_CAP] = [ZERO; LIVE_CAP];
static LIVE_ALIGN: [AtomicUsize; LIVE_CAP] = [ZERO; LIVE_CAP];

/// Deallocations whose `(size, align)` differed from the recorded allocation.
static LAYOUT_MISMATCHES: AtomicUsize = AtomicUsize::new(0);
/// Deallocations of an address that is not in the live table.
static UNKNOWN_FREES: AtomicUsize = AtomicUsize::new(0);
/// Calls that arrived with a zero size.
static ZERO_SIZE_CALLS: AtomicUsize = AtomicUsize::new(0);
/// Calls that arrived with an alignment that is not a power of two.
static BAD_ALIGN_CALLS: AtomicUsize = AtomicUsize::new(0);
/// Calls whose size, rounded up to the alignment, exceeds `isize::MAX`.
static OVERSIZE_CALLS: AtomicUsize = AtomicUsize::new(0);
static TABLE_OVERFLOWS: AtomicUsize = AtomicUsize::new(0);

struct Recorder;

fn log(kind: usize, size: usize, align: usize, addr: usize, extra: usize) {
    if !RECORDING.load(SeqCst) {
        return;
    }
    let i = LOG_LEN.fetch_add(1, SeqCst);
    if i < LOG_CAP {
        LOG_KIND[i].store(kind, SeqCst);
        LOG_SIZE[i].store(size, SeqCst);
        LOG_ALIGN[i].store(align, SeqCst);
        LOG_ADDR[i].store(addr, SeqCst);
        LOG_EXTRA[i].store(extra, SeqCst);
    }
}

fn check_request(size: usize, align: usize) {
    if size == 0 {
        ZERO_SIZE_CALLS.fetch_add(1, SeqCst);
    }
    if !align.is_power_of_two() {
        BAD_ALIGN_CALLS.fetch_add(1, SeqCst);
    } else if size > (isize::MAX as usize + 1) - align {
        OVERSIZE_CALLS.fetch_add(1, SeqCst);
    }
}

fn live_insert(addr: usize, size: usize, align: usize) {
    for i in 0..LIVE_CAP {
        if LIVE_ADDR[i].compare_exchange(0, addr, SeqCst, SeqCst).is_ok() {
            LIVE_SIZE[i].store(size, SeqCst);
            LIVE_ALIGN[i].store(align, SeqCst);
            return;
        }
    }
    TABLE_OVERFLOWS.fetch_add(1, SeqCst);
}

fn live_remove(addr: usize, size: usize, align: usize) {
    for i in 0..LIVE_CAP {
        if LIVE_ADDR[i].load(SeqCst) == addr {
            if LIVE_SIZE[i].load(SeqCst) != size || LIVE_ALIGN[i].load(SeqCst) != align {
                LAYOUT_MISMATCHES.fetch_add(1, SeqCst);
            }
            LIVE_ADDR[i].store(0, SeqCst);
            return;
        }
    }
    UNKNOWN_FREES.fetch_add(1, SeqCst);
}

unsafe impl GlobalAlloc for Recorder {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        check_request(layout.size(), layout.align());
        if layout.size() >= REFUSE_FROM {
            log(KIND_ALLOC, layout.size(), layout.align(), 0, usize::MAX);
            return std::ptr::null_mut();
        }
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            live_insert(p as usize, layout.size(), layout.align());
        }
        log(KIND_ALLOC, layout.size(), layout.align(), p as usize, 0);
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        check_request(layout.size(), layout.align());
        live_remove(ptr as usize, layout.size(), layout.align());
        log(KIND_DEALLOC, layout.size(), layout.align(), ptr as usize, 0);
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        check_request(layout.size(), layout.align());
        if layout.size() >= REFUSE_FROM {
            log(KIND_ALLOC_ZEROED, layout.size(), layout.align(), 0, usize::MAX);
            return std::ptr::null_mut();
        }
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            live_insert(p as usize, layout.size(), layout.align());
        }
        log(KIND_ALLOC_ZEROED, layout.size(), layout.align(), p as usize, 0);
        p
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        check_request(layout.size(), layout.align());
        check_request(new_size, layout.align());
        if new_size >= REFUSE_FROM {
            log(KIND_REALLOC, layout.size(), layout.align(), ptr as usize, usize::MAX);
            return std::ptr::null_mut();
        }
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            live_remove(ptr as usize, layout.size(), layout.align());
            live_insert(p as usize, new_size, layout.align());
        }
        log(KIND_REALLOC, layout.size(), layout.align(), ptr as usize, new_size);
        p
    }
}

#[global_allocator]
static GLOBAL: Recorder = Recorder;

// ---------------------------------------------------------------------------------------------
// Measured types.
// ---------------------------------------------------------------------------------------------

const TAGS: usize = 64;
static DROPS: [AtomicUsize; TAGS] = [ZERO; TAGS];

/// Size 64, alignment 64, with a destructor that counts how often each tag is dropped.
#[repr(align(64))]
struct Counted {
    tag: usize,
    pad: [u64; 7],
}

impl Counted {
    #[inline(never)]
    fn new(tag: usize) -> Counted {
        Counted { tag, pad: [tag as u64; 7] }
    }
}

impl Drop for Counted {
    fn drop(&mut self) {
        DROPS[self.tag].fetch_add(1, SeqCst);
    }
}

/// Size 128, alignment 64. It has drop glue (its fields do) but no `Drop` implementation of its
/// own, so its fields can be moved out individually.
struct Pair {
    first: Counted,
    second: Counted,
}

impl Pair {
    #[inline(never)]
    fn new(a: usize, b: usize) -> Pair {
        Pair { first: Counted::new(a), second: Counted::new(b) }
    }
}

/// A zero-sized type with alignment 64.
#[repr(align(64))]
struct Zst64;

trait Describe {
    fn tag_sum(&self) -> usize;
}

impl Describe for Pair {
    fn tag_sum(&self) -> usize {
        self.first.tag + self.second.tag
    }
}

impl Describe for Zst64 {
    fn tag_sum(&self) -> usize {
        0
    }
}

#[inline(never)]
fn maybe_panic(yes: bool) {
    if black_box(yes) {
        panic!("deliberate panic");
    }
}

#[inline(never)]
fn make_or_panic(yes: bool) -> Pair {
    maybe_panic(yes);
    Pair::new(60, 61)
}

// ---------------------------------------------------------------------------------------------
// Recording windows and JSON output.
// ---------------------------------------------------------------------------------------------

fn window_begin() {
    LOG_LEN.store(0, SeqCst);
    for d in DROPS.iter() {
        d.store(0, SeqCst);
    }
    RECORDING.store(true, SeqCst);
}

fn kind_name(k: usize) -> &'static str {
    match k {
        KIND_ALLOC => "alloc",
        KIND_DEALLOC => "dealloc",
        KIND_REALLOC => "realloc",
        KIND_ALLOC_ZEROED => "alloc_zeroed",
        _ => "?",
    }
}

/// Closes the recording window. Scenarios call this before they format anything, because
/// formatting allocates.
fn window_stop() {
    RECORDING.store(false, SeqCst);
}

/// Prints one JSON object for the window that was just closed. Addresses are replaced by small
/// per-window ordinals so that the output is stable across runs.
fn report(name: &str, extra: &[(&str, String)]) {
    assert!(!RECORDING.load(SeqCst), "report() called with the window still open");
    let n = LOG_LEN.load(SeqCst).min(LOG_CAP);
    let mut addrs: Vec<usize> = Vec::new();
    let mut events = String::new();
    let mut a64 = 0usize;
    let mut d64 = 0usize;
    let mut a_other = 0usize;
    let mut d_other = 0usize;
    let mut refused = 0usize;
    for i in 0..n {
        let kind = LOG_KIND[i].load(SeqCst);
        let size = LOG_SIZE[i].load(SeqCst);
        let align = LOG_ALIGN[i].load(SeqCst);
        let addr = LOG_ADDR[i].load(SeqCst);
        let ex = LOG_EXTRA[i].load(SeqCst);
        let ordinal = if addr == 0 {
            -1isize
        } else if let Some(p) = addrs.iter().position(|a| *a == addr) {
            p as isize
        } else {
            addrs.push(addr);
            (addrs.len() - 1) as isize
        };
        let is_refused = ex == usize::MAX;
        if is_refused {
            refused += 1;
        }
        match (kind, align == 64) {
            (KIND_ALLOC | KIND_ALLOC_ZEROED, true) if !is_refused => a64 += 1,
            (KIND_DEALLOC, true) => d64 += 1,
            (KIND_ALLOC | KIND_ALLOC_ZEROED, false) if !is_refused => a_other += 1,
            (KIND_DEALLOC, false) => d_other += 1,
            _ => {}
        }
        if !events.is_empty() {
            events.push(',');
        }
        events.push_str(&format!(
            "{{\"op\":\"{}\",\"size\":{},\"align\":{},\"block\":{},\"refused\":{}{}}}",
            kind_name(kind),
            size,
            align,
            ordinal,
            is_refused,
            if kind == KIND_REALLOC && !is_refused { format!(",\"new_size\":{}", ex) } else { String::new() },
        ));
    }
    let mut drops = String::new();
    for (tag, d) in DROPS.iter().enumerate() {
        let c = d.load(SeqCst);
        if c != 0 {
            if !drops.is_empty() {
                drops.push(',');
            }
            drops.push_str(&format!("\"{}\":{}", tag, c));
        }
    }
    let mut ex = String::new();
    for (k, v) in extra {
        ex.push_str(&format!(",\"{}\":{}", k, v));
    }
    println!(
        "{{\"scenario\":\"{}\",\"align64_allocs\":{},\"align64_deallocs\":{},\"other_allocs\":{},\"other_deallocs\":{},\"refused\":{},\"drops_by_tag\":{{{}}},\"events\":[{}]{}}}",
        name, a64, d64, a_other, d_other, refused, drops, events, ex
    );
}

fn caught<F: FnOnce()>(f: F) -> bool {
    catch_unwind(AssertUnwindSafe(f)).is_err()
}

// ---------------------------------------------------------------------------------------------
// Scenarios.
// ---------------------------------------------------------------------------------------------

fn zst_box_unit() {
    window_begin();
    let b = black_box(Box::new(()));
    let addr = &*b as *const () as usize;
    drop(b);
    window_stop();
    report("zst_box_unit", &[("addr", addr.to_string())]);
}

fn zst_box_align64() {
    window_begin();
    let b = black_box(Box::new(Zst64));
    let addr = &*b as *const Zst64 as usize;
    let c = black_box(Box::new([0u64; 0]));
    let addr8 = c.as_ptr() as usize;
    let d: Box<dyn Describe> = black_box(Box::new(Zst64));
    let dyn_addr = &*d as *const dyn Describe as *const u8 as usize;
    drop(b);
    drop(c);
    drop(d);
    window_stop();
    report(
        "zst_box_align64",
        &[("addr_align64", addr.to_string()), ("addr_align8", addr8.to_string()), ("dyn_addr", dyn_addr.to_string())],
    );
}

fn zst_vec_unit_capacity() {
    window_begin();
    let mut v = black_box(Vec::<()>::with_capacity(1_000_000));
    let cap = v.capacity();
    let addr = v.as_ptr() as usize;
    for _ in 0..1_000_000 {
        v.push(());
    }
    let len = black_box(&v).len();
    v.shrink_to_fit();
    drop(v);
    window_stop();
    report(
        "zst_vec_unit_capacity",
        &[("capacity_is_usize_max", (cap == usize::MAX).to_string()), ("addr", addr.to_string()), ("len", len.to_string())],
    );
}

fn sized_box_roundtrip() {
    window_begin();
    let b = black_box(Box::new(Pair::new(1, 2)));
    let aligned = (&*b as *const Pair as usize) % 64 == 0;
    drop(b);
    window_stop();
    report("sized_box_roundtrip", &[("aligned_to_64", aligned.to_string())]);
}

fn box_new_uninit_dropped() {
    window_begin();
    let b = black_box(Box::<Pair>::new_uninit());
    drop(b);
    window_stop();
    report("box_new_uninit_dropped", &[]);
}

fn box_new_uninit_mid_init_panic() {
    window_begin();
    let panicked = caught(|| {
        let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
        unsafe { addr_of_mut!((*b.as_mut_ptr()).first).write(Counted::new(3)) };
        black_box(&b);
        maybe_panic(true);
        unsafe { addr_of_mut!((*b.as_mut_ptr()).second).write(Counted::new(4)) };
        let b: Box<Pair> = unsafe { b.assume_init() };
        drop(b);
    });
    window_stop();
    report("box_new_uninit_mid_init_panic", &[("panicked", panicked.to_string())]);
}

fn box_new_uninit_completed() {
    window_begin();
    let panicked = caught(|| {
        let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
        unsafe { addr_of_mut!((*b.as_mut_ptr()).first).write(Counted::new(5)) };
        black_box(&b);
        maybe_panic(false);
        unsafe { addr_of_mut!((*b.as_mut_ptr()).second).write(Counted::new(6)) };
        let b: Box<Pair> = unsafe { b.assume_init() };
        drop(b);
    });
    window_stop();
    report("box_new_uninit_completed", &[("panicked", panicked.to_string())]);
}

fn box_write_uninit() {
    window_begin();
    let b: Box<Pair> = Box::write(Box::new_uninit(), Pair::new(7, 8));
    drop(black_box(b));
    window_stop();
    report("box_write_uninit", &[]);
}

fn box_partial_move_then_panic_forget() {
    window_begin();
    let panicked = caught(|| {
        let b = black_box(Box::new(Pair::new(10, 11)));
        let first = b.first;
        std::mem::forget(first);
        maybe_panic(true);
    });
    window_stop();
    report("box_partial_move_then_panic_forget", &[("panicked", panicked.to_string())]);
}

fn box_partial_move_then_panic_keep() {
    window_begin();
    let panicked = caught(|| {
        let b = black_box(Box::new(Pair::new(12, 13)));
        let first = b.first;
        maybe_panic(true);
        drop(first);
    });
    window_stop();
    report("box_partial_move_then_panic_keep", &[("panicked", panicked.to_string())]);
}

fn box_partial_move_no_panic() {
    window_begin();
    let panicked = caught(|| {
        let b = black_box(Box::new(Pair::new(14, 15)));
        let first = b.first;
        maybe_panic(false);
        drop(first);
    });
    window_stop();
    report("box_partial_move_no_panic", &[("panicked", panicked.to_string())]);
}

fn box_move_both_fields_then_panic() {
    window_begin();
    let panicked = caught(|| {
        let b = black_box(Box::new(Pair::new(16, 17)));
        let first = b.first;
        let second = b.second;
        maybe_panic(true);
        drop(first);
        drop(second);
    });
    window_stop();
    report("box_move_both_fields_then_panic", &[("panicked", panicked.to_string())]);
}

fn box_full_move_out() {
    window_begin();
    let sum = {
        let b = black_box(Box::new(Pair::new(18, 19)));
        let p: Pair = *b;
        let sum = black_box(&p).tag_sum();
        drop(p);
        sum
        // `b` (now holding no value) goes out of scope here.
    };
    window_stop();
    report("box_full_move_out", &[("tag_sum", sum.to_string())]);
}

fn box_argument_panics_before_allocation() {
    window_begin();
    let panicked = caught(|| {
        let b = Box::new(make_or_panic(true));
        drop(black_box(b));
    });
    window_stop();
    report("box_argument_panics_before_allocation", &[("panicked", panicked.to_string())]);
}

fn vec_macro_literal() {
    window_begin();
    let v = black_box(vec![Counted::new(20), Counted::new(21), Counted::new(22)]);
    let cap = v.capacity();
    drop(v);
    window_stop();
    report("vec_macro_literal", &[("capacity", cap.to_string())]);
}

fn boxed_slice_and_dyn_dealloc() {
    window_begin();
    let s: Box<[Counted]> = black_box(vec![Counted::new(23), Counted::new(24), Counted::new(25)].into_boxed_slice());
    drop(s);
    let d: Box<dyn Describe> = black_box(Box::new(Pair::new(26, 27)));
    let sum = d.tag_sum();
    drop(d);
    window_stop();
    report("boxed_slice_and_dyn_dealloc", &[("tag_sum", sum.to_string())]);
}

fn box_leak() {
    window_begin();
    let r: &'static mut Pair = Box::leak(black_box(Box::new(Pair::new(28, 29))));
    let sum = r.tag_sum();
    window_stop();
    report("box_leak", &[("tag_sum", sum.to_string())]);
}

fn box_into_raw_from_raw() {
    window_begin();
    let raw: *mut Pair = Box::into_raw(black_box(Box::new(Pair::new(30, 31))));
    let b = unsafe { Box::from_raw(black_box(raw)) };
    drop(b);
    window_stop();
    report("box_into_raw_from_raw", &[]);
}

fn vec_growth_realloc() {
    window_begin();
    let mut v: Vec<Counted> = Vec::new();
    for i in 0..5 {
        v.push(Counted::new(32 + i));
        black_box(&v);
    }
    drop(v);
    window_stop();
    report("vec_growth_realloc", &[]);
}

fn vec_try_reserve_refused() {
    window_begin();
    let mut v: Vec<u8> = Vec::new();
    let r = v.try_reserve_exact(REFUSE_FROM * 2);
    let is_err = r.is_err();
    let cap = v.capacity();
    let too_big = v.try_reserve_exact(usize::MAX / 2 + 1).is_err();
    window_stop();
    report(
        "vec_try_reserve_refused",
        &[("is_err", is_err.to_string()), ("capacity_after", cap.to_string()), ("over_isize_max_is_err", too_big.to_string())],
    );
}

/// A heap round trip whose value never escapes. Nothing pins the allocation, so an optimizing
/// build is allowed to remove it.
#[inline(never)]
fn unpinned_roundtrip(seed: u64) -> u64 {
    let b = Box::new([seed; 8]);
    let mut s = 0u64;
    for x in b.iter() {
        s = s.wrapping_add(*x);
    }
    s
}

fn unpinned_box_roundtrip() {
    window_begin();
    let s = unpinned_roundtrip(black_box(3));
    window_stop();
    report("unpinned_box_roundtrip", &[("sum", s.to_string())]);
}

fn main() {
    // A silent hook, installed before any window opens, so that the default hook's own
    // allocations do not appear in the logs.
    std::panic::set_hook(Box::new(|_| {}));
    // Force the standard output buffer into existence outside any window.
    println!("{{\"scenario\":\"_start\"}}");

    zst_box_unit();
    zst_box_align64();
    zst_vec_unit_capacity();
    sized_box_roundtrip();
    box_new_uninit_dropped();
    box_new_uninit_mid_init_panic();
    box_new_uninit_completed();
    box_write_uninit();
    box_partial_move_then_panic_forget();
    box_partial_move_then_panic_keep();
    box_partial_move_no_panic();
    box_move_both_fields_then_panic();
    box_full_move_out();
    box_argument_panics_before_allocation();
    vec_macro_literal();
    boxed_slice_and_dyn_dealloc();
    box_leak();
    box_into_raw_from_raw();
    vec_growth_realloc();
    vec_try_reserve_refused();
    unpinned_box_roundtrip();

    println!(
        "{{\"scenario\":\"_totals\",\"layout_mismatches\":{},\"unknown_frees\":{},\"zero_size_calls\":{},\"bad_align_calls\":{},\"oversize_calls\":{},\"table_overflows\":{}}}",
        LAYOUT_MISMATCHES.load(SeqCst),
        UNKNOWN_FREES.load(SeqCst),
        ZERO_SIZE_CALLS.load(SeqCst),
        BAD_ALIGN_CALLS.load(SeqCst),
        OVERSIZE_CALLS.load(SeqCst),
        TABLE_OVERFLOWS.load(SeqCst)
    );
}
