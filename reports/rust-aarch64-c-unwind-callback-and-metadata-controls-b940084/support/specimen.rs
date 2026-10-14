// PREPARED ONLY. Do not compile or execute before the parent's ABI/CFI review.
// Then compile and inspect metadata before executing only the positive subject.
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
compile_error!("This specimen requires reviewed macOS aarch64-apple-darwin.");

use std::cell::RefCell;
use std::ffi::{c_char, c_int, c_void, CStr};
use std::panic;
use std::sync::atomic::{AtomicUsize, Ordering};

std::arch::global_asm!(include_str!("bounce.s"), options(raw));

type Callback = extern "C-unwind" fn(u64) -> u64;
unsafe extern "C-unwind" {
    fn anneal_unwind_bounce(callback: Callback, value: u64) -> u64;
    static anneal_unwind_bounce_end: u8;
}

// Opaque context is never dereferenced. FFI declarations transcribed from the
// preserved selected SDK unwind.h/unwind_itanium.h and dlfcn.h.
#[repr(C)]
struct UnwindContext { _opaque: [u8; 0] }
#[repr(C)]
struct DlInfo {
    dli_fname: *const c_char,
    dli_fbase: *mut c_void,
    dli_sname: *const c_char,
    dli_saddr: *mut c_void,
}
unsafe extern "C" {
    fn _Unwind_Backtrace(
        callback: unsafe extern "C" fn(*mut UnwindContext, *mut c_void) -> c_int,
        argument: *mut c_void,
    ) -> c_int;
    fn _Unwind_GetIP(context: *mut UnwindContext) -> usize;
    fn dladdr(address: *const c_void, info: *mut DlInfo) -> c_int;
}

#[derive(Clone, Copy)]
struct Trace { ips: [usize; 64], len: usize, truncated: bool, status: c_int }
impl Trace {
    const fn empty() -> Self { Self { ips: [0; 64], len: 0, truncated: false, status: -1 } }
}
thread_local! { static LAST_TRACE: RefCell<Trace> = const { RefCell::new(Trace::empty()) }; }

// This non-unwinding C callback only writes within a live uniquely borrowed
// Trace supplied synchronously to _Unwind_Backtrace. It never allocates or panics.
unsafe extern "C" fn trace_frame(context: *mut UnwindContext, argument: *mut c_void) -> c_int {
    if context.is_null() || argument.is_null() { return 5; }
    let trace = unsafe { &mut *argument.cast::<Trace>() };
    if let Some(slot) = trace.ips.get_mut(trace.len) {
        *slot = unsafe { _Unwind_GetIP(context) };
        trace.len += 1; // bounded by the successful get_mut above
        0 // _URC_NO_REASON
    } else {
        trace.truncated = true;
        5 // _URC_END_OF_STACK; recorded as truncated, never accepted as full trace
    }
}

#[inline(never)]
fn capture_trace() {
    let mut trace = Trace::empty();
    trace.status = unsafe { _Unwind_Backtrace(trace_frame, (&mut trace as *mut Trace).cast()) };
    LAST_TRACE.with(|last| *last.borrow_mut() = trace);
}

static CALLS: AtomicUsize = AtomicUsize::new(0);
static CALLBACK_DROPS: AtomicUsize = AtomicUsize::new(0);
static OUTER_DROPS: AtomicUsize = AtomicUsize::new(0);
static DROP_ORDER: AtomicUsize = AtomicUsize::new(0);
static EXPECTED_HOOKS: AtomicUsize = AtomicUsize::new(0);
const VALUE: u64 = 0x1122_3344_5566_7788;
const MARKER: u64 = 0x4534_305f_554e_5744;

#[derive(Clone, Copy)]
enum Role { Callback, Outer }
struct Guard(Role);
impl Drop for Guard {
    fn drop(&mut self) {
        let digit = match self.0 {
            Role::Callback => { CALLBACK_DROPS.fetch_add(1, Ordering::SeqCst); 1 },
            Role::Outer => { OUTER_DROPS.fetch_add(1, Ordering::SeqCst); 2 },
        };
        // Single thread. No allocation, assertion, checked arithmetic or panic.
        let previous = DROP_ORDER.load(Ordering::SeqCst);
        DROP_ORDER.store(previous.wrapping_mul(10).wrapping_add(digit), Ordering::SeqCst);
    }
}

#[derive(Debug)]
struct ExpectedPanic { marker: u64, value: u64 }

#[inline(never)]
extern "C-unwind" fn normal_callback(value: u64) -> u64 {
    let _callback_guard = Guard(Role::Callback);
    CALLS.fetch_add(1, Ordering::SeqCst);
    capture_trace();
    value.wrapping_mul(3)
}

#[inline(never)]
extern "C-unwind" fn panic_callback(value: u64) -> u64 {
    let _callback_guard = Guard(Role::Callback);
    CALLS.fetch_add(1, Ordering::SeqCst);
    capture_trace();
    panic::panic_any(ExpectedPanic { marker: MARKER, value });
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn anneal_rust_bounce(callback: Callback, value: u64) -> u64 {
    // The result adjustment ensures this generic bounce cannot be a tail call.
    callback(value).wrapping_add(1)
}

#[derive(Clone, Copy, Debug)]
enum Path { Assembly, Rust }

fn image_identity(label: &str, address: usize) -> Result<(), String> {
    let mut info = DlInfo { dli_fname: std::ptr::null(), dli_fbase: std::ptr::null_mut(),
                            dli_sname: std::ptr::null(), dli_saddr: std::ptr::null_mut() };
    let found = unsafe { dladdr(address as *const c_void, &mut info) };
    if found == 0 || info.dli_fname.is_null() || info.dli_fbase.is_null() {
        return Err(format!("dladdr failed for {label}"));
    }
    let image = unsafe { CStr::from_ptr(info.dli_fname) }.to_string_lossy();
    let symbol = if info.dli_sname.is_null() { std::borrow::Cow::Borrowed("<no-symbol>") }
                 else { unsafe { CStr::from_ptr(info.dli_sname) }.to_string_lossy() };
    let base = info.dli_fbase as usize;
    let offset = address.checked_sub(base).ok_or_else(|| format!("address below image base: {label}"))?;
    println!("IMAGE label={label} address={address:#x} image_base={base:#x} offset={offset:#x} symbol={symbol} image={image}");
    Ok(())
}

fn run_case(path: Path, should_panic: bool) -> Result<(), String> {
    for counter in [&CALLS, &CALLBACK_DROPS, &OUTER_DROPS, &DROP_ORDER, &EXPECTED_HOOKS] {
        counter.store(0, Ordering::SeqCst);
    }
    LAST_TRACE.with(|last| *last.borrow_mut() = Trace::empty());
    let callback = std::hint::black_box(if should_panic { panic_callback as Callback } else { normal_callback as Callback });
    let outcome = panic::catch_unwind(|| {
        let _outer_guard = Guard(Role::Outer);
        match path {
            Path::Assembly => unsafe { anneal_unwind_bounce(callback, VALUE) },
            Path::Rust => anneal_rust_bounce(callback, VALUE),
        }
    });
    match (should_panic, outcome) {
        (false, Ok(value)) => {
            // Independent widened mathematical oracle; implementation uses u64 wrapping ops.
            let expected = ((3u128 * VALUE as u128 + 1) & u64::MAX as u128) as u64;
            if value != expected { return Err(format!("normal result mismatch: {path:?} got={value:#x} expected={expected:#x}")); }
            println!("NORMAL_RESULT path={path:?} value={value:#x}");
        }
        (true, Err(payload)) => {
            let exact = payload.downcast_ref::<ExpectedPanic>()
                .is_some_and(|p| p.marker == MARKER && p.value == VALUE);
            if !exact {
                eprintln!("UNEXPECTED_PANIC path={path:?}; resuming without accepting it");
                panic::resume_unwind(payload);
            }
            println!("EXPECTED_PAYLOAD_CONFIRMED path={path:?} marker={MARKER:#x} value={VALUE:#x}");
        }
        (false, Err(payload)) => {
            eprintln!("UNEXPECTED_PANIC in normal case path={path:?}; resuming");
            panic::resume_unwind(payload);
        }
        (true, Ok(_)) => return Err(format!("expected subject panic did not occur: {path:?}")),
    }
    let counts = [CALLS.load(Ordering::SeqCst), CALLBACK_DROPS.load(Ordering::SeqCst),
                  OUTER_DROPS.load(Ordering::SeqCst), DROP_ORDER.load(Ordering::SeqCst),
                  EXPECTED_HOOKS.load(Ordering::SeqCst)];
    let expected = [1, 1, 1, 12, usize::from(should_panic)];
    if counts != expected { return Err(format!("call/drop/hook mismatch: {path:?} got={counts:?} expected={expected:?}")); }
    let trace = LAST_TRACE.with(|last| *last.borrow());
    if trace.truncated || trace.len == 0 || !matches!(trace.status, 0 | 5) {
        return Err(format!("unwind backtrace incomplete/error: {path:?} status={} len={} truncated={}", trace.status, trace.len, trace.truncated));
    }
    let ips = &trace.ips[..trace.len];
    if matches!(path, Path::Assembly) {
        let start = anneal_unwind_bounce as *const () as usize;
        let end = unsafe { std::ptr::addr_of!(anneal_unwind_bounce_end) } as usize;
        if end.checked_sub(start) != Some(32) || !ips.contains(&(start + 20)) {
            return Err(format!("assembly frame/range missing from live backtrace: start={start:#x} end={end:#x}"));
        }
    }
    println!("CASE_PASS path={path:?} panic={should_panic} counts={counts:?} trace_status={} ips={ips:x?}", trace.status);
    Ok(())
}

fn run() -> Result<(), String> {
    // Only our exact typed payload suppresses the original default hook output.
    // Every other panic uses the original hook and is resumed by run_case.
    let previous = panic::take_hook();
    panic::set_hook(Box::new(move |info| {
        if let Some(p) = info.payload().downcast_ref::<ExpectedPanic>() {
            if p.marker == MARKER && p.value == VALUE {
                EXPECTED_HOOKS.fetch_add(1, Ordering::SeqCst);
                eprintln!("EXPECTED_SUBJECT_PANIC marker={:#x} value={:#x}", p.marker, p.value);
                return;
            }
        }
        previous(info);
    }));
    image_identity("assembly-bounce", anneal_unwind_bounce as *const () as usize)?;
    image_identity("rust-bounce", anneal_rust_bounce as *const () as usize)?;
    image_identity("platform-unwinder", _Unwind_Backtrace as *const () as usize)?;
    for path in [Path::Rust, Path::Assembly] {
        run_case(path, false)?;
        run_case(path, true)?;
    }
    Ok(())
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => { println!("ALL_FOUR_CASES_PASSED"); std::process::ExitCode::SUCCESS },
        Err(message) => { eprintln!("STOP_UNEXPECTED_DISAGREEMENT: {message}"); std::process::ExitCode::FAILURE },
    }
}
