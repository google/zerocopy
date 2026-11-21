#![crate_type = "rlib"]
#![crate_name = "crate_callee"]

use std::num::NonZeroU64;
use std::sync::Mutex;

pub static EVENT_LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());

pub fn record_event(ev: &str) {
    EVENT_LOG.lock().unwrap().push(ev.to_string());
}

pub fn take_events() -> Vec<String> {
    std::mem::take(&mut *EVENT_LOG.lock().unwrap())
}

#[derive(Debug)]
pub struct DropToken {
    pub label: &'static str,
    pub panic_on_drop: bool,
}

impl DropToken {
    pub fn new(label: &'static str) -> Self {
        record_event(&format!("init:{}", label));
        Self { label, panic_on_drop: false }
    }

    pub fn bomb(label: &'static str) -> Self {
        record_event(&format!("init:{}", label));
        Self { label, panic_on_drop: true }
    }
}

impl Drop for DropToken {
    #[inline(never)]
    fn drop(&mut self) {
        record_event(&format!("drop:{}", self.label));
        // Flush stderr line in double-panic subprocess modes so parent sees exact pre-abort drops
        if std::env::var_os("CRUCIBLE_STDERR_TRACE").is_some() {
            use std::io::Write;
            let _ = writeln!(std::io::stderr(), "TRACE_DROP:{}", self.label);
            let _ = std::io::stderr().flush();
        }
        if self.panic_on_drop {
            panic!("intentional destructor panic in {}", self.label);
        }
    }
}

/// 12-byte mixed integer + float aggregate: under `extern "C-unwind"` on SysV x86-64,
/// eightbyte 0 = (a: u32, b: u32) -> Class::Int (i64 in %rdi / %rax),
/// eightbyte 1 = (c: f32) -> Class::Sse (float in %xmm0 / %xmm0) => `PassMode::Cast`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MixedCast12 {
    pub a: u32,
    pub b: u32,
    pub c: f32,
}

/// >16-byte aggregate with `Drop`: `40` bytes (`4 * 8 + 16`), returned via `PassMode::Indirect` (`sret` in `%rdi`).
pub struct BigSretDrop {
    pub words: [u64; 4],
    pub token: DropToken,
}

/// Cross-crate global calibration value to force GOT / PC-relative data access across crates.
#[used]
pub static CALLEE_GLOBAL_BIAS: u64 = 0x0102_0304_0506_0708;

/// 1. `PassMode::Direct`: scalar u64 in `%rdi` -> `%rax`.
#[no_mangle]
#[inline(never)]
pub fn callee_direct(x: u64, should_panic: bool) -> u64 {
    let _callee_guard = DropToken::new("callee_direct_guard");
    let bias = unsafe { std::ptr::read_volatile(&CALLEE_GLOBAL_BIAS) };
    if should_panic {
        record_event("panic:callee_direct");
        panic!("callee_directunwind");
    }
    x.wrapping_add(bias & 0xff)
}

/// 2. `PassMode::Pair`: 16-byte niche-optimized `Option<(NonZeroU64, u64)>` (`ScalarPair` in `%rdi, %rsi` -> `%rax, %rdx`).
#[allow(improper_ctypes_definitions)]
#[no_mangle]
#[inline(never)]
pub fn callee_pair_niche(
    inp: Option<(NonZeroU64, u64)>,
    should_panic: bool,
) -> Option<(NonZeroU64, u64)> {
    let _callee_guard = DropToken::new("callee_pair_guard");
    if should_panic {
        record_event("panic:callee_pair");
        panic!("callee_pair_unwind");
    }
    match inp {
        Some((nz, v)) => NonZeroU64::new(nz.get().saturating_add(1)).map(|n2| (n2, v + 10)),
        None => Some((NonZeroU64::new(7).unwrap(), 70)),
    }
}

/// 3. `PassMode::Cast`: 12-byte `MixedCast12` over `extern "C-unwind"` (`{ i64, float }` in `%rdi, %xmm0` -> `%rax, %xmm0`).
#[no_mangle]
#[inline(never)]
pub extern "C-unwind" fn callee_cast_12(inp: MixedCast12, should_panic: bool) -> MixedCast12 {
    let _callee_guard = DropToken::new("callee_cast12_guard");
    if should_panic {
        record_event("panic:callee_cast12");
        panic!("callee_cast12_unwind");
    }
    MixedCast12 {
        a: inp.a.wrapping_add(1),
        b: inp.b.wrapping_add(2),
        c: inp.c + 0.5,
    }
}

/// 4. `PassMode::Indirect` (`sret` in `%rdi`): `>16`-byte `BigSretDrop` (`40` bytes).
/// Note that if `should_panic` is true, `*sret` is NEVER written; caller must NOT drop `_ret`!
#[allow(improper_ctypes_definitions)]
#[no_mangle]
#[inline(never)]
pub fn callee_indirect_sret(seed: u64, should_panic: bool) -> BigSretDrop {
    let _callee_guard = DropToken::new("callee_sret_guard");
    if should_panic {
        record_event("panic:callee_sret");
        panic!("callee_sret_unwind");
    }
    BigSretDrop {
        words: [seed, seed + 1, seed + 2, seed + 3],
        token: DropToken::new("sret_ret_token"),
    }
}

/// 5. Diverging `-> !` cross-crate panicking function (`NoTrapAfterNoreturn = true` target).
#[no_mangle]
#[inline(never)]
pub fn callee_noreturn_panic(tag: u64) -> ! {
    let _callee_guard = DropToken::new("callee_noreturn_guard");
    record_event("panic:callee_noreturn");
    panic!("callee_noreturn_unwind:{}", tag);
}
