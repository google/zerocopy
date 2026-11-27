#![forbid(unsafe_code)]

//! Safe-Rust hybrid building-block probes:
//! 1. `double_panic_drop_bypasses_catch_unwind` (proving `catch_unwind` != `noAbort` in-process)
//! 2. `shared_atomic_toctou` vs `copy_and_verify` (RLBox-style single-fetch snapshot sealing)
//! 3. `witness_bomb_cap` (O(1) witness-size cap preventing checker DoS)
//! 4. `trust_core` combinators (`Untrusted<T>`, `Checked<T, Spec>`, `verify_opt`, `verify_result`,
//!    `verify_or_fallback`, `copy_and_verify`, and `split_slice_checked` zerocopy-style guard)

use core::fmt;
use core::marker::PhantomData;
use core::sync::atomic::{AtomicU64, Ordering};
use std::panic::{self, RefUnwindSafe, UnwindSafe};

pub mod trust_core {
    use super::*;

    /// Taint wrapper for raw data originating from an untrusted or external producer
    /// (modeled after RLBox `tainted<T>`). Cannot be inspected directly without passing a
    /// verified validator via `verify` / `copy_and_verify`.
    #[derive(Debug)]
    pub struct Untrusted<T> {
        raw: T,
    }

    impl<T> Untrusted<T> {
        pub fn from_producer(raw: T) -> Self {
            Self { raw }
        }

        /// Consumes the tainted wrapper by transferring ownership into a verified validator.
        pub fn validate_with<Spec, E>(
            self,
            checker: impl FnOnce(&T) -> Result<(), E>,
        ) -> Result<Checked<T, Spec>, E> {
            checker(&self.raw)?;
            Ok(Checked {
                value: self.raw,
                _spec: PhantomData,
            })
        }
    }

    /// Capability-sealed output certified to satisfy phantom specification marker `Spec`.
    /// Private `value` and private `PhantomData` prevent external forgery even inside safe Rust.
    /// Manual `Debug`/`PartialEq`/`Eq` impls avoid requiring trait bounds on phantom `Spec`.
    pub struct Checked<T, Spec> {
        value: T,
        _spec: PhantomData<fn() -> Spec>,
    }

    impl<T: fmt::Debug, Spec> fmt::Debug for Checked<T, Spec> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_tuple("Checked").field(&self.value).finish()
        }
    }

    impl<T: PartialEq, Spec> PartialEq for Checked<T, Spec> {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }

    impl<T: Eq, Spec> Eq for Checked<T, Spec> {}

    impl<T, Spec> Checked<T, Spec> {
        pub(super) fn mint(value: T) -> Self {
            Self {
                value,
                _spec: PhantomData,
            }
        }

        pub fn into_inner(self) -> T {
            self.value
        }

        pub fn as_ref(&self) -> &T {
            &self.value
        }
    }

    /// RLBox-style single-fetch `copy_and_verify` over shared atomic memory: copies once
    /// into owned private storage BEFORE validating, preventing concurrent TOCTOU double-fetch.
    pub fn copy_and_verify<Spec, E>(
        shared_slot: &AtomicU64,
        checker: impl FnOnce(u64) -> Result<(), E>,
    ) -> Result<Checked<u64, Spec>, E> {
        let snap = shared_slot.load(Ordering::Acquire);
        checker(snap)?;
        Ok(Checked::mint(snap))
    }
}

pub use trust_core::{copy_and_verify, Checked, Untrusted};

#[derive(Debug, PartialEq, Eq)]
pub enum HybridErr<E> {
    ProducerPanicked,
    ProducerFailed(E),
    RejectedByChecker,
    WitnessTooLarge { len: usize, max: usize },
}

/// Rung 1/2 `Option`-returning hybrid wrapper with `RefUnwindSafe` state isolation.
pub fn verify_opt<I, T, W, Spec>(
    input: &I,
    producer: impl FnOnce(&I) -> Option<(T, W)> + UnwindSafe,
    checker: impl FnOnce(&I, &T, &W) -> bool,
) -> Option<Checked<T, Spec>>
where
    I: Sync + RefUnwindSafe + ?Sized,
{
    let cand = panic::catch_unwind(panic::AssertUnwindSafe(|| producer(input))).ok()??;
    if checker(input, &cand.0, &cand.1) {
        Some(Checked::mint(cand.0))
    } else {
        None
    }
}

/// Rung 1/2 `Result`-returning hybrid wrapper preserving structured producer errors vs rejections.
pub fn verify_result<I, T, W, E, Spec>(
    input: &I,
    producer: impl FnOnce(&I) -> Result<(T, W), E> + UnwindSafe,
    checker: impl FnOnce(&I, &T, &W) -> bool,
) -> Result<Checked<T, Spec>, HybridErr<E>>
where
    I: Sync + RefUnwindSafe + ?Sized,
{
    let res = match panic::catch_unwind(panic::AssertUnwindSafe(|| producer(input))) {
        Ok(r) => r,
        Err(_) => return Err(HybridErr::ProducerPanicked),
    };
    let (val, witness) = res.map_err(HybridErr::ProducerFailed)?;
    if checker(input, &val, &witness) {
        Ok(Checked::mint(val))
    } else {
        Err(HybridErr::RejectedByChecker)
    }
}

/// Total verified fallback wrapper: `fallback` is directly trusted/verified against `Spec`
/// and does NOT require runtime re-checking through `checker` (preventing completeness panics).
pub fn verify_or_fallback<I, T, W, Spec>(
    input: &I,
    producer: impl FnOnce(&I) -> Option<(T, W)> + UnwindSafe,
    checker: impl FnOnce(&I, &T, &W) -> bool,
    verified_fallback: impl FnOnce(&I) -> T,
) -> Checked<T, Spec>
where
    I: Sync + RefUnwindSafe + ?Sized,
{
    if let Some(checked) = verify_opt(input, producer, checker) {
        checked
    } else {
        Checked::mint(verified_fallback(input))
    }
}

/// Concurrent TOCTOU counterexample over safe `&AtomicU64`: `naive_check_in_place` validates
/// at t1, then a writer thread changes the slot before t2 consumer read.
pub fn naive_check_atomic_in_place(slot: &AtomicU64) -> bool {
    slot.load(Ordering::Acquire) < 100
}

/// Safe `Drop` guard whose destructor panics during an active unwind, causing immediate
/// process abort (`SIGABRT`) that `std::panic::catch_unwind` CANNOT catch.
pub struct DoublePanicGuard;
impl Drop for DoublePanicGuard {
    fn drop(&mut self) {
        panic!("panic inside Drop while unwinding");
    }
}

pub fn trigger_double_panic_inside_catch_unwind() {
    let _ = panic::catch_unwind(|| {
        let _guard = DoublePanicGuard;
        panic!("initial producer panic");
    });
}

/// Witness-size capped checker rejecting oversized untrusted witnesses in O(1) before allocation.
pub fn check_witness_bounded(input_len: usize, witness: &[u64], max_factor: usize) -> Result<usize, HybridErr<()>> {
    let max = input_len.saturating_mul(max_factor);
    if witness.len() > max {
        return Err(HybridErr::WitnessTooLarge {
            len: witness.len(),
            max,
        });
    }
    let mut acc = 0usize;
    for &w in witness {
        acc = acc.wrapping_add(w as usize);
    }
    Ok(acc)
}

/// Zerocopy-style checked split wrapper: pairs an untrusted mid-point estimator with a
/// formally verifiable bounds check `mid <= buf.len()` before splitting.
pub struct ValidSplit;
pub fn split_slice_with_untrusted_hint<'a>(
    buf: &'a [u8],
    untrusted_mid: impl FnOnce(&[u8]) -> Option<usize> + UnwindSafe,
) -> Option<Checked<(&'a [u8], &'a [u8]), ValidSplit>> {
    verify_opt::<[u8], usize, (), ValidSplit>(
        buf,
        |b| untrusted_mid(b).map(|m| (m, ())),
        |b, &m, _| m <= b.len(),
    )
    .map(|checked_mid| {
        let mid = checked_mid.into_inner();
        Checked::mint(buf.split_at(mid))
    })
}

/// Deterministic tie-breaker / canonical witness checker example: requires not only `x * x <= n`
/// (which leaves relational freedom if floor/lower approximation were allowed) but canonical
/// integer square root `r*r <= n && (r + 1)*(r + 1) > n`.
pub struct CanonicalIsqrt;
pub fn checked_isqrt(n: u64, approx_producer: impl FnOnce(&u64) -> Option<u64> + UnwindSafe) -> Checked<u64, CanonicalIsqrt> {
    let is_canon_isqrt = |&x: &u64, &r: &u64, _: &()| -> bool {
        let sq = r.checked_mul(r);
        let next_sq = r.checked_add(1).and_then(|r1| r1.checked_mul(r1));
        matches!(sq, Some(s) if s <= x) && match next_sq {
            Some(ns) => ns > x,
            None => true,
        }
    };
    verify_or_fallback(
        &n,
        |x| approx_producer(x).map(|r| (r, ())),
        is_canon_isqrt,
        |&x| {
            // Verified total binary-search fallback
            let mut lo = 0u64;
            let mut hi = x.min(u32::MAX as u64) + 1;
            while lo + 1 < hi {
                let mid = lo + (hi - lo) / 2;
                if mid * mid <= x {
                    lo = mid;
                } else {
                    hi = mid;
                }
            }
            lo
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::AtomicBool;
    use std::sync::Arc;
    use std::thread;

    struct BoundedLt100;

    #[test]
    fn test_shared_atomic_toctou_vs_copy_and_verify() {
        let slot = Arc::new(AtomicU64::new(10));
        let start_flip = Arc::new(AtomicBool::new(false));
        let done_flip = Arc::new(AtomicBool::new(false));

        let slot_w = Arc::clone(&slot);
        let start_w = Arc::clone(&start_flip);
        let done_w = Arc::clone(&done_flip);
        let h = thread::spawn(move || {
            while !start_w.load(Ordering::Acquire) {
                thread::yield_now();
            }
            slot_w.store(999, Ordering::Release);
            done_w.store(true, Ordering::Release);
        });

        // 1. Naive check-in-place observes 10 (< 100), then consumer observes 999!
        assert!(naive_check_atomic_in_place(&slot));
        start_flip.store(true, Ordering::Release);
        while !done_flip.load(Ordering::Acquire) {
            thread::yield_now();
        }
        assert_eq!(slot.load(Ordering::Acquire), 999);
        h.join().unwrap();

        // 2. RLBox-style copy_and_verify observes snapshot 999 and rejects, or on 10 captures
        //    owned Checked<u64, BoundedLt100> immune to concurrent mutation.
        let rejected = copy_and_verify::<BoundedLt100, ()>(&slot, |v| if v < 100 { Ok(()) } else { Err(()) });
        assert!(rejected.is_err());

        slot.store(42, Ordering::Release);
        let sealed = copy_and_verify::<BoundedLt100, ()>(&slot, |v| if v < 100 { Ok(()) } else { Err(()) }).unwrap();
        slot.store(999, Ordering::Release);
        assert_eq!(*sealed.as_ref(), 42);
    }

    #[test]
    fn test_witness_bomb_cap_rejects_in_o1() {
        let bomb = vec![1u64; 100_000];
        let err = check_witness_bounded(4, &bomb, 8).unwrap_err();
        assert_eq!(err, HybridErr::WitnessTooLarge { len: 100_000, max: 32 });
    }

    #[test]
    fn test_result_and_zerocopy_split_and_isqrt() {
        let data = b"hello_zerocopy";
        let split = split_slice_with_untrusted_hint(data, |_| Some(5)).unwrap();
        assert_eq!(split.into_inner(), (&b"hello"[..], &b"_zerocopy"[..]));
        // Out-of-bounds or panicking hint fails closed to None
        assert!(split_slice_with_untrusted_hint(data, |_| Some(999)).is_none());
        assert!(split_slice_with_untrusted_hint(data, |_| panic!("boom")).is_none());

        // Result combinator distinguishes producer panic vs producer error vs checker reject
        let r_pan = verify_result::<u64, u64, (), &'static str, CanonicalIsqrt>(
            &16,
            |_| panic!("untrusted crash"),
            |&x, &y, _| y * y == x,
        );
        assert_eq!(r_pan, Err(HybridErr::ProducerPanicked));

        let r_rej = verify_result::<u64, u64, (), &'static str, CanonicalIsqrt>(
            &16,
            |_| Ok((3, ())),
            |&x, &y, _| y * y == x,
        );
        assert_eq!(r_rej, Err(HybridErr::RejectedByChecker));

        // Canonical isqrt handles forged hint and huge u64::MAX without overflow
        let c1 = checked_isqrt(17, |_| Some(3)); // bad hint -> fallback 4
        assert_eq!(*c1.as_ref(), 4);
        let c_max = checked_isqrt(u64::MAX, |_| Some(u32::MAX as u64));
        assert_eq!(*c_max.as_ref(), u32::MAX as u64);
    }

    #[test]
    fn test_double_panic_drop_aborts_despite_catch_unwind() {
        if std::env::var("HYBRID_BB_DO_DOUBLE_PANIC").as_deref() == Ok("1") {
            trigger_double_panic_inside_catch_unwind();
            return;
        }
        let exe = std::env::current_exe().unwrap();
        let out = std::process::Command::new(exe)
            .arg("tests::test_double_panic_drop_aborts_despite_catch_unwind")
            .arg("--exact")
            .arg("--nocapture")
            .env("HYBRID_BB_DO_DOUBLE_PANIC", "1")
            .output()
            .unwrap();
        // Process MUST terminate abnormally (SIGABRT / non-zero), never returning normally!
        assert!(!out.status.success(), "expected fatal abort, got {:?}", out.status);
    }
}
