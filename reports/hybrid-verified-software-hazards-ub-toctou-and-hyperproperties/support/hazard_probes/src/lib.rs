//! Standalone probes demonstrating Rust memory-safety, TOCTOU, trait-spoofing,
//! and panic-state-pollution hazards across unverified-producer / verified-checker
//! boundaries, paired with `#![forbid(unsafe_code)]` snapshot-sealing fixes.

pub mod safe_boundary {
    #![forbid(unsafe_code)]

    use std::cell::Cell;
    use std::cmp::Ordering;
    use std::panic::{self, AssertUnwindSafe};

    /// Naive reference-based checker that validates `&Cell<u64>` in place without
    /// taking an owned frozen snapshot (vulnerable to safe-Rust TOCTOU).
    pub fn naive_check_cell_lt_100(x: &Cell<u64>) -> bool {
        x.get() < 100
    }

    /// Linearly sealed wrapper: private field ensures an instance of
    /// `CertifiedU64Lt100` can only be constructed after copying `snap = x.get()`
    /// into owned memory and validating `snap < 100`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct CertifiedU64Lt100(u64);

    impl CertifiedU64Lt100 {
        pub fn check_cell(x: &Cell<u64>) -> Option<Self> {
            let snap = x.get();
            if snap < 100 {
                Some(Self(snap))
            } else {
                None
            }
        }

        pub fn value(self) -> u64 {
            self.0
        }
    }

    /// Generic checker trusting arbitrary `T: Ord` trait implementations.
    pub fn generic_is_sorted<T: Ord>(xs: &[T]) -> bool {
        xs.windows(2).all(|w| w[0] <= w[1])
    }

    /// Sealed concrete primitive checker (`&[u64]` only — no untrusted `Ord`).
    pub fn concrete_u64_is_sorted(xs: &[u64]) -> bool {
        xs.windows(2).all(|w| w[0] <= w[1])
    }

    #[derive(Clone, Debug)]
    pub struct TrojanOrd {
        pub payload: u64,
        pub armed: Cell<bool>,
    }

    impl PartialEq for TrojanOrd {
        fn eq(&self, other: &Self) -> bool {
            self.payload == other.payload
        }
    }
    impl Eq for TrojanOrd {}
    impl PartialOrd for TrojanOrd {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for TrojanOrd {
        fn cmp(&self, other: &Self) -> Ordering {
            // Lies during the first comparison (checker), exposes inverted order later!
            if self.armed.get() {
                self.armed.set(false);
                Ordering::Less
            } else {
                self.payload.cmp(&other.payload)
            }
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LedgerState {
        pub balance: u64,
    }

    pub fn naive_mut_catch_unwind_with_fallback<P, F>(
        st: &mut LedgerState,
        producer: P,
        fallback: F,
    ) -> u64
    where
        P: FnOnce(&mut LedgerState) -> Option<u64>,
        F: FnOnce(&LedgerState) -> u64,
    {
        let res = panic::catch_unwind(AssertUnwindSafe(|| producer(st)));
        match res {
            Ok(Some(v)) if v == st.balance => v,
            _ => fallback(st),
        }
    }

    pub fn snapshot_isolated_with_fallback<P, F>(
        st: &LedgerState,
        producer: P,
        fallback: F,
    ) -> u64
    where
        P: FnOnce(&LedgerState) -> Option<u64>,
        F: FnOnce(&LedgerState) -> u64,
    {
        let res = panic::catch_unwind(AssertUnwindSafe(|| producer(st)));
        match res {
            Ok(Some(v)) if v == st.balance => v,
            _ => fallback(st),
        }
    }
}

/// Deliberate `unsafe` producer bypassing in-process safe checker invariants:
/// holds a raw `*mut u64` alias while lending `&u64` to the checker, then
/// mutates through `*mut u64` after the check succeeds.
pub fn unsafe_aliasing_post_check_bypass() -> (bool, u64) {
    let raw = Box::into_raw(Box::new(10u64));
    let shared_ref: &u64 = unsafe { &*raw };
    let checked = *shared_ref < 100;
    // UB under Stacked Borrows and Tree Borrows: writing through `raw`
    // while `shared_ref` is later dereferenced (or invalidating shared tag).
    unsafe {
        *raw = 999;
    }
    let observed = *shared_ref;
    unsafe {
        drop(Box::from_raw(raw));
    }
    (checked, observed)
}

/// Deliberate `unsafe` producer forging an invalid `bool` representation (`0x02`)
/// that breaks safe checker/branch consistency under optimization.
pub fn unsafe_invalid_bool_probe() -> (bool, u8) {
    // UB: constructing bool with bit pattern 0x02
    let forged: bool = unsafe { std::mem::transmute::<u8, bool>(2u8) };
    let branch_taken = if forged { true } else { false };
    (branch_taken, forged as u8)
}

#[cfg(test)]
mod tests {
    use super::safe_boundary::*;
    use std::cell::Cell;

    #[test]
    fn test_safe_toctou_cell_bypass_vs_certified_snap() {
        let cell = Cell::new(10u64);
        assert!(naive_check_cell_lt_100(&cell));
        // Untrusted producer / callback mutates shared Cell after check:
        cell.set(999);
        assert!(cell.get() >= 100);

        // Snapshot-sealed CertifiedU64Lt100 isolates checked value from Cell:
        let cell2 = Cell::new(10u64);
        let sealed = CertifiedU64Lt100::check_cell(&cell2).expect("valid snapshot");
        cell2.set(999);
        assert!(sealed.value() < 100);
        assert_eq!(sealed.value(), 10);
    }

    #[test]
    fn test_safe_trojan_ord_bypasses_generic_checker() {
        let arr = [
            TrojanOrd { payload: 100, armed: Cell::new(true) },
            TrojanOrd { payload: 1, armed: Cell::new(false) },
        ];
        // Safe Rust generic checker accepts an unsorted [100, 1] array!
        assert!(generic_is_sorted(&arr));
        assert!(arr[0].payload > arr[1].payload);

        // Sealed primitive slice check cannot be spoofed:
        assert!(!concrete_u64_is_sorted(&[100, 1]));
    }

    #[test]
    fn test_safe_panic_state_pollution_vs_snapshot_isolation() {
        let mut st = LedgerState { balance: 100 };
        let out_naive = naive_mut_catch_unwind_with_fallback(
            &mut st,
            |s| {
                s.balance = 0;
                panic!("simulated producer crash mid-mutation");
            },
            |s| s.balance,
        );
        // Even though panic was caught and fallback ran, balance was corrupted to 0!
        assert_eq!(out_naive, 0);
        assert_eq!(st.balance, 0);

        let st_clean = LedgerState { balance: 100 };
        let out_safe = snapshot_isolated_with_fallback(
            &st_clean,
            |_s| panic!("simulated producer crash in read-only borrow"),
            |s| s.balance,
        );
        assert_eq!(out_safe, 100);
        assert_eq!(st_clean.balance, 100);
    }

    #[test]
    #[ignore = "Deliberate UB: caught by Miri; demonstrates why unsafe producers break in-process checkers"]
    fn ub_aliasing_bypass_detected_by_miri() {
        let (checked, observed) = super::unsafe_aliasing_post_check_bypass();
        assert!(checked && observed == 999);
    }

    #[test]
    #[ignore = "Deliberate UB: caught by Miri; demonstrates invalid enum/bool niche forgery"]
    fn ub_invalid_bool_detected_by_miri() {
        let _ = super::unsafe_invalid_bool_probe();
    }
}
