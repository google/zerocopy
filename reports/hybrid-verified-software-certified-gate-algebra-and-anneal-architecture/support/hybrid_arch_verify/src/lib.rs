#![forbid(unsafe_code)]

//! Executable verification of the Stage 2 Unified Hybrid Building Block (`CertifiedGate` algebra)
//! and proof of the `AtomicU64` `Sync + RefUnwindSafe` TOCTOU loophole against borrowed `&I` gates:
//! 1. `AtomicU64` implements BOTH `Sync` and `RefUnwindSafe`, so a gate accepting `&I` where
//!    `I: Sync + RefUnwindSafe` can be defeated by concurrent `AtomicU64::store` between check
//!    and consumer read (`test_sync_refunwindsafe_still_allows_atomic_toctou`).
//! 2. Enforcing value-snapshot `CopyAndVerify` (`SnapshotSource`) into owned value types before
//!    evaluating `CertifiedGate` closes the `AtomicU64` TOCTOU gap under both Stacked and Tree
//!    Borrows Miri (`0` UB).
//! 3. `CertifiedGate` + `first_accepted` + `with_fallback` + `fold_stream_prefix` +
//!    `DstLayout`-style slice-DST cast metadata validator (`check_slice_dst_cast_candidate`)
//!    exercise `S1`–`S6` through one minimal core interface without `assert!(V(fb))`.

use core::fmt;
use core::marker::PhantomData;

pub mod gate_core {
    use super::*;

    /// Uniform raw outcome produced by any untrusted producer + containment boundary `Iso`.
    #[derive(Debug, PartialEq, Eq)]
    pub enum RawOutcome<E, Y, W> {
        Candidate(Y, W),
        ProducerFailed(E),
        Trapped,
    }

    /// Structured failure provenance for `CertifiedGate` evaluation.
    #[derive(Debug, PartialEq, Eq)]
    pub enum HybridErr<E> {
        ProducerTrapped,
        ProducerFailed(E),
        WitnessOversized { actual: usize, max_allowed: usize },
        RejectedByChecker,
    }

    /// Zero-cost capability sealing `value: Y` to phantom specification `Spec`.
    /// Private fields ensure `Checked<Y, Spec>` can ONLY be minted by `eval_gate` (`GateSound`)
    /// or `with_fallback` (`FallbackSound`), never forged by untrusted code and never re-checked
    /// via `assert!(gate.check(fb))`.
    #[repr(transparent)]
    pub struct Checked<Y, Spec> {
        value: Y,
        _spec: PhantomData<fn() -> Spec>,
    }

    impl<Y: fmt::Debug, Spec> fmt::Debug for Checked<Y, Spec> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_tuple("Checked").field(&self.value).finish()
        }
    }

    impl<Y: PartialEq, Spec> PartialEq for Checked<Y, Spec> {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }

    impl<Y: Eq, Spec> Eq for Checked<Y, Spec> {}

    impl<Y, Spec> Checked<Y, Spec> {
        pub(super) fn mint(value: Y) -> Self {
            Self {
                value,
                _spec: PhantomData,
            }
        }

        pub fn into_inner(self) -> Y {
            self.value
        }

        pub fn as_ref(&self) -> &Y {
            &self.value
        }
    }

    /// Minimal core checker interface unifying S1 (`W = ()`), S2 (`W = ()`), and S3 (`W`).
    pub trait CertifiedGate {
        type Input: ?Sized;
        type Output;
        type Witness;
        type Spec;

        /// Mandatory O(1) upper bound on `witness_size` computed from `input` BEFORE traversal.
        fn max_witness_size(&self, input: &Self::Input) -> usize;

        /// Mandatory O(1) structural measure of `witness` (e.g., `slice.len()`, `0` for `()`).
        fn witness_size(&self, witness: &Self::Witness) -> usize;

        /// Total boolean/decidable validation under `witness_size(w) <= max_witness_size(x)`.
        fn check(&self, input: &Self::Input, output: &Self::Output, witness: &Self::Witness) -> bool;
    }

    /// Verified fallback contract (`∀ x, Pre(x) -> Spec(x, fallback(x))`), eliminating `HybridErr`
    /// directly without invoking `gate.check` at runtime.
    pub trait VerifiedFallback<Input: ?Sized, Output, Spec> {
        fn fallback(&self, input: &Input) -> Output;
    }

    /// Evaluates `gate` on a single `RawOutcome`, enforcing the O(1) witness cap BEFORE `check`.
    pub fn eval_gate<G: CertifiedGate, E>(
        gate: &G,
        input: &G::Input,
        raw: RawOutcome<E, G::Output, G::Witness>,
    ) -> Result<Checked<G::Output, G::Spec>, HybridErr<E>> {
        match raw {
            RawOutcome::Trapped => Err(HybridErr::ProducerTrapped),
            RawOutcome::ProducerFailed(e) => Err(HybridErr::ProducerFailed(e)),
            RawOutcome::Candidate(y, w) => {
                let actual = gate.witness_size(&w);
                let max_allowed = gate.max_witness_size(input);
                if actual > max_allowed {
                    return Err(HybridErr::WitnessOversized { actual, max_allowed });
                }
                if gate.check(input, &y, &w) {
                    Ok(Checked::mint(y))
                } else {
                    Err(HybridErr::RejectedByChecker)
                }
            }
        }
    }

    /// Gate-aware portfolio choice (`S6`): evaluates lazy producers sequentially and returns the
    /// first gate-accepted `Checked<Output, Spec>`, avoiding the pre-gate `orElse` drop bug.
    pub fn first_accepted<G, E, I, F>(
        gate: &G,
        input: &G::Input,
        producers: I,
    ) -> Result<Checked<G::Output, G::Spec>, HybridErr<E>>
    where
        G: CertifiedGate,
        I: IntoIterator<Item = F>,
        F: FnOnce(&G::Input) -> RawOutcome<E, G::Output, G::Witness>,
    {
        let mut last_err = HybridErr::ProducerTrapped;
        for prod in producers {
            match eval_gate(gate, input, prod(input)) {
                Ok(checked) => return Ok(checked),
                Err(e) => last_err = e,
            }
        }
        Err(last_err)
    }

    /// Carrier projection to `Option<Checked<Y, Spec>>` (matching Anneal Profile v2 `MirTy.option`).
    pub fn to_option<Y, Spec, E>(res: Result<Checked<Y, Spec>, HybridErr<E>>) -> Option<Checked<Y, Spec>> {
        res.ok()
    }

    /// Eliminates `HybridErr<E>` via a `VerifiedFallback` without runtime completeness checks.
    pub fn with_fallback<Input: ?Sized, Y, Spec, E, Fb>(
        input: &Input,
        res: Result<Checked<Y, Spec>, HybridErr<E>>,
        fb: &Fb,
    ) -> Checked<Y, Spec>
    where
        Fb: VerifiedFallback<Input, Y, Spec>,
    {
        match res {
            Ok(checked) => checked,
            Err(_) => Checked::mint(fb.fallback(input)),
        }
    }

    /// Single-fetch value snapshot gate (`RLBox`-style `copy_and_verify`): copies shared/atomic
    /// input ONCE into owned private value `Snap` before running producer + `eval_gate`.
    pub fn snapshot_and_eval<G, E, SnapFn, ProdFn>(
        gate: &G,
        snapshot_once: SnapFn,
        producer: ProdFn,
    ) -> Result<(G::Input, Checked<G::Output, G::Spec>), HybridErr<E>>
    where
        G: CertifiedGate,
        G::Input: Sized,
        SnapFn: FnOnce() -> G::Input,
        ProdFn: FnOnce(&G::Input) -> RawOutcome<E, G::Output, G::Witness>,
    {
        let owned_snap = snapshot_once();
        let raw = producer(&owned_snap);
        let checked = eval_gate(gate, &owned_snap, raw)?;
        Ok((owned_snap, checked))
    }

    /// Prefix-safe incremental streaming combinator (`S5`): validates each `(next_state, chunk)`
    /// via `gate` BEFORE pushing `chunk` to the output vector, halting on first rejection.
    pub fn fold_stream_prefix<S, U, C, W, Spec, E, G, ProdFn>(
        gate: &G,
        init_state: S,
        tokens: impl IntoIterator<Item = U>,
        mut step_producer: ProdFn,
    ) -> (Vec<C>, Option<HybridErr<E>>)
    where
        G: CertifiedGate<Input = (S, U), Output = (S, C), Witness = W, Spec = Spec>,
        ProdFn: FnMut(&S, &U) -> RawOutcome<E, (S, C), W>,
    {
        let mut state = init_state;
        let mut emitted = Vec::new();
        for u in tokens {
            let pair = (state, u);
            let raw = step_producer(&pair.0, &pair.1);
            match eval_gate(gate, &pair, raw) {
                Ok(checked_sc) => {
                    let (next_state, chunk) = checked_sc.into_inner();
                    emitted.push(chunk);
                    state = next_state;
                }
                Err(err) => return (emitted, Some(err)),
            }
        }
        (emitted, None)
    }
}

pub use gate_core::*;

/// Demonstrates the `zerocopy` `DstLayout::validate_cast_and_convert_metadata` hybrid pattern:
/// an untrusted fast bit-packing producer proposes `(elems, split_at)`, and a compact overflow-safe
/// relational `CertifiedGate` verifies exact prefix/suffix alignment, size fit, and maximality!
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastMode {
    Prefix,
    Suffix,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SliceDstCastInput {
    pub addr: usize,
    pub bytes_len: usize,
    pub base_size: usize,
    pub elem_size: usize, // required > 0
    pub align: usize,     // required power of two > 0
    pub mode: CastMode,
}

pub struct ValidSliceDstCast;

fn rounded_size_for_elems(base_size: usize, elem_size: usize, align: usize, elems: usize) -> Option<usize> {
    let raw = elems.checked_mul(elem_size)?.checked_add(base_size)?;
    let rem = raw % align;
    if rem == 0 {
        Some(raw)
    } else {
        raw.checked_add(align - rem)
    }
}

pub struct SliceDstCastGate;

impl CertifiedGate for SliceDstCastGate {
    type Input = SliceDstCastInput;
    type Output = (usize, usize); // (elems, split_at)
    type Witness = ();
    type Spec = ValidSliceDstCast;

    fn max_witness_size(&self, _input: &Self::Input) -> usize {
        0
    }

    fn witness_size(&self, _witness: &Self::Witness) -> usize {
        0
    }

    fn check(&self, inp: &Self::Input, &(elems, split_at): &Self::Output, _: &()) -> bool {
        if inp.elem_size == 0 || !inp.align.is_power_of_two() {
            return false;
        }
        let Some(_end_addr) = inp.addr.checked_add(inp.bytes_len) else {
            return false;
        };
        let Some(self_bytes) = rounded_size_for_elems(inp.base_size, inp.elem_size, inp.align, elems) else {
            return false;
        };
        if self_bytes > inp.bytes_len {
            return false;
        }
        let expected_split = match inp.mode {
            CastMode::Prefix => self_bytes,
            CastMode::Suffix => inp.bytes_len - self_bytes,
        };
        if split_at != expected_split {
            return false;
        }
        let target_addr = match inp.mode {
            CastMode::Prefix => inp.addr,
            CastMode::Suffix => inp.addr + split_at,
        };
        if target_addr % inp.align != 0 {
            return false;
        }
        // Maximality: `elems + 1` must either overflow `usize` or exceed `bytes_len`!
        match elems
            .checked_add(1)
            .and_then(|e1| rounded_size_for_elems(inp.base_size, inp.elem_size, inp.align, e1))
        {
            Some(next_bytes) => next_bytes > inp.bytes_len,
            None => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::panic::RefUnwindSafe;
    use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::Arc;
    use std::thread;

    fn assert_sync_and_ref_unwind_safe<T: Sync + RefUnwindSafe>() {}

    #[test]
    fn test_sync_refunwindsafe_still_allows_atomic_toctou_without_snapshot() {
        // Compile-time proof: `AtomicU64` satisfies BOTH `Sync` and `RefUnwindSafe`!
        assert_sync_and_ref_unwind_safe::<AtomicU64>();

        struct BorrowedAtomicGate;
        struct EqualToInput;
        impl CertifiedGate for BorrowedAtomicGate {
            type Input = AtomicU64;
            type Output = u64;
            type Witness = ();
            type Spec = EqualToInput;
            fn max_witness_size(&self, _: &AtomicU64) -> usize { 0 }
            fn witness_size(&self, _: &()) -> usize { 0 }
            fn check(&self, inp: &AtomicU64, &y: &u64, _: &()) -> bool {
                inp.load(Ordering::Acquire) == y
            }
        }

        let shared = Arc::new(AtomicU64::new(10));
        let checked_done = Arc::new(AtomicBool::new(false));
        let mutated_done = Arc::new(AtomicBool::new(false));

        let s_w = Arc::clone(&shared);
        let cd_w = Arc::clone(&checked_done);
        let md_w = Arc::clone(&mutated_done);
        let h = thread::spawn(move || {
            while !cd_w.load(Ordering::Acquire) {
                thread::yield_now();
            }
            s_w.store(999, Ordering::Release);
            md_w.store(true, Ordering::Release);
        });

        // 1. Borrowing `&AtomicU64` directly allows post-check mutation of the input reference!
        let bad_checked = eval_gate::<BorrowedAtomicGate, ()>(&BorrowedAtomicGate, &shared, RawOutcome::Candidate(10, ())).unwrap();
        checked_done.store(true, Ordering::Release);
        while !mutated_done.load(Ordering::Acquire) {
            thread::yield_now();
        }
        h.join().unwrap();
        // Now `*bad_checked.as_ref() == 10`, while `shared` is `999`!
        assert_ne!(*bad_checked.as_ref(), shared.load(Ordering::Acquire));

        // 2. Single-fetch `snapshot_and_eval` over owned `u64` binds `(snap, Checked<u64, Spec>)` immutably!
        struct OwnedValGate;
        impl CertifiedGate for OwnedValGate {
            type Input = u64;
            type Output = u64;
            type Witness = ();
            type Spec = EqualToInput;
            fn max_witness_size(&self, _: &u64) -> usize { 0 }
            fn witness_size(&self, _: &()) -> usize { 0 }
            fn check(&self, &inp: &u64, &y: &u64, _: &()) -> bool {
                inp == y
            }
        }
        let (snap, good_checked) = snapshot_and_eval::<OwnedValGate, (), _, _>(
            &OwnedValGate,
            || shared.load(Ordering::Acquire),
            |&x| RawOutcome::Candidate(x, ()),
        )
        .unwrap();
        shared.store(12345, Ordering::Release);
        assert_eq!(snap, 999);
        assert_eq!(*good_checked.as_ref(), snap);
    }

    #[test]
    fn test_portfolio_first_accepted_and_incomplete_checker_fallback() {
        // Incomplete checker: accepts ONLY `y == x + 1` for spec `y >= x`, while fallback returns `x`!
        struct GeInputSpec;
        struct StrictPlusOneGate;
        impl CertifiedGate for StrictPlusOneGate {
            type Input = u64;
            type Output = u64;
            type Witness = Vec<u8>;
            type Spec = GeInputSpec;
            fn max_witness_size(&self, _: &u64) -> usize { 4 }
            fn witness_size(&self, w: &Vec<u8>) -> usize { w.len() }
            fn check(&self, &x: &u64, &y: &u64, _: &Vec<u8>) -> bool {
                x.checked_add(1) == Some(y)
            }
        }
        struct IdentityFallback;
        impl VerifiedFallback<u64, u64, GeInputSpec> for IdentityFallback {
            fn fallback(&self, &x: &u64) -> u64 {
                x
            }
        }

        let gate = StrictPlusOneGate;
        // Producer 1 emits an oversized witness bomb; Producer 2 emits bogus candidate; Producer 3 succeeds!
        type ProdFn = fn(&u64) -> RawOutcome<&'static str, u64, Vec<u8>>;
        let p_bomb: ProdFn = |_| RawOutcome::Candidate(11, vec![0u8; 1024]);
        let p_bad: ProdFn = |_| RawOutcome::Candidate(999, vec![]);
        let p_good: ProdFn = |&x| RawOutcome::Candidate(x + 1, vec![1, 2]);

        let won = first_accepted(&gate, &10, [p_bomb, p_bad, p_good]).unwrap();
        assert_eq!(*won.as_ref(), 11);

        // When all producers fail, `with_fallback` returns `fb(10) = 10` WITHOUT calling `gate.check(10, 10)`
        // (which would return `false` and abort under a naive `assert!(V(fb))` wrapper!).
        let all_bad = first_accepted(&gate, &10, [p_bomb, p_bad]);
        assert_eq!(all_bad, Err(HybridErr::RejectedByChecker));
        let total = with_fallback(&10, all_bad, &IdentityFallback);
        assert_eq!(*total.as_ref(), 10);
    }

    #[test]
    fn test_slice_dst_cast_gate_and_streaming_prefix() {
        let gate = SliceDstCastGate;
        let inp = SliceDstCastInput {
            addr: 0x1000,
            bytes_len: 26,
            base_size: 4,
            elem_size: 6,
            align: 4,
            mode: CastMode::Prefix,
        };
        // elems = 3 -> raw = 4 + 18 = 22 -> rounded up to align 4 = 24 <= 26; elems = 4 -> 4 + 24 = 28 > 26!
        let ok = eval_gate::<_, ()>(&gate, &inp, RawOutcome::Candidate((3, 24), ())).unwrap();
        assert_eq!(ok.into_inner(), (3, 24));

        // Sub-maximal elems = 2 (rounded size 16 <= 26, but elems=3 also fits!) is rejected!
        assert_eq!(
            eval_gate::<_, ()>(&gate, &inp, RawOutcome::Candidate((2, 16), ())),
            Err(HybridErr::RejectedByChecker)
        );
        // Misaligned Suffix cast (`0x1000 + (26 - 24) = 0x1002`, not 4-byte aligned!) is rejected!
        let inp_suffix = SliceDstCastInput { mode: CastMode::Suffix, ..inp };
        assert_eq!(
            eval_gate::<_, ()>(&gate, &inp_suffix, RawOutcome::Candidate((3, 2), ())),
            Err(HybridErr::RejectedByChecker)
        );

        // Streaming prefix gate: monotonically increasing chunks < 100
        struct MonotoneStreamGate;
        struct MonotoneSpec;
        impl CertifiedGate for MonotoneStreamGate {
            type Input = (u64, u64);
            type Output = (u64, u64);
            type Witness = ();
            type Spec = MonotoneSpec;
            fn max_witness_size(&self, _: &(u64, u64)) -> usize { 0 }
            fn witness_size(&self, _: &()) -> usize { 0 }
            fn check(&self, &(prev, _): &(u64, u64), &(next_st, chunk): &(u64, u64), _: &()) -> bool {
                chunk >= prev && chunk < 100 && next_st == chunk
            }
        }
        let (emitted, err) = fold_stream_prefix::<u64, u64, u64, (), MonotoneSpec, (), _, _>(
            &MonotoneStreamGate,
            0,
            [10, 25, 500, 30],
            |_st, &tok| RawOutcome::Candidate((tok, tok), ()),
        );
        assert_eq!(emitted, vec![10, 25]);
        assert_eq!(err, Some(HybridErr::RejectedByChecker));
    }
}
