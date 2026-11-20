// Minimal standalone Rust probe reproducing the MIR move-deinitialization
// hazards (M3 partial-field move, M4 same-call `copy _k, move _k` aliasing)
// and LLVM IR poison/freeze/unwind constructs cataloged in REPORT.md.
//
// Compile with:
//   rustc --edition=2021 --crate-type=lib -C opt-level=3 --emit=mir,llvm-ir reproduce_hazards_probe.rs

use std::ops::Range;

/// Reproduces M3 (`m3_partial_field_move`): sequential moves of disjoint fields
/// `(_2.0: usize)` and `(_2.1: usize)` out of a single `Range<usize>` local,
/// matching `tests/mir-opt/pre-codegen/slice_index.rs` and `zerocopy::Split`.
#[no_mangle]
pub fn probe_m3_range_partial_move<'a>(slice: &'a [u32], range: Range<usize>) -> &'a [u32] {
    &slice[range]
}

/// Reproduces M3 in a `Split`-like pair struct (`zerocopy::split_at::Split<&T>`).
pub struct SplitPair<'a, T> {
    pub src: &'a [T],
    pub mid: usize,
}

pub fn probe_m3_split_pair<T>(s: SplitPair<'_, T>) -> (&[T], &[T]) {
    s.src.split_at(s.mid)
}

/// Reproduces M4 (`m4_same_stmt_move_alias`): indexing a slice with a constant
/// `RangeFrom<usize>` (`&bytes[8..]`) inlines `<RangeFrom<usize> as SliceIndex>::index`,
/// which calls `slice_index_fail(self.start, slice.len(), slice.len())`.
/// After `LowerSliceLenCalls` + `GVN`, both `slice.len()` arguments share one
/// local `_k`, yielding `slice_index_fail(const 8_usize, copy _k, move _k)`.
#[no_mangle]
pub fn probe_m4_range_from_const(bytes: &[u8]) -> u8 {
    let tail = &bytes[8..];
    tail.first().copied().unwrap_or(0)
}

/// Reproduces LLVM IR `noundef`, `noalias`, `captures(none)`, `range`, `nuw`,
/// `nsw`, `zext nneg`, `icmp samesign`, and `or disjoint` under `-C opt-level=3`.
#[no_mangle]
pub fn probe_llvm_poison_flags(xs: &[u32], idx: i8, hi: u8, lo: u8) -> u32 {
    let packed = ((hi as u32) << 8) | (lo as u32);
    if idx >= 0 {
        let i = (idx as u8) as usize;
        if i < xs.len() {
            return xs[i].wrapping_add(packed);
        }
    }
    packed
}

/// Reproduces optimizer-inserted `freeze` (`.fr`) instructions via `SimpleLoopUnswitch`
/// / `InstCombineSelect` on `IntoIter<Vec<u8>>::flatten()` iteration and `bcmp`
/// equality, matching `FlattenCompat::next` (`%.fr = freeze ptr`) and `bcmp.i.fr`.
/// Exercises `IntoIter<Vec<String>>::flatten().next()` (non-trivial `Drop`
/// `FlattenCompat::next`) and dual `String` key search (`bcmp` + `select` fold),
/// matching the two `freeze` families observed in `anneal_audit` / `cargo_anneal`.
#[no_mangle]
pub fn probe_llvm_freeze_and_bcmp(
    outer: Vec<Vec<String>>,
    pairs: &[(String, u64)],
    k1: &str,
    k2: &str,
) -> (Option<String>, Option<usize>) {
    let first = outer.into_iter().flatten().next();
    let pos = pairs.iter().position(|(k, v)| *v > 0 && (k == k1 || k == k2));
    (first, pos)
}

/// Reproduces the `std`-crate unwinding cliff: an owned heap destructor (`String`)
/// active across a potentially unwinding callee plus an indirect `sret` return
/// (`[u64; 8]`), forcing `invoke` + `landingpad cleanup` + `sret(...) dead_on_unwind`.
#[no_mangle]
pub fn probe_unwind_sret_and_drop(input: &str, may_panic: fn(&str) -> u64) -> [u64; 8] {
    let owned = String::from(input);
    let v = may_panic(owned.as_str());
    [v, owned.len() as u64, v ^ 1, v ^ 2, v ^ 3, v ^ 4, v ^ 5, v ^ 6]
}
