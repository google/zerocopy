# Safe-Trait Adversarial Implementations, Coherence-Keyed Dispatch, and Soundness Boundaries in Rust Verification

## Summary

Rust's safety model enforces an asymmetric trust boundary between **safe traits** (`Ord`, `Eq`, `Hash`, `Borrow`, `Deref`, `DerefMut`, `Clone`, `Iterator`, `Read`, `Error`) and **`unsafe` traits** (`Send`, `Sync`, `GlobalAlloc`, `TrustedLen`, `TrustedStep`, `InPlaceIterable`, `CloneToUninit`, and `zerocopy`'s `Immutable`, `TryFromBytes`, `FromBytes`, and `IntoBytes`):

1. **The Asymmetric Safe-Trait Soundness Invariant:** Any `#![forbid(unsafe_code)]` client can implement a safe trait using arbitrary safe expressions—including interior mutability (`AtomicBool`, `Cell`, `RefCell`), global state, non-total comparisons, mismatched hashes, length-shifting borrows, and targeted panics. Consequently, **unsafe code in a generic function or collection must never rely on a safe trait's documented algebraic laws to prevent Undefined Behavior (`WellFormed`)**. Violating `Ord` totality, `Hash`/`Eq` congruence, `Borrow` equivalence, or `Iterator::size_hint` accuracy is a *logic error*: it may yield unspecified outputs, missed lookups, leaks, aborts, divergence, or panics, **never** out-of-bounds memory access, use-after-free, uninitialized byte exposure, or double-drops.
2. **Primary-Source Lessons from Historical `std` CVEs and Modern Hardening:**
   - **`CVE-2019-12083` (`Error::type_id`):** Allowing safe types to override default method `Error::type_id` let safe code spoof `TypeId::of::<Box<usize>>()` and downcast `&dyn Error` to an unrelated type; fixed by destabilizing `type_id` and sealing it with an unnameable `private::Internal` token (`core/src/error.rs:116-127`).
   - **`CVE-2020-36323` (`<[S]>::join` for `S: Borrow<str>`):** Two-pass buffer preallocation computed `reserved_len` on pass 1 and called `Vec::set_len(reserved_len)` after pass 2; a stateful `Borrow<str>` shrinking on pass 2 exposed uninitialized heap bytes to `String::from_utf8_unchecked`. Fixed in `alloc/src/str.rs:114-175` by borrowing `slice[0]` once, copying subsequent slices via checked `split_at_mut`, and setting length strictly to written bytes.
   - **`CVE-2021-28875` (`Read::read_to_end`) & `CVE-2021-31162` / `CVE-2021-28876`–`28879` (`Iterator` vs. `TrustedLen` / `TrustedRandomAccess`):** Trusting unvalidated `Read::read` counts or composing `Zip` + `TrustedRandomAccess` across panics, nested adapters, mixed `next`/`next_back`, or saturating `size_hint` sums caused buffer overflows and double-frees.
   - **Modern Defensive Idioms (`driftsort`, `ipnsort`, `BTreeMap`, `BinaryHeap`, `HashMap`, `pin!`):** `core`/`alloc` uses checked slice splits and RAII gap-restoration guards (`CopyOnDrop`, `MergeState`, `BinaryHeap::Hole`) plus non-fundamental `helper::Pin` (`#85099`) and `PinMacroHelper` (`#153438`) wrappers to stay UB-free against adversarial `Ord`, `Borrow`, and `DerefMut` implementations.
3. **Verification Soundness Hazard (Naive `LawfulOrd` Injection):** If a deductive Rust verifier supplies `LawfulOrd K` from a background typeclass registry while discharging baseline UB-freedom (`WellFormed`, e.g., `vals.get_unchecked(idx)` in `SortedPairCache<K: Ord>`), it certifies memory-corrupting Rust code as unconditionally safe without surfacing any caller precondition or TCB waiver—enabling a `#![forbid(unsafe_code)]` caller with a stateful `EvilKey` to trigger immediate OOB UB.
4. **`SafeTraitCoherentOnly` vs. `UnsafeTraitVerifiedLaw` and Coherence-Keyed Dispatch in Lean 4:**
   - **Two-Class Polarity Split:** For safe traits (`SafeTraitCoherentOnly`), `WellFormed` must be proved under a demonic open-call summary (arbitrary valid return values, arbitrary `!Freeze` mutations, and arbitrary unwinding), while algebraic laws (`LawfulOrd`) guard *only* functional postconditions (`SatisfiesPost`). Only Rust `unsafe trait`s (`UnsafeTraitVerifiedLaw`) may guard `WellFormed`, paired with mandatory proof discharge on every crate-local `unsafe impl`.
   - **Coherence-Keyed Lookup `(MirTyId, TraitDefId)`:** Unlike Lean 4's non-coherent `SynthInstance` resolution—where passing two individually lawful `Ord` instances (`asc` at `insert`, `desc` at `get`) corrupts invariants—keying dispatch to a `CoherentTraitTable` backed by Rust's RFC 2451 orphan/overlap rules yields judgmental dictionary equality (`rfl`) across calls.

## Applicability

This report covers the semantic boundary between safe and `unsafe` traits across the pinned repositories and papers in `REPORT.json`:

- **Rust compiler, standard library, and specifications:** `rust-lang/rust@4b5350e87e487aed08ab2f9f0160a4b2616438bc` (`rustc_hir_analysis`, `rustc_next_trait_solver`, `core`, `alloc`, `std`), `rust-lang/nomicon@b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` (`src/safe-unsafe-meaning.md`), `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/items/{traits,implementations}.md`), and `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFCs 1023 and 2451). Historical CVE comparisons contrast pre-fix releases (`1.34.0`–`1.34.1` for `CVE-2019-12083`; `< 1.50.0` for `CVE-2021-28875`; `< 1.52.0` for `CVE-2020-36323`, `CVE-2021-28876`–`28879`, `CVE-2021-31162`) against `4b5350e87e48`.
- **Ecosystem `unsafe trait` design and Lean 4 verification anchors:** `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897` (`zerocopy/src/lib.rs`), `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`THREAT_MODEL.md`, `trusted/lean/Trusted/MirSemantics.lean`), `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`FreezeVisitor.lean`, `VTable.lean`), and foundational Rust verification frameworks (RustBelt, RefinedRust, Aeneas, Creusot, Verus, and Bottu et al.).

**Relationship to Adjacent Corpus Packages:** Extends `rust-unsafe-traits-coinduction-gats-and-safety-invariants` (auto-trait coinduction, GATs, `unsafe_fields`) to adversarial implementations of *safe* traits; operationalizes `coherence-orphan-instances-and-module-system-compilation` for Lean 4 collection verification via `CoherentTraitTable`; and complements `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`.

## Findings

### 1. The Asymmetric Safe-vs-Unsafe Trait Contract in Rust

`Basis: normative + documentation + source + derived`

Under the Rust Reference (`src/items/traits.md`, `src/unsafety.md` at `c9cc32825b03`) and the Rustonomicon (`src/safe-unsafe-meaning.md:58-149` at `b0bb569883a3`), `unsafe` on trait declarations shifts proof obligations from generic consumers to trait implementors:

1. **Syntactic Polarity Enforcement Only (`compiler/rustc_hir_analysis/src/coherence/unsafety.rs:14-122` at `4b5350e87e48`):** `check_item` rejects safe `impl`s of `unsafe trait`s (and `Copy` on types with `has_unsafe_fields()`) with `E0200` (`L55-87`), and rejects `unsafe impl`s of safe traits (unless `#[may_dangle]` is present) with `E0199` (`L37-53`). Neither check inspects semantic laws.
2. **Open-World Universal Quantification (`safe-unsafe-meaning.md:61-130`):** Rust's library soundness guarantee (formalized in **RustBelt**, Jung et al., POPL 2018, DOI `10.1145/3158154`) states that **no `#![forbid(unsafe_code)]` client can trigger Undefined Behavior**. While `unsafe` code may trust concrete safe dependencies it chooses to import (`safe-unsafe-meaning.md:86-99`), generic `unsafe` code parameterized over `T: SafeTrait` faces arbitrary client-supplied implementations that may mutate interior `!Freeze` state (`AtomicBool`, `Cell`, `RefCell`), return inconsistent results across calls, re-enter library APIs, or unwind via `panic!`.
3. **Safe Traits vs. Paired `unsafe` Companion Traits (`rust-lang/rust@4b5350e87e48` & `google/zerocopy@ec133ce4d799`):** Whenever `unsafe` code must omit runtime bounds, initialization, or bit-validity checks, Rust introduces an explicit `unsafe trait`:

| Domain | Safe Trait (`#![forbid(unsafe_code)]`) | Documented Logical Law (Logic Error Only) | Paired `unsafe trait` for Unchecked `unsafe` Reliance | Primary Source Coordinates |
| :--- | :--- | :--- | :--- | :--- |
| **Ordering** | `PartialOrd`, `Ord` | Reflexive, antisymmetric, transitive total order (`cmp.rs:1016-1046`) | *(None in `core`; Rustonomicon hypothetical `UnsafeOrd`)* | `core/src/cmp.rs:1046`; `nomicon/src/safe-unsafe-meaning.md:119` |
| **Hashing / Keys** | `PartialEq`, `Eq`, `Hash`, `Borrow<B>` | `k1 == k2 -> hash(k1) == hash(k2)`; `Borrow` matches `Eq`/`Ord`/`Hash` | *(None; `HashMap`/`BTreeMap` enforce physical bounds defensively)* | `core/src/hash/mod.rs:185`; `core/src/borrow.rs:158`; `std/src/collections/hash/map.rs:43-58` |
| **Iteration** | `Iterator`, `ExactSizeIterator` | `size_hint() -> (lo, Option<hi>)` bounds remaining elements | `TrustedLen`, `TrustedStep`, `TrustedFused`, `InPlaceIterable` | `core/src/iter/traits/iterator.rs:132-191`; `core/src/iter/traits/marker.rs:13,67,92,119` |
| **Cloning** | `Clone` (`clone`, `clone_from`) | Returns owned value | `CloneToUninit` (guarantees `*dest` initialized), `TrivialClone` | `core/src/clone.rs:608`; `alloc/src/slice.rs:844` |
| **Dereferencing** | `Deref`, `DerefMut` | Pure borrow projection `&Self::Target` (`deref.rs:139-150`) | Private `helper::Pin` (`#85099`) & `PinMacroHelper` (`#153438`) | `core/src/ops/deref.rs:139`; `core/src/pin.rs:1698-1712,2145-2200` |
| **Type Identity** | `Error` | Diagnostic reporting | `Error::type_id` sealed via `private::Internal` (`#60784`) | `core/src/error.rs:116-127` |
| **Byte Layout** | `AsRef<[u8]>`, `From<[u8; N]>` | Value conversion | `zerocopy::{Immutable, TryFromBytes, FromBytes, IntoBytes}` | `google/zerocopy` `zerocopy/src/lib.rs:1729,1965,4358,6005` |

Crucially, `ExactSizeIterator` (`core/src/iter/traits/iterator.rs:132-145`) is a **safe** trait whose `len()` cannot be trusted for unchecked memory writes—hence `pub const unsafe trait TrustedLen` (`marker.rs:67`). Likewise, writing a clone directly into uninitialized DST memory requires `pub unsafe trait CloneToUninit` (`core/src/clone.rs:608-622`) because safe `Clone` code cannot be trusted to initialize raw `*mut u8` storage.

---

### 2. Primary-Source Anatomy of `std` CVEs and Defensive Collection Hardening

`Basis: source + normative + documentation + execution + derived`

Inspecting historical `std` vulnerabilities alongside `rust-lang/rust@4b5350e87e487aed08ab2f9f0160a4b2616438bc` isolates four failure modes and their exact structural cures:

#### 2.1 Unsealed Default Methods on Safe Traits (`CVE-2019-12083`, `Error::type_id`)

Rust `1.34.0` stabilized `Error::type_id(&self) -> TypeId` with default body `TypeId::of::<Self>()` and relied on `self.type_id() == TypeId::of::<T>()` inside `dyn Error::downcast_ref::<T>()` before casting `*const dyn Error` to `*const T`. Because `Error` is a safe trait, a `#![forbid(unsafe_code)]` implementation overriding `fn type_id(&self) -> TypeId { TypeId::of::<Box<usize>>() }` caused safe downcasting to interpret stack bytes as a heap pointer (`CVE-2019-12083`, patched in `1.34.2`). In `library/core/src/error.rs:116-127`, `type_id` is marked `#[unstable(feature = "error_type_id", reason = "this is memory-unsafe to override in user code", issue = "60784")]` and requires an unconstructible `private::Internal` argument, preventing external overrides.

#### 2.2 Multi-Pass Stateful Safe-Trait Drift (`CVE-2020-36323`, `<[S]>::join` & `CVE-2021-28875`, `Read::read_to_end`)

Pre-`1.52.0` `<[S]>::join` (`S: Borrow<str>`) summed `s.borrow().len()` in pass 1 (`reserved_len`), copied `s.borrow().as_bytes()` in pass 2, and ran `unsafe { v.set_len(reserved_len); String::from_utf8_unchecked(v) }`. Because `Borrow<str>` is safe, an interior-mutable `Cell<bool>` implementation returning an 8-byte `&str` on pass 1 and a 2-byte `&str` on pass 2 left 6 uninitialized bytes inside the resulting `String` (`CVE-2020-36323`). In `library/alloc/src/str.rs:114-175`:
1. `first` (`slice[0]`) is borrowed **only once** (`L160-163`);
2. Each remaining element copies through `copy_slice_and_advance!` (`L114-121`), which calls safe **checked** `target.split_at_mut(len)`—panicking cleanly if an element grows on pass 2 (`L143-144`); and
3. Final `Vec` length tracks actual written bytes (`reserved_len - target.len()`), leaving spare uninitialized bytes outside `len` if an element shrinks (`L145-146`).

Similarly, `CVE-2021-28875` (`Read::read_to_end`, Rust `< 1.50.0`) trusted untrusted safe `Read::read` return counts to advance `Vec::set_len` over uninitialized spare capacity, fixed by tracking initialized high-water marks via `BorrowedBuf`.

#### 2.3 Unsafe Specialization Trait Composition (`CVE-2021-31162` & `CVE-2021-28876`–`28879`)

Even internal `unsafe` traits fail if safe callback panics or arithmetic saturation break single-read invariants:
- **`CVE-2021-31162` (`Vec::from_iter` / `InPlaceIterable`):** An unwinding `Drop` or closure during in-place `Vec` collection left overlapping ownership between the source drop guard and destination `Vec`, causing a double-free (`< 1.52.0`).
- **`CVE-2021-28876`–`28879` (`core::iter::Zip` + `TrustedRandomAccess`):** `TrustedRandomAccess::__iterator_get_unchecked(i)` moves out of index `i` on in-place adapters and must never be called twice for the same `i`. Panics (`28876`), nested `Zip`s (`28877`), mixed `next`/`next_back` (`28878`), and `size_hint` overflow (`28879`) caused duplicate index reads or OOB accesses. Note `library/core/src/iter/traits/marker.rs:49-58`, documenting why `Skip<I>` cannot implement `TrustedLen` even when `I: TrustedLen`: an inner iterator with `> usize::MAX` elements saturates `size_hint` to `(usize::MAX, None)`, erasing the true count.

#### 2.4 Defensive Invariants Against Adversarial `Ord` and `DerefMut` (`driftsort`, `ipnsort`, `BTreeMap`, `BinaryHeap`, `HashMap`, `pin!`)

1. **Permutation-Preserving RAII Gap Guards (`smallsort.rs`, `merge.rs`, `quicksort.rs`, `binary_heap/mod.rs`):**
   - Unlike C++ `std::sort` (where reflexive `x < x == true` drives unguarded linear insertion out of bounds), Rust's `insert_tail` (`library/core/src/slice/sort/shared/smallsort.rs:536-571`) checks `if sift == begin { break; }` (`L560`) prior to `sift = sift.sub(1)` (`L565`) and tracks the displaced element in `CopyOnDrop { src: &*tmp, dst: tail, len: 1 }` (`L551-558`).
   - `driftsort`'s `MergeState` (`library/core/src/slice/sort/stable/merge.rs:51-150`) copies the shorter run `save_len` to `scratch` and maintains `(self.end - self.start) == remaining_gap_in_v` before every `is_less` call (`L90`, `L122`). If `is_less` panics or violates transitivity, `MergeState::drop` (`L139-149`) copies `self.start..self.end` into `self.dst`, preserving an exact permutation of all original elements (`alloc/src/slice.rs:109-115`).
   - `ipnsort`'s `quicksort` (`library/core/src/slice/sort/unstable/quicksort.rs:50-114`) guards `if pivot >= len { intrinsics::abort_immediate(); }` (`L104-106`), partitions `v[1..]` so `num_lt < v.len()` (`L65`) holds regardless of `is_less`, and uses checked slicing `v = &mut v[(num_lt + 1)..]` (`L56`) on `ancestor_pivot`.
   - `BinaryHeap` (`library/alloc/src/collections/binary_heap/mod.rs:1530-1563`) uses `struct Hole<'a, T>` (`ManuallyDrop<T>`) to refill `data[self.pos]` on comparator panic.
2. **Collection Logic-Error Containment & `#[fundamental]` Sealing:**
   - `BTreeMap` (`library/alloc/src/collections/btree/map.rs:53-58`) and `HashMap` (`library/std/src/collections/hash/map.rs:39-58`) bound physical node/bucket indices independently of `Ord`/`Hash`/`Eq`, confining comparator inconsistencies to logic errors.
   - Because `Pin<Ptr>` is `#[fundamental]` (`core/src/pin.rs:1087`), `core::pin` delegates `DerefMut` through non-fundamental `helper::Pin` (`L1698-1712`, fixing `#85099`) and wraps `pin!($value)` in `PinMacroHelper` (`L2145-2200`, fixing `#153438`) so malicious downstream `DerefMut` impls cannot forge mutable access or mis-target `Pin::new_unchecked`.

---

### 3. Why Naive `LawfulOrd` Typeclass Axioms Break Verification Soundness

`Basis: source + execution + derived`

Deductive Rust verifiers—including **Aeneas** (Ho & Protzenko, ICFP 2022, DOI `10.1145/3547647`), **Creusot** (Denis et al., ICFEM 2022, DOI `10.1007/978-3-031-10872-6_6`), **Verus** (Lattuada et al., OOPSLA 2023, DOI `10.1145/3586037`), and **RefinedRust** (Gäher et al., PLDI 2024, DOI `10.1145/3656422`)—translate Rust trait bounds into logical dictionaries or trait predicates. Under **Anneal**'s threat model (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `THREAT_MODEL.md:65-115, 248-276`), baseline UB-freedom (`WellFormed` in `trusted/lean/Trusted/MirSemantics.lean:45-53`) is unconditional across safe callers, and every unproved assumption must be surfaced on the stated specification surface or TCB audit log.

Consider a generic cache whose author elides a bounds check using `K: Ord`:

```rust
pub struct SortedPairCache<K, V> { keys: Vec<K>, vals: Vec<V> } // keys.len() == vals.len()

impl<K: Ord, V> SortedPairCache<K, V> {
    pub fn get_two_step(&self, q: &K) -> Option<&V> {
        if self.keys.len() == 1 && self.keys[0].cmp(q) == core::cmp::Ordering::Equal {
            // Step 2 re-evaluates cmp assuming `K: Ord` is deterministic:
            let idx = if self.keys[0].cmp(q) == core::cmp::Ordering::Equal { 0 } else { 1 };
            Some(unsafe { self.vals.get_unchecked(idx) }) // UNSOUND!
        } else {
            None
        }
    }
}
```

A `#![forbid(unsafe_code)]` caller defines `struct EvilKey;` whose `Ord::cmp` flips a `static FLIP: AtomicBool` via `fetch_xor(true, Ordering::Relaxed)`, returning `Ordering::Equal` on call 1 and `Ordering::Less` on call 2. On `keys = vec![EvilKey], vals = vec![42u64]`, `get_two_step(&EvilKey)` computes `idx = 1` and executes out-of-bounds `vals.get_unchecked(1)` (`FaultKind.undefined`) in 100% safe Rust!

Exhaustive enumeration over a 2-key domain `{0, 1}` (`Basis: execution`, §Revalidation Probe) shows that only `3` of the $3^4 = 81$ deterministic comparator tables satisfy `LawfulOrd`, while `2` of the `9` two-step stateful traces (`(Equal, Less)` and `(Equal, Greater)`) trigger OOB `get_unchecked(1)` UB in `get_two_step` versus `0` UB traces when `idx < vals.len()` is checked. If a verifier injects `LawfulOrd K` while proving `WellFormed`, `cmp k q = cmp k q` makes `idx = 1` unreachable (`False`), silently certifying memory-corrupting Rust code with an empty TCB audit log! *(Even in Creusot/Verus where verified callers must discharge trait laws at monomorphization sites, an unverified safe Rust downstream crate linking against a verified library crate can pass `EvilKey` unless `WellFormed` holds without `LawfulOrd`.)*

---

### 4. Coherence-Keyed Dispatch vs. Proof-Assistant Typeclass Non-Coherence

`Basis: normative + source + execution + derived`

Even when `LawfulOrd` is restricted to functional postconditions ($\text{LawfulOrd}(K) \implies \text{set.contains}(x)$ after $\text{set.insert}(x)$)—or when an `unsafe trait` guards `WellFormed` across multiple calls—passing unkeyed Lean 4 typeclass dictionaries `[inst : Ord K]` introduces a second soundness hole (cf. `coherence-orphan-instances-and-module-system-compilation` and Bottu et al., ICFP 2019, DOI `10.1145/3341695`):

1. **The Two-Lawful-Dictionaries Swap:** Both `ord_asc(a, b) = compare a b` and `ord_desc(a, b) = compare b a` on `u32` satisfy **every** axiom of `LawfulOrd`. If `insert` builds `[10, 20, 30]` under `ord_asc` and `contains` runs binary search for `10` under `ord_desc` (via local `letI` or explicit dictionary application in Lean 4), midpoint comparison `ord_desc(20, 10) = Less` searches `[30]` and returns `false` (`Basis: execution`, §Revalidation Probe)! For an `unsafe trait` invariant spanning `insert` and `get_unchecked`, dictionary swapping breaks physical memory safety despite both dictionaries satisfying `safetyLaw`.
2. **Rust's Global Coherence Anchor (`rustc_next_trait_solver/src/coherence.rs` & `VTable.lean:68-93`):** Under RFC 1023 / RFC 2451 orphan and overlap rejection (`E0119`), post-borrowck lifetime-erased `Runtime(PostCleanup)` MIR admits at most one implementation per closed `(MirTyId, TraitDefId)`. For `&dyn Trait`, `Miri/Interpreter/VTable.lean:68-93` (`proofs-rs/lean-miri@c92d1d9754c9`) resolves `vtable_ptr` in `globalVTable`, strips auto traits via `sortedPredicates` (`L68`), and rejects forged cross-trait fat-pointer casts with `InvalidVTableTrait` UB (`L77, L81`).
3. **Canonical `CoherentTraitTable`:** Indexing trait semantics by `CoherenceKey (tyId, traitId)` inside the captured MIR `Program` guarantees `lookupCoherent table k = some s1` and `lookupCoherent table k = some s2` imply `s1 = s2` definitionally (`rfl`) across every call site in the crate.

---

### 5. Mechanizing `SafeTraitCoherentOnly` vs. `UnsafeTraitVerifiedLaw` in Lean 4 (`v4.34.1`)

`Basis: source + derived`

In Lean 4 (`v4.34.1`, restricted to `prelude` + `Init.*` and `{propext, Quot.sound, Classical.choice}`), trait obligations split cleanly into two constructors keyed by `rustc`'s `tcx.trait_def(def_id).safety`:

- **`SafeTraitCoherentOnly` (`Safety::Safe`):** Calls to `<T as SafeTrait>::m` execute against a demonic open-call summary (returning any valid output of the return `MirTy`, mutating any reachable `!Freeze` `UnsafeCell` byte ranges per `Miri/TreeBorrows/FreezeVisitor.lean:80-100`, or unwinding). `WellFormed` is proved universally over **all** `sem : ImplSem`; `logicalLaw sem` guards **only** `postCond`.
- **`UnsafeTraitVerifiedLaw` (`Safety::Unsafe`):** `safetyLaw sem` may guard both `WellFormed` and `postCond`, provided (1) every crate-local positive `unsafe impl` discharges `safetyLaw` in `LocalImplsVerified` (without coinductive self-cycles) or logs an explicit TCB waiver, and (2) custom `unsafe trait` law definitions appear on the human-reviewed specification surface (`THREAT_MODEL.md:82-98, 259-264`).

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Verification.TraitSoundness

structure CoherenceKey where
  tyId    : Nat
  traitId : Nat

def CoherenceKey.beq (a b : CoherenceKey) : Bool :=
  Nat.beq a.tyId b.tyId && Nat.beq a.traitId b.traitId

structure CoherentEntry (ImplSem : Type) where
  key : CoherenceKey
  sem : ImplSem

def lookupCoherent {ImplSem : Type}
    (table : List (CoherentEntry ImplSem)) (k : CoherenceKey) : Option ImplSem :=
  match table with
  | [] => none
  | e :: rest =>
    match CoherenceKey.beq e.key k with
    | true  => some e.sem
    | false => lookupCoherent rest k

theorem lookupCoherent_unique {ImplSem : Type}
    (table : List (CoherentEntry ImplSem)) (k : CoherenceKey) (s1 s2 : ImplSem)
    (h1 : lookupCoherent table k = some s1)
    (h2 : lookupCoherent table k = some s2) : s1 = s2 := by
  rw [h1] at h2
  injection h2

inductive TraitDiscipline (ImplSem : Type) where
  | safeTraitCoherentOnly  (logicalLaw : ImplSem → Prop)
  | unsafeTraitVerifiedLaw (safetyLaw  : ImplSem → Prop)

def GenericFnObligation {ImplSem Input Output : Type}
    (disc        : TraitDiscipline ImplSem)
    (wellFormed  : ImplSem → Input → Prop)
    (execReaches : ImplSem → Input → Output → Prop)
    (postCond    : ImplSem → Input → Output → Prop) : Prop :=
  match disc with
  | .safeTraitCoherentOnly logicalLaw =>
    (∀ (sem : ImplSem) (x : Input), wellFormed sem x) ∧
    (∀ (sem : ImplSem) (x : Input) (y : Output),
      logicalLaw sem → execReaches sem x y → postCond sem x y)
  | .unsafeTraitVerifiedLaw safetyLaw =>
    (∀ (sem : ImplSem) (x : Input), safetyLaw sem → wellFormed sem x) ∧
    (∀ (sem : ImplSem) (x : Input) (y : Output),
      safetyLaw sem → execReaches sem x y → postCond sem x y)

def LocalImplsVerified {ImplSem : Type}
    (table : List (CoherentEntry ImplSem))
    (localKeys : List CoherenceKey)
    (traitClass : Nat → TraitDiscipline ImplSem) : Prop :=
  ∀ k, k ∈ localKeys →
    match traitClass k.traitId, lookupCoherent table k with
    | .safeTraitCoherentOnly _, some _ => True
    | .unsafeTraitVerifiedLaw safetyLaw, some sem => safetyLaw sem
    | _, none => False

end Verification.TraitSoundness
```

## Boundaries

- **Lifetime-Dependent Specialization (`known not to apply`):** Uniqueness of `(MirTyId, TraitDefId)` after region erasure is **known not to apply** under incomplete `#![feature(specialization)]` or lifetime-sensitive `#[rustc_allow_lifetime_dependent_specialization]` impls (`marker.rs:65`, `sort/shared/mod.rs:10`); soundness requires `always_applicable` impls.
- **Legacy `OrphanCheckMode::Compat` Projection Warning (`known not to apply` without lint-denial):** In `compiler/rustc_next_trait_solver/src/coherence.rs:20-33`, `rustc` warns (`UNCOVERED_PARAM_IN_PROJECTION`) rather than rejecting legacy uncovered projections; cross-crate coherence proofs require denying that lint until `OrphanCheckMode::Proper` is enforced unconditionally.
- **GATs and Higher-Ranked `for<'a>` Trait Bounds (`not examined` in `CoherenceKey`):** Extending `CoherenceKey` to Generic Associated Type families and higher-ranked region binders was **not examined** in the minimal Lean model above (see `rust-unsafe-traits-coinduction-gats-and-safety-invariants`).
- **Cross-DSO Symbol Interposition (`cdylib` / `dlopen`, `unsupported`):** Linking separately compiled shared libraries with conflicting trait symbols or transmuting `dyn Trait` vtables across compiler versions is **unsupported** by Rust's coherence guarantees.
- **Full Unwind-Corner Verification of `alloc::collections::BTreeMap` (`unknown` pending mechanization):** While `btree/map.rs:53-58` normatively forbids UB on inconsistent or panicking `Ord` keys, whether every node-split/allocator unwind path in `alloc::collections::btree` currently upholds that invariant without exception remains **unknown** until mechanically verified under `SafeTraitCoherentOnly`.

## Evidence

1. **Specifications & RFCs:** `rust-lang/nomicon@b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` (`src/safe-unsafe-meaning.md:58-149`); `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/items/{traits,implementations}.md`); `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`text/1023-rebalancing-coherence.md`, `text/2451-re-rebalancing-coherence.md`).
2. **Compiler & Standard Library (`rust-lang/rust@4b5350e87e487aed08ab2f9f0160a4b2616438bc`):**
   - `compiler/rustc_hir_analysis/src/coherence/unsafety.rs:14-122` (`E0199`/`E0200`); `compiler/rustc_next_trait_solver/src/coherence.rs:20-33`.
   - `library/core/src/cmp.rs:1016-1057` (`Ord`); `library/core/src/hash/mod.rs:160-194` (`Hash`); `library/core/src/borrow.rs:133-169` (`Borrow`); `library/core/src/ops/deref.rs:133-150` (`Deref`); `library/core/src/clone.rs:598-622` (`CloneToUninit` at `L608`).
   - `library/core/src/iter/traits/iterator.rs:131-192` (`size_hint`) & `library/core/src/iter/traits/marker.rs:10-119` (`TrustedFused` `L13`, `Skip` note `L49-58`, `TrustedLen` `L67`, `InPlaceIterable` `L92`, `TrustedStep` `L119`).
   - `library/core/src/error.rs:115-127` (`Error::type_id` sealed with `private::Internal`, `#60784` / `CVE-2019-12083`).
   - `library/alloc/src/str.rs:72-175` (`join_generic_copy` `# Safety notes` `L132-146`, single first borrow `L160-163`, checked `split_at_mut` `L114-121` for `CVE-2020-36323`).
   - `library/core/src/slice/mod.rs:3095-3204`, `library/alloc/src/slice.rs:104-136, 828-888`, `library/core/src/slice/sort/shared/smallsort.rs:279-296, 536-571`, `library/core/src/slice/sort/stable/merge.rs:51-150`, `library/core/src/slice/sort/unstable/quicksort.rs:50-114` (`driftsort` and `ipnsort` bounds and `CopyOnDrop`/`MergeState` invariants).
   - `library/alloc/src/collections/btree/map.rs:53-58`, `library/alloc/src/collections/binary_heap/mod.rs:1530-1563` (`Hole`), `library/std/src/collections/hash/map.rs:39-58`, and `library/core/src/pin.rs:1087, 1698-1712, 2145-2200` (`helper::Pin` `#85099`, `PinMacroHelper` `#153438`).
3. **Ecosystem, Mechanized Semantics & Literature:** `google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897` (`zerocopy/src/lib.rs:1729, 1965, 4358, 6005`); `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`THREAT_MODEL.md:58-122, 234-281`, `trusted/lean/Trusted/MirSemantics.lean:45-108`); `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/TreeBorrows/FreezeVisitor.lean:80-100`, `Miri/Interpreter/VTable.lean:68-93`); Jung et al. (`10.1145/3158154`), Gäher et al. (`10.1145/3656422`), Ho & Protzenko (`10.1145/3547647`), Denis et al. (`10.1007/978-3-031-10872-6_6`), Lattuada et al. (`10.1145/3586037`), Bottu et al. (`10.1145/3341695`).
4. **Execution (`2026-11-20`, Python `3.13.15` on `x86_64` Linux):** Ran §Revalidation probe (`exit 0`), verifying `81` static 2-key comparator tables (`3` lawful), `2` OOB UB traces under naive `LawfulOrd` vs. `0` under `SafeTraitCoherentOnly`, pre-`1.52.0` vs. modern `CVE-2020-36323` behavior, and lookup miss (`false`) on incoherent `asc`/`desc` dictionary swap.

## Revalidation

1. **Upstream Diff Checks (~5 seconds):** Check `compiler/rustc_hir_analysis/src/coherence/unsafety.rs` (`check_item`), `library/core/src/error.rs` (`type_id`), `library/alloc/src/str.rs` (`join_generic_copy`), and `library/core/src/pin.rs` (`helper::Pin`, `PinMacroHelper`) to verify private-token and non-fundamental wrapper guards remain intact.
2. **Deterministic Model Probe (<0.1 seconds, Python 3.10+ stdlib only):**

```python
#!/usr/bin/env python3
"""Self-contained revalidation probe for safe-vs-unsafe trait soundness boundaries."""
from __future__ import annotations
import itertools
import json

ORDS = (-1, 0, 1)

def is_lawful_ord_2key(tbl: dict[tuple[int, int], int]) -> bool:
    return (
        all(tbl[(a, a)] == 0 for a in (0, 1))
        and all(tbl[(a, b)] == -tbl[(b, a)] for a in (0, 1) for b in (0, 1))
    )

def buggy_unchecked_cache_op(cmp_seq: list[int]) -> bool:
    it = iter(cmp_seq)
    if next(it) == 0:
        idx = 0 if next(it) == 0 else 1
        return idx < 1
    return True

def defensive_cache_op(cmp_seq: list[int]) -> bool:
    it = iter(cmp_seq)
    if next(it) == 0:
        idx = 0 if next(it) == 0 else 1
        return True if idx >= 1 else (idx < 1)
    return True

def model_join_cve_2020_36323(pass1: list[int], pass2: list[int], sep: int) -> dict[str, bool]:
    pre_res = sum(pass1) + sep * max(0, len(pass1) - 1)
    pre_wrt = sum(pass2) + sep * max(0, len(pass2) - 1)
    rem = pass1[0] + sum(pass1[1:]) + sep * max(0, len(pass1) - 1)
    mod_res = rem
    panicked = False
    written = pass1[0]
    rem -= pass1[0]
    for l2 in pass2[1:]:
        if sep > rem or l2 > rem - sep:
            panicked = True
            break
        rem -= sep + l2
        written += sep + l2
    final_len = 0 if panicked else (mod_res - rem)
    return {
        "pre152_exposes_uninit": pre_wrt < pre_res,
        "modern_panicked_safely": panicked,
        "modern_exposes_uninit": (not panicked) and (final_len > written),
    }

def binary_search_contains(keys: list[int], q: int, cmp_fn) -> bool:
    lo, hi = 0, len(keys)
    while lo < hi:
        mid = (lo + hi) // 2
        c = cmp_fn(keys[mid], q)
        if c < 0:
            lo = mid + 1
        elif c > 0:
            hi = mid
        else:
            return True
    return False

static_tables = [
    {(0, 0): v[0], (0, 1): v[1], (1, 0): v[2], (1, 1): v[3]}
    for v in itertools.product(ORDS, repeat=4)
]
lawful_count = sum(1 for t in static_tables if is_lawful_ord_2key(t))
buggy_ub = sum(1 for s in itertools.product(ORDS, repeat=2) if not buggy_unchecked_cache_op(list(s)))
defensive_ub = sum(1 for s in itertools.product(ORDS, repeat=2) if not defensive_cache_op(list(s)))
shrink = model_join_cve_2020_36323([4, 8], [4, 2], 1)
grow = model_join_cve_2020_36323([4, 2], [4, 8], 1)
dict_swap_ok = binary_search_contains([10, 20, 30], 10, lambda a, b: (b > a) - (b < a))

assert len(static_tables) == 81 and lawful_count == 3
assert buggy_ub == 2 and defensive_ub == 0
assert shrink == {"pre152_exposes_uninit": True, "modern_panicked_safely": False, "modern_exposes_uninit": False}
assert grow == {"pre152_exposes_uninit": False, "modern_panicked_safely": True, "modern_exposes_uninit": False}
assert dict_swap_ok is False
print(json.dumps({"status": "ok", "static_tables": 81, "lawful": 3, "buggy_ub": buggy_ub, "defensive_ub": defensive_ub}))
```

3. **Verifier Canary Test:** Submit `SortedPairCache::get_two_step<K: Ord, V>` with zero `unsafe` preconditions and zero TCB waivers. Any sound Rust verifier **must reject** `WellFormed` (`exit 1`) rather than assuming `LawfulOrd K`.
