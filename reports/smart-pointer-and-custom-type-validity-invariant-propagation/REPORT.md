# Smart-Pointer (`Vec`, `Box<[T]>`, `Arc<[T]>`, `SmallVec`, `Bytes`, `NonNull`) and Custom Type-Validity Invariant Propagation

## Summary

In `rust-postcleanup-mir-type-validity-and-range-invariant-catalog`, language-level slice length validity (`VAL-08`: $\text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ for $\text{sizeof}(T) \ge 1$) applied directly to `&[T]`, `&mut [T]`, and `Box<[T]>`, whereas standard-library and ecosystem smart-pointer ADTs (`Vec<T>`, `String`, `Rc<[T]>`, `Arc<[T]>`, `SmallVec<[T; N]>`, `Bytes`, `NonNull<[T]>`) lowered to `Runtime(PostCleanup)` MIR struct fields whose length or metadata scalar had raw type `usize` (`0..=usize::MAX`). By auditing `library/alloc/src/{vec/mod.rs,raw_vec/mod.rs,sync.rs,rc.rs,boxed.rs}` and `library/core/src/{num/niche_types.rs,ptr/non_null.rs,ptr/unique.rs}` in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), inspecting the emitted `Runtime(PostCleanup)` MIR and LLVM `23.1.1` IR across 11 container access patterns ([`support/inspect_smart_pointer_mir_invariants.py`](support/inspect_smart_pointer_mir_invariants.py), [`support/smart_pointer_layout_and_mir_catalog.json`](support/smart_pointer_layout_and_mir_catalog.json)), and mechanizing the two-tier invariant propagation bridge in Lean `v4.34.1` ([`support/SmartPointerValidityAndTypeInvariantProbe.lean`](support/SmartPointerValidityAndTypeInvariantProbe.lean)), we establish four governing findings:

1. **Exact `rustc 1.99.1` Field Layouts, `UsizeNoHighBit`, and the `Vec::len` vs. `Vec::as_slice` Asymmetry:**
   - In `library/alloc/src/raw_vec/mod.rs:39,85-94` and `library/core/src/num/niche_types.rs:113,128`, `Vec<T>` stores its capacity in `RawVecInner.cap` of type `Cap = core::num::niche_types::UsizeNoHighBit`, defined as `pattern_type!(usize is 0..=HALF_USIZE)` (`0..=0x7fff_ffff_ffff_ffff`, i.e., $0 \le \text{cap} \le \texttt{isize::MAX}$). Thus `RawVecInner.cap` carries a **Tier 1 language-level `WrappingRange` invariant** ($\text{cap} \le 2^{63}-1$ on 64-bit targets), and `rustc 1.99.1 -C opt-level=3` emits `range(i64 0, -9223372036854775808)` on `@vec_u8_capacity`.
   - By contrast, `Vec<T>.len` (`library/alloc/src/vec/mod.rs:438`) is a plain `usize`. To communicate `len <= T::MAX_SLICE_LEN` (`isize::MAX / sizeof(T)`), `Vec::len(&self)` (`vec/mod.rs:3100-3109`) executes `unsafe { intrinsics::assume(len <= T::MAX_SLICE_LEN) };` (`StatementKind::Intrinsic(NonDivergingIntrinsic::Assume)`).
   - However, `Vec::as_slice(&self) -> &[T]` (`vec/mod.rs:1848-1867`, which `<Vec<T> as Deref>::deref` calls) reads `self.len` **directly** without calling `self.len()`, constructing `&*core::intrinsics::aggregate_raw_ptr::<*const [T], _, _>(self.as_ptr(), self.len)`. Because `rustc 1.99.1` omits `!range` metadata on intermediate `&[T]` locals (`layout.rs:504`), `@vec_u8_as_slice_len(v: &Vec<u8>)` loses the upper bound $\text{len} \le 2^{63}-1$ entirely—and LLVM `23.1.1`'s `MergeFunctions` pass aliases `@vec_zst_len` directly to `@vec_u8_as_slice_len`!
2. **Why `while i + 16 <= v.len()` Retains 100% (`32 / 32` Unrolled) of Its Bounds Checks in Stock `rustc 1.99.1 -O3`:**
   - Even when the loop header calls `v.len()` (emitting `@llvm.assume(len <= isize::MAX)`), stock `rustc 1.99.1 -C opt-level=3` leaves **`32` `panic_bounds_check` calls** (`16` in the peeled/unrolled loop + `16` in the main loop body) in `@vec_chunk16_sum_stock` (`support/smart_pointer_layout_and_mir_catalog.json`). Inside the loop body, each `v[i + k]` invokes `Deref::deref(v)` $\rightarrow$ `v.as_slice()`, and LLVM's `ConstraintElimination` + `CorrelatedValuePropagation` fail to upgrade the wrapping loop-header addition `i + 16` to `add nuw` across the 16 conditional panic blocks.
3. **Two-Tier Invariant Architecture in `MiniSSA`'s $\Gamma_{\text{valid}}$ (`seedAdtFieldValidRanges_sound` and `TypeInvariantContract_sound`):**
   - **Tier 1 (Language Layout & Niche Validity — Unconditional):** Recursive ADT field traversal (`seedAdtFieldValidRanges_sound`) inspects every non-`MaybeUninit`, non-`UnsafeCell` leaf field of any loaded or borrowed ADT, seeding $0 \le \text{cap} \le \texttt{isize::MAX}$ from `UsizeNoHighBit`, $\text{addr}(\text{ptr}) \ge 1$ from `NonNull<T>` / `Unique<T>`, and $\text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ whenever `&[T]` is materialized by `Vec::as_slice()` or `Arc<[T]>::deref()`.
   - **Tier 2 (Modular Relational Type Invariants — `#[anneal_spec::type_invariant]`):** Relational invariants between private ADT fields (`vec.len <= vec.cap && vec.cap * sizeof(T) <= isize::MAX`, `smallvec.len <= smallvec.capacity()`, `bytes.len <= isize::MAX`) are verified once at the defining module's public constructor and `&mut` method boundaries (`TypeInvariantContract_sound`), allowing private helpers to temporarily break the invariant internally while guaranteeing that every external caller entry receives $I_{\text{adt}}(s)$ in $\Gamma_{\text{valid}}$.
4. **Why `NonNull<[T]>` and `Arc<[T]>` Raw Fat Pointers Differ Before vs. After `Deref` (`nonNullSliceRawMetadata_usizeMax_not_bounded_rejected`):**
   - `NonNull<[T]>` (`library/core/src/ptr/non_null.rs:79-81`) and `Arc<[T]>.ptr` (`NonNull<ArcInner<[T]>>`, `library/alloc/src/sync.rs:278`) are raw fat pointers (`pattern_type!(*const ... is !null)`). At the language bit-validity level, only scalar `0` (the data address) is constrained to `1..=usize::MAX`; scalar `1` (the slice length metadata) has full `0..=usize::MAX` validity because `NonNull::slice_from_raw_parts(NonNull::dangling(), usize::MAX)` is safe without allocation.
   - `checkSmartPtrMaxSliceLenSeed` therefore rejects `NonNull<[T]>` and `*const [T]` (`= false`) unless accompanied by a dereference to `&[T]` or a verified container `TypeInvariantSummary`.

## Applicability

- **Extends:** `rust-postcleanup-mir-type-validity-and-range-invariant-catalog`, `type-validity-seeded-range-and-farkas-bounds-check-elimination`, `anneal-spec-minissa-normalization-and-proof-compression`
- **Subjects:**
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)**: `library/alloc/src/{vec/mod.rs,raw_vec/mod.rs,sync.rs,rc.rs,boxed.rs}`, `library/core/src/{num/niche_types.rs,ptr/non_null.rs,ptr/unique.rs}`, and `compiler/rustc_ty_utils/src/layout.rs`.
  - **LLVM (`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `23.1.1`)**: `-C opt-level=3` `range(...)` attributes, `@llvm.assume`, `MergeFunctions`, and `ConstraintElimination`.
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel verification of `SmartPointerValidityAndTypeInvariantProbe.lean`.
  - **Anneal (`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`)**: `#[anneal_spec]` and modular `type_invariant` propagation.

## Findings

### 1. Catalog of Smart-Pointer Representations and Invariants in `rustc 1.99.1`

`Basis: source + execution (support/inspect_smart_pointer_mir_invariants.py, support/smart_pointer_layout_and_mir_catalog.json)`

Table 1 records the `Runtime(PostCleanup)` MIR field layout, Tier 1 language validity, inlined `Assume` behavior, Tier 2 relational invariant, and emitted LLVM `23.1.1` IR across all seven container families in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):

| Container / Smart-Pointer Type | `rustc 1.99.1` Source Coordinates | `Runtime(PostCleanup)` MIR Leaf Fields | Tier 1 Language Validity (`WrappingRange` / `VAL-*`) | Inlined `Assume` / `Deref` Fact in `Runtime(PostCleanup)` MIR | Tier 2 Relational Invariant (`#[anneal_spec::type_invariant]`) | Emitted `range(i64 0, 2^63)` in Stock `rustc 1.99.1 -O3`? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Vec<T>` ($\text{sizeof}(T) \ge 1$)** | `alloc/src/vec/mod.rs:436-439`, `raw_vec/mod.rs:39,85-94` | `ptr: Unique<u8>`, `cap: UsizeNoHighBit`, `len: usize` | $\text{ptr} \ge 1$, $0 \le \text{cap} \le \texttt{isize::MAX}$; $\text{len} \in [0, \texttt{usize::MAX}]$ | `Vec::len()` emits `assume(len <= T::MAX_SLICE_LEN)` (`vec/mod.rs:3106`); `Vec::as_slice()` omits `assume` (`vec/mod.rs:1865`) | $\text{len} \le \text{cap} \land \text{cap} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ | **On `capacity()` & `len()` only; MISSED on `as_slice().len()`!** |
| **`Vec<ZST>` ($\text{sizeof}(T) = 0$)** | `alloc/src/raw_vec/mod.rs:46-48` | `ptr: Unique<u8>`, `cap: Cap(0)`, `len: usize` | $\text{ptr} \ge 1$, $\text{cap} = 0$; $\text{len} \in [0, \texttt{usize::MAX}]$ | `T::MAX_SLICE_LEN == usize::MAX` | $0 \le \text{len} \le \texttt{usize::MAX}$ (unbounded up to $2^{64}-1$) | **No** (correctly omitted) |
| **`String`** | `alloc/src/string.rs:365-367` | `vec: Vec<u8>` (`ptr`, `cap: UsizeNoHighBit`, `len: usize`) | $\text{ptr} \ge 1$, $0 \le \text{cap} \le \texttt{isize::MAX}$ | `String::len()` delegates to `Vec<u8>::len()` $\rightarrow$ `assume(len <= isize::MAX)` | $\text{len} \le \text{cap} \le \texttt{isize::MAX} \land \text{utf8}(\text{buf}[..\text{len}])$ | **Yes** (`@string_len`) |
| **`Box<[T]>` ($\text{sizeof}(T) \ge 1$)** | `alloc/src/boxed.rs:235-241` | `0: Unique<[T]>` (`ptr: NonNull<[T]>`), `1: Global` | `VAL-08`: $\text{addr}(\text{ptr}) \ge \text{align}(T) \land \text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ | `PtrMetadata(*b)` | Covered by Tier 1 `VAL-08` on `Box<[T]>` | **No (`Missed` on `@box_slice_len`!)** |
| **`Arc<[T]>` / `Rc<[T]>` ($\text{sizeof}(T) \ge 1$)** | `alloc/src/sync.rs:274-281,393-405`, `rc.rs:285-331` | `ptr: NonNull<ArcInner<[T]>>` (`data_ptr`, `len: usize`) | $\text{addr}(\text{ptr}) \ge 2$; raw metadata `len` is `0..=usize::MAX` before `Deref` | `Deref::deref` materializes `&[T]` (seeding `VAL-08`: $\text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$) | $16 + \text{len} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ | **No (`Missed` on `@arc_slice_len` & `@rc_slice_len`!)** |
| **`NonNull<[T]>` / `Unique<[T]>`** | `core/src/ptr/non_null.rs:79-81`, `unique.rs:35-43` | `pointer: pattern_type!(*const [T] is !null)` | $\text{addr}(\text{ptr}) \ge 1$; metadata $\text{len} \in [0, \texttt{usize::MAX}]$ | None (`NonNull::slice_from_raw_parts(dangling, usize::MAX)` is sound!) | None on standalone `NonNull<[T]>` | **No** (correctly omitted) |
| **`SmallVec<[T; N]>` / `Bytes`** | Ecosystem container ADTs | Discriminant/tag + inline array or `(ptr, len, cap)` | `NonNull` niche on heap pointer | `as_slice()` calls `slice::from_raw_parts`, materializing `&[T]` (`VAL-08`) | $\text{len} \le \text{cap} \land \text{cap} \cdot \text{sizeof}(T) \le \texttt{isize::MAX}$ | **No** |

Direct LLVM `23.1.1` IR evidence extracted by [`support/inspect_smart_pointer_mir_invariants.py`](support/inspect_smart_pointer_mir_invariants.py):

```llvm
; 1. Vec<u8>::capacity(&self) -> HAS range(i64 0, -9223372036854775808) from UsizeNoHighBit!
define noundef range(i64 0, -9223372036854775808) i64 @vec_u8_capacity(
    ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(24) %v)

; 2. String::len(&self) and Vec<u8>::len(&self) -> HAS range(i64 0, -9223372036854775808) from intrinsics::assume!
define noundef range(i64 0, -9223372036854775808) i64 @string_len(
    ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(24) %s)
@vec_u8_len = unnamed_addr alias i64 (ptr), ptr @string_len

; 3. Vec<u8>::as_slice(&self).len() -> MISSED! Merged with Vec<()>::len()!
define noundef i64 @vec_u8_as_slice_len(
    ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(24) %v)
@vec_zst_len = unnamed_addr alias i64 (ptr), ptr @vec_u8_as_slice_len

; 4. Arc<[u8]>::len(), Rc<[u8]>::len(), and Box<[u8]>::len() -> ALL MISSED!
define noundef i64 @arc_slice_len(
    ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(16) %a)
@box_slice_len = unnamed_addr alias i64 (ptr), ptr @arc_slice_len
@rc_slice_len = unnamed_addr alias i64 (ptr), ptr @arc_slice_len
```

---

### 2. Lean 4.34.1 Mechanization of Two-Tier Invariant Seeding and `Vec<T>` Loop BCE

`Basis: execution (support/SmartPointerValidityAndTypeInvariantProbe.lean)`

[`support/SmartPointerValidityAndTypeInvariantProbe.lean`](support/SmartPointerValidityAndTypeInvariantProbe.lean) (`252` lines, checked in `697.16 ms` with **`0` `sorryAx`** and **`0` `Lean.ofReduceBool`**) mechanizes the four governing theorems:

| Theorem Name | Tier & Role | Statement Summary | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `seedAdtFieldValidRanges_sound` | **Tier 1** (Recursive ADT Layout Range) | Any non-`MaybeUninit`, non-`UnsafeCell` leaf field with `rangeHi ≤ claimedUpper` satisfies `rangeLo ≤ v ∧ v ≤ claimedUpper` (`rawVecInner_cap_le_isizeMax`, `nonNull_ptr_nonzero`) | `[propext]` |
| `TypeInvariantContract_sound` | **Tier 2** (`#[anneal_spec::type_invariant]`) | If a private-field ADT's public constructors establish `inv` and public `&mut` methods preserve `inv`, every reachable external caller state `evalModuleTrace tr` satisfies `inv` | **None (`[]`)** |
| `vecChunk16LoopBce_eliminates_all_16` | **Tier 1 + Tier 2 $\rightarrow$ `MiniSSA` BCE** | Combining `VecTier1LanguageValid` (`cap ≤ isizeMax64`) and `VecTier2TypeInvariant` (`len ≤ cap`, `elemSize ≥ 1`) proves `add nuw` on `i + 16` and `i + k` and eliminates all **16 / 16** bounds checks (`0 → 16` eliminated vs. `32` surviving in stock `-O3`) | `[propext, Quot.sound]` |
| `nonNullSliceRawMetadata_usizeMax_not_bounded_rejected` | **Negative Soundness Guard** | Rejects seeding `len ≤ isizeMax64` on `NonNull<[u8]>`, `*const [u8]`, and `Vec<()>` (`elemSize = 0`) | **None (`[]`)** |

## Boundaries

1. **Trust-Boundary Rule for Tier 2 Type Invariants in Unverified Crates (`known not to apply` without either inlined `Assume` or an Anneal proof):**
   - Because Rust's module privacy does not prevent `unsafe` code inside a module from constructing a broken `Vec` (`vec.set_len(usize::MAX)`), the verified compiler (`MiniSSA` BCE) may use a Tier 2 relational invariant (`len <= cap`) to elide runtime bounds checks **only** when either:
     (a) the invariant is derived from a language-level `Intrinsic::Assume` statement (`Vec::len()`'s `intrinsics::assume(len <= T::MAX_SLICE_LEN)`) or a materialized `&[T]` reference (`VAL-08` in `Vec::as_slice()` / `Arc<[T]>::deref()`), where violating the invariant is already source-level language UB; or
     (b) the defining module carries a kernel-checked Anneal `TypeInvariantContract_sound` proof certifying that no public path violates $I_{\text{adt}}$.
2. **Interior Mutability Inside Custom Invariant-Bearing Fields (`known not to apply` for fields inside `UnsafeCell`):**
   - `checkAdtLeafUpperBound` enforces `!d.insideUnsafeCell`. If a struct stores an invariant-coupled field inside `Cell<usize>` or `AtomicUsize`, its value can be mutated through shared references `&S` without passing through `&mut S` method exits.

## Evidence

1. **Kernel-Checked Lean 4.34.1 Mechanization:**
   - [`support/SmartPointerValidityAndTypeInvariantProbe.lean`](support/SmartPointerValidityAndTypeInvariantProbe.lean): Proves `seedAdtFieldValidRanges_sound`, `TypeInvariantContract_sound`, `vecChunk16LoopBce_eliminates_all_16`, and `nonNullSliceRawMetadata_usizeMax_not_bounded_rejected` in `697.16 ms` (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
2. **`rustc 1.99.1` Smart-Pointer MIR/LLVM Inspector and Catalog:**
   - [`support/inspect_smart_pointer_mir_invariants.py`](support/inspect_smart_pointer_mir_invariants.py)
   - [`support/smart_pointer_layout_and_mir_catalog.json`](support/smart_pointer_layout_and_mir_catalog.json)
3. **`rustc 1.99.1` Standard Library Source Coordinates (`58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `library/core/src/num/niche_types.rs:113, 128` (`HALF_USIZE`, `UsizeNoHighBit`)
   - `library/alloc/src/raw_vec/mod.rs:39, 85-94` (`type Cap = UsizeNoHighBit`, `RawVecInner`)
   - `library/alloc/src/vec/mod.rs:436-439, 1848-1867, 3100-3109` (`Vec`, `Vec::as_slice`, `Vec::len`)
   - `library/alloc/src/sync.rs:274-281, 393-405` (`Arc`, `ArcInner`)
   - `library/core/src/ptr/non_null.rs:79-81` (`NonNull`)

## Revalidation

Run the `rustc 1.99.1` MIR/LLVM inspector and Lean `v4.34.1` probe:

```bash
python3 reports/smart-pointer-and-custom-type-validity-invariant-propagation/support/inspect_smart_pointer_mir_invariants.py
```
