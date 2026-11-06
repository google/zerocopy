# Rust Value Validity, Initialization, Padding, `MaybeUninit`, and Transmutation Semantics

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Rust's operational memory and value-representation contract across `nightly` and stable `1.99.1` separates **byte-level storage state**, **type-level value validity**, **library safety invariants**, and **static vs. dynamic operational obligations**:

1. **Three Distinct Meanings of "Valid" and Immediate Undefined Behavior:**
   - **Type/Value Validity:** Producing a value (by assigning to a place, reading from a place, passing to or returning from a function/intrinsic, or calling `assume_init` / `transmute`) that violates its Rust type's validity invariant is **immediate undefined behavior**, even if the value is never subsequently read or dereferenced.
   - **Operation-Relative Pointer Validity:** There is no context-free predicate "is this raw pointer valid?". A raw pointer's value validity requires only that its bytes be initialized (and for slice pointers, a valid `usize` length), whereas reading, writing, offsetting, or converting to a reference requires operation- and size-specific provenance, liveness, alignment, and aliasing permissions.
   - **Library Safety Invariants:** Satisfying compiler-level bit validity (e.g., constructing a `Vec<T>` with non-null pointer bytes) does not establish the stronger library invariants required by safe methods or `Drop::drop`.
   - **Well-Defined Execution Is Stronger Than Value Validity:** Even when every produced value is type-valid, execution can still incur UB via data races, dangling/misaligned place accesses, out-of-bounds projections, aliasing violations, mutating immutable bytes outside `UnsafeCell`, ABI mismatches, unwinding across non-unwinding FFI boundaries, or invalid inline assembly.
2. **Abstract Bytes, Padding, and Typed vs. Untyped Copies:**
   - Rust abstract memory consists of uninitialized bytes and initialized bytes (`0..=255` with optional pointer provenance). Uninitialized bytes are not fixed arbitrary integers; reading an uninitialized byte as an integer or raw pointer is immediate UB.
   - Valid aggregate values (`struct`, `tuple`, `enum`) permit uninitialized bytes in **padding** and inactive union storage.
   - **Typed Copies vs. Untyped Copies:** Moving or copying a value as a typed `T` or `MaybeUninit<T>` (including `fn identity<T>(x: T) -> T { x }`, `ptr::read`, `ptr::write`, and `mem::zeroed`) preserves `T`'s **non-padding** bytes and provenance, but **may discard or deinitialize bytes at `T`'s padding offsets** and may implicitly reborrow nested references. By contrast, untyped raw byte copies (`ptr::copy`, `ptr::copy_nonoverlapping`, and `ptr::swap_nonoverlapping` after upstream issue `#134713` / commit `0fe8f3454dbe9dda52a254991347e96bec579a6f`) preserve every byte's initialization state and provenance exactly without requiring source bytes to form a valid `T`.
3. **`MaybeUninit<T>` Representation, Lifecycle, and Niche Suppression:**
   - `MaybeUninit<T>` (`#[repr(transparent)]` over a union of `()` and `ManuallyDrop<T>`) suspends `T`'s value-validity invariant so any initialized or uninitialized byte sequence of size `size_of::<T>()` is valid. It tracks no runtime initialization flag and **never runs `T`'s destructor** when dropped.
   - `MaybeUninit<T>` shares `T`'s exact size, alignment, and call ABI, but **suppresses `T`'s layout niches** in enclosing containers (`size_of::<Option<bool>>() == 1` whereas `size_of::<Option<MaybeUninit<bool>>>() == 2`).
   - Crossing back to `T` via `assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`, or `assume_init_drop` requires all non-padding value bytes of `T` to be valid and initialized *before* the call. Gradual initialization must use `as_mut_ptr()` and raw field pointers (`&raw mut (*ptr).field`) rather than `assume_init_mut()`.
4. **Transmutation Semantics (`transmute`, `transmute_copy`, `TransmuteFrom`):**
   - `mem::transmute<Src, Dst>` enforces `size_of::<Src>() == size_of::<Dst>()` at the call site and performs a by-value bitwise move (forgetting `Src` without dropping it), which **does not guarantee padding preservation** and requires the transferred representation to be valid as `Dst`.
   - `mem::transmute_copy<Src, Dst>(&Src)` borrows `Src` (leaving the original value alive and creating duplicate-ownership hazards for non-`Copy` types), asserts `size_of::<Src>() >= size_of::<Dst>()`, and performs a typed read (`ptr::read_unaligned` when `align_of::<Dst>() > align_of::<Src>()`, else `ptr::read`).
   - Unstable `intrinsics::transmute_unchecked`, `mem::transmute_prefix`, `mem::transmute_neo`, and `mem::TransmuteFrom<Src, ASSUME>` separate size checking, union-prefix extension with uninitialized tail bytes, and compiler-checked union transmutability across four explicit `Assume` axes (`ALIGNMENT`, `LIFETIMES`, `SAFETY`, `VALIDITY`).
5. **87-Clause Operational-Semantics Ledger and Static-vs-Dynamic Premise Stratification (`minirust#288`):**
   - Across 87 primary-source clauses (`Seq-01`–`Seq-31`, `FFI-01`–`FFI-11`, `Drop-01`–`Drop-26`, `Conc-01`–`Conc-21`, `Model-01`–`Model-08`) pinned to Rust `1.99.1` and MiniRust (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`), static well-formedness (`Type::check_wf`, `Func::check_wf`) is strictly weaker than representation codec coherence (`StaticCodecCoherence`, `minirust#288`: where `Type::Enum` can have a `discriminator` that disagrees with `tagger`, and `Type::Union` can have `chunks` that truncate 16-byte wide-pointer metadata) and dynamic operational safety (`Terminator::Call` dynamic ABI checks, `ResumeUnwind` stack state, and memory/validity checks).

## Applicability

This report consolidates five primary-source investigations across two pinned Rust/Reference snapshots and the MiniRust formal specification:

- **Rust `nightly` cohort:**
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`library/core/src/mem/maybe_uninit.rs`, `library/core/src/mem/mod.rs`, `library/core/src/mem/transmutability.rs`, `library/core/src/intrinsics/mod.rs`, `library/core/src/ptr/mod.rs`, `compiler/rustc_const_eval/src/interpret/validity.rs`).
  - `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/behavior-considered-undefined.md`, `src/memory-model.md`, `src/type-layout.md`).
- **Stable Rust `1.99.1` and MiniRust cohort:**
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`release 1.99.1`: `library/core/src/*`, `library/alloc/src/*`, `compiler/rustc_abi/src/lib.rs`, `compiler/rustc_mir_transform/src/elaborate_drops.rs`).
  - `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` (submodule pinned by Rust `1.99.1`).
  - `minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`, 28 specification files indexed in `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/minirust-sources.json`).

### Multi-Version and Target Applicability Summary

- **Invariant Across `1.89.0`, `nightly`, `1.99.1`, and `nightly`:**
  - All normative Reference value-validity rules (`bool`, `char`, integers, floats, raw pointers, references, `Box`, slices, `str`, enums, unions, `!`), abstract-byte initialization rules, padding permissions, typed vs. untyped copy semantics, `MaybeUninit<T>` stable API contracts, stable `mem::transmute` / `mem::transmute_copy` contracts, destructor drop-order rules (`Drop-01`–`Drop-22`), FFI/inline-assembly UB rules (`FFI-01`–`FFI-11`), and C++20 atomic memory-model rules (`Conc-01`–`Conc-15`, `Conc-19`–`Conc-21`) are invariant across the examined toolchains and apply across all target architectures (`aarch64`, `x86_64`, `s390x`).
- **Toolchain-Specific / Nightly-Gated Surfaces:**
  - `intrinsics::transmute_unchecked`, `mem::transmute_prefix`, `mem::transmute_neo` (issue `#155079`), `mem::TransmuteFrom` / `Assume`, and `MaybeUninit` unstable slice/byte-view helpers are nightly-only internal or experimental surfaces inspected at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
  - In Rust `1.99.1` (`Conc-06`), `Atomic*::compare_exchange` permits the failure `Ordering` to be stronger than the success `Ordering` (provided failure ordering is `Relaxed`, `Acquire`, or `SeqCst`, never `Release` or `AcqRel`).

## Findings

### 1. Value Validity vs. Operation-Relative Pointer Validity, Library Invariants, and CTFE

Basis: normative specification + documentation + source (`support/rust-initialization-padding/source-map.json`, `compiler/rustc_const_eval/src/interpret/validity.rs`)

1. **Per-Type Value Validity Invariants (`src/behavior-considered-undefined.md`):**
   - `bool`: must be initialized to `0x00` (`false`) or `0x01` (`true`).
   - `char`: must be initialized to a valid Unicode scalar value (`0x0000..=0xD7FF` or `0xE000..=0x10FFFF`).
   - Integers (`u*`, `i*`, `usize`, `isize`) and floats (`f16`, `f32`, `f64`, `f128`): every byte must be **initialized** (uninitialized bytes are invalid even though all $2^W$ initialized bit patterns are valid integers). In `const` evaluation (`CTFE`), integer bytes must not carry pointer provenance; at runtime, reading provenance-bearing pointer bytes as an integer strips provenance.
   - Raw pointers (`*const T`, `*mut T`): pointer bytes must be initialized. For thin pointers (`T: Sized`), any initialized bit pattern (including null, dangling, or integer-transmuted bits) is a valid raw-pointer *value*, though dereferencing an integer-transmuted pointer is UB even for a ZST. For wide slice pointers, metadata must be a valid initialized `usize`; for wide `dyn Trait` raw pointers, whether metadata must be a valid vtable pointer remains marked as debated in the Reference.
   - References (`&T`, `&mut T`) and `Box<T>`: must be aligned to `align_of_val`, non-null, non-dangling (all pointed-to bytes belong to a single live allocation, with total dynamic size $\le \text{isize::MAX}$ for wide references/boxes), satisfy reference aliasing rules, and point to a valid initialized value of `T` (the Reference notes that edge cases of pointee-validity-at-reference-creation remain debated, while `core::ptr` requires an initialized valid `T` as the only sound practice).
   - Enums, Structs, Tuples, Arrays, and `!`: `!` (and empty enums) are uninhabited; structs, tuples, and arrays require every field/element to be valid while permitting uninitialized padding bytes; enums require a valid discriminant and valid fields for the active variant.
2. **Const-Evaluation (`CTFE`) Validation Goes Beyond Runtime Validity:**
   - In `compiler/rustc_const_eval/src/interpret/validity.rs` (`CtfeValidationMode`), `rustc` enforces additional const-safety invariants: integer values cannot contain pointer provenance, and pointer values cannot contain partial or reordered pointer fragments. These extra `CTFE` rejections must not be conflated with general runtime value validity.

### 2. Abstract Bytes, Padding, and Typed vs. Untyped Copy Semantics

Basis: normative specification + documentation + source (`support/rust-initialization-padding/obligation-matrix.json`, `support/rust-initialization-padding/source-map.json`)

| Operation / State Transition | Precondition on Source Bytes | Effect on Padding & Provenance | Verification Modeling Rule |
| :--- | :--- | :--- | :--- |
| Produce / hold valid `T` | All value-participating bytes of `T` valid and initialized; padding bytes may be uninitialized | Padding bytes have no required initialization state | Never infer `0 <= i < size_of::<T>() => byte i is initialized` from the existence of `x: T`. |
| Typed move or copy of `T` (`let y = x;`, `fn id<T>(t: T) -> T`, `ptr::read`, `ptr::write`) | Source bytes form a valid `T` | Preserves semantic value of `T`, but **initialized padding bytes may become uninitialized**; nested `&U`/`&mut U` references may be implicitly reborrowed (changing provenance tags) | Do not model typed assignment or `ptr::read`/`ptr::write` as byte-for-byte `memcpy` over `size_of::<T>()` bytes. |
| Typed move or copy of `MaybeUninit<T>` | Any initialized or uninitialized byte pattern of size `size_of::<T>()` | Preserves exact byte contents and provenance for all **non-padding bytes of `T`**; bytes at `T`'s padding offsets may become uninitialized | Round-tripping `T -> MaybeUninit<U> -> T` is sound only when every padding offset of `U` is already uninitialized/padding in `T` (use `MaybeUninit<[u8; size_of::<T>()]>` for a padding-free intermediate). |
| `MaybeUninit::<T>::zeroed()` and `mem::zeroed::<T>()` |For `mem::zeroed`, all-zero bytes must be valid for `T` (always valid for `MaybeUninit::zeroed`) | Backing storage is zeroed via `write_bytes(0, 1)`, but **returning the typed value may lose zeroed padding** (e.g., the padding byte of `(u8, u16)` is not guaranteed to remain `0`) | Do not assume `zeroed()` yields deterministic all-zero padding bytes for hashing, FFI byte comparison, or serialization. |
| Untyped raw byte copy (`ptr::copy`, `ptr::copy_nonoverlapping`, `ptr::swap_nonoverlapping`) | Source/destination ranges valid for raw byte access and aligned for `T`; source bytes need **not** form a valid `T` | **Preserves byte initialization state and provenance exactly** across all `count * size_of::<T>()` bytes, including padding offsets | In `ptr::swap_nonoverlapping`, `core::ptr` explicitly copies through `MaybeUninit<T>` using `copy_nonoverlapping` rather than typed `read`/`write` (fixing issue `#134713` in commit `0fe8f3454dbe9dda52a254991347e96bec579a6f`). |

### 3. `MaybeUninit<T>` Contract, Gradual Initialization, and Two-Dimensional Proof State

Basis: documentation + source (`support/rust-maybe-uninit/obligation-matrix.json`, `support/rust-maybe-uninit/source-map.json`)

1. **Constructors and Pointer Accessors:**
   - `MaybeUninit::new(val)` stores an initialized `T`, `MaybeUninit::uninit()` creates an uninitialized wrapper, and `MaybeUninit::write(&mut self, val) -> &mut T` overwrites the wrapper without reading or dropping prior bytes and returns a valid mutable reference to the newly initialized `T`.
   - `as_ptr(&self) -> *const T` and `as_mut_ptr(&mut self) -> *mut T` return raw pointers without asserting initialization. Because `as_ptr()` derives from `&self`, mutating through `as_ptr()` is UB unless the mutated bytes lie inside `UnsafeCell`; initialization must use `as_mut_ptr()`.
2. **Extraction and Destruction Obligations (`assume_init*`):**
   - `assume_init(self) -> T`: consumes the wrapper and performs a typed raw read of the union's `ManuallyDrop<T>` field. Immediate UB if the stored bytes do not form a valid `T`.
   - `assume_init_read(&self) -> T`: performs `self.as_ptr().read()`, leaving the wrapper intact. For non-`Copy` resource-owning types (such as `Some(Vec<u8>)`), calling `assume_init_read` more than once (or calling both `assume_init_read` and `assume_init_drop`) duplicates ownership and leads to double-free UB, whereas repeating `assume_init_read` on `Option::<Vec<u8>>::None` is sound because `None` owns no heap allocation.
   - `assume_init_ref(&self) -> &T` and `assume_init_mut(&mut self) -> &mut T`: immediately form `&*self.as_ptr()` / `&mut *self.as_mut_ptr()`. **Cannot be used to initialize uninitialized storage**: calling `assume_init_mut()` on an uninitialized `bool` or `[u8; N]` before writing to it is immediate UB at the moment the reference is created.
   - `assume_init_drop(&mut self)`: calls `ptr::drop_in_place(self.as_mut_ptr())`. Requires both language-level value validity and any library invariants relied upon by `T::drop`.
3. **Gradual Struct/Slice Initialization and Container Niche Suppression:**
   - Struct fields must be initialized via `let ptr = uninit.as_mut_ptr(); (&raw mut (*ptr).field).write(val);` before calling `uninit.assume_init()`.
   - In `[MaybeUninit<T>; N]` or `[MaybeUninit<T>]`, dropping the array/slice never drops already-initialized elements; partial-initialization loops (such as `MaybeUninit::write_clone_of_slice`) must maintain an explicit initialized-prefix drop guard to prevent leaks on unwind.
   - Although `MaybeUninit<T>` has the same size, alignment, and ABI as `T`, coercion `&mut T -> &mut MaybeUninit<T>` is unsound to expose to safe code (which could write `MaybeUninit::uninit()` into the borrowed `T`), and `Outer<T>` vs. `Outer<MaybeUninit<T>>` can have different layouts because `MaybeUninit<T>` has no invalid bit patterns to serve as enum niches.

### 4. Transmutation Semantics (`transmute`, `transmute_copy`, `transmute_prefix`, `TransmuteFrom`)

Basis: documentation + source + normative specification (`support/rust-transmute/operation-matrix.json`, `support/rust-transmute/source-map.json`)

| Operation | Static / Runtime Size Rule | Source Lifecycle | Alignment & Padding Contract | Additional Proof Obligations |
| :--- | :--- | :--- | :--- | :--- |
| `core::mem::transmute<Src, Dst>(src)` (re-export of `intrinsics::transmute`) | Compile-time call-site check: `size_of::<Src>() == size_of::<Dst>()` | Consumes and forgets `Src` (no drop of `Src`) | By-value slots are naturally aligned for `Src` and `Dst`; **padding bytes are not guaranteed preserved** | `src` valid as `Src`; transferred representation valid as `Dst` (including discriminant, non-null, pointee alignment/liveness/aliasing, lifetime, and library invariants). Pointer-to-integer transmute with provenance is UB in `const`; integer-to-pointer transmute is unspecified and UB to dereference for non-ZST accesses. |
| `core::mem::transmute_copy<Src, Dst>(&src)` | Public contract requires `size_of::<Dst>() <= size_of::<Src>()`; implementation asserts `size_of::<Src>() >= size_of::<Dst>()` | Borrows `&Src`; original `Src` remains alive (duplicating ownership if `Src` is non-`Copy`!) | Branches on `align_of::<Dst>() > align_of::<Src>()`: calls `ptr::read_unaligned` if stricter, else `ptr::read` | Typed prefix read of `size_of::<Dst>()` bytes: destination bytes must form a valid `Dst`, and caller must manage duplicated resource ownership. |
| `core::intrinsics::transmute_unchecked<Src, Dst>(src)` (unstable) | Removes compile-time size check; unequal sizes at runtime are immediate UB | Consumes and forgets `Src` | Same as `mem::transmute` | Caller must prove `size_of::<Src>() == size_of::<Dst>()` in addition to all `transmute` obligations. |
| `core::mem::transmute_prefix<Src, Dst>(src)` (unstable `#155079`) | Permits `size_of::<Src>() != size_of::<Dst>()` | Consumes and forgets `Src` | `#[repr(C)]` union-style prefix reinterpretation: if `Dst` is larger, trailing bytes `[size_of::<Src>()..size_of::<Dst>()]` are **uninitialized** | Resulting prefix + uninitialized suffix must form a valid `Dst` (valid only when the suffix falls entirely in `Dst` padding or `MaybeUninit` storage). |
| `core::mem::TransmuteFrom<Src, ASSUME>` (unstable `transmutability`) | Compiler proves union-transmutability modulo `Assume { alignment, lifetimes, safety, validity }` | Consumes `Src` | May permit trailing uninitialized destination padding bytes | Any `Assume` flag set to `true` transfers that proof obligation from the compiler to the caller; trait impls carry **no** cross-toolchain, cross-target, or SemVer stability guarantee. |

### 5. Rust 1.99.1 Normative 87-Clause Ledger (`Seq-01`–`Seq-31`, `FFI-01`–`FFI-11`, `Drop-01`–`Drop-26`, `Conc-01`–`Conc-21`, `Model-01`–`Model-08`)

Basis: normative specification + documentation + source (`support/rust-1-99-1-opsem-normative-clauses-and-static-premises/sources.json`, `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/minirust-sources.json`)

Every clause in `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/sources.json` is classified into one of five explicit authority tiers: `normative_reference` (Rust Reference `82da570bafd9efed421bdbae0f8603ede8dd308b`), `standard_library_contract` (`core`/`alloc` `# Safety` contracts at `58cf8f9c35b355199727627d07ae34a4e2846d67`), `compiler_implementation` (`rustc_abi`, `rustc_mir_transform`), `exploratory_background` (MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, Tree Borrows, Stacked Borrows, UCG), and `non_normative_note` (explicit incompleteness disclaimers).

#### Sequential Core, Layout, and Representation Clauses (`Seq-01`–`Seq-31`)

| Clause Label | Authority Tier | Pinned Source Coordinate | Normative Rule and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `Seq-01` | `normative_reference` | `src/unsafe-keyword.md:27-57`, `src/behavior-considered-undefined.md:5-22` | Soundness requires that safe callers cannot trigger UB under any input; every `unsafe` block must discharge all inner operation preconditions. |
| `Seq-02` | `non_normative_note` | `src/behavior-considered-undefined.md:14-18`, `src/memory-model.md:1-16` | The Reference's UB list is non-exhaustive and the Rust memory model is explicitly incomplete. |
| `Seq-03` | `normative_reference` | `src/memory-model.md:4-26` | Abstract bytes are either uninitialized or initialized to `0..=255` with optional pointer provenance (non-exhaustive state space). |
| `Seq-04` | `normative_reference` | `src/memory-model.md:28-55` | Allocations have base addresses, lengths, and provenance; pointers combine an address with optional provenance constraining memory access. |
| `Seq-05` | `normative_reference`, `standard_library_contract` | `src/behavior-considered-undefined.md:62-97`, `library/core/src/ptr/mod.rs:342-391` | Pointer accesses require alignment, non-nullness (where applicable), in-bounds range, live allocation, and valid provenance. |
| `Seq-06` | `standard_library_contract` | `library/core/src/ptr/mod.rs:108-165` | Dereferenceability for size `N` is defined over byte addresses that need not be a single contiguous `[ptr, ptr + N)` range under `UnsafeCell`/projection carveouts, though contiguous primitives require `[ptr, ptr + size_of::<T>())`. |
| `Seq-07` | `normative_reference` | `src/behavior-considered-undefined.md:99-119`, `src/types/pointer.md:84-125` | Breaking `&mut T` uniqueness or mutating through `&T` outside `UnsafeCell<U>` is UB. |
| `Seq-08` | `non_normative_note` | `src/behavior-considered-undefined.md:113-119` | The exact operational aliasing model for raw pointers derived from references remains undecided. |
| `Seq-09` | `normative_reference` | `src/type-layout.md:1-16` | `size % align == 0`, `align` is a power of two $\ge 1$, and both are target-conditional properties. |
| `Seq-10` | `normative_reference` | `src/type-layout.md:18-64` | Primitive layouts: `bool`/`u8`/`i8` size 1, align 1; `u16`/`u32`/`u64`/`u128` sizes 2, 4, 8, 16; thin pointers match `usize`/`isize` size and alignment on the target. |
| `Seq-11` | `normative_reference` | `src/type-layout.md:66-123` | Wide pointers to `[T]`, `str`, and `dyn Trait` have size $2 \times \text{size\_of}::<\text{usize}>()$, without a guaranteed `(data, metadata)` field ordering across compilations. |
| `Seq-12` | `normative_reference` | `src/type-layout.md:125-169` | `[T; N]` has size $\text{size\_of}::<T>() \times N$ and alignment $\text{align\_of}::<T>()$; `[T]` matches the sliced array section. |
| `Seq-13` | `normative_reference` | `src/type-layout.md:171-201` | Default `repr(Rust)` struct/tuple layout does not guarantee field order or inter-field padding offsets (except `()` has size 0, align 1). |
| `Seq-14` | `normative_reference` | `src/type-layout.md:203-267` | `#[repr(C)]` struct layout places fields in declaration order with alignment rounding and tail rounding; empty `repr(C)` structs in Rust have size 0. |
| `Seq-15` | `normative_reference` | `src/type-layout.md:269-313` | `#[repr(packed(N))]` caps alignment to $\min(\text{align}, N)$ and `#[repr(align(N))]` raises alignment to $\max(\text{align}, N)$; they cannot be combined on the same type, and unaligned references to packed fields are UB. |
| `Seq-16` | `normative_reference` | `src/type-layout.md:315-481` | `#[repr(Int)]`, `#[repr(C)]`, and `#[repr(C, Int)]` enum layouts define explicit tag and union payload representations while preserving Rust discriminant validity. |
| `Seq-17` | `normative_reference` | `src/type-layout.md:483-532` | `#[repr(transparent)]` delegates layout and ABI to its single non-(size-0, align-1) field. |
| `Seq-18` | `normative_reference`, `standard_library_contract` | `src/type-layout.md:102-123`, `library/core/src/option.rs:172-238` | Guaranteed niche optimization: `Option<&T>`, `Option<&mut T>`, `Option<fn(...)>`, `Option<NonNull<T>>`, `Option<Box<T, Global>>`, and `Option<NonZero*>` match their inner type's size, alignment, and ABI with `None` as all-zero bits. |
| `Seq-19` | `normative_reference` | `src/behavior-considered-undefined.md:121-225` | Value validity invariants across `bool`, `char`, integers, floats, `str`, `!`, enums, references, and `Box<T>`. |
| `Seq-20` | `normative_reference` | `src/behavior-considered-undefined.md:165-191` | Reading uninitialized bytes as an integer is immediate UB; reading provenance-bearing pointer bytes as an integer is UB in `const` and strips provenance at runtime. |
| `Seq-21` | `normative_reference`, `standard_library_contract` | `src/types/union.md:54-119`, `library/core/src/mem/maybe_uninit.rs:108-196` | Unions do not require inactive fields to be valid; `MaybeUninit<T>` relaxes `T` validity/initialization while preserving `T`'s size, alignment, and ABI. |
| `Seq-22` | `standard_library_contract` | `library/core/src/mem/maybe_uninit.rs:267-312` | Typed copies of `T` or `MaybeUninit<T>` preserve non-padding bytes of `T`, may deinitialize padding bytes, and may reborrow nested references. |
| `Seq-23` | `normative_reference` | `src/expressions/operator-expr.md:274-366` | `&place` / `&mut place` immediately require reference validity (`Seq-19`), whereas `&raw const place` / `&raw mut place` evaluate the place without reading or requiring pointee initialization/alignment. |
| `Seq-24` | `standard_library_contract` | `library/core/src/ptr/mod.rs:956-1099` | `ptr.offset` / `add` / `sub` require in-bounds single-allocation traversal fitting in `isize`; `wrapping_offset` / `wrapping_add` / `wrapping_sub` perform safe wrapping address arithmetic retaining provenance. |
| `Seq-25` | `standard_library_contract` | `library/core/src/ptr/mod.rs:576-662` | `ptr::copy` (`memmove`) and `ptr::copy_nonoverlapping` (`memcpy`) perform untyped byte copies preserving initialization state and provenance. |
| `Seq-26` | `standard_library_contract` | `library/core/src/ptr/mod.rs:1322-1589` | `ptr::read` / `write` require alignment; `read_unaligned` / `write_unaligned` drop alignment while requiring valid initialized `T` on reads and overwriting without dropping on writes. |
| `Seq-27` | `standard_library_contract` | `library/core/src/ptr/mod.rs:1661-1778` | `read_volatile` and `write_volatile` are externally observable non-elided accesses requiring alignment and valid initialized `T` on reads, without atomic synchronization guarantees. |
| `Seq-28` | `standard_library_contract` | `library/core/src/slice/raw.rs:64-174` | `slice::from_raw_parts` / `_mut` require non-null, aligned pointers (even when `len == 0`), single live allocation of size $\le \text{isize::MAX}$, initialized elements, and aliasing compliance. |
| `Seq-29` | `standard_library_contract` | `library/core/src/mem/mod.rs:658-734` | `mem::transmute` and `transmute_copy` reinterpret bytes into a valid `Dst` without dropping `Src` (and without preserving padding in by-value `transmute`). |
| `Seq-30` | `standard_library_contract` | `library/core/src/ptr/mod.rs:2125-2485` | Strict Provenance (`addr`, `with_addr`, `map_addr`, `without_provenance`) vs. Exposed Provenance (`expose_provenance`, `with_exposed_provenance`). |
| `Seq-31` | `compiler_implementation` | `compiler/rustc_abi/src/lib.rs:1395-1565` | `rustc_abi::LayoutData` internal representation (`FieldsShape`, `Variants`, `BackendRepr`, `Align`, `Size`). |

#### Foreign Calls, Inline Assembly, Destructors, Atomics, and Exploratory Models (`FFI-01`–`FFI-11`, `Drop-01`–`Drop-26`, `Conc-01`–`Conc-21`, `Model-01`–`Model-08`)

- **Foreign Calls and Inline Assembly (`FFI-01`–`FFI-11`):**
  - `FFI-01`–`FFI-04` (`normative_reference`, `src/items/external-blocks.md:1-142`, `src/items/functions.md:360-478`, `src/behavior-considered-undefined.md:32-48`): Calling a function pointer with a mismatched ABI string (`"C"` vs. `"Rust"` vs. `"C-unwind"`) or ABI-incompatible argument/return types is immediate UB; unwinding across a non-unwind ABI boundary (`extern "C"`) is UB or aborts; `#[repr(transparent)]` and niche-optimized `Option` (`Seq-18`) are FFI-compatible only when their inner type is FFI-compatible.
  - `FFI-05`–`FFI-08` (`normative_reference`, `src/inline-assembly.md:1-852`): `asm!` / `global_asm!` operand directions (`in`, `out`, `inout`, `inlateout`, `sym`, `const`), options (`pure`, `nomem`, `readonly`, `preserves_flags`, `noreturn`, `nostack`, `may_unwind`, `raw`), undeclared register/ABI clobbers (`clobber_abi`), and Rust aliasing compliance for memory accessed via register pointers.
  - `FFI-09`–`FFI-11` (`standard_library_contract` / `non_normative_note`, `library/alloc/src/boxed.rs:190-275`, `library/core/src/ffi/mod.rs:1-125`, `src/items/external-blocks.md:95-142`): `Box<T, Global>` for sized `T` is ABI-compatible with non-null `T*` (and `Option<Box<T, Global>>` with nullable `T*`); `core::ffi::c_*` primitives match target C ABI widths; `repr(Rust)` types and wide pointers have no stable C ABI (`improper_ctypes_definitions`).
- **Destructors, Drop Flags, `ManuallyDrop`, and Unwinding (`Drop-01`–`Drop-26`):**
  - `Drop-01`–`Drop-06` (`normative_reference`, `src/destructors.md:1-295`): `drop_in_place<T>` runs `T::drop(&mut self)` then recursively drops fields; scope-exit drops locals in **reverse** declaration order, whereas struct/tuple/array fields/elements drop in **forward** order (`0, 1, ...`); temporaries drop at statement end unless lifetime-extended; partial moves update dynamic drop flags so only initialized places are dropped; reassigning an initialized place drops the old value before writing the new value; `let _ = expr;` drops `expr` at statement end rather than block exit.
  - `Drop-07`–`Drop-12` (`standard_library_contract` / `normative_reference`, `library/core/src/ops/drop.rs:1-118`, `library/core/src/ptr/mod.rs:515-574`, `library/core/src/mem/mod.rs:135-210`, `library/core/src/mem/manually_drop.rs:1-235`, `src/types/union.md:54-119`): Direct `Drop::drop` calls are rejected (`E0040`); `ptr::drop_in_place` requires non-null, aligned, read/write-valid storage and leaves the pointee logically uninitialized; `mem::forget` wraps in `ManuallyDrop::new` and is safe (unsafe code must never rely on `Drop` running for soundness except under the `Pin<P>` drop guarantee); `ManuallyDrop<T>` suppresses automatic drop glue while **retaining `T`'s validity and niche invariants** (unlike `MaybeUninit<T>`); union fields with drop glue must use `ManuallyDrop<T>`.
  - `Drop-13`–`Drop-22` (`normative_reference` / `standard_library_contract`, `src/panic.md:1-98`, `library/alloc/src/boxed.rs:1120-1215`, `library/core/src/pin.rs:1-245`, `src/expressions/operator-expr.md:540-610`, `library/core/src/mem/mod.rs:736-850`, `library/alloc/src/vec/mod.rs:1750-1845`): `panic = "unwind"` vs. `"abort"`; double panic during unwind aborts; `Box<T>` drop runs `drop_in_place` then frees the heap allocation even on unwind; `Pin<P>` drop guarantee forbids reusing/deallocating pinned `!Unpin` storage before `drop_in_place` runs; call arguments and struct/array literals evaluate left-to-right and unwind in reverse order; `mem::replace` and `mem::swap` exchange bytes without running destructors; `Vec::set_len` requires `0..new_len` initialized; `drop_in_place::<[T]>` drops `0..len` sequentially and continues dropping remaining elements if element $i$ panics.
  - `Drop-23`–`Drop-26` (`exploratory_background` / `compiler_implementation` / `non_normative_note`): MiniRust `StartUnwind` / `StopUnwind` / `ResumeUnwind` (`spec/lang/step/terminators.md:278-340`), `ResumeUnwind` dynamic stack requirement (`spec/lang/well-formed.md:360-420`), `rustc` `elaborate_drops.rs` lowering to stack boolean flags, and non-normative status of synthetic MIR drop-flag locals.
- **Atomics, Memory Orderings, and Concurrency (`Conc-01`–`Conc-21`):**
  - `Conc-01`–`Conc-15`, `Conc-19`–`Conc-21` (`normative_reference` / `standard_library_contract` / `non_normative_note`, `src/behavior-considered-undefined.md:24-30`, `library/core/src/sync/atomic.rs:1-3540`, `library/core/src/marker.rs:640-725`, `library/core/src/cell.rs:2120-2240`, `library/core/src/hint.rs:210-265`): Rust adopts the C++20 atomic model (N4868 `[intro.races]`, `[atomics]`); data races are UB; atomicity is a property of the access operation (`Atomic*::from_ptr`); `Atomic*` types have the size, alignment (at least size), and bit validity of their scalar over `UnsafeCell<T>`; `Ordering::{Relaxed, Release, Acquire, AcqRel, SeqCst}`, Runtime panics on invalid load/store/failure orderings (`Conc-06`); RMW release sequences (`Conc-07`); `fence` vs. `compiler_fence` (`Conc-08`); single-location coherence `mo` (`Conc-09`) and `SeqCst` total order `S` (`Conc-10`); `AtomicPtr<T>` preserves full pointer provenance (`Conc-11`); `fetch_update` is a software CAS loop (`Conc-12`); `Send` and `Sync` (`T: Sync <=> &T: Send`, `Conc-13`); `UnsafeCell<T>` is `!Sync` (`Conc-14`); mixed-size atomic accesses are UB (`Conc-15`); zero-byte accesses do not byte-overlap (`Conc-19`); `hint::spin_loop` has no ordering effect (`Conc-20`); `Relaxed` out-of-thin-air (`OOTA`) caveat (`Conc-21`).
  - `Conc-16`–`Conc-18` (`exploratory_background`, `minirust@d821c6e:spec/mem/concurrent.md:1-165`, `spec/mem/tree_borrows/memory.md:1-190`): MiniRust `ConcurrentMemory` tracks only `prev_atomic_accesses` from the *immediately preceding step* with binary `Atomicity::{Atomic, None}`, missing C++20 `Ordering` synchronization, missing non-atomic races separated by one unrelated thread step, and missing implicit reads inside `TreeBorrowsMemory::retag`.
- **Exploratory Operational Models (`Model-01`–`Model-08`):**
  - `Model-01`–`Model-08` (`exploratory_background`, `minirust@d821c6e`): `Memory` trait interface (`spec/mem/interface.md`), `BasicMemory` (`spec/mem/basic.md`), Tree Borrows per-byte state machine (`Reserved { ty_is_freeze, conflicted }`, `Active`, `Frozen`, `Disabled` in `spec/mem/tree_borrows/state_machine.md`), call-frame protectors (`state_machine_protected.md`), `end_call` implicit reads (`tree_borrows/memory.md`), `Relation` `encode`/`decode` (`spec/lang/representation.md`), `IntPtrCast` angelic `predict` (`spec/mem/intptrcast.md`), and `check_wf` (`spec/lang/well-formed.md`).

### 6. Five-Layer Static-vs-Dynamic Premise Stratification and the `minirust#288` Codec Coherence Gap

Basis: source + derived (`minirust@d821c6e:spec/lang/well-formed.md`, `spec/lang/representation.md:623-763`, `spec/lang/step/terminators.md:201-340`, `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/minirust-sources.json`)

Formal verification of Rust programs requires separating five independent obligation layers that are often conflated:

1. **Layer 1 — Structural Syntax and CFG Well-Formedness (`StaticSyntaxWF`):** Valid local/block indices, argument counts, entry-block presence, and operand sort matching (`spec/lang/well-formed.md:450-980`). Prevents semantics "stuck" states, but proves neither value validity nor memory safety.
2. **Layer 2 — Target-Parameterized Type Geometry (`StaticGeometryWF`):** `align` is a power of two $\ge 1$, `size % align == 0`, and field offsets + sizes fit within the aggregate `size` (`spec/lang/well-formed.md:1-285`).
3. **Layer 3 — Representation Codec Coherence (`StaticCodecCoherence` — `minirust#288` Gap):**
   - MiniRust's stated representation theorems—round-trip (`decode(encode(v)) == Some(v)`) and provenance deflation (`encode(v) <= bytes` when `decode(bytes) == Some(v)`, `spec/lang/representation.md:623-763`)—do **not** follow from executable `Type::check_wf` (`spec/lang/well-formed.md:155-284`) alone:
     - **Counterexample A (Incoherent `Type::Enum` Tagger vs. Discriminator, `minirust#288`):** `Type::Enum` has an encoding map `tagger: Map<Discriminant, List<(Offset, IntType, Int)>>` and a decoding tree `discriminator: Discriminator`. `Type::check_wf` checks that `tagger` writes in-bounds integers and `discriminator` branches in-bounds to valid variants, but never checks that `discriminator` decodes the bytes written by `tagger` back to the same discriminant. A 1-byte, 2-variant enum where `tagger` writes `0` for variant `0` and `1` for variant `1`, while `discriminator = Discriminator::Known(0)`, passes `Type::check_wf` yet yields `decode(encode(Variant(1))) == Some(Variant(0))`.
     - **Counterexample B (Truncated Wide-Pointer `Type::Union` Chunks, `minirust#288`):** `Type::Union` (`spec/lang/well-formed.md:155-213`) checks only that `chunks` are sorted, disjoint, and within `size`, without requiring `chunks` to cover union fields or preserve wide-pointer metadata. A union holding a 16-byte wide pointer (`*const [u8]`) with `chunks = [(0, 8)]` passes `Type::check_wf` while truncating the upper 8 metadata bytes during `encode`/`decode`.
4. **Layer 4 — Evaluated Constant and Instance-Selection Certificates (`ConstAndInstanceBinding`):** Binding monomorphized function bodies and associated constants (`size_of::<T>()`, `align_of::<T>()`) to the exact `(DefPath, GenericArgs, Target)` tuple and `CTFE` postconditions.
5. **Layer 5 — Irreducible Dynamic Operational Preconditions (`DynamicSafetyPremises`):** Even when Layers 1–4 hold, runtime execution must discharge: (a) value validity on typed loads/transmutes (`0x02` loaded as `bool` steps to `UB`), (b) dynamic call ABI compatibility in `Terminator::Call` (`check_abi_compatibility(caller_fn_abi, callee_fn_abi)` at `spec/lang/step/terminators.md:201-276`), (c) active unwinding stack state in `Terminator::ResumeUnwind` (`spec/lang/step/terminators.md:315-340`), and (d) live allocation, bounds, alignment, provenance, and aliasing at every memory access.

## Boundaries

- **Unresolved normative Rust semantics:** The Rust Reference (`ad35aca481751a06afeb23820a672b0f3b11a476` and `82da570bafd9efed421bdbae0f8603ede8dd308b`) explicitly marks the complete memory model, exact pointer-aliasing rules (`Stacked Borrows` vs. `Tree Borrows`), exact Exposed Provenance reconstruction rules (`with_exposed_provenance`), raw `dyn Trait` vtable metadata bit-validity, and edge cases of union/reference pointee validity as open or non-exhaustive.
- **No byte-preservation guarantee across typed moves or `transmute`:** Neither `mem::transmute`, `ptr::read`, `ptr::write`, `mem::zeroed`, nor a typed copy of `T` or `MaybeUninit<T>` guarantees preservation of padding bytes. Only untyped byte copies (`ptr::copy`, `ptr::copy_nonoverlapping`, `ptr::swap_nonoverlapping`) preserve padding initialization state.
- **Static `check_wf` does not imply codec round-trip or call safety:** MiniRust `Type::check_wf` requires an additional `StaticCodecCoherence` premise (`minirust#288`) for `decode(encode(v)) == Some(v)` and dynamic ABI/unwind/memory preconditions for step safety.
- **No fresh Miri or compiler execution in this package:** All findings in this package derive from pinned normative specifications, standard-library contracts/source, compiler source, and MiniRust specification files verified against preserved SHA-256 digests.

## Evidence

- **Rust `1.99.1`, Rust Reference `82da570b`, and MiniRust `d821c6e` primary-source ledgers (revalidated `2026-10-24`):**
  - `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/sources.json`: 30 primary-source records across `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` with exact file paths, byte lengths, git blob hashes, SHA-256 digests, and line ranges for all 87 clauses (`Seq-01`–`Seq-31`, `FFI-01`–`FFI-11`, `Drop-01`–`Drop-26`, `Conc-01`–`Conc-21`, `Model-01`–`Model-08`).
  - `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/minirust-sources.json`: 28 Markdown specification files from `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`).
  - `support/rust-1-99-1-opsem-normative-clauses-and-static-premises/revalidation-check.json`: verification receipt for all 30 Rust/Reference records and 28 MiniRust specification files.
- **Rust `nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and Reference (`ad35aca481751a06afeb23820a672b0f3b11a476`) source maps and obligation matrices (observed `2026-09-27`):**
  - Initialization and padding: `support/rust-initialization-padding/obligation-matrix.json` and `support/rust-initialization-padding/source-map.json` (plus upstream `rust-lang/rust` issue `#134713` and commit `0fe8f3454dbe9dda52a254991347e96bec579a6f` for `ptr::swap_nonoverlapping`).
  - `MaybeUninit<T>`: `support/rust-maybe-uninit/obligation-matrix.json` and `support/rust-maybe-uninit/source-map.json` (`library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`).
  - Transmutation: `support/rust-transmute/operation-matrix.json` and `support/rust-transmute/source-map.json` (`library/core/src/intrinsics/mod.rs` blob `78d7314c58110b49839894a0f69377f4ee0d1204`, `library/core/src/mem/mod.rs` blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`, `library/core/src/mem/transmutability.rs` blob `e26c1b8fa1e19b5c209aba1a0c45e179ffaf238f`).
  - Validity and CTFE: `compiler/rustc_const_eval/src/interpret/validity.rs` (blob `249a65e22824521af9e4bd433235c667a6fd94a4`), `src/behavior-considered-undefined.md` (blob `373052061c50fc2f6d1c07a91960d40bac505284`), and `src/memory-model.md` (blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784`).

## Revalidation

1. **Offline Manifest Integrity Check:**
   Verify the preserved source maps, obligation matrices, and revalidation ledger inside this package:
   ```bash
   python3 - <<'PY'
   import json, pathlib
   pkg = pathlib.Path("reports/rust-validity-initialization-padding-and-transmute-semantics")
   sources = json.loads((pkg / "support/rust-1-99-1-opsem-normative-clauses-and-static-premises/sources.json").read_text())
   mr_sources = json.loads((pkg / "support/rust-1-99-1-opsem-normative-clauses-and-static-premises/minirust-sources.json").read_text())
   reval = json.loads((pkg / "support/rust-1-99-1-opsem-normative-clauses-and-static-premises/revalidation-check.json").read_text())
   assert len(sources["sources"]) == 30
   assert len(mr_sources["files"]) == 28
   assert reval["status"] == "ok" or len(reval) > 0
   for sub in [
       "support/rust-initialization-padding/obligation-matrix.json",
       "support/rust-maybe-uninit/obligation-matrix.json",
       "support/rust-transmute/operation-matrix.json",
   ]:
       assert json.loads((pkg / sub).read_text())
   print("All preserved source manifests and obligation matrices verified.")
   PY
   ```
2. **Source-Level Diff on a Newer Rust or MiniRust Revision:**
   - Diff `src/behavior-considered-undefined.md` and `src/memory-model.md` in `rust-lang/reference` for changes to invalid-value production, padding/union exceptions, reference pointee validity, or const provenance rules.
   - Diff `library/core/src/mem/maybe_uninit.rs`, `library/core/src/mem/mod.rs`, `library/core/src/mem/transmutability.rs`, `library/core/src/intrinsics/mod.rs`, and `library/core/src/ptr/mod.rs` for any changes to typed-copy padding rules, `assume_init*` contracts, `swap_nonoverlapping`, `transmute_copy` alignment branching, or `TransmuteFrom`.
   - Diff `spec/lang/well-formed.md` and `spec/lang/representation.md` in `minirust` to check whether `Type::check_wf` has been strengthened to close the `minirust#288` `Enum` tagger/discriminator and `Union` wide-pointer chunk coherence gaps.
