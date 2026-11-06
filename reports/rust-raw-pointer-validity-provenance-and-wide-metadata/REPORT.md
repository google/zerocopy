# Rust Raw Pointer Validity, Provenance, Arithmetic, NonNull, and Wide Metadata

## Summary

Raw pointers (`*const T` and `*mut T`) and `core::ptr::NonNull<T>` separate **pointer-value validity** from **memory-access validity**, while carrying hidden **provenance** (allocation authority) and optional **wide-pointer metadata** (`<T as Pointee>::Metadata`). Across the Rust Reference, `core::ptr` safety contracts, and the compiler's MIR/CTFE/Codegen implementations:

1. **Authority and Provenance Stratification:** A pointer is not reducible to its numerical machine address. In the abstract machine, a pointer pairs a runtime address with provenance recording which live allocation instance it is authorized to access and over what spatial extent and permissions. Lowering a pointer to an integer or byte index in a verification model erases this link unless the model retains, reconstructs, or explicitly assumes an allocation-authority witness connecting the logical `(allocation, offset)` pair to a live source allocation and valid access permission (`support/rust-authority-provenance/coverage.json`).
2. **Value Validity vs. Operation-Relative Access Validity:** At runtime, a thin raw pointer has no non-null, alignment, or live-allocation value invariant (`0x1 as *const u32` is a valid pointer value), whereas `NonNull<T>` carries a permanent non-null value invariant (`NonNull::new_unchecked(ptr::null_mut())` is immediate UB even if never dereferenced) and enables niche optimization (`size_of::<Option<NonNull<T>>>() == size_of::<NonNull<T>>()`). Conversely, dereferencing or accessing memory through a pointer requires operation-relative alignment (`align_of_val_raw`), non-nullness (unless `size_of_val_raw == 0` under operations that allow zero-sized accesses), and provenance-backed in-bounds allocation liveness (`support/rust-raw-pointer-validity-provenance-alignment/obligation-matrix.json`, `support/rust-nonnull/obligation-matrix.json`).
3. **Strict vs. Exposed Provenance APIs:** `ptr.addr()` strips provenance without exposing it; `ptr.with_addr(addr)` and `ptr.map_addr(f)` compute a new address while preserving `ptr`'s provenance via wrapping byte offset; `ptr::without_provenance` and `ptr::without_provenance_mut` (which powers `NonNull::dangling()`) produce address-only pointers usable only for aligned zero-sized accesses. By contrast, `ptr.expose_provenance()` (and `ptr as usize`) marks provenance as exposed, and `ptr::with_exposed_provenance(addr)` (and `addr as *const T`) nondeterministically selects a previously exposed provenance (or accesses non-Rust-allocated hardware/MMIO memory), triggering UB if no exposed provenance justifies a subsequent Rust-allocation access (`support/rust-pointer-casts-provenance-apis/api-matrix.json`).
4. **In-Bounds vs. Wrapping Pointer Arithmetic:** Unsafe arithmetic (`offset`, `add`, `sub`, `byte_offset`, `byte_add`, `byte_sub`, and `offset_from` / `byte_offset_from`) requires the scaled byte delta to fit in `isize` and, whenever nonzero, requires both source and destination to lie within (or one byte past the end of) the **same live allocated object**; crossing an allocation boundary in `add`/`offset` is immediate UB even if the result is never dereferenced. Safe wrapping arithmetic (`wrapping_offset`, `wrapping_add`, `wrapping_sub`, `wrapping_byte_*`, lowered to `intrinsics::arith_offset`) defers bounds checks to dereference time, permits temporarily leaving and re-entering an allocation, and preserves the original pointer's provenance (`support/rust-pointer-arithmetic/api-matrix.json`).
5. **Raw Slice Construction and Wide-Pointer Metadata:** `ptr::slice_from_raw_parts` and `ptr::slice_from_raw_parts_mut` are safe, `const`-stable metadata constructors (`from_raw_parts(data, len)`) that do not dereference or validate `data` or `len`, whereas `slice::from_raw_parts` and `slice::from_raw_parts_mut` immediately reborrow `&*ptr::slice_from_raw_parts(data, len)` and enforce full reference validity (including non-null aligned `data` even when `len == 0` or `T` is a ZST). Under `Pointee::Metadata`, wide pointers pair a data pointer with `usize` (for `[T]` and `str`) or `DynMetadata<Dyn>` (for trait objects); `with_metadata_of` replaces metadata while strictly preserving the first operand's data address and provenance (`support/rust-raw-slice-pointer-construction/contract-matrix.json`, `support/rust-wide-pointer-metadata/metadata-matrix.json`).

---

## Applicability

### Multi-Version and Multi-Architecture Coverage

The semantics consolidated in this report are anchored to `rust-lang/rust` commit `e75bad700fc6eb2cfe2bfec5fd6cb0fd1ab3cde5` (`nightly`, `1.98.0-nightly`) and `rust-lang/reference` commit `f100ffd2dc3fbef43fbca8facf7fb5dc9be2bc8b`, and cross-checked across `rustc` **1.89**, **1.99.1**, **nightly**, and **nightly** as well as target architectures **`aarch64`**, **`x86_64`**, and **`s390x`**:

| Semantic Surface | `rustc 1.89` | `rustc 1.99.1` | `nightly` | `nightly` | Target Architecture Dependence (`aarch64`, `x86_64`, `s390x`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Pointer width, `usize`/`isize` bounds, and `NonNull<T>` niche (`Option<NonNull<T>>`)** | Stable (`#[repr(transparent)]`, `rustc_layout_scalar_valid_range_start(1)`). | Invariant with 1.89. | Invariant with 1.89. | Invariant with 1.89. | **Target-width dependent (`64-bit` across `aarch64`, `x86_64`, `s390x`):** Thin pointers are 8 bytes with alignment 8 on all three 64-bit targets (`isize::MAX == 0x7fff_ffff_ffff_ffff`), and wide pointers (`*const [T]`, `*const str`, `*const dyn Trait`) are 16 bytes with alignment 8. Endianness (`s390x` big-endian vs. `aarch64`/`x86_64` little-endian) affects the byte representation of stored addresses and metadata, not high-level API semantics. |
| **Strict & Exposed Provenance APIs (`addr`, `with_addr`, `map_addr`, `without_provenance(_mut)`, `expose_provenance`, `with_exposed_provenance(_mut)`)** | Stable since Rust 1.84.0 (`strict_provenance` / `exposed_provenance`). | Invariant with 1.89. | Invariant with 1.89. | Invariant with 1.89. | **Architecture-invariant** at the Rust AM level. |
| **Pointer arithmetic (`offset`, `add`, `sub`, `byte_offset`, `byte_add`, `byte_sub`, `wrapping_*`, `offset_from`, `offset_from_unsigned`)** | Stable (`byte_*` stable since 1.75.0; `offset_from_unsigned` stable since 1.87.0). | Invariant with 1.89. | Invariant with 1.89. | Invariant with 1.89. | **Target-width dependent only via `isize::MAX` and `size_of::<T>()` / `align_of::<T>()`** (identical 64-bit bounds across `aarch64`, `x86_64`, `s390x`). |
| **`ptr::slice_from_raw_parts(_mut)` vs. `slice::from_raw_parts(_mut)`** | Stable and `const`-stable across all four versions. | Invariant with 1.89. | Invariant with 1.89. | Invariant with 1.89. | **Architecture-invariant** (subject to target `isize::MAX` byte-length cap on `slice::from_raw_parts`). |
| **Unstable wide-pointer metadata (`ptr_metadata`: `Pointee`, `DynMetadata`, `from_raw_parts`, `to_raw_parts`, `metadata`), `cast_slice` (`ptr_cast_slice`), and `NonNull::as_uninit_*` (`ptr_as_uninit`)** | Unstable on stable 1.89 (internal `ptr::from_raw_parts` used by `slice_from_raw_parts`). | Unstable on stable 1.99.1 (same internal lowering). | Available on `nightly` under `#![feature(ptr_metadata)]`, `#![feature(ptr_cast_slice)]`, `#![feature(ptr_as_uninit)]`. | Available on `nightly` under the same feature gates. | **Architecture-invariant** in API contract; vtable layout and address placement depend on compiler ABI and codegen partitioning. |

---

## Findings

### 1. Allocation Authority and Provenance Stratification

A sound verification model for low-level Rust cannot treat raw pointers as bare integers without tracking **authority** (provenance):

1. **Four Authority Strata (`support/rust-authority-provenance/coverage.json`):**
   - **Normative Language Level (Rust Reference):** `src/behavior-considered-undefined.md` defines a pointer as **dangling** if not all of the bytes it points to are part of the same live allocation, and explicitly warns that pointers carry provenance so producing a pointer with the right numerical address in the wrong way can still cause UB on dereference.
   - **Standard Library Contract Level (`core::ptr`):** `library/core/src/ptr/mod.rs` (blob `ff2c18d685b65832c296731f23f1664779b874f2`) defines pointer validity for reads/writes relative to access size `size_of_val_raw(ptr)`, allocation provenance, spatial bounds, and liveness, and provides explicit APIs to strip, transfer, or expose provenance.
   - **Compiler / Execution Level (`rustc` MIR & CTFE):** `rustc` lowers `with_addr` to `ptr.wrapping_byte_offset((addr as isize).wrapping_sub(ptr.addr() as isize))` (`intrinsics::arith_offset`) so the pointer's origin allocation remains attached in the compiler's IR, while CTFE (`compiler/rustc_const_eval/src/interpret/validity.rs`, blob `bd2942702dd5ebbc5e898c0142423437f78979d0`) tracks exact allocation IDs (`AllocId`) and rejects integer-to-pointer casts with provenance or partial pointer fragments at compile time.
   - **Explanatory / Design Level (Unsafe Code Guidelines & WG14 N2364):** UCG `src/glossary.md` (blob `d809f91e62968913d808e53397fbcf7cea762cce`) and ISO C WG14 N2364 (`2019-04-01`, PVI/PNVI-ae/PNVI-ae-udi) explain the design rationale for Strict and Exposed Provenance, while remaining subordinate to the Reference and `core::ptr` contracts.
2. **Verification Rule for Pointer-to-Index Lowering:** If a verification pipeline lowers a pointer `p` into a pure mathematical pair `(alloc_id, offset)` or a bare integer offset `idx`, any step that discharges a memory-access safety obligation (`read`, `write`, `copy`, or reference creation) must carry an explicit **authority witness** proving that `p`'s provenance is authorized to access `[offset, offset + size)` in `alloc_id`, that `alloc_id` is still live, and that no intervening aliasing revocation has occurred. Numeric equality `p.addr() == q.addr()` never transfers `q`'s allocation authority to `p`.

---

### 2. Raw-Pointer Value Validity vs. Access Validity and Alignment

Raw pointers distinguish between what bit patterns may exist **as a pointer value** (`ValidityInvariant(*const T / *mut T)`) and what conditions must hold **when accessing or dereferencing memory** (`AccessValid(ptr, access_kind)`):

1. **Runtime vs. CTFE Value Validity (`support/rust-raw-pointer-validity-provenance-alignment/obligation-matrix.json`):**
   - **Thin raw pointers (`*const T`, `*mut T` where `T: Sized`):** At runtime, any fully initialized pointer-sized integer bit pattern (including `0`, `usize::MAX`, or `transmute::<usize, *const u32>(1)`) is a valid thin raw pointer value. However, pointers forged via `transmute` from integers have **no provenance** (`without_provenance`) and are UB to dereference for any non-zero-sized access.
   - **Wide raw pointers:** A wide pointer value must have initialized data-pointer bytes and valid metadata (`usize` for `[T]` / `str`; `DynMetadata<Dyn>` for trait objects, where whether a raw `*const dyn Trait` value requires a valid vtable pointer even without calling `size_of_val_raw` or dynamic dispatch remains an open specification question in `behavior-considered-undefined.md` and `validity.rs`, so sound tooling must require valid vtable metadata whenever forming wide trait-object pointers).
   - **Const Evaluation (CTFE) Tightening:** During `const` evaluation (`validity.rs` lines 421–665), storing a pointer with provenance into an integer type or reading partial pointer fragments is rejected even when equivalent bit manipulation would be permitted at runtime.
2. **"Dangling" Terminology Split Between the Reference and `core::ptr`:**
   - In the **Rust Reference** (`behavior-considered-undefined.md`), "dangling" is size-relative: a pointer is dangling if not all pointed-to bytes belong to the same live allocation. Under this definition, a pointer to a zero-sized region (`0` bytes) is **never dangling**, even if it is null or `without_provenance(align)`.
   - In **`core::ptr` module docs** (`library/core/src/ptr/mod.rs`), "dangling" is frequently used as shorthand for a pointer created by `NonNull::dangling()` or `without_provenance(align)` that has no live allocation and is therefore only valid for aligned zero-sized accesses.
3. **Place Projection vs. Dereference Alignment:**
   - Misalignment of a dereferenced place `*ptr` is determined by the pointee type of the **last `*` dereference projection**, not just the final leaf field type (`behavior-considered-undefined.md`). If `S` has alignment 4 (`#[repr(C)] struct S { a: u32, b: u8 }`) and `ptr: *const S` has address `0x1001`, then evaluating `&raw const (*ptr).b` is **immediate UB** because `*ptr` dereferences a misaligned `*const S` before projecting `.b`, even though `b: u8` has alignment 1!
   - To project a field from a potentially unaligned base pointer without UB, one must compute the byte offset on the raw pointer itself (e.g., `ptr.wrapping_byte_add(offset_of!(S, b)).cast::<u8>()`) rather than evaluating `(*ptr).b`.
   - Conversely, if a place `place` is already validly constructed without dereferencing an unaligned pointer (for example, a field inside a `#[repr(packed)]` struct reached through a properly aligned `*const Packed`), taking `&raw const place.unaligned_field` or `&raw mut place.unaligned_field` is valid; UB occurs only if `&place.unaligned_field` is formed or the resulting unaligned `*const Field` is dereferenced with `*` or `ptr::read` instead of `ptr::read_unaligned`.
4. **Alignment Query Helpers (`is_aligned` and `is_aligned_to`):**
   - `ptr.is_aligned()` (for `T: Sized`, stable) and `ptr.is_aligned_to(align)` (unstable under `pointer_is_aligned_to`, requiring `align.is_power_of_two()`) inspect only the numerical data address (`self.addr() & (align - 1) == 0`) without reading memory or checking provenance (`support/rust-raw-pointer-validity-provenance-alignment/source-map.json`).

---

### 3. Pointer Casts and Provenance APIs (Strict vs. Exposed Provenance)

`core::ptr` and Rust's `as` cast operator provide two complementary provenance regimes (`support/rust-pointer-casts-provenance-apis/api-matrix.json`):

| Operation / API | Signature / Syntax | Provenance & Metadata Behavior | Safety / UB Conditions |
| :--- | :--- | :--- | :--- |
| **`ptr.addr()`** | `fn addr(self) -> usize` (`T: ?Sized`) | Extracts the numerical data address and **discards** provenance without exposing it. | Safe (`const` stable). Internally uses a privileged sysroot `transmute` on `self.cast::<()>()` that user code must not imitate. |
| **`ptr.with_addr(addr)`** / **`ptr.map_addr(f)`** | `fn with_addr(self, addr: usize) -> Self` (`T: ?Sized`) | Replaces the data address with `addr` (or `f(self.addr())`) via wrapping byte offset from `self`, preserving `self`'s provenance and wide metadata. | Safe to construct (`const` on `with_addr`); dereferencing the result is valid only if `self`'s original provenance covers `addr..addr + size`. |
| **`ptr::without_provenance(addr)`** / **`ptr::without_provenance_mut(addr)`** / **`ptr::dangling()`** / **`ptr::dangling_mut()`** | `const fn without_provenance(addr: usize) -> *const T` (`T: Sized`) | Creates a pointer with numerical address `addr` (or `align_of::<T>()` for `dangling`) and **empty provenance** (no associated allocation). | Safe to construct. Any non-zero-sized Rust-allocation read/write is **immediate UB**. Aligned zero-sized reads/writes are valid when `addr != 0`. |
| **`ptr.expose_provenance()`** / **`ptr as usize`** | `fn expose_provenance(self) -> usize` (`T: ?Sized`) | Returns the numerical data address and globally marks `self`'s provenance as **exposed** in the abstract machine. | Safe (not `const` when `self` carries provenance). |
| **`ptr::with_exposed_provenance(addr)`** / **`ptr::with_exposed_provenance_mut(addr)`** / **`addr as *const T`** | `fn with_exposed_provenance(addr: usize) -> *const T` (`T: Sized`) | Reconstructs a pointer at `addr` whose provenance is nondeterministically ("angelically") chosen from previously exposed provenances (or targets non-Rust hardware/MMIO addresses). | Safe to construct; dereferencing a Rust allocation is **UB** if the allocation's provenance was never exposed prior to reconstruction or no longer covers the access. |
| **`ptr.cast::<U>()`** / **`ptr as *const U`** | `const fn cast<U>(self) -> *const U` (`T: ?Sized, U: Sized`) | Preserves data address and provenance; drops any wide metadata of `T` because `U: Sized`. | Safe (`const`). Does not check alignment of `U` or adjust the address. |
| **`ptr.cast_mut()`** / **`ptr.cast_const()`** | `const fn cast_mut(self) -> *mut T` / `const fn cast_const(self) -> *const T` (`T: ?Sized`) | Changes only the pointer type's mutability marker while preserving address, provenance, and wide metadata unchanged. | Safe (`const`), but **does not upgrade provenance permissions**: casting a pointer derived from `&T` (without `UnsafeCell`) to `*mut T` via `cast_mut()` and writing through it is still **immediate UB**! |
| **Wide-to-wide `ptr as *const U`** | `*const [T; N] as *const [T]`, `*const U as *const V` (same DST tail) | Unsizing cast (`*const [T; N] -> *const [T]`) sets metadata to `N`; wide-to-wide raw cast between types with identical DST tails preserves existing metadata unchanged (`src/expressions/operator-expr.md`, blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a`). | Safe (`const`). Notice that casting `*const [u16] as *const [u8]` via raw `as` (when allowed on compatible slice tails) or `with_metadata_of` copies the **element count** without scaling by `size_of::<u16>() / size_of::<u8>()`! |

---

### 4. Pointer Arithmetic (`offset`, `add`, `sub`, `byte_*`, `wrapping_*`, and `offset_from`)

Pointer arithmetic splits strictly between **unsafe in-bounds arithmetic** (lowered to LLVM `getelementptr inbounds`) and **safe wrapping arithmetic** (lowered to `intrinsics::arith_offset`) (`support/rust-pointer-arithmetic/api-matrix.json`):

1. **Unsafe In-Bounds Arithmetic (`offset`, `add`, `sub`, `byte_offset`, `byte_add`, `byte_sub`):**
   - For element-scaled methods (`T: Sized`), let $\Delta = \text{count} \times \text{size\_of}::\langle T \rangle()$ (with negative sign for `sub`); for byte-scaled methods (`T: ?Sized`), let $\Delta = \text{count} \times 1$ (preserving wide metadata via `self.cast::<u8>().offset(count).with_metadata_of(self)`).
   - **Precondition 1 (Zero Delta):** If $\Delta == 0$ (either `count == 0` or `size_of::<T>() == 0`), `offset`/`add`/`sub` are **always safe** and return `self` unchanged, even if `self` is null, dangling, or unaligned!
   - **Precondition 2 (Non-Zero Delta):** If $\Delta \neq 0$, all of the following must hold at the moment of the arithmetic call (even if the resulting pointer is never dereferenced):
     1. $\Delta$ must fit mathematically in `isize` without overflow (`|\Delta| <= isize::MAX`).
     2. `self`'s address plus $\Delta$ must not wrap around the address space (`usize`).
     3. `self` must be derived from a pointer to some **live allocated object**, and the **entire closed byte range** between `self` and `self + \Delta` must lie within the bounds of that single allocated object (including the one-byte-past-the-end boundary `alloc_base + alloc_size`, which may be formed by `add`/`offset` so long as it is not dereferenced for non-zero bytes).
   - **Alignment Independence:** `offset`, `add`, `sub`, and `byte_*` do **not** require `self` to be aligned for `T` (`support/rust-pointer-arithmetic/source-map.json`).
2. **Safe Wrapping Arithmetic (`wrapping_offset`, `wrapping_add`, `wrapping_sub`, `wrapping_byte_offset`, `wrapping_byte_add`, `wrapping_byte_sub`):**
   - Always safe (`const fn`) for any pointer value (null, dangling, unaligned, or out-of-bounds) and any `count`.
   - Computes two's-complement wrapping arithmetic `(self.addr() + (count as isize).wrapping_mul(size_of::<T>() as isize)) as usize` while **retaining `self`'s original provenance** and wide metadata.
   - A pointer may step outside its allocation with `wrapping_add` and later step back inside with `wrapping_sub` and still be validly dereferenced. However, if `wrapping_add` numerically lands inside a *different* allocation's address range, dereferencing it is **UB** because its provenance still belongs to the original allocation.
3. **Pointer Difference (`offset_from`, `offset_from_unsigned`, `byte_offset_from`, `byte_offset_from_unsigned`):**
   - Unsafe (`const fn`). For element-scaled `ptr1.offset_from(ptr2)` / `ptr1.offset_from_unsigned(ptr2)` (`T: Sized`), **`size_of::<T>() == 0` panics at runtime (or fails const-eval) unconditionally** (`assert!(0 < pointee_size && pointee_size <= isize::MAX as usize)`).
   - When `ptr1` and `ptr2` have different addresses (`ptr1.addr() != ptr2.addr()`), both must be derived from the **same live allocated object**, both must be in bounds (or one-past-the-end) of that allocation, the byte distance `(ptr1.addr() as isize) - (ptr2.addr() as isize)` must be an exact multiple of `size_of::<T>()` (`byte_offset_from` sets stride to `1`), and for `*_unsigned` `ptr1.addr() >= ptr2.addr()` must hold.

---

### 5. `core::ptr::NonNull<T>` Value Invariant, Variance, and Provenance

`core::ptr::NonNull<T>` (`library/core/src/ptr/non_null.rs`, blob `86e9d01381a5198a4694137fafa75beb6a4f9f06`) wraps a raw pointer in a non-zero layout scalar (`#[repr(transparent)]`, `rustc_layout_scalar_valid_range_start(1)` on the inner `*const T`):

1. **Permanent Non-Null Value Invariant and Niche Layout (`support/rust-nonnull/obligation-matrix.json`):**
   - `NonNull<T>` is guaranteed never to have data address `0`. Calling `NonNull::new_unchecked(ptr)` when `ptr.is_null()` is **immediate UB** even if the `NonNull<T>` is never dereferenced or inspected.
   - Because `0` is a niche, `size_of::<Option<NonNull<T>>>() == size_of::<NonNull<T>>()` and `align_of::<Option<NonNull<T>>>() == align_of::<NonNull<T>>()` for both thin (`T: Sized`, 8 bytes on 64-bit targets) and wide (`T: ?Sized`, 16 bytes on 64-bit targets, where the niche lives in the data-pointer half) pointers.
2. **Covariance and Thread-Safety Markers:**
   - Unlike `*mut T` (which is **invariant** in `T`), `NonNull<T>` is **covariant** in `T` because it stores `*const T` internally. Data structures that logically own or mutate `T` through `NonNull<T>` must add `PhantomData<T>` (for ownership dropcheck) or `PhantomData<Cell<T>>` / `PhantomData<*mut T>` if invariance is required for soundness.
   - `NonNull<T>` is explicitly `!Send` and `!Sync`, and implements `Copy` and `Clone` unconditionally regardless of whether `T: Copy`.
3. **Read-Only Provenance Under `From<&T>` / `NonNull::from_ref`:**
   - Converting `&T` to `NonNull<T>` (`NonNull::from(r)` or `NonNull::from_ref(r)`) and calling `.as_ptr() -> *mut T` yields a mutable pointer **type**, but its **provenance remains shared/read-only** (unless `T` contains `UnsafeCell`). Writing through `NonNull::from(shared_ref).as_ptr()` is immediate UB.
4. **`NonNull::dangling()` Address Coincidence Hazard:**
   - `NonNull::<T>::dangling()` returns `NonNull::without_provenance(NonZero::new(align_of::<T>()).unwrap())`. Because `align_of::<T>()` is a small non-zero integer, it is **not guaranteed to be distinct from all live allocations** in every address space, and therefore must never be used as an in-band "uninitialized" sentinel compared by address against potentially allocated pointers (use `Option<NonNull<T>>` instead, which is zero-cost due to niche optimization).
5. **Deliberate Omission of Wrapping Arithmetic on `NonNull<T>`:**
   - `NonNull<T>` provides unsafe in-bounds arithmetic (`offset`, `add`, `sub`, `byte_offset`, `byte_add`, `byte_sub`, where non-null in-bounds arithmetic cannot wrap to zero) and `NonZero<usize>`-typed provenance methods (`addr() -> NonZero<usize>`, `with_addr(NonZero<usize>)`, `without_provenance(NonZero<usize>)`), but **intentionally omits `wrapping_offset` / `wrapping_add` / `wrapping_sub`** because wrapping arithmetic on a non-null pointer could wrap to address `0` and violate `NonNull`'s validity invariant.

---

### 6. Raw Slice Pointer Construction vs. Reference Slice Construction

Raw slice pointer constructors and reference slice constructors have fundamentally different safety boundaries (`support/rust-raw-slice-pointer-construction/contract-matrix.json`):

| Function | Signature | Immediate Preconditions at Call Site | Dereference / Reborrow Preconditions |
| :--- | :--- | :--- | :--- |
| **`ptr::slice_from_raw_parts(data, len)`** / **`ptr::slice_from_raw_parts_mut(data, len)`** | `const fn(*const T, usize) -> *const [T]` / `const fn(*mut T, usize) -> *mut [T]` | **None (completely safe!).** `data` may be null, dangling, unaligned, or uninitialized, and `len` may be any `usize` (even exceeding `isize::MAX`). Calling `(*slice_ptr).len()` or `(*slice_ptr).is_empty()` reads only the pointer metadata without dereferencing `data`. | Before indexing or converting to `&[T]` / `&mut [T]`, `data` and `len` must satisfy the target operation's validity rules. |
| **Unstable `(*const [T; N]).cast_slice()`** / **`(*mut [T; N]).cast_slice()`** (`ptr_cast_slice`) | `const fn(*const [T; N]) -> *const [T]` | **None (completely safe!).** Equivalent to `slice_from_raw_parts(self.cast(), N)` (`as *const [T]`). | Same deferred requirements as `slice_from_raw_parts`. |
| **`slice::from_raw_parts<'a, T>(data, len)`** / **`slice::from_raw_parts_mut<'a, T>(data, len)`** | `const unsafe fn(*const T, usize) -> &'a [T]` / `const unsafe fn(*mut T, usize) -> &'a mut [T]` (`library/core/src/slice/raw.rs`, blob `80b2176933dab215bef525076ceb9089c04389cb`) | **Immediate UB at call site unless all hold:** (1) `data` is **non-null and aligned for `T` even when `len == 0` or `size_of::<T>() == 0`** (use `NonNull::dangling().as_ptr()` for empty slices); (2) `len * size_of::<T>() <= isize::MAX`; (3) if `len * size_of::<T>() > 0`, `data` points to `len` contiguous initialized `T` values within a **single live allocated object**; (4) `&'a [T]` / `&'a mut [T]` aliasing rules hold for the duration of `'a`. | Already discharged at construction. |

---

### 7. Wide-Pointer Metadata (`Pointee::Metadata`, `DynMetadata`, and `with_metadata_of`)

Under `#![feature(ptr_metadata)]` (`library/core/src/ptr/metadata.rs`, blob `1eeadf1217b5f941890c`), every type `T: ?Sized` has an associated `<T as Pointee>::Metadata: Copy + Send + Sync + Ord + Hash + Unpin + Freeze` (`support/rust-wide-pointer-metadata/metadata-matrix.json`):

1. **Metadata Classification by Pointee Kind:**
   - **Thin pointers (`Metadata = ()`, trait alias `ptr::Thin = Pointee<Metadata = ()>`):** All `T: Sized` types and unstable `extern type` foreign types.
   - **Slices (`[T]`):** `Metadata = usize`, storing the **element count** (not byte length, unless `size_of::<T>() == 1`).
   - **String slices (`str`):** `Metadata = usize`, storing the **byte length**.
   - **Trait objects (`dyn Trait`):** `Metadata = DynMetadata<dyn Trait>`, wrapping a non-null static vtable pointer (`&'static VTable`).
   - **Custom DST structs (`struct Dst<T: ?Sized> { head: H, tail: T }`):** `<Dst<T> as Pointee>::Metadata == <T as Pointee>::Metadata`.
2. **Metadata Extraction, Recomposition, and `with_metadata_of`:**
   - `ptr::metadata(ptr)` and `ptr.to_raw_parts() -> (*const (), <T as Pointee>::Metadata)` are safe (`const`) and never dereference `ptr`.
   - `ptr::from_raw_parts(data_ptr, meta)` and `ptr::from_raw_parts_mut(data_ptr, meta)` are safe (`const`) and take the data address and provenance from `data_ptr` (`*const impl Thin` / `*mut impl Thin`) and attach `meta`.
   - `ptr.with_metadata_of(meta_src)` (`*const T::with_metadata_of<U: ?Sized>(self, val: *const U) -> *const U` where `U` is a DST or `Sized`) takes the **data address and provenance exclusively from `self`** and the **metadata exclusively from `val`**, lowered via the `set_ptr_value` intrinsic. It never merges or transfers provenance from `val`!
3. **`DynMetadata<Dyn>` Size/Align Footgun on Structs with `dyn Trait` Tails:**
   - `DynMetadata::size_of(self)`, `align_of(self)`, and `layout(self)` read the size and alignment stored in the vtable of the concrete erased type `T` that implements `Trait`.
   - For a direct trait object `*const dyn Trait`, `metadata(ptr).size_of()` equals the dynamic size of the pointee. However, for a **struct with a `dyn Trait` tail** such as `struct MyDst(u64, dyn Send)`, `<MyDst as Pointee>::Metadata` is `DynMetadata<dyn Send>`, so `metadata(ptr).size_of()` returns **only the size of the `dyn Send` tail**, excluding the `u64` prefix and tail padding! To compute the full size of a general `?Sized` value, callers must use `mem::size_of_val_raw(ptr)` rather than `ptr::metadata(ptr).size_of()`.
4. **Wide-Pointer Equality and Ordering (`==`, `<`) and Vtable Identity:**
   - Raw wide-pointer comparisons (`*const [T]`, `*const dyn Trait`) compare **both** the data address and the metadata (`(a.to_raw_parts().0.addr(), a.to_raw_parts().1) == (b.to_raw_parts().0.addr(), b.to_raw_parts().1)`).
   - Two `DynMetadata<dyn Trait>` values for the **same concrete type** may compare unequal if codegen units duplicate vtables, and two vtables for **different concrete types** may be merged by linker ICF; therefore, `DynMetadata` equality must never be relied upon as a sound runtime type-identity test (`TypeId` / `Any` must be used instead).

---

## Boundaries

1. **Typed vs. Untyped Memory Reads/Writes, `copy`, `read_volatile`, and `UnsafeCell`:** Once a raw pointer's provenance, alignment, and bounds are established, the operational rules for `ptr::read`, `ptr::write`, `ptr::copy`, `ptr::read_volatile`, `&*ptr` reference creation, and `UnsafeCell<T>` interior mutability are covered in `rust-pointer-read-write-copy-volatile-and-reference-reborrowing`.
2. **Stacked Borrows vs. Tree Borrows Retagging Nuances:** Fine-grained differences between Miri's experimental aliasing models (`-Zmiri-tree-borrows` vs. default Stacked Borrows) on protector tags and two-phase borrows remain active research areas outside the settled `core::ptr` and Reference provenance rules documented here.
3. **Inline Assembly (`asm!`) and External FFI Provenance Exposure:** Whether passing a pointer to an external C function or `asm!` block implicitly exposes its provenance depends on target FFI semantics and compiler flags; verification models should treat explicit `.expose_provenance()` or Strict Provenance `with_addr` as the normative contract.

---

## Evidence

| Package Namespace | Preserved Support Artifacts | Key Upstream Commits & Files |
| :--- | :--- | :--- |
| `rust-authority-provenance` | `support/rust-authority-provenance/coverage.json` | `rust-lang/reference@f100ffd2dc3fbef43fbca8facf7fb5dc9be2bc8b` (`src/behavior-considered-undefined.md`); `rust-lang/rust@e75bad700fc6eb2cfe2bfec5fd6cb0fd1ab3cde5` (`library/core/src/ptr/mod.rs`); UCG `d809f91e62968913d808e53397fbcf7cea762cce` (`src/glossary.md`); WG14 N2364 (`2019-04-01`). |
| `rust-raw-pointer-validity-provenance-alignment` | `support/rust-raw-pointer-validity-provenance-alignment/obligation-matrix.json`, `support/rust-raw-pointer-validity-provenance-alignment/source-map.json` | `library/core/src/ptr/mod.rs` (blob `ff2c18d685b65832c296731f23f1664779b874f2`); `library/core/src/ptr/const_ptr.rs` (blob `5cbbebf9f478819ee80e0c6486d622ae9ffdac00`); `compiler/rustc_const_eval/src/interpret/validity.rs` (blob `bd2942702dd5ebbc5e898c0142423437f78979d0`). |
| `rust-pointer-casts-provenance-apis` | `support/rust-pointer-casts-provenance-apis/api-matrix.json`, `support/rust-pointer-casts-provenance-apis/source-map.json` | `rust-lang/reference@f100ffd2dc3fbef43fbca8facf7fb5dc9be2bc8b` (`src/expressions/operator-expr.md`, blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a`); `library/core/src/ptr/mod.rs`, `const_ptr.rs`, `mut_ptr.rs` (blob `53ef7f754d201a1dc08aa50a320266a8ab55245f`). |
| `rust-pointer-arithmetic` | `support/rust-pointer-arithmetic/api-matrix.json`, `support/rust-pointer-arithmetic/source-map.json` | `library/core/src/ptr/const_ptr.rs`, `mut_ptr.rs`; `library/core/src/intrinsics/mod.rs` (blob `78d7314c58110b49839894a0f69377f4ee0d1204`, `offset` and `arith_offset`). |
| `rust-nonnull` | `support/rust-nonnull/obligation-matrix.json`, `support/rust-nonnull/source-map.json` | `library/core/src/ptr/non_null.rs` (blob `86e9d01381a5198a4694137fafa75beb6a4f9f06`). |
| `rust-raw-slice-pointer-construction` | `support/rust-raw-slice-pointer-construction/contract-matrix.json`, `support/rust-raw-slice-pointer-construction/source-map.json` | `library/core/src/ptr/mod.rs`, `const_ptr.rs`, `mut_ptr.rs`; `library/core/src/slice/raw.rs` (blob `80b2176933dab215bef525076ceb9089c04389cb`). |
| `rust-wide-pointer-metadata` | `support/rust-wide-pointer-metadata/metadata-matrix.json`, `support/rust-wide-pointer-metadata/source-map.json` | `library/core/src/ptr/metadata.rs` (blob `1eeadf1217b5f94b48a33de62cd82ad47941890c`). |

---

## Revalidation

Revalidate this package whenever:
1. `rust-lang/reference` updates `src/behavior-considered-undefined.md` or `src/expressions/operator-expr.md` regarding pointer provenance, dangling pointers, place-projection alignment, or wide-pointer raw casts.
2. `rust-lang/rust` modifies `library/core/src/ptr/{mod.rs,const_ptr.rs,mut_ptr.rs,non_null.rs,metadata.rs}` or `library/core/src/slice/raw.rs`, stabilizes `ptr_metadata`, `ptr_cast_slice`, `pointer_is_aligned_to`, or `ptr_as_uninit`, or changes CTFE pointer-fragment checking in `compiler/rustc_const_eval/src/interpret/validity.rs`.
