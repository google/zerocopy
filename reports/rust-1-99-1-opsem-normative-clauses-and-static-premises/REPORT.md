# Normative Rust 1.99.1 Operational-Semantics Clauses and Static-vs-Dynamic Premise Stratification

## Summary

This report records an 87-clause primary-source ledger of Rust operational-semantics, layout, pointer/memory, cleanup/unwinding, and atomic/concurrency contracts pinned to stable Rust `1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) and its bundled Rust Reference submodule (`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`), paired with a static-versus-dynamic premise stratification across Rust `1.99.1` and MiniRust (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`).

The investigation establishes two foundational results for formal verification and unsafe-code reasoning:
1. **Explicit Authority Stratification across 87 Clauses (`S01`–`S31`, `F01`–`F11`, `D01`–`D26`, `C01`–`C21`, `M01`–`M08`):** Normative Reference guarantees, standard-library API safety contracts, compiler implementation behaviors, exploratory operational models (such as Stacked Borrows, Tree Borrows, and MiniRust), and non-normative warnings are separated so that unratified aliasing or provenance heuristics are never conflated with stable language guarantees.
2. **Separation of Static Well-Formedness from Dynamic Operational Safety:** Static well-formedness (`check_wf`), layout/ABI coherence, constant-evaluation certificates, and dynamic execution safety (validity, initialization, dereferenceability, alignment, and alias permissions) are independent obligations. In particular, MiniRust's executable `Type::check_wf` (`spec/lang/well-formed.md`) is strictly weaker than the representation coherence premises required by its own value-representation round-trip and deflation theorems (`spec/lang/representation.md:623-763`, `minirust#288`), and `Terminator::Call` (`spec/lang/step/terminators.md:201-276`) requires dynamic ABI compatibility checks even when static `check_wf` succeeds.

## Applicability

- **Rust release and standard library (`rust`):** `1.99.1`, commit `58cf8f9c35b355199727627d07ae34a4e2846d67` (`library/core/src/*`, `library/alloc/src/*`, `compiler/rustc_abi/src/lib.rs`, `src/doc/reference` gitlink).
- **The Rust Reference (`rust-reference`):** Commit `82da570bafd9efed421bdbae0f8603ede8dd308b` (`src/behavior-considered-undefined.md`, `src/memory-model.md`, `src/type-layout.md`, `src/destructors.md`, `src/panic.md`, `src/items/external-blocks.md`, `src/items/functions.md`, `src/inline-assembly.md`, `src/expressions/operator-expr.md`, `src/types/pointer.md`, `src/types/union.md`, `src/unsafe-keyword.md`).
- **MiniRust specification (`minirust`):** Commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`, 28 Markdown specification files in [`support/minirust-sources.json`](support/minirust-sources.json)).
- **Downstream relevance:** Unsafe Rust libraries (such as `zerocopy`), formal operational semantics, and verification condition generators that must distinguish documented stable Rust guarantees from target-conditional layout properties, library precondition contracts, and open semantic questions.

## Findings

### 1. Source-Authority Hierarchy and Claim Discipline

Basis: documentation, source

Every clause in this ledger is assigned one of five explicit authority classes, verified against [`support/sources.json`](support/sources.json):

| Authority Class | Definition | Operational Role |
| :--- | :--- | :--- |
| `normative_reference` | Normative prose in The Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`) | Defines language-level layout guarantees, evaluation order, destructor scopes, and behaviors considered undefined (`UB`). |
| `standard_library_contract` | Normative API documentation and `# Safety` sections in `core`/`alloc` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) | Defines caller preconditions and postconditions for pointer reads/writes, copies, slices, `MaybeUninit`, `ManuallyDrop`, `Box`, and `atomic`. |
| `compiler_implementation` | Compiler data structures and queries in `rustc` (`compiler/rustc_abi`, `compiler/rustc_ty_utils`) | Documents how a pinned `rustc` revision represents and computes layouts or lowers MIR, without elevating internal compiler choices to cross-version language guarantees. |
| `exploratory_background` | MiniRust, Unsafe Code Guidelines (UCG), Stacked Borrows, and Tree Borrows | Candidate operational models and design references; must not be cited as settled Rust law where the Reference or library docs explicitly leave behavior open. |
| `non_normative_note` | Reference/library `Note:` blocks, warnings, and incompleteness disclaimers | Bounds what may be inferred from surrounding normative rules (for example, that the Reference's UB list is non-exhaustive and the aliasing model is still unsettled). |

### 2. Sequential Core, Layout, and Value Representation Clauses (`S01`–`S31`)

Basis: documentation, source

The 31 sequential core clauses pinned in [`support/sources.json`](support/sources.json) govern soundness obligations, byte representation, pointer provenance, type layout, validity invariants, and primitive memory operations:

| Clause | Authority | Pinned Source Location | Normative Content and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `S01` | `normative_reference` | `src/unsafe-keyword.md:27-57`, `src/behavior-considered-undefined.md:5-22` | Soundness means safe callers cannot cause UB under any input. Every `unsafe` block bears the obligation of satisfying the preconditions of all operations inside it. |
| `S02` | `non_normative_note` | `src/behavior-considered-undefined.md:14-18`, `src/memory-model.md:1-16` | The Reference's UB list is explicitly non-exhaustive and the Rust memory model is incomplete; absence from a single bullet does not by itself certify soundness. |
| `S03` | `normative_reference` | `src/memory-model.md:4-26` | A byte is either uninitialized or initialized to a numeric value `0..=255` with optional pointer provenance. This byte state space is explicitly marked non-exhaustive. |
| `S04` | `normative_reference` | `src/memory-model.md:28-55` | Allocations have base addresses, lengths, and provenance; pointers combine an address with optional provenance; provenance is preserved across valid pointer copies/casts and constrains memory accesses. |
| `S05` | `normative_reference`, `standard_library_contract` | `src/behavior-considered-undefined.md:62-97`, `library/core/src/ptr/mod.rs:342-391` | Dereferencing or accessing memory through a pointer requires alignment, non-nullness (where applicable), in-bounds address range, live allocation, and valid provenance (except zero-sized accesses, which still require non-nullness and alignment on typed APIs). |
| `S06` | `standard_library_contract` | `library/core/src/ptr/mod.rs:108-165` | Whether a pointer is "dereferenceable" for size `N` is defined over a set of byte addresses that need **not** be a single contiguous `[ptr, ptr + N)` interval (`UnsafeCell` / partial-projection carveouts), though standard contiguous primitives require `[ptr, ptr + size_of::<T>())`. |
| `S07` | `normative_reference` | `src/behavior-considered-undefined.md:99-119`, `src/types/pointer.md:84-125` | Reference aliasing rules: breaking `&mut T` uniqueness or mutating through `&T` without `UnsafeCell<U>` is UB; the exact operational aliasing boundary for raw pointers derived from references remains open (`S08`). |
| `S08` | `non_normative_note` | `src/behavior-considered-undefined.md:113-119` | The exact aliasing model is not yet decided; until settled, programmers must satisfy both uniqueness/immutability of active references and provenance tracking through raw pointer conversions. |
| `S09` | `normative_reference` | `src/type-layout.md:1-16` | Size is always a multiple of alignment (`size % align == 0`), alignment is a power of two $\ge 1$, and both are target-conditional properties of a type. |
| `S10` | `normative_reference` | `src/type-layout.md:18-64` | Primitive layout guarantees: `bool` and `u8`/`i8` have size 1 and align 1; `u16`/`u32`/`u64`/`u128` have sizes 2, 4, 8, 16; thin pointers and `usize`/`isize` have identical size and alignment on a given target. |
| `S11` | `normative_reference` | `src/type-layout.md:66-123` | Wide pointer layout:Pointers/references to `[T]`, `str`, and `dyn Trait` have size $2 \times \text{size\_of}::<\text{usize}>()$, but the internal field ordering `(data, metadata)` vs. `(metadata, data)` is **not** guaranteed across compilations. |
| `S12` | `normative_reference` | `src/type-layout.md:125-169` | Array layout `[T; N]` has size $\text{size\_of}::<T>() \times N$ and alignment $\text{align\_of}::<T>()$ with dense element stride; slice `[T]` has the same element layout as an array of the dynamic length. |
| `S13` | `normative_reference` | `src/type-layout.md:171-201` | Default `repr(Rust)` struct/tuple layout does **not** guarantee field order, inter-field padding offsets, or deterministic layout across distinct struct definitions (save for `()` having size 0, align 1). |
| `S14` | `normative_reference` | `src/type-layout.md:203-267` | `#[repr(C)]` struct layout guarantees deterministic forward field placement (`offset` rounded up to each field's alignment, aggregate alignment = max field alignment, total size rounded up to aggregate alignment; empty `repr(C)` fieldless structs in Rust have size 0, differing from C/C++). |
| `S15` | `normative_reference` | `src/type-layout.md:269-313` | `#[repr(packed(N))]` and `#[repr(align(N))]` modifiers: `packed(N)` caps field and aggregate alignment to $\min(\text{natural\_align}, N)$; `align(N)` raises aggregate alignment to $\max(\text{natural\_align}, N)$; `packed` and `align` cannot be combined on the same type, and taking an unaligned reference to a packed field is UB. |
| `S16` | `normative_reference` | `src/type-layout.md:315-481` | `#[repr(Int)]`, `#[repr(C)]`, and `#[repr(C, Int)]` enum layouts: fieldless enums have the size/align of the discriminant integer; data-carrying enums have explicit C/primitive representation equivalents (`tag` + union of variant payloads). |
| `S17` | `normative_reference` | `src/type-layout.md:483-532` | `#[repr(transparent)]` requires exactly one non-zero-sized field (with any number of ZST fields of alignment 1 unless `align` is compatible) and guarantees identical layout and ABI to that single field. |
| `S18` | `normative_reference`, `standard_library_contract` | `src/type-layout.md:102-123`, `library/core/src/option.rs:172-238` | Guaranteed niche optimization: `Option<&T>`, `Option<&mut T>`, `Option<fn(...)>`, `Option<NonNull<T>>`, `Option<Box<T>>` (with global allocator), and `Option<NonZero*>` have identical size, alignment, and ABI to their inner non-null type, with `None` represented as all-zero pointer/integer bits. |
| `S19` | `normative_reference` | `src/behavior-considered-undefined.md:121-225` | Value validity invariants: `bool` must be `0x00` or `0x01`; `char` must be a non-surrogate Unicode scalar value; integers/floats must be initialized; `str` must be valid UTF-8; `!` is uninhabited; enums must have a valid discriminant and valid active variant fields; references/boxes must be aligned, non-null, and point to valid values. |
| `S20` | `normative_reference` | `src/behavior-considered-undefined.md:165-191` | Integer and raw-pointer validity subtilty: reading uninitialized bytes as an integer is immediate UB, whereas reading provenance-bearing pointer bytes as an integer is UB **in `const` evaluation** and strips provenance (producing an integer without provenance) at runtime unless specific operational rules apply. |
| `S21` | `normative_reference`, `standard_library_contract` | `src/types/union.md:54-119`, `library/core/src/mem/maybe_uninit.rs:108-196` | Unions and `MaybeUninit<T>`: union validity does not require all fields to be simultaneously valid; `MaybeUninit<T>` (`#[repr(transparent)]` over a union of `ManuallyDrop<T>` and `()`) has identical size, alignment, and ABI to `T`, while relaxing initialization/validity invariants until `assume_init` is called. |
| `S22` | `standard_library_contract` | `library/core/src/mem/maybe_uninit.rs:267-312` | Typed copies of `MaybeUninit<T>` or `T` (`*x = *y`): preserve initialized data bytes for fields of `T`, but padding bytes of `T` may become uninitialized on a typed copy of `T` (whereas copying `MaybeUninit<T>` or `[MaybeUninit<u8>; N]` preserves every byte); if `T` contains references, typed copies may reborrow them. |
| `S23` | `normative_reference` | `src/expressions/operator-expr.md:274-366` | Place vs. value expressions and borrow/addr-of operators: `&place`, `&mut place`, `&raw const place`, and `&raw mut place` evaluate the place without reading its stored value, though reference creation (`&`/`&mut`) immediately requires reference validity (`S19`) while `&raw` does not require pointee validity or initialization. |
| `S24` | `standard_library_contract` | `library/core/src/ptr/mod.rs:956-1099` | Wrapping vs. in-bounds pointer offset arithmetic: `ptr.offset(count)` / `ptr.add(count)` require the start, end, and intermediate range to lie within a single live allocation (and not wrap around `isize::MAX` / address space); `wrapping_offset` / `wrapping_add` perform two's-complement address arithmetic without in-bounds UB, retaining the original provenance. |
| `S25` | `standard_library_contract` | `library/core/src/ptr/mod.rs:576-662` | Raw byte-copy intrinsics: `ptr::copy(src, dst, count)` (`memmove`) allows overlapping ranges and behaves as if reading through a temporary array; `ptr::copy_nonoverlapping(src, dst, count)` (`memcpy`) requires disjoint `[src, src + count * size_of::<T>())` and `[dst, dst + count * size_of::<T>())` intervals. Both preserve initialization and pointer provenance byte-for-byte. |
| `S26` | `standard_library_contract` | `library/core/src/ptr/mod.rs:1322-1589` | Typed pointer reads and writes: `ptr::read` and `ptr::write` require alignment; `ptr::read_unaligned` and `ptr::write_unaligned` drop the alignment requirement on the outer pointer while still requiring pointee initialization/validity (for `read*`) and valid writable storage (for `write*`) without dropping the previous destination value. |
| `S27` | `standard_library_contract` | `library/core/src/ptr/mod.rs:1661-1778` | Volatile accesses (`read_volatile`, `write_volatile`): treated as externally observable side effects that cannot be elided or reordered across other volatile operations, require alignment and valid initialized values, and have unsettled cross-thread data-race semantics on non-atomic memory. |
| `S28` | `standard_library_contract` | `library/core/src/slice/raw.rs:64-174` | Raw slice construction (`slice::from_raw_parts`, `from_raw_parts_mut`): requires a non-null, aligned data pointer, a single contiguous live allocation covering `len * size_of::<T>()` bytes (`len * size_of::<T>() <= isize::MAX`), valid initialized elements `0..len`, and reference aliasing compliance for the slice's lifetime (even when `len == 0`, the pointer must be non-null and aligned!). |
| `S29` | `standard_library_contract` | `library/core/src/mem/mod.rs:658-734` | `mem::transmute<Src, Dst>` and `transmute_copy`: reinterpret the bytes of `Src` as `Dst` (taking ownership of `Src` without running its destructor in `transmute`), requiring that the bytes of `Src` form a valid value of type `Dst` at that point in execution. |
| `S30` | `standard_library_contract` | `library/core/src/ptr/mod.rs:2125-2485` | Strict Provenance and Exposed Provenance APIs (`with_addr`, `map_addr`, `addr`, `expose_provenance`, `with_exposed_provenance`): `with_addr` combines an existing pointer's provenance with a new address without exposing provenance; `with_exposed_provenance` reconstructs provenance only if previously exposed, under angelically/nondeterministically resolved rules. |
| `S31` | `compiler_implementation` | `compiler/rustc_abi/src/lib.rs:1395-1565` | Compiler `LayoutData<FieldIdx, VariantIdx>` in `rustc_abi`: packages `FieldsShape` (`Primitive`, `Union`, `Array`, `Arbitrary`), `Variants` (`Single`, `Empty`, `Multiple` with `TagEncoding::Direct` or `Niche`), `BackendRepr` (`Scalar`, `ScalarPair`, `SimdVector`, `Memory`), `Align`, and `Size`. This is an internal compiler representation, not a surface-language stability promise. |

### 3. Foreign Calls, Inline Assembly, and ABI Boundaries (`F01`–`F11`)

Basis: documentation, source

| Clause | Authority | Pinned Source Location | Normative Content and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `F01` | `normative_reference` | `src/items/external-blocks.md:1-142`, `src/items/functions.md:360-478` | Calling an `extern` function or passing a function pointer across an ABI boundary requires matching calling-convention strings (`"C"`, `"Rust"`, `"system"`, etc., with `"C-unwind"` vs. `"C"` unwind-behavior distinction). |
| `F02` | `normative_reference` | `src/behavior-considered-undefined.md:32-48` | Invoking a function through a function pointer whose ABI, argument types, or return type are ABI-incompatible with the target function definition is immediate UB. |
| `F03` | `normative_reference` | `src/type-layout.md:483-532`, `src/type-layout.md:102-123` | ABI compatibility for `#[repr(transparent)]` wrappers and guaranteed niche-optimized `Option` types (`S18`) holds only when the inner non-ZST field is itself FFI-compatible. |
| `F04` | `normative_reference` | `src/items/functions.md:430-478` | Unwinding across an FFI boundary whose ABI does not permit unwinding (e.g., `extern "C"` instead of `extern "C-unwind"`) is UB or triggers an immediate process abort. |
| `F05` | `normative_reference` | `src/inline-assembly.md:1-145` | `core::arch::asm!` and `global_asm!` syntax, register classes, and operand direction modifiers (`in`, `out`, `inout`, `inlateout`, `sym`, `const`). |
| `F06` | `normative_reference` | `src/inline-assembly.md:490-615` | Inline assembly options (`pure`, `nomem`, `readonly`, `preserves_flags`, `noreturn`, `nostack`, `may_unwind`, `raw`): violating any declared option (e.g., writing memory under `nomem`/`readonly`, or returning from a `noreturn` block) is UB. |
| `F07` | `normative_reference` | `src/inline-assembly.md:617-758` | Register clobbers and ABI preservation in `asm!`: any register modified by the assembly template that is not declared as an output or clobber (`clobber_abi(...)`) causes UB. |
| `F08` | `normative_reference` | `src/inline-assembly.md:760-852` | Memory and aliasing interaction of `asm!`: assembly blocks must obey the Rust memory and aliasing model for all memory accessed through passed pointers (`in(reg) ptr`), and may only unwind if `options(may_unwind)` is declared. |
| `F09` | `standard_library_contract` | `library/alloc/src/boxed.rs:190-275` | `Box<T>` FFI layout contract: `Box<T>` with the global allocator (`Box<T, Global>`) for sized `T` is ABI-compatible with a non-null C pointer `T*` (and `Option<Box<T>>` with a nullable `T*`), provided ownership/deallocation remains matched to the Rust allocator. |
| `F10` | `standard_library_contract` | `library/core/src/ffi/mod.rs:1-125` | `core::ffi::c_void` and C integer primitives (`c_char`, `c_int`, `c_ulong`, etc.) match the target platform's C ABI type widths and alignments. |
| `F11` | `non_normative_note` | `src/items/external-blocks.md:95-142` | Improper C types warning (`improper_ctypes_definitions`): passing `repr(Rust)` structs, fat pointers (`&[T]`, `&str`, `&dyn Trait`), or non-`repr(C)` enums across `extern "C"` boundaries has no stable ABI contract. |

### 4. Destructors, Drop Flags, `ManuallyDrop`, and Unwinding (`D01`–`D26`)

Basis: documentation, source

| Clause | Authority | Pinned Source Location | Normative Content and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `D01` | `normative_reference` | `src/destructors.md:1-48` | A type has drop glue if it implements `Drop` or recursively contains a field/element with drop glue; `drop_in_place<T>` executes `T::drop(&mut self)` first, followed recursively by the drop glue of `T`'s fields. |
| `D02` | `normative_reference` | `src/destructors.md:50-112` | Scope-exit drop order: variables in a block or scope are dropped in **reverse** declaration order; struct, tuple, and array fields/elements are dropped in **forward** declaration/index order (`0, 1, ...`). |
| `D03` | `normative_reference` | `src/destructors.md:114-188` | Temporary lifetimes: temporaries created in a statement are dropped at the end of the enclosing statement unless lifetime-extended by a syntactic reference/pattern binding into an outer `let`. |
| `D04` | `normative_reference` | `src/destructors.md:190-256` | Partial initialization and dynamic drop flags: moving out of a variable or struct field deinitializes that subpath; at scope exit or unwind, only currently initialized fields/variables are dropped. |
| `D05` | `normative_reference` | `src/destructors.md:230-256` | Reassignment of an already-initialized place drops the old value **before** overwriting it with the new value (whereas initializing an uninitialized variable or moved-from subpath does not run a destructor on the old storage). |
| `D06` | `normative_reference` | `src/destructors.md:258-295` | Binding to the wildcard pattern `_` (`let _ = expr;`) does **not** bind the value to a local; `expr` is evaluated as a temporary and dropped at the end of the statement, whereas `let _x = expr;` drops at block exit. |
| `D07` | `standard_library_contract` | `library/core/src/ops/drop.rs:1-118` | `Drop::drop(&mut self)` cannot be called directly in safe or unsafe code (`E0040`); explicit destruction must use `core::mem::drop(x)` (by value) or `core::ptr::drop_in_place(ptr)` (in place). |
| `D08` | `standard_library_contract` | `library/core/src/ptr/mod.rs:515-574` | `ptr::drop_in_place(to_drop: *mut T)` safety contract: `to_drop` must be non-null, aligned, and valid for both reads and writes, and the pointee must be valid for dropping; after `drop_in_place` returns, the pointee must be treated as uninitialized/moved-from unless reinitialized. |
| `D09` | `standard_library_contract` | `library/core/src/mem/mod.rs:135-210` | `core::mem::forget(t)` and `core::mem::drop(t)`: `drop(t)` moves `t` into an empty function body so its destructor runs immediately; `forget(t)` wraps `t` in `ManuallyDrop::new(t)` and returns without running any destructor. Leaking a value via `forget` is always safe (`S01`), so unsafe code must **never** rely on a destructor running for soundness (`leaking` / `Pin` drop guarantee caveat). |
| `D10` | `standard_library_contract` | `library/core/src/mem/manually_drop.rs:1-148` | `ManuallyDrop<T>` is a `#[repr(transparent)]` wrapper that suppresses automatic compiler drop glue for `T` while preserving `T`'s exact size, alignment, niche layout, and validity invariants (`ManuallyDrop<T>` still requires `T`'s validity invariants, unlike `MaybeUninit<T>`!). |
| `D11` | `standard_library_contract` | `library/core/src/mem/manually_drop.rs:150-235` | `ManuallyDrop::take` and `ManuallyDrop::drop`: `drop(&mut slot)` runs `ptr::drop_in_place` on the wrapped `T` in place; using or dropping the `ManuallyDrop<T>` again without reinitializing it is UB if `T`'s destructor invalidated the inner state. |
| `D12` | `normative_reference` | `src/types/union.md:54-119` | Union fields cannot have non-trivial drop glue unless wrapped in `ManuallyDrop<T>`; dropping a union does not automatically drop its active field unless the `union` itself implements `Drop`. |
| `D13` | `normative_reference` | `src/panic.md:1-98` | Panic profiles (`unwind` vs. `abort`): under `panic = "unwind"`, panicking unwinds the stack frame by frame, running destructors for all live initialized locals in reverse order; under `panic = "abort"`, the process terminates immediately without running stack destructors. |
| `D14` | `normative_reference`, `standard_library_contract` | `src/panic.md:65-98`, `library/core/src/panicking.rs:1-95` | Double panic during unwinding: if a destructor (`Drop::drop`) itself panics while the thread is already unwinding from an earlier panic, the runtime aborts the process (or invokes the no-unwind panic abort path). |
| `D15` | `standard_library_contract` | `library/alloc/src/boxed.rs:1120-1215` | Dropping `Box<T>` runs `drop_in_place::<T>(ptr)` first, and **then** deallocates the backing heap allocation even if `T::drop` unwinds (the allocation is freed on the cleanup path before resuming unwind). |
| `D16` | `standard_library_contract` | `library/core/src/pin.rs:1-245` | `Pin<P>` drop guarantee: once a value of a `!Unpin` type `T` has been pinned at a memory address, its memory must not be deallocated, overwritten, or reused until `drop_in_place::<T>` has run on that exact address. |
| `D17` | `normative_reference` | `src/expressions/operator-expr.md:540-610` | Evaluation order of call arguments and compound expressions: function and method arguments are evaluated left-to-right; if argument $k$ panics, arguments $0..k$ that have already been evaluated are dropped in reverse order ($k-1$ down to $0$) during unwinding. |
| `D18` | `normative_reference` | `src/expressions/struct-expr.md:1-125`, `src/expressions/array-expr.md:1-90` | Aggregate construction unwind order: in a struct or array literal, fields/elements are evaluated in source order; if an expression panics midway, the already-evaluated fields/elements are dropped in reverse evaluation order. |
| `D19` | `standard_library_contract` | `library/core/src/ptr/mod.rs:1460-1589` | `ptr::write(dst, src)` vs. `*dst = src`: `*dst = src` evaluates `src`, drops the old value at `*dst` (`D05`), and writes `src`; `ptr::write(dst, src)` overwrites `dst` without reading or dropping the prior contents of `*dst`. |
| `D20` | `standard_library_contract` | `library/core/src/mem/mod.rs:736-850` | `mem::replace(dest, src)` and `mem::swap(x, y)`: swap bytes in place without running destructors on either value, preserving provenance and initialization. |
| `D21` | `standard_library_contract` | `library/alloc/src/vec/mod.rs:1750-1845` | `Vec::set_len(new_len)` and partial-drop safety in collections: callers must ensure elements `0..new_len` are initialized before `Vec`'s destructor runs, as `Drop for Vec<T>` calls `drop_in_place::<[T]>` over `0..self.len`. |
| `D22` | `standard_library_contract` | `library/core/src/ptr/mod.rs:540-574` | `drop_in_place::<[T]>(slice_ptr)` drops slice elements sequentially from index `0` to `len - 1`; if element $i$'s destructor panics, elements $i+1..\text{len}$ are still dropped on the unwind path before unwinding continues. |
| `D23` | `exploratory_background` | `minirust@d821c6e:spec/lang/step/terminators.md:278-340` | MiniRust explicit unwind state machine: represents unwinding via `Terminator::StartUnwind`, `StopUnwind`, and `ResumeUnwind`, with per-frame `unwind_block` continuations on `Call`. |
| `D24` | `exploratory_background` | `minirust@d821c6e:spec/lang/well-formed.md:360-420` | MiniRust `ResumeUnwind` well-formedness gap: static `check_wf` verifies that `ResumeUnwind`'s target block exists in `func.blocks`, but whether a frame is currently in an active unwinding phase is a dynamic stack condition (`resume-unwind-source-audit`). |
| `D25` | `compiler_implementation` | `compiler/rustc_mir_transform/src/elaborate_drops.rs` | `rustc` drop elaboration pass: transforms `MirPhase::Built` conditional drop terminators into explicit stack boolean drop flags (`StorageLive`/`StorageDead`/`Assign`) and cleanup basic blocks in `MirPhase::Runtime(PostCleanup)`. |
| `D26` | `non_normative_note` | `src/destructors.md:275-295` | Exact drop-flag lowering is an internal compiler strategy; source-level specifications must characterize observable destructor execution and initialization state rather than requiring a specific synthetic MIR boolean local number. |

### 5. Atomics, Memory Orderings, and Concurrency (`C01`–`C21`)

Basis: documentation, source

| Clause | Authority | Pinned Source Location | Normative Content and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `C01` | `normative_reference`, `standard_library_contract` | `src/behavior-considered-undefined.md:24-30`, `library/core/src/sync/atomic.rs:1-95` | Rust adopts the C++20 atomic memory model (ISO/IEC 14882:2020 / N4868 `[intro.races]`, `[atomics]`): data races are undefined behavior. |
| `C02` | `normative_reference` | `src/behavior-considered-undefined.md:24-30` | A data race occurs when two or more threads concurrently access the same memory location, at least one access is a write, at least one access is non-atomic, and the accesses are not ordered by happens-before (`hb`). |
| `C03` | `standard_library_contract` | `library/core/src/sync/atomic.rs:97-185` | Atomic accesses are properties of the **access operation** (via `Atomic*` methods or `atomic_*` intrinsics), not merely the storage allocation; `AtomicUsize::from_ptr` allows atomic accesses to aligned, non-concurrently-non-atomically-accessed `*mut usize` storage. |
| `C04` | `standard_library_contract` | `library/core/src/sync/atomic.rs:187-265` | `Atomic*` types (`AtomicBool`, `AtomicI*`, `AtomicU*`, `AtomicPtr<T>`) have the same size, alignment (at least size), and bit validity as their underlying scalar type (`#[repr(C, align(N))]` over `UnsafeCell<T>`). |
| `C05` | `standard_library_contract` | `library/core/src/sync/atomic.rs:310-445` | The five `Ordering` variants (`Relaxed`, `Release`, `Acquire`, `AcqRel`, `SeqCst`) match C++20 `memory_order_*`: `Relaxed` provides per-location coherence without cross-location synchronization; `Release`/`Acquire` establish synchronizes-with (`sw`) when an acquire load reads from (`rf`) a release store (or release sequence). |
| `C06` | `standard_library_contract` | `library/core/src/sync/atomic.rs:447-520` | Forbidden orderings panic at runtime: `load` panics on `Release` or `AcqRel`; `store` panics on `Acquire` or `AcqRel`; `compare_exchange` failure ordering panics on `Release` or `AcqRel` (in Rust `1.99.1`, failure ordering may be stronger than success ordering provided it is `Relaxed`, `Acquire`, or `SeqCst`). |
| `C07` | `standard_library_contract` | `library/core/src/sync/atomic.rs:1250-1390` | Read-modify-write (`RMW`) operations (`swap`, `fetch_add`, `fetch_sub`, `fetch_and`, `fetch_or`, `fetch_xor`, `compare_exchange`, `compare_exchange_weak`) read the immediately preceding value in that atomic object's modification order (`mo`) atomically and participate in C++20 release sequences. |
| `C08` | `standard_library_contract` | `library/core/src/sync/atomic.rs:3420-3540` | `atomic::fence(order)` and `atomic::compiler_fence(order)`: `fence` establishes fence-to-atomic, atomic-to-fence, or fence-to-fence synchronization (`Release`, `Acquire`, `AcqRel`, `SeqCst`; panics on `Relaxed`); `compiler_fence` restricts only single-thread compiler instruction reordering without emitting hardware barriers or cross-thread `sw`. |
| `C09` | `standard_library_contract` | `library/core/src/sync/atomic.rs:1-95` (`N4868 [atomics.order]`) | Single-location coherence axioms (`coherence-RR`, `coherence-WW`, `coherence-RW`, `coherence-WR`): the modification order `mo` of each atomic location is a total order consistent with `hb`. |
| `C10` | `standard_library_contract` | `library/core/src/sync/atomic.rs:395-445` (`N4868 [atomics.order]`) | `SeqCst` total order (`psc` / `S`): there exists a single total order `S` over all `SeqCst` operations and `SeqCst` fences consistent with `hb` and `mo`, including C++20's strengthened fence-to-atomic conditions. |
| `C11` | `standard_library_contract` | `library/core/src/sync/atomic.rs:780-865` | `AtomicPtr<T>` provenance preservation: `AtomicPtr::load`, `store`, `swap`, and `compare_exchange*` preserve full pointer provenance (whereas casting pointers to `usize` and storing via `AtomicUsize` drops/exposes provenance per `S30`). |
| `C12` | `standard_library_contract` | `library/core/src/sync/atomic.rs:1490-1565` | `Atomic*::fetch_update` is a software loop over `load` and `compare_exchange_weak`, **not** a single hardware atomic RMW step; the closure may run multiple times if contending writes intervene. |
| `C13` | `standard_library_contract` | `library/core/src/marker.rs:640-725` | `Send` and `Sync` auto-trait soundness contracts: `T: Send` means transferring ownership of `T` to another thread is sound; `T: Sync` is equivalent to `&T: Send` (sharing immutable references across threads cannot cause data races or UB). |
| `C14` | `standard_library_contract` | `library/core/src/cell.rs:2120-2240` | `UnsafeCell<T>` is the **only** legal mechanism in Rust for interior mutability (`&T` mutation); `UnsafeCell<T>` disables `Sync` by default (`!Sync`) and wraps `T` in `#[repr(transparent)]` (or compiler-magic layout equivalent to `T`). |
| `C15` | `non_normative_note` | `library/core/src/sync/atomic.rs:45-95` | Mixed-size atomic accesses (accessing overlapping byte ranges with different atomic granularities simultaneously) are not supported by the C++20/Rust atomic model and result in UB. |
| `C16` | `exploratory_background` | `minirust@d821c6e:spec/mem/concurrent.md:1-165` | MiniRust `ConcurrentMemory`: wraps an inner `Memory` and records only `prev_atomic_accesses` from the *immediately preceding step* with binary `Atomicity::{Atomic, None}`, leaving C++20 `Ordering` (`Acquire`/`Release`/`Relaxed`) unimplemented in upstream MiniRust. |
| `C17` | `exploratory_background` | `minirust@d821c6e:spec/mem/concurrent.md:50-115` | MiniRust `ConcurrentMemory` race-window limitation: because `prev_atomic_accesses` is cleared on every step, unsynchronized non-atomic accesses separated by one unrelated thread step are missed by `ConcurrentMemory` (`atomic-message-passing-minirust-boundary`). |
| `C18` | `exploratory_background` | `minirust@d821c6e:spec/mem/tree_borrows/memory.md:1-190` | MiniRust `TreeBorrowsMemory` + `ConcurrentMemory` interaction: `TreeBorrowsMemory::retag` performs implicit pointee reads inside the inner memory without going through `ConcurrentMemory::load`, making retag reads invisible to MiniRust's outer race detector. |
| `C19` | `standard_library_contract` | `library/core/src/sync/atomic.rs:187-265` | Zero-sized types have no `Atomic*` wrapper; zero-byte non-atomic pointer operations access zero bytes (`[ptr, ptr)` is empty) and therefore do not byte-overlap with concurrent accesses. |
| `C20` | `standard_library_contract` | `library/core/src/hint.rs:210-265` | `core::hint::spin_loop()` is a processor hint with no memory-ordering or synchronization effect. |
| `C21` | `non_normative_note` | `library/core/src/sync/atomic.rs:45-95` | Out-of-thin-air (`OOTA`) values in `Relaxed` cycles remain a known theoretical corner of the C++20 `rf`/`hb` axiom set; formal models using `Relaxed` must explicitly state their acyclicity or causal-prefix assumptions. |

### 6. Exploratory Operational Models and Aliasing Extensions (`M01`–`M08`)

Basis: documentation, source

| Clause | Authority | Pinned Source Location | Normative Content and Explicit Boundary |
| :--- | :--- | :--- | :--- |
| `M01` | `exploratory_background` | `minirust@d821c6e:spec/mem/interface.md:1-215` | MiniRust `Memory` trait interface: decouples the typed `Machine` from untyped byte-level memory via `allocate`, `deallocate`, `load`, `store`, `dereferenceable`, `retag`, and `end_call` parameterized over `Provenance`. |
| `M02` | `exploratory_background` | `minirust@d821c6e:spec/mem/basic.md:1-265` | MiniRust `BasicMemory`: tracks `AllocId` provenance, allocation size, alignment, and liveness (`live: bool`), enforcing bounds, alignment, and live-allocation checks without per-tag aliasing permissions. |
| `M03` | `exploratory_background` | `minirust@d821c6e:spec/mem/tree_borrows/state_machine.md:1-95` | Tree Borrows per-byte permission state machine: four core states (`Reserved { ty_is_freeze, conflicted }`, `Active`, `Frozen`, `Disabled`) with distinct transition tables for `This` (child/self access) vs. `Foreign` (cousin/ancestor access). |
| `M04` | `exploratory_background` | `minirust@d821c6e:spec/mem/tree_borrows/state_machine_protected.md:1-190` | Tree Borrows function-call protectors: while a pointer tag's call frame is active (`protected == true`), transitions to `Disabled` (and certain foreign writes to `Reserved`) are forbidden (`UB`), preventing premature invalidation or deallocation during the call. |
| `M05` | `exploratory_background` | `minirust@d821c6e:spec/mem/tree_borrows/memory.md:155-210` | Tree Borrows `end_call(id)`: when a function call returns or unwinds, releases the frame's protector and performs an implicit read on all initialized locations covered by the protected tag. |
| `M06` | `exploratory_background` | `minirust@d821c6e:spec/lang/representation.md:1-763` | MiniRust `Relation` (`encode` / `decode`): maps `Type` and `Value` to `List<AbstractByte<Provenance>>` and back, parameterized by concrete offsets, sizes, alignments, `Chunks`, `Tagger`, and `Discriminator`. |
| `M07` | `exploratory_background` | `minirust@d821c6e:spec/mem/intptrcast.md:1-65` | MiniRust `IntPtrCast` (`expose` and `int2ptr` via `predict`): models integer-to-pointer provenance recovery using angelic prediction over previously exposed allocation IDs. |
| `M08` | `exploratory_background` | `minirust@d821c6e:spec/lang/well-formed.md:1-980` | MiniRust static well-formedness (`Prog::check_wf`, `Type::check_wf`, `Func::check_wf`): checks structural type/CFG constraints before execution, which (`Finding 7` below) do not suffice by themselves to guarantee representation round-trip coherence or dynamic call ABI compatibility. |

### 7. Static-vs-Dynamic Premise Stratification and the `minirust#288` Coherence Gap

Basis: source, derived

Auditing the boundary between static program well-formedness (`check_wf` / `rustc` type checking) and dynamic operational transitions across `rust-lang/rust@58cf8f9c` and `minirust@d821c6e` reveals a strict 5-layer stratification of premises:

1. **Category 1 — Structural Syntax and CFG Well-Formedness (`StaticSyntaxWF`):**
   - Local indices, basic-block indices, argument counts, entry-block presence, and instruction operand sort matching (`minirust@d821c6e:spec/lang/well-formed.md:450-980`).
   - Necessary to prevent interpreter/semantics "stuck" states (` specification failure`), but proves neither value validity nor memory safety.
2. **Category 2 — Target-Parameterized Type Geometry (`StaticGeometryWF`):**
   - Alignment is a positive power of two, size is a multiple of alignment (`S09`), and field offsets + field sizes fit within the aggregate size (`minirust@d821c6e:spec/lang/well-formed.md:1-285`).
3. **Category 3 — Representation Codec Coherence (`StaticCodecCoherence` — `minirust#288` Gap):**
   - In MiniRust (`spec/lang/representation.md:623-763`), the stated representation laws—round-trip (`decode(encode(v)) == Some(v)`) and provenance deflation (`encode(v) <= bytes` when `decode(bytes) == Some(v)`)—do **not** follow from `Type::check_wf` (`spec/lang/well-formed.md:155-284`) alone:
     - **Counterexample A (Incoherent `Enum` Tagger vs. Discriminator, `minirust#288`):** `Type::Enum` carries an encoding map `tagger: Map<Discriminant, List<(Offset, IntType, Int)>>` and a decoding decision tree `discriminator: Discriminator`. `Type::check_wf` checks that `tagger` writes in-bounds integers and `discriminator` branches in-bounds to valid variants, but **never checks that `discriminator` decodes the bytes written by `tagger` to the same discriminant**. Specifically, a 2-variant 1-byte enum `Two` (`variant 0`, `variant 1`) where `tagger` writes `0` for variant `0` and `1` for variant `1`, while `discriminator` is `Discriminator::Known(0)`, passes `Type::check_wf` (`spec/lang/well-formed.md:215-284`), yet `decode(encode(Variant(1))) == Some(Variant(0))`!
     - **Counterexample B (Truncated Wide-Pointer `Union` Chunks, `minirust#288`):** `Type::Union` (`spec/lang/well-formed.md:155-213`) checks only that `chunks` are sorted, disjoint, and within `size`, without requiring `chunks` to cover the fields or preserve wide-pointer metadata. A union containing a 16-byte wide pointer (`*const [u8]`) with `chunks = [(0, 8)]` passes `Type::check_wf`, but encoding and decoding truncates the upper 8 metadata bytes, causing `decode_ptr` (`spec/lang/representation.md:112-133`) to fail or corrupt metadata.
4. **Category 4 — Evaluated Constant and Instance-Selection Certificates (`ConstAndInstanceBinding`):**
   - Selecting a monomorphized function body or associated constant (`T::N`, `size_of::<T>()`, `align_of::<T>()`) requires binding the exact `(DefPath, GenericArgs, Target)` tuple and any const-evaluation postcondition (`ConstCert`). Neither structural CFG well-formedness nor codec coherence alone prevents dispatching a swapped coherent instance (e.g., normal vs. reversed enum codec).
5. **Category 5 — Dynamic Operational Preconditions (`DynamicSafetyPremises`):**
   - Even when Categories 1–4 hold, dynamic steps retain irreducible runtime obligations:
     - **Value Validity (`S19`, `M06`):** Loading a `bool` from a well-typed, well-sized 1-byte buffer containing `0x02` is dynamically admitted by the operational wrapper and steps to explicit `UB` (`spec/lang/representation.md:50-68, 590-618`).
     - **Dynamic Call ABI Compatibility (`spec/lang/step/terminators.md:201-276`):** In MiniRust, `Terminator::Call` checks `check_abi_compatibility(caller_fn_abi, callee_fn_abi)` and return-place size/alignment **dynamically at call time** because indirect calls through function pointers (`F02`) can target arbitrary `Func` definitions.
     - **Dynamic Unwind Phase (`spec/lang/step/terminators.md:315-340`):** `Terminator::ResumeUnwind` requires an active unwinding stack state; static `Func::check_wf` checks only that basic-block targets exist.
     - **Dynamic Allocation, Alignment, Bounds, and Aliasing (`S05`, `S06`, `M02`–`M05`):** Checked at each memory access (`load`, `store`, `dereferenceable`, `retag`, `end_call`, `deallocate`).

## Boundaries

- **Not examined:**
  - Floating-point NaN payload bit-pattern propagation across arithmetic operations and target-specific SIMD intrinsics (`core::arch::x86_64` / `aarch64`).
  - OS-level virtual-memory mapping (`mmap`/`mprotect`), signal handlers, and multi-process shared memory.
- **Unknown / unsettled in normative Rust `1.99.1`:**
  - The authoritative operational aliasing model for raw pointers derived from references (`S08`: Stacked Borrows vs. Tree Borrows vs. future UCG specification).
  - Exact runtime semantics of reading provenance-bearing pointer bytes through an integer load (`S20`: UB in `const`, provenance-stripping or target-dependent at runtime) and exact `int2ptr` exposed-provenance resolution (`S30`, `M07`).
  - Out-of-thin-air (`OOTA`) execution constraints for `Ordering::Relaxed` cycles (`C21`) and mixed-size atomic accesses (`C15`).
- **Known not to apply:**
  - `#[repr(Rust)]` field ordering or padding offsets (`S13`) and wide-pointer `(data, metadata)` field ordering (`S11`) do **not** apply across types or compiler versions.
  - MiniRust's executable `Type::check_wf` (`M08`) does **not** imply value-representation round-trip (`decode(encode(v)) == Some(v)`) without an explicit `CodecCoherence` premise (`Finding 7`, `minirust#288`).
- **Unsupported as a static guarantee:**
  - Assuming that destructors (`Drop::drop`) are guaranteed to run before memory reuse without `Pin<P>` (`D09`, `D16`), or assuming that `ManuallyDrop<T>` relaxes `T`'s validity invariants (`D10`: only `MaybeUninit<T>` relaxes validity/initialization, `S21`).

## Evidence

- [`support/sources.json`](support/sources.json) — 30 pinned primary-source entries across `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` with exact file paths, byte counts, git blob hashes, SHA-256 digests, and line ranges backing clauses `S01`–`S31`, `F01`–`F11`, `D01`–`D26`, `C01`–`C21`, and `M01`–`M08`.
- [`support/minirust-sources.json`](support/minirust-sources.json) — 28 pinned Markdown specification files from `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`) backing the static-versus-dynamic premise audit (`spec/lang/well-formed.md`, `spec/lang/representation.md`, `spec/lang/step/terminators.md`, `spec/mem/interface.md`, `spec/mem/basic.md`, `spec/mem/tree_borrows/*`, `spec/mem/concurrent.md`).
- [`support/revalidation-check.json`](support/revalidation-check.json) — Local re-verification ledger confirming all 30 Rust/Reference source entries and all 28 MiniRust specification files against the retained archive on `2026-10-24`.

## Revalidation

To re-verify the source manifests and archive digests from the repository root:

```sh
python3 - <<'PY'
import hashlib, json, pathlib, tarfile

pkg = pathlib.Path("reports/rust-1-99-1-opsem-normative-clauses-and-static-premises")
sources = json.loads((pkg / "support/sources.json").read_text())
mr_sources = json.loads((pkg / "support/minirust-sources.json").read_text())
archive_path = pathlib.Path(mr_sources["archive_path"])

assert len(sources["sources"]) == 30
assert hashlib.sha256(archive_path.read_bytes()).hexdigest() == mr_sources["archive_sha256"]

with tarfile.open(archive_path, "r:gz") as tf:
    members = {m.name.split("/", 1)[1]: m for m in tf.getmembers() if "/" in m.name and m.isfile()}
    for entry in mr_sources["files"]:
        data = tf.extractfile(members[entry["path"]]).read()
        assert len(data) == entry["bytes"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

print("Verified 30 Rust/Reference source records and 28 MiniRust archive files.")
PY
```
