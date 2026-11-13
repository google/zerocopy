# Allocation, Pointer Provenance, Stack Lifetimes, and Static Immutability Across Rust 1.99.1, MIR, MiniRust, and LLVM 23.1.1

## Summary

Achieving optimization parity with `rustc` + LLVM while preserving end-to-end
semantic soundness requires an operational memory model that justifies
heap-allocation elision, `calloc` fusion, strict and exposed pointer provenance,
`inbounds`/`nuw` pointer arithmetic, stack-slot lifetime reuse, and read-only
static/promoted memory at the **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`) and **LLVM 23.1.1**
(`rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) baseline:

1. **Heap allocation contract, allocator shim, and LLVM `allockind` /
   `alloc-family` optimizations:**
   - `alloc::alloc::alloc` (`library/alloc/src/alloc.rs:L67-L132`) documents
     four normative rules that separate `alloc::alloc::alloc` from calling
     `GlobalAlloc::alloc` directly: (a) the compiler may non-deterministically
     **elide** or **merge** heap allocations, (b) the returned allocation has
     *exactly* the requested `layout.size()` and `layout.align()` (even if the
     underlying OS allocator provides larger blocks), (c) the allocation may
     only be freed via `alloc::alloc::{dealloc, realloc}`, and (d) returned
     bytes are logically **uninitialized** (`de-initialized`) even if the
     custom `GlobalAlloc` zeroed them.
   - To prevent premature elision of custom allocator calls in stable code while
     still allowing `Box::new` elision after linking, `alloc::alloc::alloc`
     calls `__rust_no_alloc_shim_is_unstable_v2()` (`alloc.rs:L128`), which the
     synthetic allocator module (`compiler/rustc_codegen_llvm/src/allocator.rs:L89-L99`)
     defines as an empty `ret void` body.
   - In `compiler/rustc_codegen_llvm/src/attributes.rs:L568-L625`,
     `llfn_attrs_from_instance` annotates `__rust_alloc` with
     `noalias allockind("alloc,uninitialized,aligned") allocsize(0)
     "alloc-family"="__rust_alloc"
     "alloc-variant-zeroed"="...___rust_alloc_zeroed"` and parameter `1` with
     `allocalign`; annotates `__rust_alloc_zeroed` with
     `allockind("alloc,zeroed,aligned")`; annotates `__rust_realloc` with
     `allockind("realloc,aligned") allocsize(3)` + `allocptr` on arg `0` +
     `allocalign` on arg `2`; and annotates `__rust_dealloc` with
     `allockind("free") "alloc-family"="__rust_alloc"` and
     `allocptr captures(address)` on arg `0`.
   - Empirically (`support/s9_alloc_prov_lifetime_probe.rs`), at `-C opt-level=3`,
     LLVM 23.1.1's `InstCombine` completely removes matched
     `__rust_alloc` + `__rust_dealloc` pairs in `elide_box` and fuses
     `__rust_alloc(n, 8)` + `if !p.is_null() { write_bytes(p, 0, n) }` into a
     single tail call to **`__rust_alloc_zeroed(n, 8)`** in `alloc_then_zero`.
2. **Strict vs. exposed provenance, fine-grained `captures(...)`, and GEP
   flags (`inbounds`, `nuw`, `nusw`):**
   - **Strict provenance (`with_addr` / `map_addr`):** Implemented in `core::ptr`
     via `wrapping_byte_offset((addr as isize).wrapping_sub(self.addr() as isize))`.
     At `-O3`, `strict_with_addr` lowers to `ptrtoint`, integer bit-masking, and
     `getelementptr i8, ptr %p, i64 %delta`—preserving `%p`'s exact provenance
     without any `inttoptr` cast or exposure side effect.
   - **Exposed provenance (`expose_provenance` / `with_exposed_provenance`):**
     Lowers to `CastKind::PointerExposeProvenance` (`ptrtoint`) and
     `CastKind::PointerWithExposedProvenance` (`inttoptr`). In Miri
     (`compiler/rustc_const_eval/src/interpret/cast.rs:L287-L323`),
     `expose_provenance` marks the allocation ID exposed in the global
     provenance set, and `with_exposed_provenance` returns a pointer with
     `Provenance::Wildcard` (or fails under `-Zmiri-strict-provenance`).
   - **Fine-grained capture attributes in LLVM 23.1.1:** In place of legacy
     coarse `nocapture`, LLVM 23.1.1 uses `captures(none)`,
     `captures(address)`, `captures(address, read_provenance)`, and
     `captures(ret: address, provenance)`. Marked on `__rust_dealloc`
     (`attributes.rs:L619-L624`), `captures(address)` allows the allocator to
     inspect or store the integer address of a freed block while proving that
     its provenance cannot escape or be used after `dealloc` returns.
   - **`ptr_offset_from` / `ptr_offset_from_unsigned` and `isize::MAX` bound:**
     In Miri (`intrinsics.rs:L398-L525`) and MiniRust
     (`spec/lang/step/operators.md:L378-L454`), both pointers must point within
     the same live allocation (or both be provenance-free addresses), the byte
     range between them must lie within `[0..alloc.size]` with
     $|a - b| \le \texttt{isize::MAX}$, and `ptr_offset_from_unsigned` requires
     $a \ge b$. In LLVM 23.1.1, `offset_from` lowers to `sub i64 %a, %b`
     followed by `ashr exact` (signed) or `lshr exact` (unsigned).
3. **Stack lifetimes (`StorageLive` / `StorageDead`) vs. whole-alloca
   `llvm.lifetime.start.p0` / `llvm.lifetime.end.p0`:**
   - In `compiler/rustc_codegen_ssa/src/mir/place.rs:L316-L322` and
     `compiler/rustc_codegen_llvm/src/builder.rs:L1444-L1450`, `StorageLive` and
     `StorageDead` emit `@llvm.lifetime.start.p0(ptr nonnull %local)` and
     `@llvm.lifetime.end.p0(ptr nonnull %local)` for stack-allocated locals
     (`LocalRef::Place`). Notice that in LLVM 23.1.1, the legacy byte-size
     argument on `llvm.lifetime.start`/`end` has been removed: lifetime markers
     apply to the **entire `alloca`**, eliminating partial-alloca lifetime bugs
     in `StackColoring`.

## Applicability

These findings apply to **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`), **LLVM 23.1.1**
(`rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`),
**MiniRust** (`minirust/minirust` `063d784186d3252bee242217f218223205c0b568`),
the **Unsafe Code Guidelines** (`rust-lang/unsafe-code-guidelines`
`d809f91e62968913d808e53397fbcf7cea762cce`), and **Miri 0.1.0**
(`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`).

## Findings

### 1. Global Allocator Symbols, Shim Generation, and LLVM Attribute Contract

Basis: documentation (`library/alloc/src/alloc.rs:L12-L140`) + source
(`compiler/rustc_codegen_llvm/src/{allocator.rs:L19-L184, attributes.rs:L568-L625}`)
+ execution (`support/s9_alloc_prov_lifetime_probe.rs`)

Table 1 records the five internal allocator symbols declared in
`library/alloc/src/alloc.rs:L12-L44`, their rustc internal attributes, and the
exact LLVM 23.1.1 attributes emitted by `rustc 1.99.1`.

| Internal Symbol | Rustc Attributes (`library/alloc/src/alloc.rs`) | LLVM 23.1.1 Function & Parameter Attributes (`attributes.rs:L568-L625`) | Optimization Enabled in LLVM 23.1.1 |
| :--- | :--- | :--- | :--- |
| `__rust_alloc(size, align)` | `#[rustc_allocator]`, `#[rustc_nounwind]`, `#[rustc_allocator_zeroed_variant = "__rust_alloc_zeroed"]` | Return: `noalias`; Arg 1: `allocalign`; Fn: `nounwind allockind("alloc,uninitialized,aligned") allocsize(0) "alloc-family"="__rust_alloc" "alloc-variant-zeroed"="...___rust_alloc_zeroed"` | Dead allocation elimination; `alloc` + `memset(0)` $\rightarrow$ `__rust_alloc_zeroed` (`InstCombine`); heap-to-stack conversion. |
| `__rust_alloc_zeroed(size, align)` | `#[rustc_allocator_zeroed]`, `#[rustc_nounwind]` | Return: `noalias`; Arg 1: `allocalign`; Fn: `nounwind allockind("alloc,zeroed,aligned") allocsize(0) "alloc-family"="__rust_alloc"` | Known zero-initialized memory reads before first store; dead allocation elimination. |
| `__rust_dealloc(ptr, size, align)` | `#[rustc_deallocator]`, `#[rustc_nounwind]` | Arg 0: `allocptr captures(address)`; Fn: `nounwind allockind("free") "alloc-family"="__rust_alloc"` | Pairs with matching `alloc-family="__rust_alloc"` allocations for elision; `captures(address)` proves provenance does not escape. |
| `__rust_realloc(ptr, old_size, align, new_size)` | `#[rustc_reallocator]`, `#[rustc_nounwind]` | Return: `noalias`; Arg 0: `allocptr`; Arg 2: `allocalign`; Fn: `nounwind allockind("realloc,aligned") allocsize(3) "alloc-family"="__rust_alloc"` | Bounds analysis (`allocsize(3)`) and family matching. |
| `__rust_no_alloc_shim_is_unstable_v2()` | `#[rustc_nounwind]` | Fn: `nounwind`; defined as empty `ret void` in `allocator.rs:L89-L99` | Prevents downstream crates from linking without the rustc-generated allocator shim; inlined away during LTO / binary linking. |

---

### 2. Pointer Provenance, Integer-Pointer Casts, `offset_from`, and GEP Flags

Basis: source (`compiler/rustc_const_eval/src/interpret/{cast.rs:L287-L323, intrinsics.rs:L398-L525, operator.rs:L340-L370}`,
`compiler/rustc_codegen_llvm/src/builder.rs:L960-L995`) + execution
(`support/s9_alloc_prov_lifetime_probe.rs`)

1. **Provenance representation across Miri, MiniRust, and LLVM 23.1.1:**
   - **CTFE (`CtfeProvenance`):** Carries an explicit `AllocId` (plus immutable
     shared-ref tag). `PointerWithExposedProvenance` (`inttoptr`) is **rejected
     at compile time** for non-zero addresses because CTFE cannot guess which
     `AllocId` an integer address belongs to (`cast.rs:L321`).
   - **Miri (` src/tools/miri/src/machine.rs`):** Every pointer carries
     `Option<Provenance>` where `Provenance` is either `Concrete { alloc_id, tag }`
     or `Wildcard`. `CastKind::PointerExposeProvenance` (`ptr as usize` or
     `ptr.expose_provenance()`) inserts `alloc_id` into the machine's exposed
     set; `CastKind::PointerWithExposedProvenance` (`usize as *const T` or
     `with_exposed_provenance`) creates `Provenance::Wildcard`. By contrast,
     `CastKind::Transmute` from `*const T` to `usize` is **rejected as UB** if
     the pointer has provenance (because transmuting a pointer to an integer
     strips provenance without exposing it; `memory.rs` / `validity.rs`),
     whereas `ptr.addr()` uses `CastKind::Transmute` after `ptr_mask` or
     `ptrtoint` without exposing provenance.
   - **MiniRust (`spec/mem/basic.md`, `spec/lang/step/intrinsics.md:L31-L78`):**
     Models memory with parametric `Provenance`; `IntrinsicOp::PointerExposeProvenance`
     calls `mem.expose_provenance(prov)`, and
     `IntrinsicOp::PointerWithExposedProvenance` non-deterministically selects a
     previously exposed provenance (or `None`) via
     `mem.with_exposed_provenance(addr)`.
2. **GEP flags (`inbounds`, `nusw`, `nuw`) in `rustc 1.99.1` + LLVM 23.1.1:**
   - In `compiler/rustc_codegen_llvm/src/builder.rs:L960-L995`:
     - `inbounds_gep(ty, ptr, indices)` emits `getelementptr inbounds` (which in
       LLVM 23 implies `nusw`: signed byte offset addition does not overflow
       `isize` and stays within the allocated object's bounds `[0..size]`).
     - `inbounds_nuw_gep(ty, ptr, indices)` emits `getelementptr inbounds nuw`
       (both unsigned and signed non-wrapping addition within the allocated
       object).
     - `inbounds_ptradd(ptr, offset)` emits `getelementptr inbounds nuw i8, ptr, offset`.
   - `ProjectionElem::Field` (`place.rs:L186`) uses `inbounds_ptradd`.
   - `ProjectionElem::Index` (`place.rs:L291`) uses `inbounds_nuw_gep`.
   - `BinOp::Offset` (`rvalue.rs:L971-L976`) uses `inbounds_nuw_gep` when the
     count operand is `usize` (`ptr::add` / `byte_add`) and `inbounds_gep` when
     the count operand is `isize` (`ptr::offset` / `byte_offset`).
   - Wrapping pointer offsets (`wrapping_add` / `wrapping_offset` / `with_addr`)
     lower via `arith_offset` intrinsic to plain `getelementptr` (no `inbounds`,
     no `nuw`, no `nusw`).

---

### 3. Stack Objects (`StorageLive` / `StorageDead`) and Static / Promoted Memory

Basis: source (`compiler/rustc_codegen_ssa/src/mir/{analyze.rs,place.rs:L316-L322,statement.rs:L71-L85}`,
`compiler/rustc_const_eval/src/interpret/intern.rs`) + execution
(`support/s9_alloc_prov_lifetime_probe.rs`)

1. **When a MIR local becomes a stack `alloca` (`LocalRef::Place`) vs. SSA
   (`LocalRef::Operand`):**
   - Before codegen, `mir::analyze::non_ssa_locals`
     (`compiler/rustc_codegen_ssa/src/mir/analyze.rs:L25-L185`) classifies every
     MIR local. A local whose `BackendRepr` is `Scalar` or `ScalarPair` and
     whose address is never taken (`Rvalue::Ref` / `Rvalue::RawPtr`), never
     indexed dynamically (`ProjectionElem::Index`), and assigned cleanly is
     lowered directly to an SSA `LocalRef::Operand`, for which `StorageLive` and
     `StorageDead` are complete no-ops (`statement.rs:L71-L85`).
   - All other non-ZST locals are allocated via `alloca` in the function entry
     block (`LocalRef::Place`), and `StorageLive` / `StorageDead` emit
     `call void @llvm.lifetime.start.p0(ptr nonnull %local)` and
     `call void @llvm.lifetime.end.p0(ptr nonnull %local)`.
   - In `support/s9_alloc_prov_lifetime_probe.rs` (`disjoint_stack_lifetimes`),
     two `64`-byte arrays `a: [u64; 8]` and `b: [u64; 8]` in sequential blocks
     whose addresses escape into `black_box` are bracketed by disjoint
     `llvm.lifetime.start.p0` / `llvm.lifetime.end.p0` pairs, allowing LLVM's
     `StackColoring` pass to coalesce both `64`-byte arrays into a single
     `64`-byte stack frame region.
2. **Static memory, promoted constants, and `Freeze`:**
   - In `compiler/rustc_const_eval/src/interpret/intern.rs:L140-L320`, constant
     allocations (`ConstValue::Indirect` / `Slice`) and promoted rvalues
     (`promoted_mir`) are interned with `Mutability::Not` whenever the type is
     `Freeze` (`tcx.type_is_freeze_modulo_regions`), placing them in `.rodata`
     and attaching `constant` to the LLVM global variable. Writing through a raw
     pointer to any `Mutability::Not` allocation is immediate UB in Miri,
     MiniRust, and LLVM.

## Boundaries

- **Cross-allocation pointer comparison (`known subtlety`):** Comparing two
  pointers (`==`, `<`) in Rust lowers to integer address comparison (`icmp` on
  `ptr` in LLVM), which LLVM's folding rules may evaluate using either pointer
  provenance (treating distinct `noalias` / `alloca` objects as unequal) or
  concrete runtime addresses; see RFC 3514 / UCG issues on pointer comparison
  non-determinism when comparing one-past-the-end of one allocation with the
  start of an adjacent allocation.

## Evidence

- **Primary upstream sources:**
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`:
    - `library/alloc/src/alloc.rs:L12-L140`
    - `library/core/src/alloc/global.rs:L1-L417`
    - `compiler/rustc_codegen_llvm/src/{allocator.rs:L19-L184, attributes.rs:L568-L625, builder.rs:L960-L995, L1444-L1450}`
    - `compiler/rustc_codegen_ssa/src/mir/{analyze.rs:L25-L185, place.rs:L186-L322, statement.rs:L71-L115}`
    - `compiler/rustc_const_eval/src/interpret/{cast.rs:L287-L323, intrinsics.rs:L398-L525, intern.rs:L140-L320}`
  - `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`:
    `spec/mem/{basic.md,interface.md}`, `spec/lang/step/{intrinsics.md:L31-L78, operators.md:L378-L454, statements.md:L160-L185}`.
- **Preserved support artifacts:**
  - [`support/s9_alloc_prov_lifetime_probe.rs`](support/s9_alloc_prov_lifetime_probe.rs)

## Revalidation

To inspect the emitted LLVM 23.1.1 IR (`elide_box`, `alloc_then_zero`,
`strict_with_addr`, `exposed_roundtrip`, `offset_from_pair`,
`disjoint_stack_lifetimes`) and verify under Miri:

```bash
RUSTC_BOOTSTRAP=1 rustc +1.99.1-x86_64-unknown-linux-gnu --edition 2021 \
  -C opt-level=3 --emit=llvm-ir \
  reports/rust-allocation-provenance-and-stack-lifetime-semantics/support/s9_alloc_prov_lifetime_probe.rs \
  -o /tmp/s9_O3.ll
grep -E "define .*@(elide_box|alloc_then_zero|strict_with_addr|offset_from_pair)" -A 12 /tmp/s9_O3.ll
```
