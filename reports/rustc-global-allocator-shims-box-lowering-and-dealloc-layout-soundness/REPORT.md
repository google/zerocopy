# `rustc` global allocator symbols, `Box` construction and destruction, and exact deallocation layouts

## Summary

This report fixes, for two pinned `rust-lang/rust` revisions, how heap allocation reaches the
global allocator, what `Box::new` and the destruction of a `Box` compile to, and which layout a
deallocation carries. It combines source reading at both revisions, a probe that compiles and
runs specimens on the older one (including under Miri), and a kernel-checked Lean model.

What to retain:

1. **The allocator entry points are internal, version-mangled symbols.** `__rust_alloc`,
   `__rust_alloc_zeroed`, `__rust_realloc` and `__rust_dealloc` are
   `#[rustc_std_internal_symbol]` items. In an object file they are not called `__rust_alloc`
   but `_RNvCs<hash>_7___rustc12___rust_alloc`: a v0-mangled value in a pseudo-crate `__rustc`
   whose disambiguator hashes the compiler version. Their alignment parameter has the type
   `core::mem::Alignment`, not `usize`.
2. **Who defines them depends on `#[global_allocator]`.** With the attribute, its expansion
   defines the four functions in the user's crate and they call the `GlobalAlloc` methods of
   the annotated static. Without it, a compiler-synthesized allocator module defines them as
   tail calls to `__rdl_alloc` and friends in `std`. In both cases that module also defines the
   empty function `__rust_no_alloc_shim_is_unstable_v2`.
3. **`__rust_no_alloc_shim_is_unstable_v2` is a link-time marker and nothing else.** It is an
   empty function that `alloc::alloc::alloc` and `alloc_zeroed` call before the allocator, so
   that code cannot be linked without the compiler-generated module. It has no ordering or
   synchronization meaning. In optimized code the call stays behind even when LLVM removes the
   allocation it preceded.
4. **`Box::new` is ordinary library code.** It is `box_new_uninit(LAYOUT)`, then the intrinsic
   `write_via_move(ptr, x)`, then a transmute of the pointer to `Box<T>`. `write_via_move` is
   turned into the plain assignment `*ptr = x` (no drop of the destination) while MIR is built.
   Neither revision has `Rvalue::ShallowInitBox`, a nullary-operator rvalue, an
   `exchange_malloc` or `box_free` lang item, or a `#[rustc_box]` attribute.
5. **A `Box` is destroyed in two steps: the compiler drops the contents, then the library frees
   the block.** Drop elaboration expands the drop of a `Box<T>` out of which fields were moved
   into drops of exactly the remaining fields, followed by a call of `<Box<T> as Drop>::drop`,
   on the normal path and on the unwind path alike. That destructor only deallocates: it
   computes the layout with `Layout::for_value_raw` and skips the call when the size is zero.
6. **A `Box<MaybeUninit<T>>` that unwinds half-written frees its block and runs no destructor.**
   Fields written by hand before the panic are leaked (their destructors never run). That is a
   leak, not undefined behaviour. "Every field destroyed exactly once" holds for the field-wise
   cleanup of a `Box<T>`, not for `Box<MaybeUninit<T>>`.
7. **Zero-sized boxes and vectors never reach the allocator.** `Box::new(())`,
   `Box::new` of a zero-sized type with alignment 64, and `Vec::<()>::with_capacity(1_000_000)`
   followed by a million pushes produced zero allocator calls. The address of a zero-sized box
   is its alignment (1, 8, 64 observed); the capacity of the vector is `usize::MAX`.
8. **Every deallocation carried the layout of its allocation.** Across 21 scenarios at two
   optimization levels the recording allocator saw 26 deallocations per build, each with the
   same block, size and alignment as the matching allocation (or, after a `realloc`, the
   reallocated size). `GlobalAlloc::dealloc` requires exactly that; Miri reports
   `incorrect layout on deallocation` for a wrong size or a wrong alignment, and the
   deallocation of a zero-sized box's address as a dangling pointer.
9. **Allocation failure aborts; it does not unwind.** With `std` linked,
   `__rust_alloc_error_handler` is defined by `std` itself (`rust_oom`), prints
   `memory allocation of N bytes failed` and aborts with `SIGABRT`. Neither revision contains a
   `__rust_alloc_error_handler_should_panic_v2` symbol or an out-of-memory strategy option.
   `Vec::try_reserve_exact` returns `Err` instead.
10. **Counts of allocator calls are not a language guarantee.** The documentation of
    `GlobalAlloc` allows the compiler to remove allocations, and the newer revision's text also
    allows merging them. With the default allocator the probe's unpinned `Box` round trip
    compiles to no `__rust_alloc` call at `-C opt-level=3`.
11. **The Lean model proves the shape of items 5 to 8.** A flag policy for the drop ladder is
    free of undefined behaviour exactly when it never selects a field without a value, and
    leaves nothing undestroyed exactly when it selects every field with a value; the field-wise
    policy does both and frees the block once; a zero-sized box makes no allocator call; every
    deallocation event in a well-formed history has an allocation event with the same block and
    layout; and two counterexample families show the conditions are needed.

Differences between the two revisions that matter here: `box_new_uninit` is a plain `fn` that
relies on `Global.allocate` for the zero-sized case at the older revision and a `const fn` with
its own zero-size early return at the newer one; the pass that rewrites `*box` uses
`CastKind::Transmute` at the older revision and a dedicated `CastKind::BoxDerefTransmute` at the
newer one; and the `GlobalAlloc` documentation is considerably more explicit at the newer one.

## Applicability

**Subjects and how they relate.**

- `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (committed 2026-05-31; the
  compiler reports `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6). This is the
  revision whose source was read **and** whose toolchain was executed: every measurement in this
  report (symbols, LLVM IR, MIR dumps, run-time counts, Miri diagnostics, abort behaviour) comes
  from this toolchain. Below it is called **the older revision**.
- `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (committed 2026-11-11;
  `src/version` at that commit reads `1.102.0`). Only its source was read. Below it is called
  **the newer revision**. Statements about it are source statements; no binary built from it was
  run for this report.
- `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`: the Lean definitions
  `Trusted.MirAst` and `Trusted.MirSemantics` were read to record how that MIR semantics treats
  the constructs discussed here (Finding 17). Nothing from that repository is imported by the
  Lean file of this report.
- `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): the proof
  checker used for `support/AllocatorShimsAndBoxDropSoundness.lean`.

**Configuration of the executed observations.** Host and target `x86_64-unknown-linux-gnu`;
edition 2021; `-C panic=unwind`; `std` linked; executables (not dynamic libraries); the LLVM
backend; one codegen unit where object files are inspected; `-C opt-level=0` and
`-C opt-level=3` for the run-time counts. MIR was dumped with `-Zdump-mir`; one MIR configuration
additionally raises the MIR inliner's thresholds (`-Zinline-mir=yes
-Zinline-mir-threshold=10000 -Zinline-mir-hint-threshold=10000`) to make it inline `Box::new`.
Miri is the `miri` component of the same toolchain (`miri 0.1.0 (14210df0e2 2026-05-31)`), run
on single files with its default flags and the default allocator.

**What is shared by both revisions and what is not.** Every source statement in the Findings is
marked by which revision it was checked at; `support/source_audit.json` records, for each cited
file and each revision, the line numbers at which the quoted anchor text occurs. Where a finding
says "both revisions", the anchor text is present at both. Run-time behaviour is claimed for the
older revision only. Extending a measured behaviour to the newer revision is a *derived* step
that rests on the unchanged source anchors (for example the unchanged `Drop` implementation of
`Box` and the unchanged shim generator); it was not executed.

**What the Lean model is.** It is a hand-written abstract model of the allocator contract, of
`Global`'s zero-size rule, of `Box` construction and of the cleanup the compiler emits. It is not
extracted from compiler or library source, and no theorem in it is a statement about `rustc`
itself. Finding 16 lists which model definition stands for which source construct and how each
correspondence was checked.

**Scope limits.** Only the global allocator path (`Box<T>` with the default `Global` allocator
parameter, `Vec<T>` likewise) is covered; `Box<T, A>` with another allocator is not. Other
backends (Cranelift, GCC), other targets, dynamic linking of `std`, `no_std` binaries,
`-C panic=abort`, link-time optimization and incremental builds were not examined.

## Findings

Line numbers are those of the older revision unless a second number is given as
"older / newer". Evidence roles follow each finding as a `Basis:` line.

### 1. The allocator entry points

`library/alloc/src/alloc.rs` lines 12-44 (identical line numbers at both revisions) declare:

```rust
unsafe extern "Rust" {
    #[rustc_allocator]
    #[rustc_nounwind]
    #[rustc_std_internal_symbol]
    #[rustc_allocator_zeroed_variant = "__rust_alloc_zeroed"]
    fn __rust_alloc(size: usize, align: Alignment) -> *mut u8;
    #[rustc_deallocator]
    #[rustc_nounwind]
    #[rustc_std_internal_symbol]
    fn __rust_dealloc(ptr: NonNull<u8>, size: usize, align: Alignment);
    #[rustc_reallocator]
    #[rustc_nounwind]
    #[rustc_std_internal_symbol]
    fn __rust_realloc(ptr: NonNull<u8>, old_size: usize, align: Alignment, new_size: usize) -> *mut u8;
    #[rustc_allocator_zeroed]
    #[rustc_nounwind]
    #[rustc_std_internal_symbol]
    fn __rust_alloc_zeroed(size: usize, align: Alignment) -> *mut u8;

    #[rustc_nounwind]
    #[rustc_std_internal_symbol]
    fn __rust_no_alloc_shim_is_unstable_v2();
}
```

The public functions forward to them. `alloc(layout)` (lines 95-103) is the marker call followed
by `__rust_alloc(layout.size(), layout.alignment())`; `alloc_zeroed` (192-200) is the same with
`__rust_alloc_zeroed`; `dealloc(ptr, layout)` (120-129) is
`__rust_dealloc(ptr, layout.size(), layout.alignment())` with no marker call; `realloc` likewise
has none.

**Symbol names.** `#[rustc_std_internal_symbol]` items are mangled by
`rustc_symbol_mangling::v0::mangle_internal_symbol` (`compiler/rustc_symbol_mangling/src/v0.rs`
lines 87-133 / from line 144): the prefix `_R`, a value path `Nv` in a crate root `C` whose
disambiguator is a hash of the compiler's version string, the crate name `__rustc`, then the item
name. The reason is stated in `compiler/rustc_symbol_mangling/src/lib.rs` lines 179-200: such
symbols are imported "from another crate without a direct dependency", and mangling in the
version ensures that linking against a static library "compiled by a different rustc version"
gives neither "symbol conflicts or even UB due to a different implementation/ABI". Observed with
`nm` on the older revision:

| item | mangled symbol (`<crate-hash>` is the version disambiguator) |
| --- | --- |
| `__rust_alloc` | `_RNvCs<crate-hash>_7___rustc12___rust_alloc` |
| `__rust_alloc_zeroed` | `_RNvCs<crate-hash>_7___rustc19___rust_alloc_zeroed` |
| `__rust_realloc` | `_RNvCs<crate-hash>_7___rustc14___rust_realloc` |
| `__rust_dealloc` | `_RNvCs<crate-hash>_7___rustc14___rust_dealloc` |
| `__rust_no_alloc_shim_is_unstable_v2` | `_RNvCs<crate-hash>_7___rustc35___rust_no_alloc_shim_is_unstable_v2` |
| `__rust_alloc_error_handler` | `_RNvCs<crate-hash>_7___rustc26___rust_alloc_error_handler` |
| `__rdl_alloc` | `_RNvCs<crate-hash>_7___rustc11___rdl_alloc` |

The `_` between a length and a name (`12___rust_alloc`) is the v0 separator that is inserted
when an identifier starts with `_` or a digit; the identifier itself is `__rust_alloc` (12
bytes). A tool that searches a binary for the literal symbol `__rust_alloc` therefore finds it
only as a substring.

**LLVM-level contract.** In the LLVM IR of a crate that uses the default allocator
(`-C opt-level=3`), the declarations carry:

| symbol | return | parameters | function attributes |
| --- | --- | --- | --- |
| `__rust_alloc` | `noalias noundef ptr` | `i64 noundef`, `i64 allocalign noundef range(i64 1, -9223372036854775807)` | `nounwind`, `allockind("alloc,uninitialized,aligned")`, `allocsize(0)`, `"alloc-family"="__rust_alloc"`, `"alloc-variant-zeroed"=<the mangled __rust_alloc_zeroed>` |
| `__rust_realloc` | `noalias noundef ptr` | `ptr allocptr noundef nonnull`, `i64`, `i64 allocalign ...`, `i64` | `nounwind`, `allockind("realloc,aligned")`, `allocsize(3)`, same family |
| `__rust_dealloc` | `void` | `ptr allocptr noundef nonnull captures(address)`, `i64 noundef`, `i64 noundef range(...)` | `nounwind`, `allockind("free")`, same family |
| `__rust_no_alloc_shim_is_unstable_v2` | `void` | none | `nounwind` only; no allocator attribute |

The alignment range `[1, 2^63]` is the niche of `Alignment`. These attributes come from
`compiler/rustc_codegen_llvm/src/attributes.rs` (the `alloc-family` string at line 400 / 496;
`AllocKindFlags::Free` at line 551 / 652) and are what lets LLVM treat an
allocation/deallocation pair as removable (Finding 11).

Basis: source (both revisions) + execution (older revision: `nm`, LLVM IR).

### 2. Who defines the entry points

**The decision.** `compiler/rustc_metadata/src/creader.rs` (`inject_allocator_crate`, lines
1080-1177 at the older revision) sets the allocator kind to `AllocatorKind::Global` if this crate
or a dependency has a `#[global_allocator]` item, and to `AllocatorKind::Default` otherwise (in
which case some crate must carry `#![default_lib_allocator]`, as `library/std/src/lib.rs` does at
line 436 / 443; two global allocators, or no provider at all, are compile errors). The allocation error handler kind
is computed the same way from `#[alloc_error_handler]`.

**With `#[global_allocator]`.** The attribute is a built-in macro
(`compiler/rustc_builtin_macros/src/global_allocator.rs`). For each entry of the table
`ALLOCATOR_METHODS` (`compiler/rustc_ast/src/expand/allocator.rs` line 60: `alloc`, `dealloc`,
`realloc`, `alloc_zeroed`) it generates a function named by `global_fn_name`
(`format!("__rust_{base}")`, line 13), marked `#[rustc_std_internal_symbol]` (line 119 / 114) and
with the matching one of `#[rustc_allocator]`, `#[rustc_deallocator]`, `#[rustc_reallocator]`,
`#[rustc_allocator_zeroed]` (lines 111-117). The probe captured the expansion of

```rust
#[global_allocator]
static GLOBAL: Forward = Forward;
```

with `-Zunpretty=expanded` (`support/probe_output/global_allocator_expansion.txt`):

```rust
static GLOBAL: Forward = Forward;
const _: () =
    {
        #[rustc_std_internal_symbol]
        #[rustc_allocator]
        unsafe fn __rust_alloc(size: usize, align: ::core::mem::Alignment)
            -> *mut u8 {
            ::core::alloc::GlobalAlloc::alloc(&GLOBAL,
                ::core::alloc::Layout::from_size_alignment_unchecked(size,
                    align))
        }
        #[rustc_std_internal_symbol]
        #[rustc_deallocator]
        unsafe fn __rust_dealloc(ptr: *mut u8, size: usize,
            align: ::core::mem::Alignment) -> () {
            ::core::alloc::GlobalAlloc::dealloc(&GLOBAL, ptr,
                ::core::alloc::Layout::from_size_alignment_unchecked(size,
                    align))
        }
        // __rust_realloc and __rust_alloc_zeroed follow the same pattern
    };
```

So the `(size, align)` pair that the library passes to `__rust_dealloc` is turned back into a
`Layout` without any check and handed to `GlobalAlloc::dealloc`: a wrong pair is not detected at
this boundary.

**Without `#[global_allocator]`.** `allocator_shim_contents`
(`compiler/rustc_codegen_ssa/src/base.rs` lines 670-689 / from 692) returns the four methods only
`if kind == AllocatorKind::Default`, and the error handler only if the error-handler kind is
`Default`. The LLVM backend (`compiler/rustc_codegen_llvm/src/allocator.rs` lines 33-87) then
emits, in a separate module, one wrapper per method named `__rust_<method>` that tail-calls
`__rdl_<method>` (`default_fn_name`, `format!("__rdl_{base}")`) with hidden visibility. The
`__rdl_` functions live in `library/std/src/alloc.rs` (`__rdl_alloc` at line 450 / 474) and call
the `System` allocator.

**In both cases** the same module defines the marker function (Finding 3); that part of
`codegen` is unconditional (lines 89-99 / 90-100).

**When the module exists at all.** `allocator_kind_for_codegen` (lines 640-655) returns `None`,
so no module is generated, when every crate type being produced links some dependency
dynamically, because a dynamic library "already got an allocator shim". This case was not
executed.

**Observed** (`nm` on the saved codegen objects of two executables, older revision,
`-C opt-level=3 -C codegen-units=1 -C save-temps`; `T`/`t` = defined, `U` = undefined):

| object | default allocator | `#[global_allocator]` in the crate |
| --- | --- | --- |
| allocator module | defines `__rust_alloc`, `__rust_alloc_zeroed`, `__rust_dealloc`, `__rust_realloc`, `__rust_no_alloc_shim_is_unstable_v2`; undefined `__rdl_alloc`, `__rdl_alloc_zeroed`, `__rdl_dealloc`, `__rdl_realloc` | defines only `__rust_no_alloc_shim_is_unstable_v2`; nothing undefined |
| crate object | undefined `__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_no_alloc_shim_is_unstable_v2` | defines `__rust_alloc`, `__rust_alloc_zeroed`, `__rust_dealloc`, `__rust_realloc`; undefined `__rust_no_alloc_shim_is_unstable_v2` |
| linked executable | all of the above defined, plus `__rust_alloc_error_handler` and the four `__rdl_` functions | the four `__rust_` functions, the marker and `__rust_alloc_error_handler` defined; no `__rdl_` symbol referenced by the crate or the module |

No symbol named `__rg_alloc`, `__rg_dealloc`, `__rg_oom` or `__rdl_oom` exists in any of these
objects. Comments that still mention `__rg_alloc` and `__rg_oom`
(`compiler/rustc_monomorphize/src/partitioning.rs`, `library/alloc/src/alloc.rs`) describe an
earlier scheme.

Basis: source (both revisions) + execution (older revision).

### 3. `__rust_no_alloc_shim_is_unstable_v2`

- **Definition.** The compiler emits it with an empty body: `create_wrapper_function` is called
  with no target and ends in `bx.ret_void()` (`compiler/rustc_codegen_llvm/src/allocator.rs`
  lines 89-99 and 180-183). Its name is the constant `NO_ALLOC_SHIM_IS_UNSTABLE` in
  `compiler/rustc_ast/src/expand/allocator.rs` line 21.
- **Use.** `alloc` and `alloc_zeroed` call it (lines 99 and 196 / 156 and 321), with the comment
  "Make sure we don't accidentally allow omitting the allocator shim in stable code until it is
  actually stabilized." `dealloc` and `realloc` do not call it. Miri treats it as "a no-op shim
  that only exists to prevent making the allocator shims instantly stable"
  (`src/tools/miri/src/shims/foreign_items.rs` line 309 / 319).
- **Consequence (derived).** Its one effect is a link-time dependency: any crate that allocates
  references a symbol that only the compiler-generated allocator module defines, so a program
  that provides `__rust_alloc` and friends by other means still does not link without that
  module. It takes no argument, returns nothing and touches no state, so it orders nothing.
- **Observed.** In the default-allocator executable the function
  `unpinned_roundtrip` (a `Box::new([seed; 8])` that is summed and dropped, with nothing forcing
  the allocation) compiles at `-C opt-level=3` to a body whose only call is
  `__rust_no_alloc_shim_is_unstable_v2`: the `__rust_alloc`/`__rust_dealloc` pair is gone and
  the marker call is still there, because LLVM knows nothing that would let it delete an opaque
  external call. The number of marker calls executed is therefore not the number of allocations
  performed.
- **Absent variants.** No symbol without the `_v2` suffix exists in the inspected objects.

Basis: source (both revisions) + execution (older revision) + derived.

### 4. Allocation failure

- `box_new_uninit` turns a failed allocation into `handle_alloc_error(layout)`
  (`library/alloc/src/boxed.rs` line 250 / 328). `handle_alloc_error`
  (`library/alloc/src/alloc.rs` lines 543-562) calls
  `__rust_alloc_error_handler(layout.size(), layout.align())`, declared at line 510 / 636 as
  `fn __rust_alloc_error_handler(size: usize, align: usize) -> !` (here the alignment is a
  plain `usize`).
- With `std` linked that symbol is defined by `std` through `#[alloc_error_handler]` on
  `pub fn rust_oom(layout: Layout) -> !` (`library/std/src/alloc.rs` lines 421-431 / 441-451):
  it runs the allocation error hook and then `crate::process::abort()`. The default hook prints
  `memory allocation of {} bytes failed` (line 379 / 399). The attribute is another built-in
  macro that generates
  `unsafe fn __rust_alloc_error_handler(size: usize, align: usize) -> ! { handler(Layout::from_size_align_unchecked(size, align)) }`
  (`compiler/rustc_builtin_macros/src/alloc_error_handler.rs`). This is why, in Finding 2, the
  symbol is defined in the executable but not in the allocator module.
- Without any `#[alloc_error_handler]` the allocator module forwards the symbol to
  `__rdl_alloc_error_handler` (`library/alloc/src/alloc.rs` line 572 / 698), which calls
  `core::panicking::panic_nounwind_fmt`. Not executed here.
- **No panic-on-failure switch.** The strings `should_panic_v2`,
  `alloc_error_handler_should_panic` and `OomStrategy` occur in no file of `compiler/`,
  `library/alloc`, `library/core/src`, `library/std/src/alloc.rs` or `src/tools/miri/src` at
  either revision, and no such symbol exists in the inspected objects.
- **Observed** (`support/specimens/oom_abort.rs`: a global allocator that returns null for any
  request of at least 2^40 bytes):

| operation | result |
| --- | --- |
| `Box::<[u8; 1 << 41]>::new_uninit()` | `memory allocation of 2199023255552 bytes failed` on standard error, then `SIGABRT` |
| `Vec::<u8>::with_capacity(1 << 41)` | the same message, then `SIGABRT` |
| `Vec::<u8>::try_reserve_exact(1 << 41)` | returns `Err`; the allocator was asked once; exit status 0 |
| `std::alloc::alloc` with a 2^41-byte layout | returns null; exit status 0 |
| `Vec::<u8>::with_capacity(usize::MAX)` | panic `capacity overflow` (exit status 101) |

  In the accounting specimen, `try_reserve_exact(usize::MAX / 2 + 1)` returned `Err` and the
  recorder saw no call for it: a request above `isize::MAX` is rejected before the allocator.

Basis: source (both revisions) + execution (older revision).

### 5. `Global`, zero-sized requests, and the `Layout` invariant

- `Global`'s allocation (`library/alloc/src/alloc.rs` lines 205-215 / from 330) is

  ```rust
  match layout.size() {
      0 => Ok(layout.dangling_ptr().cast_slice(0)),
      size => unsafe {
          let raw_ptr = if zeroed { alloc_zeroed(layout) } else { alloc(layout) };
          let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
          Ok(ptr.cast_slice(size))
      },
  }
  ```

  and its deallocation (lines 219-231) is `if layout.size() != 0 { dealloc_nonnull(ptr, layout) }`.
- `Layout::dangling_ptr` (`library/core/src/alloc/layout.rs` lines 270-272 / 276-278) is
  `NonNull::without_provenance(self.align.as_nonzero_usize())`: the address is the alignment,
  and the pointer has no provenance.
- A `Layout` stores `size: usize` and `align: Alignment` (lines 28-42); the alignment is a power
  of two by its type, and the size bound is `size <= isize::MAX + 1 - align`
  (`max_size_for_alignment`, lines 79-98, which notes that this is equivalent to the size
  rounded up to the alignment not overflowing `isize`).
- The contract these rules protect is that of `GlobalAlloc`
  (`library/core/src/alloc/global.rs`): for `alloc`, "`layout` must have non-zero size.
  Attempting to allocate for a zero-sized `layout` will result in undefined behavior" (line
  152 / 197); for `dealloc`, "`ptr` is a block of memory currently allocated via this allocator
  and, `layout` is the same layout that was used to allocate that block of memory" (lines
  186-189 / 231-234); and "It's undefined behavior if global allocators unwind" (line 90 / 158).
- `RawVec` never allocates for a zero-sized element type and reports the capacity as
  `usize::MAX` (`library/alloc/src/raw_vec/mod.rs` line 619:
  `if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }`).

**Observed** (older revision, both optimization levels, recording allocator):

| scenario | allocator calls | observed value |
| --- | --- | --- |
| `Box::new(())`, then drop | 0 | address 1 |
| `Box::new(Zst64)` (`#[repr(align(64))]`, size 0), `Box::new([0u64; 0])`, `Box<dyn Trait>` of `Zst64`, then drop | 0 | addresses 64, 8, 64 |
| `Vec::<()>::with_capacity(1_000_000)`, 1,000,000 pushes, `shrink_to_fit`, drop | 0 | capacity `usize::MAX`, length 1,000,000, pointer address 1 |

Over the whole run the recorder counted zero calls with size 0, zero with an alignment that is
not a power of two, and zero whose size exceeds `isize::MAX + 1 - align`. The optimized IR of a
function returning the address of `Box::new(())` contains no allocator call and the store
`inttoptr (i64 1 to ptr)`.

Basis: normative (the `GlobalAlloc` documentation) + source (both revisions) + execution (older
revision).

### 6. `Box::new`

Older revision, `library/alloc/src/boxed.rs` lines 239-252 and 284-292:

```rust
#[inline]
#[rustc_no_mir_inline]
#[cfg(not(no_global_oom_handling))]
fn box_new_uninit(layout: Layout) -> *mut u8 {
    match Global.allocate(layout) {
        Ok(ptr) => ptr.as_mut_ptr(),
        Err(_) => handle_alloc_error(layout),
    }
}

pub fn new(x: T) -> Self {
    // This is `Box::new_uninit` but inlined to avoid build time regressions.
    let ptr = box_new_uninit(<T as SizedTypeProperties>::LAYOUT) as *mut T;
    // Nothing below can panic so we do not have to worry about deallocating `ptr`.
    // SAFETY: we just allocated the box to store `x`.
    unsafe { core::intrinsics::write_via_move(ptr, x) };
    // SAFETY: we just initialized `b`.
    unsafe { mem::transmute(ptr) }
}
```

`Box::new_uninit` (line 317 / 402) is
`unsafe { mem::transmute(box_new_uninit(<T as SizedTypeProperties>::LAYOUT)) }`. At the newer
revision `box_new_uninit` is `const fn` and begins with
`if layout.size() == 0 { return layout.dangling_ptr().as_ptr(); }` (lines 322-330); `Box::new` is
unchanged (lines 368-376).

**`write_via_move`.** It is declared as an intrinsic,
`pub const unsafe fn write_via_move<T>(ptr: *mut T, value: T);`
(`library/core/src/intrinsics/mod.rs` line 2217 / 2298), and it never survives as a call: MIR
building recognizes it (`compiler/rustc_mir_build/src/builder/expr/into.rs` from line 397 / 407)
with the comment "`write_via_move(ptr, val)` becomes `*ptr = val` but without any dropping",
and the later intrinsic-lowering pass notes "`write_via_move` is already lowered during MIR
building" (`compiler/rustc_mir_transform/src/lower_intrinsics.rs` line 183 / 206).

**Observed MIR** (older revision; `Pair` is two fields with destructors, size 16, alignment 8):

- A local function that calls the intrinsic directly has, in its *built* MIR, the statement
  `(*_3) = move _2;` and no call (`support/probe_output/mir/opt_level_0/write_via_move_direct.built.mir`).
- `fn box_new_sized(p: Pair) -> Box<Pair> { Box::new(p) }` is, in built MIR,
  `_0 = Box::<Pair>::new(move _2) -> [return: bb1, unwind: bb3];`, an ordinary call whose unwind
  edge drops the argument. It is still that call in the final MIR at `-C opt-level=0` and at
  `-C opt-level=3`: with default thresholds the MIR inliner does not inline `Box::new` here.
- With the MIR inliner's thresholds raised, the final MIR shows the library body in place
  (`support/probe_output/mir/opt_level_3_forced_mir_inline/box_new_sized.final.mir`; storage
  markers omitted here):

  ```text
  bb0: {
      _2 = move _1;
      _4 = boxed::box_new_uninit(const Layout {{ size: 16_usize, align: std::mem::Alignment {{ _inner_repr_trick: mem::alignment::AlignmentEnum::_Align1Shl3 }} }}) -> [return: bb1, unwind: bb3];
  }
  bb1: {
      _3 = copy _4 as *mut Pair (PtrToPtr);
      (*_3) = move _2;
      _0 = copy _4 as std::boxed::Box<Pair> (Transmute);
      return;
  }
  ```

  The block that stores the value also holds the transmute and ends in `return`; it has no
  unwind edge, which is the MIR form of "nothing below can panic". `box_new_uninit` itself stays
  a call (`#[rustc_no_mir_inline]`). For `Box::new(())` the same configuration shows
  `box_new_uninit(const Layout {{ size: 0_usize, ... _Align1Shl0 }})` followed directly by the
  transmute, with no store: at the older revision the zero-size case is decided at run time
  inside `Global.allocate`, not in MIR.
- **Evaluation order.** The argument is evaluated before the allocation: in the scenario where
  constructing the argument panics, the recorder saw no allocation with the measured layout.
- **Names from earlier compilers.** None of `ShallowInitBox`, `exchange_malloc`, `box_free`,
  `NullaryOp`, `SizeOf(` occurs in any of the MIR dumps the probe produced (three
  configurations, ten functions). In source, `ShallowInitBox`, `ExchangeMalloc`, `BoxFree` and
  `NullaryOp` occur nowhere under `compiler/` at either revision; `Rvalue` has thirteen variants
  at both (`Use`, `Repeat`, `Ref`, `ThreadLocalRef`, `RawPtr`, `Cast`, `BinaryOp`, `UnaryOp`,
  `Discriminant`, `Aggregate`, `CopyForDeref`, `WrapUnsafeBinder`, `Reborrow`).

Basis: source (both revisions) + execution (older revision).

### 7. The `vec!` literal

`vec![a, b, c]` is (`library/alloc/src/macros.rs` lines 50-60)

```rust
$crate::boxed::box_assume_init_into_vec_unsafe(
    $crate::intrinsics::write_box_via_move($crate::boxed::Box::new_uninit(), [$($x),+])
)
```

`write_box_via_move<T>(b: Box<MaybeUninit<T>>, x: T) -> Box<MaybeUninit<T>>`
(`library/alloc/src/intrinsics.rs` line 15) is a second intrinsic lowered while MIR is built
(`into.rs` from line 425 / 437): the value is stored directly into the box's contents through the
field path `MaybeUninit` -> `ManuallyDrop` -> `MaybeDangling` -> `T`, and the box is then moved
to the destination. The source comment explains that the store has to go through the box (and
not through a raw pointer) so that the borrow checker still sees that the value must outlive the
box. `box_assume_init_into_vec_unsafe` (line 262 / 341; `const fn` at the newer revision) is
`(b.assume_init() as Box<[T]>).into_vec()`.

Observed: the built MIR of `vec![a, b]` calls `Box::<[Counted; 2]>::new_uninit()`, stores the
array through the box, and calls `box_assume_init_into_vec_unsafe`; no call named
`write_box_via_move` remains. At run time a three-element literal of a 64-byte, 64-aligned type
made one allocation of `(192, 64)`, had capacity 3, and its drop ran three destructors and made
one deallocation of `(192, 64)`.

Basis: source (both revisions) + execution (older revision).

### 8. Destroying a `Box`: drop elaboration plus `<Box<T> as Drop>::drop`

**The library half** (`library/alloc/src/boxed.rs` lines 1947-1962 / from 2125):

```rust
unsafe impl<#[may_dangle] T: ?Sized, A: Allocator> Drop for Box<T, A> {
    fn drop(&mut self) {
        // the T in the Box is dropped by the compiler before the destructor is run
        let ptr = self.0;
        unsafe {
            let layout = Layout::for_value_raw(ptr.as_ptr());
            if layout.size() != 0 {
                self.1.deallocate(From::from(ptr.cast()), layout);
            }
        }
    }
}
```

The layout handed to the allocator is recomputed from the pointee: from the type for a sized
`T`, from the pointer metadata for a slice or a trait object.

**The compiler half.** In `compiler/rustc_mir_transform/src/elaborate_drop.rs`,
`open_drop_for_adt` (line 774 / 1013) special-cases `Box`: "we need to drop the inside of
the box before running the destructor" (line 802 / 1037). `open_drop_for_box_contents` (line
737 / 976) reads the raw pointer out of the box, drops the interior through the *deref subpath*
of the box's move path (`self.elaborator.deref_subpath(self.path)`, line 759 / 998; the trait
documents at line 126 / 125 that this subpath "is only relevant for `Box<T>`, where the contained
`T` can be moved out of the box"), and continues to `destructor_call_block_sync` (line 966 / 1209), which emits a call of `Drop::drop` on `&mut` the box. The pass order is `ElaborateDrops` and later
`ElaborateBoxDerefs` (`compiler/rustc_mir_transform/src/lib.rs` lines 634 and 645 / 663 and 674).
There is no deallocation function that the compiler calls by name.

**Observed MIR after `ElaborateDrops`** (older revision), for

```rust
pub fn box_partial_move(b: Box<Pair>, should_panic: bool) -> Counted {
    let first = b.first;
    maybe_panic(should_panic);
    first
}
```

- before the pass: two terminators `drop(_1)` of the whole box (one on the normal path, one in
  cleanup);
- after the pass: no `drop(_1)`; no drop of `((*_n).0: Counted)` anywhere; three drops of
  `((*_n).1: Counted)` (one on the normal path, two in cleanup blocks); three calls of
  `<Box<Pair> as Drop>::drop` (one normal, two cleanup); the pointer is obtained twice by
  `_n = copy ((_1.0: std::ptr::Unique<Pair>).0: std::ptr::NonNull<Pair>) as *const Pair (Transmute)`;
  no drop flag is needed because the move is unconditional.
- The normal-path field drop is `drop(((*_10).1: Counted)) -> [return: bb11, unwind: bb9]` where
  `bb9` is a cleanup block that calls `<Box<Pair> as Drop>::drop`: if the remaining field's
  destructor unwinds, the block is still freed.
- With a conditional move (`if take { Some(b.first) } else { None }`), the pass introduces a
  boolean local that is set to `true` at entry and to `false` where the field is moved out, and
  each drop of field 0 is guarded by `switchInt(copy _8)`; field 1 is dropped unconditionally.
- `*b` moved out whole (`fn(b: Box<Pair>) -> Pair { *b }`): `_0 = move (*_1);`, no drop of the
  contents, and `<Box<Pair> as Drop>::drop` is still called.

**Observed at run time** (older revision; identical at `-C opt-level=0` and `-C opt-level=3`;
the measured pointee is two 64-byte, 64-aligned fields, so its layout is `(128, 64)`; "runs" are
destructor runs per field, counted by the destructors themselves):

| scenario | allocations `(128, 64)` | deallocations `(128, 64)` | destructor runs |
| --- | --- | --- | --- |
| `Box::new(pair)`, drop | 1 | 1 | each field once |
| move `b.first` out, `mem::forget` it, panic | 1 | 1 | second field once, first field never |
| move `b.first` out, panic (the local is dropped by unwinding) | 1 | 1 | each field once |
| move `b.first` out, no panic | 1 | 1 | each field once |
| move both fields out, panic | 1 | 1 | each field once (by the locals) |
| `let p = *b;` then drop `p` | 1 | 1 | each field once |
| `Box::into_raw` then `Box::from_raw` at the same type, drop | 1 | 1 | each field once |
| `Box::leak` | 1 | 0 | none |
| the argument of `Box::new` panics | 0 | 0 | none |

A panic that is caught adds two allocations and two deallocations made by the panic runtime to
the window, with layouts `(16, 8)` and `(56, 8)` (plausibly the boxed payload and the unwinder's
exception object; which is which was not checked). They are why the measured type has alignment
64: its layouts cannot be confused with theirs.

Basis: source (both revisions) + execution (older revision).

### 9. A half-written `Box<MaybeUninit<T>>` during unwinding

For

```rust
let mut b: Box<MaybeUninit<Pair>> = Box::new_uninit();
unsafe { addr_of_mut!((*b.as_mut_ptr()).first).write(Counted { tag: 1 }) };
maybe_panic(should_panic);
unsafe { addr_of_mut!((*b.as_mut_ptr()).second).write(Counted { tag: 2 }) };
unsafe { b.assume_init() }
```

the MIR after `ElaborateDrops` has exactly one drop in cleanup, `drop(_2)` of the local of type
`Box<MaybeUninit<Pair>>`, guarded by a drop flag that is cleared where the box is moved into
`assume_init`; there is no field drop at all. `MaybeUninit<Pair>` has no drop glue, so dropping
this box is only the library destructor of Finding 8.

At run time: one allocation and one deallocation of `(128, 64)` and **zero** destructor runs when
the panic occurs between the two writes; one allocation, one deallocation and one run per field
when it does not. Dropping a `Box::<Pair>::new_uninit()` untouched is one allocation and one
deallocation.

Miri (older revision) confirms both sides: the half-written box of a type that owns nothing
unwinds without any report, and the half-written box whose written field is a `Box<u64>` ends
with `error: memory leaked: alloc298 (Rust heap, size: 8, align: 8)` and no report of undefined
behaviour. The block of the outer box is freed; what the written field owned is not.

Basis: execution (older revision) + source (both revisions, Finding 8).

### 10. Every deallocation carries the layout of its allocation

**Normative.** `GlobalAlloc::dealloc` requires that "`layout` is the same layout that was used to
allocate that block of memory"; `realloc` returns a block whose "new layout must be used when
deallocating the new memory block" (`library/core/src/alloc/global.rs`).

**Observed.** The recording allocator keeps a table of live blocks with the size and alignment
of their allocation and compares every `dealloc` against it. Per build (two builds: optimization
levels 0 and 3) the 21 scenarios produced 27 successful allocations, 1 reallocation, 1 refused
request and 26 deallocations (the difference of one is `Box::leak`); the counters for a
deallocation with a different layout, for a deallocation of an unknown address, and for a
malformed request were all zero. Beyond the sized cases of Finding 8:

| scenario | events seen by the allocator |
| --- | --- |
| `Box<[Counted]>` of length 3, drop | `alloc(192, 64)`, `dealloc(192, 64)`: the layout comes from the slice length |
| `Box<dyn Describe>` holding a `Pair`, drop | `alloc(128, 64)`, `dealloc(128, 64)`: the layout comes from the vtable |
| `Vec<Counted>` growing by five pushes, drop | `alloc(256, 64)`, `realloc(256, 64 -> 512)`, `dealloc(512, 64)` |

**What a checker reports.** Miri's `__rust_dealloc` shim passes the size and alignment to the
interpreter's `deallocate_ptr`, which fails with "incorrect layout on deallocation: {alloc_id}
has size {size} and alignment {align}, but gave size {size_found} and alignment {align_found}"
(`compiler/rustc_const_eval/src/interpret/memory.rs` line 426, both revisions); its
`__rust_alloc` shim rejects size zero with "creating allocation with size 0"
(`src/tools/miri/src/shims/alloc.rs` line 92, both revisions). Observed diagnostics (older
revision; allocation numbers vary):

| specimen | first diagnostic |
| --- | --- |
| `dealloc` of an `(8, 8)` block with `(8, 4)` | `Undefined Behavior: incorrect layout on deallocation: alloc232 has size 8 and alignment 8, but gave size 8 and alignment 4` |
| `dealloc` of an `(8, 8)` block with `(16, 8)` | `... has size 8 and alignment 8, but gave size 16 and alignment 8` |
| `Box<u64>` re-wrapped as `Box<u32>` and dropped | `... has size 8 and alignment 8, but gave size 4 and alignment 4` |
| `Box<u64>` re-wrapped as `Box<[u8; 8]>` and dropped | `... has size 8 and alignment 8, but gave size 8 and alignment 1` |
| `alloc` with a `(0, 8)` layout | `Undefined Behavior: creating allocation with size 0` |
| `dealloc` of the address of a `Box<()>` with `Layout::new::<()>()` | `Undefined Behavior: pointer not dereferenceable: pointer must point to some allocation, but got 0x1[noalloc] which is a dangling pointer (it has no provenance)` |
| the same block deallocated twice | `Undefined Behavior: memory access failed: alloc232 has been freed, so this pointer is dangling` |

The two re-wrapping specimens show that the pairing is a property of the *type* of the box that
is dropped: `<Box<T> as Drop>::drop` derives the layout from `T`, so a box at the wrong type
frees with the wrong layout even though the pointer is right.

Basis: normative + source (both revisions) + execution (older revision).

### 11. The optimizer may remove allocations

- Documentation, older revision (`library/core/src/alloc/global.rs` lines 98-100): "You must not
  rely on allocations actually happening, even if there are explicit heap allocations in the
  source. The optimizer may detect unused allocations that it can either eliminate entirely or
  move to the stack and thus never invoke the allocator."
- Documentation, newer revision (a new section "The `#[global_allocator]` attribute"):
  "Allocation functions may non-deterministically entirely skip the underlying allocator ... The
  compiler may also merge multiple allocation operations into one, as long as it can also adjust
  all corresponding deallocation operations accordingly", and an allocation made through the
  global functions "can only be freed by invoking `dealloc` or `realloc`. In particular, passing
  a pointer to such an allocation directly to the underlying method on `GlobalAlloc` is not
  permitted."
- Observed, older revision, default allocator, `-C opt-level=3`: `unpinned_roundtrip` contains no
  call of `__rust_alloc` or `__rust_dealloc` (Finding 3), while the variant that passes the box
  through `std::hint::black_box` calls the marker, `__rust_alloc(64, 8)`, `handle_alloc_error`
  on the null branch, and `__rust_dealloc`.
- Observed, older revision, `#[global_allocator]` in the same crate: the same unpinned round trip
  made one allocation and one deallocation at both optimization levels. The recorder's numbers
  for the other scenarios are stable across optimization levels because each scenario passes its
  box through `black_box`.

The pairing of Finding 10 is therefore a statement about the calls that do reach the allocator.
How many source-level boxes correspond to a call is not fixed by the language.

Basis: documentation (both revisions, different text) + execution (older revision).

### 12. What differs between the two revisions

| item | older revision (`14210df0e`, executed) | newer revision (`3ef0c22cd`, source only) |
| --- | --- | --- |
| `box_new_uninit` | `fn`, line 247; the zero-size case is handled inside `Global.allocate` | `const fn`, line 322, behind `#[rustc_const_unstable(feature = "const_heap", issue = "79597")]`; begins with `if layout.size() == 0 { return layout.dangling_ptr().as_ptr(); }` |
| `Box::new` body | lines 284-292 | lines 368-376, same statements |
| `box_assume_init_into_vec_unsafe` | `pub fn`, line 262 | `pub const fn`, line 341 |
| rewriting of `*box` in `ElaborateBoxDerefs` | `Rvalue::Cast(CastKind::Transmute, ...)` from the `NonNull` field to `*const T` (`elaborate_box_derefs.rs` line 74) | `Rvalue::Cast(CastKind::BoxDerefTransmute, Operand::Copy(field_place), ptr_ty)` (line 67); `BoxDerefTransmute` is a new `CastKind` variant |
| `GlobalAlloc` documentation on removed allocations | one bullet (lines 98-100) | a section on `#[global_allocator]` that also permits merging allocations and forbids freeing a global allocation through the underlying `GlobalAlloc` method directly |
| line positions | as cited | shifted; see `support/source_audit.json` |

Unchanged between the two (anchor text present at both): the declarations of the entry points
and of the marker; the marker's name and unconditional emission; `global_fn_name` /
`default_fn_name`; the `#[global_allocator]` and `#[alloc_error_handler]` expansions' use of
`#[rustc_std_internal_symbol]`; `allocator_shim_contents`; the LLVM allocator attributes; the
zero-size rules of `Global`; `Layout::dangling_ptr`; the body of `Box::new`; the `Drop`
implementation of `Box`; `open_drop_for_box_contents` and the call of the box destructor; the
lowering comments for `write_via_move` and `write_box_via_move`; the Miri diagnostics for a
zero-sized allocation and a layout mismatch; the absence of `ShallowInitBox`, `NullaryOp`,
`exchange_malloc`, `box_free`, `rustc_box` (as an attribute) and of any `should_panic` handler
symbol. The path `compiler/rustc_allocator/src/lib.rs` does not exist at either (HTTP 404).

Basis: source (both revisions).

### 13. The Lean model: what is defined

`support/AllocatorShimsAndBoxDropSoundness.lean` (1561 lines, no imports, namespace `AllocBox`)
defines, bottom to top:

- **Outcomes.** `Outcome α` is `ok a`, `ub e` or `oom`; `UB` enumerates `allocZeroSize`,
  `allocInvalidLayout`, `deallocZeroSize`, `deallocDangling`, `deallocNotLive`,
  `deallocLayoutMismatch`, `dropOfMovedOrUninit`.
- **Layouts and pointers.** `Layout` is a size and the base-2 logarithm of the alignment, so the
  alignment `2 ^ alignLog2` is a power of two by construction; `Layout.Valid imax l` is
  `l.size + l.align ≤ imax + 1`. `Ptr` is `block id` (the start of the heap block with that
  identity) or `dangling addr` (a bare address).
- **The heap.** `Heap` holds `isize::MAX` of the target, the live blocks `(id, layout)`, the next
  unused identity, the history of successful allocator operations (`Event.alloc id l`,
  `Event.dealloc id l`, oldest first) and two call counters.
- **The allocator contract.** `rustAlloc h l avail` is undefined behaviour for size 0 and for an
  invalid layout; otherwise it yields a fresh block (`avail = true`) or null (`avail = false`,
  the call is still counted). `rustDealloc h p l` is undefined behaviour for size 0, for a
  dangling pointer, for a block that is not live, and for a live block whose recorded layout
  differs from `l`; otherwise it removes the block and appends the event.
- **`Global`.** `globalAllocate` returns `dangling l.align` without calling `rustAlloc` when the
  size is 0; `globalDeallocate` does nothing when the size is 0.
- **Boxes.** A `BoxVal` is a pointer, the pointee layout, one `Slot` per field
  (`init : Bool`, whether the field holds a value the box is responsible for, and `runs : Nat`,
  how often its destructor has run), and `hasDropGlue` (`false` stands for
  `Box<MaybeUninit<T>>`). `boxNewUninit` allocates through `globalAllocate` and turns a null
  result into `oom`; `BoxVal.writeAll` marks every field as holding a value and cannot fail;
  `BoxVal.assumeInit` sets `hasDropGlue`; `boxNew` is their composition. `moveOutField i` clears
  `init` without running a destructor and is undefined behaviour on a field that holds no value;
  `writeField i` sets `init`.
- **Destruction.** `Slot.runDtor` is undefined behaviour on a slot with `init = false`, else it
  clears `init` and increments `runs`. `dropWhere flag slots` is the drop ladder under a *flag
  policy*: it visits the fields in order and runs the destructor of each field for which `flag`
  is true. `boxFree` is `globalDeallocate h b.ptr b.layout`. `cleanupWith flag` is the ladder
  followed by `boxFree`, and
  - `dropLiveFieldsThenFreeBacking := cleanupWith (fun s => s.init)`,
  - `freeBackingOnly := cleanupWith (fun _ => false)`,
  - `fullDropThenFreeBacking := cleanupWith (fun _ => true)`,
  - `boxDrop` chooses the first if `hasDropGlue` and the second otherwise.
- **Histories.** `replay events live` re-executes a history and fails at an allocation of size 0
  or of a live identity and at a deallocation whose block is not live or has another layout.
  `Heap.WF` says: identities at or above `next` are unused, the history replays from the empty
  heap to exactly the live set, and no live block has size 0. `Owns h b` says the box's pointer
  and layout agree with the heap (a live block with that layout and non-zero size, or the
  dangling address `align` with size 0); `Released h b` says its block is no longer live.

Every definition is marked `noncomputable`, which only suppresses code generation (and with it
the compiler's auxiliary recursive helpers); the definitions are structural recursions that the
kernel evaluates, and the concrete statements are proved by `decide`.

Basis: source (the Lean file in this package).

### 14. The Lean model: what is proved

All statements below are theorems of the file, checked by the Lean 4.34.1 kernel
(`support/lean_check_receipt.json`: 0 errors, 0 warnings with every warning treated as an error;
465 constants, of which 169 theorems, 253 definitions, 11 inductive types; the only axioms any
theorem depends on are `propext` and `Quot.sound`; no axiom is declared; 142 theorems depend on
no axiom at all).

**The ladder under any flag policy.**

- `dropWhere_ok_iff_sound`: `(∃ r, dropWhere flag ss = .ok r) ↔ FlagsSound flag ss`, where
  `FlagsSound flag ss` is `∀ s ∈ ss, flag s = true → s.init = true`. A policy is free of
  undefined behaviour exactly when it never selects a field without a value.
- `no_field_left_of_sound_complete` and `field_left_of_not_complete`: after a policy has run, no
  field still holds a value if the policy selects every field that held one
  (`FlagsComplete`), and some field does if the policy missed one.
- Hence the field-wise policy `fun s => s.init` is the policy that is both: `dropWhere_init`
  shows it always succeeds with effect `Slot.afterDrop` on each field, `totalRuns_afterDrop`
  that it adds exactly one destructor run per field that held a value
  (`totalRuns (ss.map Slot.afterDrop) = totalRuns ss + countInit ss`), and
  `afterDrop_idempotent` that running it again runs nothing.

**Statement 1: cleanup after field moves and of a half-written box.**

- `cleanup_selective_leak_free_exactly_once`: for every heap `h` and box `b` with `Owns h b`,
  `dropLiveFieldsThenFreeBacking h b = .ok (b', h')` for some `b'`, `h'` with
  `b'.slots = b.slots.map Slot.afterDrop`, no slot of `b'` holding a value,
  `totalRuns b'.slots = totalRuns b.slots + countInit b.slots`, `Released h' b`,
  `h'.allocCalls = h.allocCalls` and
  `h'.deallocCalls = h.deallocCalls + (if b.layout.size = 0 then 0 else 1)`.
- `cleanup_uninit_frees_block_runs_no_destructor`: under the same hypothesis
  `freeBackingOnly h b = .ok (b, h')` with `Released h' b` and the same counters: the box value,
  including every `runs` counter, is unchanged.
- `cleanup_uninit_leaves_written_fields`: if moreover some slot holds a value, then after
  `freeBackingOnly` the block is released and that slot still holds its value. This is the
  model's statement of the leak of Finding 9, and the reason "exactly once" is not claimed for
  `Box<MaybeUninit<T>>`.
- `full_drop_ub_of_missing_field`: if some slot of `b` holds no value,
  `fullDropThenFreeBacking h b = .ub .dropOfMovedOrUninit` in every heap;
  `full_drop_eq_selective_of_all_init`: if every slot holds a value, the whole-value cleanup
  equals the field-wise one.

**Statement 2: zero-sized boxes.**

- `dangling_address_nonzero_and_aligned`: `0 < l.align ∧ l.align % l.align = 0`.
- `boxNewUninit_zero_size`: for `l.size = 0`, `boxNewUninit h l n avail` is `.ok` of the box with
  pointer `dangling l.align` and the heap `h` itself, for either value of `avail`.
- `zst_box_lifecycle_never_reaches_allocator`: for `l.size = 0` there is a `b` with
  `boxNew h l n avail = .ok (b, h)`, `b.ptr = .dangling l.align`, `Owns h b`, and
  `boxDrop h b = .ok (b', h)` with no slot of `b'` holding a value. The heap after creation and
  after destruction is the heap before: no call, no event, no block.
- `rustDealloc_dangling_ub`: `rustDealloc` on any `dangling` pointer is undefined behaviour for
  every heap and layout; `rustAlloc_zero_size_ub`: so is `rustAlloc` with size 0.

**Statement 3: every deallocation carries the layout of its allocation.**

- `rustDealloc_ok_iff`: `(∃ h', rustDealloc h p l = .ok h') ↔ ∃ id, p = .block id ∧
  find h.live id = some l ∧ l.size ≠ 0`. A deallocation is defined exactly when the pointer is
  the start of a live block allocated with exactly that size and alignment.
- `rustAlloc_wf`, `rustDealloc_wf`, `Heap.empty_wf`: well-formedness holds initially and is
  preserved by every successful allocator operation.
- `dealloc_event_has_matching_alloc`: if `es₁ ++ Event.dealloc id l :: es₂` replays from the
  empty heap, then `Event.alloc id l ∈ es₁`. Together with the previous item: in the history of
  any heap reachable from the empty one, each deallocation event is preceded by an allocation
  event with the same block and the same layout.
- `double_dealloc_ub` and `rustDealloc_mismatch_ub`: a second deallocation of a block, and a
  deallocation of a live block with any other layout, are undefined behaviour.
- `box_lifecycle_dealloc_layout_eq_alloc_layout`: if `boxNewUninit h l n avail = .ok (b, h₁)` on
  a well-formed `h`, then `h₁` is well formed and `Owns h₁ b`; if `l.size ≠ 0` the box points to
  block `h.next` and `h₁.events = h.events ++ [Event.alloc h.next l]`; and for every well-formed
  later heap `h₂` in which the box still owns its block and every box value `c` with the same
  pointer and layout (whatever its fields and drop-glue marker), `boxFree h₂ c = .ok h₃` with
  `h₃` well formed, the block released, and, if `l.size ≠ 0`,
  `h₃.events = h₂.events ++ [Event.dealloc h.next l]`. The layout in the deallocation event is
  the `l` of the allocation event.
- `owns_after_rustAlloc`, `owns_after_rustDealloc_other`: allocating, or deallocating another
  block, does not disturb `Owns`, so the hypothesis "still owns" survives unrelated heap
  activity.
- `boxFree_wrong_layout_ub`: a box value whose layout was replaced by a different non-zero-sized
  one cannot be freed (`.ub .deallocLayoutMismatch`).
- `boxNewUninit_oom`: a null answer for a valid non-zero-sized layout makes `boxNewUninit`
  `.oom`; no box value results.

Basis: source (the Lean file) + execution (the kernel check recorded in the receipt).

### 15. Sharpness: two counterexample families and their native mirrors

Both are theorems of `AllocBox.Example`, proved by evaluation, about a pointee of two fields
with layout size 128 and alignment `2 ^ 6` on a target with `isize::MAX = 2^63 - 1`.

`ce1_full_drop_after_partial_move_or_uninit_ub` states four facts:

1. `Box::new`, move field 0 out, then the *whole-value* cleanup: `.ub .dropOfMovedOrUninit`;
2. `box_new_uninit`, write field 0 only, `assume_init`, then the whole-value cleanup:
   `.ub .dropOfMovedOrUninit`;
3. and 4. in the same two states the field-wise cleanup is defined.

`ce2_zst_or_mismatched_align_dealloc_ub` states five facts:

1. `rustDealloc` on `dangling 1` with the zero-sized layout: `.ub .deallocZeroSize`;
2. on `dangling 64` with a non-zero size: `.ub .deallocDangling`;
3. on the live `(128, 2^6)` block with `(128, 2^3)`: `.ub .deallocLayoutMismatch`;
4. on the same block with `(64, 2^6)`: `.ub .deallocLayoutMismatch`;
5. with the allocation layout itself the call is defined.

| model fact | native mirror (Miri, older revision) | native diagnostic |
| --- | --- | --- |
| ce1, fact 1 | `specimens/miri/ub_full_drop_after_partial_move.rs` (`ptr::drop_in_place` of a pair whose first field was read out and dropped) | `memory access failed: alloc235 has been freed, so this pointer is dangling` |
| ce1, fact 2 | `specimens/miri/ub_full_drop_of_uninit_box.rs` (`assume_init` on a half-written box, then drop) | `reading memory at alloc235[0x8..0x10], but memory is uninitialized at [0x8..0x10]` |
| ce1, facts 3-4 | `specimens/miri/ok_partial_move_unwind.rs`, and the run-time counts of Finding 8 | no report; each destructor ran once |
| ce2, fact 1 (fact 2 has no separate specimen) | `specimens/miri/ub_dealloc_zst_dangling.rs` | `pointer not dereferenceable ... got 0x1[noalloc] which is a dangling pointer` |
| ce2, fact 3 | `specimens/miri/ub_dealloc_wrong_align.rs`, `ub_box_from_raw_wrong_align_only.rs` | `incorrect layout on deallocation ... gave size 8 and alignment 4` (resp. `alignment 1`) |
| ce2, fact 4 | `specimens/miri/ub_dealloc_wrong_size.rs`, `ub_box_from_raw_wrong_layout.rs` | `incorrect layout on deallocation ... gave size 16 and alignment 8` (resp. `size 4 and alignment 4`) |

The model and Miri classify the deallocation of a zero-sized box's address differently in name
(the model checks the size first and says `deallocZeroSize`; Miri resolves the pointer first and
reports a dangling pointer); both reject it.

Further evaluated statements tie the model to the run-time table of Finding 8:
`sizedRoundTrip_summary` (1 allocation call, 1 deallocation call, runs `[1, 1]`),
`moveFirstThenUnwind_summary` (1, 1, runs `[0, 1]`: one remaining-field destructor),
`moveBothThenUnwind_summary` (1, 1, `[0, 0]`), `uninitMidInitUnwind_summary` (1, 1, `[0, 0]`
with a field left holding a value), `uninitCompleted_summary` (1, 1, `[1, 1]`),
`zstRoundTrip_summary` (0, 0), `zst_box_address` (`dangling 64` and `dangling 1`),
`box_new_null_aborts` (`.oom`) and `box_from_raw_at_wrong_type_ub`.

Basis: source (the Lean file) + execution (kernel check; Miri on the older revision).

### 16. How the model corresponds to the compiler and library

| model | stands for | how the correspondence was checked |
| --- | --- | --- |
| `rustAlloc`: size 0 is undefined behaviour | `GlobalAlloc::alloc` safety clause | documentation quoted in Finding 5; Miri `creating allocation with size 0` |
| `rustDealloc`: live block, same layout | `GlobalAlloc::dealloc` safety clause | documentation quoted in Finding 10; Miri `incorrect layout on deallocation`; double free reported |
| `Layout.Valid` | `Layout::max_size_for_alignment` | source, Finding 5; the recorder saw no request violating it |
| `globalAllocate` / `globalDeallocate` zero-size branches | `Global::alloc_impl_runtime`, `deallocate_impl_runtime` | source, Finding 5; zero allocator calls measured |
| `dangling l.align` | `Layout::dangling_ptr` | source; addresses 1, 8, 64 measured |
| `boxNewUninit`, `writeAll`, `assumeInit` | `box_new_uninit`, `write_via_move`, the transmute | source and MIR, Finding 6 |
| `writeAll` cannot fail | "Nothing below can panic" | the storing block has no unwind edge, Finding 6 |
| `oom` | `handle_alloc_error` aborting | `SIGABRT` measured, Finding 4 |
| `dropLiveFieldsThenFreeBacking` | the open drop of a `Box<T>` plus `<Box<T> as Drop>::drop` | MIR after `ElaborateDrops` and run-time counts, Finding 8 |
| the flag policy `fun s => s.init` | drop flags (or their static resolution) for the fields of `*box` | MIR: no flag for the unconditional move, a `switchInt` on a boolean for the conditional one |
| `freeBackingOnly` | drop of a `Box<MaybeUninit<T>>` | MIR and run-time counts, Finding 9 |
| `boxFree` uses `b.layout` | `Layout::for_value_raw` in the `Drop` implementation | source, Finding 8; re-wrapped boxes in Miri, Finding 10 |
| `Event` history and `replay` | the calls that reach the allocator | the recording allocator's event log, Finding 10 |

Simplifications that a reader must not read past: a box has a flat list of fields (no nested move
paths); a destructor cannot unwind; `writeAll` and `writeField` do not model overwriting a field
that already holds a value; block identities are never reused and blocks have no addresses, so
alignment of real addresses and address reuse are outside the model; `realloc` is absent; memory
contents are absent.

Basis: derived (from the findings above).

### 17. The Anneal trusted MIR semantics does not yet reach these constructs

At `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- `Trusted.MirAst.Rvalue` (`trusted/lean/Trusted/MirAst.lean` line 620) has the constructors
  `use`, `binaryOp`, `unaryOp`, `discriminant`, `ref`, `addressOf`, `aggregateTuple` and
  `unsupported`; its documentation (line 612) says `.unsupported` "represents all other `Rvalue`
  variants", naming `Cast` among them. The thirteen-variant `Rvalue` it quotes (line 566) is that
  of `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`, a third revision that this
  report did not audit; its variant names equal those found at the two audited revisions.
- `Trusted.MirAst.MirTy` (line 312) has no struct type: "non-fieldless-enum `Adt`" is listed
  among the kinds that map to `.unsupported` (line 309). `Box<T>` is such an `Adt`.
- `Trusted.MirAst.TerminatorKind` (line 785) represents `Drop` as `.unsupported` (line 783).
- In `trusted/lean/Trusted/MirSemantics.lean`, `evalTerminator` (line 1537) answers
  `.fault .unsupported` for a `.call` terminator (line 1568), and `initState` (line 799) rejects
  a query whose caller-visible memory is not empty (line 803).

Derived consequence: a MIR body that creates, reads through, moves out of or drops a `Box`, or
that calls an allocator entry point, lies outside the fragment that this semantics executes and
fails closed with `FaultKind.unsupported`. Nothing in this report is contradicted by that
semantics, and none of the theorems of Finding 14 is stated over it. To bring the constructs of
this report into such a semantics one would need at least: a table of heap blocks that records
the allocation layout; the allocator entry points as primitives with the contract of
`rustAlloc` / `rustDealloc` (they are bodyless foreign items in MIR); the marker as a no-op;
`Drop` terminators including the open drop of a box and the call of its destructor; and the
pointer cast that `ElaborateBoxDerefs` inserts (`Transmute` at the older revision,
`BoxDerefTransmute` at the newer one).

Basis: source (the pinned Anneal revision) + derived.

### 18. Names that older descriptions use and that do not exist at these revisions

| name | status at both revisions | what exists instead |
| --- | --- | --- |
| `compiler/rustc_allocator/src/lib.rs` | no such path (HTTP 404) | `rustc_ast/src/expand/allocator.rs` (names and method table), `rustc_builtin_macros/src/global_allocator.rs` and `alloc_error_handler.rs` (expansions), `rustc_codegen_ssa/src/base.rs` (`allocator_shim_contents`), `rustc_codegen_llvm/src/allocator.rs` (the module). A comment in `library/std/src/alloc.rs` still points to `src/librustc_allocator/lib.rs` |
| `__rust_alloc_error_handler_should_panic_v2`, an out-of-memory strategy option | absent from source and from the built objects | `__rust_alloc_error_handler` only (Finding 4) |
| `alloc::alloc::box_free`, `exchange_malloc` | no lang item, no function | `<Box<T, A> as Drop>::drop` and `box_new_uninit`. The `rustc-dev-guide` pages `lang-items.md` and `profiling.md` still mention the old names |
| `Rvalue::ShallowInitBox`, a nullary-operator rvalue | absent from `rustc_middle/src/mir/syntax.rs` | `write_via_move` lowered to an assignment (Finding 6) |
| `#[rustc_box]` | not an attribute; the only occurrence is the note on the removed `box_syntax` feature in `rustc_feature/src/removed.rs` ("replaced with `#[rustc_box]`") | `Box::new` is a plain function call |
| `__rg_alloc`, `__rg_oom` | no such symbols; two stale comments | the expansion defines `__rust_alloc` etc. directly |
| `const fn box_new_uninit` | true at the newer revision only | a plain `fn` at the older revision |
| the marker as an "ordering fence" | not supported by source or by the generated code | a link-time marker (Finding 3) |

Documentation and source disagree in the two `rustc-dev-guide` pages named above; this report
follows the source and the built artifacts.

Basis: source (both revisions) + execution (older revision).

## Boundaries

**Not examined.**

- `Box<T, A>` and `Vec<T, A>` with an allocator other than `Global`; `Rc`, `Arc`, `ThinBox`,
  `String` and the collections other than `Vec`.
- `-C panic=abort`, link-time optimization, incremental compilation, dynamic linking of `std`
  (the case in which no allocator module is generated), `no_std` binaries and the
  `__rdl_alloc_error_handler` path, the Cranelift and GCC backends, and targets other than
  `x86_64-unknown-linux-gnu`.
- Whether the marker call disappears under link-time optimization, where the empty definition
  becomes visible to the optimizer.
- The compile-time (const-evaluation) branch of `Global` (`alloc_impl_const`,
  `const_allocate`).
- A destructor that panics during the open drop of a box: the cleanup edge that still frees the
  block was read in MIR (Finding 8) but no such program was run.
- Miri with a user `#[global_allocator]` installed. All Miri specimens use the default
  allocator, for which Miri itself implements the entry points and their checks.
- Any execution on the newer revision.
- The census of absent names covers `compiler/`, `library/alloc`, `library/core/src`,
  `library/std/src/alloc.rs`, `library/std/src/sys/alloc`, `src/tools/miri/src`,
  `tests/mir-opt`, `tests/ui/allocator` and the `rustc-dev-guide` sources at each revision, not
  the whole repository or its submodules.

**Unknown.**

- Why the MIR inliner does not inline `Box::new` into the specimen at default thresholds. Only
  the fact (and that raised thresholds change it) was measured.
- Whether the newer revision emits the same symbols and the same MIR. The relevant source is
  unchanged where Finding 12 says so, which makes it likely; it was not run.

**Known not to apply.**

- "Every field is destroyed exactly once" does not hold for `Box<MaybeUninit<T>>`: fields
  written by hand are leaked when the box is dropped or unwound (Finding 9; Lean
  `cleanup_uninit_leaves_written_fields`).
- The number of allocator calls is not a guarantee of the language: the documentation at both
  revisions says so, and the default-allocator build removes the unpinned round trip.
- The marker symbol is not a memory-ordering or synchronization device.
- The layout pairing is not enforced for arbitrary code: `Box::from_raw` at a pointee type with
  another layout produces a deallocation with the wrong layout (Finding 10). It is a property of
  boxes whose type matches their allocation.

**Unsupported.**

- The Anneal trusted MIR semantics at the pinned revision does not execute calls, `Drop`
  terminators or struct types (Finding 17): the constructs of this report are explicitly
  `.unsupported` there.
- The Lean model has no `realloc`, no unsized pointees, no destructors that unwind, no nested
  move paths and no memory contents (Finding 16).

**Stronger conclusions that the evidence does not establish.**

- That `rustc` is proved to pair layouts or to destroy fields exactly once. The theorems are
  about the model of Finding 13; the link to the compiler is the correspondence table of Finding
  16, checked by reading source and by 21 run-time scenarios, ten MIR specimens and fourteen Miri
  specimens on one revision and one target.
- That a user-supplied allocator may assume anything about zero-sized or mismatched requests
  being filtered for it. The filtering observed here is done by `Global` and by `Box`; code that
  calls `std::alloc::alloc` / `dealloc` directly is bound by the contract itself.
- That the behaviours measured at `-C opt-level=0` and `3` hold at every optimization setting.

## Evidence

All evidence was acquired on 2026-11-21.

**Upstream source.** Repository, revision, path and line are given inline in the Findings. The
complete list of cited files, with for each revision the HTTP status, the SHA-256 of the file and
the line numbers of every quoted anchor, is `support/source_audit.json`, produced by
`support/audit_sources.py`. That script also resolves each pinned revision through the GitHub API
and requires the returned 40-hex SHA to equal the pin:

| repository | revision | committer date | first line of the commit message |
| --- | --- | --- | --- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | 2026-05-31T20:13:59Z | `Auto merge of #157219 - jhpratt:rollup-70ooTMg, r=jhpratt` |
| `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | 2026-11-11T17:59:24Z | `Auto merge of #165821 - JonathanBrouwer:rollup-TeJSwaI, r=JonathanBrouwer` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | 2026-11-19T21:39:21Z | `[theory] Bridge PureLift onto Trusted MIR semantics (#266)` |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | 2026-09-24T17:27:27Z | `chore: prepare release` |

The statements "occurs in no file of ..." were established by extracting the listed directories
of the GitHub source archive of each revision and searching them; the per-file anchors in
`audit_sources.py` (expected `absent`) re-check the same strings in the files that matter most.

**Execution.** Toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host
`x86_64-unknown-linux-gnu`, LLVM 22.1.6; `miri 0.1.0 (14210df0e2 2026-05-31)`; GNU `nm` 2.47.
Driver: `support/probe_allocator_shims_and_box.py` (no arguments). It compiles and runs:

| part | specimen | what it yields |
| --- | --- | --- |
| A | `support/specimens/alloc_lifecycle.rs` | per-scenario allocator event logs and destructor counts under a recording `#[global_allocator]`, at `-C opt-level=0` and `3` |
| B | `support/specimens/default_alloc.rs`, `alloc_lifecycle.rs` | `nm` on the saved codegen objects and the executable; LLVM IR declarations and call lists; `-Zunpretty=expanded` of a minimal global allocator |
| C | `support/specimens/mir_specimens.rs` | MIR dumps at five points of the pipeline for ten functions, the final MIR at `-C opt-level=0` and `3`, and the final MIR of two functions with the inliner thresholds raised |
| D | `support/specimens/miri/*.rs` (14 files) | exit status and first diagnostic under Miri, each compared with an expected pattern |
| E | `support/specimens/oom_abort.rs` | exit status or signal and messages for five allocation-failure modes |

Its output is `support/probe_output/probe_results.json` (101 checks, all passing, with the raw
measurements they were computed from), `support/probe_output/global_allocator_expansion.txt`,
and 54 MIR files under `support/probe_output/mir/`. Host paths are removed from everything the
script writes; thread ids in panic messages are replaced by `<tid>` and the toolchain's embedded
source prefix by `<rust-src>`.

**Lean.** `support/AllocatorShimsAndBoxDropSoundness.lean` (SHA-256
`28a8075a1ea5081c16883a388ec1b64116c162eb35c7e3cd345b638283fe254f`), checked by
`support/check_lean.py`, which (1) scans the source for the words `sorry`, `admit`, `omega`,
`bv_decide`, `native_decide`, `partial`, `unsafe`, `axiom`, `opaque`, `implemented_by`, `extern`,
`Classical` and `_unsafe_rec` (all counts 0), (2) compiles it with
`lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, and (3) runs
`support/AllocatorShimsAndBoxDropAudit.lean` against the compiled module. The audit walks every
constant the module declares, rejects axioms, opaque constants, definitions that are not `safe`
and any `_unsafe_rec` helper, rejects any theorem that depends on an axiom other than `propext`
and `Quot.sound`, and prints the axiom dependencies of 27 named theorems. The result is
`support/lean_check_receipt.json`.

**What is synthesis rather than source fact.** Findings 3 (the consequence drawn from the empty
body), 16 and the last paragraph of 17 are this report's reasoning; the tables of Findings 12 and
18 are compilations of source facts.

## Revalidation

Cheapest first. A passing check establishes only what it checks.

1. **Structure of this package.** `python3 tools/reference.py check` at the corpus root.
2. **Pins and source anchors (no toolchain needed, a few minutes).**
   `python3 support/audit_sources.py` (it reaches the GitHub API through the `gh` command, or
   whatever `--gh` names, and fetches files from `raw.githubusercontent.com`). It fails if a
   pinned revision no longer resolves to
   itself or if any quoted anchor is missing where it is expected or present where it is expected
   to be absent. To test another `rust-lang/rust` revision, add it as a subject and to the
   revision tuples in the script; the anchors that fail are the findings to re-read. The ones
   most likely to move: the declarations in `library/alloc/src/alloc.rs` (Finding 1), the marker
   name in `rustc_ast/src/expand/allocator.rs` (Finding 3), the body of `Box::new` and the `Drop`
   implementation in `library/alloc/src/boxed.rs` (Findings 6 and 8), and
   `open_drop_for_box_contents` (Finding 8).
3. **The Lean statements (seconds).** `python3 support/check_lean.py --lean lean` with Lean
   `v4.34.1` on `PATH`. A newer Lean may rename core lemmas; the file uses only `List.mem_cons`,
   `List.mem_cons_self`, `List.mem_cons_of_mem`, `List.mem_map`, `List.map_congr_left`,
   `Nat.two_pow_pos`, `Nat.mod_self`, `Nat.add_add_add_comm`, `Nat.ne_of_lt`, `Nat.le_of_lt`,
   `Nat.le_of_eq`, `Nat.le_refl` and the decidability lemmas `of_decide_eq_true` /
   `of_decide_eq_false` from the core library.
4. **The measurements (about fifteen seconds with a nightly toolchain and its `miri`
   component).** `python3 support/probe_allocator_shims_and_box.py`. With another toolchain the
   individual checks say which finding changed:
   - a `B.` check failing means the symbol set, the mangling or the LLVM attributes of Findings
     1-3 changed (for instance a renamed marker, or the error handler moving into the allocator
     module);
   - `C.write_via_move_is_an_assignment_in_built_mir`,
     `C.box_new.inlined_body_is_box_new_uninit_then_store_then_transmute` and
     `C.no_legacy_box_names_in_any_dump` cover Finding 6; at the newer revision the zero-sized
     check `C.box_new_zst...` is expected to need re-reading, because `box_new_uninit` gained its
     own zero-size return there;
   - the `C.partial_move.*`, `C.conditional_partial_move.*`, `C.uninit_mid_init.*` and
     `C.full_move_out.*` checks cover Findings 8 and 9;
   - the `A.` checks cover the run-time tables; `A.*.every_dealloc_layout_equals_its_alloc_layout`
     and `A.*.no_layout_mismatch_no_unknown_free_no_bad_request` are the pairing of Finding 10;
   - the `D.` checks compare Miri's diagnostics with the expected text, so a reworded diagnostic
     fails them without any change in behaviour;
   - the `E.` checks cover Finding 4.
   `--skip-miri` runs everything else without the Miri component.
5. **A single discriminating command for Finding 2.** Build any program with
   `-C codegen-units=1 -C save-temps` and run `nm` on the object whose name has no `-cgu.`
   component: with the default allocator it defines the four `___rust_` allocator symbols and the
   marker; with a `#[global_allocator]` it defines the marker only.

What has to be repeated by hand if the checks fail: the reading of the MIR-building and
drop-elaboration code (Findings 6 and 8), since the probe only recognizes the MIR shapes
described there, and the Anneal reading of Finding 17 for another revision of that repository.
