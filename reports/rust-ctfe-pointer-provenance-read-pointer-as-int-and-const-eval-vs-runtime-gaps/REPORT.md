# Rust CTFE Pointer Provenance, ReadPointerAsInt, and Compile-Time vs Runtime Semantic Divergences

## Summary

Although Rust's compile-time function evaluator (`CompileTimeMachine` in `rustc_const_eval`) and the Miri Undefined Behavior interpreter (`MiriMachine` in `rust-lang/miri`) instantiate the same generic MIR interpreter (`InterpCx<'tcx, M: Machine<'tcx>>`), **neither semantics subsumes the other**. Compile-time evaluation (`const fn` / CTFE) and runtime execution diverge **bidirectionally** across six pointer-provenance and memory invariants:

1. **Symbolic relocatable offsets (`CtfeProvenance::OFFSET_IS_ADDR = false`) vs concrete addresses (`miri::Provenance::OFFSET_IS_ADDR = true`).** Before linking, compile-time allocations have no physical virtual addresses: `Pointer<CtfeProvenance>` stores a packed 64-bit `(AllocId, immutable, shared_ref)` handle alongside an allocation-relative `offset` (`WILDCARD = None`), whereas runtime memory in Miri and MiniRust `BasicMemory` assigns every allocation a concrete non-zero base address and stores absolute addresses in `offset`.
2. **`ReadPointerAsInt` is `InterpErrorKind::Unsupported`, not Abstract Machine `UndefinedBehavior`.** Transmuting a provenance-bearing pointer to `usize`, reading pointer bytes through a `union` integer field or `*const u8`, or invoking `raw_eq` / `compare_bytes` on pointer-bearing memory is **well-defined at runtime** (stripping provenance to expose concrete address bytes, per MiniRust `Type::Int::decode`), whereas CTFE aborts with `UnsupportedOpInfo::ReadPointerAsInt` at two gates: `Scalar::try_to_scalar_int` (immediate registers) and `Allocation::get_bytes_strip_provenance` (memory ranges). Conversely, provenance-free pointers (`ptr::null()`, `ptr::without_provenance(addr)`) are stored as `Scalar::Int` without `ProvenanceMap` entries, so pointer-to-integer transmutation on them **succeeds** in CTFE.
3. **Sub-pointer `PointerFrag` copying vs `ReadPartialPointer` and constant interning.** Byte-wise pointer copying via `MaybeUninit<u8>` (unlike `u8`) preserves `PointerFrag<CtfeProvenance>` slices and succeeds in CTFE if reassembled intact (`ProvenanceMap::read_ptr`), whereas loading a partially overwritten pointer as `*const T` yields a valid provenance-free raw pointer at runtime (`Ok(None)`) while raising `UnsupportedOpInfo::ReadPartialPointer` in CTFE, and leaving unmerged fragments in a final `const`/`static` fails `prepare_alloc` (`InternError::PartialPointer`).
4. **Symbolic alignment and Kleene 3-valued pointer comparison.** CTFE's `check_align` requires `alloc_info.align >= required_align` (`AlignmentCheckFailed`) regardless of offset, whereas runtime tests `(base_addr + offset) % required_align == 0`. Similarly, `guaranteed_cmp` returns `2` ("unknown") whenever linker deduplication, ICF, or unknown base addresses leave equality undecidable before linking.
5. **Global `.rodata` freezing vs absent Stacked/Tree Borrows in CTFE.** CTFE recursively freezes `const`, promoted, and nested `static` allocations (`Mutability::Not` in `.rodata`, where runtime writes trigger `WriteToReadOnly` UB), **yet CTFE omits Stacked Borrows and Tree Borrows completely** (`AllocExtra = ()`, `FrameExtra = ()`), maintaining only a 2-bit `(IMMUTABLE_MASK, SHARED_REF_MASK)` latch on `&Freeze` references. Raw-pointer and `&mut` aliasing violations therefore **pass CTFE silently** while causing immediate runtime UB in Miri and LLVM codegen.
6. **Verification consequences.** A sound verifier for `const fn` libraries cannot treat CTFE success as runtime UB-freedom, cannot treat runtime UB-freedom as `const` evaluability (`E0080`), and cannot treat `ReadPointerAsInt` as `unreachable` UB during runtime constant propagation; it must discharge a **Dual-Interpretation Contract** plus `const_eval_select` refinement obligations.

## Applicability

These findings apply to Rust `const fn` libraries, `const` and `static` initializers, promoted constant expressions, MIR optimization passes (`ConstProp` / GVN), and formal verification frameworks targeting Rust MIR, MiniRust, or LLVM IR.

The five subjects in `REPORT.json` establish the normative specification, reference UB oracle, and compiler implementation:

- **`rust-lang/rust` (`560abf7946ae41fd210edac5dfe829d7eff86eec`):** Defines the shared MIR engine (`compiler/rustc_const_eval/src/interpret/`), value/allocation/provenance structures (`compiler/rustc_middle/src/mir/interpret/`), `CompileTimeMachine` (`compiler/rustc_const_eval/src/const_eval/machine.rs`), constant interning (`compiler/rustc_const_eval/src/interpret/intern.rs`), and Strict/Exposed Provenance APIs (`library/core/src/ptr/const_ptr.rs`, stabilized in Rust 1.84.0 under RFC 3559).
- **`rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`):** Instantiates `InterpCx` with `MiriMachine` (`src/machine.rs`), concrete addresses, `Provenance::{Concrete, Wildcard}`, and Stacked Borrows / Tree Borrows aliasing checks.
- **`minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`):** Specifies runtime `BasicMemory` (`spec/mem/basic.md`), `Value` (`spec/lang/values.md`), and typed `encode`/`decode` over `AbstractByte<Provenance>` (`spec/lang/representation.md`).
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) and `rust-lang/unsafe-code-guidelines` (`d809f91e62968913d808e53397fbcf7cea762cce`):** Define normative constant-expression rules (`src/const_eval.md`, `r[const-eval.const-expr.cast]`, `r[const-eval.const-expr.borrows]`, `r[const-eval.const-expr.path-static]`) and representation invariants.

Within the corpus, this report complements `rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence`, `rust-allocation-provenance-and-stack-lifetime-semantics`, `minirust-representation-transfers-provenance-and-primitive-lowering`, and `ctfe-const-eval-select-and-reflection-intrinsic-verification-contracts` by analyzing the `OFFSET_IS_ADDR` provenance split, `ReadPointerAsInt` and `ReadPartialPointer` enforcement, and bidirectional CTFE-vs-runtime verification hazards.

## Findings

### 1. Memory and Provenance Representations Across CTFE, Miri, and MiniRust

Basis: source + normative

CTFE and Miri share the `interpret::Provenance` trait (`compiler/rustc_middle/src/mir/interpret/pointer.rs:59-80`), whose associated constants separate symbolic relocatable memory from concrete addressable memory:

```rust
pub trait Provenance: Copy + PartialEq + fmt::Debug + 'static {
    const OFFSET_IS_ADDR: bool;
    const WILDCARD: Option<Self>;
    fn fmt(ptr: &Pointer<Self>, f: &mut fmt::Formatter<'_>) -> fmt::Result;
    fn get_alloc_id(self) -> Option<AllocId>;
}
```

| Dimension | CTFE (`CompileTimeMachine`, `rustc_const_eval`) | Runtime UB Oracle (`MiriMachine`, `rust-lang/miri`) | Normative Spec (`MiniRust`, `minirust/minirust`) |
| --- | --- | --- | --- |
| Provenance type | `CtfeProvenance(NonZero<u64>)` (`pointer.rs:91`) | `miri::Provenance` (`Concrete { alloc_id, tag } \| Wildcard`, `miri/src/machine.rs:272-297`) | `Option<(AllocId, ProvExtra)>` (`spec/mem/basic.md:18-20`) |
| Bit / structural payload | Bits `0..=61`: `AllocId`; bit `62`: `SHARED_REF_MASK`; bit `63`: `IMMUTABLE_MASK` (`immutable ⇒ shared_ref`, `pointer.rs:114-164`) | 64-bit `AllocId` + 64-bit `BorTag` (borrow node ID), or `Wildcard` | Mathematical `(AllocId(Int), Extra)` |
| `OFFSET_IS_ADDR` | **`false`** (`pointer.rs:169`): `Pointer.offset` is relative to `alloc_id` (`0..=size`) | **`true`** (`miri/src/machine.rs:338`): `Pointer.offset` is absolute virtual address | Concrete address (`Allocation.addr > 0`, `offset = ptr.addr - alloc.addr`, `basic.md:29-30, 218`) |
| `WILDCARD` (exposed int-to-ptr) | **`None`** (`pointer.rs:172`); `expose_provenance` rejected (`const_eval/machine.rs:1165-1171`) | **`Some(Provenance::Wildcard)`** (`miri/src/machine.rs:341`, PNVI-ae-udi over-approximation) | Parameterized `expose_provenance` / `int_to_ptr`; `without_provenance` gives `None` |
| Provenance-free pointer (`ptr::without_provenance(a)`) | `Scalar::Int(ScalarInt(a))` in registers; raw bytes without `ProvenanceMap` entry in memory (`value.rs:271-279`) | `Scalar::Int(ScalarInt(a))` (`Pointer { provenance: None, offset: a }`) | `ThinPointer { addr: a, provenance: None }` (`representation.md:90-93`) |
| Aliasing / borrow state | **None** beyond `IMMUTABLE_MASK` (`AllocExtra = ()`, `FrameExtra = ()`, `intern.rs:41-42`) | Full per-allocation Stacked Borrows or Tree Borrows (`FrameExtra::borrow_tracker`, `miri/src/machine.rs:134`) | Pluggable `ProvExtra` / `AllocExtra` (Tree Borrows) |

When Miri imports a CTFE-evaluated global from `tcx` into runtime memory, `Allocation::adjust_from_tcx` (`compiler/rustc_middle/src/mir/interpret/allocation.rs:504-534`) bridges the two representations: for each `(offset, ctfe_prov)` in `self.provenance.ptrs()`, it reads the relative offset stored in `bytes[idx..idx + ptr_size]`, invokes `adjust_ptr` to allocate a concrete base address and `BorTag`, and **rewrites `bytes[idx..idx + ptr_size]` in-place** to `(base_addr + rel_offset)`. During CTFE those bytes contain only `rel_offset`, explaining why exposing them as integer bytes before link time would leak pre-relocation offsets `0, 4, 8, ...` inconsistent with runtime execution.

### 2. `ReadPointerAsInt` vs Runtime Provenance Stripping: Error Taxonomy and Dual Enforcement Gates

Basis: source + normative + derived

`compiler/rustc_middle/src/mir/interpret/error.rs` (lines 324–434 vs 683–739) draws a strict architectural boundary between **`InterpErrorKind::UndefinedBehavior(UndefinedBehaviorInfo)`** and **`InterpErrorKind::Unsupported(UnsupportedOpInfo)`**:

- **Abstract Machine `UndefinedBehaviorInfo`:** Violations invalid in *both* CTFE and runtime, including dereferencing a provenance-free integer pointer (`DanglingIntPointer`, `error.rs:369-375`), out-of-bounds `offset` (`PointerOutOfBounds`, `error.rs:360-367`), uninitialized integer/boolean reads (`InvalidUninitBytes`, `error.rs:410`), and writes to immutable globals (`WriteToReadOnly`, `error.rs:379`).
- **CTFE representation limits (`UnsupportedOpInfo`, `error.rs:688-708`):** Operations **well-defined at runtime** in MiniRust and Miri whose outputs depend on link-time addresses: `ReadPointerAsInt` (`"unable to turn pointer into integer"`, `error.rs:703, 722`), `ReadPartialPointer` (`"unable to read parts of a pointer from memory"`, `error.rs:701, 720`), `ThreadLocalStatic`, and `ExternStatic`.

#### Runtime semantics (MiniRust and Miri)

In MiniRust (`spec/lang/representation.md:73-93`), `Type::Int::decode` runs `bytes.try_map(|b| b.data())?`, rejecting only `AbstractByte::Uninit` and discarding `Option<ProvenanceFrag>`. Consequently, at runtime:

1. `ptr.addr()` (`library/core/src/ptr/const_ptr.rs:152-159`, implemented via `unsafe { mem::transmute(self.cast::<()>()) }`) strips provenance without exposing `AllocId` and returns the `usize` address.
2. `ptr as usize` / `ptr.expose_provenance()` (`const_ptr.rs:186-188`, `CastKind::PointerExposeProvenance` in `cast.rs:96-100, 287-305`) calls `M::expose_provenance` and extracts the integer via `Scalar::try_to_scalar_int` (`value.rs:295-297`).
3. Union punning `union { p: *const u8, n: usize }` at `n`, reading `*(&p as *const *const u8 as *const u8)`, and calling `core::intrinsics::raw_eq(&p1, &p2)` or `compare_bytes` succeed via `Allocation::get_bytes_strip_provenance` (`allocation.rs:586-612`), which bypasses its provenance guard whenever `Prov::OFFSET_IS_ADDR == true`.

#### CTFE enforcement gates and the provenance-free fast path

1. **Static cast rejection (`r[const-eval.const-expr.cast]`, `const_eval.md:222-224`; `const_eval/machine.rs:1165-1171`):** Pointer-to-address `as` casts are rejected statically (`addr` and `expose_provenance` omit `const`), and `CompileTimeMachine::expose_provenance` returns `Unsupported("exposing pointers is not possible at compile-time")`.
2. **Immediate scalar gate (`Scalar::try_to_scalar_int`, `value.rs:291-318`):** Coercing an SSA `Scalar::Ptr(ptr, sz)` to an integer (e.g., `transmute::<*const u8, usize>(p)` or `binary_int_op` in `operator.rs:106-107`) checks `CtfeProvenance::OFFSET_IS_ADDR` (`false`) and fails with `UnsupportedOpInfo::ReadPointerAsInt(None)`.
3. **Memory byte-range gate (`Allocation::get_bytes_strip_provenance`, `allocation.rs:586-612`):** Typed integer loads, `compare_bytes_intrinsic` (`intrinsics.rs:1140-1156`), and `raw_eq_intrinsic` (`intrinsics.rs:1158-1181`) execute:
   ```rust
   if !Prov::OFFSET_IS_ADDR && !self.provenance.range_empty(range, cx) {
       return Err(AllocError::ReadPointerAsInt(Some(BadBytesAccess { ... })));
   }
   ```
   Notably, `raw_eq(&p, &p)` in `const fn` fails with `ReadPointerAsInt` even when comparing an identical pointer variable with itself, because `raw_eq_intrinsic` strips provenance unconditionally on both ranges.
4. **Provenance-free exception (`ptr::null()`, `ptr::without_provenance(k)`):** Because provenance-free pointers reside in `Scalar::Int(k)` and leave `provenance.range_empty(range, cx) == true` in memory, `transmute::<*const u8, usize>(ptr::without_provenance(0x2a))`, union `usize` reads, and `raw_eq` **all succeed in CTFE**! Only non-ZST dereferences (`memory.rs:751` -> `DanglingIntPointer`) or non-zero `offset` (`intrinsics.rs:1043` -> `DanglingIntPointer`, whereas `p.offset(0)` is valid) trigger UB.

In required const contexts (`const`, `static`, `[T; N]`, `const { ... }`), both `UndefinedBehavior` and `Unsupported` emit `E0080`. During opportunistic MIR `ConstProp` or verification of runtime `const fn` calls, however, treating `Unsupported(ReadPointerAsInt)` as `UndefinedBehavior` would misclassify legal runtime code (`raw_eq`, `ptr.addr()`) as `unreachable` and cause miscompilations.

### 3. Sub-Pointer Byte Manipulation, `PointerFrag` Merging, and Relocation Interning Limits

Basis: source + derived

`ProvenanceMap<Prov>` (`compiler/rustc_middle/src/mir/interpret/allocation/provenance_map.rs:36-42`) maintains provenance at two levels:

- `ptrs: SortedMap<Size, Prov>` — aligned/unaligned whole-pointer provenances (`PTR_SIZE` bytes) mapping to object-file relocations.
- `bytes: Option<Box<SortedMap<Size, PointerFrag<Prov>>>>` — per-byte fragments (`PointerFrag { idx: u8, prov: Prov, bytes: [u8; 8] }`, `provenance_map.rs:21-31`) produced when untyped copies (`mem_copy`, `ptr::copy_nonoverlapping::<u8>`, `MaybeUninit<u8>` array moves) slice pointers (`prepare_copy`, `provenance_map.rs:380-455`) or partial writes clobber part of a pointer (`clear`, `provenance_map.rs:293-341`).

Three rules govern byte-level buffer manipulation in `const fn`:

1. **`MaybeUninit<u8>` preserves `PointerFrag`; `u8` strips provenance:** Copying `T = *const i32` byte-by-byte through `MaybeUninit<u8>` or `ptr::copy_nonoverlapping::<u8>` copies `PointerFrag` (`idx = 0..8`) without calling `get_bytes_strip_provenance`. Reading the destination back as `*const i32` invokes `ProvenanceMap::read_ptr` (`provenance_map.rs:186-246`), which verifies `frag.idx == idx` and uniform `(frag.prov, frag.bytes)` across all `PTR_SIZE` bytes to reconstruct `Ok(Some(prov))` in **both** CTFE and Miri. Copying through typed `u8` loads/stores fails with `ReadPointerAsInt` in CTFE and silently strips provenance at runtime.
2. **Reading corrupted fragments as `*const T` (`ReadPartialPointer` vs `Ok(None)`):** Overwriting byte `0` of a stored pointer `p: *const u8` with `0u8` and reading the slot back as `*const u8` (without dereferencing) diverges sharply:
   - **Runtime / Miri (`OFFSET_IS_ADDR == true`) and MiniRust (`decode_ptr`, `representation.md:112-133`):** `read_ptr` returns `Ok(None)`, producing a valid provenance-free `Pointer::without_provenance(modified_addr)`.
   - **CTFE (`OFFSET_IS_ADDR == false`, `provenance_map.rs:239-244`):** `if prov.is_none() && !Prov::OFFSET_IS_ADDR` aborts with `UnsupportedOpInfo::ReadPartialPointer(offset)`, because carry propagation in `(base_addr + offset)` makes the resulting address unknowable before linking.
3. **Final constant interning (`prepare_alloc`, `intern.rs:76-80`):** Even if never read during CTFE, an unmerged `PointerFrag` inside `MaybeUninit<*const u8>` fails `alloc.provenance_merge_bytes(&tcx)` (`provenance_map.rs:153-182`) with `InternError::PartialPointer` (`ValidationErrorKind::PartialPointer`, `validity.rs:174, 193`), because object formats cannot represent sub-pointer byte relocations portably.

### 4. Symbolic Alignment, 3-Valued Pointer Comparison, and Same-Allocation Offset Arithmetic

Basis: source + normative

`OFFSET_IS_ADDR = false` induces three further pointer-arithmetic restrictions:

1. **Symbolic alignment (`memory.rs:599-623`):** While runtime checks `(base_addr + offset) % align == 0`, CTFE requires **both** `alloc_info.align >= align` **and** `offset % align == 0`. Reading `*(buf.as_ptr().add(k) as *const u32)` from `let buf = [0u8; 8];` (`alloc_info.align = 1`) fails with `AlignmentCheckFailed { has: 1, required: 4 }` for **every** $k \in \{0..4\}$, even though runtime execution guarantees alignment for some $k \in \{0..3\}$. Accordingly, `align_offset` and `is_aligned` (`const_ptr.rs:1301, 1339`) are not `const fn`.
2. **Kleene 3-valued `guaranteed_cmp` and `is_null()` panics (`const_eval/machine.rs:281-390`, `const_ptr.rs:22-41`):** Direct MIR `BinOp::Eq` on pointers errors in CTFE (`const_eval/machine.rs:1097-1104`). `(*const T)::is_null` dispatches via `const_eval_select!`: runtime evaluates `ptr.addr() == 0`, whereas CTFE calls `ptr_guaranteed_cmp(ptr, null_mut())`, returning `0` ( unequal), `1` (equal), or `2` (unknown—causing `is_null()` to panic at compile time!). Out-of-bounds wrapped pointers such as `(&x as *const u8).wrapping_sub(64)` return `2` (`scalar_may_be_null`), and pointer-to-pointer `guaranteed_cmp` returns `2` on functions, vtables, stack locals, and deduplicable `.rodata` `GlobalAlloc::Memory` allocations because LLVM `MergeFunctions`, linker ICF, and constant merging can coalesce or split addresses across codegen units.
3. **`ptr_offset_from` (`intrinsics.rs:436-561`):** Both CTFE and Miri require identical live `AllocId`s (`a_alloc_id == b_alloc_id`) with an in-bounds span, except that two equal provenance-free pointers (`a == b`, zero-byte span) succeed and return `0` in both engines while `a != b` without provenance raises `DanglingIntPointer`.

### 5. Bidirectional Divergence: Global `.rodata` Freezing vs Unchecked Aliasing in CTFE

Basis: source + normative + derived

#### Direction A: Valid runtime mutations rejected or frozen by CTFE

1. **Recursive `.rodata` freezing (`intern_const_alloc_recursive`, `intern.rs:204-357`):**
   - `InternKind::Constant` and `InternKind::Promoted` (`intern.rs:216-220`) force the root and every transitively reachable allocation to `Mutability::Not` (`.rodata`), rejecting nested pointers lacking `SHARED_REF_MASK` (`InternError::BadMutablePointer`, `intern.rs:302-323`).
   - `InternKind::Static(Mutability::Not)` (`intern.rs:222-235`) keeps the root `Mutability::Mut` iff `!T::is_freeze` (`UnsafeCell`), while freezing all nested allocations to `Mutability::Not` (`E0492` in `const_eval.md:93-98` rejects interior-mutable nested borrows).
   - `const_allocate` heap allocations (`const_eval/machine.rs:522-540`) cannot escape into globals unless frozen at `offset == 0` via `const_make_global` (`memory.rs:335-350`; otherwise `InternError::ConstAllocNotGlobal`, `intern.rs:65-71`). Any later write to a frozen allocation raises `UndefinedBehaviorInfo::WriteToReadOnly(alloc_id)` (`memory.rs:828-830`).
2. **Global static isolation (`const_eval.md:38-43`, `const_eval/machine.rs:1200-1230`):** Mutating any `static` fails (`ModifiedGlobal`), and reading mutable or `!Freeze` statics inside `const` fails (`ConstAccessesMutGlobal`).

#### Direction B: Runtime Undefined Behavior that passes CTFE silently

Because `CompileTimeMachine` sets `AllocExtra = ()` and `FrameExtra = ()` (`intern.rs:41-42`), **CTFE executes neither Stacked Borrows (Jung et al., DOI `10.1145/3371109`) nor Tree Borrows (Villani et al., DOI `10.1145/3735592`)**. `CompileTimeMachine::retag_ptr_value` (`const_eval/machine.rs:1232-1265`) only sets `IMMUTABLE_MASK | SHARED_REF_MASK` on `&T` when `T: Freeze` (checked on direct writes through *that* pointer in `before_memory_write`, `const_eval/machine.rs:1278-1296`):

1. **`&mut T` aliasing UB goes completely undetected:** `let mut x = 0; let p = &raw mut x; let r = &mut *p; *p = 1; *r = 2;` evaluates cleanly to `2` in CTFE (`&mut` retags set no tag and invalidate no sibling pointers), yet triggers immediate Undefined Behavior under Stacked Borrows, Tree Borrows, and LLVM `noalias` at runtime!
2. **Mutation behind a live `&Freeze` reference via a raw pointer passes CTFE:** `let mut x = 0; let p = &raw mut x; let s: &i32 = &*p; *p = 42; *s` evaluates to `42` in CTFE (since `p` lacks `IMMUTABLE_MASK` and `x` is `Mutability::Mut`), whereas runtime Stacked/Tree Borrows flags `*p = 42` + `*s` as immediate UB!
3. **Deferred intermediate validity (`const_eval/machine.rs:413-415`):** Without `-Zextra-const-ub-checks`, intermediate `enforce_validity` checks only `layout.is_uninhabited()`, deferring full `ValidityVisitor` validation to final constant interning.

### 6. Soundness Contracts for Formal Verification of `const fn` Libraries

Basis: derived + source

Because a `pub const fn f(x: A) -> B` executes both at runtime and in `const` contexts—and may branch via `core::intrinsics::const_eval_select` (`const_ptr.rs:26`)—verifying `const fn` libraries requires a **three-part Dual-Interpretation Contract**:

1. **Runtime UB-Freedom and Postcondition ($\text{WP}_{\text{rt}}$):** Verify `f` against full runtime operational semantics (MiniRust + Stacked/Tree Borrows with non-deterministic concrete base addresses `OFFSET_IS_ADDR = true`), proving full aliasing discipline (`&mut` uniqueness, `&Freeze` immutability), step-by-step validity, and postcondition $\Phi(x, \text{ret})$. Never treat CTFE evaluation success as evidence for $\text{WP}_{\text{rt}}$.
2. **CTFE Evaluability Certificate ($\text{Safe}_{\text{ctfe}}$):** To guarantee `E0080`-free `const` evaluation under precondition $P_{\text{const}}(x)$, verify: (a) no `Scalar::Ptr` hits `to_scalar_int` and no `Type::Int` / `raw_eq` / `compare_bytes` read overlaps provenance-bearing bytes (generic byte copies of pointer-bearing types use `MaybeUninit<u8>`, never `u8`); (b) every `read_ptr` sees either complete ordered fragments `0..PTR_SIZE` of one pointer or provenance-free bytes, and all escaped allocations satisfy `merge_bytes`; (c) every access at alignment $A$ targets an allocation created with `alloc.align >= A` at `offset % A == 0`; and (d) all `is_null()` / `guaranteed_cmp` calls avoid `2` ("unknown") and touch no mutable/`!Freeze` statics.
3. **`const_eval_select` Refinement:** At every `const_eval_select!(@capture { c } -> R: if const { f_ctfe(c) } else { f_rt(c) })` call, prove that whenever `f_ctfe(c)` terminates normally with $v$, `f_rt(c)` under every valid linker address assignment is UB-free and refines $v$ up to concrete address assignment.

## Boundaries

- **Final normative Rust aliasing model (`unknown`):** While `rust-lang/miri` implements Stacked Borrows (default) and Tree Borrows (`-Zmiri-tree-borrows`) and `rustc_const_eval` implements neither, which aliasing model Rust will adopt normatively remains **`unknown`** as of 2026-11-20. Sound verifiers should target their common safe discipline (strict Stacked Borrows without exposed-pointer guesswork, or deferred-reservation-safe Tree Borrows).
- **Compile-time pointer-to-integer casts and `expose_provenance` (`unsupported`):** Turning provenance-bearing pointers into integers during CTFE is explicitly **`unsupported`** (`UnsupportedOpInfo::ReadPointerAsInt` and `CompileTimeMachine::expose_provenance`, `const_eval/machine.rs:1165-1171`), because assigning synthetic addresses before linking would falsify runtime observations unless `ScalarInt` were replaced by symbolic address expressions.
- **CTFE compilation as a runtime UB check (`known not to apply`):** Using `const _: () = { f(); };` to certify runtime UB-freedom is **`known not to apply`**: `&mut` / `&Freeze` aliasing violations and intermediate non-uninhabited validity violations (without `-Zextra-const-ub-checks`) pass CTFE while triggering immediate runtime UB.
- **Universal failure of `*const T` to `usize` transmutation in CTFE (`known not to apply` to provenance-free pointers):** The claim that pointer-to-`usize` transmutation always fails in `const fn` is **`known not to apply`** to `ptr::null()` and `ptr::without_provenance(addr)`, which use `Scalar::Int` and transmute cleanly in CTFE.
- **CHERI hardware capabilities and LLVM IR `ptrtoint` backend lowering (`not examined`):** Hardware 128-bit capability provenance (Morello/CHERI) and LLVM optimizer `inttoptr`/`ptrtoint` miscompilations downstream of MIR were **`not examined`** here (see `rustc-llvm-ir-attributes-metadata-and-cross-path-obligations` and `rust-allocation-provenance-and-stack-lifetime-semantics`).

## Evidence

### Primary Repository Sources (Observed 2026-11-20)

1. **`rust-lang/rust` (`560abf7946ae41fd210edac5dfe829d7eff86eec`):**
   - `compiler/rustc_middle/src/mir/interpret/pointer.rs:59-191, 226-349`: `trait Provenance` (`OFFSET_IS_ADDR`, `WILDCARD`), `CtfeProvenance(NonZero<u64>)` bit-packing (`IMMUTABLE_MASK`, `SHARED_REF_MASK`, `ALLOC_ID_MASK`), `OFFSET_IS_ADDR = false`, and `WILDCARD = None`.
   - `compiler/rustc_middle/src/mir/interpret/value.rs:271-325` and `error.rs:324-434, 683-739, 788-800`: `Scalar::to_pointer` / `try_to_scalar_int` and separation of `UndefinedBehaviorInfo` from `UnsupportedOpInfo` (`ReadPointerAsInt`, `ReadPartialPointer`).
   - `compiler/rustc_middle/src/mir/interpret/allocation.rs:305-330, 504-534, 586-612` and `allocation/provenance_map.rs:21-42, 153-246, 293-482`: `adjust_from_tcx`, `get_bytes_strip_provenance`, `PointerFrag`, `merge_bytes`, `read_ptr`, `clear`, and `prepare_copy`.
   - `compiler/rustc_const_eval/src/interpret/memory.rs:599-624, 708-832`, `intrinsics.rs:436-561, 1040-1085, 1140-1181`, `intern.rs:36-95, 204-357`, and `validity.rs:167-205, 264-286`: Symbolic `check_align`, `WriteToReadOnly`, `ptr_offset_from`, `raw_eq_intrinsic` / `compare_bytes_intrinsic`, `AllocExtra = ()`, `prepare_alloc` (`PartialPointer`, `ConstAllocNotGlobal`), and `intern_const_alloc_recursive`.
   - `compiler/rustc_const_eval/src/const_eval/machine.rs:281-390, 408-415, 516-575, 1097-1104, 1165-1171, 1200-1296` and `library/core/src/ptr/const_ptr.rs:22-41, 152-188, 1301-1344`: `guaranteed_cmp`, `enforce_validity`, `expose_provenance`, `retag_ptr_value`, `before_memory_write`, `is_null` (`const_eval_select!`), and non-const `addr`/`expose_provenance`/`align_offset`/`is_aligned`.
2. **`rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`):**
   - `src/machine.rs:63-70, 132-153, 272-350`: `AlignmentCheck`, `FrameExtra::borrow_tracker`, `Provenance::{Concrete, Wildcard}`, `OFFSET_IS_ADDR = true`, and `WILDCARD = Some(Provenance::Wildcard)`.
3. **`minirust/minirust` (`063d784186d3252bee242217f218223205c0b568`):**
   - `spec/mem/basic.md:25-41, 91-142, 193-275`, `spec/lang/values.md:6-24`, and `spec/lang/representation.md:73-142`: Non-deterministic concrete `Allocation.addr > 0`, `Type::Int::decode` provenance stripping, and `decode_ptr` returning `provenance: None` on partial/corrupted fragments.
4. **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) and `rust-lang/unsafe-code-guidelines` (`d809f91e62968913d808e53397fbcf7cea762cce`):**
   - `rust-lang/reference` `src/const_eval.md:38-43, 76-197, 221-225, 276-284`: Static access restrictions, borrow rules (`E0764`, `E0492`), and pointer-to-address cast prohibition (`r[const-eval.const-expr.cast]`).

### Peer-Reviewed Literature and RFCs

- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer. "Stacked Borrows: An Aliasing Model for Rust." *Proc. ACM Program. Lang.* 4, POPL, Article 41 (2020). DOI: `10.1145/3371109`.
- Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung. "Tree Borrows." *Proc. ACM Program. Lang.* 9, PLDI (2025). DOI: `10.1145/3735592`.
- Kayvan Memarian et al. "Exploring C Semantics and Pointer Provenance." *Proc. ACM Program. Lang.* 3, POPL, Article 67 (2019). DOI: `10.1145/3290380`.
- Jeehoon Kang et al. "A Formal C Memory Model Supporting Integer-Pointer Casts." *PLDI 2015*, pp. 326–335 (2015). DOI: `10.1145/2737924.2737965`.
- Juneyoung Lee et al. "Reconciling High-Level Optimizations and Low-Level Code in LLVM." *Proc. ACM Program. Lang.* 2, OOPSLA, Article 125 (2018). DOI: `10.1145/3276495`.
- Aria Beingessner (`Gankra`) and Ralf Jung. *Rust RFC 3559: Rust Has Provenance* (stabilized in Rust 1.84.0).

## Revalidation

Save the following discriminator suite to `/tmp/ctfe_vs_runtime_probes.rs` to test each CTFE vs runtime/Miri boundary via `--cfg` flags:

```rust
// 1. Passing CTFE cases (provenance-free transmute, MaybeUninit<u8> PointerFrag
//    copy, and aliasing-&mut false negative in CTFE):
//      rustc --edition=2021 --crate-type=lib /tmp/ctfe_vs_runtime_probes.rs
// 2. ReadPointerAsInt E0080 ("unable to turn pointer into integer"):
//      rustc --edition=2021 --crate-type=lib --cfg fail_read_ptr_as_int /tmp/ctfe_vs_runtime_probes.rs
// 3. ReadPartialPointer E0080 ("unable to read parts of a pointer from memory"):
//      rustc --edition=2021 --crate-type=lib --cfg fail_partial_ptr /tmp/ctfe_vs_runtime_probes.rs
// 4. Symbolic alignment E0080 ("alignment 1, but alignment 4 is required"):
//      rustc --edition=2021 --crate-type=lib --cfg fail_sym_align /tmp/ctfe_vs_runtime_probes.rs
// 5. Miri catches the `&mut` aliasing UB inside `aliasing_mut_in_const_fn` that CTFE accepts:
//      cargo miri run  (invoking `aliasing_mut_in_const_fn()` from `fn main()`)

use core::mem::{transmute, MaybeUninit};
use core::ptr;

pub const PROV_FREE_ADDR: usize = unsafe {
    transmute::<*const u8, usize>(ptr::without_provenance::<u8>(0x1234))
};
const _: () = assert!(PROV_FREE_ADDR == 0x1234);

pub const fn copy_ptr_via_maybe_uninit_bytes() -> i32 {
    let val: i32 = 99;
    let p: *const i32 = &val;
    let src = &p as *const *const i32 as *const MaybeUninit<u8>;
    let mut dst_slot: MaybeUninit<*const i32> = MaybeUninit::uninit();
    let dst = dst_slot.as_mut_ptr() as *mut MaybeUninit<u8>;
    let mut i = 0;
    while i < core::mem::size_of::<*const i32>() {
        unsafe { *dst.add(i) = *src.add(i); }
        i += 1;
    }
    unsafe { *dst_slot.assume_init() }
}
pub const REASSEMBLED_DEREF: i32 = copy_ptr_via_maybe_uninit_bytes();
const _: () = assert!(REASSEMBLED_DEREF == 99);

pub const fn aliasing_mut_in_const_fn() -> i32 {
    let mut x = 10;
    let raw: *mut i32 = &raw mut x;
    unsafe {
        let r: &mut i32 = &mut *raw;
        *raw = 20; // Invalidates `r` in Stacked Borrows & active Tree Borrows
        *r = 30;   // Runtime UB, yet CTFE (`AllocExtra = ()`) evaluates to 30!
        x
    }
}
pub const ALIASING_CTFE_RESULT: i32 = aliasing_mut_in_const_fn();
const _: () = assert!(ALIASING_CTFE_RESULT == 30);

#[cfg(fail_read_ptr_as_int)]
pub const BAD_PTR_TO_INT: usize = unsafe {
    let x = 0u8;
    transmute::<*const u8, usize>(&x as *const u8)
};

#[cfg(fail_partial_ptr)]
pub const BAD_PARTIAL_PTR: bool = unsafe {
    let x = 0u8;
    let mut slot: MaybeUninit<*const u8> = MaybeUninit::new(&x);
    *(slot.as_mut_ptr() as *mut u8) = 0;
    let _corrupted_raw_ptr: *const u8 = slot.assume_init();
    true
};

#[cfg(fail_sym_align)]
pub const BAD_SYM_ALIGN: u32 = unsafe {
    let buf = [0u8; 8];
    *(buf.as_ptr() as *const u32)
};
```

For source-only revalidation on a newer `rust-lang/rust` commit, diff `compiler/rustc_middle/src/mir/interpret/pointer.rs` (`CtfeProvenance::OFFSET_IS_ADDR`), `allocation.rs` (`get_bytes_strip_provenance`), `allocation/provenance_map.rs` (`read_ptr`, `merge_bytes`), `compiler/rustc_const_eval/src/interpret/intern.rs` (`intern_const_alloc_recursive`), and `const_eval/machine.rs` (`retag_ptr_value`, `guaranteed_cmp`).
