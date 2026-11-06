# `rustc` Codegen Backend Architecture, Static and DST Layouts, `FnAbi` Lowering, Intrinsics, and 249-Crate RV64GC Cross-Compilation

## Summary

This report synthesizes three source-and-mechanization investigations into `rustc`'s layout engine, `CodegenBackend` monomorphization and ABI lowering (`rustc_codegen_anneal`), and full-scale 249-crate cross-compilation of the `rustc` compiler workspace to `riscv64gc-unknown-linux-gnu`:

1. **Static `LayoutData`, Non-Recursive `#[repr(C, packed(P))]`, Slice-Tail DST Extents, and Sparse Allocation Footprints:**
   - Across `rustc_abi`, `rustc_ty_utils`, and `rustc_codegen_ssa` (`1.99.1` commit `58cf8f9c35b355199727627d07ae34a4e2846d67`), `#[repr(Rust)]` reorders struct fields (`can_ireorder_fields`) while pinning unsized tails to the final offset; `#[repr(C, packed(P))]` caps direct field alignments to $\min(\text{align}, P)$ without recursively stripping internal padding inside already-sized nested `#[repr(C)]` struct fields; and `size_of_val_raw` (`size_of_val.rs`, lines 11–94) computes `round_up(head_offset + elem_size * slice_len, align)` for slice-tail DSTs and loads `(size, align)` from vtable slots `COMMON_VTABLE_ENTRIES_SIZE` and `COMMON_VTABLE_ENTRIES_ALIGN` for `dyn Trait` tails.
   - Standard-library pointer dereferenceability (`library/core/src/ptr/mod.rs`, lines 108–165) distinguishes a pointer's contiguous bounding extent `[0, size_of_val(ptr))` from its active non-padding/non-`UnsafeCell` byte footprint (`isActivePayloadOffset`).
   - In Lean `4.34.1`, layout-table binding requires hashing all serialized layout entries, binding the target triple, and enforcing `1 <= sizeBytes <= 65535` and `1 <= alignBytes <= 65535` to defeat the 16-bit modular aliasing collision (`65540 == 4 mod 65536`), while distinct nominal `#[repr(C)]` structs with identical `{u32, u32}` geometry require `DefPathHash` disambiguation.
2. **`CodegenBackend` Monomorphization, `deduced_param_attrs` Soundness Bug, 264-Intrinsic Classification, and `FnAbi` Lowering:**
   - Across `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `1.101.0-nightly` (`92b5b8c87c61b20adc9001b41baf587634a74734`), passing the canonical seven flags (`-Z mir-opt-level=0`, `-Z mir-enable-passes=-ElaborateBoxDerefs,-Derefer,-LowerSliceLenCalls,-CheckNull,-CheckAlignment,-CheckEnums`, `-Z mir-preserve-ub`) makes `tcx.optimized_mir` structurally identical to `Runtime(PostCleanup)` modulo `const_eval_select` remapping and `#[rustc_force_inline]` inlining.
   - **Critical Phase-Mismatch Soundness Hazard (`deduced_param_attrs`):** `tcx.fn_abi_of_instance` calls `tcx.deduced_param_attrs(def_id)` (`compiler/rustc_ty_utils/src/abi.rs`, lines 542–600), which inspects `tcx.optimized_mir(def_id)` when `-C opt-level > 0` (`deduce_param_attrs.rs`, lines 217–240). If an optimization pass (`GVN`/`CopyProp`) eliminates a mutation of a by-value parameter in `optimized_mir` while a backend translates the unoptimized `Runtime(PostCleanup)` body (where the parameter is still mutated in place), `fn_abi_of_instance` marks the `PassMode::Indirect` pointer `ArgAttribute::ReadOnly`, causing the caller to omit its scratch copy and observe callee mutations! A `PostCleanup` backend must strip `ArgAttribute::ReadOnly` (`fn_abi_of_instance_no_deduced_attrs`, proved sound in Lean `4.34.1`).
   - All `264` `#[rustc_intrinsic]` declarations in `library/core/src/intrinsics/mod.rs` partition into four lowering tiers (`12` `LowerIntrinsics`-eliminated, `22` default-MIR-body fallback, `20` `IntrinsicDef::must_be_overridden` without fallback, and `210` `#[rustc_nounwind]` codegen intrinsics), with an exact `38` vs. `11` split of the `49` floating-point intrinsics between `mir_Fallback` (`38` listed in `fallback_intrinsics` in `rustc_codegen_llvm/src/context.rs`) and `libm`/hardware lowering (`11` in `replaced_intrinsics`).
   - In Lean `4.34.1`, `PassMode::Indirect { on_stack: false }` caller-allocated scratch isolation (`indirect_byval_caller_isolation_verified`), `PassMode::Cast` multi-field packing across `x86_64` SysV, `aarch64` AAPCS64, and `riscv64` LP64D with `MaskedWord` + `freezeMaskedWord` padding-poison elimination, and byte-offset-dispatched `BackendRepr::ScalarPair` / sub-word niche discriminant extraction are mechanically proved.
3. **249-Crate Cross-Compilation of `rustc` to `riscv64gc-unknown-linux-gnu` via `rustc_codegen_anneal`:**
   - Across `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `1.101.0-nightly` (`19833af7224424e8b53e288097d56b6af43d5bcf`, `2026-10-20`), and `joshlf/anneal@beb778bb135474a67dc017c185d2753a60693d8c`, five compiler and linker traps were diagnosed and resolved to cross-compile the entire pure-Rust `rustc` compiler workspace (`249` crates, `11,558` CGUs, `931,257` `MonoItem`s) in `55.14s` wall-clock (`18` jobs):
     1. Calling `tcx.def_path_str` inside `CodegenBackend::codegen_crate` triggers `trimmed_def_paths` (`expensive_diagnostic_calculation`), which fails in `DiagCtxtInner::drop` under `-Z Verify-ich` unless `tcx.def_path_debug_str` is used; calling `tcx.item_name` on `DefKind::Closure` panics across `1.99.1` and `1.101.0-nightly`.
     2. `tcx.instance_mir(instance.def)` returns polymorphic `Body<'tcx>` requiring `instance.instantiate_mir_and_normalize_erasing_regions(tcx, TypingEnv::fully_monomorphized(), EarlyBinder::bind(body.clone()))` (with `EarlyBinder::bind` taking `(tcx, value)` in `1.101.0-nightly` vs. `(value)` in `1.99.1`).
     3. `compiler/rustc` (`rustc-main`) is a 40-line wrapper calling `rustc_driver::main()`, where `rustc_driver` is an empty facade crate (`crate-type = ["dylib"]`, `1` CGU, `0` `MonoItem`s) that re-exports `rustc_driver_impl`; linking `librustc_driver.so` via `rust-lld -flavor gnu -m elf64lriscv -shared` drops all `.rlib` archive members unless wrapped in `--whole-archive ... --no-whole-archive`, and cross-CGU internal calls require `STB_GLOBAL` (`STV_DEFAULT`) symbol binding.
     4. Target-scoped `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS` keeps the `53` host `build.rs` and `31` host `proc-macro` targets on the host `x86_64` backend while routing all `249` target RV64GC crates through `librustc_codegen_anneal.so`, and `--no-default-features` cleanly excludes `rustc_codegen_llvm` (`llvm-sys`).
     5. Executing the resulting dynamically linked RV64GC `rustc-main` binary (`linked against 146 MB librustc_driver-*.so`) under `qemu-riscv64` (`10.0.2`) verified end-to-end startup, while motivating strict anti-stub-drift verification gates (`ANNEAL_STRICT_NO_FALLBACK=1`) and documenting the three remaining requirements (`TLS`/`__tls_get_addr`, `va_list`, and PIC `.got`/PLT call lowering) for un-intercepted `rustc_driver_impl::main()` execution.

---

## Applicability

This report applies to the following pinned compilers, target architectures, and verification repositories recorded in `REPORT.json`:

| Component / Subject | Version / Toolchain Date | Commit / Revision | Scope & Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (`1.98.0-nightly` Linux capture)** | `1.98.0-nightly` (`2026-05-30`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | Layout witness capture (`out_r5_inner_lib_open_hash.json`) on `x86_64-unknown-linux-gnu`. |
| **`rust-lang/rust` (`1.99.1` stable baseline)** | `1.99.1` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Source audit of `LayoutData`, `size_of_val_raw`, `core::ptr`, `CodegenBackend`, `FnAbi`, 264 intrinsics, and the 249-crate `compiler/` workspace. |
| **`rust-lang/rust` (MIR syntax/semantics baseline)** | Nightly baseline | `8006091eb71ae7d9e9bccb66c6122c9d68af4466` | MIR syntax and semantics baseline audited alongside `1.99.1` and `1.101.0-nightly`. |
| **`rust-lang/rust` (`1.100.0-nightly` Darwin capture)** | `1.100.0-nightly` | `923c95cdf5ba65cea505aa2ea829f578e1506ed8` | Dual-nominal `#[repr(C)]` layout capture (`dual_nominal.rs`) on `aarch64-apple-darwin`. |
| **`rust-lang/rust` (`1.101.0-nightly` codegen & RV64GC sysroot)** | `1.101.0-nightly` (`2026-10-20`) | `92b5b8c87c61b20adc9001b41baf587634a74734`, `19833af7224424e8b53e288097d56b6af43d5bcf` | Host `rustc_driver` / `rust-lld` toolchain and `riscv64gc-unknown-linux-gnu` target sysroot used to compile the 249-crate `rustc` workspace. |
| **`joshlf/anneal`** | `main` | `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, `beb778bb135474a67dc017c185d2753a60693d8c` | Anneal verification framework, RV64GC compiler, and `rustc_codegen_anneal` backend. |
| **`leanprover/lean4`** | `v4.34.1` | `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel verification of layout binding, slice-tail DST recurrences, `FnAbi` `PassMode` lowering, and `MaskedWord` poison elimination. |
| **`qemu-riscv64`** | `10.0.2` (`1:10.0.2+ds-2+gl0`) | Host Linux user-mode emulator | Execution of cross-compiled RV64GC ELF binaries and `librustc_driver.so` dynamic linking probes. |

---

## Findings

### 1. Static `LayoutData`, Non-Recursive `#[repr(C, packed(P))]`, Slice-Tail DST Extents, and Sparse Allocation Footprints

`Basis: source, documentation, execution, derived`

Auditing `compiler/rustc_abi/src/lib.rs` (lines 1395–1565), `compiler/rustc_ty_utils/src/layout.rs` (lines 341–705), `compiler/rustc_codegen_ssa/src/size_of_val.rs` (lines 11–94), `compiler/rustc_codegen_ssa/src/mir/place.rs` (lines 285–355), and `library/core/src/ptr/mod.rs` (lines 108–165) at `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), together with the Lean `4.34.1` modules under [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/), establishes five layout invariants:

1. **Static `LayoutData` vs. Dynamic `size_of_val_raw` Lowering:**
   - For an unsized struct ending in a slice tail `[T]`, `LayoutData.size` stores the static byte offset of the tail (`head_offset`), and `LayoutData.align.abi` stores $\max(\text{header\_align}, \text{align\_of}::<T>())$.
   - At runtime, `size_of_val_raw` extracts the slice length `slice_len: usize` from wide pointer metadata (`PtrMetadata`), computes `head_offset + elem_size * slice_len`, and rounds up to `align` via `(unaligned + (align - 1)) & !(align - 1)`. For `dyn Trait` tails, `(size, align)` are loaded from vtable slots `COMMON_VTABLE_ENTRIES_SIZE` (`index 1`) and `COMMON_VTABLE_ENTRIES_ALIGN` (`index 2`).
2. **`#[repr(Rust)]` Field Reordering vs. Non-Recursive `#[repr(C, packed(P))]`:**
   - `#[repr(Rust)]` sorts sized fields by decreasing effective alignment/niche compatibility (`ScopedTicket<'a>` in [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/out_r5_inner_lib_open_hash.json`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/out_r5_inner_lib_open_hash.json) places field 1 of size/align 8 at offset `0` and field 0 of size/align 4 at offset `8`: `"field_offsets_bytes": [8, 0]`).
   - Applying `#[repr(C, packed(P))]` to an outer struct lowers direct field alignments to $\min(\text{field\_align}, P)$, but queries each nested struct field's `LayoutOf` as an opaque `(size, align)` block—preserving all internal padding inside an already-sized nested `#[repr(C)]` struct field.
3. **Contiguous Extent vs. Sparse Active Byte Footprint (`core::ptr`):**
   - `library/core/src/ptr/mod.rs` (lines 108–165) defines pointer dereferenceability over a set of active byte addresses rather than a single contiguous `[addr, addr + size_of_val)` range (excluding `UnsafeCell` interiors for `&T` and padding bytes for typed loads).
   - Mechanized in [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditRepairs.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditRepairs.lean) (`q5_r10_joined_specimen_and_footprint_boundaries_verified`, lines 1655–1735): for `#[repr(C)] struct PacketWithTail { header: u32, flags: u16, payload: [u32] }` at length `n = 3`, total aligned extent is `20` bytes (`[0, 20)`), where byte `6` lies inside `[0, 20)` (`6 < 20`) but is inter-field padding (`isActivePayloadOffset = false`), while byte `8` (`payload[0]`) satisfies both.
4. **Full-Range `1..=65535` Layout-Table Binding Repair (Defeating the `65540` Modular Aliasing Counterexample):**
   - In [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR92AuditCounterexamples.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR92AuditCounterexamples.lean) (`layout_binding_loses_high_size_bits`), serializing `sizeBytes` and `alignBytes` into 16-bit little-endian fields without range admission allows `sizeBytes = 65540` ($4 + 2^{16}$) to produce the exact same 5-byte layout entry and fingerprint as `sizeBytes = 4`.
   - Enforcing `checkLayoutEntryInRangeQ2` (`1 <= sizeBytes <= 65535`, `1 <= alignBytes <= 65535`, power-of-two alignment, and target-triple binding in [`PR86AuditRepairs.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditRepairs.lean), `encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2`) makes the entry encoding injective and rejects `65540`.
5. **Universal `∀ n : Nat` Slice-Tail DST Agreement and `DefPathHash` Nominal Disambiguation:**
   - In [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR94AuditCounterexamples.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR94AuditCounterexamples.lean) (`c2_repaired_captured_layout_to_repr_c_universal_law_joined`), the compiler-queried descriptor for `PacketWithTail` agrees with the independent `#[repr(C)]` recurrence (`8 + n * 4`, offsets `[0, 4, 8]`, alignment `4`) for every `n : Nat`.
   - In [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/dual_nominal.rs`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/dual_nominal.rs) and [`Post96ChallengeGenerated.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96ChallengeGenerated.lean), `MetersPair { a: u32, b: u32 }` and `SecondsPair { x: u32, y: u32 }` share identical `(size = 8, align = 4, offsets = [0, 4])` geometry across `x86_64-unknown-linux-gnu` (`1.98.0-nightly`) and `aarch64-apple-darwin` (`1.100.0-nightly`), proving that layout lookups must be keyed by `DefPathHash` (`0x6f199dc811be5d82` vs. `0x328a7482f1582680`) rather than `(size, align, offsets)` alone.

---

### 2. `CodegenBackend` Monomorphization, `deduced_param_attrs` Soundness Hazard, 264-Intrinsic Partitioning, and `FnAbi` Lowering

`Basis: source, execution, derived`

Auditing `rustc_codegen_ssa`, `rustc_monomorphize`, `rustc_mir_transform`, and `rustc_ty_utils` across `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `1.101.0-nightly` (`92b5b8c87c61b20adc9001b41baf587634a74734`), paired with the Lean `4.34.1` mechanization in [`support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/track1_abi_and_mono_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/track1_abi_and_mono_probe.lean) and [`support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean), establishes six codegen-backend invariants:

1. **Canonical Seven-Flag Contract Aligning `optimized_mir` with `Runtime(PostCleanup)`:**
   - Because `tcx.instance_mir(instance.def)` queries `tcx.optimized_mir(def_id)` for `InstanceKind::Item`, `optimized_mir` steals `mir_drops_elaborated_and_const_checked`.
   - Passing `-Z mir-opt-level=0`, `-Z mir-enable-passes=-ElaborateBoxDerefs,-Derefer,-LowerSliceLenCalls,-CheckNull,-CheckAlignment,-CheckEnums`, and `-Z mir-preserve-ub` disables all optimization passes in `run_optimization_passes` except two unconditional passes (`remap_mir_for_const_eval_select` and `Inline` for `#[rustc_force_inline]`), making `tcx.instance_mir` structurally match `Runtime(PostCleanup)` while still supporting `InstanceKind::{DropGlue, VtableShim, ReifyShim, ClosureOnceShim, CloneShim}` via `mir_shims`.
2. **Phase-Mismatch Soundness Bug in `deduced_param_attrs` (`ReadOnly` on `PassMode::Indirect`) and Mitigation:**
   - `tcx.fn_abi_of_instance` calls `tcx.deduced_param_attrs(def_id)` (`compiler/rustc_ty_utils/src/abi.rs`, lines 542–600). In `compiler/rustc_mir_transform/src/deduce_param_attrs.rs` (lines 217–240), `deduced_param_attrs` inspects `tcx.optimized_mir(def_id)` whenever `tcx.sess.opts.optimize != OptLevel::No`.
   - If `-C opt-level > 0` is active (or for an upstream precompiled `core`/`std` `.rmeta` compiled with `-O`), `InstSimplify`/`DeadStoreElimination` in `optimized_mir` can eliminate a dead store `_1.0 = 99` to a by-value struct parameter `_1` that still exists in the unoptimized `Runtime(PostCleanup)` body. `deduced_param_attrs` then attaches `ArgAttribute::ReadOnly` to `_1`'s `PassMode::Indirect` ABI descriptor.
   - In `compiler/rustc_codegen_ssa/src/mir/block.rs` (lines 1035–1055, `make_pass_indirect`), when `ArgAttribute::ReadOnly` is set and the caller's argument is `Operand::Move(place)`, the caller passes `&place` **directly without allocating a caller scratch copy**! When the `PostCleanup` callee executes its uneliminated store `_1.0 = 99`, it silently mutates the caller's memory in place!
   - **Mitigation (Mechanized in [`round2_track1_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean)):** A backend translating `PostCleanup` MIR (or linking against `-O` upstream `.rmeta` crates) must strip `ArgAttribute::ReadOnly` from `PassMode::Indirect` arguments (`fn_abi_of_instance_no_deduced_attrs`), ensuring the caller always allocates a fresh scratch copy (`indirect_byval_caller_isolation_verified`).
3. **Complete Four-Tier Classification of All 264 `#[rustc_intrinsic]` Declarations and Floating-Point Partitioning:**
   - Auditing `library/core/src/intrinsics/mod.rs` and `compiler/rustc_mir_transform/src/lower_intrinsics.rs` partitions all `264` intrinsics into:
     - **Tier 1 (`12` intrinsics):** Lowered to native MIR statements/rvalues/terminators by `LowerIntrinsics` (`unreachable`, `ub_checks`, `assume`, `copy_nonoverlapping`, `transmute`, `transmute_unchecked`, `aggregate_raw_ptr`, `ptr_metadata`, `discriminant_value`, `unchecked_add`, `unchecked_sub`, `unchecked_mul`).
     - **Tier 2 (`22` intrinsics):** Carry a default Rust body in `core::intrinsics::fallback` (`is_val_statically_known`, `ctlz`, `cttz`, `ctpop`, `bitreverse`, `bswap`, `rotate_left`, `rotate_right`, `saturating_add`, `saturating_sub`, `carrying_mul_add`, `three_way_compare`, `exact_div`, `unchecked_div`, `unchecked_rem`, `unchecked_shl`, `unchecked_shr`, `disjoint_bitor`, `fadd_fast`, `fsub_fast`, `fmul_fast`, `fdiv_fast`, `frem_fast`, etc.), retrievable via `tcx.instance_mir(InstanceKind::Intrinsic(def_id))`.
     - **Tier 3 (`20` intrinsics):** Marked `#[rustc_intrinsic_must_be_overridden]` (no MIR body: `abort`, `size_of_val`, `align_of_val`, `vtable_size`, `vtable_align`, `NeedsDrop`, `type_id`, `type_name`, `variant_count`, `offset`, `arith_offset`, `ptr_mask`, `const_eval_select`, `caller_location`, `assert_inhabited`, `assert_zero_valid`, `assert_mem_uninitialized_valid`, `va_arg`, `va_copy`, `va_end`).
     - **Tier 4 (`210` intrinsics):** `#[rustc_nounwind]` intrinsics spanning atomics (`~80`), SIMD (`~61`), memory ops (`copy`, `write_bytes`, `volatile_*`, `raw_eq`, `compare_bytes`), checked/wrapping arithmetic, float-to-int saturating casts, and `49` floating-point math intrinsics.
   - Among the `49` floating-point intrinsics (`f16`, `f32`, `f64`, `f128`), `compiler/rustc_codegen_llvm/src/context.rs` (lines 410–475) lists `38` transcendental/power intrinsics (`sinf*`, `cosf*`, `powf*`, `powif*`, `expf*`, `exp2f*`, `logf*`, `log2f*`, `log10f*`, `fmaf*`, `fmuladdf*`) in `fallback_intrinsics` (redirecting `core` to software traps unless routed to `libm`), whereas `11` rounding/extremum/sqrt intrinsics (`sqrtf*`, `fabsf*`, `copysignf*`, `floorf*`, `ceilf*`, `truncf*`, `rint*`, `nearbyint*`, `roundf*`, `round_ties_even_f*`, `minimum*`/`maximum*`) are in `replaced_intrinsics` and lower directly to IEEE-754 hardware instructions (`fsqrt.{s,d}`, `fsgnj.{s,d}`, `fmin.{s,d}`, `fmax.{s,d}`) or `libm` symbols.
4. **Target `FnAbi` `PassMode::Cast` Packing, `MaskedWord` Poison Elimination, and `ScalarPair` Byte-Offset Dispatch:**
   - Across `x86_64` SysV (`rustc_target/src/callconv/x86_64.rs`), `aarch64` AAPCS64 (`aarch64.rs`), and `riscv64` LP64D (`riscv.rs`), small composite structs (`<= 16` bytes on `x86_64`/`aarch64`, or scalar-pair/integer-packed on `riscv64`) use `PassMode::Cast { pad_i32, cast: CastTarget }`.
   - Loading an 8-byte integer word from a struct with uninitialized padding bytes (such as `#[repr(C)] struct Padded { a: u8, b: u32 }` with padding at offsets `1..4`) introduces poison bits in the padding byte lanes. In [`round2_track1_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean), `MaskedWord` tracks a 64-bit `value` alongside an 8-bit `initMask`, and `freezeMaskedWord` deterministically zeroes uninitialized byte lanes (`value &&& expandedMask`, `initMask := 0xFF`), proving `freeze_eliminates_padding_poison` and round-trip field preservation (`padded_struct_cast_roundtrip_verified`).
   - For `BackendRepr::ScalarPair(a, b)`, field 0 is not guaranteed to lie at byte offset `0` under `#[repr(Rust)]` field reordering (`b_offset = a.size.align_to(b.align)`). Extracting fields by byte offset (`extractScalarPairField` dispatching on `fieldOffset == 0` vs. `fieldOffset == bOffset`, together with sub-word bit-shift/mask extraction `(word >>> (discOffset * 8)) &&& mask` for niche-encoded enums like `Result<u16, ()>`) is proved exact in [`round2_track1_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean).

---

### 3. Cross-Compiling the 249-Crate `rustc` Compiler Workspace to `riscv64gc-unknown-linux-gnu`

`Basis: source, execution`

In [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/), the `rustc_codegen_anneal` backend (`joshlf/anneal@beb778bb135474a67dc017c185d2753a60693d8c`, running under host `rustc 1.101.0-nightly` `19833af7224424e8b53e288097d56b6af43d5bcf`) cross-compiled the `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` `compiler/rustc` workspace for `--target riscv64gc-unknown-linux-gnu`. Five architectural mechanisms govern this cross-compilation:

1. **Eliminating the `tcx.def_path_str` $\to$ `trimmed_def_paths` $\to$ `DiagCtxtInner::drop` ICE and Closure `item_name` Panic:**
   - Calling `tcx.def_path_str(def_id)` inside `CodegenBackend::codegen_crate` invokes `tcx.trimmed_def_paths(())` (`compiler/rustc_middle/src/ty/print/pretty.rs`, lines 1554–1620), which calls `tcx.dcx().Register_diagnostic_used()` (`expensive_diagnostic_calculation`). When no diagnostic is actually emitted, `DiagCtxtInner::drop` (`compiler/rustc_errors/src/lib.rs`, lines 495–515) panics under `-Z Verify-ich` (`debug_assertions`) with `ICE: expensive_diagnostic_calculation called without emitting any diagnostics`. Using `tcx.def_path_debug_str(def_id)` avoids `trimmed_def_paths` completely.
   - Calling `tcx.item_name(def_id)` on `DefKind::Closure`, `DefKind::InlineConst`, or `DefKind::AnonConst` panics because anonymous items have `DefPathData::Closure` / `AnonConst` rather than `ValueNs`/`TypeNs` symbols; backends must check `tcx.opt_item_name(def_id)` or `tcx.symbol_name(instance)`.
2. **Monomorphizing `tcx.instance_mir` Across `1.99.1` and `1.101.0-nightly` (`EarlyBinder::bind` API Evolution):**
   - `tcx.instance_mir(instance.def)` returns the **polymorphic** `mir::Body<'tcx>` containing `ty::Param` (`T/#0`). Passing uninstantiated types to `tcx.layout_of` fails with `LayoutError::TooGeneric`.
   - Backends must call `instance.instantiate_mir_and_normalize_erasing_regions(tcx, ty::TypingEnv::fully_monomorphized(), ty::EarlyBinder::bind(tcx, body.clone()))`.
   - **Multi-version API delta:** Between `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rustc 1.101.0-nightly` (`19833af7224424e8b53e288097d56b6af43d5bcf`), `ty::EarlyBinder::bind` in `compiler/rustc_type_ir/src/binder.rs` changed from a one-argument constructor `EarlyBinder::bind(value)` to a two-argument constructor `EarlyBinder::bind(tcx, value)`.
3. **The `librustc_driver.so` Facade-Crate Linker Trap (`--whole-archive` and `STB_GLOBAL`):**
   - `compiler/rustc/src/main.rs` (`rustc-main`) calls `rustc_driver::main()`. However, `compiler/rustc_driver/src/lib.rs` (`crate-type = ["dylib"]`, `1` CGU, `0` `MonoItem`s) contains only `pub use rustc_driver_impl::*;` and defines zero functions of its own; all `1,098` driver `MonoItem`s live in `librustc_driver_impl-*.rlib` (`16` CGUs).
   - When `CodegenBackend::link` builds a `CrateType::Dylib` via `rust-lld -flavor gnu -m elf64lriscv -shared`, passing upstream `.rlib` archives without `--whole-archive` causes `rust-lld` to see zero undefined symbol references in `rustc_driver`'s empty `.o` file and drop **every** upstream `.rlib` member, producing an empty `librustc_driver.so` missing `rustc_driver_impl::main` (`rust-lld: error: undefined symbol: _RNvCs..._17rustc_driver_impl4main` when linking `rustc-main`, reproduced in [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.rs`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.rs) and [`rustc_codegen_traps_and_link_probe.out.txt`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.out.txt)).
   - Wrapping local `.rlib` inputs in `--whole-archive ... --no-whole-archive` (while keeping sysroot `libstd`/`libcore`/`libcompiler_builtins` outside `--whole-archive`) and emitting `STB_GLOBAL` (`STV_DEFAULT`) ELF symbols across all `16` CGUs per crate resolves both the facade-dylib and multi-CGU linking traps.
4. **249-Crate Build Census and Execution Under `qemu-riscv64`:**
   - Using target-scoped `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS="-Zcodegen-backend=target/release/librustc_codegen_anneal.so -Cpanic=abort"` and `--no-default-features` (executable recipe in [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/cross_compile_rustc_rv64gc_recipe.sh`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/cross_compile_rustc_rv64gc_recipe.sh), full census in [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_249_crate_rv64gc_census.json`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_249_crate_rv64gc_census.json)), Cargo compiled `53` host `build.rs` binaries and `31` host `proc-macro` `.so` crates with the host `x86_64` backend and cross-compiled all `249` target RV64GC crates (`164` third-party dependencies + `85` `rustc_*` compiler crates, `11,558` CGUs, `931,257` `MonoItem`s) in `55.14s` wall-clock, linking `librustc_driver-4c72a4f5080f30e2.so` (`146,161,720` bytes, `528,159` dynamic `.dynsym` functions) and `rustc-main` (`15,832` bytes).

---

## Boundaries

1. **Current RV64GC Backend Subset vs. Un-Intercepted `rustc_driver_impl::main()` Execution:** In `joshlf/anneal@beb778bb135474a67dc017c185d2753a60693d8c`, `rustc_codegen_anneal` compiles `632,148` (`67.88%`) of the `931,257` `MonoItem`s through the native RV64GC instruction selector (`lower_function_to_rv64`) and routes the remaining `299,109` (`32.12%`) unsupported bodies through `emit_stub_rv64_object` (`li a0, 0; ret`) unless `ANNEAL_STRICT_NO_FALLBACK=1` is set. Executing `rustc_driver_impl::main()` un-intercepted requires completing three remaining codegen features: (a) ELF Thread-Local Storage (`LocalInfo::StaticRef { is_thread_local: true }` / `Rvalue::ThreadLocalRef` via `R_RISCV_TLS_GD_HI20` and `__tls_get_addr` for `scoped_tls::ScopedKey` in `SESSION_GLOBALS`), (b) `va_list` intrinsics (`va_arg`, `va_copy`, `va_end`), and (c) full position-independent (`.got` / `@plt`) address materialization inside `librustc_driver.so`.
2. **`EarlyBinder::bind` Signature Across `rustc` Releases:** Codegen backends targeting both `rustc 1.99.1` and `rustc 1.101.0-nightly` must account for the `ty::EarlyBinder::bind(value)` $\to$ `ty::EarlyBinder::bind(tcx, value)` signature change in `rustc_type_ir`.

---

## Evidence

All supporting Rust probes, Lean `4.34.1` proof modules, build recipes, and census receipts are preserved under `support/`:

- **Static & DST Layouts, Sparse Allocation Footprints, and Lean `4.34.1` Layout Binding Proofs (`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/`):**
  - Captured layout JSON, Rust probe, and check receipt: [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/out_r5_inner_lib_open_hash.json`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/out_r5_inner_lib_open_hash.json), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/dual_nominal.rs`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/dual_nominal.rs), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/r02-check-results.json`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/r02-check-results.json), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/lean-toolchain`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/lean-toolchain).
  - Lean `4.34.1` modules: [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditRepairs.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditRepairs.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditCounterexamples.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR86AuditCounterexamples.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR92AuditCounterexamples.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR92AuditCounterexamples.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR94AuditCounterexamples.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/PR94AuditCounterexamples.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/OpenHashMultiCrateR5R6R9R10.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96ChallengeGenerated.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96ChallengeGenerated.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96Consumer.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96Consumer.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96LifecycleInterface.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96LifecycleInterface.lean), [`support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96NativeConsumer.lean`](support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit/AnnealResearch/Post96NativeConsumer.lean).
- **Monomorphization, `deduced_param_attrs`, Intrinsics, and `FnAbi` Lowering Proofs (`support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/`):**
  - [`support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/track1_abi_and_mono_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/track1_abi_and_mono_probe.lean), [`support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean`](support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean).
- **249-Crate RV64GC `rustc` Cross-Compilation Census & Reproducer (`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/`):**
  - [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_249_crate_rv64gc_census.json`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_249_crate_rv64gc_census.json), [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/cross_compile_rustc_rv64gc_recipe.sh`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/cross_compile_rustc_rv64gc_recipe.sh), [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.rs`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.rs), [`support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.out.txt`](support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.out.txt).

---

## Revalidation

Run the following self-contained commands from this package directory to re-check the Lean `4.34.1` layout, `FnAbi`, and `MaskedWord` proofs and the `rustc_driver` / `rust-lld` RV64GC cross-compilation trap probe:

```bash
# 1. Re-check the standalone Lean 4.34.1 FnAbi, PassMode::Indirect, PassMode::Cast, and MaskedWord proofs
lean support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/track1_abi_and_mono_probe.lean
lean support/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/round2_track1_probe.lean

# 2. Re-check the Lean 4.34.1 layout-table binding, 65540 aliasing counterexample, and DST recurrence modules
LEAN_PATH=$(pwd)/support/rustc-1-99-1-layout-dst-extent-and-sparse-allocation-audit
for mod in \
  BuiltPhaseControlsR1.lean \
  SemanticVerticalSliceCore.lean \
  SubstantiveMirByteParser.lean \
  StatefulGenericLibraryH3H7Core.lean \
  StatefulGenericLibraryH3H7.lean \
  StatefulGenericLibraryH3H7Controls.lean \
  CargoWorkspaceIntegration.lean \
  CargoWorkspaceIntegrationControls.lean \
  CharonNativeAndControlsR3R4.lean \
  OpenHashMultiCrateR5R6R9R10.lean \
  PR86AuditRepairs.lean \
  PR86AuditCounterexamples.lean \
  PR92AuditCounterexamples.lean \
  PR94AuditCounterexamples.lean \
  Post96LifecycleInterface.lean \
  Post96Consumer.lean \
  Post96ChallengeGenerated.lean \
  Post96NativeConsumer.lean; do
  lean --o="$LEAN_PATH/AnnealResearch/${mod%.lean}.olean" "$LEAN_PATH/AnnealResearch/$mod"
done

# 3. Compile and run the self-contained rustc_driver + rust-lld RV64GC trap reproducer
mkdir -p build/rv64gc-probe
SYSROOT=$(rustc +nightly --print sysroot)
LD_LIBRARY_PATH="$SYSROOT/lib" rustc +nightly --edition 2021 \
  support/rustc-codegen-backend-cross-compiling-249-crate-rustc-rv64gc-2026/rustc_codegen_traps_and_link_probe.rs \
  -o build/rv64gc-probe/probe
LD_LIBRARY_PATH="$SYSROOT/lib" ./build/rv64gc-probe/probe
```
