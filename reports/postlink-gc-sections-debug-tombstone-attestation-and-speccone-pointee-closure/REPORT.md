<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Post-Link `--gc-sections` `.debug_anneal_sites` Tombstone Attestation, Dual-Query `stdarch` Interception, and `TyCtxt` `SpecConeCollector` Pointee Closure

## Summary

Moving inline-assembly attestation from pre-link `.rcgu.o` `SHF_EXCLUDE`
sections to a post-link ELF section—so RISC-V `R_RISCV_RELAX` byte-shrinking
relocations and LTO/linker transforms are observed on the final linked
image—exposes three load-bearing compiler and linker gaps in earlier
prototypes ([`rustc-driver-asm-injection-multi-cgu-lto-containment-and-speccone-hash`](../rustc-driver-asm-injection-multi-cgu-lto-containment-and-speccone-hash/REPORT.md)
and [`riscv64-rvc-parcel-gadgets-relaxation-shf-exclude-and-isa-seam-hazards`](../riscv64-rvc-parcel-gadgets-relaxation-shf-exclude-and-isa-seam-hazards/REPORT.md)).
This package reproduces each failure mode across five ELF linkers and three
`rustc` toolchains, implements the complete `rustc_driver` v2 protocol
([`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs)), and mechanizes
nine theorems (`0` `sorry`) in `Init.*`-only Lean `v4.34.1`
([`support/PostLinkGcTombstoneAndSpecConeClosure.lean`](support/PostLinkGcTombstoneAndSpecConeClosure.lean)):

1. **`--gc-sections` Fractures Non-`.debug_*` `.anneal.asm_sites,"",@progbits`
   Across ELF Linkers; `.debug_anneal_sites,"",@progbits` + DWARF Tombstones +
   Live-Symbol ICF Coverage Resolves All Linkers and ISAs (`Basis: normative +
   source + execution + derived`):**
   - `rustc` passes `-Wl,--gc-sections` on ELF targets by default. Under
     `--gc-sections`, a non-`SHF_ALLOC`, non-`SHF_EXCLUDE` section named
     `.anneal.asm_sites,"",@progbits` fails in two opposite ways:
     * **GNU `ld.bfd 2.47`** sweeps non-`SHF_ALLOC` sections lacking
       `SEC_DEBUGGING` (`bfd/elflink.c` `_bfd_elf_gc_mark_extra_sections`),
       stripping `.anneal.asm_sites` to **`0` bytes (`0` records, 100%
       attestation loss)** even when live attested `asm!` sites remain in
       `.text`.
     * **`rust-lld` (`21.1.8`, `23.1.1`, `23.1.5`) and `ld.mold 2.42.1`**
       unconditionally retain non-`SHF_ALLOC` sections (`lld/ELF/MarkLive.cpp`),
       keeping records emitted by GC-discarded dead functions. On `x86_64` and
       `aarch64`, LLVM's `ELFObjectWriter` folds local directional labels
       (`200001b`) into `STT_SECTION (.text.dead_fn) + r_addend`, and
       `relocateNonAlloc` (`!isDebug`) evaluates `0 + r_addend`, producing
       **phantom non-zero-length spans** (`[0x4, 0x7)` `3 B` on `x86_64`;
       `[0x4, 0xc)` `8 B` on `aarch64`). On `riscv64gc`, `RISCVELFObjectWriter`
       retains `STT_NOTYPE` `.Ltmp` symbols (`r_addend = 0`), resolving dead
       `(start_va, end_va)` to `(0x0, 0x0)` (`span_len = 8` without `+relax`,
       `span_len = 0` via `R_RISCV_ADD64`/`R_RISCV_SUB64` with `+relax`).
     * **`SHF_LINK_ORDER` (`"o"`) cannot repair this:** `llvm-mc 21.1.8`
       rejects directional numeric labels as linked-to symbols (`rc=1`, `error:
       invalid linked-to symbol`); named `.L` labels collide under loop
       unrolling or multi-inlining (`rc=1`, `error: symbol '.L_s_unroll' is
       already defined`); `ld.mold 2.42.1` ignores `SHF_LINK_ORDER` GC on
       non-`SHF_ALLOC` sections (retaining phantom `[0x1, 0x5)`); and an
       upstream `.rmeta` MIR rewriter cannot predict downstream `.text.<caller>`
       section names before monomorphization.
   - Naming the non-`SHF_ALLOC` sections **`.debug_anneal_sites,"",@progbits`**
     and **`.debug_anneal_descs,"",@progbits`** activates ELF linker `.debug_*`
     GC-root preservation (`SEC_DEBUGGING` in `ld.bfd`; `isDebug` in `lld` and
     `mold`) with **`0 B` `PT_LOAD` overhead** and **DWARF dead-section
     tombstoning**: all five linkers (`ld.bfd 2.47`, `rust-lld 21.1.8/23.1.1/23.1.5`,
     and `ld.mold 2.42.1`) rewrite dead 64-bit `.quad` address relocations to
     **`(0x0, 0x0)` by default** even when `r_addend != 0` (and to
     `(0xffffffffffffffff, 0xffffffffffffffff)` under explicit `-Wl,-z,dead-reloc-in-nonalloc=.debug_anneal_sites=0xffffffffffffffff`),
     while `llvm-objcopy --remove-section=.debug_anneal_*` strips them cleanly
     after verification.
   - Across `27/27` `{1.98.0-nightly, 1.99.1, 1.102.0-nightly} × {lto=off,
     lto=thin, lto=fat}` cells, `debug_tombstone_cr` (`\r` + `.space 0 <cmt>` +
     CSPRNG directional labels) achieves **100% bit-for-bit `.text` SHA-256
     parity (`0 B` drift)** across `x86_64` (`35` live sites, `150 B`),
     `aarch64` (`5,000` live sites inside a `20,020 B < 32 KiB` `tbz` span),
     and `riscv64gc` (`900` live sites inside an `1,812 B < 4 KiB` `beqz`
     span), tombstoning dead sites cleanly.
   - Combining `--gc-sections` + `+relax` (`R_RISCV_RELAX`) + `--icf=all` on
     `riscv64gc` (`qemu-riscv64` `rc=0`) uncovers a subtle ICF × DWARF
     tombstone interaction: both `lld` and `mold` mark ICF-folded follower
     sections `!isLive()`, tombstoning the folded follower's `.debug_anneal_sites`
     entry to `(0x0, 0x0)`. When two attested Rust twins fold, the canonical
     leader's record survives at the shared PC with exact post-relaxation
     `ADD64`/`SUB64` lengths (`[4, 2, 4, 10, 6]`); however, if an **unannotated
     C/assembly section** precedes an identical attested Rust `asm!` function in
     link order, the unannotated section becomes the ICF leader and **`0`
     surviving `.debug_anneal_sites` records cover the live Rust symbol's PC**—a
     soundness gap closed deterministically by the post-link live-symbol
     coverage gate (`verifyLiveAsmSymbolCoverage`, Theorems 3 and 4).

2. **Dual-Query (`queries.optimized_mir` + `extern_queries.optimized_mir`)
   Interception Captures Prebuilt Sysroot `libcore` `stdarch` `asm!` (`197`
   Sites Including `__writeeflags` `RFLAGS.DF` UB) (`Basis: source + execution
   + derived`):**
   - Auditing the shipped `libcore` sources across `1.98.0-nightly`, `1.99.1`,
     and `1.102.0-nightly` finds **`197` `asm!` sites in `core_arch`** (`34`
     `x86` + `5` `x86_64` = **`39` `x86`/`x86_64`**, **`4` `arm_shared`**,
     `146` `riscv_shared` + `5` `riscv64` = **`151` RISC-V**, and **`3`
     LoongArch**, `100%` marked `#[inline]` or `#[inline(always)]`) plus `2`
     x87 `asm!` sites in `core/src/num/imp/dec2flt/fpu.rs`. Among these,
     `core::arch::x86_64::__writeeflags` (`x86/eflags.rs:65`) executes `push
     {}; popfq` with `options(nomem, att_syntax)` and is empirically verified
     to leak `RFLAGS.DF = 1` (`0x400`) directly into caller Rust code in
     violation of the System V AMD64 ABI (`DF = 0` invariant).
   - Because `libcore` is precompiled into the toolchain sysroot without
     Anneal's driver, `providers.queries.optimized_mir` (`LocalDefId`) captures
     **`0/7` (`0%`)** monomorphized `stdarch` `asm!` expansions (`_mm256_stream_si256`,
     `_mm_stream_si64`, `_bittestandset64`, `__readeflags`, `__writeeflags`,
     `__cpuid_count`). Overriding **both** `providers.queries.optimized_mir`
     and `providers.extern_queries.optimized_mir` (`DefId`) in
     [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs) (with an
     idempotence guard for already-wrapped upstream `.rmeta` crates and quote
     stripping on `InlineAsmRegOrRegClass::Reg` clobbers to prevent `.asciz`
     breakout) captures **`7/7` (`100%`)** live `stdarch` expansions,
     tombstones dead `stdarch` callers under `--gc-sections`, preserves
     upstream `.rmeta` nonces without double-wrapping, and maintains **100%
     `.text` SHA-256 parity (`0 B` drift)** across all three toolchains.

3. **Complete `TyCtxt` Type-Graph (`ty.walk()`) & Pointee-Validity Closure in
   `SpecConeCollector` v2 (`18/18` Recall, `0/5` False Positives) (`Basis:
   source + execution + derived`):**
   - `SpecConeCollector` v1 (`Adt`-only recursion + raw `{inst:?}` keys)
     detects `10/10` original indirect-tampering vectors (`V01`..`V10`) **but
     misses `8/8` (`0%`) pointee, compound-wrapper, `FnPtr`-ABI, foreign-static,
     and `NonNull` vectors (`V11`..`V18`, `10/18 = 55.6%` overall)**—including
     `&RefBoundedByte(u8 -> NonZeroU8)`, `&[SlicePair]` padding-mask fills,
     `*const RawTarget` `#[repr(C, packed)]`, `[ArrInner; 4]` niches,
     `(TupInner, u8, u8)` `BackendRepr::Memory` niches, `extern "C" fn(FnArgAdt)`
     `Direct` $\to$ `Indirect` `PassMode`, `extern "C" { static EXT_COUNTER }`
     type/`#[link_name]`, and `NonNull<SmartTarget>` `Drop`/padding—while also
     suffering **`1/5` false positive** when unrelated items are inserted
     earlier in the file (shifting raw `DefId(0:NN)` indices inside `{inst:?}`
     and `FnDef(...)`).
   - Upgrading `SpecConeCollector` v2 in
     [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs) to perform
     full `ty.walk()` transitive type-graph closure (`ty::Ref`, `ty::RawPtr`,
     `ty::Adt`, `ty::Slice`, `ty::Array`, `ty::Tuple`, `ty::FnPtr` +
     `tcx.fn_abi_of_fn_ptr`, `ty::FnDef`, `ty::Dynamic`, `try_normalize_erasing_regions`),
     stepwise `PlaceRef::ty` projection walking, foreign/local
     `GlobalAlloc::Static` closure (`type_of`, `is_mutable_static`,
     `is_foreign_item`, `codegen_fn_attrs` `symbol_name`/`linkage`/`link_section`),
     and `DefId(<krate>:<idx> ~ ...)` index scrubbing achieves **`18/18`
     (`100.0%`) tamper recall** and **`0/5` (`0.0%`) benign false positives**
     across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`, backed by Lean
     `v4.34.1` refutation and non-interference proofs (`ref_pointee_niche_omission_unsound`,
     `compound_tuple3_fnptr_and_extern_static_omission_unsound`,
     `evalMir_wellClosedTypeGraph_noninterference`, and
     `wellClosedSpecConeEq_preserves_totalMirAsmEquiv`).

## Applicability

This report governs post-link ELF inline-assembly attestation under section
garbage collection (`--gc-sections`), instruction relaxation (`R_RISCV_RELAX`),
and Identical Code Folding (`--icf`), cross-crate/sysroot MIR `asm!`
interception, and `TyCtxt` specification-cone hashing across the pinned
subjects in [`REPORT.json`](REPORT.json):

- **Rust toolchains examined (`rust-lang/rust`):**
  - `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`,
    toolchain `nightly-2026-06-01`);
  - `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `2026-10-13`, shipped
    `rust-lld 23.1.1` at `rust-lang/llvm-project`
    `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`);
  - `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`,
    `2026-11-11`, shipped `rust-lld 23.1.5` at `rust-lang/llvm-project`
    `0a5579eb649d3634a9c30ac873300cc2944fa070`);
  - `1.95.0-nightly` (`f134bbc78dac04a17324341a8d4a15a6930d81a7`, `2026-01-24`,
    supplying `rust-lld 21.1.8` at `rust-lang/llvm-project`
    `00d23d10dc48c6bb9d57ba96d4a748d85d77d0c7` for multi-generation linker
    comparison).
- **ELF linkers, object tools, and emulators examined:**
  - GNU `ld.bfd 2.47` (`GNU Binutils for Debian 2.47`, `x86_64-linux-gnu`);
  - `rust-lld 21.1.8`, `23.1.1`, and `23.1.5` (`x86_64`, `aarch64`, and
    `riscv64gc` ELF targets);
  - `ld.mold 2.42.1` (`rui314/mold`, Debian `2.42.1`, `x86_64`, `aarch64`, and
    `riscv64gc` ELF targets);
  - `llvm-mc 21.1.8` and `llvm-objcopy 21.1.8` (`llvm/llvm-project`
    `85a90d119deb25b518867cd37d62c7b93b575a6f`);
  - `qemu-riscv64 11.1.2` (user-mode execution of relaxed + GC'd + ICF-folded
    `riscv64gc-unknown-linux-gnu` binaries).
- **Target architectures:** `x86_64-unknown-linux-gnu`,
  `aarch64-unknown-linux-gnu`, and `riscv64gc-unknown-linux-gnu` (`+c`, with and
  without `+relax`).
- **Verification target and theorem prover:** Anneal
  (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) and Lean 4
  `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  checked synchronously and replayed onto `Init` at `trustLevel := 0`).
- **Version-shared vs. version-specific `rustc_private` APIs:** All linker
  tombstone behaviors, `stdarch` `asm!` counts (`197` sites), LTO `.text`
  SHA-256 digests, and `18/18` `SpecConeCollector` v2 detection outcomes are
  identical across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`. Only three
  internal `rustc_private` signatures differ across those compiler revisions
  (handled via `--cfg anneal_rustc_1_98` and `--cfg anneal_rustc_1_102` in
  [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs)):
  1. `ty::EarlyBinder::bind(val)` (`1.98.0-nightly`) vs.
     `ty::EarlyBinder::bind(tcx, val)` (`1.99.1+`);
  2. `TyKind::FnDef(_, args)` where `args` is `GenericArgsRef<'tcx>`
     (`1.98.0-nightly`) vs. `EarlyBinder<'tcx, GenericArgsRef<'tcx>>`
     (`1.99.1+`, `.skip_binder()`);
  3. `layout.align.abi.bytes()` (`1.98.0-nightly`, `1.99.1`) vs.
     `layout.align.bytes()` (`1.102.0-nightly`, after `AbiAndPrefAlign`
     flattening).

## Findings

### 1. `--gc-sections` × Non-`SHF_EXCLUDE` Attestation Fracture and the Unified `.debug_anneal_sites` Tombstone Protocol

`Basis: normative + source + execution + derived`

#### 1.1 Why `.anneal.asm_sites,"",@progbits` Fractures Under `-Wl,--gc-sections`

To verify `TerminatorKind::InlineAsm` machine bytes *after* linker instruction
relaxation (`R_RISCV_RELAX`, `R_RISCV_ALIGN`) and FatLTO `ModuleInlineAsm`
concatenation, [`riscv64-rvc-parcel-gadgets-relaxation-shf-exclude-and-isa-seam-hazards`](../riscv64-rvc-parcel-gadgets-relaxation-shf-exclude-and-isa-seam-hazards/REPORT.md)
proposed dropping `"e"` (`SHF_EXCLUDE`) in favor of `.anneal.asm_sites,"",@progbits`
with `R_RISCV_ADD64`/`R_RISCV_SUB64` length pairs (`4b - 3b`). However, `rustc`'s
ELF link args enable `-ffunction-sections` (`-Zfunction-sections=yes` by
default) and pass `-Wl,--gc-sections` on every normal executable/cdylib link.
Executing [`support/probe_gc_tombstone_and_stdarch.py`](support/probe_gc_tombstone_and_stdarch.py)
across a two-section object containing a GC-discarded `dead_fn` (`site_id =
0x1111`, non-zero prologue offset `startAddend = 4`) and a reachable `_start`
(`site_id = 0x2222`) demonstrates three incompatible linker behaviors on
`.anneal.asm_sites,"",@progbits`:

| Target ISA | Linker (`--gc-sections`) | `.anneal.asm_sites` Bytes | Dead `0x1111` `(start_va, end_va, span_len)` | Live `0x2222` `(start_va, end_va, span_len)` | Failure Mode on Non-`.debug_*` Section |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `x86_64` | `ld.bfd 2.47` | **`0 B`** | *(stripped)* | *(stripped)* | **100% attestation loss** (`!SEC_DEBUGGING` swept by BFD GC) |
| `x86_64` | `rust-lld 21.1.8 / 23.1.1 / 23.1.5` | `112 B` | **`(0x4, 0x7, 3)`** | `(0x201127, 0x20112a, 3)` | **Phantom non-empty `[0x4, 0x7)` dead span** (`STT_SECTION` `0 + r_addend`) |
| `x86_64` | `ld.mold 2.42.1` | `112 B` | **`(0x4, 0x7, 3)`** | `(0x201217, 0x20121a, 3)` | **Phantom non-empty `[0x4, 0x7)` dead span** (`STT_SECTION` `0 + r_addend`) |
| `aarch64` | `rust-lld 21.1.8 / 23.1.1 / 23.1.5` | `112 B` | **`(0x4, 0xc, 8)`** | `(0x210124, 0x210128, 4)` | **Phantom non-empty `[0x4, 0xc)` dead span** (`STT_SECTION` `0 + r_addend`) |
| `aarch64` | `ld.mold 2.42.1` | `112 B` | **`(0x4, 0xc, 8)`** | `(0x210214, 0x210218, 4)` | **Phantom non-empty `[0x4, 0xc)` dead span** (`STT_SECTION` `0 + r_addend`) |
| `riscv64gc` (`-relax`) | `rust-lld 21..23` & `ld.mold 2.42.1` | `112 B` | `(0x0, 0x0, 8)` | `(0x11126, 0x1112e, 8)` / `(0x201216, 0x20121e, 8)` | `end_va - start_va (0) != span_len (8)` (`STT_NOTYPE` `.Ltmp + 0`) |
| `riscv64gc` (`+relax`) | `rust-lld 21..23` & `ld.mold 2.42.1` | `112 B` | `(0x0, 0x0, 0)` | `(0x11126, 0x1112a, 4)` / `(0x201216, 0x20121a, 4)` | Dead `ADD64`/`SUB64` collapses `span_len` `8 -> 0` (`call -> jal` live `8 -> 4`) |

The mechanism behind the `x86_64`/`aarch64` vs. `riscv64gc` split is at the
LLVM MC object writer boundary:
- On `x86_64` and `aarch64`, `MCAssembler` / `ELFObjectWriter::shouldRelocateWithSymbol`
  converts `R_X86_64_64` and `R_AARCH64_ABS64` against local directional labels
  (`200001b`, `200002b`) into section-relative relocations `STT_SECTION
  (.text.dead_fn) + r_addend` (`0x4` and `0x7` after a 4-byte prologue). In
  `lld/ELF/InputSection.cpp` (`InputSection::relocateNonAlloc`), when
  `!isDebug` holds, a relocation targeting a discarded section substitutes `0`
  for the section VA **but still adds `r_addend`**, writing `0 + 4 = 0x4` and
  `0 + 7 = 0x7` (`end_va - start_va == 3 == span_len_field`!). Any verifier
  that rejects only `(0, 0)` or `start_va == end_va` falsely treats the dead
  record as a 3-byte or 8-byte live span at VA `0x4`, failing closed with an
  unmapped-VA error on every binary containing even one dead `asm!` function.
- On `riscv64gc`, `RISCVELFObjectWriter::shouldRelocateWithSymbol` forces
  symbol-relative relocations (`STT_NOTYPE` `.LtmpN` with `r_addend = 0`)
  whenever linker relaxation may move offsets, so `0 + 0 = 0x0`.
- On GNU `ld.bfd 2.47` (default system `cc` linker on Linux when `rust-lld` is
  not active), `_bfd_elf_gc_mark_extra_sections` keeps non-`SHF_ALLOC` sections
  only when `SEC_DEBUGGING` (`.debug*`, `.zdebug*`) or special note/comment
  rules match; `.anneal.asm_sites` is discarded completely (`0 B`),confirmed
  both on standalone `.o` links and full `rustc` host executables
  (`rustc_default_gc_bfd_strips_non_debug_anneal_sites_to_zero == true`).

#### 1.2 Why `SHF_LINK_ORDER` (`"o"`) Cannot Repair Non-`SHF_ALLOC` Attestation

Attempting `.pushsection .anneal.asm_sites,"o",@progbits,<linked_sym>` fails on
four independent axes (verified in [`support/probe_1_2_gc_stdarch_results.json`](support/probe_1_2_gc_stdarch_results.json)):
1. **Directional labels rejected by `llvm-mc`:** `.pushsection
   .anneal.asm_sites,"o",@progbits,200001b` fails assembly immediately in
   `llvm-mc 21.1.8` (`rc=1`, `error: invalid linked-to symbol`).
2. **Named `.L` labels break loop unrolling and multi-inlining:** Replacing
   directional labels (`200001:`) with named local symbols (`.L_anneal_s:`)
   fails whenever LLVM unrolls a loop or inlines a callee twice into the same
   CGU (`rc=1`, `error: symbol '.L_s_unroll' is already defined`), while `${:uid}`
   cannot be injected from MIR because `rustc_codegen_llvm/src/asm.rs:192`
   escapes `$` $\to$ `$$`.
3. **`ld.mold 2.42.1` ignores `SHF_LINK_ORDER` GC on non-`SHF_ALLOC` sections:**
   Even when a function symbol `dead_fn` is supplied manually, `ld.mold 2.42.1`
   retains the non-`SHF_ALLOC` `SHF_LINK_ORDER` section and emits phantom span
   `["0x1", "0x5"]` (`mold_ignores_nonalloc_shf_link_order_gc == true`).
4. **Cross-crate `.rmeta` blindness:** When `rewrite_body_inline_asm` rewrites a
   generic or `#[inline]` function in an upstream crate, the downstream
   monomorphized caller's `.text.<mangled_caller>` symbol does not yet exist.

#### 1.3 The `.debug_anneal_sites` / `.debug_anneal_descs` Tombstone Protocol and 27/27 LTO Parity

Renaming the two non-`SHF_ALLOC` sections to **`.debug_anneal_sites,"",@progbits`**
and **`.debug_anneal_descs,"",@progbits`** resolves all five linkers without
adding a single byte to `PT_LOAD` (`debug_anneal_sites_in_pt_load == false`):

```text
Record layout in `.debug_anneal_sites` (56 bytes, little-endian 64-bit ELF):
  +0x00: start_va    (.quad {l_s}b)               -- 64-bit ABS reloc to site start
  +0x08: end_va      (.quad {l_e}b)               -- 64-bit ABS reloc to site end
  +0x10: span_len    (.quad {l_e}b - {l_s}b)      -- R_RISCV_ADD64/SUB64 on riscv64 +relax
  +0x18: desc_off    (.quad {l_d}b)               -- section-rel offset into .debug_anneal_descs
  +0x20: desc_len    (.quad {l_de}b - {l_d}b)     -- static descriptor byte length (incl. NUL)
  +0x28: site_id     (.quad <u64>)                -- FNV-1a(krate::def_path, bb_idx)
  +0x30: num_relocs  (.quad <K>) + K * .quad sym  -- sym_fn / sym_static targets
```

Measured across all `21` `{x86_64, aarch64, riscv64gc-norelax, riscv64gc-relax}
× {ld.bfd 2.47, rust-lld 21.1.8, 23.1.1, 23.1.5, ld.mold 2.42.1}` combinations:
1. **100% GC survival of live records:** `ld.bfd 2.47`, `rust-lld` (`21.1.8`..`23.1.5`),
   and `ld.mold 2.42.1` all classify `.debug_anneal_*` as debugging metadata and
   preserve `112 B` (`2` records) under `--gc-sections`.
2. **Exact DWARF dead-section tombstones:** When `isDebug` holds (`lld/ELF/InputSection.cpp`
   `getRelocTargetVA` for `.debug_*` other than legacy DWARF4 `.debug_loc` /
   `.debug_ranges`, `bfd/elflink.c`, and `mold` `InputSection::apply_reloc_nonalloc`),
   **all five linkers ignore `r_addend` on discarded sections and write the exact
   tombstone `(0x0, 0x0)` by default**—eliminating the `[0x4, 0x7)` and
   `[0x4, 0xc)` phantom spans on `x86_64` and `aarch64`! Passing
   `-Wl,-z,dead-reloc-in-nonalloc=.debug_anneal_sites=0xffffffffffffffff` to
   `rust-lld` writes `(0xffffffffffffffff, 0xffffffffffffffff)` (`UINT64_MAX`).
3. **Post-link acceptance predicate (`acceptDebugSiteRecord`):** Rejecting any
   record where `start_va ∈ {0, 1, UINT64_MAX}`, `end_va ∈ {0, 1, UINT64_MAX}`,
   `[start_va, end_va)` is not contained within an executable `PT_LOAD` (`PF_X`)
   segment, or `end_va - start_va != span_len` discards `100%` of dead-section
   records across default `(0, 0)`, legacy DWARF4 `1`, and explicit `UINT64_MAX`
   tombstones while retaining `100%` of live records (mechanized in Theorem 2,
   `postlink_debug_tombstone_filter_sound_and_complete`).
4. **27/27 LTO × ISA `.text` SHA-256 parity:** Coupled with `cr_zero_drift`
   (`\r` + `.space 0 <cmt>`, where `<cmt>` is `#` on `x86_64`/`riscv64gc` and
   `//` on `aarch64`), [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs)
   achieves **exact `.text` byte-length and SHA-256 identity (`0 B` drift)**
   between uninstrumented (`off`) and attested (`debug_tombstone_cr`) builds
   across all `3` toolchains and `{lto=off, lto=thin, lto=fat}`:
   - `x86_64` (`35` live sites + `1` tombstoned dead site): `150 B`, SHA-256
     prefix `7c10a51c64871f96`;
   - `aarch64` (`5,000` live sites inside a tight `tbz` `< 32 KiB` branch + `1`
     tombstoned dead site): `20,020 B`, SHA-256 prefix `49f465c24c436c2d`;
   - `riscv64gc` (`900` live `c.addi` sites inside a tight `beqz` `< 4 KiB`
     branch + `1` tombstoned dead site): `1,812 B`, SHA-256 prefix
     `e2612ad493252f3b`.

#### 1.4 Subtle `--icf=all` × `.debug_anneal_sites` Tombstone Interaction and Live-Symbol Coverage Gate

Testing `--gc-sections` + `+relax` (`R_RISCV_RELAX`) + `--icf=all` simultaneously
on `riscv64gc-unknown-linux-gnu` across `rust-lld` (`21.1.8`, `23.1.1`, `23.1.5`)
and `ld.mold 2.42.1` (`10` rewritten `asm!` sites across `twin_relax_a`,
`twin_relax_b`, `live_extra_site`, and `dead_relax_fn`; executed under
`qemu-riscv64 11.1.2` with `rc=0`) establishes two critical properties:

1. **Verified-twin ICF folding + `R_RISCV_RELAX`:** Both `lld` and `mold` fold
   `twin_relax_b` into `twin_relax_a` (`0x11200` in `lld`, `0x201300` in `mold`)
   and mark `twin_relax_b`'s input section dead (`!isLive()`), so `5` records
   are tombstoned (`1` in `dead_relax_fn` + `4` in folded `twin_relax_b`) and
   `5` live records survive (`4` on canonical leader `twin_relax_a` + `1` on
   `live_extra_site`) with exact post-relaxation `ADD64`/`SUB64` byte lengths
   `[4, 2, 4, 10, 6]` (`call` `8 B -> 4 B jal`, `c.addi` `2 B`, `lla` `8 B ->
   8 B` + `c.MV` `10 B`).
2. **Unannotated-leader ICF absorption hazard (closed by `verifyLiveAsmSymbolCoverage`):**
   When an unannotated C/assembly object (`c_leader.o` defining `.text.c_leader`
   with `lea eax, [rdi + 9]; ret`, `0` `.debug_anneal_sites` records) is linked
   *ahead of* an attested Rust object (`r_follower.o` defining `.text.rust_follower`
   with identical machine bytes and `1` `.debug_anneal_sites` record) under
   `rust-lld --gc-sections --icf=all`, `lld` elects `.text.c_leader` (`0x201120`)
   as the canonical ICF section and marks `.text.rust_follower` dead—**tombstoning
   `rust_follower`'s `.debug_anneal_sites` record to `(0x0, 0x0)` (`0` surviving
   records) even though `rust_follower` remains a live callable symbol at
   `0x201120`!** Verifying that every `ManifestAsmFn` whose symbol resolves into
   `PT_LOAD_X` has at least one surviving `.debug_anneal_sites` record at
   `symAddr(fnSym) + relSiteOff` (`verifyLiveAsmSymbolCoverage` in
   [`support/PostLinkGcTombstoneAndSpecConeClosure.lean`](support/PostLinkGcTombstoneAndSpecConeClosure.lean))
   deterministically rejects unannotated-leader absorption while admitting
   verified-twin ICF folding (Theorems 3 and 4).

---

### 2. Prebuilt Sysroot `stdarch` `asm!` Interception via `providers.extern_queries.optimized_mir` (and Explicit-Clobber Quote Fix)

`Basis: source + execution + derived`

#### 2.1 `libcore` `stdarch` Inline-Assembly Census and the `__writeeflags` `RFLAGS.DF` UB Hazard

Scanning the shipped `library/` source tree across `1.98.0-nightly`, `1.99.1`,
and `1.102.0-nightly` yields identical counts across all three releases:
- **`197` `asm!` sites in `library/stdarch/crates/core_arch/src`**, `100%` inside
  `#[inline]` or `#[inline(always)]` functions:
  * **`39` `x86` + `x86_64` sites** (`34` in `x86/{eflags,cpuid,sse,sse2,avx2,bsr,bt,rdtsc,xsave,fxsr,rtm,...}`,
    including `_mm256_stream_si256` `vmovntdq`, `_mm_stream_si64` `movnti`,
    `_bittestandset` `bts`, `__cpuid_count` `cpuid`, `__readeflags`, and
    `__writeeflags`; plus `5` in `x86_64/{bt,sse2,avx2,macros}` including
    `_bittestandset64`);
  * **`4` `arm_shared` sites** (`barrier/cp15.rs` `dmb`/`dsb`/`isb` MCR
    coprocessor barriers and `hints.rs` `__nop`);
  * **`151` RISC-V sites** (`146` in `riscv_shared/` CSR/hlvm/fence intrinsics
    + `5` in `riscv64/`);
  * **`3` LoongArch sites** (`2` in `loongarch_shared/` + `1` in `loongarch64/`).
- **`2` additional `asm!` sites in `library/core/src/num/imp/dec2flt/fpu.rs`**
  (`fstcw` / `fldcw` x87 FPU precision control on `x86` without `sse2`).

Crucially, `core::arch::x86_64::__writeeflags` (`library/stdarch/crates/core_arch/src/x86/eflags.rs:65`,
`#[stable(feature = "simd_x86", since = "1.27.0")]`) executes:

```rust
asm!("push {}", "popfq", in(reg) eflags, options(nomem, att_syntax));
```

Executing `core::arch::x86_64::__writeeflags(orig | 0x400)` followed immediately
by reading `RFLAGS` in caller Rust code (`stdarch_app.rs` in
[`support/probe_gc_tombstone_and_stdarch.py`](support/probe_gc_tombstone_and_stdarch.py))
confirms **`writeeflags_df_leaked_into_caller == true`** across all three
toolchains: `popfq` sets the x86-64 Direction Flag (`RFLAGS.DF = 1`) across the
function boundary, violating LLVM's and the System V AMD64 psABI's standing
invariant that `DF == 0` on function entry/exit (causing subsequent
compiler-emitted `rep movsb`/`rep stosb` operations to copy memory backward). Any
verifier that silently skips sysroot `core::arch` inline assembly fails to
detect or obligate caller `DF = 0` preconditions on `__writeeflags`.

#### 2.2 Dual-Query (`queries.optimized_mir` + `extern_queries.optimized_mir`) Interception and Clobber Quote Stripping

Because `libcore.rlib` is precompiled into the toolchain sysroot without
Anneal's driver, when a user crate calls `#[inline]` `stdarch` intrinsics, LLVM
inlines or monomorphizes their cross-crate MIR via `tcx.instance_mir` $\to$
**`providers.extern_queries.optimized_mir(tcx, def_id: DefId)`**, completely
bypassing `providers.queries.optimized_mir(tcx, LocalDefId)`:

| `rustc` Toolchain | `local_only` (`queries.optimized_mir`) `core` Sites | `dual_query_v2` (`queries` + `extern_queries`) Live `core` Sites | Dead `core` Sites Tombstoned | Upstream `.rmeta` Nonce Preserved (`0` Double-Wrap) | `.text` Bytes (`off` == `dual_query_v2`) | `.text` SHA-256 Prefix (`100%` Parity) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `1.98.0-nightly` | **`0 / 7`** (`0%`) | **`7 / 7`** (`100%`) | `1` | `1` (`true`) | `248,570 B` | `7f268e0262a3b09a` |
| `1.99.1` | **`0 / 7`** (`0%`) | **`7 / 7`** (`100%`) | `1` | `1` (`true`) | `238,577 B` | `7d863951110f9d0d` |
| `1.102.0-nightly` | **`0 / 7`** (`0%`) | **`7 / 7`** (`100%`) | `1` | `1` (`true`) | `239,345 B` | `5e5536281dd5b040` |

Two implementation invariants in [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs)
make dual-query interception sound and non-interfering:
1. **Idempotence & `SpecCone` snapshot isolation on `extern_queries.optimized_mir`:**
   `custom_extern_optimized_mir` first saves the un-rewritten `&'tcx Body<'tcx>`
   in `SAVED_EXTERN_MIR` (so `SpecConeCollector` hashes pure upstream MIR
   without per-session `ANNEAL_SESSION_NONCE` noise) and skips rewriting any
   body whose `InlineAsmTemplatePiece::String` already contains
   `".debug_anneal_sites"` or `".anneal.asm_sites"`—preserving an instrumented
   upstream `.rmeta` crate's own session nonce (`upstream_rmeta_nonce_preserved_records
   == 1`) with zero double-wrapping (Theorem 5,
   `local_only_query_misses_extern_stdarch_and_dual_query_complete`).
2. **Explicit-clobber `InlineAsmRegOrRegClass::Reg` quote-stripping fix:**
   Testing `riscv64` and `x86_64` explicit register clobbers (`out("ra") _`,
   `out("eax") _`, `out("ecx") _` in `__cpuid_count`) uncovered a latent bug in
   `anneal_driver_prototype.rs`: `Display` on `InlineAsmRegOrRegClass::Reg(sym)`
   formats explicit register names with literal double quotes (`"ra"`, `"eax"`),
   which breaks out of `.asciz "...|clob0="eax""` with `llvm-mc` `error:
   unexpected token`! Sanitizing `reg.to_string().replace('"', "")` in
   [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs) eliminates the
   `.asciz` breakout across all ISAs.

---

### 3. Complete `TyCtxt` Type-Graph & Pointee-Validity Closure in `SpecConeCollector` v2

`Basis: source + execution + derived`

#### 3.1 Reproducing `v1`'s `0/8` Blind Spot on Pointees, Compound Wrappers, `FnPtr` ABIs, and Foreign Statics

In `anneal_driver_prototype.rs` (`v1`), `record_type_and_layout` recursed into
constituent types **only** on `ty::Adt(adt_def, args)` (`adt_def.all_fields()`),
hashed `Place` projections only on `ProjectionElem::Field`, ignored
`GlobalAlloc::Static` metadata beyond `canonical_def_id`, and formatted
`Instance` keys via raw `{inst:?}` (`DefId(0:37 ~ ...)`). Evaluating `v1` vs.
`v2` across an expanded **23-scenario suite** (`10` original indirect-tampering
vectors `V01`..`V10`, `8` new pointee/compound/`FnPtr`/foreign-static/`NonNull`
vectors `V11`..`V18`, and `5` benign controls `C01`..`C05` in
[`support/probe_speccone_18vectors_closure.py`](support/probe_speccone_18vectors_closure.py))
shows that **`v1` misses `8/8` (`0%`) of `V11`..`V18` and triggers `1/5` false
positive (`C05`)** across all three `rustc` toolchains, whereas **`v2` detects
`18/18` (`100%`) with `0/5` (`0%`) false positives**:

| ID | Scenario (`hot_ref` Tokens 100% Identical on `V01`..`V18` & `C01`..`C03`,`C05`) | Token Hash | `SpecCone` `v1` (`Adt`-Only) | `SpecCone` `v2` (`ty.walk()` Full Closure) | Semantic Mechanism Captured by `v2` (`69` Base Types vs. `52` in `v1`) |
| :--- | :--- | :---: | :---: | :---: | :--- |
| `V01`..`V10` | Original 10 indirect vectors (callee, packed, pad mask, direct niche, `Drop`, trait default, `ConstAlloc`, `Deref`, ABI, `promoted[0]`) | `0 / 10` | `10 / 10` | **`10 / 10`** | Transitive `Instance` callgraph, direct `Adt` layout/`init_byte_mask`/`valid_range`, `Drop`, `ConstAllocation` |
| `V11` | `ref_niche: &RefBoundedByte` (`u8` $\to$ `NonZeroU8`) | Miss | **Miss** | **Detected** | `ty::Ref(_, pointee, _)` + `PlaceRef` `Deref` step (`valid_range: 1..=255` UB on `*r == 0`) |
| `V12` | `pair_slice: &[SlicePair]` (`{a: u8, b: u32}` $\to$ `+_pad: [u8; 3]`) | Miss | **Miss** | **Detected** | `ty::Ref` $\to$ `ty::Slice(elem)` (`SlicePair` `init_byte_mask`: `IUUUIIII` $\to$ `IIIIIIII`) |
| `V13` | `raw_ptr: *const RawTarget` (`#[repr(C)]` $\to$ `#[repr(C, packed)]`) | Miss | **Miss** | **Detected** | `ty::RawPtr(pointee, _)` (`RawTarget` `size: 8 -> 5`, `align: 4 -> 1`, `payload` offset `4 -> 1`) |
| `V14` | `arr_wrap: [ArrInner; 4]` (`ArrInner(u8)` $\to$ `ArrInner(NonZeroU8)`) | Miss | **Miss** | **Detected** | `ty::Array(elem, len)` + `FieldsShape::Array` element `valid_range` (`0..=255` $\to$ `1..=255`) |
| `V15` | `tup_wrap: (TupInner, u8, u8)` (`TupInner(u8)` $\to$ `TupInner(NonZeroU8)`) | Miss | **Miss** | **Detected** | `ty::Tuple(elems)` (`BackendRepr::Memory` hides element `0`'s `NonZeroU8` niche at outer tuple level!) |
| `V16` | `cb: extern "C" fn(FnArgAdt) -> u64` (`8 B` $\to$ `32 B` `FnArgAdt`) | Miss | **Miss** | **Detected** | `ty::FnPtr` + `tcx.fn_abi_of_fn_ptr` (`arg[0]` `PassMode::Direct` in `rdi` $\to$ `PassMode::Indirect` on stack) |
| `V17` | `extern "C" { static EXT_COUNTER: ExtStatVal }` (`u32` $\to$ `u64` + `#[link_name]`) | Miss | **Miss** | **Detected** | `GlobalAlloc::Static(def_id)`: `type_of`, `is_mutable_static`, `is_foreign_item`, `codegen_fn_attrs.symbol_name` |
| `V18` | `nn: NonNull<SmartTarget>` (`+_pad: [u8; 3]` + `impl Drop for SmartTarget`) | Miss | **Miss** | **Detected** | `Adt` (`NonNull`) $\to$ `NonZero<*const SmartTarget>` $\to$ `RawPtr` $\to$ `SmartTarget` `init_byte_mask` + `resolve_drop_glue` |
| `C01`..`C04` | Optimize `hot_opt` `asm!`, add module/types at EOF, 50-line shift, alpha-rename locals | `1 / 4` FP | `0 / 4` FP | **`0 / 4` FP** | Out-of-cone isolation + de Bruijn `_local` indexing + content-addressed `GlobalAlloc` sorting |
| `C05` | Insert unrelated `AboveUnrelated` struct + `above_unused_fn` *above* `hot_ref` | `0 / 1` FP | **`1 / 1` FP** | **`0 / 1` FP** | `scrub_raw_def_indices` strips HIR-order-dependent `DefId(<krate>:<idx> ~ ...)` from `Instance` & `FnDef` |

Note the subtle compiler representation hazard in `V15` (`tup_wrap: (TupInner,
u8, u8)`): because a 3-byte tuple is not a power-of-two scalar or two-element
scalar pair, `rustc_ty_utils::layout` assigns the outer tuple
`BackendRepr::Memory { sized: true }`—which carries **no top-level scalar
`valid_range` at all**! Without recursing into `ty::Tuple(elems)` (and
`layout.field(&cx, i).ty`), `TupInner`'s `NonZeroU8` niche (`1..=255`) is
completely invisible on the outer tuple's `LayoutData`.

#### 3.2 Lean `v4.34.1` Mechanization (`PostLinkGcTombstoneAndSpecConeClosure.lean`)

[`support/PostLinkGcTombstoneAndSpecConeClosure.lean`](support/PostLinkGcTombstoneAndSpecConeClosure.lean)
(`49,500 B`, `1,182` lines, `Init.*` only, `0` `sorry`, `0` `axiom` / `opaque` /
`unsafe` / `partial` / `._unsafe_rec`, synchronous compile `2.475 s`, `806`
declarations replayed onto `Init` in `270 ms` at `trustLevel := 0`) proves nine
machine-checked theorems:

1. `non_debug_gc_sections_bfd_loss_and_lld_phantom_span_unsound` *(zero axioms)*:
   Constructive proof that under `--gc-sections`, `ld.bfd` strips non-`.debug_*`
   `.anneal.asm_sites` to `[]` while `lld`/`mold` resolve dead `STT_SECTION +
   r_addend` relocations (`4`, `7`) to phantom non-empty `[0x4, 0x7)` spans.
2. `postlink_debug_tombstone_filter_sound_and_complete` *(`[propext,
   Classical.choice, Quot.sound]`)*: Universal soundness and completeness of
   `acceptDebugSiteRecord` across all three DWARF tombstone encodings (`0`, `1`,
   `UINT64_MAX`) and arbitrary `R_RISCV_RELAX` byte-shrinking `SectionAtom`
   streams (`WellPlacedExecSegments`).
3. `unannotated_icf_leader_absorbs_debug_record_unless_sym_gated` *(zero axioms)*:
   Constructive witness that `--icf=all` folding of an attested section onto an
   earlier unannotated leader zeroes the follower's `.debug_anneal_sites` record
   (`[]`), caught deterministically by `verifyLiveAsmSymbolCoverage = false`
   while verified-twin folding passes (`= true`).
4. `gc_relax_icf_postlink_composition_sound` *(`[propext, Quot.sound]`)*:
   Universal post-link composition theorem across `--gc-sections` ×
   `R_RISCV_RELAX` × `--icf=all`: when `filterDebugSiteRecords` passes
   `verifyPostLinkSlice` and `verifyLiveAsmSymbolCoverage`, every live `PT_LOAD_X`
   `ManifestAsmFn` executes an authorized post-relaxation byte slice satisfying
   `AddressObliviousSiteSound` and zero tombstoned dead records are admitted.
5. `local_only_query_misses_extern_stdarch_and_dual_query_complete` *(zero axioms)*:
   Proves `LocalDefId`-only `optimized_mir` misses sysroot `stdarch`
   `__writeeflags` (`setDirectionFlagDF`), whereas `rewriteDualQueriesIdempotent`
   wraps `100%` of local, sysroot `stdarch`, and upstream `.rmeta` items with
   exact `wrapCount = 1` and flags `__writeeflags`.
6. `ref_pointee_niche_omission_unsound` *(`[propext, Quot.sound]`)*:
   Constructive refutation showing `AdtOnlyConeEq` misses `Ty.sharedRef (.adt 1)`
   (`&BoundedByte(NonZeroU8)` $\to$ `&BoundedByte(u8)`), breaking
   `TotalMirAsmEquiv` when `opt` traps on `*r = 0`.
7. `compound_tuple3_fnptr_and_extern_static_omission_unsound` *(`[propext,
   Quot.sound]`)*: Three-part constructive refutation for `Ty.tuple3`
   `BackendRepr::Memory` element niches (`V15`), `Ty.fnPtr` `PassMode` ABI
   changes (`V16`), and `extern "C" { static ... }` `#[link_name]` rebinding
   (`V17`).
8. `evalMir_wellClosedTypeGraph_noninterference` *(`[propext]`)*: Step-indexed
   `evalMirV2` operational non-interference under `WellClosedSpecCone` and
   `WellClosedSpecConeEq` (invariant to out-of-cone definitions and `rawAllocIds`).
9. `wellClosedSpecConeEq_preserves_totalMirAsmEquiv` *(`[propext]`)*: Relational
   transfer theorem proving `WellClosedSpecCone p1 cone rootFn ->
   WellClosedSpecConeEq p1 p2 cone -> TotalMirAsmEquiv fuel p1 rootFn opt ->
   TotalMirAsmEquiv fuel p2 rootFn opt`.

## Boundaries

- **Non-ELF object formats (`known not to apply`):** `.debug_anneal_sites` relies
  on ELF non-`SHF_ALLOC` `.debug_*` GC-root preservation and DWARF tombstone
  relocation rules (`ld.bfd`, `lld/ELF`, `mold`). Mach-O (`ld64` / `lld-macho`
  `__DWARF` segment rules) and COFF/PE (`link.exe` / `lld-link` `IMAGE_SCN_MEM_DISCARDABLE`)
  require separate format-specific section attributes and were **not examined**.
- **Executable `PT_LOAD` mapped at virtual address `0x0` or `0x1` (`unsupported`
  without custom tombstone override):** `WellPlacedExecSegments` requires
  executable `PT_LOAD` (`PF_X`) segments to lie in `[0x1000, UINT64_MAX)`.
  Bare-metal embedded linker scripts that map `.text` at VA `0x0` collide with
  the default `(0x0, 0x0)` DWARF tombstone on `lld`/`ld.bfd`/`mold`; such targets
  must pass `-Wl,-z,dead-reloc-in-nonalloc=.debug_anneal_sites=0xffffffffffffffff`
  (verified on `rust-lld 23.1.5`) and restrict `isDwarfTombstone` to
  `UINT64_MAX`.
- **`strip --strip-debug` / `-C strip=debuginfo` ordering (`known not to
  apply` if stripped before audit):** Because `.debug_anneal_*` intentionally
  uses the `.debug_` prefix to inherit ELF linker GC-root and DWARF tombstone
  semantics, running `strip --strip-debug` or passing `-C strip=debuginfo` *at
  link time* removes `.debug_anneal_sites` before the post-link verifier runs.
  Post-link verification must run on the unstripped linker output first, after
  which `llvm-objcopy --remove-section=.debug_anneal_sites --remove-section=.debug_anneal_descs`
  (or `strip --strip-debug`) produces the stripped deployment binary.
- **Precompiled C/assembly archives (`libfoo.a`) and sysroot `.o` intrinsics
  without MIR (`unsupported` by `extern_queries.optimized_mir`):** Dual-query MIR
  interception covers `100%` of Rust functions with serialized MIR in `.rlib` /
  `.rmeta` metadata (including all `197` `#[inline]` `core_arch` `stdarch`
  intrinsics and `dec2flt::fpu`). Non-inlined `#[inline(never)]` functions in
  prebuilt sysroot `.rlib` objects, `global_asm!`, and foreign C/S static
  archives have no MIR body to rewrite and remain subject to object-level symbol
  and section audits (`verifyLiveAsmSymbolCoverage` catches ICF collisions
  between unannotated C objects and attested Rust `asm!` functions).
- **Dynamic trait-object (`dyn Trait`) open-world dispatch and foreign `extern`
  static contents (`known not to apply` without whole-program closure):**
  `SpecConeCollector` v2 hashes `ty::Dynamic` existential predicate bounds and
  foreign `extern "C" { static ... }` symbol names, types, and mutability, but a
  per-function cone cannot predict concrete vtable implementations constructed
  by arbitrary unknown callers or external C initializer bytes linked later
  (Theorem 7c models `p1.externSymbolVals = p2.externSymbolVals` as an explicit
  link-environment hypothesis).

## Evidence

### Preserved Package Artifacts (`support/`)

| Relative Path | Size | SHA-256 | Role |
| :--- | :---: | :--- | :--- |
| [`support/anneal_driver_v2.rs`](support/anneal_driver_v2.rs) | `74,817 B` | `ce0ac577921bd6cbeaef4b820d469f42d16ffc6d5c3de24d8117c2cbb84dfbe6` | Standalone `rustc_driver` v2: `.debug_anneal_sites` / `.debug_anneal_descs` emission, `queries` + `extern_queries` `optimized_mir` hook, clobber quote sanitization, rewritten-site manifest, and `SpecConeCollector` v2 (`ty.walk()`, `fn_abi_of_fn_ptr`, `PlaceRef::ty`, `GlobalAlloc::Static`, `DefIndex` scrubbing) |
| [`support/PostLinkGcTombstoneAndSpecConeClosure.lean`](support/PostLinkGcTombstoneAndSpecConeClosure.lean) | `49,500 B` | `458a3fad244f66ad7ae4198de09ddeae78e086f0d525d6a334adeaccd0e046c9` | Self-contained `Init.*`-only Lean `v4.34.1` mechanization of all `9` soundness, composition, and counterexample theorems (`0` `sorry`, `0` `_unsafe_rec`) |
| [`support/probe_gc_tombstone_and_stdarch.py`](support/probe_gc_tombstone_and_stdarch.py) | `47,080 B` | `919dcf1184898881a6bbaba57c988ca418ef85580d02ac2b708998d6d76c4a5a` | End-to-end probe reproducing the 5-linker × 3-ISA `--gc-sections` fracture, `SHF_LINK_ORDER` failures, `27/27` LTO `.text` parity, `riscv64gc` `--gc-sections` + `+relax` + `--icf=all` composition + unannotated ICF leader hazard, `197`-site `stdarch` census, `__writeeflags` `DF` leak, and `7/7` dual-query capture |
| [`support/probe_speccone_18vectors_closure.py`](support/probe_speccone_18vectors_closure.py) | `21,036 B` | `01429da8f11f119edf90647ae8329996ce4442d8e97a3298e643be0ad02761af` | 23-scenario (`18` indirect-tampering + `5` benign-control) benchmark comparing token hashing, `SpecCone` `v1` (`10/18`, `1/5` FP), and `SpecCone` `v2` (`18/18`, `0/5` FP) across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly` |
| [`support/probe_1_2_gc_stdarch_results.json`](support/probe_1_2_gc_stdarch_results.json) | `58,966 B` | `d9320f55dddcd04d7345be040a174b48cf2fe7e85fa772603d8d4ff6063196b0` | Recorded JSON output of `probe_gc_tombstone_and_stdarch.py` (`observed_at = 2026-11-21`) |
| [`support/probe_3_speccone_18vectors_results.json`](support/probe_3_speccone_18vectors_results.json) | `30,448 B` | `fde9881f6169edde90bf579b99acada8938f11307ef5a0112c9c58438db1b24e` | Recorded JSON output of `probe_speccone_18vectors_closure.py` (`observed_at = 2026-11-21`) |

### Primary Upstream Source Coordinates

- **`rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67` / `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):**
  - `compiler/rustc_middle/src/query/mod.rs`: `optimized_mir` query (`LocalDefId`
    `queries.optimized_mir` vs. cross-crate `DefId` `extern_queries.optimized_mir`).
  - `compiler/rustc_codegen_llvm/src/asm.rs:88-126, 189-199`: `InlineAsmOperand`
    lowering (`$` $\to$ `$$` template escaping; explicit-register clobbers).
  - `library/stdarch/crates/core_arch/src/x86/eflags.rs:51-70`: `__writeeflags`
    (`asm!("push {}", "popfq", in(reg) eflags, options(nomem, att_syntax))`
    without restoring `RFLAGS.DF`).
  - `compiler/rustc_middle/src/ty/walk.rs`: `TypeVisitableExt::walk` preorder
    generic-argument / constituent-type iterator used by `SpecConeCollector` v2.
- **`rust-lang/llvm-project` (`0a5579eb649d3634a9c30ac873300cc2944fa070`):**
  - `lld/ELF/MarkLive.cpp` and `lld/ELF/InputSection.cpp` (`relocateNonAlloc`,
    `getRelocTargetVA`): non-`SHF_ALLOC` section retention under `--gc-sections`
    and `!isDebug` (`0 + r_addend`) vs. `isDebug` (`0x0` / `deadRelocInNonAlloc`
    DWARF tombstone) dead-target relocation resolution, including ICF-folded
    (`!sec->isLive()`) sections.
  - `llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149` and
    `llvm/lib/MC/MCParser/AsmLexer.cpp:313, 898-906`: `getInlineAsmLength` vs.
    `AsmLexer` `\r` + `.space 0 <cmt>` zero-drift invariant.
- **GNU Binutils `2.47` (`bfd/elflink.c` `_bfd_elf_gc_mark_extra_sections`):**
  Preserves non-`SHF_ALLOC` sections under `--gc-sections` when `SEC_DEBUGGING`
  (`.debug*` / `.zdebug*`) is set and sweeps `.anneal.asm_sites` to `0` bytes.
- **RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc@56561cb3e7330fe99a98fd27457229707b2786ae`):**
  `R_RISCV_ADD64` (`35`) / `R_RISCV_SUB64` (`39`) label-difference relocation
  pairs under `R_RISCV_RELAX` (`51`).

## Revalidation

Run the following three self-contained commands from a temporary working
directory (requiring `rustup` toolchains `nightly-2026-06-01`, `1.99.1`,
`nightly`, and `nightly-2026-01-25` with `aarch64-unknown-linux-gnu` and
`riscv64gc-unknown-linux-gnu` targets, `ld.bfd`, `ld.mold`, `llvm-mc-21`,
`llvm-objcopy-21`, `qemu-riscv64`, and Lean `v4.34.1`):

1. **Revalidate `--gc-sections` tombstones, `SHF_LINK_ORDER`, 27/27 LTO parity,
   `riscv64gc` `--gc-sections` + `+relax` + `--icf=all`, and `stdarch`
   `extern_queries.optimized_mir` (`~45 s`):**
   ```bash
   python3 -B support/probe_gc_tombstone_and_stdarch.py --out /tmp/reval_1_2.json
   ```
   Exits `0` only if `ld.bfd` strips `.anneal.asm_sites` to `0 B`, `lld`/`mold`
   tombstone `.debug_anneal_sites` dead spans to `(0x0, 0x0)`, all `27/27` LTO
   cells achieve exact `.text` SHA-256 parity, `qemu-riscv64` exits `0` on the
   ICF+relaxed binary, `verifyLiveAsmSymbolCoverage` catches unannotated ICF
   absorption, and `dual_query_v2` captures `7/7` `stdarch` `asm!` expansions
   with `0 B` `.text` drift.

2. **Revalidate `SpecConeCollector` v2 across all `18` indirect-tampering
   vectors and `5` benign controls (`~40 s`):**
   ```bash
   python3 -B support/probe_speccone_18vectors_closure.py --out /tmp/reval_3.json
   ```
   Exits `0` only if `v2_total_detected_18 == 18` and
   `v2_benign_false_positives_5 == 0` across all three `rustc` toolchains.

3. **Revalidate synchronous Lean `v4.34.1` compilation and `trustLevel := 0`
   kernel replay (`~3 s`):**
   ```bash
   python3 -B -c '
   import shutil, subprocess, tempfile
   from pathlib import Path
   src = Path("support/PostLinkGcTombstoneAndSpecConeClosure.lean").resolve()
   with tempfile.TemporaryDirectory() as td:
       shutil.copy2(src, Path(td) / src.name)
       subprocess.run([
           "elan", "run", "leanprover/lean4:v4.34.1", "lean",
           "-DElab.async=false", "-Ddebug.skipKernelTC=false",
           "-DwarningAsError=true", src.name, "-o", "out.olean"
       ], cwd=td, check=True)
   '
   ```
   Confirm `rc = 0` and verify in `#print axioms` output that all nine theorems
   depend solely on subsets of `{propext, Classical.choice, Quot.sound}` with
   zero `sorryAx`.
