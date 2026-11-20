# Vertical Seam Composition and ELF `DT_RUNPATH` TCB Closure for a Verified `rustc` Pipeline

## Summary

Per-layer compiler verification artifacts—scalar MIR normalization over `Trusted.MirSemantics`, Tree Borrows partial SROA, `x86-64` backend stack-probe/`vzeroupper`/CFI checking, and external dual-kernel proof checking—compose soundly **only when explicit cross-layer coupling contracts are enforced at all five vertical seams (`V1`–`V5`)**. Composing the uncoupled single-stage checks from `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` silently breaks soundness under realistic compiler upgrades, ABI transitions, AVX-512 codegen, red-zone flags, and dynamic-linker layouts—even when every local stage check returns `true` (`cex_v5_locally_valid_stages_fail_when_composed_without_seam_couplings`, `Basis: Lean kernel check [toy model]`).

Five principal results govern vertical integration across the verified `rustc` stack:

1. **Live P0 TCB Vulnerability in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`V4`, `Basis: source + execution`):** `trusted/audit/src/lib.rs:2468-2508` hashes only the `9,024`-byte `bin/lean` launcher (`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`) and never authenticates the `233,708,536`-byte `lib/lean/libleanshared.so` that contains the actual Lean 4 elaborator and C++ kernel. Live `readelf -d bin/lean` inspection reveals a **second bypass that defeats even a naive fixed-path patch**: `bin/lean` sets `DT_RUNPATH = [$ORIGIN/../lib:$ORIGIN/../lib/lean]`, and `<prefix>/lib/` exists yet contains **no** `libleanshared*.so` or `libInit_shared.so`. Dropping a trojan `libleanshared.so` into `<prefix>/lib/` hijacks dynamic linking inside `ld-linux-x86-64.so.2` even when `anneal-audit` scrubs `LD_PRELOAD`/`LD_LIBRARY_PATH` (`env_clear()` at `lib.rs:1973`) and even if a patch hashes `<prefix>/lib/lean/libleanshared.so` at its fixed path. Closing the TCB requires ordered `DT_RUNPATH` + `DT_NEEDED` ELF closure verification paired with statement-hash-pinned `lean4export` + statically linked `nanoda_bin` dual-kernel checking.
2. **MIR Normalization × `Const::Unevaluated` Cone × `WithRetag` Release Drift (`V1`, `Basis: source + execution + Lean kernel check [toy model]`):** Keying incremental MIR proof caches on span-stripped `Runtime(PostCleanup)` body syntax misses external `Const::Unevaluated` mutations (`miniz_oxide 0.9.1` `BASE_EXTRA_MASK` leaves callers byte-identical while changing runtime behavior) and cross-release semantic shifts (`rustc 1.96.0 -> 1.99.0` removed `StatementKind::Retag` in `e402c1edf047a23b0cfef40c6097d1caa294050b`, introducing implicit `WithRetag::Yes` on copies and rewriting `124/641` (`19.34%`) of `memchr 2.8.3` bodies with `no_retag copy`). Uncertified `MoveToCopy` additionally turns `UseAfterMove` UB into silent value reuse. Sound caching binds `(stmts, evalConstCone(constConeIds), rustcRelease, specHash)` alongside a static no-use-after-move / storage certificate.
3. **Partial SROA × Multi-Target `FnAbi` Drift × `UnsafeCell`/`Atomic<T>` `readonly` Hazards (`V2`, `Basis: source + execution + Lean kernel check [toy model]`):** Across `9` targets × `3` `rustc` releases (`1.99.1`, `1.100.0`, `1.102.0-nightly`), `78/833` (`9.36%`) IR-level ABI drifts split into `55/833` (`6.60%`) real `.o`/calling-convention breaks, including staggered x86-vs-AArch64 `#[repr(simd)]` divergence at `1.100.0`, Win64 non-`#[repr(C)]` ZST argument-register shifts, and `4/27` `vectorcall` `.o` linker breaks (`abi_vec_hfa4@@16 -> @@24`). Composing `Indirect` hidden-pointer lowering with Partial SROA and `Atomic<T>` (`rustc 1.94.0 -> 1.96.0`, `fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`) requires release/target/ABI epoch pinning, `Freeze` (`!hasUnsafeCell`) gating before attaching LLVM `readonly`, and mandatory SROA write-through flushing before indirect stack copies.
4. **AVX-512 `ZMM512` Guard-Page Cliff × EVEX `vzeroupper` × `-C no-redzone=yes` `SeqCst` Fences (`V3`, `Basis: execution + Lean kernel check [toy model]`):** Disabling `prefer-256-bit` under `x86-64-v4` doubles full-register SIMD spill size (`32 × 32 B = 1,024 B` YMM -> `32 × 64 B = 2,048 B` ZMM), pushing a sub-page `3,136 B` frame across the `4,096 B` guard-page cliff to `4,160 B`. Meanwhile `rustc 1.99.1`/`1.100.0`/`1.102.0-nightly` at `-O3` on `x86_64-unknown-linux-gnu` lower `fence(Ordering::SeqCst)` to `lock orl $0, -64(%rsp)` by default and `lock orl $0, (%rsp)` under `-C no-redzone=yes`. Emitting `-64(%rsp)` under `-C no-redzone=yes`, Win64, kernel targets, or inside a leaf calling a `16 B`-aligned outlined throwing thunk causes red-zone corruption, whereas `(%rsp)` preserves the top-of-stack slot identically across both modes (proved with **zero axioms `[]`**).
5. **Constructive End-to-End Composition & Adversarial Ablation (`V5`, `Basis: Lean kernel check [toy model]`):** All five seams are mechanized in [`support/VerticalSeamComposition.lean`](support/VerticalSeamComposition.lean) (`2,109` lines, `93,914` bytes, SHA-256 `af3f1f3afbbe3c9841dd5aa7fcc0a0d4172390af720b43e999dfc8f3753dd4eb`), containing **`27` total theorems** (`17` public + `10` private), synchronously kernel-checked under `Lean v4.34.1` (`-DElab.async=false -Ddebug.skipKernelTC=false`) in `6.247 s` (`558.95 MB` peak RSS) with `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `omega`, `0` `bv_decide`, `0` `partial`, `0` `._unsafe_rec`, and `0` `Trusted` namespace declarations.

## Applicability

These findings synthesize and couple five verification layers across concrete upstream revisions observed on `2026-11-20` on `x86_64-unknown-linux-gnu`:

- **Anneal TCB & MIR Capture Baseline (`Basis: source`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, specifically `trusted/audit/src/lib.rs`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs`.
- **Lean 4 & External Proof-Checker Toolchains (`Basis: source + execution`):**
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu` release binaries inspected with `readelf -d`, `stat`, and `sha256sum`, and executed synchronously to verify `support/VerticalSeamComposition.lean`).
  - `leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (`v4.35.0`), `leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe` (`format 3.1.0`), and `ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (`nanoda_bin 0.4.19`) for dual-kernel external checking measurements.
- **`rustc` Cross-Release & Multi-Target Empirical Span (`Basis: execution + source`):** Official `rustc` releases `1.94.0` (`4a4ef493e3a1488c6e321570238084b38948f6db`), `1.96.0` (`ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96`), `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, pinned in `driver.rs:25`), `1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `LLVM 23.1.1`), `2026-10-20` nightly (`8144389c895da997dbdecaa635e41d6a50be6ffd`, cited in `MirAst.lean:511`), `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`, `LLVM 23.1.5`), and `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `LLVM 23.1.5`), plus `rust-lang/miri@7e679961edcfe2c526f19153bb8b03de346efa5c` and real crates `miniz_oxide 0.9.1`, `serde_json 1.0.154`, and `memchr 2.8.3`.
- **Companion Corpus Reports Synthesized (`google/zerocopy` `refs/heads/reference`):**
  - Scalar MIR normalization over `Trusted.MirSemantics`: [`anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge`](../anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/REPORT.md) (`6e24ad128d7f29afc0f47733eb42ec4d3392ba63`)
  - Tree Borrows partial SROA & store sinking: [`tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption`](../tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption/REPORT.md) (`14176bbedd11ec1e98b5ab732562d3c2d91c4551`)
  - Surgical-edit MIR invalidation & `Const::Unevaluated` cones: [`rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius`](../rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius/REPORT.md) (`4e59b26602689aaf0b4dd0d46cad3a90cf7d6ef9`)
  - Seven-release `PostCleanup` MIR drift: [`rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility`](../rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility/REPORT.md) (`7ac36b3ef5b297b1c69f44025f4f8464b524f26b`)
  - `9`-target × `3`-release `FnAbi` drift matrix: [`rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`](../rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting/REPORT.md) (`120889696dc131f0fc7cf814e898ee72cd04a19e`)
  - AVX-512 silicon & `prefer-256-bit` vectorization: [`rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality`](../rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality/REPORT.md) (`ce80a654ab246bd6ab7e274171c9540dbb352e07`)
  - Coupled backend seam (`vzeroupper`, probes, CFI, `16 B` thunks): [`coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi`](../coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi/REPORT.md) (`b31e6312edc1c6ef2ca8e2dbd528c856f36d131f`)
  - Bootstrapping & `libleanshared.so` TCB audit gap: [`compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain`](../compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain/REPORT.md) (`7176fdd92a14672f169ef6809c04924c70ac3e5e`)
  - External Lean 4 checkers (`nanoda_bin`, `lean4export`): [`lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb`](../lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb/REPORT.md) (`e1d84aa8ef0cc7635845be021c54d3d7418c89c6`)
  - Proof-checker trust layers & statement pinning: [`proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`](../proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings/REPORT.md) (`fb407b1d31432ebe8e4d97fcc95717e8193c0c28`)
- **Formal Scope Qualification (`[toy model]`):** `support/VerticalSeamComposition.lean` formalizes stylized operational transition systems over fixed finite MIR, ABI, backend-frame, and ELF-resolution schemas rather than full `rustc`, LLVM, `x86-64`, or `glibc` `ld.so` semantics. Its theorems establish exact mathematical couplings and counterexamples inside that transition model; empirical measurements establish that every modeled hazard occurs on real upstream binaries and toolchains.

## Findings

### Master Vertical Seam Composition Summary (`V1`–`V5`)

`Basis: source + execution + Lean kernel check [toy model]`

| Seam | Coupled Verification Layers | Exact Breakage When Uncoupled | Minimal Required Coupling Guard | Formal & Empirical Anchors |
| :--- | :--- | :--- | :--- | :--- |
| **V1** | `Trusted.MirSemantics` (`deinitMovedPlace = true`) × `Const::Unevaluated` cache × `no_retag copy` MIR drift | Function MIR text stays identical while an external `const` changes (`miniz_oxide` `BASE_EXTRA_MASK`), or `rustc 1.96.0 -> 1.99.0` injects implicit `WithRetag::Yes` on copies (`memchr` `19.50%` drift), or uncertified `MoveToCopy` masks `UseAfterMove` UB. | Cache key binds `(stmts, evalConstCone(constConeIds), rustcRelease, specHash)` + mandatory no-use-after-move / storage certificate (`checkMirV1Cert`). | `v1_const_cone_and_profile_cache_preserves_semantics`, `v1_certified_f11b_norm_preserves_eval`, `cex_v1a_*`, `cex_v1b_*` (`Lean kernel check [toy model]`); `miniz_oxide`, `serde_json`, `memchr` (`execution`) |
| **V2** | Tree Borrows Partial SROA × Multi-target/multi-release `FnAbi` drift × `Atomic<T>` / `UnsafeCell` lowering | Cross-release (`1.99.1 -> 1.100.0 -> 1.102.0-nightly`) or x86-vs-AArch64 ABI skew misaligns registers (`sret <-> xmm0`, Win64 ZST `%rcx` shift, `vectorcall @@16 -> @@24`); `Indirect` hidden pointer with erroneous LLVM `readonly` triggers UB on `Atomic<T>`/`UnsafeCell`; unflushed Partial SROA reads stale caller memory. | Same `(RustcRelease, TargetTriple, CallConv)` ABI descriptor pinning + `!isIndirectReadonly` when `UnsafeCell`/atomic write is possible (`Freeze` check) + mandatory SROA write-through flush before `Indirect` copy. | `v2_epoch_pinned_freeze_aware_abi_call_sound`, `cex_v2a_*`, `cex_v2b_*` (`Lean kernel check [toy model]`); `78/833` IR / `55/833` `.o` ABI breaks (`execution`) |
| **V3** | AVX-512 `ZMM512` vs `prefer-256-bit` × `vzeroupper`/stack-probe/CFA × `-C no-redzone=yes` `SeqCst` fence | Spilling `32` `ZMM` regs pushes sub-page frames (`3,136 B -> 4,160 B`) across the `4,096 B` guard-page cliff; missing `vzeroupper` leaks dirty `ZMM[511:128]` lanes at legacy/unwind boundaries; `lock orl $0, -64(%rsp)` corrupts `-C no-redzone=yes`, Win64, kernel stacks, or `16 B` outlined-thunk frames. | Target-coupled red-zone gate (`targetAllowsRedZone`) forcing `dispZeroRsp` `(%rsp)` under `.noRedZone` or outlined calls + `spShift = 16` thunk CFA parity + exact `4,096 B` step probe check + EVEX-wide `vzeroupper` discipline. | `v3_backend_zmm512_probe_vzeroupper_redzone_sound`, `v3_noredzone_rejects_neg64_and_admits_zeroRsp`, `cex_v3a_*`, `cex_v3b_*` (`Lean kernel check [toy model]`); Xeon AVX-512 & `rustc` `-O3` asm (`execution`) |
| **V4** | `joshlf/anneal@c131b320e` `bin/lean`-only hashing × `DT_RUNPATH` precedence × `nanoda_bin 0.4.19` + statement-hash pinning | `trusted/audit/src/lib.rs:2468-2508` hashes only `9,024 B` `bin/lean`; **even a naive patch hashing `lib/lean/libleanshared.so` is bypassable** because `bin/lean` sets `DT_RUNPATH = [$ORIGIN/../lib:$ORIGIN/../lib/lean]` and `<prefix>/lib/` has no `libleanshared*.so` (`$ORIGIN/../lib` shadows `lib/lean/`). Unpinned `lean4export` lets an exporter substitute a trivial theorem. | Hash transitive `DT_NEEDED` ELF closure across ordered `DT_RUNPATH` rejecting shadow hits in `$ORIGIN/../lib` + statically linked `nanoda_bin` acceptance with choice-axiom gate + cryptographic pin on exported target statement hash. | `v4_closed_tcb_and_pinned_dual_kernel_sound`, `cex_v4a_*`, `cex_v4b_*` (`Lean kernel check [toy model]`); live `readelf -d`/`sha256sum` on Lean `v4.34.1`, `nanoda_bin 0.4.19` (`source + execution`) |
| **V5** | End-to-end composition of `V1`–`V4` | Four locally green stage checks compose into immediate runtime panic (`V1`), ABI fault/UB (`V2`), guard-page/red-zone fault (`V3`), and trojanized TCB acceptance (`V4`). | Unified conjunctive gate `checkVerticalPipeline` binding `V1` `soundV1CacheKey` + `checkMirV1Cert` -> `V2` epoch/`Freeze`/SROA check -> `V3` `targetAllowsRedZone` + `checkBackendV3` -> `V4` closed ELF + pinned dual-kernel audit. | `v5_unified_vertical_seam_composition_sound`, `witness_v5_*`, `cex_v5_*` (`Lean kernel check [toy model]`) |

---

### 1. Seam `V1`: Scalar MIR Normalization, `Const::Unevaluated` Cones, and Cross-Release `WithRetag` Drift

`Basis: source + execution + Lean kernel check [toy model]`

#### 1.1 Empirical Collision at the Source-to-MIR-to-Proof Boundary

Three independently established properties collide when verification proofs are normalized and cached incrementally across compiler releases:

1. **Certified Scalar Normalization Over `Trusted.MirSemantics` (`Basis: source`):** In [`anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge`](../anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/REPORT.md) (`6e24ad128d7f29afc0f47733eb42ec4d3392ba63`, `6,489` lines, `19` public theorems, `[propext]` only, checked by `nanoda_bin 0.4.19` across `1,795` decls in `0.889 s` / `34.29 MB`), bidirectional operational equivalence (`vc_transport_moveToCopy_certified_iff`, `vc_transport_removeStorageMarkers_certified_iff`) over `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`'s `Trusted.MirSemantics` (`deinitMovedPlace = true`, `maxDepth = 0`) holds strictly for scalar / fieldless-enum / non-calling MIR bodies certified by `checkNoUseAfterMoveProgram` and `checkStorageSafeProgram`. Without that static dataflow certificate, rewriting `move` to `copy` turns `.useAfterMoveUb` into silent value reuse. Meanwhile, `joshlf/anneal@c131b320e` `trusted/lean/Trusted/MirAst.lean:504-506` defines `ConstLit` solely as:
   ```lean
   inductive ConstLit where
     | scalar (bits : BitVec 128)
     | zeroSized
   ```
   lowering pointer, slice, and indirect constants to `.unsupported`.
2. **`Const::Unevaluated` Incremental Cutoff Blind Spot (`Basis: execution`):** In [`rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius`](../rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius/REPORT.md) (`4e59b26602689aaf0b4dd0d46cad3a90cf7d6ef9`), mutating `const BASE_EXTRA_MASK: usize = 32 - 1` -> `16 - 1` in `miniz_oxide 0.9.1` (`358` `PostCleanup` items, `280` `PreCodegen` items, `38` `-O3` `cgu=1` functions) yields `span_stripped_changed_count = 1` (`inflate::core::BASE_EXTRA_MASK` alone) in `Runtime(PostCleanup)` MIR. Both consumers (`inflate::core::decompress_fast` and `inflate::core::decompress_with_limit`) remain **byte-identical** in `PostCleanup` MIR because expression-position `const` operands stay `Const::Unevaluated`. Extending provenance tracking to the transitive `Const::Unevaluated` cone raises changed MIR items to `3` and `-O3` LLVM changed functions to `2` (`cgu=1` and `cgu=16` alloc-erased; `3.999x` incremental speedup with `13/16` `.o`s reused). In `serde_json 1.0.154` (`1,105` `PostCleanup` items, `184` `cgu=1` / `271` `cgu=16` `-O3` functions), editing pattern-position `const BB` mutates `1` MIR cone item (`ser::format_escaped_str_contents`) and `2` `cgu=1` / `12` `cgu=16` `-O3` functions. Conversely, a pure comment-line shift in `miniz_oxide` mutates `80` raw source spans with `0` span-stripped MIR semantic diffs, showing raw span-sensitive MIR hashing causes spurious invalidation.
3. **Cross-Release `WithRetag` Drift and Internal `joshlf/anneal` Pin Skew (`Basis: source + execution`):**
   - *Five-month internal pin skew in `joshlf/anneal@c131b320e`:* `trusted/rustc-capture/src/driver.rs:25` locks `COMPILER_VERSION = "1.98.0-nightly (f8a08b688 2026-05-30)"` (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), lagging five months behind `trusted/lean/Trusted/MirAst.lean:510-511`, which cites `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`2026-10-20` nightly). Four upstream `rustc_middle::mir::syntax` mutations landed across that interval (`+AssertKind::NullReferenceConstructed`, `+CastKind::BoxDerefTransmute`, `+ProjectionElem::PhantomDeref`, and `TerminatorKind::Goto { loop_hint_attrs }`).
   - *`rustc 1.96.0 -> 1.99.0` retagging break:* In `rust-lang/rust@e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`), `rustc` removed `StatementKind::Retag`, turning `Rvalue::Use(Operand, WithRetag::Yes)` into an implicit retag and emitting explicit `no_retag copy` (`WithRetag::No`) for projected references. As measured in [`rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility`](../rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility/REPORT.md) (`7ac36b3ef5b297b1c69f44025f4f8464b524f26b`), `memchr 2.8.3` exhibited `125/641` (`19.50%`) span-stripped semantic MIR diffs across `1.96.0 -> 1.99.0` (`124/641 = 19.34%` from `no_retag copy` normalization alone), whereas pure arithmetic crates such as `ryu 1.0.23` showed `0/45` across all seven releases and `itoa 1.0.19` showed `1/59` (`1.69%`) at `1.99.1 -> 1.100.0`.

#### 1.2 Mechanized Seam `V1` Coupling & Counterexamples (`support/VerticalSeamComposition.lean`, Section 1)

`Basis: Lean kernel check [toy model]`

- **Failure `V1a` (Stale Cache Hit Across Mutated `Const::Unevaluated`):** Keying a verification cache on `NaiveBodyKey := { stmts, specHash }` collides when `cenvMask15` (`cid 7 = 15`) changes to `cenvMask31` (`cid 7 = 31`). In `bodyMinizMaskProbe`, input `16#64` masked with `15` indexes LUT slot `0` cleanly (`.ok 0#64`), whereas mutating `const cid=7` to `31` computes `16 &&& 31 = 16 >= 16` and traps with `.error .oobPanic` while `naiveBodyOnlyKey` stays equal (`cex_v1a_unevaluated_const_change_breaks_uncached_cone`, `L983`, `[propext, Quot.sound]`).
- **Failure `V1b` (`1.96.0 -> 1.99.1` `WithRetag` Drift × Uncertified `MoveToCopy`):**
  1. On a projected `&mut` copy (`bodyRefProjWithoutNoRetag`), `r1_96_0` evaluates `useRefAssign` without automatic child retagging (`.ok 77#64` after a parent write), whereas `r1_99_1` interprets non-`no_retag` copy as `WithRetag::Yes`, creating a child tag in `BorrowCell` whose permission is disabled (`.error .tbUb`) when parent tag `0` writes `77#64`. Explicit `noRetag = true` (`bodyRefProjWithNoRetag`) restores `.ok 77#64`.
  2. On `bodyScalarUseAfterMove`, uncertified `MoveToCopy` turns `move _1; copy _1` from `.error .useAfterMoveUb` into `.ok 9#64`, which `checkMirV1Cert` rejects (`false`) (`cex_v1b_rustc_196_to_199_retag_drift_and_movetocopy_ub`, `L1038`, `[propext, Quot.sound]`).
- **Sound Seam `V1` Theorems:**
  - `v1_const_cone_and_profile_cache_preserves_semantics` (`L521`, `[propext, Quot.sound]`): Equal `soundV1CacheKey cenv rel body` across cached/live environments under `stmtsInCone body.constConeIds body.stmts` guarantees identical `evalMirBody`.
  - `v1_certified_f11b_norm_preserves_eval` (`L914`, `[propext, Quot.sound]`): Under `isScalarPureStmts body.stmts` and `checkMirV1Cert body = true`, `normalizeF11b` (`applyRemoveStorageProg ∘ applyMoveToCopyProg`) preserves exact `evalMirBody` across both `.ok` values and `.error` outcomes.

---

### 2. Seam `V2`: Tree Borrows Partial SROA, Multi-Target `FnAbi` Drift, and `UnsafeCell`/`Atomic<T>` `readonly` Hazards

`Basis: source + execution + Lean kernel check [toy model]`

#### 2.1 Empirical ABI Drift & Partial-SROA Indirect-Copy Tension

1. **Multi-Target / Multi-Release `FnAbi` Drift Matrix (`Basis: execution`):** As measured in [`rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`](../rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting/REPORT.md) (`120889696dc131f0fc7cf814e898ee72cd04a19e`), compiling an ABI corpus across `9` targets × `3` `rustc` releases (`1.99.1`, `1.100.0`, `1.102.0-nightly` = `2,499` compiled functions, `833` comparison pairs per transition) produced **`78/833` (`9.36%`) IR-level ABI drifts**, comprising **`55/833` (`6.60%`) real `.o`/calling-convention breaks** and **`23/833` IR-only symbol-decoration shifts**:
   - *`1.99.1 -> 1.100.0` (`30` drifts across `x86_64-{linux,darwin,win-msvc,win-gnu}` and `i686-{linux,win-msvc}`):* `#[repr(simd)]` aggregates (`abi_rust_simd_f32x4`, `abi_rust_simd_f32x2`) shifted from hidden `sret` + indirect pointer (`void (ptr sret([16 x i8]) align 16, ptr align 16)`) to direct vector register `<4 x float> (<4 x float>)`.
   - *Staggered `1.100.0` target divergence:* AArch64 targets (`aarch64-{linux,darwin,win-msvc}`) remained on `sret` in `1.100.0` and switched only in `1.100.0 -> 1.102.0-nightly` (`48` drifts in that step), making `rustc 1.100.0` a cross-architecture divergence release (`classifyFnAbi .r1_100_0 .x86_64_linux ≠ classifyFnAbi .r1_100_0 .aarch64_linux`).
   - *Win64 `extern "C"` non-`#[repr(C)]` ZSTs (`1.100.0 -> 1.102.0-nightly` on `x86_64-pc-windows-{msvc,gnu}`):* `abi_c_zst_struct` and `abi_c_zst_enum` shifted from `void (ptr align 1)` to `void ()`, shifting `%rcx`/`%rdx` argument slots and turning subsequent pointer parameters into wild dereferences.
   - *`vectorcall` symbol decoration (`rust-lang/rust@d11b3f4d61c50f4149ea34a89302cf24a0c52b86`, `1.100.0 -> 1.102.0-nightly`):* Moving `\x01`-prefixed decoration into `rustc_codegen_llvm::declare` changed IR names (`abi_vec_hfa4` -> `\01abi_vec_hfa4@@24` on `x86_64-*`, `@@20` on `i686-*`; `abi_vec_f32x4` -> `\01abi_vec_f32x4@@32`). Direct `.o` `llvm-nm` inspection established that `23/27` shifts keep identical `.o` symbols, while **`4/27` (`abi_vec_hfa4` across all four `x86_64` targets) are genuine `.o` linker breaks: `abi_vec_hfa4@@16 -> abi_vec_hfa4@@24`**.
2. **Partial SROA Boundary Meets `PassMode::Indirect` and `Atomic<T>` (`Basis: source + execution`):** [`tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption`](../tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption/REPORT.md) (`14176bbedd11ec1e98b5ab732562d3c2d91c4551`, `5,878` lines, `110` theorems, `[propext, Quot.sound]`, `nanoda_bin` `2,505` decls in `1.36 s` / `55.1 MiB`) models scalar entry arguments (`initArgs : List UInt64`) over a 2-level borrow tree. When ABI classification lowers an aggregate via `PassMode::Indirect` onto a caller-allocated temporary stack slot:
   - *Stale SROA shadow:* If Partial SROA keeps promoted scalar fields in virtual registers without **write-through flushing** prior to materializing the indirect stack copy, the callee reads stale memory (`staleSroaCopy`).
   - *`Freeze` / `UnsafeCell` / `Atomic<T>` vs. LLVM `readonly`:* In `rustc 1.94.0 -> 1.96.0`, `rust-lang/rust@fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7` migrated `AtomicU64` -> `Atomic<u64>` (`21/640` `memchr` bodies and `5/37` probe functions). Attaching LLVM `readonly` to an `Indirect` shared-reference/aggregate parameter without checking `!hasUnsafeCell` (`Freeze`) causes LLVM `readonly` UB (`llvmReadonlyUb`) whenever the callee performs an interior atomic or `UnsafeCell` write.

#### 2.2 Mechanized Seam `V2` Theorems (`support/VerticalSeamComposition.lean`, Section 2)

`Basis: Lean kernel check [toy model]`

- `classifyFnAbi` (`L1054–L1183`) encodes all four empirical ABI drift classes plus `hybridPairStruct hasUnsafeCell` (`llvmReadonly = !hasUnsafeCell`).
- `checkAbiLinkCompat` requires identical `(callerRel, callerTgt, callerCc)`, identical classified `FnAbi` descriptors, `!hasUnsafeCell -> !calleeAtomicWrite`, `!isIndirectReadonly` whenever `calleePerformsAtomicWrite`, and `sroaWriteThrough = true` whenever `PassMode = indirectHiddenPtr`.
- `v2_epoch_pinned_freeze_aware_abi_call_sound` (`L1184`, `[propext]` only) proves value-preserving cross-unit execution across all four signature kinds; `cex_v2a_cross_release_and_cross_target_fnabi_breaks` (`L1244`, `[propext]`) and `cex_v2b_indirect_copy_readonly_on_atomic_and_unflushed_sroa_unsound` (`L1270`, `[propext]`) witness each failure mode by kernel reduction.

---

### 3. Seam `V3`: AVX-512 `ZMM512` Spill Cliff, EVEX `vzeroupper`, `16 B` Outlined Thunks, and Red-Zone `SeqCst` Fences

`Basis: execution + source + Lean kernel check [toy model]`

#### 3.1 Three-Way Hardware and Codegen Coupling (`rustc 1.99.1 / LLVM 23.1.1`)

Composing [`coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi`](../coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi/REPORT.md) (`b31e6312edc1c6ef2ca8e2dbd528c856f36d131f` — covering AVX2 `vzeroupper`, `4,096 B` inline stack probes, `%r11+36880` loop CFA, and `16 B`-aligned outlined panic thunks) with [`rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality`](../rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality/REPORT.md) (`ce80a654ab246bd6ab7e274171c9540dbb352e07`) and cross-target atomic fence lowering exposes three coupled backend hazards:

1. **AVX-512 `ZMM512` Register Spills Cross the `4,096 B` Guard-Page Cliff (`Basis: execution + Lean kernel check [toy model]`):** Across `7` real crates, LLVM vectorization expands from `159/1,507` (`10.55%`, `124` 512-bit pre-legalized IR ops) on baseline `x86-64` to `190/1,493` (`12.73%`, `240` 512-bit / `133` `>512`-bit IR ops) on `x86-64-v3`. On Xeon Ice Lake-SP (`x86-64-v4`), LLVM defaults to `prefer-256-bit` (`k15_u32_indexed_gather_sum`: `10` ZMM insns, `10` kmask insns, `93` total insns), whereas `-C target-feature=-prefer-256-bit` unlocks full 512-bit ZMM allocation (`k15`: `31` ZMM insns, `18` kmask insns, `9` gather insns, `115` total insns; `k04`: `0 -> 12` ZMM insns; `k12`: `0 -> 9` ZMM insns). Spilling all `32` architectural SIMD registers doubles spill bytes from `32 × 32 B = 1,024 B` (`YMM`) to `32 × 64 B = 2,048 B` (`ZMM`). Combined with `2,112 B` of locals, a `3,136 B` `prefer-256-bit` frame safely below `4,096 B` crosses to **`4,160 B`** (`> 4,096 B`); emitting a single unprobed `sub $4160, %rsp` jumps over a `4,096 B` guard page (`guardPageSkipped`).
2. **EVEX `[511:128]` `vzeroupper` and `16 B` Outlined-Thunk CFA Parity (`Basis: source + execution + Lean kernel check [toy model]`):** Under AVX-512 EVEX (`ZMM0..31`), `ZMM0..15` alias `YMM0..15`/`XMM0..15`, so transitioning to legacy SSE or cold unwinder code still requires `vzeroupper` to clear `[511:128]` (both `[255:128]` and `[511:256]`), while `ZMM16..31` remain subject to ABI clobber rules. Meanwhile, invoking a throwing outlined cold thunk (`hasOutlinedThunkCall = true`) pushes an `8 B` return address onto `-8(%rsp)` via `callq`, clobbering any red-zone spill and requiring `sub rsp, 8` (`spShift = 16`, `outlinedThunkShift = 16`) plus `.cfi_remember_state`/`.cfi_restore_state` around preceding epilogues (omission caused a live `-11 SIGSEGV` inside `std::panic::catch_unwind` in `b31e6312ed`).
3. **`fence(Ordering::SeqCst)` Red-Zone Lowering `-64(%rsp)` vs. `(%rsp)` (`Basis: execution + Lean kernel check [toy model]`):** Compiling `core::sync::atomic::fence(Ordering::SeqCst)` at `-C opt-level=3` across official `rustc` toolchains produces target- and flag-sensitive x86 lowering:

   | `rustc` Release | Target Triple | Flags | Emitted `at_fence_seqcst` Assembly |
   | :--- | :--- | :--- | :--- |
   | `1.99.1`, `1.100.0`, `1.102.0-nightly` | `x86_64-unknown-linux-gnu` | `-C opt-level=3` (default red-zone) | `lock orl $0, -64(%rsp); retq` |
   | `1.99.1` | `x86_64-unknown-linux-gnu` | `-C opt-level=3 -C no-redzone=yes` | `lock orl $0, (%rsp); retq` |
   | `1.99.1` | `i686-unknown-linux-gnu` | `-C opt-level=3` (default SSE2) | `mfence; retl` |
   | `1.99.1` | `i686-unknown-linux-gnu` | `-C opt-level=3 -C target-feature=-sse2,-sse` | `lock orl $0, (%esp); retl` |
   | `1.99.1` | `aarch64-unknown-linux-gnu` | `-C opt-level=3` | `dmb ish; ret` |

   Under `-C no-redzone=yes`, Windows x64 (`targetAllowsRedZone .x86_64_win_msvc = false`), kernel/interrupt stacks, or any leaf function that outlines a throwing cold thunk (`hasOutlinedThunkCall = true`), `lock orl $0, -64(%rsp)` writes below `%rsp` into live signal/interrupt or callee stack space (`noRedZoneViolation` / `redZoneClobberedByThunk`). By contrast, `lock orl $0, (%rsp)` executes `x ||| 0#64 = x` in place on the live return-address slot and is sound in **both** modes.

#### 3.2 Mechanized Seam `V3` Theorems (`support/VerticalSeamComposition.lean`, Section 3)

`Basis: Lean kernel check [toy model]`

- `v3_backend_zmm512_probe_vzeroupper_redzone_sound` (`L1441`, `[propext, Quot.sound]`): Inductively proves (`runProbes_of_checkAux` + `BitVec.or_zero`) that `checkBackendV3 rzMode spec = true` guarantees clean execution returning `(spec.retAddrSlotVal, totalSpillFrameBytes ...)`, using Lean kernel GMP `Nat.ble`/`Nat.beq` checks without `maxRecDepth` blowup.
- `v3_noredzone_rejects_neg64_and_admits_zeroRsp` (`L1517`, **empty axiom set `[]`**): Proves `checkBackendV3 .noRedZone` rejects `.dispNeg64` (`false`) and admits `.dispZeroRsp` (`true`), executing cleanly to `.ok (retVal, 4160)`.
- `cex_v3a_zmm512_spill_crosses_4096_cliff_and_leaks_zmmHi` (`L1528`, `[propext, Quot.sound]`) and `cex_v3b_redzone_fence_corrupts_noredzone_and_outlined_leaf` (`L1550`, `[propext, Quot.sound]`): Exhibit the `3,136 -> 4,160 B` guard-page skip, missing `vzeroupper` `ZMM[511:128]` leak, `-C no-redzone=yes` fault, and outlined-thunk red-zone clobber.

---

### 4. Seam `V4`: Live P0 `DT_RUNPATH` ELF TCB Vulnerability in `joshlf/anneal` and Statement-Pinned Dual-Kernel Closure

`Basis: source + execution + Lean kernel check [toy model]`

#### 4.1 Live Audit of `joshlf/anneal@c131b320e` and `Lean v4.34.1` ELF Resolution

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/src/lib.rs:2468-2508` and `trusted/lean/foundation-lock.json`) confirms and extends the `libleanshared.so` TCB identity gap first identified in [`compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain`](../compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain/REPORT.md) (`7176fdd92a14672f169ef6809c04924c70ac3e5e`):

- `Checker::new_with_env` (`lib.rs:1856-1866`) and `run_lean` (`lib.rs:1970-1979`) sanitize child `lean` invocations with `.env_clear().envs(&self.environment)`, retaining only `HOME`, `TMPDIR`, `LANG`, `LC_ALL` and pinning `PATH=/usr/bin:/bin`, which scrubs `LD_PRELOAD` and `LD_LIBRARY_PATH`.
- However, `tool_admission` (`lib.rs:2468-2508`) hashes **only** `&self.lean` (`bin/lean`, `9,024` bytes, SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` in `foundation-lock.json`), verifies `lean --version`, queries `lean --print-prefix`, and hashes `prefix/src/lean/*.lean` and `Init.*` `.olean` companions. It **never** hashes `lib/lean/libleanshared.so` (`233,708,536` bytes) or any other `DT_NEEDED` ELF shared object.

**New `DT_RUNPATH` Shadowing Bypass (`Basis: execution`):** Running `readelf -d` on the official `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) `x86_64-unknown-linux-gnu` `bin/lean` binary exposes an ordered search path that **defeats even a naive patch hashing `<prefix>/lib/lean/libleanshared.so`**:

```text
readelf -d bin/lean:
  0x000000000000001d (RUNPATH) Library runpath: [$ORIGIN/../lib:$ORIGIN/../lib/lean]
  0x0000000000000001 (NEEDED)  Shared library: [libInit_shared.so]
  0x0000000000000001 (NEEDED)  Shared library: [libleanshared_2.so]
  0x0000000000000001 (NEEDED)  Shared library: [libleanshared_1.so]
  0x0000000000000001 (NEEDED)  Shared library: [libleanshared.so]
  0x0000000000000001 (NEEDED)  Shared library: [libc.so.6]
  0x0000000000000001 (NEEDED)  Shared library: [libpthread.so.0]
  0x0000000000000001 (NEEDED)  Shared library: [libdl.so.2]
  0x0000000000000001 (NEEDED)  Shared library: [libm.so.6]
```

Critically, `<prefix>/lib/` **already exists** in the shipped toolchain (holding `clang`, `libc++.so`, `libLLVM-22.so`, `libgmp.a`, `libz.so`, etc.) and contains **no** `libleanshared*.so` and **no** `libInit_shared.so`. Because `ld-linux-x86-64.so.2` searches `DT_RUNPATH` in strict left-to-right order (`$ORIGIN/../lib` before `$ORIGIN/../lib/lean`), placing a trojan `libleanshared.so` at `<prefix>/lib/libleanshared.so` preempts `<prefix>/lib/lean/libleanshared.so` during every `bin/lean` execution—even under `env_clear()` and even if `trusted/audit` hashes `<prefix>/lib/lean/libleanshared.so` at its fixed path!

#### Transitive ELF TCB Closure Measured on `Lean v4.34.1` (`x86_64-unknown-linux-gnu`)

`Basis: execution (readelf -d, stat -c, sha256sum on official Lean v4.34.1 + Linux x86_64 host libs)`

| Artifact (Relative to Lean Toolchain Prefix or System Root) | Size (Bytes) | Measured SHA-256 Digest | Role in Dynamic TCB Closure |
| :--- | ---: | :--- | :--- |
| `bin/lean` | `9,024` | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` | Launcher binary (sole ELF file hashed by `anneal@c131b320e`) |
| `bin/lake` (`DT_NEEDED` adds `libLake_shared.so`) | `13,840` | `6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d` | Build driver (`lake build` / `lake env`) |
| `lib/lean/libleanshared.so` | `233,708,536` | `6b30cc963d065fc9d2f87f7e9cbe0682b23000ae5425bccd769c5d477fa74f13` | **Actual Lean 4 elaborator + C++ kernel** (`DT_RUNPATH: [$ORIGIN/..:$ORIGIN]`) |
| `lib/lean/libLake_shared.so` | `12,545,496` | `ef0eb8942cd68ffb61ae573850a7181f70860580959e296c6e1a0e31ec50a38a` | Lake runtime |
| `lib/lean/libInit_shared.so` | `6,264` | `07f8c1156271ab6ec36c14c3031b5572329325d5f73dde3e89a1615d88f4e5cb` | Precompiled `Init` shared library stub |
| `lib/lean/libleanshared_1.so` | `6,264` | `69e900c025f40bf05c14f5b9ec48071b3130e34c96a7c45ee2eb5b6f307e19e6` | Lean shared split stub 1 |
| `lib/lean/libleanshared_2.so` | `6,264` | `38d0a03750b2e8d51161885ad597a8b4f6d3b85215c5a52aecd2b3753273cf3f` | Lean shared split stub 2 |
| `/lib64/ld-linux-x86-64.so.2` (`PT_INTERP`) | host-specific | `247846d87e13b9d8f1fd9b56cdc166bba25ea4169d4262cc9b2b7e51ae4ab8ae` | Dynamic linker interpreting `DT_RUNPATH` and `DT_NEEDED` |
| `/lib/x86_64-linux-gnu/libc.so.6` | host-specific | `551bd390f2c49d099d68590aa3f845e268be6a993b0d89168ec6f5ddaa6362cd` | System C library |
| `/lib/x86_64-linux-gnu/libm.so.6` | host-specific | `693e3e0052c2de588d72a1e8da51fdb4385f3fdb59819ff87c4dcfe8e65bb166` | System math library |
| `/lib/x86_64-linux-gnu/libpthread.so.0` | host-specific | `cbb98f8079e70e5a6383ad4f979ac601ee9a9d5136fa3703c2cb56bc694aabbc` | System pthreads library |
| `/lib/x86_64-linux-gnu/libdl.so.2` | host-specific | `8baf02270bb6e99ce03ef300333ce411b6ed7bb4c2a69170c72bc58c0f0e3245` | Dynamic loader (`dlopen`) library |
| `/lib/x86_64-linux-gnu/librt.so.1` | host-specific | `2b51aa780387aac8698a9ae0eb3ce82abe216af5b6b14cf1123ab18051be44d6` | Realtime extensions (`libleanshared.so` `DT_NEEDED`) |

*(Host `/lib*` hashes vary by OS distribution and patch level; the seven Lean toolchain hashes above are fixed per official `Lean v4.34.1` `x86_64-unknown-linux-gnu` release archive.)*

#### 4.2 Dual-Kernel Checking (`nanoda_bin 0.4.19`) Coupled With Statement-Hash Pinning

`Basis: execution + source + Lean kernel check [toy model]`

- **Empirical Dual-Kernel Measurements (`Basis: execution`):** As measured in [`lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb`](../lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb/REPORT.md) (`e1d84aa8ef0cc7635845be021c54d3d7418c89c6`), statically built `nanoda_bin 0.4.19` (a 29-crate Rust closure over `lean4export 3.1.0` from `Lean v4.35.0`) outpaces Lean's kernel on pure checking (`HonestGmp_4000`: `nanoda_bin` `3.2624 s` / `268.53 MB` = `1,226.1` end-to-end steps/s vs. Lean `9.1589 s` / `772.93 MB` = `436.7` steps/s; scalar MIR bridge `1,795` decls in `0.889 s` / `34.29 MB`; Tree Borrows partial SROA `2,505` decls in `1.36 s` / `55.1 MiB`), and **fails closed (`rc = 101`)** when an unpermitted transitive `Classical.choice` dependency appears (`0.6404 s` panic `declaration not found in infer_const, Classical.choice`, vs. `0.726 s` / `33.1 MB` / `3,032` decls when explicitly permitted).
- **Statement-Hash Pinning and Shared-Bug Boundary (`Basis: source + Lean kernel check [toy model]`):** As mechanized in [`proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`](../proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings/REPORT.md) (`fb407b1d31432ebe8e4d97fcc95717e8193c0c28`, `Toy.KernelTrust.unpinned_faithful_checker_for_sound_rules_accepts_renamed_False`), even a 100% faithful external checker provides zero assurance about the intended Rust verification theorem if an unpinned exporter (`lean4export` or a compromised `libleanshared.so`) substitutes a trivial renamed statement (`hashTrivialStmt` instead of `pinnedTargetStmtHash`). Furthermore, dual-kernel quorums do not eliminate *shared* specification bugs (e.g., `leanprover/lean4#14807`, `is_prop` missing sort check shared by both Lean's C++ kernel and `nanoda`).
- **Mechanized Seam `V4` Closure (`support/VerticalSeamComposition.lean`, Section 4):**
  - `v4_closed_tcb_and_pinned_dual_kernel_sound` (`L1668`, `[propext]`): Authenticates the primary Lean toolchain via ordered `DT_RUNPATH` + `DT_NEEDED` resolution (`checkPrimaryElfClosure`, rejecting any `$ORIGIN/../lib` shadow file), pairs it with pinned `lean4export` + statically linked `nanoda_bin` (`checkDualKernelClosure`), enforces exact statement-hash agreement (`exp.exportedStmtHash = lock.pinnedTargetStmtHash`), and enforces the transitive axiom policy (`!(usesChoiceAxiom && !allowClassicalChoice)`).
  - `cex_v4a_launcher_only_and_runpath_shadow_accept_trojan_kernel` (`L1793`, `[propext]`): Proves both `auditCurrentAnnealLauncherOnly` (`fsTrojanLibLean`) **and** `auditNaiveFixedPathLibLean` (`fsRunpathShadowed`) return `true` while resolving `.libLeanSharedMain` to `digestTrojanKernel`, whereas `checkPrimaryElfClosure` returns `false` on both.
  - `cex_v4b_unpinned_lean4export_or_unpermitted_choice_breaks_dual_kernel` (`L1806`, `[propext]`): Proves unpinned `lean4export` statement renaming (`hashTrivialStmt`) and unpermitted `Classical.choice` are rejected by `checkDualKernelClosure`.

---

### 5. Seam `V5`: Unified End-to-End Composition and Complete Kernel-Checked Theorem Ledger

`Basis: Lean kernel check [toy model]`

Section 5 (`L1830–L2089`) of [`support/VerticalSeamComposition.lean`](support/VerticalSeamComposition.lean) couples Stages `V1`–`V4` via `VerticalCompilationBundle`, `checkVerticalPipeline`, and `execVerticalPipeline`:

1. **Master Composition Theorem (`v5_unified_vertical_seam_composition_sound`, `L1908`, `[propext, Quot.sound]`):** Composing all four positive seam theorems (`v1_*`, `v2_*`, `v3_*`, `v4_*`), whenever `checkVerticalPipeline b = true` and cached baseline execution succeeds with `vSrc`, every stage executes without fault returning `.ok (vSrc, totalSpillFrameBytes ...)` **and** `SemanticallyValid b.mirBody.specHash` holds.
2. **Non-Vacuity Concrete Witness (`witness_v5_end_to_end_zmm512_noredzone_dual_kernel_verified`, `L2041`, `[propext, Quot.sound]`):** Instantiates a complete end-to-end passing bundle (`const MASK = 15`, input `29#64` -> `29 &&& 15 = 13#64`, `r1_99_1`, `hybridPairStruct true` with `UnsafeCell` atomic write, `sroaWriteThrough = true`, `llvmReadonly = false`, `fullZmm512` `32` spilled ZMMs + `2,112 B` locals = `4,160 B` split-probed `[sub 4096; touch; sub 64]`, `vzeroupper` enabled, `outlinedThunkShift = 16`, `noRedZone` with `lock orl $0, (%rsp)`, shadow-free ELF closure matching the measured `Lean v4.34.1` SHA-256 digests, and static `nanoda_bin` pinned to `bodyMinizMaskProbe.specHash`), reducing cleanly to `.ok (13#64, 4160)` via `⟨rfl, rfl, rfl⟩`.
3. **Adversarial Uncoupled-Stage Counterexample (`cex_v5_locally_valid_stages_fail_when_composed_without_seam_couplings`, `L2078`, `[propext, Quot.sound]`):** Constructs `adversarialBrokenCompositionBundle` where **every uncoupled local check passes** (`checkMirV1Cert = true`, cached `evalMirBody = .ok 0#64`, caller & callee each use individually valid per-release ABIs, userspace `checkBackendV3 .redZoneAllowed = true`, legacy `auditCurrentAnnealLauncherOnly = true`), yet composed execution crashes immediately with `.error (.v1Fault .oobPanic)` while masked `V2` (`1.99.1 -> 1.100.0` `simdF32x4`), `V3` (`dispNeg64` under `.noRedZone`), and `V4` (`$ORIGIN/../lib` shadowed `libleanshared.so` + renamed `hashTrivialStmt`) defects are simultaneously present and caught by `checkVerticalPipeline = false`.

#### Complete Public Theorem Ledger (`17` Public Theorems + `10` Private Helper Theorems = `27` Total)

`Basis: Lean kernel check (Lean v4.34.1, -DElab.async=false -Ddebug.skipKernelTC=false, exit 0, 6.247 s, 558.95 MB peak RSS, 0 errors, 0 warnings)`

| # | Seam | Public Theorem Symbol (`VrustcProbe.VerticalSeamComposition.*`) | Line | Role | Exact `#print axioms` |
| :-: | :-: | :--- | :-: | :--- | :--- |
| 1 | V1 | `v1_const_cone_and_profile_cache_preserves_semantics` | 521 | Positive (Cone + Release Cache) | `[propext, Quot.sound]` |
| 2 | V1 | `v1_certified_f11b_norm_preserves_eval` | 914 | Positive (Scalar Normalization) | `[propext, Quot.sound]` |
| 3 | V1a | `cex_v1a_unevaluated_const_change_breaks_uncached_cone` | 983 | Counterexample (`Const::Unevaluated` Cone) | `[propext, Quot.sound]` |
| 4 | V1b | `cex_v1b_rustc_196_to_199_retag_drift_and_movetocopy_ub` | 1038 | Counterexample (`WithRetag` + `MoveToCopy`) | `[propext, Quot.sound]` |
| 5 | V2 | `v2_epoch_pinned_freeze_aware_abi_call_sound` | 1184 | Positive (`FnAbi` + `Freeze` + SROA) | `[propext]` |
| 6 | V2a | `cex_v2a_cross_release_and_cross_target_fnabi_breaks` | 1244 | Counterexample (`4` `FnAbi` Drift Classes) | `[propext]` |
| 7 | V2b | `cex_v2b_indirect_copy_readonly_on_atomic_and_unflushed_sroa_unsound` | 1270 | Counterexample (`readonly` + Stale SROA) | `[propext]` |
| 8 | V3 | `v3_backend_zmm512_probe_vzeroupper_redzone_sound` | 1441 | Positive (`ZMM512` + Probes + `vzeroupper` + RZ) | `[propext, Quot.sound]` |
| 9 | V3 | `v3_noredzone_rejects_neg64_and_admits_zeroRsp` | 1517 | Positive (`noRedZone` Gate Separation) | `[]` (**no axioms**) |
| 10 | V3a | `cex_v3a_zmm512_spill_crosses_4096_cliff_and_leaks_zmmHi` | 1528 | Counterexample (`4,160 B` Cliff + `ZMM` Leak) | `[propext, Quot.sound]` |
| 11 | V3b | `cex_v3b_redzone_fence_corrupts_noredzone_and_outlined_leaf` | 1550 | Counterexample (`-64(%rsp)` & Thunk Clobber) | `[propext, Quot.sound]` |
| 12 | V4 | `v4_closed_tcb_and_pinned_dual_kernel_sound` | 1668 | Positive (ELF Closure + Dual-Kernel Pin) | `[propext]` |
| 13 | V4a | `cex_v4a_launcher_only_and_runpath_shadow_accept_trojan_kernel` | 1793 | Counterexample (`libleanshared.so` + `RUNPATH` Shadow) | `[propext]` |
| 14 | V4b | `cex_v4b_unpinned_lean4export_or_unpermitted_choice_breaks_dual_kernel` | 1806 | Counterexample (Statement Rename + `Choice` Gate) | `[propext]` |
| 15 | V5 | `v5_unified_vertical_seam_composition_sound` | 1908 | Master Composition Theorem | `[propext, Quot.sound]` |
| 16 | V5 | `witness_v5_end_to_end_zmm512_noredzone_dual_kernel_verified` | 2041 | Non-Vacuity Concrete Witness | `[propext, Quot.sound]` |
| 17 | V5 | `cex_v5_locally_valid_stages_fail_when_composed_without_seam_couplings` | 2078 | Uncoupled-Stage Ablation Counterexample | `[propext, Quot.sound]` |

*(The `10` private helper theorems transitively checked inside those proofs are `evalConstCone_eq_implies_mem_eq` [`L456`], `evalMirOp_eq_of_cone_agree` [`L469`], `evalMirStmts_eq_of_cone_agree` [`L483`], `hasStorageMarker_norm_eq_false` [`L562`], `envScalarAgree_checkAbsOp` [`L586`], `slotScalarAgree_nonDead_tgt` [`L638`], `assign_preserves_envScalarAgree` [`L656`], `evalMirStmts_scalar_norm_preserves_clean` [`L696`], `runProbes_of_checkAux` [`L1416`], and `checkElfDepList_mem` [`L1647`].)*

---

### 6. Analytical Evaluation Across Performance (`L1`–`L6`), Comprehensibility (`C1`–`C2`), and Validation (`V1`–`V4`)

`Basis: execution (L5, L6 for VerticalSeamComposition.lean & Lean v4.34.1 ELF artifacts; L3, L5, L6 from companion reports) + source/derived (C1, C2, V1–V4); unmeasured metrics explicitly labeled not measured`

| Dimension | Measurement / Architectural Assessment | Evidence Basis |
| :--- | :--- | :--- |
| **`L1` Authoring & Proof Velocity** | **`not measured`** (interactive proof authoring time was not systematically benchmarked; structurally, discharging all `27` theorems constructively without `omega`, `bv_decide`, or `Classical.choice` required `2,109` lines of self-contained Lean). | `not measured` (`source` line count only) |
| **`L2` Toolchain Build Time** | **`not measured`** (official pre-built `elan` `Lean v4.34.1` and `rustup` `rustc` toolchains were executed directly; building `lean`, `rustc`, or `anneal-audit` from source was not timed). | `not measured` |
| **`L3` Compile / Capture Extraction Latency** | **`not measured`** for an integrated production `V1`–`V5` driver (`joshlf/anneal@c131b320e` lacks a production MIR emitter). Companion measurements bound stage costs: `miniz_oxide 0.9.1` `-O3` incremental edit (`BASE_EXTRA_MASK`) achieves `3.999x` wall-clock speedup (`13/16` `.o`s reused) when keyed on the `Const::Unevaluated` cone. | `not measured` (integrated); `execution` (companion incremental report) |
| **`L4` Generated Code Performance** | **`not measured`** for full end-to-end verified binary execution. Qualitatively (`derived`), enabling `x86-64-v4 -prefer-256-bit` unlocks `31` vs. `10` ZMM instructions on gather kernels while doubling worst-case SIMD spill frame bytes (`1,024 -> 2,048 B`), and emitting `lock orl $0, (%rsp)` vs. `-64(%rsp)` trades a false dependency on the top-of-stack slot for `-C no-redzone=yes` / thunk soundness. | `not measured` (`execution` instruction counts; `derived` tradeoff) |
| **`L5` Certificate Checking Throughput & Cold-Start Latency** | **Measured live on `support/VerticalSeamComposition.lean` (`Lean v4.34.1` synchronous kernel):** **`6.247 s`** wall time (`5.81 s` user + `0.29 s` sys) on high-clock `x86-64` Linux (`23.382 s` on a resource-constrained Linux VM for full `.olean` compilation). Companion `nanoda_bin 0.4.19` checks `1,795` decls (`MoveToCopy` bridge) in `0.889 s`, `2,505` decls (partial SROA) in `1.36 s`, and `HonestGmp_4000` in `3.2624 s` (`1,226.1` steps/s vs. Lean `9.1589 s` / `436.7` steps/s). | `execution` (`Lean kernel check` + companion `nanoda_bin` benchmarks) |
| **`L6` RAM / Disk / Binary Footprint** | **Measured live:** `support/VerticalSeamComposition.lean` is `93,914 B` (`2,109` lines); synchronous `Lean v4.34.1` typecheck peaked at **`558.95 MB`** RSS (`572,360` kB); compiled `.olean` is `4,079,392 B`. Authenticated `Lean v4.34.1` ELF closure totals **`246,301,688 B`** (`233,708,536 B` `libleanshared.so` + `12,545,496 B` `libLake_shared.so` + `9,024 B` `bin/lean` + `13,840 B` `bin/lake` + `3 × 6,264 B` split/init stubs), of which `anneal@c131b320e` currently hashes only **`0.0037%`** (`9,024 B`). | `execution` (`stat -c`, `/usr/bin/time -v`, `Lean v4.34.1`) |
| **`C1` Auditability of Specs & Assumptions** | Every stage invariant is stated as an explicit computable Boolean gate (`soundV1CacheKey`, `checkMirV1Cert`, `checkAbiLinkCompat`, `checkBackendV3`, `checkPrimaryElfClosure`, `checkDualKernelClosure`) and composed conjunctively in `checkVerticalPipeline`. All `17` public theorems use strictly `[]`, `[propext]`, or `[propext, Quot.sound]` (`0` `Classical.choice`, `0` `sorryAx`, `0` opaque tactics). | `source` + `Lean kernel check [toy model]` |
| **`C2` Conceptual Orthogonality & Expressibility** | The five seams are structurally orthogonal yet failure-coupled: weakening any single cross-layer edge (`V1` cone/release, `V2` epoch/`Freeze`/SROA, `V3` spill-cliff/red-zone/thunk, `V4` `DT_RUNPATH`/statement-hash) produces a concrete counterexample even while all other local checks stay green (`cex_v5_*`). | `derived` + `Lean kernel check [toy model]` |
| **`V1` Spec Adequacy, Mutation & Non-Vacuity** | Non-vacuity is established by `witness_v5_end_to_end_zmm512_noredzone_dual_kernel_verified` (`⟨rfl, rfl, rfl⟩`); mutation sensitivity is established by `8` dedicated adversarial counterexample theorems (`cex_v1a`, `cex_v1b`, `cex_v2a`, `cex_v2b`, `cex_v3a`, `cex_v3b`, `cex_v4a`, `cex_v4b`) plus cross-seam ablation `cex_v5_*`. | `Lean kernel check [toy model]` |
| **`V2` Lowering / Checker Differential Fuzzing** | **`not measured`** inside this study (no live differential fuzzer was run across an end-to-end Rust-to-ELF pipeline). Companion empirical matrices (`833` ABI pairs × `9` targets × `3` releases; `782` MIR bodies × `7` releases; `1,493–1,507` vectorized functions) provide concrete cross-release differential evidence. | `not measured` (integrated); `execution` (companion matrices) |
| **`V3` Weak-Memory / Crash / Silicon Leakage Validation** | Live `rustc` assembly probes confirm `-64(%rsp)` vs. `(%rsp)` `SeqCst` fence emission across `-C no-redzone=yes` and `i686`/`aarch64`, while companion execution confirms live `-11 SIGSEGV` unwinding failure on missing CFI restore and Xeon AVX-512 `ZMM` allocation. Hardware side-channel / microarchitectural leakage is **`not measured`**. | `execution` (codegen/unwind); `not measured` (silicon side channels) |
| **`V4` Held-Out Ecosystem / Hardware Replay** | **`not measured`** end-to-end across a full crates.io compilation under an integrated verified driver. Individual empirical layers replay on `miniz_oxide 0.9.1`, `serde_json 1.0.154`, `memchr 2.8.3`, `ryu 1.0.23`, `itoa 1.0.19`, and real `Lean v4.34.1` host ELF binaries. | `not measured` (end-to-end); `execution` (per-layer corpora) |

---

### 7. Actionable Remediation Requirements (`Basis: derived`)

1. **P0 Security Fix (`joshlf/anneal` `trusted/audit/src/lib.rs` + `trusted/lean/foundation-lock.json`):** Extend `tool_admission` (`lib.rs:2402, 2468-2508`) to parse ELF `PT_INTERP`, `DT_RUNPATH`/`DT_RPATH`, and transitive `DT_NEEDED` entries for `bin/lean` (and `bin/lake` when invoked), **simulate ordered left-to-right `DT_RUNPATH` lookup so any shadowing hit in `<prefix>/lib/` fails closed**, pin SHA-256 digests for `lib/lean/libleanshared.so`, `lib/lean/libInit_shared.so`, `lib/lean/libleanshared_{1,2}.so`, and `bin/lake`/`lib/lean/libLake_shared.so` in `foundation-lock.json`, and retain `env_clear()` (`lib.rs:1973`) for every future `lean4export` and `nanoda_bin` subprocess.
2. **P1 Capture-Driver Alignment (`trusted/rustc-capture/src/driver.rs` × `Trusted/MirAst.lean`):** Reconcile the five-month pin skew between `driver.rs:25` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`) and `MirAst.lean:511` (`8144389c895da997dbdecaa635e41d6a50be6ffd`, `2026-10-20`), and extend `Trusted.MirAst` to represent transitive `Const::Unevaluated` cones, `WithRetag` (`no_retag copy`), and indirect/slice constants before enabling incremental verification caching.
3. **Cross-Layer ABI and Backend Guardrails:** Extend Partial SROA verification beyond scalar entry arguments (`initArgs : List UInt64`) to enforce `Freeze` (`!hasUnsafeCell`) checks before LLVM `readonly` attributes on `Indirect` parameters and write-through SROA flushes across indirect calls; extend backend stack-probe/CFI verification to account for full `32 × 64 B` `ZMM` spill expansion across `4,096 B` guard pages and reject `lock orl $0, -64(%rsp)` under `-C no-redzone=yes`, Win64, kernel targets, or outlined cold calls.

## Boundaries

- **Toy Formalization Scope (`known not to apply` to unmodeled full semantics; `[toy model]`):** `support/VerticalSeamComposition.lean` is a standalone zero-import Lean `v4.34.1` transition model over finite scalar/reference MIR programs, four stylized `FnAbi` signature kinds, abstract `x86-64` backend block specs, and a finite `ToolchainFs` map. It does **not** import `joshlf/anneal`'s `Trusted.MirSemantics`, does not decode real `x86-64` or ELF64 machine bytes, and does not prove that real `rustc`, LLVM, or `glibc` `ld.so` implement the modeled transition rules.
- **No Live Exploitation of `DT_RUNPATH` Shadowing (`not examined` dynamically):** The `$ORIGIN/../lib` precedence bypass was established statically from `joshlf/anneal@c131b320e` `trusted/audit/src/lib.rs:2468-2508`, live `readelf -d bin/lean` (`DT_RUNPATH: [$ORIGIN/../lib:$ORIGIN/../lib/lean]`), live directory inspection showing `<prefix>/lib/` contains no `libleanshared*.so`, and the System V / `glibc` `ld.so` `DT_RUNPATH` specification (`Basis: source + execution + derived`). No trojan `.so` was written into a live toolchain directory.
- **System Library Hash Portability (`known not to apply` across OS distributions):** While the seven `Lean v4.34.1` toolchain ELF hashes (`bin/lean`, `bin/lake`, `lib/lean/lib*.so`) are invariant for the official `x86_64-unknown-linux-gnu` release archive, `/lib64/ld-linux-x86-64.so.2`, `libc.so.6`, `libm.so.6`, `libpthread.so.0`, `libdl.so.2`, and `librt.so.1` digests depend on the host Linux distribution and `glibc` version. Pinning those requires hermetic container/Nix rootfs hashes or static musl/Nix linking rather than one global `foundation-lock.json` digest.
- **macOS `Mach-O` / Windows `PE` Dynamic Loaders (`not examined`):** `DT_RUNPATH` analysis covers ELF64 on Linux (`x86_64-unknown-linux-gnu`). Equivalent `@rpath`/`@loader_path` (`dyld`) hazards on `x86_64-apple-darwin` / `arm64-apple-darwin` and DLL search-order hijacking on Windows are not examined here.
- **Shared Dual-Kernel Soundness Bugs (`known not to apply` to quorum defense):** As proved in [`proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`](../proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings/REPORT.md) (`fb407b1d31432ebe8e4d97fcc95717e8193c0c28`), `v4_closed_tcb_and_pinned_dual_kernel_sound` relies on faithfulness hypotheses (`PrimaryGenuineFaithful`, `NanodaGenuineFaithful`). A kernel specification bug shared by both Lean's C++ kernel and `nanoda_bin` (such as `leanprover/lean4#14807`) breaks soundness of both checkers simultaneously.
- **Integrated Production Pipeline (`unsupported` in `joshlf/anneal@c131b320e`):** `joshlf/anneal@c131b320e` does not yet ship an end-to-end Rust-to-ELF certified compiler driver, `lean4export`/`nanoda_bin` orchestration, or `ZMM512`/red-zone backend verification; all remediation prescriptions in Section 7 are `derived` design requirements rather than tested patches.

## Evidence

### Preserved Support Artifact

- [`support/VerticalSeamComposition.lean`](support/VerticalSeamComposition.lean): `2,109` lines, `93,914` bytes, SHA-256 `af3f1f3afbbe3c9841dd5aa7fcc0a0d4172390af720b43e999dfc8f3753dd4eb`. Zero-import standalone Lean `v4.34.1` module defining namespace `VrustcProbe.VerticalSeamComposition` with `27` theorems (`17` public `#print axioms`-audited + `10` private helpers).

### Synchronous Lean `v4.34.1` Kernel & `.olean` Audit Receipts (`2026-11-20`)

- **Synchronous kernel check (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
  - Invocation: `lean -DElab.async=false -Ddebug.skipKernelTC=false support/VerticalSeamComposition.lean`
  - Result (`x86_64-unknown-linux-gnu`): `returncode = 0`, `elapsed_sec = 6.247 s` (`5.81 s` user, `0.29 s` sys), `peak_rss = 558.95 MB` (`572,360` kB), `theorem_count = 27`, `kernel_clean = true`, `pass1_clean = true`, `omega_count = 0`, `disallowed_axioms = []`, `forbidden_tokens = []`.
- **Compiled `.olean` constant-table inspection (`lean -DElab.async=false -Ddebug.skipKernelTC=false ... -o VerticalSeamComposition.olean`):**
  - `.olean` size `4,079,392` bytes (SHA-256 `61eb681f0f1e23554c85993ca6072a2409efed59e6e40a6444ac0887600eb132`).
  - Constant-table audit: `total_env=67659`, `user_consts=1472`, `user_thms=512`, `user_defs=785`, `isPartial=0`, `unsafeRecUser=0`, `trusted=0`, `sorryAx=0`, `classicalChoice=0`, `nativeDecide=0`.
  - Non-comment source scan: `0` occurrences of `sorry`, `admit`, `axiom`, `partial`, `omega`, `bv_decide`, `native_decide`, `Classical.choice`, `._unsafe_rec`, `namespace Trusted`, or `@[extern`.

### Primary Upstream Source Citations (Verified via GitHub API on `2026-11-20`)

- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
  - `trusted/audit/src/lib.rs:1856-1866, 1970-1979` (`Checker::new_with_env` and `env_clear()` environment allowlist scrubbing `LD_PRELOAD` / `LD_LIBRARY_PATH`).
  - `trusted/audit/src/lib.rs:2402-2515` (`tool_admission`: hashes `&self.lean` at `L2468`, checks `--version` at `L2481-2500`, reads `--print-prefix` at `L2502-2507`, hashes `prefix/src/lean/*.lean` and `Init.*` `.olean`s without hashing `lib/lean/libleanshared.so` or inspecting `DT_RUNPATH`/`DT_NEEDED`).
  - `trusted/lean/foundation-lock.json` (`distributions` maps `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` exclusively to `bin/lean` digest `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`).
  - `trusted/lean/Trusted/MirAst.lean:504-520` (`ConstLit := scalar (BitVec 128) | zeroSized`; cites `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`).
  - `trusted/rustc-capture/src/driver.rs:25` (`const COMPILER_VERSION: &str = "1.98.0-nightly (f8a08b688 2026-05-30)";` matching `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).
- `rust-lang/rust` behavioral commits:
  - `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`: removes `StatementKind::Retag`, introduces `Rvalue::Use(_, WithRetag)` and `no_retag copy`).
  - `fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7` (`AtomicU*` -> `Atomic<T>` refactor).
  - `d11b3f4d61c50f4149ea34a89302cf24a0c52b86` (`vectorcall` `\x01` symbol decoration migration into `rustc_codegen_llvm::declare`).
- `leanprover/lean4#14807` (`fix: make the kernel is_prop check require a sort`, shared kernel bug affecting both Lean C++ and `nanoda`).

### Companion `google/zerocopy` (`refs/heads/reference`) Empirical Reports

- [`anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge`](../anneal-trusted-mir-movetocopy-and-storage-elision-refinement-bridge/REPORT.md) (`6e24ad128d7f29afc0f47733eb42ec4d3392ba63`)
- [`tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption`](../tree-borrows-partial-sroa-store-sinking-and-unwind-abort-subsumption/REPORT.md) (`14176bbedd11ec1e98b5ab732562d3c2d91c4551`)
- [`rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius`](../rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius/REPORT.md) (`4e59b26602689aaf0b4dd0d46cad3a90cf7d6ef9`)
- [`rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility`](../rustc-seven-release-postcleanup-mir-schema-drift-and-capture-compatibility/REPORT.md) (`7ac36b3ef5b297b1c69f44025f4f8464b524f26b`)
- [`rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting`](../rustc-multi-target-multi-release-abi-drift-matrix-and-fingerprinting/REPORT.md) (`120889696dc131f0fc7cf814e898ee72cd04a19e`)
- [`rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality`](../rustc-ecosystem-vectorization-fp-reductions-and-avx512-silicon-reality/REPORT.md) (`ce80a654ab246bd6ab7e274171c9540dbb352e07`)
- [`coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi`](../coupled-backend-seam-verification-subregisters-vzeroupper-probestack-and-cfi/REPORT.md) (`b31e6312edc1c6ef2ca8e2dbd528c856f36d131f`)
- [`compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain`](../compiler-bootstrapping-diverse-double-compiling-and-verified-rustc-tcb-chain/REPORT.md) (`7176fdd92a14672f169ef6809c04924c70ac3e5e`)
- [`lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb`](../lean4-external-checkers-nanoda-leanexport-and-compiled-checker-tcb/REPORT.md) (`e1d84aa8ef0cc7635845be021c54d3d7418c89c6`)
- [`proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings`](../proof-checker-trust-layers-faithfulness-semantic-soundness-and-verifier-rings/REPORT.md) (`fb407b1d31432ebe8e4d97fcc95717e8193c0c28`)

## Revalidation

1. **Re-verify the Formal Composition Artifact Under `Lean v4.34.1`:**
   ```bash
   sha256sum support/VerticalSeamComposition.lean
   # Expected: af3f1f3afbbe3c9841dd5aa7fcc0a0d4172390af720b43e999dfc8f3753dd4eb
   lean -DElab.async=false -Ddebug.skipKernelTC=false support/VerticalSeamComposition.lean
   ```
   Confirm exit code `0` and inspect the `17` `#print axioms` lines at the end of stdout: `v3_noredzone_rejects_neg64_and_admits_zeroRsp` must report no axioms, and all remaining `16` public theorems must list only subsets of `[propext, Quot.sound]` (`0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`).
2. **Re-check the `DT_RUNPATH` & `libleanshared.so` TCB Gap on a Newer `Lean` or `joshlf/anneal` Revision:**
   ```bash
   TC="$(lean --print-prefix)"
   readelf -d "$TC/bin/lean" | grep -E 'RUNPATH|RPATH|NEEDED'
   ls -la "$TC/lib/" "$TC/lib/lean/libleanshared"*
   sha256sum "$TC/bin/lean" "$TC/lib/lean/libleanshared.so"
   ```
   Diff `trusted/audit/src/lib.rs` (`tool_admission`) and `trusted/lean/foundation-lock.json` in `joshlf/anneal` to verify whether `libleanshared.so` and ordered `DT_RUNPATH` shadow rejection are now enforced.
3. **Re-check `joshlf/anneal` Capture-Driver vs. `Trusted.MirAst` Pin Alignment:**
   Compare `COMPILER_VERSION` in `trusted/rustc-capture/src/driver.rs` against the `rust-lang/rust` commit cited in `trusted/lean/Trusted/MirAst.lean` and check whether `Const::Unevaluated` cones and `WithRetag` (`no_retag copy`) are captured.
4. **Re-probe `x86_64` `fence(Ordering::SeqCst)` Red-Zone Lowering on a Newer `rustc`:**
   ```bash
   printf '#![crate_type="lib"]\n#[no_mangle] pub fn f() { core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst); }\n' > /tmp/fence_probe.rs
   rustc --target x86_64-unknown-linux-gnu -C opt-level=3 --emit=asm -o - /tmp/fence_probe.rs | grep -A3 '^f:'
   rustc --target x86_64-unknown-linux-gnu -C opt-level=3 -C no-redzone=yes --emit=asm -o - /tmp/fence_probe.rs | grep -A3 '^f:'
   ```
   Verify whether default compilation still emits `lock orl $0, -64(%rsp)` while `-C no-redzone=yes` emits `lock orl $0, (%rsp)`.
