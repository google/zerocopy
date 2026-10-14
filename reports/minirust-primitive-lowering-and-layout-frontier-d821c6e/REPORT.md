# Numeric, layout and primitive-lowering boundaries in MiniRust

## Summary

MiniRust d821c6e has bounded integer semantics but no floating-point type. Rust's FP rules therefore belong to an additional semantics, rather than an implicit interpretation of MiniRust mathematical integers or real numbers. Native ARM64 and wasm32 controls exercise the same explicit Rust numeric rules while exposing different word and aggregate layouts.

The importer review also finds a concrete union concern: its chunk calculator marks every pointer as one word, including wide pointers. A two-word pointer routed through that chunk map loses metadata. A separately executed generated-core control confirms this consequence, while actual Rust-to-MiniRust translation of the candidate remains unexecuted. Library source inspection resolves the read/write-unaligned, copy and realloc routes without treating those distinct leaves as verified standard-library code.

## Applicability

Direct source comparison: MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, Rust/compiler/core/alloc `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (Rust 1.99.0), and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. These are **distinct subjects**, not a tested combined importer toolchain. MiniRust's requested nightly-2026-05-01 is different from the installed compiler used for the new safe controls. `minimize` sysroot setup builds/selects std for the invoked compiler, target and `MINIRUST_SYSROOT`; a source-level primitive name does not determine one timeless lowering.

New execution uses Rust 1.99.0, LLVM 23.1.1, edition 2024, opt-level 0, panic=abort, native `aarch64-apple-darwin` and `wasm32-unknown-unknown`. The wasm component was already installed separately; the revalidation script copies it into an owned sysroot. Node is 24.21.0, V8 13.6.233.17-node.53. All executed Rust functions are safe; an export-name attribute exposes scalar wasm functions. No invalid pointer, union field read, unchecked arithmetic or malformed metadata is executed in Rust. The Darwin replay explicitly supplies the selected compiler's matching LLVM library directory to the linker subprocess; it does not change a global runtime configuration.

This extends the earlier [target/DST report](../minirust-target-dst-and-intrinsic-contracts-d821c6e/REPORT.md), which owns dynamic tail/retag-mask formulas, allocation reuse and target-interface inventory. It substantively reviews and reuses the [two-target zerocopy controls](../zerocopy-two-target-byte-and-layout-controls-2026-10-14/REPORT.md), rather than repeating their 65,536 bool-pair cases. Its stored native/wasm fixture, version, result and layout evidence were read; those original zerocopy executions were not rerun here. No all-target or compiler-correctness result follows from either package.

## Findings

### F1. Numeric operations need an explicit bounded or floating-point semantics

Basis: **source** + **normative documentation**, with **derived** portability obligations.

MiniRust `Int` is mathematical. Integer result types bound machine values: ordinary add/subtract/multiply wrap after evaluation; unchecked forms raise semantic UB when the mathematical result does not fit. Ordinary shifts reduce the count modulo width; unchecked shifts require 0 ≤ count < width. Division/remainder reject zero and signed MIN/-1, and exact division additionally requires zero remainder. `IntToInt` uses the target type's range reduction. Surface overflow panics require elaborated assertions; the core wrapping Add rule does not alone describe a checked source `+`. The importer selects the separate unchecked MIR operators explicitly. [Core integer rules](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/operators.md#L183), [importer operators](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/rvalue.rs#L34).

There is no float variant in the inspected core Type. `translate_ty` has no Float case and its fallback rejects unsupported kinds; FloatToFloat/FloatToInt/IntToFloat casts are explicitly rejected. Thus the exact FP semantics **of this MiniRust fragment is absent**, not unspecified real arithmetic. That does not imply Rust FP is unspecified. Rust's binary32 documentation specifies round-to-nearest/ties-to-even for ordinary +, −, ×, ÷, signed zero, infinity and NaNs. Arithmetic NaN sign/payload choices are nondeterministic within a documented set, with target-specific extra payloads. The choice is per operation; repeated observations of one result are stable. Bit operations such as to_bits/from_bits preserve the relevant input bits. Const arithmetic can choose a different permitted NaN from runtime arithmetic. [MiniRust type/import boundary](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/ty.rs#L181), [Rust binary32 rules](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/primitive_docs.rs#L1174).

Rust casts from float to integer truncate toward zero, map NaN to zero and saturate out-of-range values. Integer-to-float and float-narrowing casts have their own rounding/overflow rules. A bit-exact Rust FP proof must retain these rules and allowed NaN alternatives; a real-number proof or one host's NaN payload does not supply them. This report does not add FP operators to MiniRust. [Reference numeric casts](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/operator-expr.md#L591).

The Target interface still supplies pointer width/alignment, integer alignment cap, byte order, maximum atomic size and valid-size predicate. A maximum atomic width is not a per-operation availability certificate. Both new targets expose `target_has_atomic="ptr"`; the probe records this configuration fact and executes no atomic instruction. Neither target is big endian. The owned 32/64-bit × little/big-endian controls exercise formulas only, not a big-endian compiler/runtime. [Target interface](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/prelude/target.md).

### F2. New native and wasm controls distinguish semantics from layout

Basis: **execution**, `support/primitive.rs`, `primitive-check.mjs`, `runs/results.json`.

The same 32 cases pass on both targets; wasm has no imports. Selected outcomes are:

| Control | Native ARM64 | wasm32 | What the control discriminates |
| --- | --- | --- | --- |
| f32 2²⁴ + 1; integer 2²⁴+1 as f32 | bits 0x4b800000 | same | rounding rather than real arithmetic |
| smallest subnormal + itself | bits 2 | same | these executions retain subnormal result |
| negative zero to_bits | 0x80000000 | same | value equality does not erase representation |
| +∞ / −∞ / NaN as u8 | 255 / 0 / 0 | same | saturating float-to-int casts |
| −1.9f32 as i32 | −1 | same | truncation toward zero |
| 1u8 wrapping_shl(8); checked_shl(8) | 1; None | same | modulo count versus checked rejection |
| i8::MIN checked_div(−1) | None | same | signed division overflow |
| size usize; repr(C) {u8,usize} | 8; 16 | 4; 8 | target-specific word/aggregate certificate |
| packed {u8,usize}; one-field wide-pointer union | 9; 16 | 5; 8 | packed and wide layout dependence |
| Option<NonZeroU8> size | 1 | 1 | selected niche layout, not arbitrary enum validity |

Other cases check narrowing integer casts, u8 overflow result/flag, NaN inequality and propagation to *some* NaN, exact non-arithmetic payload round trip, FP overflow to infinity, two directions of overlapping safe `copy_within`, and an empty copy. Arithmetic NaN payload equality is deliberately not required. These finite outcomes do not establish every FP operator, rounding mode, f64 case, target or optimization setting. Exact case indices and complete output arrays are preserved.

The owned arithmetic control covers signed/unsigned widths 4, 8, 32 and 64 at the overflow/shift boundary. The four width/byte-order union controls preserve abstract pointer-fragment labels while varying metadata bytes. These controls distinguish host Python arithmetic from explicitly bounded modeled operations; they are not an import of the specification.

### F3. Compiler-supplied unions, niches and wide metadata have separate obligations

Basis: **source** + **owned execution**; the union core consequence additionally has reviewed, reused **generated-core execution**.

`translate_enum` consumes rustc's layout, tag type/offset, variant fields, TagEncoding and valid range. Single-inhabited-variant layouts use Known(actual discriminant); directly tagged variants write discriminants and have exact branches with invalid fallback. Niche layouts compute wrapped tags for niche variants, leave the untagged variant's tagger empty, use an untagged fallback and add invalid branches outside the compiler-supplied tag valid range. This imports compiler layout decisions; it does not prove that they implement a Rust enum. The source also translates char as u32 with a documented niche-model limitation, erases pattern-type restrictions, and translates str as [u8]. [Enum lowering](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/enums.rs#L27), [type lowering](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/ty.rs#L181).

The owned niche discriminator checks a wrapping valid byte domain 250..255 ∪ 0..5, with tag 0 selecting None: 12 valid values and 244 invalid values. This is a range/fallback discriminator, **not** a claim that rustc emits that layout for a chosen enum. The independently investigated Known(0) coherence counterexample shows why generic laws over all WF core types require extra coherence; it is not a rustc-produced niche counterexample. [Actual core enum evidence](../minirust-actual-core-disagreement-evidence-d821c6e/REPORT.md).

For unions, `translate_ty` calls `calc_chunks`, which recursively marks data bytes of fields and coalesces them into preserved intervals. Its `Type::Ptr(_)` arm marks only `DefaultTarget::PTR_SIZE`. Core wide pointers instead serialize a data pointer followed by one pointer-sized metadata field. Consider a union with one `*const [u8]` field, size 2p, alignment p: the calculator selects [(0,p)], while the field occupies 2p. Union encode initializes omitted bytes to Uninit. Thus the length word is discarded by a union value round trip. The same issue applies to pointer metadata generally when no other field causes those bytes to be retained. This is a **source-derived importer candidate**, not an observed `minimize` output. [Chunk calculation](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/chunks.rs#L39), [wide pair](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md#L153), [union encoding](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md#L321).

The coordinated [actual-core package, Finding 6](../minirust-actual-core-disagreement-evidence-d821c6e/REPORT.md) executes this 16-byte type on generated MiniRust/Specr using BasicMem and modeled x86_64. The short one-word chunk type passes WF, then pointer→union→pointer returns `Ub("transmuted value is not valid at new type")`; the full [(0,16)] control retains length 3 and reaches MachineStop. Its fixture and logs were read for this report. This validates the core consequence for those ASTs; it does not validate actual importer output, Tree Borrows behavior or a physical Rust ABI.

Wide-pointer validation remains layered. Counts must fit usize; vtables must name an allocated vtable for the expected trait. Safe pointers additionally check total dynamic size ≤ isize::MAX, nonnull/aligned/inhabited pointee and dereferenceability. Raw pointers skip safe-pointee requirements, while retaining metadata checks. Our 26 selected 32/64-bit cases reject oversized counts, wrong metadata kind, wrong-trait vtable, dead/no-provenance nonempty data and misalignment. Aligned nonnull ZST slices with usize::MAX count can pass without allocation provenance because BasicMemory checks no allocation for size zero. Null safe ZST pointers still fail. None of this recursively validates the referent's stored Rust value. [Pointer checks](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md#L490).

### F4. Primitive routes must be classified at the actual library/compiler boundary

Basis: exact Rust/MiniRust **source**; no `minimize` execution for these library APIs.

| Operation | Rust 1.99 source route actually inspected | MiniRust status justified by inspected source |
| --- | --- | --- |
| read_unaligned<T> | cast to alignment-one packed Unaligned<T>, typed read, transmute_neo to T | Constituent typed place/cast operations have core definitions; complete API lowering under MiniRust's requested compiler is unexecuted |
| write_unaligned<T> | construct Unaligned(src), cast destination, typed write | Same conditional route; no dedicated unaligned intrinsic is required by this Rust source |
| typed read/write | read_via_copy becomes MIR Copy of dereference; write_via_move is lowered during MIR building | A typed operation, including value/padding rules; not interchangeable with an arbitrary byte copy |
| copy_nonoverlapping | explicit intrinsic; compiler lowers to NonDivergingIntrinsic::CopyNonOverlapping | That MIR statement is explicitly rejected by d821c6e minimize |
| overlapping copy | ptr::copy calls intrinsic copy | Intrinsic is not in minimize's supported intrinsic match; if it remains such a call it reaches explicit unsupported fallback. A different selected compiler's complete optimized path is unexecuted |
| alloc::alloc::realloc | wrapper → realloc_nonnull → foreign __rust_realloc | No demonstrated implementation expansion/contract binding; foreign-call importer branch rejects foreign items |
| default GlobalAlloc::realloc | allocate new block, copy_nonoverlapping prefix, deallocate on success | This is one default method, not proof that the registered allocator/runtime uses it or that its leaves import |

In particular, classifying current read_unaligned/write_unaligned as necessarily lowering through copy_nonoverlapping would be wrong. `transmute_neo` checks equal sizes in const context and calls transmute_unchecked; Rust's MIR pass lowers that intrinsic to a Transmute cast. Actual importer/compiler/sysroot selection, UB-check configuration, monomorphic T and reachability still have to be bound. Defined constituent core operations are not a verified expansion of the complete standard-library API. [Pointer methods](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L1834), [transmute_neo](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/mem/mod.rs#L1238), [MIR lowering](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/compiler/rustc_mir_transform/src/lower_intrinsics.rs#L152), [import rejection/fallback](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src/bb.rs#L117).

The owned snapshot-copy discriminator enumerates all 285 in-bounds source/destination/length combinations in eight labeled bytes, including 81 empty cases. A forward-streaming mutant disagrees in 34; its smallest stored witness is source 0, destination 1, length 2. Labels retain byte provenance distinctions. This witnesses why overlap requires a snapshot-equivalent contract; it is not execution of either MiniRust copy lowering. The new safe Rust copies supply concrete standard-library controls only.

### F5. Reallocation success, failure and zero size are different contracts

Basis: **documented library contract/source** + **owned contract execution**, with MiniRust allocation **source** from the earlier report.

GlobalAlloc's realloc contract preserves the original prefix on success and transfers ownership: the old pointer is invalid for access even if the numeric address is unchanged. Null failure leaves ownership and contents with the caller. New size must be positive; allocation layout and overflow conditions matter. The default implementation's alloc/copy/dealloc sequence is a source implementation of that method, not a characterization of every allocator. [GlobalAlloc realloc](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/alloc/global.rs#L273), [foreign wrapper](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/alloc/src/alloc.rs#L220).

Five owned controls separate failure preserving the old bytes, in-place success with a fresh capability, moved success, shrinking prefix and invalid zero-size request. These are candidate contract checks, not actual allocator fault injection. The companion library control's `Vec::try_reserve(usize::MAX)` observes a safe capacity error and preserved contents, **not** physical OOM. MiniRust Allocate currently chooses a fresh live allocation and explicitly flags exhausted choice as unsatisfactory “no behavior”; it has no corresponding satisfactory null-failure branch. Address reuse remains distinct from provenance reuse. A sound wrapper must quantify over permitted failure/abort behavior and bind the allocator implementation/interface. [MiniRust basic allocation](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/basic.md#L90).

Panic runtime and callbacks remain contracts on exits and environment interaction. MiniRust implements unwind payloads and Start/Stop/ResumeUnwind; this does not identify the Rust panic runtime with those operations. The [unwind report](../minirust-unwind-elaboration-and-open-client-obligations-d821c6e/REPORT.md) owns the source cleanup mismatch and exceptional restoration analysis. FFI item rejection is an importer boundary, not a semantics for foreign clients.

## Boundaries

**Completed bounded research:** exact numeric/import inventory; explicit Rust FP semantics for the tested cases; two real target controls; union/niche importer review; mixed metadata/overlap discriminators; actual library primitive routes; failure/zero-size ownership contract distinctions. `coverage.json` maps MR09/MR10/MR17 subquestions to these findings and earlier owned coverage.

**Stronger claims unestablished:** target-parametric layout/representation theorem, FP MiniRust extension, source-to-core lowering correctness, full enum/union coherence, verified allocator/runtime and environment adequacy. These are future design/proof goals; their absence is not an unperformed 32-case experiment.

**Genuinely unexamined experiments:** actual minimize output for the wide-pointer union and the selected library operations with its requested compiler/sysroot; big-endian Rust execution; actual OOM/fault injection; complete niche/recursive-DST families and malformed UnsafeCell masks; all atomic-operation availability. These are not silently converted into unsupported outcomes. No broad upstream build or invalid Rust was attempted in this package.

## Evidence

Observed 2026-10-14. `source-evidence.json` records source revisions, blob SHAs, primary links and selected lines. `reused-evidence.json` identifies the earlier reports and the exact reviewed actual-core fixture/result/log hashes. New `support/runs/commands.json` and stream logs preserve 11 successful commands, exact versions/configurations, owned outputs and native/wasm result arrays. Python is 3.9.6. A draft compile failed with E0277/E0599 because an extern-C function item was passed directly as an iterator closure; wrapping it in a closure corrected the fixture before any execution. This setup diagnostic is preserved in results and is not semantic UB.

An independent direct-compiler replay exposed a missing linker-runtime prerequisite: rust-lld aborted before producing wasm because its @rpath did not find libLLVM.dylib. Native results were unaffected. The library exists in the same selected compiler sysroot/lib. The revised helper queries that sysroot, checks the library identity, records the linker version and sets subprocess-only DYLD_LIBRARY_PATH for wasm linking. This is an environment repair, not an object-language outcome. An independent fresh replay with direct rustc and no ambient DYLD override passes all13 commands,32 native and32 wasm cases, the import-free wasm check and unchanged historical wasm hash. The computed shift predicate passes its valid/invalid boundary controls. `support/independent-replay/` retains that evidence and the original aborted-link regression; no abort is counted as a semantic outcome.

No kernel proof, full test suite or native/Miri comparison is claimed. The coordinated generated-core run has separate MiniRust/Specr/nightly identities and a portable replay in its own package. Node's runtime identity is the strongest recorded runtime version tuple; no reproducible-runtime binary hash was acquired.

Historical independent-replay command/log display paths are explicitly normalized for publication. `public-path-projection.json` records original and public hashes; historical producer hashes describe original observations. Raw statuses and technical results are unchanged, source/program bytes are unchanged, and the package file manifest binds published bytes.

## Revalidation

In a disposable package copy, run `python3 support/revalidate.py /path/to/existing/rust-std-wasm32-component`. It writes only beside the script, copies the target component, reruns the two targets and checks expected output. Review source-to-control correspondence before trusting unchanged outputs after a source change. For the union, rerun the companion core package and then separately obtain actual minimize output with its exact requested toolchain; a core AST control cannot discharge that final importer correspondence.

*Authored by an AI agent acting on joshlf's behalf.*
