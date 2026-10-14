# Typed storage, conversion exits and destructor obligations

## Summary

Type validity, initialized representation bytes and ownership are distinct. Untyped copying preserves initialization state; by-value transmutation does not promise padding preservation. `MaybeUninit` permits uninitialized representation, whereas `ManuallyDrop` suppresses destruction without relaxing its payload's validity. A conversion must track ownership separately on success, validation failure and panic.

At zerocopy `cce761ad53785973ec2f4a6b13715b770b340c87`, `try_transmute` suppresses the source destructor before validation, reads the destination only on success and restores source ownership on failure. The Lean storage/model interface separately retains physical byte admission and mathematical admission. These inspected mechanisms identify proof obligations; they are not a full source-safety certificate.

## Applicability

The source case is the PR stack at the exact commit above, tree `1292218b60e07c576be420f09c767d368c45ec27`, remote `https://github.com/google/zerocopy.git`. Worktree files were compared byte-for-byte with `git show` at this commit. The Rust contracts are from `rust-lang/rust@d8ef4f3fe7031514cbd7d056b7b058814987ecec`, and Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. Those contract snapshots are not silently assigned to all supported zerocopy toolchains. No zerocopy extraction/build, Lean proof checking, allocator execution or uninitialized-byte experiment was run.

## Findings

### Typed validity does not imply initialized padding or exact byte preservation

The standard-library `copy_nonoverlapping` contract copies the stated byte extent, permits uninitialized or type-invalid contents and preserves initialization state. It still requires readable/writable ranges, alignment and nonoverlap; zero-byte copies retain the alignment precondition. Copying a non-Copy payload does not authorize using both owners. Basis: **normative** operation contract, [copy](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/ptr/mod.rs#L458).

`transmute` is a by-value bitwise move with source/result validity requirements; its documentation specifically declines padding preservation. `MaybeUninit` documents that padding need not be initialized for `assume_init`. Thus a rule that represents every native typed transfer as an exact list-of-initialized-bytes copy is too strong without a representation-specific premise. This is a **derived** implication from **normative** API contracts, [transmute](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/intrinsics/mod.rs#L783), [MaybeUninit](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/mem/maybe_uninit.rs#L57).

The Reference's array layout supplies element stride and alignment, but not initialization of an element's padding. Struct/union layout similarly specifies geometry without initializing its bytes. This prevents an array/record proof from deriving a byte-read permission solely from a size calculation. Basis: **normative** + **derived**, [layout](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-layout.md).

### Physical admission and mathematical decoding are independent in the PR model

`Rust.Storage.AMByte` distinguishes uninitialized and initialized bytes. `Initialized` quantifies over every representation byte, including padding. `BitDecoder.run` first checks width; `BitDecoder.Initialized` is a separate law over all accepted representations. Successful bool decoding accepts only initialized 0/1; array decoding uses consecutive equal-size chunks and its initialization theorem requires the element law. Basis: **source**, `anneal/lean/Rust/Storage.lean:30–85,108–168,174–234`.

`RustModel` retains the exact provider, a mathematical `decode`, and optional physical `representation`. `initializedRepresentation` is false when the physical decoder is absent and otherwise requires its initialization law. It does not restrict the quantifier through a narrower mathematical decoder. `decodeBitsResult` rejects absent models/physical rejection before producing a raw value; `decodeResult` separately preserves prior failure/divergence and rejects unadmitted returned values. `spec_decodeResult_iff` and `dspec_decodeResult_iff` preserve total/partial correctness distinctions. Basis: **source**, `verification/aeneas/lean/RustModel.lean:31–137`.

The displayed Lean declarations describe these pure/model transitions. A native Rust representation relation, including typed transfers and provenance-bearing bytes, remains an explicit premise when using them. Mathematical rejection is not automatically native Rust UB: the source comments and `decodeResult` documentation retain that distinction. Basis: **source** + **derived**.

### By-value conversion has different ownership exits

The exact case `zerocopy/src/util/macro_util.rs:525–591` has `Src: IntoBytes`, `Dst: TryFromBytes` and a compile-time equal-size assertion. It constructs `ManuallyDrop<ReadOnly<Src>>` before obtaining a candidate destination pointer. The cast is `CastSizedExact`; validation runs on a reborrowed shared `ReadOnly<Dst>`. Basis: **source**, [case trace](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy/src/util/macro_util.rs#L525).

| Exit | Inspected source transition | Resource obligation consumed |
| --- | --- | --- |
| Validation returns true | `read_unaligned` produces destination; return unwraps `ReadOnly<Dst>` | Exact readable live range, initialized/valid Dst, no intervening mutation, source no longer used/dropped |
| Validation returns false | `ManuallyDrop::into_inner`, then `ReadOnly::into_inner`, returns source inside error | No destination read occurred; original ownership is restored once |
| Validation panics | No destination read appears before the validation branch | Suppressed source destructor may leak; no duplicated destination owner may be exposed |

The source's detailed safety comment explicitly traces non-nullness even for ZST, provenance/range preservation, absence of mutation between validation and read, and suppression of duplicate ownership use. Those are **source assertions**. The `read_unaligned` contract supplies a bitwise copy and its initialized/readable-range obligations; `IntoBytes` and `TryFromBytes` supply library implementer laws. A complete derivation still has to establish the selected dictionary and exact cast/ReadOnly invariants and apply the cited documentation to the supported configuration. This report records the trace, not a universal `PROVED` verdict. Basis: **normative**, **source** and **derived**.

### Partial initialization and destructor suppression need independent state

`MaybeUninit<T>` permits uninitialized data and its own drop performs no T destruction. Initializing an array prefix therefore needs a separate prefix count or ownership map if the promised behavior includes cleanup on unwind. Leaking initialized elements can be memory-safe but does not satisfy an independently promised cleanup guarantee. `ManuallyDrop<T>` retains T's layout and bit validity; a destroyed payload must not be exposed through a safe access path and destruction must not repeat. Basis: **normative** contracts, [MaybeUninit array example](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/mem/maybe_uninit.rs#L118), [ManuallyDrop](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/mem/manually_drop.rs#L9).

The pinned ManuallyDrop documentation explicitly labels the historical drop-then-move Box restriction as pre-1.96. This version-sensitive statement must not be propagated unchanged across Rust versions. The source snapshot does not authorize retroactive rewriting of older contract premises. Basis: **normative** versioned documentation, `manually_drop.rs:94–144`.

Rust's `forget` contract says unsafe abstractions must tolerate a caller not running a returned value's destructor. A proof may require a destructor before *storage reuse* in a pin protocol, but cannot infer that a safe caller will eventually destroy every guard. Leaks, unwind cleanup, double drop and functional cleanup guarantees therefore need separate dispositions. Basis: **normative** + **derived**, [forget](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/mem/mod.rs#L87), Reference `destructors.md`.

### Allocator identity, reallocation and capacity are separate resources

`GlobalAlloc` distinguishes trait methods from global allocation functions and forbids mixing their returned allocations/deallocation APIs. It permits optimization to skip or merge global allocator calls; counting those calls is not a semantic allocation-count guarantee. Its documentation distinguishes initialized contents, allocation size/alignment and derivation from the returned pointer. Successful reallocation deallocates the old block; failed reallocation retains it. Basis: **normative** contracts, [GlobalAlloc](https://github.com/rust-lang/rust/blob/d8ef4f3fe7031514cbd7d056b7b058814987ecec/library/core/src/alloc/global.rs).

The exact trait-method contracts require nonzero size for `alloc`/`alloc_zeroed`, and positive new size plus rounded isize bounds for `realloc`. Null indicates failure; successful `alloc_zeroed` initializes the block. Unwinding from a global allocator is forbidden at this snapshot. These method-level facts cannot be substituted for every safe container's zero-capacity/OOM policy. Basis: **normative**, `global.rs:158–160,197–209,245–252,273–305`.

Consequently a realloc rule must split success/failure, transfer the deallocation token, retire old access rights on success even if the numerical address matches, and initialize only the promised new bytes. Allocator-wrapper OOM/abort versus recoverable error, Vec capacity and initialized length must match the particular API. The acquired `RawVec` file is an implementation lead, not proof of every allocator or std::Vec release. Basis: **derived**. Complete current Vec and allocator-wrapper paths remain unexamined.

### The checked byte-copy model exposes its trust boundary

`Zerocopy/FunsExternal.lean:27–79` models whole opaque raw-pointer helpers. `copy_unchecked` receives readable source and exclusive destination slice premises and guards destination length; its modeled bytes are U8 payloads. Offset copying preserves prefix and suffix and distinguishes checked-subslice panic from forbidden oversized copy. `transmute_unchecked` supports only original U8-to-Bool instantiation and rejects invalid bytes before constructing Bool. Other instantiations fail closed. Basis: **source**.

These checks prevent unsupported/invalid cases from becoming ordinary success, but they do not themselves derive physical reference validity or byte-preserving arbitrary T movement. The file exposes layout parameters as unconstrained data axioms and separately identifies an Aeneas subslice-reconstruction limitation. A future bridge must preserve failure/divergence and exact source arguments before erased generic types lose this distinction. Basis: **source** + **derived**.

## Boundaries

- **Not examined:** exhaustive source/dictionary/configuration closure of the PR, all partial-initialization algorithms, unwind/abort code generation, current Vec allocator paths and OOM policy.
- **Unknown:** a source correspondence theorem for native typed storage transfers, raw-pointer helper models and optional representation decoders.
- **Known not to apply:** language-valid T alone does not entail initialized padding or unrestricted duplicate ownership; the checked transmute model does not support arbitrary Src/Dst.
- **Not examined:** reading padding/uninitialized memory, native drop-count experiments for zerocopy or fresh Lean checking. No UB experiment was used as evidence.

## Evidence

`source-evidence.json` binds PR files to their Git blob and SHA-256 values and Rust contract files to exact commits/blobs. Reads occurred 2026-10-14. The source trace deliberately retains library laws as obligations rather than treating existing safety comments as proofs. Language/stdlib statements are **normative** for their identified snapshots; model declarations and code are **source**; transition implications are **derived**. No new execution establishes this PR's soundness.

## Revalidation

Diff the concrete converter, cast implementation, ReadOnly representation and selected trait laws together. Reconstruct all exits before widening coverage. For each physical decoder, check its entire language-valid domain, not only mathematically accepted values. Revalidate the exact read/copy/transmute/drop/allocator contracts for each claimed version and configuration. Test a model's rejection behavior separately from proving its source representation relation.

*Authored by an AI agent acting on joshlf's behalf.*
