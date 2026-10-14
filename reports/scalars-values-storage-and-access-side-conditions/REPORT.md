# Scalars, values, storage and access side conditions

## Summary

Value equality, byte representation, initialized storage and authority to access storage require different certificate propositions. Aeneas scalar definitions supply concrete model endpoints; the PR's mathematical layout/storage laws supply reusable geometry and decoder facts. Neither establishes that a physical Rust operation has the same behavior.

The derived obligations below separate these layers and identify source seams where their evidence must survive. In particular, the four named MIR pointer-cast families remain distinguishable through their retained source/target type classes; a shared CastKind bucket alone is not evidence of semantic information loss.

## Applicability

The directly inspected subjects are the full revisions in REPORT.json. Rust core source is `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, corresponding to the inspected 1.99.0 documentation header; it is a semantic-contract snapshot, not Charon's compiler binary identity. Rust Reference revision `2dafab96d919d6ab2884488e970bf95610ff83eb` is a separate normative source. Charon's compiler toolchain selects nightly-2026-09-17.

The cce Memory/Storage library is mathematical source inspected read-only. It was not rebuilt here. Aeneas scalar files and translator cases were directly inspected but not replayed with a fresh upstream build. Original relations are proposed certificate interfaces, not claims of complete unsafe Rust support.

## Findings

### Concrete scalar and cast endpoints

Basis: normative + source; required bridge is derived.

The [Reference operator rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/expressions/operator-expr.md#L25) make overflow behavior configuration-sensitive; integer division by zero panics, and signed minimum divided by −1 has a mandatory overflow check. Numeric casts truncate/extend, or use specified floating conversions; lazy Boolean operators omit evaluation of an unnecessary operand. These source behaviors cannot all be modeled by unconstrained mathematical arithmetic.

Aeneas [Scalar/Core.lean 50–84](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Core.lean#L50) represents unsigned/signed values by BitVec and projects Nat/Int; isize/usize widths use System.Platform.numBits. [Ops/Div.lean 17–25, 405–428](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Ops/Div.lean#L17) has explicit zero/overflow failures and success specifications under nonzero/nonoverflow premises. [Scalar/Casts.lean 18–44, 110–148](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/backends/lean/Aeneas/Std/Scalar/Casts.lean#L18) implements bit-vector truncation/extension and bounds-conditional mathematical-value specifications.

Derived scalar certificate must bind actual Rust type, target word width, operation mode, arithmetic/cast semantics, guard evaluation and failure outcome to the exact builtin denotation. A success theorem's arithmetic preconditions must be established by caller state/invariants; they cannot simply exclude all overflowing source behavior from a safety claim. An unchecked operation needs bad-reflection on failing inputs or a proved invariant ruling them out at each call. Floating values additionally need rounding, NaNs, infinities and signed-zero rules; full float/backend correspondence was not investigated here.

Charon [translate_bodies.rs 1272–1338](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/bin/charon-driver/translate/translate_bodies.rs#L1272) groups pointer casts while retaining source and target types. [TyKind](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/type_level/types.rs#L22) distinguishes scalar, raw pointer and function pointer/definition types; [CastKind](https://github.com/AeneasVerif/charon/blob/cf02e3f228f97ee7be3a415be56989053063326d/charon/src/ast/bodies/expressions.rs#L179) retains both types.

| Named MIR operation | Retained type-class pair, derived from the inspected import |
| --- | --- |
| PtrToPtr | raw pointer → raw pointer |
| FnPtrToPtr | function pointer → raw pointer |
| PointerExposeProvenance | pointer → integer |
| PointerWithExposedProvenance | integer → raw pointer |

These pairs distinguish the four named cases for well-typed input; no same-retained-fields/different-semantic-operation witness was found. MutToConstPointer/ArrayToPointer and other coercions still require their own type-sensitive rule. Aeneas [SymbolicToPureExpressions.ml 568–598](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/src/symbolic/SymbolicToPureExpressions.ml#L568) only supports raw casts between pointers to scalar types at this conversion point, and rejects function casts, transmute and dyn concretization. This is an implementation boundary, not evidence that exposing provenance is modeled by a pointer-to-pointer identity.

### Representation and validity authorities

Basis: normative contracts + derived consequences.

[Reference layout](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/type-layout.md#L5) gives guarantees rather than a fixed layout across compilations. Rust representation permits field reordering and coincident ZST addresses; DST-pointer size has a lower bound, not a universal two-word guarantee. Layout equality of pointers/references does not establish interchangeable access semantics.

[Reference validity](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md#L115) distinguishes initialized scalars/raw pointers, Boolean range, valid enum discriminants/fields, reference constraints and wide metadata. Invalid production is immediate UB. Union validity and aspects of aliasing/reference validity remain explicitly unsettled. A complete certificate cannot silently resolve these unsettled rules as universally established Rust semantics.

Derived representational bridge should be indexed by exact Rust type instantiation and target/configuration, not only by a Lean carrier. Define a relation Rep(T,target,bytes,logicalValue) with its validity/initialization requirements and a separate Access(state,pointer,operation) proposition. Address interval arithmetic establishes neither one automatically. When pointer-containing bytes matter, a byte relation may need provenance fragments from the chosen semantic authority; replacing them with integers can erase relevant information.

### Typed transfer, byte copying and packed access

Basis: standard-library contracts + derived interface.

At the pinned core source, [ptr::read 1606–1620](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L1606) leaves source storage unchanged and requires valid initialized typed input and alignment, including ZST alignment. [copy_nonoverlapping 466–495](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L466) performs an untyped copy preserving initialization state, with readable/writable ranges, alignment and nonoverlap; using both copies of a non-Copy value can violate safety. [read_unaligned 1759–1785](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/ptr/mod.rs#L1759) does not authorize first forming an unaligned reference. The same pointer module documents stronger Strict Provenance support and less settled exposed-provenance semantics.

[MaybeUninit source 205–225, 269–317](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/mem/maybe_uninit.rs#L205) permits uninitialized storage and warns that typed moves/copies may lose initialized padding. An assumed-initialized value must satisfy T's requirements; MaybeUninit does not automatically run T's destructor. These are distinct from an untyped copy's initialization-preservation contract.

Derived certificate consequences: a typed value transfer preserves the logical value only with an explicit permitted padding effect, source initialization/move status, ownership/drop responsibility and destination validity. A memcpy-style rule preserves the relevant raw representation but does not automatically create two independent owners. A packed raw access can be allowed by its exact primitive rule while intermediate reference creation remains forbidden. A ZST's empty byte footprint does not eliminate alignment, metadata, lifetime or logical resource obligations.

### State and heap obligation matrix

Basis: derived original certificate design, constrained by the primary authorities above.

The following propositions are required interface obligations. They are not claimed upstream proofs.

| IDs | Transformation | Required state/representation certificate |
| --- | --- | --- |
| P079, P087 | Pointer/address exposure, arithmetic, cast | Preserve allocation/lifetime and chosen provenance semantics; justify in-bounds offsets, target width and metadata. Equal numeric addresses alone are insufficient. |
| P080 | Erase permission/borrow structure | Preserve read/write authority and every bad access prefix. A ghost permission cannot be manufactured because the final logical value looks valid. |
| P081 | Layout/ABI normalization | Bind size, alignment, offsets, discriminant/niche and target ABI to exact instantiated Rust type; distinguish guaranteed layout from observed compiler layout. |
| P082 | Packed field and unaligned access | Preserve the exact access operation and all intermediate reference formation; use a raw unaligned primitive rule where justified. |
| P083 | Initialization and padding abstraction | Preserve initializedness of required bytes; allow only justified padding effects. A representation decoder is not a physical-memory load. |
| P084 | Logical ADT / niche conversion | Relate valid discriminant, active fields and niche encoding. Reject invalid production before entering a carrier that has no invalid constructor. |
| P085 | Move, copy, assignment, call/return | Preserve source/destination storage effects, ownership, validity and destructor obligations; mathematical value equality does not transfer storage rights. |
| P086 | Allocate, free, reuse, failure | Relate allocation identities/epochs, live extents, failure outcomes and deallocation ownership. Reuse of an address does not revive an old pointer's authority. |
| P088 | Slice/DST/ZST conversion | Relate metadata, dynamic size/bounds, alignment and element permissions; handle zero-size empty footprints and target arithmetic explicitly. |
| P089 | Heap restructuring / alias collapse | Relate all observable aliases and future writes, frame permissions and disjointness; independent pure values cannot duplicate an exclusive resource. |
| P090 | Interior mutation / projections | Preserve UnsafeCell-dependent permissions and effects; every projection has source validity obligations even if its result is unused. |
| P074–76, P091 | Scalars, ADTs, builtin replacement | Bind mathematical operations to exact machine-value/failure semantics and external contracts, with independent domain coverage. |

Derived heap-model comparison: a byte heap can retain invalid representations, initialization masks and provenance, but requires typed access/decoding rules. A typed heap simplifies validity and field reasoning, but must still represent partially initialized or invalid source states at their failure boundary rather than manufacture a valid T. Pure collections simplify functional proofs only when aliasing, access authority, transfer effects and relevant interference have a proved state relation. This is a representation choice with different obligations, not a ranking by convenience.

The [UnsafeCell contract 2149–2162, 2221–2229](https://github.com/rust-lang/rust/blob/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/core/src/cell.rs#L2149) changes shared immutability, not exclusive uniqueness or race rules; its inner-layout guarantee does not extend automatically through niche-using outer types. Derived: syntactic wrapper removal needs a semantic relation for both enclosing representation and permitted effects.

### Exact mathematical bridge and its limits

Basis: directly inspected cce source + derived application.

In [Rust/Memory.lean](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/lean/Rust/Memory.lean#L23), Allocation/Referent bound Nat-address footprints. FitsInAllocation combines footprint inclusion with endpoint bounds, including empty-footprint endpoints. Its theorems transfer numerical bounds; the file explicitly supplies no existence, liveness, initialization or access authority.

In [Rust/Storage.lean 26–96](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/anneal/lean/Rust/Storage.lean#L26), AMByte distinguishes uninit/init; BitDecoder.run checks width and run_length proves accepted width. Initialized is an additional decoder law. boolDecoder rejects initialized byte 2 and uninitialized input (159–162); arrayDecoder_initialized transfers an element initialization law to an accepted array (216–221). These are mathematical representation/decoder propositions, not physical Rust read theorems.

Derived complete bridge has three stages: actual storage state/access → permitted abstract bytes, abstract bytes/type validity → raw logical carrier, raw carrier → consumer ghost domain. Each arrow needs failure reflection and coverage for its claimed domain. A successful second/third arrow cannot supply the first. The cce [consumer semantics](https://github.com/google/zerocopy/blob/cce761ad53785973ec2f4a6b13715b770b340c87/verification/aeneas/SEMANTICS.md#L95) accordingly retains concrete byte/ABI/primitive correspondence premises.

## Boundaries

This answers the certificate-side-condition and named source-seam questions. No complete heap transformer, general typed-storage model, aliasing model or provenance adequacy theorem was proved. Allocation/reuse, all float cases, full union rules, arbitrary interior mutation and concurrent atomics remain genuine research gaps. Rust's unsettled rules require an explicit selected authority and residual premise.

Implementing these interfaces in future Anneal is future engineering; it is distinct from the researched difference between representation facts and runtime access authority. No LLVM-wide correctness claim, numerical proof-cost claim or current full unsafe Rust support follows from this inventory.

## Evidence

Primary files and blobs: Rust ptr `8b8a65d630189dbd98fa8ccfaa54d89665f5e291`, MaybeUninit `6275d7cd59a2c2fc82514082f4e87bf2cc7990db`, cell `2dc2c5981cafddb5cb7ceeabdadb269d52416ac7`; Reference layout `9d56ea757019745702ab5b50c04e129a073bee5d`, validity `ff34d0af28ca3ec42f548abf6cd3bce5840a6798`, operators `3b63884a5e445787078c19422fe627105e2a4933`.

Aeneas Scalar/Core `e066fff573f3bc51b18c26a8c770c79ea67b7173`, Div `7a99c7e89c5778956ec4d4d2c62b8f5326dcc7e4`, Casts `5047d34876b38b9c9443f4a906501e27dc58ac99`, SymbolicToPureExpressions `5d575dfd639cfb243c32a467759c5482c165a1cf`. Charon import/type/cast blobs are named by the immutable links and the companion pass inventory. cce source was read at the exact local commit; no upstream source mirrors are retained.

## Revalidation

Reinspect the named typed-cast arms and retained type classes before claiming information loss; demand a collision witness for that claim. Recheck scalar widths/failure definitions, current normative/library contracts and exact instantiated ABI/layout. Any changed primitive or memory representation requires a new bridge review. Local package validation checks structure only; this report has no executable Rust/heap adequacy experiment.

*Authored by an AI agent acting on joshlf's behalf.*
