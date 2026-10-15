# Aeneas type, trait, closure and standard-library interfaces

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The inspected Aeneas source translates a substantial generic and trait-bearing safe-Rust subset into explicit functional interfaces. It erases ordinary references in target types, passes trait dictionaries and associated-type information, preserves mutation through returned values and backward functions, and maps selected standard-library operations to handwritten Lean models. These are selective contracts, not admission of all safe Rust or an execution model for unsafe memory.

Three restrictions materially qualify the interface: the README excludes instantiating generic types with mutable references; the symbolic-to-pure translation has explicit GAT/function-pointer and complex-binder limits; and the default statement interpreter treats Drop as a no-op. Current Result is an interaction tree over RustEffect, not a three-constructor inductive datatype. Scalar arithmetic families and collection models have different failure and resource abstractions which clients must keep distinct.

## Applicability

This report answers G07 / A19–A23 using **source** and **documentation** inspected at Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`. Source excerpts, exact paths, blob coordinates and fetch misses are preserved in [source-index.json](source-index.json). No Rust, Charon, Aeneas or Lean execution, target compilation, theorem checking, build, installation or reproduction was performed.

The coordinating Charon source pin is `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`. However, Aeneas's own [charon-pin](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin) declares `1aebab5f03a58067e5dc0ede2fec584117f54964`. This report characterizes the Aeneas source and the interfaces it expects; it does not assert that the coordinating pair is a tested compatible bundle. The inspected Lean toolchain file selects `leanprover/lean4:v4.35.0-rc4`.

| Crosswalk | Subject actually examined |
|---|---|
| A19 | ADTs, reference/Box erasure, type/const generics, associated-type representation, universes and restrictions. |
| A20 | Explicit trait references, parent clauses, default methods, model dictionaries/laws, FnOnce/FnMut/Fn interfaces, callable kinds and closure lifetime repairs. |
| A21 | Scalar widths, arithmetic/overflow families and representation boundaries. |
| A22 | Interaction-tree failure interface and panic/unwind/Drop admission. |
| A23 | Arrays, slices, vectors, allocation/raw-pointer abstraction and model registration contracts. |

## Findings

### Support matrix: representation is not a blanket language promise

Basis: **source** in SymbolicToPureTypes, ExtractTypes, PrePasses, Core/Ops, scalar and container modules, plus the pinned README's stated limitations.

| Rust feature/input class | Current source-established handling | Material qualification |
|---|---|---|
| Structs/enums and tuples | Type-declaration translation maps fields/variants; tuples use simplified tuple types. | Positivity and recursive grouping are backend concerns; this audit did not typecheck a generated recursive ADT. |
| Shared/mutable reference types | Signature and forward translation erase the reference constructor and translate its referent. | Borrow checking and backward reconstruction happen before/around this erasure. Target erasure alone cannot justify aliasing-sensitive code. |
| Box | Builtin Box signature types reduce to the contained type; deref/deref_mut models are value and value-plus-replacement-function. | No allocator identity, allocation failure, address or layout is retained by these models. |
| Arrays/slices | Array carries element type and length const generic; slice carries element type. | Array length is modeled with Usize; container length proofs are explicit; no byte layout follows. |
| Generic type parameters | Types and const generics are translated; trait references become explicit arguments. | README excludes mutable-reference instantiations, including Self through trait implementation. This is broader than merely forbidding a literal `id(&mut x)` call. |
| Const generics | Supported parameter types must be scalar types; selected literal/global/variable constant-expression kinds translate. | Other kinds fail with an unsupported-constant diagnostic; this is not arbitrary const evaluation. |
| Associated types | Trait-type references and constraints have translation paths; ordinary associated types are often parameters after Charon normalization. | ItemClause explicitly rejects GATs; trait-associated arguments must match constrained expectations. |
| Trait implementations/supertraits | Explicit dictionary/parent-clause representation and builtin-instance handling. | Only enumerated BuiltinOrAuto cases are admitted by the inspected branch. Method models may intentionally cover a subset of a Rust trait. |
| Generic trait methods | Extracted type parameters inside trait structure fields stay in Lean Type. | Ordinary item parameters use Type _; this is not unrestricted universe polymorphism throughout traits. |
| Function items/closures | Forward type translation can convert eligible TFnDef items to function types; Fn traits model callable interfaces. | Signature translation rejects arrow kinds; forward branch requires no binder regions, an ordinary function ID and compatible failure effects. |
| `fn(...)` pointer types | Explicit TFnPtr rejection in the inspected type-translation paths. | Function-item support must not be reported as function-pointer support. |
| Dynamic traits | Forward TDynTrait has a restricted representation; target extraction accepts a narrow shape. | Signature translation and borrow-projection paths still reject dynamic traits; Config acknowledges region-analysis limitations. No general dyn support conclusion. |
| Float/char/string literal kinds | Literal/type translation and float target-name branches exist. | This audit did not inspect a complete floating-point model or validate IEEE operations; presence of F16/F32/F64/F128 names establishes only printer handling. |
| Unions/opaque/error declarations | Type declaration kinds become Opaque in the inspected translator branch. | An opaque target declaration is not a verified implementation of union memory behavior. |
| Raw pointers | Converted to a typed RawPtr model with Mut/Const tag; selected scalar cast returns undef failure. | The model is a value wrapper, not pointer provenance, layout, validity or allocation semantics. |
| Drop/unwind | Drop statement defaults to no-op; optional evaluation performs local drop bookkeeping; UnwindResume errors. | A Drop trait record/model exists independently. Full destructor execution and Rust unwinding are not established by either representation. |

### A19: type translation has several different notions of type

[SymbolicToPureTypes.ml](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureTypes.ml) distinguishes signature, forward and backward/projected type translation. In `translate_sty` (lines 137–198), a reference maps recursively to its referent, Box disappears, arrays become a builtin with one type and one length argument, slices become a builtin with one type argument, and trait-associated types retain a translated trait reference plus associated name. A callable type rejected in this branch can still have a separate permitted representation in forward translation; the forward TFnDef case around lines 397–425 demonstrates why a one-word “closures supported” label loses necessary scope.

`translate_generic_args` (lines 58–72) explicitly drops regions while translating types, constants and trait refs. Its comment conditions that erasure on the preceding symbolic-execution handling. Therefore it is not a standalone semantics for lifetimes; the region-sensitive obligations belong to the earlier interpreter and signature decomposition. A target type contains less information because the translator has already used that information, not because arbitrary Rust lifetime structure is irrelevant.

`translate_region_binder` (lines 11–17) simply takes binder_value. Its source comment acknowledges de Bruijn shifting would be needed in complex binding situations and says these are not yet handled. This is an explicit implementation boundary, not a proof that dropping binders is always valid. Type aliases are expected to have been removed before declaration translation; seeing an alias there is an error. Union, opaque and erroneous declarations map to Opaque rather than a concrete field model (lines 274–284).

[ExtractBase.type_keyword](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/ExtractBase.ml#L1460-L1477) prints `Type _` for polymorphic Lean binders and `Type` where levels cannot be inferred. [ExtractTypes](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/ExtractTypes.ml#L1368-L1379) explicitly uses the latter for generic trait-method parameters inside structure fields; opaque type result sorts also use a nonpolymorphic keyword. Consequently universe generalization at ordinary generic items does not establish that every associated type or generic method can accept a higher-universe instantiation.

### A20: traits are explicit operational dictionaries, not automatic laws

The Lean [Core/Cmp models](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Core/Cmp.lean) make the operational distinction concrete. PartialEq is a record containing effectful eq/ne functions. Eq contains a PartialEq dictionary and an assert_fields_are_eq method whose default returns unit. PartialOrd contains its PartialEq parent plus partial_cmp and default comparisons. Ord contains Eq and PartialOrd parents plus cmp/max/min/clamp. These records contain no reflexivity, transitivity, antisymmetry or agreement proof fields. Rust trait selection therefore does not manufacture Lean proofs of mathematical equality or order laws.

The local `PartialEq.ne.default.spec` requires a hypothesis that the supplied eq computes logical equality (Cmp lines 42–51). That premise is evidence of the intended proof interface: the derived logical guarantee is conditional on a law for the dictionary, rather than inherent in any inhabitant of the record. Likewise an arbitrary custom cmp can disagree with partial_cmp unless a client establishes consistency. Default bodies give executable definitions, not a proof that every impl respects all trait documentation.

### A20: closure state and mutation are returned explicitly

The [Fn family](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Core/Ops.lean#L67-L100) preserves three callable shapes:

| Trait model | Method shape | Meaning recoverable from the interface |
|---|---|---|
| FnOnce Self Args Output | Self → Args → Result Output | Consume the supplied callable state to obtain the output. |
| FnMut Self Args Output | Self → Args → Result (Output × Self) | Return both output and updated callable state, including when Output is Unit. |
| Fn Self Args Output | Self → Args → Result Output | Shared callable interface with explicit FnMut/FnOnce parents. |
| BuiltinFn-family for a Lean function | Inputs → Result Outputs | BuiltinFnMut returns the original function as updated state after applying it. |

[PrePasses.fix_closure_lifetimes](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/PrePasses.ml#L1954-L2014) repairs missing relationships between closure inputs and outputs in generated methods. `fix_closure_signature_regions` (lines 2016–2080) repairs erased lifetime arguments of closure types in signatures only when the function binds exactly one region; multiple candidates are left unchanged because the pass cannot guess which was captured. The source labels both as workarounds for Charon issues. This makes closure support dependent on normalization and on specific lifetime patterns. The small [tests/src/closures.rs](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/tests/src/closures.rs) fixture demonstrates the existence of source regression inputs; it was read, not executed here.

### A21: scalar widths and arithmetic, with the A22 effect interface

The pinned [Std/Primitives](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Primitives.lean#L41-L100) defines Result as `ITree RustEffect α`. RustEffect has fail inputs indexed by Error, with PEmpty response type. Result.ok returns a value, Result.fail emits an unresumable failure event, Result.div denotes divergence, and bind delegates to ITree.bind. Error contains assertionFailure, integerOverflow, divisionByZero, arrayOutOfBounds, maximumSizeExceeded, panic and undef. The auxiliary MatchResult type used for matching/printing must not be confused with Result itself. This report relies on those interfaces only; full DWP/DWLP semantics are a separate report subject.

[Scalar/Core](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/Core.lean#L31-L80) represents signed and unsigned machine scalars by bitvectors indexed by the scalar kind. Fixed integer widths are 8, 16, 32, 64 and 128. Usize/Isize use `System.Platform.numBits`; the source proves their bounds equal the 32-bit or 64-bit cases. Unsigned maximum is `2^w-1`; signed minimum/maximum are `-2^(w-1)` and `2^(w-1)-1`. Thus a claim involving usize must record the Lean/model platform width as well as the Rust target. This audit did not validate arbitrary cross-compilation combinations or a mechanism that forces every Rust target to match that platform value.

| Operation family actually read | Current definition | Observable failure/result contract |
|---|---|---|
| Ordinary modeled add | UScalar/IScalar.add delegates to tryMk on mathematical sum. | Result value in range; integerOverflow otherwise. |
| checked_add | Option.ofResult of ordinary add. | Some result or None; not an overflow failure event at this interface. |
| wrapping_add | Bitvector addition directly. | Pure wrapped value, modulo width; no overflow failure. |
| overflowing_add | Bitvector sum plus uaddOverflow/saddOverflow. | Pure pair of wrapped value and overflow flag. |
| saturating_add/sub | Clamp mathematical operation to kind bounds before constructing bitvector. | Pure clamped result; no overflow failure. |
| Unsigned division | Bitvector udiv after nonzero test. | divisionByZero at zero divisor. |
| Signed division | sdiv after zero and minimum/-1 checks. | divisionByZero or integerOverflow for the exceptional pair; truncating signed semantics. |

Sources: [Ops/Add](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/Ops/Add.lean), [CheckedOps/Add](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/CheckedOps/Add.lean), [WrappingOps/Add](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/WrappingOps/Add.lean), [OverflowingOps/Add](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/OverflowingOps/Add.lean), [SaturatingOps](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/SaturatingOps.lean), [Ops/Div](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Scalar/Ops/Div.lean). Scalar.tryMk's failure is defined in Core lines 602–616. These are model definitions, not a claim that every Rust build mode/operator lowers to the same ordinary-add function. MIR lowering, explicit wrapping APIs, overflow options and registry routing are separate parts of that correspondence.

### A22: Drop, panic and unwinding have different boundaries

[Config.drop_as_no_op](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Config.ml#L625-L627) defaults true. [Main's -eval-drops option](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml#L255-L258) clears it. In [InterpStatements](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/interp/InterpStatements.ml#L760-L781), Drop ignores its extra fields and either returns unchanged context or calls `drop_value`; StorageDead always calls drop_value. The latter prepares a write access and places bottom at the location as part of borrow/loan bookkeeping. This inspected branch does not itself call a destructor function field. Explicit destructor calls that Charon has already turned into calls remain a separate Call path. Therefore neither “all destructors are erased everywhere” nor “full Rust destructor semantics is modeled” follows from this code.

Panic, UnwindTerminate and UndefinedBehavior all synthesize a panic node in symbolic mode, or a Panic result in concrete interpreter mode. Assert evaluates its condition but ignores its supplied unwind continuation at the statement match. UnwindResume rejects with an unwinding-not-supported diagnostic. [SymbolicToPure.translate_fun_decl_body](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPure.ml#L33-L48) constructs a result failure for symbolic panic, rather than preserving a Rust stack/unwind machine. These are admission/abstraction facts: modeled failure paths are meaningful for panic-freedom proofs, while absence of a stack/unwind representation means such proofs do not characterize cleanup during caught unwinding.

### A23: collection models preserve contents and lengths

[Array](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Array/Array.lean#L21-L45) stores a length-indexed ListN and proves its exposed list has length n.val. Array.from requires a length equality; Array.make has an explicit equality argument, with a simp tactic default. The model therefore does not silently manufacture arbitrary length proofs merely because a default tactic can fill a valid argument. [SliceDef](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/SliceDef.lean#L10-L35) stores an existential Nat length, ListN of that length and bound by Usize.max. [Vec](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Std/Vec.lean#L25-L55) wraps Slice; it does not include capacity or allocator state. The source explains that ListN and the wrapper choice avoid positivity failures when these models occur inside recursive inductive types.

Array/Slice/Vec checked indexing returns arrayOutOfBounds for failed lookup. Mutable indexing returns the element with a pure replacement function; Vec's usize path returns `(x, fun x => v.set i x)`. For slice ranges, specifications describe the selected contents/length and the reconstruction function under explicit range premises. Bounds are proof obligations, not implicit facts supplied by the type of a Usize index.

Vec.push appends if the new length is representable, otherwise returns maximumSizeExceeded. Vec.insert uses insertIdx and checks capacity, but the current source still requires `i < length`, excluding end insertion from this model's success branch. This exact source fact is enough to prevent a blanket claim of complete Vec::insert fidelity; no execution is needed to read the guard. Vec.extend_from_slice checks the combined length and sequences cloning effects rather than treating an effectful clone as a pure list operation. The presence of one capacity-bound failure must not be described as a general allocator/OOM semantics: the representation contains no heap allocator.

### A23: library registration is an interface contract

A mutable index/deref result contains a focused value and a pure replacement function to rebuild its owner. It is not a pointer. Model review separates mathematical behavior, target ABI, and Rust-name/parameter/effect registration; a local theorem proves the specified model proposition under its premises.

The README describes split templates for missing external models, with handwritten companion files. Registration uses rust_type/rust_const/rust_fun/rust_trait/rust_trait_impl, and make extract-lean-std regenerates ExtractBuiltinLean. Config.filter_trait_impl_methods explicitly permits models containing only a subset of a Rust trait's methods.

CoreConvertNum lines582–612 uses Array U8 for signed and unsigned fixed-width endian conversions; these macros exclude usize/isize. This was source inspection, not exhaustive cast/byte testing. Target.lean supplies get_target, its unconstrained-result specification, and target_feature_enabled as axioms. Alloc removes allocator parameters and models Box dereference as identity. RawPtr wraps a value and mutability tag; its selected scalar cast fails with undef. These facts define model/assumption boundaries, not layout or allocator behavior.

[Extract/Extract.lean](https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/backends/lean/Aeneas/Extract/Extract.lean#L90-L109) records kept type parameters, kept trait clauses, whether a function can fail and whether a nonfailing model should be lifted to Result. Attribute documentation around lines 612–620 explains the canFail/lift distinction. Those flags determine target signature shape and call construction; they are not proofs that the Rust operation cannot fail. keepParams and keepTraitClauses remove erased allocator or other irrelevant arguments only where the model contract specifies them. Parent clauses, associated types, default methods and constructor mappings likewise contribute to a coherent ABI.

## Boundaries

- **Not examined:** a complete Rust language feature census, exhaustive builtin registry coverage, every scalar/float/string/intrinsic operation, all container methods, all borrow nesting patterns, complete Charon normalization at either Charon pin, fresh backend acceptance or fresh proof replay.
- **Unknown:** compatibility of the coordinating Charon pin with this Aeneas revision; complete dyn-trait support beyond the explicitly inspected branches; target-width alignment in arbitrary cross-target configurations; equivalence of every handwritten model with its Rust implementation.
- **Unsupported/restricted by inspected source/documentation:** generic mutable-reference instantiation; GAT ItemClause; fn pointer kinds in inspected type paths; complex region binding; unwind resume; unsafe/concurrent memory as a general current contract.
- **Known not to follow:** raw-pointer type printing implies unsafe semantics; a Drop trait record implies full destructor handling; Eq/Ord dictionaries imply their mathematical laws; successful target typing implies Rust correspondence; a pure array/list representation preserves runtime layout or allocation costs.
- Current Result is interaction-tree based. Historical reports using an inductive ok/fail/div representation must not supply current constructor or reduction facts. Full WP and mechanized semantic results belong to separate packages.

## Evidence

Acquired 2026-10-15. [source-index.json](source-index.json) binds the selected symbol/line excerpts and blob IDs to `21345f80fa212c596f6437378d7d57984fa2ea77`; it also records guessed paths which returned 404 so they cannot be mistaken for inspected source. The Findings link immutable source throughout. The important regions are type translation lines 11–198, 274–284 and 397–428; generic extraction lines 1330–1382; closure repairs lines 1954–2080; statement handling lines 760–781; Scalar/Core representation and tryMk; primitive effect definitions; and the selected registry, arithmetic and collection model definitions.

Documentation claims are attributed to README or source comments. The support distinctions, ABI implications and separation between local model proofs and Rust correspondence are **derived** from the inspected definitions. No **execution** evidence is present.

## Revalidation

For another revision, diff these narrow symbols before revising the support matrix: translate_region_binder, translate_sty/translate_fwd_ty, translate_trait_ref_kind, generic type keyword selection, closure lifetime repairs, Drop/Panic/Unwind statement cases, scalar tryMk/operator families, Array/Slice/Vec representations and rust_fun registration metadata. Check charon-pin and the backend Lean toolchain independently of the requested coordinating pins.

A concrete acceptance check would translate fixtures spanning mutable-reference generic instantiation, associated outputs equal to Unit, function items and fn pointers, single/multiple captured lifetimes, trait law premises, usize widths, every arithmetic family, indexing/reconstruction and conditional Drop/unwind. Such execution is not part of this report. Passing isolated fixtures would establish only those configurations; claims about Rust preservation still require their correspondence evidence.
