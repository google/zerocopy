# Production LLBC, control-flow reconstruction and the MiniRust boundary

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Current Charon LLBC is a rich production representation: typed places, explicit storage, existential body regions, conditional or precise drops, calls with cleanup blocks, intrinsics, explicit UB and several non-executable body variants. It is not automatically the small LLBC calculus studied in a paper or formalization.

The ULLBC-to-LLBC implementation builds a graph including unwind edges, rejects irreducible control flow, heuristically selects exits and converts edges into structured fallthrough, nested loops and depth-indexed break/continue. It supports either code duplication or synthetic one-shot loops for forward jumps. The inspected pass supplies neither a correspondence certificate nor an independent semantic proof checker. A finite positional certificate is a plausible separate validation seam, with divergence and unwind preservation as explicit obligations.

MiniRust export supplies an operational meaning for a restricted, differently configured ULLBC route. It forces monomorphization, precise drops, byte constants and elaborated-or-later MIR. Charon documents MiniRust translation as authoritative for ambiguous statement meanings, but that convention does not prove the exporter preserves Rust, cover every generic LLBC construct, or eliminate documented unsound cases. The harness also records failures beyond those in the short user manual.

## Applicability

Source subject: AeneasVerif/charon `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`, package 0.1.291. Source only; no builds, tests, exporter invocation or MiniRust execution occurred. Root toolchain metadata requests nightly-2026-09-17, not an established installed runtime identity.

The comparison with the Charon dependency `1aebab5f03a58067e5dc0ede2fec584117f54964` declared for Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77` is limited to identical acquired `options.rs`, `transform/mod.rs` and `docs/minirust.md` bytes. Neither complete-repository equivalence nor running compatible heads is claimed. At the upstream Charon pin the `crates/minirust` Gitlink is `c0b555e5b15accc6c1366b1d911a1bfd49c3d9d0`; this records dependency identity, not an audit of that MiniRust implementation.

A08, A09 and A10 are answered below. Paper/formalized LLBC is treated as a separate semantic subject; this report examines the production representation and the observable source interfaces needed for a correspondence argument. The companion extraction/normalization report explains transformations before and after CFG reconstruction.

## Findings

### A09: the production language and semantic distinctions

Basis: **source**, principally [common bodies](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies.rs), [ULLBC](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies/unstructured.rs), [LLBC](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies/structured.rs), [expressions](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies/expressions.rs) and [places](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies/places.rs).

| Layer | Representation and consequence |
| --- | --- |
| Body | Unstructured, Structured, TargetDispatch, Extern, Intrinsic, Opaque, Missing or Error; absence has multiple meanings |
| Shared body data | span, local declarations, return/argument convention, existential region count and comments |
| ULLBC control | numbered blocks, statement sequences, one terminator, regular/cleanup/terminate block kind |
| ULLBC ordinary statements | Assign, SetDiscriminant, StorageLive, StorageDead, PlaceMention, Borrowck, Assert with AbortKind, Nop |
| ULLBC terminators | Goto, Switch, Call, Drop, InlineAsm, Assert, Panic, UnwindTerminate, UnwindResume, Return, UndefinedBehavior |
| LLBC control | sequence blocks with statement IDs; Loop, Switch, Break(depth), Continue(depth), and nested cleanup blocks rather than goto targets |
| LLBC effects | the ordinary statements plus Call, Drop, Assert, InlineAsm, Panic and terminal Return/UnwindResume/UnwindTerminate/UndefinedBehavior |
| Places | Local, Global or recursive Projection, each carrying a type; projections include Deref, Field, pointer metadata, Index and Subslice |
| Values | Copy/Move/constant operands; Use with retag flag, Ref, RawPtr, binary/unary/nullary operations, Discriminant, Aggregate, Len and Repeat |
| Type/evidence data | generic types/regions/constants and trait evidence, associated types and layouts occur elsewhere in the production AST; these are not erased merely by structuring CFG |

Return local is index zero, followed by the argument locals and then temporaries. StorageLive allocates/reallocates a local; StorageDead deallocates with already-dead as a no-op. Non-return locals can be implicitly deallocated at function exit; `--deallocate-all-locals` asks for explicit markers. Storage is therefore semantically relevant, not just a compiler debugging annotation.

PlaceMention checks place validity even though it does not read its value; invalid projections can cause UB. MIR translation elides a mention of a bare local, where its source comments say no such UB arises, but retains projected places. Borrowck statements express FakeRead, type/ascription variance, outlives and trait obligations and are described as runtime no-ops. The translator discards coverage, const-eval counters, no-ops and backward-incompatible drop lint hints. FalseEdge and FalseUnwind select their real runtime target. Thus translated ULLBC is already a selected runtime-oriented representation, even before later normalization.

`AbortKind` distinguishes panic, UB and unwind termination; some statements can fail implicitly without a visible outgoing control edge. ULLBC additionally has explicit assert terminators with normal/unwind successors. Explicit UndefinedBehavior denotes UB to reach; it is not equivalent to a recoverable panic. UnwindResume propagates unwinding to the caller; UnwindTerminate stops it for ABI/double-panic reasons. `translate_unwind_action` maps MIR Continue to a fresh resume block, Unreachable to a UB block, Terminate to terminate, and Cleanup to its translated block. `UnwindKind::further_unwind_kind` sends regular to cleanup and cleanup/terminate to terminate.

`DropKind::Precise` denotes calling `Destruct::drop_glue(&mut place)` and marking the place moved out. `Conditional` may elaborate to partial, conditional or async destruction; the source deliberately leaves exact semantics unspecified and allows unaligned packed fields at that stage. Built/promoted requests therefore cannot by themselves supply one precise runtime-drop operation. Precise-drop mode changes extraction and trait-bound behavior; it is not simply a pretty-printer preference.

The current AST explicitly supports function-pointer calls through `FnOperand::Dynamic`, despite an old adjacent ULLBC statement comment saying dynamic calls are unsupported. Enum variants and the actual translator/exporter arms are stronger evidence than that misplaced historical comment.

### Regions, typing and body availability are separate axes

Basis: **source**.

[`Region`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/type_level/regions.rs) has Var, Static, Body and Erased variants. `GExprBody::bound_body_regions` counts existentially bound body regions introduced in place of rustc-erased regions. [`typecheck_and_unify`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/typecheck_and_unify.rs) checks type consistency and unifies body lifetimes on a best-effort basis; the schedule runs it after translation and after transformations, unless disabled. This does not recover the original lexical lifetime assignment or provide a proof that borrow analysis or execution semantics are correct. Full monomorphization and explicit lifetime erasure are additional configuration choices.

The [Body enum](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies.rs) distinguishes:

- Extern(symbol): a foreign declaration needing an external implementation.
- Intrinsic(name, argument names): backend-defined built-in semantics.
- Opaque: user opacity policy suppressed translation.
- Missing: no body available, for example because of a chosen sysroot.
- Error(error): translation attempted and failed.
- TargetDispatch: a per-target map to function declarations produced by multi-target merging.
- Structured/Unstructured: actual executable syntax in this representation.

These categories cannot safely share one “abstract function” rule. Extern/intrinsic modeling needs an explicit semantics; opaque functions need specified contracts; missing/error entries need admission policy; target dispatch needs an exact selected target and corresponding type/layout data. `Body::has_contents` excludes all of them except Structured and Unstructured.

Serialized AST types use stateful serde support and Charon version checks in `CrateData`; they are implementation interfaces, not a stand-alone declarative typing/evaluation specification. The type checker skips already erroneous items and explicitly accepts some mismatches in copied default methods under contradictory premises checked in their original context. The production language has more syntax than a borrow-calculus core, and exact well-formedness depends on item references, binder arities, local types, jump depth, layout and target information. No total formal evaluation relation for all these constructs was established in this audit.

### A08: reconstruction includes cleanup edges and two output styles

Basis: **source** in [`ullbc_to_llbc.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/control_flow/ullbc_to_llbc.rs).

`CfgInfo::build` creates both the full graph from `targets()` and a graph without unwind successors. Dominators and reverse postorder are computed on the full graph. Edges whose source reverse-postorder number is at least the target number are classified as backward. Their targets become loop headers; each must dominate the edge source. Failure yields `Irreducible`. `translate_body` registers the nonreducible-control-flow error and panics; surrounding transformation recovery determines how the body/error is retained. This implementation does not repair irreducible regions or silently turn them into a general state machine.

The pass then derives loop membership, merge targets, reachability, shortest paths and flow weights. Exit selection uses heuristics: loop/switch exits seek usable shared continuations, with ranking based on reachability/flow/order and preference for normal blocks. Cleanup-only status is computed using the graph without unwind edges. The flow heuristic avoids letting cleanup paths dilute normal-flow exit choice, but unwind-only subgraphs still use their own successors. A loop reaching no error is not classified as error just because it can diverge.

`ReconstructCtx::translate_block_inner` maintains a stack of special destinations. A loop header installs a loop-continue destination and, when chosen, a loop-break exit. Switch exits can become NextBlock continuations placed after a branch. `translate_jump` searches the stack from the innermost context: destinations become depth-indexed Continue/Break, a fallthrough Nop, or recursive block translation. Depth counts lexical loop contexts, including synthetic contexts. This is why source block identity cannot be equated to a single statement number.

With default code duplication, a shared forward continuation can be translated separately in multiple branches. With `--no-code-duplication`, the ForwardBreak mode registers immediately dominated merge targets and creates `loop { ...; break 0 }` wrappers, then places the merge continuation after that wrapper. These loops implement forward jumps rather than source iteration. Actual source loops receive continue behavior; ForwardBreak mode appends explicit continue at their tails. `remove_useless_jump_blocks` later removes redundant wrappers and adjusts break/continue depths.

The option documentation explicitly warns that consumers expecting source-shaped if/loop bodies, including Aeneas, may not support ForwardBreak output. Producing well-structured Charon syntax is therefore a different condition from satisfying a particular downstream consumer's structural expectations.

Before this pass, [`duplicate_return`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/control_flow/duplicate_return.rs) clones eligible return blocks and duplicates cleanup paths. Its path-local old-to-new ancestor map closes cycles without infinite cloning along that path. This is distinct from the reconstruction option: disabling reconstruction's duplication does not imply no prior cloning happened. Return blocks eligible for cloning contain only StorageDead statements before Return.

For Call, Drop, Assert, Panic and InlineAsm terminators, translation recursively builds the corresponding cleanup block rather than discarding it. The [`unwind-llbc` fixture](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/tests/ui/unwind-llbc.out) shows calls and dynamic assertions with conditional-drop cleanup and unwind termination/resume. It uses no default options; it is evidence of a checked-in expected representation for that configuration, not a fresh run or proof. Normalization modes that first turn assertions into implicit-failure statements require a separate cleanup argument, as discussed in the companion report.

### A finite positional certificate can avoid trusting exit discovery

Basis: **derived** design result; no implemented certificate/checker claimed.

The narrowest clean relation begins at the ULLBC immediately before reconstruction and ends immediately after it, before builtins-to-calls and further cleanup. Source positions are (block ID, statement index), including the terminator position. Structured positions are statement/block IDs plus finite lexical continuation and loop-target information. Flattening the structured syntax to a graph gives explicit fallthrough, branch, break, continue, return and unwind transitions; repeated iteration is represented by graph edges, not by unbounded enumeration.

A proposed witness maps structured positions to source positions, with multiple target positions allowed for a duplicated source block, and explicitly marks inserted control-only positions. A checker can independently:

1. Check start position, ordinary statement/value equality, local/region agreement and all copy maps.
2. Check each observable step and branch label against the same source instruction, and each normal successor against the mapped destination.
3. Check each unwind successor, panic/UB/termination and return effect, including cleanup nesting and call-return control.
4. Resolve break/continue targets lexically, without using the producer's loop or dominator analysis.
5. Permit finite administrative stuttering for wrapper entry, fallthrough Nops and jump removal, while requiring a well-founded rank or acyclicity for purely administrative cycles.

The fifth condition is necessary: a finite graph relation with unconstrained epsilon cycles can admit target divergence without any source progress. Conversely source loops must retain observable progress or matched control cycles; termination-only simulations are insufficient. A bidirectional correspondence or suitable divergence-sensitive refinement must be chosen according to the intended theorem. Calls can be treated as shared semantic instructions at this narrow seam; interprocedural validity then remains a separate premise.

This finite checking idea avoids redoing heuristic exit selection but cannot certify arbitrary normalizations that change operations, regions, allocations or models. It also cannot recover a cleanup path erased before the chosen source artifact. No certificate output was found in `ReconstructCtx`; generated statement IDs/spans are not such a witness.

### A10: MiniRust is a restricted semantic route with different extraction

Basis: **documentation** for the authoritative-semantics convention; **source** for implementation.

[`docs/minirust.md`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/docs/minirust.md) says ambiguous Charon statement semantics should be resolved by its translation to MiniRust. This is an upstream convention defining how to interpret the supported route; it is not a mathematical proof of exporter correctness relative to Rust, nor a total semantics of uninstantiated generic ASTs. MiniRust's independently developed language/interpreter is a separate subject whose internal semantics was not audited here.

[`CliOpts::apply_preset`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/options.rs) applies this overlay for MiniRust serialization or execution:

| Property | Generic Aeneas preset | MiniRust overlay |
| --- | --- | --- |
| Body form | structured unless separately overridden | ULLBC forced |
| Genericity | no full monomorphization forced | full monomorphization forced |
| Requested MIR | default promoted unless user changes it | at least elaborated |
| Drops | precise drops not forced | precise and desugared |
| Constants | ordinary configured handling | bytes |
| Opacity | ordinary selected policy | extract opaque bodies enabled |
| Storage/Box | deallocate locals, treat Box built-in | both enabled |
| Fallible checks/panic/indexing models | reconstruction and calls enabled | no such reset/enable in overlay |

The overlay runs after preset selection; it sets particular fields and does not clear every Aeneas field. Combining the Aeneas preset with MiniRust output can therefore preserve conflicting normalization flags. Source validation rejects monomorphization with ops/index-to-calls, and the exporter separately rejects reconstructed assert/panic constructs. “Switch format to MiniRust” does not automatically establish an equivalent executable version of generic Aeneas LLBC.

The `minirust` Cargo feature is required; multi-target translation is rejected. Full-body export looks for recognized intrinsics or an Unstructured body and otherwise fails. An entry named crate::main with signature `fn main()` is required; the exporter synthesizes a start function. Trait methods must have resolved under monomorphization, while trait objects are represented through vtables. Types/layouts, byte constants and relocations are translated explicitly. Generic proof evidence is not directly executed.

The monomorphization option's help text still says dyn Trait is unsupported, while the exporter and type code contain explicit vtable handling and the manual gives narrower dyn Trait restrictions. These sources do not support a blanket dyn Trait coverage claim. This report records the implemented representation and the stated restrictions without resolving all accepted input combinations.

### Exported operations and test evidence

Basis: **source** in [`minirust.rs`](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/minirust.rs) and [the harness](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/tests/minirust.rs).

`TranslateCtx::function` retains regular/cleanup/terminate block kind and validates function arguments at entry. It suppresses storage markers for return/argument locals because MiniRust keeps them live for the call. Assignments with WithRetag::Yes add a MiniRust Validate instruction. Storage, PlaceMention, assignments and discriminants translate explicitly; Borrowck and Nop emit no runtime instruction. Pointer-expose-provenance operations become intrinsics and may split blocks; they require usize at that boundary.

`terminator` maps calls with both normal and unwind blocks; Move arguments use MiniRust in-place arguments. Assert terminators become branches with a synthesized start-unwind block on regular failure; an already unwinding block uses its terminate path. UndefinedBehavior becomes MiniRust Unreachable; UnwindResume becomes ResumeUnwind; UnwindTerminate becomes Abort. Undesugared drops, inline assembly and reconstructed panic terminators are rejected. Translation rejection and runtime UB are distinct outcomes.

`run` uses `TreeBorrowsMemory<T>`, then distinguishes MachineStop, IllFormed, Abort, Ub, Deadlock and MemoryLeak. These mappings describe code, not outcomes observed here. The selected alias model is consequential; successful execution in that model would not prove all alternative Rust memory models or all executions correct.

The harness reads MiniRust minimize-suite pass/panic/UB cases, applies compile flags and revisions, compares expected status/stdout and an appropriate stderr prefix, imposes a 60-second timeout, skips certain cases/options, and accepts matching known failures as expected failures. It sets cfg=miri, MIR optimization zero, preserve-UB, ub-checks=false and extra const UB checks. A green harness would therefore include admitted failures and exclusions; it would not mean all suite cases pass unconditionally.

### Unsupported and known-unsound cases require restrictions

Basis: **documentation** and **source**; no fresh reproduction.

The pinned manual lists MiniRust limitations for pattern types/char validity, floats, inline assembly and conventions beyond Rust/C. It labels these Charon translations unsound: nonzero-offset pointers to statics, missing track_caller information, and overly preserved union padding. It separately lists dyn Trait upcasting and CoerceUnsized pointers as rejected although MiniRust supports them.

The harness adds concrete qualifications: known failures involving caller_location, union-padding `ub/enum_mark_used_bytes.rs`, static relocation offsets, panic=abort cases, missing marker-trait information for closures, a stack overflow for static.rs, and an atomic Tree Borrows frozen-reference write. It also skips the large-array ptr_byte_order case and unsupported MiniRust-specific option combinations. These are source-maintained known-failure entries; they are not universal diagnoses or proof of current runtime reproducibility.

The [invalid-char fixture](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/tests/ui/minirust/invalid-char.rs) intentionally transmutes 0xD800 to char and documents that the model accepts it as u32; its [expected output](https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/tests/ui/minirust/invalid-char.out) is 55296. This prevents interpreting a successful export/execution as a validity proof for arbitrary char values.

A defensible restricted use must exclude these documented cases or supply repairs and revalidated correspondence, and distinguish a rejected input from an accepted but mismodeled input. “MiniRust is the semantics” does not remove the restrictions.

### A richer language needs an explicit core-elaboration argument

Basis: **derived**.

A small core could represent typed local storage, values/places, primitive effects, branches/loops and explicit unwind/UB outcomes. Intrinsics could be admitted with specified contracts; precise drops could elaborate to glue calls; target dispatch could specialize to one recorded target. This is a coherent shape for a correspondence argument, not evidence that a total verified elaborator exists.

Conditional drops with intentionally unspecified behavior need prior elaboration or a deliberately abstract semantics. Opaque/missing/error bodies cannot acquire concrete execution meaning by syntactic elaboration. Regions, trait evidence, layouts, retagging and unsafe-cell/alias information require a justified preservation or erasure argument. Different generic instantiations can change layouts and effects, so monomorphic MiniRust observations do not by themselves validate generic Aeneas semantics. A shared MIR ancestry is useful engineering structure, not a semantic theorem.

## Boundaries

- **Not examined:** internal MiniRust semantics at its Gitlink, the complete paper/formalized-calculus correspondence, all exporter type/intrinsic arms, whole-program proofs, any native execution or compatibility build.
- **Unknown:** total semantic correspondence of current production LLBC to a formal calculus; exporter preservation for all admitted inputs; full divergence-sensitive reconstruction correctness. Source comments about equivalence are design claims, not mechanized results.
- **Unsupported:** irreducible CFG reconstruction in this implementation; several MiniRust cases above are explicitly rejected.
- **Known not to apply:** the old statement that LLBC universally discards call/drop cleanup edges; the inference that every current LLBC construct is accepted by MiniRust; the inference that formatting generic LLBC as MiniRust leaves extraction semantics unchanged.
- The hypothetical certificate is analysis of a validation seam. No checker was built, run or found in the inspected implementation. Stored goldens provide upstream expected-output evidence only.

## Evidence

Evidence was acquired 2026-10-15 from immutable GitHub files. The companion report's source inventory and this package's [source index](source-index.json) identify exact files and Git blob identities; this report's [coverage map](coverage.json) lists answer scope and remaining theorem boundaries. Principal symbols: `Body`, `GExprBody`, `DropKind`, `AbortKind`, `Region`, `StatementKind`, `TerminatorKind`, `CfgInfo::build`, `ReconstructCtx::{build,translate_jump,translate_block_inner,translate_terminator}`, `remove_useless_jump_blocks`, `duplicate_unwind_path`, `CliOpts::{apply_preset,validate}`, `TranslateCtx::{translate,function,statement,terminator}` and `run`.

The older corpus report `charon-drop-destructor-semantics-0-1-210` was used to locate questions, not as present-version evidence. Current AST and expected-output reads establish the changed cleanup representation. No archived execution log is imported as a result for this pin.

## Revalidation

Diff the AST enums first, especially body variants, implicit failure, storage, drop kind and regions. Then diff `CfgInfo::build`, full/normal successor enumeration, exit ranking, special-jump stack handling and wrapper-depth cleanup. Check both default and ForwardBreak source/golden fixtures, and duplicate-unwind fixtures, by reading their pinned expected syntax. Structural source/golden consistency alone does not prove preservation.

For the MiniRust boundary, diff the option overlay and validation before examining operation lowering. Re-read manual limitations and the harness FAILURES/SKIP lists together: the manual alone misses documented test restrictions. Compare argument validation/retagging, storage suppression, constants/relocations, drop lowering and failure outcomes. Execution results would need the exact input, dependency/runtime identities, configuration and outcome. For semantic proof, a finite CFG/structured certificate checker and operation-level correspondence are distinct obligations; neither is replaced by rerunning sample programs.
