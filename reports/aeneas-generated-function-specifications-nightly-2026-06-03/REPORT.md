# Generated function interfaces in Aeneas nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the generated Lean interface for a Rust function is a pure functional interface, not a direct transcription of the Rust signature and not an automatically generated Hoare-logic theorem. Ordinary reference constructors disappear from the forward value types. Mutable-borrow behavior is represented by additional backward computations whose types are derived from Charon region groups. In the Lean output selected by current Anneal, those backward computations are ordinarily merged into the forward function's return value as closures.

The resulting shape is systematic. Aeneas first translates the Rust inputs and return into forward pure types, computes one backward interface per relevant region group, filters degenerate backward interfaces, then forms the final output from the forward result plus the surviving backward values/functions. If the forward computation can fail, the combined output is wrapped in `Result`. If the Rust return is `unit` and a useful backward result remains, the default `simplify_merged_fwd_backs` pass can omit the unit component. A backward computation with no inputs can likewise be evaluated inside the forward function and returned as its value rather than as a closure.

Checked-in generated Lean makes the mutable-state contract concrete. Rust `choose(b, x: &mut T, y: &mut T) -> &mut T` becomes a function with shape `Bool → T → T → Result (T × (T → (T × T)))`: the first `T` is the forward value, and the returned function consumes the value eventually written through the returned borrow and reconstructs the updated owners. `index_mut_array` similarly returns `Result (T × (T → Array T ...))`; `array_to_mut_slice_` returns a slice together with a closure that turns the eventual slice value back into the updated array. Nested-borrow fixtures can return multiple backward closures.

Generated declaration names follow Aeneas's normal Lean naming pipeline; the companion naming report owns the complete path/namespace rules. The important function-interface-specific detail is that current Lean output does not generally materialize each backward computation as a top-level `<name>_back` declaration. It returns local closures. At call sites Aeneas derives local names from the callee basename plus `_back`, uniquifying as necessary, which yields forms such as `inner_mut_back` and `inner_mut_back1` in checked-in output.

“Postcondition shape” therefore has two distinct meanings that must not be conflated. The generated function's computational return type carries the forward result and mutation-restoration functions. User-facing logical postconditions are separate Lean propositions/theorems over that generated function. The current Aeneas proof tooling can reason about the returned backward functions, but the examined extraction path does not manufacture a per-function semantic postcondition theorem from Rust source.

Basis: exact pinned Aeneas source plus same-revision checked-in Rust/generated-Lean pairs. No fresh Aeneas, Charon, or Lean execution was performed.

## Applicability

This report applies to the ordinary Aeneas Lean backend at release `nightly-2026.06.03`, revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`, consuming LLBC produced by its pinned Charon revision `a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`). This is the Aeneas release selected by current Anneal.

The report is intentionally narrower than the corpus's general Rust-to-Lean translation, resource-semantics, naming, and WP/proof-tool reports. It records the generated function interface as an integration contract: declaration name boundary, parameter shape, forward output, backward/mutation-return shape, `Result` wrapping, and the distinction between a generated computational interface and a logical specification theorem.

The checked-in `.lean` files are preserved same-revision generated artifacts. They are stronger evidence than an illustrative pseudocode example, but they are not fresh execution in this run. Where source describes a representational possibility not exercised by the cited Lean specimens, this report labels that distinction.

## Findings

### The generated function signature is assembled in two stages

`SymbolicToPureTypes.translate_inst_fun_sig_to_decomposed_fun_type` first constructs a `decomposed_fun_type`. Its forward inputs are the Rust/LLBC input types translated through `translate_fwd_ty`; its forward output is the translated Rust/LLBC return type before `Result` wrapping and before backward functions are added. The same pass computes backward inputs and outputs from the function's region hierarchy.

`translate_fun_sig_from_decomposed` then computes the final function signature. `compute_output_ty_from_decomposed` gathers the surviving backward types, combines them with the forward output unless `ignore_output` applies, simplifies singleton/product structure, and finally applies the forward effect. At this revision the ordinary effect used here is failure: when `can_fail` is true, `mk_output_ty_from_effect_info` wraps the combined output in `Result`.

This gives a useful invariant for Anneal: the emitted Lean return type is not merely `translate(RustReturn)`. It can also encode future mutation restoration and translation effects.

Basis: **source** in `src/symbolic/SymbolicToPureTypes.ml` and `src/pure/Pure.ml`.

### Ordinary Rust references disappear from forward value types

For `TRef`, `translate_fwd_ty` recursively translates the referent and does not retain a reference constructor. Thus both shared and mutable references contribute the pure referent type to the forward signature. Region/lifetime information is used earlier to determine backward structure, but ordinary reference identity is not part of the final forward value type.

The checked-in examples expose this directly. Rust `fn array_to_mut_slice_<T>(s: &mut [T; 32]) -> &mut [T]` becomes Lean `array_to_mut_slice_ {T} (s : Array T 32#usize) : Result ((Slice T) × (Slice T → Array T 32#usize))`. The input is an `Array`, not a Lean reference. The returned mutable slice is a `Slice`, accompanied by a function that later reconstructs the updated array.

Basis: **source** + **checked-in generated fixture**.

### Mutable-borrow effects become backward inputs and outputs derived from region groups

Aeneas computes a region hierarchy for the LLBC signature, then derives one `back_sg_info` per relevant region group. Each backward interface records inputs and outputs, grouped by abstraction level. The source describes backward outputs as the values “given back” to the caller and notes that there is at most one output type per original forward input argument at a level.

The type traversal is directional. `translate_back_input_ty` computes values that must be supplied when ending the borrow; `translate_back_output_ty` computes values restored to earlier owners. Shared references do not create the same mutable update path. Nested mutable borrows can introduce more than one abstraction level and more than one returned backward computation.

The canonical source comment uses `choose<'a, T>(b, x: &'a mut T, y: &'a mut T) -> &'a mut T`: the forward output is one `T`; the backward output is two `T`s, corresponding to `x` and `y`.

Basis: **source** in `src/symbolic/SymbolicToPureTypes.ml` and `src/pure/Pure.ml`.

### The Lean backend normally exposes backward behavior as returned closures

The final merged output includes the forward value and the arrow types returned by `compute_back_tys`. `SymbolicToPureExpressions.translate_forward_end` constructs those backward expressions, binds them, and returns them together with the forward value. Calls to translated functions similarly destructure the forward destination and returned backward functions in one result pattern.

The checked-in Lean output is direct evidence of this merged interface:

- `choose {T} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`;
- `array_to_mut_slice_ {T} (s : Array T 32#usize) : Result ((Slice T) × (Slice T → Array T 32#usize))`;
- `index_mut_array {T} (s : Array T 32#usize) (i : Std.Usize) : Result (T × (T → Array T 32#usize))`;
- `index_mut_slice {T} (s : Slice T) (i : Std.Usize) : Result (T × (T → Slice T))`;
- `inner_mut (x : Std.U32) : Result (Std.U32 × (Std.U32 → Std.U32) × (Std.U32 → Std.U32))` for a nested mutable-reference source function.

A consumer should therefore treat “the backward function” as part of the returned value unless current exact-pin evidence establishes a different extraction mode. It should not assume a separately addressable top-level `_back` declaration exists.

Basis: **source** + **checked-in generated fixtures**.

### The backward closure is the mutable-state return channel

In this functional model, the value returned by a backward closure is how mutation flows back to the original owner. For `choose`, the forward result identifies the selected borrowed `T`. The closure accepts the final selected value and returns a pair representing the final values of both original mutable inputs. The implementation chooses which component changes according to the branch taken.

For `index_mut_array`, the forward value is the indexed element and the backward closure has type `T → Array T ...`; applying it to the final element value reconstructs the updated array. For a mutable subslice or mutable nested borrow, the same idea scales to larger returned owner values and multiple closures.

This is not a heap delta, pointer identity, or mutation log. It is a pure value transformation justified by Aeneas's symbolic borrow analysis. The companion resource-semantics report owns the stronger negative boundary: the final pure interface does not retain a general heap/resource model.

Basis: **checked-in Rust/generated-Lean pairs** + **source**; resource-model distinction cross-checked against the published companion report.

### Unit-returning mutators can collapse to the updated owner value

`Config.simplify_merged_fwd_backs` is true at this revision. The source documents two relevant simplifications when forward and backward computations are merged:

- if the forward output is `unit` and a nontrivial backward result remains, the unit can be omitted;
- if a backward computation has no inputs, Aeneas can evaluate it inside the forward function instead of returning a function value.

The source's own example is Rust `fn incr(x: &mut u32) { *x += 1 }`. Before simplification it can conceptually have a result containing `unit` plus the backward result; after simplification the generated shape is simply `result u32`. This is why “mutable-state return” must be understood semantically, not by looking only for arrow types in the result. A mutation can appear as a directly returned updated owner when no future backward input is required.

Basis: **source** in `src/Config.ml` and `src/symbolic/SymbolicToPureTypes.ml`.

### Failure wraps the combined interface, not only the forward Rust result

`compute_output_ty_from_decomposed` first combines the forward output and all surviving backward values/functions, then `mk_output_ty_from_effect_info` wraps that combined type in `Result` when the forward computation can fail. The checked-in Lean fixtures therefore commonly have the form `Result (forward × back...)`, not `(Result forward) × back...`.

Backward computations have their own effect metadata. At this pin, the raw effect calculation forces ordinary backward functions not to fail, and the signature code additionally avoids a `Result` wrapper for an input-free backward computation that is evaluated immediately. The emitted type should be read from the exact generated signature rather than reconstructed from a generic “all Aeneas functions return Result” rule.

Basis: **source**.

### Function parameters include translated Rust arguments plus generated generic/effect machinery where applicable

`Pure.fun_sig.inputs` contains the final input types and `explicit_info` records which parameters are explicit or implicit at extraction. `translate_fun_sig_from_decomposed` computes that explicitness from the translated generics and inputs. The generated Lean fixtures consequently use forms such as `{T : Type}` for inferable type parameters and ordinary parentheses for value arguments.

The pure IR comments also allow fuel/state-like generated parameters in configurations that introduce them during later micro-passes. Those comments are broader than the ordinary checked-in Lean examples used here. Anneal should therefore regard the exact emitted signature as authority for generated parameters rather than hard-code “Rust parameters only.”

The critical stable point is narrower: `bs_ctx.forward_inputs` explicitly denotes the input parameters corresponding to translated Rust inputs before generated fuel/state additions, while backward inputs are tracked separately and become returned closures' parameters rather than extra forward-call parameters in the merged Lean shape.

Basis: **source**.

### Top-level function naming is separate from backward local naming

The complete Rust-to-Lean declaration naming rules are already established by `aeneas-rust-lean-naming-nightly-2026-06-03`. For this interface, two narrower naming facts matter.

First, `Pure.fun_decl.name` is only debugging metadata; extraction computes the actual declaration name from the LLBC item name through the extraction naming context. Ordinary local functions therefore keep their normalized Rust item path, subject to namespace, rename, trait/impl, collision, and helper rules documented by the naming report.

Second, returned backward computations are local values in the merged interface. When translating a call, Aeneas derives a base local name from the callee's last source-name component and appends `_back`; local uniquification can add numeric suffixes. The checked-in nested-borrow call therefore binds `inner_mut_back` and `inner_mut_back1`. Inside a generated function, backward variables use `back` plus region-name hints when available, again subject to local uniquification.

These local names are readability aids, not semantic identifiers. Consumers should key semantic relationships by the generated term/type structure and source correspondence, not by assuming `_back` names are stable API handles.

Basis: **source** + **checked-in generated fixture** + published naming report.

### “Postcondition shape” is not an automatically generated logical contract

The generated function return interface describes what values are produced by the translated computation, including backward mutation-restoration functions. It does not by itself state a logical theorem relating those values to the source program's intended behavior.

The same-revision Lean tutorial explicitly introduces user-written specification theorems in Hoare-logic style, with preconditions and postconditions over generated functions. The companion WP/proof-tools report establishes that the examined extraction path does not generate a per-translated-function WP theorem. A specification for `choose`, for example, can destructure the forward result and backward closure and assert how the closure reconstructs the owners, but that proposition is a separate theorem checked by Lean.

For Anneal, this distinction prevents a category error: the Aeneas-generated type is the proof-facing computational API. A correctness postcondition must still be supplied or derived and proved at the logical layer.

Basis: **same-revision tutorial** + **published companion WP report** + **derived integration distinction**.

### Loops and helper declarations can change the declaration family without changing the interface principles

Aeneas can extract loop helpers such as `<function>_loop`, and Lean loop bodies can use `.body`; the naming report owns those exact rules. Checked-in tutorial output shows `list_nth_mut1_loop` with the same style of mutable-borrow result as its wrapper: `Result (T × (T → CList T))`.

Thus a Rust function may correspond to more than one generated Lean declaration after loop decomposition. Each generated declaration still has an explicit pure signature whose forward/backward output structure should be inspected independently. A consumer should not assume the wrapper alone contains every proof-relevant interface used by generated recursion/loop code.

Basis: **checked-in generated fixture** + published naming report.

## Boundaries

No fresh Charon, Aeneas, or Lean execution was performed. The checked-in generated Lean files are preserved execution artifacts committed at the exact Aeneas revision.

This report does not claim that generated function types are semantic specifications. They are computational interfaces. Logical WP/postcondition theorems and proof automation are separate and covered by the companion WP/proof-tools report.

This report does not duplicate all Rust-to-Lean type translation rules. The companion Rust-to-Lean report covers scalar, ADT, reference, raw-pointer, trait, and other translation details. Here those rules are used only to explain function-interface construction.

This report does not redefine Aeneas's naming ABI. The companion naming report covers namespace/path/trait/impl/rename/collision behavior. Local `_back` variable names are reported only because they are directly relevant to reading merged function interfaces.

The exact ordering and decomposition of backward inputs/outputs follows region groups and abstraction levels computed from the pinned LLBC signature. A different Charon/Aeneas pair may produce a different grouping even if the Rust source text is unchanged.

Nested mutable borrows remain structurally constrained. The cited fixture demonstrates cases Aeneas supports; it is not evidence that every nested mutable-borrow shape is accepted.

The pure IR contains comments about stateful signatures and generated state parameters, while the ordinary pinned function-effect structure inspected here chiefly exposes failure/divergence/recursion and the checked-in Lean examples do not exercise a general mutable heap state parameter. This report does not promote those broader comments into a claim that ordinary Anneal-selected translations carry an explicit heap state. “Mutable-state return” here means the functional return of updated borrowed-owner values.

The report does not establish byte-for-byte stability of generated signatures across releases. Aeneas's representation and simplification policy are implementation-level behavior and must be revalidated on upgrade.

## Evidence

Primary Aeneas subject: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`).

- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: `fun_sig_info`, `back_sg_info`, `decomposed_fun_type`, `fun_sig`, final input/output metadata, and comments describing forward/backward signature layers.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: reference erasure, region-group backward input/output construction, simplification/filtering, `compute_back_tys`, combined output construction, effect wrapping, explicit parameter computation.
- `src/symbolic/SymbolicToPureCore.ml`, blob `2f2b34275b8d7313733b146218bc6ed26716a7be`: forward versus backward input tracking, backward outputs, named-output hints, and body-synthesis context.
- `src/symbolic/SymbolicToPureExpressions.ml`, blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`: returned backward functions, caller destructuring, `_back` local-name derivation, region-based local back names, and merged forward-end construction.
- `src/symbolic/SymbolicToPure.ml`, blob `95ba91f539e48009efa420dfa956c4c55581cb3a`: final pure function declaration/signature assembly and body translation.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: extraction-time function name construction and loop/helper suffixes.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: extraction of function parameters and final output type.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: `simplify_merged_fwd_backs = true` and its source-level examples.
- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: Aeneas's Rust-to-pure-functional translation role and Lean backend context.

Checked-in source/generated pairs from the same Aeneas revision:

- `tests/src/no_nested_borrows.rs`, blob `707f7d6e1201d1220380dd565a4178806cf3a9ec`, and `tests/lean/NoNestedBorrows.lean`, blob `e2a706b744e2e9a105e305cf8a2b353354209dae`: `choose` maps two `&mut T` inputs and one `&mut T` output to a forward `T` plus a `T → (T × T)` backward closure.
- `tests/src/arrays.rs`, blob `478af7171452826436f56f12c88493debac8e0d0`, and `tests/lean/Arrays.lean`, blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`: mutable array/slice borrow interfaces and owner reconstruction closures.
- `tests/src/nested-borrows.rs`, blob `61d62cf0e0723a4019e024882e35fb8b212a67eb`, and `tests/lean/NestedBorrows.lean`, blob `61b3b2b31e50555182867a5b73fa510d05106e22`: multiple returned backward closures and local `_back` call-site names.
- `tests/lean/Tutorial/Tutorial.lean`, blob `4513b4db1863ea7f3f55fb597ed3b94eb9c770a3`: checked-in generated `choose`, mutable-list interfaces, and loop-helper signatures.
- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`: user-written Hoare-style specification theorems over generated functions.

Paired Charon subject: `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`). Its structured signature and region information are consumed by Aeneas; this report does not duplicate Charon's own signature/region representation reports.

Related current reference reports used only to preserve scope boundaries:

- `aeneas-rust-to-lean-translation-nightly-2026-06-03` — general type/reference/backward translation;
- `aeneas-resource-semantics-nightly-2026-06-03` — resource/lifetime-erasure boundary;
- `aeneas-rust-lean-naming-nightly-2026-06-03` — complete generated-name rules;
- `aeneas-wp-proof-tools-nightly-2026-06-03` — logical specifications, `step`, and postcondition proof interface.

No evidence acquired for this report is fresh **execution**.

## Revalidation

For another Aeneas revision, revalidate the generated interface in this order:

1. Resolve the exact Aeneas revision and its paired Charon revision/toolchain.
2. Diff `Pure.ml` around `back_sg_info`, `decomposed_fun_type`, and `fun_sig`. A changed data model means the interface contract must be reconstructed rather than patched by example.
3. Diff `SymbolicToPureTypes.ml` around `translate_fwd_ty`, backward input/output translation, `compute_back_tys_with_info`, `compute_output_ty_from_decomposed`, and `translate_fun_sig_from_decomposed`.
4. Diff `Config.simplify_merged_fwd_backs` and its users. A default or simplification change can alter unit removal and whether a no-input backward computation appears as a closure or an immediate returned value.
5. Diff `SymbolicToPureExpressions.ml` around call destructuring and `translate_forward_end` to establish whether Lean still receives merged backward closures and how local names are produced.
6. Diff the extraction naming and function-printing path, or rely on the separately revalidated naming report for top-level declarations.

On an execution-capable surface, regenerate a small exact-pin matrix and preserve Rust, LLBC, generated Lean, command line, and hashes:

- a pure function with no borrows;
- a shared-borrow function;
- `choose(b, &mut T, &mut T) -> &mut T`;
- a `&mut` input with unit Rust return that mutates the referent;
- mutable array element and mutable subslice access;
- one nested mutable-borrow case that yields multiple backward closures;
- one fallible operation around a mutable borrow; and
- one loop carrying a mutable borrow.

For each generated declaration, record the full Lean name, explicit/implicit parameters, final return type, returned closure count, closure input/output types, and whether unit/backward simplification occurred. A mismatch in any of those fields is sufficient to revisit this report before Anneal relies on the old interface shape.
