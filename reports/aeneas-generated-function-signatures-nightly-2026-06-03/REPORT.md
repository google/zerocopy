# Aeneas generated Lean function interfaces and specification shape at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the Lean backend generates executable/model function declarations, not a separate semantic specification theorem for each Rust function. The generated declaration's name is registered from the translated item's Rust/LLBC identity, subject to Aeneas rename, trait, implementation, builtin, and loop naming rules. Its value parameters come from the translated pure function body and signature; its return type is the translated forward result combined with any generated backward functions and then wrapped in the function's modeled effects.

This distinction is especially important for mutable references. A Rust parameter `&mut T` is represented in the forward Lean function as a `T`, while mutations that must flow back to the caller are represented by returned backward functions. The checked-in `choose` fixture turns

`fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T`

into a Lean declaration with the shape

`choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`.

The successful result contains both the chosen value and a backward function that later maps the final borrowed value to the updated owners. Other fixtures show that one Rust function can return multiple backward functions when its region structure requires them.

A proof-facing specification is a separate Lean theorem. The reusable predicate is `Aeneas.Std.WP.spec`, exposed through `f args ⦃ outputs => postcondition ⦄` notation. Specification theorems may be registered with `@[step]`, but the ordinary extraction path does not synthesize one theorem per translated Rust function. The postcondition therefore ranges over the generated function's successful payload, including backward functions when those are part of the payload.

No fresh Aeneas, Charon, Lean, or rustc execution was performed. The report is based on exact pinned source plus checked-in generated Lean fixtures at the same Aeneas revision.

## Applicability

The findings apply to Aeneas release `nightly-2026.06.03`, commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`, using its Lean extraction backend. This is the Aeneas release selected by the Anneal revision whose reference corpus prompted this investigation.

"Generated function" means a Lean function declaration emitted from Aeneas's translated pure representation. "Specification theorem" means a Lean theorem whose conclusion uses `Aeneas.Std.WP.spec`, normally through `⦃ ... ⦄` notation. These are different artifacts.

The report describes declaration and proof-interface shape. It does not claim that the generated model is semantically complete for arbitrary Rust, nor that names or signatures remain unchanged in adjacent Aeneas releases.

## Findings

### Aeneas registers an extraction name, then prints the translated declaration under that name

`extract_fun_decl_register_names` registers ordinary translated functions and generated loop/body functions before extraction. Non-builtin declarations go through `ctx_add_fun_decl`; builtins may instead supply an explicit extraction name.

`ctx_add_fun_decl` computes the name with `ctx_compute_fun_name`. The underlying naming logic starts from the function or associated item's LLBC identity, applies configured rename handling, treats trait implementations specially, and appends loop/body suffixes where needed. For Lean, a single generated loop normally receives `_loop`, and a loop body adds `.body`. Default trait-method implementations receive a `default` path element to avoid colliding with the corresponding trait-record field. Aeneas also checks registered names for collisions and supports explicit `#[aeneas::rename(...)]` or `#[charon::rename(...)]` remediation.

`extract_fun_decl_gen` retrieves that registered name, prints it, then prints the declaration parameters and translated output type. The emitted function name is therefore a generated name with defined transformation rules, not an independent stable identifier unrelated to the Rust/LLBC item.

Basis: **source**.

### Trait declarations and callable definitions have different name surfaces

Trait method declarations are not registered as ordinary standalone function names in `extract_fun_decl_register_names`; their translated types become fields of the generated trait structure. The checked-in `Traits.lean` fixture shows:

`structure BoolTrait (Self : Type) where`

with fields such as

`get_bool : Self → Result Bool`.

A default implementation is a separate callable definition, for example `BoolTrait.ret_true.default`. Trait implementation methods likewise use implementation-aware generated names.

A consumer mapping Rust callable identities into Lean must therefore distinguish trait declaration fields, default implementations, and implementation methods rather than assuming one uniform `crate.module.function` naming rule.

Basis: **source** + preserved generated artifact.

### Generated value arguments come from the pure translated function, not the Rust surface signature verbatim

`extract_fun_parameters` first prints the translated generic parameters, then prints each input pattern and its pure type from the generated function body. `Pure.fun_sig.inputs` and the function body's inputs have already passed through Aeneas's translation and micro-passes.

This is why ordinary Rust references do not remain Lean reference parameters. At this pin the forward type translation maps ordinary references to their referent values. The checked-in `choose` function therefore receives `(x : T) (y : T)`, not Lean encodings of `&mut T`.

The translated signature can also carry parameters introduced by Aeneas's model rather than by the Rust surface syntax. `Pure.fun_sig` explicitly accounts for effect-related inputs such as fuel or state in modes that use them. A consumer should inspect the generated declaration or translated signature instead of reconstructing the Lean argument list from the Rust AST alone.

Basis: **source** + preserved generated artifact.

### The output type is assembled from the forward value and backward functions before effects are applied

Aeneas first represents the function as a decomposed signature with:

- `fwd_inputs`, the forward pure inputs;
- `fwd_output`, the pure forward return value;
- `back_sg`, the backward-function information indexed by region group; and
- `fwd_info`, including effect metadata and whether a trivial forward output should be omitted.

`compute_back_tys_with_info` converts each nonfiltered backward signature into an arrow type from its backward inputs to its reconstructed outputs. `compute_output_ty_from_decomposed` then groups the forward output and those backward-function types into one result value. Only after that grouping does `mk_output_ty_from_effect_info` apply the modeled effect wrapper.

Thus the proof-facing output type is not merely "the Rust return type translated to Lean." It can include generated functions needed to return mutable state to the caller, and its outer `Result` or other effect shape comes from Aeneas effect analysis.

Basis: **source**.

### `choose` is a compact witness for mutable-state returns

The Rust fixture defines:

`pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T`.

The checked-in Lean output defines:

`def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))`.

The function returns the chosen `T` together with a backward function. In the true branch that function maps the eventual final borrowed value to `(updated_x, original_y)`; in the false branch it maps it to `(original_x, updated_y)`. The generated caller binds `(z, choose_back)`, computes a new `z`, and invokes `choose_back` to recover the final `x` and `y`.

The backward function is therefore part of the successful return payload. It is not a hidden mutation side channel and is not a separate proof theorem.

Basis: preserved upstream **execution** artifact paired with its Rust fixture; no fresh execution in this report.

### Region structure can produce more than one returned backward function

The decomposed signature stores backward inputs and outputs per region group and abstraction level. Empty backward functions can be filtered, but nonempty groups contribute separate arrow types to the combined output.

The checked-in fixtures demonstrate the consequence. `id_mut_pair3` returns a forward pair plus two independent backward functions, one for each element. `NestedBorrows.lean` includes functions whose callers bind multiple backward functions and invoke them separately. The exact number and types of these returned functions therefore come from translated region structure, not from a rule such as "one backward function per `&mut` token."

Basis: **source** + preserved generated artifacts.

### Failure is an outer effect around the combined successful payload

For functions that Aeneas classifies as fallible, the combined forward/backward payload is wrapped in `Result`. The `choose` fixture has the type `Result (T × (T → (T × T)))`; the `Result` governs whether that whole successful payload is available.

This ordering matters for specifications. A proof theorem about `choose` does not separately prove one proposition about the forward value and another about a mutation channel. It states a postcondition over the successful result payload, which can be destructured into the forward value and backward function.

Basis: **source** + preserved generated artifact.

### Aeneas does not emit one semantic specification theorem per translated Rust function in this extraction path

`extract_fun_decl_gen` emits the translated function declaration itself. The proof library separately defines the generic predicate `Aeneas.Std.WP.spec`. Upstream proof documentation instructs users to write theorems such as:

`@[step] theorem my_func_spec ... : my_func x ⦃ r => ... ⦄ := by ...`

and explains that `@[step]` registers those theorems for proof automation.

The checked-in `BaseTutorial.lean` follows that pattern: it defines model functions, then separately states and proves specification theorems. There is no one-to-one generated specification theorem that should be treated as the semantic contract for every emitted Rust function.

For integration code, this means that "find the generated function" and "find a proved specification theorem for that function" are separate operations.

Basis: **source** + upstream **documentation** + preserved proof example.

### The postcondition shape follows the successful Lean payload

`WP.spec` has type `Result α → (α → Prop) → Prop`. The Hoare-style notation uses `uncurry'` so tuple-valued successful payloads can be presented with multiple binders. If a generated function returns a forward value and one backward function, a specification can bind both. If it returns several backward functions, the postcondition may bind all of them or pattern-match the tuple.

`WP.spec` is false for both modeled failure and modeled divergence, so such a theorem asserts successful return plus its postcondition. That is distinct from merely describing the generated function's type.

Basis: **source** + upstream **documentation**.

### Generated declarations preserve source correspondence comments, but those comments are not the declaration identity

`extract_fun_decl_gen` emits a source-linking comment before the declaration. Checked-in generated files show comments with Rust item paths and source ranges immediately above the corresponding Lean `def`.

These comments are useful for diagnostics and auditability, but call sites and proof theorems refer to the generated Lean name. A robust integration should retain both the Rust/LLBC identity and the generated Lean identity rather than using the comment text as the callable symbol.

Basis: **source** + preserved generated artifact.

## Boundaries

- No fresh Aeneas, Charon, Lean, or rustc execution was performed.
- Checked-in generated `.lean` files are preserved upstream execution artifacts. They demonstrate output produced by the pinned project history but were not regenerated by this report.
- The report does not provide a complete algorithm for predicting every generated Lean name from raw Rust syntax. Name generation can depend on Charon/LLBC identity, rename attributes, trait/impl context, target suffixes, loop position, collision avoidance, and backend configuration.
- The report does not inventory monomorphization, closures, globals, opaque functions, every builtin override, or every effect combination.
- The report establishes the declaration/specification interface shape, not semantic soundness of Aeneas's Rust functionalization.
- It does not establish a one-to-one source map from a Rust span to every generated helper. Returned backward functions may be synthesized values rather than standalone source items.
- It does not imply that every generated function already has a useful proved `@[step]` specification theorem.
- Adjacent Aeneas versions may change naming, signature simplification, effect modeling, proof notation, or emitted fixtures; no continuity is inferred.

## Evidence

**Primary source — Aeneas release selected by Anneal.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, release `nightly-2026.06.03`.

- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: `opt_rename_llbc_name`, `default_fun_suffix`, `ctx_compute_fun_global_name_no_suffix`, `ctx_compute_fun_name`, `ctx_add_fun_decl`, region-group naming comments.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: `extract_fun_decl_register_names`, `extract_fun_parameters`, `extract_fun_decl_gen`.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: `back_sg_info`, `decomposed_fun_type`, `decomposed_fun_sig`, `fun_sig`.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: forward-input translation, backward input/output construction, `compute_back_tys_with_info`, `compute_output_ty_from_decomposed`, `translate_fun_sig_from_decomposed`.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b`: `WP.spec`, `uncurry'`, success/failure/divergence behavior.

**Documentation — same Aeneas revision.**

- `documentation/tactics-reference.md`, blob `d09ac06bc02835e354a9fe7e6829762962439f2a`: `step`, `@[step]`, specification theorem shape.

**Preserved generated/proof artifacts — same Aeneas revision.**

- `tests/src/no_nested_borrows.rs`, blob `707f7d6e1201d1220380dd565a4178806cf3a9ec`: Rust `choose` fixture.
- `tests/lean/NoNestedBorrows.lean`, blob `e2a706b744e2e9a105e305cf8a2b353354209dae`: generated `choose`, `choose_test`, `id_mut_pair*`, and simple scalar functions.
- `tests/lean/NestedBorrows.lean`, blob `61b3b2b31e50555182867a5b73fa510d05106e22`: multiple backward-function payloads and generated loop names.
- `tests/lean/Traits.lean`, blob `d234936b72231024fbccf0030a08023836e5eb6e`: trait structure fields and default implementation naming.
- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`: separately authored `WP.spec` theorems and `@[step]` registration.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For another Aeneas revision, first diff the narrow implementation points that determine the interface:

1. `ExtractBase.ml`: `ctx_compute_fun_global_name_no_suffix`, `default_fun_suffix`, `ctx_compute_fun_name`, and `ctx_add_fun_decl`;
2. `Extract.ml`: `extract_fun_decl_register_names`, `extract_fun_parameters`, and `extract_fun_decl_gen`;
3. `SymbolicToPureTypes.ml`: forward input translation, backward signature construction, and `compute_output_ty_from_decomposed`;
4. `Pure.ml`: `decomposed_fun_type`, `back_sg_info`, and `fun_sig`;
5. `Std/WP.lean` plus the tactics documentation: `spec`, tuple-postcondition notation, and `@[step]` expectations.

Then compare four checked-in fixtures: one ordinary scalar function, `choose`, one case with multiple backward functions, and one trait default/implementation method. Record exact generated names, parameter lists, result types, and source comments.

On an execution-capable surface, regenerate those fixtures with the exact target Aeneas/Charon/Lean revisions and preserve the generated Lean. Add a minimal probe with: a renamed function, a trait default method, one function with a single generated loop, one function with two loops, a single `&mut` update, and a function returning `&mut`. Separately prove one `@[step]` theorem over a generated mutable-borrow function to confirm that its postcondition binds the forward value and returned backward function. That probe revalidates the emitted interface; it does not establish semantic adequacy of the translation.
