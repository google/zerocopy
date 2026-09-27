# Charon constants, statics, and associated constants at 0.1.210

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (0.1.210), named Rust constants and statics are not serialized as already-computed scalar values alone. Charon represents each as a `GlobalDecl` plus a separate initializer `FunDecl`. The global records its type, generic parameters, source context, global category, and initializer function ID. The initializer contains the translated computation when Charon can obtain and translate it. The same rustc definition can therefore have two Charon identities: one `Global` item for the constant/static and one `Fun` item for its initializer.

`GlobalKind` distinguishes ordinary statics, thread-local statics, named constants, and anonymous constants. It does **not** distinguish `static` from `static mut`: both map to `GlobalKind::Static`, and `GlobalDecl` has no separate mutability field at this revision. The checked-in static fixture nevertheless preserves important use-site distinctions from MIR: shared-static references are emitted through shared global references, while `static mut` accesses use raw mutable pointers before reads or reference formation. A consumer must therefore not infer Rust static mutability solely from `GlobalDecl.global_kind`.

Associated constants use the same global machinery and are integrated into Charon's trait representation. Trait declarations record an associated-constant slot with its type and optional default `GlobalDeclRef`; trait impls record the selected `GlobalDeclRef`. The pinned fixtures preserve generic associated constants, overrides, defaults, and defaults whose initializer depends on the implicit `Self: Trait` proof.

Charon's constant-expression representation is separate from named-global initialization. It directly represents literals, ADTs, arrays, tuples, global/trait-constant references, borrows, raw borrows, const-generic variables, function definitions/pointers, and raw memory. Some constant-expression forms remain unsupported: the pinned translator records an error and substitutes an opaque constant expression for unsupported casts or other `Todo` cases.

The resulting LLBC is not uniformly “fully CTFE-normalized.” The checked-in named-constant fixture retains computations such as `incr(32)` in initializer functions instead of replacing every named constant with its final scalar value. Conversely, a nested inline-const fixture reaches final LLBC with the nested const computation folded to `9` and no separate global declaration. Charon therefore consumes a rustc-derived representation in which some const computations remain explicit while others have already been evaluated or simplified. The companion Rust CTFE report defines the language/compiler execution-mode boundary; this report records what the pinned Charon representation actually retains.

No fresh Cargo, rustc, Charon, or CTFE execution was performed. The conclusions are from exact pinned Charon source and checked-in upstream golden outputs.

## Applicability

This report applies to:

- Charon repository `AeneasVerif/charon`;
- revision `a535e914f74db4fd9e6be7048f4233270d8945c0`;
- Charon version `0.1.210`;
- embedded Rust toolchain `nightly-2026-05-31`.

It covers the #3720 subject **Charon constants/statics/associated constants**. It includes:

- top-level and local named `const` items;
- ordinary `static` and `static mut` items;
- Charon's `ThreadLocal` category as represented by source, though no fresh thread-local probe was run;
- inherent and trait associated constants;
- default and overridden trait associated constants;
- constant expressions only to the extent needed to understand the global/initializer boundary.

It does not re-specify Rust's normative const-evaluation rules. The existing `rust-const-eval-const-functions-nightly-2026-05-31` report covers required CTFE, const-function execution modes, and rustc's CTFE interpreter. It also does not characterize raw-pointer soundness, concurrent access to mutable statics, or the downstream Aeneas/Lean treatment of these Charon forms.

## Findings

### Every translated global has a separate initializer function

Charon's translation queue explicitly allows one rustc definition to appear under more than one translation kind. The source comment uses constants as the example: a constant has both a `Global` translation and a `FunDecl` translation for its initializer.

`translate_global` translates the global's type and category, then registers the same rustc item with `TransItemSourceKind::Fun`. The resulting `GlobalDecl.init` points to that function ID. `FunDecl` separately records `is_global_initializer: Option<GlobalDeclId>`.

The representation therefore separates **global identity** from **initializer computation**.

Basis: pinned Charon **source**.

### The global categories are static, thread-local, named const, and anonymous const

`GlobalKind` has four variants:

- `Static`;
- `ThreadLocal`;
- `NamedConst`;
- `AnonConst`.

`translate_global` maps a thread-local static to `ThreadLocal`, every other static to `Static`, top-level and associated named constants to `NamedConst`, and other const definitions to `AnonConst`.

The `AnonConst` documentation names inline const expressions, const expressions in types, and promoted constants as examples. This category says what kind of compiler global Charon is representing; it does not imply that every source-level inline const survives as a standalone final LLBC declaration.

Basis: pinned Charon **source**.

### Named constants retain computation through initializer functions

The checked-in `constants.rs` fixture contains constants initialized by:

- literals;
- another named constant;
- a block expression;
- calls to `const fn`;
- tuple and struct construction.

Its golden LLBC consistently emits an initializer function and a global const declaration. For example, `X3: u32 = incr(32)` is preserved as an `X3()` initializer that calls `incr(32)`, followed by the global declaration `const X3: u32 = X3()`.

Likewise, `Q3 = add(Q2, 3)` remains an initializer body that calls `add` and reads `Q2`. Charon does not replace all named constants with their final CTFE result in this output.

Basis: preserved upstream **execution** artifacts.

### `const fn` remains an ordinary translated function

The same fixture contains `const fn incr`, `mk_pair0`, `mk_pair1`, and other const functions. In final LLBC they appear as ordinary function declarations with ordinary translated bodies. Their use by constant initializers is represented as calls from the initializer functions.

Nothing in the Charon `FunDecl` shown by this report marks such a function as “compile-time only.” This matches Rust's language rule that `const fn` is eligible for const contexts but can also execute at runtime.

Basis: preserved upstream **execution** artifact + companion Rust CTFE **normative/source** report.

### Local named constants retain their own global identity

A constant declared inside `get_z1` is not necessarily flattened into its enclosing function. The golden output contains both:

- `get_z1::Z1()` as an initializer function; and
- `const get_z1::Z1: i32 = ...` as a global declaration.

`get_z1` then reads that global.

Thus source nesting does not imply that a named local constant disappears as an independent Charon global.

Basis: preserved upstream **execution** artifact.

### Statics use the same initializer split but retain storage identity at use sites

The fixture's ordinary statics `S1` through `S4` are represented by initializer functions plus `static` declarations, just as named constants use initializer functions plus `const` declarations.

The separate `statics.rs` fixture shows a crucial operational difference at use sites. For a shared static, LLBC forms references to the global itself, for example through `&SHARED_STATIC`, before dereferencing or converting to a raw pointer. A non-`Copy` shared static is likewise borrowed by reference rather than copied into a temporary value.

This is consistent with a static denoting storage rather than a replaceable value expression.

Basis: preserved upstream **execution** artifact.

### `static mut` and shared `static` collapse to the same `GlobalKind`

`translate_global` maps every non-thread-local `Static` definition to `GlobalKind::Static`. `GlobalDecl` contains no separate field for Rust static mutability.

The pretty-printed golden output likewise prints the mutable source item as `static MUT_STATIC`, not `static mut MUT_STATIC`.

This means a consumer cannot classify a declaration as shared versus mutable solely from `GlobalDecl.global_kind`. The report does not claim that all consequences of static mutability are erased; use-site MIR can still carry operations that depend on it.

Basis: pinned Charon **source** + preserved upstream **execution** artifact.

### `static mut` use sites retain raw-mutable access structure

In the `statics.rs` fixture, each access to `MUT_STATIC` first obtains `&raw mut MUT_STATIC`. Charon then represents reads, shared-reference formation, mutable-reference formation, raw-const conversion, or raw-mut use through that pointer.

The corresponding shared-static fixture starts from shared references to the global instead.

Thus the declaration taxonomy collapses shared versus mutable statics, while the translated operations in this fixture still distinguish how rustc permits the storage to be reached. This is an important scope boundary: a declaration-only consumer sees less information than a consumer that also analyzes all uses.

Basis: preserved upstream **execution** artifact.

### References to ordinary consts behave differently from references to static storage

The `constant()` fixture forms both `&CONST` and `&mut CONST`. In final LLBC, Charon first copies the const value into temporaries and then forms references to those temporaries. The references are not represented as references to persistent global storage.

By contrast, references to a static are based on the static global itself.

This captures the Rust distinction between a const's value semantics and a static's storage identity at the pinned compiler/Charon boundary.

Basis: preserved upstream **execution** artifact.

### Foreign constants can retain identity while losing initializer semantics

The checked-in foreign-constant fixture refers to a constant from an auxiliary crate. Final LLBC contains:

- a global const declaration for the foreign constant; and
- a same-name initializer function whose body is `<opaque>`.

The local caller reads the global. This matches Charon's default foreign-item opacity: the declaration boundary can remain available even when the foreign implementation body is not translated.

A foreign constant's presence in LLBC therefore does not establish that Charon captured the computation that justifies its value.

Basis: preserved upstream **execution** artifact + companion Charon opacity/dependency **source** reports.

### Inherent associated constants are globals parameterized by impl generics

The fixture `V<const N: usize, T>` defines `V::LEN = N`. Charon emits an initializer function and a named global constant that carry the enclosing generic parameters and relevant trait clauses.

A generic function that reads `V::<N, T>::LEN` references that parameterized global.

Associated constants are therefore not flattened to an unqualified scalar table; they preserve their generic environment as Charon global references.

Basis: preserved upstream **execution** artifact.

### Trait declarations give associated constants typed slots with optional defaults

`TraitAssocConst` records the associated-constant name, attributes, type, and `default: Option<GlobalDeclRef>`.

When translating a trait declaration, Charon builds the associated-constant entry and, when a default exists, registers the default as a global reference under the trait's binder. The default can depend on the trait's implicit `Self` proof.

The representation separates the abstract trait slot from the global that computes a default value.

Basis: pinned Charon **source**.

### Trait impls select concrete or default associated-constant globals

`TraitImpl.consts` maps each `AssocConstId` to a `GlobalDeclRef`.

The checked-in generic associated-constant fixture demonstrates both cases:

- an impl-provided associated constant maps to the impl's own global; and
- an impl that omits the item maps to the trait default global instantiated with the impl's generics and the required `Self: Trait` proof.

This is not textual copying of the default initializer into every impl. The impl records a reference to the selected global.

Basis: pinned Charon **source** + preserved upstream **execution** artifact.

### Associated constants can depend on trait proofs

The fixture includes `Wrapper<T>` with `T: HasLen` and defines `LEN = T::LEN`. Its initializer body contains a trait-proof-qualified associated-constant reference.

It also defines a default associated constant `ALSO_LEN = Self::LEN + 1` under a supertrait. Charon's emitted default carries the `Self: AlsoHasLen` proof, from which the supertrait proof is selected to reach `LEN`.

For downstream verification, the value of an associated constant can therefore depend on trait resolution evidence carried in Charon's generic/trait-reference structure.

Basis: preserved upstream **execution** artifact.

### Overridden associated constants get distinct initializer/global items

The fixture includes an impl that overrides a default associated constant with its own definition. Charon emits a distinct initializer function and distinct global for the override, then points that trait impl's constant slot at the override.

The override body can itself contain control flow and recursive associated-constant references. The representation does not reduce “associated constant” to a literal-only feature.

Basis: preserved upstream **execution** artifact.

### Charon directly represents many constant-expression forms

`translate_constant_expr` supports direct Charon forms for:

- byte strings, strings, characters, booleans, integers, floating-point values, and provenance-free integer pointers;
- ADTs, arrays, and tuples;
- named globals and trait-associated constants;
- shared/mutable borrows and raw borrows;
- const-generic variables;
- function definitions and function pointers;
- raw memory.

Borrowed arrays/strings can carry unsizing length metadata. This expression-level representation is used where rustc/Hax gives Charon a constant expression rather than a named global initializer body.

Basis: pinned Charon **source**.

### Some constant-expression forms deliberately become error-marked opaque values

The same translator explicitly handles constant-expression casts by registering an unsupported-constant error and returning `ConstantExprKind::Opaque`. Hax `Todo` constant forms take the same error-plus-opaque path. A failed const-generic variable lookup also yields an opaque expression containing the error message.

An opaque constant expression is therefore not positive evidence that Charon understood or evaluated the missing semantics. Anneal must treat the associated error/partial-output state fail-closed rather than reasoning through the opaque placeholder as though it were an established value.

Basis: pinned Charon **source** + Anneal's fail-closed **derived** requirement.

### Inline const source boundaries need not survive into final LLBC

The source fixture:

`1 + const { 2 + const { 3 + 4 } }`

has final LLBC containing a constant `9` for the nested inline computation and no standalone Charon global for either source `const { ... }` block.

This does not contradict the existence of `GlobalKind::AnonConst`. It shows that compiler/Charon processing can evaluate or simplify an anonymous const before the final serialized item set retains it as a declaration.

A source-level verification domain that cares about every inline-const boundary therefore needs explicit source/model correspondence; final LLBC declaration enumeration alone is insufficient.

Basis: preserved upstream **execution** artifact + **derived** correspondence implication.

### Final LLBC is not a uniform record of either source expressions or final CTFE values

The named-constant fixture retains initializer computations such as calls and arithmetic, while the nested inline-const fixture shows an already-folded value. These two preserved outputs are enough to reject both oversimplifications:

- “Charon always keeps the original const expression”; and
- “Charon always serializes the fully evaluated CTFE result.”

The exact retained form depends on the compiler representation and Charon transformations for that construct.

Basis: preserved upstream **execution** artifacts.

## Boundaries

- No fresh Cargo, rustc, Charon, CTFE, LLBC, Aeneas, or Lean execution was performed.
- Checked-in `.out` files are preserved upstream execution/test evidence; this report did not regenerate them.
- The report does not prove that Charon's global/initializer representation is semantically equivalent to Rust CTFE or runtime static behavior.
- It does not inventory every constant-expression kind supported by rustc; it records the cases visible in the pinned Charon translator and the important explicit unsupported paths.
- It does not characterize all anonymous constants, promoted constants, const generic solver behavior, or array-length evaluation.
- It does not characterize thread-local runtime semantics. `GlobalKind::ThreadLocal` is source-defined representation evidence only.
- It does not claim that loss of a declaration-level `static mut` flag makes every relevant mutability distinction unavailable. The checked-in use-site fixture preserves raw-mutable access structure.
- Conversely, it does not establish that use-site structure is sufficient to reconstruct source static mutability in every program, especially for unused/exported globals or across downstream transformations.
- It does not establish concurrency, atomicity, synchronization, provenance, or aliasing semantics for statics or raw pointers.
- It does not establish memory-layout or initialization-byte semantics of statics.
- It does not claim that every named constant remains unevaluated. The evidence only shows that some named initializer computations survive.
- It does not claim that every inline const is folded away. The evidence only shows that the pinned nested-inline-const fixture is.
- Foreign-global initializer availability depends on compiler metadata and Charon opacity; the foreign fixture establishes one preserved case.
- Downstream Aeneas handling of globals, statics, associated constants, and opaque constant expressions is a separate research subject.

## Evidence

**Primary Charon subject:** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`.

Source:

- `charon/src/ast/gast.rs`, blob `23044319a8f763d241912c5d693ed94cf597682f`: `FunDecl.is_global_initializer`, `GlobalKind`, `GlobalDecl`, `TraitAssocConst`, and `TraitImpl.consts`.
- `charon/src/bin/charon-driver/translate/translate_crate.rs`, blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`: dual Global/Fun identity for constants, global registration, and translation kinds.
- `charon/src/bin/charon-driver/translate/translate_items.rs`, blob `7964644be017856c6d165545a67bd6ef06e0c85c`: `translate_global`; global-category classification; initializer registration; trait associated-constant default/impl wiring.
- `charon/src/bin/charon-driver/translate/translate_constants.rs`, blob `e0b037b340b3ef1b5316f7af472cd7632ba5e89b`: constant-expression forms, named-global and trait-constant references, borrow handling, function-pointer constants, and unsupported/opaque paths.

Preserved upstream execution fixtures:

- `charon/tests/ui/constants.rs`, blob `83904eed3f73ab16e17b5e774ac582897c856ba5`, and `constants.out`, blob `ec8e151a643fa7a68a4b7413e0404d6235ef7a22`: named/local constants, const functions, statics, generic inherent associated constants, initializer/global split.
- `charon/tests/ui/statics.rs`, blob `bdc1142fbe86dd58a7a8720738e69c560530629a`, and `statics.out`, blob `d5ba9f4f77cc45fd54fd8fa08edd48217b562ab5`: const references, shared static storage, `static mut` access structure, raw references, and non-`Copy` static borrowing.
- `charon/tests/ui/assoc-const-with-generics.rs`, blob `13aebc63cb104e7951d3bdbb1205536ab1fd666b`, and `.out`, blob `30d515f82a9965131a61dfcbc5dd99375349e732`: associated-constant generics, defaults, overrides, trait-proof references, and impl selection.
- `charon/tests/ui/foreign-constant.rs`, blob `a1fb5cabcb25a91768e92da42507fefde6d47dda`, and `.out`, blob `c1922db9b1316978cc31c64cd1a69d7514e11d5f`: represented foreign global with opaque initializer.
- `charon/tests/ui/simple/nested-inline-const.rs`, blob `7c97dd0c6a053e350985477956172644a8fde238`, and `.out`, blob `692ac7be926626398d4d53eabe6fee1452bcfd17`: nested inline const folded in final LLBC.
- `charon/tests/ui/simple/trait-default-const.rs`, blob `15174933431c222931e9812860258da4772eb8be`, and `.out`, blob `a68f06677570a38515a5562a01f5f0b2f6e8991e`: default associated constant and blanket-impl reuse.

Existing corpus synthesis used rather than repeated:

- `rust-const-eval-const-functions-nightly-2026-05-31`: Rust's normative const-function/const-context distinction and the pinned rustc CTFE execution boundary.
- `charon-opaque-nightly-2026-06-03`: foreign/default opacity semantics.
- `charon-dependency-and-source-coverage-nightly-2026-06-03`: foreign-item reachability and MIR-availability boundary.
- `charon-support-and-unsoundness-nightly-2026-06-03`: fail/partial-output interpretation for unsupported translation.

No evidence gathered for this report is fresh **execution**.

## Revalidation

For a future Charon revision, first diff:

1. `GlobalKind`, `GlobalDecl`, `TraitAssocConst`, and `TraitImpl.consts`;
2. `TransItemSourceKind` and the global/initializer dual-registration rule;
3. `translate_global` category selection and initializer registration;
4. trait declaration/impl associated-constant wiring;
5. `translate_constant_expr`, especially unsupported-to-opaque cases;
6. transforms that can inline, evaluate, erase, or rewrite anonymous constants.

On an execution-capable surface, regenerate a compact fixture matrix containing:

- a literal named const;
- a named const that calls a `const fn`;
- a named const that refers to another const;
- a local function-scoped named const;
- a shared static and a `static mut`, each read and referenced in every permitted form;
- a non-`Copy` shared static;
- a thread-local static where supported by the target/toolchain;
- a generic inherent associated constant;
- a trait associated constant with no default;
- a default associated constant depending on `Self`/a supertrait;
- one impl reusing that default and one overriding it;
- a foreign constant under default opacity and explicit inclusion;
- nested inline const blocks;
- representative supported constant-expression ADT/array/borrow/function-pointer forms;
- a source shape that reaches each currently unsupported constant-expression path if rustc/Hax can produce it.

Preserve exact rustc/Charon revisions, compiler arguments, Charon options, diagnostics, ULLBC, final LLBC, and serialized metadata. Compare global declarations, initializer functions, associated-constant references, and error/`has_errors` state.

The discriminators are:

- whether the global/initializer split still exists;
- whether shared and mutable statics remain collapsed at the declaration category;
- whether use-site operations still preserve their access distinction;
- whether associated defaults/overrides still resolve through explicit `GlobalDeclRef`s and trait proofs;
- which source const computations remain as initializer code versus evaluated/simplified values;
- whether unsupported constant-expression forms still become error-marked opaque values.

That experiment would validate these representation claims for the tested revision. It would not prove Rust-level CTFE correctness, runtime static-memory semantics, or downstream Aeneas fidelity.