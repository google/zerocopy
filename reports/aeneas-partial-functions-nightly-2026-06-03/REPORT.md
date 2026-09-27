# Aeneas partial functions at nightly-2026.06.03

## Summary

Aeneas does not require every recursive Rust function or translated loop to come with a termination proof before it can emit Lean. At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the Lean backend marks translated recursive function groups with Lean's `partial_fixpoint` mechanism by default. This gives the generated function a mathematical fixed-point definition that can represent nontermination, while still exposing equations that proofs can use.

The runtime model makes that choice meaningful rather than merely syntactic. Aeneas's `Result α` has three cases: `ok`, `fail`, and `div`. The Lean library orders `Result α` as a flat partial order with `div` at the bottom, provides a chain-complete partial order (`CCPO`), and makes monadic bind monotone while propagating `div`. Lean's `partial_fixpoint` accepts recursive definitions over such a result domain when their recursive use is monotone. The generated function can therefore denote a diverging computation as `div` instead of forcing Aeneas to prove termination during translation.

This is a translation facility, not a proof that a Rust function terminates. A later specification can prove termination for selected inputs: Aeneas's weakest-precondition `spec` is false for both `fail` and `div`, so proving `f x ⦃ y => P y ⦄` establishes an `ok` result and excludes modeled divergence for that invocation.

No fresh Aeneas or Lean execution was performed. The findings come from the pinned Aeneas translator and Lean support library, the pinned Lean implementation of `partial_fixpoint`, and checked-in Aeneas generated examples.

## Applicability

This report applies to:

- Aeneas release `nightly-2026.06.03`, repository revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- the Lean backend's ordinary recursive-function extraction path;
- Lean 4 `v4.30.0-rc2` at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, which is the Lean revision used by the Anneal toolchain for this Aeneas release.

"Partial function" here means a translated semantic function that may not terminate on every input. It does not mean that Rust has a source-level `partial` function declaration.

This report focuses on Aeneas's default `partial_fixpoint` path. Aeneas also has a `-decreases-clauses` mode that asks for explicit termination measures and proofs. That alternate path, and its proof-authoring workflow, belongs to the separate extrinsic-termination subject and is not characterized here beyond the boundary noted below.

## Findings

### Aeneas marks recursive Lean functions with `partial_fixpoint`

The Lean extractor classifies function declarations as nonrecursive, singly recursive, or members of a mutually recursive group. `fun_decl_kind_to_post_qualif` maps every recursive declaration kind to the post-qualifier `partial_fixpoint`; nonrecursive, builtin, and declared functions receive no such qualifier.

`Translate.export_functions_group_scc` obtains strongly connected groups from the translated function dependency graph. A transparent singleton in a recursive SCC becomes `SingleRec`; members of a larger recursive SCC become `MutRecFirst`, `MutRecInner`, or `MutRecLast`. `Extract.extract_fun_decl_gen` then prints the qualifier returned by `fun_decl_kind_to_post_qualif`.

The mechanism is therefore driven by Aeneas's translated recursion structure, not by a hand-written annotation on one special function.

Basis: **source**.

### Translated loops can use the same mechanism

Aeneas represents loop bodies as generated function declarations. During extraction setup, it records a translated function as recursive when its forward-effect metadata says it is recursive, and it also records translated loop functions in the recursive-function set.

The checked-in `MiniTree.lean` output gives a concrete specimen. The Rust source contains a `while let` loop that walks child pointers. Aeneas's checked-in Lean output contains a generated `Tree.explore_loop` that recursively calls itself and ends with `partial_fixpoint`; the public wrapper simply calls that helper.

This demonstrates that `partial_fixpoint` is part of the ordinary loop-lowering story as well as direct source recursion.

Basis: Aeneas **source** + checked-in generated-output **source artifact**.

### Aeneas's semantic result type distinguishes divergence from failure

`Aeneas.Std.Result α` has exactly three constructors at this revision:

- `ok v` for successful completion;
- `fail e` for modeled failure;
- `div` for divergence.

Its bind operation runs the continuation only for `ok`. It preserves `fail` and maps `div` directly to `div`.

This matters because recursive partiality is not collapsed into the same result as a panic or other modeled error. A nonterminating semantic computation has a distinct representation.

Basis: Aeneas **source**.

### `div` is the bottom element used for partial fixed points

The same primitives file gives `Result α` a `PartialOrder` by reusing `FlatOrder .div`, then constructs a `CCPO` with `Result.div` as the bottom witness. It also supplies a `MonoBind Result` instance and monotonicity lemmas needed by Lean's partial-fixpoint checker.

These definitions connect the semantic `div` constructor to the fixed-point machinery. Recursive approximations can begin at divergence/bottom, and monadic sequencing remains monotone as the approximation improves.

Aeneas additionally provides `partial_fixpoint_monotone` lemmas for its internal `uncurry` form because the generated `do` elaboration can place recursive continuations behind `uncurry`. Without those lemmas, the generated syntax could obscure monotonicity from Lean's checker.

Basis: Aeneas **source** + **derived** interpretation of the order instances.

### Lean's `partial_fixpoint` keeps equations available for reasoning

At the pinned Lean revision, the parser documentation describes `partial_fixpoint` as defining a possibly nonterminating function as a fixed point in a suitable partial order. Lean compiles it as it would a `partial` definition but also provides its equations as theorems, so the definition remains usable in verification.

For the general case Lean requires a `CCPO` instance for the result domain and monotonicity with respect to recursive calls. The elaborator constructs the needed result-domain order, generates monotonicity goals, and builds the fixed point from the monotone functional.

Aeneas's `Result` instances are designed to satisfy this contract for generated monadic code.

Basis: Lean **documentation** in parser source + Lean **source** + Aeneas **source**.

### Translation can represent genuine input-dependent nontermination

The checked-in Aeneas tutorial contains a deliberately partial recursive example, `i32_id`. The function decrements a signed integer until it reaches zero. The tutorial notes that it terminates on nonnegative inputs but can recurse forever for negative inputs, and the definition ends in `partial_fixpoint`.

The same tutorial states the broader repository expectation: when Aeneas generates a recursive function, it annotates it with `partial_fixpoint`.

This example is useful because it separates two questions that are easy to conflate:

1. Can Aeneas emit a semantic definition for a possibly nonterminating recursive computation? Yes, through `partial_fixpoint`.
2. Has a particular call been proved to terminate? Not merely by translation.

Basis: checked-in Aeneas tutorial **source**.

### A specification can rule out `div` for the inputs it covers

`Aeneas.Std.WP.theta` maps:

- `ok x` to the supplied postcondition;
- `fail _` to `False`;
- `div` to `False`.

Accordingly, `WP.spec` is false on divergence, and the library proves
`spec m P ↔ ∃ y, m = ok y ∧ P y`.

A proof of an Aeneas specification therefore does more than establish a postcondition conditional on return. For the covered invocation it proves that the translated semantic computation reaches an `ok` result, which excludes both modeled failure and modeled divergence.

This proof-level fact composes with `partial_fixpoint`: translation may conservatively admit divergence, while a later theorem can rule it out on a chosen precondition.

Basis: Aeneas **source**.

### `partial_fixpoint` is not itself a termination proof

The generated fixed point gives a meaning to recursive code without first supplying a well-founded measure. It does not convert a potentially diverging Rust computation into a terminating Lean computation, and it does not establish that the source function terminates.

The checked-in tutorial makes the distinction explicit. Its theorem about `i32_id` restricts the input and then uses an ordinary Lean `termination_by` / `decreasing_by` argument for the recursive proof. Those clauses justify termination of the proof's recursive use; the function definition itself remains a `partial_fixpoint`.

Basis: checked-in Aeneas tutorial **source** + **derived** distinction.

## Boundaries

- No fresh Aeneas generation, Lean elaboration, or execution was performed.
- The checked-in Lean files are repository artifacts, not newly regenerated golden outputs on this surface.
- This report does not characterize all recursion and loop proof tactics. Another coordination scope covers loops, recursion, termination, and divergence more broadly.
- Aeneas has a `-decreases-clauses` option for generating explicit termination measures/proofs for recursive definitions. The detailed behavior and usability of that alternate path are not established here.
- The report does not prove that every Rust nontermination mode is faithfully modeled by `Result.div`; it describes the partial-recursion machinery present in the pinned translator and runtime.
- It does not establish translation correctness from Rust operational semantics to the generated fixed point.
- It does not establish how partial fixed points interact with every effect, external model, unsafe operation, or unsupported Rust construct.
- It does not assume adjacent Aeneas or Lean revisions preserve the same `partial_fixpoint` contract.

## Evidence

**Aeneas source:** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`, especially lines 1536-1544: recursive declaration kinds map to `partial_fixpoint`.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`, especially lines 838-913: recursive SCC classification and extraction; lines 1411-1430: recursive-function and loop accounting.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`, especially lines 2356-2361: emission of the post-qualifier.
- `backends/lean/Aeneas/Std/Primitives.lean`, blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1`, lines 62-65, 117-142, 159-179, and 196-222: `Result`, divergence propagation, partial-order/CCPO/monotone-bind instances, and monotonicity support for generated `uncurry`.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b`, lines 23-36, 54-61, and 178-188: `spec` rejects `fail` and `div` and is equivalent to existence of an `ok` result.
- `tests/src/mini_tree.rs`, blob `fbed6893fb840c0f0bc21bbf3b4e58b69db5ab6c`, lines 13-20: source loop specimen.
- `tests/lean/MiniTree.lean`, blob `ae54d4543872edac62862c999a2f91a227489b2f`, lines 33-48: corresponding checked-in recursive loop helper with `partial_fixpoint`.
- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`, lines 319-353 and 355-384: explicit partial-function explanation, diverging-input example, and a theorem that proves success for a restricted input domain.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`, lines 112-123 and 577-590: the separate decreases-clause option and its mutual-recursion restriction.
- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`, lines 216-245: fuel and decreases-clause configuration.

**Lean source:** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/Lean/Parser/Term.lean`, blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559`, lines 594-617: user-facing `partial_fixpoint` contract.
- `src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean`, blob `e83567283e7079a0c2f9c1a188d0f096d50dd13f`, lines 79-115 and 154-190: CCPO construction, monotonicity goals, and fixed-point construction.

No evidence above is fresh **execution**.

## Revalidation

For another Aeneas revision:

1. Diff `fun_decl_kind_to_post_qualif` in `src/extract/ExtractBase.ml`.
2. Diff recursive-SCC classification and recursive loop accounting in `src/Translate.ml`.
3. Diff `Aeneas.Std.Result`, its order/CCPO instances, bind, and `partial_fixpoint_monotone` lemmas in `backends/lean/Aeneas/Std/Primitives.lean`.
4. Diff the generated `MiniTree.lean` and partial-function tutorial examples.
5. Identify the Lean revision used with that Aeneas release and diff Lean's `partial_fixpoint` parser/elaborator contract.

On a capable execution surface, regenerate a minimal matrix at the exact revisions:

- a terminating nonrecursive Rust function;
- a structurally recursive Rust function;
- a loop translated to a recursive helper;
- a recursive signed-integer function that terminates only on a restricted input set.

Preserve the Rust inputs, generated Lean, stderr, tool revisions, and hashes. Confirm that recursive definitions receive `partial_fixpoint`, nonrecursive definitions do not, and the restricted-input theorem rules out `div` without changing the function definition itself.

That probe revalidates the emitted syntax and proof-facing behavior. It does not by itself prove semantic preservation from Rust to Lean.