# Aeneas recursion and termination treatment at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the Lean backend does not require ordinary translated Rust recursion to be proven terminating when it defines the translated program. It emits recursive Lean functions with `partial_fixpoint`. Aeneas gives its `Result` type a flat chain-complete partial order whose bottom element is `Result.div`, so Lean's `partial_fixpoint` machinery gives recursive translated computations a semantic divergence case rather than an unchecked total definition.

Termination reappears at the specification boundary. Aeneas' standard `WP.spec` is false for both `Result.fail` and `Result.div`, and the library proves that `spec m P` is equivalent to the existence of an `ok` result satisfying `P`. A recursive proof of a specification is itself an ordinary Lean recursive theorem and must satisfy Lean's termination checker. Checked-in tutorial output therefore pairs generated `partial_fixpoint` program definitions with specification proofs that use `termination_by` and `decreasing_by`.

This split is the central operational model for Anneal: translated recursion may remain partial in the semantic program, while a proof that an invocation satisfies the usual Aeneas specification establishes successful termination for the proved inputs. Aeneas also has optional decreases-clause and fuel mechanisms, but neither replaces this default Lean behavior at this pin: fuel is rejected by the Lean backend, and decreases clauses are opt-in, unsupported for mutually recursive groups, and have an unexecuted source-level interaction with the ordinary `partial_fixpoint` suffix that should be revalidated before Anneal depends on that mode.

## Applicability

The Aeneas subject is release `nightly-2026.06.03`, whose Git tag resolves to `ac9f1bc5262a5e4ff1e24ca78617121382202727`. Current Anneal `main` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` downloads that Aeneas release in `anneal/flake.nix`. The selected Aeneas Lean backend pins `leanprover/lean4:v4.30.0-rc2`; this report therefore interprets Aeneas' generated `partial_fixpoint` declarations against `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

The report concerns Aeneas' treatment of recursive source functions and the termination boundary exposed to Lean proofs. Loops are relevant only where the same effect analysis marks them as potentially divergent or where they become recursive helpers. The dedicated loop-lowering subject should remain the authority for Aeneas' loop transformation choices.

The default-mode conclusions are based on exact implementation source and checked-in generated Lean at the pinned Aeneas revision. No fresh Aeneas or Lean executable was run for this report. In particular, the optional `-decreases-clauses` path is described only to the extent established by source; this report does not claim that a newly generated decreases-clause specimen compiles.

## Findings

### Aeneas classifies recursion as a possible source of divergence

`src/llbc/FunsAnalysis.ml` computes one effect summary for each function declaration group. A call to another member of the current group sets both `can_diverge` and `is_rec`. Calls to already analyzed functions propagate `can_diverge`, and encountering a loop also sets `can_diverge`. The same summary is assigned to every function in a mutually recursive group.

`src/pure/Pure.ml` preserves the intended distinction: `can_diverge` means that a function may not terminate because it is recursive, contains a loop, or transitively calls something that can diverge; `is_rec` means that the function is recursive or belongs to a mutually recursive group. `src/symbolic/SymbolicToPureTypes.ml` carries these flags into pure function effect information.

This analysis is conservative about ordinary failures as well. For non-global, non-builtin functions, `FunsAnalysis.ml` currently forces `can_fail = true`; `SymbolicToPureTypes.ml` wraps forward outputs in Aeneas' `Result` when `can_fail` is true. Consequently, ordinary translated recursive functions have a result type that can represent both failure and divergence even when a particular Rust body never panics.

Basis: source.

### Default Lean extraction marks recursive definitions `partial_fixpoint`

`src/Translate.ml` computes strongly connected components of translated functions and classifies a recursive singleton as `SingleRec`; members of a mutually recursive component become `MutRecFirst`, `MutRecInner`, or `MutRecLast`.

For the Lean backend, `src/extract/ExtractBase.ml` prints `def` for every one of those recursive declaration kinds. It then maps every recursive kind—single or mutual—to the post-qualifier `partial_fixpoint`. Non-recursive definitions receive no such post-qualifier.

The checked-in Lean tutorial is a concrete specimen of both cases. `tests/lean/Tutorial/Exercises.lean` contains a singly recursive `i32_id` ending in `partial_fixpoint`. It also contains a mutual block in which `even` calls `odd`, `odd` calls `even`, and both definitions end in `partial_fixpoint`.

This is not merely a marker that suppresses Lean's termination checker. At Lean v4.30.0-rc2, the parser documents `partial_fixpoint` as defining a possibly non-terminating function as a fixed point in a suitable partial order. The return type generally needs a `Lean.Order.CCPO` instance, and the recursive functional must be monotone. Lean's elaborator packs mutual groups, synthesizes the relevant order instances, proves monotonicity, and constructs the fixed point. It also produces equation theorems, so the definition remains usable in proofs.

Basis: Aeneas source + checked-in generated output + Lean source/documentation.

### Aeneas makes `Result.div` the bottom value used by partial fixed points

`backends/lean/Aeneas/Std/Primitives.lean` defines:

- `Result.ok v` for successful return;
- `Result.fail e` for modeled failure;
- `Result.div` for divergence.

Its monadic bind propagates both `fail` and `div`, invoking the continuation only for `ok`.

The same file then equips `Result α` with a partial order by using `FlatOrder .div`, installs a `CCPO (Result α)` whose bottom is therefore `Result.div`, and provides a monotone bind instance. It also registers monotonicity lemmas needed for generated tuple-destructuring continuations. These are exactly the structures consumed by Lean's `partial_fixpoint` elaborator.

The resulting interpretation is precise at this pin: the least element used to approximate an Aeneas recursive `Result` computation is modeled divergence, not arbitrary failure or an unconstrained inhabitant. Recursive translated code can therefore denote `div` if the fixed-point computation does not produce a successful or failing result.

Basis: Aeneas source + Lean fixed-point implementation; the final sentence is derived from the flat-order bottom and fixed-point construction.

### Aeneas specifications turn modeled partiality into a termination obligation

`backends/lean/Aeneas/Std/WP.lean` defines the weakest-precondition interpretation `theta` so that:

- `theta (ok x)` evaluates the requested postcondition at `x`;
- `theta (fail _)` is false;
- `theta div` is false.

`WP.spec m P` is `theta m P`. The library proves `spec_div : spec div p ↔ False` and, more strongly, `spec m P ↔ ∃ y, m = ok y ∧ P y`.

Therefore the ordinary Aeneas Hoare-style proposition

```lean
f x ⦃ y => P y ⦄
```

does not mean only "if `f x` returns successfully, then `P y`." A proof establishes that the translated computation is an `ok` result and that its value satisfies the postcondition. It excludes both modeled failure and modeled divergence for that invocation.

This fact is especially important for recursive functions. Aeneas may define the translated program by a partial fixed point without a source-level termination proof, while a later theorem can establish termination on a restricted precondition. For Anneal, a theorem of the standard `WP.spec` shape can therefore carry the total-correctness fact needed by a verified API even when the generated function itself remains semantically partial.

Basis: source; the last paragraph is derived from the definition and equivalence theorem.

### Recursive specification proofs have a separate Lean termination check

The generated function's `partial_fixpoint` does not make recursive proof reuse circularly sound by itself. A specification theorem is an ordinary Lean theorem definition. If its proof recursively invokes the theorem being defined, Lean checks termination of that proof definition.

The checked-in tutorial makes the separation explicit. After the `i32_id` program definition ends with `partial_fixpoint`, `i32_id_spec` unfolds the program, uses `step` at the recursive call, and ends with a `termination_by` measure and a `decreasing_by` proof. The mutually recursive `even_spec` and `odd_spec` theorem block does the same: each theorem has a measure `n.val` and a decreasing proof even though the underlying `even` and `odd` program definitions use `partial_fixpoint`.

Thus two different termination questions coexist:

1. **program semantics:** Aeneas can define recursive translated code without proving termination, using `partial_fixpoint` and the `Result.div` bottom;
2. **proof construction:** a recursively defined proof of `WP.spec` must itself satisfy Lean's ordinary well-founded-recursion requirements.

A failed proof-termination check therefore does not, by itself, show that the translated Rust function is unsupported. It may show only that the chosen recursive proof has not supplied a valid decreasing argument.

Basis: checked-in generated/tutorial Lean + Lean termination syntax.

### `-use-fuel` is not a Lean escape hatch at this pin

Aeneas contains a generic fuel transformation. `Config.use_fuel` defaults to false, and `PureMicroPassesGeneral.ml` can add fuel to potentially divergent functions, thread it through calls, and guard recursive bodies by matching on fuel.

That mechanism is unavailable for Lean here. `src/Main.ml` explicitly rejects `-use-fuel` for the Lean backend. It also rejects combining fuel with decreases clauses before backend-specific checks.

Anneal should therefore not plan around a hidden generated fuel parameter as the ordinary or fallback Lean recursion model for this release.

Basis: source.

### `-decreases-clauses` is an opt-in alternative with narrower support

`Config.extract_decreases_clauses` defaults to false. When enabled, Aeneas describes the Lean behavior as generating termination measures and decreasing proofs for recursive definitions, whose bodies the user supplies. Template termination/decrease declarations can be emitted to help fill those bodies.

`Translate.ml` records every recursively classified forward function, plus translated loop functions, in `functions_with_decreases_clause`. When decreases-clause extraction is enabled, `Extract.ml` emits a `termination_by` clause referring to the generated termination-measure name and a `decreasing_by` clause referring to the generated proof name.

The mode is not a general replacement for default recursive extraction. `Main.ml` rejects `-decreases-clauses` for Lean if the LLBC declaration list contains any mutually recursive function group. It also rejects the mode in combination with `-use-fuel`.

There is an additional source-level caveat at this exact revision. `Translate.ml` still classifies a recursive singleton as `SingleRec` when decreases-clause extraction is active. `Extract.ml` emits the `termination_by` / `decreasing_by` text when `has_decreases_clause` is true, and afterward unconditionally asks `fun_decl_kind_to_post_qualif` for the recursive declaration's post-qualifier. `ExtractBase.ml` maps `SingleRec` to `partial_fixpoint`. Source inspection therefore indicates that this path attempts to emit both the decreases-clause material and the ordinary recursive `partial_fixpoint` suffix. This report did not execute the path and does not assert that the resulting syntax is accepted by the selected Lean toolchain. Treat exact-pin execution of a one-function recursive specimen as required before relying on `-decreases-clauses` operationally.

Basis: source. The final compatibility statement is deliberately an unresolved source-derived concern, not an execution result.

### Mutual recursion is supported in the default partial-fixpoint model

The optional decreases-clause mode rejects mutual recursion, but the default Lean path does not. `ExtractBase.ml` assigns `partial_fixpoint` to all mutual-recursion declaration kinds, and the selected Lean elaborator explicitly handles cliques of multiple `partial_fixpoint` definitions by packing their function spaces and constructing one fixed point.

The pinned tutorial provides a checked-in Aeneas specimen: `even` and `odd` are emitted in a Lean `mutual` block, both use `partial_fixpoint`, and their matching specification theorems form a separate mutual block with explicit termination measures.

Accordingly, "Aeneas supports mutual recursion" and "Aeneas decreases clauses support mutual recursion" have different answers at this pin: default partial-fixed-point extraction has a concrete checked-in mutual-recursion specimen; the decreases-clause mode is explicitly rejected.

Basis: Aeneas source + checked-in generated output + Lean source.

## Boundaries

**No fresh execution.** The report did not run Aeneas, Lean, or Anneal. The default path has stronger evidence than source alone because the repository preserves generated Lean specimens, but this report does not independently establish that every checked-in specimen was regenerated by precisely the release binary distributed to Anneal.

**Optional decreases-clause compatibility is unresolved.** Source inspection establishes the CLI rules and emitted components, but not whether the combined emitted suffix accepted by the exact Lean toolchain is valid in practice. Do not upgrade the source-level observation into a working-mode guarantee without the revalidation probe below.

**Loop transformation is not inventoried here.** A loop can set `can_diverge` and may become a recursive helper, but the choice among loop encodings, loop-body generation, and loop-specific proof interfaces belongs to the separate Aeneas loop-lowering report.

**Divergence propagation beyond recursion is not exhaustive here.** `FunsAnalysis.ml` propagates `can_diverge` through calls and marks loops, but this report does not inventory every opaque external, dynamic call, trait method, builtin, or unsupported construct that may affect semantic termination. The issue inventory has a separate infinite/diverging-execution subject for that broader question.

**No claim about Rust source termination.** A recursive Rust function can terminate for all reachable inputs even though Aeneas conservatively models its translated definition with `partial_fixpoint`. Conversely, a generated `partial_fixpoint` definition is not evidence that the original function actually diverges. The annotation defines the semantic allowance and proof boundary.

**No claim that `WP.spec` is the only useful specification relation.** The conclusion about successful termination applies to the standard `Aeneas.Std.WP.spec` / `⦃ ⦄` interface examined here. Other predicates could intentionally express weaker properties of `Result.div`.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

### Aeneas selection and toolchain

- `AeneasVerif/aeneas` tag `nightly-2026.06.03` resolves to commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: Anneal downloads Aeneas release `nightly-2026.06.03`.
- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: selected Lean toolchain is `leanprover/lean4:v4.30.0-rc2`.

### Recursion/effect analysis and extraction

- `src/llbc/FunsAnalysis.ml`, blob `a2678ba12e8baaaf14fc99c3f061b10edae2da86`: group effect analysis; recursive calls set `can_diverge` and `is_rec`; loops and transitive calls propagate divergence.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: definitions and intended meanings of `can_diverge` and `is_rec`.
- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: effect propagation and `Result` output wrapping.
- `src/Translate.ml`, blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`: recursive SCC classification; decreases-clause target set; extraction dispatch.
- `src/extract/ExtractBase.ml`, blob `4fc8a3f35643ba66555f0889790d50993feef1b9`: Lean recursive declaration qualifiers and unconditional `partial_fixpoint` post-qualifier for recursive kinds.
- `src/extract/Extract.ml`, blob `52754e4fdb25b50fce63abe2d2184751d69632e8`: function extraction, optional `termination_by` and `decreasing_by` emission, then recursive post-qualifier emission.
- `tests/lean/Tutorial/Exercises.lean`, blob `6db5aeffbaec39f5d3a335995b948e2d72ca1f07`: checked-in single recursion, mutual recursion, `partial_fixpoint`, and recursive specification proofs with termination measures.
- `tests/lean/BaseTutorial.lean`, blob `52a9947feab2f607729e23c10dfc9e12bba02d41`: explanatory checked-in examples of `partial_fixpoint` and proof-level termination.

### Divergence semantics and specifications

- `backends/lean/Aeneas/Std/Primitives.lean`, blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`: `Result.ok`, `Result.fail`, `Result.div`; bind propagation; flat partial order with `.div` bottom; CCPO and monotone-bind support.
- `backends/lean/Aeneas/Std/WP.lean`, blob `018c456bcab5374de0b09b17eda0df1a48e2288b`: `theta`, `spec`, `spec_div`, and `spec_equiv_exists`.
- Existing reference package `reports/aeneas-wp-proof-tools-nightly-2026-06-03`, `REPORT.md` blob `d20e3e593534645fa394649b34eaaff71c734719`: independently preserved reference coverage of the same WP success/termination boundary; this report specializes the recursion side rather than replacing that report.

### Optional termination mechanisms

- `src/Config.ml`, blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`: defaults and intended semantics of fuel and decreases-clause generation.
- `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`: CLI compatibility checks, Lean fuel rejection, and Lean mutual-recursion rejection for decreases clauses.
- `src/pure/PureMicroPassesGeneral.ml`, blob `32d37b2363a69b9cf8a765b6446deb753aadc27b`: generic fuel threading/wrapping logic.

### Lean `partial_fixpoint`

- `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `src/Lean/Parser/Term.lean`, blob `16b73a52ad5c2e6819a9d009012a5e2d75f30559`: documented `partial_fixpoint` contract and syntax.
- Same revision, `src/Init/Internal/Order/Basic.lean`, blob `10e5888e1e43cc87e64509b489de2204fc3ea296`: CCPO and bottom construction used by partial fixed points.
- Same revision, `src/Lean/Elab/PreDefinition/PartialFixpoint/Main.lean`, blob `e83567283e7079a0c2f9c1a188d0f096d50dd13f`: CCPO synthesis, mutual-function packing, monotonicity proof, and fixed-point construction.

## Revalidation

For a newer Aeneas release, first inspect the smallest set of source points that determines the model:

1. resolve the immutable Aeneas tag/revision and its `backends/lean/lean-toolchain`;
2. inspect `FunsAnalysis.ml` and `Pure.ml` for `can_diverge` / `is_rec` semantics;
3. inspect `ExtractBase.ml` for the Lean qualifier and post-qualifier assigned to all recursive declaration kinds;
4. inspect `Primitives.lean` for the `Result` constructors and the CCPO bottom;
5. inspect `WP.lean` for the exact semantics of `spec`, especially failure and divergence;
6. inspect a checked-in generated single-recursion and mutual-recursion specimen.

A narrow execution probe is preferable when changing operational behavior. Use one Rust source with a self-recursive function and one mutually recursive pair. Generate Lean in the default mode and verify that the emitted declarations elaborate with the selected Lean toolchain; then prove a terminating-input `WP.spec` theorem with an explicit decreasing measure.

Before relying on `-decreases-clauses`, add a separate exact-pin probe for a singly recursive function. Capture the generated Lean text, specifically the ordering and coexistence of `termination_by`, `decreasing_by`, and any `partial_fixpoint` suffix, and compile it with the selected Lean toolchain. Then repeat with mutual recursion and confirm the Aeneas CLI rejects that configuration before translation, as `Main.ml` specifies.

For fuel, a source check of the Lean backend's argument validation is sufficient while `-use-fuel` remains explicitly rejected. If that rejection disappears, re-run a recursive specimen and inspect both function signatures and recursive calls rather than assuming the old generic fuel micro-pass became the Lean semantics unchanged.