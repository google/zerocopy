# Aeneas Lean backend, generated signatures, WP proof tools, package anatomy, scaling, and trusted base

## Summary

Across the Aeneas Lean backend at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`release: nightly-2026.06.03`) and `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`, seven structural and proof-engineering boundaries govern how translated Rust functions are emitted, specified, proved, packaged, scaled, and trusted:

1. **Generated Lean function interfaces vs. logical specification theorems**: The Lean backend emits pure executable/model function declarations (`extract_fun_decl_gen`), **not** an automatically generated weakest-precondition (`WP`) definition or Hoare specification theorem per Rust function. Generated signatures are assembled in two stages (`translate_inst_fun_sig_to_decomposed_fun_type` -> `translate_fun_sig_from_decomposed`): ordinary references (`&T`, `&mut T`) erase to `T` in `fwd_inputs` and `fwd_output`; mutable-borrow effects become region-group-indexed (`back_sg`) backward functions merged as returned closures (`compute_output_ty_from_decomposed`); unit-returning mutators collapse via `Config.simplify_merged_fwd_backs = true` (`fn incr(x: &mut u32)` becomes `Result Std.U32`, while `choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` becomes `Bool → T → T → Result (T × (T → (T × T)))`); and `mk_output_ty_from_effect_info` wraps the combined forward/backward tuple in `Result` when `can_fail` holds.
2. **Weakest-precondition (`Aeneas.Std.WP.spec`) and `step` / `step*` / `step*?` automation**: At `ac9f1bc5262a5e4ff1e24ca78617121382202727`, `Aeneas.Std.Result` has constructors `ok v`, `fail e`, and `div` (whereas at `21345f80fa212c596f6437378d7d57984fa2ea77`, `Result α := ITree RustEffect α` with DWP/DWLP). The generic specification predicate `WP.spec m P` (`theta m P`) evaluates to `P x` on `ok x` and `False` on both `fail _` and `div`, satisfying `spec_equiv_exists : spec m P ↔ ∃ y, m = ok y ∧ P y`. Hoare notation `f x ⦃ r₁ ... rₙ => Q ⦄` elaborates to `WP.spec` via `uncurry'` and quantifies directly over returned backward closures without needing a separate ownership logic. User-authored `@[step]` theorems register call specifications in the step database; `step` composes calls across monadic binds via `spec_bind'` (or `spec_mono'`), discharging preconditions via local hypotheses and `grind` (leaving unproven preconditions as subgoals); `step*` iterates across branches and finishes terminal goals with `agrind`; `step*?` emits an explicit `"Try this"` script (inserting `sorry` placeholders for unsolved subgoals); and `inferPost` (`false` by default) assigns unassigned `?post` metavariables. Historical Anneal V1 (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/v1`) layered `wp_prove_orthogonal : (∃ y, m = .ok y) → (∀ y, m = .ok y → P y) → WP.spec m P` and `eval_progress` on top of `WP.spec`.
3. **Lean package and split-file module anatomy**: `backends/lean/lakefile.lean` defines Lake package `aeneas` (pinning `leanprover/lean4:v4.30.0-rc2` at `ac9f1bc5262a5e4ff1e24ca78617121382202727` and Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`), exposing two default libraries (`Aeneas` and `AeneasMeta`) and the `extract` executable (`AeneasExtract.lean`), which inspects the compiled `Aeneas` Lean environment and generates `src/extract/ExtractBuiltinLean.ml`. Every generated crate file starts with `import Aeneas` (which transitively imports `Command`, `Data`, `Do`, `Extract`, `Std`, and `Tactic`, but not `AeneasMeta`). Under `-split-files`, Aeneas emits `<Crate>/Types.lean` and `<Crate>/Funs.lean` (plus `TypesExternal_Template.lean`, `FunsExternal_Template.lean`, and `Clauses/Template.lean` when needed, while importing user-maintained `TypesExternal`, `FunsExternal`, and `Clauses.Clauses`, and optional `<Crate>.lean` under `-gen-lib-entry`). Although `Translate.ml` contains code to emit a default `lakefile.lean` when `Config.lean_gen_lakefile` is `true`, `Config.ml` initializes `lean_gen_lakefile = false` and `Main.ml` binds `-lean-default-lakefile` to `Arg.Clear lean_gen_lakefile` (which also sets it to `false`), making manual Lake project setup required at this pin.
4. **Scaling, cost accounting, and proof-engineering maintenance**: End-to-end verification cost spans eight distinct stages (Rust/Charon LLBC extraction, whole-crate context setup, per-function symbolic translation, pure micro-passes, backend emission, Lake/Lean elaboration, proof search, and proof maintenance across interface/model updates). While `Config.parallel` defaults to `true` (using a persistent `Domainslib` pool in `Parallel.ml`) and `-diagnose-translation` / `-diagnose-micro-passes` record per-function wall times under a mutex, `-checks` (`Config.sanity_checks`, enabled by `tests/test_runner/run_test.ml` alongside `-sequential`) carries an upstream help-text warning of an approximately 100x slowdown. Industrial and pipeline experience reports (`arXiv:2609.15648v1` on SymCrypt with 16.7 KLOC Rust / 237,160 Lean lines and ~5,100 agent theorems; `arXiv:2605.30106v1` mixing Hax and Aeneas) and retained component probes (`fa65b241fd0cb2c791c841eace86d43d724359bc` on binary `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`) provide bounded workload evidence without establishing universal throughput or semantic preservation.
5. **Translation-correctness obligations**: A kernel-checked Lean theorem over generated definitions is conditional on five source-to-target bridges: (i) Rust -> Charon LLBC fidelity, (ii) LLBC -> Aeneas pure IR preservation across `PrePasses`, symbolic execution, and `PureMicroPasses`, (iii) soundness of internal builtins (`src/llbc/Builtin.ml`), `Aeneas.Std` models, and external models, (iv) fail-closed declaration coverage and zero-error exit status, and (v) target Lean elaboration and axiom-free theorem closure. Notably, `-checks` enables `Invariants.check_invariants` and `Translate.check_fun_decl_vars_are_well_bound`, **not** `Config.type_check_pure_code` (which remains `false` with `TODO: fix the bugs and reactivate`).
6. **Four-layer trusted computing base (TCB) and explicit library admissions**: Trust is claim-relative and dependency-sensitive:
   - For **Lean-level theorem validity**, tactics (`step`, `step*`, `agrind`), Charon, and Aeneas's code generator are outside the logical TCB because the Lean kernel (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) checks declaration typing unless `debug.skipKernelTC` is enabled or native evaluation (`native_decide` / `bv_decide` via `Lean/Meta/Native.lean` or `@[implemented_by]`) is used.
   - However, the pinned `Aeneas.Std` library contains explicit `axiom` declarations (`Pin.lean`, `Panic.lean`, `Atomic.lean`, `Fmt.lean`) and `sorry` proofs (`Slice.get_unchecked` and `get_unchecked_SliceIndexUsizeSlice_spec` in `Aeneas/Std/Slice.lean`, which elaborate to `sorryAx`), and Aeneas emits `axiom` for unresolved opaque declarations and `sorry` on extraction errors (`ExtractErrors.ml`). Transitive `#print axioms` (`Lean/Util/CollectAxioms.lean`) is therefore mandatory for Lean-level integrity, while **Rust-level theorem validity** additionally trusts `rustc` + `charon-driver`, Aeneas's translation pipeline and internal builtins, and every reached external/standard-library model.

---

## Applicability

This report synthesizes findings across all eight subjects recorded in `REPORT.json`:

1. **Aeneas `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`), the primary Aeneas revision selected by Anneal (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` in `anneal/flake.nix`).
2. **Paired Charon `0.1.210`** (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`), pinned by `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`charon-pin` blob `06dbe0dbf1d5b7f1e6f2a21889ab6bf770e89de6`).
3. **Lean 4 `v4.30.0-rc2`** (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), selected by `backends/lean/lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`) at `ac9f1bc5262a5e4ff1e24ca78617121382202727` together with Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (`backends/lean/lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee`).
4. **Historical Anneal V1 WP adapter** (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `path: anneal/v1`), examined solely to document the historical `wp_prove_orthogonal` / `eval_progress` decomposition over `Aeneas.Std.WP.spec`.
5. **Aeneas later source workflow revision** (`AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77`), whose `charon-pin` declares Charon `1aebab5f03a58067e5dc0ede2fec584117f54964` and whose `backends/lean/lean-toolchain` names `v4.35.0-rc4`, examined for scaling diagnostics (`-diagnose-translation`, `-diagnose-micro-passes`), `tests/test_runner/run_test.ml`, `scripts/check-charon-install.sh`, and `ITree RustEffect` / DWP context.
6. **SymCrypt scaling technical report** (`arXiv:2609.15648v1`, version `2026-09-14`) and **Rust-to-Lean pipeline experience report** (`arXiv:2605.30106v1`), examined as external documentation benchmarks of large-scale Aeneas/Hax proof engineering.
7. **Prior retained component experiments** (`corpus_revision: fa65b241fd0cb2c791c841eace86d43d724359bc`, `aeneas_source: ac9f1bc5262a5e4ff1e24ca78617121382202727`, `binary_sha256: f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`), providing empirical measurements of repeat-run determinism, concurrent split-file generation, and two-worker macOS `arm64` pipeline RSS/wall-time.

### Shared vs. Revision-Specific Behavior

- **Shared across `ac9f1bc5262a5e4ff1e24ca78617121382202727` and `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - Two-stage signature decomposition (`decomposed_fun_type` -> `fun_sig`), reference erasure in forward types, region-group-indexed backward closures (`back_sg`), `Config.simplify_merged_fwd_backs = true`, and outer `Result` wrapping.
  - Emitting pure Lean definitions without auto-generating per-function semantic `WP.spec` theorems; `⦃ ... ⦄` Hoare notation and `@[step]` / `step` / `step*` / `step*?` automation.
  - Lake package structure (`backends/lean/lakefile.lean` with `Aeneas`, `AeneasMeta`, and `extract` writing `src/extract/ExtractBuiltinLean.ml`), split-file dependency graph (`Types.lean`, `Funs.lean`, external templates), default `maxHeartbeats = 1000000` and `maxRecDepth = 2048` (`Config.ml`), `Config.sanity_checks = false` (`-checks` warning of ~100x slowdown), `Config.type_check_pure_code = false`, and process-global `Config` / `Errors` refs.
- **Specific to `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)**:
  - `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`) defines `Aeneas.Std.Result` as a 3-constructor inductive datatype (`ok v`, `fail e`, `div`) and `backends/lean/Aeneas/Std/WP.lean` (blob `018c456bcab5374de0b09b17eda0df1a48e2288b`) defines `theta` and `spec` by pattern matching on `ok`, `fail`, and `div`.
  - Pins Lean `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and Charon `0.1.210` (`a535e914f74db4fd9e6be7048f4233270d8945c0`).
- **Specific to `21345f80fa212c596f6437378d7d57984fa2ea77`**:
  - `Result` is defined as an interaction tree over `RustEffect` (`@[irreducible] def Result α := ITree RustEffect α`) and the WP layer uses DWP/DWLP.
  - Pins `lean-toolchain` `v4.35.0-rc4` and `charon-pin` `1aebab5f03a58067e5dc0ede2fec584117f54964`.

---

## Findings

### 1. Generated Lean Function Signatures and Backward-Closure Interfaces

#### 1.1 Two-Stage Signature Decomposition (`decomposed_fun_type` -> `fun_sig`)

In `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/symbolic/SymbolicToPureCore.ml` (blob `2f2b34275b8d7313733b146218bc6ed26716a7be`), and `src/symbolic/SymbolicToPure.ml` (blob `95ba91f539e48009efa420dfa956c4c55581cb3a`), Aeneas constructs each function's pure signature in two stages (`support/aeneas-generated-function-signatures/evidence-index.json`, `support/aeneas-generated-function-specifications/signature-shape-matrix.json`, and `support/aeneas-generated-function-specifications/source-map.json`):

1. **Decomposed signature (`translate_inst_fun_sig_to_decomposed_fun_type`)**: Produces a `decomposed_fun_type` record containing:
   - `fwd_inputs`: the Rust/LLBC input types translated via `translate_fwd_ty` (where `TRef` erases `&T` and `&mut T` to `T`, and `Box<T>` erases to `T`);
   - `fwd_output`: the pure forward return type before `Result` wrapping or backward continuations;
   - `back_sg`: a map indexed by region-group ID (`RegionGroupId`) mapping each group to a `back_sg_info` record of level-indexed backward inputs (`translate_back_input_ty`, values supplied when ending returned borrows) and backward outputs (`translate_back_output_ty`, values restored to original borrowed input arguments, with at most one output type per original forward input argument at a given abstraction level); and
   - `fwd_info`: effect metadata (`fun_effect_info`, including `can_fail`) and `ignore_output` (whether a unit forward output should be omitted).
2. **Final merged signature (`translate_fun_sig_from_decomposed`)**:
   - `compute_back_tys_with_info` converts each non-filtered `back_sg_info` into an arrow type from its backward inputs to its reconstructed backward outputs.
   - `compute_output_ty_from_decomposed` combines `fwd_output` (unless omitted by `ignore_output`) with all surviving backward values/functions into a tuple type.
   - `mk_output_ty_from_effect_info` wraps that combined forward+backward payload in `Result` when `fwd_info.effect_info.can_fail` holds.
   - `explicit_info` records which generic/type parameters are implicit (`{T : Type}`) vs. explicit (`(...)`), and `bs_ctx.forward_inputs` tracks the parameters corresponding to translated Rust inputs (before any micro-pass-introduced fuel or state parameters).

Basis: **source**.

#### 1.2 Merged Backward Closures, `simplify_merged_fwd_backs`, and Representative Shapes

In `src/symbolic/SymbolicToPureExpressions.ml` (blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`) and `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`), `translate_forward_end` constructs backward expressions inside the forward body and returns them as local closures alongside the forward value, rather than emitting separate top-level `<name>_back` declarations. Furthermore, `Config.simplify_merged_fwd_backs = true` performs two critical simplifications:

- If a backward computation requires **no backward inputs** (because the Rust function mutates `&mut` inputs in place without returning a borrow), Aeneas evaluates the backward update inside the forward function and returns the updated owner value directly rather than returning a closure (and avoids a redundant inner `Result` wrapper because raw effect calculation forces ordinary backward functions not to fail).
- If the Rust forward return type is `()` (`unit`) and a non-trivial backward output remains, `ignore_output` omits the `Unit` component from the returned tuple.

| Rust Signature Pattern | Checked-In Generated Lean Signature (`ac9f1bc5262a5e4ff1e24ca78617121382202727`) | Forward vs. Backward / Simplification Structure |
| --- | --- | --- |
| `fn incr(x: &mut u32) { *x += 1 }` (`Config.ml` doc example) | `incr (x : Std.U32) : Result Std.U32` | Forward `Unit` omitted (`simplify_merged_fwd_backs`); 0-input backward evaluated immediately to return updated `Std.U32`. |
| `pub fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T` (`NoNestedBorrows.lean` blob `e2a706b744e2e9a105e305cf8a2b353354209dae`) | `def choose {T : Type} (b : Bool) (x : T) (y : T) : Result (T × (T → (T × T)))` | Forward `T` paired with 1-region-group backward closure `T → (T × T)` reconstructing `(x', y')`; caller `choose_test` binds `(z, choose_back)`. |
| `fn array_to_mut_slice_<T>(s: &mut [T; 32]) -> &mut [T]` (`Arrays.lean` blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`) | `def array_to_mut_slice_ {T : Type} (s : Array T 32#usize) : Result ((Slice T) × (Slice T → Array T 32#usize))` | Forward `Slice T` paired with closure `Slice T → Array T 32#usize`. |
| `fn index_mut_array<T>(s: &mut [T; 32], i: usize) -> &mut T` / `index_mut_slice` (`Arrays.lean`) | `Result (T × (T → Array T 32#usize))` / `Result (T × (T → Slice T))` | Forward element `T` paired with element-to-container update closure. |
| `id_mut_pair3` (`NoNestedBorrows.lean`) / `inner_mut` (`NestedBorrows.lean` blob `61b3b2b31e50555182867a5b73fa510d05106e22`) | `inner_mut (x : Std.U32) : Result (Std.U32 × (Std.U32 → Std.U32) × (Std.U32 → Std.U32))` | Multiple region groups / abstraction levels yield multiple independent backward closures bound at call sites as `inner_mut_back`, `inner_mut_back1`. |
| `list_nth_mut1_loop` (`tests/lean/Tutorial/Tutorial.lean` blob `4513b4db1863ea7f3f55fb597ed3b94eb9c770a3`) | `Result (T × (T → CList T))` | Extracted `_loop` helper preserves the same forward+backward `Result` payload shape as its wrapper. |

#### 1.3 Registration of Callable Names vs. Trait Fields and Local `_back` Variables

In `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`) and `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`):

- `Pure.fun_decl.name` is debugging metadata only; `extract_fun_decl_register_names` registers top-level functions and loop/body helpers via `ctx_add_fun_decl` and `ctx_compute_fun_name` (`opt_rename_llbc_name`, `default_fun_suffix`), and `extract_fun_decl_gen` prints the registered name, `extract_fun_parameters`, and output type (preceded by a synthetic source-correspondence comment).
- Trait method declarations are **not** registered as standalone functions in `extract_fun_decl_register_names`; instead, they become structure fields on the trait dictionary (`structure BoolTrait (Self : Type) where get_bool : Self → Result Bool` in `tests/lean/Traits.lean` blob `d234936b72231024fbccf0030a08023836e5eb6e`), while default trait method bodies become separate definitions (`BoolTrait.ret_true.default`).
- Local variables bound to returned backward closures at call sites (`SymbolicToPureExpressions.ml`) take the callee's last path component plus `_back` (uniquified to `_back1`, etc.), and inside generated function bodies use `back` plus region-name hints.

Basis: **source** + checked-in generated **execution** artifacts.

---

### 2. Weakest-Precondition (`Aeneas.Std.WP.spec`) and `step` Proof Automation

#### 2.1 `Result`, `WP.spec`, and Total-Correctness Semantics

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`) defines `Aeneas.Std.Result α` as an inductive type with three constructors: `ok (v : α)` (normal return), `fail (e : Error)` (modeled failure/panic), and `div` (divergence), whose monadic `bind` propagates `fail` and `div` unchanged.

In `backends/lean/Aeneas/Std/WP.lean` (blob `018c456bcab5374de0b09b17eda0df1a48e2288b`), the weakest-precondition layer defines:

```lean
def Post (α : Type u) := α → Prop
def Pre := Prop
def Wp (α : Type u) := Post α → Pre
def wp_return (x : α) : Wp α := fun p => p x

def theta (x : Result α) : Wp α :=
  match x with
  | ok x => wp_return x
  | fail _ => fun _ => False
  | div => fun _ => False

def spec (x : Result α) (p : α → Prop) : Prop := theta x p
```

and proves the fundamental characterization theorem:

```lean
theorem spec_equiv_exists (m : Result α) (P : α → Prop) :
  spec m P ↔ ∃ y, m = ok y ∧ P y
```

Thus `WP.spec m P` is a **total successful-return specification** over the `Result` model: it rules out both modeled failure (`fail _`) and modeled divergence (`div`), and reduces on `ok x` to `P x`. The Hoare-style notation `f x ⦃ r₁ ... rₙ => Q ⦄` elaborates directly to `Aeneas.Std.WP.spec (f x) (uncurry' (fun r₁ ... rₙ => Q))`. Because backward closures are ordinary arrow values inside the tuple payload `α`, a specification for `choose` simply binds both the forward value and the backward closure:

```lean
choose b x y ⦃ z back => ... ⦄
```

without requiring any separate separation-logic or borrow-specific WP connective.

Basis: **source** + upstream **documentation** (`documentation/tactics-reference.md` blob `d09ac06bc02835e354a9fe7e6829762962439f2a`, `documentation/proof-strategies.md` blob `2b10ed04a1594d6b8a95a80c742af10885974143`).

#### 2.2 `@[step]`, `step`, `step*`, `step*?`, `inferPost`, Recursion, and Loops

Aeneas does not auto-generate a `WP.spec` theorem per extracted Rust function (only narrow metaprogramming helpers like `step_pure_def` synthesize `.step_spec` lemmas for pure Lean definitions). Instead, proof engineers write and register `@[step]` theorems (`tests/lean/BaseTutorial.lean` blob `52a9947feab2f607729e23c10dfc9e12bba02d41`; `tests/lean/Demo/Properties.lean` blob `fc3182dd7ce98fa9052a680b863ab7100feb1f4c`):

```lean
@[step] theorem my_func_spec ... (h₁ : pre₁) ... : my_func args ⦃ r₁ ... rₙ => post ⦄ := by ...
```

The tactic stack in `backends/lean/Aeneas/Tactic/Step/` operates as follows:

- **Step database and configuration (`Init.lean` blob `afaa4f2243a4d6bfcf08b36eff282886ed175ef2`)**: `@[step]` indexes theorems by target function symbol rather than theorem name. Default configuration enables matching local hypotheses, `step_pre_simps`, and `grind` for precondition discharge (`scalar_tac` is available but not enabled by default in the base step config).
- **Single-step symbolic composition (`Step.lean` blob `7939a977951e96143cda58b27094db0274c89ed2`)**: When the goal is a monadic bind `do let y ← f x; k y ⦃ P ⦄`, `step` applies `Std.WP.spec_bind'` (or `spec_mono'` on a terminal call), matches `f x` against the `@[step]` database (or an explicit theorem via `step with thm_name`), attempts to discharge theorem preconditions `hᵢ` (leaving any unproved precondition as an explicit Lean subgoal), introduces the output variables and postcondition hypotheses (named via `step as ⟨y, h₁, ...⟩`), and advances the goal to the continuation `k y ⦃ P ⦄`.
- **Multi-step branch traversal (`StepStar.lean` blob `710371a5675e053ce59c0d961ab5465ff0633738`)**: `step*` repeatedly applies `step`, simplifies, splits `match` / `if` branches into independent proof states (threading `grind` state across sequential steps while discarding branch-specific e-graphs across splits), and attempts to close terminal goals with `agrind`. `step*?` runs the same traversal and constructs a `"Try this:"` tactic script with explicit `step with ... as ...` calls, branch splits, and `sorry` placeholders where subgoals remain unsolved.
- **Postcondition metavariable inference (`InferPost.lean` blob `1de2fa4219832273f750b82abf3118c006aeeab6`)**: When `inferPost` is enabled (defaults to `false`) and a goal has the shape `?post args...` with an unassigned metavariable `?post`, `InferPost` synthesizes a predicate from escaping local variables, assigns `?post`, and runs `agrind`.
- **Recursive and loop specifications**: Recursive `@[step]` theorems are ordinary recursive Lean theorems checked by Lean's termination checker (`termination_by` / `decreasing_by` in `BaseTutorial.lean`; applying the recursive theorem before case-splitting triggers a Lean termination error rather than unsound circularity). Fixed-point loops use `loop.spec_decr_nat` (for a `Nat` measure) or `loop.spec` (for a general well-founded relation).

Basis: **source** + upstream **documentation** + preserved proof artifacts.

#### 2.3 Historical Anneal V1 "Orthogonal WP" Adapter

In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/v1/src/Anneal.lean` blob `727199a54622d56dd429f2b3b178748f2cc5b7f1`, `anneal/v1/docs/agent/05_proof_architecture.md` blob `8f7f589c629876a4696ed86f215ba1c050a4ba36`, `anneal/v1/docs/agent/06_tactics_and_tooling.md` blob `c8aac2f6cfdb244bafce5bc90669a679e6ab65fd`), Anneal V1 defined `SpecificationHolds`, `eval_progress`, and:

```lean
theorem wp_prove_orthogonal :
  (∃ y, m = .ok y) → (∀ y, m = .ok y → P y) → WP.spec m P
```

decomposing upstream `WP.spec m P` (via `spec_equiv_exists` / `spec_imp_exists`) into a progress obligation (`∃ y, m = .ok y`) and a partial-correctness implication (`∀ y, m = .ok y → P y`). This split was an Anneal V1 adapter pattern over `WP.spec`, not an upstream Aeneas primitive.

Basis: historical Anneal V1 **source** + **derived** comparison.

---

### 3. Lean Backend Package and Generated Module Anatomy

#### 3.1 `backends/lean` Lake Package, Umbrella Imports, and `AeneasExtract`

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- **Lake targets and toolchain (`backends/lean/lakefile.lean` blob `c32062866e2f88d2eb768b904745e7104edddb0d`, `lean-toolchain` blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`, `lake-manifest.json` blob `1a5af703163d8b39f4311aafe22ae171788179ee`)**: Declares package `aeneas` requiring Mathlib at `v4.30.0-rc2` (resolved to `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, along with `Plausible`, `LeanSearchClient`, `import-graph`, `ProofWidgets`, `Aesop`, `Qq`, `Batteries`, and `Cli`). It exposes three targets:
  1. `default_target` library `Aeneas` (`backends/lean/Aeneas.lean` blob `6fc8d91f1d1fcead6971b6e0aad88eb889a6f370`), which imports six umbrella modules: `Aeneas.Command` (blob `dc50083d6aad72e0ccd9e2bc840b7fa296cae6c7`), `Aeneas.Data` (blob `825cb5c009818b011433120a935c0b6beb0df8ef`), `Aeneas.Do` (blob `8cd4a8403eaf6e0cf70e944bbcbb74d34953d638`), `Aeneas.Extract` (blob `b8b88568546d9050c91158cec337cb2567e9b731`), `Aeneas.Std` (blob `565950fb36d3da1618a12866e0e5e3db2cc3be33`), and `Aeneas.Tactic` (blob `fc7a52a9fa77b762628de83a685f31cd0e98a273`).
  2. `default_target` library `AeneasMeta` (`backends/lean/AeneasMeta.lean` blob `c12cdc64f9b6f8b4457759e703a76c048f9fb106`, with `precompileModules` disabled when `CI` is set), importing `Async`, `Extensions`, `OptionConfig`, `Saturate`, `Simp`, and `Utils`. `Aeneas.lean` does not directly import `AeneasMeta`.
  3. Executable `extract` (`backends/lean/AeneasExtract.lean` blob `8982440660888eeb671bda0e726adf5b31c4ec2d`, `supportInterpreter := false`), invoked via `make extract-lean-std` to load the compiled `Aeneas` environment and write `src/extract/ExtractBuiltinLean.ml` in the repository root (populating the OCaml translator's builtin/external model registry).

#### 3.2 Generated Crate Module Graph, Prologues, and Unwired `-lean-default-lakefile`

In `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`), and `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`):

- **Common generated Lean prologue**: Every generated file emits `import Aeneas` (plus sibling module imports), `open Aeneas Aeneas.Std Result ControlFlow Error`, three linter suppressions (`dupNamespace`, `hashCommand`, `unusedVariables`), `set_option maxHeartbeats <N>` (default `1000000`), `set_option maxRecDepth <N>` (default `2048`), an optional `noncomputable section` (when opaque definitions exist and `-all-computable` is not set), and `namespace <crate_namespace>`.
- **Single-file vs. `-split-files` module graph**:
  - Without `-split-files`, all declarations are emitted into `<Crate>.lean`.
  - With `-split-files` (witnessed by `tests/lean/Avl/Types.lean` blob `3e5ad7260c9193434f73bd4d0b858794855e12f2` and `tests/lean/Avl/Funs.lean` blob `34be2c16a95a5ab7c59ebccc9cb54bb0bb84d38c`), Aeneas splits the crate into:
    ```text
    TypesExternal      Clauses.Clauses      FunsExternal
          ↖                 ↑                   ↗
           Types    [template/support]          |
              ↖             |                  |
                        Funs ------------------+
                         ↑
                      <Crate> (when -gen-lib-entry is passed; forbidden with -subdir)
    ```
    where Aeneas writes `TypesExternal_Template.lean`, `FunsExternal_Template.lean`, and `Clauses/Template.lean`, while `Types.lean` and `Funs.lean` import the user-maintained `TypesExternal`, `FunsExternal`, and `Clauses.Clauses` modules.
- **Unwired CLI flag for `lakefile.lean` generation**: Although `Translate.ml` contains a branch gated on `!Config.lean_gen_lakefile` to emit a default `lakefile.lean`, `Config.ml` initializes `let lean_gen_lakefile = ref false` and `Main.ml` wires `-lean-default-lakefile` to `Arg.Clear lean_gen_lakefile` (which sets the `ref` to `false`). Thus, as documented in `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`) and realized in `tests/lean/lakefile.lean` (blob `936ca23067e20c2f05bee88f77bbc00cc2b3b04e`) and `tests/lean/lean-toolchain` (blob `635bb9534e5a211d17a7d660a07dd31d1d64c450`), consumers must construct the surrounding Lake project and `require aeneas` from the `backends/lean` package path.

Basis: **source** + checked-in build/generated artifacts + upstream **documentation**.

---

### 4. Scaling, Cost Accounting, Test Workflows, and Empirical Probes

#### 4.1 Published Industrial and Pipeline Experience Benchmarks

As documented in `support/aeneas-scaling-proof-engineering-and-maintenance/evidence.json`:

- **SymCrypt verification (`arXiv:2609.15648v1`)**: Reports translating 16.7 KLOC of Rust into 237,160 lines of Lean (30,253 generated lines + 206,907 handwritten/agent definitions and proofs; Abstract and Table 1), with ~5,100 agent-generated theorems and 125 KLOC of proof scripts (Section 8.1). Across its 7-hard-proof suite (HKDF, ML-KEM, SHA-3; Figure 6), Opus 5 closed all 7 in single sessions and averaged ~2.8x faster and ~2.5x cheaper than Opus 4.8 on successful terminal runs. Section 8.3 separately benchmarks compiled C/Rust cryptographic throughput (16 KB messages, >=500 iterations on Intel Xeon W-2155 with AES-NI/AVX2). These proofs verify functional correctness relative to translator/model/specification assumptions (not side-channel leakage resistance).
- **Rust-to-Lean pipeline experience report (`arXiv:2605.30106v1`)**: Combines Hax (on Lean `4.26.0`, where Aleph completed 2 running-example theorems while 4 remained `sorry`) and Aeneas (on Lean `4.28.0`, verifying `fold_step` over 13 checked operations and a finite-field specification under explicit bounds). Its historical workarounds (monomorphic math core and explicit termination measures) reflect that earlier snapshot rather than current Aeneas dictionary/partial-fixpoint capabilities.

Basis: upstream **documentation** (papers).

#### 4.2 Stage-Separated Cost Accounting and Workload-Altering Flags

At `AeneasVerif/aeneas@21345f80fa212c596f6437378d7d57984fa2ea77` (`src/Config.ml` L95–99, L176–182, L478–497, L617–627; `src/Parallel.ml` L19–38; `src/Translate.ml` L315–325, L445–526, L2198–2211; `src/Main.ml` L133–136, L259–274; `src/Errors.ml` L79–98):

- **Parallel scheduling and diagnostics**: `Parallel.Pool` lazily spawns `recommended_domain_count - 1` worker domains; `Translate.translate_crate_to_pure` sorts transparent functions by descending size (noting in a comment that size-first ordering does not seem to have much effect) and records per-function elapsed wall time and syntax size/rank under a mutex when `-diagnose-translation`, `-diagnose-micro-passes`, `-diagnose-detailed`, or `-diagnose-limit` is passed. Because parallel tasks overlap, per-function wall times do not sum to critical-path latency.
- **Flags that change workload and proof obligations**:
  - `-checks` (`Config.sanity_checks = true`): Help text in `Main.ml` L133–136 warns of an approximately 100-fold slowdown; `tests/test_runner/run_test.ml` passes `-checks -sequential` by default, whereas default CLI runs have `sanity_checks = false` and `parallel = true`.
  - Loop and drop flags: `-loops-to-rec`, `-loops-no-rec`, `-feature-gates`, `-eval-drops` (clears `drop_as_no_op = true`), and `Config.ml` L176–182's loop fixed-point iteration guard of `2` (an internal convergence guard, not a semantic theorem).
  - Resource limits: `-max-heartbeats` (default `1,000,000`) and `-max-recdepth` (default `2,048`).
- **Separation of generation (`test`) and verification (`verify`) in CI**: `tests/test_runner/run_test.ml` runs Charon (`--preset=aeneas`, skipping Charon regeneration under `IN_CI` when a crate's `.llbc` file already exists) and then `aeneas` (`-print-error-emitters -no-progress-bar -checks -color -sequential` and `-abort-on-error` for normal tests), without invoking Lean. Target Lean checking occurs separately in `tests/lean/Makefile` (`lake exe cache get && lake build`) and the root `Makefile` (`verify` target), while `scripts/check-charon-install.sh` skips hash enforcement if `charon` is a symlink (`tests/README.md`).

#### 4.3 Retained Component Execution Probes (`ac9f1bc5262a5e4ff1e24ca78617121382202727`)

In the retained component experiments (`corpus_revision: fa65b241fd0cb2c791c841eace86d43d724359bc`, `binary_sha256: f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`):

| Retained Component Probe | Observed Measurement (`ac9f1bc5262a5e4ff1e24ca78617121382202727` / Lean `4.30.0-rc2`) | Scope Boundary |
| --- | --- | --- |
| 10 repeat-run generation invocations | Fixed 19,827-byte `.llbc` input produced byte-identical 1,219-byte `Probe.lean` across all 10 runs (only logs/mtimes varied) | Single fixture; does not prove universal parallel determinism across all crates. |
| Concurrent split-file generation | 4 isolated processes and 3 same-input shared-destination processes (`-sequential` inside each process) emitted matching 3-file split inventories | Does not establish in-process reentrancy or safety of concurrent writes with differing inputs. |
| 2-worker full pipeline on macOS `arm64` (8 GiB RAM) | Low-overhead serial run took `44.276 s` (sampled group RSS `1,999,008 KiB`) vs. 2-worker parallel `25.946 s` (sampled group RSS `3,599,968 KiB`); 4-worker ramp skipped | Tiny wrapping-add fixtures with warm caches; RSS sums can double-count shared pages. |

Basis: **source** + **documentation** + retained **execution** records in `support/aeneas-scaling-proof-engineering-and-maintenance/evidence.json`.

---

### 5. Translation-Correctness Obligations and Trusted Computing Base (TCB)

#### 5.1 What Aeneas Checks Locally vs. Disabled Pure Typechecking

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- **Local admission and invariant checks**:
  1. `Main.ml` checks that the `.llbc` file was generated with Charon's `Aeneas` preset and exits with status `1` if `Errors.error_list` is non-empty.
  2. When `-checks` is passed (`Config.sanity_checks = true`), `src/interp/Invariants.ml` (blob `3b67d1e21b165013ed503a3b8b9ceb5ca636a2a4`) checks five interpreter invariants at every evaluation step: (a) loan/borrow relationships, (b) borrowed-value invariants, (c) typing invariants, (d) symbolic-value invariants, and (e) abstraction-ID uniqueness; and `Translate.check_fun_decl_vars_are_well_bound` (`src/Translate.ml` blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`) checks free/bound variable closure.
- **Disabled pure-IR typechecker (`Config.type_check_pure_code = false`)**:
  - `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`) defines `type_check_pure_code = ref false` with the comment `TODO: fix the bugs and reactivate`, and `-checks` in `Main.ml` does **not** enable `type_check_pure_code`.
  - Consequently, `SymbolicToPureTypes.type_check_texpr` never invokes `src/pure/PureTypeCheck.ml` (blob `e9a07a43c2b77a1f71ca894af824ad23497e7fe0`, which itself has unfinished `TODO` branches for several qualifiers) during normal or `-checks` runs. Target type well-formedness is checked only when Lean compiles the emitted `.lean` files.

Basis: **source**.

#### 5.2 Four-Layer Trusted Base Partition (`Lean` vs. `Rust` Claims)

Evaluating what must be trusted for a theorem proved over Aeneas-generated Lean requires separating four layers:

| Trust Layer | Components / Mechanisms (`ac9f1bc5262a5e4ff1e24ca78617121382202727` & Lean `v4.30.0-rc2`) | Trusted for Lean-Level Theorem? | Trusted for Rust-Level Theorem? |
| --- | --- | --- | --- |
| 1. Logical checker & kernel bypasses | Lean kernel (`src/kernel/type_checker.cpp` blob `dd3741a339e1a3d6ea2cc0ebf9ecff2ad472f335`, `src/Lean/AddDecl.lean` blob `d56aec5aa4722268596e201a0ab26f6875007e85`), `debug.skipKernelTC` (`src/Lean/Environment.lean` blob `8a485808c7b0e4c32959740efa012a37610b6914`), native evaluation (`native_decide` / `bv_decide` in `src/Lean/Meta/Native.lean` blob `13a36c9408b4aecd716c2e0087085621f4f7cfe8`), `@[implemented_by]` (`src/Lean/Compiler/ImplementedByAttr.lean` blob `11ca8e5d512008b3efe1bd43d7d809f8ad53f7c8`) | **Yes** (`debug.skipKernelTC` must be `false`; tactics/metaprograms in `Aeneas/Tactic` are **not** trusted unless they invoke native evaluation). | **Yes** |
| 2. Theorem-specific logical admissions (`#print axioms`) | `sorryAx` (`src/Init/Prelude.lean` blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`), `Aeneas.Std` axioms (`Pin.lean` blob `6b9986ee9d37bb9d91cd4d4c313d58577d407f77`, `Panic.lean` blob `9b68b34206d1df98cd2c2f9e11ab6667a3d1fbda`, `Atomic.lean` blob `d686f3154fe6da9c2b4c1d6694764a1005332958`, `Fmt.lean` blob `0192e8acbb6d51c080abbc3a7addc61ecd24ec8e`), `Aeneas.Std` `sorry`s (`Slice.get_unchecked` and `get_unchecked_SliceIndexUsizeSlice_spec` in `Aeneas/Std/Slice.lean` blob `cab42e4f6ab768e97df8f5d3d9a5de73079a785c`), unresolved opaque `axiom`s (`ExtractBase.ml`), extraction-error `sorry`s (`ExtractErrors.ml` blob `9169ab076be376ee6150ef7f04b298b92a840965`) | **Yes, if reachable** in `#print axioms` (`src/Lean/Util/CollectAxioms.lean` blob `dc9897059a4463dfd143a2b3f8fbb4f4a3c3f154`, `src/Lean/Elab/Print.lean` blob `d9743c99111329d6ec43d94d84ae563d9cd7112d`). Unreached axioms in imported files do not taint the theorem. | **Yes, if reachable** (plus semantic adequacy of any reached axiom). |
| 3. Source-to-model translation & models | `rustc` + `charon-driver` (`main.rs` blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`, `driver.rs` blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`, `translate_crate.rs` blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`, `transform/mod.rs` blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`, `docs/what_charon_translates.md` blob `780949ef1304a89e34c87b04958d65dbc3bf0810`), Aeneas pipeline (`PrePasses`, symbolic execution, `SymbolicToPure`, `PureMicroPasses`, `Extract`), internal builtins (`src/llbc/Builtin.ml` blob `fec847925d30e0236f4bd5a83b18b270577f7918`), and reached `Aeneas.Std` / user external models | **No** (a translator or model bug cannot force the Lean kernel to accept a false Lean theorem). | **Yes** (Aeneas is not a proof-producing compiler; a bug here makes Lean prove a true theorem about the wrong model). |
| 4. Artifact, coverage, and exit-status ledger | Exact tool/model revisions, `.llbc` and `.lean` hashes, zero exit status from Charon and Aeneas (`Errors.error_list` empty), declaration coverage mapping, and theorem specification statement | Needed to identify the checked Lean environment and theorem. | **Yes** (prevents partial fail-open output or missing functions from being claimed as verified Rust). |

Basis: Aeneas, Charon, and Lean 4 **source** + **derived** four-layer TCB synthesis.

---

## Boundaries

- **Not examined**: No fresh execution of Charon, Aeneas, Lake, or Lean was performed in this synthesis; checked-in `.lean` files (`NoNestedBorrows.lean`, `NestedBorrows.lean`, `Arrays.lean`, `Traits.lean`, `BaseTutorial.lean`, `Tutorial.lean`, `Demo/Properties.lean`, `Avl/{Types,Funs}.lean`) and the retained component probes at `fa65b241fd0cb2c791c841eace86d43d724359bc` are pre-existing upstream/corpus artifacts. Exhaustive enumeration of every `axiom` or `sorry` across all `Aeneas.Std` submodules and transitive file-to-file imports inside `backends/lean` was not performed.
- **Unknown**: Whether any non-CLI internal script mutates `Config.lean_gen_lakefile` (`-lean-default-lakefile` clears it in `Main.ml`); general multi-core speedup and memory scaling of `Config.parallel = true` on large production crates; and whether `Config.type_check_pure_code` can be re-enabled without false positives after fixing its `TODO` branches.
- **Known not to apply**:
  - A generated Lean function declaration is **not** a semantic specification theorem, and `WP.spec` does **not** distinguish `fail` from `div` in positive specification claims (`spec m P` is `False` for both).
  - Passing `-checks` to `aeneas` does **not** enable `Config.type_check_pure_code`, and a `0` exit code from `aeneas` does **not** certify semantic preservation from Rust to Lean.
  - Importing `Aeneas` (which imports files containing `axiom` and `sorry` such as `Pin.lean`, `Atomic.lean`, and `Slice.lean`) does **not** taint a theorem unless those declarations appear in the theorem's transitive `#print axioms` closure; conversely, `lake build` succeeding on a Lean file does **not** mean the file is `sorry`-free.
  - Historical Anneal V1's `wp_prove_orthogonal` (`anneal/v1`) is an adapter lemma over `WP.spec`, not an upstream Aeneas primitive or a mandate for Anneal V2.
- **Unsupported**:
  - Enabling default `lakefile.lean` generation via the `-lean-default-lakefile` CLI flag at `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`Arg.Clear` sets the boolean ref to `false`).
  - Combining `-gen-lib-entry` without `-split-files` or combining `-gen-lib-entry` with `-subdir` (`Main.ml`).
  - Reasoning about arbitrary unsafe or concurrent Rust through the ordinary functional `Result` / backward-closure interface (unsafe raw-pointer dereference and concurrency lie outside the functional translation domain).

---

## Evidence

### 1. Primary Aeneas Source and Fixtures — `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`)

- **Signature translation, extraction, and error/invariant machinery**:
  - `src/pure/Pure.ml` (blob `acde8579d6861a08efae086c72f3156283110342`), `src/symbolic/SymbolicToPureTypes.ml` (blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`), `src/symbolic/SymbolicToPureCore.ml` (blob `2f2b34275b8d7313733b146218bc6ed26716a7be`), `src/symbolic/SymbolicToPureExpressions.ml` (blob `b24d12a8a8403a5bc8aae7b55c35ce0259b75bc8`), `src/symbolic/SymbolicToPure.ml` (blob `95ba91f539e48009efa420dfa956c4c55581cb3a`).
  - `src/extract/ExtractBase.ml` (blob `4fc8a3f35643ba66555f0889790d50993feef1b9`), `src/extract/Extract.ml` (blob `52754e4fdb25b50fce63abe2d2184751d69632e8`), `src/extract/ExtractErrors.ml` (blob `9169ab076be376ee6150ef7f04b298b92a840965`).
  - `src/Main.ml` (blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`), `src/Config.ml` (blob `99a9eba5ae67dde20dbfd8d835cdc2900fc60355`), `src/Translate.ml` (blob `8376e580b542bf3ee28cc9e3d4c170a17b23d379`), `src/PrePasses.ml` (blob `dc0ab803c26dafb14caf0da1bcc73e3499716835`), `src/Errors.ml` (blob `c135674b8601786616c6c20ad81ec388bb8cbfea`), `src/interp/Invariants.ml` (blob `3b67d1e21b165013ed503a3b8b9ceb5ca636a2a4`), `src/pure/PureTypeCheck.ml` (blob `e9a07a43c2b77a1f71ca894af824ad23497e7fe0`), `src/pure/PureMicroPasses.ml` (blob `e0662ab3153f3c401b44cbe6c0cad4e17157f063`), `src/llbc/Builtin.ml` (blob `fec847925d30e0236f4bd5a83b18b270577f7918`).
- **Lean backend package, WP, tactics, and standard-library models**:
  - `backends/lean/lakefile.lean` (blob `c32062866e2f88d2eb768b904745e7104edddb0d`), `backends/lean/lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`), `backends/lean/lake-manifest.json` (blob `1a5af703163d8b39f4311aafe22ae171788179ee`).
  - `backends/lean/Aeneas.lean` (blob `6fc8d91f1d1fcead6971b6e0aad88eb889a6f370`), `backends/lean/AeneasMeta.lean` (blob `c12cdc64f9b6f8b4457759e703a76c048f9fb106`), `backends/lean/AeneasExtract.lean` (blob `8982440660888eeb671bda0e726adf5b31c4ec2d`), `backends/lean/Aeneas/Std.lean` (blob `565950fb36d3da1618a12866e0e5e3db2cc3be33`), `backends/lean/Aeneas/Data.lean` (blob `825cb5c009818b011433120a935c0b6beb0df8ef`), `backends/lean/Aeneas/Tactic.lean` (blob `fc7a52a9fa77b762628de83a685f31cd0e98a273`), `backends/lean/Aeneas/Command.lean` (blob `dc50083d6aad72e0ccd9e2bc840b7fa296cae6c7`), `backends/lean/Aeneas/Do.lean` (blob `8cd4a8403eaf6e0cf70e944bbcbb74d34953d638`), `backends/lean/Aeneas/Extract.lean` (blob `b8b88568546d9050c91158cec337cb2567e9b731`).
  - `backends/lean/Aeneas/Std/Primitives.lean` (blob `bb730a91a4172fa5bd162f13c3e50bb8e9282b1f`), `backends/lean/Aeneas/Std/WP.lean` (blob `018c456bcab5374de0b09b17eda0df1a48e2288b`).
  - `backends/lean/Aeneas/Tactic/Step/Init.lean` (blob `afaa4f2243a4d6bfcf08b36eff282886ed175ef2`), `backends/lean/Aeneas/Tactic/Step/Step.lean` (blob `7939a977951e96143cda58b27094db0274c89ed2`), `backends/lean/Aeneas/Tactic/Step/StepStar.lean` (blob `710371a5675e053ce59c0d961ab5465ff0633738`), `backends/lean/Aeneas/Tactic/Step/InferPost.lean` (blob `1de2fa4219832273f750b82abf3118c006aeeab6`).
  - Explicit model axioms and `sorry`s: `backends/lean/Aeneas/Std/Core/Pin.lean` (blob `6b9986ee9d37bb9d91cd4d4c313d58577d407f77`), `backends/lean/Aeneas/Std/Core/Panic.lean` (blob `9b68b34206d1df98cd2c2f9e11ab6667a3d1fbda`), `backends/lean/Aeneas/Std/Core/Atomic.lean` (blob `d686f3154fe6da9c2b4c1d6694764a1005332958`), `backends/lean/Aeneas/Std/Core/Fmt.lean` (blob `0192e8acbb6d51c080abbc3a7addc61ecd24ec8e`), `backends/lean/Aeneas/Std/Slice.lean` (blob `cab42e4f6ab768e97df8f5d3d9a5de73079a785c`).
- **Documentation and checked-in fixtures**:
  - `README.md` (blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`), `documentation/aeneas-overview.md` (blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`), `documentation/tactics-reference.md` (blob `d09ac06bc02835e354a9fe7e6829762962439f2a`), `documentation/proof-strategies.md` (blob `2b10ed04a1594d6b8a95a80c742af10885974143`).
  - `tests/lean/lakefile.lean` (blob `936ca23067e20c2f05bee88f77bbc00cc2b3b04e`), `tests/lean/lean-toolchain` (blob `635bb9534e5a211d17a7d660a07dd31d1d64c450`), `tests/lean/NoNestedBorrows.lean` (blob `e2a706b744e2e9a105e305cf8a2b353354209dae`), `tests/lean/NestedBorrows.lean` (blob `61b3b2b31e50555182867a5b73fa510d05106e22`), `tests/lean/Arrays.lean` (blob `00b7716b63b41c4747889b42f2dee3796d3ab12d`), `tests/lean/Traits.lean` (blob `d234936b72231024fbccf0030a08023836e5eb6e`), `tests/lean/BaseTutorial.lean` (blob `52a9947feab2f607729e23c10dfc9e12bba02d41`), `tests/lean/Tutorial/Tutorial.lean` (blob `4513b4db1863ea7f3f55fb597ed3b94eb9c770a3`), `tests/lean/Demo/Properties.lean` (blob `fc3182dd7ce98fa9052a680b863ab7100feb1f4c`), `tests/lean/Avl/Types.lean` (blob `3e5ad7260c9193434f73bd4d0b858794855e12f2`), `tests/lean/Avl/Funs.lean` (blob `34be2c16a95a5ab7c59ebccc9cb54bb0bb84d38c`).

### 2. Scaling, Workflow, and Multi-Subject Sources

- **Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`**: `src/Main.ml` (L133–136, L259–274), `src/Config.ml` (L95–99, L176–182, L478–497, L617–627), `src/Parallel.ml` (L19–38), `src/Translate.ml` (L315–325, L445–526, L2198–2211), `src/Errors.ml` (L79–98), `tests/test_runner/run_test.ml`, `tests/README.md`, `tests/lean/Makefile`, `Makefile`, `charon-pin`, `scripts/check-charon-install.sh`.
- **Charon `0.1.210` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`)**: `charon/src/bin/charon-driver/main.rs` (blob `ab74f3f3d12a869bd8c3c94083b93b7dee1c2482`), `driver.rs` (blob `3f90a7a31857aed462694066e5ffaa6e28b9dcfa`), `translate/translate_crate.rs` (blob `53536c6df6e241c9655840f6b1f8a4aca2113f90`), `charon/src/transform/mod.rs` (blob `8d9ec016c3b6e42ba0cbac180546551d4a52587a`), `docs/what_charon_translates.md` (blob `780949ef1304a89e34c87b04958d65dbc3bf0810`).
- **Lean 4 `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)**: `src/Init/Prelude.lean` (blob `e55fd8785ca9d4f4b7ea61ce5c6939628d4bfe4b`), `src/Lean/Declaration.lean` (blob `3934023d7fce1054be48d71057c45d0ccada97b8`), `src/Lean/Util/CollectAxioms.lean` (blob `dc9897059a4463dfd143a2b3f8fbb4f4a3c3f154`), `src/Lean/Elab/Print.lean` (blob `d9743c99111329d6ec43d94d84ae563d9cd7112d`), `src/Lean/AddDecl.lean` (blob `d56aec5aa4722268596e201a0ab26f6875007e85`), `src/Lean/Environment.lean` (blob `8a485808c7b0e4c32959740efa012a37610b6914`), `src/kernel/type_checker.cpp` (blob `dd3741a339e1a3d6ea2cc0ebf9ecff2ad472f335`), `src/Lean/Compiler/ImplementedByAttr.lean` (blob `11ca8e5d512008b3efe1bd43d7d809f8ad53f7c8`), `src/Lean/Meta/Native.lean` (blob `13a36c9408b4aecd716c2e0087085621f4f7cfe8`).
- **Historical Anneal V1 (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`)**: `anneal/v1/src/Anneal.lean` (blob `727199a54622d56dd429f2b3b178748f2cc5b7f1`), `anneal/v1/docs/agent/05_proof_architecture.md` (blob `8f7f589c629876a4696ed86f215ba1c050a4ba36`), `anneal/v1/docs/agent/06_tactics_and_tooling.md` (blob `c8aac2f6cfdb244bafce5bc90669a679e6ab65fd`).
- **External reports**: `arXiv:2609.15648v1` (SymCrypt scaling report, `2026-09-14`) and `arXiv:2605.30106v1` (Rust-to-Lean experience report).

### 3. Preserved Package Support Artifacts

- `support/aeneas-generated-function-signatures/evidence-index.json`: source and fixture index for generated function signatures and `WP.spec` shape.
- `support/aeneas-generated-function-specifications/signature-shape-matrix.json` and `support/aeneas-generated-function-specifications/source-map.json`: matrix of Rust borrow/return patterns vs. decomposed and merged Lean signature shapes.
- `support/aeneas-scaling-proof-engineering-and-maintenance/evidence.json`: source excerpts, paper coordinates, and retained execution coordinates (`fa65b241fd0cb2c791c841eace86d43d724359bc`).

---

## Revalidation

To revalidate this package on a newer Aeneas, Charon, or Lean revision:

1. **Signature and WP interface diff**:
   - Diff `Pure.ml` (`decomposed_fun_type`, `back_sg_info`, `fun_sig`), `SymbolicToPureTypes.ml` (`translate_fwd_ty`, `compute_back_tys_with_info`, `compute_output_ty_from_decomposed`), `SymbolicToPureExpressions.ml` (`translate_forward_end`), and `Config.simplify_merged_fwd_backs`.
   - Diff `backends/lean/Aeneas/Std/Primitives.lean` (`Result` representation), `backends/lean/Aeneas/Std/WP.lean` (`spec`, `theta`, `spec_equiv_exists`, `spec_bind'`, `⦃ ... ⦄`), and `backends/lean/Aeneas/Tactic/Step/{Init,Step,StepStar,InferPost}.lean`.
2. **Package anatomy and build-bridge diff**:
   - Diff `backends/lean/{lean-toolchain,lakefile.lean,lake-manifest.json,Aeneas.lean,AeneasMeta.lean,AeneasExtract.lean}` and `src/Translate.ml` / `Main.ml` / `Config.ml` around `-split-files`, `-gen-lib-entry`, and `lean_gen_lakefile`.
3. **Trust, checks, and axiom audit**:
   - Diff `Config.ml` (`sanity_checks`, `type_check_pure_code`), `Invariants.ml`, `PureTypeCheck.ml`, `ExtractErrors.ml`, and scan `backends/lean/Aeneas/Std/` for `axiom`, `sorry`, `implemented_by`, and `native_decide`.
   - Run an end-to-end discriminating probe: translate a small crate containing `choose`, `incr`, a two-bind arithmetic caller, a call to `Slice.get_unchecked` (or an unresolved opaque external function), and one unsupported construct. Verify fail-closed exit status on the error case, prove a `@[step]` theorem over `choose` and its caller using `step` and `step*` with `debug.skipKernelTC = false`, and run `#print axioms` to confirm that the clean theorem has no `sorryAx` or model axioms while the `get_unchecked`/opaque theorem explicitly surfaces `sorryAx` or the external `axiom`.
