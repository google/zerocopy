# `iris-lean@81bc350` `NotStuck` Adequacy Semantics, Undefined-Behavior Encoding Bridges, and MiniRust Formalization Survey

## Summary

Connecting an operational semantics for a low-level language with undefined
behavior (such as MiniRust) to an Iris-style program logic in Lean 4 requires
aligning two distinct layers: (1) how undefined behavior, divergence, and
nondeterminism are encoded into `iris-lean`'s `Language` and `Adequate`
interfaces, and (2) what upstream MiniRust (`minirust@d821c6e`) and existing
theorem-prover formalizations actually mechanize. This report establishes two
sets of findings:

1. **`iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c` `NotStuck` Adequacy and UB-Encoding Bridge (Mechanized in Lean 4.34.1):**
   - In `Iris/ProgramLogic/Language.lean:68-120` and
     `Iris/ProgramLogic/Adequacy.lean:174-372`, `NotStuck .NotStuck e σ` is
     defined as `(toVal e).isSome ∨ reducible e σ`, and `adequate .NotStuck e₁ σ₁ φ`
     enforces the return-value postcondition `φ` on the main thread (index `0`
     of the thread pool) together with `NotStuck` on **every** thread in every
     finitely reachable configuration (`NSteps L n ([e₁], σ₁) (t₂, σ₂)` for all
     `n : Nat`, including `n = 0`).
   - **Exact Equivalence Under Irreducible Non-Value UB Encoding (`stuck_ub_adequacy_iff_no_ub`):**
     `Adequate L .NotStuck e₁ σ₁ (fun _ _ => True)` is logically equivalent to
     operational `NoReachableUB` if and only if every UB state is an irreducible
     non-value (`toVal e = none ∧ ¬ reducible L e σ`) and every non-UB state is
     either a value or reducible (`WellEncodedUB`). Safe diverging computations
     (`loop`, `toVal = none ∧ reducible`) satisfy `Adequate L .NotStuck` across
     all finite horizons without any termination premise (`loop_adequate_notstuck`).
   - **Three Machine-Checked Failure Modes When `WellEncodedUB` Is Violated:**
     - *Terminal value-encoded errors (`valueError`, `toVal = some .errorVal`):*
       Every value satisfies `NotStuck` (`Or.inl rfl`). Under `φ = True`,
       `Adequate` holds (`value_error_masks_ub_under_true_post`). More subtly,
       even when the main-thread postcondition `φ` explicitly rejects `.errorVal`
       (`φ v _ := v ≠ .errorVal`), standard `Adequate` (`wp_adequacy_gen`, which
       existentially hides `forkPost`) **still accepts** a program whose forked
       child thread evaluates to `.val .errorVal` while the main thread returns
       `.okVal 0` (`value_error_in_forked_thread_masks_ub_under_standard_adequacy`).
       Catching value-encoded UB in forked threads requires `StrongAdequate`
       (`wp_strong_adequacy_gen`) with an explicit `forkPost`
       (`strong_adequacy_rejects_value_error_in_forked_thread`).
     - *Stutter-reducible error states (`stutterError → stutterError`):*
       Stuttering error states are `reducible` and never reach a value, so they
       satisfy `Adequate L .NotStuck` for **every** postcondition `φ`, including
       `False` (`stutter_error_masks_ub_for_all_postconditions`).
     - *Pruned nondeterministic error branches (`chooseError`):*
       Omitting a UB transition branch (`chooseError → stuckError`) while
       retaining a safe branch (`chooseError → val (okVal 0)`) preserves
       reducibility and causes `Adequate L .NotStuck` to hold on the pruned
       language (`choose_error_pruned_adequate`) while failing on the full
       language (`choose_error_unpruned_not_adequate`).
2. **Upstream MiniRust (`d821c6e`) / `specr` (`15200eb`) Audit and Comparative Formalization Survey:**
   - Upstream MiniRust separates machine words from untyped byte-level memory via
     a pluggable `Memory` trait (`BasicMemory`, `TreeBorrowsMemory`, and a
     wrapper `ConcurrentMemory`) and a typed `Value` ↔ `List<AbstractByte<Provenance>>`
     encode/decode layer with `expose`/`predict` integer-to-pointer casts.
   - However, upstream MiniRust is written in Specr-lang (`minirust/specr@15200eb5e6`),
     whose transpiler targets only executable Rust with a 50-sample angelic
     nondeterminism cap (`pick` in `libspecr/src/nondet.rs`), unimplemented
     `predict`, a known type well-formedness coherence defect (`minirust#288`),
     fixed concrete target layouts, provenance stripping on non-pointer loads
     (`decode_ptr`), and a single-step race detector in `ConcurrentMemory` whose
     multi-step inter-action window is an unimplemented placeholder.
   - Across seven existing theorem-prover efforts in Lean 4 and Rocq/Coq, no
     end-to-end mechanized transcription of full MiniRust exists: existing works
     formalize either standalone fragments (`coq-minirust`, Viktor Fukala's 2024
     Rocq thesis, Lean 4 operational fragments), standalone aliasing models
     (Tree Borrows PLDI 2025 in Simuliris over $\lambda_{\text{TB}}$), or
     bespoke intermediate languages (RefinedRust's Radium/Caesium, `iris-itree`,
     and `pcg-docs`).

## Applicability

These findings apply to:

- **`leanprover-community/iris-lean`:** Commit
  `81bc35088ba67d465db008f5261a9b341eb6cf6c` (tree
  `de91073ccc69a74b5ed56df1c41cc61f6bf05816`, pinned upstream to
  `leanprover/lean4:v4.29.0`), specifically `src/Iris/ProgramLogic/Language.lean`
  (blob `73baacd35f8c021c30010d617b323377dcfe637b`),
  `src/Iris/ProgramLogic/WeakestPre.lean` (blob
  `340e21c30faca0364498f94fba9b01983461c80e`), and
  `src/Iris/ProgramLogic/Adequacy.lean` (blob
  `0c76491cadff6b5a870df2d9b4930773d0df5623`).
  (Companion report `reports/iris-adequacy-resource-interface-8e49095/` covers
  the earlier `8e49095` snapshot.)
- **`minirust/minirust`:** Commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`
  (2026-06-05), alongside `minirust/specr` commit `15200eb5e6`.
- **`leanprover/lean4`:** Release `v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52` on `x86_64-unknown-linux-gnu`
  under deterministic flags `-j1 -M768`.

## Findings

### 1. `iris-lean@81bc350` Operational `Language`, `NotStuck`, and Adequacy Interfaces

- **Basis:** `source` (`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`,
  authenticated blob manifest in
  [`support/authenticated-selected-identities.json`](support/authenticated-selected-identities.json)
  and 183-module textual import graph in
  [`support/independent-import-graph.json`](support/independent-import-graph.json)).

In `iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`:

| Construct | Source Location | Exact Definition & Operational Role |
|---|---|---|
| `Language` | `Iris/ProgramLogic/Language.lean:21-40` | Bundles `Expr`, `Val`, `State`, `Observation`, `ofVal`, `toVal`, and `primStep : Expr → State → List Observation → Expr → State → List Expr → Prop` with round-trip axioms `to_of_val`, `of_to_val`, and `val_stuck` (`primStep e σ κs e' σ' efs → toVal e = none`). Does **not** contain a built-in undefined-behavior constructor. |
| `reducible`, `irreducible`, `stuck`, `NotStuck` | `Iris/ProgramLogic/Language.lean:68-86` | `reducible e σ := ∃ κs e' σ' efs, primStep e σ κs e' σ' efs`; `stuck e σ := toVal e = none ∧ irreducible e σ`; `NotStuck .NotStuck e σ := (toVal e).isSome ∨ reducible e σ` (`NotStuck .MaybeStuck e σ := True`). |
| `Step` & `NSteps` | `Iris/ProgramLogic/Language.lean:96-120`, `Adequacy.lean:236-246` | `Step (t₁ ++ e₁ :: t₂, σ₁) (t₁ ++ e₂ :: t₂ ++ efs, σ₂)` steps one thread `e₁` and appends spawned threads `efs`; `NSteps` is the `n`-step reflexive-transitive closure (including `n = 0`). |
| `wp.pre` | `Iris/ProgramLogic/WeakestPre.lean:35-84` | If `toVal e₁ = some v`, requires `|={E}=> Φ v`. If `toVal e₁ = none`, requires state interpretation `state_interp σ₁ ns (κ ++ κs) nt`, step-fancily-updated `reducible_or_not_stuck s e₁ σ₁` (which enforces `reducible e₁ σ₁` when `s = .NotStuck`), and universal continuation quantification over all `e₂, σ₂, efs` such that `primStep e₁ σ₁ κ e₂ σ₂ efs`, plus `[∗ list] ef ∈ efs, wp ⊤ ef fork_post`. |
| `adequate` & `wp_adequacy_gen` | `Iris/ProgramLogic/Adequacy.lean:236-246, 302-334` | `adequate s e₁ σ₁ φ` holds iff for every `n, t₂, σ₂` with `NSteps n ([e₁], σ₁) (t₂, σ₂)`: (1) if `t₂ = ofVal v₂ :: t₂'`, then `φ v₂ σ₂`; and (2) if `s = .NotStuck`, every thread `e₂ ∈ t₂` satisfies `NotStuck e₂ σ₂`. Note that `wp_adequacy_gen` existentially hides `fork_post`. |
| `wp_strong_adequacy_gen` & `wp_invariance_gen` | `Iris/ProgramLogic/Adequacy.lean:174-232, 342-372` | `wp_strong_adequacy_gen` exposes final-state resources, per-thread `NotStuck`, and `fork_post` on returned forked threads; `wp_invariance_gen` extracts a pure state invariant `φ σ₂` at any finitely reachable state `σ₂` without requiring the main thread to reach a value. |

The full local `Iris` textual source tree comprises `183` `.lean` files
(`2,686,371` bytes total, `702` internal import edges, zero import cycles, and
zero `sorry`/`axiom`/`opaque` tokens in source text, audited in
[`support/independent-import-graph.json`](support/independent-import-graph.json)).
The transitive import closure of `Iris.ProgramLogic.Adequacy` alone spans `88`
modules (`1,575,933` bytes) plus `Std`/`Batteries` dependencies.

### 2. Machine-Checked UB-Encoding Bridge and Failure Counterexamples in Lean 4.34.1

- **Basis:** `execution` and `derived`
  ([`support/iris_notstuck_adequacy_and_ub_encoding.lean`](support/iris_notstuck_adequacy_and_ub_encoding.lean)
  and [`support/iris_notstuck_adequacy_and_ub_encoding.eval.json`](support/iris_notstuck_adequacy_and_ub_encoding.eval.json)).

Because `iris-lean`'s `Language` structure has no dedicated UB constructor, a
verification bridge from `Adequate L .NotStuck` to operational UB-freedom
(`NoReachableUB`) depends entirely on how UB configurations are represented in
`toVal` and `primStep`. In
[`support/iris_notstuck_adequacy_and_ub_encoding.lean`](support/iris_notstuck_adequacy_and_ub_encoding.lean)
(checked under `lean -j1 -M768` in `0.890s` and `521.6 MB` max RSS), we prove:

| Theorem Name | Operational Scenario | Machine-Checked Result |
|---|---|---|
| `stuck_ub_adequacy_iff_no_ub` | General language `L` satisfying `WellEncodedUB L IsUB` (`IsUB e σ → toVal e = none ∧ ¬ reducible L e σ`, and `¬ IsUB e σ → NotStuck .NotStuck e σ`) | `L.Adequate .NotStuck e₁ σ₁ (fun _ _ => True) ↔ NoReachableUB L IsUB e₁ σ₁` |
| `stuckError_not_adequate` | `.stuckError` (`toVal = none`, no outgoing `primStep`) | `¬ ProbeLangFull.Adequate .NotStuck .stuckError () (fun _ _ => True)` (rejected at `n = 0` steps) |
| `loop_adequate_notstuck` | `.loop` (`toVal = none`, `primStep .loop () [] .loop () []`) | `ProbeLangFull.Adequate .NotStuck .loop () (fun _ _ => False)` (safe divergence holds at all `n : Nat` without termination) |
| `value_error_masks_ub_under_true_post` | `.val .errorVal` (`toVal = some .errorVal`) under permissive `φ = True` | `ProbeLangFull.Adequate .NotStuck (.val .errorVal) () (fun _ _ => True)` holds because every value is `NotStuck` |
| `value_error_in_forked_thread_masks_ub_under_standard_adequacy` | `.forkValueError` (steps main thread to `.val (.okVal 0)` and spawns child `.val .errorVal`) under strict main-thread `φ v _ := v ≠ .errorVal` | `ProbeLangFull.Adequate .NotStuck .forkValueError () (fun v _ => v ≠ .errorVal)` **holds**, because `Adequate` checks `φ` only on thread `0` and checks only `NotStuck` on child threads! |
| `strong_adequacy_rejects_value_error_in_forked_thread` | `.forkValueError` under `StrongAdequate` with `forkPost v _ := v ≠ .errorVal` | `¬ ProbeLangFull.StrongAdequate .NotStuck .forkValueError () (fun v _ => v ≠ .errorVal) (fun v _ => v ≠ .errorVal)` |
| `stutter_error_masks_ub_for_all_postconditions` | `.stutterError` (`toVal = none`, self-loop `primStep .stutterError () [] .stutterError () []`) | `∀ φ, ProbeLangFull.Adequate .NotStuck .stutterError () φ` holds (even for `φ = False`), completely masking UB |
| `choose_error_unpruned_not_adequate` vs. `choose_error_pruned_adequate` | `.chooseError` stepping nondeterministically to `.val (.okVal 0)` or `.stuckError` (`ProbeLangFull`) vs. pruned `ProbeLangPruned` omitting `.stuckError` | `¬ ProbeLangFull.Adequate .NotStuck .chooseError () (fun _ _ => True)`, whereas `ProbeLangPruned.Adequate .NotStuck .chooseError () (fun v _ => v = .okVal 0)` **holds** |

### 3. Upstream MiniRust (`d821c6e`) and `specr` (`15200eb`) Technical Audit

- **Basis:** `source` and `documentation` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`
  and `minirust/specr@15200eb5e6`).

#### 3.1 Architectural Separation in Upstream MiniRust

Upstream MiniRust is structured around four modular boundaries:

1. **Pluggable Untyped Memory Interface (`lang/mem.md`, `mem/interface.md`, `mem/basic.md`, `mem/tree_borrows/`):**
   The operational machine interacts with memory exclusively through an untyped
   `Memory` trait (`allocate`, `deallocate`, `load`, `store`, `dereference`,
   `retag_ptr`, `new_call`, `end_call`, `expose`, `predict`). Both `BasicMemory`
   and `TreeBorrowsMemory` implement this trait over `AbstractByte<Provenance>`
   (`Uninit` or `Init(u8, Option<Provenance>)`).
2. **Typed Representation vs. Byte Serialization (`lang/values.md`, `lang/representation.md`):**
   High-level mathematical values (`Int`, `Bool`, `Ptr`, `Tuple`, `Variant`,
   `Union`) are separated from byte-level memory via explicit `encode` and
   `decode` partial functions on `Type`.
3. **Provenance Exposure and Angelic Prediction (`mem/basic.md`, `lang/operator.md`):**
   Pointer-to-integer casts call `mem.expose(prov)`, while integer-to-pointer
   casts (`Transmute` / `int2ptr`) use angelic nondeterminism `mem.predict(addr)`
   via `pick` over previously exposed provenances.
4. **Explicit Unwind Control Flow (`lang/step.md`):**
   Stack frames track an explicit `unwinding: bool` mode alongside `StartUnwind`,
   `ResumeUnwind`, and `Cleanup` basic-block actions.

#### 3.2 Concrete Upstream Limitations for Formal Verification

| Subsystem | Upstream File / Issue | Technical Limitation |
|---|---|---|
| Specr-lang transpiler & angelic `pick` | `minirust/specr@15200eb5e6`, `libspecr/src/nondet.rs` | `specr-transpile` emits only executable Rust (`libspecr`), with no Lean 4, Rocq, or Isabelle backend. In `libspecr`, universal angelic choice `pick` retries random sampling up to 50 times before panicking, and `predict` panics as unimplemented. |
| Type well-formedness (`minirust#288`) | `lang/well-formed.md` (`Type::check_wf`) | `Type::check_wf` checks `size.in_bounds( Unsigned, dl )` on `Type::Union` and `Type::Enum`, but omits: (a) recursive `check_wf` on `Union` chunk types, (b) verification that an `Enum` `Tagger` actually writes bytes read by its `Discriminator` and that `Discriminator` returns only valid variant indices, and (c) protection against wide-pointer truncation when a `Union` size is smaller than a constituent field type (`size < ty.size(dl)`). |
| Non-pointer load provenance stripping | `lang/representation.md` (`decode_ptr`) | Provenance is preserved only when decoding `Type::Ptr`; loading pointer bytes through an integer or byte array type (`[u8; 8]` or `u64`) discards provenance (`AbstractByte::data`), turning byte-wise `memcpy` via integer loads/stores into provenance-stripping operations unless `Intrinsic::Copy` or `Union` chunk preservation is used. |
| Concrete target layouts | `lang/syntax.md` | `Type::Tuple`, `Union`, `Enum`, and `Array` bake concrete `Size`, `Offset`, and `Align` values into the syntax tree rather than parameterizing over symbolic Rust generics or layout constraints. |
| Concurrency wrapper | `mem/concurrent.md` (`ConcurrentMemory`) | Models SC/acquire/release/relaxed accesses and locks via a single-step race detector `find_race` that clears `prev_atomic_accesses` at the next machine step (`step()`); multi-step inter-action race windows are marked in upstream source as an unimplemented placeholder. |
| `minimize` translator coverage | `tooling/minimize/` | Compiles `rustc` MIR into concrete MiniRust ASTs for testing, but omits `Goto` cycles in several lowering passes, drops unwind edges on `TerminatorKind::Drop` (`todo` fallback if `unwind` is `Some`), and monomorphizes all generics prior to emission. |

### 4. Comparative Survey of MiniRust and Related Rust Operational Formalizations

- **Basis:** `documentation` and `source` (surveyed across Lean 4 and Rocq/Coq
  mechanizations through 2026).

| Project / Artifact | Prover & Logic | Scope of Mechanization | Relationship to Upstream MiniRust (`d821c6e`) |
|---|---|---|---|
| **1. `memoryleak47/coq-minirust` (2023)** | Coq (plain inductive/functional definitions, no Iris) | Early partial transcription of scalar MiniRust syntax, `BasicMemory`, and `Int`/`Bool`/`Tuple`/`Array`/`Ptr` values. | Frozen at a 2023 pre-`Enum`/`Union` MiniRust revision; omits `TreeBorrowsMemory`, `ConcurrentMemory`, unwinding, and separation logic. |
| **2. Viktor Fukala ETH Master's Thesis (2024)** (*Formalizing MiniRust in Coq*) | Rocq (Coq) | Mechanizes a sequential fragment of MiniRust (`BasicMemory`, flat allocations, basic statements/terminators, and type well-formedness) and proves type-safety/progress lemmas for the fragment. | Omits `TreeBorrowsMemory`, concurrency, unwinding, intrinsics, and Iris program-logic integration; identifies manual translation friction from Specr-lang. |
| **3. Tree Borrows PLDI 2025 Mechanization** (Villani, Hostert, Jung, Dreyer) | Rocq + Simuliris | Mechanizes the Tree Borrows aliasing state machine and proves contextual refinement of borrow-based optimizations over $\lambda_{\text{TB}}$ (a calculus with trees, tags, and capabilities). | Formalizes the aliasing model in isolation over $\lambda_{\text{TB}}$, not MiniRust's full MIR-like control flow, `Value`/`Type` representation layer, or `specr` surface. |
| **4. RefinedRust / Radium / Caesium (Gäher et al., PLDI 2024–2026)** | Rocq + Iris + Lithium | Full refinement-type verification pipeline from `rustc` MIR to **Radium** (a bespoke MIR-like intermediate language) and **Caesium** (a low-level C/byte-memory calculus), backed by Iris adequacy in Rocq. | Uses Radium/Caesium rather than MiniRust; demonstrates that production Iris-based Rust verification substitutes a purpose-built prover-native IR for Specr-lang. |
| **5. `iris-itree` (POPL 2025 / ETH 2026)** | Rocq + Iris + Interaction Trees | Modularizes operational semantics as composable `itree` effect handlers (`ubE`, `memE`, `stepE`, `concE`) with a generic Iris program logic and adequacy theorem over interpreted trees. | Architectural template for composing memory and UB effects without monolithic `Language` transitions; not instantiated with full MiniRust. |
| **6. `prusti/pcg-docs` (ETH, 2025–2026)** | Lean 4 | Formalizes Place Capability Graphs (PCG) for Rust borrow-checker analysis in Lean 4. | Targets static borrow-checker capability graphs rather than MiniRust operational semantics or dynamic memory models. |
| **7. Standalone Lean 4 Operational Fragments** | Lean 4 (`v4.34.1`) | Self-contained Lean 4 encodings of finite `.amir` byte-wire formats, bounded frame/slot execution, and Tree Borrows / `iris-lean` interface bridges. | Designed for bounded kernel reduction under strict memory ceilings (`-j1 -M768`); not a line-by-line transcription of upstream Specr-lang. |

## Boundaries

- **Not examined:**
  - Full Lake compilation of the 183-module `iris-lean@81bc350` repository under
    its upstream `leanprover/lean4:v4.29.0` toolchain (our execution evidence
    re-validates the standalone operational `Language`/`NSteps`/`Adequate` bridge
    directly in `leanprover/lean4:v4.34.1` under `-j1 -M768` and audits the
    8 authenticated official Git blobs + 183-module import graph).
  - Weak-memory axiomatic models (such as C++20/RC11) beyond MiniRust's
    interleaved `ConcurrentMemory` wrapper.
- **Unknown:**
  - Whether `minirust/specr` will add a theorem-prover backend (e.g., Lean 4 or
    Rocq output) in future upstream revisions.
- **Known not to apply:**
  - `iris-lean`'s `adequate .NotStuck` does **not** imply operational `NoUB` if
    UB is encoded as a terminal value (`toVal e = some _`) under a permissive
    postcondition, or in a forked thread without `wp_strong_adequacy_gen`'s
    `forkPost`, or as a stutter-reducible state (`reducible e σ`), or if
    nondeterministic UB branches are pruned from `primStep`.
  - Upstream `Type::check_wf` in `minirust@d821c6e` does **not** guarantee
    `Enum` `Tagger`/`Discriminator` round-trip coherence or absence of wide-pointer
    `Union` truncation (`minirust#288`).
- **Unsupported:**
  - Angelic pointer provenance prediction (`mem.predict`) is unsupported in
    upstream `libspecr` execution (`todo` panic at runtime).

## Evidence

| File | SHA-256 | Role |
|---|---|---|
| [`support/authenticated-selected-identities.json`](support/authenticated-selected-identities.json) | `055563d93c388f9612d8fec1cf16b9b09695e84c284a243b15c99803076c2b89` | Authenticated Git commit, tree, and blob SHA-256/OID manifest for 8 core files in `leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c` |
| [`support/independent-import-graph.json`](support/independent-import-graph.json) | `a64508dee010d8ec666473031807f02f73970678981afb6ab9e9d94195c3605c` | Complete 183-module (`2,686,371`-byte) dependency graph and transitive closure audit of `iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c` |
| [`support/iris_notstuck_adequacy_and_ub_encoding.lean`](support/iris_notstuck_adequacy_and_ub_encoding.lean) | `d14b7aa201d34d0fe73cdb88a305c4f1b4bc30dc0039fdc81fc82e17fbe12806` | Standalone Lean 4.34.1 mechanization of `iris-lean`'s `Language`, `NSteps`, `Adequate`, `StrongAdequate`, the `WellEncodedUB` ↔ `NoReachableUB` equivalence theorem, safe `loop` adequacy, and the 3 UB-encoding counterexamples (`valueError`, `stutterError`, `chooseError`) |
| [`support/iris_notstuck_adequacy_and_ub_encoding.eval.json`](support/iris_notstuck_adequacy_and_ub_encoding.eval.json) | `73f557eba8ad28c7db244a9e546383c58a6b831204a57377249f0aff26188637` | Fresh Lean 4.34.1 (`-j1 -M768`) execution record (`returncode: 0`, `0.890s`, `521,632 KB` max RSS) |

## Revalidation

To re-validate the Lean 4.34.1 mechanization of the `iris-lean@81bc350`
`NotStuck` adequacy bridge and all counterexamples under `-j1 -M768`:

```bash
lean +leanprover/lean4:v4.34.1 -j1 -M768 \
  reports/iris-lean-81bc350-notstuck-adequacy-and-minirust-formalization-survey/support/iris_notstuck_adequacy_and_ub_encoding.lean
```

To verify the `iris-lean@81bc350` 183-module import graph and 88-module
`Iris.ProgramLogic.Adequacy` closure from the preserved graph artifact:

```bash
python3 - <<'PY'
import json
from pathlib import Path

pkg = Path("reports/iris-lean-81bc350-notstuck-adequacy-and-minirust-formalization-survey/support")
ident = json.loads((pkg / "authenticated-selected-identities.json").read_text())
graph = json.loads((pkg / "independent-import-graph.json").read_text())

assert ident["commit"] == "81bc35088ba67d465db008f5261a9b341eb6cf6c"
assert len(ident["selected"]) == 8
assert graph["summary"]["lean_file_count"] == 183
assert graph["summary"]["total_bytes"] == 2686371
assert graph["summary"]["cycle_count"] == 0
assert graph["target_closures"]["Iris.ProgramLogic.Adequacy"]["module_count"] == 88
print("Verified iris-lean@81bc350 blob manifest and 183-module import graph.")
PY
```
