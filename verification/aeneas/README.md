<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas verification in CI

The `aeneas` job in `.github/workflows/ci.yml` compiles selected zerocopy functions
with Charon and Aeneas, compares complete generated Lean goldens, and proves
the inline Rust specifications against both the checked-in and live models.
The required `All checks succeeded (ci.yml)` job depends on it.

## Scope and proofs

Extraction starts from the arithmetic helpers in `zerocopy/src/util/mod.rs`
and alignment/phase encoding methods in `zerocopy/src/layout.rs`, including
their dependencies:

| Rust function | Checked property |
| --- | --- |
| `max` | Returns the mathematical maximum, selects an input, and bounds both inputs from above. |
| `min` | Returns the mathematical minimum, selects an input, and bounds both inputs from below. |
| `padding_needed_for` | For power-of-two alignment, returns padding below it and exactly `(align - len % align) % align`, the least padding making the sum aligned, with zero padding exactly when the input is aligned. |
| `round_down_to_next_multiple_of_alignment` | For power-of-two alignment, returns exactly `n - n % align`, the greatest aligned value at most `n`; the next multiple exceeds `n`. |
| Alignment/phase encoder and decoders | Power-of-two alignment, bounded phase, and exact encoding round-trip. |

The theorems quantify over all values of the extracted unsigned integer model;
these are not finite collections of test inputs. All seven inline specifications
use `contract`, whose Aeneas Hoare specification includes successful termination,
rather than only a postcondition conditional on success.

`lean/Corollaries.lean` composes the inline theorems: min/max preserve any
predicate shared by both inputs; round-down is monotone, is the identity on
aligned inputs, and is idempotent. The idempotence contract proves both
calls succeed, including that the first result meets the second call's needs.

Comparisons use the unsigned scalar's existing order directly (`m ≤ n`,
`p < align.val`, `min a.val b.val`). Arithmetic postconditions explicitly bind
`Nat` values (`let N : Nat := n`) so addition and remainder are unbounded
mathematical operations. The corresponding Rust scalar arithmetic operators
return checked `Result` values and are not interchangeable with these formulas.
`NonZero` still needs one `.val` to unwrap its stored scalar. Power-of-two
requirements already imply positivity, so padding and round-down contracts do
not repeat a positive-alignment requirement.

CI uses the default features, debug assertions, and the runner's native
`x86_64-unknown-linux-gnu` target. Local replay also supports macOS arm64. This
scope does not prove all `DstLayout` operations, other feature/target
combinations, or zerocopy's memory safety. Aeneas currently targets a safe Rust subset; compiling the whole
unsafe crate to a complete verified model is a separate task.

## Reproduce

Install `rustup`, Python 3.9+, Git, curl, tar, and zstd, then run from the repository
root:

```bash
bash verification/aeneas/setup.sh
bash verification/aeneas/run.sh
bash verification/aeneas/negative-controls.sh
python3 -B -m unittest discover -s verification/aeneas/tests
```

The runner builds `tools/aeneas-inline` with the pinned compiler. To run that
tool's own tests, use:

```bash
source verification/aeneas/toolchain.sh
CARGO_TARGET_DIR=target/aeneas/annotation-tool \
  cargo +"$AENEAS_RUST_TOOLCHAIN" test --locked \
  --manifest-path tools/Cargo.toml -p aeneas-inline
```

`setup.sh` downloads SHA-256-checked release archives and installs the matching
Rust compiler with `rustc-dev` and `rust-src`. It fetches the pinned Lean
backend's Mathlib dependencies using its supplied lockfile. Cache downloads
are limited to imports of the backend and handwritten proof modules,
together with their dependencies.

The resulting tools live in ignored `target/aeneas/toolchain`. To reuse an
existing installation with the same bundle layout, set `AENEAS_TOOLCHAIN_DIR`.
`run.sh` checks tool versions before extraction. It runs Charon with
`--preset=aeneas --sysroot default`, using Aeneas's builtin models for standard
library operations instead of regenerating a sysroot. Cargo resolves the
library's dependencies from its checked-in vendor configuration, offline and
locked. Charon is a compiler driver and selects its own Rust version; it does
not use zerocopy's ordinary Cargo wrapper or its stable/nightly aliases.

Every run replaces `target/aeneas/verification` (live extraction) and
`target/aeneas/golden-verification` (checked-in model), including their compiled
Lean artifacts. This prevents stale declarations or the other model's artifacts
from passing after source is removed or renamed. Both retain Lean sources,
handwritten models/proofs, and resolved Lake manifests for inspection; the live
directory also retains LLBC. External templates are compared but never imported
into proofs as axioms.

## Inline specifications and coverage

Each annotated function starts with an ordinary Rust line-comment fence. The
opening comment must be the first non-whitespace token after the function body's
`{`. Consecutive ordinary line comments are required; malformed or misspelled
fences, unsupported owners, duplicate annotations, extra declarations, and
unaccounted annotations fail.

````rust
fn example(input: usize) -> usize {
    // ```aeneas
    // spec example_spec (input : Usize)
    //   requires h : valid input
    //   ensures result => correct input result
    // ```
    ...
}
````

A fence contains exactly one `spec` declaration. It contains argument binders,
optional named `requires` clauses, and an `ensures` postcondition. The total
specification requires successful termination under its stated requirements;
panic and divergence do not satisfy even the postcondition `True`. An explicit
`partial spec` permits divergence and still excludes panic. A mathematical
`refines` clause can describe the result through a view.

The tooling derives the function application from the enclosing Rust function
and the extracted model. Rust type parameters and ordinary parameters must be
the named prefix of the specification's binders in their original order;
additional mathematical arguments may follow them. The receiver is named
`self`. This correspondence is checked, including parameters with identical
types, so swapping two binders cannot silently specify another application.
The application is fully qualified and cannot be supplied or overridden in the
comment. Charon's root identity, exact source body, source path, and signature
must match the annotation, including inherent Self types and inactive `cfg`
alternatives.

`inventory.json` is an independently maintained coverage policy. Its
`required_functions` requires named functions and its `covered_impls` closes
pre-cfg source coverage over inherent methods of supported, directly named Self
types, including inactive `cfg` definitions. It inspects all crate sources and
rejects direct macros inside covered impls, including inactive macros, and
unsupported or out-of-file impls with the same Self-type basename.

This pre-cfg closure uses source-level Self names. Inactive impls through type
aliases or generated by global macros are outside that closure.
Visible annotations are always discovered; extraction independently checks
active aliased and generated methods.

Charon's `Type::_` wildcard independently selects the covered type's actual
active inherent methods, including generated or aliased methods wherever they
were defined. Every started-from method must match the exact annotated roster.
Associated-constant initializers are compiled and audited as model definitions;
they do not require separate function specifications.

Deleting a comment does not delete its requirement. Model
names, theorem identities, filenames, and dependency edges are derived rather
than stored as additional synchronized inventory fields. Discovery scans all
repository Rust sources except generated and vendored directories. A Rust
lexer distinguishes comments from strings and `syn` establishes ownership
before conditional compilation.

No parser can recognize every informal prose claim as a proof. The `aeneas`
fence is the reserved CI-checked convention. Near-miss guard detection and the
independent policy protect that convention without treating all mathematical
prose as annotations.

## Native Lean proofs and independent checks

`Specs.lean` is generated from the Rust comments in a fixed context containing
the extracted model and mathematical vocabulary. Each `Zerocopy.Specs.*` is a
transparent proposition. The module is elaborated before proof modules are
imported, so proof declarations cannot change what the comment means.

Handwritten proofs are ordinary checked-in `.lean` modules. Their theorem types
refer directly to generated propositions rather than restating them:

```lean
theorem example_spec : Zerocopy.Specs.example_spec := by
  intro input h
  ...
```

Changing the Rust specification changes this theorem's goal. An old proof is
accepted only when Lean still establishes that goal. Normal imports and Lean
declaration order assemble proofs. There are no proof templates, insertion
slots, or hand-maintained dependency lists.

Each annotation requires its canonical exported proof and an independent
proposition in `Obligations.lean`. Missing canonical proofs, stale `Specs`
references, duplicate declarations, and unrelated required theorem types fail.
Additional helper theorems are allowed in the configured proof modules. The
required checks establish independently authored
propositions from the supplied theorems and preserve their conversion proof
terms for audit. The independent expectations are not generated from the inline
specifications. They protect against an incorrect specification expansion as
well as weak or incorrectly named proof declarations.

`Check.lean` derives dependencies from elaborated theorem types and terms,
following helpers across handwritten modules, including private helpers, and
writes `proof-dependencies.json` in each proof workspace. It imports and audits all
declarations from every handwritten Lean module, including unused auxiliary
modules, together with the model, vocabulary, obligations, and generated
specifications. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted.
New axioms, `sorryAx`, and native evaluator proof axioms fail.

Callers reuse ordinary exported theorems, either explicitly with `step with` or
through Aeneas's existing `step` registration. For a theorem whose type is a
transparent `Specs` proposition, `register_spec_step theorem_name` supplies a
kernel-checked alias with the expanded type for that registry. The canonical
theorem keeps its ordinary `Specs` type. Golden caller proofs use golden
callee theorems; live caller proofs use live callee theorems. Both models are
built in separate fresh workspaces from the same handwritten source, never
from shared compiled proofs or substituted model definitions. Handwritten
modules must not create import cycles through generated `Required` or `Check`.

## Development

Run `bash verification/aeneas/dev.sh` to prepare the stable development project from the
checked-in golden model. Add `--live` to freshly extract the Rust implementation
and use that model instead. This extraction mode prepares editable goals even
when proofs are unfinished; it does not claim that golden comparison or proof
checks have passed. Add `--check` to build the development project and audit its
proofs.

The project keeps handwritten proof modules at their checked-in paths and
generates the selected model and `Specs.lean` for native Lean editing.
Incremental Lake builds reuse
that project's compiled dependencies. The generated source map connects
specification diagnostics to the Rust comments; proof diagnostics already point
to their checked-in Lean source.

Edit a specification in Rust and run the development command again to refresh
its generated proposition. Edit its proof directly in Lean. No proof copying
back to Rust is required. This development cache is for iteration; CI always
regenerates specifications and builds both models in fresh isolated projects.

## Mathematical views and indexed loops

### Arithmetic, mathematical views, and indexed loops

Checked addition, subtraction, and multiplication already have upstream
`step_pure` specifications. Use `step as ⟨result, facts⟩` and split the `Option`
result to obtain both the exact successful value and the overflow condition.
`SupportTests.lean` exercises all inputs, including overflow.

A contract may express equality through a pure mathematical view:

```lean
contract operation_spec (input : Input)
  for operation input
  requires h : valid input
  refines view to mathematicalOperation (view input)
  ensures result => canonical result
  proof:
    ...
```

This expands to the existing total WP postcondition
`view result = mathematicalOperation (view input) ∧ canonical result`.
Omitting `ensures` leaves just the view equality. `partial contract` also
supports this syntax and retains the explicit permission to diverge. View
contracts introduce no new axioms or semantics. Use `WP.spec_mono` to adapt an
existing result specification to a view contract, and register useful caller
specifications with `attribute [step] operation_spec`. The existing Aeneas
registry then lets callers use `step` without specifying the theorem manually.

`AeneasContracts.indexed_loop_spec` specializes Aeneas's `loop.spec_decr_nat`
to a state and `Usize` index. Supply a view, the mathematical value of each
prefix, and a representation invariant. Each continuing body step must advance
the index by exactly one and establish the next prefix; a completed step must
be at the length. The adapter supplies bounds and the decreasing `length - index`
termination measure. `SupportTests.lean` contains an independent example.

The contract support, examples, and required-contract proof terms
participate in the axiom audit. Failure controls challenge an incorrect view,
divergence under a total view contract, a stationary loop index, an incorrect
prefix step, and continuing past the loop bound.

## Updating models and fuzzy comparison

`golden/` stores all four complete generated Aeneas modules, including types,
function bodies, trait dictionaries, constants, and external templates. There
are no per-function model slots or separate scaffolding. Handwritten external
models remain under `lean/Zerocopy/` and templates are never imported as axioms.

Regenerate the checked-in output with:

```bash
bash verification/aeneas/run.sh --update-goldens
```

The command extracts live output and checks its proofs and independent required
propositions before updating the complete generated module set. It then checks
comparison and both model builds. Rust comments, handwritten proofs, and
executable Rust are preserved. Review and commit the changed goldens alongside
the Rust or pin changes that prompted them. Ordinary CI never updates them.

To add coverage, add the fenced specification, its ordinary Lean theorem, and an
independent required proposition; update the coverage policy when needed.
Regenerate the complete goldens. Each annotation's model declaration is checked
in the complete generated modules; missing or duplicate declarations fail.

Fuzzy comparison ignores line and nested block comments, including source
locations, empty nonliteral lines, and trailing horizontal whitespace outside
literals. It preserves code, indentation, nonempty line boundaries, interior
whitespace, and string/character/quoted-identifier contents. Unsupported raw or
interpolated strings and malformed comments/literals fail closed. Missing or
additional generated files, changes to external-template signatures, and code
changes fail with a normalized diff and require regeneration.

CI compiles the checked-in model and the unmodified live model in separate fresh
Lake workspaces. Both must prove all inline specifications and composition
corollaries and pass required checks and the complete axiom audit. The normalized
text is used only for comparison, never compilation. This independently checks
that accepted differences preserve the proved properties; it does not by itself
prove full semantic equivalence beyond those properties.

## Pins and upgrade procedure

The selected release is
[`nightly-2026.10.01-ca282ec`](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.10.01-ca282ec).
`toolchain.sh` records its full Aeneas commit, the compatible Charon commit from
[`charon-pin`](https://github.com/AeneasVerif/aeneas/blob/ca282ec2312a96f6a985a4d23a663690816d3f3e/charon-pin),
Rust `nightly-2026-09-17`, Lean `4.31.0`, and platform archive digests. The release
supplies prebuilt Aeneas/Charon binaries and compiled Lean backend artifacts.
Its `lake-manifest.json` pins Mathlib and transitive dependencies; the generated
proof workspace shares those fetched dependencies through path entries instead
of resolving a second copy.

Upgrade this tuple together. Verify archive digests, resolve the new
`charon-pin`, inspect that Charon revision's Rust toolchain and Aeneas's Lean
version, and run extraction and all proofs from fresh output. Review new
external templates, the generated helper bodies, proof statements, and axiom
results. Remove or adapt the naming workaround only after inspecting the new
output. Do not pair Aeneas with an independently selected Charon nightly.

## Trust boundary and failure checks

These are Lean theorems about generated functions. Transferring them to Rust
requires the following external correspondence premises, which this CI job
records but does not formally prove:

- Rust MIR generation and Charon's LLBC extraction preserve these selected
  functions' semantics for the pinned configuration.
- Aeneas's translation and the pinned integer, comparison, wrapping-subtraction,
  checked-addition, bitwise, and assertion models represent those Rust
  operations faithfully. The translated layout records and variants represent
  their stored fields, not physical Rust layout or niche encoding.
- The handwritten `NonZero` wrapper represents its stored value;
  `NonZero::get` succeeds with that value and `NonZeroUsizeInner::clone`
  succeeds with a copy. These models abstract values, not niche encoding,
  layout, validity, or memory operations. The wrapper over-approximates valid
  Rust values by admitting zero; the alignment proofs establish positivity
  from their explicit power-of-two requirement rather than assuming it through
  an axiom.
- The pointer width is computed from `core.mem.size_of Usize`, modeled as the
  selected word width divided by eight. Other type instantiations remain
  unsupported at this stack position. `NonZero::new` is modeled at `Usize`:
  zero returns `None`, and nonzero inputs return the same bits. The encoder
  also uses the pinned leading-zero-count and wrapping-shift models.
- Lean's kernel, its standard logic axioms, and the imported proof artifacts
  check the encoded propositions correctly. Release checksums establish
  artifact identity, not a proof of compiler or model correctness.

Failure controls challenge missing annotations and proofs, orphaned proofs,
incorrect binding and parameter order, malformed specifications, admitted
proofs, unrelated theorem types, changed generated callees, and comments or
whitespace accepted by fuzzy comparison. Each model must pass the same controls.
Controls edit and restore scratch workspaces, then recheck the original results.

Extraction rejects warnings, translation errors, missing artifacts, and LLBC
whose `has_errors` is not exactly `false`, even when Charon exits zero.
`prepare.py` repairs one pinned Aeneas naming collision: `ZeroablePrimitive` has
two `Copy` parent dictionaries that Aeneas names `markerCopyInst`. The second
projection and initializer are renamed `innerCopyInst`; dictionary types and
values are preserved and no function body changes. Unexpected output fails.

## Research used

The upstream [Aeneas README](https://github.com/AeneasVerif/aeneas) describes the
Charon-to-LLBC-to-Lean pipeline, required compatible pins, external model
workflow, and safe-subset limitations. The repository's `reference` branch
provided useful prior evidence:

- [Compatible bundle drift](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/aeneas-compatible-bundle-source-drift-2026-09-30/REPORT.md)
  identifies the newer Lean module output and the need to resolve Charon from
  Aeneas's pin rather than release dates.
- [External models](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/aeneas-external-models-nightly-2026-06-03/REPORT.md)
  explains the generated templates and the semantic boundary of model
  registrations.
- [Whole-library Charon extraction](https://github.com/google/zerocopy/blob/ba4556c30835b56d108b0a6854a760bccf8438c5/reports/charon-zerocopy-library-repeat-order-nightly-2026-05-31/REPORT.md)
  observed successful process exits with `has_errors: true`, supporting the
  explicit LLBC completeness check.

Those older experiments are not assumed to describe the current release's
runtime. This integration was validated with the pinned October 1 bundle and
fresh translations of the current checkout.
