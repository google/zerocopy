<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Aeneas verification in CI

The `aeneas` job in `.github/workflows/ci.yml` compiles the current zerocopy
library with Charon, translates selected helpers to Lean with Aeneas, compares
the live output with goldens rendered from inline Rust comments, and
independently builds the inline proofs and checks their transitive axiom
dependencies against both models.
The existing required `All checks succeeded (ci.yml)` job depends on it.

## Scope and proofs

Extraction starts from these actual functions in `zerocopy/src/util/mod.rs`,
including their dependencies; there is no copied Rust implementation:

| Rust function | Checked property |
| --- | --- |
| `max` | Terminates successfully and returns the mathematical maximum. |
| `min` | Terminates successfully and returns the mathematical minimum. |
| `padding_needed_for` | For any positive alignment, succeeds with padding strictly below that alignment. |
| `round_down_to_next_multiple_of_alignment` | For any positive power-of-two alignment, succeeds with a result no larger than the input and divisible by the alignment. |

The theorems quantify over all values of the extracted unsigned integer model;
these are not finite collections of test inputs. Aeneas's Hoare specification
notation includes successful termination, rather than only a postcondition
conditional on success. The min/max proofs explicitly exhibit the result before
converting it to the same total specification.

CI uses the default features, debug assertions, and the runner's native
`x86_64-unknown-linux-gnu` target. Local replay also supports macOS arm64. This
initial scope does not prove minimum padding, maximality of rounded results,
all `DstLayout` operations, other feature/target combinations, or zerocopy's
memory safety. Aeneas currently targets a safe Rust subset; compiling the whole
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
are limited to modules imported by the backend and their dependencies.

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

## Inline annotations and complete accounting

Each annotated function starts with an ordinary Rust line-comment fence. The
opening comment must literally be the first non-whitespace token after the
function body's `{`; preceding comments, attributes, or statements are errors.
The following is schematic; actual annotations contain complete declarations:

````rust
fn example() {
    // ```aeneas
    // model:
    //   def util.example ... := ...
    // proof:
    //   contract example_spec ...
    //     for example ...
    //     requires h : ...
    //     ensures r => ...
    //     proof:
    //       ...
    // ```
    ...
}
````

Only `model:` followed by `proof:` is supported. Each section contains one
complete Lean declaration, indented by two spaces after the `// ` prefix.
Extraction removes exactly that prefix and section indentation, preserving
Lean's remaining indentation. Consecutive ordinary line comments are required;
doc comments, block comments, missing fences, extra sections, and extra
top-level Lean declarations are rejected.

The proof declaration may be an ordinary `theorem` or the experimental
`contract` command from `lean/Contracts.lean`. For example, one of the macro tests
uses this syntax:

```lean
contract identity_spec (x : Nat)
  for Result.ok x
  ensures ret => ret = x
  proof:
    exact WP.spec.ret rfl
```

The command expands to an ordinary theorem whose named requirements are
proposition-valued parameters and whose conclusion is Aeneas's `WP.spec`.
Under those requirements, the function must return successfully and satisfy
the postcondition. Panic and divergence both fail the contract, even when the
postcondition is `True`. Requirements are optional; omitting them adds no
preconditions. Multiple requirements all apply, in their written order.
Output binders reuse Aeneas's notation, including tuple patterns and multiple
binders for return values and mutable post-states. Argument binders and the
function application remain explicit; this prototype does not infer Rust
signatures, inject type invariants, or introduce separate proof automation.

An explicit `partial contract` instead expands to `WP.dspec`. It permits
divergence, rejects panic and other failures, and requires the postcondition
for successful returns. All registered contracts use the total form.
`Obligations.lean` retains their independently written required propositions.

Both workspaces build `ContractTests.lean`, which checks independently written
theorem types, named requirements, omitted requirements, tuple outputs, and
partial contracts. The axiom audit covers these tests and the contract module.
Failure controls also compile contracts that attempt to accept panic,
divergence in the total form, or an incorrect return in the partial form, and
require proof failures. This is a test-bed syntax experiment, not a commitment
to Anneal's eventual annotation language.

The four inline proofs use this syntax without changing their previous
preconditions or postconditions. Padding still requires only a positive
alignment; round-down retains both positivity and the power-of-two requirement.
The old explicit min/max result proofs are reused through
`WP.exists_imp_spec`; required-type checks use the converse equivalence to
compare them with the independently written successful-result requirements.

`inventory.json` independently registers each function's Rust identity, source
file, parsed function identity, Lean definition, theorem, and golden filename.
Removing or mistyping an existing annotation fails because its inventory entry
still requires it. Discovery searches repository Rust files regardless of
`cfg`, excluding only `.git`, `target`, `vendor`, and `.lake` directories. It
recognizes suspicious fence guards, including case variants and close spelling
errors, then requires exact syntax. A Rust lexer distinguishes comments from
string contents; `syn` resolves function braces and inline modules before
conditional compilation. An unknown annotation is an error, not an opt-in
that CI can overlook.

Initial support covers free functions in conventional `zerocopy/src` module
paths. Methods, nested functions, macros, and custom module-path layouts need
explicit tooling support; an annotation in an unsupported position fails.
Every registered root must be extracted in the current CI configuration.
Charon's root identities, local source contents, file paths, and function-body
end spans must match the annotations. This prevents a same-named `cfg`
alternative or a stale extraction from standing in for the annotated body.

Each annotation has exactly one function template in `golden/`, and every file
there must correspond to one registered annotation. That file contains one
`@@AENEAS_MODEL("rust::identity")@@` slot. `scaffolding/` separately retains the
generated types, external templates, trait dictionaries, and module structure;
each function slot appears there exactly once as
`@@AENEAS_GOLDEN("function.lean.in")@@`. Unknown, missing, repeated, or
unexpanded slots fail. `target/aeneas/rendered-golden` holds the assembled model
used for comparison. These invalid-Lean slots are expanded before compilation
and never interpreted as ordinary comments.

Proof bodies live only in the Rust annotations. `lean/Proofs.lean.in` supplies
their shared imports and abbreviation. `lean/Obligations.lean` independently
records the required propositions; generated `Required.lean` checks each inline
theorem against its required type. A theorem of `True` with the correct name
cannot substitute for a required property. Removing coverage requires explicit
changes to the inventory, golden slots, scaffolding, and required propositions.
The claims remain the properties listed above, not complete verification of a
function's documentation or all compilation configurations.

No parser can recognize every informal prose claim as a proof. The `aeneas`
fence is the reserved, CI-checked convention; other explanatory comments do not
claim this status. Near-miss guard detection and the independent inventory
protect that convention without treating all mathematical prose as annotations.

## Updating models and fuzzy comparison

Never edit an inline generated model or shared extraction scaffolding manually.
Regenerate them with:

```bash
bash verification/aeneas/run.sh --update-goldens
```

This command performs a fresh extraction and checks the existing inline proofs
and required propositions against the live output before updating anything.
It then updates only the `model:` sections of Rust comments, function golden
slots, and shared scaffolding; proof text and executable Rust are preserved.
Finally it checks comparison and both model builds. Review and commit all
changed source comments and scaffolding alongside the Rust or pin changes that
prompted them. Ordinary CI never updates checked-in files.

To add coverage, first add the fenced model/proof, inventory entry, and required
proposition. The update command creates the missing function golden only after
the live proof succeeds. Ordinary CI always requires the complete bijection.
The pinned generator's root declaration layout is deliberately checked during
updates; an incompatible layout requires an explicit tooling change.

The fuzzy comparison ignores line and nested block comments (including source
locations), empty nonliteral lines, and trailing horizontal whitespace outside
literals. It preserves code, indentation, nonempty line boundaries, interior
whitespace, and string/character/quoted-identifier contents. Unsupported raw or
interpolated strings and malformed comments/literals fail closed. This is a
limited comparison for the pinned generator's syntax, not a general Lean
parser, alpha-equivalence checker, or semantic equivalence proof. Missing or
additional generated files, changes to external-template signatures, and code
changes fail with a normalized diff and require regeneration.

After comparison succeeds, CI compiles the checked-in model and the unmodified
live model in separate fresh Lake workspaces. Both must prove the same four
properties and pass the required-type checks and axiom audit; neither imports
the other's compiled model. The live functions always come from Aeneas. Inline
definitions are inserted only into the checked-in model, never into live output.
The normalized text is only used for comparison, never for proof compilation.
This independently checks that accepted differences preserve the properties we
prove. Those properties do not fully specify every helper, so passing both
builds does not by itself establish full semantic equivalence. Keep accepted
fuzziness narrow; stronger equivalence claims require additional theorems.

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
  bitwise, and assertion models represent those Rust operations faithfully.
- The handwritten `NonZero` wrapper represents its stored value;
  `NonZero::get` succeeds with that value and `NonZeroUsizeInner::clone`
  succeeds with a copy. These models abstract values, not niche encoding,
  layout, validity, or memory operations. The wrapper over-approximates valid
  Rust values by admitting zero; the alignment proofs explicitly require
  positivity rather than assuming it through an axiom.
- Lean's kernel, its standard logic axioms, and the imported proof artifacts
  check the encoded propositions correctly. Release checksums establish
  artifact identity, not a proof of compiler or model correctness.

`Check.lean` checks that required declarations are theorems and audits all
declarations in `Zerocopy.Proofs`, `Zerocopy.Obligations`, the translated
`Zerocopy.util` namespace, the external `core.num` models, and the contract macro
and test namespaces. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. New axioms, `sorryAx`, and
native evaluator proof
axioms fail this check. This does not establish the source-to-model
correspondence premises.
CI also runs failure controls in both workspaces: impossible total and partial
contracts must fail their proofs, an admitted proof must fail
the axiom audit, an unrelated `True` theorem must fail its required type, and
reversing the translated `min` comparison must fail its proof. In the live
workspace, comment drift must pass fuzzy comparison and
proof checking, while reversing `min` must also fail comparison. These controls
edit scratch files and restore them before rechecking the original results.

Extraction rejects warnings, translation errors, missing artifacts, and LLBC
whose `has_errors` is not exactly `false`, even when Charon exits zero.
`prepare.py` also repairs one pinned Aeneas naming collision:
`ZeroablePrimitive` has two `Copy` parent dictionaries, which Aeneas names
`markerCopyInst`. The second projection and its initializer are renamed
`innerCopyInst`. Both dictionary types and values are preserved, and no helper
body is changed. Each replacement must match exactly once; unexpected output
fails rather than silently applying a broader rewrite.

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
