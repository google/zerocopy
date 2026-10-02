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

Extraction starts from 27 actual functions in `zerocopy/src/layout.rs` and
`zerocopy/src/util/mod.rs`, including their dependencies. The inventory closes
coverage over supported impls that directly name `DstLayout`,
`TrailingSliceLayout`, `SizeInfo`, or `RoundingAlignAndPhase`; adding an
unannotated method to such an impl fails before extraction, including under
inactive `cfg` conditions. Extraction also checks active aliased and generated
methods.

| Functions | Checked property |
| --- | --- |
| `max`, `min`, padding, round-down | Exact extrema, least padding, greatest aligned predecessor, and bounds. |
| Alignment/phase encoder and decoders | Power-of-two alignment, bounded phase, and exact encoding round-trip. |
| Trailing size, padding, capacity, and advancement | Independent unbounded size formulas, exact checked-size overflow, wrapping padding, and byte advancement. |
| Size-sequence comparison | A positive answer establishes equal sizes for every natural metadata value. |
| Zero-stride conversion and element capacity | Exact zero handling, preserved representation fields, and greatest fitting element count. |
| `DstLayout` constructors, extension, and padding | Exact fields, field placement, alignment, flags, and normalized size formulas. The record constructor terminates for arbitrary field lists satisfying the independent construction domain. |
| Static and dynamic padding queries | Exact flag result and the mathematical condition sufficient to eliminate dynamic padding for all metadata values. |
| Cast validation and exact-size metadata | Alignment/size error priority, greatest fitting metadata, exact prefix/suffix split, and rejection of unattainable sizes. |

All registered specifications use total `spec`: accepted input representations
and their stated requirements imply successful termination, a valid returned
value, and their postconditions. Intentional panic for
casting a zero-stride DST is checked separately. The size-sequence comparison
is conservative: a negative result does not claim that the sequences differ.

`LayoutMath.lean` defines an independent recursive layout semantics and proves
normalization correct for every nesting depth and metadata value. The extracted
contracts connect machine arithmetic and control flow to that mathematics.
`LayoutModel.lean` supplies shared interpretation predicates, without using
any function proof. `Corollaries.lean` connects checked sizes and physical
padding to the recursive semantics, proves that outer padding preserves
complete inner sizes, and connects the record constructor to direct
per-metadata field placement.
See [SEMANTICS.md](SEMANTICS.md) for the exact Rust premise and trust boundary.

The constructor's requirements check field alignment, the independent prefix
layout's overflow bounds, canonical encodings, and final padding bounds. These
are predicates over the mathematical construction, not assumptions that the
Rust constructor returned a correct result. Fragment operations have explicit
fit requirements; arbitrary malformed internal layout records need not succeed.
Generic size/alignment reads are explicit external data inputs, never axioms
asserting layout correctness.

Plain arithmetic clauses use mathematical word values carrying machine bounds
and, for NonZero, positivity. They coerce to `Nat` or `Int` without unwrapping
raw fields. Binding `let N : Nat := n` makes addition and remainder ordinary
unbounded mathematics. Explicit `(raw)` clauses retain the extracted scalar
operations, whose checked arithmetic returns execution `Result` values.
Operation-specific power-of-two alignment and overflow bounds remain explicit
requirements.

CI uses the default features, debug assertions, and the runner's native
`x86_64-unknown-linux-gnu` target. Local replay also supports macOS arm64. The
proofs cover all registered layout methods under their stated domains;
they do not certify other extraction configurations, a rustc implementation,
or zerocopy's pointer safety. The explicit Rust premise connects the recursive
semantics to an actual type's layout. Compiler regression tests challenge that
premise independently of the Lean algebra. Aeneas currently targets a safe Rust
subset; whole-crate unsafe verification is a separate task.

## Reproduce

Install Nix, `rustup`, Python 3.9+, Git, curl, tar, and zstd, then run from the repository
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

The local failure-control command checks both models sequentially. To select
one isolated project, pass `golden-verification` or `verification`. CI runs
these two suites concurrently, waits for both, and reports both logs; either
failure fails the job.

`setup.sh` downloads SHA-256-checked release archives, builds the pinned
Aeneas source with the checked-in CLI patch using its locked Nix dependencies,
and installs the matching Rust compiler with `rustc-dev` and `rust-src`. It fetches the pinned Lean
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

Annotations are outer Rust doc attributes before the decorated item. The Rust
parser owns the association, including attributes between docs and the item.
Every reserved fence is accounted for: malformed or misspelled fences, unsupported
owners, duplicate declarations, and orphaned annotations fail. Literal `#[doc]`
attributes are also supported. An owner with a literal Aeneas annotation cannot
also carry computed doc strings. Direct `include_str!` in owner doc expressions
is rejected, including nested, qualified, and conditional invocations. Visible
reserved literal fragments in computed docs are rejected even when split across
strings. Conditional and inner doc forms with reserved fences also fail.
Unannotated computed documentation otherwise retains its ordinary Rust meaning.
Macro-produced documentation is outside the annotation language: the checker
does not expand macros or claim to inspect arbitrary external text they produce.

````rust
/// ```aeneas
/// spec identity_spec
///   ensures result => result = x
/// ```
fn identity<T>(x: T) -> T { x }
````

A function fence contains exactly one `spec` or `partial spec` declaration.
Only explicitly typed ghost binders are authored. The original Rust type
parameters, receiver `self`, and arguments come from the exact extracted
signature. Each original type parameter receives one `RustModel T` dictionary,
including unused and result-only parameters.

Plain clauses expose value arguments as their mathematical models. Raw clauses
expose their original Aeneas representations:

```text
requires      name : proposition
requires(raw) name : proposition
ensures       resultPattern => proposition
ensures(raw)  resultPattern => proposition
```

Every requirement is a named implication premise; later clauses can use its
proof. Requirements precede all postconditions. Every postcondition contributes
a conjunct, and all plain postconditions share one decoded output witness.
Ghost types elaborate in mathematical input scope, so `(position : Fin self.length)`
can depend on a decoded sequence. Ghosts may depend on earlier ghosts. Inputs,
ghosts, and earlier requirement names cannot be shadowed. No ghost is an argument
to the extracted function or is selected after execution.

The proposition retains the original contiguous raw-input telescope. It then
introduces modeling dictionaries, mathematical inputs, decoding equations,
ghosts, and requirements before executing the original extracted function on
its original raw arguments. A successful payload must decode, even when every
postcondition is raw or is `True`. Total specifications require successful
termination and exclude panic and divergence. Explicit `partial spec` permits
divergence while excluding panic and checking every successful return.

A type fence defines one mathematical shape and one local decoder:

````rust
/// ```aeneas
/// model AlignValue where
///   value : Nat
///   power_of_two : value.isPowerOfTwo
/// decode? self =>
///   if h : self.value.value.isPowerOfTwo then
///     some { value := self.value.value, power_of_two := h }
///   else none
/// ```
struct Align { value: NonZeroUsize }
````

The alternative `model Name := ExistingType` associates an existing mathematical
type. `decode self => term` is locally infallible; `decode? self => term` may
reject the decoded fields. Both consume the owner's generated `Fields` carrier.
The full decoder first decodes every field of a structure or the active enum
constructor, including fields ignored by the local decoder. Child rejection
rejects the entire value. There is no independent validity dictionary or predicate.
An unannotated nominal owner's model is its own `Fields` carrier. `model Name := Fields`
uses that same representation under an authored name. Different Rust owners
retain distinct default carriers; aliases inherit their carrier's model.

Native adapters carry exact scalar values and machine bounds, plus positivity
or nonzero proofs for NonZero types. Products, options, Rust results, lists,
slices, and arrays traverse their child providers and preserve their constructors
and lengths. Rust `Option.none` and Rust `Result.Err` are ordinary successfully
decoded cases; Aeneas panic/failure remains a separate execution outcome.
Unsupported opaque leaves, recursive nominal groups, indexed carriers,
trait/const generics, and escaping borrow continuations fail explicitly.
Model shapes also reject forward dictionary dependencies: for example, a field
of type `Box<Child>` needs Child's complete provider when Box's mathematical type
is parameterized by that provider. `Box<T>` works with its supplied generic
provider, and functions over `Box<Child>` work after the providers exist. The
shape phase does not fabricate temporary providers to break this dependency.

Automatic decoding uses directly named native/nominal providers, fixed container
combinators, and the original generic dictionary variables. Providers are selected
before decoded witnesses and ghosts and retained explicitly, so a later ghost
instance cannot redirect admission or output meaning. Ordinary instances remain
available for authored expressions and helper lemmas. No global instance-selection
comparison is part of the automatic-decoding audit.

Generated modules follow the proof-construction dependency:

```text
raw Types + ModelPrelude → ModelShapes → ModelSupport → Models → Specs + Proofs
```

`ModelShapes` declares nominal mathematical fields and inline model types in
verified extraction order. Handwritten `ModelSupport` modules may prove model
fields, but their transitive imports cannot depend on final decoders, specifications,
function proofs, or extracted function bodies. `Models` elaborates local decoders
and composes full decoders and named providers. The generated shapes, decoders,
and specifications all carry Rust source maps. Every handwritten module is
discovered and audited; generated modules are excluded from that discovery.
The compiled audit walks Lean's actual module import graph from every imported
`ModelSupport` module, including nested modules. Resolved module names govern
this check, including imports written with quoted identifiers. Handwritten module
path components must be simple identifiers (`[A-Za-z_][A-Za-z_0-9]*`); literal
dots, whitespace, and quoted components in filenames are rejected so distinct
Lean Name segments cannot be conflated by the file inventory.

These are conditional contracts over accepted representations, supplied ghosts,
and satisfied requirements. A decoder may intentionally forget observations or
reject raw values. A ghost with type `False`, or a dependent ghost with an empty
domain, makes the relevant contract vacuous. Neither the pipeline nor a decoder
proves that every Rust caller meets the domain. `DstLayout` initially keeps a
structural mathematical model, including its unpadded flag and decoded rounding
pair, without imposing a global realizable-layout requirement. Operation-specific
alignment, fit, and construction conditions remain explicit. Independently stated
decoder-domain and representation laws should establish intended acceptance and
meaning; there is no universal decoder-correctness oracle.

The fully qualified model application is generated and cannot be supplied in
Rust. Charon's root identity, exact source body, source path, and signature must
match the annotation, including inherent Self types and inactive `cfg`
alternatives. Discovery retains exact inspected source snapshots; later digest,
binding, and assembly steps reject changes to any inspected input. The source
digest includes unannotated dependency files and the coverage policy. Every
contents-bearing Charon-local file must agree with its inspected snapshot, so an
unchanged caller cannot hide a changed dependency. Pinned external `/rustc` files
without source contents remain within the translation premise.
The elaborated call must pass exactly its original Rust input
variables, with no swapping, coercion, or substitution. Introduced signatures are
inspectable in the generated Lean propositions and native editor.

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

Each function annotation requires its canonical exported proof and an independent
proposition in `Obligations.lean`. Missing canonical proofs, stale `Specs`
references, duplicate declarations, and unrelated required theorem types fail.
Additional helper theorems are allowed in the configured proof modules. The
required checks establish independently authored
propositions from the supplied theorems and preserve their conversion proof
terms for audit. The independent expectations are not generated from the inline
specifications. They protect against an incorrect specification expansion as
well as weak or incorrectly named proof declarations. The audit requires every
independent witness to be a theorem of the expected type declared in the generated
checks module; an omitted conversion cannot silently pass. It derives required
theorems from the compiled specifications, without a separate generated roster.

The audit also compares the existing verified Rust-to-model mapping in
`bindings.json` with the functions actually called by compiled specifications
declared in `Specs`. Every mapped function must have exactly one such
specification; missing, extra, or repeated functions fail. Each specification
in turn requires its canonical theorem and independent required theorem.
The same versioned table records every extracted nominal owner's source,
raw carrier, Fields carrier, mathematical type, decoder, and provider. The compiled
audit checks those identities and their generated-module ownership in both
directions, independently scans raw nominal types, and rejects missing or extra
provider registrations. This reuses one verified table without another coverage roster.

For cast validation and
exact-size metadata, the required outcomes spell out error priority, split
positions, exact size, and greatest-fitting metadata independently of the
predicates used by the inline specs. `OutcomeTests.lean` pins distinguishing
fixed-size, suffix-alignment, and padded-size plateau examples.
`LayoutModelDomainTests.lean` also establishes concrete admitted constructor
inputs and exact views for an ordinary record and a nested packed DST. These
bounded examples guard against vacuous preconditions; they do not establish
that every Rust type meets the construction domain.

`Check.lean` derives dependencies from elaborated theorem types and terms,
following helpers across handwritten modules, including private helpers, and
writes `proof-dependencies.json` in each proof workspace. It imports and audits all
declarations from every handwritten Lean module, including unused auxiliary
modules, together with the model, vocabulary, obligations, and generated
specifications. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted.
The explicit data-only Rust layout inputs documented in `SEMANTICS.md`
are also permitted. Models with generic alignment reads must provide both
data inputs with their exact signatures; the audit also checks that generic
size/alignment reads use those inputs and that `Usize` size uses the pointer
width. These checks pin the declared external interpretation; correspondence
to the actual Rust ABI remains an explicit premise.
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
generates the selected extraction, `ModelShapes.lean`, `Models.lean`, and
`Specs.lean` for native Lean editing.
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
`SupportTests.lean` exercises all inputs, including overflow. Layout proofs use
these registrations directly, without naming bitvector specification lemmas.

A contract may express equality through a pure mathematical view:

```lean
theorem operation_spec (input : Input) (h : valid input) :
    operation input ⦃ result =>
      view result = mathematicalOperation (view input) ∧ canonical result ⦄ := by
  ...
```

This ordinary theorem states the existing total WP postcondition directly.
A view-only theorem states just the view equality. Partial correctness uses
`⦄div` in place of `⦄`: it explicitly permits divergence and still excludes
failure. These are Aeneas's existing specification operators. Use `WP.spec_mono`
to adapt an existing result specification to a view, and register useful caller
specifications with `attribute [step] operation_spec`. The existing Aeneas
registry then lets callers use `step` without specifying the theorem manually.

`AeneasContracts.indexed_loop_spec` specializes Aeneas's `loop.spec_decr_nat`
to a state and `Usize` index. Supply a view, the mathematical value of each
prefix, and a representation invariant. Each continuing body step must advance
the index by
exactly one and establish the next prefix; a completed step must be at the
length. The adapter supplies bounds and the decreasing `length - index`
termination measure. The record constructor instantiates this rule; its body
proof still establishes the arithmetic bounds needed to avoid Rust overflow.
`SupportTests.lean` contains a smaller independent example.

The specification syntax, examples, and required-contract proof terms
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
The checked-in patch exposes the existing `Config.use_tuple_structs` option as
`-use-tuple-structs false`, which our extraction selects. The upstream default
remains unchanged. Source and patch digests, a distinct tool version, and
`tests/nominal-tuples.sh` keep this change reproducible and check constructors,
projections, patterns, updates, and default-mode compatibility.
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
  Rust values by admitting zero; the generated conditional contracts assume
  successful recursive decoding of inputs and prove it for returned values.
  This introduces no axiom asserting that every modeled wrapper is nonzero.
- Lean's kernel, its standard logic axioms, and the imported proof artifacts
  check the encoded propositions correctly. Release checksums establish
  artifact identity, not a proof of compiler or model correctness.

Failure controls challenge missing annotations and proofs, orphaned proofs,
incorrect binding and parameter order, malformed specifications, admitted
proofs, unrelated theorem types, changed generated callees, and comments or
whitespace accepted by fuzzy comparison. Each model must pass the same controls.
Control families are selected from available model capabilities. Once selected,
a missing fixture or mutation target is an error. Semantic model mutations must
compile before their proof failures count as evidence; malformed mutants fail
the control run. Valid weaker contracts and weakened outcome predicates must
also be rejected. Controls edit and restore scratch workspaces, then recheck the
original results.

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
