# Build-script and proc-macro generated Rust visibility before Charon at nightly-2026-05-31

## Summary

Build scripts and procedural macros both generate or select Rust code before
Charon's translation, but they cross the compiler boundary in different ways.

A Cargo build script is a separate **host executable**. Cargo compiles and runs it
before compiling the package target. The script can write generated source into
`OUT_DIR`, emit `cargo::rustc-cfg` and `cargo::rustc-env` directives, and
supply native link inputs. Cargo does not turn every file in `OUT_DIR` into Rust
code automatically. Generated Rust becomes part of the target crate only when the
target's source/module/macro structure consumes it—for example with
`include!(concat!(env!("OUT_DIR"), "/generated.rs"))` or an equivalent module
arrangement. Rust's `include!` documentation explicitly identifies build-script
artifacts as a primary use.

A procedural macro is also implemented in a separate host `proc-macro` crate,
but its output enters the target crate as syntax. The Rust Reference specifies
that a proc macro consumes and returns token streams during compilation:
function-like output replaces the invocation, derive output appends items, and an
attribute macro replaces the annotated item with its returned items. rustc runs
name resolution and macro expansion before its `after_expansion` callback.

At the examined Charon revision, `charon cargo` deliberately compiles **host
crates**—including build scripts and proc-macro crates—normally and does not
translate them. Charon translates only the selected target crate. It installs its
rustc callback at `after_expansion`; absent a narrower `--start-from`, Charon
starts from `crate`, which its own option documentation defines as translating
the whole selected crate. Thus:

- unsafe operations *inside the implementation of* a build script or proc-macro
  crate are not part of the selected target crate's Charon output;
- Rust source emitted by a build script and then included as target-crate source
  is compiled as target Rust and is visible to Charon if it survives the normal
  cfg/MIR/reachability boundaries;
- Rust syntax emitted by a proc macro is already expanded into the selected
  crate when Charon begins translation, so generated unsafe operations are
  visible semantically on the same basis as equivalent handwritten target-crate
  operations, subject to Charon's ordinary support and later transformations;
- native code compiled/linked by a build script has no Rust MIR body for Charon
  to extract, even though Rust FFI declarations/calls can remain visible.

The important provenance caveat is that post-expansion visibility is not the same
thing as recoverable authorship. Build-script files included from `OUT_DIR` can
have ordinary real-file spans. Charon records rustc's filename, line/column
extent, and loaded file contents for such spans. Procedural macros, by contrast,
operate on tokens whose `Span` is opaque and can be manufactured or replaced.
The stable proc-macro API supports call-site and mixed-site spans and permits
separating source location from name-resolution context with `located_at` and
`resolved_at`.

Charon does not serialize rustc's macro expansion chain or hygiene context in its
ordinary span representation. Its `translate_span_data` asks rustc for the
span's filename and line/column positions and stores those; it does not walk the
macro expansion parent chain. Therefore a final Charon span can identify where
rustc locates the expanded token, but it is not a reliable general answer to
“which procedural macro invocation generated this operation?” A proc macro may
deliberately attach the invocation's call-site span, reuse an input token's span,
or otherwise choose location/hygiene.

No fresh build script or procedural-macro fixture was executed for this report.
The central compilation/visibility behavior follows directly from Cargo, the
Rust Reference/rustc, and Charon source at the pinned revisions. A small
execution matrix for preserving concrete source-map specimens is described under
**Revalidation**.

## Applicability

The relevant Anneal configuration is
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
whose `anneal/flake.nix` selects Rust date `2026-05-31` and Aeneas
`nightly-2026.06.03`.

The Charon behavior is pinned to
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
the revision selected by that Aeneas release. Its `rust-toolchain` is
`nightly-2026-05-31`.

Cargo behavior is examined at
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, the Cargo
submodule in the matching Rust source
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
Procedural-macro language rules are taken from the Rust Reference at
`rust-lang/reference@01b0ee707f4571e803c8b2c471d8335a448f5d60`, the final
Reference revision on 2026-05-31, while proc-macro `Span` API details come from
the exact Rust source revision above.

As in the other 2026-05-31 reports, the observation environment did not prove a
reproducible byte-for-byte mapping from Anneal's downloaded Rust distribution to
the chosen Rust source commit. The exact Cargo/Charon source relationships and
matching toolchain date establish the implementation subjects examined; they are
not a binary provenance proof.

“Generated Rust” here means Rust syntax whose text/tokens are produced by a
build-time program and which rustc then compiles as part of the selected target
crate. It does **not** include arbitrary native object code emitted by a build
script.

“Visible to Charon” means represented in the post-expansion selected target crate
and capable of reaching Charon's HIR/MIR-based translation. It does not mean that
the original lexical token sequence, generator identity, or every source span is
preserved. Conditional compilation, unsupported Rust, MIR preprocessing,
reachability, and later Charon transformations can still remove or transform
code; those are independent boundaries.

## Findings

### Cargo build scripts execute as host programs before target compilation

Cargo's build-script documentation says that a package build script is compiled
to an executable and run just before the package itself is built. Build scripts
receive their inputs primarily through environment variables and communicate
compilation instructions back to Cargo by printing `cargo::...` lines.

Cargo explicitly lists source generation as a build-script use case. It directs
scripts to place generated files and intermediate artifacts in the package's
`OUT_DIR`. `OUT_DIR` is unique to the package's build context but is not
cleaned or reset between builds; generated contents can persist and scripts are
responsible for managing them.

Cargo also distinguishes host and target context. The build script itself runs
for the host. Cargo supplies `HOST`, `TARGET`, and target-derived
`CARGO_CFG_*` variables; the documentation warns that `cfg!` inside the build
script tests the host, not the package target.

Basis: **documentation** — Cargo
`src/doc/src/reference/build-scripts.md` and
`environment-variables.md` at `fbb61be3…`.

### Generated files are inputs only when the target crate consumes them

Writing a `.rs` file into `OUT_DIR` is not itself a Cargo instruction to
compile that file as a new crate/module. The build-script interface exposes
`OUT_DIR` as a filesystem output location and compilation directives such as
cfg/env/link flags; it does not define an “add Rust source file” directive.

Cargo sets `OUT_DIR` again while compiling a package that has a build script,
which makes the path available to compile-time macros such as `env!`. Rust's
standard `include!` macro parses the named file as an expression or item
according to its syntactic context and places it into the surrounding code
unhygienically. Its documentation explicitly says one of its primary uses is to
include build artifacts, usually output from `build.rs`.

A canonical pattern is therefore conceptually:

```rust
include!(concat!(env!("OUT_DIR"), "/generated.rs"));
```

Once that inclusion has happened, the generated text is no longer merely a build
artifact: rustc parses/expands/lowers it as part of the target crate. Equivalent
module arrangements can achieve the same result.

Basis: **documentation** — Cargo environment/build-script docs + **source
documentation** for Rust's built-in `include!`.

### Build scripts can change the target source/configuration without generating a Rust file

Build scripts have compilation effects beyond file generation.

`cargo::rustc-cfg=KEY[="VALUE"]` tells Cargo to pass a `--cfg` value to
rustc for the package. The Cargo documentation explicitly says this enables
compile-time cfg settings but does not alter Cargo dependency resolution. Such a
directive can therefore cause one Rust source branch/module/item to be present
and another to be excluded before Charon sees the crate.

`cargo::rustc-env=VAR=VALUE` sets an environment variable while the package is
compiled. Compile-time `env!`/related macros can use that value to synthesize
constants or other syntax.

Link directives can select native libraries, search paths, and link arguments.
Those can materially affect the eventual executable without creating a Rust MIR
body for the native implementation.

Therefore a sound inventory of “build-script-generated behavior” is broader than
files in `OUT_DIR`: build-script outputs can change cfg selection, compile-time
values, and linked implementation.

Basis: **documentation** — Cargo build-script interface.

### Build-script native output is outside Charon's Rust-body visibility

Cargo's own build-script examples include compiling bundled C code and locating
or linking native libraries. Charon translates Rust compiler representations; a
native object/library linked by Cargo has no Rust HIR/MIR body for Charon to
translate.

If target Rust declares or calls an `extern` item, Charon can still observe the
Rust-side declaration/call according to its FFI support and opacity rules. That
does not expose the native callee's implementation.

This is a hard boundary distinct from generated Rust source. A build script that
writes Rust and includes it into the target can make that Rust visible to
Charon; a build script that emits an ELF/Mach-O/archive and links it cannot make
the machine-code body visible through rustc MIR.

Basis: **documentation** + **derived** from Charon's rustc/HIR/MIR extraction
architecture. Detailed FFI semantics remain a separate #3720 subject.

### Procedural macros execute host code and return target-crate syntax

The Rust Reference defines three procedural-macro forms: function-like, derive,
and attribute macros. A proc macro runs code at compile time over Rust syntax.
The stable interface is token streams rather than AST nodes.

The forms differ in how output enters the target syntax:

- a function-like proc macro replaces its invocation with the returned token
  stream;
- a derive macro receives the annotated struct/enum/union token stream and
  appends the returned items after the input item;
- an attribute macro receives the attribute input and item input and replaces
  the annotated item with zero or more returned items.

A proc macro must be defined in the root of a crate whose crate type is
`proc-macro`, and cannot be used from the same crate. Its implementation is
therefore a separately compiled host-side compiler extension; its returned syntax
belongs to the consuming target crate.

Basis: **normative** — Rust Reference at `01b0ee7…`.

### rustc completes macro expansion before Charon's selected-crate callback

rustc's `Callbacks` interface documents `after_expansion` as “Called after
expansion.” The driver implementation ensures
`tcx.resolver_for_lowering()`—with the source comment “Make sure name resolution
and macro expansion is run”—immediately before invoking the callback.

Charon's `Callbacks` implementation performs `translate_crate::translate` in
that exact `after_expansion` callback.

Consequently, Charon does not need to interpret proc-macro token streams itself.
For the selected target crate, it operates after rustc has integrated macro
output into the compiler's crate representation. Generated functions, impls,
expressions, unsafe blocks, raw-pointer operations, extern declarations, and
other supported Rust constructs are subsequently encountered through the same
compiler item/MIR machinery as handwritten expanded code.

Basis: **source** — rustc
`compiler/rustc_driver_impl/src/lib.rs`; Charon
`charon/src/bin/charon-driver/driver.rs`.

### Charon deliberately skips the generator crates themselves

When `charon cargo` invokes Cargo, it sets `RUSTC_WRAPPER` to
`charon-driver`, sets a marker `CHARON_USING_CARGO`, and forces an explicit
`--target` even for a native target. Charon's source says this explicit target
is necessary to distinguish host crates from target crates.

Every rustc invocation therefore passes through the wrapper, but the wrapper
does not translate every crate. It computes:

- whether Cargo marks the package as a primary selected package using
  `CARGO_PRIMARY_PACKAGE`;
- whether the invocation has `--target`.

Charon's source explains that **host crates are build scripts and proc macros**.
They still need to compile normally, but only target crates should be processed
by Charon. `is_selected_crate` therefore requires both a primary package and a
target invocation. For other invocations Charon runs rustc normally and returns
no translated crate.

This creates a precise distinction:

- unsafe code in `build.rs` itself is not target LLBC;
- unsafe code in the implementation of a procedural macro itself is not target
  LLBC;
- target Rust emitted/selected by either mechanism can be target LLBC.

Basis: **source** — Charon `charon/src/bin/charon/main.rs` and
`charon-driver/driver.rs`; Cargo's documented `CARGO_PRIMARY_PACKAGE`
semantics.

### By default Charon treats the selected crate as transparent and starts from it

Charon's option documentation says that, absent explicit start points,
translation starts from path `crate`, “which translates the whole crate.”
`TranslateOptions::new` materializes that default and also installs an opacity
rule making `crate` transparent.

The translation context is constructed from rustc's post-expansion `TyCtxt`.
Its work queue starts from the selected items and recursively enqueues referenced
items. Alternative start modes that select attributes or public items enumerate
rustc HIR crate definitions after expansion.

Thus local items created by a proc macro or included generated source are not
excluded merely because they were generated. Their ordinary inclusion depends on
the same selected-crate/start-point/opacity/reachability machinery as other local
items.

Basis: **source** — Charon `options.rs` and
`translate/translate_crate.rs`.

### Generated unsafe operations are visible semantically, not necessarily lexically

Once generated code has entered the target crate before Charon's post-expansion
translation, rustc lowers it into the same HIR/MIR operation forms used for
handwritten code.

For Anneal-relevant coverage, this means a proc macro that emits a raw-pointer
dereference, union access, unsafe call, inline assembly, or another
verification-relevant operation does not create a special “macro body” that
Charon ignores. If rustc's selected target actually contains the operation at
the MIR stage Charon consumes, Charon confronts it according to its ordinary
translation support.

The same is true of a generated file included from `OUT_DIR`.

This finding is intentionally about **operations/behavior**, not lexical
`unsafe { ... }` provenance. rustc/Charon may not preserve the exact original
unsafe-block boundary as a semantic object. The separate #3720 subjects for MIR
representation of unsafe operations and source-span provenance should establish
those details.

Basis: **derived** from rustc's post-expansion boundary and Charon's translation
architecture.

### Proc-macro spans are selectable metadata, not intrinsic generator provenance

The Rust Reference states that every procedural-macro token has an associated
opaque `Span`; a macro cannot mutate a `Span` value itself, but it can
manufacture spans and assign a span obtained from another token to an output
token.

At the pinned Rust source, stable `proc_macro::Span` APIs include:

- `Span::call_site()`: location of the current macro invocation; identifiers
  resolve as if written at the call site;
- `Span::mixed_site()`: macro_rules-like name resolution with location taken
  from the call site;
- `resolved_at(other)`: preserve location but use `other`'s name-resolution
  behavior;
- `located_at(other)`: preserve name-resolution behavior but use `other`'s
  source location.

`def_site()` and expansion-parent/source inspection APIs exist at this revision
but are unstable.

The Reference also explicitly calls proc macros **unhygienic**: their output
behaves as though written inline next to the invocation for ordinary name
resolution, so generated identifiers can interact with surrounding imports and
names.

These rules mean a generated operation has no intrinsic source coordinate that
must point to the proc-macro implementation. The macro author controls the spans
attached to generated tokens within the APIs available to it.

Basis: **normative** — Rust Reference + **source/API documentation** —
`library/proc_macro/src/lib.rs`.

### Charon stores source coordinates but not the rustc macro expansion chain

Charon's span translation turns a rustc `Span` into:

- a Charon file ID derived from rustc's `span_to_filename`;
- beginning line/display-column;
- ending line/display-column.

For real source files, Charon records a normalized file name and stores the
source file contents when rustc has them. It normalizes toolchain/cargo-home
paths in specific cases; otherwise local filesystem paths remain local paths.

The ordinary Charon `Span` created by `translate_span` has
`generated_from_span: None`. Charon does have a
`generated_from_span` relationship for MIR **inlining**:
`translate_span_from_source_info` walks `inlined_parent_scope` and records
the top-most inlined parent separately. That logic is about MIR inlining, not
macro-expansion parentage.

`translate_span_data` does not call rustc's expansion-parent APIs and does not
serialize syntax context/hygiene. Therefore Charon's normal source span is the
location rustc assigned to the expanded construct, not a complete expansion
backtrace.

A later diagnostic system cannot in general infer the proc-macro invocation or
proc-macro definition from that coordinate alone.

Basis: **source** — Charon
`charon/src/bin/charon-driver/translate/translate_meta.rs`.

### Included generated files can preserve a stronger filesystem provenance

The source-provenance story differs for build-script output consumed through a
real file.

`include!` parses a file and inserts it into the surrounding code. A generated
file loaded from `OUT_DIR` is therefore known to rustc as source input, and
spans from its parsed tokens can refer to that source file.

When Charon receives such a real-file span, its file registry records the
filename and copies `source_file.src` into the translated file table when
available. This can preserve the generated file's text alongside spans into it.

However, `OUT_DIR` is a build-directory path and Cargo explicitly does not
guarantee it is empty or stable across builds. Charon only normalizes some
special prefixes (sysroot and Cargo home). The report therefore does not treat
an arbitrary absolute/generated `OUT_DIR` path as a stable cross-machine
identity. Stable provenance should use package/build-subject identity plus
content when such identity is needed.

Basis: **source** — Charon span/file translation + **documentation** — Cargo
`OUT_DIR` semantics.

### Charon has an explicit limitation for non-real rustc filenames

`translate_filename` can represent rustc real filenames as Charon local or
virtual names. Other rustc `FileName` variants are converted to
`FileName::NotReal`.

But `translate_span_data` currently calls `unimplemented!()` when its
translated filename is `NotReal`. Thus Charon does not have a general
representation for every synthetic/non-real source-file kind rustc can attach to
a span.

This is a source-visible limitation relevant to generated syntax. The report
does **not** claim that ordinary proc-macro output at the pinned toolchain
necessarily triggers it; macro authors commonly use real call-site/input spans.
It establishes only that Charon's span representation is not universally capable
of representing arbitrary rustc synthetic filenames.

Basis: **source** — Charon `translate_meta.rs`.

### Build scripts can affect visibility through cfg before Charon ever sees an item

A build script can emit `cargo::rustc-cfg`, causing Cargo to pass a custom
`--cfg` to rustc for the target package. Rust conditional compilation operates
before Charon's post-expansion item/MIR traversal. Code excluded by cfg is
therefore not recoverable merely by asking Charon to “translate the whole
crate.”

This is a particularly important negative space for generated-code coverage:
Charon seeing every expanded local item is not equivalent to Charon seeing every
source token that could have been selected under another build-script output or
target configuration.

The precise cfg/module-selection rules remain covered by the separate #3720
conditional-compilation report; this package records the build-script entry
point into that mechanism.

Basis: **documentation** + **derived** from the compilation ordering.

### Generator implementation behavior and generated target behavior are different subjects

A build script or proc macro can execute arbitrary compile-time code with access
to filesystem/process resources. The Rust Reference explicitly notes that proc
macros run during compilation with the compiler's resources and have security
concerns similar to Cargo build scripts.

That compile-time execution can determine what target code is produced, but its
own runtime behavior is not target-program runtime behavior.

For verification-oriented reasoning this yields three separate layers of fact:

1. **generator implementation** — host executable/proc-macro crate, skipped by
   normal selected-target Charon translation;
2. **generation result/configuration** — files, cfg/env directives, token streams,
   native objects;
3. **selected target program** — expanded/lowered Rust that Charon translates.

Conflating these layers can produce both false coverage claims (“Charon scanned
the proc-macro implementation because it scanned generated code”) and false gaps
(“macro-generated unsafe code is invisible because the macro crate was skipped”).

Basis: **derived** from Cargo/Rust/Charon source.

## Boundaries

- **No fresh generated-code fixture was executed.** The compilation ordering,
  host/target filtering, proc-macro replacement semantics, and span serialization
  are established from exact primary source. The report does not claim to have
  observed concrete LLBC for a newly constructed build-script/proc-macro example
  on this execution surface.
- **This is not the conditional-compilation report.** Build-script
  `rustc-cfg` is recorded as an input to source selection, but the full
  `cfg`/`cfg_attr`/target/module exclusion semantics remain open.
- **This is not the full source-span provenance report.** The report establishes
  the generated-code-specific fact that proc-macro spans are assignable and
  Charon does not serialize an expansion chain. Macro_rules expansion,
  nested expansion backtraces, multibyte columns, remapped paths, and diagnostic
  recovery need broader treatment.
- **Lexical unsafe boundaries are not established.** The report says generated
  unsafe *operations* enter the same post-expansion MIR path. It does not claim
  Charon preserves the original `unsafe` block/keyword or can attribute a
  safety boundary to generated versus handwritten syntax.
- **Native build outputs are not modeled here.** Build-script-produced native
  code is outside Rust MIR. The semantics/trust treatment of FFI and assembly is
  separate work.
- **Proc-macro execution determinism is not established.** Proc macros have
  compiler process resources including filesystem access. This report does not
  claim expansion is deterministic, hermetic, or reproducible.
- **Generated-file stable identity is not established.** Charon can retain the
  rustc source filename and contents for real files, but an `OUT_DIR` path may
  be machine/build specific and contents may persist across build-script runs.
- **The Charon host/target test is implementation-specific.** The examined
  revision relies on an explicit `--target` being present for target crates,
  which `charon cargo` arranges deliberately. Do not generalize this mechanism
  to arbitrary direct wrapper invocation or future Charon revisions.
- **Manual compiler invocations by generators are not exhaustively modeled.**
  Cargo exposes `RUSTC`, `RUSTC_WRAPPER`, and related environment variables
  to build scripts, but arbitrary subprocess behavior chosen by a script is not
  equivalent to Cargo's ordinary target-crate compilation path.
- **Unsupported generated Rust remains unsupported.** Macro generation does not
  make a Rust construct semantically supported by Charon merely because rustc
  accepts it.

## Evidence

**Source — Anneal configuration.**
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix`: selected Rust date `2026-05-31` and Aeneas release.

**Documentation/source — Cargo.**
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`:

- `src/doc/src/reference/build-scripts.md` — build-script lifecycle,
  `OUT_DIR`, source generation, cfg/env/link directives, host/target inputs;
- `src/doc/src/reference/environment-variables.md` — `OUT_DIR` during package
  compilation and build-script execution, `CARGO_PRIMARY_PACKAGE`, `HOST`,
  `TARGET`, `CARGO_CFG_*`, and compiler/wrapper variables.

**Normative — Rust procedural macros.**
`rust-lang/reference@01b0ee707f4571e803c8b2c471d8335a448f5d60`,
`src/procedural-macros.md`: proc-macro kinds, token streams, span model,
compile-time execution, output replacement/append semantics, and unhygienic
behavior.

**Source/API documentation — rustc and standard macros.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `compiler/rustc_driver_impl/src/lib.rs` — macro expansion/name resolution
  occurs before `Callbacks::after_expansion`;
- `library/proc_macro/src/lib.rs` — `Span`, `call_site`, `mixed_site`,
  `resolved_at`, `located_at`, and unstable expansion-parent/source APIs;
- `library/core/src/macros/mod.rs` — `include!` parses an external file into
  surrounding syntax, is unhygienic, and is explicitly intended for
  build-script artifacts.

**Source — Charon selection and translation.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/bin/charon/main.rs` — Cargo invocation through
  `RUSTC_WRAPPER`, explicit target selection;
- `charon/src/bin/charon-driver/driver.rs` — host build-script/proc-macro
  detection, selected-target predicate, normal compilation of skipped host
  crates, and post-expansion translation callback;
- `charon/src/options.rs` — default `crate` start point and transparent local
  crate;
- `charon/src/bin/charon-driver/translate/translate_crate.rs` — post-expansion
  HIR/item work queue;
- `charon/src/bin/charon-driver/translate/translate_meta.rs` — filename/span
  conversion, file contents, generated-from-inline span handling, DefPath
  disambiguators, and `NotReal` limitation.

**Derived.**
The generated-unsafe visibility distinction follows from combining Cargo's
generator lifecycle, Rust's expansion semantics, rustc's post-expansion callback,
and Charon's host/target selection. The provenance limitation follows from the
proc-macro span API plus the fields Charon actually serializes.

## Revalidation

For a later Cargo/rustc/Charon combination, source-level revalidation should be
cheap:

1. In Cargo, diff build-script documentation/implementation for `OUT_DIR`,
   `rustc-cfg`, `rustc-env`, host/target execution, and primary-package
   environment behavior.
2. In rustc, verify that `after_expansion` is still after resolver/macro
   expansion and inspect any changed proc-macro `Span` APIs.
3. In Charon, diff the Cargo wrapper's host/target selection logic and confirm
   whether build-script/proc-macro crates are still compiled normally rather
   than translated.
4. Verify the default start point/opacity for the selected crate.
5. Diff `translate_meta.rs`: record whether macro expansion parentage/hygiene
   has become first-class, whether synthetic filenames are supported, and which
   path normalization rules changed.

On an execution surface with the pinned toolchain, preserve one compact fixture
workspace with:

- a `build.rs` that writes `generated.rs` into `OUT_DIR` containing a
  generated local function with a raw-pointer dereference inside `unsafe`;
- target source that `include!`s that file;
- a build-script `cargo::rustc-cfg=generated_cfg` controlling a second unsafe
  function;
- a proc-macro crate with a derive or function-like macro emitting a third unsafe
  local function;
- output tokens using at least (a) an input token span and (b)
  `Span::call_site()`;
- one build-script-linked native function called through an `extern`
  declaration.

Record:

1. rustc expanded output or another compiler-supported expansion view;
2. Charon original/final ULLBC and LLBC for the selected target crate;
3. Charon file table and spans for handwritten, included-file, and proc-macro
   generated operations;
4. the wrapper log showing the build script and proc-macro crate are host
   compilations skipped for translation;
5. target LLBC showing the generated Rust unsafe operations when selected;
6. the native `extern` declaration/call without a native MIR body;
7. a control run changing the build-script cfg.

A passing fixture would establish concrete observability/source-map behavior for
those exact generation patterns. It would **not** prove that every proc-macro span
can be mapped to its generator or that every arbitrary build-script subprocess is
captured.
