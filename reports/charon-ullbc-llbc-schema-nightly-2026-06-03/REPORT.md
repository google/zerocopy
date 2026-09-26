# Charon ULLBC and LLBC schema at Aeneas nightly-2026.06.03

## Summary

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
the Charon revision pinned by Aeneas `nightly-2026.06.03`, Charon's exported
crate is substantially richer than a list of function bodies. A
`TranslatedCrate` contains target information, files and spans, stable-in-file
item IDs and names, type/function/global declarations, trait declarations and
implementations, and a reordered declaration graph. Function/global bodies share
a MIR-derived expression/type vocabulary and can be represented in either ULLBC
or LLBC.

**ULLBC** ("Unstructured LLBC") is Charon's cleaned-up MIR-like control-flow
representation. A body is an indexed vector of basic blocks. Each block has
statements plus one terminator; terminators carry explicit CFG edges for goto,
branching, calls, drops, asserts, inline assembly, return and unwind behavior.

**LLBC** is the structured-control-flow form Charon normally emits. It reuses
the same places, operands, rvalues, types, calls and declaration graph, but
replaces the explicit basic-block/terminator graph with nested statements such
as `Switch`, `Loop`, `Break`, `Continue`, `Call`, `Abort` and
`Return`. Charon reconstructs `if`/integer switches and then resugars some
enum-discriminant switches into ADT matches.

The ULLBC→LLBC boundary is therefore primarily a **control-flow reconstruction
boundary**, not a fresh source-language translation. The common AST on both sides
already contains semantic information not present as direct Rust syntax:
typed places/projections, move-vs-copy operands, reference/raw-pointer creation,
borrow kinds, pointer metadata, function/trait references, generic arguments,
constant expressions and target/layout information.

Before the ULLBC→LLBC step, Charon also runs a substantial normalization and
resugaring pipeline. At this revision the pipeline inserts missing pointer
metadata and storage-liveness information, normalizes drops, resolves some trait
method references, inlines selected compiler-generated code, reconstructs
fallible operations and assertions, simplifies constants/locals, merges goto
chains and removes unreachable blocks. Thus "LLBC semantics" means the semantics
of Charon's transformed IR, not a byte-for-byte transcription of rustc MIR.

Charon serializes both ULLBC and LLBC inside the same top-level `CrateData`
format, with a Charon version string and a `has_errors` marker. JSON and
Postcard encodings are supported. The version deserializer currently requires
exact equality with the consuming Charon library version. This report describes
the source schema and transformation semantics; it does **not** establish
cross-version serialization compatibility, which remains a separate #3720
subject.

This package also contains [`ARCHITECTURE.md`](ARCHITECTURE.md), which records the same pinned Charon revision's Cargo-wrapper/rustc-driver topology, compiler callback point, MIR acquisition rules, worklist extraction, and post-rustc transformation boundary. It covers the separate #3720 subject **Charon architecture and rustc integration** without treating that architecture as part of the LLBC schema itself.

No fresh Charon execution was performed. The report is based on the exact pinned
source and its checked-in documentation.

## Applicability

The primary subject is
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon version
`0.1.210`, which Aeneas
`nightly-2026.06.03` pins through both `charon-pin` and its Nix dependency
state.

Anneal's current toolchain assembly at
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` selects that Aeneas
release. As documented separately in the reference corpus, Anneal also has an
independently declared newer `charon_lib` dependency, but current live Anneal
source does not execute an LLBC boundary through that library. This report
therefore uses the Charon source that belongs to the Aeneas release as the
relevant translation subject.

Charon's options materially affect the exported IR. In particular:

- `--ullbc` skips structured-control-flow reconstruction;
- the default MIR level is promoted MIR for current-crate items;
- `--precise-drops` raises the minimum MIR level to elaborated MIR;
- the Aeneas preset enables transformations including associated-type lifting,
  fallible-operation reconstruction, assertion reconstruction, marker-trait and
  allocator hiding, operation/index lowering to calls, and some clause cleanup.

The schema described below is the source-level AST capacity at this revision.
A concrete output file may omit or normalize constructs depending on these
options and on the translated input.

## Findings

### The serialized unit is a whole translated crate, not one function

`CrateData` wraps:

- `charon_version`;
- one `TranslatedCrate`;
- `has_errors`, which indicates that the crate description is partial because
  translation encountered errors.

`TranslatedCrate` contains:

- the crate name;
- the Charon CLI options used to produce it;
- target information, including pointer size and endianness per target;
- a file table used by spans;
- complete registered item-name tables, including names for items that failed
  translation;
- short-name mappings;
- indexed maps of type declarations, function declarations, global
  declarations, trait declarations and trait implementations;
- reordered declaration groups, including mutually recursive groups.

This makes LLBC/ULLBC a crate-level semantic exchange format with cross-item
identity and dependencies, not merely serialized MIR bodies.

Basis: **source** in `charon/src/ast/krate.rs` and
`charon/src/export.rs`.

### Charon has explicit IDs for every major declaration class

The top-level `ItemId` distinguishes:

- type declarations;
- trait declarations;
- trait implementations;
- functions;
- globals.

Each class has its own typed index (`TypeDeclId`, `TraitDeclId`,
`TraitImplId`, `FunDeclId`, `GlobalDeclId`). Associated trait items have
their own IDs for associated types, methods and constants.

These IDs are references within one translated crate; the report does not claim
that the numeric index is a revision-stable external Rust identity. Charon also
stores names and item metadata, which are the subject of the separate item-
identity/source-correspondence report.

Basis: **source**.

### Type declarations preserve semantic structure beyond source spelling

A `TypeDecl` carries item metadata, generic parameters, source context, type
kind, per-target layout information when computable, and pointer-metadata
classification.

`TypeDeclKind` distinguishes structs, enums, unions, opaque types, aliases and
translation-error placeholders. Although rustc normally inlines aliases through
uses, Charon retains top-level alias declarations as aliases to another type.

Enum variants carry their semantic discriminant value and fields. Charon's
comments explicitly distinguish this discriminant from the physical layout tag
used in memory. Type declarations can also contain per-target layout records,
which means the crate IR has a place to preserve layout information without
pretending every generic or DST layout is known.

Basis: **source** in `types.rs`.

### The type system includes regions, references, raw pointers, traits and function ABIs

The common `Ty` / `TyKind` vocabulary includes, among other cases:

- ADTs and built-in container-like types;
- type variables and generic arguments;
- integer/float/bool/char literal types;
- the never type;
- references carrying a `Region`, pointee type and reference kind;
- raw pointers;
- trait associated types;
- dynamic trait types;
- function-pointer types.

Generic arguments are split into regions, types, const generics and trait
references. Function signatures carry an `is_unsafe` bit, ABI, inputs and
output. ABI distinguishes Rust, C and other Rust ABI spellings.

Consequently LLBC does not erase every Rust type-system distinction at Charon's
boundary. In particular, the Charon AST still has regions and reference kinds;
later Aeneas handling of those fields is a separate translation question.

Basis: **source** in `types.rs`.

### Places are typed and projections retain memory-relevant structure

A `Place` consists of a place kind plus its type. Places may refer to locals,
nested projections or globals.

Projection elements include:

- pointer/reference/Box dereference;
- ADT/tuple field projection;
- pointer metadata;
- indexing;
- subslicing.

Charon explicitly models a built-in wide pointer as having an address plus
metadata and represents access to that metadata as a projection. Index and
subslice projections exist in the common AST but are eliminated by later LLBC
micro-passes.

This is semantically significant for verification: a place is not represented as
an untyped source path, and pointer metadata has a first-class representation.

Basis: **source** in `expressions.rs`.

### Operands distinguish copy, move and constants

`Operand` has three principal cases:

- `Copy(Place)`;
- `Move(Place)`;
- constant expression.

This preserves MIR's ownership-relevant distinction between reading by copy and
moving a value from a place.

Constant representation is normalized later. The source says that only literal
and variable constant-expression forms remain in final LLBC; other MIR-derived
constant forms are intermediate and are desugared.

Basis: **source**.

### Rvalues include references, raw pointers and explicit operation categories

The common `Rvalue` representation includes:

- use of an operand;
- creation of a reference to a place, with `BorrowKind` and pointer metadata;
- creation of a raw pointer with mutability/reference kind and pointer metadata;
- unary, binary and nullary operations;
- discriminant reads;
- aggregate construction;
- additional MIR-derived operation families defined in the AST.

`BorrowKind` distinguishes shared, mutable, two-phase mutable, shallow/fake and
unique-immutable borrows. Charon therefore preserves more than a binary
shared/mutable source distinction at this layer.

Charon also has an abstract-byte/provenance representation for constants:
uninitialized bytes, concrete byte values and pointer bytes with provenance to a
global/function or unknown provenance. This is not a complete Rust operational
memory model; it is the IR's constant/value representation.

Basis: **source**.

### ULLBC bodies are explicit basic-block CFGs

`ullbc_ast.rs` describes ULLBC as "LLBC before the control-flow
reconstruction" and effectively a cleaned-up MIR.

A ULLBC body is an indexed vector of `BlockData`; block 0 is the entry block.
Each block contains ordinary statements plus exactly one terminator.

ULLBC statements include:

- assignment;
- set-discriminant;
- `copy_nonoverlapping`;
- storage-live/storage-dead;
- place mention;
- non-diverging assertion with explicit failure effect;
- no-op.

ULLBC terminators include:

- goto;
- conditional/integer switch;
- function call with normal and unwind targets;
- drop with normal and unwind targets;
- assertion with normal and unwind targets;
- inline assembly with possible targets/unwind;
- abort/panic/impossible cases;
- return;
- unwind resume.

This representation preserves explicit CFG and unwind edges.

Basis: **source** in `ullbc_ast.rs`.

### LLBC replaces graph edges with structured control flow

`llbc_ast.rs` states that LLBC is MIR-like code after Charon has rebuilt
structured control flow. It intentionally collapses MIR's statement/terminator
split into one statement vocabulary.

LLBC statements include the shared semantic operations plus:

- drop as a statement;
- call as a statement;
- abort and return;
- `Break(n)` and `Continue(n)` for nested loops;
- `Switch`;
- `Loop(Block)`;
- error placeholder.

`Switch` has three forms:

- `If(condition, then, else)`;
- integer switch with grouped literal cases and an otherwise block;
- ADT match over variants, introduced by a later resugaring pass.

Blocks become nested `Block { span, statements }` trees rather than indexed CFG
nodes. Statements also receive an ID that is unique within the body, primarily as
an AST handle.

Basis: **source** in `llbc_ast.rs`.

### ULLBC→LLBC reconstructs control flow, including loops and branch joins

Charon's checked-in transformation documentation says the rustc MIR input is a
CFG with arbitrary gotos and that Charon normally converts it to nested
`match`/`if`/`loop` control flow; `--ullbc` disables this step.

The `ullbc_to_llbc` implementation builds CFG analyses including reachability,
domination, loop entries, switch nodes and selected exits. It uses this
information to decide where branches rejoin and how to represent loops,
breaks/continues and exits without duplicating large suffixes unnecessarily.

This is a reconstruction: the source comments acknowledge that multiple
structured forms may represent the same CFG and describe heuristics for selecting
loop/switch exits. Accordingly, source-level syntactic structure is not guaranteed
to be recovered exactly merely because the resulting control flow is structured.

Basis: **source** + **documentation**.

### Important semantic rewriting happens before control-flow reconstruction

`run_transformation_passes` first prints the directly translated ULLBC (when
requested), then performs item/type and body transformations before the final
ULLBC/LLBC output.

At this revision, the pre-control-flow body pipeline includes:

- pointer-metadata insertion;
- explicit unit-return assignment insertion;
- insertion of missing `StorageLive`;
- drop normalization;
- resolution of known trait-method references;
- dynamic-trait-call transformation;
- replacement/inlining of promoted and inline constants and selected generated
  functions;
- removal of trivial drops;
- moving dynamic checks into statements;
- goto-chain merging;
- reconstruction of fallible operations, with the dynamic checks folded into
  the semantics of the reconstructed operation;
- reconstruction of `vec!` lowering;
- intrinsic recognition;
- assertion reconstruction;
- constant simplification;
- local/index cleanup;
- return-block duplication;
- removal of unused locals;
- filtering of unreachable blocks.

Some of these transformations explicitly depend on recognizable rustc MIR
shapes. The comments warn that ordering is semantically important.

Thus final ULLBC is already a normalized/resugared Charon IR. LLBC adds
structured-control-flow reconstruction on top of that.

Basis: **source** in `transform/mod.rs`.

### Post-reconstruction passes further change the final LLBC vocabulary

After ULLBC→LLBC, Charon:

- reconstructs enum matches where possible;
- prettifies the structured CFG;
- converts selected operators/array constructions to function calls when the
  corresponding option is enabled;
- converts array/slice indexing to function calls when enabled.

Both final ULLBC and final LLBC then undergo shared cleanup such as removal of
unused locals/NOPs, comment recovery, allocator-parameter hiding when requested,
partial monomorphization and declaration reordering.

The output's semantics therefore depend on the recorded Charon options; the
serialized `TranslatedCrate.options` field exists specifically so consumers can
check how the producer was invoked.

Basis: **source**.

### Charon deliberately resugars some rustc checks into operation semantics

A particularly important transformation for verification is
`reconstruct_fallible_operations`. Charon's source says rustc-generated
overflow, division-by-zero and bounds checks can be removed because those checks
are part of the corresponding arithmetic/array operation's semantics in
(U)LLBC.

This means a consumer must not infer "no explicit assert edge" to mean "no
failure/UB condition." Some dynamic checks have been folded into the semantics of
a higher-level IR operation.

Basis: **source**. This report does not attempt to formalize each operation's
downstream Aeneas semantics.

### Source and diagnostic metadata are embedded throughout the schema

Statements and terminators carry `Span`; items carry `ItemMeta`; the crate
contains a file table. A `Span` has a source span and optionally a
`generated_from_span` used for macro expansion/inlining provenance. Statements
also have recovered preceding comments.

This establishes that source correspondence information exists in the schema,
but not how complete or stable it is. Granularity, macro behavior, item naming
and comments are intentionally left to the separate #3720 source-
identity/correspondence report.

Basis: **source**.

### Serialization wraps either body form in the same versioned crate envelope

`CrateData` is used for both ULLBC and LLBC. It serializes to JSON or Postcard.
The envelope contains the Charon version and `has_errors`, while the selected
body representation is determined by options and the concrete AST stored in
`TranslatedCrate`.

The deserializer checks the serialized Charon version against the local Charon
version by exact equality. The source comment says the format should be "as
stable as possible," but the current compatibility gate is equality, not a
schema-negotiation mechanism.

This report records that mechanism only. It does not establish which distinct
Charon commits happen to be structurally compatible or whether version numbers
track every semantic change.

Basis: **source** in `export.rs`.

## Boundaries

- **No fresh LLBC/ULLBC file was generated on this execution surface.** The schema
  and transformation findings come from pinned source and checked-in
  documentation.
- **This is not a JSON field-by-field wire-format specification.** Serde derives,
  hash-consing/deduplication and generated OCaml bindings determine concrete JSON
  details. The report focuses on semantic AST structure. Serialization
  compatibility remains a separate #3720 subject.
- **The schema is option-sensitive.** Aeneas uses a preset that enables several
  transformations. Other Charon consumers may emit a materially less-resugared
  AST.
- **Not every AST variant necessarily appears in final LLBC.** Several comments
  explicitly identify intermediate variants eliminated by micro-passes.
- **Operation semantics are not fully formalized here.** The report identifies
  represented operations and where checks are folded into them, but does not
  reproduce Aeneas's or Charon's semantic interpretation of every operator.
- **Item identity, naming, spans and comments are only inventoried.** Their
  precision and stability are separate #3720 work.
- **Unsupported Rust is outside this report.** The fact that the schema contains a
  variant does not prove Charon correctly supports every source-language way to
  reach that construct.
- **Control-flow reconstruction is not claimed to invert rustc lowering.** It
  produces a structured representation of the CFG; the implementation uses
  analysis and heuristics and may not recover original source syntax exactly.
- **Partial/error output is representable.** `has_errors` means a serialized
  crate can intentionally be incomplete; consumers must not equate successful
  deserialization with complete extraction.

## Evidence

**Source — pinned Charon.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/src/ast/krate.rs`: `TranslatedCrate`, item IDs, declaration maps,
  target information and declaration ordering.
- `charon/src/ast/types.rs`: type declarations, generic arguments, regions,
  references/raw pointers, trait-associated types, function signatures and ABI.
- `charon/src/ast/expressions.rs`: places/projections, borrow kinds, operands,
  constants/provenance and rvalues.
- `charon/src/ast/ullbc_ast.rs`: ULLBC blocks, statements, terminators and
  explicit CFG targets.
- `charon/src/ast/llbc_ast.rs`: structured blocks, statement kinds,
  switches/matches, loops and break/continue.
- `charon/src/ast/meta.rs`: spans, generated-from spans, files and item
  metadata.
- `charon/src/transform/mod.rs`: exact transformation ordering around the
  ULLBC→LLBC boundary.
- `charon/src/transform/control_flow/ullbc_to_llbc.rs`: CFG analysis and
  structured-control-flow reconstruction.
- `charon/src/export.rs`: `CrateData`, version gate and JSON/Postcard
  serialization.
- `charon/src/options.rs`: `--ullbc`, MIR levels, Aeneas preset and
  transformation options.

**Documentation — pinned Charon.**
Same revision, `docs/transformations.md`, which describes ULLBC as the
unstructured form and LLBC as the default structured-control-flow result.

**Source — Aeneas pin.**
`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
`charon-pin`, selects the Charon revision above.

**Derived.**
The characterization of the ULLBC→LLBC boundary as primarily control-flow
reconstruction follows from the shared AST modules plus the transformation
pipeline. The warning that absence of explicit checks does not imply absence of
failure conditions follows from Charon's own
`reconstruct_fallible_operations` comments.

## Revalidation

For a later Charon revision, the cheapest source-level procedure is:

1. Resolve the exact Charon commit actually used by the relevant Aeneas/Anneal
   subject.
2. Diff `ast/krate.rs`, `types.rs`, `expressions.rs`,
   `ullbc_ast.rs`, `llbc_ast.rs` and `meta.rs`.
3. Diff `transform/mod.rs` to identify added/removed/reordered passes and
   changed option guards.
4. Diff `control_flow/ullbc_to_llbc.rs` for changes in loop/switch
   reconstruction.
5. Diff `export.rs` and generated serializer/type bindings for wire-format or
   version-gate changes.
6. Diff the Aeneas preset in `options.rs`; the same AST revision can expose
   different semantics to a consumer when preset flags change.

On a capable execution surface, preserve a small golden fixture containing a
loop, an if, an enum match, indexing with bounds checks, overflowing arithmetic,
a mutable borrow, a raw pointer, a call that can unwind, a drop and one macro.
Generate both:

- final ULLBC with `--ullbc`;
- ordinary structured LLBC using the Aeneas preset.

Record the Charon commit/options and hashes of the JSON outputs. Compare the two
at the AST level to confirm which distinctions survive the control-flow
boundary. Such a fixture would revalidate the concrete serializer and pass
behavior for those constructs; it would not prove completeness for all Rust.
