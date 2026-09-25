# Lifetime and region information through rustc, Charon, and Aeneas

## Summary

At Anneal's pinned 2026-05-31 Rust/Charon toolchain and Aeneas
`nightly-2026.06.03`, lifetime information changes representation several
times rather than disappearing at one compiler boundary.

Rustc distinguishes declared/free/bound regions, inference variables,
placeholders, `'static`, and erased regions. During MIR borrow checking, rustc
does **not** solve lifetimes by modifying the canonical MIR body that Charon
later reads. Borrow checking first clones the input MIR, replaces regions in that
private copy with fresh NLL inference variables, constructs constraints, and
solves those variables in a `RegionInferenceContext`. The solution records CFG
points and universal regions outlived by each region variable. It is borrow-check
analysis state, not a lifetime annotation that Charon retrieves from the
pre-borrow-check MIR.

Charon deliberately runs before MIR-based analysis and, for local items at its
default/Aeneas MIR setting, requests rustc's promoted MIR. It therefore does not
receive rustc's solved NLL `RegionInferenceContext`. Charon does preserve
signature-level lifetime parameters and outlives predicates. For body types,
where rustc commonly exposes `ReErased` regions at this extraction point,
Charon replaces each erased occurrence with a fresh existential
`Region::Body` identifier while translating the body. These body-region IDs
are **Charon-generated placeholders**, not rustc NLL inference-variable IDs and
not rustc's inferred region values.

Aeneas consumes Charon's region information before erasing it from its pure
output language. It computes a hierarchy of signature regions from lifetime
parameters and outlives relationships, groups mutually-outliving regions, and
uses those groups to create borrow abstractions and forward/backward function
interfaces. Its early prepasses erase most body-region identities from locals
and places, while deliberately retaining region arguments in function-call
operands. During symbolic translation, signature regions determine which
mutable borrows are consumed or returned by each backward function.

The final pure Aeneas AST has no lifetime parameters and no reference type
constructor: pure generic arguments contain types, const generics, and trait
references only, and translating a Rust/LLBC reference `&'a T` or
`&'a mut T` yields the translated referent type. The lifetime/borrow effect
survives indirectly in the generated functional interface. The checked-in
Aeneas `Paper.lean` is a concrete example: Rust

```rust
fn choose<'a, T>(b: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T
```

is generated as a Lean function with no `'a` parameter. It returns the selected
`T` together with a backward function `T -> (T × T)` that reconstructs the
updated input state. Thus “Aeneas erases lifetimes” is true of the pure/Lean type
language, but false if interpreted to mean that lifetime structure is discarded
before influencing the translation.

This source evidence does **not** establish that Charon's fresh body regions are
equivalent to rustc's NLL solution, that Aeneas reconstructs every Rust lifetime
constraint, or that the resulting model is sound for unsafe Rust. No fresh
compiler/Charon/Aeneas execution was available on this research surface.

## Applicability

This report concerns the exact revisions in `REPORT.json`:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`;
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`;
- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
  released as `nightly-2026.06.03`; and
- Anneal source at
  `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

The Charon revision records `nightly-2026-05-31` in `rust-toolchain`.
Anneal's `anneal/flake.nix` independently sets its Rust toolchain date to
`2026-05-31` and selects the Aeneas `nightly-2026.06.03` release. The
Aeneas source pins this Charon revision. As recorded elsewhere in this corpus,
that release/pin relationship is source-coupled; this report does not repeat
binary provenance analysis.

Charon's default MIR level is `Promoted`, documented in its options as the MIR
after constant promotion and the MIR used by borrow checking. The Aeneas preset
does not override that level. Charon's driver hooks `after_expansion`, before
MIR-based analysis, specifically because requesting promoted MIR for borrow
checking would otherwise make earlier MIR queries unavailable. These facts
matter because the report distinguishes Charon's extracted MIR from rustc's
subsequent NLL working copy.

“Lifetime,” “region,” and “borrow” are not interchangeable here:

- a Rust source lifetime parameter is a language-level name or binder;
- rustc represents several region kinds, including parameter, bound, inference,
  placeholder, static, and erased regions;
- rustc NLL uses `RegionVid` inference variables whose solved values contain
  CFG points and universal regions;
- Charon has its own `Region` representation, including declared variables,
  `Static`, fresh body-local IDs, and `Erased`;
- Aeneas additionally groups signature regions into abstractions that drive its
  functional borrow translation.

The report describes these exact implementations. It does not assert that
adjacent Rust, Charon, or Aeneas revisions have the same boundaries.

## Findings

### Rustc's type system retains several distinct kinds of region

At the examined rustc revision, `rustc_middle::ty::RegionKind` supports the
region forms Charon's bridge can observe: early parameters, bound regions,
late parameters, `'static`, inference variables, placeholders, erased regions,
and error regions. Rustc's helpers distinguish named/free regions from inference,
bound, placeholder, and erased regions.

This matters because “MIR has lifetimes” is too coarse. A type in MIR can carry a
region value, but that value may be a declared universal region, an erased region,
or—inside borrow checking's private working copy—a fresh NLL inference variable.

Basis: **source**, `rustc_middle/src/ty/region.rs`.

### NLL operates on a private cloned MIR body

Rustc's borrow checker takes the MIR body and promoted bodies as input, then
clones both before replacing regions:

```text
let mut body_owned = input_body.clone();
let mut promoted = input_promoted.to_owned();
let universal_regions =
    nll::replace_regions_in_mir(&infcx, &mut body_owned, &mut promoted);
```

The source comment is explicit: this private copy is modified in place to contain
non-lexical lifetimes.

`replace_regions_in_mir` first constructs `UniversalRegions` from the
function definition and signature. That step instantiates the function's input
and output lifetimes as NLL `RegionVid` variables. It then calls
`renumber::renumber_mir`, whose contract is to replace all remaining regions
in the MIR and promoted bodies with fresh inference variables.

The region renumberer does not preserve the old region value. Its generic
`renumber_regions` fold replaces every encountered region with
`next_nll_region_var(NllRegionVariableOrigin::Existential ...)`; MIR types,
generic arguments, explicit region operands, and constants are all visited.

Basis: **source**,
`compiler/rustc_borrowck/src/lib.rs`,
`compiler/rustc_borrowck/src/nll.rs`,
`compiler/rustc_borrowck/src/renumber.rs`, and
`compiler/rustc_borrowck/src/universal_regions.rs`.

### Rustc's inferred region values are analysis state, not Charon's body-region IDs

After MIR type checking has generated liveness and outlives constraints,
`nll::compute_regions` creates a `RegionInferenceContext` and solves the
constraints. That context stores:

- a definition for each `RegionVid`, including whether it is a free,
  placeholder, or existential region;
- liveness constraints;
- outlives constraints and their SCC graph;
- the final inferred value for each region SCC; and
- relationships among universal regions.

The source describes the final inferred value as the value of a region variable
computed per SCC. The values contain control-flow locations and universal-region
elements; borrow checking uses them to decide whether constraints hold.

Nothing in Charon's extraction path reads this solved
`RegionInferenceContext`. Charon runs before this analysis and reads the
promoted MIR query itself. Therefore a Charon numeric body-region ID must not be
interpreted as rustc's NLL `RegionVid`, nor as the set of MIR locations inferred
for that `RegionVid`.

Basis: **source** + **derived** comparison of the rustc and Charon call paths.

### Charon preserves declared lifetimes and invents existential body lifetimes

Charon's type AST has four high-level region forms:

- `Region::Var` for a region variable under its binder structure;
- `Region::Static`;
- `Region::Body`, documented as body-local and existentially bound at body
  level; and
- `Region::Erased`.

Its generic parameter structures preserve region parameters and both
region-outlives and type-outlives predicates. References in the Charon type AST
therefore retain a region together with shared/mutable reference kind and
referent type.

During translation, Charon handles rustc/hax regions as follows:

- `ReStatic` becomes `Static`;
- early parameters are looked up in the item's region-parameter map;
- bound regions are looked up in the current binder;
- `ReVar` and placeholders are rejected as unexpected outside inference;
- `ReErased` becomes `Erased` outside a body, but becomes a fresh
  `Region::Body` while translating a body.

The body conversion is deliberate. `translate_erased_region` checks whether a
`lifetime_freshener` is active; if so, it allocates a new body-region ID. When
a cached translated type is reused within a body, Charon refreshes erased and
body regions again to avoid accidentally reusing the same synthetic body
identity.

This design recovers *distinct existential handles* where rustc's extracted MIR
has erased region identity. It does not recover rustc's solved lifetime values.

Basis: **source**,
`charon/src/ast/types.rs`,
`charon/src/ast/types/vars.rs`,
`charon/src/bin/charon-driver/translate/translate_types.rs`, and
`translate_generics.rs`.

### Charon's golden output exposes the signature/body distinction

The pinned Charon repository contains checked-in golden LLBC that makes this
distinction visible without a fresh run.

For a Rust method whose signature is effectively
`fn from<'a>(v: &'a bool)`, Charon prints a declared signature lifetime
`'_0`, but the argument local in the body is `&'1 bool`.
For

```rust
fn foo(x: &u32) -> Option<&u32>
```

the generated signature has a bound lifetime `'_0`, while body locals use
fresh body IDs such as `'1` and `'2`. A caller body similarly contains fresh
body-region IDs and supplies a fresh lifetime argument at a call site.

These artifacts are checked-in source/golden data at the exact Charon revision;
they are not fresh **execution** evidence from this run.

Basis: **source (checked-in golden artifacts)**,
`charon/tests/ui/region-inference-vars.{rs,out}` and
`charon/tests/ui/monomorphization/bound_lifetime.{rs,out}`.

### Charon also records whether ADT lifetime parameters participate in mutable borrows

Charon's `RegionParam` carries a `LifetimeMutability` classification. Its
generic translation computes that classification when adding early lifetime
parameters.

The pinned `lifetime-mutability` golden test demonstrates the result. A struct

```rust
struct A<'a, 'b> {
    x: &'a mut u32,
    y: &'b u32,
    z: Box<&'b mut u32>,
}
```

is printed with both parameters marked mutable because both lifetimes are used,
possibly recursively, by mutable borrows. A wrapper type propagates that
classification.

This is additional lifetime-derived structure beyond mere names/outlives edges,
and Aeneas later uses corresponding type analysis when deciding which values a
backward function must consume or return.

Basis: **source** + **source (checked-in golden artifact)**.

### Aeneas keeps Charon's region model at its LLBC boundary

Aeneas's `src/llbc/Types.ml` directly includes `Charon.Types`. Its LLBC
utilities therefore operate on Charon's region-bearing types.

Aeneas contains numerous operations whose precondition is specifically that
regions still exist:

- collect free regions from a type;
- determine whether a mutable borrow belongs to a chosen region set;
- find which ADT region parameters correspond to mutable borrows;
- refresh erased/body regions to fresh free IDs for analysis;
- compute outlives relationships within projected types.

This is direct evidence that regions have semantic work to do inside Aeneas
before pure extraction.

Basis: **source**, `src/llbc/Types.ml`, `TypesUtils.ml`, and
`TypesAnalysis.ml`.

### Aeneas intentionally erases most body-region identity early

Before borrow checking or translation, `Main.ml` runs
`PrePasses.apply_passes`. The second per-function pass is
`erase_body_regions`.

Its contract says:

- erase body regions in locals and places;
- keep those used in function calls.

The implementation erases `RBody`, `RVar`, and `RStatic` from ordinary
statement types and erases regions from local declarations. It overrides
visitation of function operands so call-site generic arguments are left intact.

This means Aeneas does **not** attempt to carry Charon's fresh body-region identity
uniformly through symbolic execution. It keeps the pieces needed to instantiate
callee signatures while treating most local body-region annotations as
dispensable.

Basis: **source**, `src/PrePasses.ml` and `src/Main.ml`.

### Signature lifetimes are converted into region groups and parent relationships

For each function signature, Aeneas computes a region hierarchy rather than
simply dropping the signature regions.

`RegionsHierarchy.compute_regions_hierarchy_for_sig` starts with the
signature-level region variables and `'static`, adds outlives edges, and
computes strongly connected components. Two regions that mutually outlive one
another fall into one group. Each resulting `region_var_group` records:

- a region-group ID;
- the member region IDs; and
- parent region-group IDs derived from the SCC dependency graph.

The analysis considers the signature's explicit region-outlives and type-outlives
predicates and derives additional constraints from input/output types where
needed. It explicitly does not yet handle all locally bound-region cases.

The symbolic signature representation keeps both the hierarchy and a parallel
hierarchy of abstraction IDs. Substitution refreshes concrete region IDs while
preserving group IDs and parent relationships.

Basis: **source**, `src/llbc/RegionsHierarchy.ml`,
`src/llbc/LlbcAst.ml`, and `src/llbc/Substitute.ml`.

### Region groups drive symbolic borrow abstractions

When Aeneas initializes symbolic execution for a function, it instantiates the
function signature, records its region groups in the evaluation context, and
creates an input abstraction for every region group. Input symbolic values are
projected into these abstractions as loans.

When synthesizing a backward function, Aeneas uses the region hierarchy to find
parent groups, creates return abstractions, projects returned borrows into the
appropriate groups, and ends the selected input abstractions in hierarchy order.
The source explicitly notes that controlling which regions can end is important
for soundness and is part of borrow checking.

Thus the lifetime graph is consumed operationally before the final pure
representation forgets region names.

Basis: **source**, `src/interp/Interp.ml`.

### Pure Aeneas types have no region parameter or reference constructor

The erasure becomes explicit at the LLBC-to-pure translation boundary.

In `SymbolicToPureTypes.ml`:

- `translate_region_binder` discards the region binder and translates only its
  value;
- `translate_generic_args` says “We ignore the regions” and emits only types,
  const generics, and trait references;
- `translate_generic_params` destructures `regions = _` and emits no region
  parameters;
- signature/type translation maps `TRef (_, referent, _)` to the translation
  of the referent.

The pure AST confirms the result structurally. `Pure.generic_args` has
`types`, `const_generics`, and `trait_refs`; `Pure.generic_params` has
type parameters, const-generic parameters, and trait clauses. `Pure.ty` has no
reference constructor and no region-bearing variant.

This is the exact point at which lifetimes cease to be first-class type
parameters in the generated pure program.

Basis: **source**, `src/symbolic/SymbolicToPureTypes.ml` and
`src/pure/Pure.ml`.

### Borrow effects survive as forward/backward function structure

Pure types omit references, but Aeneas computes the pure signature using the
region hierarchy first. Its decomposed function type contains a map from
`RegionGroupId` to backward-signature information. The backward signature
specifies the values consumed and given back for that region group.

For a mutable reference, the referent type is therefore passed as an ordinary
pure value and an updated referent is returned through the backward interface.
For a function returning a mutable borrow, the forward result can include a
backward closure that later reconstructs the affected inputs.

The pinned source includes a concrete checked-in example:

```rust
pub fn choose<'a, T>(
    b: bool,
    x: &'a mut T,
    y: &'a mut T,
) -> &'a mut T
```

becomes in `tests/lean/Paper.lean`:

```lean
def choose
  {T : Type} (b : Bool) (x : T) (y : T) :
  Result (T × (T → (T × T))) := ...
```

The returned closure remembers whether `x` or `y` supplied the borrow and,
when given the mutated returned value, reconstructs the pair of updated inputs.
There is no Lean lifetime parameter, but the Rust borrowing relationship has
changed the generated function's value-level interface.

Likewise, Rust `fn incr(x: &mut u32)` is checked in as a Lean function
`Std.U32 -> Result Std.U32`: the referent value is the input and its updated
state is the output.

Basis: **source (checked-in Rust and generated Lean artifacts)**,
`tests/src/paper.rs`, `tests/lean/Paper.lean`,
`tests/src/no_nested_borrows.rs`, and
`tests/lean/NoNestedBorrows.lean`.

### Some LLBC region metadata survives alongside the pure program

Aeneas does not discard every trace of the original LLBC region declarations
from its extraction context.

Pure type/function declarations retain an `llbc_generics` field alongside the
region-free pure generics. Extraction uses the original LLBC information for
naming. For Lean `rust_type` metadata, `ExtractTypes.ml` computes a
`mutRegions` attribute containing the positions of original lifetime
parameters that Aeneas's type analysis classifies as mutable.

The extraction code also acknowledges a limitation of its erasure strategy: it
retains Charon's binding levels but “forgot all the region binders,” so some
De Bruijn levels are no longer rigorously correct. Current code relies on its
restricted binder patterns instead.

Therefore “regions are erased” should be scoped to the pure semantic type
language. Auxiliary LLBC metadata can remain for naming, Rust correspondence,
and extraction attributes.

Basis: **source**, `src/pure/Pure.ml`,
`src/extract/ExtractBase.ml`, and `src/extract/ExtractTypes.ml`.

### What does not cross from rustc into Charon/Aeneas

The pipeline does not carry rustc's full NLL solution into Charon or Aeneas.

Rustc's borrow checker has precise inference data mapping NLL region variables to
sets of CFG locations/universal regions. Charon's ordinary extraction path does
not read that analysis. It instead starts from pre-borrow-check MIR plus rustc
type/signature information, preserves declared regions, and synthesizes fresh
body-region IDs for erased occurrences. Aeneas then performs its own
region/type analyses and symbolic borrow translation over Charon's representation.

Accordingly, two statements must be kept separate:

1. rustc accepted the program after its own NLL borrow analysis; and
2. Aeneas's region abstractions faithfully model every lifetime/resource fact
   needed for the property being proved.

The first does not establish the second. Connecting the two is a semantic
adequacy/soundness question, particularly important once unsafe Rust is in scope.

Basis: **derived** from the exact rustc, Charon, and Aeneas dataflow above.

## Boundaries

- **No fresh execution was performed.** All behavioral examples are checked-in
  golden/generated artifacts at the pinned revisions, not observations produced
  by this research run.
- **No equivalence to rustc NLL is established.** Charon body-region IDs are
  fresh placeholders introduced from erased regions. This report does not claim
  that they reproduce rustc's inferred region values or constraint graph.
- **Aeneas soundness is not established here.** The report shows where Aeneas
  uses and erases region information; it does not prove that the resulting
  functionalization is semantically adequate for all Rust programs, especially
  unsafe Rust.
- **Rustc region provenance before promoted MIR is not exhaustively cataloged.**
  The report follows the representations relevant to Charon's selected query and
  rustc borrow checking. It does not attempt a complete HIR/THIR lifetime-lowering
  reference.
- **Locally bound/higher-ranked lifetime support has explicit limitations.**
  Aeneas's region hierarchy says locally bound regions are not fully handled;
  `SymbolicToPureTypes.translate_region_binder` notes that dropping region
  binders makes some De Bruijn levels wrong, tolerated because complex binding
  situations are not yet supported.
- **Static/body-region cases are not uniformly supported in later Aeneas
  translation.** Several translation paths reject unexpected `RStatic`,
  `RErased`, bound regions, or `RBody` once they expect normalized free
  signature regions.
- **The checked-in Lean examples establish concrete translation specimens, not
  a complete translation matrix.** They demonstrate the lifetime-erasure and
  backward-function pattern for representative mutable borrows.
- **This report does not replace the separate source-correspondence or ownership/
  provenance reports.** Lifetimes/regions are only one part of Rust's resource
  semantics.

## Evidence

**Source — Anneal toolchain selection.**
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix`: Rust date `2026-05-31`, Aeneas release
`nightly-2026.06.03`.

**Source — rustc region forms.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`,
`compiler/rustc_middle/src/ty/region.rs`: region constructors and predicates
for early/bound/late/static/inference/placeholder/erased regions.

**Source — rustc NLL working copy and solution.**
Same rustc revision:
`compiler/rustc_borrowck/src/lib.rs` around
`borrowck_collect_region_constraints`;
`src/nll.rs::replace_regions_in_mir` and `compute_regions`;
`src/renumber.rs::renumber_mir`;
`src/universal_regions.rs::UniversalRegions`; and
`src/region_infer/mod.rs::RegionInferenceContext`.
These sources establish that borrow checking clones MIR, renumbers regions in
that copy, and keeps solved region values in borrow-check analysis state.

**Source — Charon extraction timing and MIR level.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`charon/src/bin/charon-driver/driver.rs`,
`translate/get_mir.rs`, and `charon/src/options.rs`.
The driver extracts before MIR analysis; local default/Aeneas translation uses
promoted MIR.

**Source — Charon region representation and translation.**
Same Charon revision:
`charon/src/ast/types.rs`, `ast/types/vars.rs`,
`translate/translate_types.rs`, and
`translate/translate_generics.rs`.
These define declared, body, static, and erased regions; signature predicates;
lifetime mutability; and fresh body-region creation.

**Source — Charon checked-in specimens.**
Same Charon revision:
`charon/tests/ui/region-inference-vars.{rs,out}`,
`charon/tests/ui/monomorphization/bound_lifetime.{rs,out}`,
`charon/tests/ui/lifetime-mutability.{rs,out}`, and
`charon/tests/ui/no_nested_borrows.{rs,out}`.
They are preserved golden output, not fresh execution in this run.

**Source — Aeneas LLBC region processing.**
`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
`src/llbc/Types.ml`, `TypesUtils.ml`, `TypesAnalysis.ml`,
`RegionsHierarchy.ml`, `LlbcAst.ml`, `Substitute.ml`,
`src/PrePasses.ml`, and `src/interp/Interp.ml`.

**Source — Aeneas pure erasure.**
Same Aeneas revision:
`src/symbolic/SymbolicToPureTypes.ml`,
`src/pure/Pure.ml`,
`src/extract/ExtractBase.ml`, and
`src/extract/ExtractTypes.ml`.

**Source — Aeneas checked-in Rust/Lean specimens.**
Same Aeneas revision:
`tests/src/paper.rs` with `choose`,
`tests/lean/Paper.lean` with the generated `choose` and backward closure,
`tests/src/no_nested_borrows.rs` with `incr`/`read_then_incr`, and
`tests/lean/NoNestedBorrows.lean` with their region-free pure forms.
These are preserved repository artifacts rather than newly observed executions.

**Derived.**
Because Charon extracts before rustc's private NLL working-copy analysis and
does not consume `RegionInferenceContext`, its synthetic body-region IDs cannot
be treated as rustc's NLL solution. Because Aeneas computes region-group-driven
borrow interfaces before its pure AST discards lifetime parameters, pure lifetime
erasure does not imply that lifetimes were irrelevant to translation.

## Revalidation

For a later Rust/Charon/Aeneas combination, the cheapest source-level
revalidation is:

1. In rustc, inspect the borrow-check entry point, `replace_regions_in_mir`,
   `renumber_mir`, `UniversalRegions`, and `RegionInferenceContext`.
   Confirm whether NLL still operates on a private MIR copy and where solved
   region values live.
2. In Charon, inspect its rustc callback timing, selected MIR query, `Region`
   enum, `translate_region`, and `translate_erased_region`. Determine whether
   Charon has begun consuming borrow-check facts or still synthesizes body
   regions independently.
3. Diff the Charon lifetime golden outputs for a signature lifetime, a body-local
   borrow, a call-site lifetime argument, and ADT lifetime mutability.
4. In Aeneas, inspect `erase_body_regions`,
   `RegionsHierarchy.compute_regions_hierarchy_for_sig`,
   symbolic signature instantiation, and `SymbolicToPureTypes`. Confirm which
   region information is consumed before pure erasure.
5. Inspect the pure AST definition itself. A change that adds region/reference
   constructors would materially change this report's erasure conclusion.
6. Diff the generated `Paper.lean` `choose` specimen. Record whether the
   source lifetime remains absent and how the backward interface represents the
   mutable-borrow effect.

On a surface capable of running the toolchain, add a small cross-layer fixture
with:

- one named signature lifetime;
- two independent named lifetimes;
- an elided local reborrow;
- a function call carrying a reborrow;
- one mutable borrow returned from the function; and
- one outlives clause.

Preserve the rustc promoted MIR, borrow-check renumbered MIR/NLL dump, Charon
ULLBC/LLBC, and Aeneas Lean output. Compare identities rather than only pretty
names. In particular, determine which Charon body regions correspond merely to
fresh erased-region occurrences and whether any mapping to rustc NLL variables
exists.

Such a probe would establish the concrete transformation for those fixtures at
that revision. It would **not** prove that Charon/Aeneas's lifetime model is
semantically equivalent to rustc borrow checking for arbitrary Rust, nor would
it by itself establish unsafe-Rust soundness.
