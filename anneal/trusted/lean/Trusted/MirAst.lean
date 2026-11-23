-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
module
prelude
public import Trusted.MirAst.Types
public import Trusted.MirAst.Places
public import Trusted.MirAst.Rvalues
public import Trusted.MirAst.Statements
public import Trusted.MirAst.Terminators
public import Trusted.MirAst.Body

/-!
# Anneal MIR Abstract Syntax (`Trusted.MirAst`)

Re-exports the modular captured `Runtime(PostCleanup)` MIR AST submodules under
`Trusted.MirAst.*` (`Types`, `Places`, `Rvalues`, `Statements`, `Terminators`,
and `Body`).

## Human-Comprehension Priority

`Trusted.MirAst` sits in the direct transitive dependency cone of Anneal's
top-level verification obligations (`CrateTheorem`, `UnitTheorem`,
`ProgramVerified`, and `BodyVerified` in `Trusted.MirSemantics`) as well as
the correspondence theorem statements (`CorrespondenceClaim` and
`FaultEquivalenceClaim` in `Trusted.Correspondence`). Human comprehension is
therefore the governing design priority for every declaration in this tree:

1. **Direct, self-evident representations:** Every AST type and constructor is
   written in plain, first-order inductive form without clever encodings or
   indirect index indirections, so a human reviewer can see at a glance that the
   syntax means in mathematical terms what it means in intuitive Rust MIR terms.
2. **Explicit fail-closed boundaries (`.unsupported`):** Every syntax category
   with unmodeled `rustc` variants either includes an explicit `.unsupported`
   constructor or documents where unmodeled variants are handled (`Operand`
   relies on capture rejecting `RuntimeChecks`, and `ConstLit` handles
   non-scalar constants one level up), and every comment documents both the
   modeled and unmodeled upstream `rustc_middle::mir` variants.
3. **Pinned upstream citations:** Every modeled AST type and operator
   declaration cites (and, where helpful for auditing, quotes) the
   corresponding `rust-lang/rust` definition at `vendor/lean-miri`'s upstream
   `rustc` commit `8144389c895da997dbdecaa635e41d6a50be6ffd` (and, where
   relevant, `rust-lang/reference` commit
   `a286e1ecb8ce193d50056e4bb042eea9b23876ef`, pinned by
   `rust-lang/rust@8144389c`'s `src/doc/reference` submodule, and
   `anneal-rustc-capture`'s pinned `rustc` commit
   `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).

## Correspondence with `rustc_middle::mir`

These modules define the trusted abstract syntax tree for post-cleanup runtime
Mid-level Intermediate Representation (`Runtime(PostCleanup)` MIR) extracted by
`anneal-rustc-capture`, corresponding to
`compiler/rustc_middle/src/mir/syntax.rs` and
`compiler/rustc_middle/src/mir/mod.rs` in `rust-lang/rust` at commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`:

> "The lowered representation of a single function."
>
> "The first local is the return value pointer, followed by `arg_count`
> locals for the function arguments, followed by any user-declared
> variables and temporaries."
> (`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
> `8144389c895da997dbdecaa635e41d6a50be6ffd`)

Unlike `rustc_middle::mir` (which interns types into `TyCtxt` as `Ty<'tcx>`)
and `lean-miri` (`Miri.MIR.Syntax`, which indexes a side-table of interned
types via `TyId`), `Trusted.MirAst` carries structural `MirTy` descriptors
directly by value on `Body.locals`, `ConstOperand`, and
`ProjectionElem.field`. This eliminates out-of-bounds `TyId` lookup states
inside $M_{\text{anneal}}$ and allows `Anneal.MirWp` to evaluate operand and
local types structurally without threading a global type table.

## Declaration Modifiers

Every `def` and term-level `abbrev` in `Trusted.MirAst` and
`Trusted.MirSemantics` carries `noncomputable`. For a computable recursive
definition (such as `natListBeq` or `MirTy.beq`), Lean adds a `._unsafe_rec`
compiler helper marked `partial`, and `TrustedBoundary.validateRepoConstant`
rejects every `partial` constant; `noncomputable` stops Lean from adding the
helper. Any non-recursive value definition that calls a `noncomputable` helper
(such as `checkVal` or `BodyStaticAdmitted`) also requires `noncomputable` in
Lean 4 (otherwise compilation fails with `dependsOnNoncomputable`). Because
`TrustedBoundary.inspectNodeKind` forbids `noncomputable section`, each
declaration carries the modifier itself. Remaining non-recursive value
definitions that do not call `noncomputable` helpers, together with
`Prop`-valued definitions, carry `noncomputable` by uniform convention so one
rule covers every definition and adding recursion or a call to a `noncomputable`
helper never requires a modifier change. Type abbreviations such as `DefId`
define types rather than terms and carry no modifier.
-/
