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
public import Init.NotationExtra
public import Init.Data.ByteArray.Bootstrap
public import Init.Data.List.Basic
public import Trusted.MirAst.Types
public import Trusted.MirAst.Statements
public import Trusted.MirAst.Terminators

@[expose] public section

namespace Trusted.MirAst

/-!
# MIR Basic Blocks, Bodies, and Programs (`Trusted.MirAst.Body`)

Control-flow blocks, function bodies, verification scope, and program containers
for captured `Runtime(PostCleanup)` MIR.
-/

/-- A MIR basic block (`rustc_middle::mir::BasicBlockData` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct BasicBlockData<'tcx> {
>     pub statements: Vec<Statement<'tcx>>,
>     pub after_last_stmt_debuginfos: StmtDebugInfos<'tcx>,
>     pub terminator: Option<Terminator<'tcx>>,
>     pub is_cleanup: bool,
> }"

Sequential `statements` followed by a `terminator` and the `cleanup`
(`is_cleanup`) unwind-pad marker. -/
structure BasicBlock where
  statements : List StatementKind
  terminator : TerminatorKind
  cleanup : Bool := false

/-- A MIR function body (`rustc_middle::mir::Body` in
`compiler/rustc_middle/src/mir/mod.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct Body<'tcx> {
>     pub basic_blocks: BasicBlocks<'tcx>,
>     pub phase: MirPhase,
>     pub pass_count: usize,
>     pub source: MirSource<'tcx>,
>     pub source_scopes: IndexVec<SourceScope, SourceScopeData<'tcx>>,
>     pub coroutine: Option<Box<CoroutineInfo<'tcx>>>,
>     pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
>     pub user_type_annotations: ty::CanonicalUserTypeAnnotations<'tcx>,
>     pub arg_count: usize,
>     pub spread_arg: Option<Local>,
>     ...
> }"

Local slot layout (`compiler/rustc_middle/src/mir/mod.rs`):
- Local `0` (`_0`) is the return place (`locals[0]`).
- Locals `1 .. argumentCount` are the function parameters
  (`locals[1..=argumentCount]`).
- Locals `> argumentCount` are temporaries and user-declared locals.
- `isUnsafe` records whether the function signature has
  `rustc_hir::Safety::Unsafe` (`compiler/rustc_hir/src/hir.rs`, `rust-lang/rust`
  `8144389c895da997dbdecaa635e41d6a50be6ffd`):

  > "pub enum Safety {
  >     ...
  >     #[default]
  >     Unsafe,
  >     Safe,
  > }"

  Only bodies with `isUnsafe = true` may assume a caller-supplied safety
  precondition in `Trusted.MirSemantics.BodyVerified`.
- `identity` records a producer-supplied definition identity string (such as
  `TyCtxt::def_path_str` in `compiler/rustc_middle/src/ty/print/pretty.rs`,
  line 2193, `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`, which
  is intended for user output rather than guaranteed unique) used to index
  `Trusted.MirSemantics.Specs.safety`. Single-body unit test fixtures that do
  not use `BodyVerified` / `ProgramVerified` may leave the default
  `identity := ""`; `BodyStaticAdmitted` rejects empty `identity` strings and
  `ProgramVerified` enforces pairwise-distinct identities across all bodies in
  `Program.bodies` (failing closed on any collision) so two functions can never
  silently alias in `Specs.safety`.
-/
structure Body where
  argumentCount : Nat
  locals : List MirTy
  basicBlocks : List BasicBlock
  isUnsafe : Bool := false
  identity : String := ""

/-- Total, kernel-reducible UTF-8 string concatenation used by
`anneal-rustc-capture` to balance long function identities into `<= 16`-char
`String.ofList` leaves so Lean kernel reduction stays `O(log L)` instead of
hitting `maxRecDepth` inside `List.utf8Encode`.

Intentionally omits `noncomputable` (with zero recursion and zero
`._unsafe_rec` helpers) so captured `Captured.body_*` constants remain plain
computable `def`s. -/
def stringAppend (a b : String) : String :=
  ⟨a.toByteArray.append b.toByteArray,
    match a.isValidUTF8, b.isValidUTF8 with
    | ByteArray.IsValidUTF8.intro m1 hm1, ByteArray.IsValidUTF8.intro m2 hm2 =>
      ⟨m1 ++ m2,
        Eq.trans (congrArg (fun x => x.append b.toByteArray) hm1)
          (Eq.trans (congrArg (fun y => (List.utf8Encode m1).append y) hm2)
            (Eq.symm
              (Eq.trans
                (congrArg List.toByteArray
                  (@List.flatMap_append _ _ m1 m2 String.utf8EncodeChar))
                (@List.toByteArray_append'
                  (m1.flatMap String.utf8EncodeChar)
                  (m2.flatMap String.utf8EncodeChar)))))⟩⟩

/-- Capture scope of a `Program`, distinguishing whole-crate verification
(`.crate`, covering every executable body in the compiled crate via
`Trusted.MirSemantics.CrateTheorem`) from selected proof-unit verification
(`.unit`, covering a designated root item and its captured dependencies via
`Trusted.MirSemantics.UnitTheorem`).

Whether a `.crate` capture actually includes every executable body and
reachable callee in the compiled crate is an external obligation of the
capture producer (such as a future `anneal-rustc-capture` emitter), not
checked by the Lean semantics alone. -/
inductive VerificationScope where
  | unit
  | crate

/-- A complete MIR program unit: function bodies indexed by `DefId`, an entry
function `entryDefId`, the captured target's pointer width `pointerWidthBits`
and byte order `targetEndian`, the MIR semantic profile version
`mirProfileVersion`, and the capture scope `scope`.

1. **Target pointer width (`pointerWidthBits`):**
   `pointerWidthBits` records the target layout that `rustc` used when it
   lowered the program. `rustc` sizes `isize` and `usize` by the target data
   layout's pointer width (`compiler/rustc_middle/src/ty/layout.rs` and
   `compiler/rustc_abi/src/lib.rs`, `rust-lang/rust`
   `8144389c895da997dbdecaa635e41d6a50be6ffd`):

   > "ty::IntTy::Isize => cx.data_layout().ptr_sized_integer(),"
   > (`IntegerExt::from_int_ty`)
   >
   > "match self.pointer_offset().bits() { 16 => I16, 32 => I32, 64 => I64, ..."
   > (`TargetDataLayout::ptr_sized_integer`)

   `IntWidth.byteSize` fixes `isize`/`usize` at 8 bytes, so the semantics models
   only 64-bit targets. `Trusted.MirSemantics.initState` and
   `Trusted.Correspondence.initRefState` reject any program whose
   `pointerWidthBits` is not `64` with `FaultKind.unsupported` (`.blocked`).

2. **Target byte order (`targetEndian`):**
   `targetEndian` records the target's `rustc_abi::Endian` (`Little` or `Big`)
   from `tcx.data_layout.endian`. Memory loads and stores (`loadIndirect`,
   `storeIndirect`) and `Trusted.Correspondence`'s
   `Miri.ABI.RuntimeTargetDataLayout` use `p.targetEndian` explicitly.

3. **MIR semantic profile version (`mirProfileVersion`):**
   `mirProfileVersion` pins the contract version of the post-cleanup runtime MIR
   semantic profile shared between `anneal-rustc-capture` (`rust-lang/rust`
   `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `Trusted.MirSemantics`, and
   `Trusted.Correspondence` (`vendor/lean-miri` upstream `rustc` reference
   `8144389c895da997dbdecaa635e41d6a50be6ffd`). Both `initState` and
   `initRefState` fail closed with `FaultKind.unsupported` (`.blocked`)
   whenever `p.mirProfileVersion ≠ 1`.

**Producer obligations:** `Program.pointerWidthBits`, `Program.targetEndian`,
`Program.mirProfileVersion`, and `Program.scope` carry no defaults so every
`Program` literal (both hand-written canaries and serialized captures) must
state the target layout, byte order, profile contract, and intended
verification scope explicitly rather than silently inheriting accepted,
big/little-endian, or `.unit` values.
The remaining Lean field defaults across `Trusted.MirAst` exist solely for
concise hand-written canary literals. Two defaults equal unprojected/non-cleanup
values (`BasicBlock.cleanup := false` and `Place.projection := []`), and
`Program.entryDefId := 0` selects body `0` as the entry point. The remaining
two defaults (`Body.isUnsafe := false` and `Body.identity := ""`) fail closed
(`isUnsafe := false` withholds caller safety preconditions, and `identity := ""`
is rejected by `BodyStaticAdmitted`). Any serializer or MIR producer (such as
`anneal-rustc-capture`) MUST explicitly populate all of these fields—
`pointerWidthBits` and `targetEndian` (from the compiled target's data layout),
`mirProfileVersion` (from the capture profile contract), `scope`, `entryDefId`,
`Body.isUnsafe`, `Body.identity`, `BasicBlock.cleanup` (from
`BasicBlockData::is_cleanup`), and `Place.projection` (from
`Place::projection`). Likewise, when `scope = .crate`, completeness of `bodies`
(ensuring every executable body and reachable callee in the crate is included)
is an external producer obligation, not checked by `Trusted.MirSemantics`
alone. -/
structure Program where
  bodies : List Body
  entryDefId : DefId := 0
  pointerWidthBits : Nat
  targetEndian : TargetEndian
  mirProfileVersion : Nat
  scope : VerificationScope

end Trusted.MirAst

end
