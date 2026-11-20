-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
prelude
import Init.NotationExtra
import Trusted.MirAst.Types
import Trusted.MirAst.Places
import Trusted.MirAst.Rvalues

namespace Trusted.MirAst

/-!
# MIR Statements (`Trusted.MirAst.Statements`)

Basic-block statements for captured `Runtime(PostCleanup)` MIR.
-/

/-- A MIR statement inside a basic block (`rustc_middle::mir::StatementKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum StatementKind<'tcx> {
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
>     FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
>     SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
>     StorageLive(Local),
>     StorageDead(Local),
>     PlaceMention(Box<Place<'tcx>>),
>     AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, ty::Variance),
>     Coverage(CoverageKind),
>     Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
>     ConstEvalCounter,
>     Nop,
>     BackwardIncompatibleDropHint { ... },
> }"

Constructor correspondence:
- `.assign dst rvalue` corresponds to `StatementKind::Assign((dst, rvalue))`.
- `.storageLive localId` corresponds to `StatementKind::StorageLive(localId)`.
- `.storageDead localId` corresponds to `StatementKind::StorageDead(localId)`.
- `.nop` corresponds to `StatementKind::Nop`.
- `.unsupported` represents all other `StatementKind` variants (`FakeRead`,
  `SetDiscriminant`, `PlaceMention`, `AscribeUserType`, `Coverage`, `Intrinsic`,
  `ConstEvalCounter`, and `BackwardIncompatibleDropHint`). -/
inductive StatementKind where
  | assign (dst : Place) (rvalue : Rvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

end Trusted.MirAst
