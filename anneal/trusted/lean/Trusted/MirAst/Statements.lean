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
- `.nop` corresponds to `StatementKind::Nop`, and to
  `StatementKind::PlaceMention(place)` when `place` is an unprojected,
  in-bounds `Sized` local (enforced during capture by `anneal-rustc-capture`).
  In `rustc_const_eval` (`compiler/rustc_const_eval/src/interpret/step.rs` and
  `place.rs`, `rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`) and
  `vendor/lean-miri/` (`Miri.Interpreter.Step.evalStatement` /
  `localToPlace`):

  > "PlaceMention(place) => {
  >     let _ =
  >         self.eval_place(**place, /* skip_validity_for_simple_deref */ false)?;
  > }"
  > (`compiler/rustc_const_eval/src/interpret/step.rs#L119-L122`)
  >
  > "let layout = self.layout_of_local(frame, local, None)?;
  > let place = if layout.is_sized() {
  >     // We can just always use the `Local` for sized values.
  >     Place::Local { local, offset: None, locals_addr: frame.locals_addr() }
  > } else {
  >     // Other parts of the system rely on `Place::Local` never being unsized.
  >     match frame.locals[local].access()? {
  >         Operand::Immediate(_) => bug!(),
  >         Operand::Indirect(mplace) => Place::Ptr(*mplace),
  >     }
  > };"
  > (`compiler/rustc_const_eval/src/interpret/place.rs#L581-L591`)

  Because `layout_of_local` checks only local bounds and type layout without
  checking liveness or reading memory, an unprojected `PlaceMention` of an
  in-bounds `Sized` local is an exact operational no-op.
- `.unsupported` represents `StatementKind::PlaceMention` on any projected
  place or unsized local, and all other `StatementKind` variants (`FakeRead`,
  `SetDiscriminant`, `AscribeUserType`, `Coverage`, `Intrinsic`,
  `ConstEvalCounter`, and `BackwardIncompatibleDropHint`). -/
inductive StatementKind where
  | assign (dst : Place) (rvalue : Rvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | nop
  | unsupported

end Trusted.MirAst
