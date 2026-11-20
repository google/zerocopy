// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure rendering of the owned syntax. Every emitted token is fixed here or is
//! a numeric/Boolean literal. Function identities use numeric Unicode scalar
//! constructors, so names never enter the emitted command or literal syntax.

use crate::ir::{self, BinOp, ConstLit, Operand, Rvalue, Statement, Terminator, Ty};

const HEADER: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n\
prelude\nimport Trusted.MirAst\n\nnamespace Captured\n\n";

fn list<T>(values: &[T], render: impl Fn(&T) -> String) -> String {
    format!(
        "[{}]",
        values.iter().map(render).collect::<Vec<_>>().join(", ")
    )
}

fn ty(t: &Ty) -> String {
    match t {
        Ty::Bool => "Trusted.MirAst.MirTy.bool".into(),
        Ty::Unit => "Trusted.MirAst.MirTy.unit".into(),
        Ty::Never => "Trusted.MirAst.MirTy.never".into(),
        Ty::Int(ity) => format!(
            "(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.{} {})",
            ity.width.lean_name(),
            ity.signed
        ),
        Ty::Enum(ety) => {
            let tag_repr = match ety.tag_repr() {
                ir::EnumTagRepr::ZeroSized => "Trusted.MirAst.EnumTagRepr.zeroSized".into(),
                ir::EnumTagRepr::Scalar(tag) => format!(
                    "(Trusted.MirAst.EnumTagRepr.scalar Trusted.MirAst.IntWidth.{} {})",
                    tag.width.lean_name(),
                    tag.signed
                ),
            };
            let discr = ety.discr();
            format!(
                "(Trusted.MirAst.MirTy.enum {{ id := {}, discrWidth := Trusted.MirAst.IntWidth.{}, discrSigned := {}, tagRepr := {tag_repr}, discriminants := {} }})",
                ety.id(),
                discr.width.lean_name(),
                discr.signed,
                list(ety.discriminants(), u64::to_string)
            )
        }
    }
}

fn const_lit(lit: ConstLit) -> String {
    match lit {
        ConstLit::ZeroSized => "Trusted.MirAst.ConstLit.zeroSized".into(),
        ConstLit::Scalar { bits } => {
            format!("(Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 {bits}))")
        }
    }
}

fn operand(op: &Operand) -> String {
    match op {
        Operand::Copy { local } => {
            format!("(Trusted.MirAst.Operand.copy (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Move { local } => {
            format!("(Trusted.MirAst.Operand.move (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Constant { ty: t, lit } => format!(
            "(Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk {} {}))",
            ty(t),
            const_lit(*lit)
        ),
    }
}

fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::BitAnd => "bitAnd",
        BinOp::BitOr => "bitOr",
        BinOp::BitXor => "bitXor",
        BinOp::Shl => "shl",
        BinOp::Shr => "shr",
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
    }
}

fn rvalue(value: &Rvalue) -> String {
    match value {
        // Render `Rvalue::Aggregate(Tuple, [])` 1:1 to `.aggregateTuple []`
        // without desugaring to a constant use; `MirSemantics.evalRvalue`
        // fails closed on `.aggregateTuple` until tuple aggregates are
        // modeled.
        Rvalue::Unit => "(Trusted.MirAst.Rvalue.aggregateTuple [])".into(),
        // `ir::Body::try_new` admits `with_retag == true` only when the
        // destination type satisfies `Ty::is_retag_noop()`.
        Rvalue::Use { operand: op, .. } => {
            format!("(Trusted.MirAst.Rvalue.use {})", operand(op))
        }
        Rvalue::Binary { op, left, right } => format!(
            "(Trusted.MirAst.Rvalue.binaryOp Trusted.MirAst.BinOp.{} {} {})",
            bin_op(*op),
            operand(left),
            operand(right)
        ),
        Rvalue::Discriminant { local } => {
            format!("(Trusted.MirAst.Rvalue.discriminant (Trusted.MirAst.Place.mk {local} []))")
        }
    }
}

fn statement(stmt: &Statement) -> String {
    match stmt {
        Statement::Assign { local, value } => format!(
            "(Trusted.MirAst.StatementKind.assign (Trusted.MirAst.Place.mk {local} []) {})",
            rvalue(value)
        ),
        Statement::StorageLive { local } => {
            format!("(Trusted.MirAst.StatementKind.storageLive {local})")
        }
        Statement::StorageDead { local } => {
            format!("(Trusted.MirAst.StatementKind.storageDead {local})")
        }
        Statement::Nop => "Trusted.MirAst.StatementKind.nop".into(),
    }
}

fn terminator(term: &Terminator) -> String {
    match term {
        Terminator::Goto { block } => {
            format!("(Trusted.MirAst.TerminatorKind.goto {block})")
        }
        Terminator::SwitchInt {
            operand: op,
            targets,
            otherwise,
        } => format!(
            "(Trusted.MirAst.TerminatorKind.switchInt {} (Trusted.MirAst.SwitchTargets.mk {} {otherwise}))",
            operand(op),
            list(targets, |(value, block)| format!(
                "((BitVec.ofNat 128 {value}), {block})"
            ))
        ),
        Terminator::Ret => "Trusted.MirAst.TerminatorKind.return_".into(),
        Terminator::Unreachable => "Trusted.MirAst.TerminatorKind.unreachable".into(),
    }
}

/// Construct a Lean string without interpolating its contents into Lean syntax.
/// The identity selects a reviewed safety predicate, so it must enter the
/// logical subject without gaining authority to add commands or change names.
/// Rust characters are Unicode scalar values; numeric Char constructors retain
/// them even when a name contains quotes, backslashes or other syntax. This
/// keeps every emitted token fixed or numeric and requires no escaping grammar.
fn identity(value: &str) -> String {
    let characters: Vec<_> = value.chars().collect();
    format!(
        "(_root_.String.ofList {})",
        list(&characters, |ch| format!(
            "(_root_.Char.ofNat {})",
            u32::from(*ch)
        ))
    )
}

fn body(body: &ir::Body) -> String {
    format!(
        "({{ argumentCount := {}, isUnsafe := {}, locals := {}, basicBlocks := {}, identity := {} }} : Trusted.MirAst.Body)",
        body.arg_count(),
        body.is_unsafe(),
        list(body.local_tys(), ty),
        list(body.blocks(), |block| format!(
            "({{ statements := {}, terminator := {}, cleanup := false }} : Trusted.MirAst.BasicBlock)",
            list(&block.statements, statement),
            terminator(&block.terminator)
        )),
        identity(body.identity())
    )
}

/// Target pointer width and MIR semantic profile version pinned by capture
/// (`capture.rs` refuses any target that is not 64-bit little-endian, matching
/// `Trusted.MirAst.Program`).
const POINTER_WIDTH_BITS: u32 = 64;
const MIR_PROFILE_VERSION: u32 = 1;

/// Entry body index of every captured program. `Trusted.MirAst.Program` gives
/// `entryDefId` a default only for hand-written canaries; its producer
/// obligations say omitting it "silently selects body `0` as the entry
/// point" and require producers to populate it explicitly. Body `0` always
/// exists because `ir::Program::try_new` refuses empty programs, so the
/// `entryDefId < bodies.length` check in `ProgramVerified` holds. That
/// judgment verifies each body through `entryProgForBody`, which replaces
/// this field; a specification that reads the program's own entry sees the
/// first captured body.
const ENTRY_DEF_ID: u32 = 0;

/// Render data constructors under one fixed module/definition skeleton.
/// Capture emits a subject, not a proof or a dynamically chosen theorem. The
/// verifier separately authenticates this source and checks the authored root;
/// neither diagnostics nor census text can add commands through this renderer.
pub fn render(program: &ir::Program) -> String {
    let scope = match program.scope() {
        ir::Scope::SelectedUnit { .. } => "unit",
        ir::Scope::Crate => "crate",
    };
    format!(
        "{HEADER}def program : Trusted.MirAst.Program :=\n  {{ pointerWidthBits := {POINTER_WIDTH_BITS}, mirProfileVersion := {MIR_PROFILE_VERSION}, scope := Trusted.MirAst.VerificationScope.{scope}, entryDefId := {ENTRY_DEF_ID}, bodies := {} }}\n\nend Captured\n",
        list(program.bodies(), body)
    )
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{identity, render};
    use crate::ir::{
        Block, Body, ConstLit, Operand, Program, Rvalue, Scope, Statement, Terminator, Ty,
    };

    #[test]
    fn identity_names_are_only_numeric_character_data() {
        assert_eq!(
            identity("a\"\\\nλ/- --"),
            "(_root_.String.ofList [(_root_.Char.ofNat 97), (_root_.Char.ofNat 34), (_root_.Char.ofNat 92), (_root_.Char.ofNat 10), (_root_.Char.ofNat 955), (_root_.Char.ofNat 47), (_root_.Char.ofNat 45), (_root_.Char.ofNat 32), (_root_.Char.ofNat 45), (_root_.Char.ofNat 45)])"
        );
    }

    #[test]
    fn render_emits_total_deterministic_lean_for_validated_program() {
        let body = Body::try_new(
            0,
            false,
            vec![Ty::Unit],
            vec![Block {
                statements: vec![
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Unit,
                    },
                    Statement::Assign {
                        local: 0,
                        value: Rvalue::Use {
                            operand: Operand::Constant {
                                ty: Ty::Unit,
                                lit: ConstLit::ZeroSized,
                            },
                            with_retag: true,
                        },
                    },
                ],
                terminator: Terminator::Ret,
            }],
            "rust-path-v1::unit_fn".into(),
        )
        .unwrap();
        let program = Program::try_new(Scope::Crate, vec![body.clone()]).unwrap();
        let rendered = render(&program);
        assert!(rendered.contains("pointerWidthBits := 64"), "{rendered}");
        assert!(rendered.contains("mirProfileVersion := 1"), "{rendered}");
        // Producers must not rely on the Lean default for the entry body.
        assert!(rendered.contains("entryDefId := 0"), "{rendered}");
        assert!(
            rendered.contains("Trusted.MirAst.VerificationScope.crate"),
            "{rendered}"
        );
        assert_eq!(
            rendered
                .matches("(Trusted.MirAst.Rvalue.aggregateTuple [])")
                .count(),
            1,
            "{rendered}"
        );
        assert_eq!(
            rendered
                .matches("(Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk Trusted.MirAst.MirTy.unit Trusted.MirAst.ConstLit.zeroSized)))")
                .count(),
            1,
            "{rendered}"
        );
        assert!(!rendered.contains("unit_fn"), "{rendered}");

        let selected = Program::try_new(
            Scope::SelectedUnit {
                roots: BTreeSet::from(["raw\"selector".into()]),
            },
            vec![body],
        )
        .unwrap();
        let selected_rendered = render(&selected);
        assert!(
            selected_rendered.contains("Trusted.MirAst.VerificationScope.unit"),
            "{selected_rendered}"
        );
        assert!(
            selected_rendered.contains("entryDefId := 0"),
            "{selected_rendered}"
        );
        assert!(
            !selected_rendered.contains("selector"),
            "{selected_rendered}"
        );
    }
}
