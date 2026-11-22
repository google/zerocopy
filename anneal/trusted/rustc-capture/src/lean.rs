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

use std::fmt::Write as _;

use crate::ir::{
    self, BinOp, CastKind, ConstLit, Operand, Rvalue, Statement, Terminator, Ty, UnOp,
};

const HEADER: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n\
prelude\nimport Trusted.MirAst\n\nnamespace Captured\n\n";

const MAX_LIST_CHUNK_LEN: usize = 16;

fn join_balanced_slice<T>(
    chunks: &[T],
    indent: Option<usize>,
    render_leaf: &impl Fn(&T, Option<usize>) -> String,
) -> String {
    match chunks {
        [] => "[]".into(),
        [single] => render_leaf(single, indent),
        _ => {
            let mid = chunks.len() / 2;
            let (left, right) = chunks.split_at(mid);
            match indent {
                None => format!(
                    "(_root_.List.append {} {})",
                    join_balanced_slice(left, None, render_leaf),
                    join_balanced_slice(right, None, render_leaf)
                ),
                Some(col) => {
                    let child_col = col + 2;
                    let pad = " ".repeat(child_col);
                    format!(
                        "(_root_.List.append {}\n{pad}{})",
                        join_balanced_slice(left, Some(child_col), render_leaf),
                        join_balanced_slice(right, Some(child_col), render_leaf)
                    )
                }
            }
        }
    }
}

fn list_literal_at<T>(
    values: &[T],
    indent: Option<usize>,
    render: &impl Fn(&T, Option<usize>) -> String,
) -> String {
    if values.is_empty() {
        return "[]".into();
    }
    match indent {
        None => {
            let items: Vec<String> = values.iter().map(|v| render(v, None)).collect();
            format!("[{}]", items.join(", "))
        }
        Some(col) => {
            let item_col = col + 2;
            let item_pad = " ".repeat(item_col);
            let close_pad = " ".repeat(col);
            let items: Vec<String> =
                values.iter().map(|v| format!("{item_pad}{}", render(v, Some(item_col)))).collect();
            format!("[\n{}\n{close_pad}]", items.join(",\n"))
        }
    }
}

fn list_literal<T>(values: &[T], render: impl Fn(&T) -> String) -> String {
    list_literal_at(values, None, &|v, _| render(v))
}

/// Render a Lean list literal, chunking lists longer than `MAX_LIST_CHUNK_LEN`
/// into a balanced binary tree of `_root_.List.append` over 1..=16-element
/// leaves.
///
/// Lean 4.34.1 expands `[...]` literals of `>= 33` elements via
/// `Init.NotationExtra`'s `%[...|...]` macro into nested `let` bindings, which
/// adds elaboration recursion overhead on top of per-element `OfNat` synthesis
/// (e.g., failing elaboration with `maximum recursion depth has been reached`
/// at `~1950+` distinct `Nat` literals in one definition, while chunking passes
/// up to `~2000`). `_root_.List.append` lives in `Init.Prelude`, avoids
/// namespace shadowing under `namespace Captured`, preserves `rfl` definitional
/// equality with a flat list in the Lean kernel, and bounds AST depth to
/// `O(log N)` (note `List.length` by `rfl` and `2050+` distinct `OfNat`s in
/// one definition still hit Lean's `maxRecDepth` limit independently of list
/// representation).
fn list<T>(values: &[T], render: impl Fn(&T) -> String) -> String {
    let chunks: Vec<&[T]> = values.chunks(MAX_LIST_CHUNK_LEN).collect();
    join_balanced_slice(&chunks, None, &|chunk, _| list_literal(chunk, &render))
}

fn list_pretty<T>(values: &[T], indent: usize, render: impl Fn(&T, usize) -> String) -> String {
    let chunks: Vec<&[T]> = values.chunks(MAX_LIST_CHUNK_LEN).collect();
    join_balanced_slice(&chunks, Some(indent), &|chunk, chunk_indent| {
        list_literal_at(chunk, chunk_indent, &|item, item_indent| {
            render(item, item_indent.unwrap_or(indent))
        })
    })
}

fn list_chunk_lines<T>(values: &[T], indent: usize, render: impl Fn(&T) -> String) -> String {
    let chunks: Vec<&[T]> = values.chunks(MAX_LIST_CHUNK_LEN).collect();
    if chunks.len() <= 1 {
        list(values, render)
    } else {
        join_balanced_slice(&chunks, Some(indent), &|chunk, _| list_literal(chunk, &render))
    }
}

fn ty_at(t: &Ty, indent: usize) -> String {
    match t {
        Ty::Bool => "Trusted.MirAst.MirTy.bool".into(),
        Ty::Char => "Trusted.MirAst.MirTy.char".into(),
        Ty::Ordering => "Trusted.MirAst.MirTy.ordering".into(),
        Ty::Unit => "Trusted.MirAst.MirTy.unit".into(),
        Ty::Never => "Trusted.MirAst.MirTy.never".into(),
        Ty::Int(ity) => format!(
            "(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.{} {})",
            ity.width.lean_name(),
            ity.signed
        ),
        Ty::OverflowPair(ity) => format!(
            "(Trusted.MirAst.MirTy.tuple [(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.{} {}), Trusted.MirAst.MirTy.bool])",
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
            let field_pad = " ".repeat(indent + 2);
            let close_pad = " ".repeat(indent);
            let discriminants = list_chunk_lines(ety.discriminants(), indent + 2, u128::to_string);
            format!(
                "(Trusted.MirAst.MirTy.enum {{\n\
                 {field_pad}id := {},\n\
                 {field_pad}discrWidth := Trusted.MirAst.IntWidth.{},\n\
                 {field_pad}discrSigned := {},\n\
                 {field_pad}tagRepr := {tag_repr},\n\
                 {field_pad}discriminants := {discriminants}\n\
                 {close_pad}}})",
                ety.id(),
                discr.width.lean_name(),
                discr.signed,
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

fn operand_at(op: &Operand, indent: usize) -> String {
    match op {
        Operand::Copy { local } => {
            format!("(Trusted.MirAst.Operand.copy (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Move { local } => {
            format!("(Trusted.MirAst.Operand.move (Trusted.MirAst.Place.mk {local} []))")
        }
        Operand::Constant { ty: t, lit } => format!(
            "(Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk {} {}))",
            ty_at(t, indent),
            const_lit(*lit)
        ),
    }
}

fn un_op(op: UnOp) -> &'static str {
    match op {
        UnOp::Not => "not",
        UnOp::Neg => "neg",
    }
}

fn cast_kind(kind: CastKind) -> &'static str {
    match kind {
        CastKind::IntToInt => "intToInt",
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
        BinOp::Div => "div",
        BinOp::Rem => "rem",
        BinOp::AddWithOverflow => "addWithOverflow",
        BinOp::SubWithOverflow => "subWithOverflow",
        BinOp::MulWithOverflow => "mulWithOverflow",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        BinOp::Cmp => "cmp",
    }
}

fn rvalue_at(value: &Rvalue, indent: usize) -> String {
    match value {
        // `ir::Body::try_new` admits `with_retag == true` only when the
        // destination type satisfies `Ty::is_retag_noop()`.
        Rvalue::Use { operand: op, .. } => {
            format!("(Trusted.MirAst.Rvalue.use {})", operand_at(op, indent))
        }
        Rvalue::Binary { op, left, right } => format!(
            "(Trusted.MirAst.Rvalue.binaryOp Trusted.MirAst.BinOp.{} {} {})",
            bin_op(*op),
            operand_at(left, indent),
            operand_at(right, indent)
        ),
        Rvalue::Unary { op, operand: opnd } => format!(
            "(Trusted.MirAst.Rvalue.unaryOp Trusted.MirAst.UnOp.{} {})",
            un_op(*op),
            operand_at(opnd, indent)
        ),
        Rvalue::Cast { cast_kind: kind, operand: opnd, ty: target_ty } => format!(
            "(Trusted.MirAst.Rvalue.cast Trusted.MirAst.CastKind.{} {} {})",
            cast_kind(*kind),
            operand_at(opnd, indent),
            ty_at(target_ty, indent)
        ),
        Rvalue::Discriminant { local } => {
            format!("(Trusted.MirAst.Rvalue.discriminant (Trusted.MirAst.Place.mk {local} []))")
        }
    }
}

fn statement_at(stmt: &Statement, indent: usize) -> String {
    match stmt {
        Statement::Assign { local, value } => format!(
            "(Trusted.MirAst.StatementKind.assign (Trusted.MirAst.Place.mk {local} []) {})",
            rvalue_at(value, indent)
        ),
        Statement::StorageLive { local } => {
            format!("(Trusted.MirAst.StatementKind.storageLive {local})")
        }
        Statement::StorageDead { local } => {
            format!("(Trusted.MirAst.StatementKind.storageDead {local})")
        }
        // `ir::Body::try_new` admits `Statement::PlaceMention` only for an
        // in-bounds, unprojected `Sized` local, where `rustc`'s `eval_place`
        // (`local_to_place`) and `lean-miri`'s `Step.evalStatement` perform no
        // memory load and no liveness check.
        Statement::PlaceMention { .. } | Statement::Nop => "Trusted.MirAst.StatementKind.nop".into(),
    }
}

fn terminator_at(term: &Terminator, indent: usize) -> String {
    match term {
        Terminator::Goto { block } => {
            format!("(Trusted.MirAst.TerminatorKind.goto {block})")
        }
        Terminator::SwitchInt { operand: op, targets, otherwise } => {
            let child_pad = " ".repeat(indent + 2);
            let target_pad = " ".repeat(indent + 4);
            format!(
                "(Trusted.MirAst.TerminatorKind.switchInt\n\
                 {child_pad}{}\n\
                 {child_pad}(Trusted.MirAst.SwitchTargets.mk\n\
                 {target_pad}{}\n\
                 {target_pad}{otherwise}))",
                operand_at(op, indent + 2),
                list_pretty(targets, indent + 4, |(value, block), _| format!(
                    "((BitVec.ofNat 128 {value}), {block})"
                ))
            )
        }
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
fn identity_at(value: &str, indent: usize) -> String {
    let characters: Vec<char> = value.chars().collect();
    let chars_list = list_chunk_lines(&characters, indent + 2, |ch| {
        format!("(_root_.Char.ofNat {})", u32::from(*ch))
    });
    format!("(_root_.String.ofList {chars_list})")
}

#[cfg(test)]
fn identity(value: &str) -> String {
    identity_at(value, 0)
}

fn body_record(body: &ir::Body, indent: usize) -> String {
    let field_col = indent + 2;
    let field_pad = " ".repeat(field_col);
    let close_pad = " ".repeat(indent);
    format!(
        "{{\n\
         {field_pad}argumentCount := {},\n\
         {field_pad}isUnsafe := {},\n\
         {field_pad}locals := {},\n\
         {field_pad}basicBlocks := {},\n\
         {field_pad}identity := {}\n\
         {close_pad}}}",
        body.arg_count(),
        body.is_unsafe(),
        list_pretty(body.local_tys(), field_col, ty_at),
        list_pretty(body.blocks(), field_col, |block, block_indent| {
            let bf_col = block_indent + 2;
            let bf_pad = " ".repeat(bf_col);
            let bc_pad = " ".repeat(block_indent);
            format!(
                "({{\n\
                 {bf_pad}statements := {},\n\
                 {bf_pad}terminator := {},\n\
                 {bf_pad}cleanup := false\n\
                 {bc_pad}}} : Trusted.MirAst.BasicBlock)",
                list_pretty(&block.statements, bf_col, statement_at),
                terminator_at(&block.terminator, bf_col)
            )
        }),
        identity_at(body.identity(), field_col)
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
///
/// Each body is emitted as its own `Captured.body_<i>` definition, and
/// `program.bodies` assembles more than [`MAX_LIST_CHUNK_LEN`] bodies via
/// `Captured.bodies_chunk_<k>` slices combined with a balanced
/// `_root_.List.append` tree so elaboration recursion depth stays bounded on
/// multi-hundred- and multi-thousand-function crates.
pub fn render(program: &ir::Program) -> String {
    let scope = match program.scope() {
        ir::Scope::SelectedUnit { .. } => "unit",
        ir::Scope::Crate => "crate",
    };
    let mut out = String::from(HEADER);
    let mut body_names = Vec::with_capacity(program.bodies().len());
    for (index, item) in program.bodies().iter().enumerate() {
        let name = format!("body_{index}");
        let _ = writeln!(out, "def {name} : Trusted.MirAst.Body :=\n  {}\n", body_record(item, 2));
        body_names.push(name);
    }
    let bodies_expr = match body_names.as_slice() {
        [] => "[]".into(),
        [single] => format!("[{single}]"),
        _ if body_names.len() <= MAX_LIST_CHUNK_LEN => {
            list_literal_at(&body_names, Some(4), &|name, _| name.clone())
        }
        _ => {
            let mut chunk_names = Vec::new();
            for (chunk_idx, chunk) in body_names.chunks(MAX_LIST_CHUNK_LEN).enumerate() {
                let chunk_name = format!("bodies_chunk_{chunk_idx}");
                let chunk_lit = list_literal_at(chunk, Some(2), &|name, _| name.clone());
                let _ = writeln!(
                    out,
                    "def {chunk_name} : _root_.List Trusted.MirAst.Body :=\n  {chunk_lit}\n"
                );
                chunk_names.push(chunk_name);
            }
            join_balanced_slice(&chunk_names, Some(4), &|name, _| name.clone())
        }
    };
    let _ = write!(
        out,
        "def program : Trusted.MirAst.Program :=\n\
         \x20 {{\n\
         \x20   pointerWidthBits := {POINTER_WIDTH_BITS},\n\
         \x20   mirProfileVersion := {MIR_PROFILE_VERSION},\n\
         \x20   scope := Trusted.MirAst.VerificationScope.{scope},\n\
         \x20   entryDefId := {ENTRY_DEF_ID},\n\
         \x20   bodies := {bodies_expr}\n\
         \x20 }}\n\nend Captured\n"
    );
    out
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{MAX_LIST_CHUNK_LEN, identity, list, render};
    use crate::ir::{
        Block, Body, ConstLit, EnumTagRepr, EnumTy, IntTy, IntWidth, Operand, Program, Rvalue,
        Scope, Statement, Terminator, Ty,
    };

    fn max_paren_depth(text: &str) -> usize {
        let mut depth = 0usize;
        let mut max_depth = 0usize;
        for ch in text.chars() {
            match ch {
                '(' => {
                    depth += 1;
                    max_depth = max_depth.max(depth);
                }
                ')' => {
                    depth = depth.checked_sub(1).expect("unbalanced closing parenthesis");
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0, "unbalanced parentheses in {text}");
        max_depth
    }

    fn assert_list_literals_at_most(text: &str, max_elems: usize) {
        let mut paren_depth = 0usize;
        // Track (paren_depth_at_open, top_level_commas, saw_element_token)
        // per active `[` so nested lists inside body/tuple elements are bounded
        // independently of enclosing list literals.
        let mut brackets: Vec<(usize, usize, bool)> = Vec::new();
        for ch in text.chars() {
            if let Some(&(open_p, _, _)) = brackets.last()
                && paren_depth == open_p
                && !ch.is_whitespace()
                && ch != ','
                && ch != ']'
            {
                brackets.last_mut().unwrap().2 = true;
            }
            match ch {
                '(' => paren_depth += 1,
                ')' => {
                    paren_depth =
                        paren_depth.checked_sub(1).expect("unbalanced closing parenthesis");
                }
                '[' => brackets.push((paren_depth, 0, false)),
                ',' => {
                    if let Some(&mut (open_p, ref mut commas, _)) = brackets.last_mut()
                        && paren_depth == open_p
                    {
                        *commas += 1;
                    }
                }
                ']' => {
                    let (open_p, commas, saw_token) =
                        brackets.pop().expect("unbalanced closing bracket");
                    assert_eq!(paren_depth, open_p, "unbalanced parens inside list literal");
                    let elems = if commas > 0 || saw_token { commas + 1 } else { 0 };
                    assert!(
                        elems <= max_elems,
                        "list literal has {elems} elements (limit {max_elems})"
                    );
                }
                _ => {}
            }
        }
        assert!(brackets.is_empty(), "unclosed bracket in {text}");
    }

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
                statements: vec![Statement::Assign {
                    local: 0,
                    value: Rvalue::Use {
                        operand: Operand::Constant { ty: Ty::Unit, lit: ConstLit::ZeroSized },
                        with_retag: true,
                    },
                }],
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
        assert!(rendered.contains("Trusted.MirAst.VerificationScope.crate"), "{rendered}");
        assert_eq!(
            rendered
                .matches("(Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk Trusted.MirAst.MirTy.unit Trusted.MirAst.ConstLit.zeroSized)))")
                .count(),
            1,
            "{rendered}"
        );
        assert!(!rendered.contains("unit_fn"), "{rendered}");

        let selected = Program::try_new(
            Scope::SelectedUnit { roots: BTreeSet::from(["raw\"selector".into()]) },
            vec![body],
        )
        .unwrap();
        let selected_rendered = render(&selected);
        assert!(
            selected_rendered.contains("Trusted.MirAst.VerificationScope.unit"),
            "{selected_rendered}"
        );
        assert!(selected_rendered.contains("entryDefId := 0"), "{selected_rendered}");
        assert!(!selected_rendered.contains("selector"), "{selected_rendered}");
        assert!(
            selected_rendered.contains("def body_0 : Trusted.MirAst.Body :="),
            "{selected_rendered}"
        );
        assert!(selected_rendered.contains("bodies := [body_0]"), "{selected_rendered}");
        assert!(!selected_rendered.contains("bodies_chunk_"), "{selected_rendered}");
    }

    #[test]
    fn render_chunks_large_programs_and_long_lists_with_balanced_append() {
        let bodies: Vec<Body> = (0..130)
            .map(|i| {
                Body::try_new(
                    0,
                    false,
                    vec![Ty::Unit],
                    vec![Block {
                        statements: vec![Statement::Nop; if i == 0 { 70 } else { 0 }],
                        terminator: Terminator::Ret,
                    }],
                    format!("rust-path-v1::fn_{i}"),
                )
                .unwrap()
            })
            .collect();
        let program = Program::try_new(Scope::Crate, bodies).unwrap();
        let rendered = render(&program);
        assert!(rendered.contains("def body_0 : Trusted.MirAst.Body :="), "{rendered}");
        assert!(rendered.contains("def body_129 : Trusted.MirAst.Body :="), "{rendered}");
        assert!(
            rendered.contains("def bodies_chunk_0 : _root_.List Trusted.MirAst.Body :="),
            "{rendered}"
        );
        assert!(
            rendered.contains("def bodies_chunk_8 : _root_.List Trusted.MirAst.Body :="),
            "{rendered}"
        );
        assert!(rendered.contains("(_root_.List.append "), "{rendered}");
        assert_list_literals_at_most(&rendered, MAX_LIST_CHUNK_LEN);
    }

    #[test]
    fn list_preserves_small_lists_and_balances_large_chunks() {
        let empty: Vec<u32> = Vec::new();
        assert_eq!(list(&empty, u32::to_string), "[]");

        let one = [42u32];
        assert_eq!(list(&one, u32::to_string), "[42]");

        let sixteen: Vec<u32> = (0..16).collect();
        assert_eq!(
            list(&sixteen, u32::to_string),
            "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
        );

        let seventeen: Vec<u32> = (0..17).collect();
        assert_eq!(
            list(&seventeen, u32::to_string),
            "(_root_.List.append [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] [16])"
        );

        let two_fifty: Vec<u32> = (0..250).collect();
        let rendered = list(&two_fifty, u32::to_string);
        assert!(max_paren_depth(&rendered) <= 10, "excessive paren depth in {rendered}");
        assert_list_literals_at_most(&rendered, MAX_LIST_CHUNK_LEN);

        // Extract every leaf number in source order to ensure zero reordering
        // or dropped items across recursive `_root_.List.append` nodes.
        let cleaned: String = rendered
            .replace("(_root_.List.append ", " ")
            .chars()
            .filter(|ch| ch.is_ascii_digit() || *ch == ' ')
            .collect();
        let recovered: Vec<u32> =
            cleaned.split_whitespace().map(|tok| tok.parse::<u32>().unwrap()).collect();
        assert_eq!(recovered, two_fifty);
    }

    #[test]
    fn identity_and_render_balance_all_large_list_fields() {
        let long_id = identity(&"a".repeat(250));
        assert!(max_paren_depth(&long_id) <= 10, "{long_id}");
        assert_list_literals_at_most(&long_id, MAX_LIST_CHUNK_LEN);

        let u64_ty = Ty::Int(IntTy { width: IntWidth::I64, signed: false });
        let big_enum = Ty::Enum(
            EnumTy::try_new(
                7,
                IntTy { width: IntWidth::I64, signed: false },
                EnumTagRepr::Scalar(IntTy { width: IntWidth::I64, signed: false }),
                (0..70).collect(),
            )
            .unwrap(),
        );
        let mut locals = vec![Ty::Unit, u64_ty.clone(), big_enum];
        locals.resize(70, u64_ty);
        let targets = (0..70u128).map(|v| (v, 1u32)).collect();
        let statements = vec![Statement::Nop; 250];
        let body0 = Body::try_new(
            0,
            false,
            locals,
            vec![
                Block {
                    statements,
                    terminator: Terminator::SwitchInt {
                        operand: Operand::Copy { local: 1 },
                        targets,
                        otherwise: 1,
                    },
                },
                Block { statements: vec![], terminator: Terminator::Ret },
            ],
            format!("rust-path-v1::{}", "f".repeat(86)),
        )
        .unwrap();

        let mut bodies = vec![body0];
        for i in 1..70 {
            bodies.push(
                Body::try_new(
                    0,
                    false,
                    vec![Ty::Unit],
                    vec![Block { statements: vec![], terminator: Terminator::Ret }],
                    format!("rust-path-v1::fn_{i}"),
                )
                .unwrap(),
            );
        }
        let program = Program::try_new(Scope::Crate, bodies).unwrap();
        let rendered = render(&program);
        // `bodies` (depth 3) + Body/BasicBlock/SwitchInt/BitVec wrappers (5)
        // + 250-statement or 70-target append tree (depth 4/3) stays O(log N).
        assert!(
            max_paren_depth(&rendered) <= 16,
            "excessive paren depth: {}",
            max_paren_depth(&rendered)
        );
        assert_list_literals_at_most(&rendered, MAX_LIST_CHUNK_LEN);
        assert!(rendered.contains("(_root_.List.append "));
        let max_line = rendered.lines().map(str::len).max().unwrap_or(0);
        assert!(max_line <= 500, "expected pretty-printed line width <= 500, got {max_line}");
        assert!(
            rendered.lines().all(|line| !line.ends_with(' ') && !line.ends_with('\t')),
            "unexpected trailing whitespace in rendered Lean"
        );
    }

    #[test]
    fn render_pretty_prints_structured_multiline_lean() {
        let enum_ty = Ty::Enum(
            EnumTy::try_new(
                9,
                IntTy { width: IntWidth::I32, signed: true },
                EnumTagRepr::Scalar(IntTy { width: IntWidth::I8, signed: true }),
                vec![0, 1],
            )
            .unwrap(),
        );
        let i32_ty = Ty::Int(IntTy { width: IntWidth::I32, signed: true });
        let body0 = Body::try_new(
            1,
            true,
            vec![i32_ty.clone(), i32_ty, enum_ty.clone()],
            vec![
                Block {
                    statements: vec![
                        Statement::StorageLive { local: 1 },
                        Statement::Assign {
                            local: 0,
                            value: Rvalue::Use {
                                operand: Operand::Copy { local: 1 },
                                with_retag: true,
                            },
                        },
                        Statement::Assign {
                            local: 2,
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: enum_ty,
                                    lit: ConstLit::Scalar { bits: 0 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Nop,
                    ],
                    terminator: Terminator::SwitchInt {
                        operand: Operand::Copy { local: 1 },
                        targets: vec![(0, 1), (1, 1)],
                        otherwise: 1,
                    },
                },
                Block { statements: vec![], terminator: Terminator::Ret },
            ],
            "rust-path-v1::multi_block_secret_fn".into(),
        )
        .unwrap();
        let body1 = Body::try_new(
            0,
            false,
            vec![Ty::Unit],
            vec![Block { statements: vec![], terminator: Terminator::Ret }],
            "rust-path-v1::helper_fn".into(),
        )
        .unwrap();
        let program = Program::try_new(Scope::Crate, vec![body0, body1]).unwrap();
        let rendered = render(&program);
        for expected in [
            "def body_0 : Trusted.MirAst.Body :=\n  {\n",
            "    argumentCount := 1,\n    isUnsafe := true,\n",
            "    locals := [\n",
            "      (Trusted.MirAst.MirTy.enum {\n",
            "        id := 9,\n",
            "        discriminants := [0, 1]\n",
            "      })\n",
            "    basicBlocks := [\n",
            "      ({\n        statements := [\n",
            "          (Trusted.MirAst.StatementKind.assign (Trusted.MirAst.Place.mk 2 []) (Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk (Trusted.MirAst.MirTy.enum {\n            id := 9,\n            discrWidth := Trusted.MirAst.IntWidth.i32,\n            discrSigned := true,\n            tagRepr := (Trusted.MirAst.EnumTagRepr.scalar Trusted.MirAst.IntWidth.i8 true),\n            discriminants := [0, 1]\n          }) (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 0)))))),\n",
            "        terminator := (Trusted.MirAst.TerminatorKind.switchInt\n",
            "          (Trusted.MirAst.SwitchTargets.mk\n",
            "            [\n",
            "              ((BitVec.ofNat 128 0), 1),\n",
            "              ((BitVec.ofNat 128 1), 1)\n",
            "            ]\n            1)),\n",
            "    bodies := [\n      body_0,\n      body_1\n    ]\n",
        ] {
            assert!(
                rendered.contains(expected),
                "missing pretty block {expected:?} in:\n{rendered}"
            );
        }
        assert!(!rendered.contains("secret_fn"));
        assert!(!rendered.contains("helper_fn"));
        assert!(rendered.lines().all(|line| !line.ends_with(' ') && !line.ends_with('\t')));
    }
}
