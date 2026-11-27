// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Parsing of specification clauses, expressions, and attachment forms.
//!
//! Clause expressions are parsed by a dedicated Pratt parser over token trees
//! rather than by `syn::Expr`, for two reasons: `==>` and `<==>` are not Rust
//! operators, and several Rust spellings that `syn` accepts silently (eager
//! `&`, `!a == b`, chained comparisons) must be rejected with a diagnostic.

use std::collections::BTreeSet;

use proc_macro2::{Delimiter, Spacing, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
    Attribute, Token,
};

use crate::{
    ast::{
        BinOp, Clause, Effect, Expr, ExprKind, IntConst, IntTy, Param, PureFn, SpannedClause,
        SpecFn, Ty, UnOp,
    },
    diag::Diagnostic,
};

/// Multi-character operators, longest first so matching is maximal munch.
const OPERATORS: &[&str] = &[
    "<==>", "==>", "<<=", ">>=", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "+=", "-=", "*=",
    "/=", "%=", "^=", "&=", "|=", "::", "->", "=>", "..", "<", ">", "=", "!", "&", "|", "^", "+",
    "-", "*", "/", "%", ".", ",", ";", ":", "?", "#", "@", "$", "~",
];

#[derive(Clone, Debug)]
enum Tok {
    Ident(String, Span),
    Lit(proc_macro2::Literal, Span),
    Op(String, Span),
    Group(Delimiter, TokenStream, Span),
}

impl Tok {
    fn span(&self) -> Span {
        match self {
            Tok::Ident(_, s) | Tok::Lit(_, s) | Tok::Op(_, s) | Tok::Group(_, _, s) => *s,
        }
    }

    fn is_op(&self, op: &str) -> bool {
        matches!(self, Tok::Op(o, _) if o == op)
    }
}

fn join(a: Span, b: Span) -> Span {
    a.join(b).unwrap_or(a)
}

/// Flattens a token stream, combining joint punctuation into operators.
fn tokenize(stream: TokenStream) -> Vec<Tok> {
    let mut out = Vec::new();
    let mut pending: Vec<(char, Span)> = Vec::new();
    let flush = |pending: &mut Vec<(char, Span)>, out: &mut Vec<Tok>| {
        let mut i = 0;
        while i < pending.len() {
            let rest: String = pending[i..].iter().map(|(c, _)| *c).collect();
            let len = OPERATORS
                .iter()
                .find(|op| rest.starts_with(**op))
                .map_or(1, |op| op.chars().count());
            let text: String = pending[i..i + len].iter().map(|(c, _)| *c).collect();
            let span = join(pending[i].1, pending[i + len - 1].1);
            out.push(Tok::Op(text, span));
            i += len;
        }
        pending.clear();
    };
    for tt in stream {
        match tt {
            TokenTree::Punct(p) => {
                pending.push((p.as_char(), p.span()));
                if p.spacing() == proc_macro2::Spacing::Alone {
                    flush(&mut pending, &mut out);
                }
            }
            other => {
                flush(&mut pending, &mut out);
                match other {
                    TokenTree::Ident(i) => out.push(Tok::Ident(i.to_string(), i.span())),
                    TokenTree::Literal(l) => {
                        let span = l.span();
                        out.push(Tok::Lit(l, span));
                    }
                    TokenTree::Group(g) => {
                        out.push(Tok::Group(g.delimiter(), g.stream(), g.span()))
                    }
                    TokenTree::Punct(_) => unreachable!(),
                }
            }
        }
    }
    flush(&mut pending, &mut out);
    out
}

fn binop(op: &str) -> Option<BinOp> {
    Some(match op {
        "<==>" => BinOp::Iff,
        "==>" => BinOp::Implies,
        "||" => BinOp::Or,
        "&&" => BinOp::And,
        "==" => BinOp::Eq,
        "!=" => BinOp::Ne,
        "<" => BinOp::Lt,
        "<=" => BinOp::Le,
        ">" => BinOp::Gt,
        ">=" => BinOp::Ge,
        "|" => BinOp::BitOr,
        "^" => BinOp::BitXor,
        "&" => BinOp::BitAnd,
        "<<" => BinOp::Shl,
        ">>" => BinOp::Shr,
        "+" => BinOp::Add,
        "-" => BinOp::Sub,
        "*" => BinOp::Mul,
        "/" => BinOp::Div,
        "%" => BinOp::Rem,
        _ => return None,
    })
}

/// `(left, right)` binding powers. A larger right power than left makes an
/// operator left-associative; `==>` is right-associative.
fn binding_power(op: BinOp) -> (u8, u8) {
    match op {
        BinOp::Iff => (1, 2),
        BinOp::Implies => (4, 3),
        BinOp::Or => (5, 6),
        BinOp::And => (7, 8),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => (9, 10),
        BinOp::BitOr => (11, 12),
        BinOp::BitXor => (13, 14),
        BinOp::BitAnd => (15, 16),
        BinOp::Shl | BinOp::Shr => (17, 18),
        BinOp::Add | BinOp::Sub => (19, 20),
        BinOp::Mul | BinOp::Div | BinOp::Rem => (21, 22),
    }
}

const PREFIX_BP: u8 = 23;

const INT_CONST_HELP: &str =
    "the only paths a specification may name are the integer constants `T::MIN`, `T::MAX`, \
     and `T::BITS`, where `T` is a fixed-width integer type such as `usize`";

struct ExprParser {
    toks: Vec<Tok>,
    pos: usize,
    end_span: Span,
    /// Whether an `if` condition is being parsed. As in Rust, a condition
    /// ends at the first `{` group in operator position, which opens the
    /// `then` branch.
    in_cond: bool,
}

impl ExprParser {
    fn new(stream: TokenStream, end_span: Span) -> Self {
        ExprParser { toks: tokenize(stream), pos: 0, end_span, in_cond: false }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        self.pos += 1;
        t
    }

    fn parse_all(mut self) -> Result<Expr, Diagnostic> {
        let e = self.parse(0)?;
        if let Some(t) = self.peek() {
            return Err(unexpected(t));
        }
        Ok(e)
    }

    fn parse(&mut self, min_bp: u8) -> Result<Expr, Diagnostic> {
        let mut lhs = self.parse_prefix()?;
        loop {
            let Some(tok) = self.peek().cloned() else { break };
            if self.in_cond && matches!(tok, Tok::Group(Delimiter::Brace, ..)) {
                break;
            }
            let Tok::Op(op, op_span) = &tok else { return Err(unexpected(&tok)) };
            if op == "," {
                return Err(unexpected(&tok));
            }
            let Some(bin) = binop(op) else {
                return Err(match op.as_str() {
                    "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "^=" | "&=" | "|=" | "<<=" | ">>=" => {
                        Diagnostic::new(
                            "E_ANNEAL_IMPURE_SPEC_EXPR",
                            *op_span,
                            format!("assignment `{op}` is not allowed in a specification"),
                        )
                        .help("specifications are pure; compare with `==` instead")
                    }
                    "." => Diagnostic::new(
                        "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                        *op_span,
                        "method calls and field accesses are not supported in profile v1 \
                         specifications",
                    )
                    .help("use a `#[anneal::pure]` helper or a built-in intrinsic"),
                    _ => unexpected(&tok),
                });
            };
            if matches!(lhs.kind, ExprKind::If(..)) {
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_SYNTAX",
                    *op_span,
                    format!("an `if` expression must be parenthesized before `{op}`"),
                )
                .help(format!(
                    "parenthesize the expression that ends with the `if`, as in \
                     `(if c {{ a }} else {{ b }}) {op} ...` or `(x == if c {{ a }} else {{ b }}) {op} ...`"
                )));
            }
            let (l_bp, r_bp) = binding_power(bin);
            if l_bp < min_bp {
                break;
            }
            self.pos += 1;
            if bin.is_comparison() {
                if let ExprKind::Binary(prev, _, _) = &lhs.kind {
                    if prev.is_comparison() {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_CHAINED_COMPARISON",
                            *op_span,
                            "comparison operators cannot be chained",
                        )
                        .help("join the comparisons with `&&`"));
                    }
                }
                if matches!(bin, BinOp::Eq | BinOp::Ne) {
                    if let ExprKind::Unary(UnOp::Not, _) = &lhs.kind {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_AMBIGUOUS_NEGATION",
                            lhs.span,
                            format!("`!a {} b` negates only `a`, which is easy to misread", op),
                        )
                        .help(format!("write `(!a) {op} b` or `!(a {op} b)`")));
                    }
                }
            }
            let rhs = self.parse(r_bp)?;
            let span = join(lhs.span, rhs.span);
            lhs = Expr { kind: ExprKind::Binary(bin, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<Expr, Diagnostic> {
        let Some(tok) = self.next() else {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SYNTAX",
                self.end_span,
                "expected an expression",
            ));
        };
        match tok {
            Tok::Op(op, span) if op == "!" || op == "-" => {
                let un = if op == "!" { UnOp::Not } else { UnOp::Neg };
                let inner = self.parse(PREFIX_BP)?;
                let span = join(span, inner.span);
                Ok(Expr { kind: ExprKind::Unary(un, Box::new(inner)), span })
            }
            Tok::Op(op, span) if op == "&" || op == "*" => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                span,
                format!(
                    "prefix `{op}` (references and dereferences) is not supported in profile v1"
                ),
            )),
            Tok::Lit(lit, span) => parse_literal(lit, span),
            Tok::Ident(name, span) => self.parse_ident(name, span),
            Tok::Group(Delimiter::Parenthesis, inner, span) => {
                if inner.is_empty() {
                    return Ok(Expr { kind: ExprKind::Unit, span });
                }
                let e = ExprParser::new(inner, span).parse_all()?;
                Ok(Expr { kind: ExprKind::Paren(Box::new(e)), span })
            }
            Tok::Group(Delimiter::Brace, _, span) => Err(Diagnostic::new(
                "E_ANNEAL_IMPURE_SPEC_EXPR",
                span,
                "block expressions are not allowed in a specification",
            )
            .help("only `math { ... }` and the branches of an `if` take a block")),
            other => Err(unexpected(&other)),
        }
    }

    fn parse_ident(&mut self, name: String, span: Span) -> Result<Expr, Diagnostic> {
        match name.as_str() {
            "true" | "false" => {
                return Ok(Expr { kind: ExprKind::Bool(name == "true"), span });
            }
            "if" => return self.parse_if(span),
            "let" | "match" | "loop" | "while" | "for" | "return" | "unsafe" | "async" | "move" => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_IMPURE_SPEC_EXPR",
                    span,
                    format!("`{name}` is not allowed in a profile v1 specification"),
                ));
            }
            _ => {}
        }
        if self.peek().is_some_and(|t| t.is_op("::")) {
            if let Some(t) = int_ty(&name) {
                return self.parse_int_const(t, span);
            }
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                span,
                "paths are not supported in profile v1 specifications",
            )
            .help(INT_CONST_HELP));
        }
        match self.peek().cloned() {
            Some(Tok::Group(Delimiter::Parenthesis, inner, gspan)) => {
                self.pos += 1;
                let full = join(span, gspan);
                let args = parse_args(inner, gspan)?;
                let one = |args: Vec<Expr>, what: &str| -> Result<Box<Expr>, Diagnostic> {
                    let mut args = args;
                    if args.len() != 1 {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_SPEC_SYNTAX",
                            full,
                            format!("`{what}` takes exactly one argument"),
                        ));
                    }
                    Ok(Box::new(args.remove(0)))
                };
                match name.as_str() {
                    "math" => Ok(Expr { kind: ExprKind::Math(one(args, "math")?), span: full }),
                    "old" => Ok(Expr { kind: ExprKind::Old(one(args, "old")?), span: full }),
                    _ => Ok(Expr { kind: ExprKind::Call(name, args), span: full }),
                }
            }
            Some(Tok::Group(Delimiter::Brace, _, gspan)) if name == "math" && self.in_cond => {
                Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_SYNTAX",
                    join(span, gspan),
                    "`math { .. }` cannot appear in an `if` condition, where `{` opens the \
                     `then` branch",
                )
                .help("write `math(..)` instead"))
            }
            Some(Tok::Group(Delimiter::Brace, inner, gspan)) if name == "math" => {
                self.pos += 1;
                let e = ExprParser::new(inner, gspan).parse_all()?;
                Ok(Expr { kind: ExprKind::Math(Box::new(e)), span: join(span, gspan) })
            }
            _ => Ok(Expr { kind: ExprKind::Ident(name), span }),
        }
    }

    /// Parses the rest of `if cond { a } else { b }` after the `if` keyword,
    /// including any `else if` chain. Unlike a Rust `if` statement, a
    /// specification `if` is an expression, so its `else` branch is required.
    fn parse_if(&mut self, if_span: Span) -> Result<Expr, Diagnostic> {
        if let Some(Tok::Group(Delimiter::Brace, _, gspan)) = self.peek() {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SYNTAX",
                *gspan,
                "expected a condition after `if`",
            ));
        }
        let outer = std::mem::replace(&mut self.in_cond, true);
        let cond = self.parse(0);
        self.in_cond = outer;
        let cond = cond?;
        let then = self.parse_branch(if_span, "the `if` condition")?;
        let else_span = match self.peek() {
            Some(Tok::Ident(name, s)) if name == "else" => *s,
            _ => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_SYNTAX",
                    join(if_span, then.span),
                    "`if` without `else`",
                )
                .help(
                    "a specification `if` is an expression, so it needs an `else` branch: \
                     `if c { a } else { b }`",
                ))
            }
        };
        self.pos += 1;
        let otherwise = match self.peek().cloned() {
            Some(Tok::Ident(name, s)) if name == "if" => {
                self.pos += 1;
                self.parse_if(s)?
            }
            _ => self.parse_branch(else_span, "`else`")?,
        };
        let span = join(if_span, otherwise.span);
        Ok(Expr { kind: ExprKind::If(Box::new(cond), Box::new(then), Box::new(otherwise)), span })
    }

    /// Parses one `{ expr }` branch of an `if`, which must hold exactly one
    /// expression.
    fn parse_branch(&mut self, after: Span, what: &str) -> Result<Expr, Diagnostic> {
        match self.next() {
            Some(Tok::Group(Delimiter::Brace, inner, gspan)) => {
                ExprParser::new(inner, gspan).parse_all()
            }
            other => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SYNTAX",
                other.map_or(after, |t| t.span()),
                format!("expected `{{` after {what}"),
            )),
        }
    }

    /// Parses the rest of `T::MIN`, `T::MAX`, or `T::BITS` after the integer
    /// type name `T`. Any other path, a longer path, or a call is rejected,
    /// so a specification names only constants whose values the lowering
    /// knows.
    fn parse_int_const(&mut self, t: IntTy, span: Span) -> Result<Expr, Diagnostic> {
        let colons = self.next().expect("caller peeked `::`");
        let (name, end) = match self.next() {
            Some(Tok::Ident(name, end)) => (name, end),
            Some(other) => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                    join(span, other.span()),
                    "paths are not supported in profile v1 specifications",
                )
                .help(INT_CONST_HELP));
            }
            None => {
                return Err(Diagnostic::new(
                    "E_ANNEAL_SPEC_SYNTAX",
                    join(span, colons.span()),
                    "expected a constant name after `::`",
                )
                .help(INT_CONST_HELP));
            }
        };
        let full = join(span, end);
        let Some(c) = IntConst::from_rust_name(&name) else {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                full,
                format!(
                    "`{}::{name}` is not supported in profile v1 specifications",
                    t.rust_name()
                ),
            )
            .help(INT_CONST_HELP));
        };
        match self.peek() {
            Some(tok) if tok.is_op("::") => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                join(full, tok.span()),
                "paths are not supported in profile v1 specifications",
            )
            .help(INT_CONST_HELP)),
            Some(Tok::Group(Delimiter::Parenthesis, _, gspan)) => Err(Diagnostic::new(
                "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
                join(full, *gspan),
                format!("`{}::{name}` is a constant, not a function", t.rust_name()),
            )
            .help(INT_CONST_HELP)),
            _ => Ok(Expr { kind: ExprKind::IntConst(t, c), span: full }),
        }
    }
}

fn unexpected(t: &Tok) -> Diagnostic {
    let what = match t {
        Tok::Ident(s, _) | Tok::Op(s, _) => format!("`{s}`"),
        Tok::Lit(l, _) => format!("`{l}`"),
        Tok::Group(..) => "group".to_string(),
    };
    Diagnostic::new("E_ANNEAL_SPEC_SYNTAX", t.span(), format!("unexpected {what}"))
}

/// Splits `stream` at top-level commas.
fn split_commas(stream: TokenStream) -> Vec<TokenStream> {
    let mut parts = vec![TokenStream::new()];
    for tt in stream {
        if matches!(&tt, TokenTree::Punct(p) if p.as_char() == ',') {
            parts.push(TokenStream::new());
        } else {
            parts.last_mut().unwrap().extend([tt]);
        }
    }
    if parts.last().is_some_and(TokenStream::is_empty) {
        parts.pop();
    }
    parts
}

fn parse_args(stream: TokenStream, span: Span) -> Result<Vec<Expr>, Diagnostic> {
    split_commas(stream).into_iter().map(|part| ExprParser::new(part, span).parse_all()).collect()
}

fn parse_literal(lit: proc_macro2::Literal, span: Span) -> Result<Expr, Diagnostic> {
    match syn::Lit::new(lit) {
        syn::Lit::Bool(b) => Ok(Expr { kind: ExprKind::Bool(b.value), span }),
        syn::Lit::Int(i) => {
            let value = i.base10_parse::<u128>().map_err(|e| {
                Diagnostic::new("E_ANNEAL_SPEC_SYNTAX", span, format!("invalid integer: {e}"))
            })?;
            let suffix = match i.suffix() {
                "" => None,
                s => Some(int_ty(s).ok_or_else(|| {
                    Diagnostic::new(
                        "E_ANNEAL_UNSUPPORTED_TYPE",
                        span,
                        format!("unsupported integer suffix `{s}`"),
                    )
                })?),
            };
            Ok(Expr { kind: ExprKind::Int(value, suffix), span })
        }
        _ => Err(Diagnostic::new(
            "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
            span,
            "only integer and boolean literals are supported in profile v1",
        )),
    }
}

/// Parses an expression from a token stream (used for helper bodies).
pub fn parse_expr(stream: TokenStream, span: Span) -> Result<Expr, Diagnostic> {
    ExprParser::new(stream, span).parse_all()
}

pub fn int_ty(name: &str) -> Option<IntTy> {
    match name {
        "u8" => Some(IntTy { bits: 8, signed: false, pointer_sized: false }),
        "u16" => Some(IntTy { bits: 16, signed: false, pointer_sized: false }),
        "u32" => Some(IntTy { bits: 32, signed: false, pointer_sized: false }),
        "u64" => Some(IntTy { bits: 64, signed: false, pointer_sized: false }),
        "u128" => Some(IntTy { bits: 128, signed: false, pointer_sized: false }),
        "usize" => Some(IntTy { bits: 64, signed: false, pointer_sized: true }),
        "i8" => Some(IntTy { bits: 8, signed: true, pointer_sized: false }),
        "i16" => Some(IntTy { bits: 16, signed: true, pointer_sized: false }),
        "i32" => Some(IntTy { bits: 32, signed: true, pointer_sized: false }),
        "i64" => Some(IntTy { bits: 64, signed: true, pointer_sized: false }),
        "i128" => Some(IntTy { bits: 128, signed: true, pointer_sized: false }),
        "isize" => Some(IntTy { bits: 64, signed: true, pointer_sized: true }),
        _ => None,
    }
}

/// Parses the arguments of one `anneal::spec(...)` attribute.
pub fn parse_clauses(stream: TokenStream, span: Span) -> Result<Vec<SpannedClause>, Diagnostic> {
    let mut clauses = Vec::new();
    for part in split_commas(stream) {
        let toks = tokenize(part.clone());
        let Some(Tok::Ident(name, name_span)) = toks.first().cloned() else {
            let s = toks.first().map_or(span, Tok::span);
            return Err(Diagnostic::new("E_ANNEAL_SPEC_SYNTAX", s, "expected a clause name"));
        };
        let clause_span = toks.iter().map(Tok::span).fold(name_span, join);
        let effect = |e| Ok(Clause::Effect(e));
        let clause: Result<Clause, Diagnostic> = match (name.as_str(), &toks[1..]) {
            ("total", []) => effect(Effect::Total),
            ("terminates", []) => effect(Effect::Terminates),
            ("no_panic", []) => effect(Effect::NoPanic),
            ("no_unwind", []) => effect(Effect::NoUnwind),
            ("may_diverge", []) => effect(Effect::MayDiverge),
            ("may_unwind", []) => effect(Effect::MayUnwind),
            ("may_panic", []) => effect(Effect::MayPanic),
            ("no_abort", _) => Err(Diagnostic::new(
                "E_ANNEAL_UNSUPPORTED_CLAUSE",
                name_span,
                "`no_abort` is not supported: every contract already rules out aborting",
            )),
            ("target", [eq, Tok::Lit(lit, lspan)]) if eq.is_op("=") => {
                match syn::Lit::new(lit.clone()) {
                    syn::Lit::Str(s) => Ok(Clause::Target(s.value())),
                    _ => Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        *lspan,
                        "`target` takes a string literal",
                    )),
                }
            }
            ("claim", [eq, Tok::Lit(lit, lspan)]) if eq.is_op("=") => {
                match syn::Lit::new(lit.clone()) {
                    syn::Lit::Str(s) => Ok(Clause::Claim(s.value())),
                    _ => Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        *lspan,
                        "`claim` takes a string literal",
                    )),
                }
            }
            ("instantiate", [eq, Tok::Group(Delimiter::Bracket, inner, g)]) if eq.is_op("=") => {
                parse_instantiate(inner.clone(), *g).map(Clause::Instantiate)
            }
            ("requires", [Tok::Group(Delimiter::Parenthesis, inner, g)]) => {
                parse_expr(inner.clone(), *g).map(Clause::Requires)
            }
            ("safety_requires", [Tok::Group(Delimiter::Parenthesis, inner, g)]) => {
                parse_expr(inner.clone(), *g).map(Clause::SafetyRequires)
            }
            ("ensures", [Tok::Group(Delimiter::Parenthesis, inner, g)]) => {
                parse_ensures(inner.clone(), *g)
            }
            ("max_steps", [eq, rest @ ..]) if eq.is_op("=") => {
                if rest.is_empty() {
                    Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        eq.span(),
                        "expected an expression",
                    )
                    .help("write `max_steps = <expr>`"))
                } else {
                    ExprParser {
                        toks: rest.to_vec(),
                        pos: 0,
                        end_span: clause_span,
                        in_cond: false,
                    }
                    .parse_all()
                    .map(Clause::MaxSteps)
                }
            }
            (
                "cases" | "modifies" | "ensures_err" | "ensures_unwind" | "after_expiry"
                | "unwinds_if" | "decreases" | "witness" | "must_reject",
                _,
            ) => Err(Diagnostic::new(
                "E_ANNEAL_UNSUPPORTED_CLAUSE",
                name_span,
                format!("`{name}` is not supported by the profile v1 lowering yet"),
            )),
            (
                "requires" | "safety_requires" | "ensures" | "total" | "terminates" | "no_panic"
                | "no_unwind" | "may_diverge" | "may_unwind" | "may_panic" | "max_steps" | "target"
                | "claim" | "instantiate",
                _,
            ) => {
                let mut d = Diagnostic::new(
                    "E_ANNEAL_SPEC_SYNTAX",
                    clause_span,
                    format!("malformed `{name}` clause"),
                );
                if name == "max_steps" {
                    d = d.help("write `max_steps = <expr>`");
                }
                Err(d)
            }
            _ => Err(Diagnostic::new(
                "E_ANNEAL_UNKNOWN_CLAUSE",
                name_span,
                format!("unknown specification clause `{name}`"),
            )),
        };
        clauses.push(SpannedClause { clause: clause?, span: clause_span });
    }
    Ok(clauses)
}

/// Parses the bracketed list of `instantiate = [["u8"], ["u32", "bool"]]`:
/// a non-empty list of non-empty lists of type names as string literals.
fn parse_instantiate(stream: TokenStream, span: Span) -> Result<Vec<Vec<String>>, Diagnostic> {
    let malformed = |s| {
        Diagnostic::new(
            "E_ANNEAL_SPEC_SYNTAX",
            s,
            "`instantiate` takes a non-empty list of non-empty lists of type names, \
             such as `[[\"u8\"], [\"u32\"]]`",
        )
    };
    let mut out = Vec::new();
    for part in split_commas(stream) {
        let toks = tokenize(part);
        let [Tok::Group(Delimiter::Bracket, inner, g)] = toks.as_slice() else {
            return Err(malformed(toks.first().map_or(span, Tok::span)));
        };
        let mut tys = Vec::new();
        for ty in split_commas(inner.clone()) {
            match tokenize(ty).as_slice() {
                [Tok::Lit(lit, lspan)] => match syn::Lit::new(lit.clone()) {
                    syn::Lit::Str(s) if !s.value().trim().is_empty() => tys.push(s.value()),
                    _ => return Err(malformed(*lspan)),
                },
                _ => return Err(malformed(*g)),
            }
        }
        if tys.is_empty() {
            return Err(malformed(*g));
        }
        out.push(tys);
    }
    if out.is_empty() {
        return Err(malformed(span));
    }
    Ok(out)
}

fn parse_ensures(stream: TokenStream, span: Span) -> Result<Clause, Diagnostic> {
    let tts: Vec<TokenTree> = stream.into_iter().collect();
    let is_bar = |t: &TokenTree| matches!(t, TokenTree::Punct(p) if p.as_char() == '|');
    // `|ret| Q`, `|_| Q`, or `|| Q`; a missing closure head binds nothing.
    let (binder, skip) = match tts.as_slice() {
        [a, TokenTree::Ident(i), b, ..] if is_bar(a) && is_bar(b) => {
            (if i == "_" { None } else { Some(i.to_string()) }, 3)
        }
        [a, b, ..] if is_bar(a) && is_bar(b) => (None, 2),
        _ => (None, 0),
    };
    let body = parse_expr(tts[skip..].iter().cloned().collect(), span)?;
    Ok(Clause::Ensures { binder, body })
}

/// Resolves a Rust type to a profile v1 specification type.
pub fn parse_type(ty: &syn::Type, self_ty: Option<Ty>) -> Result<Ty, Diagnostic> {
    match ty {
        syn::Type::Tuple(t) if t.elems.is_empty() => Ok(Ty::Unit),
        syn::Type::Paren(p) => parse_type(&p.elem, self_ty),
        syn::Type::Path(p) if p.qself.is_none() && p.path.get_ident().is_some() => {
            let name = p.path.get_ident().unwrap().to_string();
            match name.as_str() {
                "bool" => Ok(Ty::Bool),
                "Self" => self_ty.ok_or_else(|| {
                    Diagnostic::new(
                        "E_ANNEAL_UNSUPPORTED_TYPE",
                        ty.span(),
                        "`Self` is only meaningful inside an `impl` block",
                    )
                }),
                n => int_ty(n).map(Ty::Int).ok_or_else(|| unsupported_type(ty)),
            }
        }
        _ => Err(unsupported_type(ty)),
    }
}

fn unsupported_type(ty: &syn::Type) -> Diagnostic {
    Diagnostic::new(
        "E_ANNEAL_UNSUPPORTED_TYPE",
        ty.span(),
        format!(
            "type `{}` is not supported by profile v1 specifications",
            ty.to_token_stream().to_string().replace(' ', "")
        ),
    )
    .help("profile v1 supports `bool`, `()`, and fixed-width integers")
}

fn token_path(tokens: TokenStream) -> String {
    tokens.to_string().replace(' ', "")
}

/// The anneal attribute an item carries, if any.
enum AnnealAttr {
    Spec(TokenStream, Span),
    Pure,
    VacuousOk(String),
}

/// Recognizes `#[anneal::X(..)]`, `#[X(..)]` (inside `external_spec!`), and
/// `#[cfg_attr(anneal, anneal::X(..))]`. Returns `Ok(None)` for unrelated
/// attributes such as `#[inline]` or doc comments.
///
/// Every `anneal::` path it accepts is recorded in `handled`, so that
/// [`ignored_anneal_paths`] can report forms this parser does not understand
/// (such as `#[cfg_attr(all(anneal), anneal::spec(..))]`) instead of
/// dropping them silently.
fn classify_attr(
    attr: &Attribute,
    bare_ok: bool,
    handled: &mut Vec<Span>,
) -> Result<Option<AnnealAttr>, Diagnostic> {
    let meta = &attr.meta;
    if meta.path().is_ident("cfg_attr") {
        let syn::Meta::List(list) = meta else { return Ok(None) };
        let parts = split_commas(list.tokens.clone());
        let [pred, inner] = parts.as_slice() else { return Ok(None) };
        if token_path(pred.clone()) != "anneal" {
            return Ok(None);
        }
        let inner_meta: syn::Meta = syn::parse2(inner.clone())?;
        return classify_meta(&inner_meta, attr.span(), false, handled);
    }
    classify_meta(meta, attr.span(), bare_ok, handled)
}

fn classify_meta(
    meta: &syn::Meta,
    span: Span,
    bare_ok: bool,
    handled: &mut Vec<Span>,
) -> Result<Option<AnnealAttr>, Diagnostic> {
    let path = meta.path();
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    let name = match segs.as_slice() {
        [a, n] if a == "anneal" => {
            handled.push(path.segments[0].ident.span());
            n.as_str()
        }
        [n] if bare_ok => n.as_str(),
        _ => return Ok(None),
    };
    match (name, meta) {
        ("spec", syn::Meta::List(l)) => Ok(Some(AnnealAttr::Spec(l.tokens.clone(), span))),
        ("pure", syn::Meta::Path(_)) => Ok(Some(AnnealAttr::Pure)),
        ("vacuous_ok", syn::Meta::List(l)) => {
            let nv: syn::MetaNameValue = syn::parse2(l.tokens.clone())?;
            let reason = match (&nv.value, nv.path.is_ident("reason")) {
                (syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(s), .. }), true)
                    if !s.value().trim().is_empty() && !s.value().chars().any(is_hidden_char) =>
                {
                    s.value()
                }
                _ => {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_VACUOUS_OK_REASON",
                        span,
                        "`vacuous_ok` requires a non-empty `reason = \"...\"` without control \
                         or invisible characters",
                    ))
                }
            };
            Ok(Some(AnnealAttr::VacuousOk(reason)))
        }
        ("spec" | "pure" | "vacuous_ok", _) => Err(Diagnostic::new(
            "E_ANNEAL_SPEC_SYNTAX",
            span,
            format!("malformed `anneal::{name}` attribute"),
        )),
        (other, _) if segs.len() == 2 => Err(Diagnostic::new(
            "E_ANNEAL_UNKNOWN_ATTRIBUTE",
            span,
            format!("unknown attribute `anneal::{other}`"),
        )),
        _ => Ok(None),
    }
}

/// Control and format characters, which can hide or reorder text.
fn is_hidden_char(c: char) -> bool {
    c.is_control()
        || matches!(c, '\u{AD}' | '\u{61C}' | '\u{180E}' | '\u{200B}'..='\u{200F}'
            | '\u{2028}'..='\u{202E}' | '\u{2060}'..='\u{206F}' | '\u{FEFF}')
}

struct FnAttrs {
    spec: Option<(TokenStream, Span)>,
    pure: bool,
    vacuous_ok: Option<(String, Span)>,
}

impl FnAttrs {
    fn reject_vacuous_ok(&self, why: &str) -> Result<(), Diagnostic> {
        match &self.vacuous_ok {
            Some((_, span)) => Err(Diagnostic::new(
                "E_ANNEAL_VACUOUS_OK_REASON",
                *span,
                format!("`vacuous_ok` has no effect {why}"),
            )),
            None => Ok(()),
        }
    }
}

fn collect_attrs(
    attrs: &[Attribute],
    bare_ok: bool,
    handled: &mut Vec<Span>,
) -> Result<FnAttrs, Diagnostic> {
    let mut out = FnAttrs { spec: None, pure: false, vacuous_ok: None };
    for attr in attrs {
        match classify_attr(attr, bare_ok, handled)? {
            Some(AnnealAttr::Spec(tokens, span)) => {
                if out.spec.is_some() {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_DUPLICATE_CLAUSE",
                        span,
                        "an item may carry at most one `anneal::spec` attribute",
                    ));
                }
                out.spec = Some((tokens, span));
            }
            Some(AnnealAttr::Pure) => out.pure = true,
            Some(AnnealAttr::VacuousOk(r)) => {
                if out.vacuous_ok.is_some() {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_DUPLICATE_CLAUSE",
                        attr.span(),
                        "an item may carry at most one `anneal::vacuous_ok` attribute",
                    ));
                }
                out.vacuous_ok = Some((r, attr.span()));
            }
            None => {}
        }
    }
    Ok(out)
}

fn params_of(sig: &syn::Signature, self_ty: Option<Ty>) -> Result<Vec<Param>, Diagnostic> {
    if !sig.generics.params.is_empty() || sig.generics.where_clause.is_some() {
        return Err(Diagnostic::new(
            "E_ANNEAL_UNSUPPORTED_TYPE",
            sig.generics.span(),
            "generic functions are not supported by profile v1 specifications",
        ));
    }
    let mut params = Vec::new();
    let mut seen = BTreeSet::new();
    for input in &sig.inputs {
        match input {
            syn::FnArg::Receiver(r) => {
                if r.reference.is_some() || r.colon_token.is_some() {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_UNSUPPORTED_TYPE",
                        r.span(),
                        "only a by-value `self` receiver is supported in profile v1",
                    ));
                }
                let ty = self_ty.ok_or_else(|| {
                    Diagnostic::new(
                        "E_ANNEAL_UNSUPPORTED_TYPE",
                        r.span(),
                        "`self` is only meaningful inside an `impl` block",
                    )
                })?;
                if !seen.insert("self".to_string()) {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        r.span(),
                        "duplicate parameter name `self`",
                    ));
                }
                params.push(Param { name: "self".into(), ty, span: r.span() });
            }
            syn::FnArg::Typed(pt) => {
                let syn::Pat::Ident(pi) = &*pt.pat else {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        pt.pat.span(),
                        "parameters must be plain identifiers",
                    ));
                };
                let name = pi.ident.to_string();
                if !seen.insert(name.clone()) {
                    return Err(Diagnostic::new(
                        "E_ANNEAL_SPEC_SYNTAX",
                        pi.ident.span(),
                        format!("duplicate parameter name `{name}`"),
                    ));
                }
                params.push(Param { name, ty: parse_type(&pt.ty, self_ty)?, span: pt.span() });
            }
        }
    }
    Ok(params)
}

fn ret_of_spec(sig: &syn::Signature, self_ty: Option<Ty>) -> Result<Ty, Diagnostic> {
    match &sig.output {
        syn::ReturnType::Default => Ok(Ty::Unit),
        syn::ReturnType::Type(_, ty) => match &**ty {
            syn::Type::Never(_) => Ok(Ty::Never),
            _ => parse_type(ty, self_ty),
        },
    }
}

fn ret_of(sig: &syn::Signature, self_ty: Option<Ty>) -> Result<Ty, Diagnostic> {
    match &sig.output {
        syn::ReturnType::Default => Ok(Ty::Unit),
        syn::ReturnType::Type(_, ty) => parse_type(ty, self_ty),
    }
}

/// Builds a [`SpecFn`] from a signature and its `anneal::spec` attribute.
pub fn spec_fn(
    path: String,
    sig: &syn::Signature,
    self_ty: Option<Ty>,
    spec: (TokenStream, Span),
    vacuous_ok: Option<String>,
) -> Result<SpecFn, Diagnostic> {
    let clauses = parse_clauses(spec.0, spec.1)?;
    Ok(SpecFn {
        path,
        params: params_of(sig, self_ty)?,
        ret: ret_of_spec(sig, self_ty)?,
        is_unsafe: sig.unsafety.is_some(),
        clauses,
        vacuous_ok,
        claim: None,
        external: false,
        sig_span: sig.span(),
        attr_span: spec.1,
        file: 0,
    })
}

/// Helper names that would be shadowed by built-in intrinsics, or that are not
/// plain ASCII identifiers and so might not name the same thing in Lean.
fn reserved_helper_name(name: &str) -> bool {
    name == "math"
        || name == "old"
        || name.starts_with("wrapping_")
        || name.starts_with("no_overflow_")
        || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn pure_fn(sig: &syn::Signature, body: &syn::Block) -> Result<PureFn, Diagnostic> {
    if reserved_helper_name(&sig.ident.to_string()) {
        return Err(Diagnostic::new(
            "E_ANNEAL_RESERVED_HELPER_NAME",
            sig.ident.span(),
            format!(
                "`{}` cannot name a `#[anneal::pure]` helper: it is reserved for an \
                 intrinsic or is not an ASCII identifier",
                sig.ident
            ),
        ));
    }
    if sig.unsafety.is_some() {
        return Err(Diagnostic::new(
            "E_ANNEAL_IMPURE_SPEC_EXPR",
            sig.span(),
            "`#[anneal::pure]` helpers cannot be `unsafe`",
        ));
    }
    let expr = match body.stmts.as_slice() {
        [syn::Stmt::Expr(e, None)] => e,
        _ => {
            return Err(Diagnostic::new(
                "E_ANNEAL_IMPURE_SPEC_EXPR",
                body.span(),
                "a `#[anneal::pure]` helper body must be a single expression",
            ))
        }
    };
    Ok(PureFn {
        name: sig.ident.to_string(),
        params: params_of(sig, None)?,
        ret: ret_of(sig, None)?,
        body: parse_expr(expr.to_token_stream(), body.span())?,
        span: sig.span(),
        file: 0,
    })
}

/// Specification items collected from one file, before checking.
#[derive(Default)]
pub struct Collected {
    pub fns: Vec<SpecFn>,
    pub helpers: Vec<PureFn>,
    /// Spans of the `anneal` segment of every `anneal::` path consumed.
    pub handled: Vec<Span>,
}

impl Collected {
    fn push_helper(
        &mut self,
        attrs: &FnAttrs,
        sig: &syn::Signature,
        block: &syn::Block,
    ) -> Result<(), Diagnostic> {
        if attrs.spec.is_some() {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SYNTAX",
                sig.span(),
                "a `#[anneal::pure]` helper cannot also carry `anneal::spec`",
            ));
        }
        attrs.reject_vacuous_ok("on a `#[anneal::pure]` helper")?;
        self.helpers.push(pure_fn(sig, block)?);
        Ok(())
    }
}

fn join_path(prefix: &[String], name: &str) -> String {
    prefix.iter().map(String::as_str).chain([name]).collect::<Vec<_>>().join("::")
}

fn type_path(ty: &syn::Type) -> Result<String, Diagnostic> {
    match ty {
        syn::Type::Tuple(t) if t.elems.is_empty() => Ok("()".into()),
        syn::Type::Path(p)
            if p.qself.is_none() && p.path.segments.iter().all(|s| s.arguments.is_none()) =>
        {
            Ok(token_path(p.path.to_token_stream()))
        }
        _ => Err(unsupported_type(ty)),
    }
}

fn trait_path(path: &syn::Path) -> Result<String, Diagnostic> {
    if path.segments.iter().any(|s| !s.arguments.is_none()) {
        return Err(Diagnostic::new(
            "E_ANNEAL_UNSUPPORTED_TYPE",
            path.span(),
            "generic traits are not supported by profile v1 specifications",
        ));
    }
    Ok(token_path(path.to_token_stream()))
}

fn self_spec_ty(ty: &syn::Type) -> Option<Ty> {
    parse_type(ty, None).ok()
}

/// `impl Trait for Ty { fn ...; }` inside `external_spec!`.
struct ExtImpl {
    trait_path: syn::Path,
    self_ty: syn::Type,
    fns: Vec<ExtFn>,
}

/// A bodiless function declaration, or a helper with a body.
struct ExtFn {
    attrs: Vec<Attribute>,
    sig: syn::Signature,
    body: Option<syn::Block>,
}

enum ExtItem {
    Impl(ExtImpl),
    Mod(syn::Path, Vec<ExtFn>),
    Fn(ExtFn),
}

impl Parse for ExtFn {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let sig: syn::Signature = input.parse()?;
        let body = if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            None
        } else {
            Some(input.parse()?)
        };
        Ok(ExtFn { attrs, sig, body })
    }
}

fn parse_fns(input: ParseStream<'_>) -> syn::Result<Vec<ExtFn>> {
    let mut fns = Vec::new();
    while !input.is_empty() {
        fns.push(input.parse()?);
    }
    Ok(fns)
}

struct ExternalSpec(Vec<ExtItem>);

impl Parse for ExternalSpec {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut items = Vec::new();
        while !input.is_empty() {
            if input.peek(Token![impl]) {
                input.parse::<Token![impl]>()?;
                let trait_path: syn::Path = input.call(syn::Path::parse_mod_style)?;
                input.parse::<Token![for]>()?;
                let self_ty: syn::Type = input.parse()?;
                let content;
                syn::braced!(content in input);
                items.push(ExtItem::Impl(ExtImpl {
                    trait_path,
                    self_ty,
                    fns: parse_fns(&content)?,
                }));
            } else if input.peek(Token![mod]) {
                input.parse::<Token![mod]>()?;
                let path = input.call(syn::Path::parse_mod_style)?;
                let content;
                syn::braced!(content in input);
                items.push(ExtItem::Mod(path, parse_fns(&content)?));
            } else {
                items.push(ExtItem::Fn(input.parse()?));
            }
        }
        Ok(ExternalSpec(items))
    }
}

fn require_spec(attrs: &FnAttrs, sig: &syn::Signature) -> Result<(TokenStream, Span), Diagnostic> {
    attrs.spec.clone().ok_or_else(|| {
        Diagnostic::new(
            "E_ANNEAL_SPEC_SYNTAX",
            sig.span(),
            "a function declared in `external_spec!` needs an `anneal::spec` attribute",
        )
    })
}

fn collect_ext_fn(
    out: &mut Collected,
    f: &ExtFn,
    path: String,
    self_ty: Option<Ty>,
) -> Result<(), Diagnostic> {
    let attrs = collect_attrs(&f.attrs, true, &mut out.handled)?;
    if attrs.pure {
        let Some(body) = &f.body else {
            return Err(Diagnostic::new(
                "E_ANNEAL_SPEC_SYNTAX",
                f.sig.span(),
                "a `#[anneal::pure]` helper needs a body",
            ));
        };
        return out.push_helper(&attrs, &f.sig, body);
    }
    if let Some(body) = &f.body {
        return Err(Diagnostic::new(
            "E_ANNEAL_SPEC_SYNTAX",
            body.span(),
            "functions declared in `external_spec!` take no body; end the declaration with `;`",
        ));
    }
    let spec = require_spec(&attrs, &f.sig)?;
    let vacuous_ok = attrs.vacuous_ok.map(|(r, _)| r);
    let mut spec_f = apply_target(spec_fn(path, &f.sig, self_ty, spec, vacuous_ok)?)?;
    spec_f.external = true;
    out.fns.push(spec_f);
    Ok(())
}

/// Parses the body of one `external_spec! { ... }` invocation. Paths inside
/// are relative to the crate root.
pub fn parse_external(tokens: TokenStream, out: &mut Collected) -> Result<(), Diagnostic> {
    let ExternalSpec(items) = syn::parse2(tokens)?;
    for item in items {
        match item {
            ExtItem::Impl(imp) => {
                let ty_path = type_path(&imp.self_ty)?;
                let tr = trait_path(&imp.trait_path)?;
                let self_ty = self_spec_ty(&imp.self_ty);
                for f in &imp.fns {
                    let path = format!("<{ty_path} as {tr}>::{}", f.sig.ident);
                    collect_ext_fn(out, f, path, self_ty)?;
                }
            }
            ExtItem::Mod(path, fns) => {
                let prefix: Vec<String> =
                    path.segments.iter().map(|s| s.ident.to_string()).collect();
                for f in &fns {
                    collect_ext_fn(out, f, join_path(&prefix, &f.sig.ident.to_string()), None)?;
                }
            }
            ExtItem::Fn(f) => {
                let name = f.sig.ident.to_string();
                collect_ext_fn(out, &f, name, None)?;
            }
        }
    }
    Ok(())
}

fn is_external_spec_macro(path: &syn::Path) -> bool {
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    matches!(segs.as_slice(), [n] if n == "external_spec")
        || matches!(segs.as_slice(), [a, n] if a == "anneal" && n == "external_spec")
}

/// Applies a `target = "..."` clause, which overrides the derived path, and
/// validates and records a `claim = "..."` clause.
///
/// The path is emitted into `Spec.lean`, so it is restricted to characters
/// that can appear in a Rust item path: in particular, no `/`, quote,
/// backslash, or control character can open a Lean comment or end a string.
fn apply_target(mut f: SpecFn) -> Result<SpecFn, Diagnostic> {
    // Duplicates are rejected here, not only when lowering, because
    // `list_targets` reports these values without lowering.
    let (mut target_seen, mut claim_seen) = (false, false);
    for c in &f.clauses {
        let duplicate = match &c.clause {
            Clause::Target(_) => std::mem::replace(&mut target_seen, true),
            Clause::Claim(_) => std::mem::replace(&mut claim_seen, true),
            _ => false,
        };
        if duplicate {
            return Err(Diagnostic::new(
                "E_ANNEAL_DUPLICATE_CLAUSE",
                c.span,
                "at most one `target` and one `claim` clause are allowed",
            ));
        }
        if let Clause::Target(t) = &c.clause {
            let ok = !t.is_empty()
                && t.chars().all(|ch| ch.is_ascii_alphanumeric() || "_:<>(),[]&*;' ".contains(ch));
            if !ok {
                return Err(Diagnostic::new(
                    "E_ANNEAL_INVALID_TARGET",
                    c.span,
                    format!("`{}` is not a Rust item path", t.escape_debug()),
                ));
            }
            f.path = t.clone();
        }
        if let Clause::Claim(id) = &c.clause {
            if !is_claim_ident(id) {
                return Err(Diagnostic::new(
                    "E_ANNEAL_INVALID_CLAIM",
                    c.span,
                    format!(
                        "`{}` is not a valid claim name: use 1 to 64 ASCII letters, digits, and \
                         `_`, starting with a letter, other than a reserved Lean or Anneal name",
                        id.escape_debug()
                    ),
                ));
            }
            f.claim = Some(id.clone());
        }
    }
    Ok(f)
}

/// Names that a claim identifier may not take, compared case-insensitively:
/// Anneal's module roots and the Lean names a claim namespace could shadow.
const RESERVED_CLAIM_NAMES: &[&str] = &[
    "Trusted",
    "Anneal",
    "Captured",
    "Expected",
    "Specs",
    "Spec",
    "Generated",
    "Proof",
    "ProofLib",
    "Pure",
    "Shared",
    "Handwritten",
    "Bodies",
    "TraitMeta",
    "Init",
    "Lean",
    "Std",
    "Option",
    "List",
    "Nat",
    "Int",
    "Bool",
    "Fin",
    "BitVec",
    "Classical",
    "Prop",
    "Type",
    "Sort",
    "True",
    "False",
    "namespace",
    "section",
    "end",
    "def",
    "theorem",
    "open",
    "import",
    "module",
    "prelude",
    "private",
    "public",
    "fun",
    "match",
    "with",
    "if",
    "then",
    "else",
    "let",
    "do",
    "where",
    "instance",
    "structure",
    "class",
    "inductive",
    "axiom",
    "variable",
    "universe",
    // Identifier components that `cargo-anneal`'s specification preflight
    // rejects anywhere in a specification.
    "autoParam",
    "panic",
    "panicCore",
    "panicWithPos",
    "panicWithPosWithDecl",
    "outOfBounds",
    "repeatM",
    "sliceOrPanic",
];

/// Whether `id` can name a claim: a 1-to-64-character ASCII identifier that
/// starts with a letter and is not reserved.
pub fn is_claim_ident(id: &str) -> bool {
    (1..=64).contains(&id.len())
        && id.starts_with(|c: char| c.is_ascii_alphabetic())
        && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !RESERVED_CLAIM_NAMES.iter().any(|r| r.eq_ignore_ascii_case(id))
}

/// Walks the items of one Rust source file whose module path is `module`,
/// collecting inline `#[cfg_attr(anneal, anneal::spec(...))]` items and
/// `anneal::external_spec!` invocations.
pub fn collect_items(
    items: &[syn::Item],
    module: &[String],
    out: &mut Collected,
) -> Result<(), Diagnostic> {
    for item in items {
        match item {
            syn::Item::Fn(f) => {
                let attrs = collect_attrs(&f.attrs, false, &mut out.handled)?;
                if attrs.pure {
                    out.push_helper(&attrs, &f.sig, &f.block)?;
                } else if let Some(spec) = attrs.spec.clone() {
                    let path = join_path(module, &f.sig.ident.to_string());
                    let vacuous_ok = attrs.vacuous_ok.map(|(r, _)| r);
                    out.fns.push(apply_target(spec_fn(path, &f.sig, None, spec, vacuous_ok)?)?);
                } else {
                    attrs.reject_vacuous_ok("without an `anneal::spec` attribute")?;
                }
            }
            syn::Item::Impl(imp) => {
                let self_ty = self_spec_ty(&imp.self_ty);
                for ii in &imp.items {
                    let syn::ImplItem::Fn(f) = ii else { continue };
                    let attrs = collect_attrs(&f.attrs, false, &mut out.handled)?;
                    if attrs.pure {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_SPEC_SYNTAX",
                            f.sig.span(),
                            "`#[anneal::pure]` helpers must be free functions",
                        ));
                    }
                    let Some(spec) = attrs.spec.clone() else {
                        attrs.reject_vacuous_ok("without an `anneal::spec` attribute")?;
                        continue;
                    };
                    let base = if module.is_empty() {
                        match &imp.trait_ {
                            Some((None, tr, _)) => {
                                format!(
                                    "<{} as {}>::{}",
                                    type_path(&imp.self_ty)?,
                                    trait_path(tr)?,
                                    f.sig.ident
                                )
                            }
                            _ => String::new(),
                        }
                    } else {
                        String::new()
                    };
                    let vacuous_ok = attrs.vacuous_ok.map(|(r, _)| r);
                    let spec_f = apply_target(spec_fn(base, &f.sig, self_ty, spec, vacuous_ok)?)?;
                    if spec_f.path.is_empty() {
                        return Err(Diagnostic::new(
                            "E_ANNEAL_TARGET_REQUIRED",
                            f.sig.span(),
                            "this `impl` method requires an explicit `target = \"...\"` clause",
                        ));
                    }
                    out.fns.push(spec_f);
                }
            }
            syn::Item::Mod(m) => {
                if let Some((_, items)) = &m.content {
                    let mut sub = module.to_vec();
                    sub.push(m.ident.to_string());
                    collect_items(items, &sub, out)?;
                }
            }
            syn::Item::Macro(m) if is_external_spec_macro(&m.mac.path) => {
                if m.mac.path.segments.len() == 2 {
                    out.handled.push(m.mac.path.segments[0].ident.span());
                }
                parse_external(m.mac.tokens.clone(), out)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// `anneal::` uses this parser cannot follow, with a diagnostic code:
/// - `anneal::{spec,pure,vacuous_ok,external_spec}` paths that are not in
///   `handled`, i.e. in positions this parser does not read (for example
///   inside a function body or a `cfg_attr` with another predicate), which
///   would otherwise be dropped silently; and
/// - imports or renames of the crate (`use anneal::*`, `use anneal::{..}`,
///   `use anneal as a`, `extern crate anneal as a`), after which a bare
///   `#[spec(..)]` or `#[a::spec(..)]` would be a live attribute this parser
///   does not recognize.
pub fn ignored_anneal_paths(stream: TokenStream, handled: &[Span]) -> Vec<(Span, &'static str)> {
    fn key(s: Span) -> (usize, usize) {
        (s.start().line, s.start().column)
    }
    fn walk(
        stream: TokenStream,
        handled: &[(usize, usize)],
        in_attr: bool,
        out: &mut Vec<(Span, &'static str)>,
    ) {
        let tts: Vec<TokenTree> = stream.into_iter().collect();
        let is_attr_bracket = |idx: usize| -> bool {
            let bang_bracket = idx >= 2
                && matches!(tts.get(idx - 2), Some(TokenTree::Punct(p)) if p.as_char() == '#')
                && matches!(tts.get(idx - 1), Some(TokenTree::Punct(p)) if p.as_char() == '!');
            let hash_bracket = idx >= 1
                && matches!(tts.get(idx - 1), Some(TokenTree::Punct(p)) if p.as_char() == '#');
            bang_bracket || hash_bracket
        };
        let colon =
            |j: usize| matches!(tts.get(j), Some(TokenTree::Punct(p)) if p.as_char() == ':');
        for (i, tt) in tts.iter().enumerate() {
            if let TokenTree::Group(g) = tt {
                let next_attr =
                    in_attr || (g.delimiter() == Delimiter::Bracket && is_attr_bracket(i));
                walk(g.stream(), handled, next_attr, out);
            }
            let TokenTree::Ident(id) = tt else { continue };
            let path = colon(i + 1) && colon(i + 2);
            if id == "anneal" {
                let renamed = matches!(tts.get(i + 1), Some(TokenTree::Ident(n)) if n == "as");
                let glob = path
                    && matches!(tts.get(i + 3), Some(TokenTree::Punct(p)) if p.as_char() == '*')
                    || path
                        && matches!(tts.get(i + 3), Some(TokenTree::Group(g))
                            if g.delimiter() == Delimiter::Brace);
                let named = path
                    && matches!(tts.get(i + 3), Some(TokenTree::Ident(n))
                        if ["spec", "pure", "vacuous_ok", "external_spec"].iter().any(|k| n == k));
                if renamed || glob {
                    out.push((id.span(), "E_ANNEAL_UNSUPPORTED_IMPORT"));
                } else if named && !handled.contains(&key(id.span())) {
                    out.push((id.span(), "E_ANNEAL_IGNORED_ATTRIBUTE"));
                }
            } else if path {
                // Reject Cargo-renamed `#[alias::spec(...)]` attributes and
                // `alias::external_spec! { ... }` invocations that bypass
                // `id == "anneal"`.
                let Some(TokenTree::Ident(n)) = tts.get(i + 3) else { continue };
                let name = n.to_string();
                let is_attr = in_attr && matches!(name.as_str(), "spec" | "pure" | "vacuous_ok");
                let is_macro = name == "external_spec"
                    && matches!(tts.get(i + 4), Some(TokenTree::Punct(p)) if p.as_char() == '!')
                    && matches!(tts.get(i + 5), Some(TokenTree::Group(_)));
                if is_attr || is_macro {
                    out.push((id.span(), "E_ANNEAL_UNSUPPORTED_IMPORT"));
                }
            }
        }
    }
    let handled: Vec<_> = handled.iter().map(|s| key(*s)).collect();
    let mut out = Vec::new();
    walk(stream, &handled, false, &mut out);
    out
}

/// Uses of the `anneal` cfg, or of the identifier `anneal`, other than
/// `#[cfg_attr(anneal, A)]` where `A` is `anneal::spec(..)`, `anneal::pure`, or
/// `anneal::vacuous_ok(..)`, and `anneal::` paths.
///
/// Those attributes carry specifications and nothing else. Any other code
/// conditional on `anneal` (a `#[cfg(anneal)]` item, a compound predicate such
/// as `cfg_attr(any(anneal, x), ..)`, or `cfg!(anneal)`) would make the crate
/// the specifications describe differ from the crate users build. A macro can
/// assemble such a predicate from tokens that are never adjacent in the source
/// (`#[cfg($p)]` with `m!(not(anneal))`), so the identifier `anneal` is
/// reserved: it may appear only as the predicate of an accepted `cfg_attr` or
/// at the start of an `anneal::{spec,pure,vacuous_ok,external_spec}` path.
pub fn cfg_anneal_misuse(stream: TokenStream) -> Vec<Span> {
    /// Whether `id` is `name`, written plainly or as the raw identifier
    /// `r#name`, which `rustc` treats identically in a cfg.
    fn is(id: &proc_macro2::Ident, name: &str) -> bool {
        let s = id.to_string();
        s.strip_prefix("r#").unwrap_or(&s) == name
    }
    fn mentions_anneal(stream: TokenStream) -> bool {
        stream.into_iter().any(|tt| match tt {
            TokenTree::Ident(id) => is(&id, "anneal"),
            TokenTree::Group(g) => mentions_anneal(g.stream()),
            _ => false,
        })
    }
    fn is_spec_attr(part: &[TokenTree]) -> bool {
        let colon =
            |t: Option<&TokenTree>| matches!(t, Some(TokenTree::Punct(p)) if p.as_char() == ':');
        let head = matches!(part.first(), Some(TokenTree::Ident(a)) if a == "anneal")
            && colon(part.get(1))
            && colon(part.get(2));
        let name = match part.get(3) {
            Some(TokenTree::Ident(n)) => n.to_string(),
            _ => return false,
        };
        let args_ok = match &part[4.min(part.len())..] {
            [] => true,
            [TokenTree::Group(g)] => g.delimiter() == Delimiter::Parenthesis,
            _ => false,
        };
        head && matches!(name.as_str(), "spec" | "pure" | "vacuous_ok") && args_ok
    }
    /// Walks `stream`. `in_attr` is set inside `#[..]` and `#![..]`;
    /// `reported` inside a group already reported, so that one misuse yields
    /// one diagnostic; `allow_first` for the arguments of an accepted
    /// `cfg_attr`, whose first token is its `anneal` predicate.
    fn walk(
        stream: TokenStream,
        in_attr: bool,
        reported: bool,
        allow_first: bool,
        out: &mut Vec<Span>,
    ) {
        let tts: Vec<TokenTree> = stream.into_iter().collect();
        let punct = |j: Option<usize>, c: char| matches!(j.and_then(|j| tts.get(j)), Some(TokenTree::Punct(p)) if p.as_char() == c);
        let group = |j: usize| match tts.get(j) {
            Some(TokenTree::Group(g)) => Some(g.stream()),
            _ => None,
        };
        // Groups whose contents are already reported, and the arguments of
        // accepted `cfg_attr`s.
        let mut covered = vec![false; tts.len() + 2];
        let mut accepted = vec![false; tts.len() + 2];
        for (i, tt) in tts.iter().enumerate() {
            if let TokenTree::Group(g) = tt {
                // `#[..]` or `#![..]`.
                let attr = in_attr
                    || (g.delimiter() == Delimiter::Bracket
                        && (punct(i.checked_sub(1), '#')
                            || (punct(i.checked_sub(1), '!') && punct(i.checked_sub(2), '#'))));
                walk(g.stream(), attr, reported || covered[i], accepted[i], out);
                continue;
            }
            let TokenTree::Ident(id) = tt else { continue };
            if reported {
                continue;
            }
            // The index of the arguments of a misused `cfg`, `cfg!`, or
            // `cfg_attr`.
            let mut misused = None;
            if is(id, "anneal") {
                // Exactly `anneal::spec`, `anneal::pure`, `anneal::vacuous_ok`,
                // or `anneal::external_spec`. `ignored_anneal_paths` rejects
                // those that are not in a position the parser reads, such as
                // macro arguments.
                let joint = matches!(tts.get(i + 1),
                    Some(TokenTree::Punct(p)) if p.as_char() == ':' && p.spacing() == Spacing::Joint);
                let named = matches!(tts.get(i + 3), Some(TokenTree::Ident(n))
                    if ["spec", "pure", "vacuous_ok", "external_spec"].iter().any(|k| n == k));
                let path = *id == "anneal" && joint && punct(Some(i + 2), ':') && named;
                if !path && !(allow_first && i == 0) {
                    out.push(id.span());
                }
            } else if is(id, "cfg") && punct(Some(i + 1), '!') {
                if group(i + 2).is_some_and(mentions_anneal) {
                    misused = Some(i + 2);
                }
            } else if in_attr && is(id, "cfg") {
                if group(i + 1).is_some_and(mentions_anneal) {
                    misused = Some(i + 1);
                }
            } else if in_attr && is(id, "cfg_attr") {
                let Some(args) = group(i + 1) else { continue };
                let mut parts = split_commas(args).into_iter();
                let pred: Vec<TokenTree> = parts.next().unwrap_or_default().into_iter().collect();
                if !mentions_anneal(pred.iter().cloned().collect()) {
                    continue;
                }
                let exact = matches!(pred.as_slice(), [TokenTree::Ident(a)] if a == "anneal");
                let attrs: Vec<Vec<TokenTree>> = parts
                    .map(|p| p.into_iter().collect())
                    .filter(|p: &Vec<_>| !p.is_empty())
                    .collect();
                if exact && matches!(attrs.as_slice(), [a] if is_spec_attr(a)) {
                    accepted[i + 1] = true;
                } else {
                    misused = Some(i + 1);
                }
            }
            if let Some(args) = misused {
                out.push(id.span());
                covered[args] = true;
            }
        }
    }
    let mut out = Vec::new();
    walk(stream, false, false, false, &mut out);
    out
}

/// Checks only the syntax of an `anneal::spec(...)` argument list.
pub fn check_clause_syntax(stream: TokenStream, span: Span) -> Result<(), Diagnostic> {
    parse_clauses(stream, span).map(|_| ())
}

/// Checks only the syntax of an `external_spec! { ... }` body.
pub fn check_external_syntax(stream: TokenStream) -> Result<(), Diagnostic> {
    parse_external(stream, &mut Collected::default())
}
