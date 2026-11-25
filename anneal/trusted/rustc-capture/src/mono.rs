// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Structured parsing and fail-closed compiler resolution for explicit concrete
//! monomorphization requests (`Scope::SelectedUnit { instantiations, .. }`).

use std::ops::ControlFlow;

use rustc_hir::def::{DefKind, Namespace, Res};
use rustc_hir::def_id::{CRATE_DEF_ID, CRATE_DEF_INDEX, DefId, LOCAL_CRATE, LocalDefId};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_infer::traits::Obligation;
use rustc_metadata::creader::CStore;
use rustc_middle::metadata::{AmbigModChild, ModChild};
use rustc_middle::mir;
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{
    self, EarlyBinder, GenericArg, GenericArgsRef, Instance, InstanceKind, Ty, TyCtxt,
    TypeFoldable, TypeSuperVisitable, TypeVisitable, TypeVisitableExt, TypeVisitor,
};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::traits::{ObligationCtxt, wf};

const MAX_AST_DEPTH: usize = 32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IntSpec {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FloatSpec {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum MonoTyAst {
    Unit,
    Never,
    Bool,
    Char,
    Str,
    Int(IntSpec),
    Float(FloatSpec),
    Tuple(Vec<MonoTyAst>),
    Array(Box<MonoTyAst>, u64),
    Slice(Box<MonoTyAst>),
    Ref { mutable: bool, elem: Box<MonoTyAst> },
    RawPtr { mutable: bool, elem: Box<MonoTyAst> },
    Adt { leading_colons: bool, path: Vec<String>, args: Vec<MonoArgAst> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum MonoArgAst {
    RegionStatic,
    ConstBool(bool),
    ConstChar(char),
    ConstInt { negative: bool, magnitude: u128, suffix: Option<IntSpec> },
    Ty(MonoTyAst),
}

struct Parser<'a> {
    src: &'a str,
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(src: &'a str) -> Self {
        Self { src, pos: 0 }
    }

    fn rest(&self) -> &'a str {
        &self.src[self.pos..]
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.rest().chars().next() {
            if ch.is_whitespace() {
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }
    }

    fn starts_with(&mut self, prefix: &str) -> bool {
        self.skip_ws();
        self.rest().starts_with(prefix)
    }

    fn eat(&mut self, prefix: &str) -> bool {
        self.skip_ws();
        if self.rest().starts_with(prefix) {
            self.pos += prefix.len();
            true
        } else {
            false
        }
    }

    fn eat_ident(&mut self) -> Option<&'a str> {
        self.skip_ws();
        let rest = self.rest();
        let mut chars = rest.char_indices();
        let (_, first) = chars.next()?;
        if !(first.is_ascii_alphabetic() || first == '_') {
            return None;
        }
        let mut end = first.len_utf8();
        for (idx, ch) in chars {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                end = idx + ch.len_utf8();
            } else {
                break;
            }
        }
        let ident = &rest[..end];
        self.pos += end;
        Some(ident)
    }

    fn parse_arg(&mut self, depth: usize) -> Result<MonoArgAst, String> {
        if depth > MAX_AST_DEPTH {
            return Err("generic argument nesting exceeds maximum depth".into());
        }
        self.skip_ws();
        if self.eat("'static") {
            if self.rest().chars().next().is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err("unexpected identifier suffix after `'static`".into());
            }
            return Ok(MonoArgAst::RegionStatic);
        }
        if self.rest().starts_with("'_") && !self.rest().starts_with("'_'") {
            self.pos += 2;
            if self.rest().chars().next().is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err("unexpected identifier suffix after `'_`".into());
            }
            return Ok(MonoArgAst::RegionStatic);
        }
        if self.rest().starts_with('\'') {
            return Ok(MonoArgAst::ConstChar(self.parse_char_lit()?));
        }
        if self.rest().starts_with('-')
            || self.rest().chars().next().is_some_and(|c| c.is_ascii_digit())
        {
            return self.parse_int_lit();
        }
        if self.starts_with("true") && keyword_boundary(self.rest(), "true") {
            self.pos += "true".len();
            return Ok(MonoArgAst::ConstBool(true));
        }
        if self.starts_with("false") && keyword_boundary(self.rest(), "false") {
            self.pos += "false".len();
            return Ok(MonoArgAst::ConstBool(false));
        }
        Ok(MonoArgAst::Ty(self.parse_ty(depth + 1)?))
    }

    fn parse_ty(&mut self, depth: usize) -> Result<MonoTyAst, String> {
        if depth > MAX_AST_DEPTH {
            return Err("generic type nesting exceeds maximum depth".into());
        }
        self.skip_ws();
        if self.eat("!") {
            return Ok(MonoTyAst::Never);
        }
        if self.eat("(") {
            self.skip_ws();
            if self.eat(")") {
                return Ok(MonoTyAst::Unit);
            }
            let first = self.parse_ty(depth + 1)?;
            self.skip_ws();
            if self.eat(")") {
                return Ok(first);
            }
            if !self.eat(",") {
                return Err("expected `,` or `)` in tuple type".into());
            }
            let mut elems = vec![first];
            loop {
                self.skip_ws();
                if self.eat(")") {
                    break;
                }
                elems.push(self.parse_ty(depth + 1)?);
                self.skip_ws();
                if self.eat(",") {
                    continue;
                }
                if self.eat(")") {
                    break;
                }
                return Err("expected `,` or `)` in tuple type".into());
            }
            return Ok(MonoTyAst::Tuple(elems));
        }
        if self.eat("[") {
            let elem = self.parse_ty(depth + 1)?;
            self.skip_ws();
            if self.eat(";") {
                let len = self.parse_array_len()?;
                self.skip_ws();
                if !self.eat("]") {
                    return Err("expected `]` after array length".into());
                }
                return Ok(MonoTyAst::Array(Box::new(elem), len));
            }
            if !self.eat("]") {
                return Err("expected `;` or `]` in slice/array type".into());
            }
            return Ok(MonoTyAst::Slice(Box::new(elem)));
        }
        if self.eat("&") {
            self.skip_ws();
            if self.eat("'static") || self.eat("'_") {
                if self.rest().chars().next().is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    return Err("invalid lifetime in reference type".into());
                }
            } else if self.rest().starts_with('\'') {
                return Err("only `'static` or `'_` lifetimes are supported in reference types".into());
            }
            let mutable = self.eat_kw("mut");
            let elem = self.parse_ty(depth + 1)?;
            return Ok(MonoTyAst::Ref { mutable, elem: Box::new(elem) });
        }
        if self.eat("*") {
            let mutable = if self.eat_kw("const") {
                false
            } else if self.eat_kw("mut") {
                true
            } else {
                return Err("expected `const` or `mut` after `*` in raw pointer type".into());
            };
            let elem = self.parse_ty(depth + 1)?;
            return Ok(MonoTyAst::RawPtr { mutable, elem: Box::new(elem) });
        }

        let leading_colons = self.eat("::");
        let first = self.eat_ident().ok_or_else(|| {
            format!("expected type identifier near {:?}", self.rest())
        })?;
        if !leading_colons
            && !self.starts_with("::")
            && !self.starts_with("<")
            && let Some(prim) = primitive_ty(first)
        {
            return Ok(prim);
        }
        let mut path = vec![first.to_owned()];
        while self.eat("::") {
            let seg = self.eat_ident().ok_or_else(|| {
                format!("expected path segment after `::` near {:?}", self.rest())
            })?;
            path.push(seg.to_owned());
        }
        let mut args = Vec::new();
        if self.eat("<") {
            self.skip_ws();
            if !self.eat(">") {
                loop {
                    args.push(self.parse_arg(depth + 1)?);
                    self.skip_ws();
                    if self.eat(",") {
                        self.skip_ws();
                        if self.eat(">") {
                            break;
                        }
                        continue;
                    }
                    if self.eat(">") {
                        break;
                    }
                    return Err(format!("expected `,` or `>` in generic args near {:?}", self.rest()));
                }
            }
        }
        Ok(MonoTyAst::Adt { leading_colons, path, args })
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        self.skip_ws();
        if keyword_boundary(self.rest(), kw) {
            self.pos += kw.len();
            true
        } else {
            false
        }
    }

    fn parse_char_lit(&mut self) -> Result<char, String> {
        self.skip_ws();
        let rest = self.rest();
        if !rest.starts_with('\'') {
            return Err("expected character literal".into());
        }
        let mut chars = rest[1..].char_indices();
        let Some((idx0, ch0)) = chars.next() else {
            return Err("unterminated character literal".into());
        };
        let (ch, after_idx) = if ch0 == '\'' {
            return Err("unescaped `'` in character literal".into());
        } else if ch0 == '\\' {
            let Some((_, esc)) = chars.next() else {
                return Err("unterminated escape in character literal".into());
            };
            match esc {
                'n' => ('\n', 1 + 2),
                'r' => ('\r', 1 + 2),
                't' => ('\t', 1 + 2),
                '\\' => ('\\', 1 + 2),
                '\'' => ('\'', 1 + 2),
                '0' => ('\0', 1 + 2),
                'x' => {
                    let h1 = chars.next().map(|(_, c)| c).ok_or("short \\x escape")?;
                    let h2 = chars.next().map(|(_, c)| c).ok_or("short \\x escape")?;
                    if !h1.is_ascii_hexdigit() || !h2.is_ascii_hexdigit() {
                        return Err("invalid \\x hex escape".into());
                    }
                    let byte = u8::from_str_radix(&format!("{h1}{h2}"), 16)
                        .map_err(|_| "invalid \\x hex escape".to_owned())?;
                    if byte > 0x7f {
                        return Err("\\x char escape must be ASCII (<= 0x7f)".into());
                    }
                    (byte as char, 1 + 4)
                }
                _ => return Err(format!("unsupported char escape `\\{esc}`")),
            }
        } else {
            (ch0, 1 + idx0 + ch0.len_utf8())
        };
        if !rest[after_idx..].starts_with('\'') {
            return Err("expected closing `'` in character literal".into());
        }
        self.pos += after_idx + 1;
        Ok(ch)
    }

    fn parse_int_lit(&mut self) -> Result<MonoArgAst, String> {
        self.skip_ws();
        let negative = self.eat("-");
        self.skip_ws();
        let rest = self.rest();
        let (radix, digit_start) = if rest.starts_with("0x") || rest.starts_with("0X") {
            (16u32, 2)
        } else if rest.starts_with("0b") || rest.starts_with("0B") {
            (2u32, 2)
        } else if rest.starts_with("0o") || rest.starts_with("0O") {
            (8u32, 2)
        } else {
            (10u32, 0)
        };
        let mut idx = digit_start;
        let mut digits = String::new();
        for (off, ch) in rest[digit_start..].char_indices() {
            if ch == '_' {
                idx = digit_start + off + 1;
            } else if ch.is_digit(radix) {
                digits.push(ch);
                idx = digit_start + off + ch.len_utf8();
            } else {
                break;
            }
        }
        if digits.is_empty() {
            return Err(format!("expected integer digits near {:?}", rest));
        }
        let magnitude = u128::from_str_radix(&digits, radix)
            .map_err(|_| format!("integer literal `{digits}` overflows u128"))?;
        self.pos += idx;
        let mut suffix = None;
        let tail = self.rest();
        if tail.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_') {
            let ident = self.eat_ident().ok_or("invalid integer suffix")?;
            let parsed = parse_int_spec(ident)
                .ok_or_else(|| format!("unsupported integer literal suffix `{ident}`"))?;
            suffix = Some(parsed);
        }
        Ok(MonoArgAst::ConstInt { negative, magnitude, suffix })
    }

    fn parse_array_len(&mut self) -> Result<u64, String> {
        match self.parse_int_lit()? {
            MonoArgAst::ConstInt { negative: false, magnitude, suffix } => {
                if let Some(s) = suffix
                    && s != IntSpec::Usize
                {
                    return Err("array length suffix must be `usize` if specified".into());
                }
                u64::try_from(magnitude).map_err(|_| "array length overflows u64".into())
            }
            _ => Err("array length must be a non-negative integer literal".into()),
        }
    }
}

fn keyword_boundary(rest: &str, kw: &str) -> bool {
    let Some(after) = rest.strip_prefix(kw) else {
        return false;
    };
    !after.chars().next().is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn parse_int_spec(name: &str) -> Option<IntSpec> {
    Some(match name {
        "u8" => IntSpec::U8,
        "u16" => IntSpec::U16,
        "u32" => IntSpec::U32,
        "u64" => IntSpec::U64,
        "u128" => IntSpec::U128,
        "usize" => IntSpec::Usize,
        "i8" => IntSpec::I8,
        "i16" => IntSpec::I16,
        "i32" => IntSpec::I32,
        "i64" => IntSpec::I64,
        "i128" => IntSpec::I128,
        "isize" => IntSpec::Isize,
        _ => return None,
    })
}

fn primitive_ty(name: &str) -> Option<MonoTyAst> {
    if let Some(int) = parse_int_spec(name) {
        return Some(MonoTyAst::Int(int));
    }
    Some(match name {
        "bool" => MonoTyAst::Bool,
        "char" => MonoTyAst::Char,
        "str" => MonoTyAst::Str,
        "f16" => MonoTyAst::Float(FloatSpec::F16),
        "f32" => MonoTyAst::Float(FloatSpec::F32),
        "f64" => MonoTyAst::Float(FloatSpec::F64),
        "f128" => MonoTyAst::Float(FloatSpec::F128),
        _ => return None,
    })
}

fn parse_mono_arg(input: &str) -> Result<MonoArgAst, String> {
    let mut parser = Parser::new(input);
    let arg = parser.parse_arg(0)?;
    parser.skip_ws();
    if !parser.rest().is_empty() {
        return Err(format!(
            "unexpected trailing tokens in generic argument {input:?}: {:?}",
            parser.rest()
        ));
    }
    Ok(arg)
}

pub(crate) fn resolve_callable_def_id(tcx: TyCtxt<'_>, path: &str) -> Result<LocalDefId, String> {
    let mut matches = Vec::new();
    for local_def in tcx.hir_crate_items(()).definitions() {
        let def_id = local_def.to_def_id();
        let kind = tcx.def_kind(def_id);
        if matches!(kind, DefKind::Fn | DefKind::AssocFn) && tcx.def_path_str(def_id) == path {
            matches.push(local_def);
        }
    }
    match matches.len() {
        0 => Err(format!("selected generic function `{path}` was not found")),
        1 => Ok(matches[0]),
        _ => Err(format!("selected generic function `{path}` resolved ambiguously")),
    }
}

fn collect_generic_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<&'tcx ty::GenericParamDef> {
    let generics = tcx.generics_of(def_id);
    let mut out = if let Some(parent) = generics.parent {
        collect_generic_params(tcx, parent)
    } else {
        Vec::new()
    };
    out.extend(&generics.own_params);
    out
}

/// Look up child item definitions matching `seg` inside module `mod_did`.
///
/// Routes local modules through `TyCtxt::module_children_local`
/// (`ResolverGlobalCtxt::module_children`) because `TyCtxt::module_children`
/// provides only external-crate metadata (`separate_provide_extern`) and panics
/// on `LOCAL_CRATE` `DefId`s.
///
/// Upstream `TyCtxt::module_children`:
/// "separate_provide_extern"
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/queries.rs#L2160-L2163
/// Upstream `TyCtxt::module_children_local`:
/// "Named module children from all kinds of items, including imports."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/context.rs#L2700-L2711
///
/// Neither list holds a name that glob imports make ambiguous. The resolver
/// records such a name apart from the other children, as two of its
/// candidates (`finalize_resolutions_in`):
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_resolve/src/imports.rs#L1888-L1899
/// A crate's metadata carries those records for each of its modules, and
/// `rustc` reads them back to resolve paths into that crate, so a glob
/// ambiguity is ambiguous across crates too:
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_metadata/src/rmeta/encoder.rs#L1749-L1755
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_resolve/src/build_reduced_graph.rs#L350-L366
/// Any type-namespace ambiguity for `seg`, local or external, therefore fails
/// closed, whichever kinds of definition its two recorded candidates are: they
/// need not include every candidate. Without this check, a walk would treat the
/// name as missing and could let another reading of the path resolve.
///
/// For the same reason, `seg` counts as absent only when the module binds
/// nothing of that name in the type namespace. A binding of any other kind
/// than the walk wants fails closed: a trait, a re-exported primitive type, a
/// module as the last segment, or a struct or enum before it. There `rustc`
/// would name that binding or report an error, never fall back to another
/// definition.
///
/// A `_` segment matches no child. Modules list their underscore imports
/// (`use X as _;`, `extern crate k as _;`) as children named `_`, but no Rust
/// path can name them. Upstream `BindingKey`: "When a key is constructed for
/// name lookup (as opposed to name definition), this field is also zero, even
/// for underscore names, so for underscores the lookup will never succeed."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_resolve/src/lib.rs#L619-L623
/// Upstream `try_plant_decl_into_local_module`: "Even if underscore names
/// cannot be looked up, we still need to add them to modules".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_resolve/src/imports.rs#L612-L614
fn lookup_module_child_defs<'tcx>(
    tcx: TyCtxt<'tcx>,
    mod_did: DefId,
    seg: &str,
    is_last: bool,
    display_path: &str,
) -> Result<Vec<(DefKind, DefId)>, String> {
    if seg == "_" {
        return Ok(Vec::new());
    }
    let names_type =
        |child: &ModChild| child.ident.as_str() == seg && child.res.ns() == Some(Namespace::TypeNS);
    let ambiguous = |entry: &AmbigModChild| names_type(&entry.main) || names_type(&entry.second);
    let (children, is_ambiguous) = if let Some(local_did) = mod_did.as_local() {
        let ambig = tcx.resolutions(()).ambig_module_children.get(&local_did);
        (tcx.module_children_local(local_did), ambig.is_some_and(|v| v.iter().any(ambiguous)))
    } else {
        // External ambiguity records are reachable only through the metadata
        // crate store (`CStore::ambig_module_children_untracked`):
        // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_metadata/src/rmeta/decoder/cstore_impl.rs#L622-L628
        let cstore = tcx.cstore_untracked();
        let Some(cstore) = cstore.as_any().downcast_ref::<CStore>() else {
            return Err(format!(
                "cannot read glob ambiguities of external module `{}` while resolving type path \
                 `{display_path}`: the crate store is not `rustc_metadata`'s",
                tcx.def_path_str(mod_did)
            ));
        };
        let is_ambiguous =
            cstore.ambig_module_children_untracked(tcx, mod_did).any(|entry| ambiguous(&entry));
        (tcx.module_children(mod_did), is_ambiguous)
    };
    if is_ambiguous {
        return Err(format!("type path `{display_path}` resolved ambiguously at segment `{seg}`"));
    }
    let (wanted, matches_wanted_kind): (&str, fn(DefKind) -> bool) = if is_last {
        ("a struct, enum, union, or type alias", |kind| {
            matches!(kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::TyAlias)
        })
    } else {
        ("a module", |kind| matches!(kind, DefKind::Mod))
    };
    let mut hits = Vec::new();
    for child in children.iter().filter(|child| names_type(child)) {
        match child.res {
            Res::Def(kind, next_did) if matches_wanted_kind(kind) => {
                if !hits.contains(&(kind, next_did)) {
                    hits.push((kind, next_did));
                }
            }
            res => {
                return Err(format!(
                    "type `{display_path}` could not be resolved: segment `{seg}` names {} {}, \
                     not {wanted}",
                    res.article(),
                    res.descr()
                ));
            }
        }
    }
    Ok(hits)
}

/// Walk `rest` from module `root` through module children to a type.
///
/// Returns `Ok(None)` when `rest` is empty or some segment names nothing in the
/// type namespace of its module, and fails closed when a segment is ambiguous
/// or names something other than the wanted kind of definition.
fn walk_module_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: DefId,
    rest: &[String],
    display_path: &str,
) -> Result<Option<(DefKind, DefId)>, String> {
    let mut curr_did = root;
    for (idx, seg) in rest.iter().enumerate() {
        let is_last = idx + 1 == rest.len();
        let hits = lookup_module_child_defs(tcx, curr_did, seg, is_last, display_path)?;
        match hits.as_slice() {
            [] => return Ok(None),
            [hit] if is_last => return Ok(Some(*hit)),
            [(_, next_did)] => curr_did = *next_did,
            _ => {
                return Err(format!(
                    "type path `{display_path}` resolved ambiguously at segment `{seg}`"
                ));
            }
        }
    }
    Ok(None)
}

/// Find the local ADT or type alias that `TyCtxt::def_path_str` prints as
/// `rest`, failing closed when it prints several definitions that way.
///
/// This spelling reaches local definitions that no module path reaches, such
/// as a type declared inside a function or inside a `const _` item.
fn local_def_spelled<'tcx>(
    tcx: TyCtxt<'tcx>,
    rest: &[String],
    display_path: &str,
) -> Result<Option<(DefKind, DefId)>, String> {
    let target = rest.join("::");
    let mut matches = tcx.hir_crate_items(()).definitions().filter_map(|local_def| {
        let did = local_def.to_def_id();
        let kind = tcx.def_kind(did);
        let is_type =
            matches!(kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::TyAlias);
        (is_type && tcx.def_path_str(did) == target).then_some((kind, did))
    });
    match (matches.next(), matches.next()) {
        (None, _) => Ok(None),
        (Some(hit), None) => Ok(Some(hit)),
        (Some(_), Some(_)) => Err(format!("type path `{display_path}` resolved ambiguously")),
    }
}

/// Resolve a type path to the ADT or type alias it names.
///
/// `::krate::...` starts at the root of the crate named `krate`, and
/// `crate::...` at the local crate root. Any other path is relative, and this
/// language has no enclosing module in which to resolve its leading segment.
/// Such a path is read both ways its leading segment allows:
///
/// - as a crate name (an external crate, or the local crate by its own name),
///   continuing with the remaining segments from that crate's root; and
/// - as a name in the local crate root, continuing with every segment from
///   there.
///
/// At the crate root `rustc` would rank these readings, upstream
/// `visit_scopes`: "Places to search (in order of decreasing priority): (Type
/// NS) [...] 2. Names in modules [...] 3. Extern prelude".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_resolve/src/ident.rs#L72-L78
/// Here the readings are not ranked. Each reading resolves on its own, and the
/// path resolves only if the readings that resolve all name one definition, so
/// no request silently means a different type than one of its readings says.
/// A leading `_` is not an identifier and names no crate.
///
/// A reading resolves through module children, or failing that as the
/// `def_path_str` spelling of a local definition (`local_def_spelled`). A path
/// that also reads as an external crate's is never taken as such a spelling.
fn resolve_adt_or_alias_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    leading_colons: bool,
    segments: &[String],
) -> Result<(DefKind, DefId), String> {
    if segments.is_empty() {
        return Err("empty type path in generic argument".into());
    }
    let display_path = if leading_colons {
        format!("::{}", segments.join("::"))
    } else {
        segments.join("::")
    };
    let first = &segments[0];
    let after_first = &segments[1..];
    let local_root = CRATE_DEF_ID.to_def_id();

    // Each reading is a root module and the segments that continue from it.
    let readings: Vec<(DefId, &[String])> = if first == "crate" {
        if leading_colons {
            return Err(format!("invalid leading `::crate` in type path `{display_path}`"));
        }
        vec![(local_root, after_first)]
    } else {
        let names_crate = |name: &str| first != "_" && name == first.as_str();
        let ext_crates: Vec<_> = tcx
            .crates(())
            .iter()
            .copied()
            .filter(|&cnum| names_crate(tcx.crate_name(cnum).as_str()))
            .collect();
        let is_local_name = names_crate(tcx.crate_name(LOCAL_CRATE).as_str());
        let named_crate_root = match (ext_crates.as_slice(), is_local_name) {
            ([], false) => None,
            ([], true) => Some(local_root),
            ([krate], false) => Some(DefId { krate: *krate, index: CRATE_DEF_INDEX }),
            ([_], true) => {
                return Err(format!(
                    "crate root `{first}` in type path `{display_path}` is ambiguous between \
                     local and external crates"
                ));
            }
            _ => {
                return Err(format!(
                    "crate `{first}` in type path `{display_path}` resolved ambiguously"
                ));
            }
        };
        let crate_reading = named_crate_root.map(|root| (root, after_first));
        if leading_colons {
            let Some(crate_reading) = crate_reading else {
                return Err(format!(
                    "unknown crate `{first}` in absolute type path `{display_path}`"
                ));
            };
            vec![crate_reading]
        } else {
            crate_reading.into_iter().chain([(local_root, segments)]).collect()
        }
    };

    let spellable = readings.iter().all(|(root, _)| root.is_local());
    let mut hits: Vec<(DefKind, DefId)> = Vec::new();
    for &(root, rest) in &readings {
        let hit = match walk_module_path(tcx, root, rest, &display_path)? {
            None if spellable => local_def_spelled(tcx, rest, &display_path)?,
            walked => walked,
        };
        if let Some(hit) = hit
            && !hits.contains(&hit)
        {
            hits.push(hit);
        }
    }
    match hits.as_slice() {
        [hit] => Ok(*hit),
        [] if readings.iter().any(|(_, rest)| rest.is_empty()) => {
            Err(format!("path `{display_path}` does not name a type"))
        }
        [] => Err(format!("type `{display_path}` could not be resolved")),
        _ => Err(format!(
            "type path `{display_path}` resolved ambiguously: leading segment `{first}` reads \
             as a crate name and as a crate-root name, and the readings name different types"
        )),
    }
}

fn lower_const_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    const_ty: Ty<'tcx>,
    arg: &MonoArgAst,
) -> Result<ty::Const<'tcx>, String> {
    let layout = tcx
        .layout_of(typing_env.as_query_input(const_ty))
        .map_err(|e| format!("failed to compute layout for const parameter `{const_ty}`: {e:?}"))?;
    match (const_ty.kind(), arg) {
        (ty::TyKind::Bool, MonoArgAst::ConstBool(b)) => {
            Ok(ty::Const::from_bits(tcx, u128::from(*b), typing_env, const_ty))
        }
        (ty::TyKind::Char, MonoArgAst::ConstChar(c)) => {
            Ok(ty::Const::from_bits(tcx, u128::from(u32::from(*c)), typing_env, const_ty))
        }
        (ty::TyKind::Uint(uty), MonoArgAst::ConstInt { negative, magnitude, suffix }) => {
            if let Some(s) = suffix {
                let expected = match uty {
                    ty::UintTy::U8 => IntSpec::U8,
                    ty::UintTy::U16 => IntSpec::U16,
                    ty::UintTy::U32 => IntSpec::U32,
                    ty::UintTy::U64 => IntSpec::U64,
                    ty::UintTy::U128 => IntSpec::U128,
                    ty::UintTy::Usize => IntSpec::Usize,
                };
                if *s != expected {
                    return Err(format!(
                        "const integer suffix does not match parameter type `{const_ty}`"
                    ));
                }
            }
            if *negative {
                return Err(format!("negative literal for unsigned const parameter `{const_ty}`"));
            }
            let bits = layout.size.bits();
            let max = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
            if *magnitude > max {
                return Err(format!(
                    "const literal {magnitude} exceeds `{const_ty}` range [0, {max}]"
                ));
            }
            Ok(ty::Const::from_bits(tcx, *magnitude, typing_env, const_ty))
        }
        (ty::TyKind::Int(ity), MonoArgAst::ConstInt { negative, magnitude, suffix }) => {
            if let Some(s) = suffix {
                let expected = match ity {
                    ty::IntTy::I8 => IntSpec::I8,
                    ty::IntTy::I16 => IntSpec::I16,
                    ty::IntTy::I32 => IntSpec::I32,
                    ty::IntTy::I64 => IntSpec::I64,
                    ty::IntTy::I128 => IntSpec::I128,
                    ty::IntTy::Isize => IntSpec::Isize,
                };
                if *s != expected {
                    return Err(format!(
                        "const integer suffix does not match parameter type `{const_ty}`"
                    ));
                }
            }
            let bits = layout.size.bits();
            let signed_val: i128 = if *negative {
                if *magnitude == 1u128 << 127 {
                    i128::MIN
                } else if *magnitude < 1u128 << 127 {
                    -(*magnitude as i128)
                } else {
                    return Err(format!("const literal -{magnitude} underflows i128"));
                }
            } else {
                i128::try_from(*magnitude)
                    .map_err(|_| format!("const literal {magnitude} overflows `{const_ty}`"))?
            };
            let (min, max) = if bits == 128 {
                (i128::MIN, i128::MAX)
            } else {
                (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
            };
            if signed_val < min || signed_val > max {
                return Err(format!(
                    "const literal {signed_val} outside `{const_ty}` range [{min}, {max}]"
                ));
            }
            let truncated = layout.size.truncate(signed_val as u128);
            Ok(ty::Const::from_bits(tcx, truncated, typing_env, const_ty))
        }
        _ => Err(format!("const argument `{arg:?}` does not match parameter type `{const_ty}`")),
    }
}

fn lower_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ast: &MonoTyAst,
    depth: usize,
) -> Result<Ty<'tcx>, String> {
    if depth > MAX_AST_DEPTH {
        return Err("type nesting exceeds maximum depth".into());
    }
    Ok(match ast {
        MonoTyAst::Unit => tcx.types.unit,
        MonoTyAst::Never => tcx.types.never,
        MonoTyAst::Bool => tcx.types.bool,
        MonoTyAst::Char => tcx.types.char,
        MonoTyAst::Str => tcx.types.str_,
        MonoTyAst::Int(spec) => match spec {
            IntSpec::U8 => tcx.types.u8,
            IntSpec::U16 => tcx.types.u16,
            IntSpec::U32 => tcx.types.u32,
            IntSpec::U64 => tcx.types.u64,
            IntSpec::U128 => tcx.types.u128,
            IntSpec::Usize => tcx.types.usize,
            IntSpec::I8 => tcx.types.i8,
            IntSpec::I16 => tcx.types.i16,
            IntSpec::I32 => tcx.types.i32,
            IntSpec::I64 => tcx.types.i64,
            IntSpec::I128 => tcx.types.i128,
            IntSpec::Isize => tcx.types.isize,
        },
        MonoTyAst::Float(spec) => match spec {
            FloatSpec::F16 => tcx.types.f16,
            FloatSpec::F32 => tcx.types.f32,
            FloatSpec::F64 => tcx.types.f64,
            FloatSpec::F128 => tcx.types.f128,
        },
        MonoTyAst::Tuple(elems) => {
            let tys: Vec<Ty<'tcx>> = elems
                .iter()
                .map(|e| lower_ty(tcx, typing_env, e, depth + 1))
                .collect::<Result<_, _>>()?;
            Ty::new_tup(tcx, &tys)
        }
        MonoTyAst::Array(elem, len) => {
            let elem_ty = lower_ty(tcx, typing_env, elem, depth + 1)?;
            Ty::new_array(tcx, elem_ty, *len)
        }
        MonoTyAst::Slice(elem) => {
            let elem_ty = lower_ty(tcx, typing_env, elem, depth + 1)?;
            Ty::new_slice(tcx, elem_ty)
        }
        MonoTyAst::Ref { mutable, elem } => {
            let elem_ty = lower_ty(tcx, typing_env, elem, depth + 1)?;
            let mutbl = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ref(tcx, tcx.lifetimes.re_static, elem_ty, mutbl)
        }
        MonoTyAst::RawPtr { mutable, elem } => {
            let elem_ty = lower_ty(tcx, typing_env, elem, depth + 1)?;
            let mutbl = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ptr(tcx, elem_ty, mutbl)
        }
        MonoTyAst::Adt { leading_colons, path, args } => {
            let (kind, did) = resolve_adt_or_alias_def(tcx, *leading_colons, path)?;
            let g_args = build_generic_args(tcx, typing_env, did, args, depth + 1)?;
            if kind == DefKind::TyAlias {
                // Form the type a use of the alias lowers to, as upstream
                // `lower_path_segment` does: "Type aliases defined in crates
                // that have the feature `lazy_type_alias` enabled get encoded
                // as a type alias that normalization will then actually
                // instantiate the where bounds of." Every other alias use is
                // its instantiated right-hand side.
                // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs#L1205-L1225
                let lowered = if tcx.type_alias_is_lazy(did) {
                    let alias = ty::AliasTy::new_from_args(tcx, ty::Free { def_id: did }, g_args);
                    ty::Unnormalized::new(Ty::new_alias(tcx, alias))
                } else {
                    tcx.type_of(did).instantiate(tcx, g_args)
                };
                normalize_use_site_ty(tcx, typing_env, lowered, "type alias", || {
                    tcx.def_path_str_with_args(did, g_args)
                })?
            } else {
                Ty::new_adt(tcx, tcx.adt_def(did), g_args)
            }
        }
    })
}

fn build_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    raw_args: &[MonoArgAst],
    depth: usize,
) -> Result<GenericArgsRef<'tcx>, String> {
    if depth > MAX_AST_DEPTH {
        return Err("generic argument nesting exceeds maximum depth".into());
    }
    let params = collect_generic_params(tcx, def_id);
    for (idx, param) in params.iter().enumerate() {
        if param.index as usize != idx {
            return Err(format!(
                "unexpected generic parameter indexing on `{}`",
                tcx.def_path_str(def_id)
            ));
        }
        if param.kind.is_synthetic() {
            return Err(format!(
                "synthetic `impl Trait` generic parameters on `{}` are unsupported",
                tcx.def_path_str(def_id)
            ));
        }
    }
    let ty_const_count = params.iter().filter(|p| p.kind.is_ty_or_const()).count();
    let include_lifetimes = if raw_args.len() == params.len() {
        true
    } else if raw_args.len() == ty_const_count
        && !raw_args.iter().any(|a| matches!(a, MonoArgAst::RegionStatic))
    {
        false
    } else {
        return Err(format!(
            "`{}` expects {} generic arguments (or {} type/const arguments), got {}",
            tcx.def_path_str(def_id),
            params.len(),
            ty_const_count,
            raw_args.len()
        ));
    };

    let mut built: Vec<GenericArg<'tcx>> = Vec::with_capacity(params.len());
    let mut arg_iter = raw_args.iter();
    for param in &params {
        match param.kind {
            ty::GenericParamDefKind::Lifetime => {
                if include_lifetimes {
                    match arg_iter.next() {
                        Some(MonoArgAst::RegionStatic) => {}
                        Some(other) => {
                            return Err(format!(
                                "lifetime parameter `{}` on `{}` expects `'static` or `'_`, got {other:?}",
                                param.name,
                                tcx.def_path_str(def_id)
                            ));
                        }
                        None => return Err("missing lifetime generic argument".into()),
                    }
                }
                built.push(tcx.lifetimes.re_static.into());
            }
            ty::GenericParamDefKind::Type { .. } => {
                let raw = arg_iter.next().ok_or("missing type generic argument")?;
                let MonoArgAst::Ty(ty_ast) = raw else {
                    return Err(format!(
                        "type parameter `{}` on `{}` expects a type, got {raw:?}",
                        param.name,
                        tcx.def_path_str(def_id)
                    ));
                };
                let concrete_ty = lower_ty(tcx, typing_env, ty_ast, depth + 1)?;
                built.push(concrete_ty.into());
            }
            ty::GenericParamDefKind::Const { .. } => {
                let raw = arg_iter.next().ok_or("missing const generic argument")?;
                let raw_const_ty = tcx.type_of(param.def_id);
                if has_param_index_at_least(raw_const_ty.skip_binder(), built.len()) {
                    return Err(format!(
                        "const parameter `{}` on `{}` references a later generic parameter",
                        param.name,
                        tcx.def_path_str(def_id)
                    ));
                }
                let prefix_args = tcx.mk_args(&built);
                let const_ty = normalize_use_site_ty(
                    tcx,
                    typing_env,
                    raw_const_ty.instantiate(tcx, prefix_args),
                    "const parameter type",
                    || format!("{}::{}", tcx.def_path_str(def_id), param.name),
                )?;
                let concrete_const = lower_const_arg(tcx, typing_env, const_ty, raw)?;
                built.push(concrete_const.into());
            }
        }
    }
    if arg_iter.next().is_some() {
        return Err("excess generic arguments supplied".into());
    }
    let args = tcx.mk_args(&built);
    if args.has_non_region_param() || args.has_non_region_infer() || args.references_error() {
        return Err("concrete monomorphization arguments remain generic or erroneous".into());
    }
    Ok(args)
}

struct OutOfRangeParamFinder {
    limit: usize,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for OutOfRangeParamFinder {
    type Result = ControlFlow<()>;

    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        if let ty::Param(p) = *ty.kind()
            && p.index as usize >= self.limit
        {
            return ControlFlow::Break(());
        }
        ty.super_visit_with(self)
    }

    fn visit_const(&mut self, ct: ty::Const<'tcx>) -> Self::Result {
        if let ty::ConstKind::Param(p) = ct.kind()
            && p.index as usize >= self.limit
        {
            return ControlFlow::Break(());
        }
        ct.super_visit_with(self)
    }

    fn visit_region(&mut self, r: ty::Region<'tcx>) -> Self::Result {
        if let ty::RegionKind::ReEarlyParam(p) = r.kind()
            && p.index as usize >= self.limit
        {
            return ControlFlow::Break(());
        }
        ControlFlow::Continue(())
    }
}

fn has_param_index_at_least<'tcx>(ty: Ty<'tcx>, limit: usize) -> bool {
    ty.visit_with(&mut OutOfRangeParamFinder { limit }).is_break()
}

/// Lift the regions that `rustc` erased from `value` back to `'static`.
///
/// `'static` is the only free region a monomorphization request can name, so
/// every free region of a requested type is `'static` and an erased region can
/// stand for no other. Bound regions stay intact. Erased regions must never
/// enter `InferCtxt`, whose region resolution cannot relate them.
fn replace_erased_regions_with_static<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    value: T,
) -> T {
    let mut folder = ty::BottomUpFolder {
        tcx,
        ty_op: |ty| ty,
        lt_op: |r| if r.is_erased() { tcx.lifetimes.re_static } else { r },
        ct_op: |ct| ct,
    };
    value.fold_with(&mut folder)
}

/// Refuse `value` unless every region free in it is `'static`, the only free
/// region a monomorphization request can name. Every obligation check calls
/// this before it enters `InferCtxt`, whose region resolution cannot relate
/// erased regions.
///
/// `rustc` does not count erased regions as free. Upstream
/// `TypeVisitableExt::has_free_regions`:
///
/// > "Free" regions in this context means that it has any region
/// > that is not (a) erased or (b) late-bound.
///
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_type_ir/src/visit.rs#L320-L328
/// So `TyCtxt::all_free_regions_meet` never sees an erased region nested in a
/// type: its visitor skips each type without free regions, "We're only
/// interested in types involving regions".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/visit.rs#L96-L103
/// Erased regions are therefore checked separately.
fn require_static_regions<'tcx, T: TypeVisitable<TyCtxt<'tcx>>>(
    tcx: TyCtxt<'tcx>,
    value: &T,
    describe: impl FnOnce() -> String,
) -> Result<(), String> {
    if value.has_erased_regions() || !tcx.all_free_regions_meet(value, |r| r.is_static()) {
        return Err(format!("{} names a region other than `'static`", describe()));
    }
    Ok(())
}

/// Normalize `lowered`, the type that a use of a type alias or of a const
/// parameter's declared type lowers to, as `rustc` would where a request
/// writes it. Requested types must be normalized only through this function.
///
/// Upstream `TyCtxt::try_normalize_erasing_regions`: "Tries to erase the
/// regions in `value` and then fully normalize all the types found within.
/// The result will also have regions erased."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/normalize_erasing_regions.rs#L93-L125
/// Its provider drops what normalizing incurs: "We don't care about the
/// `obligations`; they are always only region relations, and we are about to
/// erase those anyway".
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_traits/src/normalize_erasing_regions.rs#L29-L31
/// So that query forgets regions twice over. Going in, it does not enforce the
/// region and higher-ranked obligations that normalizing `lowered` incurs,
/// nor does it require the terms it normalizes away to be well-formed. Coming
/// out, its result has no regions for later obligations to relate.
///
/// This function therefore first requires, under region-aware trait solving,
/// that `lowered` is well-formed and normalizes; upstream `FnCtxt::lower_ty`
/// likewise registers a well-formedness obligation for each type it lowers.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_hir_typeck/src/fn_ctxt/_impl.rs#L509-L513
/// Only then does it take the erasing normalization and lift the erased
/// regions of the result back to `'static`.
fn normalize_use_site_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    lowered: ty::Unnormalized<'tcx, Ty<'tcx>>,
    label: &str,
    subject: impl Fn() -> String,
) -> Result<Ty<'tcx>, String> {
    let raw = lowered.skip_normalization();
    require_static_regions(tcx, &raw, || format!("{label} `{}`", subject()))?;
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    let ocx = ObligationCtxt::new(&infcx);
    register_wf_obligations(&ocx, param_env, raw.into(), || {
        format!("{label} `{}`", subject())
    })?;
    // Only the obligations this normalization incurs are needed; the erasing
    // normalization below supplies the result.
    let _ = ocx.normalize(&ObligationCause::dummy(), param_env, lowered);
    check_registered_obligations(ocx, param_env, label, &subject)?;
    let normalized = tcx
        .try_normalize_erasing_regions(typing_env, lowered)
        .map_err(|_| format!("failed to normalize {label} `{}`", subject()))?;
    Ok(replace_erased_regions_with_static(tcx, normalized))
}

/// Register the obligations that make `term` well-formed.
///
/// Upstream `wf::obligations` "Returns the set of obligations needed to make
/// `arg` well-formed", returning `None` if an unresolved inference variable
/// makes no progress.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_trait_selection/src/traits/wf.rs#L25-L88
fn register_wf_obligations<'tcx>(
    ocx: &ObligationCtxt<'_, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    term: ty::Term<'tcx>,
    describe: impl FnOnce() -> String,
) -> Result<(), String> {
    let Some(wf_obls) = wf::obligations(ocx.infcx, param_env, CRATE_DEF_ID, 0, term, DUMMY_SP)
    else {
        return Err(format!("failed to compute well-formedness obligations for {}", describe()));
    };
    ocx.register_obligations(wf_obls);
    Ok(())
}

/// Require every obligation registered in `ocx` to hold, then resolve the
/// region constraints that solving them produced.
///
/// Upstream `ObligationCtxt::evaluate_obligations_error_on_ambiguity`
/// "Returns a list of errors from obligations that evaluated to Ambiguous or
/// Err." `ObligationCtxt::resolve_regions` "Resolves regions and reports
/// errors. Takes ownership of the context as doing trait solving afterwards
/// will result in region constraints getting ignored."
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_trait_selection/src/traits/engine.rs#L225-L229
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_trait_selection/src/traits/engine.rs#L261-L273
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_trait_selection/src/traits/query/evaluate_obligation.rs#L94-L111
fn check_registered_obligations<'tcx>(
    ocx: ObligationCtxt<'_, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    label: &str,
    subject: impl Fn() -> String,
) -> Result<(), String> {
    let pred_errors = ocx.evaluate_obligations_error_on_ambiguity();
    if !pred_errors.is_empty() {
        return Err(format!(
            "{label} trait or well-formedness predicates unsatisfied for `{}`: {:?}",
            subject(),
            pred_errors[0]
        ));
    }
    let region_errors = ocx.resolve_regions(CRATE_DEF_ID, param_env, []);
    if !region_errors.is_empty() {
        return Err(format!(
            "{label} region or outlives predicates unsatisfied for `{}`: {:?}",
            subject(),
            region_errors[0]
        ));
    }
    Ok(())
}

/// Check concrete argument well-formedness, trait/predicate fulfillment, and
/// region/outlives obligations for `def_id` under `typing_env`.
fn verify_predicates_and_wf<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
    label: &str,
) -> Result<(), String> {
    require_static_regions(tcx, &args, || {
        format!("{label} arguments for `{}`", tcx.def_path_str(def_id))
    })?;
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    let ocx = ObligationCtxt::new(&infcx);
    for arg in args.iter() {
        let term: Option<ty::Term<'tcx>> = match arg.kind() {
            ty::GenericArgKind::Type(t) => Some(t.into()),
            ty::GenericArgKind::Const(c) => Some(c.into()),
            ty::GenericArgKind::Lifetime(_) => None,
        };
        if let Some(term) = term {
            register_wf_obligations(&ocx, param_env, term, || format!("{label} argument `{arg}`"))?;
        }
    }
    for (clause, span) in tcx.predicates_of(def_id).instantiate(tcx, args) {
        let cause = ObligationCause::dummy_with_span(span);
        let normalized = ocx.normalize(&cause, param_env, clause);
        ocx.register_obligation(Obligation::new(tcx, cause, param_env, normalized));
    }
    check_registered_obligations(ocx, param_env, label, || {
        tcx.def_path_str_with_args(def_id, args)
    })
}

pub(crate) struct ResolvedMonoBody<'tcx> {
    pub(crate) instance: Instance<'tcx>,
    pub(crate) resolved_local: LocalDefId,
    pub(crate) body: mir::Body<'tcx>,
    pub(crate) typing_env: ty::TypingEnv<'tcx>,
}

/// Resolve and monomorphize a concrete instantiation `(path, args)` of a local
/// generic function/method, validating argument well-formedness, item trait
/// and region/outlives predicates, and `Instance::try_resolve` before
/// instantiating and normalizing its `Runtime(PostCleanup)` MIR body.
///
/// Upstream `Instance::try_resolve` "Returns `Err(ErrorGuaranteed)` when the
/// `Instance` resolution process couldn't complete due to errors elsewhere"
/// and `Ok(None)` when resolution bails out or cannot resolve;
/// `try_instantiate_mir_and_normalize_erasing_regions` substitutes and
/// normalizes the MIR body under `typing_env`.
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L489-L518
/// https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_middle/src/ty/instance.rs#L888-L910
pub(crate) fn instantiate_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &str,
    raw_arg_strs: &[String],
) -> Result<ResolvedMonoBody<'tcx>, String> {
    let parsed_args: Vec<MonoArgAst> =
        raw_arg_strs.iter().map(|s| parse_mono_arg(s)).collect::<Result<_, _>>()?;
    let target_local = resolve_callable_def_id(tcx, path)?;
    let target_def = target_local.to_def_id();
    let typing_env = ty::TypingEnv::fully_monomorphized();

    let args = build_generic_args(tcx, typing_env, target_def, &parsed_args, 0)?;

    // Check both concrete argument well-formedness and every `where`, trait,
    // and region/outlives predicate on `target_def` before resolving. Without
    // this explicit check, `Instance::try_resolve` alone could instantiate a
    // callee whose `where` clauses are violated for the requested types.
    verify_predicates_and_wf(tcx, typing_env, target_def, args, "target")?;

    let instance = Instance::try_resolve(tcx, typing_env, target_def, args)
        .map_err(|_| {
            format!(
                "instance resolution reported compiler errors for `{}`",
                tcx.def_path_str_with_args(target_def, args)
            )
        })?
        .ok_or_else(|| {
            format!(
                "cannot resolve concrete instance for `{}`",
                tcx.def_path_str_with_args(target_def, args)
            )
        })?;

    let InstanceKind::Item(resolved_def) = instance.def else {
        return Err(format!(
            "unsupported non-item monomorphic instance kind for `{path}`: {:?}",
            instance.def
        ));
    };
    let Some(resolved_local) = resolved_def.as_local() else {
        return Err(format!(
            "concrete instance `{}` resolves outside the local crate",
            tcx.def_path_str_with_args(resolved_def, instance.args)
        ));
    };
    if !matches!(tcx.def_kind(resolved_def), DefKind::Fn | DefKind::AssocFn) {
        return Err(format!(
            "concrete instance `{}` is not a callable function definition",
            tcx.def_path_str_with_args(resolved_def, instance.args)
        ));
    }
    // When `try_resolve` dispatches a trait method to a concrete impl item,
    // verify the resolved impl's own predicates/WF too. `try_resolve` erases
    // regions in `instance.args`, so lift `ReErased` back to `'static` before
    // entering `InferCtxt` (leaving any higher-ranked `ReBound` intact).
    if resolved_def != target_def {
        let resolved_args = replace_erased_regions_with_static(tcx, instance.args);
        verify_predicates_and_wf(tcx, typing_env, resolved_def, resolved_args, "resolved impl")?;
    }
    if tcx.intrinsic(resolved_def).is_some() {
        return Err(format!(
            "intrinsic `{}` is unsupported: calls need not execute its fallback body",
            tcx.def_path_str(resolved_def)
        ));
    }
    if !tcx.is_mir_available(resolved_def) {
        return Err(format!(
            "MIR is unavailable for `{}`",
            tcx.def_path_str_with_args(resolved_def, instance.args)
        ));
    }

    let raw_steal = tcx.mir_drops_elaborated_and_const_checked(resolved_local);
    if raw_steal.is_stolen() {
        return Err(format!(
            "Runtime(PostCleanup) MIR for `{}` was already stolen before monomorphization",
            tcx.def_path_str_with_args(resolved_def, instance.args)
        ));
    }
    let raw_body = raw_steal.borrow();
    let inst_body = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            typing_env,
            EarlyBinder::bind(raw_body.clone()),
        )
        .map_err(|_| {
            format!(
                "failed to instantiate and normalize MIR body for `{}`",
                tcx.def_path_str_with_args(resolved_def, instance.args)
            )
        })?;
    if inst_body.has_non_region_param()
        || inst_body.has_non_region_infer()
        || inst_body.references_error()
    {
        return Err(format!(
            "monomorphized MIR body for `{}` still contains uninstantiated generics or errors",
            tcx.def_path_str_with_args(resolved_def, instance.args)
        ));
    }

    Ok(ResolvedMonoBody { instance, resolved_local, body: inst_body, typing_env })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_concrete_type_and_const_args() {
        assert_eq!(parse_mono_arg("usize").unwrap(), MonoArgAst::Ty(MonoTyAst::Int(IntSpec::Usize)));
        assert_eq!(parse_mono_arg("()").unwrap(), MonoArgAst::Ty(MonoTyAst::Unit));
        assert_eq!(parse_mono_arg("!").unwrap(), MonoArgAst::Ty(MonoTyAst::Never));
        assert_eq!(parse_mono_arg("'static").unwrap(), MonoArgAst::RegionStatic);
        assert_eq!(parse_mono_arg("'_").unwrap(), MonoArgAst::RegionStatic);
        assert_eq!(parse_mono_arg("true").unwrap(), MonoArgAst::ConstBool(true));
        assert_eq!(parse_mono_arg("'\\n'").unwrap(), MonoArgAst::ConstChar('\n'));
        assert_eq!(parse_mono_arg("'_'").unwrap(), MonoArgAst::ConstChar('_'));
        assert_eq!(parse_mono_arg("'\\x41'").unwrap(), MonoArgAst::ConstChar('A'));
        assert_eq!(
            parse_mono_arg("-42i32").unwrap(),
            MonoArgAst::ConstInt {
                negative: true,
                magnitude: 42,
                suffix: Some(IntSpec::I32),
            }
        );
        assert_eq!(
            parse_mono_arg("0xff_u16").unwrap(),
            MonoArgAst::ConstInt {
                negative: false,
                magnitude: 0xff,
                suffix: Some(IntSpec::U16),
            }
        );
        assert_eq!(
            parse_mono_arg("[u8]").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Slice(Box::new(MonoTyAst::Int(IntSpec::U8))))
        );
        assert_eq!(
            parse_mono_arg("[u32; 4usize]").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Array(Box::new(MonoTyAst::Int(IntSpec::U32)), 4))
        );
        assert_eq!(
            parse_mono_arg("&'static mut (u8, bool)").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Ref {
                mutable: true,
                elem: Box::new(MonoTyAst::Tuple(vec![
                    MonoTyAst::Int(IntSpec::U8),
                    MonoTyAst::Bool,
                ])),
            })
        );
        assert_eq!(
            parse_mono_arg("core::sync::atomic::Atomic<u8>").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Adt {
                leading_colons: false,
                path: vec![
                    "core".into(),
                    "sync".into(),
                    "atomic".into(),
                    "Atomic".into(),
                ],
                args: vec![MonoArgAst::Ty(MonoTyAst::Int(IntSpec::U8))],
            })
        );
        assert_eq!(
            parse_mono_arg("::core::mem::ManuallyDrop<u8>").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Adt {
                leading_colons: true,
                path: vec!["core".into(), "mem".into(), "ManuallyDrop".into()],
                args: vec![MonoArgAst::Ty(MonoTyAst::Int(IntSpec::U8))],
            })
        );
        assert_eq!(
            parse_mono_arg("true_value").unwrap(),
            MonoArgAst::Ty(MonoTyAst::Adt {
                leading_colons: false,
                path: vec!["true_value".into()],
                args: vec![],
            })
        );
    }

    #[test]
    fn rejects_malformed_or_excess_generic_args() {
        for bad in [
            "",
            "usize u8",
            "true 1",
            "123u9",
            "'a",
            "'_foo",
            "'''",
            "'\\x+1'",
            "'\\x80'",
            "'ab'",
            "core::sync::atomic::Atomic<u8",
            "&'a u8",
            "*u8",
        ] {
            assert!(parse_mono_arg(bad).is_err(), "expected failure for {bad:?}");
        }
    }

    /// Run `f` on the `TyCtxt` of an empty crate.
    fn with_tcx(f: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
        static USING_INTERNAL_FEATURES: std::sync::atomic::AtomicBool =
            std::sync::atomic::AtomicBool::new(false);
        let config = rustc_interface::Config {
            opts: rustc_session::config::Options::default(),
            crate_cfg: Vec::new(),
            crate_check_cfg: Vec::new(),
            input: rustc_session::config::Input::Str {
                name: rustc_span::FileName::Custom("mono_test".into()),
                input: String::new(),
            },
            output_dir: None,
            output_file: None,
            ice_file: None,
            file_loader: None,
            lint_caps: Default::default(),
            psess_created: None,
            track_state: None,
            register_lints: None,
            override_queries: None,
            extra_symbols: Vec::new(),
            make_codegen_backend: None,
            using_internal_features: &USING_INTERNAL_FEATURES,
        };
        rustc_interface::run_compiler(config, |compiler| {
            let krate = rustc_interface::passes::parse(&compiler.sess);
            rustc_interface::passes::create_and_enter_global_ctxt(compiler, krate, f);
        });
    }

    #[test]
    fn requires_static_regions_including_erased_ones_nested_in_types() {
        with_tcx(|tcx| {
            let u8_ty = tcx.types.u8;
            let static_ref = Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, u8_ty);
            let erased_ref = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, u8_ty);
            let bound = ty::BoundRegion {
                var: ty::BoundVar::ZERO,
                kind: ty::BoundRegionKind::Anon,
            };
            let bound_ref = Ty::new_imm_ref(
                tcx,
                ty::Region::new_bound(tcx, ty::INNERMOST, bound),
                u8_ty,
            );
            let hr_fn = Ty::new_fn_ptr(
                tcx,
                ty::Binder::bind_with_vars(
                    tcx.mk_fn_sig_safe_rust_abi([bound_ref], tcx.types.unit),
                    tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Region(
                        ty::BoundRegionKind::Anon,
                    )]),
                ),
            );
            let describe = || "value".to_owned();
            let erased_args = tcx.mk_args(&[erased_ref.into()]);
            // `rustc` counts none of these erased regions as free, so the
            // free-region test alone would accept them.
            assert!(tcx.all_free_regions_meet(&erased_ref, |r| r.is_static()));
            assert!(tcx.all_free_regions_meet(&erased_args, |r| r.is_static()));
            assert!(require_static_regions(tcx, &erased_ref, describe).is_err());
            assert!(require_static_regions(tcx, &erased_args, describe).is_err());
            assert!(
                require_static_regions(tcx, &tcx.lifetimes.re_erased, describe).is_err()
            );
            assert!(require_static_regions(tcx, &static_ref, describe).is_ok());
            assert!(require_static_regions(tcx, &hr_fn, describe).is_ok());
        });
    }
}
