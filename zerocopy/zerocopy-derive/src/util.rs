// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::num::NonZeroU32;

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse::ParseBuffer, parse_quote, spanned::Spanned as _, token::PathSep, Data, DataEnum,
    DataStruct, DataUnion, DeriveInput, Error, Expr, ExprLit, Field, GenericParam, Ident, Index,
    Lit, LitStr, Meta, Path, Type, Variant, Visibility, WherePredicate,
};

use crate::repr::{CompoundRepr, EnumRepr, PrimitiveRepr, Repr, Spanned};

pub(crate) struct Ctx {
    pub(crate) ast: DeriveInput,
    pub(crate) zerocopy_crate: Path,

    // The value of the last `#[zerocopy(on_error = ...)]` attribute, or `false`
    // if none is provided.
    pub(crate) skip_on_error: bool,

    // The span of the last `#[zerocopy(on_error = ...)]` attribute, if any.
    pub(crate) on_error_span: Option<proc_macro2::Span>,
}

#[derive(Eq, PartialEq)]
enum CratePath {
    External,
    CrateRelative,
    ModuleRelative,
}

fn validate_crate_path(path: &Path) -> Result<CratePath, ()> {
    if path.segments.is_empty() {
        return Err(());
    }

    enum ModuleRelative {
        Yes,
        No,
    }
    let first = path.segments[0].ident.to_string();
    let (mut prev_segment, path_type) = match first.as_str() {
        "Self" => return Err(()),
        "crate" => {
            if path.leading_colon.is_some() {
                return Err(());
            }
            (ModuleRelative::No, CratePath::CrateRelative)
        }
        "self" | "super" => {
            if path.leading_colon.is_some() {
                return Err(());
            }
            (ModuleRelative::Yes, CratePath::ModuleRelative)
        }
        _ => (ModuleRelative::No, CratePath::External),
    };

    for seg in path.segments.iter().skip(1) {
        let ident = seg.ident.to_string();
        match ident.as_str() {
            "Self" | "crate" | "self" => return Err(()),
            "super" => match prev_segment {
                ModuleRelative::Yes => {}
                ModuleRelative::No => return Err(()),
            },
            _ => {
                prev_segment = ModuleRelative::No;
            }
        }
    }
    Ok(path_type)
}

impl Ctx {
    /// Attempt to extract a crate path from the provided attributes. Defaults to
    /// `::zerocopy` if not found.
    pub(crate) fn try_from_derive_input(ast: DeriveInput) -> Result<Self, Error> {
        let mut path = parse_quote!(::zerocopy);
        let mut skip_on_error = false;
        let mut on_error_span = None;

        for attr in &ast.attrs {
            if let Meta::List(ref meta_list) = attr.meta {
                if path_is_ident(&meta_list.path, "zerocopy") {
                    attr.parse_nested_meta(|meta| {
                        if path_is_ident(&meta.path, "crate") {
                            let expr = meta.value().and_then(ParseBuffer::parse);
                            if let Ok(Expr::Lit(ExprLit { lit: Lit::Str(lit), .. })) = expr {
                                if let Ok(mut path_lit) = lit.parse_with(Path::parse_mod_style) {
                                    if let Ok(crate_path) = validate_crate_path(&path_lit) {
                                        // If not expressly relative, absolutize.
                                        if path_lit.leading_colon.is_none() && crate_path == CratePath::External {
                                            path_lit.leading_colon = Some(PathSep::default());
                                        }
                                        path = path_lit;
                                        return Ok(());
                                    }

                                    return Err(Error::new(
                                        lit.span(),
                                        "`crate` attribute requires a valid module path",
                                    ));
                                }

                                return Err(Error::new(
                                    lit.span(),
                                    "`crate` attribute requires a path as the value",
                                ));
                            }

                            return Err(Error::new(
                                meta.path.span(),
                                "`crate` attribute requires a path as the value",
                            ));
                        }

                        if path_is_ident(&meta.path, "on_error") {
                            on_error_span = Some(meta.path.span());
                            let value = meta.value()?;
                            let s: LitStr = value.parse()?;
                            match s.value().as_str() {
                                "skip" => skip_on_error = true,
                                "fail" => skip_on_error = false,
                                _ => return Err(Error::new(
                                    s.span(),
                                    "unrecognized value for `on_error` attribute from `zerocopy`; expected `skip` or `fail`",
                                )),
                            }
                            return Ok(());
                        }

                        Err(Error::new(
                            Span::call_site(),
                            format!(
                                "unknown attribute encountered: {}",
                                meta.path.into_token_stream()
                            ),
                        ))
                    })?;
                }
            }
        }

        Ok(Self { ast, zerocopy_crate: path, skip_on_error, on_error_span })
    }

    pub(crate) fn with_input(&self, input: &DeriveInput) -> Self {
        Self {
            ast: input.clone(),
            zerocopy_crate: self.zerocopy_crate.clone(),
            skip_on_error: self.skip_on_error,
            on_error_span: self.on_error_span,
        }
    }

    pub(crate) fn skip_on_error(mut self) -> Self {
        self.skip_on_error = true;
        self
    }

    pub(crate) fn core_path(&self) -> TokenStream {
        let zerocopy_crate = &self.zerocopy_crate;
        quote!(#zerocopy_crate::util::macro_util::core_reexport)
    }

    pub(crate) fn cfg_compile_error(&self) -> TokenStream {
        // By checking both during the compilation of the proc macro *and* in
        // the generated code, we ensure that `--cfg
        // zerocopy_unstable_linux` need only be passed *either* when
        // compiling this crate *or* when compiling the user's crate. The former
        // is preferable, but in some situations (such as when cross-compiling
        // using `cargo build --target`), it doesn't get propagated to this
        // crate's build by default.
        if cfg!(zerocopy_unstable_linux) {
            quote!()
        } else if let Some(span) = self.on_error_span {
            let core = self.core_path();
            let error_message =
                "`on_error` is experimental; pass '--cfg zerocopy_unstable_linux' to enable";
            quote::quote_spanned! {span=>
                #[allow(unused_attributes, unexpected_cfgs)]
                const _: () = {
                    #[cfg(not(zerocopy_unstable_linux))]
                    #core::compile_error!(#error_message);
                };
            }
        } else {
            quote!()
        }
    }

    pub(crate) fn error_or_skip<E>(&self, error: E) -> Result<TokenStream, E> {
        if self.skip_on_error {
            Ok(self.cfg_compile_error())
        } else {
            Err(error)
        }
    }
}

pub(crate) trait DataExt {
    /// Extracts the names and types of all fields. For enums, extracts the
    /// names and types of fields from each variant. For tuple structs, the
    /// names are the indices used to index into the struct (ie, `0`, `1`, etc).
    ///
    /// FIXME: Extracting field names for enums doesn't really make sense. Types
    /// makes sense because we don't care about where they live - we just care
    /// about transitive ownership. But for field names, we'd only use them when
    /// generating is_bit_valid, which cares about where they live.
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)>;

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)>;

    fn tag(&self) -> Option<Ident>;
}

#[derive(Default)]
struct UninspectableSyntaxFinder(Option<(Span, &'static str)>);

impl UninspectableSyntaxFinder {
    fn record(&mut self, span: Span, reason: &'static str) {
        if self.0.is_none() {
            self.0 = Some((span, reason));
        }
    }
}

impl<'ast> syn::visit::Visit<'ast> for UninspectableSyntaxFinder {
    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        self.record(attr.span(), "an attribute");
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if matches!(expr, Expr::Verbatim(_)) {
            self.record(expr.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_expr(self, expr);
        }
    }

    fn visit_foreign_item(&mut self, item: &'ast syn::ForeignItem) {
        if matches!(item, syn::ForeignItem::Verbatim(_)) {
            self.record(item.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_foreign_item(self, item);
        }
    }

    fn visit_impl_item(&mut self, item: &'ast syn::ImplItem) {
        if matches!(item, syn::ImplItem::Verbatim(_)) {
            self.record(item.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_impl_item(self, item);
        }
    }

    fn visit_item(&mut self, item: &'ast syn::Item) {
        if matches!(item, syn::Item::Verbatim(_)) {
            self.record(item.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_item(self, item);
        }
    }

    fn visit_lit(&mut self, lit: &'ast Lit) {
        if matches!(lit, Lit::Verbatim(_)) {
            self.record(lit.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_lit(self, lit);
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        self.record(mac.span(), "a macro invocation");
    }

    fn visit_pat(&mut self, pat: &'ast syn::Pat) {
        if matches!(pat, syn::Pat::Verbatim(_)) {
            self.record(pat.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_pat(self, pat);
        }
    }

    fn visit_trait_item(&mut self, item: &'ast syn::TraitItem) {
        if matches!(item, syn::TraitItem::Verbatim(_)) {
            self.record(item.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_trait_item(self, item);
        }
    }

    fn visit_type(&mut self, ty: &'ast Type) {
        if matches!(ty, Type::Verbatim(_)) {
            self.record(ty.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_type(self, ty);
        }
    }

    fn visit_type_param_bound(&mut self, bound: &'ast syn::TypeParamBound) {
        if matches!(bound, syn::TypeParamBound::Verbatim(_)) {
            self.record(bound.span(), "unsupported unresolved syntax");
        } else {
            syn::visit::visit_type_param_bound(self, bound);
        }
    }
}

fn reject_uninspectable_syntax(
    finder: UninspectableSyntaxFinder,
    derive_name: &str,
    location: &str,
) -> Result<(), Error> {
    if let Some((span, reason)) = finder.0 {
        return Err(Error::new(
            span,
            format!(
                "cannot derive `{}` for a type containing {} in {}; write the expanded syntax explicitly",
                derive_name, reason, location,
            ),
        ));
    }
    Ok(())
}

/// Rejects field types which contain macro invocations or uninspectable syntax.
///
/// A derive macro receives a field type macro before rustc expands it. If the
/// derive copies that macro invocation into multiple generated locations, the
/// expansions need not be identical (for example, a stateful procedural macro
/// can emit a different type each time). Since a derive cannot inspect an
/// expansion at proc-macro execution time, callers which rely on copied field
/// types must reject the unresolved invocation itself.
pub(crate) fn reject_uninspectable_types<'a>(
    types: impl IntoIterator<Item = &'a Type>,
    derive_name: &str,
) -> Result<(), Error> {
    use syn::visit::Visit as _;

    for ty in types {
        let mut finder = UninspectableSyntaxFinder::default();
        finder.visit_type(ty);
        reject_uninspectable_syntax(finder, derive_name, "a field type")?;
    }

    Ok(())
}

/// Returns the generic syntax copied into an `impl` declaration.
///
/// Type and const defaults belong to the type declaration and are not legal
/// on an `impl`. [`ImplBlockBuilder`] therefore discards them before emitting
/// its generic parameters. Keep validation in sync with that behavior so that
/// syntax which is expanded only in the original item is not rejected.
fn generics_without_defaults(generics: &syn::Generics) -> syn::Generics {
    let mut generics = generics.clone();
    for param in &mut generics.params {
        match param {
            GenericParam::Type(ty) => ty.default = None,
            GenericParam::Const(cnst) => cnst.default = None,
            GenericParam::Lifetime(_) => {}
        }
    }
    generics
}

/// Rejects macro invocations or uninspectable syntax in copied generics.
///
/// A copied bound can change how an associated type shorthand in a field type
/// resolves, so validating only the field type syntax is insufficient.
pub(crate) fn reject_uninspectable_generics(
    generics: &syn::Generics,
    derive_name: &str,
) -> Result<(), Error> {
    use syn::visit::Visit as _;

    let mut finder = UninspectableSyntaxFinder::default();
    finder.visit_generics(generics);
    reject_uninspectable_syntax(finder, derive_name, "generic parameters or predicates")
}

/// Rejects uninspectable syntax in generics copied into an `impl` declaration.
pub(crate) fn reject_uninspectable_impl_generics(
    generics: &syn::Generics,
    derive_name: &str,
) -> Result<(), Error> {
    reject_uninspectable_generics(&generics_without_defaults(generics), derive_name)
}

pub(crate) fn reject_uninspectable_field_types(
    data: &dyn DataExt,
    derive_name: &str,
) -> Result<(), Error> {
    reject_uninspectable_types(data.fields().into_iter().map(|(_, _, ty)| ty), derive_name)
}

/// Rejects identifiers which can capture generated helper items.
///
/// Derive output is unhygienic and is emitted in a nested scope. A helper item
/// in that scope can therefore change the meaning of copied syntax. Reserve
/// implementation-specific prefixes in target generic declarations and in
/// unqualified paths and patterns whose resolution can change in the generated
/// scope. Qualified paths cannot be captured by these helpers and remain
/// supported.
///
/// Every copied syntax position whose meaning is used in a safety proof must
/// also reject unresolved syntax (or validate it by an equally strict
/// grammar): an unexpanded macro could otherwise produce a name which is not
/// visible in this token stream.
pub(crate) fn reject_reserved_identifiers(
    ctx: &Ctx,
    derive_name: &str,
    reserved_prefixes: &[&str],
) -> Result<(), Error> {
    use syn::visit::Visit as _;

    fn is_reserved(ident: &Ident, reserved_prefixes: &[&str]) -> bool {
        let normalized = to_ident_str(ident);
        reserved_prefixes.iter().any(|prefix| normalized.starts_with(prefix))
    }

    struct ReservedIdentifierFinder<'a> {
        reserved_prefixes: &'a [&'a str],
        found: Option<Ident>,
    }

    impl ReservedIdentifierFinder<'_> {
        fn record(&mut self, ident: &Ident) {
            if self.found.is_none() && is_reserved(ident, self.reserved_prefixes) {
                self.found = Some(ident.clone());
            }
        }

        fn visit_use_root(&mut self, tree: &syn::UseTree) {
            match tree {
                syn::UseTree::Name(name) => self.record(&name.ident),
                syn::UseTree::Rename(rename) => self.record(&rename.ident),
                syn::UseTree::Path(path) => {
                    // Only the first segment is unqualified. The remainder is
                    // resolved through it and cannot be captured directly.
                    self.record(&path.ident);
                }
                syn::UseTree::Group(group) => {
                    for tree in &group.items {
                        self.visit_use_root(tree);
                    }
                }
                syn::UseTree::Glob(_) => {}
            }
        }

        fn visit_maybe_qself_path(&mut self, qself: Option<&syn::QSelf>, path: &Path) {
            if let Some(qself) = qself {
                self.visit_qself(qself);

                // In `<T as path::Trait>::Assoc`, only the part of `path`
                // before the associated item is resolved lexically. The
                // associated item and any following segments are resolved
                // through `T` and cannot be captured by a generated helper.
                if qself.position > 0 && path.leading_colon.is_none() {
                    if let Some(first) = path.segments.first() {
                        self.record(&first.ident);
                    }
                }
            } else if path.leading_colon.is_none() {
                if let Some(first) = path.segments.first() {
                    self.record(&first.ident);
                }
            }

            // Generic arguments can themselves contain unqualified paths,
            // including on associated segments which are otherwise safe.
            for segment in &path.segments {
                self.visit_path_arguments(&segment.arguments);
            }
        }
    }

    impl<'ast> syn::visit::Visit<'ast> for ReservedIdentifierFinder<'_> {
        fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
            for attr in &path.attrs {
                self.visit_attribute(attr);
            }
            self.visit_maybe_qself_path(path.qself.as_ref(), &path.path);
        }

        fn visit_expr_struct(&mut self, expr: &'ast syn::ExprStruct) {
            for attr in &expr.attrs {
                self.visit_attribute(attr);
            }
            self.visit_maybe_qself_path(expr.qself.as_ref(), &expr.path);
            for field in &expr.fields {
                self.visit_field_value(field);
            }
            if let Some(rest) = &expr.rest {
                self.visit_expr(rest);
            }
        }

        fn visit_item_use(&mut self, item: &'ast syn::ItemUse) {
            if item.leading_colon.is_none() {
                self.visit_use_root(&item.tree);
            }
        }

        fn visit_path(&mut self, path: &'ast Path) {
            self.visit_maybe_qself_path(None, path);
        }

        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            // A bare identifier in a pattern can resolve either as a binding
            // or as an in-scope constant. A generated constant can therefore
            // change the meaning of the copied pattern.
            self.record(&pat.ident);
            syn::visit::visit_pat_ident(self, pat);
        }

        fn visit_pat_struct(&mut self, pat: &'ast syn::PatStruct) {
            for attr in &pat.attrs {
                self.visit_attribute(attr);
            }
            self.visit_maybe_qself_path(pat.qself.as_ref(), &pat.path);
            for field in &pat.fields {
                self.visit_field_pat(field);
            }
            if let Some(rest) = &pat.rest {
                self.visit_pat_rest(rest);
            }
        }

        fn visit_pat_tuple_struct(&mut self, pat: &'ast syn::PatTupleStruct) {
            for attr in &pat.attrs {
                self.visit_attribute(attr);
            }
            self.visit_maybe_qself_path(pat.qself.as_ref(), &pat.path);
            for elem in &pat.elems {
                self.visit_pat(elem);
            }
        }

        fn visit_type_path(&mut self, path: &'ast syn::TypePath) {
            self.visit_maybe_qself_path(path.qself.as_ref(), &path.path);
        }
    }

    let mut finder = ReservedIdentifierFinder { reserved_prefixes, found: None };

    // The derive target is referenced unqualified inside generated helper
    // scopes, so its name must not be capturable either.
    finder.record(&ctx.ast.ident);
    // A target type parameter is also in scope in generated impl methods. Its
    // only semantic use can be hidden behind `Self`, so scanning path
    // references alone does not prove that it cannot capture a generated
    // helper type.
    for param in &ctx.ast.generics.params {
        if let syn::GenericParam::Type(param) = param {
            finder.record(&param.ident);
        }
    }
    finder.visit_generics(&ctx.ast.generics);
    for (_, _, ty) in ctx.ast.data.fields() {
        finder.visit_type(ty);
    }

    if let Some(ident) = finder.found {
        return Err(Error::new(
            ident.span(),
            format!(
                "cannot derive `{}` because the unqualified identifier `{}` is reserved for generated code; qualify the path or rename the identifier",
                derive_name,
                to_ident_str(&ident),
            ),
        ));
    }

    Ok(())
}

/// Rejects reserved identifiers in syntax copied into an `impl` declaration.
pub(crate) fn reject_reserved_identifiers_in_impl(
    ctx: &Ctx,
    derive_name: &str,
    reserved_prefixes: &[&str],
) -> Result<(), Error> {
    let mut input = ctx.ast.clone();
    input.generics = generics_without_defaults(&input.generics);
    reject_reserved_identifiers(&ctx.with_input(&input), derive_name, reserved_prefixes)
}

/// Rejects the contextual `Self` type in syntax which will be copied into a
/// generated type.
///
/// `Self` resolves to the derive target in the input, but to the generated type
/// in a copied field. That can change the field's layout or validity even when
/// all generated helper names are fresh.
#[derive(Default)]
struct ContextualSelfFinder(Option<Span>);

impl<'ast> syn::visit::Visit<'ast> for ContextualSelfFinder {
    fn visit_path(&mut self, path: &'ast Path) {
        if path.leading_colon.is_none()
            && path
                .segments
                .first()
                .map(|segment| to_ident_str(&segment.ident) == "Self")
                .unwrap_or(false)
        {
            if self.0.is_none() {
                self.0 = Some(path.span());
            }
            return;
        }
        syn::visit::visit_path(self, path);
    }

    fn visit_item_impl(&mut self, _item: &'ast syn::ItemImpl) {
        // `Self` inside a nested impl denotes that impl's target, not the
        // derive target whose syntax is being copied.
    }

    fn visit_item_enum(&mut self, _item: &'ast syn::ItemEnum) {
        // `Self` inside a nested type definition denotes that nested type.
    }

    fn visit_item_struct(&mut self, _item: &'ast syn::ItemStruct) {
        // `Self` inside a nested type definition denotes that nested type.
    }

    fn visit_item_trait(&mut self, _item: &'ast syn::ItemTrait) {
        // `Self` inside a nested trait denotes that trait.
    }

    fn visit_item_trait_alias(&mut self, _item: &'ast syn::ItemTraitAlias) {
        // `Self` inside a nested trait alias denotes that trait alias.
    }

    fn visit_item_union(&mut self, _item: &'ast syn::ItemUnion) {
        // `Self` inside a nested type definition denotes that nested type.
    }
}

fn reject_contextual_self(
    finder: ContextualSelfFinder,
    derive_name: &str,
    location: &str,
) -> Result<(), Error> {
    if let Some(span) = finder.0 {
        return Err(Error::new(
            span,
            format!(
                "cannot derive `{}` with `Self` in {}; write the concrete type explicitly",
                derive_name, location,
            ),
        ));
    }
    Ok(())
}

pub(crate) fn reject_contextual_self_in_types<'a>(
    types: impl IntoIterator<Item = &'a Type>,
    derive_name: &str,
) -> Result<(), Error> {
    use syn::visit::Visit as _;

    for ty in types {
        let mut finder = ContextualSelfFinder::default();
        finder.visit_type(ty);
        reject_contextual_self(finder, derive_name, "an enum field type")?;
    }

    Ok(())
}

pub(crate) fn reject_contextual_self_in_generics(
    generics: &syn::Generics,
    derive_name: &str,
) -> Result<(), Error> {
    use syn::visit::Visit as _;

    let mut finder = ContextualSelfFinder::default();
    finder.visit_generics(generics);
    reject_contextual_self(finder, derive_name, "generic parameters or predicates")
}

impl DataExt for Data {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        match self {
            Data::Struct(strc) => strc.fields(),
            Data::Enum(enm) => enm.fields(),
            Data::Union(un) => un.fields(),
        }
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        match self {
            Data::Struct(strc) => strc.variants(),
            Data::Enum(enm) => enm.variants(),
            Data::Union(un) => un.variants(),
        }
    }

    fn tag(&self) -> Option<Ident> {
        match self {
            Data::Struct(strc) => strc.tag(),
            Data::Enum(enm) => enm.tag(),
            Data::Union(un) => un.tag(),
        }
    }
}

impl DataExt for DataStruct {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(&self.fields)
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        vec![(None, self.fields())]
    }

    fn tag(&self) -> Option<Ident> {
        None
    }
}

impl DataExt for DataEnum {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(self.variants.iter().flat_map(|var| &var.fields))
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        self.variants.iter().map(|var| (Some(var), map_fields(&var.fields))).collect()
    }

    fn tag(&self) -> Option<Ident> {
        Some(Ident::new("___ZerocopyTag", Span::call_site()))
    }
}

impl DataExt for DataUnion {
    fn fields(&self) -> Vec<(&Visibility, TokenStream, &Type)> {
        map_fields(&self.fields.named)
    }

    fn variants(&self) -> Vec<(Option<&Variant>, Vec<(&Visibility, TokenStream, &Type)>)> {
        vec![(None, self.fields())]
    }

    fn tag(&self) -> Option<Ident> {
        None
    }
}

fn map_fields<'a>(
    fields: impl 'a + IntoIterator<Item = &'a Field>,
) -> Vec<(&'a Visibility, TokenStream, &'a Type)> {
    fields
        .into_iter()
        .enumerate()
        .map(|(idx, f)| {
            (
                &f.vis,
                f.ident
                    .as_ref()
                    .map(ToTokens::to_token_stream)
                    .unwrap_or_else(|| Index::from(idx).to_token_stream()),
                &f.ty,
            )
        })
        .collect()
}

pub(crate) fn to_ident_str(t: &impl ToString) -> String {
    let s = t.to_string();
    if let Some(stripped) = s.strip_prefix("r#") {
        stripped.to_string()
    } else {
        s
    }
}

/// Does `path` consist solely of the identifier `expected`?
///
/// Unlike [`Path::is_ident`], this treats a raw identifier and its ordinary
/// spelling as the same identifier. Rust applies that same normalization when
/// interpreting attribute names and arguments.
pub(crate) fn path_is_ident(path: &Path, expected: &str) -> bool {
    match path.get_ident() {
        Some(ident) => to_ident_str(ident) == expected,
        None => false,
    }
}

/// This enum describes what kind of padding check needs to be generated for the
/// associated impl.
pub(crate) enum PaddingCheck {
    /// Check that the sum of the fields' sizes exactly equals the struct's
    /// size.
    Struct,
    /// Check that a `repr(C)` struct has no padding.
    ReprCStruct,
    /// Check that the size of each field exactly equals the union's size.
    Union,
    /// Check that every variant of the enum contains no padding.
    ///
    /// Because doing so requires a tag enum, this padding check requires an
    /// additional expression which computes the tag size in an isolated scope.
    Enum { tag_type_definition: TokenStream },
}

impl PaddingCheck {
    /// Returns the idents of the trait to use and the macro to call in order to
    /// validate that a type passes the relevant padding check.
    pub(crate) fn validator_trait_and_macro_idents(&self) -> (Ident, Ident) {
        let (trt, mcro) = match self {
            PaddingCheck::Struct => ("PaddingFree", "struct_padding"),
            PaddingCheck::ReprCStruct => ("DynamicPaddingFree", "repr_c_struct_has_padding"),
            PaddingCheck::Union => ("PaddingFree", "union_padding"),
            PaddingCheck::Enum { .. } => ("PaddingFree", "enum_padding"),
        };

        let trt = Ident::new(trt, Span::call_site());
        let mcro = Ident::new(mcro, Span::call_site());
        (trt, mcro)
    }
}

#[derive(Clone)]
pub(crate) enum Trait {
    KnownLayout,
    HasTag,
    HasField {
        variant_id: Box<Expr>,
        field: Box<Type>,
        field_id: Box<Expr>,
    },
    ProjectField {
        variant_id: Box<Expr>,
        field: Box<Type>,
        field_id: Box<Expr>,
        invariants: Box<Type>,
    },
    Immutable,
    TryFromBytes,
    FromZeros,
    FromBytes,
    IntoBytes,
    Unaligned,
    Sized,
    ByteHash,
    ByteEq,
    SplitAt,
}

impl ToTokens for Trait {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        // According to [1], the format of the derived `Debug`` output is not
        // stable and therefore not guaranteed to represent the variant names.
        // Indeed with the (unstable) `fmt-debug` compiler flag [2], it can
        // return only a minimalized output or empty string. To make sure this
        // code will work in the future and independent of the compiler flag, we
        // translate the variants to their names manually here.
        //
        // [1] https://doc.rust-lang.org/1.81.0/std/fmt/trait.Debug.html#stability
        // [2] https://doc.rust-lang.org/beta/unstable-book/compiler-flags/fmt-debug.html
        let s = match self {
            Trait::HasField { .. } => "HasField",
            Trait::ProjectField { .. } => "ProjectField",
            Trait::KnownLayout => "KnownLayout",
            Trait::HasTag => "HasTag",
            Trait::Immutable => "Immutable",
            Trait::TryFromBytes => "TryFromBytes",
            Trait::FromZeros => "FromZeros",
            Trait::FromBytes => "FromBytes",
            Trait::IntoBytes => "IntoBytes",
            Trait::Unaligned => "Unaligned",
            Trait::Sized => "Sized",
            Trait::ByteHash => "ByteHash",
            Trait::ByteEq => "ByteEq",
            Trait::SplitAt => "SplitAt",
        };
        let ident = Ident::new(s, Span::call_site());
        let arguments: Option<syn::AngleBracketedGenericArguments> = match self {
            Trait::HasField { variant_id, field, field_id } => {
                Some(parse_quote!(<#field, #variant_id, #field_id>))
            }
            Trait::ProjectField { variant_id, field, field_id, invariants } => {
                Some(parse_quote!(<#field, #invariants, #variant_id, #field_id>))
            }
            Trait::KnownLayout
            | Trait::HasTag
            | Trait::Immutable
            | Trait::TryFromBytes
            | Trait::FromZeros
            | Trait::FromBytes
            | Trait::IntoBytes
            | Trait::Unaligned
            | Trait::Sized
            | Trait::ByteHash
            | Trait::ByteEq
            | Trait::SplitAt => None,
        };
        tokens.extend(quote!(#ident #arguments));
    }
}

impl Trait {
    pub(crate) fn crate_path(&self, ctx: &Ctx) -> Path {
        let zerocopy_crate = &ctx.zerocopy_crate;
        let core = ctx.core_path();
        match self {
            Self::Sized => parse_quote!(#core::marker::#self),
            _ => parse_quote!(#zerocopy_crate::#self),
        }
    }
}

pub(crate) enum TraitBound {
    Slf,
    Other(Trait),
}

pub(crate) enum FieldBounds<'a> {
    None,
    All(&'a [TraitBound]),
    Trailing(&'a [TraitBound]),
    Explicit(Vec<WherePredicate>),
}

impl<'a> FieldBounds<'a> {
    pub(crate) const ALL_SELF: FieldBounds<'a> = FieldBounds::All(&[TraitBound::Slf]);
    pub(crate) const TRAILING_SELF: FieldBounds<'a> = FieldBounds::Trailing(&[TraitBound::Slf]);
}

pub(crate) enum SelfBounds<'a> {
    None,
    All(&'a [Trait]),
}

// FIXME(https://github.com/rust-lang/rust-clippy/issues/12908): This is a false
// positive. Explicit lifetimes are actually necessary here.
#[allow(clippy::needless_lifetimes)]
impl<'a> SelfBounds<'a> {
    pub(crate) const SIZED: Self = Self::All(&[Trait::Sized]);
}

/// Normalizes a slice of bounds by replacing [`TraitBound::Slf`] with `slf`.
pub(crate) fn normalize_bounds<'a>(
    slf: &'a Trait,
    bounds: &'a [TraitBound],
) -> impl 'a + Iterator<Item = Trait> {
    bounds.iter().map(move |bound| match bound {
        TraitBound::Slf => slf.clone(),
        TraitBound::Other(trt) => trt.clone(),
    })
}

pub(crate) struct ImplBlockBuilder<'a> {
    ctx: &'a Ctx,
    data: &'a dyn DataExt,
    trt: Trait,
    field_type_trait_bounds: FieldBounds<'a>,
    self_type_trait_bounds: SelfBounds<'a>,
    padding_check: Option<PaddingCheck>,
    param_extras: Vec<GenericParam>,
    inner_extras: Option<TokenStream>,
    outer_extras: Option<TokenStream>,
}

impl<'a> ImplBlockBuilder<'a> {
    pub(crate) fn new(
        ctx: &'a Ctx,
        data: &'a dyn DataExt,
        trt: Trait,
        field_type_trait_bounds: FieldBounds<'a>,
    ) -> Self {
        Self {
            ctx,
            data,
            trt,
            field_type_trait_bounds,
            self_type_trait_bounds: SelfBounds::None,
            padding_check: None,
            param_extras: Vec::new(),
            inner_extras: None,
            outer_extras: None,
        }
    }

    pub(crate) fn self_type_trait_bounds(mut self, self_type_trait_bounds: SelfBounds<'a>) -> Self {
        self.self_type_trait_bounds = self_type_trait_bounds;
        self
    }

    pub(crate) fn padding_check<P: Into<Option<PaddingCheck>>>(mut self, padding_check: P) -> Self {
        self.padding_check = padding_check.into();
        self
    }

    pub(crate) fn param_extras(mut self, param_extras: Vec<GenericParam>) -> Self {
        self.param_extras.extend(param_extras);
        self
    }

    pub(crate) fn inner_extras(mut self, inner_extras: TokenStream) -> Self {
        self.inner_extras = Some(inner_extras);
        self
    }

    pub(crate) fn outer_extras<T: Into<Option<TokenStream>>>(mut self, outer_extras: T) -> Self {
        self.outer_extras = outer_extras.into();
        self
    }

    pub(crate) fn build(self) -> TokenStream {
        // In this documentation, we will refer to this hypothetical struct:
        //
        //   #[derive(FromBytes)]
        //   struct Foo<T, I: Iterator>
        //   where
        //       T: Copy,
        //       I: Clone,
        //       I::Item: Clone,
        //   {
        //       a: u8,
        //       b: T,
        //       c: I::Item,
        //   }
        //
        // We extract the field types, which in this case are `u8`, `T`, and
        // `I::Item`. We re-use the existing parameters and where clauses. If
        // `require_trait_bound == true` (as it is for `FromBytes), we add where
        // bounds for each field's type:
        //
        //   impl<T, I: Iterator> FromBytes for Foo<T, I>
        //   where
        //       T: Copy,
        //       I: Clone,
        //       I::Item: Clone,
        //       T: FromBytes,
        //       I::Item: FromBytes,
        //   {
        //   }
        //
        // NOTE: It is standard practice to only emit bounds for the type
        // parameters themselves, not for field types based on those parameters
        // (e.g., `T` vs `T::Foo`). For a discussion of why this is standard
        // practice, see https://github.com/rust-lang/rust/issues/26925.
        //
        // The reason we diverge from this standard is that doing it that way
        // for us would be unsound. E.g., consider a type, `T` where `T:
        // FromBytes` but `T::Foo: !FromBytes`. It would not be sound for us to
        // accept a type with a `T::Foo` field as `FromBytes` simply because `T:
        // FromBytes`.
        //
        // While there's no getting around this requirement for us, it does have
        // the pretty serious downside that, when lifetimes are involved, the
        // trait solver ties itself in knots:
        //
        //     #[derive(Unaligned)]
        //     #[repr(C)]
        //     struct Dup<'a, 'b> {
        //         a: PhantomData<&'a u8>,
        //         b: PhantomData<&'b u8>,
        //     }
        //
        //     error[E0283]: type annotations required: cannot resolve `core::marker::PhantomData<&'a u8>: zerocopy::Unaligned`
        //      --> src/main.rs:6:10
        //       |
        //     6 | #[derive(Unaligned)]
        //       |          ^^^^^^^^^
        //       |
        //       = note: required by `zerocopy::Unaligned`

        let type_ident = &self.ctx.ast.ident;
        let trait_path = self.trt.crate_path(self.ctx);
        let fields = self.data.fields();
        let variants = self.data.variants();
        let tag = self.data.tag();
        let zerocopy_crate = &self.ctx.zerocopy_crate;

        fn bound_tt(ty: &Type, traits: impl Iterator<Item = Trait>, ctx: &Ctx) -> WherePredicate {
            let traits = traits.map(|t| t.crate_path(ctx));
            parse_quote!(#ty: #(#traits)+*)
        }
        let field_type_bounds: Vec<_> = match (self.field_type_trait_bounds, &fields[..]) {
            (FieldBounds::All(traits), _) => fields
                .iter()
                .map(|(_vis, _name, ty)| {
                    bound_tt(ty, normalize_bounds(&self.trt, traits), self.ctx)
                })
                .collect(),
            (FieldBounds::None, _) | (FieldBounds::Trailing(..), []) => vec![],
            (FieldBounds::Trailing(traits), [.., last]) => {
                vec![bound_tt(last.2, normalize_bounds(&self.trt, traits), self.ctx)]
            }
            (FieldBounds::Explicit(bounds), _) => bounds,
        };

        let padding_check_bound = self.padding_check.map(|check| {
            // Parse the repr for `align` and `packed` modifiers. Note that
            // `Repr::<PrimitiveRepr, NonZeroU32>` is more permissive than
            // what Rust supports for structs, enums, or unions, and thus
            // reliably extracts these modifiers for any kind of type.
            let repr = Repr::<PrimitiveRepr, NonZeroU32>::from_attrs(&self.ctx.ast.attrs).unwrap();
            let core = self.ctx.core_path();
            let option = quote! { #core::option::Option };
            let nonzero = quote! { #core::num::NonZeroUsize };
            let none = quote! { #option::None::<#nonzero> };
            let repr_align = repr
                .get_align()
                .map(|spanned| {
                    let n = spanned.t.get();
                    quote_spanned! { spanned.span => (#nonzero::new(#n as usize)) }
                })
                .unwrap_or(quote! { (#none) });
            let repr_packed = repr
                .get_packed()
                .map(|packed| {
                    let n = packed.get();
                    quote! { (#nonzero::new(#n as usize)) }
                })
                .unwrap_or(quote! { (#none) });
            let variant_types = variants.iter().map(|(_, fields)| {
                let types = fields.iter().map(|(_vis, _name, ty)| ty);
                quote!([#((#types)),*])
            });
            let (trt, validator_macro) = check.validator_trait_and_macro_idents();
            let check = match check {
                PaddingCheck::Enum { tag_type_definition } => quote! {
                    #zerocopy_crate::#validator_macro!(
                        @tag_size,
                        Self,
                        #repr_align,
                        #repr_packed,
                        {
                            #tag_type_definition
                            #core::mem::size_of::<___ZerocopyTag>()
                        },
                        #(#variant_types),*
                    )
                },
                _ => {
                    let t = tag.iter();
                    quote! {
                        #zerocopy_crate::#validator_macro!(
                            Self,
                            #repr_align,
                            #repr_packed,
                            #(#t,)*
                            #(#variant_types),*
                        )
                    }
                }
            };
            parse_quote! {
                (): #zerocopy_crate::util::macro_util::#trt<
                    Self,
                    {
                        #check
                    }
                >
            }
        });

        let self_bounds: Option<WherePredicate> = match self.self_type_trait_bounds {
            SelfBounds::None => None,
            SelfBounds::All(traits) => {
                Some(bound_tt(&parse_quote!(Self), traits.iter().cloned(), self.ctx))
            }
        };

        let zerocopy_bounds =
            field_type_bounds
                .into_iter()
                .chain(padding_check_bound)
                .chain(self_bounds)
                .map(|bound| {
                    if self.ctx.skip_on_error {
                        parse_quote!(for<'zc> #bound)
                    } else {
                        bound.clone()
                    }
                })
                .collect::<Vec<_>>();

        let bounds = self
            .ctx
            .ast
            .generics
            .where_clause
            .as_ref()
            .map(|where_clause| where_clause.predicates.iter())
            .into_iter()
            .flatten()
            .chain(zerocopy_bounds.iter());

        // The parameters with trait bounds, but without type defaults.
        let mut params: Vec<_> = generics_without_defaults(&self.ctx.ast.generics)
            .params
            .into_iter()
            .map(|param| parse_quote!(#param))
            .chain(self.param_extras)
            .collect();

        // For MSRV purposes, ensure that lifetimes precede types precede const
        // generics.
        params.sort_by_cached_key(|param| match param {
            GenericParam::Lifetime(_) => 0,
            GenericParam::Type(_) => 1,
            GenericParam::Const(_) => 2,
        });

        // The identifiers of the parameters without trait bounds or type
        // defaults.
        let param_idents = self.ctx.ast.generics.params.iter().map(|param| match param {
            GenericParam::Type(ty) => {
                let ident = &ty.ident;
                quote!(#ident)
            }
            GenericParam::Lifetime(l) => {
                let ident = &l.lifetime;
                quote!(#ident)
            }
            GenericParam::Const(cnst) => {
                let ident = &cnst.ident;
                quote!({#ident})
            }
        });

        let inner_extras = self.inner_extras;
        let allow_trivial_bounds =
            if self.ctx.skip_on_error { quote!(#[allow(trivial_bounds)]) } else { quote!() };
        let impl_tokens = quote! {
            #allow_trivial_bounds
            unsafe impl < #(#params),* > #trait_path for #type_ident < #(#param_idents),* >
            where
                #(#bounds,)*
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                #inner_extras
            }
        };

        let outer_extras = self.outer_extras.filter(|e| !e.is_empty());
        let cfg_compile_error = self.ctx.cfg_compile_error();
        const_block([Some(cfg_compile_error), Some(impl_tokens), outer_extras])
    }
}

// A polyfill for `Option::then_some`, which was added after our MSRV.
//
// The `#[allow(unused)]` is necessary because, on sufficiently recent toolchain
// versions, `b.then_some(...)` resolves to the inherent method rather than to
// this trait, and so this trait is considered unused.
//
// FIXME(#67): Remove this once our MSRV is >= 1.62.
#[allow(unused)]
trait BoolExt {
    fn then_some<T>(self, t: T) -> Option<T>;
}

impl BoolExt for bool {
    fn then_some<T>(self, t: T) -> Option<T> {
        if self {
            Some(t)
        } else {
            None
        }
    }
}

pub(crate) fn const_block(items: impl IntoIterator<Item = Option<TokenStream>>) -> TokenStream {
    let items = items.into_iter().flatten();
    quote! {
        #[allow(
            // FIXME(#553): Add a test that generates a warning when
            // `#[allow(deprecated)]` isn't present.
            deprecated,
            // Required on some rustc versions due to a lint that is only
            // triggered when `derive(KnownLayout)` is applied to `repr(C)`
            // structs that are generated by macros. See #2177 for details.
            private_bounds,
            non_local_definitions,
            non_camel_case_types,
            non_upper_case_globals,
            non_snake_case,
            non_ascii_idents,
            clippy::missing_inline_in_public_items,
        )]
        #[deny(ambiguous_associated_items)]
        // While there are not currently any warnings that this suppresses
        // (that we're aware of), it's good future-proofing hygiene.
        #[automatically_derived]
        const _: () = {
            #(#items)*
        };
    }
}

fn validate_tag_enum_discriminant(discriminant: &Expr) -> Result<(), Error> {
    fn reject(syntax: impl ToTokens, message: &'static str) -> Result<(), Error> {
        Err(Error::new_spanned(syntax, message))
    }

    fn validate_attrs(attrs: &[syn::Attribute]) -> Result<(), Error> {
        match attrs.first() {
            Some(attr) => reject(
                attr,
                "attributes are not supported in enum discriminants because their effect cannot \
                 be preserved in Zerocopy's generated helper enum",
            ),
            None => Ok(()),
        }
    }

    fn has_supported_integer_suffix(integer: &syn::LitInt) -> bool {
        matches!(
            integer.suffix(),
            "" | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
        )
    }

    fn validate_path(path: &Path) -> Result<(), Error> {
        if path.segments.iter().any(|segment| segment.ident == "Self") {
            // In the original discriminant, `Self` denotes the type being
            // derived. In the copied discriminant, it would denote the
            // generated tag enum instead.
            return reject(
                path,
                "`Self` is not supported in enum discriminants because its meaning cannot be \
                 preserved in Zerocopy's generated helper enum",
            );
        }

        // The original enum and generated helper enum evaluate copied
        // discriminants independently. Even a fully-qualified constant path
        // is not guaranteed to evaluate repeatably: safe const evaluation can
        // be nondeterministic, and a path can introduce caller-defined types
        // whose operators have caller-defined semantics. Restrict every leaf
        // to syntax whose value is defined directly by the compiler.
        reject(
            path,
            "paths are not supported in enum discriminants because Zerocopy's generated helper \
             enum evaluates copied discriminants independently",
        )
    }

    fn validate_endian_method_call(call: &syn::ExprMethodCall) -> Result<(), Error> {
        validate_attrs(&call.attrs)?;
        let integer = match call.receiver.as_ref() {
            Expr::Lit(ExprLit { attrs, lit: Lit::Int(integer), .. }) if attrs.is_empty() => integer,
            _ => {
                return reject(
                    call,
                    "only `.to_le()` and `.to_be()` on explicitly typed integer literals are \
                     supported in enum discriminants",
                )
            }
        };
        if !integer.suffix().is_empty()
            && has_supported_integer_suffix(integer)
            && (call.method == "to_le" || call.method == "to_be")
            && call.turbofish.is_none()
            && call.args.is_empty()
        {
            // These inherent primitive methods are selected entirely by the
            // explicit literal suffix and cannot be affected by the helper
            // enum's surrounding item or trait scope.
            Ok(())
        } else {
            reject(
                call,
                "only `.to_le()` and `.to_be()` on explicitly typed integer literals are \
                 supported in enum discriminants",
            )
        }
    }

    fn validate_expr(expr: &Expr) -> Result<(), Error> {
        match expr {
            Expr::Binary(binary) => {
                validate_attrs(&binary.attrs)?;
                match &binary.op {
                    syn::BinOp::Add(_)
                    | syn::BinOp::Sub(_)
                    | syn::BinOp::Mul(_)
                    | syn::BinOp::Div(_)
                    | syn::BinOp::Rem(_)
                    | syn::BinOp::BitXor(_)
                    | syn::BinOp::BitAnd(_)
                    | syn::BinOp::BitOr(_)
                    | syn::BinOp::Shl(_)
                    | syn::BinOp::Shr(_) => {}
                    _ => {
                        return reject(
                            binary.op,
                            "only arithmetic and bitwise operators are supported in enum \
                             discriminants",
                        )
                    }
                }
                validate_expr(&binary.left)?;
                validate_expr(&binary.right)
            }
            Expr::Group(group) => {
                validate_attrs(&group.attrs)?;
                validate_expr(&group.expr)
            }
            Expr::Lit(lit) => {
                validate_attrs(&lit.attrs)?;
                match &lit.lit {
                    Lit::Byte(_) => Ok(()),
                    Lit::Int(integer) if has_supported_integer_suffix(integer) => Ok(()),
                    Lit::Int(integer) => reject(
                        integer,
                        "only unsuffixed or primitive-integer-suffixed literals are supported in \
                         enum discriminants",
                    ),
                    Lit::Verbatim(literal) => reject(
                        literal,
                        "unparsed syntax is not supported in enum discriminants because its \
                         meaning cannot be preserved in Zerocopy's generated helper enum",
                    ),
                    _ => reject(
                        &lit.lit,
                        "only integer and byte literals are supported in enum discriminants",
                    ),
                }
            }
            Expr::MethodCall(call) => validate_endian_method_call(call),
            Expr::Paren(paren) => {
                validate_attrs(&paren.attrs)?;
                validate_expr(&paren.expr)
            }
            Expr::Path(path) => {
                validate_attrs(&path.attrs)?;
                if let Some(qself) = &path.qself {
                    if matches!(qself.ty.as_ref(), Type::Path(ty) if ty.qself.is_none() && ty.path.is_ident("Self"))
                    {
                        return reject(
                            &qself.ty,
                            "`Self` is not supported in enum discriminants because its meaning \
                             cannot be preserved in Zerocopy's generated helper enum",
                        );
                    }
                    return reject(
                        path,
                        "qualified type-relative paths are not supported in enum discriminants \
                         because their meaning cannot be preserved in Zerocopy's generated \
                         helper enum",
                    );
                }
                validate_path(&path.path)
            }
            Expr::Unary(unary) => {
                validate_attrs(&unary.attrs)?;
                match &unary.op {
                    syn::UnOp::Neg(_) | syn::UnOp::Not(_) => validate_expr(&unary.expr),
                    _ => reject(
                        unary.op,
                        "only negation and bitwise-not unary operators are supported in enum \
                         discriminants",
                    ),
                }
            }
            Expr::Macro(mac) => {
                // A macro can emit `Self` even if its invocation does not
                // contain a `Self` token. Expanding it once in the original
                // enum and again in the helper enum can produce different
                // values.
                reject(
                    mac,
                    "macros are not supported in enum discriminants because their expansion \
                     cannot be preserved in Zerocopy's generated helper enum",
                )
            }
            Expr::Verbatim(tokens) => reject(
                tokens,
                "unparsed syntax is not supported in enum discriminants because its meaning \
                 cannot be preserved in Zerocopy's generated helper enum",
            ),
            _ => {
                // This is a positive grammar. In particular, it rejects every
                // pattern, binding, control-flow construct, call, non-endian
                // method call, block item, macro, and current or future
                // unparsed AST variant. Those constructs can resolve names
                // differently after the expression is copied into the
                // generated helper enum.
                reject(
                    expr,
                    "this expression is not supported in enum discriminants because its meaning \
                     cannot be preserved in Zerocopy's generated helper enum",
                )
            }
        }
    }

    validate_expr(discriminant)
}

pub(crate) fn validate_tag_enum_discriminants(data: &DataEnum) -> Result<(), Error> {
    for variant in &data.variants {
        if let Some((_, discriminant)) = &variant.discriminant {
            validate_tag_enum_discriminant(discriminant)?;
        }
    }
    Ok(())
}

fn tag_enum_discriminant_lint_attrs(attrs: &[syn::Attribute]) -> Vec<TokenStream> {
    attrs
        .iter()
        .filter_map(|attr| {
            // A lint level explicitly attached to the source enum or one of
            // its variants applies to its discriminants, but not to the
            // generated helper enum. Copy only source-provided levels which
            // can permit the primitive expressions admitted by
            // `validate_tag_enum_discriminant`.
            //
            // In particular, do not add an unconditional `allow`: lowering a
            // lint which an enclosing scope forbids is itself an error, even
            // when the copied discriminant would not trigger that lint.
            if !path_is_ident(attr.path(), "allow")
                && !path_is_ident(attr.path(), "expect")
                && !path_is_ident(attr.path(), "warn")
            {
                return None;
            }

            let nested = attr
                .parse_args_with(
                    syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
                )
                .ok()?;
            let lints = nested.iter().filter_map(|meta| match meta {
                Meta::Path(path)
                    if path_is_ident(path, "overflowing_literals")
                        || path_is_ident(path, "arithmetic_overflow") =>
                {
                    Some(path)
                }
                _ => None,
            });
            let lints = lints.collect::<Vec<_>>();
            if lints.is_empty() {
                return None;
            }

            // `warn` lowers these deny-by-default lints, and `expect` also
            // permits them while requiring a diagnostic in the source item.
            // The helper only needs the permissive level. Reproducing `warn`
            // would emit duplicate diagnostics, while reproducing `expect`
            // could create a new unfulfilled expectation.
            Some(quote_spanned! { attr.span()=> #[allow(#(#lints),*)] })
        })
        .collect()
}

pub(crate) fn generate_tag_enum(
    ctx: &Ctx,
    repr: &EnumRepr,
    data: &DataEnum,
) -> Result<TokenStream, Error> {
    // This proof assumes that rustc does not let a later attribute macro
    // replace the input item while retaining this derive's output. That is a
    // compiler TCB premise; rust-lang/rust#148423 tracks its violation. A
    // local check cannot distinguish later active attributes from arbitrary
    // inert derive-helper attributes, and a partial attribute allowlist would
    // not protect Zerocopy's other generated unsafe impls.
    validate_tag_enum_discriminants(data)?;
    let zerocopy_crate = &ctx.zerocopy_crate;
    let discriminant_lint_attrs = tag_enum_discriminant_lint_attrs(&ctx.ast.attrs);
    let variants = data
        .variants
        .iter()
        .map(|v| -> Result<TokenStream, Error> {
            let ident = &v.ident;
            let variant_lint_attrs = tag_enum_discriminant_lint_attrs(&v.attrs);
            if let Some((eq, discriminant)) = &v.discriminant {
                Ok(quote! { #(#variant_lint_attrs)* #ident #eq #discriminant })
            } else {
                Ok(quote! { #(#variant_lint_attrs)* #ident })
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Don't include any `repr(align)` when generating the tag enum, as that
    // could add padding after the tag but before any variants, which is not the
    // correct behavior.
    let repr = match repr {
        EnumRepr::Transparent(span) => quote::quote_spanned! { *span => #[repr(transparent)] },
        EnumRepr::Compound(c, _) => quote! { #c },
    };

    Ok(quote! {
        #repr
        #(#discriminant_lint_attrs)*
        #[allow(dead_code)]
        pub enum ___ZerocopyTag {
            #(#variants,)*
        }

        // SAFETY: `___ZerocopyTag` has no fields, and so it does not permit
        // interior mutation.
        unsafe impl #zerocopy_crate::Immutable for ___ZerocopyTag {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    })
}

pub(crate) fn enum_has_full_discriminant_domain(repr: &EnumRepr, enm: &DataEnum) -> bool {
    enum_size_from_repr(repr).map(|size| enm.variants.len() == 1usize << size).unwrap_or(false)
}

pub(crate) fn enum_could_be_from_bytes(repr: &EnumRepr, enm: &DataEnum) -> bool {
    enm.fields().is_empty() && enum_has_full_discriminant_domain(repr, enm)
}

pub(crate) fn enum_size_from_repr(repr: &EnumRepr) -> Result<usize, Error> {
    use CompoundRepr::*;
    use PrimitiveRepr::*;
    use Repr::*;
    match repr {
        Transparent(span)
        | Compound(
            Spanned {
                t: C | Rust | Primitive(U32 | I32 | U64 | I64 | U128 | I128 | Usize | Isize),
                span,
            },
            _,
        ) => Err(Error::new(
            *span,
            "`FromBytes` only supported on enums with `#[repr(...)]` attributes `u8`, `i8`, `u16`, or `i16`",
        )),
        Compound(Spanned { t: Primitive(U8 | I8), span: _ }, _align) => Ok(8),
        Compound(Spanned { t: Primitive(U16 | I16), span: _ }, _align) => Ok(16),
    }
}

#[cfg(test)]
pub(crate) mod testutil {
    use proc_macro2::TokenStream;
    use syn::visit::{self, Visit};

    #[test]
    fn rejects_opaque_syntax_nested_in_field_types() {
        let attributed: syn::Type = syn::parse_quote!(
            [u8; #[stateful]
            1]
        );
        let error = super::reject_uninspectable_types([&attributed], "IntoBytes").unwrap_err();
        assert!(error.to_string().contains("containing an attribute"));

        let verbatim = syn::Type::Verbatim(quote::quote!(dyn* Trait));
        let error = super::reject_uninspectable_types([&verbatim], "KnownLayout").unwrap_err();
        assert!(error.to_string().contains("unsupported unresolved syntax"));

        let generic: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T: Select<{ choose!() }>>(T);
        };
        let error =
            super::reject_uninspectable_generics(&generic.generics, "TryFromBytes").unwrap_err();
        assert!(error.to_string().contains("a macro invocation"));
        assert!(error.to_string().contains("generic parameters or predicates"));

        let defaults: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T = type_default!(), const N: usize = { const_default!() }>([T; N]);
        };
        super::reject_uninspectable_impl_generics(&defaults.generics, "TryFromBytes").unwrap();
        super::reject_uninspectable_generics(&defaults.generics, "TryFromBytes").unwrap_err();
    }

    #[test]
    fn rejects_reserved_unqualified_identifiers() {
        let direct: syn::DeriveInput = syn::parse_quote! {
            struct Packet {
                field: __ZerocopyGeneratedHelper,
            }
        };
        let direct = super::Ctx::try_from_derive_input(direct).unwrap();
        let error = super::reject_reserved_identifiers(&direct, "KnownLayout", &["__Zerocopy"])
            .unwrap_err();
        assert!(error.to_string().contains("`__ZerocopyGeneratedHelper` is reserved"));

        let qualified: syn::DeriveInput = syn::parse_quote! {
            struct Packet {
                field: crate::types::__ZerocopyGeneratedHelper,
            }
        };
        let qualified = super::Ctx::try_from_derive_input(qualified).unwrap();
        super::reject_reserved_identifiers(&qualified, "KnownLayout", &["__Zerocopy"]).unwrap();

        let qself_terminal: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T>(<T>::__ZerocopyAssociated);
        };
        let qself_terminal = super::Ctx::try_from_derive_input(qself_terminal).unwrap();
        super::reject_reserved_identifiers(&qself_terminal, "KnownLayout", &["__Zerocopy"])
            .unwrap();

        let qself_expr_terminal: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T>([u8; <T>::__ZerocopyAssociated]);
        };
        let qself_expr_terminal = super::Ctx::try_from_derive_input(qself_expr_terminal).unwrap();
        super::reject_reserved_identifiers(&qself_expr_terminal, "KnownLayout", &["__Zerocopy"])
            .unwrap();

        let qself_struct_terminals: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T>([u8; {
                let _ = <T>::__ZerocopyStruct { field: 0 };
                match todo!() {
                    <T>::__ZerocopyStruct { field: _ } => 0,
                    <T>::__ZerocopyTuple(_) => 1,
                }
            }]);
        };
        let qself_struct_terminals =
            super::Ctx::try_from_derive_input(qself_struct_terminals).unwrap();
        super::reject_reserved_identifiers(&qself_struct_terminals, "KnownLayout", &["__Zerocopy"])
            .unwrap();

        let qself_trait_root: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T>(<T as __ZerocopyTrait>::Associated);
        };
        let qself_trait_root = super::Ctx::try_from_derive_input(qself_trait_root).unwrap();
        super::reject_reserved_identifiers(&qself_trait_root, "KnownLayout", &["__Zerocopy"])
            .unwrap_err();

        let qself_argument: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T>(<T>::Associated<__ZerocopyArgument>);
        };
        let qself_argument = super::Ctx::try_from_derive_input(qself_argument).unwrap();
        super::reject_reserved_identifiers(&qself_argument, "KnownLayout", &["__Zerocopy"])
            .unwrap_err();

        let target: syn::DeriveInput = syn::parse_quote! {
            struct __ZerocopyGeneratedHelper;
        };
        let target = super::Ctx::try_from_derive_input(target).unwrap();
        super::reject_reserved_identifiers(&target, "KnownLayout", &["__Zerocopy"]).unwrap_err();

        // The type parameter's only use is through `Self`, so this exercises
        // declaration scanning rather than an ordinary type-path reference.
        let type_parameter: syn::DeriveInput = syn::parse_quote! {
            struct Packet<___ZerocopyType>(<Self as Assoc>::Type)
            where
                Self: Assoc;
        };
        let type_parameter = super::Ctx::try_from_derive_input(type_parameter).unwrap();
        super::reject_reserved_identifiers(&type_parameter, "TryFromBytes", &["___Zerocopy"])
            .unwrap_err();

        let default_only: syn::DeriveInput = syn::parse_quote! {
            struct Packet<T = ___ZcDefault>(T);
        };
        let default_only = super::Ctx::try_from_derive_input(default_only).unwrap();
        super::reject_reserved_identifiers_in_impl(&default_only, "TryFromBytes", &["___Zc"])
            .unwrap();
        super::reject_reserved_identifiers(&default_only, "TryFromBytes", &["___Zc"]).unwrap_err();

        let pattern: syn::DeriveInput = syn::parse_quote! {
            enum Packet {
                Variant([u8; match 0 { ___ZEROCOPY_TAG_Variant => 1, _ => 2 }]),
            }
        };
        let pattern = super::Ctx::try_from_derive_input(pattern).unwrap();
        super::reject_reserved_identifiers(&pattern, "TryFromBytes", &["___ZEROCOPY"]).unwrap_err();

        let imported: syn::DeriveInput = syn::parse_quote! {
            struct Packet([u8; {
                use __ZerocopyGeneratedHelper as T;
                core::mem::size_of::<T>()
            }]);
        };
        let imported = super::Ctx::try_from_derive_input(imported).unwrap();
        super::reject_reserved_identifiers(&imported, "KnownLayout", &["__Zerocopy"]).unwrap_err();

        let qualified_import: syn::DeriveInput = syn::parse_quote! {
            struct Packet([u8; {
                use crate::types::__ZerocopyGeneratedHelper as T;
                core::mem::size_of::<T>()
            }]);
        };
        let qualified_import = super::Ctx::try_from_derive_input(qualified_import).unwrap();
        super::reject_reserved_identifiers(&qualified_import, "KnownLayout", &["__Zerocopy"])
            .unwrap();
    }

    #[test]
    fn accepts_inspectable_blocks_but_rejects_nested_macros() {
        let inspectable: syn::Type = syn::parse_quote!(
            [u8; {
                const N: usize = 4;
                N
            }]
        );
        super::reject_uninspectable_types([&inspectable], "IntoBytes").unwrap();

        let macro_in_block: syn::Type = syn::parse_quote! {
            [u8; { macro_rules! n { () => { 4 } } n!() }]
        };
        let error = super::reject_uninspectable_types([&macro_in_block], "IntoBytes").unwrap_err();
        assert!(error.to_string().contains("a macro invocation"));
    }

    #[test]
    fn rejects_contextual_self_recursively() {
        let nested: syn::Type =
            syn::parse_quote!([u8; core::mem::size_of::<core::mem::Discriminant<Self>>()]);
        let error = super::reject_contextual_self_in_types([&nested], "TryFromBytes").unwrap_err();
        assert!(error.to_string().contains("`Self` in an enum field type"));

        let generic: syn::DeriveInput = syn::parse_quote! {
            enum Packet<T: Select<Self>> {
                Variant(T),
            }
        };
        let error = super::reject_contextual_self_in_generics(&generic.generics, "TryFromBytes")
            .unwrap_err();
        assert!(error.to_string().contains("`Self` in generic parameters or predicates"));

        let nested_items: syn::Type = syn::parse_quote! {
            [u8; {
                struct NestedStruct(core::marker::PhantomData<Self>);
                enum NestedEnum {
                    Variant(core::marker::PhantomData<Self>),
                }
                union NestedUnion {
                    field: core::mem::ManuallyDrop<Self>,
                }
                0
            }]
        };
        super::reject_contextual_self_in_types([&nested_items], "TryFromBytes").unwrap();
    }

    /// Checks for hygiene violations in the generated code.
    ///
    /// # Panics
    ///
    /// Panics if a hygiene violation is found.
    pub(crate) fn check_hygiene(ts: TokenStream) {
        struct AmbiguousItemVisitor;

        fn panic_ambiguous_path(path: &impl quote::ToTokens) -> ! {
            panic!(
                "Found ambiguous path `{}` in generated output. \
                 All associated item access must be fully qualified (e.g., `<Self as Trait>::Item`) \
                 to prevent hygiene issues.",
                quote::quote!(#path)
            );
        }

        impl<'ast> Visit<'ast> for AmbiguousItemVisitor {
            fn visit_expr_path(&mut self, i: &'ast syn::ExprPath) {
                if let Some(qself) = &i.qself {
                    if qself.position == 0 {
                        panic_ambiguous_path(i);
                    }
                }
                visit::visit_expr_path(self, i);
            }

            fn visit_path(&mut self, i: &'ast syn::Path) {
                if i.segments.len() > 1 && i.segments.first().unwrap().ident == "Self" {
                    panic_ambiguous_path(i);
                }
                visit::visit_path(self, i);
            }

            fn visit_type_path(&mut self, i: &'ast syn::TypePath) {
                if let Some(qself) = &i.qself {
                    if qself.position == 0 {
                        panic_ambiguous_path(i);
                    }
                }
                visit::visit_type_path(self, i);
            }
        }

        let file = syn::parse2::<syn::File>(ts).expect("failed to parse generated output as File");
        AmbiguousItemVisitor.visit_file(&file);
    }

    #[test]
    fn test_check_hygiene_success() {
        check_hygiene(quote::quote! {
            fn foo() {
                let _ = <Self as Trait>::Item;
            }
        });
    }

    #[test]
    #[should_panic(expected = "Found ambiguous path `Self :: Ambiguous`")]
    fn test_check_hygiene_failure() {
        check_hygiene(quote::quote! {
            fn foo() {
                let _ = Self::Ambiguous;
            }
        });
    }

    #[test]
    #[should_panic(expected = "Found ambiguous path `< T > :: Ambiguous`")]
    fn test_check_hygiene_type_relative_expr_failure() {
        check_hygiene(quote::quote! {
            fn foo<T>() {
                let _ = <T>::Ambiguous;
            }
        });
    }

    #[test]
    #[should_panic(expected = "Found ambiguous path `< T > :: Ambiguous`")]
    fn test_check_hygiene_type_relative_type_failure() {
        check_hygiene(quote::quote! {
            fn foo<T>() {
                let _: <T>::Ambiguous;
            }
        });
    }

    #[test]
    fn test_validate_tag_enum_discriminant_accepts_stable_context() {
        use syn::parse_quote;

        for expr in [
            parse_quote!(1),
            parse_quote!(1 + 2),
            parse_quote!(!0 & (1 << 2)),
            parse_quote!(9_u32.to_le()),
            parse_quote!(0x0800_u16.to_be()),
        ] {
            assert!(super::validate_tag_enum_discriminant(&expr).is_ok());
        }
    }

    #[test]
    fn test_validate_tag_enum_discriminant_rejects_context_dependent_syntax() {
        use syn::parse_quote;

        for expr in [
            parse_quote!(Self::TAG),
            parse_quote!(1 + Self::TAG),
            parse_quote!(<Self as crate::Tag>::TAG),
            parse_quote!(TAG),
            parse_quote!(module::TAG),
            parse_quote!(crate::TAG),
            parse_quote!(self::TAG),
            parse_quote!(super::TAG),
            parse_quote!(super::super::TAG),
            parse_quote!(crate::CUSTOM + 1),
            parse_quote!(crate::Type::TAG),
            parse_quote!(::core::primitive::u8::MAX),
            parse_quote!(<crate::Type>::TAG),
            parse_quote!(<crate::Type as crate::Trait>::TAG),
            parse_quote!(tag!()),
            parse_quote!(1 + tag!()),
            parse_quote!(crate::tag()),
            parse_quote!(0_u8.count_ones()),
            parse_quote!(0.to_le()),
            parse_quote!((0_u8).to_le()),
            parse_quote!(0 as u8),
            parse_quote!(0_custom),
            parse_quote!(if true { 0 } else { 1 }),
            parse_quote!(match 0 {
                ___ZEROCOPY_TAG_Raw if true => 0,
                _ => 1,
            }),
            parse_quote!({
                const TAG: u8 = 0;
                TAG
            }),
            parse_quote!(crate::Tag::<u8>::VALUE),
            parse_quote!(
                #[cfg(any())]
                1
            ),
            syn::Expr::Verbatim(quote::quote!(some future syntax)),
        ] {
            assert!(super::validate_tag_enum_discriminant(&expr).is_err());
        }
    }

    #[test]
    fn test_validate_tag_enum_discriminant_rejects_nested_verbatim_type() {
        use syn::{Expr, Type};

        // `syn` 2.0.56 accepts `dyn*` but represents it as `Type::Verbatim`.
        // The `Self` token in this type must not evade structural validation.
        let expr =
            syn::parse_str::<Expr>("<dyn* crate::Marker<Self> as crate::Value>::VALUE").unwrap();
        let ty = match &expr {
            Expr::Path(path) => &path.qself.as_ref().unwrap().ty,
            _ => panic!("expected an expression path"),
        };
        assert!(matches!(ty.as_ref(), Type::Verbatim(_)));
        assert!(super::validate_tag_enum_discriminant(&expr).is_err());
    }

    #[test]
    fn test_validate_tag_enum_discriminant_rejects_verbatim_literal() {
        use syn::{parse_quote, Expr, Lit};

        let mut expr: Expr = parse_quote!(0);
        match &mut expr {
            Expr::Lit(expr) => {
                expr.lit = Lit::Verbatim(proc_macro2::Literal::u8_unsuffixed(0));
            }
            _ => panic!("expected a literal expression"),
        }
        assert!(super::validate_tag_enum_discriminant(&expr).is_err());
    }

    #[test]
    fn test_tag_enum_discriminant_lint_attrs_normalize_permissive_levels() {
        use syn::parse_quote;

        let input = parse_quote! {
            #[allow(overflowing_literals)]
            #[warn(arithmetic_overflow)]
            #[expect(overflowing_literals, reason = "checked on the source enum")]
            #[deny(overflowing_literals)]
            enum Foo {
                #[warn(overflowing_literals)]
                #[expect(arithmetic_overflow, reason = "checked on the source variant")]
                #[deny(arithmetic_overflow)]
                A = 0,
            }
        };
        let ctx = super::Ctx::try_from_derive_input(input).unwrap();
        let attrs = super::tag_enum_discriminant_lint_attrs(&ctx.ast.attrs);
        assert_eq!(
            quote::quote!(#(#attrs)*).to_string(),
            "# [allow (overflowing_literals)] # [allow (arithmetic_overflow)] # [allow (overflowing_literals)]",
        );
        let variant = match &ctx.ast.data {
            syn::Data::Enum(data) => &data.variants[0],
            _ => unreachable!(),
        };
        let attrs = super::tag_enum_discriminant_lint_attrs(&variant.attrs);
        assert_eq!(
            quote::quote!(#(#attrs)*).to_string(),
            "# [allow (overflowing_literals)] # [allow (arithmetic_overflow)]",
        );
    }

    #[test]
    fn test_validate_crate_path() {
        use syn::parse_str;

        let valid = [
            "zerocopy",
            "crate",
            "crate::foo::bar",
            "self",
            "self::foo",
            "self::super::foo",
            "super",
            "super::foo",
            "super::super::foo",
            "super::super::super",
            "foo::bar::baz",
            "::foo::bar",
        ];

        for path_str in valid {
            let path = parse_str::<syn::Path>(path_str).unwrap();
            assert!(
                super::validate_crate_path(&path).is_ok(),
                "expected valid path for `{}`",
                path_str
            );
        }

        let invalid = [
            "::crate::foo",
            "::self::foo",
            "::super::foo",
            "Self",
            "Self::foo",
            "foo::Self::bar",
            "foo::crate::bar",
            "foo::super::bar",
            "foo::self",
            "super::foo::super",
            "super::crate::foo",
            "crate::super::foo",
            "self::self::foo",
        ];

        for path_str in invalid {
            let path = parse_str::<syn::Path>(path_str).unwrap();
            assert!(
                super::validate_crate_path(&path).is_err(),
                "expected invalid path for `{}`",
                path_str
            );
        }
    }

    #[test]
    fn test_path_is_ident() {
        use syn::parse_str;

        for (expected, ordinary, raw) in [
            ("doc", "doc", "r#doc"),
            ("repr", "repr", "r#repr"),
            ("zerocopy", "zerocopy", "r#zerocopy"),
            ("on_error", "on_error", "r#on_error"),
        ] {
            let ordinary = parse_str::<syn::Path>(ordinary).unwrap();
            let raw = parse_str::<syn::Path>(raw).unwrap();
            assert!(super::path_is_ident(&ordinary, expected));
            assert!(super::path_is_ident(&raw, expected));
        }

        // `r#crate` is forbidden by Rust's raw identifier grammar.
        let crate_path = parse_str::<syn::Path>("crate").unwrap();
        assert!(super::path_is_ident(&crate_path, "crate"));

        for path in ["::zerocopy", "module::zerocopy"] {
            let path = parse_str::<syn::Path>(path).unwrap();
            assert!(!super::path_is_ident(&path, "zerocopy"));
        }
    }

    #[test]
    fn test_raw_zerocopy_attributes() {
        let ast: syn::DeriveInput = syn::parse_quote! {
            #[r#zerocopy(crate = "renamed", r#on_error = "skip")]
            struct Foo;
        };

        let ctx = super::Ctx::try_from_derive_input(ast).unwrap();
        let path = &ctx.zerocopy_crate;
        assert_eq!(quote::quote!(#path).to_string(), ":: renamed");
        assert!(ctx.skip_on_error);
    }
}
