//! Translate information about items: name, attributes, etc.
use itertools::Itertools;
use rustc_middle::mir;
use rustc_span::RemapPathScopeComponents;
use std::{
    cmp::Ord,
    path::{Component, PathBuf},
    sync::LazyLock,
};

use super::translate_crate::RustcItem;
use super::translate_ctx::*;
use crate::hax;
use crate::hax::{DefPathItem, SInto};
use charon_lib::{ast::*, name_matcher::NamePattern};

// Spans
impl<'tcx> TranslateCtx<'tcx> {
    /// Register a file if it is a "real" file and was not already registered
    /// `span` must be a span from which we obtained that filename.
    fn register_file(&mut self, filename: FileName, span: rustc_span::Span) -> FileId {
        // Lookup the file if it was already registered
        match self.file_to_id.get(&filename) {
            Some(id) => *id,
            None => {
                let source_file = self.tcx.sess.source_map().lookup_source_file(span.lo());
                let crate_name = self.tcx.crate_name(source_file.cnum).to_string();
                let id = self.translated.files.push_with(|id| File {
                    id,
                    name: filename.clone(),
                    crate_name,
                    contents: source_file.src.as_deref().cloned(),
                });
                self.file_to_id.insert(filename, id);
                id
            }
        }
    }

    pub fn translate_filename(&mut self, name: rustc_span::FileName) -> meta::FileName {
        match name {
            rustc_span::FileName::Real(name) => {
                match name.local_path() {
                    Some(path) => {
                        // Normalize path separators: cross-compiling to Windows uses `\` as path
                        // separators.
                        let path: PathBuf = {
                            let mut normalized = PathBuf::new();
                            for comp in path.components() {
                                for segment in comp.as_os_str().to_string_lossy().split("\\") {
                                    normalized.push(segment);
                                }
                            }
                            normalized
                        };
                        // Find the cargo home directory: according to cargo docs and having a
                        // look at the cargo source, it's either the `$CARGO_HOME` var or
                        // `$HOME/.cargo`
                        static CURRENT_DIR: LazyLock<Option<PathBuf>> =
                            LazyLock::new(|| std::env::current_dir().ok());
                        static CARGO_HOME: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
                            std::env::var("CARGO_HOME")
                                .map(PathBuf::from)
                                .ok()
                                .or_else(|| std::env::home_dir().map(|p| p.join(".cargo")))
                        });
                        // The path to files in the standard library may be full paths to
                        // somewhere in the sysroot or in the original toolchain source tree. This
                        // may depend on how the toolchain is installed (rustup vs nix), so we
                        // normalize the paths here to avoid inconsistencies in the translation.
                        let path = if let Some(rust_src) = path
                            .ancestors()
                            .find(|ancestor| ancestor.ends_with("lib/rustlib/src/rust"))
                            && let Ok(path) = path.strip_prefix(rust_src)
                        {
                            let mut rewritten_path: PathBuf = "/rustc".into();
                            rewritten_path.extend(path);
                            rewritten_path
                        } else if let Ok(path) = path.strip_prefix(&self.sysroot) {
                            // Unclear if this can happen, but just in case.
                            let mut rewritten_path: PathBuf = "/toolchain".into();
                            rewritten_path.extend(path);
                            rewritten_path
                        } else if let Some(cargo_home) = &*CARGO_HOME
                            && let Ok(path) = path.strip_prefix(cargo_home)
                        {
                            let mut rewritten_path: PathBuf = "/cargo".into();
                            rewritten_path.extend(path);
                            rewritten_path
                        } else if let Some(current_dir) = &*CURRENT_DIR
                            && let Ok(path) = path.strip_prefix(current_dir)
                        {
                            path.to_path_buf()
                        } else {
                            path
                        };
                        FileName::Local(path)
                    }
                    None => {
                        // We use the virtual name because it is always available.
                        // That name normally starts with `/rustc/<hash>/`. For our purposes we hide
                        // the hash.
                        let virtual_name = name.path(RemapPathScopeComponents::MACRO);
                        let mut components_iter = virtual_name.components();
                        if let Some(
                            [
                                Component::RootDir,
                                Component::Normal(rustc),
                                Component::Normal(hash),
                            ],
                        ) = components_iter.by_ref().array_chunks().next()
                            && rustc.to_str() == Some("rustc")
                            && hash.len() == 40
                        {
                            let path_without_hash = [Component::RootDir, Component::Normal(rustc)]
                                .into_iter()
                                .chain(components_iter)
                                .collect();
                            FileName::Virtual(path_without_hash)
                        } else {
                            FileName::Virtual(virtual_name.into())
                        }
                    }
                }
            }
            // We use the debug formatter to generate a filename.
            // This is not ideal, but filenames are for debugging anyway.
            _ => FileName::NotReal(format!("{name:?}")),
        }
    }

    pub fn translate_span_data(&mut self, span: rustc_span::Span) -> meta::SpanData {
        if let Some(data) = self.cached_spans.get(&span) {
            return *data;
        }
        let data = self.translate_span_data_uncached(span);
        self.cached_spans.insert(span, data);
        data
    }

    fn translate_span_data_uncached(&mut self, span: rustc_span::Span) -> meta::SpanData {
        let smap: &rustc_span::source_map::SourceMap = self.tcx.sess.psess.source_map();
        let source_file = smap.lookup_source_file(span.lo());
        let file_id = match self.cached_file_ids.get(&source_file.stable_id) {
            Some(id) => *id,
            None => {
                let filename = self.translate_filename(source_file.name.clone());
                let file_id = match &filename {
                    FileName::NotReal(_) => {
                        // For now we forbid not real filenames
                        unimplemented!();
                    }
                    FileName::Virtual(_) | FileName::Local(_) => self.register_file(filename, span),
                };
                self.cached_file_ids.insert(source_file.stable_id, file_id);
                file_id
            }
        };

        let convert_loc = |pos: rustc_span::BytePos| -> Loc {
            let (line, _col, col_display) = source_file.lookup_file_pos_with_col_display(pos);
            Loc {
                line: line as u32,
                col: col_display as u32,
            }
        };
        let beg = convert_loc(span.lo());
        let end = convert_loc(span.hi());

        // Put together
        meta::SpanData { file_id, beg, end }
    }

    /// Compute span data from a Rust source scope
    pub fn translate_span_from_source_info(
        &mut self,
        source_scopes: &rustc_index::IndexVec<mir::SourceScope, mir::SourceScopeData>,
        source_info: &mir::SourceInfo,
    ) -> Span {
        // Translate the span
        let data = self.translate_span_data(source_info.span);

        // Lookup the top-most inlined parent scope.
        let mut parent_span = None;
        let mut scope_data = &source_scopes[source_info.scope];
        while let Some(parent_scope) = scope_data.inlined_parent_scope {
            scope_data = &source_scopes[parent_scope];
            parent_span = Some(scope_data.span);
        }

        if let Some(parent_span) = parent_span {
            let parent_span = self.translate_span_data(parent_span);
            Span::new(parent_span, Some(data))
        } else {
            Span::new(data, None)
        }
    }

    pub(crate) fn translate_span(&mut self, span: &rustc_span::Span) -> Span {
        Span::new(self.translate_span_data(*span), None)
    }

    pub(crate) fn def_span(&mut self, def_id: &hax::DefId) -> Span {
        let span = def_id.def_span(&self.hax_state);
        self.translate_span(&span)
    }
}

// Names
impl<'tcx> TranslateCtx<'tcx> {
    fn path_elem_for_def(
        &mut self,
        span: Span,
        item: &RustcItem,
    ) -> Result<Option<PathElem>, Error> {
        let def_id = item.def_id();
        if let Some(synthetic) = def_id.as_synthetic(&self.hax_state) {
            return Ok(match synthetic {
                hax::SyntheticItem::Tuple(n) => Some(PathElem::Builtin(
                    BuiltinPathElem::Tuple(n),
                    Disambiguator::ZERO,
                )),
                hax::SyntheticItem::Str => {
                    Some(PathElem::Builtin(BuiltinPathElem::Str, Disambiguator::ZERO))
                }
                hax::SyntheticItem::Array
                | hax::SyntheticItem::Slice
                | hax::SyntheticItem::FnPtr(_) => None,
            });
        }
        let path_elem = def_id.path_item(&self.hax_state);
        // Disambiguator disambiguates identically-named (but distinct) identifiers. This happens
        // notably with macros and inherent impl blocks.
        let disambiguator = Disambiguator::new(path_elem.disambiguator as usize);
        // Match over the key data
        let path_elem = match path_elem.data {
            DefPathItem::CrateRoot { name, .. } => {
                Some(PathElem::Ident(name.to_string(), disambiguator))
            }
            // We map the three namespaces onto a single one. We can always disambiguate by looking
            // at the definition.
            DefPathItem::TypeNs(symbol)
            | DefPathItem::ValueNs(symbol)
            | DefPathItem::MacroNs(symbol) => {
                Some(PathElem::Ident(symbol.to_string(), disambiguator))
            }
            DefPathItem::Impl => {
                // Two cases, depending on whether the impl block is
                // a "regular" impl block (`impl Foo { ... }`) or a trait
                // implementation (`impl Bar for Foo { ... }`).
                let impl_elem = match def_id.kind {
                    // Inherent impl ("regular" impl)
                    hax::DefKind::Impl { of_trait: false } => {
                        let full_def = self.hax_def_for_item(item)?;
                        let hax::FullDefKind::InherentImpl(i) = full_def.kind() else {
                            unreachable!()
                        };
                        // We need to convert the type, which may contain quantified
                        // substs and bounds. In order to properly do so, we introduce
                        // a body translation context.
                        let item_src =
                            TransItemSource::new(item.clone(), TransItemSourceKind::InherentImpl);
                        let mut bt_ctx = ItemTransCtx::new(item_src, None, self);
                        bt_ctx.translate_item_generics(
                            span,
                            &full_def,
                            &TransItemSourceKind::InherentImpl,
                        )?;
                        let ty = bt_ctx.translate_ty(span, i.ty())?;
                        ImplElem::Ty(Box::new(Binder {
                            kind: BinderKind::InherentImplBlock,
                            params: bt_ctx.into_generics(),
                            skip_binder: ty,
                        }))
                    }
                    // Trait implementation
                    hax::DefKind::Impl { of_trait: true } => {
                        let impl_id = {
                            let item_src = TransItemSource::new(
                                item.clone(),
                                TransItemSourceKind::TraitImpl(TransImplSource::Normal),
                            );
                            self.register_and_enqueue(&None, item_src).unwrap()
                        };
                        ImplElem::Trait(impl_id)
                    }
                    _ => unreachable!(),
                };

                Some(PathElem::Impl(impl_elem))
            }
            // TODO: do nothing for now
            DefPathItem::OpaqueTy => None,
            // TODO: this is not very satisfactory, but on the other hand
            // we should be able to extract closures in local let-bindings
            // (i.e., we shouldn't have to introduce top-level let-bindings).
            DefPathItem::Closure => {
                Some(PathElem::Builtin(BuiltinPathElem::Closure, disambiguator))
            }
            // Do nothing, functions in `extern` blocks are in the same namespace as the
            // block.
            DefPathItem::ForeignMod => None,
            // Do nothing, the constructor of a struct/variant has the same name as the
            // struct/variant.
            DefPathItem::Ctor => None,
            DefPathItem::Use => Some(PathElem::Builtin(BuiltinPathElem::Use, disambiguator)),
            DefPathItem::AnonConst => {
                Some(PathElem::Builtin(BuiltinPathElem::AnonConst, disambiguator))
            }
            DefPathItem::PromotedConst => Some(PathElem::Builtin(
                BuiltinPathElem::PromotedConst,
                disambiguator,
            )),
            _ => {
                raise_error!(
                    self,
                    span,
                    "Unexpected DefPathItem for `{def_id:?}`: {path_elem:?}"
                );
            }
        };
        Ok(path_elem)
    }

    /// Retrieve the name for this [`hax::DefId`]. Because a given `DefId` may give rise to several
    /// charon items, prefer to use `translate_name` when possible.
    ///
    /// We lookup the path associated to an id, and convert it to a name.
    /// Paths very precisely identify where an item is. There are important
    /// subcases, like the items in an `Impl` block:
    /// ```ignore
    /// impl<T> List<T> {
    ///   fn new() ...
    /// }
    /// ```
    ///
    /// One issue here is that "List" *doesn't appear* in the path, which would
    /// look like the following:
    ///
    ///   `TypeNS("Crate") :: Impl :: ValueNs("new")`
    ///                       ^^^
    ///           This is where "List" should be
    ///
    /// For this reason, whenever we find an `Impl` path element, we actually
    /// lookup the type of the sub-path, from which we can derive a name.
    ///
    /// Besides, as there may be several "impl" blocks for one type, each impl
    /// block is identified by a unique number (rustc calls this a
    /// "disambiguator"), which we grab.
    ///
    /// Example:
    /// ========
    /// For instance, if we write the following code in crate `test` and module
    /// `bla`:
    /// ```ignore
    /// impl<T> Foo<T> {
    ///   fn foo() { ... }
    /// }
    ///
    /// impl<T> Foo<T> {
    ///   fn bar() { ... }
    /// }
    /// ```
    ///
    /// The names we will generate for `foo` and `bar` are:
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(0)), Ident("foo")]`
    /// `[Ident("test"), Ident("bla"), Ident("Foo"), Impl(impl<T> Ty<T>, Disambiguator(1)), Ident("bar")]`
    fn name_for_item(&mut self, item: &RustcItem) -> Result<Name, Error> {
        if let Some(name) = self.cached_names.get(item) {
            return Ok(name.clone());
        }
        let def_id = item.def_id();
        trace!("Computing name for `{def_id:?}`");

        let is_builtin = def_id.as_synthetic(&self.hax_state).is_some();
        let parent_name = if !is_builtin && let Some(parent_id) = def_id.parent(&self.hax_state) {
            if let RustcItem::Mono(item_ref) = item
                && let Some(parent_item) = item_ref.typing_parent(&self.hax_state)
            {
                self.name_for_item(&RustcItem::Mono(parent_item))?
            } else {
                self.name_for_item(&RustcItem::Poly(parent_id.clone()))?
            }
        } else {
            Name { name: Vec::new() }
        };
        let span = self.def_span(def_id);
        let mut name = parent_name;
        if let Some(path_elem) = self.path_elem_for_def(span, item)? {
            name.name.push(path_elem);
        }

        trace!("Computed name for `{def_id:?}`: `{name:?}`");
        self.cached_names.insert(item.clone(), name.clone());
        Ok(name)
    }

    /// Compute the name for an item.
    /// Internal function, use `translate_name`.
    pub fn name_for_src(&mut self, src: &TransItemSource) -> Result<Name, Error> {
        let mut name = if let Some(parent) = src.parent() {
            self.name_for_src(&parent)?
        } else {
            self.name_for_item(&src.item)?
        };
        match &src.kind {
            // Nothing to do for the real items.
            TransItemSourceKind::Type
            | TransItemSourceKind::Fun
            | TransItemSourceKind::Global
            | TransItemSourceKind::TraitImpl(TransImplSource::Normal)
            | TransItemSourceKind::TraitDecl
            | TransItemSourceKind::InherentImpl
            | TransItemSourceKind::Module => {}

            TransItemSourceKind::TraitImpl(
                kind @ (TransImplSource::Callable(..)
                | TransImplSource::ImplicitDestruct
                | TransImplSource::TraitAlias),
            ) => {
                if let TransImplSource::Callable(..) = kind {
                    let _ = name.name.pop(); // Pop the `{closure}`
                }
                let impl_id = self.register_and_enqueue(&None, src.clone()).unwrap();
                name.name.push(PathElem::Impl(ImplElem::Trait(impl_id)));
            }
            TransItemSourceKind::TraitImpl(TransImplSource::Marker) => {
                unreachable!("marker impls are only used as vtable item sources")
            }
            TransItemSourceKind::CallableMethod(kind) => {
                let fn_name = kind.method_name().to_string();
                name.name
                    .push(PathElem::Ident(fn_name, Disambiguator::ZERO));
            }
            TransItemSourceKind::DropGlueMethod(..) => {
                name.name.push(PathElem::Builtin(
                    BuiltinPathElem::DropGlue,
                    Disambiguator::ZERO,
                ));
            }
            TransItemSourceKind::ClosureAsFnCast => {
                name.name.push(PathElem::Builtin(
                    BuiltinPathElem::ClosureAsFn,
                    Disambiguator::ZERO,
                ));
            }
            TransItemSourceKind::VTable
            | TransItemSourceKind::VTableInstance(..)
            | TransItemSourceKind::VTableInstanceInitializer(..) => {
                name.name.push(PathElem::Builtin(
                    BuiltinPathElem::VTable,
                    Disambiguator::ZERO,
                ));
            }
            TransItemSourceKind::VTableMethod(..) => {
                name.name.push(PathElem::Builtin(
                    BuiltinPathElem::VTableMethod,
                    Disambiguator::ZERO,
                ));
            }
            TransItemSourceKind::VTableDropShim(..) => {
                name.name.push(PathElem::Builtin(
                    BuiltinPathElem::VTableDropShim,
                    Disambiguator::ZERO,
                ));
            }
        }
        Ok(name)
    }

    /// Retrieve the name for an item.
    pub fn translate_name(&mut self, src: &TransItemSource) -> Result<Name, Error> {
        let mut name = self.name_for_src(src)?;
        // Push the generics used for monomorphization, if any. We skip mono trait impls as the
        // generics are already included in the `PathElem::Impl` reference.
        if let RustcItem::Mono(item_ref) = &src.item
            && !item_ref.generic_args.is_empty()
            && !matches!(src.kind, TransItemSourceKind::TraitImpl(..))
        {
            let trans_id = self.register_no_enqueue(&None, src).unwrap();
            let span = self.def_span(&item_ref.def_id);
            let mut bt_ctx = ItemTransCtx::new(src.clone(), trans_id, self);
            let binder = bt_ctx.inside_binder(BinderKind::Other, None, |bt_ctx| {
                // We skip the clauses: the args are enough to uniquely identify an ite.
                bt_ctx.translate_generic_args(span, &item_ref.generic_args, &[])
            })?;
            if !binder.skip_binder.is_empty() {
                name.name.push(PathElem::Instantiated(Box::new(binder)));
            }
        }
        Ok(name)
    }

    pub(crate) fn opacity_for_name(&self, name: &Name) -> ItemOpacity {
        self.options.opacity_for_name(&self.translated, name)
    }
}

enum ContractTarget {
    Parent,
    Path(String),
}

// Attributes
impl<'tcx> TranslateCtx<'tcx> {
    fn resolve_contract_target(
        &mut self,
        def_id: &hax::DefId,
        target: ContractTarget,
    ) -> Result<MaybeAssocItemId, String> {
        if !matches!(
            def_id.kind,
            hax::DefKind::Fn | hax::DefKind::AssocFn | hax::DefKind::Closure
        ) {
            return Err("contract attributes can only be applied to functions".to_string());
        }

        let parent_id = def_id.parent(&self.hax_state);
        let target_def_id = match &target {
            ContractTarget::Parent => parent_id.ok_or_else(|| {
                "#[charon::contract(..., parent)] is invalid at the crate root".to_string()
            })?,
            ContractTarget::Path(target_name) => {
                let mut siblings = Vec::new();
                if let Some(parent_id) = &parent_id {
                    let parent_def = self.poly_hax_def(parent_id).map_err(|err| err.msg)?;
                    siblings.extend(
                        parent_def
                            .nameable_children(&self.hax_state)
                            .into_iter()
                            .map(|(_, id)| id),
                    );

                    // Free items inside a function body aren't in the `nameable_children`.
                    if matches!(
                        parent_def.kind(),
                        hax::FullDefKind::Fn(_)
                            | hax::FullDefKind::AssocFn(_)
                            | hax::FullDefKind::Closure(_)
                    ) && let Some(parent_local_id) =
                        parent_id.as_real_def_id().and_then(|id| id.as_local())
                        && let Some(body_id) =
                            self.tcx.hir_node_by_def_id(parent_local_id).body_id()
                    {
                        use rustc_hir::intravisit;

                        struct NestedItems(Vec<rustc_hir::def_id::LocalDefId>);
                        impl<'tcx> intravisit::Visitor<'tcx> for NestedItems {
                            fn visit_nested_item(&mut self, id: rustc_hir::ItemId) {
                                self.0.push(id.owner_id.def_id);
                            }
                        }

                        let mut nested_items = NestedItems(Vec::new());
                        intravisit::walk_body(&mut nested_items, self.tcx.hir_body(body_id));
                        siblings.extend(
                            nested_items
                                .0
                                .into_iter()
                                .map(|id| id.to_def_id().sinto(&self.hax_state)),
                        );
                    }
                }
                let siblings = siblings
                    .into_iter()
                    .filter(|sibling| sibling != def_id)
                    .filter(|sibling| match sibling.path_item(&self.hax_state).data {
                        DefPathItem::ValueNs(name)
                        | DefPathItem::TypeNs(name)
                        | DefPathItem::MacroNs(name) => name.as_str() == target_name.as_str(),
                        _ => false,
                    })
                    .collect_vec();
                match siblings.as_slice() {
                    [sibling] => sibling.clone(),
                    [] => {
                        // Fall back to full path search.
                        let path = NamePattern::parse(target_name)
                            .map_err(|err| format!("invalid item path `{target_name}`: {err}"))?;
                        let targets =
                            super::resolve_path::def_path_def_ids(&self.hax_state, &path, true)
                                .map_err(|err| {
                                    format!("failed to resolve item path `{target_name}`: {err}")
                                })?;
                        let [target] = targets.as_slice() else {
                            return Err(format!(
                                "item path `{target_name}` resolved to {} items; expected exactly one",
                                targets.len()
                            ));
                        };
                        target.sinto(&self.hax_state)
                    }
                    _ => {
                        return Err(format!(
                            "found several sibling items named `{target_name}`; expected exactly one"
                        ));
                    }
                }
            }
        };

        let target_def = self.poly_hax_def(&target_def_id).map_err(|err| err.msg)?;
        if self.options.monomorphize_with_hax && target_def.this().has_non_lt_param {
            return Err("contracts on generic items are not supported \
                with `--monomorphize`"
                .to_string());
        }

        let associated_item = match target_def.kind() {
            hax::FullDefKind::AssocFn(f) => Some(f.associated_item()),
            hax::FullDefKind::AssocConst(c) => Some(c.associated_item()),
            hax::FullDefKind::AssocTy(t) => Some(t.associated_item()),
            _ => None,
        };
        if let ContractTarget::Path(_) = target
            && let Some(associated_item) = associated_item
            && let hax::AssocItemContainer::TraitContainer { trait_ref } =
                &associated_item.container
        {
            let kind = TransItemSourceKind::TraitDecl;
            let trait_src =
                TransItemSource::from_item(trait_ref, kind, self.options.monomorphize_with_hax);
            let trait_id = self.register_and_enqueue(&None, trait_src).unwrap();
            let item_id = self
                .translate_assoc_item_id(trait_id, &target_def_id)
                .map_err(|err| err.msg)?;
            Ok(MaybeAssocItemId::Assoc(trait_id, item_id))
        } else {
            let kind = match target_def.kind() {
                // Point at the method that contains the closure code.
                hax::FullDefKind::Closure(c) => TransItemSourceKind::CallableMethod(
                    super::translate_closures::translate_closure_kind(&c.args().kind),
                ),
                _ => self
                    .base_kind_for_item(&target_def_id)
                    .ok_or_else(|| format!("`{target_def_id:?}` is not a translatable item"))?,
            };
            let target_src = TransItemSource::from_item(
                target_def.this(),
                kind,
                self.options.monomorphize_with_hax,
            );
            let item_id: ItemId = self.register_and_enqueue(&None, target_src).unwrap();
            Ok(MaybeAssocItemId::Free(item_id))
        }
    }

    /// Parse a raw attribute to recognize our special `charon::*`, `aeneas::*` and `verify::*` attributes.
    fn parse_attr_from_raw(
        &mut self,
        def_id: &hax::DefId,
        raw_attr: RawAttribute,
    ) -> Result<Attribute, String> {
        // If the attribute path has two components, the first of which is `charon` or `aeneas`, we
        // try to parse it. Otherwise we return `Unknown`.
        let path = raw_attr.path.split("::").collect_vec();
        let attr_name = if let &[path_start, attr_name] = path.as_slice()
            && (path_start == "charon" || path_start == "aeneas" || path_start == "verify")
        {
            attr_name
        } else {
            return Ok(Attribute::Unknown(raw_attr));
        };

        match self.parse_special_attr(def_id, attr_name, &raw_attr)? {
            Some(parsed) => Ok(parsed),
            None => Err(format!("Unrecognized attribute: `{}`", raw_attr)),
        }
    }

    /// Parse a `charon::*`, `aeneas::*` or `verify::*` attribute.
    fn parse_special_attr(
        &mut self,
        def_id: &hax::DefId,
        attr_name: &str,
        raw_attr: &RawAttribute,
    ) -> Result<Option<Attribute>, String> {
        let args = raw_attr.args.as_deref();
        let parsed = match attr_name {
            // `#[charon::opaque]`
            "opaque" if args.is_none() => Attribute::Opaque,
            // `#[charon::opaque]`
            "exclude" if args.is_none() => Attribute::Exclude,
            // `#[charon::transparent]`
            "transparent" if args.is_none() => Attribute::Transparent,
            // `#[charon::contract(kind = "...", parent)]` or
            // `#[charon::contract(kind = "...", for = "path")]`
            "contract" if let Some(args) = args => {
                use syn::{ext::IdentExt, parse::Parser};

                let parser = |input: syn::parse::ParseStream<'_>| {
                    let mut kind = None;
                    let mut target = None;
                    while !input.is_empty() {
                        let key = input.call(syn::Ident::parse_any)?;
                        let key_name = key.to_string();
                        if key_name == "parent" && !input.peek(syn::Token![=]) {
                            if target.is_some() {
                                return Err(syn::Error::new(
                                    key.span(),
                                    "duplicate contract target",
                                ));
                            }
                            target = Some(ContractTarget::Parent);
                        } else {
                            input.parse::<syn::Token![=]>()?;
                            let value = input.parse::<syn::LitStr>()?.value();
                            match key_name.as_str() {
                                "kind" => {
                                    if kind.is_some() {
                                        return Err(syn::Error::new(
                                            key.span(),
                                            "duplicate contract argument `kind`",
                                        ));
                                    }
                                    kind = Some(value);
                                }
                                "for" => {
                                    if target.is_some() {
                                        return Err(syn::Error::new(
                                            key.span(),
                                            "duplicate contract target",
                                        ));
                                    }
                                    target = Some(ContractTarget::Path(value));
                                }
                                "parent" => {
                                    return Err(syn::Error::new(
                                        key.span(),
                                        "contract argument `parent` does not take a value",
                                    ));
                                }
                                _ => {
                                    return Err(syn::Error::new(
                                        key.span(),
                                        format!("unknown contract argument `{key}`"),
                                    ));
                                }
                            }
                        }
                        if !input.is_empty() {
                            input.parse::<syn::Token![,]>()?;
                        }
                    }
                    let kind =
                        kind.ok_or_else(|| input.error("missing contract argument `kind`"))?;
                    let target = target
                        .ok_or_else(|| input.error("missing contract target `parent` or `for`"))?;
                    Ok((kind, target))
                };
                let (kind, target) = parser.parse_str(args).map_err(|err| {
                    format!(
                        "invalid contract syntax: {err}; expected \
                         `#[charon::contract(kind = \"...\", parent)]` or \
                         `#[charon::contract(kind = \"...\", for = \"item path\")]`"
                    )
                })?;
                Attribute::IsContract {
                    kind,
                    target: self.resolve_contract_target(def_id, target)?,
                }
            }
            // `#[charon::rename("new_name")]`
            "rename" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the new name should be between quotes: `rename(\"{attr}\")`."
                    ));
                };

                if attr.is_empty() {
                    return Err(format!("attribute `rename` should not be empty"));
                }

                let first_char = attr.chars().nth(0).unwrap();
                let is_identifier = (first_char.is_alphabetic() || first_char == '_')
                    && attr.chars().all(|c| c.is_alphanumeric() || c == '_');
                if !is_identifier {
                    return Err(format!(
                        "attribute `rename` should contain a valid identifier"
                    ));
                }

                Attribute::Rename(attr.to_string())
            }
            // `#[charon::variants_prefix("T")]`
            "variants_prefix" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the name should be between quotes: `variants_prefix(\"{attr}\")`."
                    ));
                };

                Attribute::VariantsPrefix(attr.to_string())
            }
            // `#[charon::variants_suffix("T")]`
            "variants_suffix" if let Some(attr) = args => {
                let Some(attr) = attr
                    .strip_prefix("\"")
                    .and_then(|attr| attr.strip_suffix("\""))
                else {
                    return Err(format!(
                        "the name should be between quotes: `variants_suffix(\"{attr}\")`."
                    ));
                };

                Attribute::VariantsSuffix(attr.to_string())
            }
            // `#[verify::start_from]`
            "start_from" => {
                if matches!(def_id.kind, hax::DefKind::Mod) {
                    return Err("`start_from` on modules has no effect".to_string());
                }
                Attribute::Unknown(raw_attr.clone())
            }
            // `#[verify::test]`: mark a function for test extraction
            "test" if args.is_none() => Attribute::Unknown(raw_attr.clone()),
            _ => return Ok(None),
        };
        Ok(Some(parsed))
    }

    /// Translates a rust attribute. Returns `None` if the attribute is a doc comment (rustc
    /// encodes them as attributes). For now we use `String`s for `Attributes`.
    pub(crate) fn translate_attribute(
        &mut self,
        def_id: &hax::DefId,
        attr: &rustc_hir::Attribute,
    ) -> Option<Attribute> {
        use rustc_hir as hir;
        use rustc_hir::attrs as hir_attrs;
        match attr {
            hir::Attribute::Parsed(hir_attrs::AttributeKind::DocComment { comment, .. }) => {
                (!self.options.no_doc_comments).then(|| Attribute::DocComment(comment.to_string()))
            }
            hir::Attribute::Parsed(attr) => self
                .translate_rustc_attribute_kind(attr)
                .ok()
                .map(Attribute::Builtin),
            hir::Attribute::Unparsed(attr) => {
                let raw_attr = RawAttribute {
                    path: attr.path.to_string(),
                    args: match &attr.args {
                        hir::AttrArgs::Empty => None,
                        hir::AttrArgs::Delimited(args) => {
                            Some(rustc_ast_pretty::pprust::tts_to_string(&args.tokens))
                        }
                        hir::AttrArgs::Eq { expr, .. } => {
                            self.tcx.sess.source_map().span_to_snippet(expr.span).ok()
                        }
                    },
                };
                match self.parse_attr_from_raw(def_id, raw_attr) {
                    Ok(a) => Some(a),
                    Err(msg) => {
                        let span = self.translate_span(&attr.span.sinto(&self.hax_state));
                        register_error!(self, span, "Error parsing attribute: {msg}");
                        None
                    }
                }
            }
        }
    }

    pub(crate) fn translate_inline(&self, def: &hax::FullDef<'tcx>) -> Option<InlineAttr> {
        let inline = match def.kind() {
            hax::FullDefKind::Fn(f) => f.inline(),
            hax::FullDefKind::AssocFn(f) => f.inline(),
            hax::FullDefKind::Closure(c) => c.inline(),
            _ => return None,
        };
        match inline {
            hax::InlineAttr::None => None,
            hax::InlineAttr::Hint => Some(InlineAttr::Hint),
            hax::InlineAttr::Never => Some(InlineAttr::Never),
            hax::InlineAttr::Always => Some(InlineAttr::Always),
            hax::InlineAttr::Force { .. } => Some(InlineAttr::Always),
        }
    }

    pub(crate) fn translate_attr_info(&mut self, def: &hax::FullDef<'tcx>) -> AttrInfo {
        // Default to `false` for impl blocks and closures.
        let public = def.visibility.unwrap_or(false);
        let inline = self.translate_inline(def);
        let attributes = def
            .attributes
            .iter()
            .filter_map(|attr| self.translate_attribute(def.def_id(), attr))
            .collect_vec();

        let rename = {
            let mut renames = attributes.iter().filter_map(|a| a.as_rename()).cloned();
            let rename = renames.next();
            if renames.next().is_some() {
                let span = self.translate_span(&def.span);
                register_error!(
                    self,
                    span,
                    "There should be at most one `charon::rename(\"...\")` \
                    or `aeneas::rename(\"...\")` attribute per declaration",
                );
            }
            rename
        };

        AttrInfo {
            attributes,
            inline,
            public,
            rename,
        }
    }
}

// `ItemMeta`
impl<'tcx> TranslateCtx<'tcx> {
    /// Whether this item is in an `extern { .. }` block, in which case it has no body.
    pub(crate) fn is_extern_item(&mut self, def: &hax::FullDef<'tcx>) -> bool {
        def.def_id()
            .parent(&self.hax_state)
            .is_some_and(|parent| matches!(parent.kind, hax::DefKind::ForeignMod))
    }

    /// If this is an item declared in an `extern { .. }` block, return its symbol name.
    pub(crate) fn extern_item_symbol_name(&mut self, def: &hax::FullDef<'tcx>) -> Option<String> {
        if !self.is_extern_item(def) {
            return None;
        }
        let path_item = def.def_id().path_item(&self.hax_state);
        match path_item.data {
            hax::DefPathItem::ValueNs(name) | hax::DefPathItem::TypeNs(name) => {
                Some(name.to_string())
            }
            _ => None,
        }
    }

    /// Compute the meta information for a Rust item.
    pub(crate) fn translate_item_meta(
        &mut self,
        def: &hax::FullDef<'tcx>,
        item_src: &TransItemSource,
        name: Name,
        name_opacity: ItemOpacity,
    ) -> ItemMeta {
        if let Some(item_meta) = self.cached_item_metas.get(item_src) {
            return item_meta.clone();
        }
        let span = def.source_span.as_ref().unwrap_or(&def.span);
        let span = self.translate_span(span);
        let is_local = def.def_id().is_local();
        let (attr_info, lang_item, diagnostic_item) = if !item_src.is_derived_item()
            || matches!(item_src.kind, TransItemSourceKind::CallableMethod(..))
        {
            let attr_info = self.translate_attr_info(def);
            let lang_item = def
                .def_id()
                .as_real_def_id()
                .and_then(|id| self.tcx.as_lang_item(id))
                .map(|lang_item| {
                    self.translate_rustc_lang_item(&lang_item)
                        .expect("all rustc LangItem variants should be translated")
                });
            let diagnostic_item = def.diagnostic_item.map(|s| s.to_string());
            (attr_info, lang_item, diagnostic_item)
        } else {
            (AttrInfo::default(), None, None)
        };

        let opacity = if attr_info.attributes.iter().any(|attr| attr.is_exclude()) {
            ItemOpacity::Invisible.max(name_opacity)
        } else if self.is_poly_in_mono(item_src) {
            if matches!(item_src.kind, TransItemSourceKind::TraitImpl(..)) {
                ItemOpacity::Opaque.max(name_opacity)
            } else {
                ItemOpacity::Invisible.max(name_opacity)
            }
        } else if self.is_extern_item(def)
            || attr_info.attributes.iter().any(|attr| attr.is_opaque())
        {
            // Force opaque in these cases.
            ItemOpacity::Opaque.max(name_opacity)
        } else {
            name_opacity
        };

        let item_meta = ItemMeta {
            name,
            span,
            source_text: def.source_text.clone(),
            attr_info,
            is_local,
            started_from: !item_src.is_derived_item()
                && self.started_from.contains(item_src.def_id()),
            opacity,
            lang_item,
            diagnostic_item,
            has_errors: false,
        };
        self.cached_item_metas
            .insert(item_src.clone(), item_meta.clone());
        item_meta
    }
}
