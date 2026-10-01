use super::translate_crate::*;
use super::translate_ctx::*;
use crate::hax;
use crate::hax::SInto;
use charon_lib::ast::*;
use charon_lib::formatter::IntoFormatter;
use charon_lib::options::ConstHandling;
use charon_lib::pretty::FmtWithCtx;
use derive_generic_visitor::Visitor;
use itertools::Itertools;
use rustc_span::sym;
use std::mem;
use std::ops::ControlFlow;

impl<'tcx> TranslateCtx<'tcx> {
    pub(crate) fn translate_item(&mut self, item_src: &TransItemSource) {
        let _guard = charon_lib::timing::scope_lazy("translate-item", || {
            let kind = format!("{:?}", item_src.kind);
            kind.split('(').next().unwrap().to_owned()
        });
        let trans_id = self.register_no_enqueue(&None, item_src);
        let def_id = item_src.def_id();
        if let Some(trans_id) = trans_id {
            if self.translate_stack.contains(&trans_id) {
                register_error!(
                    self,
                    Span::dummy(),
                    "Cycle detected while translating {def_id:?}! Stack: {:?}",
                    &self.translate_stack
                );
                return;
            } else {
                self.translate_stack.push(trans_id);
            }
        }
        self.with_def_id(def_id, trans_id, |mut ctx| {
            let span = ctx.def_span(def_id);
            // Catch cycles
            let res = {
                // Stopgap measure because there are still many panics in charon and hax.
                let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                std::panic::catch_unwind(move || ctx.translate_item_aux(item_src, trans_id))
            };
            match res {
                Ok(Ok(())) => return,
                // Translation error
                Ok(Err(_)) => {
                    register_error!(ctx, span, "Item `{def_id:?}` caused errors; ignoring.")
                }
                // Panic
                Err(_) => register_error!(
                    ctx,
                    span,
                    "Thread panicked when extracting item `{def_id:?}`."
                ),
            };
        });
        if let Some(trans_id) = trans_id
            && self.errors.borrow().item_has_errors(trans_id)
            && let Some(mut item) = self.translated.get_item_mut(trans_id)
        {
            item.item_meta().has_errors = true;
        }
        // We must be careful not to early-return from this function to not unbalance the stack.
        self.translate_stack.pop();
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: &TransItemSource,
        trans_id: Option<ItemId>,
    ) -> Result<(), Error> {
        // The name may have already been computed.
        let name = match trans_id.and_then(|id| self.translated.item_names.get(&id)) {
            Some(name) => name.clone(),
            None => {
                let name = self.translate_name(item_src)?;
                if let Some(trans_id) = trans_id {
                    self.translated.item_names.insert(trans_id, name.clone());
                }
                name
            }
        };
        let opacity = self.opacity_for_name(&name);
        if opacity.is_invisible() {
            // Don't even start translating the item. In particular don't call `hax_def` on it.
            return Ok(());
        }
        let def = self.hax_def_for_item(&item_src.item)?;
        let item_meta = self.translate_item_meta(&def, item_src, name, opacity);
        if item_meta.opacity.is_invisible() {
            return Ok(());
        }

        // For items in the current crate that have bodies, also enqueue items defined in that
        // body.
        if !item_meta.opacity.is_opaque()
            && let Some(def_id) = def.def_id().as_real_def_id()
            && let Some(ldid) = def_id.as_local()
            && let node = self.tcx.hir_node_by_def_id(ldid)
            && let Some(body_id) = node.body_id()
        {
            use rustc_hir::intravisit;
            struct EnqueueNestedItems<'a, 'tcx> {
                ctx: &'a mut TranslateCtx<'tcx>,
                started_from: bool,
            }
            impl<'tcx> intravisit::Visitor<'tcx> for EnqueueNestedItems<'_, 'tcx> {
                fn visit_nested_item(&mut self, id: rustc_hir::ItemId) {
                    let def_id = id.owner_id.def_id.to_def_id();
                    let def_id = def_id.sinto(&self.ctx.hax_state);
                    self.ctx.enqueue_module_item(&def_id, self.started_from);
                }
            }
            let body = self.tcx.hir_body(body_id);
            intravisit::walk_body(
                &mut EnqueueNestedItems {
                    ctx: self,
                    started_from: item_meta.started_from,
                },
                body,
            );
        }

        // Initialize the item translation context
        let mut bt_ctx = ItemTransCtx::new(item_src.clone(), trans_id, self);
        trace!(
            "About to translate item `{:?}` as a {:?}; \
            target_id={trans_id:?}, mono={}",
            def.def_id(),
            item_src.kind,
            bt_ctx.monomorphize(),
        );
        if !matches!(
            &item_src.kind,
            TransItemSourceKind::InherentImpl | TransItemSourceKind::Module,
        ) {
            bt_ctx.translate_item_generics(item_meta.span, &def, &item_src.kind)?;
        }
        match &item_src.kind {
            TransItemSourceKind::InherentImpl | TransItemSourceKind::Module => {
                bt_ctx.register_module(item_meta, &def);
            }
            TransItemSourceKind::Type => {
                let Some(ItemId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let ty = bt_ctx.translate_type_decl(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSourceKind::Fun => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_fun_decl(id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSourceKind::Global => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl = bt_ctx.translate_global(id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            TransItemSourceKind::TraitDecl => {
                let Some(ItemId::TraitDecl(id)) = trans_id else {
                    unreachable!()
                };
                let trait_decl = bt_ctx.translate_trait_decl(id, item_meta, &def)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            TransItemSourceKind::TraitImpl(kind) => {
                let Some(ItemId::TraitImpl(id)) = trans_id else {
                    unreachable!()
                };
                // In Mono mode, only user-defined trait is supported for now.
                let trait_impl = match kind {
                    TransImplSource::Normal => bt_ctx.translate_trait_impl(id, item_meta, &def)?,
                    TransImplSource::TraitAlias => {
                        bt_ctx.translate_trait_alias_blanket_impl(id, item_meta, &def)?
                    }
                    &TransImplSource::Callable(kind) => {
                        bt_ctx.translate_closure_trait_impl(id, item_meta, &def, kind)?
                    }
                    TransImplSource::ImplicitDestruct => {
                        bt_ctx.translate_implicit_destruct_impl(id, item_meta, &def)?
                    }
                    TransImplSource::Marker => {
                        unreachable!("marker impls are only used as vtable item sources")
                    }
                };
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
            &TransItemSourceKind::CallableMethod(kind) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_closure_method(id, item_meta, &def, kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSourceKind::ClosureAsFnCast => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_stateless_closure_as_fn(id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            &TransItemSourceKind::DropGlueMethod(impl_kind) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_drop_glue_method(id, item_meta, &def, impl_kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSourceKind::VTable => {
                let Some(ItemId::Type(id)) = trans_id else {
                    unreachable!()
                };
                let ty_decl = bt_ctx.translate_vtable_struct(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty_decl);
            }
            &TransItemSourceKind::VTableInstance(impl_kind) => {
                let Some(ItemId::Global(id)) = trans_id else {
                    unreachable!()
                };
                let global_decl =
                    bt_ctx.translate_vtable_instance(id, item_meta, &def, impl_kind)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            &TransItemSourceKind::VTableInstanceInitializer(impl_kind) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl =
                    bt_ctx.translate_vtable_instance_init(id, item_meta, &def, impl_kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            &TransItemSourceKind::VTableMethod(impl_kind) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_vtable_shim(id, item_meta, &def, impl_kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            &TransItemSourceKind::VTableDropShim(impl_kind) => {
                let Some(ItemId::Fun(id)) = trans_id else {
                    unreachable!()
                };
                let fun_decl = bt_ctx.translate_vtable_drop_shim(id, item_meta, &def, impl_kind)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
        }
        Ok(())
    }

    /// While translating an item you may need the contents of another. Use this to retreive the
    /// translated version of this item. Use with care as this could create cycles.
    pub(crate) fn get_or_translate(&mut self, id: ItemId) -> Result<ItemRef<'_>, Error> {
        // We have to call `get_item` a few times because we're running into the classic `Polonius`
        // problem case.
        if self.translated.get_item(id).is_none() {
            let item_source = self.reverse_id_map.get(&id).unwrap().clone();
            self.translate_item(&item_source);
            if self.translated.get_item(id).is_none() {
                let span = self.def_span(item_source.def_id());
                let name = id.to_string_with_ctx(&self.into_fmt());
                // Not a real error, its message won't be displayed.
                return Err(Error {
                    span,
                    msg: format!("Failed to translate item {name}."),
                });
                // raise_error!(self, span, "Failed to translate item {name}.")
            }
            // Add to avoid the double translation of the same item
            self.processed.insert(item_source.clone());
        }
        let item = self.translated.get_item(id);
        Ok(item.unwrap())
    }

    /// Record that `method_id` is an implementation of the given method of the trait. If the
    /// method is not used anywhere yet we simply record the implementation. If the method is used
    /// then we enqueue it for translation.
    pub fn register_method_impl(
        &mut self,
        trait_id: TraitDeclId,
        method_id: TraitMethodId,
        fun_id: FunDeclId,
    ) {
        match &mut self.method_status[trait_id][method_id] {
            MethodStatus::Unused { implementors } => {
                implementors.insert(fun_id);
            }
            MethodStatus::Used => {
                self.enqueue_id(fun_id);
            }
        }
    }

    /// Mark the method as "used", which will enqueue for translation all the implementations of
    /// that method.
    pub fn mark_method_as_used(&mut self, trait_id: TraitDeclId, method_id: TraitMethodId) {
        let old_status = mem::replace(
            &mut self.method_status[trait_id][method_id],
            MethodStatus::Used,
        );
        match old_status {
            MethodStatus::Unused { implementors } => {
                for fun_id in implementors {
                    self.enqueue_id(fun_id);
                }
            }
            MethodStatus::Used => {}
        }
    }

    /// Keep only the methods we marked as "used".
    pub fn remove_unused_methods(&mut self) {
        let method_is_used = |trait_id: TraitDeclId, method_id: TraitMethodId| {
            matches!(self.method_status[trait_id][method_id], MethodStatus::Used)
        };
        for tdecl in self.translated.trait_decls.iter_mut() {
            tdecl
                .methods
                .retain(|i, _m| method_is_used(tdecl.def_id, i));
        }
        for timpl in self.translated.trait_impls.iter_mut() {
            let trait_id = timpl.impl_trait.id;
            timpl.methods.retain(|i, _m| method_is_used(trait_id, i));
        }
    }
}

enum TraitItemSource {
    Default {
        trait_ref: TraitDeclRef,
        item_id: AssocItemId,
    },
    Impl {
        impl_ref: TraitImplRef,
        trait_ref: TraitDeclRef,
        item_id: AssocItemId,
        reuses_default: bool,
    },
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Register the items inside this module or inherent impl.
    // TODO: we may want to accumulate the set of modules we found, to check that all
    // the opaque modules given as arguments actually exist
    #[tracing::instrument(skip(self, item_meta, def))]
    pub(crate) fn register_module(&mut self, item_meta: ItemMeta, def: &hax::FullDef<'tcx>) {
        if !item_meta.opacity.is_transparent() {
            return;
        }
        match def.kind() {
            hax::FullDefKind::InherentImpl(i) => {
                for assoc in i.items(self.hax_state()) {
                    self.t_ctx
                        .enqueue_module_item(&assoc.def_id, item_meta.started_from);
                }
            }
            hax::FullDefKind::Mod(m) => {
                for (_, def_id) in m.items(self.hax_state()) {
                    self.t_ctx
                        .enqueue_module_item(def_id, item_meta.started_from);
                }
            }
            hax::FullDefKind::ForeignMod(m) => {
                for def_id in m.items() {
                    self.t_ctx
                        .enqueue_module_item(def_id, item_meta.started_from);
                }
            }
            _ => panic!("Item should be a module but isn't: {def:?}"),
        }
    }

    fn get_trait_item_source(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<Option<TraitItemSource>, Error> {
        let assoc = match def.kind() {
            hax::FullDefKind::AssocConst(c) => c.associated_item(),
            hax::FullDefKind::AssocFn(f) => f.associated_item(),
            _ => return Ok(None),
        };
        Ok(Some(match &assoc.container {
            // E.g.:
            // ```
            // impl<T> List<T> {
            //   fn new() -> Self { ... } <- inherent method
            // }
            // ```
            hax::AssocItemContainer::InherentImplContainer { .. } => return Ok(None),
            // E.g.:
            // ```
            // impl Foo for Bar {
            //   fn baz(...) { ... } // <- implementation of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitImplContainer {
                impl_,
                implemented_trait_ref,
                overrides_default,
                ..
            } => {
                let impl_ref =
                    self.translate_trait_impl_ref(span, impl_, TransImplSource::Normal)?;
                let trait_ref = self.translate_trait_ref(span, implemented_trait_ref)?;
                let item_id = self.translate_assoc_item_id(trait_ref.id, def.def_id())?;
                if matches!(def.kind(), hax::FullDefKind::AssocFn(_)) {
                    // If the implementation is getting translated, that means the method is
                    // getting used.
                    let method_id = *item_id.as_method().unwrap();
                    self.mark_method_as_used(trait_ref.id, method_id);
                }
                TraitItemSource::Impl {
                    impl_ref,
                    trait_ref,
                    item_id,
                    reuses_default: !overrides_default,
                }
            }
            // This method is the *declaration* of a trait item
            // E.g.:
            // ```
            // trait Foo {
            //   fn baz(...); // <- declaration of a trait method
            // }
            // ```
            hax::AssocItemContainer::TraitContainer { trait_ref, .. } => {
                // The trait id should be Some(...): trait markers (that we may eliminate)
                // don't have associated items.
                let trait_ref = self.translate_trait_ref(span, trait_ref)?;
                let item_id = self.translate_assoc_item_id(trait_ref.id, def.def_id())?;
                if matches!(def.kind(), hax::FullDefKind::AssocFn(_)) {
                    // If the method fundecl is getting translated, that means the method is
                    // getting used.
                    let method_id = *item_id.as_method().unwrap();
                    self.mark_method_as_used(trait_ref.id, method_id);
                }
                debug_assert!(assoc.has_value);
                TraitItemSource::Default { trait_ref, item_id }
            }
        }))
    }

    /// Translate a type definition.
    ///
    /// Note that we translate the types one by one: we don't need to take into
    /// account the fact that some types are mutually recursive at this point
    /// (we will need to take that into account when generating the code in a file).
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_type_decl(
        mut self,
        trans_id: TypeDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TypeDecl, Error> {
        let span = item_meta.span;

        // Get the kind of the type decl.
        let src = if let hax::FullDefKind::Closure(c) = def.kind() {
            let info = self.translate_closure_info(span, c.args())?;
            TypeSource::Closure { info }
        } else if let Some(builtin) = self.recognize_builtin_adt(def.this()) {
            TypeSource::Builtin(builtin)
        } else {
            TypeSource::Normal
        };

        // Translate type body
        let kind = match &def.kind {
            _ if item_meta.opacity.is_opaque() => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::OpaqueTy | hax::FullDefKind::ForeignTy => Ok(TypeDeclKind::Opaque),
            hax::FullDefKind::TyAlias(a) => {
                // Don't error on missing trait refs.
                self.error_on_trait_proof_error = false;
                self.translate_ty(span, a.ty()).map(TypeDeclKind::Alias)
            }
            hax::FullDefKind::Adt(_) => self.translate_adt_def(trans_id, span, &item_meta, def),
            hax::FullDefKind::Closure(c) => self.translate_closure_adt(span, c.args()),
            _ => panic!("Unexpected item when translating types: {def:?}"),
        };

        let kind = match kind {
            Ok(kind) => kind,
            Err(err) => TypeDeclKind::Error(err.msg),
        };
        let layout = self
            .translate_layout(span, def, &kind)
            .into_iter()
            .map(|l| (self.get_target_triple(), l))
            .collect();
        let ptr_metadata = self.translate_ptr_metadata(span, def.this())?;
        Ok(TypeDecl {
            def_id: trans_id,
            item_meta,
            generics: self.into_generics(),
            kind,
            src,
            layout,
            ptr_metadata,
        })
    }

    /// Translate one function.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_fun_decl(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;

        let src = if matches!(
            def.kind(),
            hax::FullDefKind::Const(_)
                | hax::FullDefKind::AssocConst(_)
                | hax::FullDefKind::Static(_)
        ) {
            let global_id = self.register_item(span, def.this(), TransItemSourceKind::Global);
            FunSource::GlobalInitializer(GlobalDeclRef {
                id: global_id,
                generics: Box::new(self.outermost_generics().identity_args()),
            })
        } else if matches!(def.kind(), hax::FullDefKind::Ctor(_)) {
            FunSource::AdtConstructor
        } else {
            match self.get_trait_item_source(span, def)? {
                None => FunSource::Normal,
                Some(TraitItemSource::Default { trait_ref, item_id }) => FunSource::TraitDefault {
                    trait_ref,
                    item_id: *item_id.as_method().unwrap(),
                },
                Some(TraitItemSource::Impl {
                    impl_ref,
                    trait_ref,
                    item_id,
                    reuses_default,
                }) => FunSource::TraitImpl {
                    impl_ref,
                    trait_ref,
                    item_id: *item_id.as_method().unwrap(),
                    reuses_default,
                },
            }
        };

        if let hax::FullDefKind::Ctor(ctor) = def.kind() {
            let signature = FunSig {
                inputs: ctor
                    .fields()
                    .iter()
                    .map(|field| self.translate_ty(span, &field.ty))
                    .try_collect()?,
                output: self.translate_ty(span, ctor.output_ty())?,
                is_unsafe: false,
                abi: Abi::rust(),
                is_variadic: false,
            };

            let body = if item_meta.opacity.with_private_contents().is_opaque() {
                Body::Opaque
            } else {
                self.build_ctor_body(span, def)?
            };
            return Ok(FunDecl {
                def_id,
                item_meta,
                generics: self.into_generics(),
                signature: Box::new(signature),
                src,
                body,
            });
        }

        // Translate the function signature
        trace!("Translating function signature");
        let signature = match &def.kind {
            hax::FullDefKind::Fn(f) => self.translate_fun_sig(span, &f.sig().value)?,
            hax::FullDefKind::AssocFn(f) => self.translate_fun_sig(span, &f.sig().value)?,
            hax::FullDefKind::Const(_)
            | hax::FullDefKind::AssocConst(_)
            | hax::FullDefKind::Static(_) => {
                let ty = match &def.kind {
                    hax::FullDefKind::Const(c) => c.ty(),
                    hax::FullDefKind::AssocConst(c) => c.ty(),
                    hax::FullDefKind::Static(s) => s.ty(),
                    _ => unreachable!(),
                };
                FunSig {
                    inputs: vec![],
                    output: self.translate_ty(span, ty)?,
                    is_unsafe: false,
                    abi: Abi::rust(),
                    is_variadic: false,
                }
            }
            _ => panic!("Unexpected definition for function: {def:?}"),
        };

        let intrinsic_name = def
            .def_id()
            .as_real_def_id()
            .and_then(|id| self.tcx.intrinsic(id))
            .map(|i| i.name.to_ident_string());

        let body = if intrinsic_name.as_deref() == Some("type_id") {
            self.build_type_id_body(span, def, &signature)?
        } else if let Some(name) = intrinsic_name {
            let arg_names = self.translate_argument_names(span, def, signature.inputs.len());
            Body::Intrinsic { name, arg_names }
        } else if let Some(name) = self.t_ctx.extern_item_symbol_name(def) {
            Body::Extern(name)
        } else if item_meta.diagnostic_item.as_deref()
            == Some(names::BOX_ASSUME_INIT_INTO_VEC_UNSAFE)
            && self.options.treat_box_as_builtin
        {
            // FIXME(#865): the MIR we get is unusably optimized. Instead we build our own body
            // here.
            self.build_box_assume_init_into_vec_unsafe(span, def)?
        } else if item_meta.lang_item.as_ref() == Some(&from_rustc::LangItem::DropGlue) {
            self.build_drop_glue_body(span, def, &signature)?
        } else if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            // Translate the MIR body for this definition.
            self.translate_def_body(item_meta.span, def)
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src,
            body,
        })
    }

    /// Translate one global.
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_global(
        mut self,
        def_id: GlobalDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<GlobalDecl, Error> {
        let span = item_meta.span;

        // Retrieve the kind
        let item_source = match self.get_trait_item_source(span, def)? {
            None => GlobalSource::Normal,
            Some(TraitItemSource::Default { trait_ref, item_id }) => GlobalSource::TraitDefault {
                trait_ref,
                item_id: *item_id.as_const().unwrap(),
            },
            Some(TraitItemSource::Impl {
                impl_ref,
                trait_ref,
                item_id,
                reuses_default,
            }) => GlobalSource::TraitImpl {
                impl_ref,
                trait_ref,
                item_id: *item_id.as_const().unwrap(),
                reuses_default,
            },
        };

        trace!("Translating global type");
        let ty = match &def.kind {
            hax::FullDefKind::Const(c) => c.ty(),
            hax::FullDefKind::AssocConst(c) => c.ty(),
            hax::FullDefKind::Static(s) => s.ty(),
            _ => panic!("Unexpected def for constant: {def:?}"),
        };
        let ty = self.translate_ty(span, ty)?;

        let (size, align) = if let hax::DefIdBase::Alloc(alloc_id) = def.def_id().base {
            let tcx = self.t_ctx.tcx;
            let alloc = tcx.global_alloc(alloc_id).unwrap_memory().inner();
            (
                Size::new(alloc.size().bytes()),
                Size::new(alloc.align.bytes()),
            )
        } else {
            (
                Size::from_expr(SizeExpr::size_of(&ty)),
                Size::from_expr(SizeExpr::align_of(&ty)),
            )
        };

        let global_kind = match &def.kind {
            hax::FullDefKind::Static(s) if s.thread_local() => GlobalKind::ThreadLocal,
            hax::FullDefKind::Static(_) => GlobalKind::Static,
            hax::FullDefKind::Const(c) if matches!(c.kind(), hax::ConstKind::TopLevel) => {
                GlobalKind::NamedConst
            }
            hax::FullDefKind::AssocConst(_) => GlobalKind::NamedConst,
            hax::FullDefKind::Const(_) => GlobalKind::AnonConst,
            _ => panic!("Unexpected def for constant: {def:?}"),
        };

        // With `--consts=values`, try to evaluate the constant/static into a value. This
        // isn't always possible (e.g. for generic constants or recursive statics), in which
        // case we fall back to a call to the initializer below. Globals that stand for an
        // anonymous allocation have no initializer, so they are always evaluated.
        let is_anon_alloc = matches!(def.def_id().base, hax::DefIdBase::Alloc(..));
        let value = if (matches!(self.options.consts, ConstHandling::Values) || is_anon_alloc)
            && let Some(evaluated) = self.evaluate_const_def(def)
        {
            self.translate_constant_expr(span, &evaluated)?
        } else {
            // Default: the value is a call to the initializer function, which uses the same
            // generic parameters as the global.
            let initializer = self.register_item(span, def.this(), TransItemSourceKind::Fun);
            ConstantExpr::new(
                ConstantExprKind::Call(
                    FnPtr::new(
                        FnPtrKind::Fun(initializer),
                        self.outermost_generics().identity_args(),
                    ),
                    vec![],
                ),
                ty.clone(),
            )
        };

        Ok(GlobalDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            ty,
            size,
            align,
            src: item_source,
            global_kind,
            value,
        })
    }

    // either Poly or MonoTrait
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_trait_decl(
        mut self,
        trait_decl_id: TraitDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TraitDecl, Error> {
        let span = item_meta.span;

        let implied_predicates = match def.kind() {
            hax::FullDefKind::Trait(t) => t.implied_predicates(),
            hax::FullDefKind::TraitAlias(t) => t.implied_predicates(),
            _ => raise_error!(self, span, "Unexpected definition: {def:?}"),
        };
        let src = match def.kind() {
            hax::FullDefKind::Trait(_) => TraitDeclSource::Normal,
            hax::FullDefKind::TraitAlias(_) => TraitDeclSource::TraitAlias,
            _ => unreachable!(),
        };

        // Register implied predicates. We gather the clauses and consider the other predicates as
        // required since the distinction doesn't matter for non-trait-clauses.
        let mut implied_clauses = Default::default();
        self.translate_predicates(
            implied_predicates,
            PredicateOrigin::WhereClauseOnTrait,
            Some(&mut implied_clauses),
        )?;

        let vtable = self.translate_vtable_struct_ref_no_enqueue(span, def.this())?;

        if let hax::FullDefKind::TraitAlias(_) = def.kind() {
            // Trait aliases don't have any items. Everything interesting is in the parent clauses.
            return Ok(TraitDecl {
                def_id: trait_decl_id,
                item_meta,
                src,
                implied_clauses,
                generics: self.into_generics(),
                consts: Default::default(),
                types: Default::default(),
                methods: Default::default(),
                vtable,
            });
        }

        let hax::FullDefKind::Trait(t) = &def.kind else {
            unreachable!()
        };
        let self_trait_ref = TraitRef::new(
            TraitRefKind::SelfId,
            RegionBinder::empty(self.translate_trait_predicate(span, t.self_predicate())?),
        );

        // Translate the associated items
        self.register_assoc_items(def.def_id(), trait_decl_id)?;
        let mut consts: IndexMap<AssocConstId, _> = IndexMap::new();
        let mut types: IndexMap<AssocTypeId, _> = IndexMap::new();
        let mut methods: IndexMap<TraitMethodId, _> = IndexMap::new();

        if def.lang_item == Some(sym::destruct) {
            // Add a `drop_in_place(*mut self)` method that contains the drop glue for this type.
            let destruct_trait_def_id = def.def_id();
            let method_id =
                self.translate_drop_glue_method_id(destruct_trait_def_id, trait_decl_id)?;
            self.mark_method_as_used(trait_decl_id, method_id);
            let method = {
                let method_name = self.translated.assoc_item_name(trait_decl_id, method_id);
                let mut method_item_meta = ItemMeta::dummy_public(
                    span,
                    item_meta.name.clone(),
                    item_meta.is_local,
                    item_meta.opacity,
                );
                method_item_meta.name.name.push(PathElem::Ident(
                    method_name.to_string(),
                    Disambiguator::ZERO,
                ));
                let self_ty = if self.monomorphize() {
                    // FIXME: put something real here
                    Ty::mk_unit()
                } else {
                    TyKind::TypeVar(DeBruijnVar::bound(DeBruijnId::one(), TypeVarId::ZERO))
                        .into_ty()
                };
                let signature = self.drop_glue_method_sig(
                    self_ty,
                    Region::Var(DeBruijnVar::new_at_zero(RegionId::ZERO)),
                );
                let method_params = Self::drop_glue_params();
                Binder::new(
                    BinderKind::TraitMethod(trait_decl_id, method_id),
                    method_params,
                    TraitMethod {
                        name: method_name,
                        default: None,
                        item_meta: method_item_meta,
                        signature,
                    },
                )
            };
            methods.set_slot_extend(method_id, method);
        }

        // skip all associated items of trait decl in mono mode
        // question: what if the associated methods (or consts) has default implmentation?
        // TODO: support default methods and default consts
        if self.monomorphize() {
            return Ok(TraitDecl {
                def_id: trait_decl_id,
                item_meta,
                src,
                implied_clauses,
                generics: self.into_generics(),
                consts,
                types,
                methods,
                vtable,
            });
        }

        for hax_item in t.items(self.hax_state()) {
            let item_def_id = &hax_item.def_id;
            let item_span = self.def_span(item_def_id);
            let assoc_item_id = self.translate_assoc_item_id(trait_decl_id, item_def_id)?;
            let item_name = self
                .translated
                .assoc_item_name(trait_decl_id, assoc_item_id);

            // In --mono mode, we keep only non-polymorphic items; in not-mono mode, we use the
            // polymorphic item as usual.
            let trans_kind = match hax_item.kind {
                hax::AssocKind::Fn { .. } => TransItemSourceKind::Fun,
                hax::AssocKind::Const { .. } => TransItemSourceKind::Global,
                hax::AssocKind::Type { .. } => TransItemSourceKind::Type,
            };

            let item_def = self.poly_hax_def(item_def_id)?;
            let item_src = TransItemSource::polymorphic(item_def_id, trans_kind);
            let attr_info = self.translate_attr_info(&item_def);

            match item_def.kind() {
                hax::FullDefKind::AssocFn(f) => {
                    let trait_method_id = *assoc_item_id.as_method().unwrap();
                    let method_name = self.translate_name(&item_src)?;
                    let method_opacity = self.opacity_for_name(&method_name);
                    let method_item_meta =
                        self.translate_item_meta(&item_def, &item_src, method_name, method_opacity);
                    // By default we only enqueue required methods (those that don't have a default
                    // impl). If the trait is transparent, we enqueue all its methods.
                    if self.options.translate_all_methods
                        || item_meta.opacity.is_transparent()
                        || !hax_item.has_value
                    {
                        self.mark_method_as_used(trait_decl_id, trait_method_id);
                    }
                    let default_fun_id = f.associated_item().has_value.then(|| {
                        let fun_id = self.register_no_enqueue(item_span, &item_src);
                        // Register this method.
                        self.register_method_impl(trait_decl_id, trait_method_id, fun_id);
                        fun_id
                    });

                    let binder_kind = BinderKind::TraitMethod(trait_decl_id, trait_method_id);
                    let mut method = self.translate_binder_for_def(
                        item_span,
                        binder_kind,
                        &item_def,
                        |bt_ctx| {
                            assert_eq!(bt_ctx.binding_levels.len(), 2);
                            let default = default_fun_id.map(|id| {
                                let fun_generics = bt_ctx
                                    .outermost_binder()
                                    .params
                                    .identity_args_at_depth(DeBruijnId::one())
                                    .concat(
                                        &bt_ctx
                                            .innermost_binder()
                                            .params
                                            .identity_args_at_depth(DeBruijnId::zero()),
                                    );
                                FunDeclRef {
                                    id,
                                    generics: Box::new(fun_generics),
                                }
                            });
                            // `skip_binder` is allowed because `translate_binder_for_def` puts the
                            // late bound params in scope.
                            let signature =
                                bt_ctx.translate_fun_sig(span, f.sig().hax_skip_binder_ref())?;
                            Ok(TraitMethod {
                                name: item_name,
                                item_meta: method_item_meta,
                                signature,
                                default,
                            })
                        },
                    )?;
                    // In hax, associated items take an extra explicit `Self: Trait` clause, but we
                    // don't want that to be part of the method clauses. Hence we remove the first
                    // bound clause and replace its uses with references to the ambient `Self`
                    // clause available in trait declarations.
                    struct ReplaceSelfVisitor;
                    impl VarsVisitor for ReplaceSelfVisitor {
                        fn visit_clause_var(&mut self, v: ClauseDbVar) -> Option<TraitRefKind> {
                            if let DeBruijnVar::Bound(DeBruijnId::ZERO, clause_id) = v {
                                // Replace clause 0 and decrement the others.
                                Some(if let Some(new_id) = clause_id.index().checked_sub(1) {
                                    TraitRefKind::Clause(DeBruijnVar::Bound(
                                        DeBruijnId::ZERO,
                                        TraitClauseId::new(new_id),
                                    ))
                                } else {
                                    TraitRefKind::SelfId
                                })
                            } else {
                                None
                            }
                        }
                    }
                    method.params.visit_vars(&mut ReplaceSelfVisitor);
                    method.skip_binder.visit_vars(&mut ReplaceSelfVisitor);
                    method
                        .params
                        .trait_clauses
                        .remove_and_shift_ids(TraitClauseId::ZERO);
                    method.params.trait_clauses.iter_mut().for_each(|clause| {
                        clause.clause_id -= 1;
                    });

                    // We insert the `Binder<TraitMethod>` unconditionally here; we'll remove the
                    // ones that correspond to unused methods at the end of translation.
                    methods.set_slot_extend(trait_method_id, method);
                }
                hax::FullDefKind::AssocConst(c) => {
                    let assoc_const_id = *assoc_item_id.as_const().unwrap();
                    // The const is defined in a context that has an extra `Self: Trait` clause, so
                    // we translate it bound first.
                    let bound_assoc_const = self.translate_binder_for_def(
                        item_span,
                        BinderKind::Other,
                        &item_def,
                        |ctx| {
                            // Check if the constant has a value (i.e., a body).
                            let default = hax_item.has_value.then(|| {
                                // The parameters of the constant are the same as those of the item that
                                // declares them.
                                let id = ctx.register_and_enqueue(item_span, item_src);
                                let generics = ctx
                                    .outermost_binder()
                                    .params
                                    .identity_args_at_depth(DeBruijnId::one())
                                    .concat(
                                        &ctx.innermost_binder()
                                            .params
                                            .identity_args_at_depth(DeBruijnId::zero()),
                                    );
                                GlobalDeclRef {
                                    id,
                                    generics: Box::new(generics),
                                }
                            });
                            let ty = ctx.translate_ty(item_span, c.ty())?;
                            Ok(TraitAssocConst {
                                name: item_name,
                                attr_info,
                                ty,
                                default,
                            })
                        },
                    )?;
                    let assoc_const = bound_assoc_const.apply(&{
                        let mut generics = GenericArgs::empty();
                        // Provide the `Self` clause.
                        generics.trait_refs.push(self_trait_ref.clone());
                        generics
                    });
                    consts.set_slot_extend(assoc_const_id, assoc_const);
                }
                hax::FullDefKind::AssocTy(assoc_ty_def) => {
                    let assoc_type_id = *assoc_item_id.as_type().unwrap();
                    let binder_kind = BinderKind::TraitType(trait_decl_id, assoc_type_id);
                    let assoc_ty =
                        self.translate_binder_for_def(item_span, binder_kind, &item_def, |ctx| {
                            // Also add the implied predicates.
                            let mut implied_clauses = Default::default();
                            ctx.translate_predicates(
                                assoc_ty_def.implied_predicates(),
                                PredicateOrigin::TraitItem(assoc_type_id),
                                Some(&mut implied_clauses),
                            )?;

                            let default = assoc_ty_def
                                .value(ctx.hax_state())
                                .map(|(ty, trait_proofs)| -> Result<_, Error> {
                                    let ty = ctx.translate_ty(item_span, &ty)?;
                                    let trefs = ctx.translate_trait_proofs(span, &trait_proofs)?;
                                    Ok(TraitAssocTyImpl {
                                        value: ty,
                                        implied_trait_refs: trefs,
                                    })
                                })
                                .transpose()?;
                            Ok(TraitAssocTy {
                                name: item_name,
                                attr_info,
                                default,
                                implied_clauses,
                            })
                        })?;
                    types.set_slot_extend(assoc_type_id, assoc_ty);
                }
                _ => panic!("Unexpected definition for trait item: {item_def:?}"),
            }
        }

        // In case of a trait implementation, some values may not have been
        // provided, in case the declaration provided default values. We
        // check those, and lookup the relevant values.
        Ok(TraitDecl {
            def_id: trait_decl_id,
            item_meta,
            src,
            implied_clauses,
            generics: self.into_generics(),
            consts,
            types,
            methods,
            vtable,
        })
    }

    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        let hax::FullDefKind::TraitImpl(timpl) = &def.kind else {
            unreachable!()
        };

        // Retrieve the information about the implemented trait.
        let trait_pred = timpl.trait_pred();
        let implemented_trait = self.translate_trait_ref(span, &trait_pred.trait_ref)?;
        let trait_id = implemented_trait.id;

        // Translate the bare minimum needed for names: `impl_trait`.
        if self.is_poly_in_mono(&self.item_src) {
            return Ok(TraitImpl {
                def_id,
                item_meta,
                src: TraitImplSource::Normal,
                impl_trait: implemented_trait,
                generics: self.into_generics(),
                implied_trait_refs: Default::default(),
                consts: Default::default(),
                types: Default::default(),
                methods: Default::default(),
                vtable: VTableDecl::Unknown("polymorphic impl in monomorphic mode".into()),
            });
        }

        // A `TraitRef` that points to this impl with the correct generics.
        let self_predicate = TraitRef::new(
            TraitRefKind::TraitImpl(TraitImplRef {
                id: def_id,
                generics: Box::new(self.the_only_binder().params.identity_args()),
            }),
            RegionBinder::empty(implemented_trait.clone()),
        );

        let vtable = self.translate_trait_impl_vtable(
            span,
            &trait_pred.trait_ref,
            def.this(),
            TransImplSource::Normal,
        )?;

        // The trait refs which implement the parent clauses of the implemented trait decl.
        let implied_trait_refs = self.translate_trait_proofs(span, timpl.implied_trait_proofs())?;

        {
            // Debugging
            let ctx = self.into_fmt();
            let refs = implied_trait_refs
                .iter()
                .map(|c| c.with_ctx(&ctx))
                .format("\n");
            trace!(
                "Trait impl: {:?}\n- implied_trait_refs:\n{}",
                def.def_id(),
                refs
            );
        }

        let implemented_trait_def = self.poly_hax_def(&trait_pred.trait_ref.def_id)?;
        if implemented_trait_def.lang_item == Some(sym::destruct) {
            raise_error!(
                self,
                span,
                "found an explicit impl of `core::marker::Destruct`, this should not happen"
            );
        }

        // Explore the associated items
        let mut consts: IndexMap<AssocConstId, _> = IndexMap::new();
        let mut types: IndexMap<AssocTypeId, _> = IndexMap::new();
        let mut methods: IndexMap<TraitMethodId, _> = IndexMap::new();

        // In mono mode, we do not translate any associated items in trait impl.
        if self.monomorphize() {
            return Ok(TraitImpl {
                def_id,
                item_meta,
                src: TraitImplSource::Normal,
                impl_trait: implemented_trait,
                generics: self.into_generics(),
                implied_trait_refs,
                consts,
                types,
                methods,
                vtable,
            });
        }

        for impl_item in timpl.items(self.hax_state()) {
            let item_def_id = impl_item.def_id().unwrap_or(impl_item.decl_def_id());
            let item_span = self.def_span(item_def_id);
            let assoc_item_id = self.translate_assoc_item_id(trait_id, item_def_id)?;

            // In not-mono mode, we use the polymorphic item as usual.
            let trans_kind = match item_def_id.kind {
                hax::DefKind::AssocFn => TransItemSourceKind::Fun,
                hax::DefKind::AssocConst => TransItemSourceKind::Global,
                hax::DefKind::AssocTy => TransItemSourceKind::Type,
                _ => unreachable!(),
            };
            let item_src = TransItemSource::polymorphic(item_def_id, trans_kind);

            match item_def_id.kind {
                hax::DefKind::AssocFn => {
                    let trait_method_id = *assoc_item_id.as_method().unwrap();
                    let binder_kind = BinderKind::TraitMethod(trait_id, trait_method_id);
                    let bound_fn_ref = match &impl_item.value {
                        Some(value) => {
                            // By default we only enqueue required methods (those that don't have a default
                            // impl). If the impl is transparent, we enqueue all the implemented methods.
                            if item_meta.opacity.is_transparent() {
                                self.mark_method_as_used(trait_id, trait_method_id);
                            }
                            self.translate_item_binder(
                                item_span,
                                binder_kind,
                                value,
                                PredicateOrigin::WhereClauseOnFn,
                                |ctx, value| {
                                    let bound_fn_ptr = ctx.translate_bound_fn_ptr_no_enqueue(
                                        item_span,
                                        &value.item,
                                        TransItemSourceKind::Fun,
                                    )?;
                                    // FIXME(#513): the regions may not match.
                                    let late_bound_regions = ctx
                                        .innermost_binder()
                                        .bound_region_vars
                                        .iter()
                                        .map(|rid| Region::Var(DeBruijnVar::new_at_zero(*rid)))
                                        .collect();
                                    let fn_ptr = bound_fn_ptr.apply(late_bound_regions);
                                    Ok(FunDeclRef {
                                        id: *fn_ptr.kind.as_fun().unwrap(),
                                        generics: fn_ptr.generics,
                                    })
                                },
                            )?
                        }
                        None => {
                            // Reuse the default method from the trait declaration.
                            let bound_method = match self.get_or_translate(trait_id.into()) {
                                Ok(ItemRef::TraitDecl(tdecl)) => {
                                    tdecl.methods.get(trait_method_id).cloned()
                                }
                                _ => None,
                            };
                            let Some(bound_method) = bound_method else {
                                continue;
                            };
                            bound_method
                                .substitute_with_tref(&self_predicate)
                                .map(|method| {
                                    method
                                        .default
                                        .expect("default method should have a default")
                                })
                        }
                    };

                    // Register this method.
                    self.register_method_impl(
                        trait_id,
                        trait_method_id,
                        bound_fn_ref.skip_binder.id,
                    );

                    // We insert the `Binder<FunDeclRef>` unconditionally here; we'll remove the
                    // ones that correspond to unused methods at the end of translation.
                    methods.set_slot_extend(trait_method_id, bound_fn_ref);
                }
                hax::DefKind::AssocConst => {
                    let assoc_const_id = *assoc_item_id.as_const().unwrap();
                    let id = self.register_and_enqueue(item_span, item_src);
                    // The parameters of the constant are the same as those of the item that
                    // declares them.
                    let generics = match &impl_item.value {
                        Some(_) => self.the_only_binder().params.identity_args(),
                        None => {
                            let mut generics = implemented_trait.generics.as_ref().clone();
                            // For default consts, we add an extra `Self` predicate.
                            generics.trait_refs.push(self_predicate.clone());
                            generics
                        }
                    };
                    let gref = GlobalDeclRef {
                        id,
                        generics: Box::new(generics),
                    };
                    consts.set_slot_extend(assoc_const_id, gref);
                }
                hax::DefKind::AssocTy => {
                    let assoc_type_id = *assoc_item_id.as_type().unwrap();
                    let binder_kind = BinderKind::TraitType(trait_id, assoc_type_id);
                    let assoc_ty = match &impl_item.value {
                        Some(impl_value) => self.translate_item_binder(
                            item_span,
                            binder_kind,
                            impl_value,
                            PredicateOrigin::WhereClauseOnType,
                            |ctx, impl_value| {
                                let ty = ctx.translate_ty(
                                    item_span,
                                    impl_value.assoc_ty_value.as_ref().unwrap(),
                                )?;
                                let implied_trait_refs = ctx.translate_trait_proofs(
                                    item_span,
                                    &impl_value.implied_trait_proofs,
                                )?;
                                Ok(TraitAssocTyImpl {
                                    value: ty,
                                    implied_trait_refs,
                                })
                            },
                        )?,
                        None => {
                            // Retrieve the type from the trait decl.
                            let trait_id = implemented_trait.id;
                            let bound_ty = match self.get_or_translate(trait_id.into()) {
                                Ok(ItemRef::TraitDecl(tdecl)) => tdecl.types.get(assoc_type_id),
                                _ => None,
                            };
                            let Some(bound_ty) = bound_ty else {
                                register_error!(
                                    self,
                                    item_span,
                                    "couldn't translate defaulted associated type; \
                                    either the corresponding trait decl caused errors \
                                    or it was declared opaque."
                                );
                                continue;
                            };
                            bound_ty
                                .clone()
                                .substitute_with_tref(&self_predicate)
                                .map(|ty_decl: TraitAssocTy| ty_decl.default.unwrap())
                        }
                    };

                    types.set_slot_extend(assoc_type_id, assoc_ty);
                }
                _ => panic!("Unexpected definition for trait item: {item_def_id:?}"),
            }
        }

        Ok(TraitImpl {
            def_id,
            item_meta,
            src: TraitImplSource::Normal,
            impl_trait: implemented_trait,
            generics: self.into_generics(),
            implied_trait_refs,
            consts,
            types,
            methods,
            vtable,
        })
    }

    /// Generate a blanket impl for this trait, as in:
    /// ```
    ///     trait Alias<U> = Trait<Option<U>, Item = u32> + Clone;
    /// ```
    /// becomes:
    /// ```
    ///     trait Alias<U>: Trait<Option<U>, Item = u32> + Clone {}
    ///     impl<U, Self: Trait<Option<U>, Item = u32> + Clone> Alias<U> for Self {}
    /// ```
    #[tracing::instrument(skip(self, item_meta, def))]
    pub fn translate_trait_alias_blanket_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;

        let hax::FullDefKind::TraitAlias(t) = &def.kind else {
            raise_error!(self, span, "Unexpected definition: {def:?}");
        };

        // Retrieve the information about the implemented trait.
        let implemented_trait = self.translate_trait_ref(span, &t.self_predicate().trait_ref)?;

        // Register the trait implied clauses as required clauses for the impl.
        assert!(self.innermost_generics_mut().trait_clauses.is_empty());
        self.register_predicates(t.implied_predicates(), PredicateOrigin::WhereClauseOnTrait)?;

        let mut generics = self.the_only_binder().params.identity_args();
        // Do the inverse operation: the trait considers the clauses as implied.
        let implied_trait_refs = mem::take(&mut generics.trait_refs);

        let mut timpl = TraitImpl {
            def_id,
            item_meta,
            src: TraitImplSource::TraitAlias,
            impl_trait: implemented_trait,
            generics: self.the_only_binder().params.clone(),
            implied_trait_refs,
            consts: Default::default(),
            types: Default::default(),
            methods: Default::default(),
            // TODO(dyn)
            vtable: VTableDecl::Unknown("vtables of trait alias impls are not supported".into()),
        };
        // We got the predicates from a trait decl, so they may refer to the virtual `Self`
        // clause, which doesn't exist for impls. We fix that up here.
        {
            struct FixSelfVisitor {
                binder_depth: DeBruijnId,
            }
            struct UnhandledSelf;
            impl Visitor for FixSelfVisitor {
                type Break = UnhandledSelf;
            }
            impl VisitorWithBinderDepth for FixSelfVisitor {
                fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
                    &mut self.binder_depth
                }
            }
            impl VisitAstMut for FixSelfVisitor {
                fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
                    VisitWithBinderDepth::new(self).visit(x)
                }
                fn visit_trait_ref_kind(
                    &mut self,
                    kind: &mut TraitRefKind,
                ) -> ControlFlow<Self::Break> {
                    match kind {
                        TraitRefKind::SelfId => return ControlFlow::Break(UnhandledSelf),
                        TraitRefKind::ParentClause(sub, clause_id)
                            if matches!(sub.kind, TraitRefKind::SelfId) =>
                        {
                            *kind = TraitRefKind::Clause(DeBruijnVar::bound(
                                self.binder_depth,
                                *clause_id,
                            ))
                        }
                        _ => (),
                    }
                    self.visit_inner(kind)
                }
            }
            match timpl.drive_mut(&mut FixSelfVisitor {
                binder_depth: DeBruijnId::zero(),
            }) {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(UnhandledSelf) => {
                    register_error!(
                        self,
                        span,
                        "Found `Self` clause we can't handle \
                         in a trait alias blanket impl."
                    );
                }
            }
        };

        Ok(timpl)
    }

    /// Make a trait impl from a hax `VirtualTraitImpl`. Used for constructing fake trait impls for
    /// builtin types like `FnOnce`.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_virtual_trait_impl(
        &mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        vtable_item: &hax::ItemRef,
        impl_kind: TransImplSource,
        vimpl: &hax::VirtualTraitImpl<'tcx>,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let src = match impl_kind {
            TransImplSource::Callable(kind) => TraitImplSource::Closure { kind },
            TransImplSource::ImplicitDestruct => TraitImplSource::Destruct,
            _ => unreachable!("not a virtual impl source: {impl_kind:?}"),
        };

        let implemented_trait = self.translate_trait_predicate(span, &vimpl.trait_pred)?;
        let implied_trait_refs = self.translate_trait_proofs(span, &vimpl.implied_trait_proofs)?;
        let vtable = self.translate_trait_impl_vtable(
            span,
            &vimpl.trait_pred.trait_ref,
            vtable_item,
            impl_kind,
        )?;

        let mut types: IndexMap<AssocTypeId, _> = IndexMap::new();
        // Monomorphic traits have no associated types.
        if !self.monomorphize() {
            let trait_def = self.poly_hax_def(&vimpl.trait_pred.trait_ref.def_id)?;
            let hax::FullDefKind::Trait(t) = trait_def.kind() else {
                panic!()
            };
            let trait_items = t.items(self.hax_state());
            let type_items = trait_items
                .iter()
                .filter(|assoc| matches!(assoc.kind, hax::AssocKind::Type { .. }));
            for ((ty, trait_proofs), assoc) in vimpl.types.iter().zip(type_items) {
                let assoc_type_id =
                    self.translate_assoc_type_id(implemented_trait.id, &assoc.def_id)?;
                let assoc_ty = TraitAssocTyImpl {
                    value: self.translate_ty(span, ty)?,
                    implied_trait_refs: self.translate_trait_proofs(span, trait_proofs)?,
                };
                let binder_kind = BinderKind::TraitType(implemented_trait.id, assoc_type_id);
                types.set_slot_extend(assoc_type_id, Binder::empty(binder_kind, assoc_ty));
            }
        }

        let generics = self.the_only_binder().params.clone();
        Ok(TraitImpl {
            def_id,
            item_meta,
            src,
            impl_trait: implemented_trait,
            generics,
            implied_trait_refs,
            consts: IndexMap::new(),
            types,
            methods: IndexMap::new(),
            vtable,
        })
    }
}
