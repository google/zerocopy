//! This file governs the overall translation of items.
//!
//! Translation works as follows: we translate each `TransItemSource` of interest into an
//! appropriate item. In the process of translating an item we may find more `hax::DefId`s of
//! interest; we register those as an appropriate `TransItemSource`, which will 1/ enqueue the item
//! so that it eventually gets translated too, and 2/ return an `ItemId` we can use to refer to
//! it.
//!
//! We start with the DefId of the current crate (or of anything passed to `--start-from`) and
//! recursively translate everything we find.
//!
//! There's another important component at play: opacity. Each item is assigned an opacity based on
//! its name. By default, items from the local crate are transparent and items from foreign crates
//! are opaque (this can be controlled with `--include`, `--opaque` and `--exclude`). If an item is
//! opaque, its signature/"outer shell" will be translated (e.g. for functions that's the
//! signature) but not its contents.
use itertools::Itertools;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{def_id::DefId, sym};
use std::cell::RefCell;
use std::collections::HashSet;
use std::path::PathBuf;

use super::translate_ctx::*;
use crate::hax;
use crate::hax::SInto;
use charon_lib::ast::*;
use charon_lib::name_matcher::NamePattern;
use charon_lib::options::{CliOpts, ConstHandling, StartFrom, TranslateOptions};
use charon_lib::transform::TransformCtx;
use macros::VariantIndexArity;

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TransItemSource {
    pub item: RustcItem,
    pub kind: TransItemSourceKind,
}

/// Refers to a rustc item. Can be either the polymorphic version (`Poly`) of the item, or a
/// monomorphization (`Mono` or `MonoTrait`) of it.
/// For `MonoTrait` items, their kind should be either `trait decl` or `struct vtable`:
///     1. the trait is translated as in poly mode, except that we don't translate any of its
///        associated item lists.
///     2. the vtable is translated with erased signature of the methods and without generic types.
///        In other words, there is one "opaque" vtable per trait.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RustcItem {
    Poly(hax::DefId),
    Mono(hax::ItemRef),
    MonoTrait(hax::DefId),
}

/// The kind of a [`TransItemSource`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantIndexArity)]
pub enum TransItemSourceKind {
    Global,
    TraitDecl,
    TraitImpl(TransImplSource),
    Fun,
    Type,
    /// We don't translate these as proper items, but we translate them a bit in names.
    InherentImpl,
    /// We don't translate these as proper items, but we use them to explore the crate.
    Module,
    /// The `call_*` method of the generated `Fn*` impl for a closure or fn item.
    CallableMethod(ClosureKind),
    /// A cast of a stateless closure to a function pointer.
    ClosureAsFnCast,
    /// The `drop_glue` method of a `Destruct` impl. It contains the drop glue that calls
    /// `Drop::drop` for the type and then drops its fields. This is a method implementation (and
    /// the DefId is that of the ADT or closure for which to generate the drop glue).
    DropGlueMethod(TransImplSource),
    /// The virtual table struct definition for a trait. The `DefId` is that of the trait.
    VTable,
    /// The static vtable value for a specific impl.
    VTableInstance(TransImplSource),
    /// The initializer function of the `VTableInstance`.
    VTableInstanceInitializer(TransImplSource),
    /// Shim function to store a method in a vtable; give a method with `self: Ptr<Self>` argument,
    /// this takes a `Ptr<dyn Trait>` and forwards to the method. For a `Normal` impl the `DefId`
    /// refers to the method implementation; for a `Callable` one it refers to the closure or fn
    /// item, whose `call_*` method has no `DefId` of its own.
    VTableMethod(TransImplSource),
    /// The drop shim function to be used in the vtable as a field.
    VTableDropShim(TransImplSource),
}

/// The kind of a [`TransItemSourceKind::TraitImpl`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantIndexArity)]
pub enum TransImplSource {
    /// A user-written trait impl with a `DefId`.
    Normal,
    /// The blanket impl we generate for a trait alias. The `DefId` is that of the trait alias.
    TraitAlias,
    /// An impl of the appropriate `Fn*` trait for a closure or function item.
    Callable(ClosureKind),
    /// A fictitious `impl Destruct for T` that contains the drop glue code for the given ADT or
    /// closure. The `DefId` is that of the ADT or closure.
    ImplicitDestruct,
    /// A marker-trait implementation. The `DefId` is that of the trait.
    Marker,
}

impl TransItemSource {
    pub fn new(item: RustcItem, kind: TransItemSourceKind) -> Self {
        if let RustcItem::Mono(item) = &item {
            if item.has_non_lt_param {
                panic!("Item is not monomorphic: {item:?}")
            }
        } else if let RustcItem::MonoTrait(_) = &item
            && !kind.is_for_trait()
        {
            panic!("Item kind {kind:?} should not be translated as monomorphic_trait")
        }
        Self { item, kind }
    }

    /// Refers to the given item. Depending on `monomorphize`, this chooses between the monomorphic
    /// and polymorphic versions of the item.
    pub fn from_item(item: &hax::ItemRef, kind: TransItemSourceKind, monomorphize: bool) -> Self {
        if monomorphize {
            if kind.is_for_trait() {
                Self::monomorphic_trait(&item.def_id, kind)
            } else {
                Self::monomorphic(item, kind)
            }
        } else {
            Self::polymorphic(&item.def_id, kind)
        }
    }

    /// Refers to the polymorphic version of this item.
    pub fn polymorphic(def_id: &hax::DefId, kind: TransItemSourceKind) -> Self {
        Self::new(RustcItem::Poly(def_id.clone()), kind)
    }

    /// Refers to the monomorphic version of this item.
    pub fn monomorphic(item: &hax::ItemRef, kind: TransItemSourceKind) -> Self {
        Self::new(RustcItem::Mono(item.clone()), kind)
    }

    /// Refers to the monomorphic trait (or vtable).
    /// See the docs of `RustcItem::MonoTrait` for details.
    pub fn monomorphic_trait(def_id: &hax::DefId, kind: TransItemSourceKind) -> Self {
        Self::new(RustcItem::MonoTrait(def_id.clone()), kind)
    }

    pub fn def_id(&self) -> &hax::DefId {
        self.item.def_id()
    }

    /// Keep the same def_id but change the kind.
    pub(crate) fn with_kind(&self, kind: TransItemSourceKind) -> Self {
        let mut ret = self.clone();
        ret.kind = kind;
        ret
    }

    /// For virtual items that have a parent (typically a method impl), return this parent. Does
    /// not attempt to generally compute the parent of an item. Used to compute names.
    pub(crate) fn parent(&self) -> Option<Self> {
        let parent_kind = match self.kind {
            TransItemSourceKind::CallableMethod(kind)
            | TransItemSourceKind::VTableMethod(TransImplSource::Callable(kind)) => {
                TransItemSourceKind::TraitImpl(TransImplSource::Callable(kind))
            }
            TransItemSourceKind::DropGlueMethod(TransImplSource::Marker)
            | TransItemSourceKind::VTableInstance(TransImplSource::Marker)
            | TransItemSourceKind::VTableInstanceInitializer(TransImplSource::Marker)
            | TransItemSourceKind::VTableDropShim(TransImplSource::Marker) => {
                TransItemSourceKind::TraitDecl
            }
            TransItemSourceKind::DropGlueMethod(impl_kind)
            | TransItemSourceKind::VTableInstance(impl_kind)
            | TransItemSourceKind::VTableInstanceInitializer(impl_kind)
            | TransItemSourceKind::VTableDropShim(impl_kind) => {
                TransItemSourceKind::TraitImpl(impl_kind)
            }
            _ => return None,
        };
        Some(self.with_kind(parent_kind))
    }

    /// Whether this item is the "main" item for this def_id or not (e.g. Destruct impl/methods are not
    /// the main item).
    pub(crate) fn is_derived_item(&self) -> bool {
        self.kind.is_derived_item()
    }
}

impl TransItemSourceKind {
    fn is_derived_item(self) -> bool {
        use TransItemSourceKind::*;
        !matches!(
            self,
            Global
                | TraitDecl
                | TraitImpl(TransImplSource::Normal)
                | InherentImpl
                | Module
                | Fun
                | Type
        )
    }

    pub fn is_for_trait(&self) -> bool {
        matches!(
            self,
            TransItemSourceKind::TraitDecl | TransItemSourceKind::VTable
        )
    }
}

impl RustcItem {
    pub fn def_id(&self) -> &hax::DefId {
        match self {
            RustcItem::Poly(def_id) => def_id,
            RustcItem::Mono(item_ref) => &item_ref.def_id,
            RustcItem::MonoTrait(def_id) => def_id,
        }
    }
}

impl<'tcx> TranslateCtx<'tcx> {
    /// If this is a method declaration without a default, return the `DefId` of its parent trait.
    fn is_method_decl_without_default(&mut self, def_id: &hax::DefId) -> Option<hax::DefId> {
        if matches!(def_id.kind, hax::DefKind::AssocFn)
            && let def = self.poly_hax_def(def_id).ok()?
            && let hax::FullDefKind::AssocFn(f) = def.kind()
            && let associated_item = f.associated_item()
            && !associated_item.has_value
            && let hax::AssocItemContainer::TraitContainer { trait_ref } =
                &associated_item.container
        {
            Some(trait_ref.def_id.clone())
        } else {
            None
        }
    }

    /// Resolve a path to a list of matching `DefId`s.
    pub fn resolve_path(
        &self,
        span: Span,
        pat: &NamePattern,
        strict: bool,
    ) -> Result<Vec<rustc_span::def_id::DefId>, Error> {
        super::resolve_path::def_path_def_ids(&self.hax_state, pat, strict).map_err(|err| {
            register_error!(self, span, "failed to resolve item path `{pat}`: {err}")
        })
    }

    /// Resolve a path that is expected to name exactly one item.
    pub fn resolve_single_path(
        &self,
        span: Span,
        pat: &NamePattern,
    ) -> Result<rustc_span::def_id::DefId, Error> {
        self.resolve_path(span, pat, true)?
            .into_iter()
            .exactly_one()
            .map_err(|_| register_error!(self, span, "expected exactly one item for path `{pat}`"))
    }

    fn register_polymorphic_function(&mut self, def_id: DefId) -> FunDeclId {
        let def_id = def_id.sinto(&self.hax_state);
        let item = TransItemSource::polymorphic(&def_id, TransItemSourceKind::Fun);
        self.register_and_enqueue(&None, item).unwrap()
    }

    fn register_poly_function_by_path(&mut self, path: &str) -> Result<FunDeclId, Error> {
        let path = NamePattern::parse(path).unwrap();
        let def_id = self.resolve_single_path(Span::dummy(), &path)?;
        Ok(self.register_polymorphic_function(def_id))
    }

    /// Register the std functions needed for `builtins_to_function_calls`.
    fn register_builtin_functions(&mut self) -> Result<(), Error> {
        if self.options.ops_to_function_calls {
            self.register_poly_function_by_path("array::as_slice")?;
            self.register_poly_function_by_path("array::as_mut_slice")?;
            self.register_poly_function_by_path("core::array::repeat")?;
        }
        if self.options.index_to_function_calls {
            let tcx = self.tcx;
            for (trait_id, method_name) in [
                (tcx.lang_items().index_trait().unwrap(), sym::index),
                (tcx.lang_items().index_mut_trait().unwrap(), sym::index_mut),
            ] {
                let impls = tcx.all_impls(trait_id).filter(|&impl_id| {
                    matches!(
                        tcx.impl_trait_ref(impl_id).skip_binder().self_ty().kind(),
                        ty::Array(..) | ty::Slice(..)
                    )
                });
                for impl_id in impls {
                    let method_id = tcx
                        .associated_items(impl_id)
                        .in_definition_order()
                        .find(|item| item.name() == method_name)
                        .unwrap()
                        .def_id;
                    self.register_polymorphic_function(method_id);
                }
            }
            let trait_id = self.tcx.get_diagnostic_item(sym::SliceIndex).unwrap();
            let impls = self.tcx.all_impls(trait_id).filter(|&impl_id| {
                let trait_ref = tcx.impl_trait_ref(impl_id).skip_binder();
                trait_ref.args.type_at(1).is_slice()
                    && match trait_ref.self_ty().kind() {
                        ty::Uint(ty::UintTy::Usize) => true,
                        ty::Adt(def, args) => {
                            tcx.is_lang_item(def.did(), rustc_attr_ir::LangItem::Range)
                                && args.type_at(0) == tcx.types.usize
                        }
                        _ => false,
                    }
            });
            for impl_id in impls {
                let methods = tcx
                    .associated_items(impl_id)
                    .in_definition_order()
                    .filter(|item| item.name() == sym::index || item.name() == sym::index_mut)
                    .map(|item| item.def_id);
                for method_id in methods {
                    self.register_polymorphic_function(method_id);
                }
            }
        }
        Ok(())
    }

    /// Returns the default translation kind for the given `DefId`. Returns `None` for items that
    /// we don't translate. Errors on unexpected items.
    pub fn base_kind_for_item(&mut self, def_id: &hax::DefId) -> Option<TransItemSourceKind> {
        use crate::hax::DefKind::*;
        Some(match &def_id.kind {
            Enum | Struct | Union | TyAlias | ForeignTy => TransItemSourceKind::Type,
            Fn | AssocFn => TransItemSourceKind::Fun,
            Const | Static { .. } | AssocConst => TransItemSourceKind::Global,
            Trait | TraitAlias => TransItemSourceKind::TraitDecl,
            Impl { of_trait: true } => TransItemSourceKind::TraitImpl(TransImplSource::Normal),
            Impl { of_trait: false } => TransItemSourceKind::InherentImpl,
            Mod | ForeignMod => TransItemSourceKind::Module,

            // We skip these
            ExternCrate | FnPtr | GlobalAsm | Macro { .. } | Use => return None,
            // These can happen when doing `--start-from` on a foreign crate. We can skip them
            // because their parents will already have been registered.
            Ctor { .. } | Variant => return None,
            // We cannot encounter these since they're not top-level items.
            AnonConst
            | AssocTy
            | Closure
            | ConstParam
            | Field
            | PromotedConst
            | LifetimeParam
            | OpaqueTy
            | SyntheticCoroutineBody
            | TestBinderConstraints
            | TyParam => {
                let span = self.def_span(def_id);
                register_error!(
                    self,
                    span,
                    "Cannot register item `{def_id:?}` with kind `{:?}`",
                    def_id.kind
                );
                return None;
            }
        })
    }

    /// Add this item to the queue of items to translate. Each translated item will then
    /// recursively register the items it refers to. We call this on the crate root and end up
    /// exploring the whole crate.
    #[tracing::instrument(skip(self))]
    pub fn enqueue_module_item(&mut self, def_id: &hax::DefId, started_from: bool) {
        if started_from {
            self.started_from.insert(def_id.clone());
        }
        if let Some(trait_def_id) = self.is_method_decl_without_default(def_id) {
            // Don't translate the method itself as it doesn't correspond to an item, translate the
            // trait instead.
            self.enqueue_module_item(&trait_def_id, started_from);
            return;
        }
        let Some(kind) = self.base_kind_for_item(def_id) else {
            return;
        };
        let item_src = if self.options.monomorphize_with_hax {
            if let Ok(def) = self.poly_hax_def(def_id)
                && !def.has_any_generics()
            {
                // Monomorphize this item and the items it depends on.
                TransItemSource::monomorphic(def.this(), kind)
            } else {
                // Skip polymorphic items and items that cause errors.
                return;
            }
        } else {
            TransItemSource::polymorphic(def_id, kind)
        };
        let _: Option<ItemId> = self.register_and_enqueue(&None, item_src);
    }

    /// Whether this item is polymorphic, while we are in monomorphic mode.
    pub(crate) fn is_poly_in_mono(&self, item_src: &TransItemSource) -> bool {
        self.options.monomorphize_with_hax && matches!(item_src.item, RustcItem::Poly(..))
    }

    pub(crate) fn register_no_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        dep_src: &Option<DepSource>,
        src: &TransItemSource,
    ) -> Option<T> {
        let item_id = match self.id_map.get(src) {
            Some(tid) => *tid,
            None => {
                use TransItemSourceKind::*;
                let trans_id = match src.kind {
                    Type | VTable => ItemId::Type(self.translated.type_decls.reserve_slot()),
                    TraitDecl => ItemId::TraitDecl(self.translated.trait_decls.reserve_slot()),
                    TraitImpl(..) => ItemId::TraitImpl(self.translated.trait_impls.reserve_slot()),
                    Global | VTableInstance(..) => {
                        ItemId::Global(self.translated.global_decls.reserve_slot())
                    }
                    Fun
                    | CallableMethod(..)
                    | ClosureAsFnCast
                    | DropGlueMethod(..)
                    | VTableInstanceInitializer(..)
                    | VTableMethod(..)
                    | VTableDropShim(..) => ItemId::Fun(self.translated.fun_decls.reserve_slot()),
                    InherentImpl | Module => return None,
                };
                // Add the id to the queue of declarations to translate
                self.id_map.insert(src.clone(), trans_id);
                self.reverse_id_map.insert(trans_id, src.clone());
                // Store the name early so the name matcher can identify paths.
                if let Ok(name) = self.translate_name(src) {
                    self.translated.item_names.insert(trans_id, name);
                }
                trans_id
            }
        };
        self.errors
            .borrow_mut()
            .register_dep_source(dep_src, item_id, src.def_id().is_local());
        item_id.try_into().ok()
    }

    /// Register this item source and enqueue it for translation.
    pub(crate) fn register_and_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        dep_src: &Option<DepSource>,
        item_src: TransItemSource,
    ) -> Option<T> {
        let id = self.register_no_enqueue(dep_src, &item_src);
        self.items_to_translate.push_back(item_src);
        id
    }

    /// Enqueue an item from its id.
    pub(crate) fn enqueue_id(&mut self, id: impl Into<ItemId>) {
        let id = id.into();
        if self.translated.get_item(id).is_none() {
            let item_src = self.reverse_id_map[&id].clone();
            self.items_to_translate.push_back(item_src);
        }
    }

    /// Register the associated types of this trait.
    pub fn register_assoc_items(
        &mut self,
        trait_def_id: &hax::DefId,
        trait_id: TraitDeclId,
    ) -> Result<(), Error> {
        if self.method_status.get(trait_id).is_some() {
            return Ok(());
        }
        let trait_def = self.poly_hax_def(trait_def_id)?;
        let hax::FullDefKind::Trait(t) = trait_def.kind() else {
            unreachable!()
        };
        let names = self
            .translated
            .assoc_item_names
            .get_or_insert_with(trait_id, Default::default);
        for item in t.items(&self.hax_state) {
            let name = TraitItemName(
                item.name
                    .as_ref()
                    .map(|n| n.to_string().into())
                    .unwrap_or_default(),
            );
            let id: AssocItemId = match item.kind {
                hax::AssocKind::Type { .. } => names.types.push(name).into(),
                hax::AssocKind::Fn { .. } => names.methods.push(name).into(),
                hax::AssocKind::Const { .. } => names.consts.push(name).into(),
            };
            self.assoc_item_id_map.insert(item.def_id.clone(), id);
        }
        // Add a virtual method to the `Destruct` trait.
        if trait_def.lang_item == Some(sym::destruct) {
            let method_name = TraitItemName("drop_glue".into());
            names.methods.push(method_name);
        }
        self.method_status.get_or_insert_with(trait_id, || {
            names.methods.map_ref(|_| MethodStatus::default())
        });
        Ok(())
    }

    /// Get the unique per-trait id corresponding to this associated item. The `DefId` can be of an
    /// item declaration or item implementation.
    pub fn translate_assoc_item_id(
        &mut self,
        trait_id: TraitDeclId,
        item_def_id: &hax::DefId,
    ) -> Result<AssocItemId, Error> {
        // The same assoc item `DefId` could belong to several `TraitDeclId`s because of
        // monomorphization, so we only return the item id if we know this trait's data is
        // initialized.
        if let Some(&item_id) = self.assoc_item_id_map.get(item_def_id)
            && self.method_status.get(trait_id).is_some()
        {
            return Ok(item_id);
        }

        let item_def = self.poly_hax_def(item_def_id)?;
        let assoc = match item_def.kind() {
            hax::FullDefKind::AssocTy(t) => t.associated_item(),
            hax::FullDefKind::AssocConst(c) => c.associated_item(),
            hax::FullDefKind::AssocFn(f) => f.associated_item(),
            _ => panic!("Unexpected def for associated item: {item_def:?}"),
        };
        let decl_def_id = assoc.implemented_trait_item_id();

        if decl_def_id != item_def_id
            && let Some(&item_id) = self.assoc_item_id_map.get(decl_def_id)
            && self.method_status.get(trait_id).is_some()
        {
            self.assoc_item_id_map.insert(item_def_id.clone(), item_id);
            return Ok(item_id);
        }

        let trait_def_id = decl_def_id.parent(&self.hax_state).unwrap();
        self.register_assoc_items(&trait_def_id, trait_id)?;
        let item_id = *self.assoc_item_id_map.get(decl_def_id).unwrap();
        Ok(item_id)
    }

    /// Register a trait method and return its `TraitMethodId`. This id is unique per trait.
    /// This does not make the method be considered "used"; use `mark_method_as_used` for that.
    pub fn translate_trait_method_id_no_enqueue(
        &mut self,
        trait_id: TraitDeclId,
        def_id: &hax::DefId,
    ) -> Result<TraitMethodId, Error> {
        let item_id = self.translate_assoc_item_id(trait_id, def_id)?;
        Ok(*item_id.as_method().unwrap())
    }
    /// Register a trait method and return its `TraitMethodId`. This id is unique per trait.
    /// This makes the method be considered "used".
    pub fn translate_trait_method_id(
        &mut self,
        trait_id: TraitDeclId,
        def_id: &hax::DefId,
    ) -> Result<TraitMethodId, Error> {
        let method_id = self.translate_trait_method_id_no_enqueue(trait_id, def_id)?;
        self.mark_method_as_used(trait_id, method_id);
        Ok(method_id)
    }
    /// Register a trait associated type and return its `AssocTypeId`. This id is unique per trait.
    pub fn translate_assoc_type_id(
        &mut self,
        trait_id: TraitDeclId,
        def_id: &hax::DefId,
    ) -> Result<AssocTypeId, Error> {
        let item_id = self.translate_assoc_item_id(trait_id, def_id)?;
        Ok(*item_id.as_type().unwrap())
    }
    /// Register a trait associated const and return its `AssocTypeId`. This id is unique per trait.
    pub fn translate_assoc_const_id(
        &mut self,
        trait_id: TraitDeclId,
        def_id: &hax::DefId,
    ) -> Result<AssocConstId, Error> {
        let item_id = self.translate_assoc_item_id(trait_id, def_id)?;
        Ok(*item_id.as_const().unwrap())
    }

    /// Claim the first type id for the declaration of the unit type.
    pub(crate) fn reserve_unit_decl(&mut self) {
        let def_id = hax::DefId::make_synthetic(&self.hax_state, hax::SyntheticItem::Tuple(0));
        let item_src = if self.options.monomorphize_with_hax
            && let Ok(def) = self.poly_hax_def(&def_id)
        {
            TransItemSource::monomorphic(def.this(), TransItemSourceKind::Type)
        } else {
            TransItemSource::polymorphic(&def_id, TransItemSourceKind::Type)
        };
        let id: Option<TypeDeclId> = if self.options.no_gen_tuple_structs {
            self.register_and_enqueue(&None, item_src)
        } else {
            self.register_no_enqueue(&None, &item_src)
        };
        assert_eq!(id, Some(TypeDeclId::UNIT), "the unit type must come first");
    }

    pub(crate) fn register_target_info(&mut self) {
        let target_data = &self.tcx.data_layout;
        let triple = self.get_target_triple();

        let mut primitive_alignments = SeqHashMap::new();
        primitive_alignments.insert(ScalarTy::Bool, target_data.i8_align.bytes());
        for (ty, alignment) in [
            (IntegerTy::Signed(IntTy::I8), target_data.i8_align.bytes()),
            (IntegerTy::Signed(IntTy::I16), target_data.i16_align.bytes()),
            (IntegerTy::Signed(IntTy::I32), target_data.i32_align.bytes()),
            (IntegerTy::Signed(IntTy::I64), target_data.i64_align.bytes()),
            (
                IntegerTy::Signed(IntTy::I128),
                target_data.i128_align.bytes(),
            ),
            (
                IntegerTy::Signed(IntTy::Isize),
                target_data.pointer_align().bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::U8),
                target_data.i8_align.bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::U16),
                target_data.i16_align.bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::U32),
                target_data.i32_align.bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::U64),
                target_data.i64_align.bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::U128),
                target_data.i128_align.bytes(),
            ),
            (
                IntegerTy::Unsigned(UIntTy::Usize),
                target_data.pointer_align().bytes(),
            ),
        ] {
            primitive_alignments.insert(ScalarTy::Integer(ty), alignment);
        }
        primitive_alignments.insert(ScalarTy::Float(FloatTy::F16), target_data.f16_align.bytes());
        primitive_alignments.insert(ScalarTy::Float(FloatTy::F32), target_data.f32_align.bytes());
        primitive_alignments.insert(ScalarTy::Float(FloatTy::F64), target_data.f64_align.bytes());
        primitive_alignments.insert(
            ScalarTy::Float(FloatTy::F128),
            target_data.f128_align.bytes(),
        );
        // INFO: This is not explicitly guaranteed by the reference, but by the implementation of rustc.
        // https://doc.rust-lang.org/1.97.1/nightly-rustc/src/rustc_ty_utils/layout.rs.html#391
        primitive_alignments.insert(ScalarTy::Char, target_data.i32_align.bytes());

        let c_enum_smallest_repr_ty = match target_data.c_enum_min_size {
            rustc_abi::Integer::I8 => IntTy::I8,
            rustc_abi::Integer::I16 => IntTy::I16,
            rustc_abi::Integer::I32 => IntTy::I32,
            rustc_abi::Integer::I64 => IntTy::I64,
            rustc_abi::Integer::I128 => IntTy::I128,
        };

        let info = TargetInfo {
            target_pointer_size: target_data.pointer_size().bytes(),
            is_little_endian: matches!(target_data.endian, rustc_abi::Endian::Little),
            c_enum_smallest_repr_ty,
            primitive_alignments,
        };
        self.translated.target_information.insert(triple, info);
    }
}

// Id and item reference registration.
impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: self.item_src.def_id().is_local().then_some(span),
        })
    }

    /// Register this item source and enqueue it for translation.
    pub(crate) fn register_and_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        span: Span,
        item_src: TransItemSource,
    ) -> T {
        let dep_src = self.make_dep_source(span);
        self.t_ctx.register_and_enqueue(&dep_src, item_src).unwrap()
    }

    pub(crate) fn register_no_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        span: Span,
        src: &TransItemSource,
    ) -> T {
        let dep_src = self.make_dep_source(span);
        self.t_ctx.register_no_enqueue(&dep_src, src).unwrap()
    }

    /// Register this item and maybe enqueue it for translation.
    pub(crate) fn register_item_maybe_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        span: Span,
        enqueue: bool,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> T {
        let item = if self.monomorphize() && item.has_param {
            item.erase(self.hax_state_with_id())
        } else {
            item.clone()
        };
        // In mono mode:
        //   1. If the item being registered is a `trait decl`, we construct a
        //      `monomorphic_trait` item source.
        //   2. Otherwise, if the current `item_trans_ctx` is under a `trait decl`
        //      or a `vtable`, we construct a `poly` item.
        //   3. In all other cases, we construct a `mono` item.
        let mono =
            self.monomorphize() && (kind.is_for_trait() || !self.item_src.kind.is_for_trait());
        let item_src = TransItemSource::from_item(&item, kind, mono);
        if enqueue {
            self.register_and_enqueue(span, item_src)
        } else {
            self.register_no_enqueue(span, &item_src)
        }
    }

    /// Register this item and enqueue it for translation.
    pub(crate) fn register_item<T: TryFrom<ItemId>>(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> T {
        self.register_item_maybe_enqueue(span, true, item, kind)
    }

    /// Register this item without enqueueing it for translation.
    #[expect(dead_code)]
    pub(crate) fn register_item_no_enqueue<T: TryFrom<ItemId>>(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> T {
        self.register_item_maybe_enqueue(span, false, item, kind)
    }

    /// Register this item and maybe enqueue it for translation.
    pub(crate) fn translate_item_maybe_enqueue<T: TryFrom<DeclRef<ItemId>>>(
        &mut self,
        span: Span,
        hax_item: &hax::ItemRef,
        kind: TransItemSourceKind,
        enqueue: bool,
    ) -> Result<T, Error> {
        let hax_item = if kind.is_derived_item() {
            // If the original item is an associated item we should ignore that and refer to it
            // like a top-level item.
            &hax_item.re_resolve(self.hax_state_with_id(), hax::AssocItemResolution::None)
        } else {
            hax_item
        };

        let id: ItemId = self.register_item_maybe_enqueue(span, enqueue, hax_item, kind);
        // In mono mode, we keep trait decls generic.
        let mut generics = if self.monomorphize() && !matches!(kind, TransItemSourceKind::TraitDecl)
        {
            GenericArgs::empty()
        } else {
            self.translate_generic_args(span, &hax_item.generic_args, &hax_item.trait_proofs)?
        };

        // Add regions to make sure the item args match the params we set up in
        // `translate_item_generics`.
        if matches!(
            hax_item.def_id.kind,
            hax::DefKind::Fn
                | hax::DefKind::FnPtr
                | hax::DefKind::AssocFn
                | hax::DefKind::Closure
                | hax::DefKind::Ctor(..)
        ) {
            let def = self.hax_def(hax_item)?;
            let sig = match def.kind() {
                hax::FullDefKind::Fn(f) => Some(f.sig()),
                hax::FullDefKind::FnPtr(f) => Some(f.sig()),
                hax::FullDefKind::AssocFn(f) => Some(f.sig()),
                hax::FullDefKind::Ctor(f) => Some(f.sig()),
                _ => None,
            };
            if let Some(sig) = sig {
                generics.regions.extend(
                    sig.bound_vars
                        .iter()
                        .map(|_| self.translate_erased_region()),
                );
            } else if let hax::FullDefKind::Closure(c) = def.kind() {
                let closure_args = c.args();
                let upvar_regions = if self.item_src.def_id() == &closure_args.item.def_id {
                    assert!(self.outermost_binder().closure_upvar_tys.is_some());
                    self.outermost_binder().closure_upvar_regions.len()
                } else {
                    // If we're not translating a closure item, fetch the closure adt
                    // definition and add enough erased lifetimes to match its number of
                    // arguments.
                    let adt_decl_id: ItemId =
                        self.register_item(span, hax_item, TransItemSourceKind::Type);
                    let adt_decl = self.get_or_translate(adt_decl_id)?;
                    let adt_generics = adt_decl.generic_params();
                    adt_generics.regions.len() - generics.regions.len()
                };
                generics
                    .regions
                    .extend((0..upvar_regions).map(|_| self.translate_erased_region()));
                if let TransItemSourceKind::TraitImpl(TransImplSource::Callable(..))
                | TransItemSourceKind::VTableInstance(TransImplSource::Callable(..))
                | TransItemSourceKind::VTableInstanceInitializer(TransImplSource::Callable(
                    ..,
                ))
                | TransItemSourceKind::VTableDropShim(TransImplSource::Callable(..))
                | TransItemSourceKind::CallableMethod(..)
                | TransItemSourceKind::VTableMethod(TransImplSource::Callable(..))
                | TransItemSourceKind::ClosureAsFnCast = kind
                {
                    generics.regions.extend(
                        closure_args
                            .fn_sig
                            .bound_vars
                            .iter()
                            .map(|_| self.translate_erased_region()),
                    );
                }
            }
            if let TransItemSourceKind::CallableMethod(ClosureKind::FnMut | ClosureKind::Fn)
            | TransItemSourceKind::VTableMethod(TransImplSource::Callable(
                ClosureKind::FnMut | ClosureKind::Fn,
            )) = kind
            {
                generics.regions.push(self.translate_erased_region());
            }
            // If we're in the process of translating this same item (possibly with a
            // different `TransItemSourceKind`), we can reuse the generics they have in
            // common.
            if self.item_src.def_id() == &hax_item.def_id {
                let depth = self.binding_levels.depth();
                for (a, b) in generics.regions.iter_mut().zip(
                    self.outermost_binder()
                        .params
                        .identity_args_at_depth(depth)
                        .regions,
                ) {
                    *a = b;
                }
            }
        }
        if matches!(
            kind,
            TransItemSourceKind::DropGlueMethod(..) | TransItemSourceKind::VTableDropShim(..)
        ) {
            generics = generics.concat(&self.drop_glue_generic_args());
        }

        let trait_ref = hax_item
            .in_trait
            .as_ref()
            .map(|trait_proof| self.translate_trait_proof(span, trait_proof))
            .transpose()?;

        let item = DeclRef {
            id,
            generics: Box::new(generics),
            trait_ref,
        };
        Ok(item.try_into().ok().unwrap())
    }

    /// Register this item and enqueue it for translation.
    ///
    /// Note: for `FnPtr`s use `translate_fn_ptr` instead, as this handles late-bound variables
    /// correctly. For `TypeDeclRef`s use `translate_type_decl_ref` instead, as this correctly
    /// recognizes built-in ADTs.
    pub(crate) fn translate_item<T: TryFrom<DeclRef<ItemId>>>(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> Result<T, Error> {
        self.translate_item_maybe_enqueue(span, item, kind, true)
    }

    /// Translate a type def id
    pub(crate) fn translate_type_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TypeDeclRef, Error> {
        self.translate_type_decl_ref_maybe_enqueue(span, item, TransItemSourceKind::Type, true)
    }

    /// Register a type item and maybe enqueue it for translation. Use this to
    /// obtain a `TypeDeclRef`, don't construct one manually.
    pub(crate) fn translate_type_decl_ref_maybe_enqueue(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
        enqueue: bool,
    ) -> Result<TypeDeclRef, Error> {
        let builtin = match kind {
            TransItemSourceKind::Type => self.recognize_builtin_adt(item),
            _ => None,
        };
        if builtin == Some(BuiltinAdt::Tuple) && self.t_ctx.options.no_gen_tuple_structs {
            let mut generics = self.translate_generic_args(span, &item.generic_args, &[])?;
            // The declaration has no clauses, so we drop the `Sized` proofs of the fields.
            generics.trait_refs.clear();
            return Ok(TypeDeclRef {
                id: TypeDeclId::UNIT,
                generics: Box::new(generics),
                builtin,
            });
        }
        let item_ref: DeclRef<ItemId> =
            self.translate_item_maybe_enqueue(span, item, kind, enqueue)?;
        assert!(item_ref.trait_ref.is_none());
        Ok(TypeDeclRef {
            id: item_ref.id.try_into().unwrap(),
            generics: item_ref.generics,
            builtin,
        })
    }

    /// Translate a reference to a trait method declaration without registering the declaration as
    /// a `FunDecl`. `TraitDecl.methods` contains the declaration signature and metadata; only
    /// default implementations give rise to a real function item.
    fn translate_method_decl_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<Option<RegionBinder<FnPtr>>, Error> {
        let Some(in_trait) = &item.in_trait else {
            return Ok(None);
        };
        let def = self.hax_def(item)?;
        let hax::FullDefKind::AssocFn(f) = def.kind() else {
            return Ok(None);
        };
        if !matches!(
            &f.associated_item().container,
            hax::AssocItemContainer::TraitContainer { .. }
        ) {
            return Ok(None);
        }

        let trait_ref = self.translate_trait_proof(span, in_trait)?;
        let generics = self.translate_generic_args(span, &item.generic_args, &item.trait_proofs)?;
        self.translate_region_binder(span, &f.sig().as_ref().rebind(()), |ctx, _| {
            let method_id = ctx.translate_trait_method_id(trait_ref.trait_id(), &item.def_id)?;
            let fn_kind = FnPtrKind::Trait(trait_ref.move_under_binder(), method_id);
            let generics = generics.move_under_binder();
            let generics = generics.concat(&ctx.innermost_binder().params.identity_args());
            Ok(FnPtr::new(fn_kind, generics))
        })
        .map(Some)
    }

    /// Translate a function reference, assuming that the late-bound regions are in scope. Prefer
    /// the `translate_bound_fn_ptr*` methods whenever sensible.
    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_unbound_fn_ptr_maybe_enqueue(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
        enqueue: bool,
    ) -> Result<FnPtr, Error> {
        let fun_item: DeclRef<ItemId> =
            self.translate_item_maybe_enqueue(span, item, kind, enqueue)?;
        let fun_item: DeclRef<FunDeclId> = fun_item.try_convert_id().unwrap();
        let fun_id = match fun_item.trait_ref {
            // Direct function call
            None => FnPtrKind::Fun(fun_item.id),
            // Trait method
            Some(trait_ref) => {
                let trait_decl_id = trait_ref.trait_id();
                let method_id = self.translate_trait_method_id(trait_decl_id, &item.def_id)?;
                FnPtrKind::Trait(trait_ref, method_id)
            }
        };
        let mut generics = fun_item.generics;
        // The last n regions are the late-bound ones and were provided as erased regions by
        // `translate_item`.
        for (a, b) in generics.regions.iter_mut().rev().zip(
            self.innermost_binder()
                .params
                .identity_args()
                .regions
                .into_iter()
                .rev(),
        ) {
            *a = b;
        }
        Ok(FnPtr::new(fun_id, generics))
    }

    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_bound_fn_ptr_maybe_enqueue(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
        enqueue: bool,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        if let Some(fn_ptr) = self.translate_callable_method_fn_ptr(span, item)? {
            return Ok(fn_ptr);
        }
        if let Some(fn_ptr) = self.translate_method_decl_fn_ptr(span, item)? {
            return Ok(fn_ptr);
        }

        let late_bound = self.hax_def(item)?.late_bound();
        self.translate_region_binder(span, &late_bound, |ctx, _| {
            ctx.translate_unbound_fn_ptr_maybe_enqueue(span, item, kind, enqueue)
        })
    }

    /// Translate a reference to a function or trait method.
    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_bound_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        self.translate_bound_fn_ptr_maybe_enqueue(span, item, kind, true)
    }

    pub(crate) fn translate_bound_fn_ptr_no_enqueue(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        self.translate_bound_fn_ptr_maybe_enqueue(span, item, kind, false)
    }

    /// Translate a reference to a function or trait method, erasing or inferring its late-bound
    /// lifetimes.
    pub(crate) fn translate_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
    ) -> Result<FnPtr, Error> {
        let fn_ptr = self.translate_bound_fn_ptr(span, item, kind)?;
        let fn_ptr = self.erase_region_binder(fn_ptr);
        Ok(fn_ptr)
    }

    pub(crate) fn translate_global_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<GlobalDeclRef, Error> {
        self.translate_item(span, item, TransItemSourceKind::Global)
    }

    pub(crate) fn translate_trait_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TraitDeclRef, Error> {
        self.translate_item(span, item, TransItemSourceKind::TraitDecl)
    }

    pub(crate) fn translate_trait_impl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransImplSource,
    ) -> Result<TraitImplRef, Error> {
        self.translate_item(span, item, TransItemSourceKind::TraitImpl(kind))
    }
}

#[tracing::instrument(skip(tcx, error_ctx))]
pub fn translate<'tcx>(
    tcx: TyCtxt<'tcx>,
    cli_options: &CliOpts,
    mut error_ctx: ErrorCtx,
    sysroot: PathBuf,
) -> Result<TransformCtx, Error> {
    let translate_options = TranslateOptions::new(&mut error_ctx, cli_options);

    let traits_to_remove: HashSet<rustc_hir::def_id::DefId> = {
        let hax_state = hax::state::State::new(
            tcx,
            hax::options::Options::default(),
            hax::options::BoundsOptions::default(),
        );
        translate_options
            .hide_traits
            .iter()
            .flat_map(|pat| super::resolve_path::def_path_def_ids(&hax_state, pat, true).unwrap())
            .collect()
    };
    let hax_state = hax::state::State::new(
        tcx,
        hax::options::Options {
            inline_anon_consts: !translate_options.raw_consts,
            anon_allocs_as_globals: matches!(translate_options.consts, ConstHandling::Values),
        },
        hax::options::BoundsOptions {
            add_destruct_bounds: translate_options.add_destruct_bounds,
            remove_traits: traits_to_remove,
        },
    );

    let crate_def_id: hax::DefId = rustc_span::def_id::CRATE_DEF_ID
        .to_def_id()
        .sinto(&hax_state);
    let crate_name = crate_def_id.crate_name(&hax_state).to_string();
    trace!("# Crate: {}", crate_name);

    let mut ctx = TranslateCtx {
        tcx,
        sysroot,
        hax_state,
        options: translate_options,
        errors: RefCell::new(error_ctx),
        translated: TranslatedCrate {
            crate_name,
            options: cli_options.clone(),
            ..TranslatedCrate::default()
        },
        method_status: Default::default(),
        assoc_item_id_map: Default::default(),
        id_map: Default::default(),
        reverse_id_map: Default::default(),
        file_to_id: Default::default(),
        items_to_translate: Default::default(),
        processed: Default::default(),
        started_from: Default::default(),
        translate_stack: Default::default(),
        cached_spans: Default::default(),
        cached_file_ids: Default::default(),
        cached_names: Default::default(),
        cached_item_metas: Default::default(),
        panic_fns: Default::default(),
        lt_mutability_computer: Default::default(),
    };
    ctx.register_target_info();
    ctx.panic_fns = [
        "core::panicking::assert_failed",
        &names::EXPLICIT_PANIC_NAME.join("::"),
    ]
    .into_iter()
    .filter_map(|path| {
        let pat = NamePattern::parse(path).unwrap();
        super::resolve_path::def_path_def_ids(&ctx.hax_state, &pat, true).ok()
    })
    .flatten()
    .collect();
    ctx.reserve_unit_decl();
    ctx.register_builtin_functions()?;

    // Start translating from the selected items.
    for start_from in ctx.options.start_from.clone() {
        match start_from {
            StartFrom::Pattern { pattern, strict } => {
                if let Ok(def_ids) = ctx.resolve_path(Span::dummy(), &pattern, strict) {
                    for def_id in def_ids {
                        let def_id: hax::DefId = def_id.sinto(&ctx.hax_state);
                        ctx.enqueue_module_item(&def_id, true);
                    }
                }
            }
            StartFrom::Attribute(attr_name) => {
                let attr_path = attr_name
                    .split("::")
                    .map(rustc_span::Symbol::intern)
                    .collect_vec();
                let mut add_if_attr_matches = |ldid: rustc_hir::def_id::LocalDefId| {
                    let def_id: hax::DefId = ldid.to_def_id().sinto(&ctx.hax_state);
                    if !matches!(def_id.kind, hax::DefKind::Mod)
                        && def_id.attrs(tcx).iter().any(|a| a.path_matches(&attr_path))
                    {
                        ctx.enqueue_module_item(&def_id, true);
                    }
                };
                for ldid in tcx.hir_crate_items(()).definitions() {
                    add_if_attr_matches(ldid)
                }
            }
            StartFrom::Pub => {
                let mut add_if_matches = |ldid: rustc_hir::def_id::LocalDefId| {
                    let def_id: hax::DefId = ldid.to_def_id().sinto(&ctx.hax_state);
                    if !matches!(def_id.kind, hax::DefKind::Mod)
                        && def_id.visibility(tcx) == Some(true)
                    {
                        ctx.enqueue_module_item(&def_id, true);
                    }
                };
                for ldid in tcx.hir_crate_items(()).definitions() {
                    add_if_matches(ldid)
                }
            }
        }
    }

    if ctx.errors.borrow().has_errors() {
        // Don't continue translating if there were errors while parsing options.
        return Err(Error::dummy());
    }

    trace!(
        "Queue after we explored the crate:\n{:?}",
        &ctx.items_to_translate
    );

    // Translate.
    //
    // For as long as the queue of items to translate is not empty, we pop the top item and
    // translate it. If an item refers to non-translated (potentially external) items, we add them
    // to the queue.
    //
    // Note that the order in which we translate the definitions doesn't matter:
    // we never need to lookup a translated definition, and only use the map
    // from Rust ids to translated ids.
    while let Some(item_src) = ctx.items_to_translate.pop_front() {
        if ctx.processed.insert(item_src.clone()) {
            ctx.translate_item(&item_src);
        }
    }

    // Remove methods not marked as "used". They are never called and we made sure not to translate
    // them. This removes them from the traits and impls.
    ctx.remove_unused_methods();

    // Return the context, dropping the hax state and rustc `tcx`.
    Ok(TransformCtx {
        options: ctx.options,
        translated: ctx.translated,
        errors: ctx.errors,
    })
}
