use std::fmt;

use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use index_vec::Idx;
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};

use crate::ast::*;
use crate::formatter::{AstFormatter, FmtCtx, IntoFormatter};
use crate::ids::{IndexMap, IndexVec};
use crate::pretty::FmtWithCtx;
use crate::utils::serialize_map_to_array::SeqHashMapToArray;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};

/// A target triple, e.g. `x86_64-unknown-linux-gnu`.
pub type TargetTriple = String;

/// The complete data of a Rust crate.
///
/// A crate is mainly composed of 5 kinds of items:
/// - Functions;
/// - Type definitions;
/// - Globals (constants and statics);
/// - Trait declarations;
/// - Trait implementations.
///
/// These can each be found in the corresponding `IndexVec`. They are in an unspecified (though
/// deterministic) order.
/// If you need a more robust order, see `ordered_decls`.
///
/// To get a `TranslatedCrate`, run `charon cargo` inside a Rust crate, then deserialize
/// the resulting `crate_name.llbc` file using [`crate::deserialize_llbc`].
#[derive(Default, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(state_implements = DedupSerializerState)]
pub struct TranslatedCrate {
    /// The name of the crate.
    pub crate_name: String,

    /// The options used when calling Charon. Can be used to check that Charon was called with the
    /// options that a given consumer requires.
    #[serde_state(stateless)]
    pub options: crate::options::CliOpts,

    /// Information about each target platform for which the crate was translated. When translating
    /// a crate normally this will have a single entry; when using `--targets` this will have one
    /// entry per chosen target.
    #[serde(with = "SeqHashMapToArray::<TargetTriple, TargetInfo>")]
    pub target_information: SeqHashMap<TargetTriple, TargetInfo>,

    /// The source files composing the crate and its dependencies. Each [`Span`] refers to a byte
    /// range within one of these files.
    // This field must come before any field containing spans, as the OCaml deserialization of
    // spans requires the files to be deserialized already.
    #[serde_state(stateless)]
    pub files: IndexVec<FileId, File>,

    /// The names of all registered items. Available so we can know the names even of items that
    /// failed to translate.
    /// Invariant: after translation, any existing `ItemId` must have an associated name, even
    /// if the corresponding item wasn't translated.
    #[serde(with = "SeqHashMapToArray::<ItemId, Name>")]
    pub item_names: SeqHashMap<ItemId, Name>,
    /// The names of all the registered associated items. Available so we can know the names even
    /// of items that failed to translate.
    /// Invariant: after translation, any existing `AssocItemId` must have an associated name, even
    /// if the corresponding item wasn't translated.
    pub assoc_item_names: IndexMap<TraitDeclId, AssocItemNames>,
    /// Short names, for items whose last PathElem is unique.
    #[serde(with = "SeqHashMapToArray::<ItemId, Name>")]
    pub short_names: SeqHashMap<ItemId, Name>,

    /// The type definitions (structs, enums, ...).
    pub type_decls: IndexMap<TypeDeclId, TypeDecl>,
    /// The function definitions.
    ///
    /// Each item with a body becomes a function: actual functions, methods, and unevaluated
    /// consts/statics.
    pub fun_decls: IndexMap<FunDeclId, FunDecl>,
    /// The global definitions, which are constants, statics, and thread locals.
    pub global_decls: IndexMap<GlobalDeclId, GlobalDecl>,
    /// The trait declarations.
    pub trait_decls: IndexMap<TraitDeclId, TraitDecl>,
    /// The trait implementations.
    pub trait_impls: IndexMap<TraitImplId, TraitImpl>,
    /// This contains a list of all the reachable items in the crate in a stable, logical order
    /// based on crate and file order, then further grouped and sorted such that every item comes
    /// after the items it depends on.
    /// Mutually-dependent groups of items are identified as such.
    /// This is meant for code-generation tools that want a stable output order.
    ///
    /// Not all the items in the `TranslatedCrate` are included: some trait impls are never
    /// referred to by reachable items so could in principle be removed from the crate, but we keep
    /// them around to be able to tell method implementations apart.
    ///
    /// `Some` after translation unless `--no-reorder-decls` is passed.
    #[serde_state(stateless)]
    pub ordered_decls: Option<Vec<DeclarationGroup>>,
}

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, Clone)]
#[derive(VariantIndexArity, VariantName, EnumAsGetters, EnumIsA)]
#[derive(Serialize, Deserialize)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Group"))]
pub enum GDeclarationGroup<Id> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, Clone)]
#[derive(VariantIndexArity, VariantName, EnumAsGetters, EnumIsA)]
#[derive(Serialize, Deserialize)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Group"))]
pub enum DeclarationGroup {
    /// A type declaration group
    Type(GDeclarationGroup<TypeDeclId>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunDeclId>),
    /// A global declaration group
    Global(GDeclarationGroup<GlobalDeclId>),
    TraitDecl(GDeclarationGroup<TraitDeclId>),
    TraitImpl(GDeclarationGroup<TraitImplId>),
    /// Anything that doesn't fit into these categories.
    Mixed(GDeclarationGroup<ItemId>),
}

#[derive(Default, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct AssocItemNames {
    pub types: IndexVec<AssocTypeId, TraitItemName>,
    pub methods: IndexVec<TraitMethodId, TraitItemName>,
    pub consts: IndexVec<AssocConstId, TraitItemName>,
}

impl TranslatedCrate {
    pub fn item_name(&self, id: impl Into<ItemId>) -> &Name {
        // `unwrap` is ok because we ensure to translate the item name as soon as we create a new
        // item id.
        self.item_names.get(&id.into()).unwrap()
    }
    pub fn assoc_item_name(
        &self,
        trait_id: TraitDeclId,
        id: impl Into<AssocItemId>,
    ) -> TraitItemName {
        let names = &self.assoc_item_names[trait_id];
        match id.into() {
            AssocItemId::Type(id) => names.types[id],
            AssocItemId::Method(id) => names.methods[id],
            AssocItemId::Const(id) => names.consts[id],
        }
    }

    pub fn item_short_name(&self, id: impl Into<ItemId>) -> &Name {
        let id = id.into();
        self.short_names
            .get(&id)
            .unwrap_or_else(|| self.item_name(id))
    }

    pub fn get_item(&self, trans_id: impl Into<ItemId>) -> Option<ItemRef<'_>> {
        match trans_id.into() {
            ItemId::Type(id) => self.type_decls.get(id).map(ItemRef::Type),
            ItemId::Fun(id) => self.fun_decls.get(id).map(ItemRef::Fun),
            ItemId::Global(id) => self.global_decls.get(id).map(ItemRef::Global),
            ItemId::TraitDecl(id) => self.trait_decls.get(id).map(ItemRef::TraitDecl),
            ItemId::TraitImpl(id) => self.trait_impls.get(id).map(ItemRef::TraitImpl),
        }
    }
    pub fn get_item_mut(&mut self, trans_id: ItemId) -> Option<ItemRefMut<'_>> {
        match trans_id {
            ItemId::Type(id) => self.type_decls.get_mut(id).map(ItemRefMut::Type),
            ItemId::Fun(id) => self.fun_decls.get_mut(id).map(ItemRefMut::Fun),
            ItemId::Global(id) => self.global_decls.get_mut(id).map(ItemRefMut::Global),
            ItemId::TraitDecl(id) => self.trait_decls.get_mut(id).map(ItemRefMut::TraitDecl),
            ItemId::TraitImpl(id) => self.trait_impls.get_mut(id).map(ItemRefMut::TraitImpl),
        }
    }

    /// Remove this item from the crate, including the name information about it.
    ///
    /// See also [`TranslatedCrate::remove_item_temporarily`].
    pub fn remove_item(&mut self, trans_id: ItemId) -> Option<ItemByVal> {
        self.short_names.swap_remove(&trans_id);
        self.item_names.swap_remove(&trans_id);
        self.remove_item_temporarily(trans_id)
    }
    /// Insert a new item into a slot, and record its name in the name map.
    pub fn set_new_item_slot(&mut self, id: ItemId, item: impl Into<ItemByVal>) {
        let item = item.into();
        self.item_names
            .insert(id, item.as_ref().item_meta().name.clone());
        self.put_item_back(id, item);
    }
    /// Remove this item from the crate without touching the name maps.
    /// Useful for modifying items whilst being able to access the rest of the crate.
    /// Put the item back using [`TranslatedCrate::put_item_back`].
    ///
    /// See also [`TranslatedCrate::remove_item`].
    pub fn remove_item_temporarily(&mut self, trans_id: ItemId) -> Option<ItemByVal> {
        match trans_id {
            ItemId::Type(id) => self.type_decls.remove(id).map(ItemByVal::Type),
            ItemId::Fun(id) => self.fun_decls.remove(id).map(ItemByVal::Fun),
            ItemId::Global(id) => self.global_decls.remove(id).map(ItemByVal::Global),
            ItemId::TraitDecl(id) => self.trait_decls.remove(id).map(ItemByVal::TraitDecl),
            ItemId::TraitImpl(id) => self.trait_impls.remove(id).map(ItemByVal::TraitImpl),
        }
    }
    /// Insert the item into the corresponding slot without recording its name in the name map.
    /// Only use if the item already has its name registered, e.g. if you got it using
    /// [`TranslatedCrate::remove_item_temporarily`].
    pub fn put_item_back(&mut self, id: ItemId, item: impl Into<ItemByVal>) {
        match item.into() {
            ItemByVal::Type(decl) => self.type_decls.set_slot(*id.as_type().unwrap(), decl),
            ItemByVal::Fun(decl) => self.fun_decls.set_slot(*id.as_fun().unwrap(), decl),
            ItemByVal::Global(decl) => self.global_decls.set_slot(*id.as_global().unwrap(), decl),
            ItemByVal::TraitDecl(decl) => self
                .trait_decls
                .set_slot(*id.as_trait_decl().unwrap(), decl),
            ItemByVal::TraitImpl(decl) => self
                .trait_impls
                .set_slot(*id.as_trait_impl().unwrap(), decl),
        }
    }

    pub fn all_ids(&self) -> impl Iterator<Item = ItemId> + use<> {
        self.type_decls
            .all_indices()
            .map(ItemId::Type)
            .chain(self.trait_decls.all_indices().map(ItemId::TraitDecl))
            .chain(self.trait_impls.all_indices().map(ItemId::TraitImpl))
            .chain(self.global_decls.all_indices().map(ItemId::Global))
            .chain(self.fun_decls.all_indices().map(ItemId::Fun))
    }
    pub fn all_items(&self) -> impl Iterator<Item = ItemRef<'_>> {
        self.type_decls
            .iter()
            .map(ItemRef::Type)
            .chain(self.trait_decls.iter().map(ItemRef::TraitDecl))
            .chain(self.trait_impls.iter().map(ItemRef::TraitImpl))
            .chain(self.global_decls.iter().map(ItemRef::Global))
            .chain(self.fun_decls.iter().map(ItemRef::Fun))
    }
    pub fn all_items_mut(&mut self) -> impl Iterator<Item = ItemRefMut<'_>> {
        self.type_decls
            .iter_mut()
            .map(ItemRefMut::Type)
            .chain(self.trait_impls.iter_mut().map(ItemRefMut::TraitImpl))
            .chain(self.trait_decls.iter_mut().map(ItemRefMut::TraitDecl))
            .chain(self.fun_decls.iter_mut().map(ItemRefMut::Fun))
            .chain(self.global_decls.iter_mut().map(ItemRefMut::Global))
    }
    pub fn all_items_with_ids(&self) -> impl Iterator<Item = (ItemId, ItemRef<'_>)> {
        self.all_items().map(|item| (item.id(), item))
    }

    /// Iterate over all reachable items in dependency order. Panics if `--no-reorder-decls` cas
    /// passed to Charon.
    pub fn in_dependency_order(&self) -> impl Iterator<Item = ItemId> + '_ {
        self.ordered_decls
            .as_ref()
            .expect(
                "`in_dependency_order` no available if \
                `--no-reorder-decls` was passed to Charon",
            )
            .iter()
            .flat_map(DeclarationGroup::get_ids)
    }

    /// When translating without `--target`, there's only one target information; this method
    /// retrieves it.
    /// Panics if this crate was translated in multi-target mode.
    pub fn the_target_information(&self) -> &TargetInfo {
        self.target_information
            .values()
            .exactly_one()
            .ok()
            .expect("called `the_target_information` on a multi-target crate")
    }
}

impl fmt::Display for TranslatedCrate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let fmt: &FmtCtx = &self.into_fmt();
        self.fmt_with_ctx(fmt, f)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TranslatedCrate {
    fn fmt_with_ctx(&self, fmt: &C, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ordered_decls {
            None => {
                // We do simple: types, globals, traits, functions
                for d in &self.type_decls {
                    writeln!(f, "{}\n", d.with_ctx(fmt))?
                }
                for d in &self.global_decls {
                    writeln!(f, "{}\n", d.with_ctx(fmt))?
                }
                for d in &self.trait_decls {
                    writeln!(f, "{}\n", d.with_ctx(fmt))?
                }
                for d in &self.trait_impls {
                    writeln!(f, "{}\n", d.with_ctx(fmt))?
                }
                for d in &self.fun_decls {
                    writeln!(f, "{}\n", d.with_ctx(fmt))?
                }
            }
            Some(ordered_decls) => {
                for gr in ordered_decls {
                    for id in gr.get_ids() {
                        match self.get_item(id) {
                            Some(decl) => writeln!(f, "{}\n", decl.with_ctx(fmt))?,
                            None => {
                                let name = self.item_short_name(id).with_ctx(fmt);
                                writeln!(f, "Missing decl: {id:?} ({name})\n")?;
                            }
                        }
                    }
                }
            }
        }
        fmt::Result::Ok(())
    }
}

impl<'a> IntoFormatter for &'a TranslatedCrate {
    type C = FmtCtx<'a>;

    fn into_fmt(self) -> Self::C {
        FmtCtx {
            translated: Some(self),
            ..Default::default()
        }
    }
}

pub trait HasIdxMapOf<Id: Idx>: std::ops::Index<Id, Output: Sized> {
    fn get_idx_map(&self) -> &IndexMap<Id, Self::Output>;
    fn get_idx_map_mut(&mut self) -> &mut IndexMap<Id, Self::Output>;
}

/// Delegate `Index` implementations to subfields.
macro_rules! mk_index_impls {
    ($ty:ident.$field:ident[$idx:ty]: $output:ty) => {
        impl std::ops::Index<$idx> for $ty {
            type Output = $output;
            fn index(&self, index: $idx) -> &Self::Output {
                &self.$field[index]
            }
        }
        impl std::ops::IndexMut<$idx> for $ty {
            fn index_mut(&mut self, index: $idx) -> &mut Self::Output {
                &mut self.$field[index]
            }
        }
        impl HasIdxMapOf<$idx> for $ty {
            fn get_idx_map(&self) -> &IndexMap<$idx, Self::Output> {
                &self.$field
            }
            fn get_idx_map_mut(&mut self) -> &mut IndexMap<$idx, Self::Output> {
                &mut self.$field
            }
        }
    };
}
mk_index_impls!(TranslatedCrate.type_decls[TypeDeclId]: TypeDecl);
mk_index_impls!(TranslatedCrate.fun_decls[FunDeclId]: FunDecl);
mk_index_impls!(TranslatedCrate.global_decls[GlobalDeclId]: GlobalDecl);
mk_index_impls!(TranslatedCrate.trait_decls[TraitDeclId]: TraitDecl);
mk_index_impls!(TranslatedCrate.trait_impls[TraitImplId]: TraitImpl);
