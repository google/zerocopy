//! Compute an ordering on declarations that:
//! - Detects mutually-recursive groups;
//! - Always orders an item before any of its uses (except for recursive cases);
//! - Otherwise keeps a stable order.
//!
//! Aeneas needs this because proof assistant languages are sensitive to declaration order and need
//! to be explicit about mutual recursion. This should come useful for translation to any other
//! language with these properties.
use crate::options::TranslateOptions;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use crate::utils::*;
use derive_generic_visitor::*;
use itertools::Itertools;
use petgraph::graphmap::DiGraphMap;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::fmt::{Debug, Display, Error};
use std::vec::Vec;

use crate::transform::ctx::TransformPass;

impl<Id: Copy> GDeclarationGroup<Id> {
    pub fn get_ids(&self) -> &[Id] {
        use GDeclarationGroup::*;
        match self {
            NonRec(id) => std::slice::from_ref(id),
            Rec(ids) => ids.as_slice(),
        }
    }

    pub fn get_any_trans_ids(&self) -> Vec<ItemId>
    where
        Id: Into<ItemId>,
    {
        self.get_ids().iter().copied().map(|id| id.into()).collect()
    }

    fn make_group(is_rec: bool, ids: Vec<ItemId>) -> Self
    where
        Id: TryFrom<ItemId>,
        Id::Error: Debug,
    {
        let ids: Vec<_> = ids.into_iter().map(|x| x.try_into().unwrap()).collect();
        if is_rec {
            GDeclarationGroup::Rec(ids)
        } else {
            assert!(ids.len() == 1);
            GDeclarationGroup::NonRec(ids[0])
        }
    }

    fn to_mixed(&self) -> GDeclarationGroup<ItemId>
    where
        Id: Into<ItemId>,
    {
        match self {
            GDeclarationGroup::NonRec(x) => GDeclarationGroup::NonRec((*x).into()),
            GDeclarationGroup::Rec(_) => GDeclarationGroup::Rec(self.get_any_trans_ids()),
        }
    }
}

impl DeclarationGroup {
    fn make_group(is_rec: bool, ids: Vec<ItemId>) -> Self {
        let id0 = ids[0];
        let all_same_kind = ids
            .iter()
            .all(|id| id0.variant_index_arity() == id.variant_index_arity());
        match id0 {
            _ if !all_same_kind => {
                DeclarationGroup::Mixed(GDeclarationGroup::make_group(is_rec, ids))
            }
            ItemId::Type(_) => DeclarationGroup::Type(GDeclarationGroup::make_group(is_rec, ids)),
            ItemId::Fun(_) => DeclarationGroup::Fun(GDeclarationGroup::make_group(is_rec, ids)),
            ItemId::Global(_) => {
                DeclarationGroup::Global(GDeclarationGroup::make_group(is_rec, ids))
            }
            ItemId::TraitDecl(_) => {
                DeclarationGroup::TraitDecl(GDeclarationGroup::make_group(is_rec, ids))
            }
            ItemId::TraitImpl(_) => {
                DeclarationGroup::TraitImpl(GDeclarationGroup::make_group(is_rec, ids))
            }
        }
    }

    pub fn to_mixed_group(&self) -> GDeclarationGroup<ItemId> {
        use DeclarationGroup::*;
        match self {
            Type(gr) => gr.to_mixed(),
            Fun(gr) => gr.to_mixed(),
            Global(gr) => gr.to_mixed(),
            TraitDecl(gr) => gr.to_mixed(),
            TraitImpl(gr) => gr.to_mixed(),
            Mixed(gr) => gr.clone(),
        }
    }

    pub fn get_ids(&self) -> Vec<ItemId> {
        use DeclarationGroup::*;
        match self {
            Type(gr) => gr.get_any_trans_ids(),
            Fun(gr) => gr.get_any_trans_ids(),
            Global(gr) => gr.get_any_trans_ids(),
            TraitDecl(gr) => gr.get_any_trans_ids(),
            TraitImpl(gr) => gr.get_any_trans_ids(),
            Mixed(gr) => gr.get_any_trans_ids(),
        }
    }
}

impl<Id: Display> Display for GDeclarationGroup<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            GDeclarationGroup::NonRec(id) => write!(f, "non-rec: {id}"),
            GDeclarationGroup::Rec(ids) => {
                write!(
                    f,
                    "rec: {}",
                    pretty_display_list(|id| format!("    {id}"), ids)
                )
            }
        }
    }
}

impl Display for DeclarationGroup {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {decl} }}"),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {decl} }}"),
            DeclarationGroup::Global(decl) => write!(f, "{{ Global(s): {decl} }}"),
            DeclarationGroup::TraitDecl(decl) => write!(f, "{{ Trait decls(s): {decl} }}"),
            DeclarationGroup::TraitImpl(decl) => write!(f, "{{ Trait impl(s): {decl} }}"),
            DeclarationGroup::Mixed(decl) => write!(f, "{{ Mixed items: {decl} }}"),
        }
    }
}

#[derive(Default)]
pub struct Deps {
    /// The dependency graph between translated items. We're careful to only add items that got
    /// translated.
    graph: DiGraphMap<ItemId, ()>,
    unprocessed: Vec<ItemId>,
    visited: HashSet<ItemId>,
}

/// We use this when computing the graph
#[derive(Visitor)]
pub struct DepsForItem<'a> {
    ctx: &'a TransformCtx,
    deps: &'a mut Deps,
    current_id: ItemId,
    // Each item countains its own id; we dont' want to count that as a self-reference. Hence the
    // first time we see its own id, we skip.
    seen_current_id: bool,
    // We use this to track the trait impl block the current item belongs to
    // (if relevant).
    //
    // We use this to ignore the references to the parent impl block.
    //
    // If we don't do so, when computing our dependency graph we end up with
    // mutually recursive trait impl blocks/trait method impls in the presence
    // of associated types (the deepest reason is that we don't normalize the
    // types we query from rustc when translating the types from function
    // signatures - we avoid doing so because as of now it makes resolving
    // the trait params harder: if we get normalized types, we have to
    // implement a normalizer on our side to make sure we correctly match
    // types...).
    //
    //
    // For instance, the problem happens if in Rust we have:
    // ```text
    // pub trait WithConstTy {
    //     type W;
    //     fn f(x: &mut Self::W);
    // }
    //
    // impl WithConstTy for bool {
    //     type W = u64;
    //     fn f(_: &mut Self::W) {}
    // }
    // ```
    //
    // In LLBC we get:
    //
    // ```text
    // impl traits::Bool::0 : traits::WithConstTy<bool>
    // {
    //     type W = u64 with []
    //     fn f = traits::Bool::0::f
    // }
    //
    // fn traits::Bool::0::f<@R0>(@1: &@R0 mut (traits::Bool::0::W)) { .. }
    // //                                       ^^^^^^^^^^^^^^^
    // //                                    refers to the trait impl
    // ```
    parent_trait_impl: Option<TraitImplId>,
    parent_trait_decl: Option<TraitDeclId>,
}

impl Deps {
    fn visitor_for_item<'a>(
        &'a mut self,
        ctx: &'a TransformCtx,
        item: ItemRef<'_>,
    ) -> DepsForItem<'a> {
        let current_id = item.id();
        self.graph.add_node(current_id);

        let mut for_item = DepsForItem {
            ctx,
            deps: self,
            seen_current_id: false,
            current_id,
            parent_trait_impl: None,
            parent_trait_decl: None,
        };

        // Add the id of the impl/trait this item belongs to, if necessary
        match item {
            ItemRef::Fun(FunDecl {
                src: FunSource::TraitDefault { trait_ref, .. },
                ..
            })
            | ItemRef::Global(GlobalDecl {
                src: GlobalSource::TraitDefault { trait_ref, .. },
                ..
            }) => for_item.parent_trait_decl = Some(trait_ref.id),
            ItemRef::Fun(FunDecl {
                src: FunSource::TraitImpl { impl_ref, .. },
                ..
            })
            | ItemRef::Global(GlobalDecl {
                src: GlobalSource::TraitImpl { impl_ref, .. },
                ..
            }) => for_item.parent_trait_impl = Some(impl_ref.id),
            _ => {}
        }

        for_item
    }
}

impl DepsForItem<'_> {
    fn insert_node(&mut self, tgt: impl Into<ItemId>) {
        let tgt = tgt.into();
        // Only add translated items.
        if self.ctx.translated.get_item(tgt).is_some() && !self.deps.visited.contains(&tgt) {
            self.deps.unprocessed.push(tgt);
        }
    }
    fn insert_edge(&mut self, tgt: impl Into<ItemId>) {
        let tgt = tgt.into();
        if tgt == self.current_id && !self.seen_current_id {
            // Each item contains its own id; this is a hack to avoid considering that as a self
            // loop.
            self.seen_current_id = true;
            return;
        }
        self.insert_node(tgt);
        // Only add translated items.
        if self.ctx.translated.get_item(tgt).is_some() {
            self.deps.graph.add_edge(self.current_id, tgt, ());
        }
    }
}

impl VisitAst for DepsForItem<'_> {
    fn enter_type_decl_id(&mut self, id: &TypeDeclId) {
        self.insert_edge(*id);
    }

    fn enter_global_decl_id(&mut self, id: &GlobalDeclId) {
        self.insert_edge(*id);
    }

    fn enter_trait_impl_id(&mut self, id: &TraitImplId) {
        // If the impl is the impl this item belongs to, we ignore it
        // TODO: this is not very satisfying but this is the only way we have of preventing
        // mutually recursive groups between method impls and trait impls in the presence of
        // associated types...
        if self.parent_trait_impl != Some(*id) {
            self.insert_edge(*id);
        }
    }

    fn enter_trait_decl_id(&mut self, id: &TraitDeclId) {
        // If the trait is the trait this item belongs to, we ignore it. This is to avoid mutually
        // recursive groups between e.g. traits decls and their globals. We treat methods
        // specifically.
        if self.parent_trait_decl != Some(*id) {
            self.insert_edge(*id);
        }
    }

    fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
        self.insert_edge(*id);
    }

    fn visit_trait_assoc_const(
        &mut self,
        assoc_const: &TraitAssocConst,
    ) -> ControlFlow<Self::Break> {
        let TraitAssocConst {
            name: _,
            attr_info: _,
            ty,
            default,
        } = assoc_const;
        ty.drive(self)?;
        // We consider that a trait decl only contains the method/constant signatures.
        // Therefore we don't explore the default method/const ids.
        if let Some(gref) = default {
            self.insert_node(gref.id); // Still count the item as reachable.
            gref.generics.drive(self)?;
        }
        Continue(())
    }

    fn visit_trait_method(&mut self, method: &TraitMethod) -> ControlFlow<Self::Break> {
        let TraitMethod {
            name: _,
            item_meta: _,
            signature,
            default,
        } = method;
        // We consider that a trait decl only contains the method/constant signatures.
        // Therefore we don't explore the default method/const ids.
        signature.drive(self)?;
        if let Some(funref) = default {
            self.insert_node(funref.id); // Still count the item as reachable.
            funref.generics.drive(self)?;
        }
        Continue(())
    }

    fn visit_item_meta(&mut self, meta: &ItemMeta) -> ControlFlow<Self::Break> {
        // Don't visit the name because trait impls contain their own id in it. Attributes however
        // can contain genuine dependencies, notably between an item and its specifications.
        meta.attr_info.drive(self)
    }

    fn visit_attribute(&mut self, attr: &Attribute) -> ControlFlow<Self::Break> {
        // An item depends on its contracts, not the other way around.
        match attr {
            Attribute::IsContract { .. } => Continue(()),
            _ => self.visit_inner(attr),
        }
    }

    // The layout guarantees of a type mention the type itself -- we ignore those.
    fn visit_layout(&mut self, _: &Layout) -> ControlFlow<Self::Break> {
        Continue(())
    }
    // Sources are reverse dependencies; exploring them is likely to create dependency cycles.
    fn visit_type_source(&mut self, _: &TypeSource) -> ControlFlow<Self::Break> {
        Continue(())
    }
    fn visit_fun_source(&mut self, src: &FunSource) -> ControlFlow<Self::Break> {
        if let FunSource::TraitDefault { trait_ref, .. } = src {
            self.insert_edge(trait_ref.id);
        }
        Continue(())
    }
    fn visit_global_source(&mut self, _: &GlobalSource) -> ControlFlow<Self::Break> {
        Continue(())
    }
    fn visit_trait_decl_source(&mut self, _: &TraitDeclSource) -> ControlFlow<Self::Break> {
        Continue(())
    }
    fn visit_trait_impl_source(&mut self, _: &TraitImplSource) -> ControlFlow<Self::Break> {
        Continue(())
    }
}

fn compute_declarations_graph(ctx: &TransformCtx) -> DiGraphMap<ItemId, ()> {
    let mut deps = Deps::default();
    // Start from the items selected as starting points. We've mostly only translated items
    // accessible from those, but some passes render items inaccessible again, which we filter out
    // here.
    deps.unprocessed = ctx
        .translated
        .all_items()
        .filter(|item| item.item_meta().name.is_builtin() || item.item_meta().started_from)
        .map(|item| item.id())
        .collect();

    // Explore reachable items.
    while let Some(id) = deps.unprocessed.pop() {
        if deps.visited.insert(id)
            && let Some(item) = ctx.translated.get_item(id)
        {
            let mut visitor = deps.visitor_for_item(ctx, item);
            item.drive(&mut visitor);
        }
    }
    deps.graph
}

fn compute_reordered_decls(ctx: &mut TransformCtx) -> Vec<DeclarationGroup> {
    // Build the graph of dependencies between items.
    let graph = compute_declarations_graph(ctx);

    // Pre-sort files to limit the number of costly string comparisons. Maps file ids to an index
    // that reflects ordering on the crates (with `core` and `std` sorted first) and file names.
    let sorted_file_ids: IndexMap<FileId, usize> = ctx
        .translated
        .files
        .indices()
        .sorted_by_cached_key(|&file_id| {
            let file = &ctx.translated.files[file_id];
            let is_std = file.crate_name == "std" || file.crate_name == "core";
            (!is_std, &file.crate_name, &file.name)
        })
        .enumerate()
        .sorted_by_key(|(_i, file_id)| *file_id)
        .map(|(i, _file_id)| i)
        .collect();
    assert_eq!(ctx.translated.files.len(), sorted_file_ids.slot_count());

    // We sort items as follows: std items, then items from foreign crates (sorted by crate name),
    // then local items. Within a crate, we sort by file then by source order.
    let sort_by = |item: &ItemRef| {
        let item_meta = item.item_meta();
        let span = item_meta.span.data();
        let file_name_order = sorted_file_ids.get(span.file_id);
        (
            item_meta.is_local,
            file_name_order,
            span.beg,
            item_meta.name.mono_args().cloned(),
            item.id(),
        )
    };
    // We record for each item the order in which we're sorting it, to make `sort_by` cheap.
    let item_sorted_index: HashMap<ItemId, usize> = ctx
        .translated
        .all_items()
        .sorted_by_cached_key(sort_by)
        .enumerate()
        .map(|(i, item)| (item.id(), i))
        .collect();
    let sort_by = |id: &ItemId| item_sorted_index.get(id).unwrap();

    // Compute SCCs (Strongly Connected Components) for the graph in a way that matches the chosen
    // order as much as possible.
    let reordered_sccs = super::sccs::ordered_scc(&graph, sort_by);

    // Convert to a list of declarations.
    let reordered_decls = reordered_sccs
        .into_iter()
        // This can happen if we failed to translate the item in this group.
        .filter(|scc| !scc.is_empty())
        .map(|scc| {
            // If an SCC has length one, the declaration may be simply recursive: we determine whether
            // it is the case by checking if the def id is in its own set of dependencies.
            // Trait declarations often refer to `Self`, which means they are often considered as
            // recursive by our analysis. So we cheat an declare them non-recursive.
            // TODO: do something more precise. What is important is that we never use the "whole" self
            // clause as argument, but rather projections over the self clause (like `<Self as
            // Foo>::u`, in the declaration for `Foo`).
            let id0 = scc[0];
            let is_non_rec =
                scc.len() == 1 && (id0.is_trait_decl() || !graph.neighbors(id0).contains(&id0));

            DeclarationGroup::make_group(!is_non_rec, scc)
        })
        .collect();

    trace!("{:?}", reordered_decls);
    reordered_decls
}

pub struct Transform;
impl TransformPass for Transform {
    fn should_run(&self, options: &TranslateOptions) -> bool {
        !options.no_reorder_decls
    }

    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let reordered_decls = compute_reordered_decls(ctx);
        ctx.translated.ordered_decls = Some(reordered_decls);
    }
}
