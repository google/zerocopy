use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::fmt::Debug;
use std::mem;

use crate::hax;
use crate::hax::{BaseState, Symbol};
use rustc_middle::ty;
use rustc_span::def_id::DefId as RDefId;

use super::translate_ctx::{ItemTransCtx, TransImplSource, TransItemSourceKind};
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use charon_lib::utils::CycleDetector;

/// A level of binding for type-level variables. Each item has a top-level binding level
/// corresponding to the parameters and clauses to the items. We may then encounter inner binding
/// levels in the following cases:
/// - `for<..>` binders in predicates;
/// - `fn<..>` function pointer types;
/// - `dyn Trait` types, represented as `dyn<T: Trait>`;
/// - types in a trait declaration or implementation block;
/// - methods in a trait declaration or implementation block.
///
/// At each level, we store two things: a `GenericParams` that contains the parameters bound at
/// this level, and various maps from the rustc-internal indices to our indices.
#[derive(Debug, Default)]
pub(crate) struct BindingLevel {
    /// Whether this binding level exists in Hax's De Bruijn indices. `dyn Trait` introduces an
    /// existential binder in Charon that has no corresponding binder in rustc/Hax.
    pub is_hax_binder: bool,
    /// The definition whose generics this binding level contains, if this is an item binder.
    pub def_id: Option<hax::DefId>,
    /// Dummy rustc `DefId` that we use to `liberate_bound_regions` for our synthetic fn pointer items.
    pub late_bound_scope_alias: Option<RDefId>,
    /// The parameters and predicates bound at this level.
    pub params: GenericParams,
    /// Rust makes the distinction between early and late-bound region parameters. We do not make
    /// this distinction, and merge early and late bound regions. For details, see:
    /// <https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/>
    /// <https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/>
    ///
    /// The map from rust early regions to translated region indices.
    pub early_region_vars: HashMap<hax::EarlyParamRegion, RegionId>,
    /// The map from rust named region parameter ids to translated region indices.
    pub region_vars_by_def_id: HashMap<hax::DefId, RegionId>,
    /// The map from rust late/bound regions to translated region indices.
    pub bound_region_vars: Vec<RegionId>,
    /// Region added for the lifetime bound in the signature of the `call`/`call_mut` methods.
    pub closure_call_method_region: Option<RegionId>,
    /// Region added for the borrow accepted by a drop glue method or vtable drop shim.
    pub drop_glue_region: Option<RegionId>,
    /// The map from rust type variable indices to translated type variable indices.
    pub type_vars_map: HashMap<u32, TypeVarId>,
    /// The map from rust const generic variables to translated const generic variable indices.
    pub const_generic_vars_map: HashMap<u32, ConstGenericVarId>,
    /// The map from trait predicates to translated trait clause indices.
    pub trait_preds: HashMap<hax::GenericPredicateId, TraitClauseId>,
    /// The types of the captured variables, when we're translating a closure item. This is
    /// translated early because this translation requires adding new lifetime generics to the
    /// current binder.
    pub closure_upvar_tys: Option<IndexVec<FieldId, Ty>>,
    /// The regions we added for the upvars.
    pub closure_upvar_regions: Vec<RegionId>,
    /// RPITIT can cause region names to be reused. To avoid clashes in our output, we rename
    /// duplicate names.
    pub used_region_names: HashSet<Symbol>,
    /// Cache the translation of types. This harnesses the deduplication of `Ty` that hax does.
    // Important: we can't reuse type caches from earlier binders as the new binder may change what
    // a given variable resolves to.
    pub type_trans_cache: HashMap<hax::Ty, Ty>,
}

/// Small helper: we ignore some region names (when they are equal to "'_")
fn translate_region_name(s: hax::Symbol) -> Option<String> {
    let s = s.to_string();
    if s == "'_" { None } else { Some(s) }
}

fn translate_variance(variance: Option<&hax::Variance>) -> Variance {
    match variance {
        Some(hax::Variance::Covariant) => Variance::Covariant,
        Some(hax::Variance::Invariant) => Variance::Invariant,
        Some(hax::Variance::Contravariant) => Variance::Contravariant,
        Some(hax::Variance::Bivariant) => Variance::Bivariant,
        None => Variance::Unknown,
    }
}

impl BindingLevel {
    pub(crate) fn new(def_id: Option<hax::DefId>) -> Self {
        Self {
            def_id,
            is_hax_binder: true,
            ..Default::default()
        }
    }

    pub(crate) fn new_dyn() -> Self {
        let mut level = Self::new(None);
        level.is_hax_binder = false;
        level
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_early_region(
        &mut self,
        region: hax::EarlyParamRegion,
        def_id: hax::DefId,
        variance: Variance,
        mutability: LifetimeMutability,
    ) -> RegionId {
        let name = if self.used_region_names.insert(region.name) {
            translate_region_name(region.name)
        } else {
            None
        };
        // Check that there are no late-bound regions
        assert!(
            self.bound_region_vars.is_empty(),
            "Early regions must be translated before late ones"
        );
        let rid = self.params.regions.push_with(|index| RegionParam {
            index,
            name,
            variance,
            mutability,
        });
        self.early_region_vars.insert(region, rid);
        self.region_vars_by_def_id.insert(def_id, rid);
        rid
    }

    /// Important: we must push all the early-bound regions before pushing any other region.
    pub(crate) fn push_bound_region(
        &mut self,
        region: hax::BoundRegionKind,
        variance: Variance,
    ) -> RegionId {
        use crate::hax::BoundRegionKind::*;
        let (name, def_id) = match region {
            Anon => (None, None),
            NamedForPrinting(symbol) => (translate_region_name(symbol), None),
            Named(def_id, symbol) => (translate_region_name(symbol), Some(def_id)),
            ClosureEnv => (Some("@env".to_owned()), None),
        };
        let rid = self
            .params
            .regions
            .push_with(|index| RegionParam::new(index, name, variance));
        self.bound_region_vars.push(rid);
        if let Some(def_id) = def_id {
            self.region_vars_by_def_id.insert(def_id, rid);
        }
        rid
    }

    /// Add a region for an upvar in a closure.
    pub fn push_upvar_region(&mut self) -> RegionId {
        // We musn't push to `bound_region_vars` because that will contain the higher-kinded
        // signature lifetimes (if any) and they must be lookup-able.
        let region_id = self
            .params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Unknown));
        self.closure_upvar_regions.push(region_id);
        region_id
    }

    pub fn push_drop_glue_region(&mut self) -> RegionId {
        let region_id = self
            .params
            .regions
            .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
        self.drop_glue_region = Some(region_id);
        region_id
    }

    pub(crate) fn push_type_var(
        &mut self,
        rid: u32,
        name: hax::Symbol,
        variance: Variance,
    ) -> TypeVarId {
        // Type vars comping from `impl Trait` arguments have as their name the whole `impl Trait`
        // expression. We turn it into an identifier.
        let mut name = name.to_string();
        if name
            .chars()
            .any(|c| !(c.is_ascii_alphanumeric() || c == '_'))
        {
            name = format!("T{rid}")
        }
        let var_id = self.params.types.push_with(|index| TypeParam {
            index,
            name,
            variance,
        });
        self.type_vars_map.insert(rid, var_id);
        var_id
    }

    pub(crate) fn push_const_generic_var(&mut self, rid: u32, ty: Ty, name: hax::Symbol) {
        let var_id = self
            .params
            .const_generics
            .push_with(|index| ConstGenericParam {
                index,
                name: name.to_string(),
                ty,
            });
        self.const_generic_vars_map.insert(rid, var_id);
    }

    /// Translate a binder of regions by appending the stored reguions to the given vector.
    pub(crate) fn push_params_from_binder(&mut self, binder: hax::Binder<()>) -> Result<(), Error> {
        assert!(
            self.bound_region_vars.is_empty(),
            "Trying to use two binders at the same binding level"
        );
        use crate::hax::BoundVariableKind::*;
        for p in binder.bound_vars {
            match p {
                Region(region, variance) => {
                    let variance = translate_variance(variance.as_ref());
                    self.push_bound_region(region, variance);
                }
                Ty(_) => {
                    panic!("Unexpected locally bound type variable");
                }
                Const => {
                    panic!("Unexpected locally bound const generic variable");
                }
            }
        }
        Ok(())
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder(&self) -> &BindingLevel {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder()
    }
    /// Get the only binding level. Panics if there are other binding levels.
    pub(crate) fn the_only_binder_mut(&mut self) -> &mut BindingLevel {
        assert_eq!(self.binding_levels.len(), 1);
        self.innermost_binder_mut()
    }

    pub(crate) fn outermost_binder(&self) -> &BindingLevel {
        self.binding_levels.outermost()
    }
    pub(crate) fn outermost_binder_mut(&mut self) -> &mut BindingLevel {
        self.binding_levels.outermost_mut()
    }
    pub(crate) fn innermost_binder(&self) -> &BindingLevel {
        self.binding_levels.innermost()
    }
    pub(crate) fn innermost_binder_mut(&mut self) -> &mut BindingLevel {
        self.binding_levels.innermost_mut()
    }

    pub(crate) fn outermost_generics(&self) -> &GenericParams {
        &self.outermost_binder().params
    }
    #[expect(dead_code)]
    pub(crate) fn outermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.outermost_binder_mut().params
    }
    #[expect(dead_code)]
    pub(crate) fn innermost_generics(&self) -> &GenericParams {
        &self.innermost_binder().params
    }
    pub(crate) fn innermost_generics_mut(&mut self) -> &mut GenericParams {
        &mut self.innermost_binder_mut().params
    }

    pub(crate) fn lookup_bound_region(
        &mut self,
        span: Span,
        hax_dbid: hax::DebruijnIndex,
        var: hax::BoundVar,
    ) -> Result<RegionDbVar, Error> {
        if let Some((charon_dbid, level)) = self
            .binding_levels
            .iter_enumerated()
            .filter(|(_, l)| l.is_hax_binder)
            .nth(hax_dbid)
            && let Some(rid) = level.bound_region_vars.get(var)
        {
            Ok(DeBruijnVar::bound(charon_dbid, *rid))
        } else {
            raise_error!(
                self,
                span,
                "Unexpected error: could not find region '{hax_dbid}_{var}"
            )
        }
    }

    pub(crate) fn lookup_param<Id: Copy>(
        &mut self,
        span: Span,
        f: impl for<'a> Fn(&'a BindingLevel) -> Option<Id>,
        mk_err: impl FnOnce() -> String,
    ) -> Result<DeBruijnVar<Id>, Error> {
        for (dbid, bl) in self.binding_levels.iter_enumerated() {
            if let Some(id) = f(bl) {
                return Ok(DeBruijnVar::bound(dbid, id));
            }
        }
        let err = mk_err();
        raise_error!(self, span, "Unexpected error: could not find {}", err)
    }

    pub(crate) fn lookup_early_region(
        &mut self,
        span: Span,
        region: &hax::EarlyParamRegion,
    ) -> Result<RegionDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.early_region_vars.get(region).copied(),
            || format!("the region variable {region:?}"),
        )
    }

    pub(crate) fn lookup_late_param_region(
        &mut self,
        span: Span,
        region: &hax::LateParamRegion,
    ) -> Result<RegionDbVar, Error> {
        use hax::LateParamRegionKind::*;
        match &region.kind {
            Anon(index) | NamedAnon(index, _) => {
                let Some((dbid, binder)) =
                    self.binding_levels.iter_enumerated().find(|(_, binder)| {
                        binder.def_id.as_ref() == Some(&region.scope)
                            || binder.late_bound_scope_alias == region.scope.as_real_def_id()
                    })
                else {
                    raise_error!(
                        self,
                        span,
                        "Unexpected error: could not find the binder for late-bound region {region:?}"
                    )
                };
                let Some(region_id) = binder.bound_region_vars.get(*index as usize).copied() else {
                    raise_error!(
                        self,
                        span,
                        "Unexpected error: could not find the late-bound region variable {region:?}"
                    )
                };
                Ok(DeBruijnVar::bound(dbid, region_id))
            }
            Named(def_id, _) => self.lookup_param(
                span,
                |bl| bl.region_vars_by_def_id.get(def_id).copied(),
                || format!("the late-bound region variable {region:?}"),
            ),
            ClosureEnv => {
                raise_error!(self, span, "Unexpected late-bound region: {region:?}")
            }
        }
    }

    pub(crate) fn lookup_type_var(
        &mut self,
        span: Span,
        param: &hax::ParamTy,
    ) -> Result<TypeDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.type_vars_map.get(&param.index).copied(),
            || format!("the type variable {}", param.name),
        )
    }

    pub(crate) fn lookup_const_generic_var(
        &mut self,
        span: Span,
        param: &hax::ParamConst,
    ) -> Result<ConstGenericDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.const_generic_vars_map.get(&param.index).copied(),
            || format!("the const generic variable {}", param.name),
        )
    }

    pub(crate) fn lookup_clause_var(
        &mut self,
        span: Span,
        id: &hax::GenericPredicateId,
    ) -> Result<ClauseDbVar, Error> {
        self.lookup_param(
            span,
            |bl| bl.trait_preds.get(id).copied(),
            || format!("the trait clause variable {id:?}"),
        )
    }

    pub(crate) fn push_generic_params(&mut self, generics: &hax::TyGenerics) -> Result<(), Error> {
        for param in &generics.params {
            self.push_generic_param(param)?;
        }
        Ok(())
    }

    pub(crate) fn push_generic_param(&mut self, param: &hax::GenericParamDef) -> Result<(), Error> {
        let variance = translate_variance(param.variance.as_ref());
        match &param.kind {
            hax::GenericParamDefKind::Lifetime => {
                let region = hax::EarlyParamRegion {
                    index: param.index,
                    name: param.name,
                };
                let mutability = self
                    .t_ctx
                    .lt_mutability_computer
                    .compute_lifetime_mutability(
                        &self.hax_state,
                        self.item_src.def_id(),
                        param.index,
                    );
                let _ = self.innermost_binder_mut().push_early_region(
                    region,
                    param.def_id.clone(),
                    variance,
                    mutability,
                );
            }
            hax::GenericParamDefKind::Type { .. } => {
                let _ =
                    self.innermost_binder_mut()
                        .push_type_var(param.index, param.name, variance);
            }
            hax::GenericParamDefKind::Const { ty, .. } => {
                let span = self.def_span(&param.def_id);
                // The type should be primitive, meaning it shouldn't contain variables,
                // non-primitive adts, etc. As a result, we can use an empty context.
                let ty = self.translate_ty(span, ty)?;
                self.innermost_binder_mut()
                    .push_const_generic_var(param.index, ty, param.name);
            }
        }

        Ok(())
    }

    // The parameters (and in particular the lifetimes) are split between
    // early bound and late bound parameters. See those blog posts for explanations:
    // https://smallcultfollowing.com/babysteps/blog/2013/10/29/intermingled-parameter-lists/
    // https://smallcultfollowing.com/babysteps/blog/2013/11/04/intermingled-parameter-lists/
    // Note that only lifetimes can be late bound at the moment.
    //
    // [TyCtxt.generics_of] gives us the early-bound parameters. We add the late-bound parameters
    // here.
    fn push_late_bound_generics_for_def(
        &mut self,
        _span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<(), Error> {
        let sig = match def.kind() {
            hax::FullDefKind::Fn(f) => Some(f.sig()),
            hax::FullDefKind::FnPtr(f) => Some(f.sig()),
            hax::FullDefKind::AssocFn(f) => Some(f.sig()),
            hax::FullDefKind::Ctor(f) => Some(f.sig()),
            _ => None,
        };
        if let Some(sig) = sig {
            let innermost_binder = self.innermost_binder_mut();
            assert!(innermost_binder.bound_region_vars.is_empty());
            innermost_binder.push_params_from_binder(sig.rebind(()))?;
        }
        if let hax::FullDefKind::FnPtr(f) = def.kind() {
            self.innermost_binder_mut().late_bound_scope_alias = Some(f.late_bound_scope());
        }
        Ok(())
    }

    /// Add the generics and predicates of this item and its parents to the current context.
    #[tracing::instrument(skip(self, span, def))]
    fn push_generics_for_def(&mut self, span: Span, def: &hax::FullDef<'tcx>) -> Result<(), Error> {
        trace!("{:?}", def.param_env());
        // Add generics from the parent item, recursively (recursivity is important for closures,
        // as they can be nested). Instantiated defs have no generics, so we can skip it.
        let def_is_instantiated = self.monomorphize() && !self.item_src.kind.is_for_trait();
        if !def_is_instantiated && let Some(parent_item) = def.typing_parent(self.hax_state()) {
            let parent_def = self.hax_def(&parent_item)?;
            self.push_generics_for_def(span, &parent_def)?;
        }
        self.push_generics_for_def_without_parents(span, def)?;
        Ok(())
    }

    /// Add the generics and predicates of this item. This does not include the parent generics;
    /// use `push_generics_for_def` to get the full list.
    fn push_generics_for_def_without_parents(
        &mut self,
        _span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<(), Error> {
        if let Some(param_env) = def.param_env() {
            let origin = Self::predicate_origin_for_def(def);
            self.push_param_env_without_parents(param_env, origin)?;
        }

        Ok(())
    }

    fn predicate_origin_for_def(def: &hax::FullDef<'tcx>) -> PredicateOrigin {
        use crate::hax::FullDefKind;
        match &def.kind {
            FullDefKind::Adt(_) | FullDefKind::TyAlias(_) | FullDefKind::AssocTy(_) => {
                PredicateOrigin::WhereClauseOnType
            }
            FullDefKind::Fn(_)
            | FullDefKind::FnPtr(_)
            | FullDefKind::AssocFn(_)
            | FullDefKind::Closure(_)
            | FullDefKind::Const(_)
            | FullDefKind::AssocConst(_)
            | FullDefKind::Static(_) => PredicateOrigin::WhereClauseOnFn,
            FullDefKind::TraitImpl(_) | FullDefKind::InherentImpl(_) => {
                PredicateOrigin::WhereClauseOnImpl
            }
            FullDefKind::Trait(_) | FullDefKind::TraitAlias(_) => {
                PredicateOrigin::WhereClauseOnTrait
            }
            _ => panic!("Unexpected def: {:?}", def.def_id().kind),
        }
    }

    fn push_param_env_without_parents(
        &mut self,
        param_env: &hax::ParamEnv,
        origin: PredicateOrigin,
    ) -> Result<(), Error> {
        self.push_generic_params(&param_env.generics)?;
        self.register_predicates(&param_env.predicates, origin)?;
        Ok(())
    }

    /// Translate the generics and predicates of this item and its parents. This adds generic
    /// parameters and predicates to the current environment (as a binder in
    /// `self.binding_levels`). The constructed `GenericParams` can be recovered at the end using
    /// `self.into_generics()` and stored in the translated item.
    ///
    /// On top of the generics introduced by `push_generics_for_def`, this adds extra parameters
    /// required by the `TransItemSourceKind`.
    pub fn translate_item_generics(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        kind: &TransItemSourceKind,
    ) -> Result<(), Error> {
        assert!(self.binding_levels.is_empty());
        self.binding_levels
            .push(BindingLevel::new(Some(def.def_id().clone())));
        self.push_generics_for_def(span, def)?;
        self.push_late_bound_generics_for_def(span, def)?;

        if let hax::FullDefKind::Closure(c) = def.kind() {
            // Add the lifetime generics coming from the upvars. We translate the upvar types early
            // to know what lifetimes are needed.
            let closure_args = c.args();
            let upvar_tys = self.translate_closure_upvar_tys(span, closure_args)?;
            // Add new lifetimes params to replace the erased ones.
            let upvar_tys = upvar_tys.replace_erased_regions(|| {
                let region_id = self.the_only_binder_mut().push_upvar_region();
                Region::Var(DeBruijnVar::new_at_zero(region_id))
            });
            self.the_only_binder_mut().closure_upvar_tys = Some(upvar_tys);

            // Add the lifetime generics coming from the higher-kindedness of the signature.
            if let TransItemSourceKind::TraitImpl(TransImplSource::Callable(..))
            | TransItemSourceKind::VTableInstance(TransImplSource::Callable(..))
            | TransItemSourceKind::VTableInstanceInitializer(TransImplSource::Callable(..))
            | TransItemSourceKind::VTableDropShim(TransImplSource::Callable(..))
            | TransItemSourceKind::CallableMethod(..)
            | TransItemSourceKind::VTableMethod(TransImplSource::Callable(..))
            | TransItemSourceKind::ClosureAsFnCast = kind
            {
                self.the_only_binder_mut()
                    .push_params_from_binder(closure_args.fn_sig.rebind(()))?;
            }
        }

        if let hax::FullDefKind::Fn(_)
        | hax::FullDefKind::FnPtr(_)
        | hax::FullDefKind::AssocFn(_)
        | hax::FullDefKind::Closure(_)
        | hax::FullDefKind::Ctor(_) = def.kind()
            && let TransItemSourceKind::CallableMethod(ClosureKind::Fn | ClosureKind::FnMut)
            | TransItemSourceKind::VTableMethod(TransImplSource::Callable(
                ClosureKind::Fn | ClosureKind::FnMut,
            )) = kind
        {
            // Add the lifetime generics coming from the method itself.
            let rid = self
                .the_only_binder_mut()
                .params
                .regions
                .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
            self.the_only_binder_mut().closure_call_method_region = Some(rid);
        }

        if matches!(
            kind,
            TransItemSourceKind::DropGlueMethod(..) | TransItemSourceKind::VTableDropShim(..)
        ) {
            self.the_only_binder_mut().push_drop_glue_region();
        }

        self.innermost_binder_mut().params.check_consistency();
        Ok(())
    }

    /// Push a new binding level, run the provided function inside it, then return the bound value.
    pub(crate) fn inside_binder<F, U>(
        &mut self,
        kind: BinderKind,
        def_id: Option<hax::DefId>,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        self.binding_levels.push(BindingLevel::new(def_id));

        // Call the continuation. Important: do not short-circuit on error here.
        let res = f(self);

        // Reset
        let params = self.binding_levels.pop().unwrap().params;

        // Return
        res.map(|skip_binder| Binder {
            kind,
            params,
            skip_binder,
        })
    }

    /// Push a new binding level corresponding to the provided `def` for the duration of the inner
    /// function call.
    pub(crate) fn translate_binder_for_def<F, U>(
        &mut self,
        span: Span,
        kind: BinderKind,
        def: &hax::FullDef<'tcx>,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self) -> Result<U, Error>,
    {
        let inner_hax_state = self.t_ctx.hax_state.clone().with_hax_owner(def.def_id());
        let outer_hax_state = mem::replace(&mut self.hax_state, inner_hax_state);
        let ret = self.inside_binder(kind, Some(def.def_id().clone()), |this| {
            this.push_generics_for_def_without_parents(span, def)?;
            this.push_late_bound_generics_for_def(span, def)?;
            this.innermost_binder().params.check_consistency();
            f(this)
        });
        self.hax_state = outer_hax_state;
        ret
    }

    /// Push a new binding level corresponding to the provided item binder for the duration of the
    /// inner function call.
    pub(crate) fn translate_item_binder<F, T, U>(
        &mut self,
        _span: Span,
        kind: BinderKind,
        binder: &hax::TraitItemBinder<T>,
        predicate_origin: PredicateOrigin,
        f: F,
    ) -> Result<Binder<U>, Error>
    where
        F: FnOnce(&mut Self, &T) -> Result<U, Error>,
    {
        let inner_hax_state = self.t_ctx.hax_state.clone().with_hax_owner(&binder.def_id);
        let outer_hax_state = mem::replace(&mut self.hax_state, inner_hax_state);
        let ret = self.inside_binder(kind, Some(binder.def_id.clone()), |this| {
            this.push_param_env_without_parents(&binder.param_env, predicate_origin)?;
            this.innermost_binder_mut()
                .push_params_from_binder(binder.late_bound.clone())?;
            this.innermost_binder().params.check_consistency();
            f(this, &binder.skip_binder)
        });
        self.hax_state = outer_hax_state;
        ret
    }

    /// Push a group of bound regions and call the continuation.
    /// We use this when diving into a `for<'a>`, or inside an arrow type (because
    /// it contains universally quantified regions).
    pub(crate) fn translate_region_binder<F, T, U>(
        &mut self,
        _span: Span,
        binder: &hax::Binder<T>,
        f: F,
    ) -> Result<RegionBinder<U>, Error>
    where
        F: FnOnce(&mut Self, &T) -> Result<U, Error>,
    {
        let binder = self.inside_binder(BinderKind::Other, None, |this| {
            this.innermost_binder_mut()
                .push_params_from_binder(binder.rebind(()))?;
            f(this, binder.hax_skip_binder_ref())
        })?;
        // Convert to a region-only binder.
        Ok(RegionBinder {
            regions: binder.params.regions,
            skip_binder: binder.skip_binder,
        })
    }

    pub(crate) fn into_generics(mut self) -> GenericParams {
        assert!(self.binding_levels.len() == 1);
        self.binding_levels.pop().unwrap().params
    }
}

/// Struct to compute the "mutability" of each lifetime.
#[derive(Default)]
pub struct LifetimeMutabilityComputer {
    lt_mutability: HashMap<hax::DefId, CycleDetector<HashSet<u32>>>,
}

impl LifetimeMutabilityComputer {
    /// Compute the mutability of one lifetime.
    pub(crate) fn compute_lifetime_mutability<'tcx>(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: &hax::DefId,
        index: u32,
    ) -> LifetimeMutability {
        match self.compute_lifetime_mutabilities(s, item) {
            Some(set) => {
                if set.contains(&index) {
                    LifetimeMutability::Mutable
                } else {
                    LifetimeMutability::Shared
                }
            }
            None => LifetimeMutability::Unknown,
        }
    }

    /// Compute the "mutability" of each lifetime, i.e. whether this lifetime is used in a `&'a mut
    /// T` type or not. Returns a set of the known-mutable lifetimes for this ADT.
    fn compute_lifetime_mutabilities<'tcx>(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: &hax::DefId,
    ) -> Option<&HashSet<u32>> {
        if !matches!(
            item.kind,
            hax::DefKind::Struct | hax::DefKind::Enum | hax::DefKind::Union | hax::DefKind::FnPtr
        ) {
            return None;
        }
        if self
            .lt_mutability
            .entry(item.clone())
            .or_default()
            .start_processing()
        {
            use crate::hax::SInto;
            use ty::{TypeSuperVisitable, TypeVisitable};

            struct LtMutabilityVisitor<'a, S> {
                s: &'a S,
                computer: &'a mut LifetimeMutabilityComputer,
                set: HashSet<u32>,
            }
            impl<'tcx, S: BaseState<'tcx>> ty::TypeVisitor<ty::TyCtxt<'tcx>> for LtMutabilityVisitor<'_, S> {
                fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
                    match ty.kind() {
                        ty::Ref(r, _, ty::Mutability::Mut)
                            if let ty::RegionKind::ReEarlyParam(r) = r.kind() =>
                        {
                            self.set.insert(r.index);
                        }
                        ty::Adt(adt, args) => {
                            let item = adt.did().sinto(self.s);
                            if let Some(mutabilities) =
                                self.computer.compute_lifetime_mutabilities(self.s, &item)
                            {
                                for arg in args.iter() {
                                    if let Some(r) = arg.as_region()
                                        && let ty::RegionKind::ReEarlyParam(r) = r.kind()
                                        && mutabilities.contains(&r.index)
                                    {
                                        self.set.insert(r.index);
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                    ty.super_visit_with(self)
                }
            }
            let mut visitor = LtMutabilityVisitor {
                s,
                computer: self,
                set: HashSet::default(),
            };

            let tcx = s.base().tcx;
            if matches!(item.as_synthetic(s), Some(hax::SyntheticItem::FnPtr(_))) {
                item.type_of(s)
                    .instantiate_identity()
                    .skip_normalization()
                    .visit_with(&mut visitor);
            } else {
                let def_id = item.real_rust_def_id();
                let adt_def = tcx.adt_def(def_id);
                let generics = item.identity_args(s);
                for variant in adt_def.variants() {
                    for field in &variant.fields {
                        field.ty(tcx, generics).visit_with(&mut visitor);
                    }
                }
            }
            let set = visitor.set;

            self.lt_mutability
                .get_mut(item)
                .unwrap()
                .done_processing(set);
        }
        self.lt_mutability.get(item)?.as_processed()
    }
}
