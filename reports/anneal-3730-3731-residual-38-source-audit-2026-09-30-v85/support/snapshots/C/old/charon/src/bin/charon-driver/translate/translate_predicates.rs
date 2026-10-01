use super::translate_ctx::*;
use crate::hax;
use charon_lib::{ast::*, ids::IndexVec};
use rustc_type_ir::Interner;

impl<'tcx> TranslateCtx<'tcx> {
    pub fn recognize_builtin_impl(
        &self,
        trait_data: &hax::BuiltinTraitData,
        trait_def: &hax::FullDef<'tcx>,
    ) -> Option<BuiltinImplData> {
        Some(match trait_data {
            hax::BuiltinTraitData::Destruct(x) => {
                match x {
                    hax::DestructData::Noop => BuiltinImplData::NoopDestruct,
                    hax::DestructData::Implicit => BuiltinImplData::UntrackedDestruct,
                    // This is unconditionally replaced by a `TraitImpl`.
                    hax::DestructData::Glue { .. } => return None,
                }
            }
            hax::BuiltinTraitData::Auto => BuiltinImplData::Auto,
            hax::BuiltinTraitData::Other => {
                use rustc_type_ir::lang_items::SolverTraitLangItem;
                // The ones for which we return `None` are those I don't think would show up in a
                // builtin impl.
                match self
                    .tcx
                    .as_trait_lang_item(trait_def.def_id().real_rust_def_id())?
                {
                    SolverTraitLangItem::AsyncFn => BuiltinImplData::AsyncFn,
                    SolverTraitLangItem::AsyncFnKindHelper => return None,
                    SolverTraitLangItem::AsyncFnMut => BuiltinImplData::AsyncFnMut,
                    SolverTraitLangItem::AsyncFnOnce => BuiltinImplData::AsyncFnOnce,
                    SolverTraitLangItem::AsyncIterator => return None,
                    SolverTraitLangItem::BikeshedGuaranteedNoDrop => return None,
                    SolverTraitLangItem::Clone => BuiltinImplData::Clone,
                    SolverTraitLangItem::Copy => BuiltinImplData::Copy,
                    SolverTraitLangItem::Coroutine => BuiltinImplData::Coroutine,
                    SolverTraitLangItem::Destruct => BuiltinImplData::UntrackedDestruct,
                    SolverTraitLangItem::DiscriminantKind => BuiltinImplData::DiscriminantKind,
                    SolverTraitLangItem::Drop => return None,
                    SolverTraitLangItem::Field => return None,
                    SolverTraitLangItem::Fn => BuiltinImplData::Fn,
                    SolverTraitLangItem::FnMut => BuiltinImplData::FnMut,
                    SolverTraitLangItem::FnOnce => BuiltinImplData::FnOnce,
                    SolverTraitLangItem::FnPtrTrait => BuiltinImplData::FnPtr,
                    SolverTraitLangItem::FusedIterator => return None,
                    SolverTraitLangItem::Future => BuiltinImplData::Future,
                    SolverTraitLangItem::Iterator => return None,
                    SolverTraitLangItem::MetaSized => BuiltinImplData::MetaSized,
                    SolverTraitLangItem::PointeeSized => BuiltinImplData::PointeeSized,
                    SolverTraitLangItem::PointeeTrait => BuiltinImplData::Pointee,
                    SolverTraitLangItem::Sized => BuiltinImplData::Sized,
                    SolverTraitLangItem::TransmuteTrait => BuiltinImplData::Transmute,
                    SolverTraitLangItem::TrivialClone => BuiltinImplData::Auto,
                    SolverTraitLangItem::Tuple => BuiltinImplData::Tuple,
                    SolverTraitLangItem::Unpin => BuiltinImplData::Auto,
                    SolverTraitLangItem::Unsize => BuiltinImplData::Unsize,
                }
            }
        })
    }
}

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// Translates the given predicates and stores them as resuired preciates of the innermost
    /// binder.
    ///
    /// This function should be called **after** we translated the generics (type parameters,
    /// regions...).
    pub(crate) fn register_predicates(
        &mut self,
        preds: &hax::GenericPredicates,
        origin: PredicateOrigin,
    ) -> Result<(), Error> {
        self.translate_predicates(preds, origin, None)?;
        Ok(())
    }

    /// Translates the given predicates. This function should be called **after** we translated the
    /// generics (type parameters, regions...).
    pub(crate) fn translate_predicates(
        &mut self,
        preds: &hax::GenericPredicates,
        origin: PredicateOrigin,
        // Either put clauses there or in the innermost binder.
        mut trait_clauses: Option<&mut IndexVec<TraitClauseId, TraitParam>>,
    ) -> Result<(), Error> {
        if trait_clauses.is_none() {
            // Register the mapping from trait preds to their id early on, as these can be mentioned
            // while translating any other predicate including themselves. Each trait pred gives rise
            // to exactly one trait clause inserted into `trait_clauses`, which we use to compute
            // clause ids.
            let next_clause_id = self.innermost_generics_mut().trait_clauses.next_idx();
            for (i, pred) in preds
                .predicates
                .iter()
                .filter(|pred| {
                    matches!(
                        pred.clause.kind.hax_skip_binder_ref(),
                        hax::ClauseKind::Trait(_)
                    )
                })
                .enumerate()
            {
                self.innermost_binder_mut()
                    .trait_preds
                    .insert(pred.id.clone(), next_clause_id + i);
            }
        }

        for pred in &preds.predicates {
            self.translate_predicate(pred, origin.clone(), trait_clauses.as_deref_mut())?;
        }
        Ok(())
    }

    pub(crate) fn translate_poly_trait_ref(
        &mut self,
        span: Span,
        bound_trait_ref: &hax::Binder<hax::TraitRef>,
    ) -> Result<PolyTraitDeclRef, Error> {
        self.translate_region_binder(span, bound_trait_ref, move |ctx, trait_ref| {
            ctx.translate_trait_ref(span, trait_ref)
        })
    }

    pub(crate) fn translate_trait_predicate(
        &mut self,
        span: Span,
        trait_pred: &hax::TraitPredicate,
    ) -> Result<TraitDeclRef, Error> {
        // we don't handle negative trait predicates.
        assert!(trait_pred.is_positive);
        self.translate_trait_ref(span, &trait_pred.trait_ref)
    }

    pub(crate) fn translate_trait_ref(
        &mut self,
        span: Span,
        trait_ref: &hax::TraitRef,
    ) -> Result<TraitDeclRef, Error> {
        self.translate_trait_decl_ref(span, trait_ref)
    }

    pub(crate) fn translate_predicate(
        &mut self,
        pred: &hax::GenericPredicate,
        origin: PredicateOrigin,
        // Either put clauses there or in the innermost binder.
        mut trait_clauses: Option<&mut IndexVec<TraitClauseId, TraitParam>>,
    ) -> Result<(), Error> {
        use crate::hax::ClauseKind;
        let clause = &pred.clause;
        trace!("{:?}", clause);
        let span = self.translate_span(&pred.span);
        match clause.kind.hax_skip_binder_ref() {
            ClauseKind::Trait(trait_pred) => {
                let trait_pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    ctx.translate_trait_predicate(span, trait_pred)
                })?;
                let clause_id = trait_clauses
                    .as_deref_mut()
                    .unwrap_or(&mut self.innermost_generics_mut().trait_clauses)
                    .push_with(|clause_id| TraitParam {
                        clause_id,
                        origin,
                        span: Some(span),
                        trait_: trait_pred,
                    });

                if trait_clauses.is_none() {
                    // Sanity check.
                    let expected_clause_id = self
                        .innermost_binder_mut()
                        .trait_preds
                        .get(&pred.id)
                        .unwrap();
                    debug_assert_eq!(clause_id, *expected_clause_id);
                }
            }
            ClauseKind::RegionOutlives(p) => {
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let r0 = ctx.translate_region(span, &p.lhs)?;
                    let r1 = ctx.translate_region(span, &p.rhs)?;
                    Ok(OutlivesPred(r0, r1))
                })?;
                self.innermost_generics_mut().regions_outlive.push(pred);
            }
            ClauseKind::TypeOutlives(p) => {
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let ty = ctx.translate_ty(span, &p.lhs)?;
                    let r = ctx.translate_region(span, &p.rhs)?;
                    Ok(OutlivesPred(ty, r))
                })?;
                self.innermost_generics_mut().types_outlive.push(pred);
            }
            ClauseKind::Projection(p) => {
                // This is used to express constraints over associated types.
                // For instance:
                // ```
                // T : Foo<S = String>
                //         ^^^^^^^^^^
                // ```
                let pred = self.translate_region_binder(span, &clause.kind, |ctx, _| {
                    let trait_ref = ctx.translate_trait_proof(span, &p.trait_proof)?;
                    let ty = ctx.translate_ty(span, &p.ty)?;
                    let type_id =
                        ctx.translate_assoc_type_id(trait_ref.trait_id(), &p.assoc_item.def_id)?;
                    Ok(TraitTypeConstraint {
                        trait_ref,
                        type_id,
                        ty,
                    })
                })?;
                self.innermost_generics_mut()
                    .trait_type_constraints
                    .push(pred);
            }
            ClauseKind::ConstArgHasType(..) => {
                // These are used for trait resolution to get access to the type of const generics.
                // We don't need them.
            }
            ClauseKind::HostEffect(..) => {
                // These are used for `const Trait` clauses. Part of the `const_traits` unstable
                // features. We ignore them for now.
            }
            ClauseKind::WellFormed(..) | ClauseKind::ConstEvaluatable(..) => {
                // This is e.g. a clause `[(); N+1]:` (without anything after the `:`). This is
                // used to require that the fallible `N+1` expression succeeds, so that it can be
                // used at the type level. Part of the `generic_const_exprs` unstable feature.
            }
            ClauseKind::UnstableFeature(..) => {
                // Unclear what this means, related to stability markers which we don't care about.
            }
            #[expect(unreachable_patterns)]
            kind => raise_error!(self, span, "Unsupported clause: {:?}", kind),
        }
        Ok(())
    }

    pub(crate) fn translate_trait_proofs(
        &mut self,
        span: Span,
        impl_sources: &[hax::TraitProof],
    ) -> Result<IndexVec<TraitClauseId, TraitRef>, Error> {
        impl_sources
            .iter()
            .map(|x| self.translate_trait_proof(span, x))
            .try_collect()
    }

    #[tracing::instrument(skip(self, span, trait_proof))]
    pub(crate) fn translate_trait_proof(
        &mut self,
        span: Span,
        trait_proof: &hax::TraitProof,
    ) -> Result<TraitRef, Error> {
        let trait_decl_ref = self.translate_poly_trait_ref(span, &trait_proof.pred)?;

        match self.translate_trait_proof_aux(span, trait_proof, trait_decl_ref.clone()) {
            Ok(res) => Ok(res),
            Err(err) => {
                register_error!(self, span, "Error during trait resolution: {}", &err.msg);
                Ok(TraitRef::new(
                    TraitRefKind::Unknown(err.msg),
                    trait_decl_ref,
                ))
            }
        }
    }

    pub(crate) fn translate_trait_proof_aux(
        &mut self,
        span: Span,
        impl_source: &hax::TraitProof,
        trait_decl_ref: PolyTraitDeclRef,
    ) -> Result<TraitRef, Error> {
        trace!("trait_proof: {:#?}", impl_source);
        use crate::hax::DestructData;
        use crate::hax::TraitProofKind;

        let kind = match &impl_source.kind {
            TraitProofKind::Concrete(item) => {
                let impl_ref =
                    self.translate_trait_impl_ref(span, item, TraitImplSource::Normal)?;
                TraitRefKind::TraitImpl(impl_ref)
            }
            TraitProofKind::SelfProof => TraitRefKind::SelfId,
            TraitProofKind::LocalBound(id) => match self.lookup_clause_var(span, id) {
                Ok(var) => TraitRefKind::Clause(var),
                Err(err) => TraitRefKind::Unknown(err.msg),
            },
            TraitProofKind::Derived {
                base,
                path: path_elem,
            } => {
                let trait_ref = self.translate_trait_proof(span, base)?;
                let trait_ref = Box::new(trait_ref);
                match path_elem {
                    hax::TraitProofImpliedPredicate::AssocItem { item, index, .. } => {
                        let assoc_type_id =
                            self.translate_assoc_type_id(trait_ref.trait_id(), &item.def_id)?;
                        TraitRefKind::ItemClause(
                            trait_ref,
                            assoc_type_id,
                            TraitClauseId::new(*index),
                        )
                    }
                    hax::TraitProofImpliedPredicate::Parent { index, .. } => {
                        TraitRefKind::ParentClause(trait_ref, TraitClauseId::new(*index))
                    }
                }
            }
            TraitProofKind::Dyn => TraitRefKind::Dyn,
            TraitProofKind::Builtin {
                trait_data,
                proofs: trait_proofs,
                types,
                ..
            } => {
                let tref = &impl_source.pred;
                let trait_def = self.poly_hax_def(&tref.hax_skip_binder_ref().def_id)?;
                if let hax::FullDefKind::TraitAlias { .. } = trait_def.kind() {
                    // We reuse the same `def_id` to generate a blanket impl for the trait.
                    let mut impl_ref: TraitImplRef = self.translate_item(
                        span,
                        &tref.hax_skip_binder_ref().erase(self.hax_state_with_id()),
                        TransItemSourceKind::TraitImpl(TraitImplSource::TraitAlias),
                    )?;
                    assert!(
                        impl_ref.generics.trait_refs.is_empty(),
                        "found trait alias with non-empty required predicates"
                    );
                    impl_ref.generics.trait_refs =
                        self.translate_trait_proofs(span, trait_proofs)?;
                    TraitRefKind::TraitImpl(impl_ref)
                } else if let hax::BuiltinTraitData::Destruct(DestructData::Glue { ty, .. }) =
                    trait_data
                {
                    let (hax::TyKind::Adt(item)
                    | hax::TyKind::Closure(hax::ClosureArgs { item, .. })
                    | hax::TyKind::Array(item)
                    | hax::TyKind::Slice(item)
                    | hax::TyKind::Tuple(item)) = ty.kind()
                    else {
                        raise_error!(self, span, "failed to translate drop glue for type {ty:?}")
                    };
                    TraitRefKind::TraitImpl(self.translate_trait_impl_ref(
                        span,
                        item,
                        TraitImplSource::ImplicitDestruct,
                    )?)
                } else {
                    let Some(builtin_data) = self.recognize_builtin_impl(trait_data, &trait_def)
                    else {
                        raise_error!(
                            self,
                            span,
                            "found a built-in trait impl we did not recognize: \
                            {:?} (lang_item={:?})",
                            trait_def.def_id(),
                            trait_def.lang_item,
                        )
                    };
                    // TODO: here, if closure_ty is a FnDef, we need to generate the matching trait
                    // impls, with an empty state as the first argument.
                    if let Some(closure_kind) = builtin_data.as_closure_kind()
                        && let Some(hax::GenericArg::Type(closure_ty)) =
                            impl_source.pred.hax_skip_binder_ref().generic_args.first()
                        && let hax::TyKind::Closure(closure_args) = closure_ty.kind()
                    {
                        let binder =
                            self.translate_region_binder(span, &impl_source.pred, |ctx, _tref| {
                                ctx.translate_closure_impl_ref(span, closure_args, closure_kind)
                            })?;
                        TraitRefKind::TraitImpl(self.erase_region_binder(binder))
                    } else {
                        let parent_trait_refs = self.translate_trait_proofs(span, trait_proofs)?;
                        let types: IndexMap<AssocTypeId, _> = if self.monomorphize() {
                            IndexMap::new()
                        } else {
                            let tdecl_id = trait_decl_ref.skip_binder.id;
                            let mut type_map = IndexMap::new();
                            for (def_id, ty, trait_proofs) in types {
                                let assoc_type_id =
                                    self.translate_assoc_type_id(tdecl_id, def_id)?;
                                let assoc_ty = TraitAssocTyImpl {
                                    value: self.translate_ty(span, ty)?,
                                    implied_trait_refs: self
                                        .translate_trait_proofs(span, trait_proofs)?,
                                };
                                type_map.set_slot_extend(assoc_type_id, assoc_ty);
                            }
                            type_map
                        };
                        TraitRefKind::BuiltinOrAuto {
                            builtin_data,
                            parent_trait_refs,
                            types,
                        }
                    }
                }
            }
            TraitProofKind::Error(msg) => {
                if self.error_on_trait_proof_error {
                    register_error!(self, span, "Error during trait resolution: {}", msg);
                }
                TraitRefKind::Unknown(msg.clone())
            }
        };
        Ok(TraitRef::new(kind, trait_decl_ref))
    }
}
