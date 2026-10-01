use itertools::Itertools;
use rustc_middle::ty;
use rustc_span::sym;

use super::translate_ctx::*;
use crate::hax::{self, UnderOwnerState};
use crate::hax::{HasOwner, Visibility};
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn translate_sized_proof(
        &mut self,
        span: Span,
        ty: ty::Ty<'tcx>,
    ) -> Result<Option<TraitRef>, Error> {
        if self.options.hide_marker_traits {
            return Ok(None);
        }
        let proof = hax::solve_sized(&self.hax_state, ty);
        self.translate_trait_proof(span, &proof).map(Some)
    }

    /// Translate an erased region. If we're inside a body, this will return a fresh body region
    /// instead.
    pub(crate) fn translate_erased_region(&mut self) -> Region {
        if let Some(v) = &mut self.lifetime_freshener {
            Region::Body(v.push(()))
        } else {
            Region::Erased
        }
    }

    /// Erase a region binder by supplying erased lifetimes (or fresh body lifetimes) for all its
    /// arguments.
    pub(crate) fn erase_region_binder<T: TyVisitable>(&mut self, b: RegionBinder<T>) -> T {
        let regions = b
            .regions
            .map_ref_indexed(|_, _| self.translate_erased_region());
        b.apply(regions)
    }

    // Translate a region
    pub(crate) fn translate_region(
        &mut self,
        span: Span,
        region: &hax::Region,
    ) -> Result<Region, Error> {
        use crate::hax::RegionKind::*;
        match &region.kind {
            ReErased => Ok(self.translate_erased_region()),
            ReStatic => Ok(Region::Static),
            ReBound(hax::BoundVarIndexKind::Bound(id), br) => {
                Ok(match self.lookup_bound_region(span, *id, br.var) {
                    Ok(var) => Region::Var(var),
                    Err(_) => Region::Erased,
                })
            }
            ReEarlyParam(region) => Ok(match self.lookup_early_region(span, region) {
                Ok(var) => Region::Var(var),
                Err(_) => Region::Erased,
            }),
            ReLateParam(region) => Ok(Region::Var(self.lookup_late_param_region(span, region)?)),
            ReVar(..) | RePlaceholder(..) => {
                // Shouldn't exist outside of type inference.
                raise_error!(
                    self,
                    span,
                    "Should not exist outside of type inference: {region:?}"
                )
            }
            ReBound(..) | ReError(..) => {
                raise_error!(self, span, "Unexpected region kind: {region:?}")
            }
        }
    }

    pub(crate) fn translate_hax_int_ty(int_ty: &hax::IntTy) -> IntTy {
        match int_ty {
            hax::IntTy::Isize => IntTy::Isize,
            hax::IntTy::I8 => IntTy::I8,
            hax::IntTy::I16 => IntTy::I16,
            hax::IntTy::I32 => IntTy::I32,
            hax::IntTy::I64 => IntTy::I64,
            hax::IntTy::I128 => IntTy::I128,
        }
    }

    pub(crate) fn translate_hax_uint_ty(uint_ty: &hax::UintTy) -> UIntTy {
        use crate::hax::UintTy;
        match uint_ty {
            UintTy::Usize => UIntTy::Usize,
            UintTy::U8 => UIntTy::U8,
            UintTy::U16 => UIntTy::U16,
            UintTy::U32 => UIntTy::U32,
            UintTy::U64 => UIntTy::U64,
            UintTy::U128 => UIntTy::U128,
        }
    }

    /// Translate a Ty.
    ///
    /// Typically used in this module to translate the fields of a structure/
    /// enumeration definition, or later to translate the type of a variable.
    ///
    /// Note that we take as parameter a function to translate regions, because
    /// regions can be translated in several manners (non-erased region or erased
    /// regions), in which case the return type is different.
    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_ty(&mut self, span: Span, hax_ty: &hax::Ty) -> Result<Ty, Error> {
        let mut ty = if let Some(ty) = self
            .innermost_binder()
            .type_trans_cache
            .get(hax_ty)
            .cloned()
        {
            ty
        } else {
            let ty = self
                .translate_ty_inner(span, hax_ty)
                .unwrap_or_else(|e| TyKind::Error(e.msg).into_ty());
            self.innermost_binder_mut()
                .type_trans_cache
                .insert(hax_ty.clone(), ty.clone());
            ty
        };
        if let Some(v) = &mut self.lifetime_freshener {
            // We might be reusing a value from cache: we must refresh the erased & body regions.
            ty = ty.replace_erased_regions(|| Region::Body(v.push(())));
        }
        Ok(ty)
    }

    fn translate_ty_inner(&mut self, span: Span, ty: &hax::Ty) -> Result<Ty, Error> {
        trace!("{:?}", ty);
        let kind = match ty.kind() {
            hax::TyKind::Bool => TyKind::Scalar(ScalarTy::Bool),
            hax::TyKind::Char => TyKind::Scalar(ScalarTy::Char),
            hax::TyKind::Int(int_ty) => TyKind::Scalar(ScalarTy::Integer(IntegerTy::Signed(
                Self::translate_hax_int_ty(int_ty),
            ))),
            hax::TyKind::Uint(uint_ty) => TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(
                Self::translate_hax_uint_ty(uint_ty),
            ))),
            hax::TyKind::Float(float_ty) => TyKind::Scalar(ScalarTy::Float(match float_ty {
                hax::FloatTy::F16 => FloatTy::F16,
                hax::FloatTy::F32 => FloatTy::F32,
                hax::FloatTy::F64 => FloatTy::F64,
                hax::FloatTy::F128 => FloatTy::F128,
            })),
            hax::TyKind::Never => TyKind::Never,

            hax::TyKind::Alias(alias) => match &alias.kind {
                hax::AliasKind::Projection(item) => {
                    let trait_ref = self.translate_trait_proof(
                        span,
                        item.in_trait
                            .as_ref()
                            .expect("projection without a trait_ref?"),
                    )?;
                    let assoc_type_id =
                        self.translate_assoc_type_id(trait_ref.trait_id(), &item.def_id)?;
                    let generics =
                        self.translate_generic_args(span, &item.generic_args, &item.trait_proofs)?;
                    TyKind::TraitType(trait_ref, assoc_type_id, generics)
                }
                hax::AliasKind::Opaque { hidden_ty, .. } => {
                    return self.translate_ty(span, hidden_ty);
                }
                _ => {
                    raise_error!(self, span, "Unsupported alias type: {:?}", alias.kind)
                }
            },

            hax::TyKind::Adt(item) => {
                let tref = self.translate_type_decl_ref(span, item)?;
                TyKind::Adt(tref)
            }
            hax::TyKind::Str(item_ref) => {
                let tref = self.translate_type_decl_ref(span, item_ref)?;
                TyKind::Adt(tref)
            }
            hax::TyKind::Array(item_ref) => {
                // `Sized` is the first predicate if we're not hiding marker traits.
                let item_ty_is_sized = if self.options.hide_marker_traits {
                    None
                } else {
                    Some(self.translate_trait_proof(span, &item_ref.trait_proofs[0])?)
                };
                let mut args = self.translate_generic_args(span, &item_ref.generic_args, &[])?;
                assert!(args.types.len() == 1 && args.const_generics.len() == 1);
                TyKind::Array(
                    args.types.pop().unwrap(),
                    args.const_generics.pop().unwrap(),
                    item_ty_is_sized,
                )
            }
            hax::TyKind::Pat(ty, pat) => {
                let ty = self.translate_ty(span, ty)?;
                let pat = self.translate_pattern(span, pat)?;
                TyKind::Pattern(ty, pat)
            }
            hax::TyKind::Slice(item_ref) => {
                // `Sized` is the first predicate if we're not hiding marker traits.
                let item_ty_is_sized = if self.options.hide_marker_traits {
                    None
                } else {
                    Some(self.translate_trait_proof(span, &item_ref.trait_proofs[0])?)
                };
                let mut args = self.translate_generic_args(span, &item_ref.generic_args, &[])?;
                assert!(args.types.len() == 1);
                TyKind::Slice(args.types.pop().unwrap(), item_ty_is_sized)
            }
            hax::TyKind::Tuple(item_ref) => {
                let tref = self.translate_type_decl_ref(span, item_ref)?;
                TyKind::Adt(tref)
            }
            hax::TyKind::Ref(region, ty, mutability) => {
                trace!("Ref");

                let region = self.translate_region(span, region)?;
                let ty = self.translate_ty(span, ty)?;
                let kind = if mutability.is_mut() {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                TyKind::Ref(region, ty, kind)
            }
            hax::TyKind::RawPtr(ty, mutbl) => {
                trace!("RawPtr: {:?}", (ty, mutbl));
                let ty = self.translate_ty(span, ty)?;
                let kind = if mutbl.is_mut() {
                    RefKind::Mut
                } else {
                    RefKind::Shared
                };
                TyKind::RawPtr(ty, kind)
            }

            hax::TyKind::Param(param) => {
                // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
                // Note that this type parameter may actually have been
                // instantiated (in our environment, we may map it to another
                // type): we just have to look it up.
                // Note that if we are using this function to translate a field
                // type in a type definition, it should actually map to a type
                // parameter.
                match self.lookup_type_var(span, param) {
                    Ok(var) => TyKind::TypeVar(var),
                    Err(err) => TyKind::Error(err.msg),
                }
            }

            hax::TyKind::Foreign(item) => {
                let tref = self.translate_type_decl_ref(span, item)?;
                TyKind::Adt(tref)
            }

            hax::TyKind::FnPtr(sig, _) => {
                trace!("FnPtr");
                trace!("bound vars: {:?}", sig.bound_vars);
                let sig = self.translate_poly_fun_sig(span, sig)?;
                TyKind::FnPtr(sig)
            }
            hax::TyKind::FnDef { item, .. } => {
                let fnref = self.translate_bound_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                TyKind::FnDef(fnref)
            }
            hax::TyKind::Closure(args) => {
                let tref = self.translate_closure_type_ref(span, args)?;
                TyKind::Adt(tref)
            }

            hax::TyKind::Dynamic(dyn_binder, region) => {
                // self.check_no_monomorphize(span)?;
                // Translate the region outside the binder.
                let region = self.translate_region(span, region)?;

                let binder = self.translate_dyn_binder(span, dyn_binder, |ctx, ty, ()| {
                    let region = region.move_under_binder();
                    ctx.innermost_binder_mut()
                        .params
                        .types_outlive
                        .push(RegionBinder::empty(OutlivesPred(ty.clone(), region)));
                    Ok(ty)
                })?;

                if let hax::ClauseKind::Trait(trait_predicate) = dyn_binder.predicates.predicates[0]
                    .clause
                    .kind
                    .hax_skip_binder_ref()
                {
                    // TODO(dyn): for now, we consider traits with associated types to not be dyn
                    // compatible because we don't know how to handle them; for these we skip
                    // translating the vtable.
                    if self.trait_is_dyn_compatible(&trait_predicate.trait_ref.def_id) {
                        // Ensure the vtable type is translated. The first predicate is the one that
                        // can have methods, i.e. a vtable.
                        let _: TypeDeclId = self.register_item(
                            span,
                            &trait_predicate.trait_ref,
                            TransItemSourceKind::VTable,
                        );
                    }
                }
                TyKind::DynTrait(DynPredicate { binder })
            }

            hax::TyKind::Infer(_) => {
                raise_error!(self, span, "Unsupported type: infer type")
            }
            hax::TyKind::Coroutine(..) => {
                raise_error!(self, span, "Coroutine types are not supported yet")
            }
            hax::TyKind::Bound(_, _) => {
                raise_error!(self, span, "Unexpected type kind: bound")
            }
            hax::TyKind::Placeholder(_) => {
                raise_error!(self, span, "Unsupported type: placeholder")
            }

            hax::TyKind::Error => {
                raise_error!(self, span, "Type checking error")
            }
            hax::TyKind::Todo(s) => {
                raise_error!(self, span, "Unsupported type: {:?}", s)
            }
        };
        Ok(kind.into_ty())
    }

    pub fn translate_pattern(
        &mut self,
        span: Span,
        pat: &hax::Pattern,
    ) -> Result<TypePattern, Error> {
        Ok(match pat {
            hax::Pattern::Range { start, end } => TypePattern::Range(
                self.translate_constant_expr(span, start)?,
                self.translate_constant_expr(span, end)?,
            ),
            hax::Pattern::Or(patterns) => TypePattern::OrPattern(
                patterns
                    .iter()
                    .map(|pat| self.translate_pattern(span, pat))
                    .try_collect()?,
            ),
            hax::Pattern::NotNull => TypePattern::NotNull,
        })
    }

    pub(crate) fn translate_rustc_ty(
        &mut self,
        span: Span,
        ty: &ty::Ty<'tcx>,
    ) -> Result<Ty, Error> {
        let ty = self.t_ctx.catch_sinto(&self.hax_state, span, ty)?;
        self.translate_ty(span, &ty)
    }

    pub fn translate_poly_fun_sig(
        &mut self,
        span: Span,
        sig: &hax::Binder<hax::TyFnSig>,
    ) -> Result<RegionBinder<FunSig>, Error> {
        self.translate_region_binder(span, sig, |ctx, sig| ctx.translate_fun_sig(span, sig))
    }
    pub fn translate_fun_sig(&mut self, span: Span, sig: &hax::TyFnSig) -> Result<FunSig, Error> {
        let inputs = sig
            .inputs
            .iter()
            .map(|x| self.translate_ty(span, x))
            .try_collect()?;
        let output = self.translate_ty(span, &sig.output)?;
        Ok(FunSig {
            is_unsafe: sig.safety == hax::Safety::Unsafe,
            abi: Self::translate_abi(&sig.abi),
            is_variadic: sig.c_variadic,
            inputs,
            output,
        })
    }

    pub fn translate_abi(abi: &hax::ExternAbi) -> Abi {
        match abi {
            hax::ExternAbi::Rust => Abi::Rust,
            hax::ExternAbi::C { unwind: false } => Abi::C,
            _ => Abi::Other(abi.as_str().into()),
        }
    }

    /// Translate generic args. Don't call directly; use `translate_xxx_ref` as much as possible.
    pub fn translate_generic_args(
        &mut self,
        span: Span,
        substs: &[hax::GenericArg],
        trait_refs: &[hax::TraitProof],
    ) -> Result<GenericArgs, Error> {
        use crate::hax::GenericArg::*;
        trace!("{:?}", substs);

        let mut regions = IndexVec::new();
        let mut types = IndexVec::new();
        let mut const_generics = IndexVec::new();
        for param in substs {
            match param {
                Type(param_ty) => {
                    types.push(self.translate_ty(span, param_ty)?);
                }
                Lifetime(region) => {
                    regions.push(self.translate_region(span, region)?);
                }
                Const(c) => {
                    const_generics.push(self.translate_constant_expr(span, c)?);
                }
            }
        }
        let trait_refs = self.translate_trait_proofs(span, trait_refs)?;

        Ok(GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        })
    }

    /// Whether Rust treats this type specially, i.e. whether it is a tuple, `str` or `Box`.
    pub(crate) fn recognize_builtin_adt(&mut self, item: &hax::ItemRef) -> Option<BuiltinAdt> {
        item.def_id
            .as_synthetic(self.hax_state())
            .and_then(|synthetic| match synthetic {
                hax::SyntheticItem::Tuple(_) => Some(BuiltinAdt::Tuple),
                hax::SyntheticItem::Str => Some(BuiltinAdt::Str),
                hax::SyntheticItem::Array
                | hax::SyntheticItem::Slice
                | hax::SyntheticItem::FnPtr(_) => None,
            })
            .or_else(|| {
                (self.hax_def(item).ok()?.lang_item? == sym::owned_box).then_some(BuiltinAdt::Box)
            })
    }

    /// Translate a Dynamically Sized Type metadata kind.
    ///
    /// Returns `None` if the type is generic, or if it is not a DST.
    pub fn translate_ptr_metadata(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<PtrMetadata, Error> {
        // prepare the call to the method
        use rustc_middle::ty;
        let tcx = self.t_ctx.tcx;
        let hax_state = &self.hax_state;
        let ty_env = hax_state.typing_env();
        let ty = item
            .def_id
            .type_of(hax_state)
            .instantiate(tcx, item.rustc_args(hax_state));
        let ty = hax::normalize(tcx, ty_env, ty);

        // Get the tail type, which determines the metadata of `ty`.
        let tail_ty = tcx.struct_tail_raw(
            ty,
            &rustc_middle::traits::ObligationCause::dummy(),
            |ty| hax::normalize(tcx, ty_env, ty),
            || {},
        );
        let hax_ty: hax::Ty = self.t_ctx.catch_sinto(hax_state, span, &tail_ty)?;

        // If we're hiding `Sized`, let's consider everything to be sized.
        let everything_is_sized = self.t_ctx.options.hide_marker_traits;
        let ret = match tail_ty.kind() {
            _ if everything_is_sized || tail_ty.is_sized(tcx, ty_env) => PtrMetadata::None,
            ty::Str | ty::Slice(..) => PtrMetadata::Length,
            ty::Dynamic(..) => match hax_ty.kind() {
                hax::TyKind::Dynamic(dyn_binder, _) => {
                    let vtable = self.translate_dyn_binder(span, dyn_binder, |ctx, _, _| {
                        ctx.translate_region_binder(
                            span,
                            &dyn_binder.predicates.predicates[0].clause.kind,
                            |ctx, kind: &hax::ClauseKind| {
                                let hax::ClauseKind::Trait(trait_predicate) = kind else {
                                    unreachable!()
                                };
                                ctx.translate_vtable_struct_ref(span, &trait_predicate.trait_ref)
                            },
                        )
                    })?;
                    let vtable = vtable
                        .skip_binder
                        .try_substitute(&GenericArgs::empty())
                        .expect("vtable struct should not depend on self type");
                    let vtable = self.erase_region_binder(vtable);
                    PtrMetadata::VTable(vtable)
                }
                _ => unreachable!("Unexpected hax type {hax_ty:?} for dynamic type: {ty:?}"),
            },
            ty::Param(..) => PtrMetadata::InheritFrom(self.translate_ty(span, &hax_ty)?),
            ty::Placeholder(..) | ty::Infer(..) | ty::Bound(..) => {
                panic!(
                    "We should never encounter a placeholder, infer, or bound type from ptr_metadata translation. Got: {tail_ty:?}"
                )
            }
            _ => PtrMetadata::None,
        };

        Ok(ret)
    }

    /// Translate a type layout.
    ///
    /// Translates the layout as queried from rustc into the more restricted [`Layout`].
    #[tracing::instrument(skip(self))]
    pub fn translate_layout(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        kind: &TypeDeclKind,
    ) -> Option<Layout> {
        let item = def.this();
        use rustc_abi as r_abi;

        fn translate_variant_layout_data(
            layout_data: &r_abi::LayoutData<r_abi::FieldIdx, r_abi::VariantIdx>,
            inhabited: InhabitedPredicate,
            tagger: Vec<(ByteCount, IntegerValue)>,
        ) -> Option<VariantLayout> {
            let field_offsets = match &layout_data.fields {
                r_abi::FieldsShape::Arbitrary { offsets, .. } => {
                    offsets.iter().map(|o| OffsetExpr::new(o.bytes())).collect()
                }
                r_abi::FieldsShape::Union(n) => (0..n.get()).map(|_| OffsetExpr::new(0)).collect(),
                r_abi::FieldsShape::Primitive => IndexVec::default(),
                r_abi::FieldsShape::Array { .. } => panic!("Unexpected layout shape"),
            };
            Some(VariantLayout {
                field_offsets,
                inhabited,
                tagger,
            })
        }

        fn translate_primitive_int(int_ty: r_abi::Integer, signed: bool) -> IntegerTy {
            if signed {
                IntegerTy::Signed(match int_ty {
                    r_abi::Integer::I8 => IntTy::I8,
                    r_abi::Integer::I16 => IntTy::I16,
                    r_abi::Integer::I32 => IntTy::I32,
                    r_abi::Integer::I64 => IntTy::I64,
                    r_abi::Integer::I128 => IntTy::I128,
                })
            } else {
                IntegerTy::Unsigned(match int_ty {
                    r_abi::Integer::I8 => UIntTy::U8,
                    r_abi::Integer::I16 => UIntTy::U16,
                    r_abi::Integer::I32 => UIntTy::U32,
                    r_abi::Integer::I64 => UIntTy::U64,
                    r_abi::Integer::I128 => UIntTy::U128,
                })
            }
        }

        /// Returns expressions that compute the layout (size, align) chosen by rustc. For sized
        /// types, that's plain integers; for unsized types, we build expressions that compute the
        /// right value based on pointer metadata values. This mirrors rustc's
        /// `size_and_align_of_dst` computation:
        /// <https://github.com/rust-lang/rust/blob/3fbb92e14159dd8b9bdb81e065883d1132e5abb7/compiler/rustc_codegen_ssa/src/size_of_val.rs#L100-L182>.
        fn chosen_size_and_align<'tcx>(
            cx: &ty::layout::LayoutCx<'tcx>,
            layout: ty::layout::TyAndLayout<'tcx>,
        ) -> Option<(SizeExpr, SizeExpr)> {
            let constant = |value: u64| SizeExprKind::from_usize(u128::from(value)).into_expr();

            if layout.is_sized() {
                return Some((
                    constant(layout.size.bytes()),
                    constant(layout.align.abi.bytes()),
                ));
            }

            match layout.ty.kind() {
                ty::Dynamic(..) => Some((
                    SizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
                    SizeExprKind::FromMetadata(MetadataValue::DynAlign).into_expr(),
                )),
                ty::Slice(..) | ty::Str => {
                    let unit = layout.field(cx, 0);
                    Some((
                        SizeExprKind::Scale(
                            SizeExprKind::FromMetadata(MetadataValue::SliceLength).into_expr(),
                            ConstantExpr::mk_usize(u128::from(unit.size.bytes())),
                        )
                        .into_expr(),
                        constant(unit.align.abi.bytes()),
                    ))
                }
                ty::Adt(..) | ty::Tuple(..) => {
                    let tail_idx = layout.fields.count() - 1;
                    let tail_offset = constant(layout.fields.offset(tail_idx).bytes());
                    let sized_align = constant(layout.align.abi.bytes());
                    let tail_layout = layout.field(cx, tail_idx);
                    let (tail_size, mut tail_align) = chosen_size_and_align(cx, tail_layout)?;

                    if let ty::Adt(def, _) = layout.ty.kind()
                        && let Some(pack) = def.repr().pack
                    {
                        tail_align =
                            SizeExprKind::Min(vec![tail_align, constant(pack.bytes())]).into_expr();
                    }

                    let full_align = SizeExprKind::Max(vec![sized_align, tail_align]).into_expr();
                    let full_size = SizeExprKind::AlignTo {
                        base: SizeExprKind::Plus(tail_offset, tail_size).into_expr(),
                        target_align: full_align.clone(),
                    }
                    .into_expr();
                    Some((full_size, full_align))
                }
                ty::Foreign(..) => None,
                _ => None,
            }
        }

        let tcx = self.t_ctx.tcx;
        let hax_state = self.hax_state_with_id();
        assert_eq!(hax_state.owner(), item.def_id);
        let ty_env = hax_state.typing_env();
        let ty = item
            .def_id
            .type_of(hax_state)
            .instantiate(tcx, item.rustc_args(hax_state));
        let ty = hax::normalize(tcx, ty_env, ty);
        let pseudo_input = ty_env.as_query_input(ty);
        let ptr_size = self.translated.the_target_information().target_pointer_size;

        let repr = match &def.kind {
            hax::FullDefKind::Adt(adt) => self.translate_repr_options(adt.repr()),
            _ => ReprOptions::default(),
        };
        let ty_layout = match tcx.layout_of(pseudo_input) {
            Ok(layout) => layout,
            Err(_) => return Layout::for_type(&self.translated, kind, repr),
        };
        let rustc_variant_inhabited = |id| match ty.kind() {
            ty::Adt(adt, args) if adt.is_enum() => adt
                .variant(id)
                .inhabited_predicate(tcx)
                .instantiate(tcx, args),
            _ => ty.inhabited_predicate(tcx),
        };
        let inhabited = self
            .translate_inhabited_predicate(span, ty.inhabited_predicate(tcx))
            .ok()?;
        let layout_cx = ty::layout::LayoutCx::new(tcx, ty_env);
        let (size, align) = chosen_size_and_align(&layout_cx, ty_layout)?;
        let size = Size::from_expr(size.normalize(Some(&self.translated), None, false));
        let align = Size::from_expr(align.normalize(Some(&self.translated), None, false));
        let layout = ty_layout.layout;

        let num_variants = match ty.variant_range(self.t_ctx.tcx) {
            Some(range) => range.end.index(),
            None => match layout.fields() {
                r_abi::FieldsShape::Arbitrary { .. } | r_abi::FieldsShape::Union(_) => 1,
                r_abi::FieldsShape::Primitive | r_abi::FieldsShape::Array { .. } => 0,
            },
        };
        let mut variant_layouts: IndexVec<VariantId, Option<VariantLayout>> =
            (0..num_variants).map(|_| None).collect();
        // Build the discriminator tree and variant layouts.
        let discriminator = match layout.variants() {
            r_abi::Variants::Multiple {
                tag,
                tag_encoding,
                tag_field,
                variants,
                ..
            } => {
                // The tag_field is the index into the `offsets` vector.
                let r_abi::FieldsShape::Arbitrary { offsets, .. } = layout.fields() else {
                    unreachable!()
                };
                let tag_offset = offsets
                    .get(*tag_field)
                    .map(|s| r_abi::Size::bytes(*s))
                    .expect("No tag field offset for enum?");
                let tag_offset_expr = OffsetExpr::new(tag_offset);

                let tag_ty = match tag.primitive() {
                    r_abi::Primitive::Int(int_ty, signed) => {
                        translate_primitive_int(int_ty, signed)
                    }
                    r_abi::Primitive::Pointer(_) => IntegerTy::Signed(IntTy::Isize),
                    r_abi::Primitive::Float(_) => unreachable!(),
                };
                let tag_size = r_abi::Size::from_bytes(tag_ty.target_size(ptr_size));
                // Reinterpret raw tag bits in `tag_ty`, sign-extending if needed.
                let tag_from_bits =
                    |bits: u128| IntegerValue::from_bits(tag_ty, tag_size.truncate(bits));

                struct VariantTagInfo {
                    /// The value of the tag for this variant, even if this is the untagged variant
                    /// of a niched enum. `None` if we can't compute it.
                    value: Option<IntegerValue>,
                    /// Whether the variant is inhabited or not.
                    uninhabited: bool,
                    /// Whether this is the niched (untagged) variant of a niched enum.
                    niched: bool,
                }
                let taginfo_for_variant = |id: rustc_abi::VariantIdx| {
                    let uninhabited = variants[id].is_uninhabited();
                    match tag_encoding {
                        r_abi::TagEncoding::Direct => {
                            let value = if uninhabited {
                                None
                            } else {
                                let tag = tcx
                                    .tag_for_variant(ty_env.as_query_input((ty, id)))
                                    .unwrap();
                                Some(tag_from_bits(tag.to_bits(tag_size)))
                            };
                            VariantTagInfo {
                                value,
                                uninhabited,
                                niched: false,
                            }
                        }
                        r_abi::TagEncoding::Niche {
                            untagged_variant,
                            niche_variants,
                            niche_start,
                        } => {
                            let value = niche_variants.contains(&id).then(|| {
                                let relative = (id.index() - niche_variants.start.index()) as u128;
                                tag_from_bits(niche_start.wrapping_add(relative))
                            });
                            VariantTagInfo {
                                value,
                                uninhabited,
                                niched: id == *untagged_variant,
                            }
                        }
                    }
                };

                // Compute per-variant tag values and build tagger + discriminator children.
                let mut children = Vec::new();

                for (id, variant_layout) in variants.iter_enumerated() {
                    let variant_id = self.translate_variant_id(id);
                    let taginfo = taginfo_for_variant(id);
                    let variant_inhabited = self
                        .translate_inhabited_predicate(span, rustc_variant_inhabited(id))
                        .ok()?;
                    let tagger = if let Some(val) = taginfo.value {
                        if taginfo.niched || taginfo.uninhabited {
                            // If we could compute a tag for this variant, encountering it is UB.
                            children.push((val..=val, Discriminator::Invalid));
                            vec![]
                        } else {
                            children.push((val..=val, Discriminator::Known(variant_id)));
                            vec![(tag_offset, val)]
                        }
                    } else {
                        // Niched or uninhabited variant that corresponds to no tag.
                        vec![]
                    };

                    let field_offsets = variant_layout
                        .field_offsets
                        .iter()
                        .map(|o| OffsetExpr::new(o.bytes()))
                        .collect();
                    variant_layouts[variant_id] = Some(VariantLayout {
                        field_offsets,
                        inhabited: variant_inhabited,
                        tagger,
                    });
                }

                let fallback = match tag_encoding {
                    r_abi::TagEncoding::Direct => Discriminator::Invalid,
                    // We follow what Minirust does:
                    // https://github.com/minirust/minirust/blob/master/tooling/minimize/src/enums.rs
                    r_abi::TagEncoding::Niche {
                        untagged_variant, ..
                    } => {
                        // Every value outside the valid range of the tag is invalid. The valid
                        // range is given as bits and may wrap around; we compare in `tag_ty`.
                        let valid = tag.valid_range(&self.t_ctx.tcx);
                        let start = tag_from_bits(valid.start);
                        let end = tag_from_bits(valid.end);
                        let (min, max) = match tag_ty {
                            IntegerTy::Signed(_) => (
                                tag_from_bits(tag_size.signed_int_min() as u128),
                                tag_from_bits(tag_size.signed_int_max() as u128),
                            ),
                            IntegerTy::Unsigned(_) => {
                                (tag_from_bits(0), tag_from_bits(tag_size.unsigned_int_max()))
                            }
                        };

                        let after_end = tag_from_bits(valid.end.wrapping_add(1));
                        let before_start = tag_from_bits(valid.start.wrapping_sub(1));
                        if start <= end {
                            // The valid range is contiguous: the invalid values are on either side.
                            if end < max {
                                children.push((after_end..=max, Discriminator::Invalid));
                            }
                            if min < start {
                                children.push((min..=before_start, Discriminator::Invalid));
                            }
                        } else {
                            // The valid range wraps around: the invalid values are in the middle.
                            if after_end <= before_start {
                                children.push((after_end..=before_start, Discriminator::Invalid));
                            }
                        }
                        if variants[*untagged_variant].is_uninhabited() {
                            Discriminator::Invalid
                        } else {
                            Discriminator::Known(self.translate_variant_id(*untagged_variant))
                        }
                    }
                };

                // The ranges are disjoint; sort them for readability.
                children.sort_by_key(|(range, _)| *range.start());
                let discriminator = Discriminator::Branch {
                    offset: tag_offset_expr,
                    int_ty: tag_ty,
                    fallback: Box::new(fallback),
                    children,
                };

                Some(discriminator)
            }
            r_abi::Variants::Single { index } => {
                let variant_id = self.translate_variant_id(*index);
                match layout.fields() {
                    r_abi::FieldsShape::Arbitrary { .. } | r_abi::FieldsShape::Union(_) => {
                        let variant_inhabited = self
                            .translate_inhabited_predicate(span, rustc_variant_inhabited(*index))
                            .ok()?;
                        variant_layouts[variant_id] =
                            translate_variant_layout_data(&layout, variant_inhabited, vec![]);
                    }
                    r_abi::FieldsShape::Primitive | r_abi::FieldsShape::Array { .. } => {}
                }
                Some(Discriminator::trivial(variant_id))
            }
            r_abi::Variants::Empty => None,
        };

        Some(Layout {
            size,
            align,
            discriminator,
            inhabited,
            variant_layouts,
            repr,
        })
    }

    /// Generate a naive layout for this type.
    pub fn generate_naive_layout(&self, span: Span, ty: &TypeDeclKind) -> Result<Layout, Error> {
        match ty {
            TypeDeclKind::Struct(fields) => {
                let mut size = 0;
                let mut align = 0;
                let ptr_size = self.translated.the_target_information().target_pointer_size;
                let field_offsets = fields.map_ref(|field| {
                    let offset = size;
                    let size_of_ty = match field.ty.kind() {
                        TyKind::Scalar(scalar_ty) => scalar_ty.target_size(ptr_size) as u64,
                        // This is a lie, the pointers could be fat...
                        TyKind::Ref(..) | TyKind::RawPtr(..) | TyKind::FnPtr(..) => ptr_size,
                        _ => panic!("Unsupported type for `generate_naive_layout`: {ty:?}"),
                    };
                    size += size_of_ty;
                    // For these types, align == size is good enough.
                    align = std::cmp::max(align, size);
                    OffsetExpr::new(offset)
                });

                Ok(Layout {
                    size: Size::new(size),
                    align: Size::new(align),
                    discriminator: None,
                    inhabited: InhabitedPredicate::mk_true(),
                    variant_layouts: IndexVec::from([Some(VariantLayout {
                        field_offsets,
                        tagger: vec![],
                        inhabited: InhabitedPredicate::mk_true(),
                    })]),
                    repr: ReprOptions::default(),
                })
            }
            _ => raise_error!(
                self,
                span,
                "`generate_naive_layout` only supports structs at the moment"
            ),
        }
    }

    /// Translate the body of a type declaration.
    ///
    /// Note that the type may be external, in which case we translate the body
    /// only if it is public (i.e., it is a public enumeration, or it is a
    /// struct with only public fields).
    pub(crate) fn translate_adt_def(
        &mut self,
        trans_id: TypeDeclId,
        def_span: Span,
        item_meta: &ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<TypeDeclKind, Error> {
        use crate::hax::AdtKind;
        let hax::FullDefKind::Adt(adt) = def.kind() else {
            unreachable!()
        };

        if item_meta.opacity.is_opaque() {
            return Ok(TypeDeclKind::Opaque);
        }

        let adt_kind = adt.adt_kind();
        if matches!(adt_kind, AdtKind::Tuple) && self.t_ctx.options.no_gen_tuple_structs {
            return Ok(TypeDeclKind::Opaque);
        }

        // hax's synthetic ADTs have no variants; we must construct the fields ourselves
        let synthetic_fields = match adt_kind {
            AdtKind::Tuple => {
                let item = def.this();
                let args = self.translate_generic_args(def_span, &item.generic_args, &[])?;
                Some(args.types.into_iter().collect_vec())
            }
            AdtKind::Str => {
                let u8_ty =
                    TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U8))).into_ty();
                let u8_is_sized = self.translate_sized_proof(def_span, self.tcx.types.u8)?;
                Some(vec![Ty::mk_slice(u8_ty, u8_is_sized)])
            }
            _ => None,
        };
        if let Some(tys) = synthetic_fields {
            let fields = tys
                .into_iter()
                .enumerate()
                .map(|(field_id, ty)| Field {
                    span: def_span,
                    attr_info: AttrInfo::dummy_public(),
                    name: format!("_{field_id}"),
                    is_positional: true,
                    ty,
                })
                .collect();
            return Ok(TypeDeclKind::Struct(fields));
        }

        trace!("{}", trans_id);

        // In case the type is external, check if we should consider the type as
        // transparent (i.e., extract its body). If it is an enumeration, then yes
        // (because the variants of public enumerations are public, together with their
        // fields). If it is a structure, we check if all the fields are public.
        let variants = adt.variants();
        let contents_are_public = match adt_kind {
            AdtKind::Enum => true,
            AdtKind::Struct | AdtKind::Union => {
                // Check the unique variant
                error_assert!(self, def_span, variants.len() == 1);
                variants[hax::VariantIdx::from(0usize)]
                    .fields
                    .iter()
                    .all(|f| matches!(f.vis, Visibility::Public))
            }
            // The rest are fake adt kinds that won't reach here.
            _ => unreachable!(),
        };

        if item_meta
            .opacity
            .with_content_visibility(contents_are_public)
            .is_opaque()
        {
            return Ok(TypeDeclKind::Opaque);
        }

        // The type is transparent: explore the variants
        let mut translated_variants: IndexVec<VariantId, Variant> = Default::default();
        for (i, var_def) in variants.iter().enumerate() {
            trace!("variant {i}: {var_def:?}");

            let mut fields: IndexVec<FieldId, Field> = Default::default();
            for (j, field_def) in var_def.fields.iter().enumerate() {
                trace!("variant {i}: field {j}: {field_def:?}");
                let field_span = self.t_ctx.translate_span(&field_def.span);
                // Translate the field type
                let ty = self.translate_ty(field_span, &field_def.ty)?;
                let field_full_def = self.poly_hax_def(&field_def.did)?;
                let field_attrs = self.t_ctx.translate_attr_info(&field_full_def);

                // Retrieve the field name.
                let is_positional = field_def.name.is_none();
                let field_name = field_def
                    .name
                    .map_or_else(|| format!("_{j}"), |name| name.to_string());

                // Store the field
                let field = Field {
                    span: field_span,
                    attr_info: field_attrs,
                    name: field_name,
                    is_positional,
                    ty,
                };
                fields.push(field);
            }

            let discriminant = self.translate_discriminant(def_span, &var_def.discr_val)?;
            let variant_span = self.t_ctx.translate_span(&var_def.span);
            let variant_name = var_def.name.to_string();
            let variant_full_def = self.poly_hax_def(&var_def.def_id)?;

            let mut variant_attrs = self.t_ctx.translate_attr_info(&variant_full_def);
            // Propagate a `#[charon::variants_prefix(..)]` or `#[charon::variants_suffix(..)]` attribute to the variants.
            if variant_attrs.rename.is_none() {
                let prefix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .filter_map(|a| a.as_variants_prefix())
                    .next()
                    .map(|attr| attr.as_str());
                let suffix = item_meta
                    .attr_info
                    .attributes
                    .iter()
                    .filter_map(|a| a.as_variants_suffix())
                    .next()
                    .map(|attr| attr.as_str());
                if prefix.is_some() || suffix.is_some() {
                    let prefix = prefix.unwrap_or_default();
                    let suffix = suffix.unwrap_or_default();
                    variant_attrs.rename = Some(format!("{prefix}{variant_name}{suffix}"));
                }
            }

            translated_variants.push_with(|id| Variant {
                id,
                span: variant_span,
                attr_info: variant_attrs,
                name: variant_name,
                fields,
                discriminant,
            });
        }

        // Register the type
        let type_def_kind: TypeDeclKind = match adt_kind {
            AdtKind::Struct => TypeDeclKind::Struct(translated_variants[0].fields.clone()),
            AdtKind::Enum => TypeDeclKind::Enum(translated_variants),
            AdtKind::Union => TypeDeclKind::Union(translated_variants[0].fields.clone()),
            // The rest are fake adt kinds that won't reach here.
            _ => unreachable!(),
        };

        Ok(type_def_kind)
    }

    fn translate_discriminant(
        &mut self,
        def_span: Span,
        discr: &hax::DiscriminantValue,
    ) -> Result<IntegerValue, Error> {
        let ty = self.translate_ty(def_span, &discr.ty)?;
        let scalar_ty = ty.kind().as_scalar().unwrap();
        match scalar_ty.as_integer() {
            Some(int_ty) => Ok(IntegerValue::from_bits(*int_ty, discr.val)),
            None => raise_error!(self, def_span, "unexpected discriminant type: {ty:?}",),
        }
    }

    fn translate_inhabited_predicate(
        &mut self,
        span: Span,
        predicate: ty::inhabitedness::InhabitedPredicate<'tcx>,
    ) -> Result<InhabitedPredicate, Error> {
        use ty::inhabitedness::InhabitedPredicate as RustcPredicate;
        Ok(match predicate {
            RustcPredicate::True => InhabitedPredicateKind::True,
            RustcPredicate::False => InhabitedPredicateKind::False,
            RustcPredicate::ConstIsZero(value) => {
                InhabitedPredicateKind::ConstIsZero(self.translate_ty_constant_expr(span, &value)?)
            }
            // We only retain layout-relevant inhabitedness.
            RustcPredicate::NotInModule(_) => InhabitedPredicateKind::False,
            RustcPredicate::GenericType(ty) => {
                InhabitedPredicateKind::GenericType(self.translate_rustc_ty(span, &ty)?)
            }
            RustcPredicate::OpaqueType(key) => {
                // Reveal the opaque type.
                let opaque_ty = self
                    .tcx
                    .type_of(key.def_id)
                    .instantiate(self.tcx, key.args)
                    .skip_norm_wip();
                return self
                    .translate_inhabited_predicate(span, opaque_ty.inhabited_predicate(self.tcx));
            }
            RustcPredicate::And(&[left, right]) => InhabitedPredicateKind::And(vec![
                self.translate_inhabited_predicate(span, left)?,
                self.translate_inhabited_predicate(span, right)?,
            ]),
            RustcPredicate::Or(&[left, right]) => InhabitedPredicateKind::Or(vec![
                self.translate_inhabited_predicate(span, left)?,
                self.translate_inhabited_predicate(span, right)?,
            ]),
        }
        .into_pred())
    }

    pub fn translate_repr_options(&mut self, hax_repr_options: &hax::ReprOptions) -> ReprOptions {
        let repr_algo = if hax_repr_options.flags.is_c {
            ReprAlgorithm::C
        } else {
            ReprAlgorithm::Rust
        };

        let align_mod = if let Some(align) = &hax_repr_options.align {
            Some(AlignmentModifier::Align(align.bytes()))
        } else if let Some(pack) = &hax_repr_options.pack {
            Some(AlignmentModifier::Pack(pack.bytes()))
        } else {
            None
        };

        let explicit_discr_type =
            hax_repr_options
                .int_specified
                .then(|| match hax_repr_options.typ.kind() {
                    hax::TyKind::Int(ty) => IntegerTy::Signed(Self::translate_hax_int_ty(ty)),
                    hax::TyKind::Uint(ty) => IntegerTy::Unsigned(Self::translate_hax_uint_ty(ty)),
                    ty => unreachable!("explicit enum discriminant type is not an integer: {ty:?}"),
                });

        ReprOptions {
            transparent: hax_repr_options.flags.is_transparent,
            explicit_discr_type,
            repr_algo,
            align_modif: align_mod,
        }
    }
}
