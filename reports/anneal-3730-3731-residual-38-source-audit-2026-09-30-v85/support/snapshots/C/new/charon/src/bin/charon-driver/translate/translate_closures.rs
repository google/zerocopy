//! In rust, closures behave like ADTs that implement the FnOnce/FnMut/Fn traits automatically.
//! Function item types also implement those traits automatically.
//!
//! Here we convert closures to a struct containing the closure's state (upvars), along with
//! matching trait impls and fun decls (e.g. a Fn closure will have a trait impl for Fn, FnMut and
//! FnOnce, along with 3 matching method implementations for call, call_mut and call_once).
//! Function item types reuse the same generated trait impls and methods, with an empty state that
//! forwards to the original function item.
//!
//! For example, given the following Rust code:
//! ```ignore
//! pub fn test_closure_capture<T: Clone>() {
//!     let mut v = vec![];
//!     let mut add = |x: &u32| v.push(*x);
//!     add(&0);
//!     add(&1);
//! }
//! ```
//!
//! We generate the equivalent desugared code:
//! ```text
//! struct {test_closure_capture::closure#0}<'a, T: Clone> (&'a mut Vec<u32>);
//!
//! // The 'a comes from captured variables, the 'b comes from the closure higher-kinded signature.
//! impl<'a, 'b, T: Clone> FnMut<(&'b u32,)> for {test_closure_capture::closure#0}<'a, T> {
//!     fn call_mut<'c>(&'c mut self, arg: (&'b u32,)) {
//!         self.0.push(*arg.0);
//!     }
//! }
//!
//! impl<'a, 'b, T: Clone> FnOnce<(&'b u32,)> for {test_closure_capture::closure#0}<'a, T> {
//!     type Output = ();
//!     ...
//! }
//!
//! pub fn test_closure_capture<T: Clone>() {
//!     let mut v = vec![];
//!     let mut add = {test_closure_capture::closure#0} (&mut v);
//!     state.call_mut(&0);
//!     state.call_mut(&1);
//! }
//! ```

use crate::hax;
use itertools::Itertools;
use std::mem;

use super::translate_crate::TransItemSourceKind;
use super::translate_ctx::*;
use charon_lib::ullbc_ast::*;

pub fn translate_closure_kind(kind: &hax::ClosureKind) -> ClosureKind {
    match kind {
        hax::ClosureKind::Fn => ClosureKind::Fn,
        hax::ClosureKind::FnMut => ClosureKind::FnMut,
        hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
    }
}

/// If this trait proof is a built-in impl of a `Fn*` trait, return the `Self` type it is
/// implemented for and the kind of the implemented trait.
pub fn recognize_fn_trait_impl_proof(
    trait_proof: &hax::TraitProof,
) -> Option<(hax::Binder<&hax::Ty>, ClosureKind)> {
    let hax::TraitProofKind::Builtin {
        trait_data: hax::BuiltinTraitData::Other(lang_item),
        ..
    } = &trait_proof.kind
    else {
        return None;
    };
    let kind = match lang_item {
        hax::SolverTraitLangItem::FnOnce => ClosureKind::FnOnce,
        hax::SolverTraitLangItem::FnMut => ClosureKind::FnMut,
        hax::SolverTraitLangItem::Fn => ClosureKind::Fn,
        _ => return None,
    };
    let Some(hax::GenericArg::Type(self_ty)) =
        trait_proof.pred.hax_skip_binder_ref().generic_args.first()
    else {
        unreachable!("no `Self` type arg on a `Fn*` trait ref")
    };
    Some((trait_proof.pred.rebind(self_ty), kind))
}

/// The built-in `Fn*` impl of the given kind that we generate for this closure or function item.
pub fn callable_virtual_impl<'a, 'tcx>(
    def: &'a hax::FullDef<'tcx>,
    s: &impl hax::BaseState<'tcx>,
    target_kind: ClosureKind,
) -> &'a hax::VirtualTraitImpl<'tcx> {
    CallableFnImpls::from_def(def, s, target_kind)
        .and_then(|impls| impls.vimpl)
        .expect("expected a callable with a Fn* impl")
}

#[derive(Copy, Clone)]
enum Callable<'a> {
    Closure(&'a hax::ClosureArgs),
    FnDef {
        item: &'a hax::ItemRef,
        sig: &'a hax::PolyFnSig,
        /// The arguments, tupled as the `Fn*` traits take them. Binds the same variables as `sig`.
        tupled_args_ty: &'a hax::Binder<hax::Ty>,
    },
    FnPtr {
        item: &'a hax::ItemRef,
        sig: &'a hax::PolyFnSig,
        tupled_args_ty: &'a hax::Binder<hax::Ty>,
    },
}

impl<'a> Callable<'a> {
    fn item(self) -> &'a hax::ItemRef {
        match self {
            Callable::Closure(args) => &args.item,
            Callable::FnDef { item, .. } => item,
            Callable::FnPtr { item, .. } => item,
        }
    }

    fn sig(self) -> &'a hax::PolyFnSig {
        match self {
            Callable::Closure(args) => &args.fn_sig,
            Callable::FnDef { sig, .. } => sig,
            Callable::FnPtr { sig, .. } => sig,
        }
    }

    /// The arguments, tupled as the `Fn*` traits take them, e.g. `(A, B, C)`. This is under the
    /// same binder as `sig`.
    fn tupled_args_ty(self) -> &'a hax::Ty {
        match self {
            Callable::Closure(args) => args.tupled_args_ty.hax_skip_binder_ref(),
            Callable::FnDef { tupled_args_ty, .. } => tupled_args_ty.hax_skip_binder_ref(),
            Callable::FnPtr { tupled_args_ty, .. } => tupled_args_ty.hax_skip_binder_ref(),
        }
    }
}

#[derive(Copy, Clone)]
struct CallableFnImpls<'a, 'tcx> {
    callable: Callable<'a>,
    /// The virtual impl of the requested `Fn*` trait, if the callable implements it.
    vimpl: Option<&'a hax::VirtualTraitImpl<'tcx>>,
}

impl<'a, 'tcx> CallableFnImpls<'a, 'tcx> {
    fn from_def(
        def: &'a hax::FullDef<'tcx>,
        s: &impl hax::BaseState<'tcx>,
        target_kind: ClosureKind,
    ) -> Option<Self> {
        let vimpl_from_impls = |impls: &'a hax::FnTraitImpls<'tcx>| -> Option<_> {
            Some(match target_kind {
                ClosureKind::FnOnce => impls.fn_once_impl.as_ref(),
                ClosureKind::FnMut => impls.fn_mut_impl.as_ref(),
                ClosureKind::Fn => impls.fn_impl.as_ref(),
            })
        };
        let for_fn_def = |sig: &'a hax::PolyFnSig, impls: &'a hax::FnTraitImpls<'tcx>| {
            Some(Self {
                callable: Callable::FnDef {
                    item: def.this(),
                    sig,
                    tupled_args_ty: &impls.tupled_args_ty,
                },
                vimpl: vimpl_from_impls(impls),
            })
        };
        match def.kind() {
            hax::FullDefKind::Closure(c) => Some(Self {
                callable: Callable::Closure(c.args()),
                vimpl: match target_kind {
                    ClosureKind::FnOnce => Some(c.fn_once_impl(s)),
                    ClosureKind::FnMut => c.fn_mut_impl(s),
                    ClosureKind::Fn => c.fn_impl(s),
                },
            }),
            hax::FullDefKind::Fn(f) => for_fn_def(f.sig(), f.fn_trait_impls(s)?),
            hax::FullDefKind::AssocFn(f) => for_fn_def(f.sig(), f.fn_trait_impls(s)?),
            hax::FullDefKind::Ctor(f) => for_fn_def(f.sig(), f.fn_trait_impls(s)?),
            hax::FullDefKind::FnPtr(f) => {
                let impls = f.fn_trait_impls(s)?;
                let sig = f.sig();
                Some(Self {
                    callable: Callable::FnPtr {
                        item: def.this(),
                        sig,
                        tupled_args_ty: &impls.tupled_args_ty,
                    },
                    vimpl: vimpl_from_impls(impls),
                })
            }
            _ => None,
        }
    }
}

/// References to callable items are subtle because there are three sources of lifetimes on top of
/// the normal generics: closure upvars, the higher-kindedness of the callable itself, and the
/// late-bound generics of the `call`/`call_mut` methods. One must be careful to choose the right
/// method from these.
impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Translate a reference to a callable item that takes late-bound lifetimes. The binder binds
    /// the late-bound lifetimes of the callable itself, if it is higher-kinded.
    fn translate_callable_bound_ref_with_late_bound(
        &mut self,
        span: Span,
        callable: Callable<'_>,
        kind: TransItemSourceKind,
    ) -> Result<RegionBinder<DeclRef<ItemId>>, Error> {
        if !matches!(
            kind,
            TransItemSourceKind::TraitImpl(..) | TransItemSourceKind::ClosureAsFnCast
        ) {
            raise_error!(
                self,
                span,
                "Called `translate_callable_bound_ref_with_late_bound` on a `{kind:?}`; \
                use `translate_closure_ref_with_upvars` \
                or `translate_callable_bound_ref_with_method_bound` instead"
            )
        }
        let dref: DeclRef<ItemId> = self.translate_item(span, callable.item(), kind)?;
        self.translate_region_binder(span, callable.sig(), |ctx, _| {
            let mut dref = dref.move_under_binder();
            // The regions for these item kinds have the fn late bound regions at the end.
            for (a, b) in dref.generics.regions.iter_mut().rev().zip(
                ctx.innermost_binder()
                    .params
                    .identity_args()
                    .regions
                    .into_iter()
                    .rev(),
            ) {
                *a = b;
            }
            Ok(dref)
        })
    }

    /// Translate a reference to a callable item that takes late-bound lifetimes and method
    /// lifetimes. The binder binds the late-bound lifetimes of the `call`/`call_mut` method
    /// (specified by `target_kind`).
    fn translate_callable_bound_ref_with_method_bound(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        kind: TransItemSourceKind,
        target_kind: ClosureKind,
    ) -> Result<RegionBinder<DeclRef<ItemId>>, Error> {
        if !matches!(kind, TransItemSourceKind::CallableMethod(..)) {
            raise_error!(
                self,
                span,
                "Called `translate_callable_bound_ref_with_method_bound` on a `{kind:?}`; \
                use `translate_closure_ref_with_upvars` \
                or `translate_callable_bound_ref_with_late_bound` instead"
            )
        }
        let dref: DeclRef<ItemId> = self.translate_item(span, item, kind)?;
        let mut dref = dref.move_under_binder();
        let mut regions = IndexVec::new();
        match target_kind {
            ClosureKind::FnOnce => {}
            ClosureKind::FnMut | ClosureKind::Fn => {
                let rid =
                    regions.push_with(|index| RegionParam::new(index, None, Variance::Covariant));
                *dref.generics.regions.iter_mut().last().unwrap() =
                    Region::Var(DeBruijnVar::new_at_zero(rid));
            }
        }
        Ok(RegionBinder {
            regions,
            skip_binder: dref,
        })
    }

    /// If this trait proof is the built-in impl of a `Fn*` trait for a closure, function item or
    /// function pointer, return the callable item and the kind of the implemented trait. The
    /// returned item has its regions erased.
    pub fn recognize_callable_impl_proof(
        &self,
        trait_proof: &hax::TraitProof,
    ) -> Option<(hax::ItemRef, ClosureKind)> {
        let hax::TraitProofKind::Builtin {
            trait_data: hax::BuiltinTraitData::Other(lang_item),
            ..
        } = &trait_proof.kind
        else {
            return None;
        };
        let target_kind = match lang_item {
            hax::SolverTraitLangItem::FnOnce => ClosureKind::FnOnce,
            hax::SolverTraitLangItem::FnMut => ClosureKind::FnMut,
            hax::SolverTraitLangItem::Fn => ClosureKind::Fn,
            _ => return None,
        };
        // We skip the binder and erase regions to avoid bound vars escaping.
        let hax::GenericArg::Type(callable_ty) = trait_proof
            .pred
            .hax_skip_binder_ref()
            .generic_args
            .first()?
        else {
            return None;
        };
        let item = match callable_ty.kind() {
            hax::TyKind::Closure(closure_args) => &closure_args.item,
            hax::TyKind::FnDef { item, .. } => item,
            hax::TyKind::FnPtr(_, item) => item,
            _ => return None,
        };
        Some((item.erase(self.hax_state_with_id()), target_kind))
    }

    pub(crate) fn translate_callable_method_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<Option<RegionBinder<FnPtr>>, Error> {
        if !self.monomorphize() {
            return Ok(None);
        }
        let Some(in_trait) = &item.in_trait else {
            return Ok(None);
        };
        let Some((callable, target_kind)) = self.recognize_callable_impl_proof(in_trait) else {
            return Ok(None);
        };
        let kind = TransItemSourceKind::CallableMethod(target_kind);
        let bound_ref = self.translate_callable_bound_ref_with_method_bound(
            span,
            &callable,
            kind,
            target_kind,
        )?;
        Ok(Some(bound_ref.map(|dref| {
            let fn_ref: FunDeclRef = dref.try_into().unwrap();
            FnPtr::new(FnPtrKind::Fun(fn_ref.id), fn_ref.generics)
        })))
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    /// Translate a reference to the closure ADT.
    pub fn translate_closure_type_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
    ) -> Result<TypeDeclRef, Error> {
        self.translate_type_decl_ref(span, &closure.item)
    }

    /// For stateless closures, translate a function reference to the top-level function that
    /// executes the closure code without taking the state as parameter.If you want to instantiate
    /// the binder, use the lifetimes from `self.closure_late_regions`.
    pub fn translate_stateless_closure_as_fn_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
    ) -> Result<RegionBinder<FunDeclRef>, Error> {
        let kind = TransItemSourceKind::ClosureAsFnCast;
        let bound_dref = self.translate_callable_bound_ref_with_late_bound(
            span,
            Callable::Closure(closure),
            kind,
        )?;
        Ok(bound_dref.map(|dref| dref.try_into().unwrap()))
    }

    /// Translate a reference to the chosen closure impl. The resulting value needs lifetime
    /// arguments for late-bound lifetimes. If you want to instantiate the binder, use the
    /// lifetimes from `self.closure_late_regions`.
    pub fn translate_closure_bound_impl_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<RegionBinder<TraitImplRef>, Error> {
        let kind = TransItemSourceKind::TraitImpl(TransImplSource::Callable(target_kind));
        let bound_dref = self.translate_callable_bound_ref_with_late_bound(
            span,
            Callable::Closure(closure),
            kind,
        )?;
        Ok(bound_dref.map(|dref| dref.try_into().unwrap()))
    }

    /// Translate a reference to the chosen callable impl.
    pub fn translate_callable_impl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        target_kind: ClosureKind,
    ) -> Result<TraitImplRef, Error> {
        self.translate_item(
            span,
            item,
            TransItemSourceKind::TraitImpl(TransImplSource::Callable(target_kind)),
        )
    }

    pub fn translate_closure_info(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<ClosureInfo, Error> {
        use ClosureKind::*;
        let kind = translate_closure_kind(&args.kind);

        let fn_once_impl = self.translate_closure_bound_impl_ref(span, args, FnOnce)?;
        let fn_mut_impl = if matches!(kind, FnMut | Fn) {
            Some(self.translate_closure_bound_impl_ref(span, args, FnMut)?)
        } else {
            None
        };
        let fn_impl = if matches!(kind, Fn) {
            Some(self.translate_closure_bound_impl_ref(span, args, Fn)?)
        } else {
            None
        };
        let signature = self.translate_poly_fun_sig(span, &args.fn_sig)?;
        Ok(ClosureInfo {
            kind,
            fn_once_impl,
            fn_mut_impl,
            fn_impl,
            signature,
        })
    }

    fn get_callable_state_ty(&mut self, span: Span, callable: Callable<'_>) -> Result<Ty, Error> {
        Ok(match callable {
            Callable::Closure(args) => {
                let tref = self.translate_closure_type_ref(span, args)?;
                TyKind::Adt(tref).into_ty()
            }
            Callable::FnDef { item, .. } => {
                let fn_ref = self.translate_bound_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                TyKind::FnDef(fn_ref).into_ty()
            }
            Callable::FnPtr { sig, .. } => {
                TyKind::FnPtr(self.translate_poly_fun_sig(span, sig)?).into_ty()
            }
        })
    }

    /// Translate the types of the captured variables. Should be called only in
    /// `translate_item_generics`. If you need these types, fetch them in
    /// `outermost_binder().closure_upvar_tys`.
    pub fn translate_closure_upvar_tys(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<IndexVec<FieldId, Ty>, Error> {
        args.upvar_tys
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()
    }

    pub fn translate_closure_adt(
        &mut self,
        span: Span,
        _args: &hax::ClosureArgs,
    ) -> Result<TypeDeclKind, Error> {
        let fields: IndexVec<FieldId, Field> = self
            .the_only_binder()
            .closure_upvar_tys
            .as_ref()
            .unwrap()
            .iter()
            .cloned()
            .enumerate()
            .map(|(field_id, ty)| Field {
                span,
                attr_info: AttrInfo::dummy_private(),
                name: format!("_{field_id}"),
                is_positional: true,
                ty,
            })
            .collect();
        Ok(TypeDeclKind::Struct(fields))
    }

    /// Given an item that is callable, generate the signature of the
    /// `call_once`/`call_mut`/`call` method (depending on `target_kind`).
    fn translate_callable_method_sig(
        &mut self,
        def: &hax::FullDef<'tcx>,
        span: Span,
        callable: Callable,
        target_kind: ClosureKind,
    ) -> Result<RegionBinder<FunSig>, Error> {
        let signature = callable.sig();
        trace!(
            "signature of callable {:?}:\n{:?}",
            def.def_id(),
            signature.value,
        );

        let mut bound_regions = IndexVec::new();
        let mut fun_sig = self
            .translate_fun_sig(span, signature.hax_skip_binder_ref())?
            .move_under_binder();
        let state_ty = self
            .get_callable_state_ty(span, callable)?
            .move_under_binder();

        // Depending on the kind of the closure generated, add a reference
        let state_ty = match target_kind {
            ClosureKind::FnOnce => state_ty,
            ClosureKind::Fn | ClosureKind::FnMut => {
                let rid = bound_regions
                    .push_with(|index| RegionParam::new(index, None, Variance::Covariant));
                let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                let mutability = if target_kind == ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                TyKind::Ref(r, state_ty, mutability).into_ty()
            }
        };

        let tupled_args_ty = self
            .translate_ty(span, callable.tupled_args_ty())?
            .move_under_binder();
        fun_sig.inputs = vec![state_ty, tupled_args_ty];

        Ok(RegionBinder {
            regions: bound_regions,
            skip_binder: fun_sig,
        })
    }

    fn translate_callable_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        target_kind: ClosureKind,
        callable: Callable,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        match callable {
            Callable::Closure(args) => {
                self.translate_closure_method_body(span, def, target_kind, args, signature)
            }
            Callable::FnDef { item, .. } => {
                self.translate_fn_def_method_body(span, item, signature)
            }
            Callable::FnPtr { .. } => self.translate_fn_ptr_method_body(span, signature),
        }
    }

    fn translate_closure_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        target_kind: ClosureKind,
        args: &hax::ClosureArgs,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        use ClosureKind::*;
        let closure_kind = translate_closure_kind(&args.kind);
        Ok(match (target_kind, closure_kind) {
            (Fn, Fn) | (FnMut, FnMut) | (FnOnce, FnOnce) => {
                // Translate the function's body normally
                let mut body = self.translate_def_body(span, def);
                // The body is translated as if the locals are: ret value, state, arg-1,
                // ..., arg-N, rest...
                // However, there is only one argument with the tupled closure arguments;
                // we must thus shift all locals with index >=2 by 1, and add a new local
                // for the tupled arg, giving us: ret value, state, args, arg-1, ...,
                // arg-N, rest...
                // We then add N statements of the form `locals[N+3] := move locals[2].N`,
                // to destructure the arguments.
                let Body::Unstructured(GExprBody {
                    locals,
                    body: blocks,
                    ..
                }) = &mut body
                else {
                    return Ok(body);
                };

                // The (Arg1, Arg2, ..) type.
                let tupled_ty = &signature.inputs[1];

                blocks.dyn_visit_mut(|local: &mut LocalId| {
                    if local.index() >= 2 {
                        *local += 1;
                    }
                });

                // Remember how many arguments there are
                let closure_arg_count = locals.arg_count - 1;
                let mut old_locals = mem::take(&mut locals.locals).into_iter();
                locals.arg_count = 2;
                locals.locals.push(old_locals.next().unwrap()); // ret
                locals.locals.push(old_locals.next().unwrap()); // state
                let tupled_arg = locals.new_var(Some("tupled_args".to_string()), tupled_ty.clone());
                locals.locals.extend(old_locals.map(|mut l| {
                    l.index += 1;
                    l
                }));

                let untupled_args = locals
                    .locals
                    .iter()
                    .skip(3)
                    .take(closure_arg_count)
                    .map(|l| &l.ty)
                    .cloned();
                let new_stts = untupled_args.enumerate().map(|(i, ty)| {
                    let nth_field = tupled_arg
                        .clone()
                        .project(ProjectionElem::Field(None, FieldId::new(i)), ty);
                    let local_id = LocalId::new(i + 3);
                    Statement::new(
                        span,
                        StatementKind::Assign(
                            locals.place_for_var(local_id),
                            Rvalue::Use(Operand::Move(nth_field), WithRetag::No),
                        ),
                    )
                });
                blocks[BlockId::ZERO].statements.splice(0..0, new_stts);

                body
            }
            // Target translation:
            //
            // fn call_once(state: Self, args: Args) -> Output {
            //   let temp_ref = &[mut] state;
            //   let ret = self.call[_mut](temp, args);
            //   drop state;
            //   return ret;
            // }
            //
            (FnOnce, Fn | FnMut) => {
                // Hax (via rustc) gives us the MIR to do this.
                let Some(body) = def.this.closure_once_shim(self.hax_state()) else {
                    panic!("missing shim for closure")
                };
                self.translate_body(span, body, &def.source_text)
            }
            // Target translation:
            //
            // fn call_mut(state: &mut Self, args: Args) -> Output {
            //   let reborrow = &*state;
            //   self.call(reborrow, args)
            // }
            (FnMut, Fn) => {
                let fun_id: FunDeclId = self.register_item(
                    span,
                    def.this(),
                    TransItemSourceKind::CallableMethod(closure_kind),
                );
                let impl_ref = self.translate_callable_impl_ref(span, &args.item, closure_kind)?;
                // TODO: make a trait call to avoid needing to concatenate things ourselves.
                // TODO: can we ask hax for the trait ref?
                let fn_op = FnOperand::Regular(FnPtr::new(
                    fun_id.into(),
                    impl_ref.generics.concat(&GenericArgs {
                        regions: vec![self.translate_erased_region()].into(),
                        ..GenericArgs::empty()
                    }),
                ));

                let mut builder = BodyBuilder::new(span, 2);

                let output = builder.new_var(None, signature.output.clone());
                let state = builder.new_var(Some("state".to_string()), signature.inputs[0].clone());
                let args = builder.new_var(Some("args".to_string()), signature.inputs[1].clone());
                let deref_state = state.deref();
                let reborrow_ty = TyKind::Ref(
                    self.translate_erased_region(),
                    deref_state.ty.clone(),
                    RefKind::Shared,
                )
                .into_ty();
                let reborrow = builder.new_var(None, reborrow_ty);

                builder.push_statement(StatementKind::Assign(
                    reborrow.clone(),
                    Rvalue::Ref {
                        place: deref_state,
                        kind: BorrowKind::Shared,
                        // The state must be Sized, hence `()` as ptr-metadata
                        ptr_metadata: Operand::mk_const_unit(),
                    },
                ));

                builder.call(Call {
                    func: fn_op,
                    args: vec![Operand::Move(reborrow), Operand::Move(args)],
                    dest: output,
                });

                Body::Unstructured(builder.build())
            }
            (Fn, FnOnce) | (Fn, FnMut) | (FnMut, FnOnce) => {
                panic!(
                    "Can't make a closure body for a more restrictive kind \
                    than the closure kind"
                )
            }
        })
    }

    fn translate_fn_def_method_body(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        let late_bound_regions = self
            .innermost_binder()
            .bound_region_vars
            .iter()
            .map(|rid| Region::Var(DeBruijnVar::new_at_zero(*rid)))
            .collect();
        let fn_ptr = self
            .translate_bound_fn_ptr(span, item, TransItemSourceKind::Fun)?
            .apply(late_bound_regions);
        let fn_op = FnOperand::Regular(fn_ptr);

        let mut builder = BodyBuilder::new(span, 2);

        let output = builder.new_var(None, signature.output.clone());
        let _state = builder.new_var(Some("state".to_string()), signature.inputs[0].clone());
        let tupled_args_ty = &signature.inputs[1];
        let tupled_args = builder.new_var(Some("args".to_string()), tupled_args_ty.clone());

        // We need the type declaration to have been translated to get the fields (since in monomorphic)
        // mode they aren't in the generics. So ensure it's been translated!
        let tuple_id = tupled_args_ty.as_adt().unwrap().id;
        let _ = self.get_or_translate(ItemId::Type(tuple_id))?;
        let arg_tys = tupled_args_ty.as_tuple_fields(&self.t_ctx.translated);

        let args = arg_tys
            .into_iter()
            .enumerate()
            .map(|(i, ty)| {
                let nth_field = tupled_args
                    .clone()
                    .project(ProjectionElem::Field(None, FieldId::new(i)), ty);
                Operand::Move(nth_field)
            })
            .collect();

        builder.call(Call {
            func: fn_op,
            args,
            dest: output,
        });

        Ok(Body::Unstructured(builder.build()))
    }

    fn translate_fn_ptr_method_body(
        &mut self,
        span: Span,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        let mut builder = BodyBuilder::new(span, 2);
        let output = builder.new_var(None, signature.output.clone());
        let fn_ptr = builder.new_var(Some("fn_ptr".to_string()), signature.inputs[0].clone());
        let tupled_args_ty = &signature.inputs[1];
        let tupled_args = builder.new_var(Some("args".to_string()), tupled_args_ty.clone());

        // `FnOnce::call_once` receives the function pointer directly, whereas `Fn::call` and
        // `FnMut::call_mut` receive it through a shared or mutable reference respectively.
        let fn_ptr = if matches!(fn_ptr.ty().kind(), TyKind::FnPtr(..)) {
            Operand::Copy(fn_ptr)
        } else {
            Operand::Copy(fn_ptr.deref())
        };
        let TyKind::FnPtr(fn_sig) = fn_ptr.ty().kind() else {
            unreachable!()
        };
        let late_bound_regions = self
            .innermost_binder()
            .bound_region_vars
            .iter()
            .map(|rid| Region::Var(DeBruijnVar::new_at_zero(*rid)))
            .collect();
        let arg_tys = fn_sig.clone().apply(late_bound_regions).inputs;
        let args = arg_tys
            .into_iter()
            .enumerate()
            .map(|(i, ty)| {
                let field = tupled_args
                    .clone()
                    .project(ProjectionElem::Field(None, FieldId::new(i)), ty);
                Operand::Move(field)
            })
            .collect();
        builder.call(Call {
            func: FnOperand::Dynamic(fn_ptr),
            args,
            dest: output,
        });
        Ok(Body::Unstructured(builder.build()))
    }

    /// Given an item that is a closure, generate the `call_once`/`call_mut`/`call` method
    /// (depending on `target_kind`).
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        target_kind: ClosureKind,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let callable_impls = CallableFnImpls::from_def(def, self.hax_state(), target_kind).unwrap();
        let callable = callable_impls.callable;

        // Hax gives us trait-related information for the impl we're building.
        let vimpl = callable_impls.vimpl.unwrap();
        let implemented_trait = self.translate_trait_predicate(span, &vimpl.trait_pred)?;
        let method_id = self.translate_trait_method_id(implemented_trait.id, &vimpl.methods[0])?;

        let impl_ref = self.translate_callable_impl_ref(span, callable.item(), target_kind)?;
        let src = FunSource::TraitImpl {
            impl_ref,
            trait_ref: implemented_trait.clone(),
            item_id: method_id,
            reuses_default: false,
        };

        // Translate the function signature
        let bound_sig = self.translate_callable_method_sig(def, span, callable, target_kind)?;
        // We give it the lifetime parameter we had prepared for that purpose.
        let signature = bound_sig.apply(
            self.the_only_binder()
                .closure_call_method_region
                .iter()
                .map(|r| Region::Var(DeBruijnVar::new_at_zero(*r)))
                .collect(),
        );

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.translate_callable_method_body(span, def, target_kind, callable, &signature)?
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

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
        target_kind: ClosureKind,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let callable_impls = CallableFnImpls::from_def(def, self.hax_state(), target_kind).unwrap();
        let callable = callable_impls.callable;

        // Hax gives us trait-related information for the impl we're building.
        let vimpl = callable_impls.vimpl.unwrap();
        let mut timpl = self.translate_virtual_trait_impl(
            def_id,
            item_meta,
            callable.item(),
            TransImplSource::Callable(target_kind),
            vimpl,
        )?;

        if self.monomorphize() {
            return Ok(timpl);
        }

        // Construct the `call_*` method reference.
        let trait_decl_id = timpl.impl_trait.id;
        let trait_method_id = self.translate_trait_method_id(trait_decl_id, &vimpl.methods[0])?;
        let call_fn_binder = {
            let kind = TransItemSourceKind::CallableMethod(target_kind);
            let bound_method_ref: RegionBinder<DeclRef<ItemId>> = self
                .translate_callable_bound_ref_with_method_bound(
                    span,
                    callable.item(),
                    kind,
                    target_kind,
                )?;
            let params = GenericParams {
                regions: bound_method_ref.regions,
                ..GenericParams::empty()
            };
            let fn_decl_ref: FunDeclRef = bound_method_ref.skip_binder.try_into().unwrap();
            Binder::new(
                BinderKind::TraitMethod(trait_decl_id, trait_method_id),
                params,
                fn_decl_ref,
            )
        };
        timpl
            .methods
            .set_slot_extend(trait_method_id, call_fn_binder);

        Ok(timpl)
    }

    /// Given an item that is a non-capturing closure, generate the equivalent function,
    /// by removing the state from the parameters and untupling the arguments.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_stateless_closure_as_fn(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let hax::FullDefKind::Closure(closure) = &def.kind else {
            unreachable!()
        };

        trace!("About to translate closure as fn:\n{:?}", def.def_id());

        let closure_args = closure.args();
        assert!(
            closure_args.upvar_tys.is_empty(),
            "Only stateless closures can be translated as functions"
        );

        // Translate the function signature
        let signature = self.translate_fun_sig(span, closure_args.fn_sig.hax_skip_binder_ref())?;
        let state_ty = self.get_callable_state_ty(span, Callable::Closure(closure_args))?;

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            // Target translation:
            //
            // fn call_fn(arg0: Args[0], ..., argN: Args[N]) -> Output {
            //   let closure: Closure = {};
            //   let args = (arg0, ..., argN);
            //   closure.call(args)
            // }
            let fun_id: FunDeclId = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::CallableMethod(ClosureKind::FnOnce),
            );
            let impl_ref =
                self.translate_callable_impl_ref(span, &closure_args.item, ClosureKind::FnOnce)?;
            let fn_op = FnOperand::Regular(FnPtr::new(fun_id.into(), impl_ref.generics.clone()));

            let mut builder = BodyBuilder::new(span, signature.inputs.len());

            let output = builder.new_var(None, signature.output.clone());
            let args: Vec<Place> = signature
                .inputs
                .iter()
                .enumerate()
                .map(|(i, ty)| builder.new_var(Some(format!("arg{}", i + 1)), ty.clone()))
                .collect();
            let args_tupled_ty =
                self.translate_ty(span, closure_args.tupled_args_ty.hax_skip_binder_ref())?;
            let args_tupled = builder.new_var(Some("args".to_string()), args_tupled_ty.clone());
            let state = builder.new_var(Some("state".to_string()), state_ty.clone());

            builder.push_statement(StatementKind::Assign(
                args_tupled.clone(),
                Rvalue::Aggregate(
                    AggregateKind::Adt(args_tupled_ty.as_adt().unwrap().clone(), None, None),
                    args.into_iter().map(Operand::Move).collect(),
                ),
            ));

            let state_ty_adt = state_ty.as_adt().unwrap();
            builder.push_statement(StatementKind::Assign(
                state.clone(),
                Rvalue::Aggregate(AggregateKind::Adt(state_ty_adt.clone(), None, None), vec![]),
            ));

            builder.call(Call {
                func: fn_op,
                args: vec![Operand::Move(state), Operand::Move(args_tupled)],
                dest: output,
            });

            Body::Unstructured(builder.build())
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src: FunSource::Normal,
            body,
        })
    }
}
