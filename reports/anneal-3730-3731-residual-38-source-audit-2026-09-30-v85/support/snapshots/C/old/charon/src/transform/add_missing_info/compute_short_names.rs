use std::collections::{HashMap, hash_map::Entry};

use crate::ast::*;

use crate::transform::{TransformCtx, ctx::TransformPass};

enum FoundName<'a> {
    Unique {
        long: &'a [PathElem],
        ids: Vec<ItemId>,
    },
    Multiple,
}

fn register_short_name_candidate<'a>(
    short_names: &mut HashMap<String, FoundName<'a>>,
    short: String,
    long: &'a [PathElem],
    id: ItemId,
) {
    match short_names.entry(short) {
        Entry::Occupied(mut e) => match e.get_mut() {
            FoundName::Unique {
                long: found_long,
                ids,
            } => {
                if *found_long == long {
                    ids.push(id)
                } else {
                    e.insert(FoundName::Multiple);
                }
            }
            FoundName::Multiple => {}
        },
        Entry::Vacant(e) => {
            e.insert(FoundName::Unique {
                long,
                ids: vec![id],
            });
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut short_names: HashMap<String, FoundName> = Default::default();
        for (&id, name) in &ctx.translated.item_names {
            let mut name_slice = name.name.as_slice();

            // Trait impls are sufficiently unique information, so truncate starting from the
            // rightmost impl.
            if let Some((i, _)) = name_slice
                .iter()
                .enumerate()
                .rfind(|(_, elem)| matches!(elem, PathElem::Impl(ImplElem::Trait(..), ..)))
            {
                name_slice = &name.name[i..];
                let trunc_name = Name {
                    name: name_slice.to_vec(),
                };
                ctx.translated.short_names.insert(id, trunc_name);
            }

            if let [prefix @ .., PathElem::Instantiated(..)] = name_slice {
                name_slice = prefix;
            }
            // Ignoring monomorphizations, if a name is the only one to end with a given suffix, we
            // accumulate the ids of all the items with that name (there may be several thanks to
            // monomorphizations).
            let candidate = match name_slice {
                [.., PathElem::Ident(ident, _)] => Some(ident.clone()),
                [PathElem::Impl(ImplElem::Trait(impl_id))]
                    if let Some(trait_impl) = ctx.translated.trait_impls.get(*impl_id) =>
                {
                    trait_impl_short_name(&ctx.translated.item_names, trait_impl)
                }

                _ => None,
            };
            if let Some(short) = candidate {
                register_short_name_candidate(&mut short_names, short, name_slice, id);
            }
        }

        for (short, found) in short_names {
            if let FoundName::Unique { ids, .. } = found {
                for id in ids {
                    let mut short_name = Name {
                        name: vec![PathElem::Ident(short.clone(), Disambiguator::ZERO)],
                    };
                    if let [.., mono @ PathElem::Instantiated(..)] =
                        ctx.translated.item_names[&id].name.as_slice()
                    {
                        short_name.name.push(mono.clone());
                    }
                    ctx.translated.short_names.insert(id, short_name);
                }
            }
        }
    }
}

fn trait_impl_short_name(
    item_names: &SeqHashMap<ItemId, Name>,
    trait_impl: &TraitImpl,
) -> Option<String> {
    fn args_to_idents(
        item_names: &SeqHashMap<ItemId, Name>,
        generics: &GenericArgs,
    ) -> Vec<String> {
        generics
            .types
            .iter()
            .filter_map(|t| ty_to_idents(item_names, t))
            .collect()
    }

    fn ty_to_idents(item_names: &SeqHashMap<ItemId, Name>, ty: &Ty) -> Option<String> {
        Some(match ty.kind() {
            TyKind::Literal(literal) => literal.to_string(),
            TyKind::Slice(..) => "slice".to_owned(),
            TyKind::Array(..) => "array".to_owned(),
            TyKind::Adt(tref) => match tref.id {
                TypeId::Adt(id) => item_to_ident(item_names, ItemId::Type(id))?,
                TypeId::Builtin(builtin) => builtin.get_name().short_str()?.to_owned(),
                TypeId::Tuple if tref.generics.types.is_empty() => "unit".to_owned(),
                TypeId::Tuple => "tuple".to_owned(),
            },
            _ => return None,
        })
    }

    fn item_to_ident(item_names: &SeqHashMap<ItemId, Name>, id: ItemId) -> Option<String> {
        Some(item_names.get(&id)?.short_str()?.to_owned())
    }

    let trait_id = trait_impl.impl_trait.id;
    let (self_ty, partial_trait_ref) = trait_impl.impl_trait.split_self();
    let self_ty = self_ty.as_ref()?;

    let mut candidate = vec!["impl".to_owned()];
    candidate.push(item_to_ident(item_names, trait_id.into())?);
    candidate.extend(args_to_idents(item_names, &partial_trait_ref.generics));
    candidate.push("for".to_owned());
    candidate.push(if let TyKind::TypeVar(_) = self_ty.kind() {
        "T".to_string()
    } else {
        ty_to_idents(item_names, self_ty)?
    });
    if let TyKind::Adt(tref) = self_ty.kind() {
        candidate.extend(args_to_idents(item_names, &tref.generics));
    };
    Some(candidate.join("_"))
}
