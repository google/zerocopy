use syn::{FnArg, GenericParam, Generics, Type, TypeParamBound};

pub struct SignatureTranslator;

impl SignatureTranslator {
    pub fn translate_generics(generics: &Generics) -> String {
        let mut context = String::new();
        // 1. Type parameters: {T : Type}
        for param in &generics.params {
            if let GenericParam::Type(type_param) = param {
                let name = &type_param.ident;
                context.push_str(&format!("{{{name} : Type}} "));
            }
        }

        // 2. Trait bounds: [inst : Bar T]
        for param in &generics.params {
            if let GenericParam::Type(type_param) = param {
                let name = &type_param.ident;
                for bound in &type_param.bounds {
                    if let TypeParamBound::Trait(trait_bound) = bound {
                        // Simplistic extraction of trait name
                        // e.g. std::fmt::Display -> Display
                        if let Some(segment) = trait_bound.path.segments.last() {
                            let trait_name = &segment.ident;
                            // Naming the instance: instTDisplay
                            // This needs to match what Aeneas expects or at least be unique.
                            // Aeneas often uses just unnamed instances or specific naming conventions.
                            // For stitching, we mostly need to accept them.
                            // User prompt example: `{T : Type} [inst : Bar T]`
                            context.push_str(&format!(
                                "[inst{name}{trait_name} : {trait_name} {name}] "
                            ));
                        }
                    }
                }
            }
        }
        context
    }

    pub fn detect_statefulness(args: &[FnArg]) -> bool {
        for arg in args {
            if let FnArg::Typed(pat_type) = arg {
                if let Type::Reference(type_ref) = &*pat_type.ty {
                    if type_ref.mutability.is_some() {
                        return true;
                    }
                }
            }
        }
        false
    }
}
