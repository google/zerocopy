//! Generate USDT probes from an attribute macro

// Copyright 2024 Oxide Computer Company
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use proc_macro2::TokenStream;
use quote::quote;
use serde_tokenstream::from_tokenstream;
use syn::spanned::Spanned;
use usdt_impl::{CompileProvidersConfig, DataType, Probe, Provider};

/// Generate a provider from functions defined in a Rust module.
#[proc_macro_attribute]
pub fn provider(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr = TokenStream::from(attr);
    match from_tokenstream::<CompileProvidersConfig>(&attr) {
        Ok(config) => {
            // Renaming the module via the attribute macro isn't supported.
            if config.module.is_some() {
                syn::Error::new(
                    attr.span(),
                    "The provider module may not be renamed via the attribute macro",
                )
                .to_compile_error()
                .into()
            } else {
                generate_provider_item(TokenStream::from(item), config)
                    .unwrap_or_else(|e| e.to_compile_error())
                    .into()
            }
        }
        Err(e) => e.to_compile_error().into(),
    }
}

// Generate the actual provider implementation, include the type-checks and probe macros.
fn generate_provider_item(
    item: TokenStream,
    mut config: CompileProvidersConfig,
) -> Result<TokenStream, syn::Error> {
    let mod_ = syn::parse2::<syn::ItemMod>(item)?;
    if mod_.ident == "provider" {
        return Err(syn::Error::new(
            mod_.ident.span(),
            "Provider modules may not be named \"provider\"",
        ));
    }
    let content = &mod_
        .content
        .as_ref()
        .ok_or_else(|| {
            syn::Error::new(mod_.span(), "Provider modules must have one or more probes")
        })?
        .1;

    let mut check_fns = Vec::new();
    let mut probes = Vec::new();
    let mut use_statements = Vec::new();
    for (fn_index, item) in content.iter().enumerate() {
        match item {
            syn::Item::Fn(ref func) => {
                check_probe_name(&func.sig.ident)?;
                let signature = check_probe_function_signature(&func.sig)?;
                let mut item_check_fns = Vec::new();
                let mut item_types = Vec::new();
                for (arg_index, arg) in signature.inputs.iter().enumerate() {
                    match arg {
                        syn::FnArg::Receiver(item) => {
                            return Err(syn::Error::new(
                                item.span(),
                                "Probe functions may not take Self",
                            ));
                        }
                        syn::FnArg::Typed(ref item) => {
                            let (maybe_check_fn, item_type) =
                                parse_probe_argument(&item.ty, fn_index, arg_index)?;
                            if let Some(check_fn) = maybe_check_fn {
                                item_check_fns.push(check_fn);
                            }
                            item_types.push(item_type);
                        }
                    }
                }
                check_fns.extend(item_check_fns);
                probes.push(Probe {
                    name: signature.ident.to_string(),
                    types: item_types,
                });
            }
            syn::Item::Use(ref use_statement) => {
                verify_use_tree(&use_statement.tree)?;
                use_statements.push(use_statement.clone());
            }
            _ => {
                return Err(syn::Error::new(
                    item.span(),
                    "Provider modules may only include empty functions or use statements",
                ));
            }
        }
    }

    // We're guaranteed that the module name in the config is None. If the user has set the
    // provider name there, extract it. If they have _not_ set the provider name there, extract the
    // module name. In both cases, we don't support renaming the module via this path, so the
    // module name is passed through.
    let name = match &config.provider {
        Some(name) => {
            let name = name.to_string();
            config.module = Some(mod_.ident.to_string());
            name
        }
        None => {
            let name = mod_.ident.to_string();
            config.provider = Some(name.clone());
            config.module = Some(name.clone());
            name
        }
    };

    let provider = Provider {
        name,
        probes,
        use_statements: use_statements.clone(),
    };
    let compiled = usdt_impl::compile_provider(&provider, &config);
    let type_checks = if check_fns.is_empty() {
        quote! { const _: fn() = || {}; }
    } else {
        quote! {
            const _: fn() = || {
                #(#use_statements)*
                fn usdt_types_must_be_serialize<T: ?Sized + ::serde::Serialize>() {}
                #(#check_fns)*
            };
        }
    };
    Ok(quote! {
        #type_checks
        #compiled
    })
}

fn check_probe_name(ident: &syn::Ident) -> syn::Result<()> {
    let check = |name| {
        if ident == name {
            Err(syn::Error::new(
                ident.span(),
                format!("Probe functions may not be named \"{}\"", name),
            ))
        } else {
            Ok(())
        }
    };
    check("probe").and(check("start"))
}

fn parse_probe_argument(
    item: &syn::Type,
    fn_index: usize,
    arg_index: usize,
) -> syn::Result<(Option<TokenStream>, DataType)> {
    match item {
        syn::Type::Path(ref path) => {
            let last_ident = &path
                .path
                .segments
                .last()
                .ok_or_else(|| {
                    syn::Error::new(path.span(), "Probe arguments should resolve to path types")
                })?
                .ident;
            if is_simple_type(last_ident) {
                Ok((None, data_type_from_path(&path.path, false)))
            } else if last_ident == "UniqueId" {
                Ok((None, DataType::UniqueId))
            } else {
                let check_fn = build_serializable_check_function(item, fn_index, arg_index);
                Ok((Some(check_fn), DataType::Serializable(item.clone())))
            }
        }
        syn::Type::Ptr(ref pointer) => {
            if pointer.mutability.is_some() {
                return Err(syn::Error::new(item.span(), "Pointer types must be const"));
            }
            let ty = &*pointer.elem;
            if let syn::Type::Path(ref path) = ty {
                let last_ident = &path
                    .path
                    .segments
                    .last()
                    .ok_or_else(|| {
                        syn::Error::new(path.span(), "Probe arguments should resolve to path types")
                    })?
                    .ident;
                if !is_integer_type(last_ident) {
                    return Err(syn::Error::new(
                        item.span(),
                        "Only pointers to integer types are supported",
                    ));
                }
                Ok((None, data_type_from_path(&path.path, true)))
            } else {
                Err(syn::Error::new(
                    item.span(),
                    "Only pointers to path types are supported",
                ))
            }
        }
        syn::Type::Reference(ref reference) => {
            match parse_probe_argument(&reference.elem, fn_index, arg_index)? {
                (None, DataType::UniqueId) => Ok((None, DataType::UniqueId)),
                (None, DataType::Native(ty)) => Ok((None, DataType::Native(ty))),
                _ => Ok((
                    Some(build_serializable_check_function(item, fn_index, arg_index)),
                    DataType::Serializable(item.clone()),
                )),
            }
        }
        syn::Type::Array(_) | syn::Type::Slice(_) | syn::Type::Tuple(_) => {
            let check_fn = build_serializable_check_function(item, fn_index, arg_index);
            Ok((Some(check_fn), DataType::Serializable(item.clone())))
        }
        _ => Err(syn::Error::new(
            item.span(),
            concat!(
                "Probe arguments must be path types, slices, arrays, tuples, ",
                "references, or const pointers to integers",
            ),
        )),
    }
}

fn verify_use_tree(tree: &syn::UseTree) -> syn::Result<()> {
    match tree {
        syn::UseTree::Path(ref path) => {
            if path.ident == "super" {
                return Err(syn::Error::new(
                    path.span(),
                    concat!(
                        "Use-statements in USDT macros cannot contain relative imports (`super`), ",
                        "because the generated macros may be called from anywhere in a crate. ",
                        "Consider using `crate` instead.",
                    ),
                ));
            }
            verify_use_tree(&path.tree)
        }
        _ => Ok(()),
    }
}

// Create a function that statically asserts the given identifier implements `Serialize`.
fn build_serializable_check_function<T>(ident: &T, fn_index: usize, arg_index: usize) -> TokenStream
where
    T: quote::ToTokens,
{
    let fn_name = quote::format_ident!("usdt_types_must_be_serialize_{}_{}", fn_index, arg_index);
    quote! {
        fn #fn_name() {
            // #ident must be in scope here, because this function is defined in the same module as
            // the actual probe functions, and thus shares any imports the consumer wants.
            usdt_types_must_be_serialize::<#ident>()
        }
    }
}

// Return `true` if the type is an integer
fn is_integer_type(ident: &syn::Ident) -> bool {
    let ident = format!("{}", ident);
    matches!(
        ident.as_str(),
        "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64"
    )
}

// Return `true` if this type is "simple", a primitive type with an analog in D, i.e., _not_ a
// type that implements `Serialize`.
fn is_simple_type(ident: &syn::Ident) -> bool {
    let ident = format!("{}", ident);
    matches!(
        ident.as_str(),
        "u8" | "u16"
            | "u32"
            | "u64"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "String"
            | "str"
            | "usize"
            | "isize"
    )
}

// Return the `dtrace_parser::DataType` corresponding to the given `path`
fn data_type_from_path(path: &syn::Path, pointer: bool) -> DataType {
    use dtrace_parser::BitWidth;
    use dtrace_parser::DataType as DType;
    use dtrace_parser::Integer;
    use dtrace_parser::Sign;

    let variant = if pointer {
        DType::Pointer
    } else {
        DType::Integer
    };

    if path.is_ident("u8") {
        DataType::Native(variant(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Bit8,
        }))
    } else if path.is_ident("u16") {
        DataType::Native(variant(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Bit16,
        }))
    } else if path.is_ident("u32") {
        DataType::Native(variant(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Bit32,
        }))
    } else if path.is_ident("u64") {
        DataType::Native(variant(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Bit64,
        }))
    } else if path.is_ident("i8") {
        DataType::Native(variant(Integer {
            sign: Sign::Signed,
            width: BitWidth::Bit8,
        }))
    } else if path.is_ident("i16") {
        DataType::Native(variant(Integer {
            sign: Sign::Signed,
            width: BitWidth::Bit16,
        }))
    } else if path.is_ident("i32") {
        DataType::Native(variant(Integer {
            sign: Sign::Signed,
            width: BitWidth::Bit32,
        }))
    } else if path.is_ident("i64") {
        DataType::Native(variant(Integer {
            sign: Sign::Signed,
            width: BitWidth::Bit64,
        }))
    } else if path.is_ident("String") || path.is_ident("str") {
        DataType::Native(DType::String)
    } else if path.is_ident("isize") {
        DataType::Native(variant(Integer {
            sign: Sign::Signed,
            width: BitWidth::Pointer,
        }))
    } else if path.is_ident("usize") {
        DataType::Native(variant(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Pointer,
        }))
    } else {
        unreachable!("Tried to parse a non-path data type");
    }
}

// Sanity checks on a probe function signature.
fn check_probe_function_signature(
    signature: &syn::Signature,
) -> Result<&syn::Signature, syn::Error> {
    let to_err = |span, msg| Err(syn::Error::new(span, msg));
    if let Some(item) = signature.unsafety {
        return to_err(item.span(), "Probe functions may not be unsafe");
    }
    if let Some(ref item) = signature.abi {
        return to_err(item.span(), "Probe functions may not specify an ABI");
    }
    if let Some(ref item) = signature.asyncness {
        return to_err(item.span(), "Probe functions may not be async");
    }
    if !signature.generics.params.is_empty() {
        return to_err(
            signature.generics.span(),
            "Probe functions may not be generic",
        );
    }
    if !matches!(signature.output, syn::ReturnType::Default) {
        return to_err(
            signature.output.span(),
            "Probe functions may not specify a return type",
        );
    }
    Ok(signature)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dtrace_parser::BitWidth;
    use dtrace_parser::DataType as DType;
    use dtrace_parser::Integer;
    use dtrace_parser::Sign;
    use rstest::rstest;

    #[test]
    fn test_is_simple_type() {
        assert!(is_simple_type(&quote::format_ident!("u8")));
        assert!(!is_simple_type(&quote::format_ident!("Foo")));
    }

    #[test]
    fn test_data_type_from_path() {
        assert_eq!(
            data_type_from_path(&syn::parse_str("u8").unwrap(), false),
            DataType::Native(DType::Integer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            })),
        );
        assert_eq!(
            data_type_from_path(&syn::parse_str("u8").unwrap(), true),
            DataType::Native(DType::Pointer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            })),
        );
        assert_eq!(
            data_type_from_path(&syn::parse_str("String").unwrap(), false),
            DataType::Native(DType::String),
        );
        assert_eq!(
            data_type_from_path(&syn::parse_str("String").unwrap(), false),
            DataType::Native(DType::String),
        );
    }

    #[test]
    #[should_panic]
    fn test_data_type_from_path_panics() {
        data_type_from_path(&syn::parse_str("std::net::IpAddr").unwrap(), false);
    }

    #[rstest]
    #[case("u8", DType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit8 }))]
    #[case("*const u8", DType::Pointer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit8}))]
    #[case("&u8", DType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit8 }))]
    #[case("&str", DType::String)]
    #[case("String", DType::String)]
    #[case("&&str", DType::String)]
    #[case("&String", DType::String)]
    fn test_parse_probe_argument_native(#[case] name: &str, #[case] ty: dtrace_parser::DataType) {
        let arg = syn::parse_str(name).unwrap();
        let out = parse_probe_argument(&arg, 0, 0).unwrap();
        assert!(out.0.is_none());
        assert_eq!(out.1, DataType::Native(ty));
    }

    #[rstest]
    #[case("usdt::UniqueId")]
    #[case("&usdt::UniqueId")]
    fn test_parse_probe_argument_span(#[case] arg: &str) {
        let ty = syn::parse_str(arg).unwrap();
        let out = parse_probe_argument(&ty, 0, 0).unwrap();
        assert!(out.0.is_none());
        assert_eq!(out.1, DataType::UniqueId)
    }

    #[rstest]
    #[case("std::net::IpAddr")]
    #[case("&std::net::IpAddr")]
    #[case("&SomeType")]
    #[case("&&[u8]")]
    fn test_parse_probe_argument_serializable(#[case] name: &str) {
        let ty = syn::parse_str(name).unwrap();
        let out = parse_probe_argument(&ty, 0, 0).unwrap();
        assert!(out.0.is_some());
        assert_eq!(out.1, DataType::Serializable(ty));
        if let (Some(chk), DataType::Serializable(ty)) = out {
            println!("{}", quote! { #chk });
            println!("{}", quote! { #ty });
        }
    }

    #[test]
    fn test_check_probe_function_signature() {
        let signature = syn::parse_str::<syn::Signature>("fn foo(_: u8)").unwrap();
        assert!(check_probe_function_signature(&signature).is_ok());

        let check_is_err = |s| {
            let signature = syn::parse_str::<syn::Signature>(s).unwrap();
            assert!(check_probe_function_signature(&signature).is_err());
        };
        check_is_err("unsafe fn foo(_: u8)");
        check_is_err(r#"extern "C" fn foo(_: u8)"#);
        check_is_err("fn foo<T: Debug>(_: u8)");
        check_is_err("fn foo(_: u8) -> u8");
    }

    #[test]
    fn test_verify_use_tree() {
        let tokens = quote! { use std::net::IpAddr; };
        let item: syn::ItemUse = syn::parse2(tokens).unwrap();
        assert!(verify_use_tree(&item.tree).is_ok());

        let tokens = quote! { use super::SomeType; };
        let item: syn::ItemUse = syn::parse2(tokens).unwrap();
        assert!(verify_use_tree(&item.tree).is_err());

        let tokens = quote! { use crate::super::SomeType; };
        let item: syn::ItemUse = syn::parse2(tokens).unwrap();
        assert!(verify_use_tree(&item.tree).is_err());
    }
}
