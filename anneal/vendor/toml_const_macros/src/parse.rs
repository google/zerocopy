//! Custom input syntax for proc-macro inputs

use std::fs;
use std::path::{Path, PathBuf};

use proc_macro2 as pm2;
use proc_macro2::{Delimiter, Group};
use quote::{quote, ToTokens, TokenStreamExt};
use syn::Ident;
use syn::{braced, parse::Parse, punctuated::Punctuated, LitStr};

#[derive(Clone)]
pub struct MultipleMacroInput(pub Vec<MacroInput>);

/// Input to [toml_const!](crate::toml_const)
#[derive(Clone)]
pub struct MacroInput {
    pub attrs: Vec<syn::Attribute>,

    // pub destructure_datetime: bool,
    /// Whether the static variable is public
    pub is_pub: bool,

    /// `false` if static, `true` if const
    pub static_const: bool,

    /// Static item identifier
    pub item_ident: Ident,

    /// `final` marks if the input file can be substituted
    pub is_final: bool,

    /// Path to the template file, mandatory
    pub path: LitStr,

    /// Any optional paths to substitute over the first path
    pub sub_paths: Option<Vec<UsePath>>,
}

/// A litstring path, with an optional use override keyword
#[derive(Clone)]
pub struct UsePath {
    pub path: LitStr,
    /// Manual use override in macro input
    pub is_used: bool,
}

impl Parse for MultipleMacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut macro_inputs = Vec::new();
        while !input.is_empty() {
            let macro_input: MacroInput = input.parse()?;
            macro_inputs.push(macro_input);
        }

        Ok(Self(macro_inputs))
    }
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        // parse docstring and datetime attr
        let attrs = input.call(syn::Attribute::parse_outer).unwrap_or_default();

        let is_pub: bool = {
            let lookahead = input.lookahead1();
            match lookahead.peek(syn::Token![pub]) {
                true => {
                    let _: syn::Token![pub] = input.parse()?;
                    true
                }
                false => false,
            }
        };

        let static_const = {
            let lookahead = input.lookahead1();

            if lookahead.peek(syn::Token![const]) {
                let _: syn::Token![const] = input.parse()?;
                true
            } else if lookahead.peek(syn::Token![static]) {
                let _: syn::Token![static] = input.parse()?;
                false
            } else {
                return Err(syn::Error::new(
                    input.span(),
                    "expected `static` or `const`",
                ));
            }
        };

        let item_ident: syn::Ident = input.parse()?;
        let _: syn::Token![:] = input.parse()?;

        let is_final = {
            let lookahead = input.lookahead1();

            match lookahead.peek(syn::Token![final]) {
                true => {
                    let _: syn::Token![final] = input.parse()?;
                    true
                }
                false => false,
            }
        };

        let template: LitStr = input.parse()?;

        let lookahead = input.lookahead1();
        let sub_paths = match lookahead.peek(syn::Token![;]) {
            true => {
                let _: syn::Token![;] = input.parse()?;
                None
            }
            false => match lookahead.peek(syn::token::Brace) {
                true => {
                    let content;
                    braced!(content in input);

                    let lit_str_vec =
                        Punctuated::<UsePath, syn::token::Semi>::parse_terminated(&content)?;

                    let res = lit_str_vec.into_iter().collect::<Vec<_>>();
                    Some(res)
                }
                false => return Err(syn::Error::new(input.span(), "expected {} or ;")),
            },
        };

        match is_final && sub_paths.is_some() {
            true => Err(syn::Error::new(
                template.span(),
                "final inputs cannot accept substitutions",
            )),
            false => Ok(Self {
                attrs,
                is_pub,
                static_const,
                item_ident,
                is_final,
                path: template,
                sub_paths,
            }),
        }
    }
}

impl ToTokens for MacroInput {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        for attr in &self.attrs {
            attr.to_tokens(tokens);
        }

        if self.is_pub {
            quote! {pub}.to_tokens(tokens);
        }

        match self.static_const {
            true => quote! {const}.to_tokens(tokens),
            false => quote! {static}.to_tokens(tokens),
        }

        self.item_ident.to_tokens(tokens);
        quote! {:}.to_tokens(tokens);

        if self.is_final {
            quote! {final}.to_tokens(tokens);
        }

        self.path.to_tokens(tokens);

        match &self.sub_paths {
            Some(sub) => {
                let subs = sub.iter().collect::<Punctuated<_, syn::Token![;]>>();

                let subs = match subs.len() {
                    0 => quote! {#subs},
                    _ => quote! {#subs;},
                };

                tokens.append(Group::new(Delimiter::Brace, subs.to_token_stream()));
            }
            None => quote! {;}.to_tokens(tokens),
        }
    }
}

impl Parse for UsePath {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let is_used = {
            let lookahead = input.lookahead1();
            match lookahead.peek(syn::Token![use]) {
                true => {
                    let _: syn::Token![use] = input.parse()?;
                    true
                }
                false => false,
            }
        };

        let path: LitStr = input.parse()?;

        Ok(Self { path, is_used })
    }
}

impl ToTokens for UsePath {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        if self.is_used {
            quote! {use}.to_tokens(tokens);
        }

        self.path.to_tokens(tokens);
    }
}

impl MacroInput {
    /// Return one or more const definitions to an underscore expression (`_`).
    /// If the path does not point to a file, it will not be included.
    ///
    /// These are calls to [include_str!] containing absolute paths.
    pub fn to_const_defs(&self, base_path: &Path) -> pm2::TokenStream {
        let mut template_path = base_path.to_path_buf();
        template_path.push(PathBuf::from(&self.path.value()));
        let template_path = pathbuf_to_str(&template_path);

        let mut const_defs = vec![quote! {const _: &'static str = include_str!(#template_path);}];

        if let Some(sp) = &self.sub_paths {
            let additions = sp.iter().map(|sub_path| {
                let mut abs_sub_path = base_path.to_path_buf();
                abs_sub_path.push(PathBuf::from(sub_path.path.value()));

                match abs_sub_path.exists() {
                    true => match abs_sub_path.is_file() {
                        true => {
                            let sub_path = pathbuf_to_str(&abs_sub_path);

                            quote! {
                                const _: &'static str = include_str!(#sub_path);
                            }
                        }
                        false => syn::Error::new(
                            sub_path.path.span(),
                            format!("path {} is not a file", abs_sub_path.display()),
                        )
                        .to_compile_error()
                        .to_token_stream(),
                    },
                    false => quote! {},
                }
            });

            const_defs.extend(additions);
        }

        const_defs.into_iter().collect::<pm2::TokenStream>()
    }

    /// Create a clone of `self` with all inner paths turned to absolute paths.
    ///
    /// The input base path must be absolute.
    pub fn to_abs_path(&self, base_path: &Path) -> Self {
        let mut abs_base_path = base_path.to_path_buf();

        abs_base_path.push(PathBuf::from(self.path.value()));
        let abs_base_path = LitStr::new(pathbuf_to_str(&abs_base_path), self.path.span());

        let sub_paths = self.sub_paths.clone();
        let sub_paths = sub_paths.map(|sp| {
            sp.into_iter()
                .map(|p| {
                    let mut abs_sub_path = base_path.to_path_buf();
                    abs_sub_path.push(PathBuf::from(p.path.value()));
                    let new_path = LitStr::new(pathbuf_to_str(&abs_sub_path), p.path.span());

                    UsePath {
                        path: new_path,
                        ..p
                    }
                })
                .collect::<Vec<_>>()
        });

        Self {
            path: abs_base_path,
            sub_paths,
            ..self.clone()
        }
    }

    /// With the the data in `self`, read in the template file and apply any substitutions
    pub fn generate_toml_table(&self) -> Result<toml::Table, pm2::TokenStream> {
        let template_toml = read_litstr_to_toml(&self.path)?.ok_or(
            syn::Error::new(
                self.path.span(),
                format!("unable to read template file: {}", self.path.value()),
            )
            .to_compile_error(),
        )?;

        let substitute_file = match &self.sub_paths {
            Some(paths) => {
                let mut res_sub = None;

                for sub_path in paths.iter() {
                    let sub_toml = read_litstr_to_toml(&sub_path.path)?;
                    let sub_toml = match sub_toml {
                        Some(st) => st,
                        None => continue,
                    };

                    match (sub_path.is_used, sub_toml.contains_key("use")) {
                        // macro-level override
                        (true, _) => {
                            res_sub = Some(sub_toml);
                            break;
                        }
                        // toml-level override
                        (false, true) => {
                            let use_val = sub_toml.get("use").expect("already checked");
                            if let toml::Value::Boolean(true) = use_val {
                                res_sub = Some(sub_toml);
                                break;
                            }
                        }
                        (false, false) => continue,
                    }
                }

                res_sub
            }
            None => None,
        };

        let merged = match substitute_file {
            Some(sf) => merge_tables(&template_toml, &sf),
            None => template_toml,
        };

        Ok(merged)
    }

    pub fn doc_attrs(&self) -> Vec<&syn::Attribute> {
        self.attrs
            .iter()
            .filter(|a| match a.meta.require_name_value() {
                Ok(nv) => nv.path.is_ident("doc"),
                Err(_) => false,
            })
            .collect()
    }
}

/// Merge a toml template with a changes table. Changes will set/overwrite values in the template.
/// If both values are tables, merge recursively. If both are arrays, merge arrays element-wise.
/// Otherwise, the value from `changes` overrides the value from `template`.
fn merge_tables(template: &toml::Table, changes: &toml::Table) -> toml::Table {
    let mut merged_table = template.clone();

    for (key, value) in changes.iter() {
        match (merged_table.get(key), value) {
            (Some(toml::Value::Table(orig)), toml::Value::Table(chg)) => {
                merged_table.insert(key.clone(), toml::Value::Table(merge_tables(orig, chg)));
            }
            (Some(toml::Value::Array(orig)), toml::Value::Array(chg)) => {
                let mut merged_array = orig.clone();
                let min_len = merged_array.len().min(chg.len());
                // Overwrite elements in orig with those in chg, element-wise
                for i in 0..min_len {
                    merged_array[i] = match (&merged_array[i], &chg[i]) {
                        (toml::Value::Table(orig_t), toml::Value::Table(chg_t)) => {
                            toml::Value::Table(merge_tables(orig_t, chg_t))
                        }
                        (toml::Value::Array(orig_a), toml::Value::Array(chg_a)) => {
                            // Recursively merge arrays
                            let merged = merge_arrays(orig_a, chg_a);
                            toml::Value::Array(merged)
                        }
                        (_, chg_v) => chg_v.clone(),
                    };
                }
                // If chg is longer, append the extra elements
                if chg.len() > merged_array.len() {
                    merged_array.extend_from_slice(&chg[merged_array.len()..]);
                }
                merged_table.insert(key.clone(), toml::Value::Array(merged_array));
            }
            // Otherwise, just override
            _ => {
                merged_table.insert(key.clone(), value.clone());
            }
        }
    }

    merged_table
}

/// Merge two TOML arrays element-wise, recursively merging tables/arrays, otherwise replacing.
fn merge_arrays(orig: &[toml::Value], chg: &[toml::Value]) -> Vec<toml::Value> {
    let mut merged = orig.to_vec();
    let min_len = orig.len().min(chg.len());
    for i in 0..min_len {
        merged[i] = match (&orig[i], &chg[i]) {
            (toml::Value::Table(orig_t), toml::Value::Table(chg_t)) => {
                toml::Value::Table(merge_tables(orig_t, chg_t))
            }
            (toml::Value::Array(orig_a), toml::Value::Array(chg_a)) => {
                toml::Value::Array(merge_arrays(orig_a, chg_a))
            }
            (_, chg_v) => chg_v.clone(),
        };
    }
    if chg.len() > orig.len() {
        merged.extend_from_slice(&chg[orig.len()..]);
    }
    merged
}

fn pathbuf_to_str(input: &Path) -> &str {
    input.to_str().expect("failed to convert path to str")
}

/// Read in a litstr path to a toml file, return an error tokenstream if it fails.
fn read_litstr_to_toml(litstr: &LitStr) -> Result<Option<toml::Table>, pm2::TokenStream> {
    let path = PathBuf::from(litstr.value());

    // we allow paths that do not resolve to a file
    if !path.exists() {
        return Ok(None);
    }

    let file = match fs::read_to_string(path) {
        Ok(tf) => tf,
        Err(e) => {
            return Err(syn::Error::new(litstr.span(), e.to_string())
                .to_compile_error()
                .to_token_stream());
        }
    };

    let template_toml: toml::Table = match toml::from_str(&file) {
        Ok(tt) => tt,
        Err(e) => {
            return Err(syn::Error::new(litstr.span(), e.to_string())
                .to_compile_error()
                .to_token_stream());
        }
    };

    Ok(Some(template_toml))
}

#[cfg(test)]
mod tests {

    use super::*;

    /// Test parsing of some syntax, as well as checking that the re-generated token stream
    /// is the same as the input.
    macro_rules! test_parse {
        ($data_type: ident: $test_fn: ident {$($tokens: tt)*}) => {
            #[test]
            fn $test_fn() {
                let tokens = quote::quote! {
                    $($tokens)*
                };
                let input: $data_type = syn::parse2(tokens.clone()).expect("failed to parse input from tokenstream");

                let output = input.to_token_stream();
                assert_eq!(tokens.to_string(), output.to_string(), "generated tokenstream and original tokenstream do not match");
            }
        };
    }

    test_parse!(MacroInput: test_parse_template_new {
        const X: "some_file_path.toml";
    });

    test_parse!(MacroInput: test_parse_template_empty_brace {
        const X: "some_file_path.toml" {}
    });

    test_parse!(MacroInput: test_parse_template_and_subs {
        pub const X: "some_file_path.toml" {
            "some_sub_file_path.toml";
            "some_other_sub_file_path.toml";
        }
    });

    test_parse!(MacroInput: test_parse_public_static {
        pub static X: "some_file_path.toml" {
            "some_sub_file_path.toml";
            "some_other_sub_file_path.toml";
        }
    });

    test_parse!(MacroInput: test_parse_template_use_subs {
        pub const X: "some_file_path.toml" {
            use "some_sub_file_path.toml";
            "some_other_sub_file_path.toml";
        }
    });

    test_parse!(MacroInput: test_parse_template_final {
        pub const X: final "some_file_path.toml";
    });

    test_parse!(MacroInput: test_parse_template_with_attributes {
        /// Docstring = #[doc = "Docstring"]
        /// Another docstring line
        pub const X: final "some_file_path.toml";
    });

    test_parse!(UsePath: test_parse_use_path_used {
        use "some_file_path.toml"
    });

    test_parse!(UsePath: test_parse_use_path_unused {
        "some_file_path.toml"
    });
}
