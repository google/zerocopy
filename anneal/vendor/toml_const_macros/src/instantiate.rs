//! Struct instantiation crate.
//!
//! A toml table is converted to a custom struct.
//! The identifier of the struct is used as the struct's type.

use proc_macro2::{self as pm2, Span};
use quote::quote;
use syn::{punctuated::Punctuated, Ident};

use crate::TomlValue;

/// Chars to replace when converting to an identifier.
const REPLACE_CHARS: &[char] = &[' ', '-', '_', ':', '.', '/', '\\', '"'];

/// Generate the instantiation of an item. This can be a custom struct or a simple value.
/// If a key is provided, the instantiation will be in a field-value pair.
///
/// Keys are not provided if:
/// - the table is the root table
/// - the value is defined as an element in an array
///
/// This is basically a wrapper around [quote::ToTokens].
pub trait Instantiate {
    fn instantiate(
        &self,
        key: &str,
        toml_value: &TomlValue,
        parents: Vec<&Ident>,
    ) -> pm2::TokenStream;
}

/// Create identifiers for variables and types from a string.
pub trait ConstIdentDef {
    /// Create a valid variable identifier, formatted as SCREAMING_SNAKE_CASE.
    fn to_variable_ident(&self) -> syn::Ident;

    /// Create a valid module identifier, formatted as snake_case.
    fn to_module_ident(&self) -> syn::Ident {
        syn::Ident::new_raw(
            &self.to_variable_ident().to_string().to_lowercase(),
            Span::call_site(),
        )
    }

    /// Create a valid type identifier, formatted as PascalCase.
    fn to_type_ident(&self) -> syn::Ident;

    // /// Create an array type identifier formatted as PascalCase.
    // fn to_array_type_ident(&self) -> String {
    //     format!("{}Item", self.to_type_ident())
    // }
}

impl<T> ConstIdentDef for T
where
    T: AsRef<str>,
{
    fn to_variable_ident(&self) -> syn::Ident {
        let self_ref = self.as_ref();

        let inter = self_ref.replace(REPLACE_CHARS, "_");

        let inter = inter
            .split('_')
            .map(|item| item.to_uppercase())
            .collect::<Vec<_>>()
            .join("_");

        let inter = match inter.starts_with(char::is_numeric) {
            true => format!("_{}", inter),
            false => inter,
        };

        syn::Ident::new(&inter, Span::call_site())
    }

    fn to_type_ident(&self) -> syn::Ident {
        let inter = self.as_ref().replace(REPLACE_CHARS, "_");

        let inter = match inter.contains("_") {
            true => inter
                .split('_')
                .map(|item| {
                    let mut chars = item.chars();

                    match chars.next() {
                        Some(c) => {
                            let first_char = c.to_ascii_uppercase();
                            let rest = chars.collect::<String>().to_ascii_lowercase();
                            format!("{}{}", first_char, rest)
                        }
                        None => String::new(),
                    }
                })
                .collect::<String>(),
            false => {
                // split at a capital letter, but preserve the letter
                let inter = inter.chars().fold(String::new(), |mut acc, c| {
                    if c.is_uppercase() && !acc.is_empty() {
                        acc.push('_');
                    }
                    acc.push(c);
                    acc
                });

                inter
                    .split("_")
                    .map(|item| {
                        let mut chars = item.chars();

                        match chars.next() {
                            Some(c) => {
                                let first_char = c.to_ascii_uppercase();
                                let rest = chars.collect::<String>().to_ascii_lowercase();
                                format!("{}{}", first_char, rest)
                            }
                            None => String::new(),
                        }
                    })
                    .collect::<String>()

                // todo!()
            }
        };

        let inter = match inter.starts_with(char::is_numeric) {
            true => format!("_{}", inter),
            false => inter,
        };

        syn::Ident::new(&inter, Span::call_site())
    }
}

impl Instantiate for toml::Value {
    fn instantiate(
        &self,
        key: &str,
        toml_value: &TomlValue,
        parents: Vec<&Ident>,
    ) -> proc_macro2::TokenStream {
        use toml::Value::*;

        match self {
            // cases when items are instantiated as fields in an array
            String(val) => quote! { #val },
            Integer(val) => quote! { #val },
            Float(val) => quote! { #val },
            Boolean(val) => quote! { #val },

            // items with inner impls
            Datetime(datetime) => datetime.instantiate(key, toml_value, vec![]),
            Array(values) => values.instantiate(key, toml_value, parents),
            Table(map) => map.instantiate(key, toml_value, parents),
        }
    }
}

impl Instantiate for toml::Table {
    fn instantiate(
        &self,
        key: &str,
        toml_value: &TomlValue,
        parents: Vec<&Ident>,
    ) -> proc_macro2::TokenStream {
        let table_type = key.to_type_ident();
        let table_mod = key.to_module_ident();

        let table_ty = match parents.len() {
            0 => {
                quote! { #table_type }
            }
            _ => {
                let p = parents.iter().collect::<Punctuated<_, syn::Token![::]>>();
                quote! { #p :: #table_type }
            }
        };

        let mut parents = parents.clone();
        parents.push(&table_mod);

        let new_params = match toml_value {
            TomlValue::Table(tab) => tab
                .iter()
                .map(|(key, val)| {
                    let inner_val = self.get(key).expect("key should exist in table");

                    inner_val.instantiate(key, val, parents.clone())
                })
                .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>(),
            TomlValue::TableMap {
                keys,
                first,
                value_type,
            } => {
                let map_vals = keys
                    .iter()
                    .map(|k| {
                        let key_lit = syn::LitStr::new(k, Span::call_site());

                        let value = self.get(k).expect("key should exist in table");
                        let value = value.instantiate(first, value_type, parents.clone());

                        quote! {#key_lit => #value}
                    })
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let map_value = quote! {{
                    use toml_const::phf;
                    &toml_const::phf_map_macro! {
                        #map_vals
                    }
                }};

                self.iter()
                    .map(|(_, f_val)| f_val.instantiate(first, value_type, parents.clone()))
                    .chain([map_value])
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>()
            }
            _ => unimplemented!("expected a table or table map"),
        };

        quote! {
            #table_ty::new(
                #new_params
            )
        }
    }
}

impl Instantiate for toml::value::Array {
    fn instantiate(
        &self,
        key: &str,
        toml_value: &TomlValue,
        parents: Vec<&Ident>,
    ) -> proc_macro2::TokenStream {
        let arr = if let TomlValue::Array(arr) = toml_value {
            arr
        } else {
            unimplemented!("expected a toml array value");
        };

        let val = match arr.first() {
            Some(v) => v,
            None => return quote! { &[] },
        };

        let elements = self
            .iter()
            .map(|elem| elem.instantiate(key, val, parents.clone()))
            .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

        quote! {
            &[ #elements ]
        }
    }
}

// datetime structs do not require a key, as they are already defined.
impl Instantiate for toml::value::Datetime {
    fn instantiate(&self, k: &str, _: &TomlValue, _: Vec<&Ident>) -> proc_macro2::TokenStream {
        match (self.date, self.time, self.offset) {
            (Some(d), Some(t), Some(o)) => {
                let d = d.instantiate(k, &TomlValue::Boolean, vec![]);
                let t = t.instantiate(k, &TomlValue::Boolean, vec![]);
                let o = o.instantiate(k, &TomlValue::Boolean, vec![]);

                quote! {
                    toml_const::OffsetDateTime {
                        date: #d,
                        time: #t,
                        offset: #o
                    }
                }
            }
            (Some(d), Some(t), None) => {
                let d = d.instantiate(k, &TomlValue::Boolean, vec![]);
                let t = t.instantiate(k, &TomlValue::Boolean, vec![]);

                quote! {
                    toml_const::LocalDateTime {
                        date: #d,
                        time: #t
                    }
                }
            }
            (Some(d), None, None) => {
                let d = d.instantiate(k, &TomlValue::Boolean, vec![]);

                quote! {
                    toml_const::LocalDate {
                        date: #d
                    }
                }
            }
            (None, Some(t), None) => {
                let t = t.instantiate(k, &TomlValue::Boolean, vec![]);

                quote! {
                    toml_const::LocalTime {
                        time: #t
                    }
                }
            }

            _ => unimplemented!("unsupported datetime combination"),
        }
    }
}

// sub structs do not require key, they implement `Key::Element`.
impl Instantiate for toml::value::Date {
    fn instantiate(&self, _: &str, _: &TomlValue, _: Vec<&Ident>) -> proc_macro2::TokenStream {
        let year = self.year;
        let month = self.month;
        let day = self.day;

        quote! {
            toml_const::Date {
                year: #year,
                month: #month,
                day: #day
            }
        }
    }
}

impl Instantiate for toml::value::Time {
    fn instantiate(&self, _: &str, _: &TomlValue, _: Vec<&Ident>) -> proc_macro2::TokenStream {
        let hour = self.hour;
        let minute = self.minute;
        let second = self.second;
        let nanosecond = self.nanosecond;

        quote! {
            toml_const::Time {
                hour: #hour,
                minute: #minute,
                second: #second,
                nanosecond: #nanosecond
            }
        }
    }
}

impl Instantiate for toml::value::Offset {
    fn instantiate(&self, _: &str, _: &TomlValue, _: Vec<&Ident>) -> proc_macro2::TokenStream {
        match self {
            toml::value::Offset::Z => quote! { toml_const::Offset::Z },
            toml::value::Offset::Custom { minutes } => quote! {
                toml_const::Offset::Custom {
                    minutes: #minutes
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn test_instantiation() {
        let cargo_manifest = include_str!("../Cargo.toml");
        let toml: toml::Table = toml::Table::from_str(cargo_manifest).unwrap();
        let value: TomlValue = toml.clone().into();

        let root_ident = Ident::new("ROOT_TABLE", Span::call_site());
        let instantiation = toml.instantiate(&root_ident.to_string(), &value, vec![]);

        println!("Table instantiation: {}", instantiation);
    }

    #[test]
    fn test_split_pascal_case() {
        let inter = "PascalCase";

        let inter = inter.chars().fold(String::new(), |mut acc, c| {
            if c.is_uppercase() && !acc.is_empty() {
                acc.push('_');
            }
            acc.push(c);
            acc
        });

        println!("inter: {inter}");

        let inter = "Pascal";

        let inter = inter.chars().fold(String::new(), |mut acc, c| {
            if c.is_uppercase() && !acc.is_empty() {
                acc.push('_');
            }
            acc.push(c);
            acc
        });

        println!("inter: {inter}");
    }
}
