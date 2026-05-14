//! Normalizing module, aka field inference.
//!
//! Normalization is the process of inferring missing fields in a TOML table inside arrays.
//! A user can define only the fields they care about, and the rest are initialized with default values.
//!
//! Steps to perform normalization are:
//! - Derive a normalized "schema" from the input TOML table. Arrays are reduced to 0/1 elements
//! - Using this normalized table, visit the original table and populate missing fields
//!
//! Empty fields are populated with default values:
//! - primitive types are set to their defaults
//! - arrays are empty
//! - dates are set to `1970-01-01T00:00:00Z`

use indexmap::IndexMap;
use proc_macro2 as pm2;
use proc_macro2::Span;
use quote::{quote, ToTokens};
use syn::{punctuated::Punctuated, Ident};
use toml::value::{Date, Datetime};

use crate::{instantiate::ConstIdentDef, MAP_FIELD};

const DEFAULT_DATE: Date = Date {
    year: 1970,
    month: 1,
    day: 1,
};
const DEFAULT_TIME: toml::value::Time = toml::value::Time {
    hour: 0,
    minute: 0,
    second: 0,
    nanosecond: 0,
};
const DEFAULT_OFFSET: toml::value::Offset = toml::value::Offset::Z;

#[derive(Clone, Debug)]
pub enum NormalizationError {
    /// A mismatch in value types.
    ///
    /// Sequence of keys in reverse order that leads to this mismatch.
    ValueMismatch {
        /// Reverse key path leading to the mismatch
        path: Vec<String>,

        /// Conflicting value types
        value_types: Box<(TomlValue, TomlValue)>,
    },
}

/// Working intermediate representation - contains only key and type information
#[derive(Clone, Debug, PartialEq)]
pub enum TomlValue {
    String,
    Integer,
    Float,
    Boolean,
    Datetime {
        date: bool,
        time: bool,
        offset: bool,
    },
    Array(Vec<TomlValue>),
    Table(IndexMap<String, TomlValue>),

    /// A table map is a subset of a table that contains identical values for all keys.
    TableMap {
        keys: Vec<String>,
        /// The key that table and array types inherit
        first: String,
        value_type: Box<TomlValue>,
    },
}

impl std::error::Error for NormalizationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }

    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        self.source()
    }
}

impl std::fmt::Display for NormalizationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NormalizationError::ValueMismatch { path, value_types } => {
                let path = path
                    .iter()
                    .rev()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join("::");

                write!(
                    f,
                    "Value mismatch at {} - found: {:?} and {:?}",
                    path, value_types.0, value_types.1
                )
            }
        }
    }
}

impl From<TomlValue> for toml::Value {
    fn from(value: TomlValue) -> Self {
        match value {
            TomlValue::String => toml::Value::String(Default::default()),
            TomlValue::Integer => toml::Value::Integer(Default::default()),
            TomlValue::Float => toml::Value::Float(Default::default()),
            TomlValue::Boolean => toml::Value::Boolean(Default::default()),
            TomlValue::Datetime { date, time, offset } => {
                toml::Value::Datetime(toml::value::Datetime {
                    date: if date { Some(DEFAULT_DATE) } else { None },
                    time: if time { Some(DEFAULT_TIME) } else { None },
                    offset: if offset { Some(DEFAULT_OFFSET) } else { None },
                })
            }
            TomlValue::Array(elements) => {
                toml::Value::Array(elements.into_iter().map(|e| e.into()).collect())
            }
            TomlValue::Table(sub_table) => {
                toml::Value::Table(sub_table.into_iter().map(|(k, v)| (k, v.into())).collect())
            }
            TomlValue::TableMap {
                keys, value_type, ..
            } => toml::Value::Table(
                keys.into_iter()
                    .map(|k| (k, (*value_type.clone()).into()))
                    .collect(),
            ),
        }
    }
}

impl From<toml::Value> for TomlValue {
    fn from(value: toml::Value) -> Self {
        match value {
            toml::Value::String(_) => Self::String,
            toml::Value::Integer(_) => Self::Integer,
            toml::Value::Float(_) => Self::Float,
            toml::Value::Boolean(_) => Self::Boolean,
            toml::Value::Datetime(datetime) => Self::Datetime {
                date: datetime.date.is_some(),
                time: datetime.time.is_some(),
                offset: datetime.offset.is_some(),
            },
            toml::Value::Array(values) => {
                Self::Array(values.into_iter().map(|v| v.into()).collect())
            }
            toml::Value::Table(map) => map.into(),
        }
    }
}

impl From<toml::Table> for TomlValue {
    fn from(value: toml::Table) -> Self {
        Self::Table(value.into_iter().map(|(k, v)| (k, v.into())).collect())
    }
}

impl TomlValue {
    /// This method assumes that [TomlValue::normalize] is already called.
    ///
    /// This will recursively visit and normalize all items in a [toml::Value].
    pub fn normalize_toml(&self, toml: &mut toml::Value) {
        match (self, toml) {
            (TomlValue::String, toml::Value::String(_))
            | (TomlValue::Integer, toml::Value::Integer(_))
            | (TomlValue::Float, toml::Value::Float(_))
            | (TomlValue::Boolean, toml::Value::Boolean(_)) => (),

            (
                TomlValue::Datetime {
                    date: tv_date,
                    time: tv_time,
                    offset: tv_offset,
                },
                toml::Value::Datetime(Datetime { date, time, offset }),
            ) => {
                if *tv_date && date.is_none() {
                    *date = Some(DEFAULT_DATE)
                }

                if *tv_time && time.is_none() {
                    *time = Some(DEFAULT_TIME)
                }

                if *tv_offset && offset.is_none() {
                    *offset = Some(DEFAULT_OFFSET)
                }
            }
            (TomlValue::Array(toml_values), toml::Value::Array(values)) => {
                if let Some(toml_value) = toml_values.first() {
                    for val in values {
                        toml_value.normalize_toml(val);
                    }
                }
            }
            (TomlValue::Table(hash_map), toml::Value::Table(map)) => {
                for (key, value) in hash_map {
                    match (map.get_mut(key), value) {
                        (Some(toml_value), _) => {
                            value.normalize_toml(toml_value);
                        }
                        // for missing keys that point to arrays, we initialize them as empty arrays
                        (None, TomlValue::Array(_)) => {
                            map.insert(key.to_owned(), toml::Value::Array(vec![]));
                        }
                        (None, _) => {
                            map.insert(key.to_owned(), value.clone().into());
                        }
                    }
                }
            }
            (
                TomlValue::TableMap {
                    keys, value_type, ..
                },
                toml::Value::Table(map),
            ) => {
                for key in keys {
                    match (map.get_mut(key), value_type.as_ref()) {
                        (Some(toml_value), _) => {
                            value_type.normalize_toml(toml_value);
                        }
                        (None, TomlValue::Array(_)) => {
                            map.insert(key.to_owned(), toml::Value::Array(vec![]));
                        }
                        (None, _) => {
                            map.insert(key.to_owned(), (*value_type.clone()).into());
                        }
                    }
                }
            }
            _ => unimplemented!("normalizing different types cannot be done"),
        }
    }

    /// Derive a normalized version of [Self].
    ///
    /// At this point, the schema of [Self] will be superset of the original.
    pub fn normalize(self) -> Result<Self, NormalizationError> {
        match self {
            TomlValue::Array(toml_values) => match toml_values.first() {
                Some(first) => {
                    let first_val = first.clone();
                    let normalized = toml_values.into_iter().try_fold(first_val, |acc, item| {
                        let inter = item.normalize()?;
                        acc.union(&inter)
                    })?;

                    Ok(TomlValue::Array(vec![normalized]))
                }
                None => Ok(TomlValue::Array(vec![])),
            },

            TomlValue::Table(toml_table) => {
                let norm_table = toml_table
                    .into_iter()
                    .map(|(k, v)| {
                        let normalized_value = v.normalize();
                        match normalized_value {
                            Ok(nv) => Ok((k.clone(), nv)),
                            Err(e) => Err(e.propagate(&k)),
                        }
                    })
                    .collect::<Result<IndexMap<String, TomlValue>, NormalizationError>>()?;

                Ok(TomlValue::Table(norm_table))
            }

            TomlValue::Datetime { date, time, offset } => {
                Ok(Self::resolve_date_time_offset(date, time, offset))
            }

            // everything else is already normalized
            other => Ok(other),
        }
    }

    /// Transform tables with identical values to table maps
    #[cfg(feature = "phf")]
    pub fn reduce(self) -> Self {
        match self {
            TomlValue::Table(tab) => {
                match tab.len() {
                    0 => TomlValue::Table(tab),
                    _ => {
                        // reduce inner first
                        let reduced_inner = tab
                            .into_iter()
                            .map(|(k, v)| (k, v.reduce()))
                            .collect::<IndexMap<_, _>>();

                        // let mut key_values = reduced_inner.iter();
                        // let (first_key, first_value) =
                        //     key_values.next().expect("already checked for empty table");

                        let (keys, values): (Vec<_>, Vec<_>) = reduced_inner.into_iter().unzip();
                        let first_val = &values[0];
                        let first_key = keys[0].to_string();

                        if values.iter().all(|v| first_val == v) {
                            TomlValue::TableMap {
                                keys,
                                first: first_key,
                                value_type: Box::new(first_val.clone()),
                            }
                        } else {
                            TomlValue::Table((keys.into_iter()).zip(values).collect())
                        }
                    }
                }
            }

            TomlValue::Array(arr) => {
                TomlValue::Array(arr.into_iter().map(|a| a.reduce()).collect())
            }
            // no need to reduce primitive types
            other => other,
        }
    }

    #[cfg(not(feature = "phf"))]
    pub fn reduce(self) -> Self {
        self
    }

    /// Calculate the union of two [TomlValue] types.
    ///
    /// This will first check if both types are the same, and then merge table and array types.
    /// Arrays will be reduced to lengths 1 or 0.
    fn union(&self, other: &Self) -> Result<Self, NormalizationError> {
        match (self, other) {
            (TomlValue::String, TomlValue::String) => Ok(TomlValue::String),
            (TomlValue::Integer, TomlValue::Integer) => Ok(TomlValue::Integer),
            (TomlValue::Float, TomlValue::Float) => Ok(TomlValue::Float),
            (TomlValue::Boolean, TomlValue::Boolean) => Ok(TomlValue::Boolean),
            (
                TomlValue::Datetime {
                    date: ld,
                    time: lt,
                    offset: lo,
                },
                TomlValue::Datetime {
                    date: rd,
                    time: rt,
                    offset: ro,
                },
            ) => Ok(TomlValue::Datetime {
                date: *ld || *rd,
                time: *lt || *rt,
                offset: *lo || *ro,
            }),

            (TomlValue::Array(arr_self), TomlValue::Array(arr_other)) => {
                let mut chained = arr_self.iter().chain(arr_other.iter());

                match chained.next() {
                    Some(first) => {
                        let merged = arr_self
                            .iter()
                            .chain(arr_other.iter())
                            .try_fold(first.to_owned(), |acc, item| acc.union(item))?;

                        Ok(TomlValue::Array(vec![merged]))
                    }
                    None => Ok(TomlValue::Array(vec![])),
                }
            }

            (TomlValue::Table(tab_self), TomlValue::Table(tab_other)) => {
                let mut merged = tab_self.clone();

                for (key, value) in tab_other {
                    match merged.get_mut(key) {
                        Some(existing_val) => {
                            match existing_val.union(value) {
                                Ok(u) => *existing_val = u,
                                Err(e) => Err(e.propagate(key))?,
                            };
                        }
                        None => {
                            merged.insert(key.to_string(), value.clone());
                        }
                    }
                }

                Ok(TomlValue::Table(merged))
            }

            err_other => Err(NormalizationError::ValueMismatch {
                path: vec![],
                value_types: Box::new((err_other.0.clone(), err_other.1.clone())),
            }),
        }
    }

    /// Some date-time combinations are not valid
    fn resolve_date_time_offset(date: bool, time: bool, offset: bool) -> TomlValue {
        match (date, time, offset) {
            // offset date time - anything containing offsets is promoted to offset date time
            (_, _, true) => TomlValue::Datetime {
                date: true,
                time: true,
                offset: true,
            },
            // local date time
            (true, true, false) => TomlValue::Datetime {
                date: true,
                time: true,
                offset: false,
            },
            // local date
            (true, false, false) => TomlValue::Datetime {
                date: true,
                time: false,
                offset: false,
            },
            // local time
            (false, true, false) => TomlValue::Datetime {
                date: false,
                time: true,
                offset: false,
            },
            (false, false, false) => {
                unimplemented!("datetime cannot be constructed without any components")
            }
        }
    }

    /// Return the type of a value.
    /// Arrays will descend and return their inner type.
    fn ty(&self, key: &str, parent_mod: Option<&Ident>) -> pm2::TokenStream {
        match self {
            TomlValue::String => quote! {&'static str},
            TomlValue::Integer => quote! {i64},
            TomlValue::Float => quote! {f64},
            TomlValue::Boolean => quote! {bool},
            TomlValue::Datetime { date, time, offset } => {
                let dt_ident = date_time_struct_ident(*date, *time, *offset);
                quote! { toml_const :: #dt_ident }
            }
            TomlValue::Array(toml_values) => {
                match toml_values.first() {
                    Some(inner) => {
                        let inner_type = inner.ty(key, parent_mod);

                        quote! { &'static [#inner_type] }
                    }
                    // default to string array
                    None => quote! { &'static [&'static str] },
                }
            }
            TomlValue::Table(_) | TomlValue::TableMap { .. } => {
                let self_type = key.to_type_ident();

                match parent_mod {
                    Some(parent) => quote! { #parent :: #self_type },
                    None => quote! { #self_type },
                }
            } // TomlValue::TableMap { keys, value_type } => {
              //     // &value_type.ty(key, parent_mod)

              //     todo!()
              // }
        }
    }

    /// Recursively define array and table types.
    ///
    /// `Self` should be normalized and reduced first.
    pub fn definition(&self, key: &str, derive_attrs: &[syn::Attribute]) -> pm2::TokenStream {
        match self {
            // do not need to define primitive/provided types
            TomlValue::String
            | TomlValue::Integer
            | TomlValue::Float
            | TomlValue::Boolean
            | TomlValue::Datetime { .. } => quote! {},

            TomlValue::Array(arr) => match arr.len() {
                0 => quote! {}, // instantiated as bool array
                1 => {
                    let inner_value = &arr[0];

                    inner_value.definition(key, derive_attrs)
                }
                _ => unimplemented!("normalized array should have 0 or 1 elements"),
            },
            TomlValue::Table(tab) => {
                let self_ident = key.to_type_ident();
                let self_mod = key.to_module_ident();

                // // we make the identifier in all values the same type, if all values in the table are the same.
                // let same_val_type = match tab.len() {
                //     0 => None,
                //     _ => {
                //         let mut key_vals = tab.iter();
                //         let (first_key, first_val) =
                //             key_vals.next().expect("already checked for empty table");

                //         match key_vals.all(|(_, v)| v == first_val) {
                //             true => Some(first_val.ty(first_key, Some(&self_mod))),
                //             false => None,
                //         }
                //     }
                // };

                // let mut x = 0;

                let constructor_fields = tab
                    .iter()
                    .map(|(k, v)| {
                        // x += 1;
                        // let field_ident = k.to_variable_ident();
                        let field_ident = k.to_module_ident();

                        let field_type = v.ty(k, Some(&self_mod));

                        quote! {
                            #field_ident: #field_type
                        }
                    })
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let struct_fields = constructor_fields
                    .iter()
                    .map(|k| {
                        quote! {pub #k}
                    })
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let inner_definitions = tab
                    .iter()
                    .filter(|(_, v)| {
                        matches!(
                            v,
                            TomlValue::Array(_) | TomlValue::Table(_) | TomlValue::TableMap { .. }
                        )
                    })
                    .map(|(k, v)| v.definition(k, derive_attrs))
                    .collect::<pm2::TokenStream>();

                let shorthand_init_fields = tab
                    .iter()
                    .map(|(k, _)| k.to_module_ident().to_token_stream())
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let derives = derive_attrs
                    .iter()
                    .map(|attr| quote! { #attr })
                    .collect::<pm2::TokenStream>();

                quote! {
                    #[derive(Clone, Copy, Debug)]
                    #derives
                    pub struct #self_ident {
                        #struct_fields
                    }

                    impl #self_ident {
                        #[doc(hidden)]
                        #[allow(clippy::too_many_arguments)]
                        pub const fn new(
                            #constructor_fields
                        ) -> Self {
                            Self {
                                #shorthand_init_fields
                            }
                        }
                    }

                    pub mod #self_mod {
                        #inner_definitions
                    }
                }
            }
            TomlValue::TableMap {
                keys,
                first,
                value_type,
            } => {
                let self_ident = key.to_type_ident();
                let self_mod = key.to_module_ident();
                let all_field_type = value_type.ty(first, Some(&self_mod));

                let map_field_ident = MAP_FIELD.to_module_ident();
                let phf_map_type = quote! {::toml_const::PhfMap<&'static str, #all_field_type>};

                // final map field type
                let map_field = quote! {
                    #map_field_ident: &'static #phf_map_type
                };

                let constructor_fields = keys
                    .iter()
                    .map(|k| {
                        let field_ident = k.to_module_ident();
                        quote! {
                            #field_ident: #all_field_type
                        }
                    })
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let struct_fields = constructor_fields
                    .iter()
                    .map(|k| {
                        quote! {pub #k}
                    })
                    .chain([map_field.clone()])
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let constructor_fields = constructor_fields
                    .into_iter()
                    .chain([map_field])
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let derives = derive_attrs
                    .iter()
                    .map(|attr| quote! { #attr })
                    .collect::<pm2::TokenStream>();

                let shorthand_init_fields = keys
                    .iter()
                    .map(|k| k.to_module_ident().to_token_stream())
                    .chain([map_field_ident.to_token_stream()])
                    .collect::<Punctuated<pm2::TokenStream, syn::Token![,]>>();

                let inner_definitions = value_type.definition(first, derive_attrs);

                quote! {
                    #[derive(Clone, Copy, Debug)]
                    #derives
                    pub struct #self_ident {
                        #struct_fields
                    }

                    impl #self_ident {
                        #[doc(hidden)]
                        #[allow(clippy::too_many_arguments)]
                        pub const fn new(
                            #constructor_fields
                        ) -> Self {
                            Self {
                                #shorthand_init_fields
                            }
                        }

                        pub const fn map(&'static self) -> &'static #phf_map_type {
                            self.#map_field_ident
                        }
                    }

                    pub mod #self_mod {
                        #inner_definitions
                    }
                }
            }
        }
    }
}

fn date_time_struct_ident(date: bool, time: bool, offset: bool) -> syn::Ident {
    match (date, time, offset) {
        (_, _, true) => syn::Ident::new("OffsetDateTime", Span::call_site()),
        (true, true, false) => syn::Ident::new("LocalDateTime", Span::call_site()),
        (true, false, false) => syn::Ident::new("LocalDate", Span::call_site()),
        (false, true, false) => syn::Ident::new("LocalTime", Span::call_site()),
        (false, false, false) => {
            unimplemented!("datetime cannot be constructed without any components")
        }
    }
}

impl NormalizationError {
    /// When receiving an error when performing some op on key+values, this function accumulates current key to the error.
    pub fn propagate(self, key: &str) -> NormalizationError {
        match self {
            // NormalizationError::KeyMismatch {
            //     path: mut tp,
            //     a_diff,
            //     b_diff,
            // } => {
            //     tp.push(key.to_string());

            //     NormalizationError::KeyMismatch {
            //         path: tp,
            //         a_diff,
            //         b_diff,
            //     }
            // }
            NormalizationError::ValueMismatch {
                mut path,
                value_types,
            } => {
                path.push(key.to_string());
                NormalizationError::ValueMismatch { path, value_types }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn test_parse_toml_toml_value() {
        const NORMALIZE_FILE: &str = include_str!("../Cargo.toml");

        let parsed = toml::Table::from_str(NORMALIZE_FILE).expect("must parse");
        let toml_val = TomlValue::from(parsed.clone());

        println!("original: {:#?}", toml_val);

        let normalized = match toml_val.normalize() {
            Ok(n) => n,
            Err(e) => panic!("{}", e),
        };
        println!("normalized: {:#?}", normalized);

        let mut og_value = toml::Value::Table(parsed.clone());
        normalized.normalize_toml(&mut og_value);
        let norm_table = og_value.as_table().unwrap();

        println!("norm table: {:#?}", norm_table);

        println!(
            "definition: {}",
            normalized.definition("TOP_LEVEL_TABLE", &[])
        );
    }

    #[test]
    fn test_normalize_error_value_mismatch() {
        let toml = r#"
        [[array]]
        key1 = "value1"
        key2 = 42

        [[array]]
        key1 = "value2"
        key2 = "invalid value"
        "#;

        let parsed = toml::Table::from_str(toml).expect("must parse");
        let toml_val = TomlValue::from(parsed.clone());
        match toml_val.normalize() {
            Ok(n) => {
                panic!("Normalization should have failed, but succeeded: {:#?}", n);
            }
            Err(e) => match e {
                NormalizationError::ValueMismatch { path, value_types } => {
                    assert!(path == ["key2".to_string(), "array".to_string()]);
                    assert!(matches!(value_types.0, TomlValue::Integer));
                    assert!(matches!(value_types.1, TomlValue::String));
                }
            },
        };

        let toml = r#"
        [[array]]
        [[array.table]]
        key2 = "false"
        key1 = "value1"
        [[array.table.inner]]
        item = "name"

        [[array]]
        [[array.table]]
        key1 = "value1"
        [[array.table.inner]]
        item = false
        "#;

        let parsed = toml::Table::from_str(toml).expect("must parse");
        let toml_val = TomlValue::from(parsed.clone());
        match toml_val.normalize() {
            Ok(n) => {
                panic!("Normalization should have failed, but succeeded: {:#?}", n);
            }
            Err(e) => match e {
                NormalizationError::ValueMismatch { path, value_types } => {
                    assert!(
                        path == [
                            "item".to_string(),
                            "inner".to_string(),
                            "table".to_string(),
                            "array".to_string()
                        ]
                    );
                    assert!(matches!(value_types.0, TomlValue::String));
                    assert!(matches!(value_types.1, TomlValue::Boolean));
                }
            },
        };
    }

    #[test]
    fn test_show_tablemap_normalize() {
        let normalize_toml = include_str!("../../normalize.toml");
        let parsed = toml::Table::from_str(normalize_toml).expect("must parse");

        let toml_val = TomlValue::from(parsed.clone());
        let normalized = toml_val.normalize().expect("must normalize");

        let reduced = normalized.reduce();
        println!("reduced: {:#?}", reduced);

        // println!("normalized: {:#?}", normalized);
    }
}
