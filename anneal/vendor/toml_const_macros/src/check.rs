//! Checks performed for parsed toml inputs

use std::collections::HashSet;

// use proc_macro::Span;
use proc_macro2::{self as pm2, Span};

use crate::MAP_FIELD;

/// Various ways checks can be mismatched
#[derive(Clone, Debug)]
pub enum CheckError {
    /// Key that is in one table but not the other.
    KeyMismatch {
        /// Sequence of keys in reverse order that leads to this mismatch.
        path: Vec<String>,
        a_diff: Option<String>,
        b_diff: Option<String>,
    },
    /// A mismatch in value types.
    ///
    /// Sequence of keys in reverse order that leads to this mismatch.
    ValueMismatch(Vec<String>),
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckError::KeyMismatch {
                path: table_path,
                a_diff,
                b_diff,
            } => {
                let table_path = table_path
                    .iter()
                    .rev()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join("::");

                let desc = match (a_diff, b_diff) {
                    (None, None) => unimplemented!("cannot have both None"),
                    (None, Some(key)) | (Some(key), None) => format!(
                        "{} contains at least one additional key: {}",
                        table_path, key
                    ),
                    (Some(key_a), Some(key_b)) => format!(
                        "{} has at least 2 keys that differ: {}, {}",
                        table_path, key_a, key_b
                    ),
                };

                write!(f, "{}", desc)
            }
            CheckError::ValueMismatch(items) => {
                let key_path = items.iter().rev().cloned().collect::<Vec<_>>().join("::");

                write!(f, "type mismatch for key: {}", key_path)
            }
        }

        // todo!()
    }
}

impl std::error::Error for CheckError {
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

/// Check that this table and all child items do not contain prohibited keys.
pub fn check_unauthorized_keys(input: &toml::Table) -> Result<(), pm2::TokenStream> {
    for (key, value) in input.iter() {
        if key.is_empty() {
            return Err(
                syn::Error::new(Span::call_site(), "empty quoted keys cannot be used")
                    .to_compile_error(),
            );
        }

        if key == MAP_FIELD {
            return Err(syn::Error::new(
                Span::call_site(),
                format!("\"{MAP_FIELD}\" is a reserved key"),
            )
            .to_compile_error());
        }

        match value {
            toml::Value::Table(sub_table) => check_unauthorized_keys(sub_table)?,
            toml::Value::Array(arr) => {
                for item in arr.iter() {
                    if let toml::Value::Table(sub_table) = item {
                        check_unauthorized_keys(sub_table)?
                    }
                }
            }
            _ => (),
        }
    }

    Ok(())
}

/// Main check entry point
#[allow(unused)]
fn check(table: &toml::Table) -> Result<(), CheckError> {
    // check that all arrays are consistent
    for (key, value) in table.iter() {
        match value {
            toml::Value::Array(arr) => match check_array_schema(arr) {
                Ok(_) => (),
                Err(e) => return Err(propagate_check_error(key, e)),
            },
            toml::Value::Table(sub_table) => match check(sub_table) {
                Ok(_) => (),
                Err(e) => return Err(propagate_check_error(key, e)),
            },
            _ => (),
        }
    }

    Ok(())
}

/// When receiving an error when performing some op on key+values, this function accumulates current key to the error.
#[allow(unused)]
fn propagate_check_error(key: &str, err: CheckError) -> CheckError {
    match err {
        CheckError::KeyMismatch {
            path: mut tp,
            a_diff,
            b_diff,
        } => {
            tp.push(key.to_string());

            CheckError::KeyMismatch {
                path: tp,
                a_diff,
                b_diff,
            }
        }
        CheckError::ValueMismatch(mut items) => {
            items.push(key.to_string());
            CheckError::ValueMismatch(items)
        }
    }
}

#[allow(unused)]
fn compare_value(
    key: Option<&str>,
    val_a: &toml::Value,
    val_b: &toml::Value,
) -> Result<(), CheckError> {
    match (val_a, val_b) {
        (toml::Value::Boolean(_), toml::Value::Boolean(_))
        | (toml::Value::Datetime(_), toml::Value::Datetime(_))
        | (toml::Value::Float(_), toml::Value::Float(_))
        | (toml::Value::Integer(_), toml::Value::Integer(_))
        | (toml::Value::String(_), toml::Value::String(_)) => Ok(()),

        (toml::Value::Array(arr_a), toml::Value::Array(arr_b)) => {
            compare_array_schema(key, arr_a, arr_b)
        }
        (toml::Value::Table(a_table), toml::Value::Table(b_table)) => {
            match compare_table_schema(a_table, b_table) {
                Ok(_) => Ok(()),
                Err(e) => match key {
                    Some(k) => Err(propagate_check_error(k, e)),
                    None => Err(e),
                },
            }
        }

        _ => Err(CheckError::ValueMismatch(if let Some(k) = key {
            vec![k.to_string()]
        } else {
            vec![]
        })),
    }
}

#[allow(unused)]
fn check_array_schema(arr: &toml::value::Array) -> Result<(), CheckError> {
    match arr.len() {
        0..2 => (),
        _ => {
            let mut arr_iter = arr.iter();
            let first = arr_iter.next().unwrap();

            for elem in arr_iter {
                // arrays do not propagate their key downwards
                compare_value(None, first, elem)?;
            }
        }
    }

    Ok(())
}

#[allow(unused)]
fn compare_array_schema(
    key: Option<&str>,
    arr_a: &toml::value::Array,
    arr_b: &toml::value::Array,
) -> Result<(), CheckError> {
    check_array_schema(arr_a)?;
    check_array_schema(arr_b)?;

    match (arr_a.len(), arr_b.len()) {
        (0, 0) | (0, _) | (_, 0) => Ok(()),
        _ => compare_value(key, &arr_a[0], &arr_b[0]),
    }
}

/// Check that both tables match exactly in keys and types.
#[allow(unused)]
pub fn compare_table_schema(
    table_a: &toml::Table,
    table_b: &toml::Table,
) -> Result<(), CheckError> {
    // check that both tables have the same keys
    let a_keys = table_a.keys().collect::<HashSet<_>>();
    let b_keys = table_b.keys().collect::<HashSet<_>>();

    match (
        a_keys.difference(&b_keys).next(),
        b_keys.difference(&a_keys).next(),
    ) {
        (None, None) => (),
        (None, Some(b)) => {
            return Err(CheckError::KeyMismatch {
                path: vec![],
                a_diff: None,
                b_diff: Some(b.to_string()),
            });
        }
        (Some(a), None) => {
            return Err(CheckError::KeyMismatch {
                path: vec![],
                a_diff: Some(a.to_string()),
                b_diff: None,
            });
        }
        (Some(a), Some(b)) => {
            return Err(CheckError::KeyMismatch {
                path: vec![],
                a_diff: Some(a.to_string()),
                b_diff: Some(b.to_string()),
            });
        }
    }

    for (key, a_val) in table_a.iter() {
        let b_val = table_b.get(key).expect("already checked in previous step");

        match (a_val, b_val) {
            (toml::Value::Boolean(_), toml::Value::Boolean(_))
            | (toml::Value::Datetime(_), toml::Value::Datetime(_))
            | (toml::Value::Float(_), toml::Value::Float(_))
            | (toml::Value::Integer(_), toml::Value::Integer(_))
            | (toml::Value::String(_), toml::Value::String(_)) => (),

            // more checks
            (toml::Value::Array(a_arr), toml::Value::Array(b_arr)) => {
                compare_array_schema(Some(key), a_arr, b_arr)?;
            }
            (toml::Value::Table(a_table), toml::Value::Table(b_table)) => {
                match compare_table_schema(a_table, b_table) {
                    Ok(_) => (),
                    Err(e) => return Err(propagate_check_error(key, e)),
                }
            }

            _ => return Err(CheckError::ValueMismatch(vec![key.to_string()])),
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {

    use super::*;
    use toml::de::from_str;

    #[test]
    fn test_check_unauthorized_keys() {
        let toml_str = r#"
            [a]
            key1 = "value1"
            key2 = 42
            key3 = true

            [[b]]
            key1 = "value1"

            [[b]]
            key1 = "value2"

            [c]
            subtable.item = "value3"
            subtable.otheritem = "value4"
        "#;

        let table: toml::Table = from_str(toml_str).unwrap();
        assert!(check_unauthorized_keys(&table).is_ok());

        // Check with an empty key
        let toml_str_with_empty_key = r#"
            [a]
            "" = "value1"
            key2 = 42
            key3 = true

            [[b]]
            key1 = "value1"

            [[b]]
            key1 = "value2"

            [c]
            subtable.item = "value3"
            subtable.otheritem = "value4"
        "#;

        let table_with_empty_key: toml::Table = from_str(toml_str_with_empty_key).unwrap();
        let res = check_unauthorized_keys(&table_with_empty_key);
        assert!(res.is_err());
    }

    #[test]
    fn test_check_matching_schema() {
        let toml_a = r#"
            [a]
            key1 = "value1"
            key2 = 42
            key3 = true

            [[b]]
            key1 = "value1"

            [[b]]
            key1 = "value2"

            [c]
            subtable.item = "value3"
            subtable.otheritem = "value4"
        "#;

        let toml_b = r#"
            [a]
            key1 = "value2"
            key2 = 24
            key3 = false

            [[b]]
            key1 = "value3"

            [c]
            subtable.item = "value3"
            subtable.otheritem = "value4"
        "#;

        let table_a: toml::Table = from_str(toml_a).unwrap();
        let table_b: toml::Table = from_str(toml_b).unwrap();

        assert!(compare_table_schema(&table_a, &table_b).is_ok());
    }

    /// Return an error pointing to the key that does not have the correct data type
    #[test]
    fn test_key_type_mismatch() {
        let toml_a = r#"
            [a]
            a_inner.key1 = "value1"
            key2 = 42
        "#;

        let toml_b = r#"
            [a]
            a_inner.key1 = true
            key2 = 24
        "#;

        let table_a: toml::Table = from_str(toml_a).unwrap();
        let table_b: toml::Table = from_str(toml_b).unwrap();

        let res = compare_table_schema(&table_a, &table_b);
        assert!(res.is_err());

        if let CheckError::ValueMismatch(items) = res.clone().unwrap_err() {
            assert_eq!(items, vec!["key1", "a_inner", "a"]);
        } else {
            panic!("Expected ValueMismatch error, got {:?}", res);
        }
    }

    /// Return an error showing one or two keys that
    #[test]
    fn test_key_mismatch() {
        let toml_a = r#"
            [a]
            key1 = "value1"
            key2 = 42
        "#;

        let toml_b = r#"
            [a]
            key1 = "value2"
            key3 = 24
        "#;

        let table_a: toml::Table = from_str(toml_a).unwrap();
        let table_b: toml::Table = from_str(toml_b).unwrap();

        let res = compare_table_schema(&table_a, &table_b);
        println!("{:?}", res);
        assert!(res.is_err());

        if let CheckError::KeyMismatch { a_diff, b_diff, .. } = res.clone().unwrap_err() {
            assert_eq!(a_diff, Some("key2".to_string()));
            assert_eq!(b_diff, Some("key3".to_string()));
        } else {
            panic!("Expected KeyMismatch error, got {:?}", res);
        }
    }
}
