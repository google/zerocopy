use serde_json::Value;

use super::super::schema;
use super::super::validators;

macro_rules! kw_minmax {
    ($name:ident, $keyword:expr) => {
        #[allow(missing_copy_implementations)]
        pub struct $name;
        impl super::Keyword for $name {
            fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
                let value = keyword_key_exists!(def, $keyword);

                if value.is_number() {
                    let value = value.as_f64().unwrap();
                    Ok(Some(Box::new(validators::$name {
                        number: value
                    })))
                } else {
                    Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "the `minimum/maximum/exclusiveMinimum/exclusiveMaximum` value must be a number".to_string()
                    })
                }
            }
        }
    }
}

kw_minmax!(Maximum, "maximum");
kw_minmax!(ExclusiveMaximum, "exclusiveMaximum");
kw_minmax!(Minimum, "minimum");
kw_minmax!(ExclusiveMinimum, "exclusiveMinimum");

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;

#[cfg(test)]
use serde_json::to_value;

#[test]
fn validate_maximum() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.maximum(10f64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(9).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), false);
}

#[test]
fn validate_exclusive_maximum() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.exclusive_maximum(10f64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(9).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), false);
}

#[test]
fn mailformed_maximum() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maximum", true);
            })
            .unwrap(),
            true
        )
        .is_err());
}

#[test]
fn mailformed_exclusive_maximum() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("exclusiveMaximum", true);
            })
            .unwrap(),
            true
        )
        .is_err());
}

#[test]
fn validate_minumum() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.minimum(10f64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(9).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), true);
}

#[test]
fn validate_exclusive_minimum() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.exclusive_minimum(10f64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(9).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), true);
}

#[test]
fn mailformed_minumum() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minimum", true);
            })
            .unwrap(),
            true
        )
        .is_err());
}

#[test]
fn mailformed_exclusive_minumum() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("exclusiveMinimum", true);
            })
            .unwrap(),
            true
        )
        .is_err());
}
