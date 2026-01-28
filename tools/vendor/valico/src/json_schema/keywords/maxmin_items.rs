use serde_json::Value;

use super::super::schema;
use super::super::validators;

kw_minmax_integer!(MaxItems, "maxItems");
kw_minmax_integer!(MinItems, "minItems");

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;
#[cfg(test)]
use serde_json::to_value;

#[test]
fn validate_max_items() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.max_items(5u64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value([1, 2, 3, 4]).unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value([1, 2, 3, 4, 5]).unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value([1, 2, 3, 4, 5, 6]).unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn malformed_max_items() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxItems", to_value(-1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxItems", to_value("").unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxItems", to_value(1.1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());
}

#[test]
fn validate_min_items() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.min_items(5u64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value([1, 2, 3, 4]).unwrap()).is_valid(),
        false
    );
    assert_eq!(
        schema
            .validate(&to_value([1, 2, 3, 4, 5]).unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value([1, 2, 3, 4, 5, 6]).unwrap())
            .is_valid(),
        true
    );
}

#[test]
fn malformed_min_items() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minItems", to_value(-1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minItems", to_value("").unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minItems", to_value(1.1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());
}
