use serde_json::Value;

use super::super::schema;
use super::super::validators;

kw_minmax_integer!(MaxProperties, "maxProperties");
kw_minmax_integer!(MinProperties, "minProperties");

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;
#[cfg(test)]
use serde_json::to_value;

#[test]
fn validate_max_properties() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.max_properties(2u64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                    obj.set("p2", 0);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                    obj.set("p2", 0);
                    obj.set("p3", 0);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );
}

#[test]
fn malformed_max_properties() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxProperties", to_value(-1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxProperties", to_value("").unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("maxProperties", to_value(1.1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());
}

#[test]
fn validate_min_properties() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.min_properties(2u64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                    obj.set("p2", 0);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("p1", 0);
                    obj.set("p2", 0);
                    obj.set("p3", 0);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );
}

#[test]
fn malformed_min_properties() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minProperties", to_value(-1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minProperties", to_value("").unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("minProperties", to_value(1.1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());
}
