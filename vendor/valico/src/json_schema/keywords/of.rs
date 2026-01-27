use serde_json::Value;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

macro_rules! of_keyword {
    ($name:ident, $kw:expr) => {
        #[allow(missing_copy_implementations)]
        pub struct $name;
        impl super::Keyword for $name {
            fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
                let of = keyword_key_exists!(def, $kw);

                if of.is_array() {
                    let of = of.as_array().unwrap();

                    if of.len() == 0 {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx.fragment.join("/"),
                            detail: "This array MUST have at least one element.".to_string(),
                        });
                    }

                    let mut schemes = vec![];
                    for (idx, scheme) in of.iter().enumerate() {
                        if scheme.is_object() || scheme.is_boolean() {
                            schemes.push(helpers::alter_fragment_path(
                                ctx.url.clone(),
                                [
                                    ctx.escaped_fragment().as_ref(),
                                    $kw,
                                    idx.to_string().as_ref(),
                                ]
                                .join("/"),
                            ))
                        } else {
                            return Err(schema::SchemaError::Malformed {
                                path: ctx.fragment.join("/"),
                                detail: "Elements of the array MUST be objects or booleans."
                                    .to_string(),
                            });
                        }
                    }

                    Ok(Some(Box::new(validators::$name { schemes })))
                } else {
                    Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "The value of this keyword MUST be an array.".to_string(),
                    })
                }
            }
        }
    };
}

of_keyword!(AllOf, "allOf");
of_keyword!(AnyOf, "anyOf");
of_keyword!(OneOf, "oneOf");

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;
#[cfg(test)]
use serde_json::to_value;

#[cfg(test)]
fn mk_schema() -> Value {
    json!({
        "properties": {
            "a": {
                "oneOf": [
                    { "type": "array", "items": [{"type":"boolean"},{"default":42}] },
                    { "type": "object", "properties": {"x": {"default": "buh"}} }
                ]
            },
            "b": {
                "anyOf": [
                    { "type": "array", "items": [{"type":"boolean"},{"default":42}] },
                    { "type": "object", "properties": {"x": {"default": "buh"}} }
                ]
            },
            "c": {
                "allOf": [
                    { "properties": {"x": {"default": false}} },
                    { "properties": {"y": {"default": true}} }
                ]
            }
        }
    })
}

#[test]
fn no_default_for_schema() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    assert_eq!(schema.get_default(), None);
}

#[test]
fn default_when_needed() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"a":[true],"b":[true],"c":{}}));
    assert!(result.is_strictly_valid());
    assert_eq!(
        result.replacement,
        Some(json!({"a":[true,42],"b":[true,42],"c":{"x":false,"y":true}}))
    );
}

#[test]
fn default_when_needed2() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"a":{},"b":{}}));
    assert!(result.is_strictly_valid());
    assert_eq!(
        result.replacement,
        Some(json!({"a":{"x":"buh"},"b":{"x":"buh"}}))
    );
}

#[test]
fn no_default_otherwise() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"a":{"x":"x"},"b":[true,0],"c":{"x":1,"y":2}}));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, None);
}

#[test]
fn conflicting_defaults() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope
        .compile_and_return(
            json!({
                "allOf": [
                    {
                        "properties": {
                            "a": { "type": "number" }
                        },
                    },
                    {
                        "properties": {
                            "a": { "default": "hello" }
                        }
                    }
                ]
            }),
            true,
        )
        .unwrap();
    let result = schema.validate(&json!({}));
    assert!(!result.is_valid());
    assert_eq!(&*format!("{result:?}"),
      "ValidationState { errors: [WrongType { path: \"/a\", detail: \"The value must be number\" }], missing: [], replacement: None, evaluated: {\"/a\"} }");
}

#[test]
fn divergent_defaults() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope
        .compile_and_return(
            json!({
                "allOf": [
                    {
                        "properties": {
                            "a": {
                                "anyOf": [{
                                    "properties": {
                                        "b": { "default": 42 }
                                    }
                                }]
                            }
                        },
                    },
                    {
                        "properties": {
                            "a": { "default": {} }
                        }
                    }
                ]
            }),
            true,
        )
        .unwrap();
    let mut result = schema.validate(&json!({}));
    assert!(!result.is_valid());
    result.evaluated.clear();
    assert_eq!(&*format!("{result:?}"),
      "ValidationState { errors: [DivergentDefaults { path: \"\" }], missing: [], replacement: None, evaluated: {} }");
}

#[test]
fn validate_all_of() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.all_of(|all_of| {
                    all_of.push(|schema| {
                        schema.minimum(5f64);
                    });
                    all_of.push(|schema| {
                        schema.maximum(10f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(7).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(4).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), false);
}

#[test]
fn validate_any_of() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.any_of(|all_of| {
                    all_of.push(|schema| {
                        schema.maximum(5f64);
                    });
                    all_of.push(|schema| {
                        schema.maximum(10f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(5).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), false);
}

#[test]
fn validate_one_of() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.one_of(|all_of| {
                    all_of.push(|schema| {
                        schema.maximum(5f64);
                    });
                    all_of.push(|schema| {
                        schema.maximum(10f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(5).unwrap()).is_valid(), false);
    assert_eq!(schema.validate(&to_value(6).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11).unwrap()).is_valid(), false);
}
