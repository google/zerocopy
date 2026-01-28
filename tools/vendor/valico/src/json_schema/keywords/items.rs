use serde_json::Value;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Items;
impl super::Keyword for Items {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let maybe_items = def.get("items");
        let maybe_additional = def.get("additionalItems");

        if !(maybe_items.is_some() || maybe_additional.is_some()) {
            return Ok(None);
        }

        let items = if let Some(items_val) = maybe_items {
            Some(if items_val.is_object() || items_val.is_boolean() {
                validators::items::ItemsKind::Schema(helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "items"].join("/"),
                ))
            } else if items_val.is_array() {
                let mut schemas = vec![];
                for (idx, item) in items_val.as_array().unwrap().iter().enumerate() {
                    if item.is_object() || item.is_boolean() {
                        schemas.push(helpers::alter_fragment_path(
                            ctx.url.clone(),
                            [
                                ctx.escaped_fragment().as_ref(),
                                "items",
                                idx.to_string().as_ref(),
                            ]
                            .join("/"),
                        ))
                    } else {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx.fragment.join("/"),
                            detail: "Items of this array MUST be objects or booleans".to_string(),
                        });
                    }
                }

                validators::items::ItemsKind::Array(schemas)
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "`items` must be an object, an array or a boolean".to_string(),
                });
            })
        } else {
            None
        };

        let additional_items = if let Some(additional_val) = maybe_additional {
            Some(if additional_val.is_boolean() {
                validators::items::AdditionalKind::Boolean(additional_val.as_bool().unwrap())
            } else if additional_val.is_object() {
                validators::items::AdditionalKind::Schema(helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "additionalItems"].join("/"),
                ))
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "`additionalItems` must be a boolean or an object".to_string(),
                });
            })
        } else {
            None
        };

        Ok(Some(Box::new(validators::Items {
            items,
            additional: additional_items,
        })))
    }

    fn place_first(&self) -> bool {
        true
    }
}

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
                "items": {
                    "properties": {
                        "x": { "type": "number", "default": 42 }
                    }
                }
            },
            "b": {
                "items": [
                    {
                        "properties": {
                            "x": { "type": "boolean", "default": true }
                        }
                    },
                    { "type": "number", "default": 42 }
                ]
            }
        }
    })
}

#[test]
fn default_for_schema() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    // the "a" branch does not get a default since items is not an array
    assert_eq!(schema.get_default(), Some(json!({"b": [{"x": true}, 42]})));
}

#[test]
fn default_when_needed() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"a": [{}, {"x": 43}], "b": [{"x": false}]}));
    assert!(result.is_strictly_valid());
    assert_eq!(
        result.replacement,
        Some(json!({"a": [{"x": 42}, {"x": 43}], "b": [{"x": false}, 42]}))
    );
}

#[test]
fn no_default_otherwise() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"a": [], "b": [{"x": false}, 45]}));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, None);
}

#[test]
fn validate_items_with_schema() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.items_schema(|items| {
                    items.minimum(5f64);
                    items.maximum(10f64);
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value([5, 6, 7, 8, 9, 10]).unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value([4, 5, 6, 7, 8, 9, 10]).unwrap())
            .is_valid(),
        false
    );
    assert_eq!(
        schema
            .validate(&to_value([5, 6, 7, 8, 9, 10, 11]).unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_items_with_array_of_schemes() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.items_array(|items| {
                    items.push(|item| {
                        item.minimum(1f64);
                        item.maximum(3f64);
                    });
                    items.push(|item| {
                        item.minimum(3f64);
                        item.maximum(6f64);
                    });
                })
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value([1]).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value([1, 3]).unwrap()).is_valid(), true);
    assert_eq!(
        schema.validate(&to_value([1, 3, 100]).unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value([4, 3]).unwrap()).is_valid(),
        false
    );
    assert_eq!(
        schema.validate(&to_value([1, 7]).unwrap()).is_valid(),
        false
    );
    assert_eq!(
        schema.validate(&to_value([4, 7]).unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_items_with_array_of_schemes_with_additional_bool() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.items_array(|items| {
                    items.push(|item| {
                        item.minimum(1f64);
                        item.maximum(3f64);
                    });
                    items.push(|item| {
                        item.minimum(3f64);
                        item.maximum(6f64);
                    });
                });
                s.additional_items(false);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value([1, 3, 100]).unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_items_with_array_of_schemes_with_additional_schema() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.items_array(|items| {
                    items.push(|item| {
                        item.minimum(1f64);
                        item.maximum(3f64);
                    });
                    items.push(|item| {
                        item.minimum(3f64);
                        item.maximum(6f64);
                    });
                });
                s.additional_items_schema(|add| add.maximum(100f64));
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value([1, 3, 100]).unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value([1, 3, 101]).unwrap()).is_valid(),
        false
    );
}
