use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Type;
impl super::Keyword for Type {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let type_ = keyword_key_exists!(def, "type");

        if type_.is_string() {
            let ty = type_.as_str().unwrap().parse().ok();

            if let Some(ty) = ty {
                Ok(Some(Box::new(validators::Type {
                    item: validators::type_::TypeKind::Single(ty),
                })))
            } else {
                Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: format!(
                        "String values MUST be one of the seven primitive types defined by the core specification. Unknown type: {}",
                        type_.as_str().unwrap()
                    )
                })
            }
        } else if type_.is_array() {
            let types = type_.as_array().unwrap();

            if types.is_empty() {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "This array MUST have at least one element.".to_string(),
                });
            }

            let mut converted_types = vec![];
            for ty in types.iter() {
                if ty.is_string() {
                    let converted_ty = ty.as_str().unwrap().parse().ok();
                    if let Some(converted_ty) = converted_ty {
                        converted_types.push(converted_ty);
                    } else {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx.fragment.join("/"),
                            detail: format!("Unknown type: {}", ty.as_str().unwrap()),
                        });
                    }
                } else {
                    return Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "String values MUST be one of the seven primitive types defined by the core specification.".to_string()
                    });
                }
            }

            Ok(Some(Box::new(validators::Type {
                item: validators::type_::TypeKind::Set(converted_types),
            })))
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of this keyword MUST be either a string or an array."
                    .to_string(),
            })
        }
    }
}

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;
#[cfg(test)]
use serde_json::to_value;

#[test]
fn validate_array() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.array();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&jsonway::array(|_arr| {}).unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_boolean() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.boolean();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(true).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(false).unwrap()).is_valid(), true);
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_integer() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.integer();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(-10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11.5).unwrap()).is_valid(), false);
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_number() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.number();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(-10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(11.5).unwrap()).is_valid(), true);
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_null() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.null();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&json!(null)).is_valid(), true);
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_object() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.object();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&jsonway::object(|_arr| {}).unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_string() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.string();
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&jsonway::object(|_arr| {}).unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_set() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.types(&[
                    super::super::PrimitiveType::Integer,
                    super::super::PrimitiveType::String,
                ]);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value(10).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(-11).unwrap()).is_valid(), true);
    assert_eq!(
        schema.validate(&to_value("string").unwrap()).is_valid(),
        true
    );
    assert_eq!(schema.validate(&to_value(11.5).unwrap()).is_valid(), false);
    assert_eq!(
        schema
            .validate(&jsonway::object(|_arr| {}).unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("type", 10);
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("type", |_type| {});
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("type", "unsigned".to_string());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.array("type", |types| {
                    types.push(10);
                });
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.array("type", |types| {
                    types.push("unsigned".to_string());
                });
            })
            .unwrap(),
            true
        )
        .is_err());
}
