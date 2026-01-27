use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Enum;
impl super::Keyword for Enum {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let enum_ = keyword_key_exists!(def, "enum");

        if enum_.is_array() {
            let enum_ = enum_.as_array().unwrap();

            if enum_.is_empty() {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "This array MUST have at least one element.".to_string(),
                });
            }

            Ok(Some(Box::new(validators::Enum {
                items: enum_.clone(),
            })))
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of this keyword MUST be an array.".to_string(),
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
fn validate() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.enum_(|items| {
                    items.push("prop1".to_string());
                    items.push("prop2".to_string());
                })
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("prop1").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("prop2").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("prop3").unwrap()).is_valid(),
        false
    );
    assert_eq!(schema.validate(&to_value(1).unwrap()).is_valid(), false);
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.array("enum", |_| {});
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("enum", |_| {});
            })
            .unwrap(),
            true
        )
        .is_err());
}
