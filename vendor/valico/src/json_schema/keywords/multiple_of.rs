use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct MultipleOf;
impl super::Keyword for MultipleOf {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let multiple_of = keyword_key_exists!(def, "multipleOf");

        if multiple_of.is_number() {
            let multiple_of = multiple_of.as_f64().unwrap();
            if multiple_of > 0f64 {
                Ok(Some(Box::new(validators::MultipleOf {
                    number: multiple_of,
                })))
            } else {
                Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "The value of multipleOf MUST be strictly greater than 0".to_string(),
                })
            }
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of multipleOf MUST be a JSON number".to_string(),
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
                s.multiple_of(3.5f64);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value("").unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(7).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(6).unwrap()).is_valid(), false);
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("multipleOf", "".to_string());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("multipleOf", to_value(0).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("multipleOf", to_value(-1).unwrap());
            })
            .unwrap(),
            true
        )
        .is_err());
}
