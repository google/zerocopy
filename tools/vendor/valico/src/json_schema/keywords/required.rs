use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Required;
impl super::Keyword for Required {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let required = keyword_key_exists!(def, "required");

        if required.is_array() {
            let required = required.as_array().unwrap();

            let mut items = vec![];
            for item in required.iter() {
                if item.is_string() {
                    items.push(item.as_str().unwrap().to_string())
                } else {
                    return Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "The values of `required` MUST be strings".to_string(),
                    });
                }
            }

            Ok(Some(Box::new(validators::Required { items })))
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

#[test]
fn validate() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.required(vec!["prop1".to_string(), "prop2".to_string()]);
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
                    obj.set("prop1", 0);
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
                    obj.set("prop2", 0);
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
                    obj.set("prop1", 0);
                    obj.set("prop2", 0);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.array("required", |required| required.push(1));
            })
            .unwrap(),
            true
        )
        .is_err());
}
