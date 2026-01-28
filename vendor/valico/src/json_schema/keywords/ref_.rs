use serde_json::Value;
use url::Url;

use crate::json_schema::SchemaVersion;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Ref;
impl super::Keyword for Ref {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let ref_ = keyword_key_exists!(def, "$ref");

        if ref_.is_string() {
            let url = Url::options()
                .base_url(Some(ctx.url))
                .parse(ref_.as_str().unwrap());
            match url {
                Ok(url) => Ok(Some(Box::new(validators::Ref { url }))),
                Err(_) => Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "The value of $ref MUST be an URI-encoded JSON Pointer".to_string(),
                }),
            }
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of multipleOf MUST be a string".to_string(),
            })
        }
    }

    fn is_exclusive(&self, version: SchemaVersion) -> bool {
        version < SchemaVersion::Draft2019_09
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
        "a": { "default": 42 },
        "b": { "properties": { "x": { "default": [1,2,3] } } },
        "properties": {
            "y": { "$ref": "#/a" },
            "z": { "$ref": "#/b" }
        },
        "required": [ "y", "z" ]
    })
}

#[test]
fn default_for_schema() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), false).unwrap();
    assert_eq!(
        schema.get_default(),
        Some(json!({"y": 42, "z": {"x": [1,2,3]}}))
    );
}

#[test]
fn default_when_needed() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), false).unwrap();
    let result = schema.validate(&json!({"x": true}));
    assert!(result.is_strictly_valid());
    assert_eq!(
        result.replacement,
        Some(json!({"x": true, "y": 42, "z": {"x": [1,2,3]}}))
    );
}

#[test]
fn no_default_otherwise() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), false).unwrap();
    let result = schema.validate(&json!({"y": null, "z": {"x":false}}));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, None);
}

#[test]
fn validate() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.array();
                s.max_items(2u64);
                s.items_schema(|items| {
                    items.ref_("#");
                })
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    let array: Vec<String> = vec![];
    let array2: Vec<Vec<String>> = vec![vec![], vec![]];
    let array3: Vec<Vec<String>> = vec![vec![], vec![], vec![]];

    assert_eq!(schema.validate(&to_value(array).unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value(array2).unwrap()).is_valid(), true);

    assert_eq!(
        schema.validate(&to_value(array3).unwrap()).is_valid(),
        false
    );
    assert_eq!(
        schema.validate(&to_value(vec![1, 2]).unwrap()).is_valid(),
        false
    );
}
