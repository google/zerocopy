use serde_json::Value;

use crate::json_schema::SchemaVersion;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Contains;
impl super::Keyword for Contains {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext) -> super::KeywordResult {
        let contains = keyword_key_exists!(def, "contains");
        let (max_contains, min_contains) = if ctx.version >= SchemaVersion::Draft2019_09 {
            let max_contains = def
                .get("maxContains")
                .map(|v| {
                    v.as_u64().ok_or_else(|| schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "The value of maxContains MUST be a non-negative integer"
                            .to_string(),
                    })
                })
                .transpose()?;
            let min_contains = def
                .get("minContains")
                .map(|v| {
                    v.as_u64().ok_or_else(|| schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "The value of minContains MUST be a non-negative integer"
                            .to_string(),
                    })
                })
                .transpose()?;
            (max_contains, min_contains)
        } else {
            (None, None)
        };

        if contains.is_object() || contains.is_boolean() {
            Ok(Some(Box::new(validators::Contains {
                url: helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "contains"].join("/"),
                ),
                max_contains,
                min_contains,
            })))
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of contains MUST be an object or a boolean".to_string(),
            })
        }
    }
}

#[cfg(test)]
pub mod tests {
    use crate::json_schema::scope;
    use serde_json::Value;

    fn schema() -> Value {
        json!({
            "contains": {
                "properties": {
                    "x": {
                        "type": "string",
                        "default": "buh"
                    },
                }
            }
        })
    }

    #[test]
    fn no_default_for_schema() {
        let mut scope = scope::Scope::new().supply_defaults();
        let schema = scope.compile_and_return(schema(), true).unwrap();
        assert_eq!(schema.get_default(), None);
    }

    #[test]
    fn default_for_first() {
        let mut scope = scope::Scope::new().supply_defaults();
        let schema = scope.compile_and_return(schema(), true).unwrap();
        let result = schema.validate(&json!([{}, {}]));
        assert!(result.is_strictly_valid());
        assert_eq!(result.replacement, Some(json!([{"x": "buh"}, {}])));
    }

    #[test]
    fn no_default_when_not_needed() {
        let mut scope = scope::Scope::new().supply_defaults();
        let schema = scope.compile_and_return(schema(), true).unwrap();
        let result = schema.validate(&json!([{"x": "y"}, {}]));
        assert!(result.is_strictly_valid());
        assert_eq!(result.replacement, None);
    }
}
