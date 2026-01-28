use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct UniqueItems;
impl super::Keyword for UniqueItems {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let uniq = keyword_key_exists!(def, "uniqueItems");

        if uniq.is_boolean() {
            if uniq.as_bool().unwrap() {
                Ok(Some(Box::new(validators::UniqueItems)))
            } else {
                Ok(None)
            }
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of pattern MUST be boolean".to_string(),
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
fn validate_unique_items() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(builder::schema(|s| s.unique_items(true)).into_json(), true)
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value([1, 2, 3, 4]).unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value([1, 1, 3, 4]).unwrap()).is_valid(),
        false
    );
}
