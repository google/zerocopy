use serde_json::Value;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct PropertyNames;
impl super::Keyword for PropertyNames {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let property_names = keyword_key_exists!(def, "propertyNames");

        if property_names.is_object() || property_names.is_boolean() {
            Ok(Some(Box::new(validators::PropertyNames {
                url: helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "propertyNames"].join("/"),
                ),
            })))
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of propertyNames MUST be an object or a boolean".to_string(),
            })
        }
    }
}
