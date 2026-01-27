use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Pattern;
impl super::Keyword for Pattern {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let pattern = keyword_key_exists!(def, "pattern");

        if pattern.is_string() {
            let pattern_val = pattern.as_str().unwrap();
            match fancy_regex::Regex::new(pattern_val) {
                Ok(re) => Ok(Some(Box::new(validators::Pattern { regex: re }))),
                Err(err) => Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: format!("The value of pattern MUST be a valid RegExp, but {err:?}"),
                }),
            }
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of pattern MUST be a string".to_string(),
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
                s.pattern(r"abb.*");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(schema.validate(&to_value("abb").unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value("abbd").unwrap()).is_valid(), true);
    assert_eq!(schema.validate(&to_value("abd").unwrap()).is_valid(), false);
}

#[test]
fn mailformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("pattern", "([]".to_string());
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("pattern", 2);
            })
            .unwrap(),
            true
        )
        .is_err());
}
