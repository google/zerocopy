use serde_json::Value;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Conditional;
impl super::Keyword for Conditional {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let maybe_if = def.get("if");
        let maybe_then = def.get("then");
        let maybe_else = def.get("else");

        if maybe_if.is_none() {
            Ok(None)
        } else {
            let if_ = helpers::alter_fragment_path(
                ctx.url.clone(),
                [ctx.escaped_fragment().as_ref(), "if"].join("/"),
            );
            let then_ = maybe_then.map(|_| {
                helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "then"].join("/"),
                )
            });
            let else_ = maybe_else.map(|_| {
                helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "else"].join("/"),
                )
            });
            Ok(Some(Box::new(validators::Conditional {
                if_,
                then_,
                else_,
            })))
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
fn validate_if_then() {
    let mut scope = scope::Scope::new();
    let schema = scope.compile_and_return(
        builder::schema(|s| {
            s.if_(|if_| {
                if_.minimum(5f64);
            });
            s.then_(|then_| {
                then_.minimum(5f64);
                then_.maximum(10f64);
            });
        })
        .into_json(),
        true,
    );

    assert!(schema.is_ok(), "{}", schema.err().unwrap().to_string());

    let s = schema.unwrap();
    assert_eq!(s.validate(&to_value(3).unwrap()).is_valid(), true);
    assert_eq!(s.validate(&to_value(15).unwrap()).is_valid(), false);
}

#[test]
fn validate_if_then_else() {
    let mut scope = scope::Scope::new();
    let schema = scope.compile_and_return(
        builder::schema(|s| {
            s.if_(|if_| {
                if_.minimum(5f64);
            });
            s.then_(|then_| {
                then_.minimum(5f64);
                then_.maximum(10f64);
            });
            s.else_(|else_| {
                else_.minimum(1f64);
                else_.maximum(4f64);
            });
        })
        .into_json(),
        true,
    );

    assert!(schema.is_ok(), "{}", schema.err().unwrap().to_string());

    let s = schema.unwrap();
    assert_eq!(s.validate(&to_value(3).unwrap()).is_valid(), true);
    assert_eq!(s.validate(&to_value(0).unwrap()).is_valid(), false);
}
