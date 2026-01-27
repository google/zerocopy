use serde_json::Value;
use url;

use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Conditional {
    pub if_: url::Url,
    pub then_: Option<url::Url>,
    pub else_: Option<url::Url>,
}

impl super::Validator for Conditional {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();

        let schema_if_ = scope.resolve(&self.if_);
        if let Some(schema_if) = schema_if_ {
            // TODO should the validation be strict?
            let if_state = schema_if.validate_in(val, path);
            if if_state.is_valid() {
                state.evaluated.extend(if_state.evaluated);
                if self.then_.is_some() {
                    let schema_then_ = scope.resolve(self.then_.as_ref().unwrap());

                    if let Some(schema_then) = schema_then_ {
                        state.append(schema_then.validate_in(val, path));
                    } else {
                        state.missing.push(self.then_.as_ref().unwrap().clone());
                    }
                }
            } else if self.else_.is_some() {
                let schema_else_ = scope.resolve(self.else_.as_ref().unwrap());

                if let Some(schema_else) = schema_else_ {
                    state.append(schema_else.validate_in(val, path));
                } else {
                    state.missing.push(self.else_.as_ref().unwrap().clone());
                }
            }
        } else {
            state.missing.push(self.if_.clone());
        }
        state
    }
}
