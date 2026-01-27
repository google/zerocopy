use serde_json::Value;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Not {
    pub url: url::Url,
}

impl super::Validator for Not {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let schema = scope.resolve(&self.url);
        let mut state = super::ValidationState::new();

        if let Some(schema) = schema {
            if schema.validate_in(val, path).is_valid() {
                state.errors.push(Box::new(errors::Not {
                    path: path.to_string(),
                }))
            }
        } else {
            state.missing.push(self.url.clone());
        }

        state
    }
}
