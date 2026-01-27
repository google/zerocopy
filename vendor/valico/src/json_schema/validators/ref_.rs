use serde_json::Value;

use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Ref {
    pub url: url::Url,
}

impl super::Validator for Ref {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let schema = scope.resolve(&self.url);

        if let Some(schema) = schema {
            schema.validate_in(val, path)
        } else {
            let mut state = super::ValidationState::new();
            state.missing.push(self.url.clone());
            state
        }
    }
}
