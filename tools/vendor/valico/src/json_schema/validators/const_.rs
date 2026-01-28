use serde_json::Value;

use super::super::errors;
use super::super::helpers::is_matching;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Const {
    pub item: Value,
}

impl super::Validator for Const {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();

        if !is_matching(&self.item, val) {
            state.errors.push(Box::new(errors::Const {
                path: path.to_string(),
            }))
        } else {
            state.evaluated.insert(path.to_owned());
        }

        state
    }
}
