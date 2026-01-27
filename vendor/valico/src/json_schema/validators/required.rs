use serde_json::Value;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Required {
    pub items: Vec<String>,
}

impl super::Validator for Required {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let object = nonstrict_process!(val.as_object(), path);
        let mut state = super::ValidationState::new();

        for key in self.items.iter() {
            if !object.contains_key(key) {
                state.errors.push(Box::new(errors::Required {
                    path: [path, key.as_ref()].join("/"),
                }))
            }
        }

        state
    }
}
