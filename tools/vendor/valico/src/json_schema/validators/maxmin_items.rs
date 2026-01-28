use serde_json::Value;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct MaxItems {
    pub length: u64,
}

impl super::Validator for MaxItems {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let array = nonstrict_process!(val.as_array(), path);

        if (array.len() as u64) <= self.length {
            super::ValidationState::new()
        } else {
            val_error!(errors::MaxItems {
                path: path.to_string()
            })
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct MinItems {
    pub length: u64,
}

impl super::Validator for MinItems {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let array = nonstrict_process!(val.as_array(), path);

        if (array.len() as u64) >= self.length {
            super::ValidationState::new()
        } else {
            val_error!(errors::MinItems {
                path: path.to_string()
            })
        }
    }
}
