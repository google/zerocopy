use serde_json::Value;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Maximum {
    pub number: f64,
}

impl super::Validator for Maximum {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let number = nonstrict_process!(val.as_f64(), path);

        if number <= self.number {
            super::ValidationState::new()
        } else {
            val_error!(errors::Maximum {
                path: path.to_string()
            })
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct ExclusiveMaximum {
    pub number: f64,
}

impl super::Validator for ExclusiveMaximum {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let number = nonstrict_process!(val.as_f64(), path);

        if number < self.number {
            super::ValidationState::new()
        } else {
            val_error!(errors::Maximum {
                path: path.to_string()
            })
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Minimum {
    pub number: f64,
}

impl super::Validator for Minimum {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let number = nonstrict_process!(val.as_f64(), path);

        if number >= self.number {
            super::ValidationState::new()
        } else {
            val_error!(errors::Minimum {
                path: path.to_string()
            })
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct ExclusiveMinimum {
    pub number: f64,
}

impl super::Validator for ExclusiveMinimum {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let number = nonstrict_process!(val.as_f64(), path);

        if number > self.number {
            super::ValidationState::new()
        } else {
            val_error!(errors::Minimum {
                path: path.to_string()
            })
        }
    }
}
