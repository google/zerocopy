use serde_json::Value;

use super::super::errors;
use super::super::scope;
use std::cmp::Ordering;
use std::f64;

#[allow(missing_copy_implementations)]
pub struct MultipleOf {
    pub number: f64,
}

impl super::Validator for MultipleOf {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let number = nonstrict_process!(val.as_f64(), path);

        let valid = if (number.fract() == 0f64) && (self.number.fract() == 0f64) {
            (number % self.number) == 0f64
        } else {
            let remainder: f64 = (number / self.number) % 1f64;
            let remainder_less_than_epsilon = matches!(
                remainder.partial_cmp(&f64::EPSILON),
                None | Some(Ordering::Less)
            );
            let remainder_less_than_one = remainder < (1f64 - f64::EPSILON);
            remainder_less_than_epsilon && remainder_less_than_one
        };

        if valid {
            super::ValidationState::new()
        } else {
            val_error!(errors::MultipleOf {
                path: path.to_string()
            })
        }
    }
}
