use serde_json::Value;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct UniqueItems;
impl super::Validator for UniqueItems {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let array = nonstrict_process!(val.as_array(), path);

        // TODO we need some quicker algorithm for this

        let mut unique = true;
        'main: for (idx, item_i) in array.iter().enumerate() {
            for item_j in array[..idx].iter() {
                if item_i == item_j {
                    unique = false;
                    break 'main;
                }
            }

            for item_j in array[(idx + 1)..].iter() {
                if item_i == item_j {
                    unique = false;
                    break 'main;
                }
            }
        }

        if unique {
            super::ValidationState::new()
        } else {
            val_error!(errors::UniqueItems {
                path: path.to_string()
            })
        }
    }
}
