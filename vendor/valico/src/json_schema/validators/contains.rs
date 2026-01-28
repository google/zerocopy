use serde_json::Value;
use std::borrow::Cow;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Contains {
    pub url: url::Url,
    pub max_contains: Option<u64>,
    pub min_contains: Option<u64>,
}

impl super::Validator for Contains {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut array = Cow::Borrowed(nonstrict_process!(val.as_array(), path));

        let schema = scope.resolve(&self.url);
        let mut state = super::ValidationState::new();

        if let Some(schema) = schema {
            let mut matched_count = 0;
            for idx in 0..array.len() {
                let item_path = [path, idx.to_string().as_ref()].join("/");
                let item = &array[idx];
                let mut result = schema.validate_in(item, item_path.as_ref());
                if result.is_valid() {
                    matched_count += 1;
                    if let Some(result) = result.replacement.take() {
                        array.to_mut()[idx] = result;
                    }
                    if self.max_contains.is_none() && self.min_contains.is_none() {
                        break;
                    }
                }
            }

            if matched_count == 0 && self.min_contains != Some(0) {
                state.errors.push(Box::new(errors::Contains {
                    path: path.to_string(),
                }))
            }

            if self
                .max_contains
                .map(|max| matched_count > max)
                .unwrap_or(false)
            {
                state.errors.push(Box::new(errors::ContainsMinMax {
                    path: path.to_string(),
                }));
            }

            if self
                .min_contains
                .map(|min| matched_count < min)
                .unwrap_or(false)
            {
                state.errors.push(Box::new(errors::ContainsMinMax {
                    path: path.to_string(),
                }));
            }
        } else {
            state.missing.push(self.url.clone());
        }

        state.set_replacement(array);
        state
    }
}
