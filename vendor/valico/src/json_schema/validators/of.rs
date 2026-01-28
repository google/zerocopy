use serde_json::Value;
use std::borrow::Cow;
use std::collections::HashSet;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct AllOf {
    pub schemes: Vec<url::Url>,
}

impl super::Validator for AllOf {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();
        let mut val = Cow::Borrowed(val);

        // first get all relevant schemas
        let schemas = self
            .schemes
            .iter()
            .map(|url| (url, scope.resolve(url)))
            .filter_map(|(url, opt)| {
                if opt.is_none() {
                    state.missing.push(url.clone())
                }
                opt
            })
            .collect::<Vec<_>>();

        // first pass to populate all defaults (if enabled)
        for schema in schemas.iter() {
            let mut result = schema.validate_in(&val, path);
            if result.is_valid() && result.replacement.is_some() {
                *val.to_mut() = result.replacement.take().unwrap();
            }
            state.append(result);
        }
        if !state.is_valid() {
            return state;
        }

        // second pass if defaults are enabled to check that the result is stable
        if let Cow::Owned(v) = val {
            let mut second = Cow::Borrowed(&v);

            for schema in schemas.iter() {
                let mut result = schema.validate_in(&second, path);
                if result.is_valid() && result.replacement.is_some() {
                    *second.to_mut() = result.replacement.take().unwrap();
                }
                state.append(result);
            }
            if let Cow::Owned(_) = second {
                state.errors.push(Box::new(errors::DivergentDefaults {
                    path: path.to_string(),
                }));
            }
            if !state.is_valid() {
                return state;
            }
            val = Cow::Owned(v);
        }

        state.set_replacement(val);
        state
    }
}

#[allow(missing_copy_implementations)]
pub struct AnyOf {
    pub schemes: Vec<url::Url>,
}

impl super::Validator for AnyOf {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();
        let mut val = Cow::Borrowed(val);

        let mut invalid_states = vec![];
        // The "best" state is defined as "the one that validates the most items".
        let mut evaluated: HashSet<String> = HashSet::new();
        let mut valid = false;
        for url in self.schemes.iter() {
            let schema = scope.resolve(url);

            if let Some(schema) = schema {
                let mut result = schema.validate_in(&val, path);

                state.missing.extend(result.missing.clone());

                if result.is_valid() {
                    if let Some(result) = result.replacement.take() {
                        *val.to_mut() = result;
                    }
                    valid = true;
                    evaluated.extend(result.evaluated);
                    // Cannot short-circuit here as "unevaluatedItems" requires that we find the "best" state.
                } else {
                    invalid_states.push(result)
                }
            } else {
                state.missing.push(url.clone())
            }
        }

        if !valid {
            state.errors.push(Box::new(errors::AnyOf {
                path: path.to_string(),
                states: invalid_states,
            }))
        } else {
            state.evaluated.extend(evaluated);
        }

        state.set_replacement(val);
        state
    }
}

#[allow(missing_copy_implementations)]
pub struct OneOf {
    pub schemes: Vec<url::Url>,
}

impl super::Validator for OneOf {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();
        let mut val = Cow::Borrowed(val);

        let mut states = vec![];
        let mut valid = 0;
        let mut evaluated = HashSet::new();
        for url in self.schemes.iter() {
            let schema = scope.resolve(url);

            if let Some(schema) = schema {
                let mut result = schema.validate_in(&val, path);

                state.missing.extend(result.missing.clone());

                if result.is_valid() {
                    if let Some(result) = result.replacement.take() {
                        *val.to_mut() = result;
                    }
                    valid += 1;
                    evaluated = result.evaluated;
                } else {
                    states.push(result)
                }
            } else {
                state.missing.push(url.clone())
            }
        }

        if valid != 1 {
            state.errors.push(Box::new(errors::OneOf {
                path: path.to_string(),
                states,
            }))
        } else {
            state.evaluated = evaluated;
        }

        state.set_replacement(val);
        state
    }
}
