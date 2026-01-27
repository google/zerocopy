use serde_json::Value;
use std::borrow::Cow;

use super::super::errors;
use super::super::scope;

#[derive(Debug)]
pub enum DepKind {
    Schema(url::Url),
    Property(Vec<String>),
}

#[allow(missing_copy_implementations)]
pub struct Dependencies {
    pub items: Vec<(String, DepKind)>,
}

impl super::Validator for Dependencies {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();
        if !val.is_object() {
            return state;
        }
        let mut object = Cow::Borrowed(val);

        for (key, dep) in self.items.iter() {
            if object.get(key).is_some() {
                match dep {
                    DepKind::Schema(ref url) => {
                        let schema = scope.resolve(url);
                        if let Some(schema) = schema {
                            let mut result = schema.validate_in(&object, path);
                            if result.is_valid() && result.replacement.is_some() {
                                *object.to_mut() = result.replacement.take().unwrap();
                            }
                            state.append(result);
                        } else {
                            state.missing.push(url.clone())
                        }
                    }
                    DepKind::Property(ref keys) => {
                        for key in keys.iter() {
                            if object.get(key).is_none() {
                                state.errors.push(Box::new(errors::Required {
                                    path: [path, key.as_ref()].join("/"),
                                }))
                            }
                        }
                    }
                }
            }
        }

        state.set_replacement(object);
        state
    }
}
