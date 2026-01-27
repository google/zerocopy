use serde_json::Value;
use std::borrow::Cow;
use std::collections;

use super::super::errors;
use super::super::scope;

#[derive(Debug)]
pub enum AdditionalKind {
    Unspecified,
    Boolean(bool),
    Schema(url::Url),
}

#[allow(missing_copy_implementations)]
pub struct Properties {
    pub properties: collections::HashMap<String, url::Url>,
    pub additional: AdditionalKind,
    pub patterns: Vec<(fancy_regex::Regex, url::Url)>,
}

impl super::Validator for Properties {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut object = Cow::Borrowed(nonstrict_process!(val.as_object(), path));
        let mut state = super::ValidationState::new();

        if scope.supply_defaults {
            for (key, url) in self.properties.iter() {
                if let Some(schema) = scope.resolve(url) {
                    if object.get(key).is_none() && schema.has_default() {
                        object
                            .to_mut()
                            .insert(key.clone(), schema.get_default().unwrap());
                    }
                }
            }
        }

        // necessary due to object being mutated in the loop
        let keys = object.keys().cloned().collect::<Vec<_>>();
        'main: for key in keys.iter() {
            let is_property_passed = if self.properties.contains_key(key) {
                let url = &self.properties[key];
                let schema = scope.resolve(url);
                if let Some(schema) = schema {
                    let value_path = [path, key.as_ref()].join("/");
                    let mut result = schema.validate_in(&object[key], value_path.as_ref());
                    if result.is_valid() {
                        state.evaluated.insert(value_path);
                        if result.replacement.is_some() {
                            object
                                .to_mut()
                                .insert(key.to_string(), result.replacement.take().unwrap());
                        }
                    }
                    state.append(result);
                } else {
                    state.missing.push(url.clone())
                }

                true
            } else {
                false
            };

            let mut is_pattern_passed = false;
            for (regex, url) in self.patterns.iter() {
                if regex.is_match(key.as_ref()).unwrap_or(false) {
                    let schema = scope.resolve(url);
                    if let Some(schema) = schema {
                        let value_path = [path, key.as_ref()].join("/");
                        let mut result = schema.validate_in(&object[key], value_path.as_ref());
                        if result.is_valid() {
                            state.evaluated.insert(value_path);
                            if result.replacement.is_some() {
                                object
                                    .to_mut()
                                    .insert(key.to_string(), result.replacement.take().unwrap());
                            }
                        }
                        state.append(result);
                        is_pattern_passed = true;
                    } else {
                        state.missing.push(url.clone())
                    }
                }
            }

            if is_property_passed || is_pattern_passed {
                continue 'main;
            }

            match self.additional {
                AdditionalKind::Boolean(allowed) => {
                    if !allowed {
                        state.errors.push(Box::new(errors::Properties {
                            path: path.to_string(),
                            detail: format!("Additional property '{key}' is not allowed"),
                        }))
                    } else {
                        state.evaluated.insert([path, key.as_ref()].join("/"));
                    }
                }
                AdditionalKind::Schema(ref url) => {
                    let schema = scope.resolve(url);

                    if let Some(schema) = schema {
                        let value_path = [path, key.as_ref()].join("/");
                        let mut result = schema.validate_in(&object[key], value_path.as_ref());
                        if result.is_valid() {
                            state.evaluated.insert(value_path);
                            if result.replacement.is_some() {
                                object
                                    .to_mut()
                                    .insert(key.to_string(), result.replacement.take().unwrap());
                            }
                        }
                        state.append(result);
                    } else {
                        state.missing.push(url.clone())
                    }
                }
                // Additional are allowed here
                _ => (),
            }
        }

        state.set_replacement(object);
        state
    }
}
