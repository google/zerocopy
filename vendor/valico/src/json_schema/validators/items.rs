use serde_json::Value;
use std::borrow::Cow;
use std::cmp;

use super::super::errors;
use super::super::scope;

#[derive(Debug)]
pub enum ItemsKind {
    Schema(url::Url),
    Array(Vec<url::Url>),
}

#[derive(Debug)]
pub enum AdditionalKind {
    Boolean(bool),
    Schema(url::Url),
}

#[allow(missing_copy_implementations)]
pub struct Items {
    pub items: Option<ItemsKind>,
    pub additional: Option<AdditionalKind>,
}

impl super::Validator for Items {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let mut array = Cow::Borrowed(nonstrict_process!(val.as_array(), path));
        let mut state = super::ValidationState::new();

        if scope.supply_defaults {
            if let Some(ItemsKind::Array(urls)) = self.items.as_ref() {
                // supply default values as long as there are more schema default values
                // than values in the validated array (but stop at first gap)
                for url in urls.iter().skip(array.len()) {
                    if let Some(schema) = scope.resolve(url) {
                        if let Some(default) = schema.get_default() {
                            array.to_mut().push(default);
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            }
        }

        match self.items {
            Some(ItemsKind::Schema(ref url)) => {
                // Just validate all items against the schema

                let schema = scope.resolve(url);
                if let Some(schema) = schema {
                    for idx in 0..array.len() {
                        let item = &array[idx];
                        let item_path = [path, idx.to_string().as_ref()].join("/");
                        let mut result = schema.validate_in(item, item_path.as_ref());
                        if result.is_valid() {
                            state.evaluated.insert(item_path);
                            if result.replacement.is_some() {
                                array.to_mut()[idx] = result.replacement.take().unwrap();
                            }
                        }
                        state.append(result);
                    }
                } else {
                    state.missing.push(url.clone());
                }
            }
            Some(ItemsKind::Array(ref urls)) => {
                let min = cmp::min(urls.len(), array.len());

                // Validate against schemas
                for idx in 0..min {
                    let schema = scope.resolve(&urls[idx]);
                    let item = &array[idx];

                    if let Some(schema) = schema {
                        let item_path = [path, idx.to_string().as_ref()].join("/");
                        let mut result = schema.validate_in(item, item_path.as_ref());

                        if result.is_valid() {
                            state.evaluated.insert(item_path);
                            if result.replacement.is_some() {
                                array.to_mut()[idx] = result.replacement.take().unwrap();
                            }
                        }
                        state.append(result);
                    } else {
                        state.missing.push(urls[idx].clone())
                    }
                }

                // Validate agains additional items
                if array.len() > urls.len() {
                    match self.additional {
                        Some(AdditionalKind::Boolean(allow)) => {
                            if !allow {
                                state.errors.push(Box::new(errors::Items {
                                    path: path.to_string(),
                                    detail: "Additional items are not allowed".to_string(),
                                }))
                            } else {
                                for idx in urls.len()..array.len() {
                                    state
                                        .evaluated
                                        .insert([path, idx.to_string().as_ref()].join("/"));
                                }
                            }
                        }
                        Some(AdditionalKind::Schema(ref url)) => {
                            let schema = scope.resolve(url);
                            if let Some(schema) = schema {
                                for idx in urls.len()..array.len() {
                                    let item = &array[idx];
                                    let item_path = [path, idx.to_string().as_ref()].join("/");
                                    let mut result = schema.validate_in(item, item_path.as_ref());
                                    if result.is_valid() {
                                        state.evaluated.insert(item_path);
                                        if result.replacement.is_some() {
                                            array.to_mut()[idx] =
                                                result.replacement.take().unwrap();
                                        }
                                    }
                                    state.append(result);
                                }
                            } else {
                                state.missing.push(url.clone())
                            }
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        }

        state.set_replacement(array);
        state
    }
}
