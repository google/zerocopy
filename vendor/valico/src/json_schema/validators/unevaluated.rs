use std::{borrow::Cow, collections::HashSet};

use crate::json_schema::errors;

pub enum UnevaluatedSchema {
    Bool(bool),
    Schema(url::Url),
}

pub struct Unevaluated {
    pub is_items: bool,
    pub schema: UnevaluatedSchema,
}

impl Unevaluated {
    fn check_one_item(
        &self,
        item_path: String,
        item: &serde_json::Value,
        scope: &crate::json_schema::scope::Scope,
    ) -> super::ValidationState {
        let mut state = super::ValidationState::new();
        match self.schema {
            UnevaluatedSchema::Bool(allow_unevaluated) => {
                if !allow_unevaluated {
                    state.errors.push(Box::new(errors::Unevaluated {
                        path: item_path,
                        detail: if self.is_items {
                            "Unevaluated items are not allowed".to_string()
                        } else {
                            "Unevaluated properties are not allowed".to_string()
                        },
                    }));
                } else {
                    state.evaluated.insert(item_path);
                }
            }
            UnevaluatedSchema::Schema(ref url) => {
                let schema = scope.resolve(url);
                if let Some(schema) = schema {
                    let mut result = schema.validate_in(item, item_path.as_ref());
                    if result.is_valid() {
                        state.evaluated.insert(item_path);
                        state.replacement = result.replacement.take();
                    }

                    state.append(result);
                } else {
                    state.missing.push(url.clone())
                }
            }
        }

        state
    }
}

impl super::Validator for Unevaluated {
    fn validate(
        &self,
        val: &serde_json::Value,
        path: &str,
        scope: &crate::json_schema::scope::Scope,
        state: &super::ValidationState,
    ) -> super::ValidationState {
        let evaluated_children: HashSet<_> = state
            .evaluated
            .iter()
            .filter(|i| i.starts_with(path))
            .collect();
        let mut state = super::ValidationState::new();

        if self.is_items {
            let mut array = Cow::Borrowed(nonstrict_process!(val.as_array(), path));

            for idx in 0..array.len() {
                let item_path = [path, idx.to_string().as_ref()].join("/");
                let item = &array[idx];
                if evaluated_children.contains(&item_path) {
                    continue;
                }

                let mut result = self.check_one_item(item_path, item, scope);
                if result.replacement.is_some() {
                    array.to_mut()[idx] = result.replacement.take().unwrap();
                }
                state.append(result);
            }

            state.set_replacement(array);
        } else {
            let mut object = nonstrict_process!(val.as_object(), path).clone();
            let mut changed = false;
            for (k, item) in object.iter_mut() {
                let item_path = [path, k].join("/");

                if evaluated_children.contains(&item_path) {
                    continue;
                }

                let mut result = self.check_one_item(item_path, item, scope);
                if result.replacement.is_some() {
                    *item = result.replacement.take().unwrap();
                    changed = true;
                }
                state.append(result);
            }

            if changed {
                state.set_replacement(std::borrow::Cow::Owned::<
                    serde_json::Map<String, serde_json::Value>,
                >(object));
            }
        }

        state
    }
}
