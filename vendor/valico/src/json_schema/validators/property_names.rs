use serde_json::Value;

use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct PropertyNames {
    pub url: url::Url,
}

impl super::Validator for PropertyNames {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let object = nonstrict_process!(val.as_object(), path);

        let schema = scope.resolve(&self.url);
        let mut state = super::ValidationState::new();

        if let Some(schema) = schema {
            for key in object.keys() {
                let item_path = [path, ["[", key.as_ref(), "]"].join("").as_ref()].join("/");
                state.append(schema.validate_in(&Value::from(key.clone()), item_path.as_ref()));
            }
        } else {
            state.missing.push(self.url.clone());
        }

        state
    }
}
