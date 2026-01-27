use serde_json::Value;

use super::super::errors;

pub struct AtLeastOneOf {
    params: Vec<String>,
}

impl AtLeastOneOf {
    pub fn new(params: &[&str]) -> AtLeastOneOf {
        AtLeastOneOf {
            params: params.iter().map(|s| (*s).to_string()).collect(),
        }
    }
}

impl super::Validator for AtLeastOneOf {
    fn validate(&self, val: &Value, path: &str) -> super::ValidatorResult {
        let object = strict_process!(val.as_object(), path, "The value must be an object");

        let mut matched = vec![];
        for param in self.params.iter() {
            if object.contains_key(param) {
                matched.push(param.clone());
            }
        }

        let len = matched.len();
        if len >= 1 {
            Ok(())
        } else {
            Err(vec![Box::new(errors::AtLeastOne {
                path: path.to_string(),
                detail: Some("At least one must be present".to_string()),
                params: self.params.clone(),
            })])
        }
    }
}
