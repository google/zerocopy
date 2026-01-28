use serde_json::Value;

use super::super::errors;

pub struct MutuallyExclusive {
    params: Vec<String>,
}

impl MutuallyExclusive {
    pub fn new(params: &[&str]) -> MutuallyExclusive {
        MutuallyExclusive {
            params: params.iter().map(|s| (*s).to_string()).collect(),
        }
    }
}

impl super::Validator for MutuallyExclusive {
    fn validate(&self, val: &Value, path: &str) -> super::ValidatorResult {
        let object = strict_process!(val.as_object(), path, "The value must be an object");

        let mut matched = vec![];
        for param in self.params.iter() {
            if object.contains_key(param) {
                matched.push(param.clone());
            }
        }

        if matched.len() <= 1 {
            Ok(())
        } else {
            Err(vec![Box::new(errors::MutuallyExclusive {
                path: path.to_string(),
                params: matched,
                detail: Some("Fields are mutually exclusive".to_string()),
            })])
        }
    }
}
