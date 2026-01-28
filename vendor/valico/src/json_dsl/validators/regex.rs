use serde_json::Value;

use super::super::errors;

impl super::Validator for fancy_regex::Regex {
    fn validate(&self, val: &Value, path: &str) -> super::ValidatorResult {
        let string = strict_process!(val.as_str(), path, "The value must be a string");

        match self.is_match(string) {
            Ok(true) => Ok(()),
            Ok(false) => Err(vec![Box::new(errors::WrongValue {
                path: path.to_string(),
                detail: Some("Value is not matched by required pattern".to_string()),
            })]),
            Err(e) => Err(vec![Box::new(errors::WrongValue {
                path: path.to_string(),
                detail: Some(format!("Error evaluating regex '{self}': {e}")),
            })]),
        }
    }
}
