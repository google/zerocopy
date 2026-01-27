use super::super::errors;
use serde_json::Value;

pub struct AllowedValues {
    allowed_values: Vec<Value>,
}

impl AllowedValues {
    pub fn new(values: Vec<Value>) -> AllowedValues {
        AllowedValues {
            allowed_values: values,
        }
    }
}

impl super::Validator for AllowedValues {
    fn validate(&self, val: &Value, path: &str) -> super::ValidatorResult {
        let mut matched = false;
        for allowed_value in self.allowed_values.iter() {
            if val == allowed_value {
                matched = true;
            }
        }

        if matched {
            Ok(())
        } else {
            Err(vec![Box::new(errors::WrongValue {
                path: path.to_string(),
                detail: Some("Value is not among allowed list".to_string()),
            })])
        }
    }
}
