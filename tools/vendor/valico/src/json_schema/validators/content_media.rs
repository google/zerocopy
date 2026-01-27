use serde_json::Value;

use super::super::errors;
use super::super::scope;

use super::super::keywords::content_media::{ContentEncoding, ContentMediaType};

#[allow(missing_copy_implementations)]
pub struct ContentMedia {
    pub type_: Option<ContentMediaType>,
    pub encoding: Option<ContentEncoding>,
}

impl super::Validator for ContentMedia {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let decoded_val = if self.encoding.is_some() && val.is_string() {
            let v = self
                .encoding
                .as_ref()
                .unwrap()
                .decode_val(val.as_str().unwrap());
            if v.is_err() {
                return val_error!(errors::Format {
                    path: path.to_string(),
                    detail: v.err().unwrap(),
                });
            }
            Some(Value::String(v.ok().unwrap()))
        } else {
            None
        };

        let val_ = if decoded_val.is_some() {
            decoded_val.as_ref().unwrap()
        } else {
            val
        };

        if self.type_.is_some()
            && val_.is_string()
            && !self
                .type_
                .as_ref()
                .unwrap()
                .validate(val_.as_str().unwrap())
        {
            return val_error!(errors::Format {
                path: path.to_string(),
                detail: "".to_string(),
            });
        }

        super::ValidationState::new()
    }
}
