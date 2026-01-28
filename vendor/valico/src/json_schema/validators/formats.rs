use addr::parser::{DomainName, EmailAddress};
use addr::psl::List;
use chrono;
use json_pointer;
use serde_json::Value;
use std::net;
use uritemplate;
use url;
use uuid;

use super::super::errors;
use super::super::scope;

#[allow(missing_copy_implementations)]
pub struct Date;

impl super::Validator for Date {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match chrono::NaiveDate::parse_from_str(string, "%Y-%m-%d") {
            Ok(_) => {
                if string.len() == 10 {
                    super::ValidationState::new()
                } else {
                    val_error!(errors::Format {
                        path: path.to_string(),
                        detail: "Malformed Date".to_string()
                    })
                }
            }
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed date".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct DateTime;

impl super::Validator for DateTime {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match chrono::DateTime::parse_from_rfc3339(string) {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed date time".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Email;

impl super::Validator for Email {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match List.parse_email_address(string) {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed email address".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Hostname;

impl super::Validator for Hostname {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match List.parse_domain_name(string) {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed hostname".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Ipv4;

impl super::Validator for Ipv4 {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match string.parse::<net::Ipv4Addr>() {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed IP address".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Ipv6;

impl super::Validator for Ipv6 {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match string.parse::<net::Ipv6Addr>() {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed IP address".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct IRI;

impl super::Validator for IRI {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match url::Url::parse(string) {
            Ok(_) => super::ValidationState::new(),
            Err(err) => val_error!(errors::Format {
                path: path.to_string(),
                detail: format!("Malformed IRI: {err}")
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct IRIReference;

impl super::Validator for IRIReference {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        let base_url = url::Url::parse("http://example.com/").unwrap();

        match base_url.join(string) {
            Ok(_) => super::ValidationState::new(),
            Err(err) => val_error!(errors::Format {
                path: path.to_string(),
                detail: format!("Malformed IRI reference: {err}")
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct JsonPointer;

impl super::Validator for JsonPointer {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match string.parse::<json_pointer::JsonPointer<_, _>>() {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed JSON pointer".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Regex;

impl super::Validator for Regex {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        // Forward slash ('/') is prefixed with double backslash ('\\')
        // in a JSON string. Although this is valid in JSON, this will fail
        // regex parsing in the rust Regex library. This string replacement
        // ensures that escaped forward slashes do not fail validation.
        let string = string.replace(r"\/", "/");

        match fancy_regex::Regex::new(&string) {
            Ok(_) => super::ValidationState::new(),
            Err(er) => {
                val_error!(errors::Format {
                    path: path.to_string(),
                    detail: format!("Malformed regex - {er}")
                })
            }
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct RelativeJsonPointer;

impl super::Validator for RelativeJsonPointer {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match string.parse::<json_pointer::JsonPointer<_, _>>() {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed relative JSON pointer".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Time;

impl super::Validator for Time {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match chrono::NaiveTime::parse_from_str(string, "%H:%M:%S%.f") {
            Ok(_) => super::ValidationState::new(),
            Err(_) => val_error!(errors::Format {
                path: path.to_string(),
                detail: "Malformed time".to_string()
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Uuid;

impl super::Validator for Uuid {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match string.parse::<uuid::Uuid>() {
            Ok(_) => super::ValidationState::new(),
            Err(err) => val_error!(errors::Format {
                path: path.to_string(),
                detail: format!("Malformed UUID: {err:?}")
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Uri;

impl super::Validator for Uri {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        match url::Url::parse(string) {
            Ok(_) => super::ValidationState::new(),
            Err(err) => val_error!(errors::Format {
                path: path.to_string(),
                detail: format!("Malformed URI: {err}")
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct UriReference;

impl super::Validator for UriReference {
    fn validate(
        &self,
        val: &Value,
        path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        let base_url = url::Url::parse("http://example.com/").unwrap();

        match base_url.join(string) {
            Ok(_) => super::ValidationState::new(),
            Err(err) => val_error!(errors::Format {
                path: path.to_string(),
                detail: format!("Malformed URI reference: {err}")
            }),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct UriTemplate;

impl super::Validator for UriTemplate {
    fn validate(
        &self,
        val: &Value,
        _path: &str,
        _scope: &scope::Scope,
        _: &super::ValidationState,
    ) -> super::ValidationState {
        let string = nonstrict_process!(val.as_str(), path);

        let _ = uritemplate::UriTemplate::new(string);
        super::ValidationState::new()
    }
}

#[cfg(test)]
pub mod tests {
    use super::Regex;
    use crate::json_schema::validators::Validator;
    use crate::json_schema::{Scope, ValidationState};

    #[test]
    fn validate_valid_empty_regex() {
        let result = validate_regex("");
        assert!(result.errors.is_empty())
    }

    #[test]
    fn validate_valid_regex_simple() {
        let result = validate_regex("^[a-z][a-z0-9]{0,10}$");
        assert!(result.errors.is_empty())
    }

    #[test]
    fn validate_valid_regex_with_double_escaped_forward_slash() {
        let result = validate_regex("\\w+:(\\/?\\/?)[^\\s]+");
        assert!(result.errors.is_empty())
    }

    #[test]
    fn validate_invalid_regex() {
        let result = validate_regex("FOO\\");
        assert_eq!(result.errors.len(), 1);

        let only_err = result.errors.get(0);
        assert!(only_err.is_some());

        let err = only_err.unwrap();
        assert!(err.get_detail().is_some());
        assert!(err.get_detail().unwrap().contains("Malformed regex"))
    }

    fn validate_regex(json_string: &str) -> ValidationState {
        let value = serde_json::value::Value::String(json_string.into());
        let scope = Scope::new();
        Regex {}.validate(&value, "/", &scope, &Default::default())
    }
}
