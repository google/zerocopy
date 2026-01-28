#![allow(clippy::match_wild_err_arm)]

use serde_json::{from_str, to_string, Value};
use valico::common::error;
use valico::json_dsl;
use valico::json_schema;

pub fn test_result(
    params: &json_dsl::Builder,
    scope: Option<&json_schema::Scope>,
    body: &str,
) -> Value {
    let obj = from_str(body);
    match obj {
        Ok(mut json) => {
            let state = params.process(&mut json, scope);
            if state.is_strictly_valid() {
                json
            } else {
                panic!("Errors during process: {:?}", state);
            }
        }
        Err(_) => {
            panic!("Invalid JSON");
        }
    }
}

pub fn get_errors(
    params: &json_dsl::Builder,
    scope: Option<&json_schema::Scope>,
    body: &str,
) -> Vec<Box<dyn error::ValicoError>> {
    let obj = from_str(body);
    match obj {
        Ok(mut json) => {
            let state = params.process(&mut json, scope);
            if state.is_strictly_valid() {
                panic!("Success response when we await some errors");
            } else {
                state.errors
            }
        }
        Err(_) => {
            panic!("Invalid JSON");
        }
    }
}

pub fn assert_str_eq_with_scope(
    params: &json_dsl::Builder,
    scope: Option<&json_schema::Scope>,
    body: &str,
    res: &str,
) {
    assert_eq!(
        to_string(&test_result(params, scope, body)).unwrap(),
        res.to_string()
    );
}

pub fn assert_error_with_scope<T: error::ValicoError + 'static>(
    params: &json_dsl::Builder,
    scope: Option<&json_schema::Scope>,
    body: &str,
    path: &str,
) {
    let errors = get_errors(params, scope, body);
    let error = errors.iter().find(|error| {
        let err = error.downcast_ref::<T>();
        err.is_some() && err.unwrap().get_path() == path
    });

    assert!(
        error.is_some(),
        "{}",
        "Can't find error in {path}. Errors: {errors:?}"
    )
}

pub fn assert_str_eq(params: &json_dsl::Builder, body: &str, res: &str) {
    assert_str_eq_with_scope(params, None, body, res);
}

pub fn assert_error<T: error::ValicoError + 'static>(
    params: &json_dsl::Builder,
    body: &str,
    path: &str,
) {
    assert_error_with_scope::<T>(params, None, body, path);
}
