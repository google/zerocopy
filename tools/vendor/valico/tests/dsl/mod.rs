use serde_json::Value;
use valico::json_dsl;
use valico::json_dsl::errors;
use valico::json_schema;
use valico::json_schema::errors as schema_errors;

use self::helpers::{
    assert_error, assert_error_with_scope, assert_str_eq, assert_str_eq_with_scope,
};

mod helpers;

#[test]
fn is_process_empty_builder() {
    let params = json_dsl::Builder::build(|_params| {});
    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":1}"#);
}

#[test]
fn is_process_simple_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_defined("a");
    });

    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":1}"#);
    assert_error::<errors::Required>(&params, r#"{}"#, "/a");
}

#[test]
fn is_process_i64_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::i64());
    });

    assert_str_eq(&params, r#"{"a":"1"}"#, r#"{"a":1}"#);

    // truncate!
    assert_str_eq(&params, r#"{"a": 1.112}"#, r#"{"a":1}"#);

    // error because "a" is string that we can't convert
    assert_error::<errors::WrongType>(&params, r#"{"a": "not-int"}"#, "/a");

    // error because "a" is object
    assert_error::<errors::WrongType>(&params, r#"{"a": {"a": 1}}"#, "/a");
}

#[test]
fn is_process_string_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::string());
    });

    assert_str_eq(&params, r#"{"a":"1"}"#, r#"{"a":"1"}"#);
    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":"1"}"#);
    assert_str_eq(&params, r#"{"a":1.112}"#, r#"{"a":"1.112"}"#);

    // error because "a" is object
    assert_error::<errors::WrongType>(&params, r#"{"a": {}}"#, "/a");

    // error because "a" is null
    assert_error::<errors::WrongType>(&params, r#"{"a": null}"#, "/a");
}

#[test]
fn is_process_boolean_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::boolean());
    });

    assert_str_eq(&params, r#"{"a":true}"#, r#"{"a":true}"#);
    assert_str_eq(&params, r#"{"a":false}"#, r#"{"a":false}"#);
    assert_str_eq(&params, r#"{"a":"true"}"#, r#"{"a":true}"#);
    assert_str_eq(&params, r#"{"a":"false"}"#, r#"{"a":false}"#);

    assert_error::<errors::WrongType>(&params, r#"{"a": null}"#, "/a");
    assert_error::<errors::WrongType>(&params, r#"{"a": 1}"#, "/a");
    assert_error::<errors::WrongType>(&params, r#"{"a": "not-bool"}"#, "/a");
}

#[test]
fn is_process_simple_array_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::array());
    });

    assert_str_eq(&params, r#"{"a":[1,"2",[3]]}"#, r#"{"a":[1,"2",[3]]}"#);

    // error because "a" is object
    assert_error::<errors::WrongType>(&params, r#"{"a": {}}"#, "/a");

    // error because "a" is string
    assert_error::<errors::WrongType>(&params, r#"{"a": "test"}"#, "/a");
}

#[test]
fn is_process_typed_array_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::array_of(json_dsl::string()));
    });

    // convert all to string
    assert_str_eq(&params, r#"{"a":[1,"2",3.1]}"#, r#"{"a":["1","2","3.1"]}"#);

    // error because "a" is object
    assert_error::<errors::WrongType>(&params, r#"{"a": {}}"#, "/a");

    // error because element at index(2) is not coersible to string
    assert_error::<errors::WrongType>(&params, r#"{"a": [1,2,{}]}"#, "/a/2");
}

#[test]
fn is_process_array_with_nested_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_nested("a", json_dsl::array(), |params| {
            params.req_typed("b", json_dsl::string());
            params.req_typed("c", json_dsl::array_of(json_dsl::u64()))
        });
    });

    assert_str_eq(
        &params,
        r#"{"a":[{"b":1,"c":["1"]}]}"#,
        r#"{"a":[{"b":"1","c":[1]}]}"#,
    );

    // error because element in "a" at index(0) is not coersible to string
    assert_error::<errors::WrongType>(&params, r#"{"a":[{"b":{},"c":["1"]}]}"#, "/a/0/b");

    // error because element in "a":0:"c":0 is not coersible to string
    assert_error::<errors::WrongType>(&params, r#"{"a":[{"b":1,"c":[{}]}]}"#, "/a/0/c/0");
}

#[test]
fn it_process_encoded_array() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::encoded_array(","));
    });

    assert_str_eq(&params, r#"{"a":"a,b,c"}"#, r#"{"a":["a","b","c"]}"#);
}

#[test]
fn it_process_encoded_array_of_type() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::encoded_array_of(",", json_dsl::u64()));
    });

    assert_str_eq(&params, r#"{"a":"1,2,3"}"#, r#"{"a":[1,2,3]}"#);
}

#[test]
fn is_process_object_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_typed("a", json_dsl::object());
    });

    assert_str_eq(&params, r#"{"a":{}}"#, r#"{"a":{}}"#);

    // error because "a" is array, not object
    assert_error::<errors::WrongType>(&params, r#"{"a":[]}"#, "/a");

    // error because "a" is string, not object
    assert_error::<errors::WrongType>(&params, r#"{"a":""}"#, "/a");
}

#[test]
fn is_process_object_with_nested_require() {
    let params = json_dsl::Builder::build(|params| {
        params.req_nested("a", json_dsl::object(), |params| {
            params.req_typed("b", json_dsl::f64());
            params.req_typed("c", json_dsl::array_of(json_dsl::string()));
        });
    });

    assert_str_eq(
        &params,
        r#"{"a":{"b":"1.22","c":[1.112,""]}}"#,
        r#"{"a":{"b":1.22,"c":["1.112",""]}}"#,
    );

    // error because "a":"b" is not a f64
    assert_error::<errors::WrongType>(&params, r#"{"a":{"b":"not-f64"},"c":[1.112,""]}"#, "/a/b");

    // error because "a":"c":"1" is object and can't be coerced to string
    assert_error::<errors::WrongType>(&params, r#"{"a":{"b":"1.22","c":[1.112,{}]}}"#, "/a/c/1");
}

#[test]
fn is_process_require_allows_null() {
    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::string());
        })
    });

    // error because a is not allow null explicitly
    assert_error::<errors::WrongType>(&params, r#"{"a":null}"#, "/a");

    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::string());
            a.allow_null();
        })
    });

    // ok because "a" allows null explicitly
    assert_str_eq(&params, r#"{"a":null}"#, r#"{"a":null}"#);
}

#[test]
fn is_validates_allow_values() {
    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::string());
            a.allow_values(&["allowed1".to_string(), "allowed2".to_string()])
        })
    });

    assert_str_eq(&params, r#"{"a":"allowed1"}"#, r#"{"a":"allowed1"}"#);
    assert_str_eq(&params, r#"{"a":"allowed2"}"#, r#"{"a":"allowed2"}"#);

    // error because "a" is not in allowed list
    assert_error::<errors::WrongValue>(&params, r#"{"a":"not in allowed"}"#, "/a");
}

#[test]
fn is_validates_reject_values() {
    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::string());
            a.reject_values(&["rejected1".to_string(), "rejected2".to_string()])
        })
    });

    assert_str_eq(&params, r#"{"a":"some"}"#, r#"{"a":"some"}"#);

    // errors because "a" is in reject list
    assert_error::<errors::WrongValue>(&params, r#"{"a":"rejected1"}"#, "/a");
    assert_error::<errors::WrongValue>(&params, r#"{"a":"rejected2"}"#, "/a");
}

#[test]
fn is_validates_with_function_validator() {
    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::u64());
            a.validate_with(|val: &Value, path: &str| {
                if *val == json!(2) {
                    Ok(())
                } else {
                    Err(vec![Box::new(errors::WrongType {
                        path: path.to_string(),
                        detail: "Value is not exactly 2".to_string(),
                    })])
                }
            });
        })
    });

    assert_str_eq(&params, r#"{"a":"2"}"#, r#"{"a":2}"#);
    assert_error::<errors::WrongType>(&params, r#"{"a":3}"#, "/a");
    assert_error::<errors::WrongType>(&params, r#"{"a":"3"}"#, "/a");
}

#[test]
#[allow(clippy::trivial_regex)]
fn is_validates_with_regex() {
    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::string());
            a.regex(fancy_regex::Regex::new("^test$").unwrap());
        })
    });

    assert_str_eq(&params, r#"{"a":"test"}"#, r#"{"a":"test"}"#);

    // error because "a" is not match regex
    assert_error::<errors::WrongValue>(&params, r#"{"a":"2"}"#, "/a");
    assert_error::<errors::WrongValue>(&params, r#"{"a":"test "}"#, "/a");

    let params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            // regex can't be applied to list, so it will never be valid
            a.coerce(json_dsl::array());
            a.regex(fancy_regex::Regex::new("^test$").unwrap());
        })
    });

    // "a" is valid list but it can't pass regex validation
    assert_error::<errors::WrongType>(&params, r#"{"a":[]}"#, "/a");
}

#[test]
fn is_validates_opt() {
    let params = json_dsl::Builder::build(|params| {
        params.req_defined("a");
        params.opt_typed("b", json_dsl::u64());
    });

    // ok because a is optional
    assert_str_eq(&params, r#"{"a":"test"}"#, r#"{"a":"test"}"#);
    assert_str_eq(&params, r#"{"a":"test","b":"1"}"#, r#"{"a":"test","b":1}"#);
}

#[test]
fn is_validates_opt_with_default() {
    let params = json_dsl::Builder::build(|params| {
        params.opt("a", |a| {
            a.default("default".to_string());
        });
    });

    assert_str_eq(&params, r#"{"a":"test"}"#, r#"{"a":"test"}"#);
    assert_str_eq(&params, r#"{}"#, r#"{"a":"default"}"#);
}

#[test]
fn is_validates_mutually_exclusive() {
    let params = json_dsl::Builder::build(|params| {
        params.opt_defined("a");
        params.opt_defined("b");

        params.mutually_exclusive(&["a", "b"])
    });

    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":1}"#);
    assert_str_eq(&params, r#"{"b":1}"#, r#"{"b":1}"#);
    assert_str_eq(&params, r#"{}"#, r#"{}"#);

    assert_error::<errors::MutuallyExclusive>(&params, r#"{"a":1,"b":1}"#, "/");
}

#[test]
fn is_validates_exactly_one_of() {
    let params = json_dsl::Builder::build(|params| {
        params.opt_defined("a");
        params.opt_defined("b");

        params.exactly_one_of(&["a", "b"])
    });

    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":1}"#);
    assert_str_eq(&params, r#"{"b":1}"#, r#"{"b":1}"#);

    assert_error::<errors::ExactlyOne>(&params, r#"{}"#, "/");
    assert_error::<errors::ExactlyOne>(&params, r#"{"a":1,"b":1}"#, "/");
}

#[test]
fn is_validates_at_least_one_of() {
    let params = json_dsl::Builder::build(|params| {
        params.opt_defined("a");
        params.opt_defined("b");

        params.at_least_one_of(&["a", "b"])
    });

    assert_str_eq(&params, r#"{"a":1}"#, r#"{"a":1}"#);
    assert_str_eq(&params, r#"{"b":1}"#, r#"{"b":1}"#);
    assert_str_eq(&params, r#"{"a":1,"b":1}"#, r#"{"a":1,"b":1}"#);

    assert_error::<errors::AtLeastOne>(&params, r#"{}"#, "/");
}

#[test]
fn is_validates_with_function() {
    let params = json_dsl::Builder::build(|params| {
        params.opt_defined("a");
        params.opt_defined("b");

        params.validate_with(|_: &Value, path: &str| {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "You shall not pass!".to_string(),
            })])
        });
    });

    assert_error::<errors::WrongType>(&params, r#"{}"#, "/");
}

#[test]
fn it_validates_with_schema() {
    let mut params = json_dsl::Builder::build(|params| {
        params.opt_typed("a", json_dsl::u64());
        params.opt_typed("b", json_dsl::u64());
        params.schema(|schema| {
            schema.max_properties(2);
        })
    });

    let mut scope = json_schema::Scope::new();
    params.build_schemes(&mut scope).unwrap();

    assert_str_eq_with_scope(
        &params,
        Some(&scope),
        r#"{"a":1, "b": 1}"#,
        r#"{"a":1,"b":1}"#,
    );
    assert_error_with_scope::<schema_errors::MaxProperties>(
        &params,
        Some(&scope),
        r#"{"a":1, "b": 1, "c": 1}"#,
        "/",
    );
}

#[test]
fn it_validates_params_with_schema() {
    let mut params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.schema(|schema| {
                schema.integer();
                schema.maximum(10f64);
            })
        });
    });

    let mut scope = json_schema::Scope::new();
    params.build_schemes(&mut scope).unwrap();

    assert_str_eq_with_scope(&params, Some(&scope), r#"{"a":1}"#, r#"{"a":1}"#);
    assert_error_with_scope::<schema_errors::Maximum>(&params, Some(&scope), r#"{"a":11}"#, "/a");
    assert_error_with_scope::<schema_errors::WrongType>(
        &params,
        Some(&scope),
        r#"{"a":"test"}"#,
        "/a",
    );
}

#[test]
fn it_validates_params_with_schema_and_coercion() {
    let mut params = json_dsl::Builder::build(|params| {
        params.req("a", |a| {
            a.coerce(json_dsl::u64());
            a.schema(|schema| {
                schema.maximum(10f64);
            })
        });
    });

    let mut scope = json_schema::Scope::new();
    params.build_schemes(&mut scope).unwrap();

    assert_str_eq_with_scope(&params, Some(&scope), r#"{"a":1}"#, r#"{"a":1}"#);
    assert_str_eq_with_scope(&params, Some(&scope), r#"{"a":"10"}"#, r#"{"a":10}"#);
    assert_error_with_scope::<schema_errors::Maximum>(&params, Some(&scope), r#"{"a":"11"}"#, "/a");
    assert_error_with_scope::<errors::WrongType>(&params, Some(&scope), r#"{"a":"test"}"#, "/a");
}
