use serde_json::Value;
use std::collections;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Properties;
impl super::Keyword for Properties {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let maybe_properties = def.get("properties");
        let maybe_additional = def.get("additionalProperties");
        let maybe_pattern = def.get("patternProperties");

        if maybe_properties.is_none() && maybe_additional.is_none() && maybe_pattern.is_none() {
            return Ok(None);
        }

        let properties = if let Some(properties) = maybe_properties {
            if let Some(properties) = properties.as_object() {
                let mut schemes = collections::HashMap::new();
                for (key, value) in properties.iter() {
                    if value.is_object() || value.is_boolean() {
                        schemes.insert(
                            key.to_string(),
                            helpers::alter_fragment_path(
                                ctx.url.clone(),
                                [
                                    ctx.escaped_fragment().as_ref(),
                                    "properties",
                                    helpers::encode(key).as_ref(),
                                ]
                                .join("/"),
                            ),
                        );
                    } else {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx
                                .fragment
                                .iter()
                                .map(String::as_str)
                                .chain(["properties", key])
                                .flat_map(|s| s.chars().chain(['/']))
                                .collect(),
                            detail: "Each value of this object MUST be an object or a boolean"
                                .to_string(),
                        });
                    }
                }
                schemes
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "The value of `properties` MUST be an object.".to_string(),
                });
            }
        } else {
            collections::HashMap::new()
        };

        let additional_properties = if let Some(additional_val) = maybe_additional {
            if additional_val.is_boolean() {
                validators::properties::AdditionalKind::Boolean(additional_val.as_bool().unwrap())
            } else if additional_val.is_object() {
                validators::properties::AdditionalKind::Schema(helpers::alter_fragment_path(
                    ctx.url.clone(),
                    [ctx.escaped_fragment().as_ref(), "additionalProperties"].join("/"),
                ))
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "The value of `additionalProperties` MUST be a boolean or an object."
                        .to_string(),
                });
            }
        } else {
            validators::properties::AdditionalKind::Unspecified
        };

        let patterns = if let Some(pattern) = maybe_pattern {
            if pattern.is_object() {
                let pattern = pattern.as_object().unwrap();
                let mut patterns = vec![];

                for (key, value) in pattern.iter() {
                    if value.is_object() || value.is_boolean() {
                        match fancy_regex::Regex::new(key.as_ref()) {
                            Ok(regex) => {
                                let url = helpers::alter_fragment_path(ctx.url.clone(), [
                                    ctx.escaped_fragment().as_ref(),
                                    "patternProperties",
                                    helpers::encode(key).as_ref()
                                ].join("/"));
                                patterns.push((regex, url));
                            },
                            Err(_) => {
                                return Err(schema::SchemaError::Malformed {
                                    path: ctx.fragment.join("/"),
                                    detail: "Each property name of this object SHOULD be a valid regular expression.".to_string()
                                })
                            }
                        }
                    } else {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx.fragment.join("/") + "patternProperties",
                            detail: "Each value of this object MUST be an object or a boolean"
                                .to_string(),
                        });
                    }
                }

                patterns
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "The value of `patternProperties` MUST be an object".to_string(),
                });
            }
        } else {
            vec![]
        };

        Ok(Some(Box::new(validators::Properties {
            properties,
            additional: additional_properties,
            patterns,
        })))
    }

    fn place_first(&self) -> bool {
        true
    }
}

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;

#[test]
fn validate_properties() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.properties(|props| {
                    props.insert("prop1", |prop1| {
                        prop1.maximum(10f64);
                    });
                    props.insert("prop2", |prop2| {
                        prop2.minimum(11f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 11);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 11);
                    obj.set("prop2", 11);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 10);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 11);
                    obj.set("prop3", 1000); // not validated
                })
                .unwrap()
            )
            .is_valid(),
        true
    );
}

#[test]
fn validate_kw_properties() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.properties(|props| {
                    props.insert("id", |prop1| {
                        prop1.maximum(10f64);
                    });
                    props.insert("items", |prop2| {
                        prop2.minimum(11f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("id", 10);
                    obj.set("items", 11);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("id", 11);
                    obj.set("items", 11);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );
}

#[test]
fn validate_pattern_properties() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.properties(|properties| {
                    properties.insert("prop1", |prop1| {
                        prop1.maximum(10f64);
                    });
                });
                s.pattern_properties(|properties| {
                    properties.insert("prop.*", |prop| {
                        prop.maximum(1000f64);
                    });
                });
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 11);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1000);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1001);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );
}

#[test]
fn validate_additional_properties_false() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.properties(|properties| {
                    properties.insert("prop1", |prop1| {
                        prop1.maximum(10f64);
                    });
                });
                s.pattern_properties(|properties| {
                    properties.insert("prop.*", |prop| {
                        prop.maximum(1000f64);
                    });
                });
                s.additional_properties(false);
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1000);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1000);
                    obj.set("some_other", 0);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );
}

#[test]
fn validate_additional_properties_schema() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.properties(|properties| {
                    properties.insert("prop1", |prop1| {
                        prop1.maximum(10f64);
                    });
                });
                s.pattern_properties(|properties| {
                    properties.insert("prop.*", |prop| {
                        prop.maximum(1000f64);
                    });
                });
                s.additional_properties_schema(|additional| additional.maximum(5f64));
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1000);
                    obj.set("some_other", 5);
                })
                .unwrap()
            )
            .is_valid(),
        true
    );

    assert_eq!(
        schema
            .validate(
                &jsonway::object(|obj| {
                    obj.set("prop1", 10);
                    obj.set("prop2", 1000);
                    obj.set("some_other", 6);
                })
                .unwrap()
            )
            .is_valid(),
        false
    );
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("properties", false);
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("patternProperties", false);
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("patternProperties", |pattern| pattern.set("test", 1));
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("patternProperties", |pattern| {
                    pattern.object("((", |_malformed| {})
                });
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.set("additionalProperties", 10);
            })
            .unwrap(),
            true
        )
        .is_err());
}
