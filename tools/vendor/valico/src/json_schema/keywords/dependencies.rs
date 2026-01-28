use serde_json::Value;

use crate::json_schema::validators::dependencies::DepKind;

use super::super::helpers;
use super::super::schema;
use super::super::validators;

enum DepsMode {
    AllowAny,
    DependentSchemas,
    DependentRequired,
}

impl DepsMode {
    fn get_error(&self) -> String {
        match self {
            DepsMode::AllowAny => {
                "Each value of dependencies MUST be either an object, an array or a boolean."
            }
            DepsMode::DependentSchemas => {
                "Each value of 'dependentSchemas' MUST be an object or a boolean."
            }
            DepsMode::DependentRequired => "Each value of 'dependentRequired' MUST be an array.",
        }
        .to_owned()
    }
}

impl PartialEq for DepsMode {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DepsMode::AllowAny, _) => true,
            (_, DepsMode::AllowAny) => true,
            (a, b) => core::mem::discriminant(a) == core::mem::discriminant(b),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct Dependencies;
impl Dependencies {
    fn extract_dependencies(
        &self,
        deps: &Value,
        ctx: &schema::WalkContext<'_>,
        deps_key: &str,
        mode: DepsMode,
    ) -> Result<Vec<(String, DepKind)>, schema::SchemaError> {
        if !deps.is_object() {
            return Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of this keyword MUST be an object.".to_string(),
            });
        }

        let deps = deps.as_object().unwrap();
        let mut items = vec![];
        for (key, item) in deps.iter() {
            if (item.is_object() || item.is_boolean()) && mode == DepsMode::DependentSchemas {
                items.push((
                    key.clone(),
                    validators::dependencies::DepKind::Schema(helpers::alter_fragment_path(
                        ctx.url.clone(),
                        [
                            ctx.escaped_fragment().as_ref(),
                            deps_key,
                            helpers::encode(key).as_ref(),
                        ]
                        .join("/"),
                    )),
                ));
            } else if item.is_array() && mode == DepsMode::DependentRequired {
                let item = item.as_array().unwrap();
                let mut keys = vec![];
                for key in item.iter() {
                    if key.is_string() {
                        keys.push(key.as_str().unwrap().to_string())
                    } else {
                        return Err(schema::SchemaError::Malformed {
                            path: ctx.fragment.join("/"),
                            detail: "Each element MUST be a string, and elements in the array MUST be unique.".to_string()
                        });
                    }
                }
                items.push((
                    key.clone(),
                    validators::dependencies::DepKind::Property(keys),
                ));
            } else {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: mode.get_error(),
                });
            }
        }

        Ok(items)
    }
}

impl super::Keyword for Dependencies {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let items = if let Some(deps) = def.get("dependencies") {
            self.extract_dependencies(deps, ctx, "dependencies", DepsMode::AllowAny)?
        } else {
            let required = def.get("dependentRequired");
            let schemas = def.get("dependentSchemas");

            if required.is_none() && schemas.is_none() {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "dependencies has changed to dependentRequired and dependentSchemas in Draft 2019-09.".to_string(),
                });
            }

            let mut items = vec![];
            items.extend(
                required
                    .map(|v| {
                        self.extract_dependencies(
                            v,
                            ctx,
                            "dependentRequired",
                            DepsMode::DependentRequired,
                        )
                    })
                    .transpose()?
                    .into_iter()
                    .flatten(),
            );
            items.extend(
                schemas
                    .map(|v| {
                        self.extract_dependencies(
                            v,
                            ctx,
                            "dependentSchemas",
                            DepsMode::DependentSchemas,
                        )
                    })
                    .transpose()?
                    .into_iter()
                    .flatten(),
            );
            items
        };

        Ok(Some(Box::new(validators::Dependencies { items })))
    }
}

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;

#[cfg(test)]
fn mk_schema() -> Value {
    json!({
        "dependencies": {
            "x": {
                "properties": {
                    "y": {
                        "type": "string",
                        "default": "buh"
                    },
                }
            }
        }
    })
}

#[test]
fn no_default_for_schema() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    assert_eq!(schema.get_default(), None);
}

#[test]
fn default_when_needed() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"x": 12}));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, Some(json!({"x": 12, "y": "buh"})));
}

#[test]
fn no_default_otherwise() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!({"x": 12, "y": "a"}));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, None);
}

#[test]
fn no_default_otherwise2() {
    let mut scope = scope::Scope::new().supply_defaults();
    let schema = scope.compile_and_return(mk_schema(), true).unwrap();
    let result = schema.validate(&json!(12));
    assert!(result.is_strictly_valid());
    assert_eq!(result.replacement, None);
}

#[test]
fn validate_dependencies() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.dependencies(|deps| {
                    deps.schema("isbn", |isbn| {
                        isbn.required(vec!["price".to_string()]);
                        isbn.properties(|props| {
                            props.insert("price", |price| {
                                price.multiple_of(5f64);
                            })
                        })
                    });
                    deps.property("item_id", vec!["item_name".to_string()]);
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
                    obj.set("isbn", "some_isbn".to_string());
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
                    obj.set("isbn", "some_isbn".to_string());
                    obj.set("price", 773);
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
                    obj.set("isbn", "some_isbn".to_string());
                    obj.set("price", 775);
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
                    obj.set("item_id", "some_id".to_string());
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
                    obj.set("item_id", "some_id".to_string());
                    obj.set("item_name", "some_name".to_string());
                })
                .unwrap()
            )
            .is_valid(),
        true
    );
}

#[test]
fn malformed() {
    let mut scope = scope::Scope::new();

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("dependencies", |deps| {
                    deps.set("isbn", 10);
                });
            })
            .unwrap(),
            true
        )
        .is_err());

    assert!(scope
        .compile_and_return(
            jsonway::object(|schema| {
                schema.object("dependencies", |deps| {
                    deps.array("item_id", |item_id| item_id.push(10));
                });
            })
            .unwrap(),
            true
        )
        .is_err());
}
