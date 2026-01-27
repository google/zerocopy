use serde_json::Value;
use std::collections;

use super::super::schema;
use super::super::validators;

pub type FormatBuilders = collections::HashMap<String, Box<dyn super::Keyword + Send + Sync>>;

fn default_formats() -> FormatBuilders {
    let mut map: FormatBuilders = collections::HashMap::new();

    let date_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Date) as validators::BoxedValidator
        ))
    });
    map.insert("date".to_string(), date_builder);

    let date_time_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::DateTime) as validators::BoxedValidator
        ))
    });
    map.insert("date-time".to_string(), date_time_builder);

    let email_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Email) as validators::BoxedValidator
        ))
    });
    map.insert("email".to_string(), email_builder);

    let hostname_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Hostname) as validators::BoxedValidator
        ))
    });
    map.insert("hostname".to_string(), hostname_builder);

    let idn_email_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Email) as validators::BoxedValidator
        ))
    });
    map.insert("idn-email".to_string(), idn_email_builder);

    let idn_hostname_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Hostname) as validators::BoxedValidator
        ))
    });
    map.insert("idn-hostname".to_string(), idn_hostname_builder);

    let ipv4_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Ipv4) as validators::BoxedValidator
        ))
    });
    map.insert("ipv4".to_string(), ipv4_builder);

    let ipv6_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Ipv6) as validators::BoxedValidator
        ))
    });
    map.insert("ipv6".to_string(), ipv6_builder);

    let iri_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::IRI) as validators::BoxedValidator
        ))
    });
    map.insert("iri".to_string(), iri_builder);

    let iri_reference_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::IRIReference) as validators::BoxedValidator
        ))
    });
    map.insert("iri-reference".to_string(), iri_reference_builder);

    let json_pointer_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::JsonPointer) as validators::BoxedValidator
        ))
    });
    map.insert("json-pointer".to_string(), json_pointer_builder);

    let regex_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Regex) as validators::BoxedValidator
        ))
    });
    map.insert("regex".to_string(), regex_builder);

    let relative_json_pointer_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::RelativeJsonPointer) as validators::BoxedValidator
        ))
    });
    map.insert(
        "relative-json-pointer".to_string(),
        relative_json_pointer_builder,
    );

    let time_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Time) as validators::BoxedValidator
        ))
    });
    map.insert("time".to_string(), time_builder);

    let uri_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Uri) as validators::BoxedValidator
        ))
    });
    map.insert("uri".to_string(), uri_builder);

    let uri_reference_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::UriReference) as validators::BoxedValidator
        ))
    });
    map.insert("uri-reference".to_string(), uri_reference_builder);

    let uri_template_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::UriTemplate) as validators::BoxedValidator
        ))
    });
    map.insert("uri-template".to_string(), uri_template_builder);

    let uuid_builder = Box::new(|_def: &Value, _ctx: &schema::WalkContext<'_>| {
        Ok(Some(
            Box::new(validators::formats::Uuid) as validators::BoxedValidator
        ))
    });
    map.insert("uuid".to_string(), uuid_builder);

    map
}

#[allow(missing_copy_implementations)]
pub struct Format {
    pub formats: FormatBuilders,
}

impl Format {
    pub fn new() -> Format {
        Format {
            formats: default_formats(),
        }
    }

    pub fn with<F>(build_formats: F) -> Format
    where
        F: FnOnce(&mut FormatBuilders),
    {
        let mut formats = default_formats();
        build_formats(&mut formats);
        Format { formats }
    }
}

impl super::Keyword for Format {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let format = keyword_key_exists!(def, "format");

        if format.is_string() {
            let format = format.as_str().unwrap();
            match self.formats.get(format) {
                Some(keyword) => keyword.compile(def, ctx),
                None => Ok(None),
            }
        } else {
            Err(schema::SchemaError::Malformed {
                path: ctx.fragment.join("/"),
                detail: "The value of format MUST be a string".to_string(),
            })
        }
    }
}

#[cfg(test)]
use super::super::builder;
#[cfg(test)]
use super::super::scope;
#[cfg(test)]
use serde_json::to_value;

#[test]
fn validate_date_time() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("date-time");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value("2015-01-20T17:35:20-08:00").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("1944-06-06T04:04:00Z").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("Tue, 20 Jan 2015 17:35:20 -0800").unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_time() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("time");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value("17:35:20-08:00").unwrap())
            .is_valid(),
        false
    );
    assert_eq!(
        schema
            .validate(&to_value("04:04:00.040404Z").unwrap())
            .is_valid(),
        false // https://github.com/chronotope/chrono/issues/288
    );
    assert_eq!(
        schema
            .validate(&to_value("17:35:20 -0800").unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_date() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("date");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("2015-01-20").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("Tue, 20 Jan 2015").unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_email() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("email");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("ad@ress").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("add.ress+fd@domain.co.com").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("add:re").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_hostname() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("hostname");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("example").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("example.com").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("ex:ample").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_ipv4() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("ipv4");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("127.0.0.1").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("8.8.8.8").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("::::0.0.0.0").unwrap())
            .is_valid(),
        false
    );
}

#[test]
fn validate_ipv6() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("ipv6");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value("FE80:0000:0000:0000:0202:B3FF:FE1E:8329").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("127.0.0.1").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_json_pointer() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("json-pointer");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema.validate(&to_value("/foo/bar").unwrap()).is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("pointer").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_uri() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("uri");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value("http://example.com").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema.validate(&to_value("some-wrong").unwrap()).is_valid(),
        false
    );
}

#[test]
fn validate_uuid() {
    let mut scope = scope::Scope::new();
    let schema = scope
        .compile_and_return(
            builder::schema(|s| {
                s.format("uuid");
            })
            .into_json(),
            true,
        )
        .ok()
        .unwrap();

    assert_eq!(
        schema
            .validate(&to_value("2f5a2593-7481-49e2-9911-8fe2ad069aac").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("2f5a2593748149e299118fe2ad069aac").unwrap())
            .is_valid(),
        true
    );
    assert_eq!(
        schema
            .validate(&to_value("2f5a2593-7481-49e2-9911-8fe2ad06").unwrap())
            .is_valid(),
        false
    );
}
