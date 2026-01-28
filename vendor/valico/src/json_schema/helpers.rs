use serde_json::Value;
use serde_json::Value::Number;
use url::Url;
use uuid::Uuid;

use super::schema;

pub fn generate_id() -> Url {
    let uuid = Uuid::new_v4();
    Url::parse(&format!("json-schema://{uuid}")).unwrap()
}

/// <http://tools.ietf.org/html/draft-ietf-appsawg-json-pointer-07>
pub fn encode(string: &str) -> String {
    const QUERY_SET: percent_encoding::AsciiSet = percent_encoding::CONTROLS
        .add(b' ')
        .add(b'"')
        .add(b'#')
        .add(b'<')
        .add(b'>')
        .add(b'%');
    percent_encoding::percent_encode(
        string.replace('~', "~0").replace('/', "~1").as_bytes(),
        &QUERY_SET,
    )
    .to_string()
}

/// Encode and connect
pub fn connect(strings: &[&str]) -> String {
    strings
        .iter()
        .map(|s| encode(s))
        .collect::<Vec<String>>()
        .join("/")
}

pub fn parse_url_key(key: &str, obj: &Value) -> Result<Option<Url>, schema::SchemaError> {
    match obj.get(key) {
        Some(value) => match value.as_str() {
            Some(string) => Url::parse(string)
                .map(Some)
                .map_err(schema::SchemaError::UrlParseError),
            None => Ok(None),
        },
        None => Ok(None),
    }
}

pub fn parse_url_key_with_base(
    key: &str,
    obj: &Value,
    base: &Url,
) -> Result<Option<Url>, schema::SchemaError> {
    match obj.get(key) {
        Some(value) => match value.as_str() {
            Some(string) => Url::options()
                .base_url(Some(base))
                .parse(string)
                .map(Some)
                .map_err(schema::SchemaError::UrlParseError),
            None => Ok(None),
        },
        None => Ok(None),
    }
}

pub fn alter_fragment_path(mut url: Url, new_fragment: String) -> Url {
    let normalized_fragment = if let Some(prefix) = new_fragment.strip_prefix('/') {
        prefix
    } else {
        new_fragment.as_ref()
    };

    let result_fragment = match url.fragment() {
        Some(fragment) if !fragment.is_empty() => {
            if !fragment.starts_with('/') {
                let mut result_fragment = "".to_string();
                let mut fragment_parts = fragment.split('/').map(|s| s.to_string());
                result_fragment.push('#');
                result_fragment.push_str(fragment_parts.next().unwrap().as_ref());
                result_fragment.push('/');
                result_fragment.push_str(normalized_fragment.as_ref());
                result_fragment
            } else {
                "/".to_string() + normalized_fragment
            }
        }
        _ => "/".to_string() + normalized_fragment,
    };

    url.set_fragment(Some(&result_fragment));
    url
}

pub fn serialize_schema_path(url: &Url) -> (String, Option<String>) {
    let mut url_without_fragment = url.clone();
    url_without_fragment.set_fragment(None);
    let mut url_str: String = url_without_fragment.into();

    match url.fragment().as_ref() {
        Some(fragment) if !fragment.is_empty() => {
            if !fragment.starts_with('/') {
                let fragment_parts = fragment
                    .split('/')
                    .map(|s| s.to_string())
                    .collect::<Vec<String>>();
                url_str.push('#');
                url_str.push_str(fragment_parts[0].as_ref());
                let fragment = if fragment_parts.len() > 1 {
                    Some("/".to_string() + fragment_parts[1..].join("/").as_ref())
                } else {
                    None
                };
                (url_str, fragment)
            } else {
                (url_str, Some((*fragment).to_string()))
            }
        }
        _ => (url_str, None),
    }
}

pub fn convert_boolean_schema(val: Value) -> Value {
    match val.as_bool() {
        Some(b) => {
            if b {
                json!({})
            } else {
                json!({"not": {}})
            }
        }
        None => val,
    }
}

pub fn is_matching(va: &Value, vb: &Value) -> bool {
    match va {
        Number(a) => match vb {
            Number(b) => a.as_f64().unwrap() == b.as_f64().unwrap(),
            _ => false,
        },
        _ => *va == *vb,
    }
}
