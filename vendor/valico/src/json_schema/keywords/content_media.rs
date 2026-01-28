use base64;
use base64::Engine;
use serde_json::Value;
use std::str;

use super::super::schema;
use super::super::validators;

#[derive(Debug)]
pub enum ContentMediaType {
    ApplicationJson,
}

impl ContentMediaType {
    pub fn as_str(&self) -> &str {
        match self {
            ContentMediaType::ApplicationJson => "application/json",
        }
    }

    pub fn validate(&self, val: &str) -> bool {
        match self {
            ContentMediaType::ApplicationJson => serde_json::from_str::<Value>(val),
        }
        .is_ok()
    }
}

impl str::FromStr for ContentMediaType {
    type Err = ();
    fn from_str(s: &str) -> Result<ContentMediaType, ()> {
        match s {
            "application/json" => Ok(ContentMediaType::ApplicationJson),
            _ => Err(()),
        }
    }
}

#[derive(Debug)]
pub enum ContentEncoding {
    Base64,
}

impl ContentEncoding {
    pub fn as_str(&self) -> &str {
        match self {
            ContentEncoding::Base64 => "base64",
        }
    }

    pub fn decode_val(&self, val: &str) -> Result<String, String> {
        match self {
            ContentEncoding::Base64 => {
                match base64::engine::general_purpose::STANDARD.decode(val) {
                    Ok(v) => match str::from_utf8(&v[..]) {
                        Ok(s) => Ok(s.to_string()),
                        Err(e) => Err(e.to_string()),
                    },
                    Err(e) => Err(e.to_string()),
                }
            }
        }
    }
}

impl str::FromStr for ContentEncoding {
    type Err = ();
    fn from_str(s: &str) -> Result<ContentEncoding, ()> {
        match s {
            "base64" => Ok(ContentEncoding::Base64),
            _ => Err(()),
        }
    }
}

#[allow(missing_copy_implementations)]
pub struct ContentMedia;
impl super::Keyword for ContentMedia {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> super::KeywordResult {
        let maybe_content_media_type = def.get("contentMediaType");
        let mut type_ = None;
        if let Some(content_media_type) = maybe_content_media_type {
            if !content_media_type.is_string() {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "contentMediaType MUST be a string.".to_string(),
                });
            } else {
                let media_type = content_media_type.as_str().unwrap().parse().ok();
                if let Some(media_type) = media_type {
                    type_ = Some(media_type);
                } else {
                    return Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "contentMediaType MUST be one of [\"application/json\"]"
                            .to_string(),
                    });
                }
            }
        }

        let maybe_content_encoding = def.get("contentEncoding");
        let mut encoding = None;
        if let Some(content_encoding) = maybe_content_encoding {
            if !content_encoding.is_string() {
                return Err(schema::SchemaError::Malformed {
                    path: ctx.fragment.join("/"),
                    detail: "contentEncoding MUST be a string.".to_string(),
                });
            } else {
                let encoding_ = content_encoding.as_str().unwrap().parse().ok();
                if let Some(encoding_) = encoding_ {
                    encoding = Some(encoding_);
                } else {
                    return Err(schema::SchemaError::Malformed {
                        path: ctx.fragment.join("/"),
                        detail: "contentEncoding MUST be one of [\"base64\"]".to_string(),
                    });
                }
            }
        }

        Ok(Some(Box::new(validators::ContentMedia { type_, encoding })))
    }
}
