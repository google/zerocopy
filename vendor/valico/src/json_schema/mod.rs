use std::fmt;
use std::str;

#[macro_use]
pub mod helpers;
#[macro_use]
pub mod keywords;
pub mod builder;
pub mod errors;
pub mod schema;
pub mod scope;
pub mod validators;

pub use self::builder::{schema, Builder};
pub use self::schema::{Schema, SchemaError};
pub use self::scope::Scope;
pub use self::validators::ValidationState;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Ord, PartialOrd)]
/// Represents the schema version to use.
pub enum SchemaVersion {
    /// Use draft 7.
    Draft7,
    /// Use draft 2019-09.
    Draft2019_09,
}

#[derive(Copy, Debug, Clone)]
pub enum PrimitiveType {
    Array,
    Boolean,
    Integer,
    Number,
    Null,
    Object,
    String,
}

impl str::FromStr for PrimitiveType {
    type Err = ();
    fn from_str(s: &str) -> Result<PrimitiveType, ()> {
        match s {
            "array" => Ok(PrimitiveType::Array),
            "boolean" => Ok(PrimitiveType::Boolean),
            "integer" => Ok(PrimitiveType::Integer),
            "number" => Ok(PrimitiveType::Number),
            "null" => Ok(PrimitiveType::Null),
            "object" => Ok(PrimitiveType::Object),
            "string" => Ok(PrimitiveType::String),
            _ => Err(()),
        }
    }
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.write_str(match self {
            PrimitiveType::Array => "array",
            PrimitiveType::Boolean => "boolean",
            PrimitiveType::Integer => "integer",
            PrimitiveType::Number => "number",
            PrimitiveType::Null => "null",
            PrimitiveType::Object => "object",
            PrimitiveType::String => "string",
        })
    }
}
