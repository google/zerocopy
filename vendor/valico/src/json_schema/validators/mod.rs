use serde::{Serialize, Serializer};
use serde_json::{to_value, Value};
use std::borrow::Cow;
use std::collections::HashSet;
use std::fmt;

use super::scope;

#[macro_export]
macro_rules! strict_process {
    ($val:expr, $path:ident, $err:expr) => {{
        let maybe_val = $val;
        if maybe_val.is_none() {
            return val_error!($crate::json_schema::errors::WrongType {
                path: $path.to_string(),
                detail: $err.to_string()
            });
        }

        maybe_val.unwrap()
    }};
}

macro_rules! nonstrict_process {
    ($val:expr, $path:ident) => {{
        let maybe_val = $val;
        if maybe_val.is_none() {
            return $crate::json_schema::validators::ValidationState::new();
        }

        maybe_val.unwrap()
    }};
}

macro_rules! val_error {
    ($err:expr) => {
        $crate::json_schema::validators::ValidationState {
            errors: vec![Box::new($err)],
            missing: vec![],
            replacement: None,
            evaluated: Default::default(),
        }
    };
}

pub use self::conditional::Conditional;
pub use self::const_::Const;
pub use self::contains::Contains;
pub use self::content_media::ContentMedia;
pub use self::dependencies::Dependencies;
pub use self::enum_::Enum;
pub use self::items::Items;
pub use self::maxmin::{ExclusiveMaximum, ExclusiveMinimum, Maximum, Minimum};
pub use self::maxmin_items::{MaxItems, MinItems};
pub use self::maxmin_length::{MaxLength, MinLength};
pub use self::maxmin_properties::{MaxProperties, MinProperties};
pub use self::multiple_of::MultipleOf;
pub use self::not::Not;
pub use self::of::{AllOf, AnyOf, OneOf};
pub use self::pattern::Pattern;
pub use self::properties::Properties;
pub use self::property_names::PropertyNames;
pub use self::ref_::Ref;
pub use self::required::Required;
pub use self::type_::Type;
pub use self::unevaluated::Unevaluated;
pub use self::unique_items::UniqueItems;

mod conditional;
mod const_;
mod contains;
pub mod content_media;
pub mod dependencies;
mod enum_;
pub mod formats;
pub mod items;
mod maxmin;
mod maxmin_items;
mod maxmin_length;
mod maxmin_properties;
mod multiple_of;
mod not;
mod of;
mod pattern;
pub mod properties;
mod property_names;
mod ref_;
mod required;
pub mod type_;
pub mod unevaluated;
mod unique_items;

#[derive(Debug, Default)]
pub struct ValidationState {
    pub errors: super::super::common::error::ValicoErrors,
    pub missing: Vec<url::Url>,
    pub replacement: Option<Value>,
    /// Set of paths that have been evaluated so far. Once a path has been evaluated, it should be added
    /// here so that `unevaluatedItems` and `unevaluatedProperties` work.
    pub evaluated: HashSet<String>,
}

impl ValidationState {
    pub fn new() -> ValidationState {
        ValidationState {
            errors: vec![],
            missing: vec![],
            replacement: None,
            evaluated: Default::default(),
        }
    }

    pub fn is_valid(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn is_strictly_valid(&self) -> bool {
        self.errors.is_empty() && self.missing.is_empty()
    }

    pub fn append(&mut self, second: ValidationState) {
        self.errors.extend(second.errors);
        self.missing.extend(second.missing);
        self.evaluated.extend(second.evaluated);
    }

    pub fn set_replacement<T: Clone + Into<Value>>(&mut self, data: Cow<T>) {
        if !self.is_valid() {
            return;
        }
        if let Cow::Owned(data) = data {
            self.replacement = Some(data.into());
        }
    }
}

impl Serialize for ValidationState {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = ::serde_json::Map::new();
        map.insert(
            "errors".to_string(),
            Value::Array(
                self.errors
                    .iter()
                    .map(|err| to_value(err).unwrap())
                    .collect::<Vec<Value>>(),
            ),
        );
        map.insert(
            "missing".to_string(),
            Value::Array(
                self.missing
                    .iter()
                    .map(|url| to_value(url.to_string()).unwrap())
                    .collect::<Vec<Value>>(),
            ),
        );
        Value::Object(map).serialize(serializer)
    }
}

pub trait Validator {
    fn validate(
        &self,
        item: &Value,
        _: &str,
        _: &scope::Scope,
        prev_state: &ValidationState,
    ) -> ValidationState;
}

impl fmt::Debug for dyn Validator + 'static + Send + Sync {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.write_str("<validator>")
    }
}

pub type BoxedValidator = Box<dyn Validator + 'static + Send + Sync>;
pub type Validators = Vec<BoxedValidator>;

impl<T> Validator for T
where
    T: Fn(&Value, &str, &scope::Scope, &super::ValidationState) -> ValidationState,
{
    fn validate(
        &self,
        val: &Value,
        path: &str,
        scope: &scope::Scope,
        state: &super::ValidationState,
    ) -> ValidationState {
        self(val, path, scope, state)
    }
}
