use serde_json::Value;
use std::fmt;

use crate::common::error;

pub use self::allowed_values::AllowedValues;
pub use self::at_least_one_of::AtLeastOneOf;
pub use self::exactly_one_of::ExactlyOneOf;
pub use self::mutually_exclusive::MutuallyExclusive;
pub use self::rejected_values::RejectedValues;

macro_rules! strict_process {
    ($val:expr, $path:ident, $err:expr) => {{
        let maybe_val = $val;
        if maybe_val.is_none() {
            return Err(vec![Box::new($crate::json_dsl::errors::WrongType {
                path: $path.to_string(),
                detail: $err.to_string(),
            })]);
        }

        maybe_val.unwrap()
    }};
}

mod allowed_values;
mod at_least_one_of;
mod exactly_one_of;
mod mutually_exclusive;
mod regex;
mod rejected_values;

pub type ValidatorResult = Result<(), error::ValicoErrors>;

pub trait Validator {
    fn validate(&self, item: &Value, _: &str) -> ValidatorResult;
}

impl fmt::Debug for dyn Validator + 'static {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.write_str("[validator]")
    }
}

pub type BoxedValidator = Box<dyn Validator + 'static + Send + Sync>;
pub type Validators = Vec<BoxedValidator>;

impl<T> Validator for T
where
    T: Fn(&Value, &str) -> ValidatorResult,
{
    fn validate(&self, val: &Value, path: &str) -> ValidatorResult {
        self(val, path)
    }
}
