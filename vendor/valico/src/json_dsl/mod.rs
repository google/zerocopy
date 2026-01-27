mod builder;
mod coercers;
pub mod errors;
mod param;
#[macro_use]
pub mod validators;

use super::json_schema;

pub use self::builder::Builder;
pub use self::coercers::{
    ArrayCoercer, BooleanCoercer, Coercer, F64Coercer, I64Coercer, NullCoercer, ObjectCoercer,
    PrimitiveType, StringCoercer, U64Coercer,
};
pub use self::param::Param;

pub fn i64() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::I64Coercer)
}
pub fn u64() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::U64Coercer)
}
pub fn f64() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::F64Coercer)
}
pub fn string() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::StringCoercer)
}
pub fn boolean() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::BooleanCoercer)
}
pub fn null() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::NullCoercer)
}
pub fn array() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::ArrayCoercer::new())
}
pub fn array_of(
    coercer: Box<dyn coercers::Coercer + Send + Sync>,
) -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::ArrayCoercer::of_type(coercer))
}

pub fn encoded_array(separator: &str) -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::ArrayCoercer::encoded(separator.to_string()))
}

pub fn encoded_array_of(
    separator: &str,
    coercer: Box<dyn coercers::Coercer + Send + Sync>,
) -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::ArrayCoercer::encoded_of(
        separator.to_string(),
        coercer,
    ))
}

pub fn object() -> Box<dyn coercers::Coercer + Send + Sync> {
    Box::new(coercers::ObjectCoercer)
}

pub struct ExtendedResult<T> {
    value: T,
    state: json_schema::ValidationState,
}

impl<T> ExtendedResult<T> {
    pub fn new(value: T) -> ExtendedResult<T> {
        ExtendedResult {
            value,
            state: json_schema::ValidationState::new(),
        }
    }

    pub fn with_errors(value: T, errors: super::ValicoErrors) -> ExtendedResult<T> {
        ExtendedResult {
            value,
            state: json_schema::ValidationState {
                errors,
                missing: vec![],
                replacement: None,
                evaluated: Default::default(),
            },
        }
    }

    pub fn is_valid(&self) -> bool {
        self.state.is_valid()
    }

    pub fn append(&mut self, second: json_schema::ValidationState) {
        self.state.append(second);
    }
}
