use serde::Serialize;
use valico::common::error::ValicoError;

use crate::validation_state::ValidationState;

type BoxedValicoError = Box<dyn ValicoError>;

#[derive(Serialize, Debug)]
pub struct ParseErrorLocation {
    pub index: usize,
    pub line: usize,
    pub column: usize,
}

impl From<serde_yaml::Location> for ParseErrorLocation {
    fn from(location: serde_yaml::Location) -> Self {
        ParseErrorLocation {
            index: location.index(),
            line: location.line(),
            column: location.column(),
        }
    }
}

macro_rules! validation_errors {
    ($( $name:ident $( { $($fields:tt)* } )? ),*) => {
        #[derive(Serialize, Debug)]
        #[serde(untagged)]
        #[allow(dead_code)] // JS doesn't instantiate some of the validation errors at present
        pub enum ValidationError {
            $(
                $name {
                    code: String,
                    detail: Option<String>,
                    path: String,
                    title: String,
                    $( $($fields)* )?
                },
            )*
        }
    };
}

validation_errors!(
    // Schema Validation Errors
    WrongType,
    MultipleOf,
    Maximum,
    Minimum,
    MaxLength,
    MinLength,
    Pattern,
    MaxItems,
    MinItems,
    UniqueItems,
    Items,
    MaxProperties,
    MinProperties,
    Required,
    Properties,
    Enum,
    AnyOf { states: Vec<ValidationState> },
    OneOf { states: Vec<ValidationState> },
    Const,
    Contains,
    ContainsMinMax,
    Not,
    DivergentDefaults,
    Format,
    Unevaluated,
    Unknown,
    // Other Validation Errors
    UnresolvedJob,
    InvalidGlob,
    NoFilesMatchingGlob,
    // Other Errors
    Parse { location: Option<ParseErrorLocation> }
);

macro_rules! impl_from_valico_error {
    ($($err:ident => $name:ident $( { $($fields:tt)* } )? ),*) => {
        impl From<&BoxedValicoError> for ValidationError {
            fn from(err: &BoxedValicoError) -> Self {
                if false {
                    unreachable!()
                }
                $(
                    else if let Some($err) = err.downcast_ref::<valico::json_schema::errors::$name>() {
                        ValidationError::$name {
                            code: $err.get_code().into(),
                            path: $err.get_path().into(),
                            title: $err.get_title().into(),
                            detail: $err.get_detail().map(|s| s.into()),
                            $( $($fields)* )?
                        }
                    }
                )*
                else {
                    ValidationError::Unknown {
                        code: err.get_code().into(),
                        path: err.get_path().into(),
                        title: err.get_title().into(),
                        detail: err.get_detail().map(|s| s.into()),
                    }
                }
            }
        }
    };
}

impl_from_valico_error!(
    err => WrongType,
    err => MultipleOf,
    err => Maximum,
    err => Minimum,
    err => MaxLength,
    err => MinLength,
    err => Pattern,
    err => MaxItems,
    err => MinItems,
    err => UniqueItems,
    err => Items,
    err => MaxProperties,
    err => MinProperties,
    err => Required,
    err => Properties,
    err => Enum,
    err => AnyOf { states: err.states.iter().map(ValidationState::from).collect() },
    err => OneOf { states: err.states.iter().map(ValidationState::from).collect() },
    err => Const,
    err => Contains,
    err => ContainsMinMax,
    err => Not,
    err => DivergentDefaults,
    err => Format,
    err => Unevaluated
);

impl From<serde_yaml::Error> for ValidationError {
    fn from(err: serde_yaml::Error) -> Self {
        ValidationError::Parse {
            code: "parse_error".into(),
            detail: Some(err.to_string()),
            location: err.location().map(ParseErrorLocation::from),
            path: "".into(),
            title: "Parse Error".into(),
        }
    }
}
