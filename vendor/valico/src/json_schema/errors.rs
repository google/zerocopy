use super::super::common::error::ValicoError;
use serde::{Serialize, Serializer};
use serde_json::{to_value, Value};

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct WrongType {
    pub path: String,
    pub detail: String,
}
impl_err!(WrongType, "wrong_type", "Type of the value is wrong", +detail);
impl_serialize!(WrongType);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MultipleOf {
    pub path: String,
}
impl_err!(MultipleOf, "multiple_of", "Wrong number of the value");
impl_serialize!(MultipleOf);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Maximum {
    pub path: String,
}
impl_err!(Maximum, "maximum", "Maximum condition is not met");
impl_serialize!(Maximum);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Minimum {
    pub path: String,
}
impl_err!(Minimum, "minimum", "Minimum condition is not met");
impl_serialize!(Minimum);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MaxLength {
    pub path: String,
}
impl_err!(MaxLength, "max_length", "MaxLength condition is not met");
impl_serialize!(MaxLength);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MinLength {
    pub path: String,
}
impl_err!(MinLength, "min_length", "MinLength condition is not met");
impl_serialize!(MinLength);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Pattern {
    pub path: String,
}
impl_err!(Pattern, "pattern", "Pattern condition is not met");
impl_serialize!(Pattern);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MaxItems {
    pub path: String,
}
impl_err!(MaxItems, "max_items", "MaxItems condition is not met");
impl_serialize!(MaxItems);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MinItems {
    pub path: String,
}
impl_err!(MinItems, "min_items", "MinItems condition is not met");
impl_serialize!(MinItems);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct UniqueItems {
    pub path: String,
}
impl_err!(
    UniqueItems,
    "unique_items",
    "UniqueItems condition is not met"
);
impl_serialize!(UniqueItems);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Items {
    pub path: String,
    pub detail: String,
}
impl_err!(Items, "items", "Items condition is not met", +detail);
impl_serialize!(Items);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MaxProperties {
    pub path: String,
}
impl_err!(
    MaxProperties,
    "max_properties",
    "MaxProperties condition is not met"
);
impl_serialize!(MaxProperties);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MinProperties {
    pub path: String,
}
impl_err!(
    MinProperties,
    "min_properties",
    "MinProperties condition is not met"
);
impl_serialize!(MinProperties);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Required {
    pub path: String,
}
impl_err!(Required, "required", "This property is required");
impl_serialize!(Required);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Properties {
    pub path: String,
    pub detail: String,
}
impl_err!(Properties, "properties", "Property conditions are not met", +detail);
impl_serialize!(Properties);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Enum {
    pub path: String,
}
impl_err!(Enum, "enum", "Enum conditions are not met");
impl_serialize!(Enum);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct AnyOf {
    pub path: String,
    pub states: Vec<super::validators::ValidationState>,
}
impl_err!(AnyOf, "any_of", "AnyOf conditions are not met");
impl_serialize!(
    AnyOf,
    |err: &AnyOf, map: &mut ::serde_json::Map<String, Value>| map
        .insert("states".to_string(), to_value(&err.states).unwrap())
);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct OneOf {
    pub path: String,
    pub states: Vec<super::validators::ValidationState>,
}
impl_err!(OneOf, "one_of", "OneOf conditions are not met");
impl_serialize!(
    OneOf,
    |err: &OneOf, map: &mut ::serde_json::Map<String, Value>| map
        .insert("states".to_string(), to_value(&err.states).unwrap())
);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Const {
    pub path: String,
}
impl_err!(Const, "const", "Const condition is not met");
impl_serialize!(Const);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Contains {
    pub path: String,
}
impl_err!(Contains, "contains", "Contains condition is not met");
impl_serialize!(Contains);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct ContainsMinMax {
    pub path: String,
}
impl_err!(
    ContainsMinMax,
    "min_contains/max_contains",
    "Contains minimum/maximum is not met"
);
impl_serialize!(ContainsMinMax);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Not {
    pub path: String,
}
impl_err!(Not, "not", "Not condition is not met");
impl_serialize!(Not);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct DivergentDefaults {
    pub path: String,
}
impl_err!(
    DivergentDefaults,
    "default",
    "Application of defaults did not converge"
);
impl_serialize!(DivergentDefaults);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Format {
    pub path: String,
    pub detail: String,
}
impl_err!(Format, "format", "Format is wrong", +detail);
impl_serialize!(Format);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Unevaluated {
    pub path: String,
    pub detail: String,
}
impl_err!(Unevaluated, "unevaluated", "Unevaluated condition is not met", +detail);
impl_serialize!(Unevaluated);
