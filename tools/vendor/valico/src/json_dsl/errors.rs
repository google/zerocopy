use super::super::common::error::ValicoError;
use serde::{Serialize, Serializer};
use serde_json::{to_value, Value};

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct Required {
    pub path: String,
}
impl_err!(Required, "required", "This field is required");
impl_serialize!(Required);

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
pub struct WrongValue {
    pub path: String,
    pub detail: Option<String>,
}
impl_err!(WrongValue, "wrong_value", "The value is wrong or mailformed", +opt_detail);
impl_serialize!(WrongValue);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct MutuallyExclusive {
    pub path: String,
    pub detail: Option<String>,
    pub params: Vec<String>,
}
impl_err!(MutuallyExclusive, "mutually_exclusive", "The values are mutually exclusive", +opt_detail);
impl_serialize!(MutuallyExclusive, |err: &MutuallyExclusive,
                                    map: &mut ::serde_json::Map<
    String,
    Value,
>| {
    map.insert("params".to_string(), to_value(&err.params).unwrap());
});

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct ExactlyOne {
    pub path: String,
    pub detail: Option<String>,
    pub params: Vec<String>,
}
impl_err!(ExactlyOne, "exactly_one", "Exacly one of the values must be present", +opt_detail);
impl_serialize!(
    ExactlyOne,
    |err: &ExactlyOne, map: &mut ::serde_json::Map<String, Value>| map
        .insert("params".to_string(), to_value(&err.params).unwrap())
);

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct AtLeastOne {
    pub path: String,
    pub detail: Option<String>,
    pub params: Vec<String>,
}
impl_err!(AtLeastOne, "at_least_one", "At least one of the values must be present", +opt_detail);
impl_serialize!(
    AtLeastOne,
    |err: &AtLeastOne, map: &mut ::serde_json::Map<String, Value>| map
        .insert("params".to_string(), to_value(&err.params).unwrap())
);
