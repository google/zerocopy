use serde_json::{to_string, to_value, Value};

use super::errors;

#[allow(dead_code)]
#[derive(Copy, Clone)]
pub enum PrimitiveType {
    String,
    I64,
    U64,
    F64,
    Boolean,
    Null,
    Array,
    Object,
    // Reserved for future use in Rustless
    File,
}

pub type CoercerResult<T> = Result<T, super::super::ValicoErrors>;

pub trait Coercer: Send + Sync {
    fn get_primitive_type(&self) -> PrimitiveType;
    fn coerce(&self, _: &mut Value, _: &str) -> CoercerResult<Option<Value>>;
}

#[derive(Copy, Clone)]
pub struct StringCoercer;

impl Coercer for StringCoercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::String
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_string() {
            Ok(None)
        } else if val.is_number() {
            Ok(Some(to_value(to_string(&val).unwrap()).unwrap()))
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce value to string".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct I64Coercer;

impl Coercer for I64Coercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::I64
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_i64() {
            Ok(None)
        } else if val.is_u64() {
            let val = val.as_u64().unwrap();
            Ok(Some(to_value(val as i64).unwrap()))
        } else if val.is_f64() {
            let val = val.as_f64().unwrap();
            Ok(Some(to_value(val as i64).unwrap()))
        } else if val.is_string() {
            let val = val.as_str().unwrap();
            let converted: Option<i64> = val.parse().ok();
            match converted {
                Some(num) => Ok(Some(to_value(num).unwrap())),
                None => Err(vec![Box::new(errors::WrongType {
                    path: path.to_string(),
                    detail: "Can't coerce string value to i64".to_string(),
                })]),
            }
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object value to i64".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct U64Coercer;

impl Coercer for U64Coercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::U64
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_u64() {
            Ok(None)
        } else if val.is_i64() {
            let val = val.as_i64().unwrap();
            Ok(Some(to_value(val as u64).unwrap()))
        } else if val.is_f64() {
            let val = val.as_f64().unwrap();
            Ok(Some(to_value(val as u64).unwrap()))
        } else if val.is_string() {
            let val = val.as_str().unwrap();
            let converted: Option<u64> = val.parse().ok();
            match converted {
                Some(num) => Ok(Some(to_value(num).unwrap())),
                None => Err(vec![Box::new(errors::WrongType {
                    path: path.to_string(),
                    detail: "Can't coerce string value to u64".to_string(),
                })]),
            }
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object value to u64".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct F64Coercer;

impl Coercer for F64Coercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::F64
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_f64() {
            Ok(None)
        } else if val.is_i64() {
            let val = val.as_i64().unwrap();
            Ok(Some(to_value(val as f64).unwrap()))
        } else if val.is_u64() {
            let val = val.as_u64().unwrap();
            Ok(Some(to_value(val as f64).unwrap()))
        } else if val.is_string() {
            let val = val.as_str().unwrap();
            let converted: Option<f64> = val.parse().ok();
            match converted {
                Some(num) => Ok(Some(to_value(num).unwrap())),
                None => Err(vec![Box::new(errors::WrongType {
                    path: path.to_string(),
                    detail: "Can't coerce string value to f64".to_string(),
                })]),
            }
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object value to f64".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct BooleanCoercer;

impl Coercer for BooleanCoercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::Boolean
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_boolean() {
            Ok(None)
        } else if val.is_string() {
            let val = val.as_str().unwrap();
            if val == "true" {
                Ok(Some(json!(true)))
            } else if val == "false" {
                Ok(Some(json!(false)))
            } else {
                Err(vec![
                    Box::new(errors::WrongType {
                        path: path.to_string(),
                        detail: "Can't coerce this string value to boolean. Correct values are 'true' and 'false'".to_string()
                    })
                ])
            }
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object to boolean".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct NullCoercer;

impl Coercer for NullCoercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::Null
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_null() {
            Ok(None)
        } else if val.is_string() {
            let val = val.as_str().unwrap();
            if val.is_empty() {
                Ok(Some(json!(null)))
            } else {
                Err(vec![Box::new(errors::WrongType {
                    path: path.to_string(),
                    detail:
                        "Can't coerce this string value to null. Correct value is only empty string"
                            .to_string(),
                })])
            }
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object to null".to_string(),
            })])
        }
    }
}

pub struct ArrayCoercer {
    sub_coercer: Option<Box<dyn Coercer + Send + Sync>>,
    separator: Option<String>,
}

impl ArrayCoercer {
    pub fn new() -> ArrayCoercer {
        ArrayCoercer {
            sub_coercer: None,
            separator: None,
        }
    }

    pub fn encoded(separator: String) -> ArrayCoercer {
        ArrayCoercer {
            separator: Some(separator),
            sub_coercer: None,
        }
    }

    pub fn encoded_of(
        separator: String,
        sub_coercer: Box<dyn Coercer + Send + Sync>,
    ) -> ArrayCoercer {
        ArrayCoercer {
            separator: Some(separator),
            sub_coercer: Some(sub_coercer),
        }
    }

    pub fn of_type(sub_coercer: Box<dyn Coercer + Send + Sync>) -> ArrayCoercer {
        ArrayCoercer {
            separator: None,
            sub_coercer: Some(sub_coercer),
        }
    }

    fn coerce_array(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        let array = val.as_array_mut().unwrap();
        if self.sub_coercer.is_some() {
            let sub_coercer = self.sub_coercer.as_ref().unwrap();
            let mut errors = vec![];
            for i in 0..array.len() {
                let item_path = [path, i.to_string().as_ref()].join("/");
                match sub_coercer.coerce(&mut array[i], item_path.as_ref()) {
                    Ok(Some(value)) => {
                        array.remove(i);
                        array.insert(i, value);
                    }
                    Ok(None) => (),
                    Err(err) => {
                        errors.extend(err);
                    }
                }
            }

            if errors.is_empty() {
                Ok(None)
            } else {
                Err(errors)
            }
        } else {
            Ok(None)
        }
    }
}

impl Coercer for ArrayCoercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::Array
    }

    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_array() {
            self.coerce_array(val, path)
        } else if val.is_string() && self.separator.is_some() {
            let separator = self.separator.as_ref().unwrap();
            let string = val.as_str().unwrap();
            let mut array = Value::Array(
                string
                    .split(&separator[..])
                    .map(|s| Value::String(s.to_string()))
                    .collect::<Vec<Value>>(),
            );
            self.coerce_array(&mut array, path)?;
            Ok(Some(array))
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce object to array".to_string(),
            })])
        }
    }
}

#[derive(Copy, Clone)]
pub struct ObjectCoercer;

impl Coercer for ObjectCoercer {
    fn get_primitive_type(&self) -> PrimitiveType {
        PrimitiveType::Object
    }
    fn coerce(&self, val: &mut Value, path: &str) -> CoercerResult<Option<Value>> {
        if val.is_object() {
            Ok(None)
        } else {
            Err(vec![Box::new(errors::WrongType {
                path: path.to_string(),
                detail: "Can't coerce non-object value to the object type".to_string(),
            })])
        }
    }
}
