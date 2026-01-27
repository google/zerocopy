use crate::parser::{parse, ParseError};
use serde_json::Value;
use std::fmt::{Display, Formatter};
use std::fmt::Result as FmtResult;
use std::fmt::Write;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::str::FromStr;

/// A JSON Pointer.
///
/// Create a new JSON pointer with [`JsonPointer::new`](#method.new), or parse one from a
/// string with [`str::parse()`](https://doc.rust-lang.org/std/primitive.str.html#method.parse).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsonPointer<S: AsRef<str>, C: AsRef<[S]>> {
    ref_toks: C,
    _phantom: PhantomData<S>,
}

impl<S: AsRef<str>, C: AsRef<[S]>> JsonPointer<S, C> {
    /// Creates a new JsonPointer from the given reference tokens.
    pub fn new(ref_toks: C) -> JsonPointer<S, C> {
        JsonPointer {
            ref_toks: ref_toks,
            _phantom: PhantomData,
        }
    }

    /// Attempts to get a reference to a value from the given JSON value,
    /// returning an error if it can't be found.
    pub fn get<'json>(&self, val: &'json Value) -> Result<&'json Value, IndexError> {
        self.ref_toks.as_ref().iter().fold(Ok(val), |val, tok| val.and_then(|val| {
            let tok = tok.as_ref();
            match *val {
                Value::Object(ref obj) => obj.get(tok).ok_or_else(|| IndexError::NoSuchKey(tok.to_owned())),
                Value::Array(ref arr) => {
                    let idx = if tok == "-" {
                        arr.len()
                    } else if let Ok(idx) = tok.parse() {
                        idx
                    } else {
                        return Err(IndexError::NoSuchKey(tok.to_owned()));
                    };
                    arr.get(idx).ok_or(IndexError::OutOfBounds(idx))
                },
                _ => Err(IndexError::NotIndexable),
            }
        }))
    }

    /// Attempts to get a mutable reference to a value from the given JSON
    /// value, returning an error if it can't be found.
    pub fn get_mut<'json>(&self, val: &'json mut Value) -> Result<&'json mut Value, IndexError> {
        self.ref_toks.as_ref().iter().fold(Ok(val), |val, tok| val.and_then(|val| {
            let tok = tok.as_ref();
            match *val {
                Value::Object(ref mut obj) => obj.get_mut(tok).ok_or_else(|| IndexError::NoSuchKey(tok.to_owned())),
                Value::Array(ref mut arr) => {
                    let idx = if tok == "-" {
                        arr.len()
                    } else if let Ok(idx) = tok.parse() {
                        idx
                    } else {
                        return Err(IndexError::NoSuchKey(tok.to_owned()));
                    };
                    arr.get_mut(idx).ok_or(IndexError::OutOfBounds(idx))
                },
                _ => Err(IndexError::NotIndexable),
            }
        }))
    }

    /// Attempts to get an owned value from the given JSON value, returning an
    /// error if it can't be found.
    pub fn get_owned(&self, val: Value) -> Result<Value, IndexError> {
        self.ref_toks.as_ref().iter().fold(Ok(val), |val, tok| val.and_then(|val| {
            let tok = tok.as_ref();
            match val {
                Value::Object(mut obj) => obj.remove(tok).ok_or_else(|| IndexError::NoSuchKey(tok.to_owned())),
                Value::Array(mut arr) => {
                    let idx = if tok == "-" {
                        arr.len()
                    } else if let Ok(idx) = tok.parse() {
                        idx
                    } else {
                        return Err(IndexError::NoSuchKey(tok.to_owned()));
                    };
                    if idx >= arr.len() {
                        Err(IndexError::OutOfBounds(idx))
                    } else {
                        Ok(arr.swap_remove(idx))
                    }
                },
                _ => Err(IndexError::NotIndexable),
            }
        }))
    }

    /// Converts a JSON pointer to a string in URI Fragment Identifier
    /// Representation, including the leading `#`.
    pub fn uri_fragment(&self) -> String {
        fn legal_fragment_byte(b: u8) -> bool {
            match b {
                0x21 | 0x24 | 0x26..=0x3b | 0x3d | 0x3f..=0x5a | 0x5f | 0x61..=0x7a => true,
                _ => false,
            }
        }

        let mut s = "#".to_string();
        for part in self.ref_toks.as_ref().iter() {
            s += "/";
            for b in part.as_ref().bytes() {
                if legal_fragment_byte(b) {
                    s.push(b as char)
                } else {
                    write!(s, "%{:02x}", b).unwrap()
                }
            }
        }
        s
    }
}

impl<S: AsRef<str>> JsonPointer<S, Vec<S>> {
    /// Adds a component to the JSON pointer.
    pub fn push(&mut self, component: S) {
        self.ref_toks.push(component);
    }

    /// Removes and returns the last component from the JSON pointer.
    pub fn pop(&mut self) -> Option<S> {
        self.ref_toks.pop()
    }
}

impl<S: AsRef<str>, C: AsRef<[S]>> Display for JsonPointer<S, C> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        for part in self.ref_toks.as_ref().iter() {
            write!(fmt, "/")?;
            for ch in part.as_ref().chars() {
                match ch {
                    '~' => write!(fmt, "~0"),
                    '/' => write!(fmt, "~1"),
                    c => write!(fmt, "{}", c),
                }?
            }
        }
        Ok(())
    }
}

impl FromStr for JsonPointer<String, Vec<String>> {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse(s)
    }
}

/// An error that can be encountered when indexing using a JSON pointer.
#[derive(Clone, Debug, PartialEq)]
pub enum IndexError {
    /// The pointer pointed to a nonexistent key.
    NoSuchKey(String),
    /// The pointer resulted in trying to index a non-indexable type.
    NotIndexable,
    /// The pointer pointed to an out-of-bounds value in an array.
    OutOfBounds(usize),
}

impl<'a, S: AsRef<str>, C: AsRef<[S]>> Index<&'a JsonPointer<S, C>> for Value {
    type Output = Value;
    fn index(&self, ptr: &'a JsonPointer<S, C>) -> &Value {
        ptr.get(self).unwrap()
    }
}

impl<'a, S: AsRef<str>, C: AsRef<[S]>> IndexMut<&'a JsonPointer<S, C>> for Value {
    fn index_mut(&mut self, ptr: &'a JsonPointer<S, C>) -> &mut Value {
        ptr.get_mut(self).unwrap()
    }
}
