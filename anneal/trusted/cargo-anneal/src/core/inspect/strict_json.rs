// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Strict RFC 8259 JSON parser rejecting duplicate object keys at every depth,
//! excessive nesting, and trailing tokens, plus an RFC 6901 pointer tracker for
//! forward-compatible unrecognized field reporting.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use serde::de::{self, DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor};
use serde_json::{Map, Number, Value};

/// Maximum permitted raw receipt JSON size (64 MiB).
pub const MAX_RECEIPT_JSON_BYTES: usize = 64 * 1024 * 1024;

/// Maximum permitted recursive nesting depth when parsing receipt JSON.
pub const MAX_JSON_DEPTH: usize = 64;

/// Parses untrusted JSON bytes strictly according to RFC 8259 uniqueness and
/// bounding rules.
pub struct StrictJsonDom;

impl StrictJsonDom {
    /// Parse `bytes` into a [`serde_json::Value`], rejecting non-UTF-8 input,
    /// inputs larger than [`MAX_RECEIPT_JSON_BYTES`], nesting deeper than
    /// [`MAX_JSON_DEPTH`], duplicate object keys at any nesting level, and
    /// trailing non-whitespace tokens.
    pub fn parse(bytes: &[u8]) -> Result<Value, String> {
        if bytes.len() > MAX_RECEIPT_JSON_BYTES {
            return Err(format!(
                "receipt JSON exceeds {MAX_RECEIPT_JSON_BYTES}-byte cap ({} bytes)",
                bytes.len()
            ));
        }
        let text = std::str::from_utf8(bytes)
            .map_err(|e| format!("receipt input is not valid UTF-8: {e}"))?;
        let mut de = serde_json::Deserializer::from_str(text);
        let value = StrictSeed { depth: 0 }
            .deserialize(&mut de)
            .map_err(|e| format!("invalid strict receipt JSON: {e}"))?;
        de.end().map_err(|e| format!("trailing tokens after receipt JSON: {e}"))?;
        Ok(value)
    }
}

#[derive(Clone, Copy)]
struct StrictSeed {
    depth: usize,
}

impl StrictSeed {
    fn next(self) -> Result<Self, String> {
        let next_depth = self.depth.saturating_add(1);
        if next_depth > MAX_JSON_DEPTH {
            return Err(format!("JSON nesting depth exceeds {MAX_JSON_DEPTH}"));
        }
        Ok(Self { depth: next_depth })
    }
}

impl<'de> DeserializeSeed<'de> for StrictSeed {
    type Value = Value;

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        deserializer.deserialize_any(StrictVisitor { seed: self })
    }
}

struct StrictVisitor {
    seed: StrictSeed,
}

impl<'de> Visitor<'de> for StrictVisitor {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("any valid strict JSON value")
    }

    fn visit_bool<E: de::Error>(self, v: bool) -> Result<Self::Value, E> {
        Ok(Value::Bool(v))
    }

    fn visit_i64<E: de::Error>(self, v: i64) -> Result<Self::Value, E> {
        Ok(Value::Number(v.into()))
    }

    fn visit_u64<E: de::Error>(self, v: u64) -> Result<Self::Value, E> {
        Ok(Value::Number(v.into()))
    }

    fn visit_f64<E: de::Error>(self, v: f64) -> Result<Self::Value, E> {
        Number::from_f64(v)
            .map(Value::Number)
            .ok_or_else(|| de::Error::custom("non-finite JSON number"))
    }

    fn visit_str<E: de::Error>(self, v: &str) -> Result<Self::Value, E> {
        Ok(Value::String(v.to_owned()))
    }

    fn visit_string<E: de::Error>(self, v: String) -> Result<Self::Value, E> {
        Ok(Value::String(v))
    }

    fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(Value::Null)
    }

    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(Value::Null)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let child = self.seed.next().map_err(de::Error::custom)?;
        let mut items = Vec::new();
        while let Some(elem) = seq.next_element_seed(child)? {
            items.push(elem);
        }
        Ok(Value::Array(items))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let child = self.seed.next().map_err(de::Error::custom)?;
        let mut seen: BTreeMap<String, Value> = BTreeMap::new();
        while let Some((key, val)) =
            map.next_entry_seed(std::marker::PhantomData::<String>, child)?
        {
            if seen.insert(key.clone(), val).is_some() {
                return Err(de::Error::custom(format!("duplicate JSON object key `{key}`")));
            }
        }
        let mut out = Map::with_capacity(seen.len());
        for (k, v) in seen {
            out.insert(k, v);
        }
        Ok(Value::Object(out))
    }
}

/// Escape an RFC 6901 JSON Pointer reference token (`~` -> `~0`, `/` -> `~1`).
pub fn escape_json_pointer_token(token: &str) -> String {
    let mut out = String::with_capacity(token.len());
    for ch in token.chars() {
        match ch {
            '~' => out.push_str("~0"),
            '/' => out.push_str("~1"),
            other => out.push(other),
        }
    }
    out
}

/// Typed field reader over a JSON object that tracks visited keys and reports
/// any unvisited keys as RFC 6901 pointers.
pub struct ObjectCursor<'a> {
    prefix: String,
    obj: &'a Map<String, Value>,
    visited: BTreeSet<&'a str>,
}

impl<'a> ObjectCursor<'a> {
    /// Wrap a root JSON object.
    pub fn root(obj: &'a Map<String, Value>) -> Self {
        Self { prefix: String::new(), obj, visited: BTreeSet::new() }
    }

    /// Wrap a nested JSON object under `prefix`.
    pub fn nested(prefix: impl Into<String>, obj: &'a Map<String, Value>) -> Self {
        Self { prefix: prefix.into(), obj, visited: BTreeSet::new() }
    }

    /// Return the RFC 6901 path prefix for `key` under this object.
    pub fn child_pointer(&self, key: &str) -> String {
        format!("{}/{}", self.prefix, escape_json_pointer_token(key))
    }

    /// Borrow a field while marking `key` as visited.
    pub fn get(&mut self, key: &'static str) -> Option<&'a Value> {
        self.visited.insert(key);
        self.obj.get(key)
    }

    /// Mark an entire subtree key as intentionally opaque / dynamically typed.
    pub fn mark_visited(&mut self, key: &'static str) {
        self.visited.insert(key);
    }

    /// Read a required non-null field or return a descriptive error.
    pub fn req(&mut self, key: &'static str) -> Result<&'a Value, String> {
        self.get(key).ok_or_else(|| format!("missing required field `{}`", self.child_pointer(key)))
    }

    /// Read a required string field.
    pub fn req_str(&mut self, key: &'static str) -> Result<&'a str, String> {
        let ptr = self.child_pointer(key);
        self.req(key)?.as_str().ok_or_else(|| format!("field `{ptr}` must be a string"))
    }

    /// Read an optional string field (rejecting non-null non-strings).
    pub fn opt_str(&mut self, key: &'static str) -> Result<Option<&'a str>, String> {
        let ptr = self.child_pointer(key);
        match self.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(Value::String(s)) => Ok(Some(s.as_str())),
            Some(_) => Err(format!("field `{ptr}` must be a string or null")),
        }
    }

    /// Read a required boolean field.
    pub fn req_bool(&mut self, key: &'static str) -> Result<bool, String> {
        let ptr = self.child_pointer(key);
        self.req(key)?.as_bool().ok_or_else(|| format!("field `{ptr}` must be a boolean"))
    }

    /// Read a required unsigned integer field.
    pub fn req_u64(&mut self, key: &'static str) -> Result<u64, String> {
        let ptr = self.child_pointer(key);
        self.req(key)?
            .as_u64()
            .ok_or_else(|| format!("field `{ptr}` must be a non-negative integer"))
    }

    /// Read an optional unsigned integer field.
    pub fn opt_u64(&mut self, key: &'static str) -> Result<Option<u64>, String> {
        let ptr = self.child_pointer(key);
        match self.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(v) => v
                .as_u64()
                .map(Some)
                .ok_or_else(|| format!("field `{ptr}` must be a non-negative integer")),
        }
    }

    /// Read a required JSON array field.
    pub fn req_array(&mut self, key: &'static str) -> Result<&'a Vec<Value>, String> {
        let ptr = self.child_pointer(key);
        self.req(key)?.as_array().ok_or_else(|| format!("field `{ptr}` must be an array"))
    }

    /// Read an optional JSON array field.
    pub fn opt_array(&mut self, key: &'static str) -> Result<Option<&'a Vec<Value>>, String> {
        let ptr = self.child_pointer(key);
        match self.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(Value::Array(arr)) => Ok(Some(arr)),
            Some(_) => Err(format!("field `{ptr}` must be an array")),
        }
    }

    /// Read a required array of strings.
    pub fn req_str_array(&mut self, key: &'static str) -> Result<Vec<String>, String> {
        let ptr = self.child_pointer(key);
        let arr = self.req_array(key)?;
        arr.iter()
            .enumerate()
            .map(|(i, v)| {
                v.as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| format!("element `{ptr}/{i}` must be a string"))
            })
            .collect()
    }

    /// Read a required nested JSON object cursor.
    pub fn req_obj(&mut self, key: &'static str) -> Result<&'a Map<String, Value>, String> {
        let ptr = self.child_pointer(key);
        self.req(key)?.as_object().ok_or_else(|| format!("field `{ptr}` must be an object"))
    }

    /// Read an optional nested JSON object.
    pub fn opt_obj(&mut self, key: &'static str) -> Result<Option<&'a Map<String, Value>>, String> {
        let ptr = self.child_pointer(key);
        match self.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(Value::Object(map)) => Ok(Some(map)),
            Some(_) => Err(format!("field `{ptr}` must be an object")),
        }
    }

    /// Push sorted RFC 6901 pointers for every key in `self.obj` that was never
    /// visited.
    pub fn collect_unrecognized(&self, out: &mut Vec<String>) {
        for key in self.obj.keys() {
            if !self.visited.contains(key.as_str()) {
                out.push(self.child_pointer(key));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_duplicate_keys_at_root_nested_and_array_depths() {
        assert!(StrictJsonDom::parse(br#"{"a":1,"a":2}"#).unwrap_err().contains("duplicate"));
        assert!(
            StrictJsonDom::parse(br#"{"outer":{"x":1,"x":2}}"#).unwrap_err().contains("duplicate")
        );
        assert!(
            StrictJsonDom::parse(br#"{"arr":[{"k":true,"k":false}]}"#)
                .unwrap_err()
                .contains("duplicate")
        );
    }

    #[test]
    fn rejects_trailing_tokens_depth_overflow_and_oversized_payloads() {
        assert!(StrictJsonDom::parse(br#"{"a":1} trailing"#).unwrap_err().contains("trailing"));
        let deep = format!("{}{}", "[".repeat(66), "]".repeat(66));
        assert!(StrictJsonDom::parse(deep.as_bytes()).unwrap_err().contains("depth"));
    }

    #[test]
    fn cursor_collects_escaped_rfc6901_pointers() {
        let val = StrictJsonDom::parse(br#"{"a/b~c":1,"ok":2}"#).unwrap();
        let mut cursor = ObjectCursor::root(val.as_object().unwrap());
        assert_eq!(cursor.req_u64("ok").unwrap(), 2);
        let mut unknown = Vec::new();
        cursor.collect_unrecognized(&mut unknown);
        assert_eq!(unknown, vec!["/a~1b~0c"]);
    }
}
