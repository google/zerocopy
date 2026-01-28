//! A crate for parsing and using JSON pointers, as specified in [RFC
//! 6901](https://tools.ietf.org/html/rfc6901). Unlike the `pointer` method
//! built into `serde_json`, this handles both validating JSON Pointers before
//! use and the URI Fragment Identifier Representation.
//!
//! [![Build Status](https://travis-ci.org/remexre/json-pointer.svg?branch=master)](https://travis-ci.org/remexre/json-pointer)
//! [![crates.io](https://img.shields.io/crates/v/json-pointer.svg)](https://crates.io/crates/json-pointer)
//! [![Documentation](https://docs.rs/json-pointer/badge.svg)](https://docs.rs/json-pointer)
//! 
//! ## Creating a JSON Pointer
//! 
//! JSON pointers can be created with a literal `[&str]`, or parsed from a `String`.
//! 
//! ```rust
//! extern crate json_pointer;
//!
//! use json_pointer::JsonPointer;
//!
//! fn main() {
//!     let from_strs = JsonPointer::new([
//!         "foo",
//!         "bar",
//!     ]);
//!     let parsed = "/foo/bar".parse::<JsonPointer<_, _>>().unwrap();
//! 
//!     assert_eq!(from_strs.to_string(), parsed.to_string());
//! }
//! ```
//! 
//! ## Using a JSON Pointer
//! 
//! The `JsonPointer` type provides `.get()` and `.get_mut()`, to get references
//! and mutable references to the appropriate value, respectively.
//! 
//! ```rust
//! extern crate json_pointer;
//! #[macro_use]
//! extern crate serde_json;
//!
//! use json_pointer::JsonPointer;
//!
//! fn main() {
//!     let ptr = "/foo/bar".parse::<JsonPointer<_, _>>().unwrap();
//! 
//!     let document = json!({
//!         "foo": {
//!             "bar": 0,
//!             "baz": 1,
//!         },
//!         "quux": "xyzzy"
//!     });
//! 
//!     let indexed = ptr.get(&document).unwrap();
//! 
//!     assert_eq!(indexed, &json!(0));
//! }
//! ```
//! 
//! ## URI Fragment Identifier Representation
//! 
//! JSON Pointers can be embedded in the fragment portion of a URI. This is the
//! reason why most JSON pointer libraries require a `#` character at the beginning
//! of a JSON pointer. The crate will detect the leading `#` as an indicator to
//! parse in URI Fragment Identifier Representation. Note that this means that this
//! crate does not support parsing full URIs.
//! 
//! ```rust
//! extern crate json_pointer;
//!
//! use json_pointer::JsonPointer;
//!
//! fn main() {
//!     let str_ptr = "/f%o".parse::<JsonPointer<_, _>>().unwrap();
//!     let uri_ptr = "#/f%25o".parse::<JsonPointer<_, _>>().unwrap();
//! 
//!     assert_eq!(str_ptr, uri_ptr);
//! }
//! ```

#![deny(missing_docs)]

mod parser;
mod ptr;

pub use parser::ParseError;
pub use ptr::IndexError;
pub use ptr::JsonPointer;
