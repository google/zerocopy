#![crate_type = "rlib"]
#![deny(warnings)]
#![deny(bad_style)]

extern crate serde;
extern crate serde_json;

pub use object_builder::ObjectBuilder;
pub use array_builder::ArrayBuilder;
pub use serializer::{Serializer, ObjectSerializer, ObjectScopeSerializer};
pub use array_serializer::ArraySerializer;

pub mod array_builder;
pub mod object_builder;
pub mod serializer;
pub mod array_serializer;

/// ```rust
/// let json = jsonway::object(|json| {
///     json.set("first_name", "Luke");
///     json.set("last_name", "Skywalker");
///
///     json.object("info", |json| {
///         json.set("homeworld", "Tatooine");
///         json.set("born", "19 BBY");
///         json.set("died", "Between 45 ABY and 137 ABY");
///     });
///
///     json.array("masters", |json| {
///         json.push("Obi-Wan Kenobi");
///         json.push("Yoda");
///         json.push("Joruus C'baoth (Briefly)");
///         json.push("Darth Sidious (Briefly)");
///     });
/// }).unwrap();
///
/// assert_eq!(json.get("first_name").unwrap().as_str().unwrap(), "Luke");
/// assert_eq!(json.get("last_name").unwrap().as_str().unwrap(), "Skywalker");
///
/// assert!(json.get("info").unwrap().is_object());
/// assert!(json.get("masters").unwrap().is_array());
/// ```

/// Create and return new ListBuilder
pub fn array<F>(builder: F) -> ArrayBuilder where F: FnOnce(&mut ArrayBuilder) {
    ArrayBuilder::build(builder)
}

/// Create and return new ObjectBuilder
pub fn object<F>(builder: F) -> ObjectBuilder where F: FnOnce(&mut ObjectBuilder) {
    ObjectBuilder::build(builder)
}
