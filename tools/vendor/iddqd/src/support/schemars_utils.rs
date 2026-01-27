//! Utilities for schemars support.

use alloc::{
    boxed::Box,
    string::{String, ToString},
};
use schemars::schema::{
    ArrayValidation, InstanceType, Metadata, ObjectValidation, Schema,
    SchemaObject, SingleOrVec,
};

/// The crate name for iddqd, used in the x-rust-type extensions.
pub(crate) static IDDQD_CRATE_NAME: &str = "iddqd";

/// The crate version for iddqd, used in the x-rust-type extensions.
///
/// We use * here because we assume map types are going to stay the same
/// across breaking changes.
pub(crate) static IDDQD_CRATE_VERSION: &str = "*";

/// Helper function to create array validation for map types.
/// All iddqd map types serialize as arrays of their values.
pub(crate) fn array_validation<T>(
    generator: &mut schemars::gen::SchemaGenerator,
) -> Box<schemars::schema::ArrayValidation>
where
    T: schemars::JsonSchema,
{
    Box::new(ArrayValidation {
        items: Some(SingleOrVec::Single(Box::new(
            generator.subschema_for::<T>(),
        ))),
        // Setting unique_items to true here requires a bit of reasoning. For
        // two items T1 and T2:
        //
        // * If T1 == T2 (schema validation fails), then for all keys Key,
        //   T1::Key == T2::Key (would be rejected by the map). The map's
        //   behavior is consistent with the schema.
        //
        // * If T1 != T2 (schema validation succeeds), then there are two
        //   cases:
        //   1. For all keys Key, T1::Key != T2::Key. In this case, the map
        //      accepts the key. The map's behavior is consistent with the
        //      schema.
        //   2. There is at least one key for which T1::Key == T2::Key. In
        //      this case, the map will reject the key.
        //
        // Overall, the map's validation is strictly stronger than the schema.
        // This is normal in cases where JSON Schema cannot represent a
        // particular kind of validation.
        unique_items: Some(true),
        ..Default::default()
    })
}

/// Helper function to create the `extension` table for a given path and
/// type parameter.
pub(crate) fn make_extension_table<T>(
    path: &'static str,
    generator: &mut schemars::gen::SchemaGenerator,
) -> schemars::Map<String, serde_json::Value>
where
    T: schemars::JsonSchema,
{
    [(
        "x-rust-type".to_string(),
        serde_json::json!({
            "crate": IDDQD_CRATE_NAME,
            "version": IDDQD_CRATE_VERSION,
            "path": path,
            "parameters": [generator.subschema_for::<T>()]
        }),
    )]
    .into_iter()
    .collect()
}

/// Creates a schema object with common properties for iddqd map types.
pub(crate) fn create_map_schema<T>(
    title: &str,
    rust_type_path: &'static str,
    generator: &mut schemars::gen::SchemaGenerator,
) -> schemars::schema::Schema
where
    T: schemars::JsonSchema,
{
    Schema::Object(SchemaObject {
        instance_type: Some(InstanceType::Array.into()),
        array: Some(array_validation::<T>(generator)),
        metadata: Some(Box::new(Metadata {
            title: Some(title.to_string()),
            ..Default::default()
        })),
        extensions: make_extension_table::<T>(rust_type_path, generator),
        ..Default::default()
    })
}

/// Helper function to create object validation for map types serialized as objects.
pub(crate) fn object_validation<V>(
    generator: &mut schemars::gen::SchemaGenerator,
) -> Box<schemars::schema::ObjectValidation>
where
    V: schemars::JsonSchema,
{
    Box::new(ObjectValidation {
        additional_properties: Some(Box::new(generator.subschema_for::<V>())),
        ..Default::default()
    })
}

/// Creates a schema object for iddqd map types serialized as JSON objects.
/// This is used by the AsMap wrapper types.
pub(crate) fn create_object_schema<V>(
    title: &str,
    rust_type_path: &'static str,
    generator: &mut schemars::gen::SchemaGenerator,
) -> schemars::schema::Schema
where
    V: schemars::JsonSchema,
{
    Schema::Object(SchemaObject {
        instance_type: Some(InstanceType::Object.into()),
        object: Some(object_validation::<V>(generator)),
        metadata: Some(Box::new(Metadata {
            title: Some(title.to_string()),
            ..Default::default()
        })),
        extensions: make_extension_table::<V>(rust_type_path, generator),
        ..Default::default()
    })
}
