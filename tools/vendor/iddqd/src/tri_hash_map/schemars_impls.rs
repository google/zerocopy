//! Schemars implementations for TriHashMap.

use crate::{
    support::{
        alloc::Allocator,
        schemars_utils::{create_map_schema, create_object_schema},
    },
    tri_hash_map::{
        imp::TriHashMap, serde_impls::TriHashMapAsMap, trait_defs::TriHashItem,
    },
};
use alloc::string::String;
use schemars::{JsonSchema, gen::SchemaGenerator, schema::Schema};

impl<T, S, A> JsonSchema for TriHashMap<T, S, A>
where
    T: JsonSchema + TriHashItem,
    A: Allocator,
{
    fn schema_name() -> String {
        alloc::format!("TriHashMap_of_{}", T::schema_name())
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        create_map_schema::<T>("TriHashMap", "iddqd::TriHashMap", generator)
    }

    fn is_referenceable() -> bool {
        false
    }
}

impl<T, S, A> JsonSchema for TriHashMapAsMap<T, S, A>
where
    T: JsonSchema + TriHashItem,
    A: Allocator,
{
    fn schema_name() -> String {
        alloc::format!("TriHashMapAsMap_of_{}", T::schema_name())
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        create_object_schema::<T>(
            "TriHashMapAsMap",
            "iddqd::TriHashMap",
            generator,
        )
    }

    fn is_referenceable() -> bool {
        false
    }
}
