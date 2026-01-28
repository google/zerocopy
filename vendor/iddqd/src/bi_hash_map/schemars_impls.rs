//! Schemars implementations for BiHashMap.

use crate::{
    bi_hash_map::{
        imp::BiHashMap, serde_impls::BiHashMapAsMap, trait_defs::BiHashItem,
    },
    support::{
        alloc::Allocator,
        schemars_utils::{create_map_schema, create_object_schema},
    },
};
use alloc::string::String;
use schemars::{JsonSchema, gen::SchemaGenerator, schema::Schema};

impl<T, S, A> JsonSchema for BiHashMap<T, S, A>
where
    T: JsonSchema + BiHashItem,
    A: Allocator,
{
    fn schema_name() -> String {
        alloc::format!("BiHashMap_of_{}", T::schema_name())
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        create_map_schema::<T>("BiHashMap", "iddqd::BiHashMap", generator)
    }

    fn is_referenceable() -> bool {
        false
    }
}

impl<T, S, A> JsonSchema for BiHashMapAsMap<T, S, A>
where
    T: JsonSchema + BiHashItem,
    A: Allocator,
{
    fn schema_name() -> String {
        alloc::format!("BiHashMapAsMap_of_{}", T::schema_name())
    }

    fn json_schema(generator: &mut SchemaGenerator) -> Schema {
        create_object_schema::<T>(
            "BiHashMapAsMap",
            "iddqd::BiHashMap",
            generator,
        )
    }

    fn is_referenceable() -> bool {
        false
    }
}
