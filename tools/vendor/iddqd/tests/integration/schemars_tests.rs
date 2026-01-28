use expectorate::assert_contents;
use iddqd::{
    BiHashItem, BiHashMap, IdHashItem, IdHashMap, TriHashItem, TriHashMap,
    bi_hash_map::BiHashMapAsMap, bi_upcast, id_hash_map::IdHashMapAsMap,
    id_upcast, tri_hash_map::TriHashMapAsMap, tri_upcast,
};
#[cfg(feature = "std")]
use iddqd::{IdOrdItem, IdOrdMap, id_ord_map::IdOrdMapAsMap};
use schemars::{JsonSchema, schema_for};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
struct TestUser {
    // This is in alphabetical order to ensure that the same fixture gets
    // generated with or without the `schemars/preserve_order` feature.
    age: u32,
    email: String,
    id: u32,
    name: String,
}

impl IdHashItem for TestUser {
    type Key<'a> = &'a str;

    fn key(&self) -> Self::Key<'_> {
        &self.name
    }

    id_upcast!();
}

impl BiHashItem for TestUser {
    type K1<'a> = &'a str;
    type K2<'a> = u32;

    fn key1(&self) -> Self::K1<'_> {
        &self.name
    }

    fn key2(&self) -> Self::K2<'_> {
        self.id
    }

    bi_upcast!();
}

impl TriHashItem for TestUser {
    type K1<'a> = &'a str;
    type K2<'a> = u32;
    type K3<'a> = &'a str;

    fn key1(&self) -> Self::K1<'_> {
        &self.name
    }

    fn key2(&self) -> Self::K2<'_> {
        self.id
    }

    fn key3(&self) -> Self::K3<'_> {
        &self.email
    }

    tri_upcast!();
}

#[cfg(feature = "std")]
impl IdOrdItem for TestUser {
    type Key<'a> = &'a str;

    fn key(&self) -> Self::Key<'_> {
        &self.name
    }

    id_upcast!();
}

#[test]
fn schema_fixtures() {
    let schema = schema_for!(IdHashMap<TestUser>);
    assert_contents(
        "tests/output/id_hash_map_schema.json",
        &to_string_pretty_ln(&schema),
    );

    let schema = schema_for!(IdHashMapAsMap<TestUser>);
    assert_contents(
        "tests/output/id_hash_map_as_map_schema.json",
        &to_string_pretty_ln(&schema),
    );

    #[cfg(feature = "std")]
    {
        let schema = schema_for!(IdOrdMap<TestUser>);
        assert_contents(
            "tests/output/id_ord_map_schema.json",
            &to_string_pretty_ln(&schema),
        );

        let schema = schema_for!(IdOrdMapAsMap<TestUser>);
        assert_contents(
            "tests/output/id_ord_map_as_map_schema.json",
            &to_string_pretty_ln(&schema),
        );
    }

    let schema = schema_for!(BiHashMap<TestUser>);
    assert_contents(
        "tests/output/bi_hash_map_schema.json",
        &to_string_pretty_ln(&schema),
    );

    let schema = schema_for!(BiHashMapAsMap<TestUser>);
    assert_contents(
        "tests/output/bi_hash_map_as_map_schema.json",
        &to_string_pretty_ln(&schema),
    );

    let schema = schema_for!(TriHashMap<TestUser>);
    assert_contents(
        "tests/output/tri_hash_map_schema.json",
        &to_string_pretty_ln(&schema),
    );

    let schema = schema_for!(TriHashMapAsMap<TestUser>);
    assert_contents(
        "tests/output/tri_hash_map_as_map_schema.json",
        &to_string_pretty_ln(&schema),
    );
}

#[cfg(feature = "std")]
#[test]
fn container_fixtures() {
    #[derive(JsonSchema)]
    #[expect(unused)]
    struct Container {
        // This is in alphabetical order to ensure that the same fixture gets
        // generated with or without the `schemars/preserve_order` feature.
        users_bi: BiHashMap<TestUser>,
        users_hash: IdHashMap<TestUser>,
        users_ord: IdOrdMap<TestUser>,
        users_tri: TriHashMap<TestUser>,
    }

    // Verify the container can generate a schema.
    let schema = schema_for!(Container);
    assert_contents(
        "tests/output/container_schema.json",
        &to_string_pretty_ln(&schema),
    );

    // A simple container with just IdHashMap<TestUser>. This fixture is
    // used by `typify-types.rs` to show end-to-end usage.
    #[derive(JsonSchema)]
    #[expect(unused)]
    struct SimpleContainer {
        users: IdHashMap<TestUser>,
    }

    let schema = schema_for!(SimpleContainer);
    assert_contents(
        "tests/output/simple_container_schema.json",
        &to_string_pretty_ln(&schema),
    );

    // Container using the AsMap types with serde's `with` attribute.
    #[derive(JsonSchema)]
    #[expect(unused)]
    struct ContainerAsMap {
        // This is in alphabetical order to ensure that the same fixture gets
        // generated with or without the `schemars/preserve_order` feature.
        #[serde(with = "BiHashMapAsMap::<TestUser>")]
        users_bi: BiHashMap<TestUser>,
        #[serde(with = "IdHashMapAsMap::<TestUser>")]
        users_hash: IdHashMap<TestUser>,
        #[serde(with = "IdOrdMapAsMap::<TestUser>")]
        users_ord: IdOrdMap<TestUser>,
        #[serde(with = "TriHashMapAsMap::<TestUser>")]
        users_tri: TriHashMap<TestUser>,
    }

    let schema = schema_for!(ContainerAsMap);
    assert_contents(
        "tests/output/container_as_map_schema.json",
        &to_string_pretty_ln(&schema),
    );
}

fn to_string_pretty_ln<T: Serialize>(data: &T) -> String {
    let mut s = serde_json::to_string_pretty(data).unwrap();
    s.push('\n');
    s
}
