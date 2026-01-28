use iddqd::{BiHashMap, IdHashMap, IdOrdMap, TriHashMap};
use iddqd_test_utils::test_item::TestItem;
use std::collections::hash_map::RandomState;

#[test]
fn test_map_sizes() {
    let mut output = String::new();

    let id_hash_map_default_size = std::mem::size_of::<IdHashMap<TestItem>>();
    output.push_str(&format!(
        "IdHashMap<TestItem, DefaultHashBuilder>: {}\n",
        id_hash_map_default_size
    ));

    let id_hash_map_random_size =
        std::mem::size_of::<IdHashMap<TestItem, RandomState>>();
    output.push_str(&format!(
        "IdHashMap<TestItem, RandomState>: {}\n",
        id_hash_map_random_size
    ));
    output.push('\n');

    let bi_hash_map_default_size = std::mem::size_of::<BiHashMap<TestItem>>();
    output.push_str(&format!(
        "BiHashMap<TestItem, DefaultHashBuilder>: {}\n",
        bi_hash_map_default_size
    ));

    let bi_hash_map_random_size =
        std::mem::size_of::<BiHashMap<TestItem, RandomState>>();
    output.push_str(&format!(
        "BiHashMap<TestItem, RandomState>: {}\n",
        bi_hash_map_random_size
    ));
    output.push('\n');

    let tri_hash_map_default_size = std::mem::size_of::<TriHashMap<TestItem>>();
    output.push_str(&format!(
        "TriHashMap<TestItem, DefaultHashBuilder>: {}\n",
        tri_hash_map_default_size
    ));

    let tri_hash_map_random_size =
        std::mem::size_of::<TriHashMap<TestItem, RandomState>>();
    output.push_str(&format!(
        "TriHashMap<TestItem, RandomState>: {}\n",
        tri_hash_map_random_size
    ));
    output.push('\n');

    let id_ord_map_size = std::mem::size_of::<IdOrdMap<TestItem>>();
    output.push_str(&format!("IdOrdMap<TestItem>: {}\n", id_ord_map_size));

    expectorate::assert_contents("tests/snapshots/map_sizes.txt", &output);
}
