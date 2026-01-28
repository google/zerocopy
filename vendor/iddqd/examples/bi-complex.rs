//! An example demonstrating `BiHashMap` use with complex borrowed keys.

use iddqd::{BiHashItem, BiHashMap, bi_hash_map::Entry, bi_upcast};
use std::path::{Path, PathBuf};

/// These are the items we'll store in the `BiHashMap`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MyStruct {
    a: String,
    b: usize,
    c: PathBuf,
    d: Vec<usize>,
}

/// The map will be indexed uniquely by (b, c). Note that this is a
/// borrowed key that can be constructed efficiently.
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct MyKey1<'a> {
    b: usize,
    c: &'a Path,
}

/// The map will also be indexed uniquely by (&Path, &[usize]).
#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct MyKey2<'a> {
    c: &'a Path,
    d: &'a [usize],
}

impl BiHashItem for MyStruct {
    type K1<'a> = MyKey1<'a>;
    type K2<'a> = MyKey2<'a>;

    fn key1(&self) -> Self::K1<'_> {
        MyKey1 { b: self.b, c: &self.c }
    }

    fn key2(&self) -> Self::K2<'_> {
        MyKey2 { c: &self.c, d: &self.d }
    }

    bi_upcast!();
}

fn main() {
    // Make a `TriHashMap` with the keys we defined above.
    let mut map = BiHashMap::new();

    let item = MyStruct {
        a: "example".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: Vec::new(),
    };

    // Add an item to the map.
    map.insert_unique(item.clone()).unwrap();

    // This item will conflict with the previous one due to b and c matching.
    map.insert_unique(MyStruct {
        a: "something-else".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: vec![1],
    })
    .unwrap_err();

    // Add another item to the map. Note that this item has the same b and d
    // but a different c.
    let item2 = MyStruct {
        a: "example".to_owned(),
        b: 10,
        c: PathBuf::from("/home"),
        d: Vec::new(),
    };
    map.insert_unique(item2.clone()).unwrap();

    // Lookups can happen based on a borrowed key. For example:
    assert_eq!(map.get1(&MyKey1 { b: 20, c: Path::new("/") }), Some(&item));

    // While iterating over the map, items will be returned in arbitrary order.
    for item in map.iter() {
        println!("{item:?}");
    }

    // This matches by key1 but not key2.
    let item3 = MyStruct {
        a: "example".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: vec![1, 2, 3],
    };

    // This matches by neither key1 nor key2.
    let item4 = MyStruct {
        a: "example".to_owned(),
        b: 20,
        c: PathBuf::from("/home"),
        d: vec![1, 2, 3],
    };

    for item in [item, item2, item3, item4] {
        let entry = map.entry(item.key1(), item.key2());
        match entry {
            Entry::Occupied(entry) => {
                // Get the entry's item.
                let item = entry.get();
                println!("occupied: {item:?}");
            }
            Entry::Vacant(entry) => {
                // Insert a new item.
                let item_ref = entry.insert(item);
                println!("inserted: {item_ref:?}");
            }
        }
    }
}
