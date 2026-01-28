//! An example demonstrating `IdOrdMap` use with complex borrowed keys.

use iddqd::{
    Comparable, Equivalent, IdOrdItem, IdOrdMap, id_ord_map::Entry, id_upcast,
};
use std::path::{Path, PathBuf};

/// These are the items we'll store in the `IdOrdMap`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MyStruct {
    a: String,
    b: usize,
    c: PathBuf,
    d: Vec<usize>,
}

/// The map will be indexed uniquely by (b, c, d). Note that this is a
/// borrowed key that can be constructed efficiently.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct MyKey<'a> {
    b: usize,
    c: &'a Path,
    d: &'a [usize],
}

impl IdOrdItem for MyStruct {
    type Key<'a> = MyKey<'a>;

    fn key(&self) -> Self::Key<'_> {
        MyKey { b: self.b, c: &self.c, d: &self.d }
    }

    id_upcast!();
}

fn main() {
    // Make a `TriHashMap` with the keys we defined above.
    let mut map = IdOrdMap::new();

    let item = MyStruct {
        a: "example".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: Vec::new(),
    };

    // Add an item to the map.
    map.insert_unique(item.clone()).unwrap();

    // This item will conflict with the previous one due to b, c and d
    // matching.
    map.insert_unique(MyStruct {
        a: "something-else".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: Vec::new(),
    })
    .unwrap_err();

    // Add another item to the map. Note that this item has the same c and d
    // but a different b.
    let item2 = MyStruct {
        a: "example".to_owned(),
        b: 10,
        c: PathBuf::from("/"),
        d: Vec::new(),
    };
    map.insert_unique(item2.clone()).unwrap();

    // Lookups can happen based on a borrowed key. For example:
    assert_eq!(
        map.get(&MyKey { b: 20, c: Path::new("/"), d: &[] }),
        Some(&item)
    );

    // Values can also be mutated in place, as long as the key type implements
    // `Hash`. For example:
    {
        let mut item =
            map.get_mut(&MyKey { b: 20, c: Path::new("/"), d: &[] }).unwrap();
        item.a = "changed".to_owned();

        // Key changes will be checked when the item is dropped.
    }

    // While iterating over the map, items will be sorted by their key.
    for item in map.iter() {
        println!("{item:?}");
    }

    let item3 = MyStruct {
        a: "example".to_owned(),
        b: 20,
        c: PathBuf::from("/"),
        d: vec![1, 2, 3],
    };

    for item in [item, item2, item3.clone()] {
        let entry = map.entry(item.key());
        match entry {
            Entry::Occupied(entry) => {
                // Get the entry's item.
                let item = entry.get();
                println!("occupied: {item:?}");
            }
            Entry::Vacant(entry) => {
                // Insert a new item.
                let item_ref = entry.insert_ref(item);
                println!("inserted: {item_ref:?}");
            }
        }
    }

    // Lookups can be done with any key type that implements `Comparable`. This
    // is strictly more general than the Borrow you might be used to. For
    // example, lookups against an owned key:
    struct MyKeyOwned {
        b: usize,
        c: PathBuf,
        d: Vec<usize>,
    }

    impl Equivalent<MyKey<'_>> for MyKeyOwned {
        fn equivalent(&self, other: &MyKey<'_>) -> bool {
            self.b == other.b && self.c == other.c && self.d == other.d
        }
    }

    impl Comparable<MyKey<'_>> for MyKeyOwned {
        fn compare(&self, other: &MyKey<'_>) -> std::cmp::Ordering {
            self.b
                .cmp(&other.b)
                .then_with(|| self.c.as_path().cmp(other.c))
                .then_with(|| self.d.as_slice().cmp(other.d))
        }
    }

    let key = MyKeyOwned { b: 20, c: PathBuf::from("/"), d: vec![1, 2, 3] };
    assert_eq!(map.get(&key), Some(&item3));
}
