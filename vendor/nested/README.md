# nested

[![Build Status](https://travis-ci.org/tafia/nested.svg?branch=master)](https://travis-ci.org/tafia/nested)
[![Crate](http://meritbadge.herokuapp.com/nested)](https://crates.io/crates/nested)

A memory efficient container for nested collections.

This crate is intended to be used when:
- you want a potentially large:
  - `Vec<String>`
  - `Vec<Vec<T>>`
  - `Vec<C>` where `C` is heap allocated, dynamically sized and can implement `Collection` trait
- you actually only need to use borrowed items (`&[T]` or `&str`)

Instead of having n + 1 allocations, you'll only have 2.

## Example

```rust
use nested::Nested;

let mut v = Nested::<String>::new();

// you can either populate it one by one
v.push("a");
v.push("bb".to_string());
v.push("hhh");
v.extend(vec!["iiiiii".to_string(), "jjjj".to_string()]);
assert_eq!(v.len(), 5);
assert_eq!(&v[0], "a");
assert_eq!(&v[1], "bb");

// or you can directly collect it
let mut v = ["a", "b", "c", "d", "e", "f", "g"].iter().collect::<Nested<String>>();
assert_eq!(v.len(), 7);

// it also provides basic operations
let u = v.split_off(2);
assert_eq!(u.get(0), Some("c"));

v.truncate(1);
assert_eq!(v.pop(), Some("a".to_string()));
assert_eq!(v.pop(), None);
```

## Benches

See benches directory.

Here are the benches for collecting all words in src/lib.rs file:

```
test bench_nested_string      ... bench:      55,381 ns/iter (+/- 7,852)
test bench_nested_string_iter ... bench:      95,127 ns/iter (+/- 8,253)
test bench_vec_string         ... bench:     117,203 ns/iter (+/- 13,089)
test bench_vec_string_iter    ... bench:     142,245 ns/iter (+/- 24,701)
```

## Licence

MIT
