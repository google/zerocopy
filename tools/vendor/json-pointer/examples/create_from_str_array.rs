extern crate json_pointer;
#[macro_use]
extern crate serde_json;

use json_pointer::JsonPointer;

fn main() {
    let ptr = JsonPointer::new([
        "foo",
        "bar",
    ]);

    assert_eq!(&ptr.to_string(), "/foo/bar");

    let document = json!({
        "foo": {
            "bar": 0,
            "baz": 1,
        },
        "quux": "xyzzy"
    });

    let indexed = ptr.get(&document).unwrap();

    assert_eq!(indexed, &json!(0));
}
