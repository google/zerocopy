use enum_dispatch::enum_dispatch;

use serde::{Deserialize, Serialize};

#[enum_dispatch]
trait SomeTrait {
    fn some_method(&self);
}

#[enum_dispatch(SomeTrait)]
#[derive(Debug, PartialEq, Serialize, Deserialize)]
enum MyEnum {
    Foo,
    Bar(#[serde(skip)] Bar),
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct Foo {
    test: u32,
}

impl SomeTrait for Foo {
    fn some_method(&self) {}
}

#[derive(Debug, Default, PartialEq, Serialize, Deserialize)]
struct Bar;

impl SomeTrait for Bar {
    fn some_method(&self) {}
}

#[derive(Debug, PartialEq, Serialize, Deserialize)]
struct MyContainer {
    list: Vec<MyEnum>,
}

#[test]
fn main() {
    let data = MyContainer {
        list: vec![Foo { test: 12 }.into(), Bar.into()],
    };
    let json = serde_json::to_string(&data).unwrap();
    assert_eq!(json, "{\"list\":[{\"Foo\":{\"test\":12}},\"Bar\"]}");
    let data2 = serde_json::from_str(&json).unwrap();
    assert_eq!(data, data2);
}
