use enum_dispatch::enum_dispatch;

use serde::{Deserialize, Serialize};

#[enum_dispatch]
trait Shaped {
    fn area(&self) -> f32;
}

#[enum_dispatch(Shaped)]
#[derive(Serialize, Deserialize, Debug, PartialEq)]
enum Shape {
    Rectangle,
    Square,
    Circle,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Rectangle {
    w: f32,
    h: f32,
}

impl Shaped for Rectangle {
    fn area(&self) -> f32 {
        self.w * self.h
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Square {
    s: f32,
}

impl Shaped for Square {
    fn area(&self) -> f32 {
        self.s * self.s
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
struct Circle {
    r: f32,
}

impl Shaped for Circle {
    fn area(&self) -> f32 {
        self.r * self.r * std::f32::consts::PI
    }
}

#[test]
fn through_serde() {
    let rectangle = Rectangle { w: 10., h: 20. }.into();
    let square = Square { s: 15. }.into();
    let circle = Circle { r: 10. }.into();

    let shapes: Vec<Shape> = vec![rectangle, square, circle];

    let serialized_shapes: Vec<String> = shapes
        .iter()
        .map(|s| serde_json::to_string(&s).unwrap())
        .collect();

    assert_eq!(
        serialized_shapes,
        [
            "{\"Rectangle\":{\"w\":10.0,\"h\":20.0}}",
            "{\"Square\":{\"s\":15.0}}",
            "{\"Circle\":{\"r\":10.0}}"
        ]
    );

    let deserialized_shapes: Vec<Shape> = serialized_shapes
        .iter()
        .map(|s| serde_json::from_str(&s).unwrap())
        .collect();

    for (shape, new_shape) in shapes.iter().zip(deserialized_shapes.iter()) {
        assert_eq!(shape, new_shape);
    }
}
