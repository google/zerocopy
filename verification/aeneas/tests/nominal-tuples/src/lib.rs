// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

#[repr(transparent)]
pub struct First(pub u32);
pub struct Second(pub u32);
pub struct Empty();
pub struct OtherEmpty();
pub struct Generic<T>(pub T);
pub struct OtherGeneric<T>(pub T);
pub struct Pair<T>(pub T, pub u32);
pub struct OtherPair<T>(pub T, pub u32);
pub struct Nested<T>(pub First, pub Second, pub Generic<T>);
pub struct OtherNested<T>(pub First, pub Second, pub Generic<T>);

pub fn construct(x: u32) -> (First, Second) {
    (First(x), Second(x))
}
pub fn project(x: First, y: Second) -> (u32, u32) {
    (x.0, y.0)
}
pub fn pattern(x: First, y: Second) -> (u32, u32) {
    let First(a) = x;
    let Second(b) = y;
    (a, b)
}
pub fn empty() -> (Empty, OtherEmpty) {
    (Empty(), OtherEmpty())
}
pub fn empty_pattern(x: Empty, y: OtherEmpty) {
    let Empty() = x;
    let OtherEmpty() = y;
}
pub fn generic<T>(x: T) -> Generic<T> {
    Generic(x)
}
pub fn other_generic<T>(x: T) -> OtherGeneric<T> {
    OtherGeneric(x)
}
pub fn generic_pattern<T>(x: Generic<T>) -> T {
    let Generic(a) = x;
    a
}
pub fn pair<T>(x: T, y: u32) -> Pair<T> {
    Pair(x, y)
}
pub fn other_pair<T>(x: T, y: u32) -> OtherPair<T> {
    OtherPair(x, y)
}
pub fn other_pair_pattern<T>(x: OtherPair<T>) -> (T, u32) {
    let OtherPair(a, b) = x;
    (a, b)
}
pub fn pair_pattern<T>(x: Pair<T>) -> (T, u32) {
    let Pair(a, b) = x;
    (a, b)
}
pub fn update<T>(mut x: Pair<T>, y: u32) -> Pair<T> {
    x.1 = y;
    x
}
pub fn nested<T>(x: T, y: u32) -> Nested<T> {
    Nested(First(y), Second(y), Generic(x))
}
pub fn nested_pattern<T>(x: Nested<T>) -> (u32, u32, T) {
    let Nested(First(a), Second(b), Generic(c)) = x;
    (a, b, c)
}
pub fn ordinary(x: u32, y: u64) -> (u32, u64) {
    (x, y)
}
pub fn ordinary_pattern(x: (u32, u64)) -> (u64, u32) {
    let (a, b) = x;
    (b, a)
}
pub fn ordinary_unit(x: ()) {
    let () = x;
}
pub fn other_nested<T>(x: T, y: u32) -> OtherNested<T> {
    OtherNested(First(y), Second(y), Generic(x))
}
pub fn other_nested_pattern<T>(x: OtherNested<T>) -> (u32, u32, T) {
    let OtherNested(First(a), Second(b), Generic(c)) = x;
    (a, b, c)
}
pub fn ordinary_single<T>(x: T) -> (T,) {
    (x,)
}
