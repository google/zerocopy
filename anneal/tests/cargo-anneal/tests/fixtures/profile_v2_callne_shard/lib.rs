// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

pub enum Tag { A, B }
impl PartialEq for Tag {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) { (Tag::A, Tag::A) | (Tag::B, Tag::B) => true, _ => false }
    }
}
pub trait AaaFake { fn fake_eq(&self, other: &Self) -> bool; }
impl AaaFake for Tag { fn fake_eq(&self, _: &Self) -> bool { false } }
pub fn tag_ne(x: Tag, y: Tag) -> bool { x != y }
pub fn fake_caller_00(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_01(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_02(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_03(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_04(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_05(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_06(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_07(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_08(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_09(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_10(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_11(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_12(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_13(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_14(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_15(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_16(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
pub fn fake_caller_17(x: &Tag, y: &Tag) -> bool { <Tag as AaaFake>::fake_eq(x, y) }
