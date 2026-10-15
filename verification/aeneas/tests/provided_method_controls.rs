// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]
trait OnlyUnusedDependency {
    fn unused_dependency(&self);
}
trait RequiredDependency {
    fn required_dependency(&self);
}
trait Api {
    // Slot zero is omitted, so retaining the required slot must preserve a gap.
    fn unused<T: OnlyUnusedDependency>(&self, value: T) {
        value.unused_dependency();
    }
    fn required<T: RequiredDependency>(&self, value: T) -> T;
    fn called(&self) -> u8 {
        9
    }
}
impl Api for u8 {
    fn required<T: RequiredDependency>(&self, value: T) -> T {
        value
    }
}
impl Api for u16 {
    fn required<T: RequiredDependency>(&self, value: T) -> T {
        value
    }
    fn unused<T: OnlyUnusedDependency>(&self, value: T) {
        value.unused_dependency();
    }
    fn called(&self) -> u8 {
        10
    }
}
fn keep<T: Api>(value: T) -> T {
    value
}
fn concrete_keep(value: u8) -> u8 {
    keep(value)
}
fn override_keep(value: u16) -> u16 {
    keep(value)
}
fn generic_call<T: Api>(value: T) -> u8 {
    value.called()
}
fn concrete_call(value: u8) -> u8 {
    value.called()
}
fn override_call(value: u16) -> u8 {
    value.called()
}
fn hidden_call<T: Api>(value: T) -> u8 {
    value.called()
}
fn through_hidden(value: u8) -> u8 {
    hidden_call(value)
}

struct Plain;
impl Plain {
    fn plain() -> u8 {
        7
    }
}
fn inherent_call() -> u8 {
    Plain::plain()
}
