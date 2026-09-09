// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Shared mechanics for Kani proofs.
//!
//! Keep semantic expectations in their individual proof modules unless Rust
//! itself defines the expectation here.

// Take a pre-operation value snapshot using safe Rust language operations,
// independently of any zerocopy target. Applying unary `*` to `value: &T`
// denotes the referenced location [1]. Because `*value` is the final operand
// of the function-body block, the block evaluates it in value-expression
// context [2]. Evaluating a place expression in that context copies it instead
// of moving it when the type implements `Copy` [3]; the bound makes that
// premise explicit for every use. This records a value, not allocation
// identity or independent storage for pointer-bearing `Copy` types.
//
// [1] https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#r-expr.deref.result
// [2] https://doc.rust-lang.org/1.93.0/reference/expressions/block-expr.html#r-expr.block.value
// [3] https://doc.rust-lang.org/1.93.0/reference/expressions.html#moved-and-copied-types
pub(crate) fn copy_snapshot<T: Copy>(value: &T) -> T {
    *value
}
