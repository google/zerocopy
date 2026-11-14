-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-! Auto-generated Intrinsic Signature Delta Table: rustc 1.99.1 -> 1.100.0 -/

namespace Anneal.ToolchainTables

inductive DeltaKind where
  | identical
  | safeAddition
  | breakingSemanticDelta
  deriving Repr, DecidableEq

structure IntrinsicDeltaEntry where
  name : String
  kind : DeltaKind
  sig1991 : Option String
  sig1100 : Option String
  deriving Repr, DecidableEq

def intrinsicDelta_1991_to_1100 : List IntrinsicDeltaEntry := [
  { name := "cos", kind := .safeAddition, sig1991 := none, sig1100 := some "fn cos<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "exp", kind := .safeAddition, sig1991 := none, sig1100 := some "fn exp<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "exp2", kind := .safeAddition, sig1991 := none, sig1100 := some "fn exp2<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "integer_max", kind := .safeAddition, sig1991 := none, sig1100 := some "fn integer_max<T: [const] bounds::IntegerPrimitive>(a: T, b: T) -> T" },
  { name := "integer_min", kind := .safeAddition, sig1991 := none, sig1100 := some "fn integer_min<T: [const] bounds::IntegerPrimitive>(a: T, b: T) -> T" },
  { name := "log", kind := .safeAddition, sig1991 := none, sig1100 := some "fn log<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "log10", kind := .safeAddition, sig1991 := none, sig1100 := some "fn log10<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "log2", kind := .safeAddition, sig1991 := none, sig1100 := some "fn log2<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "offload_get_num_devices", kind := .safeAddition, sig1991 := none, sig1100 := some "fn offload_get_num_devices() -> i32" },
  { name := "sin", kind := .safeAddition, sig1991 := none, sig1100 := some "fn sin<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "type_id_array_len", kind := .safeAddition, sig1991 := none, sig1100 := some "fn type_id_array_len(_id: crate::any::TypeId) -> usize" },
  { name := "type_id_element_ty", kind := .safeAddition, sig1991 := none, sig1100 := some "fn type_id_element_ty(_id: crate::any::TypeId) -> Option<crate::any::TypeId>" },
  { name := "type_id_function_ptr", kind := .safeAddition, sig1991 := none, sig1100 := some "fn type_id_function_ptr(_type_id: crate::any::TypeId) -> Option<crate::mem::type_info::FnPtr>" },
  { name := "type_id_points_mutably", kind := .safeAddition, sig1991 := none, sig1100 := some "fn type_id_points_mutably(_id: crate::any::TypeId) -> bool" },
  { name := "type_id_points_to", kind := .safeAddition, sig1991 := none, sig1100 := some "fn type_id_points_to(_id: crate::any::TypeId) -> Option<crate::any::TypeId>" },
  { name := "variant_name", kind := .safeAddition, sig1991 := none, sig1100 := some "fn variant_name(_base: crate::any::TypeId, _variant_index: usize) -> &'static str" },
  { name := "variant_non_exhaustive", kind := .safeAddition, sig1991 := none, sig1100 := some "fn variant_non_exhaustive(base: crate::any::TypeId, variant: usize) -> bool" },
  { name := "cosf128", kind := .breakingSemanticDelta, sig1991 := some "fn cosf128(x: f128) -> f128", sig1100 := none },
  { name := "cosf16", kind := .breakingSemanticDelta, sig1991 := some "fn cosf16(x: f16) -> f16", sig1100 := none },
  { name := "cosf32", kind := .breakingSemanticDelta, sig1991 := some "fn cosf32(x: f32) -> f32", sig1100 := none },
  { name := "cosf64", kind := .breakingSemanticDelta, sig1991 := some "fn cosf64(x: f64) -> f64", sig1100 := none },
  { name := "exp2f128", kind := .breakingSemanticDelta, sig1991 := some "fn exp2f128(x: f128) -> f128", sig1100 := none },
  { name := "exp2f16", kind := .breakingSemanticDelta, sig1991 := some "fn exp2f16(x: f16) -> f16", sig1100 := none },
  { name := "exp2f32", kind := .breakingSemanticDelta, sig1991 := some "fn exp2f32(x: f32) -> f32", sig1100 := none },
  { name := "exp2f64", kind := .breakingSemanticDelta, sig1991 := some "fn exp2f64(x: f64) -> f64", sig1100 := none },
  { name := "expf128", kind := .breakingSemanticDelta, sig1991 := some "fn expf128(x: f128) -> f128", sig1100 := none },
  { name := "expf16", kind := .breakingSemanticDelta, sig1991 := some "fn expf16(x: f16) -> f16", sig1100 := none },
  { name := "expf32", kind := .breakingSemanticDelta, sig1991 := some "fn expf32(x: f32) -> f32", sig1100 := none },
  { name := "expf64", kind := .breakingSemanticDelta, sig1991 := some "fn expf64(x: f64) -> f64", sig1100 := none },
  { name := "log10f128", kind := .breakingSemanticDelta, sig1991 := some "fn log10f128(x: f128) -> f128", sig1100 := none },
  { name := "log10f16", kind := .breakingSemanticDelta, sig1991 := some "fn log10f16(x: f16) -> f16", sig1100 := none },
  { name := "log10f32", kind := .breakingSemanticDelta, sig1991 := some "fn log10f32(x: f32) -> f32", sig1100 := none },
  { name := "log10f64", kind := .breakingSemanticDelta, sig1991 := some "fn log10f64(x: f64) -> f64", sig1100 := none },
  { name := "log2f128", kind := .breakingSemanticDelta, sig1991 := some "fn log2f128(x: f128) -> f128", sig1100 := none },
  { name := "log2f16", kind := .breakingSemanticDelta, sig1991 := some "fn log2f16(x: f16) -> f16", sig1100 := none },
  { name := "log2f32", kind := .breakingSemanticDelta, sig1991 := some "fn log2f32(x: f32) -> f32", sig1100 := none },
  { name := "log2f64", kind := .breakingSemanticDelta, sig1991 := some "fn log2f64(x: f64) -> f64", sig1100 := none },
  { name := "logf128", kind := .breakingSemanticDelta, sig1991 := some "fn logf128(x: f128) -> f128", sig1100 := none },
  { name := "logf16", kind := .breakingSemanticDelta, sig1991 := some "fn logf16(x: f16) -> f16", sig1100 := none },
  { name := "logf32", kind := .breakingSemanticDelta, sig1991 := some "fn logf32(x: f32) -> f32", sig1100 := none },
  { name := "logf64", kind := .breakingSemanticDelta, sig1991 := some "fn logf64(x: f64) -> f64", sig1100 := none },
  { name := "sinf128", kind := .breakingSemanticDelta, sig1991 := some "fn sinf128(x: f128) -> f128", sig1100 := none },
  { name := "sinf16", kind := .breakingSemanticDelta, sig1991 := some "fn sinf16(x: f16) -> f16", sig1100 := none },
  { name := "sinf32", kind := .breakingSemanticDelta, sig1991 := some "fn sinf32(x: f32) -> f32", sig1100 := none },
  { name := "sinf64", kind := .breakingSemanticDelta, sig1991 := some "fn sinf64(x: f64) -> f64", sig1100 := none },
  { name := "atomic_load", kind := .breakingSemanticDelta, sig1991 := some "fn atomic_load<T: Copy, const ORD: AtomicOrdering>(src: *const T) -> T", sig1100 := some "fn atomic_load<T: Copy, const ORD: AtomicOrdering, const VOLATILE: bool>(src: *const T,) -> T" },
  { name := "atomic_store", kind := .breakingSemanticDelta, sig1991 := some "fn atomic_store<T: Copy, const ORD: AtomicOrdering>(dst: *mut T, val: T) -> ()", sig1100 := some "fn atomic_store<T: Copy, const ORD: AtomicOrdering, const VOLATILE: bool>(dst: *mut T, val: T,) -> ()" },
  { name := "fabs", kind := .breakingSemanticDelta, sig1991 := some "fn fabs<T: const bounds::FloatPrimitive>(x: T) -> T", sig1100 := some "fn fabs<T: bounds::FloatPrimitive>(x: T) -> T" },
  { name := "offload", kind := .breakingSemanticDelta, sig1991 := some "fn offload<F, T: crate::marker::Tuple, R>(f: F, workgroup_dim: [u32; 3], thread_dim: [u32; 3], dyn_cache: u32, args: T,) -> R", sig1100 := some "fn offload<F, T: crate::marker::Tuple, R>(f: F, workgroup_dim: [u32; 3], thread_dim: [u32; 3], dyn_cache: u32, device_id: i32, args: T,) -> R" }
]

end Anneal.ToolchainTables
