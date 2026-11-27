// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Zero-proc-macro declarative observable-trace recorder, padding-safe byte
//! capture, validity-checked schedule materializer, and shadow provenance
//! table.
//!
//! Uses safe Rust traits and `macro_rules!` with `core::mem::offset_of!` (zero
//! `proc-macro` crates, zero `unsafe` padding reads, zero
//! `MaybeUninit::assume_init`, and zero `#[repr(Rust)]` layout assumptions) so
//! all traced structs, enums, and external call boundaries remain Miri-clean
//! and compliant with Anneal's Cargo boundary policy.
//!
//! Architectural split:
//! 1. **In-process library primitives** (`TraceRecorder`, `MaskedByte`,
//!    `ShadowProvenanceTable`, `ScopedAllocationGuard`, `traced_external_fn!`,
//!    and `run_with_trace_recorder`) support direct in-process Rust unit and
//!    integration tests without spawning subprocess compilers.
//! 2. **Standalone subprocess runtime** (`render_embedded_trace_prelude`,
//!    emitting `mod anneal_rt`) is spliced into standalone single-file `rustc`
//!    (`-O0`/`-O2`) and `miri` binaries by `render_standalone_rust_harness`
//!    so subprocesses run with zero external crate dependencies.

use std::{
    cell::RefCell,
    collections::{BTreeMap, VecDeque},
    fmt::{self, Write as _},
    mem,
    num::{
        NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize, NonZeroU8,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
    },
    panic::{self, AssertUnwindSafe},
};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use sha2::{Digest, Sha256};

/// Error returned when a scheduled environment payload violates size or
/// bit-validity invariants of the target Rust type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ScheduleError {
    /// Payload byte length did not equal `core::mem::size_of::<T>()`.
    PayloadSizeMismatch { context: String, expected: usize, actual: usize },
    /// Payload bytes violated a type bit-validity invariant (`bool > 1`,
    /// surrogate `char`, zero `NonZero*`, or unknown enum discriminant).
    InvalidBitPattern { context: String, reason: String },
    /// Scheduled environment actions remained unconsumed when execution
    /// terminated.
    UnconsumedActions { remaining: usize },
}

impl fmt::Display for ScheduleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PayloadSizeMismatch { context, expected, actual } => write!(
                f,
                "schedule payload size mismatch for `{context}`: expected {expected} bytes, got {actual}"
            ),
            Self::InvalidBitPattern { context, reason } => {
                write!(f, "invalid bit pattern in schedule payload for `{context}`: {reason}")
            }
            Self::UnconsumedActions { remaining } => {
                write!(
                    f,
                    "{remaining} scheduled environment action(s) remained unconsumed at termination"
                )
            }
        }
    }
}

impl std::error::Error for ScheduleError {}

/// Internal marker payload used by in-process library unit tests when a
/// scheduled `EnvAction::Abort` fires inside `run_with_trace_recorder` (whereas
/// standalone `rustc` and `miri` child binaries flush `ANNEAL_ITREE_PRE_ABORT:`
/// and invoke real `std::process::abort()`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduledAbortPayload {
    pub callee: String,
    pub reason: String,
}

/// Internal non-unwind marker payload raised when a scheduled `ReturnBytes`
/// payload violates [`FromScheduleBytes`] validity invariants inside
/// `run_with_trace_recorder`, preventing invalid schedule bytes from being
/// misclassified as a normal callee `Unwind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleDecodeErrorPayload {
    pub callee: String,
    pub error: ScheduleError,
}

/// Structured terminal disposition of [`run_with_trace_recorder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceRunDisposition<R> {
    Returned(R),
    Unwound { message: String },
    ScheduledAbort(ScheduledAbortPayload),
    InvalidSchedule(ScheduleDecodeErrorPayload),
}

/// Explicit per-byte initialization tag avoiding any conflation between
/// initialized zero bytes (`Init(0)`) and uninitialized/padding bytes (`Pad`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", content = "byte", rename_all = "snake_case")]
pub enum MaskedByte {
    Init(u8),
    Pad,
}

impl MaskedByte {
    pub fn to_opt(self) -> Option<u8> {
        match self {
            Self::Init(b) => Some(b),
            Self::Pad => None,
        }
    }

    pub fn from_opt(opt: Option<u8>) -> Self {
        match opt {
            Some(b) => Self::Init(b),
            None => Self::Pad,
        }
    }
}

/// Layout-aware byte capture writing `Some(byte)` at initialized field offsets
/// and leaving inter-field and trailing padding offsets as `None`.
///
/// Implementations only ever touch primitive padding-free leaf values or
/// `#[repr(C)]` field offsets computed via `core::mem::offset_of!`, so padding
/// memory is never read even when uninitialized or poisoned under Miri.
pub trait TraceCapture {
    /// Write initialized bytes of `self` into `dst` (pre-filled with `None` of
    /// length `core::mem::size_of_val(self)`). Padding slots must stay `None`.
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]);

    /// Render a canonical cross-authority string representation matching Lean's
    /// `ITreeDriver.valRepr`.
    fn trace_repr(&self) -> String;
}

/// Capture initialized bytes of `val`, marking every padding byte as `None`.
pub fn capture_value_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<Option<u8>> {
    let size = mem::size_of_val(val);
    let mut dst = vec![None; size];
    val.write_captured_bytes(&mut dst);
    dst
}

/// Capture explicit [`MaskedByte`] tags (`Init(b)` vs `Pad`) for `val`.
pub fn capture_masked_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<MaskedByte> {
    capture_value_bytes(val).into_iter().map(MaskedByte::from_opt).collect()
}

/// Capture initialized bytes of `val` as raw `Vec<u8>`, deterministically
/// filling padding (`None`) offsets with `0u8` without reading padding memory.
pub fn value_as_raw_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<u8> {
    capture_value_bytes(val).into_iter().map(|b| b.unwrap_or(0)).collect()
}

/// Return a boolean mask (`true` = initialized field byte, `false` = padding
/// byte) for `val`.
pub fn capture_padding_mask<T: TraceCapture + ?Sized>(val: &T) -> Vec<bool> {
    capture_value_bytes(val).into_iter().map(|b| b.is_some()).collect()
}

/// Validity-checked deserialization from scheduled bytes without
/// `MaybeUninit::assume_init` or unchecked transmutes.
pub trait FromScheduleBytes: Sized {
    /// Decode `bytes` into `Self` after checking exact byte length and every
    /// scalar/niche/discriminant validity invariant.
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError>;
}

/// Helper used by declarative macros to verify exact byte-slice length.
pub fn check_exact_schedule_len(
    context: &str,
    expected: usize,
    actual: usize,
) -> Result<(), ScheduleError> {
    if expected != actual {
        Err(ScheduleError::PayloadSizeMismatch { context: context.to_string(), expected, actual })
    } else {
        Ok(())
    }
}

fn write_le_some(dst: &mut [Option<u8>], bytes: &[u8]) {
    for (slot, &b) in dst.iter_mut().zip(bytes.iter()) {
        *slot = Some(b);
    }
}

impl TraceCapture for () {
    fn write_captured_bytes(&self, _dst: &mut [Option<u8>]) {}

    fn trace_repr(&self) -> String {
        "()".to_string()
    }
}

impl FromScheduleBytes for () {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_schedule_len("()", 0, bytes.len())?;
        Ok(())
    }
}

impl TraceCapture for bool {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        if let Some(slot) = dst.first_mut() {
            *slot = Some(u8::from(*self));
        }
    }

    fn trace_repr(&self) -> String {
        if *self { "true".to_string() } else { "false".to_string() }
    }
}

impl FromScheduleBytes for bool {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_schedule_len("bool", 1, bytes.len())?;
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(ScheduleError::InvalidBitPattern {
                context: "bool".to_string(),
                reason: format!("expected 0 or 1 for `bool`, got {other:#04x}"),
            }),
        }
    }
}

impl TraceCapture for char {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        write_le_some(dst, &(*self as u32).to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        format!("char({})", *self as u32)
    }
}

impl FromScheduleBytes for char {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_schedule_len("char", 4, bytes.len())?;
        let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        char::from_u32(raw).ok_or_else(|| ScheduleError::InvalidBitPattern {
            context: "char".to_string(),
            reason: format!("invalid Unicode scalar value {raw:#010x}"),
        })
    }
}

impl TraceCapture for core::cmp::Ordering {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let b: i8 = match self {
            core::cmp::Ordering::Less => -1,
            core::cmp::Ordering::Equal => 0,
            core::cmp::Ordering::Greater => 1,
        };
        write_le_some(dst, &b.to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        match self {
            core::cmp::Ordering::Less => "Less".to_string(),
            core::cmp::Ordering::Equal => "Equal".to_string(),
            core::cmp::Ordering::Greater => "Greater".to_string(),
        }
    }
}

impl FromScheduleBytes for core::cmp::Ordering {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        check_exact_schedule_len("Ordering", 1, bytes.len())?;
        match bytes[0] as i8 {
            -1 => Ok(core::cmp::Ordering::Less),
            0 => Ok(core::cmp::Ordering::Equal),
            1 => Ok(core::cmp::Ordering::Greater),
            other => Err(ScheduleError::InvalidBitPattern {
                context: "Ordering".to_string(),
                reason: format!("expected -1, 0, or 1 for `Ordering`, got {other}"),
            }),
        }
    }
}

macro_rules! impl_prim_trace_capture {
    ($($ty:ty),* $(,)?) => {
        $(
            impl TraceCapture for $ty {
                fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                    write_le_some(dst, &self.to_le_bytes());
                }

                fn trace_repr(&self) -> String {
                    format!("{self}")
                }
            }

            impl FromScheduleBytes for $ty {
                fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
                    const N: usize = mem::size_of::<$ty>();
                    check_exact_schedule_len(stringify!($ty), N, bytes.len())?;
                    let mut arr = [0u8; N];
                    arr.copy_from_slice(bytes);
                    Ok(<$ty>::from_le_bytes(arr))
                }
            }
        )*
    };
}

impl_prim_trace_capture!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64);

macro_rules! impl_nonzero_trace_capture {
    ($($nz:ty => $prim:ty),* $(,)?) => {
        $(
            impl TraceCapture for $nz {
                fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                    self.get().write_captured_bytes(dst);
                }

                fn trace_repr(&self) -> String {
                    format!("{}", self.get())
                }
            }

            impl FromScheduleBytes for $nz {
                fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
                    let raw = <$prim as FromScheduleBytes>::from_schedule_bytes(bytes).map_err(
                        |e| match e {
                            ScheduleError::PayloadSizeMismatch { expected, actual, .. } => {
                                ScheduleError::PayloadSizeMismatch {
                                    context: stringify!($nz).to_string(),
                                    expected,
                                    actual,
                                }
                            }
                            other => other,
                        },
                    )?;
                    <$nz>::new(raw).ok_or_else(|| ScheduleError::InvalidBitPattern {
                        context: stringify!($nz).to_string(),
                        reason: "zero is not valid for NonZero*".to_string(),
                    })
                }
            }
        )*
    };
}

impl_nonzero_trace_capture!(
    NonZeroU8 => u8,
    NonZeroU16 => u16,
    NonZeroU32 => u32,
    NonZeroU64 => u64,
    NonZeroU128 => u128,
    NonZeroUsize => usize,
    NonZeroI8 => i8,
    NonZeroI16 => i16,
    NonZeroI32 => i32,
    NonZeroI64 => i64,
    NonZeroI128 => i128,
    NonZeroIsize => isize,
);

impl<T: TraceCapture, const N: usize> TraceCapture for [T; N] {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let stride = mem::size_of::<T>();
        for (idx, item) in self.iter().enumerate() {
            let start = idx * stride;
            let end = start + stride;
            if let Some(slice) = dst.get_mut(start..end) {
                item.write_captured_bytes(slice);
            }
        }
    }

    fn trace_repr(&self) -> String {
        let elems: Vec<String> = self.iter().map(TraceCapture::trace_repr).collect();
        format!("[{}]", elems.join(","))
    }
}

impl<T: FromScheduleBytes, const N: usize> FromScheduleBytes for [T; N] {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, ScheduleError> {
        let stride = mem::size_of::<T>();
        check_exact_schedule_len("[T; N]", stride * N, bytes.len())?;
        let mut items = Vec::with_capacity(N);
        for idx in 0..N {
            let start = idx * stride;
            items.push(T::from_schedule_bytes(&bytes[start..start + stride])?);
        }
        items.try_into().map_err(|_| ScheduleError::InvalidBitPattern {
            context: "[T; N]".to_string(),
            reason: "failed array conversion".to_string(),
        })
    }
}

impl<T> TraceCapture for &T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = core::ptr::from_ref::<T>(*self).addr();
        write_le_some(dst, &addr.to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        format!("ptr({:#x})", core::ptr::from_ref::<T>(*self).addr())
    }
}

impl<T> TraceCapture for &mut T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = core::ptr::from_ref::<T>(&**self).addr();
        write_le_some(dst, &addr.to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        format!("ptr({:#x})", core::ptr::from_ref::<T>(&**self).addr())
    }
}

impl<T> TraceCapture for *const T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = (*self).addr();
        write_le_some(dst, &addr.to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        format!("ptr({:#x})", (*self).addr())
    }
}

impl<T> TraceCapture for *mut T {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        let addr = (*self).addr();
        write_le_some(dst, &addr.to_le_bytes());
    }

    fn trace_repr(&self) -> String {
        format!("ptr({:#x})", (*self).addr())
    }
}

/// Define a `#[repr(C)]` struct and implement padding-safe [`TraceCapture`]
/// (via `core::mem::offset_of!`, leaving padding offsets as `None`) and
/// validity-checked [`FromScheduleBytes`] with zero proc-macros and zero
/// `unsafe`.
#[macro_export]
macro_rules! define_traced_struct {
    (
        $(#[$meta:meta])*
        $vis:vis struct $name:ident {
            $(
                $(#[$fmeta:meta])*
                $fvis:vis $fname:ident : $fty:ty
            ),* $(,)?
        }
    ) => {
        $(#[$meta])*
        #[repr(C)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        $vis struct $name {
            $(
                $(#[$fmeta])*
                $fvis $fname : $fty,
            )*
        }

        impl $crate::trace_observer::TraceCapture for $name {
            fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                $(
                    let off = core::mem::offset_of!($name, $fname);
                    let len = core::mem::size_of::<$fty>();
                    if let Some(slice) = dst.get_mut(off..off + len) {
                        $crate::trace_observer::TraceCapture::write_captured_bytes(
                            &self.$fname,
                            slice,
                        );
                    }
                )*
            }

            fn trace_repr(&self) -> String {
                let parts: Vec<String> = vec![
                    $(
                        format!(
                            "{}={}",
                            stringify!($fname),
                            $crate::trace_observer::TraceCapture::trace_repr(&self.$fname)
                        )
                    ),*
                ];
                format!("{}{{{}}}", stringify!($name), parts.join(","))
            }
        }

        impl $crate::trace_observer::FromScheduleBytes for $name {
            fn from_schedule_bytes(
                bytes: &[u8],
            ) -> Result<Self, $crate::trace_observer::ScheduleError> {
                $crate::trace_observer::check_exact_schedule_len(
                    stringify!($name),
                    core::mem::size_of::<$name>(),
                    bytes.len(),
                )?;
                Ok(Self {
                    $(
                        $fname: {
                            let off = core::mem::offset_of!($name, $fname);
                            let len = core::mem::size_of::<$fty>();
                            <$fty as $crate::trace_observer::FromScheduleBytes>::from_schedule_bytes(
                                &bytes[off..off + len],
                            )?
                        },
                    )*
                })
            }
        }
    };
}

/// Define a fieldless `#[repr($repr)]` enum and implement [`TraceCapture`] and
/// validity-checked [`FromScheduleBytes`] rejecting undeclared discriminants.
#[macro_export]
macro_rules! define_traced_enum {
    (
        #[repr($repr:ty)]
        $(#[$meta:meta])*
        $vis:vis enum $name:ident {
            $(
                $variant:ident = $discr:expr
            ),* $(,)?
        }
    ) => {
        $(#[$meta])*
        #[repr($repr)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        $vis enum $name {
            $(
                $variant = $discr,
            )*
        }

        impl $crate::trace_observer::TraceCapture for $name {
            fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                let raw: $repr = *self as $repr;
                $crate::trace_observer::TraceCapture::write_captured_bytes(&raw, dst);
            }

            fn trace_repr(&self) -> String {
                let raw: $repr = *self as $repr;
                format!("enum({raw})")
            }
        }

        impl $crate::trace_observer::FromScheduleBytes for $name {
            fn from_schedule_bytes(
                bytes: &[u8],
            ) -> Result<Self, $crate::trace_observer::ScheduleError> {
                let raw = <$repr as $crate::trace_observer::FromScheduleBytes>::from_schedule_bytes(
                    bytes,
                )
                .map_err(|e| match e {
                    $crate::trace_observer::ScheduleError::PayloadSizeMismatch {
                        expected,
                        actual,
                        ..
                    } => $crate::trace_observer::ScheduleError::PayloadSizeMismatch {
                        context: stringify!($name).to_string(),
                        expected,
                        actual,
                    },
                    other => other,
                })?;
                match raw {
                    $(
                        x if x == ($discr as $repr) => Ok(Self::$variant),
                    )*
                    other => Err($crate::trace_observer::ScheduleError::InvalidBitPattern {
                        context: stringify!($name).to_string(),
                        reason: format!(
                            "invalid discriminant {other:?} for enum `{}`",
                            stringify!($name)
                        ),
                    }),
                }
            }
        }
    };
}

/// Define a traced boundary function using pure declarative `macro_rules!`.
///
/// Records `CallEnter`, checks the active [`TraceRecorder`] [`EnvSchedule`]
/// (validating scheduled `ReturnBytes` via [`FromScheduleBytes`], surfacing
/// invalid bit patterns via [`ScheduleDecodeErrorPayload`] rather than normal
/// callee unwinds, or triggering `Unwind` / `Abort`), or runs the real body
/// under `catch_unwind` recording `CallReturn` or `CallUnwind`.
#[macro_export]
macro_rules! traced_external_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident ( $( $arg:ident : $arg_ty:ty ),* $(,)? ) -> $ret_ty:ty $body:block
    ) => {
        $(#[$meta])*
        #[inline(never)]
        $vis fn $name ( $( $arg : $arg_ty ),* ) -> $ret_ty {
            let __callee = stringify!($name);
            let __arg_bytes: Vec<Vec<Option<u8>>> = vec![
                $( $crate::trace_observer::capture_value_bytes(&$arg) ),*
            ];
            let __arg_reprs: Vec<String> = vec![
                $( $crate::trace_observer::TraceCapture::trace_repr(&$arg) ),*
            ];
            $crate::trace_observer::record_call_enter(__callee, __arg_bytes, __arg_reprs);

            if let Some(__action) = $crate::trace_observer::pop_scheduled_action(__callee) {
                match __action {
                    $crate::trace_observer::EnvAction::ReturnBytes(__raw) => {
                        match <$ret_ty as $crate::trace_observer::FromScheduleBytes>::from_schedule_bytes(&__raw) {
                            Ok(__val) => {
                                let __ret_bytes = $crate::trace_observer::capture_value_bytes(&__val);
                                let __ret_repr = $crate::trace_observer::TraceCapture::trace_repr(&__val);
                                $crate::trace_observer::record_call_return(
                                    __callee,
                                    __ret_bytes,
                                    __ret_repr,
                                );
                                return __val;
                            }
                            Err(__err) => {
                                $crate::trace_observer::record_schedule_error(
                                    __callee,
                                    __err.clone(),
                                );
                                std::panic::panic_any(
                                    $crate::trace_observer::ScheduleDecodeErrorPayload {
                                        callee: __callee.to_string(),
                                        error: __err,
                                    },
                                );
                            }
                        }
                    }
                    $crate::trace_observer::EnvAction::Unwind { message } => {
                        $crate::trace_observer::record_call_unwind(__callee, &message);
                        panic!("{message}");
                    }
                    $crate::trace_observer::EnvAction::Abort { reason } => {
                        $crate::trace_observer::record_call_unwind(
                            __callee,
                            &format!("abort:{reason}"),
                        );
                        std::panic::panic_any($crate::trace_observer::ScheduledAbortPayload {
                            callee: __callee.to_string(),
                            reason,
                        });
                    }
                }
            }

            let __res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || -> $ret_ty {
                $body
            }));
            match __res {
                Ok(__val) => {
                    let __ret_bytes = $crate::trace_observer::capture_value_bytes(&__val);
                    let __ret_repr = $crate::trace_observer::TraceCapture::trace_repr(&__val);
                    $crate::trace_observer::record_call_return(__callee, __ret_bytes, __ret_repr);
                    __val
                }
                Err(__payload) => {
                    if __payload.is::<$crate::trace_observer::ScheduledAbortPayload>()
                        || __payload.is::<$crate::trace_observer::ScheduleDecodeErrorPayload>()
                    {
                        std::panic::resume_unwind(__payload);
                    }
                    let __msg = $crate::trace_observer::panic_payload_message(&*__payload);
                    $crate::trace_observer::record_call_unwind(__callee, &__msg);
                    std::panic::resume_unwind(__payload);
                }
            }
        }
    };
}

/// Observable interaction events forming the ITree trace spine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ObservableEvent {
    /// Entry into a callee boundary with layout-aware argument bytes.
    CallEnter { callee: String, arg_bytes: Vec<Vec<Option<u8>>>, arg_reprs: Vec<String> },
    /// Normal return from a callee boundary with layout-aware return bytes.
    CallReturn { callee: String, ret_bytes: Vec<Option<u8>>, ret_repr: String },
    /// Unwind/panic propagation out of a callee boundary.
    CallUnwind { callee: String, reason: String },
    /// `switchInt` branch transition observed during execution.
    BranchTag { block: u32, discr: String, target: u32 },
    /// Caller-frame preservation checkpoint across call or cleanup boundaries.
    CallerFrameCheck {
        point: String,
        locals_preserved: bool,
        allocs_preserved: bool,
        preserved: bool,
    },
}

/// Ordered observable interaction spine collected during an authority run.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservableSpine {
    pub events: Vec<ObservableEvent>,
}

impl ObservableSpine {
    /// Return call-boundary events (`CallEnter`, `CallReturn`, `CallUnwind`),
    /// erasing internal `BranchTag` transitions while preserving call order.
    pub fn erased_call_spine(&self) -> Vec<ObservableEvent> {
        self.events
            .iter()
            .filter(|ev| {
                matches!(
                    ev,
                    ObservableEvent::CallEnter { .. }
                        | ObservableEvent::CallReturn { .. }
                        | ObservableEvent::CallUnwind { .. }
                )
            })
            .cloned()
            .collect()
    }

    /// Return all observable events except `BranchTag`, preserving relative
    /// interleaving order between call events and `CallerFrameCheck`
    /// checkpoints.
    pub fn erased_branch_spine(&self) -> Vec<ObservableEvent> {
        self.events
            .iter()
            .filter(|ev| !matches!(ev, ObservableEvent::BranchTag { .. }))
            .cloned()
            .collect()
    }

    /// Return only `BranchTag` transitions `(block, discr, target)`.
    pub fn branch_tags(&self) -> Vec<(u32, String, u32)> {
        self.events
            .iter()
            .filter_map(|ev| match ev {
                ObservableEvent::BranchTag { block, discr, target } => {
                    Some((*block, discr.clone(), *target))
                }
                _ => None,
            })
            .collect()
    }

    /// Return all caller-frame preservation checkpoints
    /// `(point, locals_preserved, allocs_preserved, preserved)`.
    pub fn caller_frame_checks(&self) -> Vec<(String, bool, bool, bool)> {
        self.events
            .iter()
            .filter_map(|ev| match ev {
                ObservableEvent::CallerFrameCheck {
                    point,
                    locals_preserved,
                    allocs_preserved,
                    preserved,
                } => Some((point.clone(), *locals_preserved, *allocs_preserved, *preserved)),
                _ => None,
            })
            .collect()
    }

    /// Deterministic SHA-256 hex digest of the canonical JSON spine.
    pub fn digest_hex(&self) -> String {
        let json = serde_json::to_string(&self.events).unwrap_or_default();
        let digest = Sha256::digest(json.as_bytes());
        let mut hex = String::with_capacity(64);
        for b in digest {
            let _ = write!(hex, "{b:02x}");
        }
        hex
    }
}

/// Scheduled environment response for an external call boundary (`MirCallE`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnvAction {
    /// Return raw little-endian bytes decoded via [`FromScheduleBytes`].
    ReturnBytes(Vec<u8>),
    /// Unwind out of the callee with the given panic message.
    Unwind { message: String },
    /// Abort execution immediately via `std::process::abort()` at the boundary.
    Abort { reason: String },
}

#[derive(Serialize)]
#[serde(tag = "action", rename_all = "snake_case")]
enum EnvActionSerializeRef<'a> {
    ReturnBytes { bytes: &'a [u8] },
    Unwind { message: &'a str },
    Abort { reason: &'a str },
}

#[derive(Deserialize)]
#[serde(tag = "action", rename_all = "snake_case")]
enum EnvActionDeserializeOwned {
    ReturnBytes { bytes: Vec<u8> },
    Unwind { message: String },
    Abort { reason: String },
}

impl Serialize for EnvAction {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let repr = match self {
            Self::ReturnBytes(bytes) => EnvActionSerializeRef::ReturnBytes { bytes },
            Self::Unwind { message } => EnvActionSerializeRef::Unwind { message },
            Self::Abort { reason } => EnvActionSerializeRef::Abort { reason },
        };
        repr.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for EnvAction {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let repr = EnvActionDeserializeOwned::deserialize(deserializer)?;
        Ok(match repr {
            EnvActionDeserializeOwned::ReturnBytes { bytes } => Self::ReturnBytes(bytes),
            EnvActionDeserializeOwned::Unwind { message } => Self::Unwind { message },
            EnvActionDeserializeOwned::Abort { reason } => Self::Abort { reason },
        })
    }
}

/// Deterministic environment response schedule for multi-call ITree runs.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvSchedule {
    /// Optional per-callee FIFO queues; when empty for a callee, falls back to
    /// `global`.
    pub per_callee: BTreeMap<String, VecDeque<EnvAction>>,
    /// Global fallback FIFO queue consumed across any scheduled callee.
    pub global: VecDeque<EnvAction>,
}

impl EnvSchedule {
    pub fn push_callee(&mut self, callee: impl Into<String>, action: EnvAction) {
        self.per_callee.entry(callee.into()).or_default().push_back(action);
    }

    pub fn push_global(&mut self, action: EnvAction) {
        self.global.push_back(action);
    }

    pub fn pop_for(&mut self, callee: &str) -> Option<EnvAction> {
        if let Some(q) = self.per_callee.get_mut(callee)
            && let Some(action) = q.pop_front()
        {
            return Some(action);
        }
        self.global.pop_front()
    }

    pub fn is_empty(&self) -> bool {
        self.remaining_count() == 0
    }

    pub fn remaining_count(&self) -> usize {
        self.global.len() + self.per_callee.values().map(VecDeque::len).sum::<usize>()
    }
}

/// Registered allocation entry in [`ShadowProvenanceTable`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShadowAllocEntry {
    pub alloc_id: u64,
    pub tag: String,
    pub base_addr: usize,
    pub byte_len: usize,
    pub mutable: bool,
}

/// Decoded abstract pointer provenance `(alloc_id, tag, offset)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedProvenance {
    pub alloc_id: u64,
    pub tag: String,
    pub offset: usize,
    pub mutable: bool,
}

/// Shadow-provenance allocation registry mapping watched runtime virtual
/// address intervals `[base_addr, base_addr + byte_len)` to abstract MIR
/// `(alloc_id, tag, offset)` coordinates.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShadowProvenanceTable {
    next_alloc_id: u64,
    entries: Vec<ShadowAllocEntry>,
}

impl ShadowProvenanceTable {
    pub fn new() -> Self {
        Self { next_alloc_id: 1, entries: Vec::new() }
    }

    /// Register a live allocation region `[base_addr, base_addr + byte_len)`
    /// and return its assigned abstract `alloc_id`.
    pub fn register_allocation(
        &mut self,
        tag: impl Into<String>,
        base_addr: usize,
        byte_len: usize,
        mutable: bool,
    ) -> u64 {
        let alloc_id = self.next_alloc_id;
        self.next_alloc_id += 1;
        self.entries.push(ShadowAllocEntry {
            alloc_id,
            tag: tag.into(),
            base_addr,
            byte_len,
            mutable,
        });
        alloc_id
    }

    /// Register an existing Rust reference's backing memory region safely via
    /// strict-provenance `.addr()`.
    pub fn register_ref<T>(&mut self, tag: impl Into<String>, r: &T, mutable: bool) -> u64 {
        let base_addr = core::ptr::from_ref::<T>(r).addr();
        let byte_len = mem::size_of::<T>();
        self.register_allocation(tag, base_addr, byte_len, mutable)
    }

    /// Unregister `alloc_id` when its stack or heap lifetime ends so reused
    /// stack addresses never resolve to stale provenance.
    pub fn unregister_allocation(&mut self, alloc_id: u64) -> bool {
        let before = self.entries.len();
        self.entries.retain(|e| e.alloc_id != alloc_id);
        self.entries.len() != before
    }

    /// Register an allocation and return an RAII [`ScopedAllocationGuard`] that
    /// automatically unregisters `alloc_id` on drop.
    pub fn register_scoped_ref<'a, T>(
        &'a mut self,
        tag: impl Into<String>,
        r: &T,
        mutable: bool,
    ) -> ScopedAllocationGuard<'a> {
        let alloc_id = self.register_ref(tag, r, mutable);
        ScopedAllocationGuard { table: self, alloc_id }
    }

    /// Resolve a runtime address into its registered abstract provenance
    /// `(alloc_id, tag, offset)`, permitting one-past-the-end addresses when
    /// `allow_one_past_end` is `true`.
    pub fn resolve_addr(
        &self,
        addr: usize,
        allow_one_past_end: bool,
    ) -> Option<ResolvedProvenance> {
        for entry in self.entries.iter().rev() {
            let end = entry.base_addr.saturating_add(entry.byte_len);
            let in_bounds = if allow_one_past_end {
                addr >= entry.base_addr && addr <= end
            } else if entry.byte_len == 0 {
                addr == entry.base_addr
            } else {
                addr >= entry.base_addr && addr < end
            };
            if in_bounds {
                return Some(ResolvedProvenance {
                    alloc_id: entry.alloc_id,
                    tag: entry.tag.clone(),
                    offset: addr - entry.base_addr,
                    mutable: entry.mutable,
                });
            }
        }
        None
    }

    /// Decode a captured pointer byte slice (8 bytes on 64-bit targets) via the
    /// shadow provenance table.
    pub fn decode_pointer_bytes(
        &self,
        bytes: &[Option<u8>],
        allow_one_past_end: bool,
    ) -> Option<ResolvedProvenance> {
        if bytes.len() != mem::size_of::<usize>() {
            return None;
        }
        let mut raw = [0u8; mem::size_of::<usize>()];
        for (dst, opt) in raw.iter_mut().zip(bytes.iter()) {
            *dst = (*opt)?;
        }
        let addr = usize::from_le_bytes(raw);
        self.resolve_addr(addr, allow_one_past_end)
    }

    pub fn entries(&self) -> &[ShadowAllocEntry] {
        &self.entries
    }
}

/// RAII scope guard that removes a registered allocation from
/// [`ShadowProvenanceTable`] when dropped.
pub struct ScopedAllocationGuard<'a> {
    table: &'a mut ShadowProvenanceTable,
    alloc_id: u64,
}

impl ScopedAllocationGuard<'_> {
    pub fn alloc_id(&self) -> u64 {
        self.alloc_id
    }

    pub fn table(&self) -> &ShadowProvenanceTable {
        self.table
    }
}

impl Drop for ScopedAllocationGuard<'_> {
    fn drop(&mut self) {
        self.table.unregister_allocation(self.alloc_id);
    }
}

/// Active trace recorder holding the observable spine, scheduled environment
/// actions, recorded schedule decode error (if any), and shadow provenance
/// registry.
#[derive(Clone, Debug, Default)]
pub struct TraceRecorder {
    pub spine: ObservableSpine,
    pub schedule: EnvSchedule,
    pub provenance: ShadowProvenanceTable,
    pub schedule_error: Option<(String, ScheduleError)>,
}

impl TraceRecorder {
    pub fn new(schedule: EnvSchedule) -> Self {
        Self {
            spine: ObservableSpine::default(),
            schedule,
            provenance: ShadowProvenanceTable::new(),
            schedule_error: None,
        }
    }

    pub fn record_branch(&mut self, block: u32, discr: impl Into<String>, target: u32) {
        self.spine.events.push(ObservableEvent::BranchTag { block, discr: discr.into(), target });
    }

    pub fn record_caller_frame_check(
        &mut self,
        point: impl Into<String>,
        locals_preserved: bool,
        allocs_preserved: bool,
    ) {
        self.spine.events.push(ObservableEvent::CallerFrameCheck {
            point: point.into(),
            locals_preserved,
            allocs_preserved,
            preserved: locals_preserved && allocs_preserved,
        });
    }
}

thread_local! {
    static ACTIVE_RECORDER: RefCell<Option<TraceRecorder>> = const { RefCell::new(None) };
}

/// Execute `f` with an installed thread-local [`TraceRecorder`], classifying
/// normal returns, panicking unwinds, scheduled aborts, and invalid schedule
/// bit-pattern errors into distinct [`TraceRunDisposition`] variants.
pub fn run_with_trace_recorder<R, F>(
    schedule: EnvSchedule,
    f: F,
) -> (TraceRunDisposition<R>, TraceRecorder)
where
    F: FnOnce() -> R,
{
    let prev = ACTIVE_RECORDER.with(|cell| cell.borrow_mut().replace(TraceRecorder::new(schedule)));
    let res = panic::catch_unwind(AssertUnwindSafe(f));
    let mut finished = ACTIVE_RECORDER
        .with(|cell| {
            let taken = cell.borrow_mut().take();
            if let Some(old) = prev {
                *cell.borrow_mut() = Some(old);
            }
            taken
        })
        .unwrap_or_default();
    let mut disposition = match res {
        Ok(val) => TraceRunDisposition::Returned(val),
        Err(payload) => {
            if let Some(abort) = payload.downcast_ref::<ScheduledAbortPayload>() {
                TraceRunDisposition::ScheduledAbort(abort.clone())
            } else if let Some(sched_err) = payload.downcast_ref::<ScheduleDecodeErrorPayload>() {
                TraceRunDisposition::InvalidSchedule(sched_err.clone())
            } else {
                TraceRunDisposition::Unwound { message: panic_payload_message(&*payload) }
            }
        }
    };
    let remaining = finished.schedule.remaining_count();
    if remaining > 0 {
        let err = ScheduleError::UnconsumedActions { remaining };
        finished.schedule_error = Some(("<unconsumed>".to_string(), err.clone()));
        disposition = TraceRunDisposition::InvalidSchedule(ScheduleDecodeErrorPayload {
            callee: "<unconsumed>".to_string(),
            error: err,
        });
    }
    (disposition, finished)
}

/// Mutate the active thread-local [`TraceRecorder`] if one is installed.
pub fn with_active_trace_recorder<R>(f: impl FnOnce(&mut TraceRecorder) -> R) -> Option<R> {
    ACTIVE_RECORDER.with(|cell| cell.borrow_mut().as_mut().map(f))
}

#[doc(hidden)]
pub fn record_call_enter(callee: &str, arg_bytes: Vec<Vec<Option<u8>>>, arg_reprs: Vec<String>) {
    let _ = with_active_trace_recorder(|rec| {
        rec.spine.events.push(ObservableEvent::CallEnter {
            callee: callee.to_string(),
            arg_bytes,
            arg_reprs,
        });
    });
}

#[doc(hidden)]
pub fn record_call_return(callee: &str, ret_bytes: Vec<Option<u8>>, ret_repr: String) {
    let _ = with_active_trace_recorder(|rec| {
        rec.spine.events.push(ObservableEvent::CallReturn {
            callee: callee.to_string(),
            ret_bytes,
            ret_repr,
        });
    });
}

#[doc(hidden)]
pub fn record_call_unwind(callee: &str, reason: &str) {
    let _ = with_active_trace_recorder(|rec| {
        rec.spine.events.push(ObservableEvent::CallUnwind {
            callee: callee.to_string(),
            reason: reason.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn record_schedule_error(callee: &str, error: ScheduleError) {
    let _ = with_active_trace_recorder(|rec| {
        rec.schedule_error = Some((callee.to_string(), error));
    });
}

#[doc(hidden)]
pub fn pop_scheduled_action(callee: &str) -> Option<EnvAction> {
    with_active_trace_recorder(|rec| rec.schedule.pop_for(callee)).flatten()
}

/// Extract a human-readable string from a `catch_unwind` panic payload.
pub fn panic_payload_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(abort) = payload.downcast_ref::<ScheduledAbortPayload>() {
        return format!("abort:{}:{}", abort.callee, abort.reason);
    }
    if let Some(sched) = payload.downcast_ref::<ScheduleDecodeErrorPayload>() {
        return format!("schedule_error:{}:{}", sched.callee, sched.error);
    }
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "non-string panic payload".to_string()
    }
}

/// Prefix emitted right before invoking the subject entry function so Miri UB
/// runs still authenticate evaluated entry argument `boundary_slots`.
pub const PRE_ENTRY_JSON_PREFIX: &str = "ANNEAL_ITREE_PRE_ENTRY:";

/// Prefix emitted immediately before `std::process::abort()` when a scheduled
/// `EnvAction::Abort` fires inside a standalone `rustc` or `miri` harness.
pub const PRE_ABORT_JSON_PREFIX: &str = "ANNEAL_ITREE_PRE_ABORT:";

/// Render a self-contained, zero-dependency, Miri-clean Rust prelude module
/// (`mod anneal_rt`) embedded in standalone `rustc` and `miri` execution
/// harnesses so host binaries and Miri emit structured observable traces,
/// dynamic padding-mask checks, `EnvSchedule` actions (`ReturnBytes`, `Unwind`,
/// and real `std::process::abort()`), and boundary byte snapshots without
/// external crate dependencies.
pub fn render_embedded_trace_prelude() -> &'static str {
    r#"
#[allow(dead_code)]
mod anneal_rt {
    use std::cell::{Cell, RefCell};
    use std::collections::{BTreeMap, VecDeque};
    use std::io::Write as _;

    pub trait TraceCapture {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]);
        fn trace_repr(&self) -> String;
    }

    pub trait FromScheduleBytes: Sized {
        fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String>;
    }

    pub fn capture_value_bytes<T: TraceCapture + ?Sized>(val: &T) -> Vec<Option<u8>> {
        let mut dst = vec![None; core::mem::size_of_val(val)];
        val.write_captured_bytes(&mut dst);
        dst
    }

    fn write_le(dst: &mut [Option<u8>], bytes: &[u8]) {
        for (slot, &b) in dst.iter_mut().zip(bytes.iter()) {
            *slot = Some(b);
        }
    }

    impl TraceCapture for () {
        fn write_captured_bytes(&self, _dst: &mut [Option<u8>]) {}
        fn trace_repr(&self) -> String { "()".to_string() }
    }

    impl FromScheduleBytes for () {
        fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
            if bytes.is_empty() { Ok(()) } else { Err(format!("expected 0 bytes for (), got {}", bytes.len())) }
        }
    }

    impl TraceCapture for bool {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            if let Some(slot) = dst.first_mut() {
                *slot = Some(u8::from(*self));
            }
        }
        fn trace_repr(&self) -> String {
            if *self { "true".to_string() } else { "false".to_string() }
        }
    }

    impl FromScheduleBytes for bool {
        fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
            if bytes.len() != 1 {
                return Err(format!("expected 1 byte for bool, got {}", bytes.len()));
            }
            match bytes[0] {
                0 => Ok(false),
                1 => Ok(true),
                b => Err(format!("invalid bool bit pattern {b:#04x}")),
            }
        }
    }

    impl TraceCapture for char {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            write_le(dst, &(*self as u32).to_le_bytes());
        }
        fn trace_repr(&self) -> String {
            format!("char({})", *self as u32)
        }
    }

    impl FromScheduleBytes for char {
        fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
            if bytes.len() != 4 {
                return Err(format!("expected 4 bytes for char, got {}", bytes.len()));
            }
            let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
            char::from_u32(raw).ok_or_else(|| format!("invalid Unicode scalar {raw:#010x}"))
        }
    }

    impl TraceCapture for core::cmp::Ordering {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            let b: i8 = match self {
                core::cmp::Ordering::Less => -1,
                core::cmp::Ordering::Equal => 0,
                core::cmp::Ordering::Greater => 1,
            };
            write_le(dst, &b.to_le_bytes());
        }
        fn trace_repr(&self) -> String {
            match self {
                core::cmp::Ordering::Less => "Less".to_string(),
                core::cmp::Ordering::Equal => "Equal".to_string(),
                core::cmp::Ordering::Greater => "Greater".to_string(),
            }
        }
    }

    impl FromScheduleBytes for core::cmp::Ordering {
        fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
            if bytes.len() != 1 {
                return Err(format!("expected 1 byte for Ordering, got {}", bytes.len()));
            }
            match bytes[0] as i8 {
                -1 => Ok(core::cmp::Ordering::Less),
                0 => Ok(core::cmp::Ordering::Equal),
                1 => Ok(core::cmp::Ordering::Greater),
                b => Err(format!("invalid Ordering discriminant {b}")),
            }
        }
    }

    macro_rules! impl_num_capture {
        ($($t:ty),*) => {
            $(
                impl TraceCapture for $t {
                    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
                        write_le(dst, &self.to_le_bytes());
                    }
                    fn trace_repr(&self) -> String {
                        format!("{self}")
                    }
                }

                impl FromScheduleBytes for $t {
                    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
                        const N: usize = core::mem::size_of::<$t>();
                        if bytes.len() != N {
                            return Err(format!("expected {N} bytes for {}, got {}", stringify!($t), bytes.len()));
                        }
                        let mut arr = [0u8; N];
                        arr.copy_from_slice(bytes);
                        Ok(<$t>::from_le_bytes(arr))
                    }
                }
            )*
        };
    }

    impl_num_capture!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

    impl<T> TraceCapture for &T {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            write_le(dst, &core::ptr::from_ref::<T>(*self).addr().to_le_bytes());
        }
        fn trace_repr(&self) -> String {
            format!("ptr({:#x})", core::ptr::from_ref::<T>(*self).addr())
        }
    }

    impl<T> TraceCapture for *const T {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            write_le(dst, &(*self).addr().to_le_bytes());
        }
        fn trace_repr(&self) -> String {
            format!("ptr({:#x})", (*self).addr())
        }
    }

    #[derive(Clone)]
    pub enum RtEnvAction {
        ReturnBytes(Vec<u8>),
        Unwind(String),
        Abort(String),
    }

    pub struct ScheduleDecodeFailed(pub String);

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub struct RootCallerFrame {
        pub tag: u8,
        pub magic: u32,
        pub flag: bool,
        pub counter: u64,
    }

    impl TraceCapture for RootCallerFrame {
        fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
            let o0 = core::mem::offset_of!(RootCallerFrame, tag);
            self.tag.write_captured_bytes(&mut dst[o0..o0 + 1]);
            let o1 = core::mem::offset_of!(RootCallerFrame, magic);
            self.magic.write_captured_bytes(&mut dst[o1..o1 + 4]);
            let o2 = core::mem::offset_of!(RootCallerFrame, flag);
            self.flag.write_captured_bytes(&mut dst[o2..o2 + 1]);
            let o3 = core::mem::offset_of!(RootCallerFrame, counter);
            self.counter.write_captured_bytes(&mut dst[o3..o3 + 8]);
        }
        fn trace_repr(&self) -> String {
            format!("RootCallerFrame({},{},{},{})", self.tag, self.magic, self.flag, self.counter)
        }
    }

    pub fn format_opt_bytes(bytes: &[Option<u8>]) -> String {
        let mut s = String::from("[");
        for (i, b) in bytes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            match b {
                Some(v) => s.push_str(&v.to_string()),
                None => s.push_str("null"),
            }
        }
        s.push(']');
        s
    }

    pub fn escape_json(input: &str) -> String {
        let mut out = String::with_capacity(input.len() + 2);
        out.push('"');
        for ch in input.chars() {
            match ch {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c if (c as u32) < 0x20 => {
                    out.push_str(&format!("\\u{:04x}", c as u32));
                }
                c => out.push(c),
            }
        }
        out.push('"');
        out
    }

    thread_local! {
        static EVENTS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
        static LOCALS_OK: Cell<bool> = const { Cell::new(true) };
        static ALLOCS_OK: Cell<bool> = const { Cell::new(true) };
        static PADDING_OK: Cell<bool> = const { Cell::new(true) };
        static FRAME_VIOLATIONS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
        static BOUNDARY_SLOTS: RefCell<Vec<Vec<Option<u8>>>> = const { RefCell::new(Vec::new()) };
        static PER_CALLEE_SCHED: RefCell<BTreeMap<String, VecDeque<RtEnvAction>>> = const { RefCell::new(BTreeMap::new()) };
        static GLOBAL_SCHED: RefCell<VecDeque<RtEnvAction>> = const { RefCell::new(VecDeque::new()) };
        static CALLER_FRAME_BASELINE: RefCell<Vec<Option<u8>>> = const { RefCell::new(Vec::new()) };
        static CALLER_FRAME_PTR: Cell<*const RootCallerFrame> = const { Cell::new(core::ptr::null()) };
        static WATCHED_ALLOC_BASELINE: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
        static WATCHED_ALLOC_PTR: Cell<*const u8> = const { Cell::new(core::ptr::null()) };
        static WATCHED_ALLOC_LEN: Cell<usize> = const { Cell::new(0) };
    }

    pub fn record_boundary_slot(bytes: Vec<Option<u8>>) {
        BOUNDARY_SLOTS.with(|b| b.borrow_mut().push(bytes));
    }

    pub fn record_post_return_slot(ret_bytes: Vec<Option<u8>>) {
        let mut slot = Vec::with_capacity(1 + ret_bytes.len());
        slot.push(Some(0x10));
        slot.extend(ret_bytes);
        record_boundary_slot(slot);
    }

    pub fn record_post_unwind_slot() {
        record_boundary_slot(vec![Some(0x20)]);
    }

    pub fn record_post_abort_slot() {
        record_boundary_slot(vec![Some(0x30)]);
    }

    pub fn push_callee_action(callee: &str, action: RtEnvAction) {
        PER_CALLEE_SCHED.with(|m| {
            m.borrow_mut().entry(callee.to_string()).or_default().push_back(action);
        });
    }

    pub fn push_global_action(action: RtEnvAction) {
        GLOBAL_SCHED.with(|g| g.borrow_mut().push_back(action));
    }

    pub fn reset_schedules() {
        PER_CALLEE_SCHED.with(|m| m.borrow_mut().clear());
        GLOBAL_SCHED.with(|g| g.borrow_mut().clear());
    }

    pub fn reset_trace_observer() {
        EVENTS.with(|e| e.borrow_mut().clear());
        LOCALS_OK.with(|c| c.set(true));
        ALLOCS_OK.with(|c| c.set(true));
        PADDING_OK.with(|c| c.set(true));
        FRAME_VIOLATIONS.with(|v| v.borrow_mut().clear());
        BOUNDARY_SLOTS.with(|b| b.borrow_mut().clear());
        CALLER_FRAME_BASELINE.with(|b| b.borrow_mut().clear());
        CALLER_FRAME_PTR.with(|p| p.set(core::ptr::null()));
        WATCHED_ALLOC_BASELINE.with(|b| b.borrow_mut().clear());
        WATCHED_ALLOC_PTR.with(|p| p.set(core::ptr::null()));
        WATCHED_ALLOC_LEN.with(|l| l.set(0));
    }

    pub fn current_boundary_slots_json() -> String {
        let slots = BOUNDARY_SLOTS.with(|b| {
            b.borrow().iter().map(|s| format_opt_bytes(s)).collect::<Vec<_>>().join(",")
        });
        format!("[{slots}]")
    }

    pub fn current_events_json() -> String {
        let events = EVENTS.with(|e| e.borrow().join(","));
        format!("[{events}]")
    }

    pub fn current_caller_frame_preserved() -> bool {
        LOCALS_OK.with(Cell::get) && ALLOCS_OK.with(Cell::get) && PADDING_OK.with(Cell::get)
    }

    pub fn pop_action(callee: &str) -> Option<RtEnvAction> {
        let specific = PER_CALLEE_SCHED.with(|m| {
            m.borrow_mut().get_mut(callee).and_then(VecDeque::pop_front)
        });
        if specific.is_some() {
            return specific;
        }
        GLOBAL_SCHED.with(|g| g.borrow_mut().pop_front())
    }

    pub fn remaining_schedule_count() -> usize {
        let per_callee: usize =
            PER_CALLEE_SCHED.with(|m| m.borrow().values().map(VecDeque::len).sum());
        let global = GLOBAL_SCHED.with(|g| g.borrow().len());
        per_callee + global
    }

    pub struct ScopedCallerWatchGuard {
        prev_frame_ptr: *const RootCallerFrame,
        prev_frame_baseline: Vec<Option<u8>>,
        prev_alloc_ptr: *const u8,
        prev_alloc_len: usize,
        prev_alloc_baseline: Vec<u8>,
    }

    impl ScopedCallerWatchGuard {
        /// Install provenance-preserving `*const` pointers to the caller's
        /// `RootCallerFrame` and watched byte buffer for the duration of the
        /// scope, restoring any enclosing caller watch state on drop.
        pub unsafe fn install(
            frame_ptr: *const RootCallerFrame,
            alloc_ptr: *const u8,
            alloc_len: usize,
        ) -> Self {
            let live_frame = unsafe { &*std::hint::black_box(frame_ptr) };
            let frame_baseline = capture_value_bytes(live_frame);
            let live_alloc =
                unsafe { core::slice::from_raw_parts(std::hint::black_box(alloc_ptr), alloc_len) };
            let prev_frame_ptr = CALLER_FRAME_PTR.with(|p| p.replace(frame_ptr));
            let prev_frame_baseline =
                CALLER_FRAME_BASELINE.with(|b| core::mem::replace(&mut *b.borrow_mut(), frame_baseline));
            let prev_alloc_ptr = WATCHED_ALLOC_PTR.with(|p| p.replace(alloc_ptr));
            let prev_alloc_len = WATCHED_ALLOC_LEN.with(|l| l.replace(alloc_len));
            let prev_alloc_baseline = WATCHED_ALLOC_BASELINE
                .with(|b| core::mem::replace(&mut *b.borrow_mut(), live_alloc.to_vec()));
            Self {
                prev_frame_ptr,
                prev_frame_baseline,
                prev_alloc_ptr,
                prev_alloc_len,
                prev_alloc_baseline,
            }
        }
    }

    impl Drop for ScopedCallerWatchGuard {
        fn drop(&mut self) {
            CALLER_FRAME_PTR.with(|p| p.set(self.prev_frame_ptr));
            WATCHED_ALLOC_PTR.with(|p| p.set(self.prev_alloc_ptr));
            WATCHED_ALLOC_LEN.with(|l| l.set(self.prev_alloc_len));
            CALLER_FRAME_BASELINE.with(|b| {
                *b.borrow_mut() = core::mem::take(&mut self.prev_frame_baseline);
            });
            WATCHED_ALLOC_BASELINE.with(|b| {
                *b.borrow_mut() = core::mem::take(&mut self.prev_alloc_baseline);
            });
        }
    }

    /// Read the live `RootCallerFrame` (`offset_of!`) and watched caller byte
    /// buffer through provenance-preserving `*const` pointers via `black_box`,
    /// recording any local, padding-mask, or allocation drift.
    pub fn check_and_emit_caller_frame(point: &str) {
        let frame_ptr = CALLER_FRAME_PTR.with(Cell::get);
        let alloc_ptr = WATCHED_ALLOC_PTR.with(Cell::get);
        let alloc_len = WATCHED_ALLOC_LEN.with(Cell::get);
        if frame_ptr.is_null() {
            return;
        }
        let before = CALLER_FRAME_BASELINE.with(|b| b.borrow().clone());
        let after = unsafe { capture_value_bytes(&*std::hint::black_box(frame_ptr)) };
        let len_ok = before.len() == after.len();
        let mut val_ok = len_ok;
        let mut pad_ok = len_ok;
        if len_ok {
            for (b, a) in before.iter().zip(after.iter()) {
                match (b, a) {
                    (None, None) => {}
                    (Some(x), Some(y)) => {
                        if x != y {
                            val_ok = false;
                        }
                    }
                    _ => {
                        pad_ok = false;
                    }
                }
            }
        }
        if !val_ok {
            LOCALS_OK.with(|c| c.set(false));
            FRAME_VIOLATIONS.with(|v| {
                v.borrow_mut().push(format!("caller local byte drift at {point}"));
            });
        }
        if !pad_ok {
            PADDING_OK.with(|c| c.set(false));
            FRAME_VIOLATIONS.with(|v| {
                v.borrow_mut().push(format!("padding mask violation at {point}"));
            });
        }

        let allocs_ok = if alloc_ptr.is_null() {
            true
        } else {
            let live_alloc =
                unsafe { core::slice::from_raw_parts(std::hint::black_box(alloc_ptr), alloc_len) };
            WATCHED_ALLOC_BASELINE.with(|b| b.borrow().as_slice() == live_alloc)
        };
        if !allocs_ok {
            ALLOCS_OK.with(|c| c.set(false));
            FRAME_VIOLATIONS.with(|v| {
                v.borrow_mut().push(format!("untouched caller allocation drift at {point}"));
            });
        }

        let locals_preserved = val_ok && pad_ok;
        let preserved = locals_preserved && allocs_ok;
        let ev = format!(
            "{{\"kind\":\"caller_frame_check\",\"point\":{},\"locals_preserved\":{locals_preserved},\"allocs_preserved\":{allocs_ok},\"preserved\":{preserved}}}",
            escape_json(point),
        );
        EVENTS.with(|e| e.borrow_mut().push(ev));
    }

    pub fn emit_call_enter(callee: &str, arg_bytes: &[Vec<Option<u8>>], arg_reprs: &[String]) {
        let ab: Vec<String> = arg_bytes.iter().map(|v| format_opt_bytes(v)).collect();
        let ar: Vec<String> = arg_reprs.iter().map(|s| escape_json(s)).collect();
        let ev = format!(
            "{{\"kind\":\"call_enter\",\"callee\":{},\"arg_bytes\":[{}],\"arg_reprs\":[{}]}}",
            escape_json(callee),
            ab.join(","),
            ar.join(",")
        );
        EVENTS.with(|e| e.borrow_mut().push(ev));
    }

    pub fn emit_call_return(callee: &str, ret_bytes: &[Option<u8>], ret_repr: &str) {
        let ev = format!(
            "{{\"kind\":\"call_return\",\"callee\":{},\"ret_bytes\":{},\"ret_repr\":{}}}",
            escape_json(callee),
            format_opt_bytes(ret_bytes),
            escape_json(ret_repr)
        );
        EVENTS.with(|e| e.borrow_mut().push(ev));
        check_and_emit_caller_frame(&format!("{callee}:return"));
    }

    pub fn emit_call_unwind(callee: &str, reason: &str) {
        let ev = format!(
            "{{\"kind\":\"call_unwind\",\"callee\":{},\"reason\":{}}}",
            escape_json(callee),
            escape_json(reason)
        );
        EVENTS.with(|e| e.borrow_mut().push(ev));
        if !reason.starts_with("abort:") {
            check_and_emit_caller_frame(&format!("{callee}:unwind"));
        }
    }

    pub fn emit_branch(block: u32, discr: &str, target: u32) {
        let ev = format!(
            "{{\"kind\":\"branch_tag\",\"block\":{block},\"discr\":{},\"target\":{target}}}",
            escape_json(discr)
        );
        EVENTS.with(|e| e.borrow_mut().push(ev));
    }

    pub fn trigger_scheduled_abort(callee: &str, reason: &str) -> ! {
        emit_call_unwind(callee, &format!("abort:{reason}"));
        record_post_abort_slot();
        let payload = render_trace_payload_json("aborted", "null", &format!("abort:{reason}"));
        println!("ANNEAL_ITREE_PRE_ABORT:{payload}");
        let _ = std::io::stdout().flush();
        std::process::abort()
    }

    pub fn handle_scheduled_call<R, F>(
        callee: &str,
        arg_bytes: Vec<Vec<Option<u8>>>,
        arg_reprs: Vec<String>,
        fallback: F,
    ) -> R
    where
        R: TraceCapture + FromScheduleBytes,
        F: FnOnce() -> R,
    {
        emit_call_enter(callee, &arg_bytes, &arg_reprs);
        if let Some(action) = pop_action(callee) {
            match action {
                RtEnvAction::ReturnBytes(raw) => match R::from_schedule_bytes(&raw) {
                    Ok(val) => {
                        let rb = capture_value_bytes(&val);
                        let rr = val.trace_repr();
                        emit_call_return(callee, &rb, &rr);
                        return val;
                    }
                    Err(err) => {
                        std::panic::panic_any(ScheduleDecodeFailed(format!(
                            "callee `{callee}` scheduled ReturnBytes invalid: {err}"
                        )));
                    }
                },
                RtEnvAction::Unwind(msg) => {
                    emit_call_unwind(callee, &msg);
                    panic!("{msg}");
                }
                RtEnvAction::Abort(reason) => {
                    trigger_scheduled_abort(callee, &reason);
                }
            }
        }
        let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(fallback));
        match out {
            Ok(val) => {
                let rb = capture_value_bytes(&val);
                let rr = val.trace_repr();
                emit_call_return(callee, &rb, &rr);
                val
            }
            Err(payload) => {
                if payload.is::<ScheduleDecodeFailed>() {
                    std::panic::resume_unwind(payload);
                }
                let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "panic".to_string()
                };
                emit_call_unwind(callee, &msg);
                std::panic::resume_unwind(payload)
            }
        }
    }

    pub fn json_scalar(kind_id: &str, bits: u128) -> String {
        format!("{{\"kind\":\"scalar\",\"kind_id\":\"{kind_id}\",\"bits\":\"{bits}\"}}")
    }

    pub fn json_bool(v: bool) -> String {
        format!("{{\"kind\":\"bool\",\"value\":{v}}}")
    }

    pub fn json_char(c: char) -> String {
        format!("{{\"kind\":\"char\",\"scalar\":{}}}", c as u32)
    }

    pub fn json_ordering(o: core::cmp::Ordering) -> String {
        let s = match o {
            core::cmp::Ordering::Less => "less",
            core::cmp::Ordering::Equal => "equal",
            core::cmp::Ordering::Greater => "greater",
        };
        format!("{{\"kind\":\"ordering\",\"value\":\"{s}\"}}")
    }

    pub fn json_unit() -> String {
        "{\"kind\":\"unit\"}".to_string()
    }

    pub fn json_padded<T: TraceCapture + ?Sized>(type_name: &str, val: &T) -> String {
        format!(
            "{{\"kind\":\"padded_bytes\",\"type_name\":{},\"bytes\":{}}}",
            escape_json(type_name),
            format_opt_bytes(&capture_value_bytes(val)),
        )
    }

    pub fn render_trace_payload_json(outcome_kind: &str, ret_json: &str, detail: &str) -> String {
        let rem = remaining_schedule_count();
        let (effective_kind, effective_ret, effective_detail) = if rem > 0 {
            (
                "unconsumed_schedule",
                "null",
                format!("{rem} scheduled EnvAction(s) remained unconsumed at termination"),
            )
        } else {
            (outcome_kind, ret_json, detail.to_string())
        };
        let events = EVENTS.with(|e| e.borrow().join(","));
        let violations = FRAME_VIOLATIONS.with(|v| {
            v.borrow().iter().map(|s| escape_json(s)).collect::<Vec<_>>().join(",")
        });
        let locals_ok = LOCALS_OK.with(Cell::get);
        let allocs_ok = ALLOCS_OK.with(Cell::get);
        let padding_ok = PADDING_OK.with(Cell::get);
        let slots = BOUNDARY_SLOTS.with(|b| {
            b.borrow().iter().map(|s| format_opt_bytes(s)).collect::<Vec<_>>().join(",")
        });
        format!(
            "{{\"outcome_kind\":{},\"ret\":{},\"detail\":{},\"boundary_slots\":[{slots}],\"caller_locals_preserved\":{locals_ok},\"untouched_alloc_bytes_preserved\":{allocs_ok},\"padding_mask_respected\":{padding_ok},\"violations\":[{violations}],\"events\":[{events}]}}",
            escape_json(effective_kind),
            effective_ret,
            escape_json(&effective_detail),
        )
    }

    pub fn emit_pre_entry_slots() {
        let slots = BOUNDARY_SLOTS.with(|b| {
            b.borrow().iter().map(|s| format_opt_bytes(s)).collect::<Vec<_>>().join(",")
        });
        println!("ANNEAL_ITREE_PRE_ENTRY:{{\"boundary_slots\":[{slots}]}}");
        let _ = std::io::stdout().flush();
    }

    pub fn finish_json(outcome_kind: &str, ret_json: &str, detail: &str) {
        let payload = render_trace_payload_json(outcome_kind, ret_json, detail);
        println!("ANNEAL_ITREE_TRACE_JSON:{payload}");
    }
}
"#
}
