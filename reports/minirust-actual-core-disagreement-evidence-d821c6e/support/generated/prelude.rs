pub trait Target: libspecr::hidden::Obj {
    /// The size and align of a pointer.
    const PTR_SIZE: Size;
    const PTR_ALIGN: Align;
    /// The maximum alignment of integer types.
    /// Smaller types are aligned to their size.
    const INT_MAX_ALIGN: Align;
    /// The endianess used for encoding multi-byte integer values (and pointers).
    const ENDIANNESS: Endianness;
    /// Maximum size of an atomic operation.
    const MAX_ATOMIC_SIZE: Size;
    /// Checks that `size` is not too large for this target.
    fn valid_size(size: Size) -> bool;
}
#[allow(non_camel_case_types)]
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub struct x86_64;
impl Target for x86_64 {
    const PTR_SIZE: Size = Size::from_bits_const(64).unwrap();
    const PTR_ALIGN: Align = Align::from_bits_const(64).unwrap();
    const INT_MAX_ALIGN: Align = Align::from_bits_const(128).unwrap();
    const ENDIANNESS: Endianness = LittleEndian;
    const MAX_ATOMIC_SIZE: Size = Size::from_bits_const(64).unwrap();
    fn valid_size(size: Size) -> bool {
        size.bytes().in_bounds(Signed, Self::PTR_SIZE)
    }
}
/// Documentation for libspecr can be found here: https://docs.rs/libspecr
pub use libspecr::prelude::*;
/// Make the two main modules available.
pub use crate::{lang, mem};
/// When a non-negative integer is used as an offset into an allocation or type
/// rather than to describe the size of an object or type, use this type instead
/// of `Size` for extra clarity.
pub type Offset = Size;
/// All operations are fallible, so they return `Result`.  If they fail, that
/// means the program caused UB or put the machine to a halt.
pub type Result<T = ()> = std::result::Result<T, TerminationInfo>;
#[derive(GcCompat)]
#[derive(Debug)]
#[derive(Clone)]
#[derive(Copy)]
#[derive(PartialEq)]
#[derive(Eq)]
#[derive(Hash)]
#[derive(PartialOrd)]
#[derive(Ord)]
#[derive(serde::Serialize)]
#[derive(serde::Deserialize)]
pub enum TerminationInfo {
    /// The execution encountered undefined behaviour.
    Ub(String),
    /// The program was executed and the machine stopped without error.
    MachineStop,
    /// The program terminated with a panic
    Abort,
    /// The program was ill-formed.
    IllFormed(String),
    /// The program did not terminate but no thread can make progress.
    Deadlock,
    /// The program terminated successfully but memory was leaked.
    MemoryLeak,
}
/// Some macros for convenient yeeting, i.e., return an error from a
/// `Option`/`Result`-returning function.
macro_rules! throw {
    ($($tt:tt)*) => {
        do yeet()
    };
}
macro_rules! throw_ub {
    ($($tt:tt)*) => {
        do yeet TerminationInfo::Ub(format!($($tt)*))
    };
}
macro_rules! throw_abort {
    () => {
        do yeet TerminationInfo::Abort
    };
}
macro_rules! throw_machine_stop {
    () => {
        do yeet TerminationInfo::MachineStop
    };
}
macro_rules! throw_memory_leak {
    () => {
        do yeet TerminationInfo::MemoryLeak
    };
}
macro_rules! throw_ill_formed {
    ($($tt:tt)*) => {
        do yeet TerminationInfo::IllFormed(format!($($tt)*))
    };
}
macro_rules! throw_deadlock {
    () => {
        do yeet TerminationInfo::Deadlock
    };
}
/// We leave the encoding of the non-determinism monad opaque.
pub use libspecr::Nondet;
pub type NdResult<T = ()> = libspecr::NdResult<T, TerminationInfo>;
