# MiniRust prelude

Across all files in this repository, we assume some definitions to always be in scope.

```rust
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
pub type Result<T=()> = std::result::Result<T, TerminationInfo>;

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
        do yeet ()
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
    }
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
pub type NdResult<T=()> = libspecr::NdResult<T, TerminationInfo>;
```
