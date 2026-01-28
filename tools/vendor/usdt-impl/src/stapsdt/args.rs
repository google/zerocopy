// Copyright 2024 Aapo Alasuutari
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Helpers for generating GNU Assembler format for use in STAPSDT probes.

use crate::DataType;
use dtrace_parser::{BitWidth, DataType as NativeDataType, Integer, Sign};

/// Convert an Integer type and a register index into a GNU Assembler operation
/// that reads the integer's value from the correct register. Effectively this
/// means generating a string like `%REG` where `REG` is the register that the
/// data is located in.
fn integer_to_asm_op(integer: &Integer, reg_index: u8) -> &'static str {
    // See common.rs for note on argument passing and maximum supported
    // argument count.
    assert!(
        reg_index <= 5,
        "Up to 6 probe arguments are currently supported"
    );
    if cfg!(target_arch = "x86_64") {
        match (integer.width, reg_index) {
            (BitWidth::Bit8, 0) => "%dil",
            (BitWidth::Bit16, 0) => "%di",
            (BitWidth::Bit32, 0) => "%edi",
            (BitWidth::Bit64, 0) => "%rdi",
            (BitWidth::Bit8, 1) => "%sil",
            (BitWidth::Bit16, 1) => "%si",
            (BitWidth::Bit32, 1) => "%esi",
            (BitWidth::Bit64, 1) => "%rsi",
            (BitWidth::Bit8, 2) => "%dl",
            (BitWidth::Bit16, 2) => "%dx",
            (BitWidth::Bit32, 2) => "%edx",
            (BitWidth::Bit64, 2) => "%rdx",
            (BitWidth::Bit8, 3) => "%cl",
            (BitWidth::Bit16, 3) => "%cx",
            (BitWidth::Bit32, 3) => "%ecx",
            (BitWidth::Bit64, 3) => "%rcx",
            (BitWidth::Bit8, 4) => "%r8b",
            (BitWidth::Bit16, 4) => "%r8w",
            (BitWidth::Bit32, 4) => "%r8d",
            (BitWidth::Bit64, 4) => "%r8",
            (BitWidth::Bit8, 5) => "%r9b",
            (BitWidth::Bit16, 5) => "%r9w",
            (BitWidth::Bit32, 5) => "%r9d",
            (BitWidth::Bit64, 5) => "%r9",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 0) => "%edi",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 0) => "%rdi",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 1) => "%esi",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 1) => "%rsi",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 2) => "%edx",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 2) => "%rdx",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 3) => "%ecx",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 3) => "%rcx",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 4) => "%e8",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 4) => "%r8",
            #[cfg(target_pointer_width = "32")]
            (BitWidth::Pointer, 5) => "%e9",
            #[cfg(target_pointer_width = "64")]
            (BitWidth::Pointer, 5) => "%r9",
            #[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
            (BitWidth::Pointer, _) => compile_error!("Unsupported pointer width"),
            _ => unreachable!(),
        }
    } else if cfg!(target_arch = "aarch64") {
        // GNU Assembly syntax for SystemTap only uses the extended register
        // for some reason.
        match reg_index {
            0 => "x0",
            1 => "x1",
            2 => "x2",
            3 => "x3",
            4 => "x4",
            5 => "x5",
            _ => unreachable!(),
        }
    } else {
        unreachable!("Unsupported Linux target architecture")
    }
}

/// Convert an Integer type into its STAPSDT probe arguments definition
/// signedness and size value as a String.
fn integer_to_arg_size(integer: &Integer) -> &'static str {
    match integer.width {
        BitWidth::Bit8 => match integer.sign {
            Sign::Unsigned => "1",
            _ => "-1",
        },
        BitWidth::Bit16 => match integer.sign {
            Sign::Unsigned => "2",
            _ => "-2",
        },
        BitWidth::Bit32 => match integer.sign {
            Sign::Unsigned => "4",
            _ => "-4",
        },
        BitWidth::Bit64 => match integer.sign {
            Sign::Unsigned => "8",
            _ => "-8",
        },
        #[cfg(target_pointer_width = "32")]
        BitWidth::Pointer => "4",
        #[cfg(target_pointer_width = "64")]
        BitWidth::Pointer => "8",
        #[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
        BitWidth::Pointer => compile_error!("Unsupported pointer width"),
    }
}

const POINTER: Integer = Integer {
    sign: Sign::Unsigned,
    width: BitWidth::Pointer,
};

const UNIQUE_ID: Integer = Integer {
    sign: Sign::Unsigned,
    width: BitWidth::Bit64,
};

/// Convert a type and register index to its GNU Assembler operation as a
/// String.
fn native_data_type_to_asm_op(typ: &NativeDataType, reg_index: u8) -> String {
    match typ {
        NativeDataType::Integer(int) => integer_to_asm_op(int, reg_index).into(),
        // Integer pointers are dereferenced by wrapping the pointer assembly
        // into parentheses.
        NativeDataType::Pointer(_) => format!("({})", integer_to_asm_op(&POINTER, reg_index)),
        NativeDataType::String => integer_to_asm_op(&POINTER, reg_index).into(),
    }
}

/// Convert a type to its GNU Assembler size representation as a string.
fn native_data_type_to_arg_size(typ: &NativeDataType) -> &'static str {
    match typ {
        NativeDataType::Integer(int) => integer_to_arg_size(int),
        NativeDataType::Pointer(_) | NativeDataType::String => integer_to_arg_size(&POINTER),
        // Note: If NativeDataType::Float becomes supported, it will need an
        // "f" suffix in the type, eg. `4f` or `8f`.
    }
}

/// Convert a DataType and register index to its GNU Assembler operation as a
/// String.
fn data_type_to_asm_op(typ: &DataType, reg_index: u8) -> String {
    match typ {
        DataType::Native(ty) => native_data_type_to_asm_op(ty, reg_index),
        DataType::UniqueId => integer_to_asm_op(&UNIQUE_ID, reg_index).into(),
        DataType::Serializable(_) => integer_to_asm_op(&POINTER, reg_index).into(),
    }
}

/// Convert a DataType to its STAPSDT probe argument size representation as a
/// String.
fn data_type_to_arg_size(typ: &DataType) -> &'static str {
    match typ {
        DataType::Native(ty) => native_data_type_to_arg_size(ty),
        DataType::UniqueId => integer_to_arg_size(&UNIQUE_ID),
        DataType::Serializable(_) => integer_to_arg_size(&POINTER),
    }
}

/// ## Format a STAPSDT probe argument into the SystemTap argument format.
/// Source: https://sourceware.org/systemtap/wiki/UserSpaceProbeImplementation
///
/// ### Summary
///
/// Argument format is `Nf@OP`, N is an optional `-` to signal signedness
/// followed by one of `{1,2,4,8}` for bit width, `f` is an optional marker
/// for floating point values, @ is a separator, and OP is the
/// "actual assembly operand". The assembly operand is given in the GNU
/// Assembler format. See
/// https://en.wikibooks.org/wiki/X86_Assembly/GNU_assembly_syntax
/// for details.
///
/// ### Examples
///
/// 1. Read a u64 from RDI: `8@%rdi`.
/// 2. Read an i32 through a pointer in RSI: `-4@(%rsi)`.
/// 3. Read an f64 through a pointer in RDI: `8f@(%rdi)`.
///    (Not sure if `-` should be added.)
/// 4. Read a u64 through a pointer with an offset: `8%-4(%rdi)`.
pub(crate) fn format_argument((reg_index, typ): (usize, &DataType)) -> String {
    format!(
        "{}@{}",
        data_type_to_arg_size(typ),
        data_type_to_asm_op(typ, u8::try_from(reg_index).unwrap())
    )
}
