//            DO WHAT THE FUCK YOU WANT TO PUBLIC LICENSE
//                    Version 2, December 2004
//
// Copyleft (ↄ) meh. <meh@schizofreni.co> | http://meh.schizofreni.co
//
// Everyone is permitted to copy and distribute verbatim or modified
// copies of this license document, and changing it is allowed as long
// as the name is changed.
//
//            DO WHAT THE FUCK YOU WANT TO PUBLIC LICENSE
//   TERMS AND CONDITIONS FOR COPYING, DISTRIBUTION AND MODIFICATION
//
//  0. You just DO WHAT THE FUCK YOU WANT TO.

use std::error;
use std::fmt;
use std::io;

#[derive(Debug)]
pub enum Error {
	/// IO error.
	Io(io::Error),

	/// Database not found.
	NotFound,

	/// Parsing error.
	Parse,

	/// Expansion error.
	Expand(Expand),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Expand {
	/// The expansion string is invalid.
	Invalid,

	/// There was a type mismatch while expanding.
	TypeMismatch,

	/// The stack underflowed while expanding.
	StackUnderflow,
}

pub type Result<T> = ::std::result::Result<T, Error>;

impl From<io::Error> for Error {
	fn from(value: io::Error) -> Self {
		Error::Io(value)
	}
}

impl From<Expand> for Error {
	fn from(value: Expand) -> Self {
		Error::Expand(value)
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> ::std::result::Result<(), fmt::Error> {
		match *self {
			Error::Io(ref err) => err.fmt(f),

			Error::NotFound => f.write_str("Capability database not found."),

			Error::Parse => f.write_str("Failed to parse capability database."),

			Error::Expand(ref err) => match *err {
				Expand::Invalid => f.write_str("The expansion string is invalid."),

				Expand::StackUnderflow => f.write_str("Not enough elements on the stack."),

				Expand::TypeMismatch => f.write_str("Type mismatch."),
			},
		}
	}
}

impl error::Error for Error {}
