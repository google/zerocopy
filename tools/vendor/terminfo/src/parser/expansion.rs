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

use crate::parser::util::number;
use nom::branch::alt;
use nom::bytes::complete;
use nom::bytes::streaming::{tag, take, take_while};
use nom::character::is_digit;
use nom::character::streaming::one_of;
use nom::combinator::{map, opt, value};
use nom::error::{make_error, ErrorKind};
use nom::IResult;

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Item<'a> {
	String(&'a [u8]),
	Constant(Constant),
	Variable(Variable),
	Operation(Operation),
	Conditional(Conditional),
	Print(Print),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Constant {
	Character(u8),
	Integer(i32),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Variable {
	Length,
	Push(u8),
	Set(bool, u8),
	Get(bool, u8),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Operation {
	Increment,
	Unary(Unary),
	Binary(Binary),
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Unary {
	Not,
	NOT,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Binary {
	Add,
	Subtract,
	Multiply,
	Divide,
	Remainder,

	AND,
	OR,
	XOR,

	And,
	Or,

	Equal,
	Greater,
	Lesser,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Conditional {
	If,
	Then,
	Else,
	End,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub struct Print {
	pub flags: Flags,
	pub format: Format,
}

#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Format {
	Chr,
	Uni,
	Str,
	Dec,
	Oct,
	Hex,
	HEX,
}

#[derive(Eq, PartialEq, Copy, Clone, Default, Debug)]
pub struct Flags {
	pub width: usize,
	pub precision: usize,

	pub alternate: bool,
	pub left: bool,
	pub sign: bool,
	pub space: bool,
}

pub fn parse(input: &[u8]) -> IResult<&[u8], Item> {
	alt((expansion, string))(input)
}

fn string(input: &[u8]) -> IResult<&[u8], Item> {
	map(complete::take_till(|b| b == b'%'), Item::String)(input)
}

fn expansion(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = tag("%")(input)?;
	let (input, item) = alt((percent, constant, variable, operation, conditional, print))(input)?;

	Ok((input, item))
}

fn percent(input: &[u8]) -> IResult<&[u8], Item> {
	value(Item::String(b"%"), tag("%"))(input)
}

fn constant(input: &[u8]) -> IResult<&[u8], Item> {
	alt((constant_char, constant_integer))(input)
}

fn constant_char(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = tag("'")(input)?;
	let (input, ch) = take(1_usize)(input)?;
	let (input, _) = tag("'")(input)?;

	Ok((input, Item::Constant(Constant::Character(ch[0]))))
}

fn constant_integer(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = tag("{")(input)?;
	let (input, digit) = take_while(is_digit)(input)?;
	let (input, _) = tag("}")(input)?;

	Ok((input, Item::Constant(Constant::Integer(number(digit)))))
}

fn variable(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, c) = take(1_usize)(input)?;
	match c {
		b"l" => Ok((input, Item::Variable(Variable::Length))),

		b"p" => map(one_of("123456789"), |n| Item::Variable(Variable::Push(n as u8 - b'1')))(input),

		b"P" => alt((
			map(one_of("abcdefghijklmnopqrstuvwxyz"), |n| {
				Item::Variable(Variable::Set(true, n as u8 - b'a'))
			}),
			map(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ"), |n| {
				Item::Variable(Variable::Set(false, n as u8 - b'A'))
			}),
		))(input),

		b"g" => alt((
			map(one_of("abcdefghijklmnopqrstuvwxyz"), |n| {
				Item::Variable(Variable::Get(true, n as u8 - b'a'))
			}),
			map(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ"), |n| {
				Item::Variable(Variable::Get(false, n as u8 - b'A'))
			}),
		))(input),

		_ => Err(nom::Err::Error(make_error(input, ErrorKind::Switch))),
	}
}

fn operation(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, c) = take(1_usize)(input)?;
	match c {
		b"+" => Ok((input, Item::Operation(Operation::Binary(Binary::Add)))),
		b"-" => Ok((input, Item::Operation(Operation::Binary(Binary::Subtract)))),
		b"*" => Ok((input, Item::Operation(Operation::Binary(Binary::Multiply)))),
		b"/" => Ok((input, Item::Operation(Operation::Binary(Binary::Divide)))),
		b"m" => Ok((input, Item::Operation(Operation::Binary(Binary::Remainder)))),
		b"i" => Ok((input, Item::Operation(Operation::Increment))),

		b"&" => Ok((input, Item::Operation(Operation::Binary(Binary::AND)))),
		b"|" => Ok((input, Item::Operation(Operation::Binary(Binary::OR)))),
		b"^" => Ok((input, Item::Operation(Operation::Binary(Binary::XOR)))),
		b"~" => Ok((input, Item::Operation(Operation::Unary(Unary::NOT)))),

		b"A" => Ok((input, Item::Operation(Operation::Binary(Binary::And)))),
		b"O" => Ok((input, Item::Operation(Operation::Binary(Binary::Or)))),
		b"!" => Ok((input, Item::Operation(Operation::Unary(Unary::Not)))),

		b"=" => Ok((input, Item::Operation(Operation::Binary(Binary::Equal)))),
		b">" => Ok((input, Item::Operation(Operation::Binary(Binary::Greater)))),
		b"<" => Ok((input, Item::Operation(Operation::Binary(Binary::Lesser)))),

		_ => Err(nom::Err::Error(make_error(input, ErrorKind::Switch))),
	}
}

fn conditional(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, c) = take(1_usize)(input)?;
	match c {
		b"?" => Ok((input, Item::Conditional(Conditional::If))),
		b"t" => Ok((input, Item::Conditional(Conditional::Then))),
		b"e" => Ok((input, Item::Conditional(Conditional::Else))),
		b";" => Ok((input, Item::Conditional(Conditional::End))),

		_ => Err(nom::Err::Error(make_error(input, ErrorKind::Switch))),
	}
}

fn print(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = opt(tag(":"))(input)?;

	let (input, flags) = take_while(is_flag)(input)?;
	let (input, width) = opt(take_while(is_digit))(input)?;
	let (input, precision) = opt(|input| {
		let (input, _) = tag(".")(input)?;
		let (input, amount) = take_while(is_digit)(input)?;

		Ok((input, amount))
	})(input)?;

	let (input, format) = one_of("doxXsc")(input)?;

	Ok((
		input,
		Item::Print(Print {
			flags: Flags {
				width: number(width.unwrap_or(b"0")) as usize,
				precision: number(precision.unwrap_or(b"0")) as usize,

				alternate: flags.contains(&b'#'),
				left: flags.contains(&b'-'),
				sign: flags.contains(&b'+'),
				space: flags.contains(&b' '),
			},

			format: match format {
				'd' => Format::Dec,
				'o' => Format::Oct,
				'x' => Format::Hex,
				'X' => Format::HEX,
				's' => Format::Str,
				'c' => Format::Chr,
				'u' => Format::Uni,
				_ => unreachable!(),
			},
		}),
	))
}

fn is_flag(i: u8) -> bool {
	i == b' ' || i == b'-' || i == b'+' || i == b'#'
}

#[cfg(test)]
mod test {
	use super::*;

	macro_rules! test {
		($string:expr => $($item:tt)*) => (
			assert_eq!(Item::$($item)*, parse($string).unwrap().1);
		)
	}

	#[test]
	fn string() {
		test!(b"foobar" =>
			String(b"foobar"));
	}

	#[test]
	fn percent() {
		test!(b"%%" =>
			String(b"%"));
	}

	#[test]
	fn constant() {
		test!(b"%{24}" =>
			Constant(Constant::Integer(24)));

		test!(b"%'a'" =>
			Constant(Constant::Character(b'a')));
	}

	#[test]
	fn variable() {
		test!(b"%l" =>
			Variable(Variable::Length));

		test!(b"%p1" =>
			Variable(Variable::Push(0)));

		test!(b"%Pa" =>
			Variable(Variable::Set(true, 0)));

		test!(b"%PA" =>
			Variable(Variable::Set(false, 0)));

		test!(b"%ga" =>
			Variable(Variable::Get(true, 0)));

		test!(b"%gA" =>
			Variable(Variable::Get(false, 0)));
	}

	#[test]
	fn operation() {
		test!(b"%i" =>
			Operation(Operation::Increment));

		test!(b"%+" =>
			Operation(Operation::Binary(Binary::Add)));

		test!(b"%-" =>
			Operation(Operation::Binary(Binary::Subtract)));

		test!(b"%*" =>
			Operation(Operation::Binary(Binary::Multiply)));

		test!(b"%/" =>
			Operation(Operation::Binary(Binary::Divide)));

		test!(b"%m" =>
			Operation(Operation::Binary(Binary::Remainder)));

		test!(b"%&" =>
			Operation(Operation::Binary(Binary::AND)));

		test!(b"%|" =>
			Operation(Operation::Binary(Binary::OR)));

		test!(b"%^" =>
			Operation(Operation::Binary(Binary::XOR)));

		test!(b"%~" =>
			Operation(Operation::Unary(Unary::NOT)));

		test!(b"%A" =>
			Operation(Operation::Binary(Binary::And)));

		test!(b"%O" =>
			Operation(Operation::Binary(Binary::Or)));

		test!(b"%!" =>
			Operation(Operation::Unary(Unary::Not)));

		test!(b"%=" =>
			Operation(Operation::Binary(Binary::Equal)));

		test!(b"%>" =>
			Operation(Operation::Binary(Binary::Greater)));

		test!(b"%<" =>
			Operation(Operation::Binary(Binary::Lesser)));
	}

	#[test]
	fn conditional() {
		test!(b"%?" =>
			Conditional(Conditional::If));

		test!(b"%t" =>
			Conditional(Conditional::Then));

		test!(b"%e" =>
			Conditional(Conditional::Else));

		test!(b"%;" =>
			Conditional(Conditional::End));
	}

	#[test]
	fn print() {
		test!(b"%s" =>
			Print(Print { flags: Default::default(), format: Format::Str }));

		test!(b"% 30s" =>
			Print(Print { flags: Flags { width: 30, space: true, .. Default::default() }, format: Format::Str }));

		test!(b"%:-3.4d" =>
			Print(Print { flags: Flags { width: 3, precision: 4, left: true, .. Default::default() }, format: Format::Dec }));
	}
}
