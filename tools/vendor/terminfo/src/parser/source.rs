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

use crate::parser::util::unescape;
use crate::parser::util::{end, is_eol, is_ws, ws};
use crate::parser::util::{is_printable_no_comma, is_printable_no_control, is_printable_no_pipe};
use nom::branch::alt;
use nom::bytes::streaming::{tag, take, take_until, take_while};
use nom::character::{is_digit, streaming::line_ending as eol};
use nom::combinator::{complete, map, map_res, opt};
use nom::error::{make_error, ErrorKind};
use nom::sequence::terminated;
use nom::IResult;
use std::borrow::Cow;
use std::str;

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Item<'a> {
	Comment(&'a str),

	Definition { name: &'a str, aliases: Vec<&'a str>, description: &'a str },

	True(&'a str),
	Number(&'a str, i16),
	String(&'a str, Cow<'a, [u8]>),
	Disable(&'a str),
}

pub fn parse(input: &[u8]) -> IResult<&[u8], Item> {
	alt((comment, definition, disable, entry))(input)
}

fn comment(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = tag("#")(input)?;
	let (input, content) = map_res(terminated(take_until("\n"), tag("\n")), str::from_utf8)(input)?;
	let (input, _) = opt(complete(take_while(is_eol)))(input)?;

	Ok((input, Item::Comment(content.trim())))
}

fn definition(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, name) =
		map(take_while(is_printable_no_pipe), |n| unsafe { str::from_utf8_unchecked(n) })(input)?;

	let (input, _) = tag("|")(input)?;

	let (input, content) =
		map(take_while(is_printable_no_comma), |n| unsafe { str::from_utf8_unchecked(n) })(input)?;

	let (input, _) = tag(",")(input)?;

	let (input, _) = take_while(is_ws)(input)?;

	let (input, _) = eol(input)?;
	let (input, _) = opt(complete(take_while(is_eol)))(input)?;

	Ok((input, {
		let mut aliases = content.split(|c| c == '|').map(|n| n.trim()).collect::<Vec<_>>();

		Item::Definition { name, description: aliases.pop().unwrap(), aliases }
	}))
}

fn disable(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = ws(input)?;
	let (input, _) = take_while(is_ws)(input)?;
	let (input, _) = tag("@")(input)?;

	let (input, name) =
		map(take_while(is_printable_no_control), |n| unsafe { str::from_utf8_unchecked(n) })(
			input,
		)?;

	let (input, _) = tag(",")(input)?;
	let (input, _) = take_while(is_ws)(input)?;
	let (input, _) = end(input)?;
	let (input, _) = opt(complete(take_while(is_eol)))(input)?;

	Ok((input, Item::Disable(name)))
}

fn entry(input: &[u8]) -> IResult<&[u8], Item> {
	let (input, _) = ws(input)?;
	let (input, _) = take_while(is_ws)(input)?;

	let (input, name) =
		map(take_while(is_printable_no_control), |n| unsafe { str::from_utf8_unchecked(n) })(
			input,
		)?;

	let (input, c) = take(1_usize)(input)?;
	let (input, value) = match c {
		b"," => (input, Item::True(name)),

		b"#" => {
			let (input, value) =
				map(take_while(is_digit), |n| unsafe { str::from_utf8_unchecked(n) })(input)?;

			let (input, _) = tag(",")(input)?;

			(input, Item::Number(name, value.parse().unwrap()))
		}

		b"=" => {
			let (input, value) = take_while(is_printable_no_comma)(input)?;

			let (input, _) = tag(",")(input)?;

			(input, Item::String(name, unescape(value)))
		}

		_ => Err(nom::Err::Error(make_error(input, ErrorKind::Switch)))?,
	};

	let (input, _) = take_while(is_ws)(input)?;
	let (input, _) = end(input)?;
	let (input, _) = opt(complete(take_while(is_eol)))(input)?;

	Ok((input, value))
}

#[cfg(test)]
mod test {
	use super::*;

	use std::fs::File;
	use std::io::Read;

	#[test]
	fn parsing() {
		let mut file = File::open("tests/xterm.terminfo").unwrap();
		let mut buffer = Vec::new();
		file.read_to_end(&mut buffer).unwrap();

		let mut input = &buffer[..];

		while !input.is_empty() {
			match parse(input) {
				Ok((rest, _)) => input = rest,

				Err(::nom::Err::Incomplete(_)) => panic!("incomplete"),

				Err(err) => panic!("parsing: {:?}", err),
			}
		}
	}
}
