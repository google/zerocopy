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

use nom::branch::alt;
use nom::bytes::streaming::{tag, take, take_until};
use nom::combinator::{complete, cond, map, map_opt, map_parser, opt};
use nom::multi::count;
use nom::number::streaming::{le_i16, le_i32};
use nom::IResult;
use std::str;

use crate::capability::Value;
use crate::names;

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Database<'a> {
	names: &'a [u8],
	standard: Standard<'a>,
	extended: Option<Extended<'a>>,
}

impl<'a> From<Database<'a>> for crate::Database {
	fn from(source: Database<'a>) -> Self {
		let mut names = source
			.names
			.split(|&c| c == b'|')
			.map(|s| unsafe { str::from_utf8_unchecked(s) })
			.map(|s| s.trim())
			.collect::<Vec<_>>();

		let mut database = crate::Database::new();

		database.name(names.remove(0));
		names.pop().map(|name| database.description(name));
		database.aliases(names);

		for (index, _) in source.standard.booleans.iter().enumerate().filter(|&(_, &value)| value) {
			if let Some(&name) = names::BOOLEAN.get(&(index as u16)) {
				database.raw(name, Value::True);
			}
		}

		for (index, &value) in source.standard.numbers.iter().enumerate().filter(|&(_, &n)| n >= 0)
		{
			if let Some(&name) = names::NUMBER.get(&(index as u16)) {
				database.raw(name, Value::Number(value));
			}
		}

		for (index, &offset) in source.standard.strings.iter().enumerate().filter(|&(_, &n)| n >= 0)
		{
			if let Some(&name) = names::STRING.get(&(index as u16)) {
				let string = &source.standard.table[offset as usize..];
				let edge = string.iter().position(|&c| c == 0).unwrap();

				database.raw(name, Value::String(Vec::from(&string[..edge])));
			}
		}

		if let Some(extended) = source.extended {
			let names = extended
				.table
				.split(|&c| c == 0)
				.skip(extended.strings.iter().cloned().filter(|&n| n >= 0).count())
				.map(|s| unsafe { str::from_utf8_unchecked(s) })
				.collect::<Vec<_>>();

			for (index, _) in extended.booleans.iter().enumerate().filter(|&(_, &value)| value) {
				database.raw(names[index], Value::True);
			}

			for (index, &value) in extended.numbers.iter().enumerate().filter(|&(_, &n)| n >= 0) {
				database.raw(names[extended.booleans.len() + index], Value::Number(value));
			}

			for (index, &offset) in extended.strings.iter().enumerate().filter(|&(_, &n)| n >= 0) {
				let string = &extended.table[offset as usize..];
				let edge = string.iter().position(|&c| c == 0).unwrap();

				database.raw(
					names[extended.booleans.len() + extended.numbers.len() + index],
					Value::String(Vec::from(&string[..edge])),
				);
			}
		}

		database.build().unwrap()
	}
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Standard<'a> {
	booleans: Vec<bool>,
	numbers: Vec<i32>,
	strings: Vec<i32>,
	table: &'a [u8],
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub struct Extended<'a> {
	booleans: Vec<bool>,
	numbers: Vec<i32>,
	strings: Vec<i32>,
	names: Vec<i32>,
	table: &'a [u8],
}

fn bit_size(magic: &[u8]) -> usize {
	match magic[1] {
		0x01 => 16,
		0x02 => 32,

		_ => unreachable!("unknown magic number"),
	}
}

pub fn parse(input: &[u8]) -> IResult<&[u8], Database> {
	let (input, magic) = alt((tag([0x1A, 0x01]), tag([0x1E, 0x02])))(input)?;

	let (input, name_size) = size(input)?;
	let (input, bool_count) = size(input)?;
	let (input, num_count) = size(input)?;
	let (input, string_count) = size(input)?;
	let (input, table_size) = size(input)?;

	let (input, names) = map_parser(take(name_size), take_until("\x00"))(input)?;

	let (input, booleans) = count(boolean, bool_count)(input)?;

	let (input, _) = cond((name_size + bool_count) % 2 != 0, take(1_usize))(input)?;

	let (input, numbers) = count(|input| capability(input, bit_size(magic)), num_count)(input)?;

	let (input, strings) = count(|input| capability(input, 16), string_count)(input)?;

	let (input, table) = take(table_size)(input)?;

	let (input, extended) = opt(complete(|input| {
		let (input, _) = cond(table_size % 2 != 0, take(1_usize))(input)?;

		let (input, ext_bool_count) = size(input)?;
		let (input, ext_num_count) = size(input)?;
		let (input, ext_string_count) = size(input)?;
		let (input, _ext_offset_count) = size(input)?;
		let (input, ext_table_size) = size(input)?;

		let (input, booleans) = count(boolean, ext_bool_count)(input)?;

		let (input, _) = cond(ext_bool_count % 2 != 0, take(1_usize))(input)?;

		let (input, numbers) =
			count(|input| capability(input, bit_size(magic)), ext_num_count)(input)?;

		let (input, strings) = count(|input| capability(input, 16), ext_string_count)(input)?;

		let (input, names) = count(
			|input| capability(input, 16),
			ext_bool_count + ext_num_count + ext_string_count,
		)(input)?;

		let (input, table) = take(ext_table_size)(input)?;

		Ok((input, Extended { booleans, numbers, strings, names, table }))
	}))(input)?;

	Ok((
		input,
		Database { names, standard: Standard { booleans, numbers, strings, table }, extended },
	))
}

fn boolean(input: &[u8]) -> IResult<&[u8], bool> {
	alt((map(tag([0]), |_| false), map(tag([1]), |_| true)))(input)
}

fn size(input: &[u8]) -> IResult<&[u8], usize> {
	map_opt(le_i16, |n| match n {
		-1 => Some(0),
		n if n >= 0 => Some(n as usize),
		_ => None,
	})(input)
}

fn capability(input: &[u8], bits: usize) -> IResult<&[u8], i32> {
	alt((
		map_opt(
			cond(bits == 16, map_opt(le_i16, |n| if n >= -2 { Some(n as i32) } else { None })),
			|o| o,
		),
		map_opt(cond(bits == 32, map_opt(le_i32, |n| if n >= -2 { Some(n) } else { None })), |o| o),
	))(input)
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::capability as cap;
	use std::fs::File;
	use std::io::Read;
	use std::path::Path;

	fn load<P: AsRef<Path>, F: FnOnce(crate::Database)>(path: P, f: F) {
		let mut file = File::open(path).unwrap();
		let mut buffer = Vec::new();
		file.read_to_end(&mut buffer).unwrap();

		f(parse(&buffer).unwrap().1.into())
	}

	#[test]
	fn name() {
		load("tests/cancer-256color", |db| assert_eq!("cancer-256color", db.name()));
	}

	#[test]
	fn aliases() {
		load("tests/st-256color", |db| assert_eq!(vec!["stterm-256color"], db.aliases()));
	}

	#[test]
	fn description() {
		load("tests/cancer-256color", |db| {
			assert_eq!("terminal cancer with 256 colors", db.description())
		});
	}

	#[test]
	fn standard() {
		load("tests/st-256color", |db| {
			assert_eq!(Some(cap::Columns(80)), db.get::<cap::Columns>());
			assert_eq!(Some(cap::AutoRightMargin(true)), db.get::<cap::AutoRightMargin>());
			assert_eq!(Some(cap::AutoLeftMargin(false)), db.get::<cap::AutoLeftMargin>());
		});
	}

	#[test]
	fn extended() {
		load("tests/cancer-256color", |db| {
			assert_eq!(Some(&cap::Value::True), db.raw("Ts"));
			assert_eq!(Some(&cap::Value::True), db.raw("AX"));
			assert_eq!(Some(&cap::Value::String(b"\x1B[2 q".to_vec())), db.raw("Se"));
		});
	}

	#[test]
	fn bigger_numbers() {
		load("tests/xterm-256color", |db| assert_eq!("xterm-256color", db.name()));
	}
}
