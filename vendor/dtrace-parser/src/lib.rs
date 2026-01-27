//! A small library for parsing DTrace provider files.

// Copyright 2021 Oxide Computer Company
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

use pest::iterators::{Pair, Pairs};
use pest_derive::Parser;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::fs;
use std::path::Path;
use thiserror::Error;

type PestError = pest::error::Error<Rule>;

/// Type representing errors that occur when parsing a D file.
#[derive(Error, Debug)]
pub enum DTraceError {
    #[error("Unexpected token type, expected {expected:?}, found {found:?}")]
    UnexpectedToken { expected: Rule, found: Rule },
    #[error("This set of pairs contains no tokens")]
    EmptyPairsIterator,
    #[error("Provider and probe name pairs must be unique: duplicated \"{0:?}\"")]
    DuplicateProbeName((String, String)),
    #[error("The provider name \"{0}\" is invalid")]
    InvalidProviderName(String),
    #[error("The probe name \"{0}\" is invalid")]
    InvalidProbeName(String),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error("Input is not a valid DTrace provider definition:\n{0}")]
    ParseError(#[from] Box<PestError>),
}

#[derive(Parser, Debug)]
#[grammar = "dtrace.pest"]
struct DTraceParser;

// Helper which verifies that the given `pest::Pair` conforms to the expected grammar rule.
fn expect_token(pair: &Pair<'_, Rule>, rule: Rule) -> Result<(), DTraceError> {
    if pair.as_rule() == rule {
        Ok(())
    } else {
        Err(DTraceError::UnexpectedToken {
            expected: rule,
            found: pair.as_rule(),
        })
    }
}

/// The bit-width of an integer data type
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BitWidth {
    Bit8,
    Bit16,
    Bit32,
    Bit64,
    /// The width of the native pointer type.
    Pointer,
}

/// The signed-ness of an integer data type
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sign {
    Signed,
    Unsigned,
}

/// An integer data type
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Integer {
    pub sign: Sign,
    pub width: BitWidth,
}

const RUST_TYPE_PREFIX: &str = "::std::os::raw::c_";

impl Integer {
    fn width_to_c_str(&self) -> &'static str {
        match self.width {
            BitWidth::Bit8 => "8",
            BitWidth::Bit16 => "16",
            BitWidth::Bit32 => "32",
            BitWidth::Bit64 => "64",
            #[cfg(target_pointer_width = "32")]
            BitWidth::Pointer => "32",
            #[cfg(target_pointer_width = "64")]
            BitWidth::Pointer => "64",
            #[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
            BitWidth::Pointer => compile_error!("Unsupported pointer width"),
        }
    }

    pub fn to_c_type(&self) -> String {
        let prefix = match self.sign {
            Sign::Unsigned => "u",
            _ => "",
        };
        format!("{prefix}int{}_t", self.width_to_c_str())
    }

    pub fn to_rust_ffi_type(&self) -> String {
        let ty = match (self.sign, self.width) {
            (Sign::Unsigned, BitWidth::Bit8) => "uchar",
            (Sign::Unsigned, BitWidth::Bit16) => "ushort",
            (Sign::Unsigned, BitWidth::Bit32) => "uint",
            (Sign::Unsigned, BitWidth::Bit64) => "ulonglong",
            #[cfg(target_pointer_width = "32")]
            (Sign::Unsigned, BitWidth::Pointer) => "uint",
            #[cfg(target_pointer_width = "64")]
            (Sign::Unsigned, BitWidth::Pointer) => "ulonglong",
            (Sign::Signed, BitWidth::Bit8) => "schar",
            (Sign::Signed, BitWidth::Bit16) => "short",
            (Sign::Signed, BitWidth::Bit32) => "int",
            (Sign::Signed, BitWidth::Bit64) => "longlong",
            #[cfg(target_pointer_width = "32")]
            (Sign::Signed, BitWidth::Pointer) => "int",
            #[cfg(target_pointer_width = "64")]
            (Sign::Signed, BitWidth::Pointer) => "longlong",

            #[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
            (_, BitWidth::Pointer) => compile_error!("Unsupported pointer width"),
        };
        format!("{RUST_TYPE_PREFIX}{ty}")
    }

    fn width_to_str(&self) -> &'static str {
        match self.width {
            BitWidth::Pointer => "size",
            _ => self.width_to_c_str(),
        }
    }

    pub fn to_rust_type(&self) -> String {
        let prefix = match self.sign {
            Sign::Signed => "i",
            Sign::Unsigned => "u",
        };
        format!("{prefix}{}", self.width_to_str())
    }
}

/// Represents the data type of a single probe argument.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DataType {
    Integer(Integer),
    Pointer(Integer),
    String,
}

impl From<Pair<'_, Rule>> for Integer {
    fn from(integer_type: Pair<'_, Rule>) -> Integer {
        let sign = match integer_type.as_rule() {
            Rule::SIGNED_INT => Sign::Signed,
            Rule::UNSIGNED_INT => Sign::Unsigned,
            _ => unreachable!("Expected a signed or unsigned integer"),
        };
        let width = match integer_type.into_inner().as_str() {
            "8" => BitWidth::Bit8,
            "16" => BitWidth::Bit16,
            "32" => BitWidth::Bit32,
            "64" => BitWidth::Bit64,
            "ptr" => BitWidth::Pointer,
            _ => unreachable!("Expected a bit width"),
        };
        Integer { sign, width }
    }
}

impl TryFrom<&Pair<'_, Rule>> for DataType {
    type Error = DTraceError;

    fn try_from(pair: &Pair<'_, Rule>) -> Result<DataType, Self::Error> {
        expect_token(pair, Rule::DATA_TYPE)?;
        let inner = pair
            .clone()
            .into_inner()
            .next()
            .expect("Data type token is expected to contain a concrete type");
        let typ = match inner.as_rule() {
            Rule::INTEGER => {
                let integer = pair
                    .clone()
                    .into_inner()
                    .next()
                    .expect("Expected a signed or unsigned integral type");
                assert!(matches!(integer.as_rule(), Rule::INTEGER));
                DataType::Integer(Integer::from(
                    integer
                        .clone()
                        .into_inner()
                        .next()
                        .expect("Expected an integral type"),
                ))
            }
            Rule::INTEGER_POINTER => {
                let pointer = pair
                    .clone()
                    .into_inner()
                    .next()
                    .expect("Expected a pointer to a signed or unsigned integral type");
                assert!(matches!(pointer.as_rule(), Rule::INTEGER_POINTER));
                let mut parts = pointer.clone().into_inner();
                let integer = parts
                    .next()
                    .expect("Expected a signed or unsigned integral type");
                let star = parts.next().expect("Expected a literal `*`");
                assert_eq!(star.as_rule(), Rule::STAR);
                DataType::Pointer(Integer::from(
                    integer
                        .clone()
                        .into_inner()
                        .next()
                        .expect("Expected an integral type"),
                ))
            }
            Rule::STRING => DataType::String,
            _ => unreachable!("Parsed an unexpected DATA_TYPE token"),
        };
        Ok(typ)
    }
}

impl TryFrom<&Pairs<'_, Rule>> for DataType {
    type Error = DTraceError;

    fn try_from(pairs: &Pairs<'_, Rule>) -> Result<DataType, Self::Error> {
        DataType::try_from(&pairs.peek().ok_or(DTraceError::EmptyPairsIterator)?)
    }
}

impl DataType {
    /// Convert a type into its C type representation as a string
    pub fn to_c_type(&self) -> String {
        match self {
            DataType::Integer(int) => int.to_c_type(),
            DataType::Pointer(int) => format!("{}*", int.to_c_type()),
            DataType::String => String::from("char*"),
        }
    }

    /// Return the Rust FFI type representation of this data type
    pub fn to_rust_ffi_type(&self) -> String {
        match self {
            DataType::Integer(int) => int.to_rust_ffi_type(),
            DataType::Pointer(int) => format!("*const {}", int.to_rust_ffi_type()),
            DataType::String => format!("*const {RUST_TYPE_PREFIX}char"),
        }
    }

    /// Return the native Rust type representation of this data type
    pub fn to_rust_type(&self) -> String {
        match self {
            DataType::Integer(int) => int.to_rust_type(),
            DataType::Pointer(int) => format!("*const {}", int.to_rust_type()),
            DataType::String => String::from("&str"),
        }
    }
}

/// Type representing a single D probe definition within a provider.
#[derive(Clone, Debug, PartialEq)]
pub struct Probe {
    pub name: String,
    pub types: Vec<DataType>,
}

impl TryFrom<&Pair<'_, Rule>> for Probe {
    type Error = DTraceError;

    fn try_from(pair: &Pair<'_, Rule>) -> Result<Self, Self::Error> {
        expect_token(pair, Rule::PROBE)?;
        let mut inner = pair.clone().into_inner();
        expect_token(
            &inner.next().expect("Expected the literal 'probe'"),
            Rule::PROBE_KEY,
        )?;
        let token = inner.next().expect("Expected a probe name");
        let name = token.as_str().to_string();
        if name == "probe" || name == "start" {
            return Err(DTraceError::InvalidProbeName(name));
        }
        expect_token(
            &inner.next().expect("Expected the literal '('"),
            Rule::LEFT_PAREN,
        )?;
        let possibly_argument_list = inner
            .next()
            .expect("Expected an argument list or literal ')'");
        let mut types = Vec::new();
        if expect_token(&possibly_argument_list, Rule::ARGUMENT_LIST).is_ok() {
            let arguments = possibly_argument_list.clone().into_inner();
            for data_type in arguments {
                expect_token(&data_type, Rule::DATA_TYPE)?;
                types.push(DataType::try_from(&data_type)?);
            }
        }
        expect_token(
            &inner.next().expect("Expected a literal ')'"),
            Rule::RIGHT_PAREN,
        )?;
        expect_token(
            &inner.next().expect("Expected a literal ';'"),
            Rule::SEMICOLON,
        )?;
        Ok(Probe { name, types })
    }
}

impl TryFrom<&Pairs<'_, Rule>> for Probe {
    type Error = DTraceError;

    fn try_from(pairs: &Pairs<'_, Rule>) -> Result<Self, Self::Error> {
        Probe::try_from(&pairs.peek().ok_or(DTraceError::EmptyPairsIterator)?)
    }
}

/// Type representing a single DTrace provider and all of its probes.
#[derive(Debug, Clone, PartialEq)]
pub struct Provider {
    pub name: String,
    pub probes: Vec<Probe>,
}

impl TryFrom<&Pair<'_, Rule>> for Provider {
    type Error = DTraceError;

    fn try_from(pair: &Pair<'_, Rule>) -> Result<Self, Self::Error> {
        expect_token(pair, Rule::PROVIDER)?;
        let mut inner = pair.clone().into_inner();
        expect_token(
            &inner.next().expect("Expected the literal 'provider'"),
            Rule::PROVIDER_KEY,
        )?;
        let name = inner
            .next()
            .expect("Expected a provider name")
            .as_str()
            .to_string();
        if name == "provider" {
            return Err(DTraceError::InvalidProviderName(name));
        }
        expect_token(
            &inner.next().expect("Expected the literal '{'"),
            Rule::LEFT_BRACE,
        )?;
        let mut probes = Vec::new();
        let mut possibly_probe = inner
            .next()
            .expect("Expected at least one probe in the provider");
        while expect_token(&possibly_probe, Rule::PROBE).is_ok() {
            probes.push(Probe::try_from(&possibly_probe)?);
            possibly_probe = inner.next().expect("Expected a token");
        }
        expect_token(&possibly_probe, Rule::RIGHT_BRACE)?;
        expect_token(
            &inner.next().expect("Expected a literal ';'"),
            Rule::SEMICOLON,
        )?;
        Ok(Provider { name, probes })
    }
}

impl TryFrom<&Pairs<'_, Rule>> for Provider {
    type Error = DTraceError;

    fn try_from(pairs: &Pairs<'_, Rule>) -> Result<Self, Self::Error> {
        Provider::try_from(&pairs.peek().ok_or(DTraceError::EmptyPairsIterator)?)
    }
}

/// Type representing a single D file and all the providers it defines.
#[derive(Debug, Clone, PartialEq)]
pub struct File {
    name: String,
    providers: Vec<Provider>,
}

impl TryFrom<&Pair<'_, Rule>> for File {
    type Error = DTraceError;

    fn try_from(pair: &Pair<'_, Rule>) -> Result<Self, Self::Error> {
        expect_token(pair, Rule::FILE)?;
        let mut providers = Vec::new();
        let mut names = HashSet::new();
        for item in pair.clone().into_inner() {
            if item.as_rule() == Rule::PROVIDER {
                let provider = Provider::try_from(&item)?;
                for probe in provider.probes.iter() {
                    let name = (provider.name.clone(), probe.name.clone());
                    if names.contains(&name) {
                        return Err(DTraceError::DuplicateProbeName(name));
                    }
                    names.insert(name.clone());
                }
                providers.push(provider);
            }
        }

        Ok(File {
            name: "".to_string(),
            providers,
        })
    }
}

impl TryFrom<&Pairs<'_, Rule>> for File {
    type Error = DTraceError;

    fn try_from(pairs: &Pairs<'_, Rule>) -> Result<Self, Self::Error> {
        File::try_from(&pairs.peek().ok_or(DTraceError::EmptyPairsIterator)?)
    }
}

impl File {
    /// Load and parse a provider from a D file at the given path.
    pub fn from_file(filename: &Path) -> Result<Self, DTraceError> {
        let mut f = File::try_from(fs::read_to_string(filename)?.as_str())?;
        f.name = filename
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        Ok(f)
    }

    /// Return the name of the file.
    pub fn name(&self) -> &String {
        &self.name
    }

    /// Return the list of providers this file defines.
    pub fn providers(&self) -> &Vec<Provider> {
        &self.providers
    }
}

impl TryFrom<&str> for File {
    type Error = DTraceError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        use pest::Parser;
        File::try_from(&DTraceParser::parse(Rule::FILE, s).map_err(|e| {
            Box::new(e.renamed_rules(|rule| match *rule {
                Rule::DATA_TYPE | Rule::BIT_WIDTH => {
                    format!(
                        "{:?}.\n\n{}",
                        *rule,
                        concat!(
                            "Unsupported type, the following are supported:\n",
                            "  - uint8_t\n",
                            "  - uint16_t\n",
                            "  - uint32_t\n",
                            "  - uint64_t\n",
                            "  - int8_t\n",
                            "  - int16_t\n",
                            "  - int32_t\n",
                            "  - int64_t\n",
                            "  - &str\n",
                        )
                    )
                }
                _ => format!("{:?}", rule),
            }))
        })?)
    }
}

#[cfg(test)]
mod tests {
    use super::BitWidth;
    use super::DTraceParser;
    use super::DataType;
    use super::File;
    use super::Integer;
    use super::Probe;
    use super::Provider;
    use super::Rule;
    use super::Sign;
    use super::TryFrom;
    use ::pest::Parser;
    use rstest::{fixture, rstest};

    #[rstest(
        token,
        rule,
        case("probe", Rule::PROBE_KEY),
        case("provider", Rule::PROVIDER_KEY),
        case(";", Rule::SEMICOLON),
        case("(", Rule::LEFT_PAREN),
        case(")", Rule::RIGHT_PAREN),
        case("{", Rule::LEFT_BRACE),
        case("}", Rule::RIGHT_BRACE)
    )]
    fn test_basic_tokens(token: &str, rule: Rule) {
        assert!(DTraceParser::parse(rule, token).is_ok());
    }

    #[test]
    #[should_panic]
    fn test_bad_basic_token() {
        assert!(DTraceParser::parse(Rule::LEFT_BRACE, "x").is_ok())
    }

    #[test]
    fn test_identifier() {
        assert!(DTraceParser::parse(Rule::IDENTIFIER, "foo").is_ok());
        assert!(DTraceParser::parse(Rule::IDENTIFIER, "foo_bar").is_ok());
        assert!(DTraceParser::parse(Rule::IDENTIFIER, "foo9").is_ok());

        assert!(DTraceParser::parse(Rule::IDENTIFIER, "_bar").is_err());
        assert!(DTraceParser::parse(Rule::IDENTIFIER, "").is_err());
        assert!(DTraceParser::parse(Rule::IDENTIFIER, "9foo").is_err());
    }

    #[test]
    fn test_data_types() {
        assert!(DTraceParser::parse(Rule::DATA_TYPE, "uint8_t").is_ok());
        assert!(DTraceParser::parse(Rule::DATA_TYPE, "int").is_err());
        assert!(DTraceParser::parse(Rule::DATA_TYPE, "flaot").is_err());
    }

    #[test]
    fn test_probe() {
        let defn = "probe foo(uint8_t, uint16_t, uint16_t);";
        assert!(DTraceParser::parse(Rule::PROBE, defn).is_ok());
        assert!(DTraceParser::parse(Rule::PROBE, &defn[..defn.len() - 2]).is_err());
    }

    #[test]
    fn test_basic_provider() {
        let defn = r#"
            provider foo {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };"#;
        println!("{:?}", DTraceParser::parse(Rule::FILE, defn));
        assert!(DTraceParser::parse(Rule::FILE, defn).is_ok());
        assert!(DTraceParser::parse(Rule::FILE, &defn[..defn.len() - 2]).is_err());
    }

    #[test]
    fn test_null_provider() {
        let defn = "provider foo { };";
        assert!(DTraceParser::parse(Rule::FILE, defn).is_err());
    }

    #[test]
    fn test_comment_provider() {
        let defn = r#"
            /* Check out this fly provider */
            provider foo {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };"#;
        assert!(DTraceParser::parse(Rule::FILE, defn).is_ok());
    }

    #[test]
    fn test_pragma_provider() {
        let defn = r#"
            #pragma I am a robot
            provider foo {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };
            "#;
        println!("{}", defn);
        assert!(DTraceParser::parse(Rule::FILE, defn).is_ok());
    }

    #[test]
    fn test_two_providers() {
        let defn = r#"
            provider foo {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };
            provider bar {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };
            "#;
        println!("{}", defn);
        assert!(DTraceParser::parse(Rule::FILE, defn).is_ok());
    }

    #[rstest(
        defn,
        data_type,
        case("uint8_t", DataType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit8 })),
        case("uint16_t", DataType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit16 })),
        case("uint32_t", DataType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit32 })),
        case("uint64_t", DataType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit64 })),
        case("uintptr_t", DataType::Integer(Integer { sign: Sign::Unsigned, width: BitWidth::Pointer })),
        case("int8_t", DataType::Integer(Integer { sign: Sign::Signed, width: BitWidth::Bit8 })),
        case("int16_t", DataType::Integer(Integer { sign: Sign::Signed, width: BitWidth::Bit16 })),
        case("int32_t", DataType::Integer(Integer { sign: Sign::Signed, width: BitWidth::Bit32 })),
        case("int64_t", DataType::Integer(Integer { sign: Sign::Signed, width: BitWidth::Bit64 })),
        case("intptr_t", DataType::Integer(Integer { sign: Sign::Signed, width: BitWidth::Pointer })),
        case("uint8_t*", DataType::Pointer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit8})),
        case("uint16_t*", DataType::Pointer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit16})),
        case("uint32_t*", DataType::Pointer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit32})),
        case("uint64_t*", DataType::Pointer(Integer { sign: Sign::Unsigned, width: BitWidth::Bit64})),
        case("int8_t*", DataType::Pointer(Integer { sign: Sign::Signed, width: BitWidth::Bit8})),
        case("int16_t*", DataType::Pointer(Integer { sign: Sign::Signed, width: BitWidth::Bit16})),
        case("int32_t*", DataType::Pointer(Integer { sign: Sign::Signed, width: BitWidth::Bit32})),
        case("int64_t*", DataType::Pointer(Integer { sign: Sign::Signed, width: BitWidth::Bit64})),
        case("char*", DataType::String)
    )]
    fn test_data_type_enum(defn: &str, data_type: DataType) {
        let dtype =
            DataType::try_from(&DTraceParser::parse(Rule::DATA_TYPE, defn).unwrap()).unwrap();
        assert_eq!(dtype, data_type);
    }

    #[test]
    fn test_data_type_conversion() {
        let dtype =
            DataType::try_from(&DTraceParser::parse(Rule::DATA_TYPE, "uint8_t").unwrap()).unwrap();
        assert_eq!(dtype.to_rust_ffi_type(), "::std::os::raw::c_uchar");
    }

    #[fixture]
    fn probe_data() -> (String, String) {
        let provider = String::from("foo");
        let probe = String::from("probe baz(char*, uint16_t, uint8_t*);");
        (provider, probe)
    }

    #[fixture]
    fn probe(probe_data: (String, String)) -> (String, Probe) {
        (
            probe_data.0,
            Probe::try_from(&DTraceParser::parse(Rule::PROBE, &probe_data.1).unwrap()).unwrap(),
        )
    }

    #[rstest]
    fn test_probe_struct_parse(probe_data: (String, String)) {
        let (_, probe) = probe_data;
        let probe = Probe::try_from(&DTraceParser::parse(Rule::PROBE, &probe).unwrap())
            .expect("Could not parse probe tokens");
        assert_eq!(probe.name, "baz");
        assert_eq!(
            probe.types,
            &[
                DataType::String,
                DataType::Integer(Integer {
                    sign: Sign::Unsigned,
                    width: BitWidth::Bit16,
                }),
                DataType::Pointer(Integer {
                    sign: Sign::Unsigned,
                    width: BitWidth::Bit8,
                }),
            ]
        );
    }

    fn data_file(name: &str) -> String {
        format!("{}/test-data/{}", env!("CARGO_MANIFEST_DIR"), name)
    }

    #[test]
    fn test_provider_struct() {
        let provider_name = "foo";
        let defn = std::fs::read_to_string(data_file(&format!("{}.d", provider_name))).unwrap();
        let provider = Provider::try_from(
            &DTraceParser::parse(Rule::FILE, &defn)
                .unwrap()
                .next()
                .unwrap()
                .into_inner(),
        );
        let provider = provider.unwrap();
        assert_eq!(provider.name, provider_name);
        assert_eq!(provider.probes.len(), 1);
        assert_eq!(provider.probes[0].name, "baz");
    }

    #[test]
    fn test_file_struct() {
        let defn = r#"
            /* a comment */
            #pragma do stuff
            provider foo {
                probe quux();
                probe quack(char*, uint16_t, uint8_t);
            };
            provider bar {
                probe bar();
                probe baz(char*, uint16_t, uint8_t);
            };
            "#;
        let file = File::try_from(&DTraceParser::parse(Rule::FILE, defn).unwrap()).unwrap();
        assert_eq!(file.providers.len(), 2);
        assert_eq!(file.providers[0].name, "foo");
        assert_eq!(file.providers[1].probes[1].name, "baz");

        let file2 = File::try_from(defn).unwrap();
        assert_eq!(file, file2);

        assert!(File::try_from("this is not a D file").is_err());
    }
}
