use alloc::string::{String, ToString as _};
use core::fmt;

use serde_core::{de, Deserialize, Deserializer, Serialize, Serializer};

use crate::ByteSize;

impl<'de> Deserialize<'de> for ByteSize {
    fn deserialize<D>(de: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ByteSizeVisitor;

        impl de::Visitor<'_> for ByteSizeVisitor {
            type Value = ByteSize;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("an integer or string")
            }

            fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
                if let Ok(val) = u64::try_from(value) {
                    Ok(ByteSize(val))
                } else {
                    Err(E::invalid_value(
                        de::Unexpected::Signed(value),
                        &"integer overflow",
                    ))
                }
            }

            fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
                Ok(ByteSize(value))
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
                if let Ok(val) = value.parse() {
                    Ok(val)
                } else {
                    Err(E::invalid_value(
                        de::Unexpected::Str(value),
                        &"parsable string",
                    ))
                }
            }
        }

        if de.is_human_readable() {
            de.deserialize_any(ByteSizeVisitor)
        } else {
            de.deserialize_u64(ByteSizeVisitor)
        }
    }
}

impl Serialize for ByteSize {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if ser.is_human_readable() {
            <String>::serialize(&self.to_string(), ser)
        } else {
            self.0.serialize(ser)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use serde::{Deserialize, Serialize};

    #[test]
    fn test_serde() {
        #[derive(Serialize, Deserialize)]
        struct S {
            x: ByteSize,
        }

        let s = serde_json::from_str::<S>(r#"{ "x": "5 B" }"#).unwrap();
        assert_eq!(s.x, ByteSize(5));

        let s = serde_json::from_str::<S>(r#"{ "x": 1048576 }"#).unwrap();
        assert_eq!(s.x, "1 MiB".parse::<ByteSize>().unwrap());

        let s = toml::from_str::<S>(r#"x = "2.5 MiB""#).unwrap();
        assert_eq!(s.x, "2.5 MiB".parse::<ByteSize>().unwrap());

        // i64 MAX
        let s = toml::from_str::<S>(r#"x = "9223372036854775807""#).unwrap();
        assert_eq!(s.x, "9223372036854775807".parse::<ByteSize>().unwrap());
    }

    #[test]
    fn test_serde_json() {
        let json = serde_json::to_string(&ByteSize::mib(1)).unwrap();
        assert_eq!(json, "\"1.0 MiB\"");

        let deserialized = serde_json::from_str::<ByteSize>(&json).unwrap();
        assert_eq!(deserialized.0, 1048576);
    }
}
