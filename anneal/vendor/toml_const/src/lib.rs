#![doc = include_str!("../README.md")]
#![no_std]

// re-exports
pub use datetime::*;
pub use macros::*;
pub use toml::value::{Date, Datetime, Offset, Time};

#[cfg(feature = "phf")]
#[doc(hidden)]
pub use phf;
#[cfg(feature = "phf")]
pub use phf::phf_ordered_map as phf_map_macro;
#[cfg(feature = "phf")]
pub use phf::OrderedMap as PhfMap;

/// Destructured datetime structs
mod datetime {
    use super::*;

    const DEFAULT_DATE: Date = Date {
        year: 1970,
        month: 1,
        day: 1,
    };

    const DEFAULT_TIME: Time = Time {
        hour: 0,
        minute: 0,
        second: 0,
        nanosecond: 0,
    };

    const DEFAULT_OFFSET: Offset = Offset::Z;

    #[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
    pub struct OffsetDateTime {
        pub date: Date,
        pub time: Time,
        pub offset: Offset,
    }

    #[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
    pub struct LocalDateTime {
        pub date: Date,
        pub time: Time,
    }

    #[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
    pub struct LocalDate {
        pub date: Date,
    }

    #[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord)]
    pub struct LocalTime {
        pub time: Time,
    }

    impl Default for OffsetDateTime {
        fn default() -> Self {
            Self {
                date: DEFAULT_DATE,
                time: DEFAULT_TIME,
                offset: DEFAULT_OFFSET,
            }
        }
    }

    impl Default for LocalDateTime {
        fn default() -> Self {
            Self {
                date: DEFAULT_DATE,
                time: DEFAULT_TIME,
            }
        }
    }

    impl Default for LocalDate {
        fn default() -> Self {
            Self { date: DEFAULT_DATE }
        }
    }

    impl Default for LocalTime {
        fn default() -> Self {
            Self { time: DEFAULT_TIME }
        }
    }

    impl From<OffsetDateTime> for Datetime {
        fn from(value: OffsetDateTime) -> Self {
            Self {
                date: Some(value.date),
                time: Some(value.time),
                offset: Some(value.offset),
            }
        }
    }

    impl From<LocalDateTime> for Datetime {
        fn from(value: LocalDateTime) -> Self {
            Self {
                date: Some(value.date),
                time: Some(value.time),
                offset: None,
            }
        }
    }

    impl From<LocalDate> for Datetime {
        fn from(value: LocalDate) -> Self {
            Self {
                date: Some(value.date),
                time: None,
                offset: None,
            }
        }
    }

    impl From<LocalTime> for Datetime {
        fn from(value: LocalTime) -> Self {
            Self {
                date: None,
                time: Some(value.time),
                offset: None,
            }
        }
    }

    impl core::fmt::Display for OffsetDateTime {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let as_dt = Datetime::from(*self);
            write!(f, "{}", as_dt)
        }
    }

    impl core::fmt::Display for LocalDateTime {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let as_dt = Datetime::from(*self);
            write!(f, "{}", as_dt)
        }
    }

    impl core::fmt::Display for LocalDate {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let as_dt = Datetime::from(*self);
            write!(f, "{}", as_dt)
        }
    }

    impl core::fmt::Display for LocalTime {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            let as_dt = Datetime::from(*self);
            write!(f, "{}", as_dt)
        }
    }
}
