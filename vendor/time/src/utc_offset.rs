use core::fmt;
use core::ops::Neg;
#[cfg(feature = "formatting")]
use std::io;

use crate::error;
#[cfg(feature = "formatting")]
use crate::formatting::Formattable;
#[cfg(feature = "parsing")]
use crate::parsing::Parsable;
#[cfg(feature = "local-offset")]
use crate::OffsetDateTime;

/// An offset from UTC.
///
/// This struct can store values up to ±23:59:59. If you need support outside this range, please
/// file an issue with your use case.
// All three components _must_ have the same sign.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UtcOffset {
    #[allow(clippy::missing_docs_in_private_items)]
    hours: i8,
    #[allow(clippy::missing_docs_in_private_items)]
    minutes: i8,
    #[allow(clippy::missing_docs_in_private_items)]
    seconds: i8,
}

impl UtcOffset {
    /// A `UtcOffset` that is UTC.
    ///
    /// ```rust
    /// # use time::{UtcOffset, macros::offset};
    /// assert_eq!(UtcOffset::UTC, offset!(UTC));
    /// ```
    pub const UTC: Self = Self::__from_hms_unchecked(0, 0, 0);

    // region: constructors
    /// Create a `UtcOffset` representing an offset of the hours, minutes, and seconds provided, the
    /// validity of which must be guaranteed by the caller. All three parameters must have the same
    /// sign.
    #[doc(hidden)]
    pub const fn __from_hms_unchecked(hours: i8, minutes: i8, seconds: i8) -> Self {
        Self {
            hours,
            minutes,
            seconds,
        }
    }

    /// Create a `UtcOffset` representing an offset by the number of hours, minutes, and seconds
    /// provided.
    ///
    /// The sign of all three components should match. If they do not, all smaller components will
    /// have their signs flipped.
    ///
    /// ```rust
    /// # use time::UtcOffset;
    /// assert_eq!(UtcOffset::from_hms(1, 2, 3)?.as_hms(), (1, 2, 3));
    /// assert_eq!(UtcOffset::from_hms(1, -2, -3)?.as_hms(), (1, 2, 3));
    /// # Ok::<_, time::Error>(())
    /// ```
    pub const fn from_hms(
        hours: i8,
        mut minutes: i8,
        mut seconds: i8,
    ) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(hours in -23 => 23);
        ensure_value_in_range!(minutes in -59 => 59);
        ensure_value_in_range!(seconds in -59 => 59);

        if (hours > 0 && minutes < 0) || (hours < 0 && minutes > 0) {
            minutes *= -1;
        }
        if (hours > 0 && seconds < 0)
            || (hours < 0 && seconds > 0)
            || (minutes > 0 && seconds < 0)
            || (minutes < 0 && seconds > 0)
        {
            seconds *= -1;
        }

        Ok(Self::__from_hms_unchecked(hours, minutes, seconds))
    }

    /// Create a `UtcOffset` representing an offset by the number of seconds provided.
    ///
    /// ```rust
    /// # use time::UtcOffset;
    /// assert_eq!(UtcOffset::from_whole_seconds(3_723)?.as_hms(), (1, 2, 3));
    /// # Ok::<_, time::Error>(())
    /// ```
    pub const fn from_whole_seconds(seconds: i32) -> Result<Self, error::ComponentRange> {
        ensure_value_in_range!(seconds in -86_399 => 86_399);

        Ok(Self::__from_hms_unchecked(
            (seconds / 3_600) as _,
            ((seconds / 60) % 60) as _,
            (seconds % 60) as _,
        ))
    }
    // endregion constructors

    // region: getters
    /// Obtain the UTC offset as its hours, minutes, and seconds. The sign of all three components
    /// will always match. A positive value indicates an offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).as_hms(), (1, 2, 3));
    /// assert_eq!(offset!(-1:02:03).as_hms(), (-1, -2, -3));
    /// ```
    pub const fn as_hms(self) -> (i8, i8, i8) {
        (self.hours, self.minutes, self.seconds)
    }

    /// Obtain the number of whole hours the offset is from UTC. A positive value indicates an
    /// offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).whole_hours(), 1);
    /// assert_eq!(offset!(-1:02:03).whole_hours(), -1);
    /// ```
    pub const fn whole_hours(self) -> i8 {
        self.hours
    }

    /// Obtain the number of whole minutes the offset is from UTC. A positive value indicates an
    /// offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).whole_minutes(), 62);
    /// assert_eq!(offset!(-1:02:03).whole_minutes(), -62);
    /// ```
    pub const fn whole_minutes(self) -> i16 {
        self.hours as i16 * 60 + self.minutes as i16
    }

    /// Obtain the number of minutes past the hour the offset is from UTC. A positive value
    /// indicates an offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).minutes_past_hour(), 2);
    /// assert_eq!(offset!(-1:02:03).minutes_past_hour(), -2);
    /// ```
    pub const fn minutes_past_hour(self) -> i8 {
        self.minutes
    }

    /// Obtain the number of whole seconds the offset is from UTC. A positive value indicates an
    /// offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).whole_seconds(), 3723);
    /// assert_eq!(offset!(-1:02:03).whole_seconds(), -3723);
    /// ```
    // This may be useful for anyone manually implementing arithmetic, as it
    // would let them construct a `Duration` directly.
    pub const fn whole_seconds(self) -> i32 {
        self.hours as i32 * 3_600 + self.minutes as i32 * 60 + self.seconds as i32
    }

    /// Obtain the number of seconds past the minute the offset is from UTC. A positive value
    /// indicates an offset to the east; a negative to the west.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert_eq!(offset!(+1:02:03).seconds_past_minute(), 3);
    /// assert_eq!(offset!(-1:02:03).seconds_past_minute(), -3);
    /// ```
    pub const fn seconds_past_minute(self) -> i8 {
        self.seconds
    }
    // endregion getters

    // region: is_{sign}
    /// Check if the offset is exactly UTC.
    ///
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert!(!offset!(+1:02:03).is_utc());
    /// assert!(!offset!(-1:02:03).is_utc());
    /// assert!(offset!(UTC).is_utc());
    /// ```
    pub const fn is_utc(self) -> bool {
        self.hours == 0 && self.minutes == 0 && self.seconds == 0
    }

    /// Check if the offset is positive, or east of UTC.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert!(offset!(+1:02:03).is_positive());
    /// assert!(!offset!(-1:02:03).is_positive());
    /// assert!(!offset!(UTC).is_positive());
    /// ```
    pub const fn is_positive(self) -> bool {
        self.hours > 0 || self.minutes > 0 || self.seconds > 0
    }

    /// Check if the offset is negative, or west of UTC.
    ///
    /// ```rust
    /// # use time::macros::offset;
    /// assert!(!offset!(+1:02:03).is_negative());
    /// assert!(offset!(-1:02:03).is_negative());
    /// assert!(!offset!(UTC).is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.hours < 0 || self.minutes < 0 || self.seconds < 0
    }
    // endregion is_{sign}

    // region: local offset
    /// Attempt to obtain the system's UTC offset at a known moment in time. If the offset cannot be
    /// determined, an error is returned.
    ///
    /// ```rust
    /// # use time::{UtcOffset, OffsetDateTime};
    /// let local_offset = UtcOffset::local_offset_at(OffsetDateTime::UNIX_EPOCH);
    /// # if false {
    /// assert!(local_offset.is_ok());
    /// # }
    /// ```
    #[cfg(feature = "local-offset")]
    #[cfg_attr(__time_03_docs, doc(cfg(feature = "local-offset")))]
    pub fn local_offset_at(datetime: OffsetDateTime) -> Result<Self, error::IndeterminateOffset> {
        local_offset_at(datetime).ok_or(error::IndeterminateOffset)
    }

    /// Attempt to obtain the system's current UTC offset. If the offset cannot be determined, an
    /// error is returned.
    ///
    /// ```rust
    /// # use time::UtcOffset;
    /// let local_offset = UtcOffset::current_local_offset();
    /// # if false {
    /// assert!(local_offset.is_ok());
    /// # }
    /// ```
    #[cfg(feature = "local-offset")]
    #[cfg_attr(__time_03_docs, doc(cfg(feature = "local-offset")))]
    pub fn current_local_offset() -> Result<Self, error::IndeterminateOffset> {
        let now = OffsetDateTime::now_utc();
        local_offset_at(now).ok_or(error::IndeterminateOffset)
    }
    // endregion: local offset
}

// region: formatting & parsing
#[cfg(feature = "formatting")]
#[cfg_attr(__time_03_docs, doc(cfg(feature = "formatting")))]
impl UtcOffset {
    /// Format the `UtcOffset` using the provided [format description](crate::format_description).
    pub fn format_into(
        self,
        output: &mut impl io::Write,
        format: &impl Formattable,
    ) -> Result<usize, error::Format> {
        format.format_into(output, None, None, Some(self))
    }

    /// Format the `UtcOffset` using the provided [format description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::offset};
    /// let format = format_description::parse("[offset_hour sign:mandatory]:[offset_minute]")?;
    /// assert_eq!(offset!(+1).format(&format)?, "+01:00");
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn format(self, format: &impl Formattable) -> Result<String, error::Format> {
        format.format(None, None, Some(self))
    }
}

#[cfg(feature = "parsing")]
#[cfg_attr(__time_03_docs, doc(cfg(feature = "parsing")))]
impl UtcOffset {
    /// Parse a `UtcOffset` from the input using the provided [format
    /// description](crate::format_description).
    ///
    /// ```rust
    /// # use time::{format_description, macros::offset, UtcOffset};
    /// let format = format_description::parse("[offset_hour]:[offset_minute]")?;
    /// assert_eq!(UtcOffset::parse("-03:42", &format)?, offset!(-3:42));
    /// # Ok::<_, time::Error>(())
    /// ```
    pub fn parse(input: &str, description: &impl Parsable) -> Result<Self, error::Parse> {
        description.parse_offset(input.as_bytes())
    }
}

impl fmt::Display for UtcOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{:02}:{:02}:{:02}",
            if self.is_negative() { '-' } else { '+' },
            self.hours.abs(),
            self.minutes.abs(),
            self.seconds.abs()
        )
    }
}
// endregion formatting & parsing

impl Neg for UtcOffset {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::__from_hms_unchecked(-self.hours, -self.minutes, -self.seconds)
    }
}

/// Attempt to obtain the system's UTC offset. If the offset cannot be determined, `None` is
/// returned.
#[cfg(feature = "local-offset")]
#[cfg_attr(__time_03_docs, doc(cfg(feature = "local-offset")))]
#[allow(clippy::too_many_lines, clippy::missing_const_for_fn)]
fn local_offset_at(datetime: OffsetDateTime) -> Option<UtcOffset> {
    // See #293 for details.
    #[cfg(all(target_family = "unix", not(unsound_local_offset)))]
    {
        let _ = datetime;
        None
    }
    // Let a user explicitly opt-in to unsound behavior. As this is not done via feature flags, it
    // can only be enabled by the end user. It must be explicitly passed on each compilation.
    #[cfg(all(target_family = "unix", unsound_local_offset))]
    {
        use core::convert::TryInto;
        use core::mem::MaybeUninit;

        /// Convert the given Unix timestamp to a `libc::tm`. Returns `None` on any error.
        fn timestamp_to_tm(timestamp: i64) -> Option<libc::tm> {
            extern "C" {
                #[cfg_attr(target_os = "netbsd", link_name = "__tzset50")]
                fn tzset();
            }

            // The exact type of `timestamp` beforehand can vary, so this conversion is necessary.
            #[allow(clippy::useless_conversion)]
            let timestamp = timestamp.try_into().ok()?;

            let mut tm = MaybeUninit::uninit();

            // Update timezone information from system. `localtime_r` does not do this for us.
            //
            // Safety: tzset is thread-safe.
            #[allow(unsafe_code)]
            unsafe {
                tzset();
            }

            // Safety: We are calling a system API, which mutates the `tm` variable. If a null
            // pointer is returned, an error occurred.
            #[allow(unsafe_code)]
            let tm_ptr = unsafe { libc::localtime_r(&timestamp, tm.as_mut_ptr()) };

            if tm_ptr.is_null() {
                None
            } else {
                // Safety: The value was initialized, as we no longer have a null pointer.
                #[allow(unsafe_code)]
                {
                    Some(unsafe { tm.assume_init() })
                }
            }
        }

        let tm = timestamp_to_tm(datetime.unix_timestamp())?;

        // `tm_gmtoff` extension
        #[cfg(not(any(target_os = "solaris", target_os = "illumos")))]
        {
            let seconds: i32 = tm.tm_gmtoff.try_into().ok()?;
            UtcOffset::from_hms(
                (seconds / 3_600) as _,
                ((seconds / 60) % 60) as _,
                (seconds % 60) as _,
            )
            .ok()
        }

        // No `tm_gmtoff` extension
        #[cfg(any(target_os = "solaris", target_os = "illumos"))]
        {
            use core::convert::TryFrom;

            use crate::Date;

            let mut tm = tm;
            if tm.tm_sec == 60 {
                // Leap seconds are not currently supported.
                tm.tm_sec = 59;
            }

            let local_timestamp =
                Date::from_ordinal_date(1900 + tm.tm_year, u16::try_from(tm.tm_yday).ok()? + 1)
                    .ok()?
                    .with_hms(
                        tm.tm_hour.try_into().ok()?,
                        tm.tm_min.try_into().ok()?,
                        tm.tm_sec.try_into().ok()?,
                    )
                    .ok()?
                    .assume_utc()
                    .unix_timestamp();

            let diff_secs: i32 = (local_timestamp - datetime.unix_timestamp())
                .try_into()
                .ok()?;

            UtcOffset::from_hms(
                (diff_secs / 3_600) as _,
                ((diff_secs / 60) % 60) as _,
                (diff_secs % 60) as _,
            )
            .ok()
        }
    }
    #[cfg(target_family = "windows")]
    {
        use core::convert::TryInto;
        use core::mem::MaybeUninit;

        // ffi: WINAPI FILETIME struct
        #[repr(C)]
        #[allow(non_snake_case)]
        struct FileTime {
            dwLowDateTime: u32,
            dwHighDateTime: u32,
        }

        // ffi: WINAPI SYSTEMTIME struct
        #[repr(C)]
        #[allow(non_snake_case)]
        struct SystemTime {
            wYear: u16,
            wMonth: u16,
            wDayOfWeek: u16,
            wDay: u16,
            wHour: u16,
            wMinute: u16,
            wSecond: u16,
            wMilliseconds: u16,
        }

        #[link(name = "Kernel32")]
        extern "system" {
            // https://docs.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-systemtimetofiletime
            fn SystemTimeToFileTime(
                lpSystemTime: *const SystemTime,
                lpFileTime: *mut FileTime,
            ) -> i32;

            // https://docs.microsoft.com/en-us/windows/win32/api/timezoneapi/nf-timezoneapi-systemtimetotzspecificlocaltime
            fn SystemTimeToTzSpecificLocalTime(
                lpTimeZoneInformation: *const std::ffi::c_void, // We only pass `nullptr` here
                lpUniversalTime: *const SystemTime,
                lpLocalTime: *mut SystemTime,
            ) -> i32;
        }

        /// Convert a `SYSTEMTIME` to a `FILETIME`. Returns `None` if any error occurred.
        fn systemtime_to_filetime(systime: &SystemTime) -> Option<FileTime> {
            let mut ft = MaybeUninit::uninit();

            // Safety: `SystemTimeToFileTime` is thread-safe. We are only assuming initialization if
            // the call succeeded.
            #[allow(unsafe_code)]
            {
                if 0 == unsafe { SystemTimeToFileTime(systime, ft.as_mut_ptr()) } {
                    // failed
                    None
                } else {
                    Some(unsafe { ft.assume_init() })
                }
            }
        }

        /// Convert a `FILETIME` to an `i64`, representing a number of seconds.
        fn filetime_to_secs(filetime: &FileTime) -> i64 {
            /// FILETIME represents 100-nanosecond intervals
            const FT_TO_SECS: i64 = 10_000_000;
            ((filetime.dwHighDateTime as i64) << 32 | filetime.dwLowDateTime as i64) / FT_TO_SECS
        }

        /// Convert an [`OffsetDateTime`] to a `SYSTEMTIME`.
        fn offset_to_systemtime(datetime: OffsetDateTime) -> SystemTime {
            let (_, month, day_of_month) =
                datetime.to_offset(UtcOffset::UTC).date().to_calendar_date();
            SystemTime {
                wYear: datetime.year() as _,
                wMonth: month as _,
                wDay: day_of_month as _,
                wDayOfWeek: 0, // ignored
                wHour: datetime.hour() as _,
                wMinute: datetime.minute() as _,
                wSecond: datetime.second() as _,
                wMilliseconds: datetime.millisecond(),
            }
        }

        // This function falls back to UTC if any system call fails.
        let systime_utc = offset_to_systemtime(datetime.to_offset(UtcOffset::UTC));

        // Safety: `local_time` is only read if it is properly initialized, and
        // `SystemTimeToTzSpecificLocalTime` is thread-safe.
        #[allow(unsafe_code)]
        let systime_local = unsafe {
            let mut local_time = MaybeUninit::uninit();

            if 0 == SystemTimeToTzSpecificLocalTime(
                core::ptr::null(), // use system's current timezone
                &systime_utc,
                local_time.as_mut_ptr(),
            ) {
                // call failed
                return None;
            } else {
                local_time.assume_init()
            }
        };

        // Convert SYSTEMTIMEs to FILETIMEs so we can perform arithmetic on them.
        let ft_system = systemtime_to_filetime(&systime_utc)?;
        let ft_local = systemtime_to_filetime(&systime_local)?;

        let diff_secs: i32 = (filetime_to_secs(&ft_local) - filetime_to_secs(&ft_system))
            .try_into()
            .ok()?;

        UtcOffset::from_hms(
            (diff_secs / 3_600) as _,
            ((diff_secs / 60) % 60) as _,
            (diff_secs % 60) as _,
        )
        .ok()
    }
    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        // Silence the unused variable warning when appropriate.
        let _ = datetime;
        None
    }
}
