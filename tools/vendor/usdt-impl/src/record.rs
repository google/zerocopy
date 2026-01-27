//! Implementation of construction and extraction of custom linker section records used to store
//! probe information in an object file.

// Copyright 2024 Oxide Computer Company
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

use crate::DataType;
use byteorder::{NativeEndian, ReadBytesExt};
use dof::{Probe, Provider, Section};
use std::collections::BTreeMap;
use std::mem::size_of;
use std::sync::atomic::AtomicU8;
use std::sync::atomic::Ordering;

// Version number for probe records containing data about all probes.
//
// NOTE: This must have a maximum of `u8::MAX - 1`. See `read_record_version` for
// details.
pub(crate) const PROBE_REC_VERSION: u8 = 1;

/// Extract records for all defined probes from our custom linker sections.
pub fn process_section(mut data: &mut [u8], register: bool) -> Result<Section, crate::Error> {
    let mut providers = BTreeMap::new();

    while !data.is_empty() {
        assert!(
            data.len() >= size_of::<u32>(),
            "Not enough bytes for length header"
        );
        // Read the length without consuming it
        let len = (&data[..size_of::<u32>()]).read_u32::<NativeEndian>()? as usize;
        let (rec, rest) = data.split_at_mut(len);
        process_probe_record(&mut providers, rec, register)?;
        data = rest;
    }

    Ok(Section {
        providers,
        ..Default::default()
    })
}

#[cfg(all(unix, not(target_os = "freebsd")))]
/// Convert an address in an object file into a function and file name, if possible.
pub(crate) fn addr_to_info(addr: u64) -> (Option<String>, Option<String>) {
    unsafe {
        let mut info = libc::Dl_info {
            dli_fname: std::ptr::null(),
            dli_fbase: std::ptr::null_mut(),
            dli_sname: std::ptr::null(),
            dli_saddr: std::ptr::null_mut(),
        };
        if libc::dladdr(addr as *const libc::c_void, &mut info as *mut _) == 0 {
            (None, None)
        } else {
            (
                Some(
                    std::ffi::CStr::from_ptr(info.dli_sname)
                        .to_string_lossy()
                        .to_string(),
                ),
                Some(
                    std::ffi::CStr::from_ptr(info.dli_fname)
                        .to_string_lossy()
                        .to_string(),
                ),
            )
        }
    }
}

// On FreeBSD, dladdr(3M) only examines the dynamic symbol table. Which is pretty useless as it
// will always return a dli_sname. To workaround this issue, we use `backtrace_symbols_fmt` from
// libexecinfo, which internally looks in the executable to determine the symbol of the given
// address.
// See: https://man.freebsd.org/cgi/man.cgi?query=backtrace&sektion=3
#[cfg(target_os = "freebsd")]
pub(crate) fn addr_to_info(addr: u64) -> (Option<String>, Option<String>) {
    unsafe {
        #[link(name = "execinfo")]
        extern "C" {
            pub fn backtrace_symbols_fmt(
                _: *const *mut libc::c_void,
                _: libc::size_t,
                _: *const libc::c_char,
            ) -> *mut *mut libc::c_char;
        }

        let addrs_arr = [addr];
        let addrs = addrs_arr.as_ptr() as *const *mut libc::c_void;

        let format = std::ffi::CString::new("%n\n%f").unwrap();
        let symbols = backtrace_symbols_fmt(addrs, 1, format.as_ptr());

        if !symbols.is_null() {
            if let Some((sname, fname)) = std::ffi::CStr::from_ptr(*symbols)
                .to_string_lossy()
                .split_once('\n')
            {
                (Some(sname.to_string()), Some(fname.to_string()))
            } else {
                (None, None)
            }
        } else {
            (None, None)
        }
    }
}

#[cfg(not(unix))]
/// Convert an address in an object file into a function and file name, if possible.
pub(crate) fn addr_to_info(_addr: u64) -> (Option<String>, Option<String>) {
    (None, None)
}

// Limit a string to the DTrace-imposed maxima. Note that this ensures a null-terminated C string
// result, i.e., the actual string is of length `limit - 1`.
// See dtrace.h,
//
// DTrace appends the PID to the provider name. The exact size is platform dependent, but use the
// largest known value of 999,999 on illumos. MacOS and the BSDs are 32-99K. We take the log to get
// the number of digits.
const MAX_PROVIDER_NAME_LEN: usize = 64 - 6;
const MAX_PROBE_NAME_LEN: usize = 64;
const MAX_FUNC_NAME_LEN: usize = 128;
const MAX_ARG_TYPE_LEN: usize = 128;
fn limit_string_length<S: AsRef<str>>(s: S, limit: usize) -> String {
    let s = s.as_ref();
    let limit = s.len().min(limit - 1);
    s[..limit].to_string()
}

// Return the probe record version, atomically updating it if the probe record will be handled.
fn read_record_version(version: &mut u8, register: bool) -> u8 {
    // First check if (1) we need to do anything other than read the version and
    // (2) if this is a version number this compiled crate could feasibly
    // handle.
    let ver = *version;
    if !register || ver > PROBE_REC_VERSION {
        return ver;
    }

    // At this point we know we need to potentially update the version, and that
    // we also have code that can handle it. We'll exchange it with the sentinel
    // unconditionally.
    //
    // If we get back the sentinel, another thread beat us to the punch. If we
    // get back anything else, it is a version we are capable of handling.
    //
    // TODO-safety: We'd love to use `AtomicU8::from_mut`, but that remains a
    // nightly-only feature. In the meantime, this is safe because we have a
    // mutable reference to the data in this method, and atomic types are
    // guaranteed to have the same layout as their inner type.
    let ver = unsafe { std::mem::transmute::<&mut u8, &AtomicU8>(version) };
    ver.swap(u8::MAX, Ordering::SeqCst)
}

// Process a single record from the custom linker section.
fn process_probe_record(
    providers: &mut BTreeMap<String, Provider>,
    rec: &mut [u8],
    register: bool,
) -> Result<(), crate::Error> {
    // First four bytes are the length, next byte is the version number.
    let (rec, mut data) = {
        // We need `rec` to be mutable and have type `&mut [u8]`, and `data` to
        // be mutable, but have type `&[u8]`. Use `split_at_mut` to get two
        // `&mut [u8]` and then convert the latter to a shared reference.
        let (rec, data) = rec.split_at_mut(5);
        (rec, &*data)
    };
    let version = read_record_version(&mut rec[4], register);

    // If this record comes from a future version of the data format, we skip it
    // and hope that the author of main will *also* include a call to a more
    // recent version. Note that future versions should handle previous formats.
    //
    // NOTE: This version check is also used to implement one-time registration of probes. On the
    // first pass through the probe section, the version is rewritten to `u8::MAX`, so that any
    // future read of the section skips all previously-read records.
    if version > PROBE_REC_VERSION {
        return Ok(());
    }

    let n_args = data.read_u8()? as usize;
    let flags = data.read_u16::<NativeEndian>()?;
    let address = data.read_u64::<NativeEndian>()?;
    let provname = data.read_cstr();
    let probename = data.read_cstr();
    let args = {
        let mut args = Vec::with_capacity(n_args);
        for _ in 0..n_args {
            args.push(limit_string_length(data.read_cstr(), MAX_ARG_TYPE_LEN));
        }
        args
    };

    let funcname = match addr_to_info(address).0 {
        Some(s) => limit_string_length(s, MAX_FUNC_NAME_LEN),
        None => format!("?{:#x}", address),
    };

    let provname = limit_string_length(provname, MAX_PROVIDER_NAME_LEN);
    let provider = providers.entry(provname.clone()).or_insert(Provider {
        name: provname,
        probes: BTreeMap::new(),
    });

    let probename = limit_string_length(probename, MAX_PROBE_NAME_LEN);
    let probe = provider.probes.entry(probename.clone()).or_insert(Probe {
        name: probename,
        function: funcname,
        address,
        offsets: vec![],
        enabled_offsets: vec![],
        arguments: vec![],
    });
    probe.arguments = args;

    // We expect to get records in address order for a given probe; our offsets
    // would be negative otherwise.
    assert!(address >= probe.address);

    if flags == 0 {
        probe.offsets.push((address - probe.address) as u32);
    } else {
        probe.enabled_offsets.push((address - probe.address) as u32);
    }
    Ok(())
}

trait ReadCstrExt<'a> {
    fn read_cstr(&mut self) -> &'a str;
}

impl<'a> ReadCstrExt<'a> for &'a [u8] {
    fn read_cstr(&mut self) -> &'a str {
        let index = self
            .iter()
            .position(|ch| *ch == 0)
            .expect("ran out of bytes before we found a zero");

        let ret = std::str::from_utf8(&self[..index]).unwrap();
        *self = &self[index + 1..];
        ret
    }
}

// Construct the ASM record for a probe. If `types` is `None`, then is is an is-enabled probe.
#[allow(dead_code)]
pub(crate) fn emit_probe_record(prov: &str, probe: &str, types: Option<&[DataType]>) -> String {
    #[cfg(not(target_os = "freebsd"))]
    let section_ident = r#"set_dtrace_probes,"aw","progbits""#;
    #[cfg(target_os = "freebsd")]
    let section_ident = r#"set_dtrace_probes,"awR","progbits""#;
    let is_enabled = types.is_none();
    let n_args = types.map_or(0, |typ| typ.len());
    let arguments = types.map_or_else(String::new, |types| {
        types
            .iter()
            .map(|typ| format!(".asciz \"{}\"", typ.to_c_type()))
            .collect::<Vec<_>>()
            .join("\n")
    });
    format!(
        r#"
                    .pushsection {section_ident}
                    .balign 8
            991:
                    .4byte 992f-991b    // length
                    .byte {version}
                    .byte {n_args}
                    .2byte {flags}
                    .8byte 990b         // address
                    .asciz "{prov}"
                    .asciz "{probe}"
                    {arguments}         // null-terminated strings for each argument
                    .balign 8
            992:    .popsection
                    {yeet}
        "#,
        section_ident = section_ident,
        version = PROBE_REC_VERSION,
        n_args = n_args,
        flags = if is_enabled { 1 } else { 0 },
        prov = prov,
        probe = probe.replace("__", "-"),
        arguments = arguments,
        yeet = if cfg!(any(target_os = "illumos", target_os = "freebsd")) {
            // The illumos and FreeBSD linkers may yeet our probes section into the trash under
            // certain conditions. To counteract this, we yeet references to the
            // probes section into another section. This causes the linker to
            // retain the probes section.
            r#"
                    .pushsection yeet_dtrace_probes
                    .8byte 991b
                    .popsection
                "#
        } else {
            ""
        },
    )
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use byteorder::{NativeEndian, WriteBytesExt};

    use super::emit_probe_record;
    use super::process_probe_record;
    use super::process_section;
    use super::DataType;
    use super::PROBE_REC_VERSION;
    use super::{MAX_PROBE_NAME_LEN, MAX_PROVIDER_NAME_LEN};
    use dtrace_parser::BitWidth;
    use dtrace_parser::DataType as DType;
    use dtrace_parser::Integer;
    use dtrace_parser::Sign;

    #[test]
    fn test_process_probe_record() {
        let mut rec = Vec::<u8>::new();

        // write a dummy length
        rec.write_u32::<NativeEndian>(0).unwrap();
        rec.write_u8(PROBE_REC_VERSION).unwrap();
        rec.write_u8(0).unwrap();
        rec.write_u16::<NativeEndian>(0).unwrap();
        rec.write_u64::<NativeEndian>(0x1234).unwrap();
        rec.write_cstr("provider");
        rec.write_cstr("probe");
        // fix the length field
        let len = rec.len();
        (&mut rec[0..])
            .write_u32::<NativeEndian>(len as u32)
            .unwrap();

        let mut providers = BTreeMap::new();
        process_probe_record(&mut providers, &mut rec, true).unwrap();

        let probe = providers
            .get("provider")
            .unwrap()
            .probes
            .get("probe")
            .unwrap();

        assert_eq!(probe.name, "probe");
        assert_eq!(probe.address, 0x1234);
    }

    #[test]
    fn test_process_probe_record_long_names() {
        let mut rec = Vec::<u8>::new();

        // write a dummy length
        let long_name = "p".repeat(130);
        rec.write_u32::<NativeEndian>(0).unwrap();
        rec.write_u8(PROBE_REC_VERSION).unwrap();
        rec.write_u8(0).unwrap();
        rec.write_u16::<NativeEndian>(0).unwrap();
        rec.write_u64::<NativeEndian>(0x1234).unwrap();
        rec.write_cstr(&long_name);
        rec.write_cstr(&long_name);
        // fix the length field
        let len = rec.len();
        (&mut rec[0..])
            .write_u32::<NativeEndian>(len as u32)
            .unwrap();

        let mut providers = BTreeMap::new();
        process_probe_record(&mut providers, &mut rec, true).unwrap();

        let expected_provider_name = &long_name[..MAX_PROVIDER_NAME_LEN - 1];
        let expected_probe_name = &long_name[..MAX_PROBE_NAME_LEN - 1];

        assert!(providers.get(&long_name).is_none());
        let probe = providers
            .get(expected_provider_name)
            .unwrap()
            .probes
            .get(expected_probe_name)
            .unwrap();

        assert_eq!(probe.name, expected_probe_name);
        assert_eq!(probe.address, 0x1234);
    }

    // Write two probe records, from the same provider.
    //
    // The version argument is used to control the probe record version, which helps test one-time
    // registration of probes.
    fn make_record(version: u8) -> Vec<u8> {
        let mut data = Vec::<u8>::new();

        // write a dummy length for the first record
        data.write_u32::<NativeEndian>(0).unwrap();
        data.write_u8(version).unwrap();
        data.write_u8(0).unwrap();
        data.write_u16::<NativeEndian>(0).unwrap();
        data.write_u64::<NativeEndian>(0x1234).unwrap();
        data.write_cstr("provider");
        data.write_cstr("probe");
        let len = data.len();
        (&mut data[0..])
            .write_u32::<NativeEndian>(len as u32)
            .unwrap();

        data.write_u32::<NativeEndian>(0).unwrap();
        data.write_u8(version).unwrap();
        data.write_u8(0).unwrap();
        data.write_u16::<NativeEndian>(0).unwrap();
        data.write_u64::<NativeEndian>(0x12ab).unwrap();
        data.write_cstr("provider");
        data.write_cstr("probe");
        let len2 = data.len() - len;
        (&mut data[len..])
            .write_u32::<NativeEndian>(len2 as u32)
            .unwrap();
        data
    }

    #[test]
    fn test_process_section() {
        let mut data = make_record(PROBE_REC_VERSION);
        let section = process_section(&mut data, true).unwrap();
        let probe = section
            .providers
            .get("provider")
            .unwrap()
            .probes
            .get("probe")
            .unwrap();

        assert_eq!(probe.name, "probe");
        assert_eq!(probe.address, 0x1234);
        assert_eq!(probe.offsets, vec![0, 0x12ab - 0x1234]);
    }

    #[test]
    fn test_re_process_section() {
        // Ensure that re-processing the same section returns zero probes, as they should have all
        // been previously processed.
        let mut data = make_record(PROBE_REC_VERSION);
        let section = process_section(&mut data, true).unwrap();
        assert_eq!(section.providers.len(), 1);
        assert_eq!(data[4], u8::MAX);
        let section = process_section(&mut data, true).unwrap();
        assert_eq!(data[4], u8::MAX);
        assert_eq!(section.providers.len(), 0);
    }

    #[test]
    fn test_process_section_future_version() {
        // Ensure that we _don't_ modify a future version number in a probe record, but that the
        // probes are still skipped (since by definition we're ignoring future versions).
        let mut data = make_record(PROBE_REC_VERSION + 1);
        let section = process_section(&mut data, true).unwrap();
        assert_eq!(section.providers.len(), 0);
        assert_eq!(data[4], PROBE_REC_VERSION + 1);
    }

    trait WriteCstrExt {
        fn write_cstr(&mut self, s: &str);
    }

    impl WriteCstrExt for Vec<u8> {
        fn write_cstr(&mut self, s: &str) {
            self.extend_from_slice(s.as_bytes());
            self.push(0);
        }
    }

    #[test]
    fn test_emit_probe_record() {
        let provider = "provider";
        let probe = "probe";
        let types = [
            DataType::Native(DType::Pointer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            })),
            DataType::Native(DType::String),
        ];
        let record = emit_probe_record(provider, probe, Some(&types));
        let mut lines = record.lines();
        println!("{}", record);
        lines.next(); // empty line
        assert!(lines.next().unwrap().contains(".pushsection"));
        let mut lines = lines.skip(3);
        assert!(lines
            .next()
            .unwrap()
            .contains(&format!(".byte {}", PROBE_REC_VERSION)));
        assert!(lines
            .next()
            .unwrap()
            .contains(&format!(".byte {}", types.len())));
        for (typ, line) in types.iter().zip(lines.skip(4)) {
            assert!(line.contains(&format!(".asciz \"{}\"", typ.to_c_type())));
        }
    }

    #[test]
    fn test_emit_probe_record_dunders() {
        let provider = "provider";
        let probe = "my__probe";
        let types = [
            DataType::Native(DType::Pointer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            })),
            DataType::Native(dtrace_parser::DataType::String),
        ];
        let record = emit_probe_record(provider, probe, Some(&types));
        assert!(
            record.contains("my-probe"),
            "Expected double-underscores to be translated to a single dash"
        );
    }
}
