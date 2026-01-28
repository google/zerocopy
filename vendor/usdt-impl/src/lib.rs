//! Main implementation crate for the USDT package.

// Copyright 2022 Oxide Computer Company
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

use serde::Deserialize;
use std::cell::RefCell;
use thiserror::Error;

// Probe record parsing required for standard backend (and `des` feature used by `dusty util)
#[cfg(any(usdt_backend_standard, usdt_backend_stapsdt, feature = "des"))]
pub mod record;

#[cfg_attr(usdt_backend_noop, path = "empty.rs")]
#[cfg_attr(usdt_backend_linker, path = "linker.rs")]
#[cfg_attr(usdt_backend_standard, path = "no-linker.rs")]
#[cfg_attr(usdt_backend_stapsdt, path = "stapsdt.rs")]
mod internal;

// Since the `empty` is mostly a no-op, parts of the common code will go unused when it is
// selected for use.
#[cfg_attr(usdt_backend_noop, allow(dead_code))]
mod common;

/// Register an application's probe points with DTrace.
///
/// This function collects information about the probe points defined in an application and ensures
/// that they are registered with the DTrace kernel module. It is critical to note that if this
/// method is not called (at some point in an application), _no probes will be visible_ via the
/// `dtrace(1)` command line tool.
///
/// NOTE: This method presents a quandary for library developers, as consumers of their library may
/// forget to (or choose not to) call this function. There are potential workarounds for this
/// problem, but each comes with significant tradeoffs. Library developers are encouraged to
/// re-export this function and document to their users that this function should be called to
/// guarantee that the library's probes are registered.
pub fn register_probes() -> Result<(), Error> {
    crate::internal::register_probes()
}

/// Errors related to building DTrace probes into Rust code
#[derive(Error, Debug)]
pub enum Error {
    /// Error during parsing of DTrace provider source
    #[error(transparent)]
    ParseError(#[from] dtrace_parser::DTraceError),
    /// Error reading or writing files, or registering DTrace probes
    #[error(transparent)]
    IO(#[from] std::io::Error),
    /// Error related to environment variables, e.g., while running a build script
    #[error(transparent)]
    Env(#[from] std::env::VarError),
    /// An error occurred extracting probe information from the encoded object file sections
    #[error("The file is not a valid object file")]
    InvalidFile,
    /// Error related to calling out to DTrace itself
    #[error("Failed to call DTrace subprocess")]
    DTraceError,
    /// Error converting input to JSON
    #[error(transparent)]
    Json(#[from] serde_json::Error),
}

#[derive(Default, Debug, Deserialize)]
pub struct CompileProvidersConfig {
    pub provider: Option<String>,
    pub probe_format: Option<String>,
    pub module: Option<String>,
}

impl CompileProvidersConfig {
    /// Return the formatted name of a probe.
    pub fn format_probe(&self, probe_name: &str) -> String {
        if let Some(fmt) = &self.probe_format {
            fmt.replace(
                "{provider}",
                self.provider
                    .as_ref()
                    .expect("Expected a provider name when formatting a rpobe"),
            )
            .replace("{probe}", probe_name)
        } else {
            String::from(probe_name)
        }
    }

    /// Return the formatted name of the probe as an identifier.
    pub fn probe_ident(&self, probe_name: &str) -> proc_macro2::Ident {
        quote::format_ident!("{}", self.format_probe(probe_name))
    }

    /// Return the formatted module name as an identifier.
    pub fn module_ident(&self) -> proc_macro2::Ident {
        let name = self.module.as_ref().unwrap_or_else(|| {
            self.provider
                .as_ref()
                .expect("Expected a provider name when making a module ident")
        });
        quote::format_ident!("{}", name)
    }
}

// Compile DTrace provider source code into Rust.
//
// This function parses a provider definition, and, for each probe, a corresponding Rust macro is
// returned. This macro may be called throughout Rust code to fire the corresponding DTrace probe
// (if it's enabled). See [probe_test_macro] for a detailed example.
//
// [probe_test_macro]: https://github.com/oxidecomputer/usdt/tree/master/probe-test-macro
pub fn compile_provider_source(
    source: &str,
    config: &CompileProvidersConfig,
) -> Result<proc_macro2::TokenStream, Error> {
    crate::internal::compile_provider_source(source, config)
}

// Compile a DTrace provider from its representation in the USDT crate.
pub fn compile_provider(
    provider: &Provider,
    config: &CompileProvidersConfig,
) -> proc_macro2::TokenStream {
    crate::internal::compile_provider_from_definition(provider, config)
}

/// A data type supported by the `usdt` crate.
#[derive(Debug, Clone, PartialEq)]
pub enum DataType {
    Native(dtrace_parser::DataType),
    UniqueId,
    Serializable(syn::Type),
}

impl DataType {
    /// Convert a data type to its C type representation as a string.
    pub fn to_c_type(&self) -> String {
        match self {
            DataType::Native(ty) => ty.to_c_type(),
            DataType::UniqueId => String::from("uint64_t"),
            DataType::Serializable(_) => String::from("char*"),
        }
    }

    /// Return the Rust FFI type representation of this data type.
    pub fn to_rust_ffi_type(&self) -> syn::Type {
        match self {
            DataType::Native(ty) => syn::parse_str(&ty.to_rust_ffi_type()).unwrap(),
            DataType::UniqueId => syn::parse_str("::std::os::raw::c_ulonglong").unwrap(),
            DataType::Serializable(_) => syn::parse_str("*const ::std::os::raw::c_char").unwrap(),
        }
    }

    /// Return the native Rust type representation of this data type.
    pub fn to_rust_type(&self) -> syn::Type {
        match self {
            DataType::Native(ty) => syn::parse_str(&ty.to_rust_type()).unwrap(),
            DataType::UniqueId => syn::parse_str("::usdt::UniqueId").unwrap(),
            DataType::Serializable(ref inner) => inner.clone(),
        }
    }
}

impl From<dtrace_parser::DataType> for DataType {
    fn from(ty: dtrace_parser::DataType) -> Self {
        DataType::Native(ty)
    }
}

impl From<&syn::Type> for DataType {
    fn from(t: &syn::Type) -> Self {
        DataType::Serializable(t.clone())
    }
}

/// A single DTrace probe function
#[derive(Debug, Clone)]
pub struct Probe {
    pub name: String,
    pub types: Vec<DataType>,
}

impl From<dtrace_parser::Probe> for Probe {
    fn from(p: dtrace_parser::Probe) -> Self {
        Self {
            name: p.name,
            types: p.types.into_iter().map(DataType::from).collect(),
        }
    }
}

impl Probe {
    /// Return the representation of this probe in D source code.
    pub fn to_d_source(&self) -> String {
        let types = self
            .types
            .iter()
            .map(|typ| typ.to_c_type())
            .collect::<Vec<_>>()
            .join(", ");
        format!("probe {name}({types});", name = self.name, types = types)
    }
}

/// The `Provider` represents a single DTrace provider, with a collection of probes.
#[derive(Debug, Clone)]
pub struct Provider {
    pub name: String,
    pub probes: Vec<Probe>,
    pub use_statements: Vec<syn::ItemUse>,
}

impl Provider {
    /// Return the representation of this provider in D source code.
    pub fn to_d_source(&self) -> String {
        let probes = self
            .probes
            .iter()
            .map(|probe| format!("\t{}", probe.to_d_source()))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "provider {provider_name} {{\n{probes}\n}};",
            provider_name = self.name,
            probes = probes
        )
    }
}

impl From<dtrace_parser::Provider> for Provider {
    fn from(p: dtrace_parser::Provider) -> Self {
        Self {
            name: p.name,
            probes: p.probes.into_iter().map(Probe::from).collect(),
            use_statements: vec![],
        }
    }
}

impl From<&dtrace_parser::Provider> for Provider {
    fn from(p: &dtrace_parser::Provider) -> Self {
        Self::from(p.clone())
    }
}

/// Convert a serializable type into a JSON string, if possible.
///
/// NOTE: This is essentially a re-export of the `serde_json::to_string` function, used to avoid
/// foisting an explicity dependency on that crate in user's `Cargo.toml`.
pub fn to_json<T>(x: &T) -> Result<String, Error>
where
    T: ?Sized + ::serde::Serialize,
{
    ::serde_json::to_string(x).map_err(Error::from)
}

thread_local! {
    static CURRENT_ID: RefCell<u32> = const { RefCell::new(0) };
    static THREAD_ID: RefCell<usize> = RefCell::new(thread_id::get());
}

/// A unique identifier that can be used to correlate multiple USDT probes together.
///
/// It's a common pattern in DTrace scripts to correlate multiple probes. For example, one can time
/// system calls by storing a timestamp on the `syscall:::entry` probe and then computing the
/// elapsed time in the `syscall:::return` probe. This requires some way to "match up" these two
/// probes, to ensure that the elapsed time is correctly attributed to a single system call. Doing
/// so requires an identifier. User code may already have an ID appropriate for this use case, but
/// the `UniqueId` type may be used when one is not already available. These unique IDs can be used
/// to correlate multiple probes occurring in a section or span of user code.
///
/// A probe function may accept a `UniqueId`, which appears in a D as a `u64`. The value is
/// guaranteed to be unique, even if multiple threads run the same traced section of code. (See the
/// [notes] for caveats.) The value may be shared between threads by calling `clone()` on a
/// constructed span -- in this case, the cloned object shares the same value, so that a traced
/// span running in multiple threads (or asynchronous tasks) shares the same identifier.
///
/// A `UniqueId` is very cheap to construct. The internal value is "materialized" in two
/// situations:
///
/// - When an _enabled_ probe fires
/// - When the value is cloned (e.g., for sharing with another thread)
///
/// This minimizes the disabled-probe effect, but still allows sharing a consistent ID in the case
/// of multithreaded work.
///
/// Example
/// -------
/// ```ignore
/// #[usdt::provider]
/// mod with_id {
///     fn work_started(_: &usdt::UniqueId) {}
///     fn halfway_there(_: &usdt::UniqueId, msg: &str) {}
///     fn work_completed(_: &usdt::UniqueId, result: u64) {}
/// }
///
/// // Constructing an ID is very cheap.
/// let id = usdt::UniqueId::new();
///
/// // The ID will only be materialized if this probe is enabled.
/// with_id_work_started!(|| &id);
///
/// // If the ID has been materialized above, this simply clone the internal value. If the ID has
/// // _not_ yet been materialized, say because the `work_started` probe was not enabled, this will
/// // do so now.
/// let id2 = id.clone();
/// let handle = std::thread::spawn(move || {
///     for i in 0..10 {
///         // Do our work.
///         if i == 5 {
///             with_id_halfway_there!(|| (&id2, "work is half completed"));
///         }
///     }
///     10
/// });
///
/// let result = handle.join().unwrap();
/// with_id_work_completed!(|| (&id, result));
/// ```
///
/// Note that this type is not `Sync`, which means we cannot accidentally share the value between
/// threads. The only way to track the same ID in work spanning threads is to first clone the type,
/// which materializes the internal value. For example, this will fail to compile:
///
/// ```compile_fail
/// #[usdt::provider]
/// mod with_id {
///     fn work_started(_: &usdt::UniqueId) {}
///     fn halfway_there(_: &usdt::UniqueId, msg: &str) {}
///     fn work_completed(_: &usdt::UniqueId, result: u64) {}
/// }
///
/// let id = usdt::UniqueId::new();
/// with_id_work_started!(|| &id);
/// let handle = std::thread::spawn(move || {
///     for i in 0..10 {
///         // Do our work.
///         if i == 5 {
///             // Note that we're using `id`, not a clone as the previous example.
///             with_id_halfway_there!(|| (&id, "work is half completed"));
///         }
///     }
///     10
/// });
/// let result = handle.join().unwrap();
/// with_id_work_completed!(|| (&id, result));
/// ```
///
/// Notes
/// -----
///
/// In any practical situation, the generated ID is unique. Its value is assigned on the basis of
/// the thread that creates the `UniqueId` object, plus a monotonic thread-local counter. However,
/// the counter is 32 bits, and so wraps around after about 4 billion unique values. So
/// theoretically, multiple `UniqueId`s could manifest as the same value to DTrace, if they are
/// exceptionally long-lived or generated very often.
#[derive(Debug)]
pub struct UniqueId {
    id: RefCell<Option<u64>>,
}

impl UniqueId {
    /// Construct a new identifier.
    ///
    /// A `UniqueId` is cheap to create, and is not materialized into an actual value until it's
    /// needed, either by a probe function or during `clone`ing to share the value between threads.
    pub const fn new() -> Self {
        Self {
            id: RefCell::new(None),
        }
    }

    // Helper function to actually materialize a u64 value internally.
    //
    // This method assigns a value on the basis of the current thread and a monotonic counter, in
    // the upper and lower 32-bits of a u64, respectively.
    fn materialize(&self) {
        // Safety: This type is not Sync, which means the current thread maintains the only
        // reference to the contained ID. A `UniqueId` in another thread is a clone, at which
        // point the value has been materialized as well. The `id` field of that object is a
        // different `RefCell` -- that type is here just to enable interior mutability.
        let mut inner = self.id.borrow_mut();
        if inner.is_none() {
            let id = CURRENT_ID.with(|id| {
                let thread_id = THREAD_ID.with(|id| *id.borrow_mut() as u64);
                let mut inner = id.borrow_mut();
                *inner = inner.wrapping_add(1);
                (thread_id << 32) | (*inner as u64)
            });
            inner.replace(id);
        }
    }

    /// Return the internal `u64` value, materializing it if needed.
    #[doc(hidden)]
    pub fn as_u64(&self) -> u64 {
        self.materialize();
        // Safety: This is an immutable borrow, so is safe from multiple threads. The cell cannot
        // be borrowed mutably at the same time, as that only occurs within the scope of the
        // `materialize` method. This method can't be called on the _same_ `UniqueId` from multiple
        // threads, because the type is not `Sync`.
        self.id.borrow().unwrap()
    }
}

impl Clone for UniqueId {
    fn clone(&self) -> Self {
        self.materialize();
        Self {
            id: self.id.clone(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use dtrace_parser::BitWidth;
    use dtrace_parser::DataType as DType;
    use dtrace_parser::Integer;
    use dtrace_parser::Sign;

    #[test]
    fn test_probe_to_d_source() {
        let probe = Probe {
            name: String::from("my_probe"),
            types: vec![DataType::Native(DType::Pointer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            }))],
        };
        assert_eq!(probe.to_d_source(), "probe my_probe(uint8_t*);");
    }

    #[test]
    fn test_provider_to_d_source() {
        let probe = Probe {
            name: String::from("my_probe"),
            types: vec![DataType::Native(DType::Integer(Integer {
                sign: Sign::Unsigned,
                width: BitWidth::Bit8,
            }))],
        };
        let provider = Provider {
            name: String::from("my_provider"),
            probes: vec![probe],
            use_statements: vec![],
        };
        assert_eq!(
            provider.to_d_source(),
            "provider my_provider {\n\tprobe my_probe(uint8_t);\n};"
        );
    }

    #[test]
    fn test_data_type() {
        let ty = DataType::Native(DType::Pointer(Integer {
            sign: Sign::Unsigned,
            width: BitWidth::Bit8,
        }));
        assert_eq!(ty.to_rust_type(), syn::parse_str("*const u8").unwrap());

        let ty = DataType::Native(dtrace_parser::DataType::String);
        assert_eq!(ty.to_rust_type(), syn::parse_str("&str").unwrap());

        let ty = DataType::UniqueId;
        assert_eq!(
            ty.to_rust_type(),
            syn::parse_str("::usdt::UniqueId").unwrap()
        );
    }

    #[test]
    fn test_unique_id() {
        let id = UniqueId::new();
        assert!(id.id.borrow().is_none());
        let x = id.as_u64();
        assert_eq!(x & 0xFFFF_FFFF, 1);
        assert_eq!(id.id.borrow().unwrap(), x);
    }

    #[test]
    fn test_unique_id_clone() {
        let id = UniqueId::new();
        let id2 = id.clone();
        assert!(id.id.borrow().is_some());
        assert!(id2.id.borrow().is_some());
        assert_eq!(id.id.borrow().unwrap(), id2.id.borrow().unwrap());

        // Verify that the actual RefCells inside the type point to different locations. This is
        // important to check that sending a clone to a different thread will operate on a
        // different cell, so that they can both borrow the value (either mutably or immutably)
        // without panics.
        assert_ne!(&(id.id) as *const _, &(id2.id) as *const _);
        assert_ne!(id.id.as_ptr(), id2.id.as_ptr());
    }

    #[test]
    fn test_compile_providers_config() {
        let config = CompileProvidersConfig {
            provider: Some(String::from("prov")),
            probe_format: Some(String::from("probe_{probe}")),
            module: Some(String::from("not_prov")),
        };
        assert_eq!(config.format_probe("prob"), "probe_prob");
        let module = config.module_ident();
        assert_eq!(
            quote::quote! { #module }.to_string(),
            quote::quote! { not_prov }.to_string(),
        );
    }
}
