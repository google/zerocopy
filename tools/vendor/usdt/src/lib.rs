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

//! Expose USDT probe points from Rust programs.
//!
//! Overview
//! --------
//!
//! This crate provides methods for compiling definitions of [DTrace probes][dtrace] into Rust
//! code, allowing rich, low-overhead instrumentation of [userland][dtrace-usdt] Rust programs.
//!
//! DTrace _probes_ are instrumented points in software, usually corresponding to some important
//! event such as opening a file, writing to standard output, acquiring a lock, and much more.
//! Probes are grouped into _providers_, collections of related probes covering distinct classes
//! functionality. The _syscall_ provider, for example, includes probes for the entry and exit of
//! certain important system calls, such as `write(2)`.
//!
//! USDT probes may be defined in the [D language](#defining-probes-in-d) or [inline in Rust
//! code](#inline-rust-probes). These definitions are used to create macros, which, when called,
//! fire the corresponding DTrace probe. The two methods for defining probes are very similar --
//! one key difference, besides the syntax used to describe them, is that inline probes support any
//! Rust type that is JSON serializable. We'll cover each in turn.
//!
//! Defining probes in D
//! --------------------
//!
//! Users define a provider, with one or more _probe_ functions in the D language. For example:
//!
//! ```d
//! provider my_provider {
//!     probe start_work(uint8_t);
//!     probe start_work(char*, uint8_t);
//! };
//! ```
//!
//! Providers and probes may be named in any way, as long as they form valid Rust identifiers. The
//! names are intended to help understand the behavior of a program, so they should be semantically
//! meaningful. Probes accept zero or more arguments, data that is associated with the probe event
//! itself (timestamps, file descriptors, filesystem paths, etc.). The arguments may be specified
//! as any of the exact bit-width integer types (e.g., `int16_t`), pointers to
//! such integers, or strings (`char *`s). See [Data types](#data-types) for a full list of
//! supported types.
//!
//! Assuming the above is in a file called `"test.d"`, the probes may be compiled into Rust code
//! with:
//!
//! ```ignore
//! usdt::dtrace_provider!("test.d");
//! ```
//!
//! This procedural macro will generate a Rust macro for each probe defined in the provider. Note
//! that for versions of rust prior to 1.66 features may be required; see [the
//! notes](#features) for a discussion. The invocation of `dtrace_provider` (and any required
//! feature directives) **should be at the crate root**, i.e., `src/lib.rs` or `src/main.rs`.
//!
//! One may then call the `start` probe via:
//!
//! ```ignore
//! let x: u8 = 0;
//! my_provider::start_work!(|| x);
//! ```
//!
//! We can see that the macros are defined in a module named by the provider, with one macro for
//! each probe, with the same name. See [below](#configurable-names) for how this naming may be
//! configured.
//!
//! Note that `start_work!` is called with a closure which returns the arguments, rather than the
//! actual arguments themselves. See [below](#probe-arguments) for details. Additionally, as the
//! probes are exposed as _macros_, they should be included in the crate root, before any other
//! module or item which references them.
//!
//! After declaring probes and converting them into Rust code, they must be _registered_ with the
//! DTrace kernel module. Developers should call the function [`register_probes`] as soon as
//! possible in the execution of their program to ensure that probes are available. At this point,
//! the probes should be visible from the `dtrace(1)` command-line tool, and can be enabled or
//! acted upon like any other probe. See [registration](#registration) for a discussion of probe
//! registration, especially in the context of library crates.
//!
//! Inline Rust probes
//! ------------------
//!
//! Writing probes in the D language is convenient and familiar to those who've previously used
//! DTrace. There are a few drawbacks though. Maintaining another file may be annoying or error
//! prone, but more importantly, it provides limited support for Rust's rich type system. In
//! particular, only those types with a clear C analog are currently supported. (See [the full
//! list](#data-types).)
//!
//! More complex, user-defined types can be supported if one defines the probes in Rust directly.
//! In particular, this crate supports any type implementing [`serde::Serialize`][serde], by
//! serializing the type to JSON and using DTrace's native [JSON support][dtrace-json]. Providers
//! can be defined inline by attaching the [`provider`] attribute macro to a module.
//!
//! ```rust,ignore
//! #[derive(serde::Serialize)]
//! pub struct Arg {
//!     pub x: u8,
//!     pub buffer: Vec<i32>,
//! }
//!
//! // A module named `test` describes the provider, and each (empty) function definition in the
//! // module's body generates a probe macro.
//! #[usdt::provider]
//! mod test {
//!     use crate::Arg;
//!     fn start_work(x: u8) {}
//!     fn stop_work(arg: &Arg) {}
//! }
//! ```
//!
//! The `arg` parameter to the `stop` probe will be converted into JSON, and its fields may be
//! accessed in DTrace with the `json` function. The signature is `json(string, key)`, where `key`
//! is used to access the named key of a JSON-encoded string. For example:
//!
//! ```console
//! $ dtrace -n 'stop_work { printf("%s", json(copyinstr(arg0), "ok.buffer[0]")); }'
//! ```
//!
//! would print the first element of the vector `Arg::buffer`.
//!
//! > **Important**: Notice that the JSON key used in the above example to access the data inside
//! DTrace is `"ok.buffer[0]"`. JSON values serialized to DTrace are always `Result` types,
//! because the internal serialization method is _fallible_. So they are always encoded as objects
//! like `{"ok": _}` or `{"err": "some error message"}`. In the error case, the message is
//! created by formatting the `serde_json::error::Error` that describes why serialization failed.
//!
//! > **Note**: It's not possible to define probes in D that accept a serializable type, because the
//! corresponding C type is just `char *`. There's currently no way to disambiguate such a type
//! from an actual string, when generating the Rust probe macros.
//!
//! See the [probe_test_attr] example for a complete example implementing probes in Rust.
//!
//! ## Configurable names
//!
//! When using the attribute macro or build.rs versions of the code-generator, the names of the
//! provider and/or probes may be configured. Specifically, the `probe_format` argument to the
//! attribute macro or `Builder` method sets a format string used to generate the names of the
//! probe macros. This can be any string, and will have the keys `{provider}` and `{probe}`
//! interpolated to the actual names of the provider and probe. As an example, consider a provider
//! named `foo` with a probe named `bar`, and a format string of `probe_{provider}_{probe}` -- the
//! name of the generated probe macro will be `probe_foo_bar`.
//!
//! In addition, when using the attribute macro version, the name of the _provider_ as seen by
//! DTrace can be configured. This defaults to the name of the provider module. For example,
//! consider a module like this:
//!
//! ```ignore
//! #[usdt::provider(provider = "foo")]
//! mod probes {
//!     fn bar() {}
//! }
//! ```
//!
//! The probe `bar` will appear in DTrace as `foo:::bar`, and will be accessible in Rust via the
//! macro `probes::bar!`. Note that it's not possible to rename the probe module when using the
//! attribute macro version.
//!
//! Conversely, one can change the name of the generated provider _module_ when using the builder
//! version, but not the name of the provider as it appears to DTrace. Given a file `"test.d"` that
//! names a provider `foo` and a probe `bar`, consider this code:
//!
//! ```ignore
//! usdt::Builder::new("test.d")
//!     .module("probes")
//!     .build()
//!     .unwrap();
//! ```
//!
//! This probe `bar` will appear in DTrace as `foo:::bar`, but will now be accessible in Rust via
//! the macro `probes::bar!`. Note that it's not possible to rename the provider as it appears in
//! DTrace when using the builder version.
//!
//! Double-underscores
//! ------------------
//!
//! It's a DTrace convention to name probes with dashes between words, rather than underscores. So
//! the probe should be `my-probe` rather than `my_probe`. The former is not a valid Rust
//! identifier, but can be achieved by using _two_ underscores in the **probe** name. This crate
//! internally translates `__` into `-` in such cases. For example, the provider:
//!
//! ```ignore
//! #[usdt::provider("my__provider")]
//! mod probes {
//!     fn my__probe() {};
//! }
//! ```
//!
//! will result in a provider and probe name of `my__provider` and `my-probe`.
//! **Important:** This translation of double-underscores to dashes only occurs
//! in the _probe_ name. Provider names are _not_ modified in any way. This
//! matches the behavior of existing DTrace implementations, and guarantees that
//! providers are similarly named regardless of the target platform.
//!
//! Examples
//! --------
//!
//! See the [probe_test_macro], [probe_test_build], and [probe_test_attr] crates in the github repo
//! for detailed working examples showing how the probes may be defined, included, and used.
//!
//! Probe arguments
//! ---------------
//!
//! Note that the probe macro is called with a closure which returns the actual arguments. There
//! are two reasons for this. First, it makes clear that the probe may not be evaluated if it is
//! not enabled; the arguments should not include function calls which are relied upon for their
//! side-effects, for example. Secondly, it is more efficient. As the lambda is only called if the
//! probe is actually enabled, this allows passing arguments to the probe that are potentially
//! expensive to construct. However, this cost will only be incurred if the probe is actually
//! enabled.
//!
//! Data types
//! ----------
//!
//! Probes support any of the integer types which have a specific bit-width, e.g., `uint16_t`, as
//! well as strings, which should be specified as `char *`. As described [above](#inline-rust-probes),
//! any types implementing `Serialize` may be used, if the probes are defined in Rust directly.
//!
//! Below is the full list of supported types.
//!
//! - `(u?)int(8|16|32|64)_t`
//! - Pointers to the above integer types
//! - `char *`
//! - `T: serde::Serialize` (Only when defining probes in Rust)
//!
//! Currently, up to six (6) arguments are supported, though this limitation may be lifted in the
//! future.
//!
//! Registration
//! ------------
//!
//! USDT probes must be registered with the DTrace kernel module. This is done via a call to the
//! [`register_probes`] function, which must be called before any of the probes become available to
//! DTrace. Ideally, this would be done automatically; however, while there are methods by which
//! that could be achieved, they all pose significant concerns around safety, clarity, and/or
//! explicitness.
//!
//! At this point, it is incumbent upon the _application_ developer to ensure that
//! `register_probes` is called appropriately. This will register all probes in an application,
//! including those defined in a library dependency. To avoid foisting an explicit dependency on
//! the `usdt` crate on downstream applications, library writers should re-export the
//! `register_probes` function with:
//!
//! ```
//! pub use usdt::register_probes;
//! ```
//!
//! The library should clearly document that it defines and uses USDT probes, and that this
//! function should be called by an application. Alternatively, library developers may call this
//! function during some initialization routines required by their library. There is no harm in
//! calling this method multiple times, even in concurrent situations.
//!
//! Unique IDs
//! ----------
//!
//! A common pattern in DTrace scripts is to use a two or more probes to understand a section or
//! span of code. For example, the `syscall:::{entry,return}` probes can be used to time the
//! duration of system calls. Doing this with USDT probes requires a unique identifier, so that
//! multiple probes can be correlated with one another. The [`UniqueId`] type can be used for this
//! purpose. It may be passed as any argument to a probe function, and is guaranteed to be unique
//! between different invocations of the same probe. See the type's documentation for details.
//!
//! About the `asm` feature
//! -----------------------
//!
//! Previous versions of `usdt` used the `asm` feature to enable inline assembly which used to
//! require nightly Rust with old versions of Rust. Currently, all supported versions of Rust
//! support inline assembly, and the `asm` feature is a no-op.
//!
//! The next breaking change to `usdt` will remove the `asm` feature entirely.
//!
//! [dtrace]: https://illumos.org/books/dtrace/preface.html#preface
//! [dtrace-usdt]: https://illumos.org/books/dtrace/chp-usdt.html#chp-usdt
//! [dtrace-json]: https://sysmgr.org/blog/2012/11/29/dtrace_and_json_together_at_last/
//! [probe_test_macro]: https://github.com/oxidecomputer/usdt/tree/master/probe-test-macro
//! [probe_test_build]: https://github.com/oxidecomputer/usdt/tree/master/probe-test-build
//! [probe_test_attr]: https://github.com/oxidecomputer/usdt/tree/master/probe-test-attr
//! [serde]: https://serde.rs

use dof::{extract_dof_sections, Section};
use goblin::Object;
use memmap2::{Mmap, MmapOptions};
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};
use std::{env, fs};

pub use usdt_attr_macro::provider;
#[doc(hidden)]
pub use usdt_impl::to_json;
pub use usdt_impl::{Error, UniqueId};
pub use usdt_macro::dtrace_provider;

/// A simple struct used to build DTrace probes into Rust code in a build.rs script.
#[derive(Debug)]
pub struct Builder {
    source_file: PathBuf,
    out_file: PathBuf,
    config: usdt_impl::CompileProvidersConfig,
}

impl Builder {
    /// Construct a new builder from a path to a D provider definition file.
    pub fn new<P: AsRef<Path>>(file: P) -> Self {
        let source_file = file.as_ref().to_path_buf();
        let mut out_file = source_file.clone();
        out_file.set_extension("rs");
        Builder {
            source_file,
            out_file,
            config: usdt_impl::CompileProvidersConfig::default(),
        }
    }

    /// Set the output filename of the generated Rust code. The default has the same stem as the
    /// provider file, with the `".rs"` extension.
    pub fn out_file<P: AsRef<Path>>(mut self, file: P) -> Self {
        self.out_file = file.as_ref().to_path_buf();
        self.out_file.set_extension("rs");
        self
    }

    /// Set the format for the name of generated probe macros.
    ///
    /// The provided format may include the tokens `{provider}` and `{probe}`, which will be
    /// substituted with the names of the provider and probe. The default is `"{probe}"`.
    pub fn probe_format(mut self, format: &str) -> Self {
        self.config.probe_format = Some(format.to_string());
        self
    }

    /// Set the name of the module containing the generated probe macros.
    pub fn module(mut self, module: &str) -> Self {
        self.config.module = Some(module.to_string());
        self
    }

    /// Generate the Rust code from the D provider file, writing the result to the output file.
    pub fn build(self) -> Result<(), Error> {
        let source = fs::read_to_string(self.source_file)?;
        let tokens = usdt_impl::compile_provider_source(&source, &self.config)?;
        let mut out_file = Path::new(&env::var("OUT_DIR")?).to_path_buf();
        out_file.push(
            self.out_file
                .file_name()
                .expect("Could not extract filename"),
        );
        fs::write(out_file, tokens.to_string().as_bytes())?;
        Ok(())
    }
}

/// Register an application's probes with DTrace.
///
/// This function collects the probes defined in an application, and forwards them to the DTrace
/// kernel module. This _must_ be done for the probes to be visible via the `dtrace(1)` tool. See
/// [probe_test_macro] for a detailed example.
///
/// Notes
/// -----
///
/// This function registers all probes in a process's binary image, regardless of which crate
/// actually defines the probes. It's also safe to call this function multiple times, even in
/// concurrent situations. Probes will be registered at most once.
///
/// [probe_test_macro]: https://github.com/oxidecomputer/usdt/tree/master/probe-test-macro
pub fn register_probes() -> Result<(), Error> {
    usdt_impl::register_probes()
}

/// Extract embedded USDT probe records from a file.
///
/// DTrace in general works by storing metadata about the probes in a special
/// section of the resulting binaries. These sections are generated by the
/// platform compiler and linker on systems with linker support (macOS), or
/// created manually by this crate on other platforms. In either case, this
/// method extracts the metadata as a [`Section`] from the object file, if it
/// can be found.
pub fn probe_records<P: AsRef<Path>>(path: P) -> Result<Vec<Section>, Error> {
    // Extract DOF section data, which is applicable for an object file built using this crate on
    // macOS, or generally using the platform's dtrace tool, i.e., `dtrace -G` and compiler.
    let dof_sections = extract_dof_sections(&path).map_err(|_| Error::InvalidFile)?;
    if !dof_sections.is_empty() {
        return Ok(dof_sections);
    }

    // File contains no DOF data. Try to parse out the ASM records inserted by the `usdt` crate.
    let file = OpenOptions::new().read(true).create(false).open(path)?;
    let (offset, len) = locate_probe_section(&file).ok_or(Error::InvalidFile)?;

    // Remap only the probe section itself as mutable, using a private
    // copy-on-write mapping to avoid writing to disk in any circumstance.
    let mut map = unsafe { MmapOptions::new().offset(offset).len(len).map_copy(&file)? };
    usdt_impl::record::process_section(&mut map, /* register = */ false).map(|s| vec![s])
}

// Return the offset and size of the file's probe record section, if it exists.
fn locate_probe_section(file: &File) -> Option<(u64, usize)> {
    let map = unsafe { Mmap::map(file) }.ok()?;
    match Object::parse(&map).ok()? {
        Object::Elf(object) => {
            // Try to find our special `set_dtrace_probes` section from the section headers. These
            // may not exist, e.g., if the file has been stripped. In that case, we look for the
            // special __start and __stop symbols themselves.
            if let Some(section) = object.section_headers.iter().find(|header| {
                if let Some(name) = object.shdr_strtab.get_at(header.sh_name) {
                    name == "set_dtrace_probes"
                } else {
                    false
                }
            }) {
                Some((section.sh_offset, section.sh_size as usize))
            } else {
                // Failed to look up the section directly, iterate over the symbols.
                let mut bounds = object.syms.iter().filter(|symbol| {
                    matches!(
                        object.strtab.get_at(symbol.st_name),
                        Some("__start_set_dtrace_probes") | Some("__stop_set_dtrace_probes")
                    )
                });

                if let (Some(start), Some(stop)) = (bounds.next(), bounds.next()) {
                    Some((start.st_value, (stop.st_value - start.st_value) as usize))
                } else {
                    None
                }
            }
        }
        Object::Mach(goblin::mach::Mach::Binary(object)) => {
            // Try to find our special `__dtrace_probes` section from the section headers.
            for (section, _) in object.segments.sections().flatten().flatten() {
                if section.sectname.starts_with(b"__dtrace_probes") {
                    return Some((section.offset as u64, section.size as usize));
                }
            }

            // Failed to look up the section directly, iterate over the symbols.
            if let Some(syms) = object.symbols {
                let mut bounds = syms.iter().filter_map(|symbol| {
                    if let Ok((name, nlist)) = symbol {
                        if name.contains("__dtrace_probes") {
                            Some(nlist.n_value)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                });
                if let (Some(start), Some(stop)) = (bounds.next(), bounds.next()) {
                    Some((start, (stop - start) as usize))
                } else {
                    None
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
