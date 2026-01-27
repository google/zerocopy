//! USDT implementation on platforms with linker support (macOS).
//!
//! On systems with linker support for the compile-time construction of DTrace
//! USDT probes we can lean heavily on those mechanisms. Rather than interpreting
//! the provider file ourselves, we invoke the system's `dtrace -h` to generate a C
//! header file. That header file contains the linker directives that convey
//! information from the provider definition such as types and stability. We parse
//! that header file and generate code that effectively reproduces in Rust the
//! equivalent of what we would see in C.
//!
//! For example, the header file might contain code like this:
//! ```ignore
//! #define FOO_STABILITY "___dtrace_stability$foo$v1$1_1_0_1_1_0_1_1_0_1_1_0_1_1_0"
//! #define FOO_TYPEDEFS "___dtrace_typedefs$foo$v2"
//!
//! #if !defined(DTRACE_PROBES_DISABLED) || !DTRACE_PROBES_DISABLED
//!
//! #define	FOO_BAR() \
//! do { \
//! 	__asm__ volatile(".reference " FOO_TYPEDEFS); \
//! 	__dtrace_probe$foo$bar$v1(); \
//! 	__asm__ volatile(".reference " FOO_STABILITY); \
//! } while (0)
//! ```
//!
//! In rust, we'll want the probe site to look something like this:
//! ```ignore
//! unsafe extern "C" {
//!     #[link_name = "__dtrace_stability$foo$v1$1_1_0_1_1_0_1_1_0_1_1_0_1_1_0"]
//!     fn stability();
//!     #[link_name = "__dtrace_probe$foo$bar$v1"]
//!     fn probe();
//!     #[link_name = "__dtrace_typedefs$foo$v2"]
//!     fn typedefs();
//!
//! }
//! unsafe {
//!     asm!(".reference {}", sym typedefs);
//!     probe();
//!     asm!(".reference {}", sym stability);
//! }
//! ```
//! There are a few things to note above:
//! 1. We cannot simply generate code with the symbol name embedded in the asm!
//!    block e.g. `asm!(".reference __dtrace_typedefs$foo$v2")`. The asm! macro
//!    removes '$' characters yielding the incorrect symbol.
//! 2. The header file stability and typedefs contain three '_'s whereas the
//!    Rust code has just two. The `sym <symbol_name>` apparently prepends an
//!    extra underscore in this case.
//! 3. The probe needs to be a function type (because we call it), but the types
//!    of the `stability` and `typedefs` symbols could be anything--we just need
//!    a symbol name we can reference for the asm! macro that won't get garbled.

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

use crate::{common, DataType, Provider};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::{
    collections::BTreeMap,
    convert::TryFrom,
    io::Write,
    process::{Command, Stdio},
};

/// Compile a DTrace provider definition into Rust tokens that implement its probes.
pub fn compile_provider_source(
    source: &str,
    config: &crate::CompileProvidersConfig,
) -> Result<TokenStream, crate::Error> {
    let dfile = dtrace_parser::File::try_from(source)?;
    let header = build_header_from_provider(&source)?;
    let provider_info = extract_providers(&header);
    let providers = dfile
        .providers()
        .into_iter()
        .map(|provider| {
            let provider = Provider::from(provider);
            // Ensure that the name of the module in the config is set, either by the caller or
            // defaulting to the provider name.
            let config = crate::CompileProvidersConfig {
                provider: Some(provider.name.clone()),
                probe_format: config.probe_format.clone(),
                module: match &config.module {
                    None => Some(provider.name.clone()),
                    other => other.clone(),
                },
            };
            compile_provider(&provider, &provider_info[&provider.name], &config)
        })
        .collect::<Vec<_>>();
    Ok(quote! {
        #(#providers)*
    })
}

pub fn compile_provider_from_definition(
    provider: &Provider,
    config: &crate::CompileProvidersConfig,
) -> TokenStream {
    // Unwrap safety: The type signature confirms that `provider` is valid.
    let header = build_header_from_provider(&provider.to_d_source()).unwrap();
    let provider_info = extract_providers(&header);
    let provider_tokens = compile_provider(provider, &provider_info[&provider.name], config);
    quote! {
        #provider_tokens
    }
}

fn compile_provider(
    provider: &Provider,
    provider_info: &ProviderInfo,
    config: &crate::CompileProvidersConfig,
) -> TokenStream {
    let mut probe_impls = Vec::new();
    for probe in provider.probes.iter() {
        probe_impls.push(compile_probe(
            provider,
            &probe.name,
            config,
            provider_info,
            &probe.types,
        ));
    }
    let module = config.module_ident();
    quote! {
        pub(crate) mod #module {
            #(#probe_impls)*
        }
    }
}

fn compile_probe(
    provider: &Provider,
    probe_name: &str,
    config: &crate::CompileProvidersConfig,
    provider_info: &ProviderInfo,
    types: &[DataType],
) -> TokenStream {
    // Retrieve the string names and the Rust identifiers used for the extern functions.
    // These are provided by the macOS linker, but have invalid Rust identifier names, like
    // `foo$bar`. We name them with valid Rust idents, and specify their link name as that of the
    // function provided by the macOS linker.
    let stability = &provider_info.stability;
    let stability_fn = format_ident!("stability");
    let typedefs = &provider_info.typedefs;
    let typedef_fn = format_ident!("typedefs");
    let is_enabled = &provider_info.is_enabled[probe_name];
    let is_enabled_fn = format_ident!("{}_{}_enabled", &provider.name, probe_name);

    // The probe function is a little different. We prefix it with `__` because otherwise it has
    // the same name as the macro itself, which leads to conflicts.
    let probe = &provider_info.probes[probe_name];
    let extern_probe_fn = format_ident!("__{}", config.probe_ident(probe_name));

    let ffi_param_list = types.iter().map(|typ| {
        let ty = typ.to_rust_ffi_type();
        syn::parse2::<syn::FnArg>(quote! { _: #ty }).unwrap()
    });
    let (unpacked_args, in_regs) = common::construct_probe_args(types);
    let type_check_fn =
        common::construct_type_check(&provider.name, probe_name, &provider.use_statements, types);

    #[cfg(target_arch = "x86_64")]
    let call_instruction = quote! { "call {extern_probe_fn}" };
    #[cfg(target_arch = "aarch64")]
    let call_instruction = quote! { "bl {extern_probe_fn}" };
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    compile_error!("USDT only supports x86_64 and AArch64 architectures");

    let impl_block = quote! {
        unsafe extern "C" {
            #[allow(unused)]
            #[link_name = #stability]
            fn stability();

            #[allow(unused)]
            #[link_name = #typedefs]
            fn typedefs();

            #[allow(unused)]
            #[link_name = #is_enabled]
            fn #is_enabled_fn() -> i32;

            #[allow(unused)]
            #[link_name = #probe]
            fn #extern_probe_fn(#(#ffi_param_list,)*);
        }
        unsafe {
            if #is_enabled_fn() != 0 {
                #unpacked_args
                #type_check_fn
                ::std::arch::asm!(
                    ".reference {typedefs}",
                    #call_instruction,
                    ".reference {stability}",
                    typedefs = sym #typedef_fn,
                    extern_probe_fn = sym #extern_probe_fn,
                    stability = sym #stability_fn,
                    #in_regs
                    options(nomem, nostack, preserves_flags)
                );
            }
        }
    };

    common::build_probe_macro(config, probe_name, types, impl_block)
}

#[derive(Debug, Default, Clone)]
struct ProviderInfo {
    pub stability: String,
    pub typedefs: String,
    pub is_enabled: BTreeMap<String, String>,
    pub probes: BTreeMap<String, String>,
}

fn extract_providers(header: &str) -> BTreeMap<String, ProviderInfo> {
    let mut providers = BTreeMap::new();
    for line in header.lines() {
        if let Some((provider_name, stability)) = is_stability_line(&line) {
            let mut info = ProviderInfo::default();
            info.stability = stability.to_string();
            providers.insert(provider_name.to_string(), info);
        }
        if let Some((provider_name, typedefs)) = is_typedefs_line(&line) {
            providers.get_mut(provider_name).unwrap().typedefs = typedefs.to_string();
        }
        if let Some((provider_name, probe_name, enabled)) = is_enabled_line(&line) {
            providers
                .get_mut(provider_name)
                .unwrap()
                .is_enabled
                .insert(probe_name.to_string(), enabled.to_string());
        }
        if let Some((provider_name, probe_name, probe)) = is_probe_line(&line) {
            providers
                .get_mut(provider_name)
                .unwrap()
                .probes
                .insert(probe_name.to_string(), probe.to_string());
        }
    }
    providers
}

// Return the (provider_name, stability) from a line, if it looks like the appropriate #define'd
// line from the autogenerated header file.
fn is_stability_line(line: &str) -> Option<(&str, &str)> {
    contains_needle(line, "___dtrace_stability$")
}

// Return the (provider_name, typedefs) from a line, if it looks like the appropriate #define'd
// line from the autogenerated header file.
fn is_typedefs_line(line: &str) -> Option<(&str, &str)> {
    contains_needle(line, "___dtrace_typedefs$")
}

fn contains_needle<'a>(line: &'a str, needle: &str) -> Option<(&'a str, &'a str)> {
    if let Some(index) = line.find(needle) {
        let rest = &line[index + needle.len()..];
        let provider_end = rest.find("$").unwrap();
        let provider_name = &rest[..provider_end];
        // NOTE: The extra offset to the start index works as follows. The symbol name really needs
        // to be `___dtrace_stability$...`. But that symbol name will have a "_" prefixed to it
        // during compilation, so we remove the leading one here, knowing it will be added back.
        let needle = &line[index + 1..line.len() - 1];
        Some((provider_name, needle))
    } else {
        None
    }
}

// Return the (provider, probe, enabled) from a line, if it looks like the appropriate extern
// function declaration from the autogenerated header file.
fn is_enabled_line(line: &str) -> Option<(&str, &str, &str)> {
    contains_needle2(line, "extern int __dtrace_isenabled$")
}

// Return the (provider, probe, probe) from a line, if it looks like the appropriate extern
// function declaration from the autogenerated header file.
fn is_probe_line(line: &str) -> Option<(&str, &str, &str)> {
    contains_needle2(line, "extern void __dtrace_probe$")
}

fn contains_needle2<'a>(line: &'a str, needle: &str) -> Option<(&'a str, &'a str, &'a str)> {
    if let Some(index) = line.find(needle) {
        let rest = &line[index + needle.len()..];
        let provider_end = rest.find("$").unwrap();
        let provider_name = &rest[..provider_end];

        let rest = &rest[provider_end + 1..];
        let probe_end = rest.find("$").unwrap();
        let probe_name = &rest[..probe_end];

        let end = line.rfind("(").unwrap();
        let start = line.find(line.split(" ").nth(2).unwrap()).unwrap();
        let needle = &line[start..end];
        Some((provider_name, probe_name, needle))
    } else {
        None
    }
}

fn build_header_from_provider(source: &str) -> Result<String, crate::Error> {
    let mut child = Command::new("dtrace")
        .arg("-h")
        .arg("-s")
        .arg("/dev/stdin")
        .arg("-o")
        .arg("/dev/stdout")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    {
        let stdin = child.stdin.as_mut().ok_or(crate::Error::DTraceError)?;
        stdin
            .write_all(source.as_bytes())
            .map_err(|_| crate::Error::DTraceError)?;
    }
    let output = child.wait_with_output()?;
    String::from_utf8(output.stdout).map_err(|_| crate::Error::DTraceError)
}

pub fn register_probes() -> Result<(), crate::Error> {
    // This function is a NOP, since we're using Apple's linker to create the DOF and call ioctl(2)
    // to send it to the driver.
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Probe;

    #[test]
    fn test_is_stability_line() {
        let line = "this line is ok \"___dtrace_stability$foo$bar\"";
        let result = is_stability_line(line);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "foo");
        assert_eq!(result.unwrap().1, "__dtrace_stability$foo$bar");
        assert!(is_stability_line("bad").is_none());
    }

    #[test]
    fn test_is_typedefs_line() {
        let line = "this line is ok \"___dtrace_typedefs$foo$bar\"";
        let result = is_typedefs_line(line);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "foo");
        assert_eq!(result.unwrap().1, "__dtrace_typedefs$foo$bar");
        assert!(is_typedefs_line("bad").is_none());
    }

    #[test]
    fn test_is_enabled_line() {
        let line = "extern int __dtrace_isenabled$foo$bar$xxx(void);";
        let result = is_enabled_line(line);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "foo");
        assert_eq!(result.unwrap().1, "bar");
        assert_eq!(result.unwrap().2, "__dtrace_isenabled$foo$bar$xxx");
        assert!(is_enabled_line("bad").is_none());
    }

    #[test]
    fn test_is_probe_line() {
        let line = "extern void __dtrace_probe$foo$bar$xxx(whatever);";
        let result = is_probe_line(line);
        assert!(result.is_some());
        assert_eq!(result.unwrap().0, "foo");
        assert_eq!(result.unwrap().1, "bar");
        assert_eq!(result.unwrap().2, "__dtrace_probe$foo$bar$xxx");
        assert!(is_enabled_line("bad").is_none());
    }

    #[test]
    fn test_compile_probe() {
        let provider_name = "foo";
        let probe_name = "bar";
        let extern_probe_name = "__bar";
        let is_enabled = "__dtrace_isenabled$foo$bar$xxx";
        let probe = "__dtrace_probe$foo$bar$xxx";
        let stability = "__dtrace_probe$foo$v1$1_1_1";
        let typedefs = "__dtrace_typedefs$foo$v2";
        let types = vec![];
        let provider = Provider {
            name: provider_name.to_string(),
            probes: vec![Probe {
                name: probe_name.to_string(),
                types: types.clone(),
            }],
            use_statements: vec![],
        };

        let mut is_enabled_map = BTreeMap::new();
        is_enabled_map.insert(String::from(probe_name), String::from(is_enabled));
        let mut probes_map = BTreeMap::new();
        probes_map.insert(String::from(probe_name), String::from(probe));
        let provider_info = ProviderInfo {
            stability: String::from(stability),
            typedefs: String::from(typedefs),
            is_enabled: is_enabled_map,
            probes: probes_map,
        };

        let tokens = compile_probe(
            &provider,
            probe_name,
            &crate::CompileProvidersConfig {
                provider: Some(provider_name.to_string()),
                ..Default::default()
            },
            &provider_info,
            &types,
        );

        let output = tokens.to_string();

        let needle = format!("link_name = \"{is_enabled}\"", is_enabled = is_enabled);
        assert!(output.contains(&needle));

        let needle = format!("link_name = \"{probe}\"", probe = probe);
        assert!(output.contains(&needle));

        let needle = format!(
            "fn {provider_name}_{probe_name}",
            provider_name = provider_name,
            probe_name = probe_name
        );
        assert!(output.contains(&needle));

        let needles = &[
            "asm ! (\".reference {typedefs}\"",
            #[cfg(target_arch = "x86_64")]
            "call {extern_probe_fn}",
            #[cfg(target_arch = "aarch64")]
            "bl {extern_probe_fn}",
            "\".reference {stability}",
            "typedefs = sym typedefs",
            &format!(
                "probe_fn = sym {extern_probe_name}",
                extern_probe_name = extern_probe_name
            ),
            "stability = sym stability",
        ];
        for needle in needles.iter() {
            assert!(
                output.contains(needle),
                "needle {} not found in haystack {}",
                needle,
                output,
            );
        }
    }
}
