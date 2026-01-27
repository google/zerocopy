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

//! The SystemTap probe version 3 of the USDT crate.
//!
//! Used on Linux platforms without DTrace.
//!
//! Name of the file comes from the `NT_STAPSDT` SystemTap probe descriptors'
//! type name in `readelf` output.

#[path = "stapsdt/args.rs"]
mod args;

use crate::{common, DataType};
use crate::{Probe, Provider};
use args::format_argument;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::convert::TryFrom;

pub fn compile_provider_source(
    source: &str,
    config: &crate::CompileProvidersConfig,
) -> Result<TokenStream, crate::Error> {
    let dfile = dtrace_parser::File::try_from(source)?;
    let providers = dfile
        .providers()
        .iter()
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
            compile_provider(&provider, &config)
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
    compile_provider(provider, config)
}

fn compile_provider(provider: &Provider, config: &crate::CompileProvidersConfig) -> TokenStream {
    let probe_impls = provider
        .probes
        .iter()
        .map(|probe| compile_probe(provider, probe, config))
        .collect::<Vec<_>>();
    let module = config.module_ident();
    quote! {
        pub(crate) mod #module {
            #(#probe_impls)*
        }
    }
}

/// ## Emit a SystemTap probe (version 3 format).
///
/// Source: https://sourceware.org/systemtap/wiki/UserSpaceProbeImplementation
///
/// A STAPSDT probe expands to a single `nop` in the generated code (the `nop`
/// instruction is generated in `compile_probe`) and a non-allocated ELF note.
/// Additionally, a special `.stapsdt.base` section is needed (once only) for
/// detecting prelink address adjustments (its contents do not matter at all).
///
/// This method generates the ELF note assembly and an `.ifndef _.stapsdt.base`
/// section for the address adjustments. Additionally, this method generates a
/// 16 bit "semaphore" (counter) and links it to the ELF note. This semaphore
/// is then used to gate invocations of the probe by reading its value at
/// runtime and checking it against 0. A value of 0 means that no consumers are
/// currently active and the probe and any parameter massaging work can be
/// skipped.
///
/// ### Summary
///
/// A STAPSDT probe in plain pseudo-Rust would look roughly like this:
/// ```rust,ignore
/// // WARNING: PSEUDO-CODE!
///
/// #[linkage = "weak", visibility = "hidden"]
/// static __usdt_sema_provider_probe: SyncUnsafeCell<u16> = SyncUnsafeCell::new(0);
///
/// let is_enabled = unsafe { __usdt_sema_provider_probe.get().read_volatile() } > 0;
///
/// if is_enabled {
///   let arg1: u64 = get_arg1();
///   let arg2: u32 = get_arg2();
///   let arg3: *const u8 = get_arg3();
///   const {
///     // Build time: Generate a USDT ELF header pointing to this location as
///     // the probe location with probe argument types defined as generics
///     // and provider name, probe name, and semaphore pointer given as
///     // parameters.
///     usdt::define::<(u64, u32, *const u8)>("provider", "probe", &__usdt_sema_provider_probe);
///   }
///   core::arch::nop();
/// }
/// ```
///
/// When probing is started using SystemTap, perf, an eBPF program, or other,
/// then the above `nop()` instruction will turn into an interrupt instruction
/// that transfers control to the kernel which will then run the probe's kernel
/// side code (such as an eBPF program).
fn emit_probe_record(prov: &str, probe: &str, types: Option<&[DataType]>) -> String {
    let sema_name = format!("__usdt_sema_{}_{}", prov, probe);
    let arguments = types.map_or_else(String::new, |types| {
        types
            .iter()
            .enumerate()
            .map(format_argument)
            .collect::<Vec<_>>()
            .join(" ")
    });
    format!(
        r#"// First define the semaphore
// Note: This uses ifndef to make sure the same probe name can be used
// in multiple places but they all use the same semaphore. This can be
// used to eg. guard additional preparatory work far away from the
// actual probe site that will only be used by the probe.
.ifndef {sema_name}
        .pushsection .probes, "aw", "progbits"
        .weak {sema_name}
        .hidden {sema_name}
{sema_name}:
        .zero 2
        .type {sema_name}, @object
        .size {sema_name}, 2
        .popsection
.endif
// Second define the actual USDT probe
        .pushsection .note.stapsdt, "", "note"
        .balign 4
        .4byte 992f-991f, 994f-993f, 3    // length, type
991:
        .asciz "stapsdt"        // vendor string
992:
        .balign 4
993:
        .8byte 990b             // probe PC address
        .8byte _.stapsdt.base   // link-time sh_addr of base .stapsdt.base section
        .8byte {sema_name}      // probe semaphore address
        .asciz "{prov}"         // provider name
        .asciz "{probe}"        // probe name
        .asciz "{arguments}"    // argument format (null-terminated string)
994:
        .balign 4
        .popsection
// Finally define (if not defined yet) the base used to detect prelink
// address adjustments.
.ifndef _.stapsdt.base
        .pushsection .stapsdt.base, "aGR", "progbits", .stapsdt.base, comdat
        .weak _.stapsdt.base
        .hidden _.stapsdt.base
_.stapsdt.base:
        .space 1
        .size _.stapsdt.base, 1
        .popsection
.endif"#,
        prov = prov,
        probe = probe.replace("__", "-"),
        arguments = arguments,
    )
}

fn compile_probe(
    provider: &Provider,
    probe: &Probe,
    config: &crate::CompileProvidersConfig,
) -> TokenStream {
    let (unpacked_args, in_regs) = common::construct_probe_args(&probe.types);
    let probe_rec = emit_probe_record(&provider.name, &probe.name, Some(&probe.types));
    let type_check_fn = common::construct_type_check(
        &provider.name,
        &probe.name,
        &provider.use_statements,
        &probe.types,
    );

    let sema_name = format_ident!("__usdt_sema_{}_{}", provider.name, probe.name);
    let impl_block = quote! {
        unsafe extern "C" {
            // Note: C libraries use a struct containing an unsigned short
            // for the semaphore counter. Using just a u16 here directly
            // offers the slightest risk that on some platforms the struct
            // wrapping could be loadbearing but it is not to the best of
            // knowledge.
            static #sema_name: u16;
        }

        let is_enabled: u16;
        unsafe {
            is_enabled = (&raw const #sema_name).read_volatile();
        }

        if is_enabled != 0 {
            #unpacked_args
            #type_check_fn
            #[allow(named_asm_labels)]
            unsafe {
                ::std::arch::asm!(
                    "990:   nop",
                    #probe_rec,
                    #in_regs
                    options(nomem, nostack, preserves_flags)
                );
            }
        }
    };
    common::build_probe_macro(config, &probe.name, &probe.types, impl_block)
}

pub fn register_probes() -> Result<(), crate::Error> {
    Ok(())
}
