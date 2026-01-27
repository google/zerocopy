//! Prototype proc-macro crate for parsing a DTrace provider definition into Rust code.

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

use std::iter::FromIterator;
use std::{fs, path::Path};

use quote::quote;
use syn::{parse_macro_input, Lit};

use usdt_impl::compile_provider_source;

/// Generate DTrace probe macros from a provider definition file.
///
/// This macro parses a DTrace provider.d file, given as a single literal string path. It then
/// generates a Rust macro for each of the DTrace probe definitions.
///
/// For example, let's say the file `"test.d"` has the following contents:
///
/// ```ignore
/// provider test {
///     probe start(uint8_t);
///     probe stop(char *, uint8_t);
/// };
/// ```
///
/// In a Rust library or application, write:
///
/// ```ignore
/// dtrace_provider!("test.d");
/// ```
///
/// The macro looks for the file relative to the root of the package, so `"test.d"`
/// in this case would be in the same directory as `"Cargo.toml"`.
///
/// By default probe macros are named `{provider}_{probe}!`. Arguments are passed
/// via a closure that returns a tuple. Note that the provided closure is only
/// evaluated when the probe is enabled. One can then add points of instrumentation
/// by invoking the macro:
///
/// ```ignore
/// fn do_stuff(count: u8, name: String) {
///     // doing stuff
///     test_stop!(|| (name, count));
/// }
/// ```
///
/// The probe macro names can be customized by adding `, format =
/// my_prefix_{provider}_{probe}` to the macro invocation where `{provider}` and
/// `{probe}` are optional and will be substituted with the actual provider and
/// probe names:
///
/// ```ignore
/// dtrace_provider!("test.d", format = "dtrace_{provider}_{probe}");
/// ```
///
/// Note
/// ----
/// The only supported types are integers of specific bit-width (e.g., `uint16_t`),
/// pointers to integers, and `char *`.
#[proc_macro]
pub fn dtrace_provider(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let mut tokens = item.into_iter().collect::<Vec<proc_macro::TokenTree>>();

    let comma_index = tokens
        .iter()
        .enumerate()
        .find_map(|(i, token)| match token {
            proc_macro::TokenTree::Punct(p) if p.as_char() == ',' => Some(i),
            _ => None,
        });

    // Split off the tokens after the comma if there is one.
    let rest = if let Some(index) = comma_index {
        let mut rest = tokens.split_off(index);
        let _ = rest.remove(0);
        rest
    } else {
        Vec::new()
    };

    // Parse the config from the remaining tokens.
    let config: usdt_impl::CompileProvidersConfig = serde_tokenstream::from_tokenstream(
        &proc_macro2::TokenStream::from(proc_macro::TokenStream::from_iter(rest)),
    )
    .unwrap();

    let first_item = proc_macro::TokenStream::from_iter(tokens);
    let tok = parse_macro_input!(first_item as Lit);
    let filename = match tok {
        Lit::Str(f) => f.value(),
        _ => panic!("DTrace provider must be a single literal string filename"),
    };
    let source = if filename.ends_with(".d") {
        let dir = std::env::var("CARGO_MANIFEST_DIR").map_or_else(
            |_| std::env::current_dir().unwrap(),
            |s| Path::new(&s).to_path_buf(),
        );

        let path = dir.join(&filename);
        fs::read_to_string(path).unwrap_or_else(|_| {
            panic!(
                "Could not read D source file \"{}\" in {:?}",
                &filename, dir,
            )
        })
    } else {
        filename.clone()
    };
    match compile_provider_source(&source, &config) {
        Ok(provider) => provider.into(),
        Err(e) => {
            let message = format!(
                "Error building provider definition in \"{}\"\n\n{}",
                filename, e
            );
            let out = quote! {
                compile_error!(#message);
            };
            out.into()
        }
    }
}
