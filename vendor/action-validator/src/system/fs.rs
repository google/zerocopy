// The below functions have duplicate implementations for WASM and non-WASM targets.
// Each target might not use all of the functions, but they are all defined for both targets
// for simplicity.
#![allow(dead_code)]

use std::path::Path;

#[cfg(feature = "js")]
mod js_fs {
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen(module = "/src/js/system.js")]
    extern "C" {
        #[wasm_bindgen(catch, js_namespace = fs, js_name = readFileSync)]
        pub fn read_file_sync(path: &str, encoding: &str) -> Result<String, js_sys::Error>;
    }
}

#[cfg(feature = "js")]
pub fn read_to_string<P>(path: P) -> Result<String, String>
where
    P: AsRef<Path>,
{
    js_fs::read_file_sync(path.as_ref().to_string_lossy().as_ref(), "utf8")
        .map_err(|e| format!("{}", e.to_string()))
}

#[cfg(not(feature = "js"))]
pub fn read_to_string<P>(path: P) -> Result<String, String>
where
    P: AsRef<Path>,
{
    std::fs::read_to_string(path).map_err(|e| e.to_string())
}
