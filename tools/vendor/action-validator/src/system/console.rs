// The below functions have duplicate implementations for WASM and non-WASM targets.
// Each target might not use all of the functions, but they are all defined for both targets
// for simplicity.
#![allow(dead_code)]

#[cfg(feature = "js")]
mod js_console {
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen(module = "/src/js/system.js")]
    extern "C" {
        #[wasm_bindgen(js_namespace = console, js_name = log)]
        pub fn log(s: &str);

        #[wasm_bindgen(js_namespace = console, js_name = error)]
        pub fn error(s: &str);

        #[wasm_bindgen(js_namespace = console, js_name = warn)]
        pub fn warn(s: &str);
    }
}

#[cfg(feature = "js")]
pub fn log(s: &str) {
    js_console::log(s);
}

#[cfg(not(feature = "js"))]
pub fn log(s: &str) {
    println!("{s}");
}

#[cfg(feature = "js")]
pub fn error(s: &str) {
    js_console::error(s);
}

#[cfg(not(feature = "js"))]
pub fn error(s: &str) {
    eprintln!("{s}");
}

#[cfg(feature = "js")]
pub fn warn(s: &str) {
    js_console::warn(s);
}

#[cfg(not(feature = "js"))]
pub fn warn(s: &str) {
    eprintln!("{s}");
}
