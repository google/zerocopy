// The below functions have duplicate implementations for WASM and non-WASM targets.
// Each target might not use all of the functions, but they are all defined for both targets
// for simplicity.
#![allow(dead_code)]

#[cfg(feature = "js")]
mod js_process {
    use wasm_bindgen::prelude::*;

    #[wasm_bindgen(module = "/src/js/system.js")]
    extern "C" {
        #[wasm_bindgen(js_namespace = process, js_name = exit)]
        pub fn exit(code: i32) -> JsValue;

        #[wasm_bindgen(thread_local_v2, js_namespace = ["process", "stdout"], js_name = isTTY)]
        pub static STDOUT_IS_TTY: bool;
    }
}

#[cfg(feature = "js")]
pub fn exit(code: i32) -> ! {
    js_process::exit(code);
    unreachable!();
}

#[cfg(not(feature = "js"))]
pub fn exit(code: i32) -> ! {
    std::process::exit(code);
}

pub mod stdout {
    #[cfg(feature = "js")]
    pub fn is_tty() -> bool {
        use super::js_process;
        js_process::STDOUT_IS_TTY.with(bool::clone)
    }
}
