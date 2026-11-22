// `.await` inside an `async fn` (the reproducer of rust-lang/rust issue 153733).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

async fn other() {}

pub async fn uhoh() {
    other().await;
}
