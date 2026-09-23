use std::env;

fn main() {
    println!("cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR");
    println!(
        "cargo::rustc-check-cfg=cfg(fixture_allocator, values(\"system\", \"arena\"))"
    );

    let allocator = match env::var("FIXTURE_ALLOCATOR") {
        Ok(value) => value,
        Err(env::VarError::NotPresent) => "system".to_owned(),
        Err(env::VarError::NotUnicode(_)) => {
            panic!("FIXTURE_ALLOCATOR must be valid Unicode")
        }
    };
    match allocator.as_str() {
        "system" | "arena" => {
            println!("cargo::rustc-cfg=fixture_allocator=\"{allocator}\"");
        }
        _ => panic!("FIXTURE_ALLOCATOR must be `system` or `arena`"),
    }
}
