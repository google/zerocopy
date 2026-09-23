use std::env;

fn main() {
    println!("cargo::rerun-if-env-changed=FIXTURE_ALLOCATOR");

    match env::var("FIXTURE_ALLOCATOR") {
        Err(env::VarError::NotPresent) => {
            println!("cargo::rustc-cfg=fixture_allocator=\"system\"");
        }
        Ok(value) => match value.as_str() {
            "system" => {
                println!("cargo::rustc-cfg=fixture_allocator=\"system\"");
            }
            "arena" => {
                println!("cargo::rustc-cfg=fixture_allocator=\"arena\"");
            }
            "arena-stop" => {
                println!("cargo::rustc-cfg=fixture_allocator=\"arena\"");
                panic!("arena-stop rejects this build after allocator emission");
            }
            _ => panic!("unsupported FIXTURE_ALLOCATOR value"),
        },
        Err(env::VarError::NotUnicode(_)) => {
            panic!("FIXTURE_ALLOCATOR must be valid Unicode");
        }
    }
}
