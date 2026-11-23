#!/usr/bin/env python3
"""Revalidate serde_json duplicate-key and #[serde(flatten)] behavior."""

import os
import subprocess
import tempfile

MAIN_RS = r'''
use serde::Deserialize;
use serde_json::Value;
use std::collections::BTreeMap;

#[derive(Debug, Deserialize)]
struct StrictReceipt {
    taint_reasons: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct FlattenReceipt {
    taint_reasons: Vec<String>,
    #[serde(flatten)]
    extra: BTreeMap<String, Value>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct DenyReceipt {
    taint_reasons: Vec<String>,
}

fn main() {
    let dup_top = r#"{"taint_reasons":["sorry_in_proof"],"taint_reasons":[]}"#;
    let dup_unknown = r#"{"taint_reasons":[],"new_taint":["a"],"new_taint":[]}"#;
    let dup_nested = r#"{"taint_reasons":[],"meta":{"a":1,"a":2}}"#;
    let unknown_field = r#"{"taint_reasons":[],"kernelsSkipped":["nanoda"]}"#;
    let trailing = r#"{"taint_reasons":[]} {"taint_reasons":["x"]}"#;

    println!("1. Value dup_top: {:?}", serde_json::from_str::<Value>(dup_top));
    println!("2. StrictReceipt dup_top: {:?}", serde_json::from_str::<StrictReceipt>(dup_top));
    println!("3. FlattenReceipt dup_top: {:?}", serde_json::from_str::<FlattenReceipt>(dup_top));
    println!("4. FlattenReceipt dup_unknown: {:?}", serde_json::from_str::<FlattenReceipt>(dup_unknown));
    println!("5. FlattenReceipt dup_nested: {:?}", serde_json::from_str::<FlattenReceipt>(dup_nested));
    println!("6. DenyReceipt unknown_field: {:?}", serde_json::from_str::<DenyReceipt>(unknown_field));
    println!("7. FlattenReceipt unknown_field: {:?}", serde_json::from_str::<FlattenReceipt>(unknown_field));
    println!("8. StrictReceipt trailing: {:?}", serde_json::from_str::<StrictReceipt>(trailing));
}
'''


def main() -> None:
    with tempfile.TemporaryDirectory() as td:
        os.makedirs(os.path.join(td, "src"))
        with open(os.path.join(td, "Cargo.toml"), "w", encoding="utf-8") as f:
            f.write(
                '[package]\nname = "serde_probe"\nversion = "0.1.0"\nedition = "2021"\n\n'
                '[dependencies]\nserde = { version = "1", features = ["derive"] }\nserde_json = "1"\n'
            )
        with open(os.path.join(td, "src", "main.rs"), "w", encoding="utf-8") as f:
            f.write(MAIN_RS)
        subprocess.check_call(["cargo", "run", "--quiet"], cwd=td)


if __name__ == "__main__":
    main()
