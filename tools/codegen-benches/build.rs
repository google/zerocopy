use std::{env, fs, path::PathBuf};

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let dest_path = PathBuf::from(out_dir).join("benches.rs");

    let benches_dir = PathBuf::from(&manifest_dir).join("../../benches");
    let mut out = String::new();

    let mut entries: Vec<_> = fs::read_dir(&benches_dir)
        .unwrap()
        .map(|res| res.unwrap())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        let name = path.file_stem().unwrap().to_str().unwrap();
        if name != "formats" {
            let abs_path = benches_dir.join(format!("{}.rs", name));
            out.push_str(&format!("#[path = \"{}\"]\n", abs_path.display()));
            out.push_str(&format!("pub mod {};\n", name));
        }
    }

    fs::write(&dest_path, out).unwrap();
    println!("cargo:rerun-if-changed=../../benches");
}
