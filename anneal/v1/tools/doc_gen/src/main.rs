use std::{env, fs, path::Path, process};

fn extract_signature(kind: &str, text: &str) -> String {
    if kind == "structure" || kind == "class" {
        return text.trim().to_string();
    }

    let mut sig = String::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("--") && !trimmed.starts_with("/--") {
            continue;
        }
        if trimmed.starts_with("#") {
            continue;
        }

        // Stop at body indicators
        if let Some(idx) = line.find(":=") {
            sig.push_str(&line[..idx]);
            break;
        }
        if let Some(idx) = line.find("where") {
            sig.push_str(&line[..idx]);
            break;
        }
        if let Some(idx) = line.find("| ") {
            sig.push_str(&line[..idx]);
            break;
        }

        sig.push_str(line);
        sig.push('\n');
    }
    sig.trim().to_string()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let check_mode = args.iter().any(|arg| arg == "--check");

    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&tree_sitter_lean4::language()).unwrap();

    let lean_path = "src/Anneal.lean";
    let source_code = fs::read_to_string(lean_path).expect("Failed to read src/Anneal.lean");
    let tree = parser.parse(&source_code, None).unwrap();

    let mut lean_docs = String::new();
    let mut cursor = tree.walk();
    let root = cursor.node();

    let mut pending_doc: Option<String> = None;

    for child in root.children(&mut cursor) {
        let text = &source_code[child.start_byte()..child.end_byte()];
        let kind = child.kind();

        if kind == "comment" && text.starts_with("/--") {
            pending_doc = Some(text.to_string());
        } else if kind == "definition"
            || kind == "structure"
            || kind == "class"
            || kind == "instance"
            || kind == "axiom"
            || kind == "ERROR"
        {
            let sig = extract_signature(kind, text);
            if !sig.is_empty() {
                if let Some(doc) = pending_doc.take() {
                    lean_docs.push_str(&doc);
                    lean_docs.push('\n');
                }
                lean_docs.push_str(&sig);
                lean_docs.push_str("\n\n");
            }
        } else {
            // clear pending docs if it's something else like whitespace
            if !text.trim().is_empty() {
                pending_doc = None;
            }
        }
    }

    // Now stitch everything together
    let mut full_txt = String::new();

    // 1. llms.txt
    full_txt.push_str("<!-- File: llms.txt -->\n\n");
    full_txt.push_str(&fs::read_to_string("llms.txt").unwrap());
    full_txt.push_str("\n\n");

    // 2. docs/agent/ files
    let docs_dir = Path::new("docs/agent");
    let mut entries: Vec<_> =
        fs::read_dir(docs_dir).unwrap().map(|res| res.unwrap().path()).collect();
    entries.sort();

    for path in entries {
        if path.extension().and_then(|s| s.to_str()) == Some("md") {
            full_txt.push_str(&format!("<!-- File: {} -->\n\n", path.display()));
            full_txt.push_str(&fs::read_to_string(&path).unwrap());
            full_txt.push_str("\n\n");
        }
    }

    // 3. Anneal.lean
    full_txt.push_str("<!-- File: src/Anneal.lean -->\n\n");
    full_txt.push_str("```lean\n");
    full_txt.push_str(lean_docs.trim());
    full_txt.push_str("\n```\n");

    let target_file = "llms-full.txt";
    if check_mode {
        let existing = fs::read_to_string(target_file).unwrap_or_default();
        if existing != full_txt {
            eprintln!(
                "Error: {} is out of date. Please run `cargo run -p doc_gen` to update it.",
                target_file
            );
            process::exit(1);
        } else {
            println!("{} is up to date.", target_file);
        }
    } else {
        fs::write(target_file, full_txt).unwrap();
        println!("Successfully generated {}", target_file);
    }
}
