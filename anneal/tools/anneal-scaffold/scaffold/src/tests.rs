// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::{
    fuel::{Edge, TERMINATOR_EDGES},
    lean::{doc_text, lean_identity, lean_list, MAX_LIST_CHUNK_LEN},
    *,
};

fn body(identity: &str, args: &[Value], blocks: Value) -> Value {
    let mut local_tys = vec![serde_json::json!({ "kind": "unit" })];
    local_tys.extend(args.iter().cloned());
    serde_json::json!({
        "identity": identity,
        "arg_count": args.len(),
        "is_unsafe": false,
        "local_tys": local_tys,
        "blocks": blocks,
    })
}

fn capture(bodies: Vec<Value>) -> String {
    serde_json::json!({
        "schema_version": SCHEMA_VERSION,
        "program": { "mir_profile_version": 1, "bodies": bodies },
    })
    .to_string()
}

fn ret_block() -> Value {
    serde_json::json!([{ "statements": [], "terminator": { "kind": "ret" } }])
}

#[test]
fn slugs_are_ascii_prefixed_and_numbered_by_identity() {
    assert_eq!(
        base_slug("rust-path-v1::<usize as PointerMetadata>::from_elem_count"),
        "b_usize_as_PointerMetadata_from_elem_count"
    );
    assert_eq!(base_slug("rust-path-v1::end"), "b_end");
    assert_eq!(base_slug("rust-path-v1::<>::_"), "b_body");
    assert_eq!(base_slug(""), "b_body");
    assert_eq!(hypothesis_name("b_body"), "h_body");
    let punctuation =
        render(&capture(vec![body("rust-path-v1::<>", &[], ret_block())]), "A").unwrap();
    assert!(punctuation.contains("namespace b_body"));
    assert!(punctuation.contains("(h_body :"));
}

fn slugs(identities: &[&str]) -> Vec<String> {
    let mut infos: Vec<BodyInfo> = identities
        .iter()
        .enumerate()
        .map(|(index, id)| BodyInfo {
            index,
            identity: format!("rust-path-v1::{id}"),
            slug: String::new(),
            is_unsafe: false,
            params: Vec::new(),
            fuel: None,
        })
        .collect();
    assign_slugs(&mut infos).unwrap();
    infos.into_iter().map(|i| i.slug).collect()
}

#[test]
fn numbered_slugs_are_globally_unique_and_order_independent() {
    assert_eq!(slugs(&["a::b", "a_b", "c"]), ["b_a_b_1", "b_a_b_2", "b_c"]);
    // `a::b` and `a_b` share the base slug `b_a_b`, and their numbering
    // must skip `b_a_b_1`, the base slug of `a_b_1`.
    assert_eq!(slugs(&["a::b", "a_b", "a_b_1"]), ["b_a_b_2", "b_a_b_3", "b_a_b_1"]);
    // Numbering skips every base slug, and numbering a numbered-looking
    // base stays distinct.
    let ids = ["x::1", "x_1", "x", "x.", "x_2"];
    let forward = slugs(&ids);
    assert_eq!(forward, ["b_x_1_1", "b_x_1_2", "b_x_3", "b_x_4", "b_x_2"]);
    let unique: BTreeSet<_> = forward.iter().collect();
    assert_eq!(unique.len(), forward.len());
    // Reversing the bodies maps each identity to the same slug.
    let mut reversed_ids = ids;
    reversed_ids.reverse();
    let mut reversed = slugs(&reversed_ids);
    reversed.reverse();
    assert_eq!(reversed, forward);
}

#[test]
fn reordering_bodies_changes_only_indices() {
    let int = serde_json::json!({ "kind": "int", "width": "isize", "signed": false });
    let a = body("rust-path-v1::a", std::slice::from_ref(&int), ret_block());
    let b = body("rust-path-v1::b", &[], ret_block());
    let forward = render(&capture(vec![a.clone(), b.clone()]), "AutoScaffold").unwrap();
    let reverse = render(&capture(vec![b, a]), "AutoScaffold").unwrap();
    assert_ne!(forward, reverse);
    let normalize = |s: &str| {
        s.replace("body_0", "body_X")
            .replace("body_1", "body_X")
            .replace("defId : DefId := 0", "defId : DefId := X")
            .replace("defId : DefId := 1", "defId : DefId := X")
            .lines()
            // The constructor lists hypotheses in body order.
            .filter(|l| !l.starts_with("    h_"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    assert_eq!(normalize(&forward), normalize(&reverse));
    assert!(forward.contains("(h_a :\n      BodyVerified Captured.program b_a.defId b_a.body"));
    assert!(forward.contains("[(MirTy.int IntWidth.isize false)]"));
}

#[test]
fn fuel_counts_acyclic_bodies_and_omits_loops() {
    let acyclic = serde_json::json!([
        { "statements": [{}, {}], "terminator": { "kind": "goto", "block": 1 } },
        { "statements": [{}], "terminator": { "kind": "ret" } },
    ]);
    assert_eq!(acyclic_fuel(acyclic.as_array().unwrap()), Ok(Some(5)));
    let cyclic = serde_json::json!([
        { "statements": [], "terminator": { "kind": "switch_int", "targets": [["0", 1]], "otherwise": 0 } },
        { "statements": [], "terminator": { "kind": "ret" } },
    ]);
    assert_eq!(acyclic_fuel(cyclic.as_array().unwrap()), Ok(None));
    let dangling =
        serde_json::json!([{ "statements": [], "terminator": { "kind": "goto", "block": 7 } }]);
    assert!(acyclic_fuel(dangling.as_array().unwrap()).is_err());
    // A call, sysroot call, or core call (`PanicAbort`) with a null
    // target diverges.
    for kind in ["call", "sysroot_call", "core_call"] {
        let diverging = serde_json::json!([
            { "statements": [], "terminator": { "kind": kind, "target": null } },
        ]);
        assert_eq!(acyclic_fuel(diverging.as_array().unwrap()), Ok(Some(1)), "{kind}");
    }
    let core_call = serde_json::json!([
        { "statements": [{}], "terminator": { "kind": "core_call", "target": 1 } },
        { "statements": [], "terminator": { "kind": "ret" } },
    ]);
    assert_eq!(acyclic_fuel(core_call.as_array().unwrap()), Ok(Some(3)));
    for missing in ["goto", "assert", "call", "sysroot_call", "core_call"] {
        let malformed =
            serde_json::json!([{ "statements": [], "terminator": { "kind": missing } }]);
        assert!(acyclic_fuel(malformed.as_array().unwrap()).is_err(), "{missing}");
    }
    for target in [serde_json::json!("bad"), serde_json::json!(-1)] {
        let malformed = serde_json::json!([
            { "statements": [], "terminator": { "kind": "sysroot_call", "target": target } },
        ]);
        assert!(acyclic_fuel(malformed.as_array().unwrap()).is_err(), "{target}");
    }
    let unknown = serde_json::json!([{ "statements": [], "terminator": { "kind": "yield" } }]);
    assert!(acyclic_fuel(unknown.as_array().unwrap()).is_err());
}

#[test]
fn types_render_like_the_capture_emitter() {
    let ty = serde_json::json!({
        "kind": "ref",
        "mutability": "shared",
        "pointee": {
            "kind": "enum", "id": 9, "discr_width": "i32", "discr_signed": true,
            "tag_repr": { "kind": "scalar", "width": "i8", "signed": true },
            "discriminants": ["0", "1"],
        },
    });
    assert_eq!(
        lean_ty(&ty).unwrap(),
        "(MirTy.ref Mutability.shared (MirTy.enum { id := 9, discrWidth := IntWidth.i32, \
         discrSigned := true, tagRepr := (EnumTagRepr.scalar IntWidth.i8 true), \
         discriminants := [0, 1] }))"
    );
    assert!(lean_ty(&serde_json::json!({ "kind": "float" })).is_err());
    assert!(lean_ty(&serde_json::json!({ "kind": "int", "width": "i7", "signed": true })).is_err());
    // `&str`, `Range<Option<u8>>`, `[RangeTo<usize>; 2]`, and a tuple of
    // `RangeFrom<i8>` and `&[char]`.
    let u8_ty = serde_json::json!({ "kind": "int", "width": "i8", "signed": false });
    let cases = [
        (
            serde_json::json!({ "kind": "ref", "mutability": "shared", "pointee": { "kind": "str" } }),
            "(MirTy.ref Mutability.shared MirTy.str)",
        ),
        (
            serde_json::json!({ "kind": "range", "elem": { "kind": "option", "elem": u8_ty } }),
            "(MirTy.range (MirTy.option (MirTy.int IntWidth.i8 false)))",
        ),
        (
            serde_json::json!({ "kind": "array", "len": 2, "elem": {
                "kind": "range_to", "elem": { "kind": "int", "width": "isize", "signed": false },
            } }),
            "(MirTy.array (MirTy.rangeTo (MirTy.int IntWidth.isize false)) 2)",
        ),
        (
            serde_json::json!({ "kind": "tuple", "fields": [
                { "kind": "range_from", "elem": { "kind": "int", "width": "i8", "signed": true } },
                { "kind": "ref", "mutability": "mut", "pointee": {
                    "kind": "slice", "elem": { "kind": "char" },
                } },
            ] }),
            "(MirTy.tuple [(MirTy.rangeFrom (MirTy.int IntWidth.i8 true)), \
             (MirTy.ref Mutability.mut (MirTy.slice MirTy.char))])",
        ),
    ];
    let more = [
        (
            serde_json::json!({ "kind": "box", "pointee": { "kind": "slice", "elem": { "kind": "int", "width": "i8", "signed": false } } }),
            "(MirTy.box (MirTy.slice (MirTy.int IntWidth.i8 false)))",
        ),
        (
            serde_json::json!({ "kind": "vec", "elem": { "kind": "bool" } }),
            "(MirTy.vec MirTy.bool)",
        ),
    ];
    for (ty, expected) in cases.into_iter().chain(more) {
        assert_eq!(lean_ty(&ty).unwrap(), expected);
    }
    // `box` reads `pointee`, not `elem`.
    assert!(lean_ty(&serde_json::json!({ "kind": "box", "elem": { "kind": "bool" } })).is_err());
    assert!(lean_ty(&serde_json::json!({ "kind": "option" })).is_err());
}

/// The source of `rel`, relative to the Anneal workspace root.
fn anneal_source(rel: &str) -> String {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    std::fs::read_to_string(root.join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"))
}

/// The text from the first line starting with `start` through the next line
/// that is exactly `}`.
fn item<'a>(source: &'a str, start: &str) -> &'a str {
    let begin = source.find(start).unwrap_or_else(|| panic!("no `{start}`"));
    let len = source[begin..].find("\n}\n").unwrap_or_else(|| panic!("unclosed `{start}`"));
    &source[begin..begin + len]
}

fn snake_case(camel: &str) -> String {
    let mut out = String::new();
    for (i, c) in camel.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            out.push('_');
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}

/// Every variant of the capture's `ir::Ty` renders, and with every `MirTy`
/// constructor that the capture's Lean emitter uses for it.
#[test]
fn every_captured_type_kind_renders_like_the_capture_emitter() {
    let ir = anneal_source("trusted/rustc-capture/src/ir.rs");
    let lean = anneal_source("trusted/rustc-capture/src/lean.rs");
    let emitter = item(&lean, "fn ty_at(");
    let variants: Vec<&str> = item(&ir, "pub enum Ty {")
        .lines()
        .skip(1)
        .filter_map(|line| line.strip_prefix("    "))
        .filter(|line| line.starts_with(|c: char| c.is_ascii_uppercase()))
        .map(|line| line.split(|c: char| !c.is_ascii_alphanumeric()).next().unwrap())
        .collect();
    assert!(variants.len() >= 18 && variants.contains(&"Option"), "{variants:?}");
    let unit = serde_json::json!({ "kind": "unit" });
    for variant in variants {
        let kind = snake_case(variant);
        // One value carrying every field any type kind reads.
        let ty = serde_json::json!({
            "kind": kind, "width": "i8", "signed": true, "mutability": "shared",
            "pointee": unit, "elem": unit, "len": 1, "fields": [unit], "id": 0,
            "discr_width": "i8", "discr_signed": true,
            "tag_repr": { "kind": "zero_sized" }, "discriminants": ["0"],
        });
        let rendered = lean_ty(&ty).unwrap_or_else(|e| panic!("{variant}: {e}"));
        let arm = emitter
            .match_indices(&format!("Ty::{variant}"))
            .map(|(at, _)| &emitter[at..])
            .find(|rest| !rest[4 + variant.len()..].starts_with(char::is_alphanumeric))
            .unwrap_or_else(|| panic!("lean.rs has no arm for `Ty::{variant}`"));
        let arm = &arm[..arm[4..].find("\n        Ty::").map_or(arm.len(), |end| end + 4)];
        let ctors: Vec<&str> = arm
            .split("Trusted.MirAst.MirTy.")
            .skip(1)
            .map(|rest| rest.split(|c: char| !c.is_ascii_alphanumeric()).next().unwrap())
            .collect();
        assert!(!ctors.is_empty(), "{variant}: no MirTy constructor in {arm}");
        for ctor in ctors {
            assert!(rendered.contains(&format!("MirTy.{ctor}")), "{variant}: {rendered}");
        }
    }
}

/// `TERMINATOR_EDGES` lists exactly the variants of the capture's
/// `ir::Terminator`, and each successor field with the edge its type
/// implies: `u32`, `Option<u32>`, or `Vec<(u128, u32)>`.
#[test]
fn terminator_edges_match_the_capture() {
    let ir = anneal_source("trusted/rustc-capture/src/ir.rs");
    let mut captured = BTreeMap::new();
    let mut variant = None;
    for line in item(&ir, "pub enum Terminator {").lines().skip(1) {
        if let Some(rest) = line.strip_prefix("    ") {
            if rest.starts_with(|c: char| c.is_ascii_uppercase()) {
                let name: String = rest.chars().take_while(char::is_ascii_alphanumeric).collect();
                variant = Some(snake_case(&name));
                captured.insert(snake_case(&name), Vec::new());
                continue;
            }
        }
        let Some(field) = line.strip_prefix("        ") else { continue };
        let Some((name, ty)) = field.trim_end_matches(',').split_once(": ") else {
            continue;
        };
        let edge = match (name, ty) {
            ("block" | "target" | "otherwise", "u32") => Edge::Block,
            ("target", "Option<u32>") => Edge::OptionalBlock,
            ("targets", "Vec<(u128, u32)>") => Edge::SwitchTargets,
            ("block" | "target" | "otherwise" | "targets", _) => {
                panic!("unexpected successor field type `{field}`")
            }
            _ => continue,
        };
        captured.get_mut(variant.as_ref().unwrap()).unwrap().push((name.to_owned(), edge));
    }
    let ours: BTreeMap<String, Vec<(String, Edge)>> = TERMINATOR_EDGES
        .iter()
        .map(|(k, fields)| {
            ((*k).to_owned(), fields.iter().map(|&(n, e)| (n.to_owned(), e)).collect())
        })
        .collect();
    let by_name = |m: BTreeMap<String, Vec<(String, Edge)>>| {
        m.into_iter()
            .map(|(k, mut v)| {
                v.sort_by(|a, b| a.0.cmp(&b.0));
                (k, v)
            })
            .collect::<BTreeMap<_, _>>()
    };
    assert_eq!(by_name(ours), by_name(captured));
}

#[test]
fn reserved_module_roots_match_cargo_anneal() {
    let verify = anneal_source("trusted/cargo-anneal/src/verify.rs");
    let reserved: BTreeSet<&str> =
        item(&verify, "fn reserved_proof_module(").split('"').skip(1).step_by(2).collect();
    assert_eq!(reserved, RESERVED_MODULE_ROOTS.iter().copied().collect());
    let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
    for root in RESERVED_MODULE_ROOTS {
        for module in [root.to_string(), format!("{root}.AutoScaffold")] {
            let e = render(&one, &module).unwrap_err();
            assert!(e.0.contains("reserved"), "{module}: {e}");
        }
    }
    for module in ["TrustedHelpers", "Proof.Trusted", "Spec.AutoScaffold"] {
        assert!(render(&one, module).is_ok(), "{module}");
    }
}

#[test]
fn identities_render_like_the_capture_emitter() {
    assert_eq!(lean_identity(""), "(_root_.String.ofList [])");
    assert_eq!(
        lean_identity("a\u{3bb}"),
        "(_root_.String.ofList [(_root_.Char.ofNat 97), (_root_.Char.ofNat 955)])"
    );
    // 33 characters make leaves of 16, 16, and 1, joined as 16 + (16 + 1)
    // exactly as the capture joins them.
    let long: String = std::iter::repeat_n('x', 33).collect();
    let rendered = lean_identity(&long);
    assert!(rendered.starts_with("(Trusted.MirAst.stringAppend (_root_.String.ofList ["));
    assert_eq!(rendered.matches("Trusted.MirAst.stringAppend").count(), 2);
    assert_eq!(rendered.matches("_root_.String.ofList").count(), 3);
}

#[test]
fn docs_stay_printable_ascii() {
    assert_eq!(doc_text("`x` -/ /-"), "'x' - / / -");
}

/// The elements of a list that `lean_list` renders, in order, after
/// checking that every literal holds at most `MAX_LIST_CHUNK_LEN` of
/// them and every join is balanced.
fn list_items(rendered: &str) -> Vec<String> {
    fn walk(s: &str, out: &mut Vec<String>) -> usize {
        if let Some(rest) = s.strip_prefix("(_root_.List.append ") {
            let inner = &rest[..rest.len() - 1];
            // Split at the top-level space between the two operands.
            let (mut depth, mut at) = (0i32, None);
            for (i, c) in inner.char_indices() {
                match c {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    ' ' if depth == 0 => {
                        at = Some(i);
                        break;
                    }
                    _ => {}
                }
            }
            let at = at.expect("two operands");
            let (l, r) = (walk(&inner[..at], out), walk(&inner[at + 1..], out));
            assert!(l.abs_diff(r) <= 1, "unbalanced join in {s}");
            return l.max(r) + 1;
        }
        let body = s.strip_prefix('[').and_then(|s| s.strip_suffix(']')).expect(s);
        let items: Vec<&str> = if body.is_empty() { vec![] } else { body.split(", ").collect() };
        assert!(items.len() <= MAX_LIST_CHUNK_LEN, "literal too long: {s}");
        out.extend(items.into_iter().map(str::to_owned));
        0
    }
    let mut out = Vec::new();
    walk(rendered, &mut out);
    out
}

#[test]
fn long_lists_render_as_balanced_appends_of_short_literals() {
    let names = |n: usize| (0..n).map(|i| format!("x{i}")).collect::<Vec<_>>();
    assert_eq!(lean_list(&[]), "[]");
    assert_eq!(lean_list(&names(16)), format!("[{}]", names(16).join(", ")));
    for n in [17, 40, 255, 1950] {
        let rendered = lean_list(&names(n));
        assert!(rendered.starts_with("(_root_.List.append "), "{n}");
        assert_eq!(list_items(&rendered), names(n), "{n}");
    }
    // A 40-field tuple, a 40-variant enum, and 40 parameters.
    let int = serde_json::json!({ "kind": "int", "width": "i8", "signed": false });
    let tuple = serde_json::json!({ "kind": "tuple", "fields": vec![int.clone(); 40] });
    let rendered = lean_ty(&tuple).unwrap();
    let fields = rendered.strip_prefix("(MirTy.tuple ").unwrap().strip_suffix(')').unwrap();
    assert_eq!(list_items(fields), vec!["(MirTy.int IntWidth.i8 false)".to_owned(); 40]);
    let discriminants: Vec<String> = (0..40).map(|i| i.to_string()).collect();
    let enum_ty = serde_json::json!({
        "kind": "enum", "id": 1, "discr_width": "i8", "discr_signed": false,
        "tag_repr": { "kind": "zero_sized" }, "discriminants": discriminants,
    });
    let rendered = lean_ty(&enum_ty).unwrap();
    let list = rendered.split("discriminants := ").nth(1).unwrap().strip_suffix(" })").unwrap();
    assert_eq!(list_items(list), discriminants);
    let scaffold = render(
        &capture(vec![body("rust-path-v1::wide", &vec![int; 40], ret_block())]),
        "AutoScaffold",
    )
    .unwrap();
    let params = scaffold.split("argumentCount =\n      ").nth(1).unwrap();
    let params = &params[..params.find(" :=\n").unwrap()];
    assert_eq!(list_items(params).len(), 40);
}

/// A capture whose one body takes an argument of `depth` nested
/// `Option`s around `inner`, built as text so that no recursive `Value`
/// is built or dropped on the test thread.
fn nested_option_capture(depth: usize, inner: &str) -> String {
    let placeholder = serde_json::json!("NESTED");
    let text = capture(vec![body("rust-path-v1::deep", &[placeholder], ret_block())]);
    let nested =
        format!("{}{inner}{}", "{\"kind\":\"option\",\"elem\":".repeat(depth), "}".repeat(depth));
    text.replace("\"NESTED\"", &nested)
}

#[test]
fn deeply_nested_types_render_within_the_depth_bound() {
    let unit = "{\"kind\":\"unit\"}";
    for depth in [200, MAX_JSON_DEPTH - 10] {
        let scaffold = render(&nested_option_capture(depth, unit), "AutoScaffold")
            .unwrap_or_else(|e| panic!("{depth}: {e}"));
        assert_eq!(scaffold.matches("(MirTy.option ").count(), depth);
    }
    // A malformed type deep inside is reported, not a crash.
    let bad = render(&nested_option_capture(200, "{\"kind\":\"float\"}"), "AutoScaffold");
    assert!(bad.unwrap_err().0.contains("unknown type kind `float`"));
    let missing = render(&nested_option_capture(200, "{}"), "AutoScaffold");
    assert!(missing.unwrap_err().0.contains("type has no kind"));
    // Beyond the bound, the capture is refused before it is parsed.
    let too_deep = render(&nested_option_capture(MAX_JSON_DEPTH, unit), "AutoScaffold");
    assert!(too_deep.unwrap_err().0.contains(&format!("nest more than {MAX_JSON_DEPTH} deep")));
    let unbalanced = format!("{}{}", "[".repeat(MAX_JSON_DEPTH + 1), "]".repeat(3));
    assert!(render(&unbalanced, "AutoScaffold").unwrap_err().0.contains("nest more than"));
    // Trailing values are malformed.
    let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
    assert!(render(&format!("{one} {one}"), "AutoScaffold").is_err());
    assert!(render(&format!("{one} ]"), "AutoScaffold").is_err());
}

#[test]
fn json_depth_ignores_brackets_in_strings() {
    assert_eq!(json_depth(""), 0);
    assert_eq!(json_depth("[[{}], {}]"), 3);
    assert_eq!(json_depth(r#"["[[[", "\"[[", "\\", [1]]"#), 2);
    assert_eq!(json_depth("]]]["), 1);
}

#[test]
fn rejects_unusable_captures() {
    assert!(render("{", "AutoScaffold").is_err());
    assert!(render(&capture(vec![]), "AutoScaffold").is_err());
    let wrong_schema = serde_json::json!({ "schema_version": 4, "program": {} }).to_string();
    assert!(render(&wrong_schema, "AutoScaffold").unwrap_err().0.contains("schema_version"));
    let dup = capture(vec![
        body("rust-path-v1::a", &[], ret_block()),
        body("rust-path-v1::a", &[], ret_block()),
    ]);
    assert!(render(&dup, "AutoScaffold").unwrap_err().0.contains("duplicate"));
    let one = capture(vec![body("rust-path-v1::a", &[], ret_block())]);
    for bad in ["", "autoScaffold", "Auto.", "Auto-Scaffold", "Auto..S"] {
        assert!(render(&one, bad).is_err(), "{bad}");
    }
    assert!(render(&one, "Proof.AutoScaffold").is_ok());
}
