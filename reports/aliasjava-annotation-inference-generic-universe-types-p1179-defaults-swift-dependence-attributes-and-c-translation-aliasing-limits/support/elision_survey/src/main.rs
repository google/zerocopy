//! Syntactic survey of lifetime elision in Rust function signatures.
//! Usage: elision_survey <dir>...   (walks *.rs files)
//! For every fn/method signature whose return type contains a lifetime position
//! (a `&` reference or an explicit lifetime argument), classify:
//!   ELIDED        - every output lifetime is elided (`&T` with no lifetime, or `'_`)
//!   EXPLICIT_ELIDABLE - output uses named lifetime(s) defined on the fn itself, and
//!                   the RFC 141 rules would have produced the same signature
//!   EXPLICIT_NEEDED - output uses fn-level named lifetime(s) that elision cannot express
//!   OUTER_LIFETIME - output names a lifetime bound by the enclosing impl/trait
//!   STATIC_ONLY    - all explicit output lifetimes are 'static
//! Limitations: purely syntactic; lifetime parameters hidden in paths without
//! explicit arguments (e.g. `Foo` for `Foo<'a>`) are invisible; macros are not expanded.
use std::collections::BTreeMap;
use syn::visit::Visit;

#[derive(Default)]
struct Lts { elided: usize, named: Vec<String> }

fn collect_ty(t: &syn::Type, acc: &mut Lts) {
    struct V<'x>(&'x mut Lts);
    impl<'ast, 'x> Visit<'ast> for V<'x> {
        fn visit_type_reference(&mut self, r: &'ast syn::TypeReference) {
            match &r.lifetime {
                None => self.0.elided += 1,
                Some(l) if l.ident == "_" => self.0.elided += 1,
                Some(l) => self.0.named.push(l.ident.to_string()),
            }
            syn::visit::visit_type(self, &r.elem);
        }
        fn visit_lifetime(&mut self, l: &'ast syn::Lifetime) {
            if l.ident == "_" { self.0.elided += 1 } else { self.0.named.push(l.ident.to_string()) }
        }
        // Do not descend into nested fn pointer / Fn-trait signatures or impl/dyn bounds'
        // higher-ranked binders: they have their own elision scope.
        fn visit_type_bare_fn(&mut self, _: &'ast syn::TypeBareFn) {}
        fn visit_parenthesized_generic_arguments(&mut self, _: &'ast syn::ParenthesizedGenericArguments) {}
    }
    V(acc).visit_type(t);
}

struct Survey { outer: Vec<Vec<String>>, counts: BTreeMap<&'static str, usize>, total_fns: usize, fns_with_ref_inputs: usize }

impl Survey {
    fn sig(&mut self, sig: &syn::Signature) {
        self.total_fns += 1;
        let fn_lts: Vec<String> = sig.generics.lifetimes().map(|l| l.lifetime.ident.to_string()).collect();
        let mut inputs = Lts::default();
        let mut self_ref: Option<Option<String>> = None; // Some(None)=&self elided, Some(Some(n)) named
        for a in &sig.inputs {
            match a {
                syn::FnArg::Receiver(r) => {
                    if let Some((_, lt)) = &r.reference {
                        let n = lt.as_ref().map(|l| l.ident.to_string()).filter(|n| n != "_");
                        if n.is_none() { inputs.elided += 1 } else { inputs.named.push(n.clone().unwrap()) }
                        self_ref = Some(n);
                    } else if r.colon_token.is_some() { collect_ty(&r.ty, &mut inputs); }
                }
                syn::FnArg::Typed(p) => collect_ty(&p.ty, &mut inputs),
            }
        }
        if inputs.elided + inputs.named.len() > 0 { self.fns_with_ref_inputs += 1; }
        let syn::ReturnType::Type(_, rt) = &sig.output else { return };
        let mut out = Lts::default();
        collect_ty(rt, &mut out);
        if out.elided + out.named.len() == 0 { return; }
        let k = if out.named.is_empty() {
            "ELIDED"
        } else if out.named.iter().all(|n| n == "static") {
            "STATIC_ONLY"
        } else if out.named.iter().any(|n| n != "static" && !fn_lts.contains(n)) {
            "OUTER_LIFETIME"
        } else {
            // All non-static output lifetimes are fn-level. Would elision reproduce them?
            let named: std::collections::BTreeSet<&String> = out.named.iter().filter(|n| *n != "static").collect();
            let one = named.len() == 1 && out.elided == 0;
            let target = named.iter().next().map(|s| s.to_string());
            let input_positions = inputs.elided + inputs.named.len();
            // Count how often the target appears among inputs, and whether other inputs are distinct.
            let uses = inputs.named.iter().filter(|n| Some(*n) == target.as_ref()).count();
            let elidable = one && (
                (input_positions == 1 && uses == 1) ||
                (matches!(&self_ref, Some(Some(n)) if Some(n) == target.as_ref()) && uses == 1
                    && !sig.generics.lifetimes().any(|l| !l.bounds.is_empty()))
            ) && fn_lts.iter().filter(|l| Some(*l) == target.as_ref()).count() == 1
              && sig.generics.lifetimes().all(|l| l.bounds.is_empty());
            if elidable { "EXPLICIT_ELIDABLE" } else { "EXPLICIT_NEEDED" }
        };
        *self.counts.entry(k).or_default() += 1;
    }
}

impl<'ast> Visit<'ast> for Survey {
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) { self.sig(&f.sig); syn::visit::visit_item_fn(self, f) }
    fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) { self.sig(&f.sig); syn::visit::visit_impl_item_fn(self, f) }
    fn visit_trait_item_fn(&mut self, f: &'ast syn::TraitItemFn) { self.sig(&f.sig); syn::visit::visit_trait_item_fn(self, f) }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        self.outer.push(i.generics.lifetimes().map(|l| l.lifetime.ident.to_string()).collect());
        syn::visit::visit_item_impl(self, i); self.outer.pop();
    }
}

fn walk(p: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
    if p.is_dir() { let mut v: Vec<_> = std::fs::read_dir(p).unwrap().flatten().map(|e| e.path()).collect(); v.sort(); for e in v { walk(&e, files) } }
    else if p.extension().map_or(false, |e| e == "rs") { files.push(p.to_path_buf()) }
}

fn main() {
    for dir in std::env::args().skip(1) {
        let mut files = vec![]; walk(std::path::Path::new(&dir), &mut files);
        let mut s = Survey { outer: vec![], counts: BTreeMap::new(), total_fns: 0, fns_with_ref_inputs: 0 };
        let mut parse_fail = 0;
        for f in &files {
            let src = std::fs::read_to_string(f).unwrap_or_default();
            match syn::parse_file(&src) {
                Ok(ast) => s.visit_file(&ast),
                Err(e) => {
                    parse_fail += 1;
                    if std::env::var_os("SHOW_PARSE_FAILURES").is_some() {
                        eprintln!("parse-failure {}: {}", f.display(), e);
                    }
                }
            }
        }
        let with_out: usize = s.counts.values().sum();
        println!("dir={} files={} parse_failures={} fn_signatures={} with_lifetime_in_inputs={} with_lifetime_in_output={}",
                 dir, files.len(), parse_fail, s.total_fns, s.fns_with_ref_inputs, with_out);
        for (k, v) in &s.counts { println!("  {:<18} {:>6}  {:5.1}%", k, v, 100.0 * *v as f64 / with_out as f64); }
    }
}
