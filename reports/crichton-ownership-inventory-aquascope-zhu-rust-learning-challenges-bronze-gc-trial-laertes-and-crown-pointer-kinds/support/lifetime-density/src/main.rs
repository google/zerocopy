//! Syntactic lifetime-annotation density counter (syn 2 parser).
//!
//! Usage: lifetime-density <label> <src-dir>...
//! Parses every `*.rs` file under the given directories (no macro expansion, no
//! cfg evaluation) and reports, per crate, counts over function signatures
//! (free fns, inherent/trait impl methods, trait methods, foreign fns).
//!
//! Definitions (all syntactic, per signature):
//! - ref position: a `&T`/`&mut T` type (or `&self`/`&mut self` receiver) in an
//!   input or the output, outside nested `fn(..)` pointer types and `Fn(..)`
//!   sugar (those open their own elision scope and are skipped).
//! - elided ref: a ref position with no written lifetime.
//! - named lifetime: any lifetime other than `'static` and `'_`.
//! - input lifetimes: (#elided input refs) + (#`'_` in inputs) + (#distinct
//!   named or `'static` lifetimes written in inputs). Lifetimes hidden inside
//!   paths (e.g. `Formatter` meaning `Formatter<'_>`) are invisible here.
//! - output carries a lifetime: output contains a ref position or a
//!   non-`'static` lifetime.
//! - elision determines output: receiver is `&self`/`&mut self`, or a typed
//!   receiver containing `&Self`/`&mut Self` such as `self: Pin<&mut Self>` (rule 3), or
//!   input lifetimes == 1 (rule 2).
//! - must annotate: output carries a lifetime and elision does not determine it,
//!   i.e. removing every written lifetime would make the signature hit E0106
//!   (modulo hidden path lifetimes).
use std::collections::BTreeSet;
use syn::visit::{self, Visit};

#[derive(Default, Debug)]
struct TyScan {
    refs_elided: usize,
    refs_named: usize,
    refs_static: usize,
    refs_anon: usize,
    lt_named: BTreeSet<String>,
    lt_named_occ: usize,
    lt_static: usize,
    lt_anon: usize,
}
impl<'ast> Visit<'ast> for TyScan {
    fn visit_type_reference(&mut self, r: &'ast syn::TypeReference) {
        match &r.lifetime {
            None => self.refs_elided += 1,
            Some(l) if l.ident == "static" => self.refs_static += 1,
            Some(l) if l.ident == "_" => self.refs_anon += 1,
            Some(_) => self.refs_named += 1,
        }
        visit::visit_type_reference(self, r);
    }
    fn visit_lifetime(&mut self, l: &'ast syn::Lifetime) {
        if l.ident == "static" { self.lt_static += 1; }
        else if l.ident == "_" { self.lt_anon += 1; }
        else { self.lt_named_occ += 1; self.lt_named.insert(l.ident.to_string()); }
    }
    // Nested elision scopes: skip.
    fn visit_type_bare_fn(&mut self, _: &'ast syn::TypeBareFn) {}
    fn visit_parenthesized_generic_arguments(&mut self, _: &'ast syn::ParenthesizedGenericArguments) {}
}

struct RefToSelf(bool);
impl<'ast> Visit<'ast> for RefToSelf {
    fn visit_type_reference(&mut self, r: &'ast syn::TypeReference) {
        if let syn::Type::Path(p) = &*r.elem {
            if p.qself.is_none() && p.path.is_ident("Self") { self.0 = true; }
        }
        visit::visit_type_reference(self, r);
    }
}

#[derive(Default, Debug)]
struct Stats {
    files: usize,
    parse_failures: usize,
    nonblank_lines: usize,
    sigs: usize,
    sigs_lifetime_relevant: usize,
    sigs_fn_lifetime_params: usize,
    sigs_write_named: usize,
    sigs_write_anon: usize,
    sigs_write_static: usize,
    sigs_output_lifetime: usize,
    sigs_output_elided_only: usize,
    sigs_output_named: usize,
    sigs_elision_rule3: usize,
    sigs_elision_rule2: usize,
    sigs_must_annotate: usize,
    sigs_must_annotate_written_named: usize,
    sigs_elidable_but_named_output: usize,
    ref_positions: usize,
    refs_elided: usize,
    refs_named: usize,
    refs_static: usize,
    refs_anon: usize,
    adts: usize,
    adts_with_lifetime_params: usize,
    impls: usize,
    impls_with_lifetime_params: usize,
    traits: usize,
    traits_with_lifetime_params: usize,
}

struct V<'s> { s: &'s mut Stats }
impl<'s> V<'s> {
    fn sig(&mut self, sig: &syn::Signature) {
        let s = &mut *self.s;
        s.sigs += 1;
        let fn_lt = sig.generics.lifetimes().count();
        if fn_lt > 0 { s.sigs_fn_lifetime_params += 1; }
        let mut inp = TyScan::default();
        let mut ref_self = false;
        for arg in &sig.inputs {
            match arg {
                syn::FnArg::Receiver(r) => {
                    if r.colon_token.is_some() {
                        inp.visit_type(&r.ty);
                        // Typed receivers such as `self: Pin<&mut Self>` also get rule 3
                        // when they contain a reference whose referent is `Self`.
                        let mut f = RefToSelf(false);
                        f.visit_type(&r.ty);
                        if f.0 { ref_self = true; }
                    } else if let Some((_, lt)) = &r.reference {
                        ref_self = true;
                        match lt {
                            None => inp.refs_elided += 1,
                            Some(l) if l.ident == "static" => { inp.refs_static += 1; inp.lt_static += 1; }
                            Some(l) if l.ident == "_" => { inp.refs_anon += 1; inp.lt_anon += 1; }
                            Some(l) => { inp.refs_named += 1; inp.lt_named_occ += 1; inp.lt_named.insert(l.ident.to_string()); }
                        }
                    }
                }
                syn::FnArg::Typed(pt) => inp.visit_type(&pt.ty),
            }
        }
        let mut out = TyScan::default();
        if let syn::ReturnType::Type(_, t) = &sig.output { out.visit_type(t); }
        let in_refs = inp.refs_elided + inp.refs_named + inp.refs_static + inp.refs_anon;
        let out_refs = out.refs_elided + out.refs_named + out.refs_static + out.refs_anon;
        s.ref_positions += in_refs + out_refs;
        s.refs_elided += inp.refs_elided + out.refs_elided;
        s.refs_named += inp.refs_named + out.refs_named;
        s.refs_static += inp.refs_static + out.refs_static;
        s.refs_anon += inp.refs_anon + out.refs_anon;
        let any_lt = in_refs + out_refs + inp.lt_named_occ + out.lt_named_occ + inp.lt_anon + out.lt_anon + inp.lt_static + out.lt_static > 0;
        if any_lt || fn_lt > 0 { s.sigs_lifetime_relevant += 1; }
        let writes_named = inp.lt_named_occ + out.lt_named_occ > 0 || fn_lt > 0;
        if writes_named { s.sigs_write_named += 1; }
        if inp.lt_anon + out.lt_anon > 0 { s.sigs_write_anon += 1; }
        if inp.lt_static + out.lt_static > 0 { s.sigs_write_static += 1; }
        let out_carries = out.refs_elided + out.refs_anon + out.refs_named > 0 || out.lt_named_occ + out.lt_anon > 0;
        let input_lifetimes = inp.refs_elided + inp.lt_anon + inp.lt_named.len() + if inp.lt_static > 0 { 1 } else { 0 };
        if out_carries {
            s.sigs_output_lifetime += 1;
            if out.lt_named_occ == 0 { s.sigs_output_elided_only += 1; } else { s.sigs_output_named += 1; }
            let determined = ref_self || input_lifetimes == 1;
            if ref_self { s.sigs_elision_rule3 += 1; } else if input_lifetimes == 1 { s.sigs_elision_rule2 += 1; }
            if !determined {
                s.sigs_must_annotate += 1;
                if out.lt_named_occ > 0 { s.sigs_must_annotate_written_named += 1; }
                else if std::env::var_os("SHOW_UNNAMED_MUST_ANNOTATE").is_some() {
                    eprintln!("must-annotate without named output lifetime: fn {} at line {}", sig.ident, sig.ident.span().start().line);
                }
            } else if out.lt_named_occ > 0 {
                s.sigs_elidable_but_named_output += 1;
            }
        }
    }
}
impl<'ast, 's> Visit<'ast> for V<'s> {
    fn visit_item_fn(&mut self, i: &'ast syn::ItemFn) { self.sig(&i.sig); visit::visit_item_fn(self, i); }
    fn visit_impl_item_fn(&mut self, i: &'ast syn::ImplItemFn) { self.sig(&i.sig); visit::visit_impl_item_fn(self, i); }
    fn visit_trait_item_fn(&mut self, i: &'ast syn::TraitItemFn) { self.sig(&i.sig); visit::visit_trait_item_fn(self, i); }
    fn visit_foreign_item_fn(&mut self, i: &'ast syn::ForeignItemFn) { self.sig(&i.sig); visit::visit_foreign_item_fn(self, i); }
    fn visit_item_struct(&mut self, i: &'ast syn::ItemStruct) { self.s.adts += 1; if i.generics.lifetimes().next().is_some() { self.s.adts_with_lifetime_params += 1; } visit::visit_item_struct(self, i); }
    fn visit_item_enum(&mut self, i: &'ast syn::ItemEnum) { self.s.adts += 1; if i.generics.lifetimes().next().is_some() { self.s.adts_with_lifetime_params += 1; } visit::visit_item_enum(self, i); }
    fn visit_item_union(&mut self, i: &'ast syn::ItemUnion) { self.s.adts += 1; if i.generics.lifetimes().next().is_some() { self.s.adts_with_lifetime_params += 1; } visit::visit_item_union(self, i); }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) { self.s.impls += 1; if i.generics.lifetimes().next().is_some() { self.s.impls_with_lifetime_params += 1; } visit::visit_item_impl(self, i); }
    fn visit_item_trait(&mut self, i: &'ast syn::ItemTrait) { self.s.traits += 1; if i.generics.lifetimes().next().is_some() { self.s.traits_with_lifetime_params += 1; } visit::visit_item_trait(self, i); }
}

fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() { walk(&p, out); } else if p.extension().map_or(false, |e| e == "rs") { out.push(p); }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let label = &args[1];
    let mut files = Vec::new();
    for d in &args[2..] { walk(std::path::Path::new(d), &mut files); }
    let mut s = Stats::default();
    for f in &files {
        let text = std::fs::read_to_string(f).unwrap();
        s.files += 1;
        s.nonblank_lines += text.lines().filter(|l| !l.trim().is_empty()).count();
        match syn::parse_file(&text) {
            Ok(file) => { let mut v = V { s: &mut s }; v.visit_file(&file); }
            Err(e) => { s.parse_failures += 1; eprintln!("parse failure {}: {}", f.display(), e); }
        }
    }
    println!("{}\t{:?}", label, s);
}
