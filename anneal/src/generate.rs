use crate::parse::{
    FunctionItem, ParsedItem, TypeItem,
    attr::{
        FunctionAnnealBlock, SpannedLine, TraitAnnealBlock,
        TypeAnnealBlock, FunctionAttribute,
    },
    hkd::AstNode,
};

/// The kind of source mapping connecting generated Lean code to the original
/// Rust context.
///
/// This resolves the misalignment between user-authored documentation syntax
/// and the structurally-required Lean proof output.
///
/// This distinguishes between:
/// - `Source`: Direct, 1-to-1 mapping to user-written code (e.g. proof lines).
/// - `Synthetic`: Generated code that doesn't definitively exist in the source,
///   but we want to anchor to a relevant Rust span (e.g., mapping an
///   auto-generated `spec` function signature back to the Rust `fn` ident).
/// - `Keyword`: Mapping to a specific structural keyword in the source (e.g.
///   mapping the Lean `theorem` keyword to the Rust `proof` block keyword).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MappingKind {
    Source,
    Synthetic,
    Keyword,
}

/// A mapping between a range in the generated Lean code and the original Rust
/// source.
///
/// Under the hood, Lean parses and resolves theorems independently. When Lean
/// emits an error (e.g., a type mismatch or a failing tactic), it reports the
/// byte range of the generated `.lean` file. We use this struct to project
/// those byte ranges back into the originating `/// ````anneal`
/// doc block in the user's `.rs` workspace.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct SourceMapping {
    /// Start byte offset in the generated Lean file.
    pub lean_start: usize,
    /// End byte offset in the generated Lean file.
    pub lean_end: usize,
    /// The absolute path to the original Rust source file.
    pub source_file: std::path::PathBuf,
    /// Start byte offset in the Rust source file.
    pub source_start: usize,
    /// End byte offset in the Rust source file.
    pub source_end: usize,
    pub kind: MappingKind,
}

/// The result of generating Lean code for a Rust artifact (library/binary).
pub struct GeneratedArtifact {
    /// The full generated Lean source code.
    pub code: String,
    /// Sidecar mappings for source-location tracking.
    pub mappings: Vec<SourceMapping>,
}

/// A helper for building Lean code strings while automatically tracking source mappings.
pub struct LeanBuilder {
    buf: String,
    mappings: Vec<SourceMapping>,
}

impl LeanBuilder {
    pub fn new() -> Self {
        Self { buf: String::new(), mappings: Vec::new() }
    }

    fn push_str(&mut self, s: &str) {
        self.buf.push_str(s);
    }

    fn push(&mut self, c: char) {
        self.buf.push(c);
    }

    /// Appends `s` to the buffer and creates a mapping to the `source_file` at `line.span`.
    ///
    /// The mapping will cover the entire range of `s` in the output, mapping it to
    /// `line.span` in the source. This is used for mapping user-written content lines
    /// (e.g. proof steps) directly to their location in the doc comment.
    fn push_spanned(
        &mut self,
        s: &str,
        line: &SpannedLine<crate::parse::hkd::Safe>,
        source_file: &std::path::Path,
    ) {
        let start = self.buf.len();
        self.buf.push_str(s);

        let trimmed_s = s.trim_start();
        let leading_ws = s.len() - trimmed_s.len();

        let trimmed_end_s = trimmed_s.trim_end();
        let trailing_ws = trimmed_s.len() - trimmed_end_s.len();

        let span = &line.span;
        // If `s` is shorter than `line.content` (e.g. stripped indentation),
        // we assume it is a suffix of `line.content`. We shift the source
        // start offset forward so the mapping aligns accurately.
        let bytes_stripped = line.content.len().saturating_sub(s.len());
        let source_start = span.offset() + bytes_stripped + leading_ws;

        if trimmed_end_s.is_empty() {
            // Do not create a mapping for a purely whitespace line. If Lean
            // highlights it, it will be safely absorbed by multi-line mappings.
            return;
        }

        self.mappings.push(SourceMapping {
            lean_start: start + leading_ws,
            lean_end: self.buf.len() - trailing_ws,
            source_file: source_file.to_path_buf(),
            source_start,
            source_end: source_start + trimmed_end_s.len(),
            kind: MappingKind::Source,
        });
    }

    /// Appends `s` to the buffer and creates a mapping to the `source_file`
    /// at `span` with `kind`.
    ///
    /// This is prominently used for injecting "Synthetic" spans. For instance,
    /// we generate a Lean theorem named `spec`, and map that identifier directly
    /// back to the Rust function's `Ident` span. Consequently, if Lean throws
    /// an error strictly about `spec`, the user will see a squiggle
    /// underlining their Rust function name, creating the illusion that `rustc`
    /// itself caught the verification error.
    fn push_mapped(
        &mut self,
        s: &str,
        span: &miette::SourceSpan,
        source_file: &std::path::Path,
        kind: MappingKind,
    ) {
        let start = self.buf.len();
        self.buf.push_str(s);
        self.mappings.push(SourceMapping {
            lean_start: start,
            lean_end: self.buf.len(),
            source_file: source_file.to_path_buf(),
            source_start: span.offset(),
            source_end: span.offset() + span.len(),
            kind,
        });
    }

    fn finish(self) -> GeneratedArtifact {
        GeneratedArtifact { code: self.buf, mappings: self.mappings }
    }
}

/// A context for generating consistent Lean names and namespaces for Rust items.
pub struct NamingContext {
    pub crate_name: String,
}

impl NamingContext {
    /// Constructs a new `NamingContext` for the given crate.
    ///
    /// The crate name is "slugged" (replacing hyphens with underscores) to
    /// ensure it is a valid Lean identifier, matching the behavior of Aeneas
    /// during code generation.
    pub fn new(crate_name: String) -> Self {
        Self { crate_name: crate_name.replace('-', "_") }
    }

    /// Returns the dot-separated namespace for an item, relative to the crate root.
    ///
    /// The returned string does *not* include the crate name itself.
    ///
    /// For functions inside `impl` blocks, this includes the name of the struct
    /// or type being implemented on. This ensures that the generated Lean
    /// theorem lives in a namespace that logically matches Aeneas's flattened
    /// function names (e.g., `Struct::method` in Rust becomes `Struct.method`
    /// in Lean).
    pub fn item_namespace(
        &self,
        item: &crate::parse::ParsedLeanItem<crate::parse::hkd::Safe>,
    ) -> String {
        let mut parts: Vec<_> =
            item.module_path.iter().filter(|&p| p != "crate").cloned().collect();

        match &item.item {
            ParsedItem::Function(func) => {
                // If this is an inherent impl, we incorporate the type name
                // into the namespace path to avoid collisions and match
                // Aeneas's naming conventions.
                if let FunctionItem::Impl(
                    _,
                    Some(crate::parse::hkd::AstNode {
                        inner: crate::parse::hkd::SafeType::Path { segments, .. },
                        ..
                    }),
                    _,
                ) = &func.item
                {
                    parts.extend(segments.iter().map(|s| s.ident.clone()));
                }
            }
            ParsedItem::Type(_) | ParsedItem::Trait(_) | ParsedItem::Impl(_) => {}
        }

        parts.join(".")
    }

    /// Returns the name used to invoke the function or type from the Lean specification.
    pub fn aeneas_call_name(
        &self,
        item: &crate::parse::ParsedLeanItem<crate::parse::hkd::Safe>,
    ) -> String {
        match &item.item {
            ParsedItem::Function(func) => func.item.sig().ident.to_string(),
            ParsedItem::Type(ty) => ty.item.name().to_string(),
            ParsedItem::Trait(tr) => tr.item.inner.ident.to_string(),
            ParsedItem::Impl(_) => String::new(),
        }
    }

    /// Returns the name of the specification theorem (e.g., "spec").
    pub fn item_spec_name(
        &self,
        _item: &crate::parse::ParsedLeanItem<crate::parse::hkd::Safe>,
    ) -> String {
        "spec".to_string()
    }
}

/// Generates the full Lean code for a given ParsedItem.
///
/// Dispatches to the appropriate generation function based on the item type.
pub fn generate_item(
    item: &crate::parse::ParsedLeanItem<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    naming_context: &NamingContext,
) {
    match &item.item {
        ParsedItem::Function(func) => {
            generate_function(&func.item, &func.anneal, builder, &item.source_file, naming_context)
        }
        ParsedItem::Type(ty) => {
            generate_type(&ty.item, &ty.anneal, builder, &item.source_file, naming_context)
        }
        ParsedItem::Trait(tr) => {
            generate_trait(&tr.item.inner, &tr.anneal, builder, &item.source_file, naming_context)
        }
        ParsedItem::Impl(_) => {}
    }
}

/// Generates the complete Lean file content for a single Anneal artifact.
///
/// This function:
/// 1. Writes the standard header and imports.
/// 2. Opens necessary namespaces (Aeneas, dependencies).
/// 3. Iterates over all items in the artifact, generating code for each.
/// 4. Wraps items in their respective module namespaces.
pub fn generate_artifact(artifact: &crate::scanner::AnnealArtifact) -> GeneratedArtifact {
    let mut builder = LeanBuilder::new();
    builder.push_str("-- This file is automatically generated by Anneal.\n");
    builder.push_str("-- Do not edit manually.\n\n");

    let slug = artifact.artifact_slug();
    builder.push_str("import Anneal\n");
    builder.push_str("import Aeneas.Std.Scalar.Core\n");
    // We import both the Funs and Types files generated by Aeneas for
    // this specific artifact slug. This allows the specifications we
    // generate to refer to Aeneas's definitions.
    builder.push_str(&format!("import «{}».Funs\n", slug));
    builder.push_str(&format!("import «{}».Types\n\n", slug));
    // We disable the `linter.dupNamespace` option globally in the generated Lean file.
    // Anneal translation commonly generates nested namespaces that trigger this linter.
    //
    // FIXME: Maybe set this in the lakefile instead?
    builder.push_str("set_option linter.dupNamespace false\n");
    builder.push_str("set_option linter.unusedVariables false\n");
    builder.push_str("open Aeneas Aeneas.Std Result\n\n");
    builder.push_str("noncomputable section\n\n");
    builder.push_str("-- Specification linking Aeneas's opaque generated built-ins to Anneal.\n");
    builder.push_str("inject_builtins\n\n");

    let naming_context = NamingContext::new(artifact.name.target_name.clone());
    builder.push_str(&format!("namespace {}\n\n", naming_context.crate_name));

    // Grouping by namespace to avoid excessive indentation or repetition
    // (though for now we still do it per item to keep structural changes minimal).
    for item in &artifact.items {
        let namespace = naming_context.item_namespace(item);
        if !namespace.is_empty() {
            builder.push_str(&format!("namespace {}\n\n", namespace));
        }

        generate_item(item, &mut builder, &naming_context);
        builder.push('\n');

        if !namespace.is_empty() {
            builder.push_str(&format!("end {}\n\n", namespace));
        }
    }

    builder.push_str(&format!("end {}\n", naming_context.crate_name));
    builder.finish()
}

struct ArgInfo {
    name: String,
    lean_type: String,
    is_mut_ref: bool,
}

// AST Nodes
struct AstField<'a> {
    name: String,
    lean_type: Option<String>,
    proof_tactic: Option<String>,
    lines: Vec<&'a SpannedLine<crate::parse::hkd::Safe>>,
}

/// Generates a Lean theorem or axiom for a function's specification.
///
/// This function performs the complex translation from a Rust function signature and Anneal
/// annotations into a Lean `Anneal.SpecificationHolds` theorem.
///
/// # key transformations
/// 1. **Signature Translation**: Rust arguments are mapped to Lean arguments.
/// 2. **Mutable References**: `&mut T` arguments are treated as input-output pairs.
///    The input value is passed in, and the new value is returned in the result tuple.
/// 3. **Specification**: The `requires` clause becomes a precondition hypothesis (`h_req`).
///    The `ensures` clause is verified against the result (including new values of mutable refs).
/// 4. **Proof/Axiom**: If `proof` is present, it generates a `theorem` with the provided proof script.
///    If `axiom` is present or `unsafe(axiom)` is used, it generates an `axiom` or uses `sorry`.
///
/// # Output Format
/// ```lean
/// theorem foo_spec (args...) (h_req : requires) :
///   Aeneas.Std.WP.spec (foo args...)
///     (fun ret =>
///       let (ret, new_mut_arg) := ret
///       ret = 5 && new_mut_arg = 6
///       ensures) :=
///   by ...
/// ```
fn generate_function(
    func: &FunctionItem<crate::parse::hkd::Safe>,
    block: &FunctionAnnealBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
    _naming_context: &NamingContext,
) {
    let fn_name = func.sig().ident.clone();
    builder.push_str(&format!("namespace {}\n\n", fn_name));

    for line in &block.content {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }

    builder.push_str(&format!("\nend {}\n", fn_name));
}

/// Generates a `Anneal.IsValid` instance for a type (struct/enum/union).
///
/// This instance proves that a type maintains its validity invariants (if any).
/// If no invariants are specified, it generates a `True` invariant.
fn generate_type(
    ty: &TypeItem<crate::parse::hkd::Safe>,
    block: &TypeAnnealBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
    _naming_context: &NamingContext,
) {
    let type_name = match ty {
        TypeItem::Struct(s) => s.inner.ident.clone(),
        TypeItem::Enum(e) => e.inner.ident.clone(),
        TypeItem::Union(u) => u.inner.ident.clone(),
    };

    builder.push_str(&format!("namespace {}\n\n", type_name));

    for line in &block.content {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }

    builder.push_str(&format!("\nend {}\n", type_name));
}

/// Generates a `Safe` class for a trait.
///
/// This defines what it means for a type to safely implement a trait, including any
/// `isSafe` invariants the trait imposes on its implementors.
fn generate_trait(
    tr: &crate::parse::hkd::SafeItemTrait,
    block: &TraitAnnealBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
    _naming_context: &NamingContext,
) {
    let trait_name = tr.ident.clone();
    builder.push_str(&format!("namespace {}\n\n", trait_name));

    for line in &block.content {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }

    builder.push_str(&format!("\nend {}\n", trait_name));
}

/// Extracts generic parameters for Lean.
/// Returns a tuple: (list of param names, list of args, list of bounds).
fn extract_generic_params(
    generics: &crate::parse::hkd::SafeGenerics,
) -> (Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    use crate::parse::hkd::{SafeGenericParam, SafeTypeParamBound, SafeWherePredicate};
    let mut params = Vec::new();
    let mut args = Vec::new();
    let mut bounds = Vec::new();
    let mut dict_args = Vec::new();

    let mut process_bound = |bound: &SafeTypeParamBound, ty_str: &str| {
        if let SafeTypeParamBound::Trait { ty: trait_ty, is_maybe } = bound {
            if *is_maybe {
                // We ignore `?Trait` bounds (such as `?Sized`) because they are
                // relaxed constraints rather than affirmative requirements.
                return;
            }

            let mapped_trait = map_type(trait_ty);
            // The `Sized` trait requires special handling because Aeneas
            // currently ignores it entirely. Since Aeneas does not generate an
            // explicit dictionary argument for `Sized`, we cannot pass one.
            // Instead, we emit it as a typeclass `[Anneal.core.marker.Sized T]`
            // which resolves implicitly.
            if mapped_trait == "core.marker.Sized" || mapped_trait == "Sized" {
                bounds.push(format!("[Anneal.core.marker.Sized {}]", ty_str));
            } else {
                // We generate an explicit dictionary argument for each trait
                // bound rather than relying on typeclass resolution. This
                // matches Aeneas's behavior, which expects explicit dictionary
                // arguments for trait bounds. We construct the identifier by
                // appending `Inst` to the base trait name, mimicking Aeneas's
                // `Clause0Inst` and `TraitInst` naming patterns.
                let mut dict_name = if mapped_trait.contains('.') {
                    mapped_trait.split('.').next_back().unwrap().to_string()
                } else {
                    mapped_trait.clone()
                };
                // Remove parentheses and take the first word to get a clean identifier
                dict_name = dict_name.replace('(', "").replace(')', "");
                if let Some(idx) = dict_name.find(' ') {
                    dict_name = dict_name[..idx].to_string();
                }
                let dict_ident = format!("{}Inst", dict_name);

                // Reconstruct the type with correct argument order (Self first)
                let mut trait_type_str = dict_name.clone();
                if let crate::parse::hkd::SafeType::Path { segments, .. } = trait_ty {
                    if let Some(segment) = segments.last() {
                        let gen_args: Vec<_> = segment.args.iter().map(map_type).collect();
                        if !gen_args.is_empty() {
                            trait_type_str =
                                format!("{} {} {}", trait_type_str, ty_str, gen_args.join(" "));
                        } else {
                            trait_type_str = format!("{} {}", trait_type_str, ty_str);
                        }
                    }
                }
                bounds.push(format!("({} : {})", dict_ident, trait_type_str));
                dict_args.push(dict_ident);
            }
        }
    };

    for param in &generics.params {
        match param {
            SafeGenericParam::Type { name, bounds: p_bounds } => {
                params.push(name.clone());
                args.push(name.clone());
                for bound in p_bounds {
                    process_bound(bound, name);
                }
            }
            SafeGenericParam::Const { name, ty } => {
                let mapped_ty = map_type(ty);
                params.push(format!("{} : {}", name, mapped_ty));
                args.push(name.clone());
            }
            SafeGenericParam::Lifetime => {}
        }
    }

    for pred in &generics.where_clause {
        if let SafeWherePredicate::Type { bounded_ty, bounds: p_bounds } = pred {
            let ty_str = map_type(bounded_ty);
            for bound in p_bounds {
                process_bound(bound, &ty_str);
            }
        }
    }

    (params, args, bounds, dict_args)
}

/// Recursively maps Rust types to Lean types.
///
/// Maps a `SafeType` to its corresponding name in the Lean functional model.
///
/// This handles:
/// - **Primitives**: `u32` -> `Std.U32`, `bool` -> `Bool`.
/// - **References**: `&T` -> `T`. References are erased in the functional
///   model because we model state transformations explicitly rather than
///   via pointer identities.
/// - **Pointers**: `*mut T` -> `(MutRawPtr T)`, `*const T` -> `(ConstRawPtr T)`.
/// - **Slices/Arrays**: `[T]` -> `(Slice T)`, `[T; N]` -> `(Array T N)`.
/// - **Never**: `!` -> `Never`. Used for diverging functions.
/// - **Tuples**: `(A, B)` -> `A × B`.
/// - **Paths**: `std::vec::Vec` -> `std.vec.Vec` (with segments joined by `.`).
fn map_type(ty: &crate::parse::hkd::SafeType) -> String {
    use crate::parse::hkd::SafeType::*;
    match ty {
        Path { qself: _, segments } => {
            if let Some(segment) = segments.last() {
                let s = &segment.ident;
                let mapped = match s.as_str() {
                    "u8" => Some("Std.U8"),
                    "u16" => Some("Std.U16"),
                    "u32" => Some("Std.U32"),
                    "u64" => Some("Std.U64"),
                    "u128" => Some("Std.U128"),
                    "usize" => Some("Std.Usize"),
                    "i8" => Some("Std.I8"),
                    "i16" => Some("Std.I16"),
                    "i32" => Some("Std.I32"),
                    "i64" => Some("Std.I64"),
                    "i128" => Some("Std.I128"),
                    "isize" => Some("Std.Isize"),
                    "bool" => Some("Bool"),
                    _ => None,
                };
                if let Some(mapped) = mapped {
                    return mapped.to_string();
                }
            }

            segments
                .iter()
                .map(|segment| {
                    let mut s = segment.ident.clone();
                    let gen_args: Vec<_> = segment.args.iter().map(map_type).collect();
                    if !gen_args.is_empty() {
                        s = format!("({s} {})", gen_args.join(" "));
                    }
                    s
                })
                .collect::<Vec<_>>()
                .join(".")
        }
        Reference { elem, .. } => map_type(elem),
        Tuple { elems } => {
            if elems.is_empty() {
                "Unit".to_string()
            } else {
                format!("({})", elems.iter().map(map_type).collect::<Vec<_>>().join(" × "))
            }
        }
        Ptr { mutability, elem } => {
            let inner = map_type(elem);
            if *mutability {
                format!("(MutRawPtr {})", inner)
            } else {
                format!("(ConstRawPtr {})", inner)
            }
        }
        Slice { elem } => format!("(Slice {})", map_type(elem)),
        Array { elem, len } => {
            let inner = map_type(elem);
            format!("(Array {} {})", inner, len)
        }
        Never => "Never".to_string(),
        Other => "MatchError".to_string(),
    }
}

/// Extracts `(arg_name, lean_type, is_mut_ref)` metadata from a function signature.
///
/// This metadata is used to build the Lean function signature and efficiently map
/// receiver parameters into their concrete structure types, bypassing generic
/// generic namespace resolution issues within generated Lean files.
///
/// **Mutable References (`&mut T`) vs Owned Mutable Variables (`mut x: T`)**
/// This function identifies whether an argument is a true struct-level mutable
/// reference `&mut T`. It intentionally distinguishes this from standard
/// pass-by-value bindings that are merely declared as mutable (`mut x: T`).
/// Only true `&mut T` references are flagged with `is_mut_ref = true` to inform
/// `generate_function` that it needs to unpack a tuple output from Aeneas.
fn escape_lean_keyword(name: &str) -> String {
    match name {
        "theorem" | "axiom" | "variable" | "lemma" | "def" | "class" | "instance" | "structure"
        | "inductive" | "from" | "have" | "show" | "calc" | "then" | "with" | "section"
        | "namespace" | "end" | "import" | "open" | "attribute" | "universe" => {
            format!("{}1", name)
        }
        _ => name.to_string(),
    }
}

fn extract_args_metadata(
    func: &FunctionItem<crate::parse::hkd::Safe>,
    impl_struct_name: &Option<crate::parse::hkd::AstNode<syn::Type, crate::parse::hkd::Safe>>,
) -> Vec<ArgInfo> {
    use crate::parse::hkd::{SafeFnArg, SafeType};
    let sig = func.sig();

    sig.inputs
        .iter()
        .map(|arg| match arg {
            SafeFnArg::Typed { name, ty } => {
                let mut is_mut_ref = false;
                if let SafeType::Reference { mutability, .. } = ty {
                    is_mut_ref = *mutability;
                }
                ArgInfo { name: escape_lean_keyword(name), lean_type: map_type(ty), is_mut_ref }
            }
            SafeFnArg::Receiver { mutability, reference } => {
                let lean_type = if let Some(t) = impl_struct_name {
                    map_type(&t.inner)
                } else {
                    "Self".to_string()
                };
                ArgInfo {
                    name: "self".to_string(),
                    lean_type,
                    is_mut_ref: *mutability && *reference,
                }
            }
        })
        .collect()
}

/// Checks if the function returns `Unit` (or equivalent).
fn is_unit_return(func: &FunctionItem<crate::parse::hkd::Safe>) -> bool {
    use crate::parse::hkd::SafeReturnType;
    let sig = func.sig();
    match &sig.output {
        SafeReturnType::Default => true,
        SafeReturnType::Type(ty) => matches!(map_type(ty).as_str(), "Unit" | "MatchError"),
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use miette::SourceSpan;
    // use proc_macro2::Span;
    use syn::parse_quote;

    use super::*;
    use crate::parse::{
        hkd::{Mirror, Safe},
    };

    // --- Helpers ---
    fn map_qt(ty: syn::Type) -> String {
        map_type(&ty.mirror())
    }



    // --- Type Mapping Tests ---

    #[test]
    fn test_map_primitives() {
        assert_eq!(map_qt(parse_quote!(u32)), "Std.U32");
        assert_eq!(map_qt(parse_quote!(bool)), "Bool");
        assert_eq!(map_qt(parse_quote!(usize)), "Std.Usize");
    }

    #[test]
    fn test_map_complex_paths() {
        // Simple
        assert_eq!(map_qt(parse_quote!(MyType)), "MyType");
        // Qualified
        assert_eq!(map_qt(parse_quote!(std::vec::Vec)), "std.vec.Vec");
    }

    #[test]
    fn test_map_generics() {
        // Vec<u32> -> (Vec Std.U32)
        assert_eq!(map_qt(parse_quote!(Vec<u32>)), "(Vec Std.U32)");
        // Result<T, E> -> (Result T E)
        assert_eq!(map_qt(parse_quote!(Result<T, E>)), "(Result T E)");
        // Nested: Vec<Vec<u32>> -> (Vec (Vec Std.U32))
        assert_eq!(map_qt(parse_quote!(Vec<Vec<u32>>)), "(Vec (Vec Std.U32))");
    }

    #[test]
    fn test_map_references() {
        assert_eq!(map_qt(parse_quote!(&u32)), "Std.U32");
        assert_eq!(map_qt(parse_quote!(&mut u32)), "Std.U32");
        assert_eq!(map_qt(parse_quote!(&mut Vec<u32>)), "(Vec Std.U32)");
    }

    #[test]
    fn test_map_tuples() {
        assert_eq!(map_qt(parse_quote!(())), "Unit");
        assert_eq!(map_qt(parse_quote!((u32, bool))), "(Std.U32 × Bool)");
    }



    #[test]
    fn test_generate_artifact_namespace() {
        use crate::{
            resolve::{AnnealTargetKind, AnnealTargetName},
            scanner::AnnealArtifact,
        };
        let name = AnnealTargetName {
            package_name: cargo_metadata::PackageName::new("my-package".to_string()),
            target_name: "my-target".to_string(),
            kind: AnnealTargetKind::Lib,
        };
        let artifact = AnnealArtifact {
            name,
            target_kind: AnnealTargetKind::Lib,
            manifest_path: std::path::PathBuf::from("Cargo.toml"),
            start_from: std::collections::HashSet::new(),
            items: vec![],
        };

        let generated = generate_artifact(&artifact);

        // It should open the robust target_name with hyphens replaced by underscores
        assert!(generated.code.contains("namespace my_target\n\n"));
        // It shouldn't contain the old package_name logic by mistake
        assert!(!generated.code.contains("open my_package"));
    }





    #[test]
    fn test_pathing_naming_context() {
        let naming_context = NamingContext::new("my-crate".to_string());
        assert_eq!(naming_context.crate_name, "my_crate");

        let dummy_span = miette::SourceSpan::from(0..0);

        // Helper to create a dummy ParsedLeanItem
        let mk_item = |path: Vec<&str>, item: ParsedItem<Safe>| crate::parse::ParsedLeanItem {
            item,
            module_path: path.into_iter().map(|s| s.to_string()).collect(),
            source_file: PathBuf::from("test.rs"),
        };



        let mk_func = |name: &str| {
            ParsedItem::Function(crate::parse::AnnealDecorated {
                item: FunctionItem::Free(AstNode {
                    inner: crate::parse::hkd::SafeItemFn {
                        sig: crate::parse::hkd::SafeSignature {
                            ident: name.to_string(),
                            name_span: dummy_span,
                            inputs: Vec::new(),
                            output: crate::parse::hkd::SafeReturnType::Default,
                        },
                        generics: crate::parse::hkd::SafeGenerics {
                            params: Vec::new(),
                            where_clause: Vec::new(),
                        },
                    },
                }),
                anneal: FunctionAnnealBlock {
                    content: Vec::new(),
                    content_span: AstNode { inner: dummy_span },
                    start_span: AstNode { inner: dummy_span },
                    mode: FunctionAttribute::Spec,
                },
            })
        };

        // Root function
        let root_fn = mk_item(vec!["crate"], mk_func("foo"));
        assert_eq!(naming_context.item_namespace(&root_fn), "");
        assert_eq!(naming_context.aeneas_call_name(&root_fn), "foo");

        // Nested function
        let nested_fn = mk_item(vec!["crate", "a", "b"], mk_func("bar"));
        assert_eq!(naming_context.item_namespace(&nested_fn), "a.b");
        assert_eq!(naming_context.aeneas_call_name(&nested_fn), "bar");

        // Impl function (local type)
        let impl_fn = mk_item(
            vec!["crate", "m"],
            ParsedItem::Function(crate::parse::AnnealDecorated {
                item: FunctionItem::Impl(
                    AstNode {
                        inner: crate::parse::hkd::SafeImplItemFn {
                            sig: crate::parse::hkd::SafeSignature {
                                ident: "method".to_string(),
                                name_span: dummy_span,
                                inputs: Vec::new(),
                                output: crate::parse::hkd::SafeReturnType::Default,
                            },
                            generics: crate::parse::hkd::SafeGenerics {
                                params: Vec::new(),
                                where_clause: Vec::new(),
                            },
                        },
                    },
                    Some(AstNode {
                        inner: crate::parse::hkd::SafeType::Path {
                            qself: None,
                            segments: vec![crate::parse::hkd::SafePathSegment {
                                ident: "S".to_string(),
                                args: Vec::new(),
                            }],
                        },
                    }),
                    None,
                ),
                anneal: FunctionAnnealBlock {
                    content: Vec::new(),
                    content_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    start_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    mode: FunctionAttribute::Spec,
                },
            }),
        );
        assert_eq!(naming_context.item_namespace(&impl_fn), "m.S");
        assert_eq!(naming_context.aeneas_call_name(&impl_fn), "method");

        // Impl function (fully qualified type)
        let q_impl_fn = mk_item(
            vec!["crate"],
            ParsedItem::Function(crate::parse::AnnealDecorated {
                item: FunctionItem::Impl(
                    AstNode {
                        inner: crate::parse::hkd::SafeImplItemFn {
                            sig: crate::parse::hkd::SafeSignature {
                                ident: "f".to_string(),
                                name_span: dummy_span,
                                inputs: Vec::new(),
                                output: crate::parse::hkd::SafeReturnType::Default,
                            },
                            generics: crate::parse::hkd::SafeGenerics {
                                params: Vec::new(),
                                where_clause: Vec::new(),
                            },
                        },
                    },
                    Some(AstNode {
                        inner: crate::parse::hkd::SafeType::Path {
                            qself: None,
                            segments: vec![
                                crate::parse::hkd::SafePathSegment {
                                    ident: "outer".to_string(),
                                    args: Vec::new(),
                                },
                                crate::parse::hkd::SafePathSegment {
                                    ident: "inner".to_string(),
                                    args: Vec::new(),
                                },
                                crate::parse::hkd::SafePathSegment {
                                    ident: "T".to_string(),
                                    args: Vec::new(),
                                },
                            ],
                        },
                    }),
                    None,
                ),
                anneal: FunctionAnnealBlock {
                    content: Vec::new(),
                    content_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    start_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    mode: FunctionAttribute::Spec,
                },
            }),
        );
        assert_eq!(naming_context.item_namespace(&q_impl_fn), "outer.inner.T");
        assert_eq!(naming_context.aeneas_call_name(&q_impl_fn), "f");

        // Foreign function
        let foreign_fn = mk_item(
            vec!["crate", "ffi"],
            ParsedItem::Function(crate::parse::AnnealDecorated {
                item: FunctionItem::Foreign(AstNode {
                    inner: crate::parse::hkd::SafeForeignItemFn {
                        sig: crate::parse::hkd::SafeSignature {
                            ident: "ext_fn".to_string(),
                            name_span: dummy_span,
                            inputs: Vec::new(),
                            output: crate::parse::hkd::SafeReturnType::Default,
                        },
                        generics: crate::parse::hkd::SafeGenerics {
                            params: Vec::new(),
                            where_clause: Vec::new(),
                        },
                    },
                }),
                anneal: FunctionAnnealBlock {
                    content: Vec::new(),
                    content_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    start_span: AstNode { inner: miette::SourceSpan::new(0.into(), 0) },
                    mode: FunctionAttribute::UnsafeAxiom,
                },
            }),
        );
        assert_eq!(naming_context.item_namespace(&foreign_fn), "ffi");
        assert_eq!(naming_context.aeneas_call_name(&foreign_fn), "ext_fn");
    }


}
