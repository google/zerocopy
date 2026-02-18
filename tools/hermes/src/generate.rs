use crate::parse::{
    attr::{
        FunctionBlockInner, FunctionHermesBlock, SpannedLine, TraitHermesBlock, TypeHermesBlock,
    },
    hkd::AstNode,
    FunctionItem, ParsedItem, TypeItem,
};

/// The kind of source mapping.
///
/// This distinguishes between:
/// - `Source`: Direct mapping to user-written code (e.g. proof lines).
/// - `Synthetic`: Generated code that doesn't exist in source but we want to map to a relevant span (e.g. `spec`).
/// - `Keyword`: Mapping to a specific keyword in the source (e.g. `proof`, `axiom`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum MappingKind {
    Source,
    Synthetic,
    Keyword,
}

/// A mapping between a range in the generated Lean code and the original Rust source.
///
/// This is used to propagate diagnostics from Lean back to the Rust source file.
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
        let end = self.buf.len();

        // Map [start, end) in Lean to [source_start, source_end) in Rust
        // We assume `s` corresponds to `line.content` (or at least `line.span`).
        // `line.span` is a `miette::SourceSpan`.
        let span = &line.span;
        self.mappings.push(SourceMapping {
            lean_start: start,
            lean_end: end,
            source_file: source_file.to_path_buf(),
            source_start: span.offset(),
            source_end: span.offset() + span.len(),
            kind: MappingKind::Source,
        });
    }

    /// Appends `s` to the buffer and creates a mapping to the `source_file` at `span` with `kind`.
    ///
    /// This is used for more manual mapping control, e.g. mapping a generated `spec` keyword
    /// to the function name in Rust, or `by` to a specific token.
    fn push_mapped(
        &mut self,
        s: &str,
        span: &miette::SourceSpan,
        source_file: &std::path::Path,
        kind: MappingKind,
    ) {
        let start = self.buf.len();
        self.buf.push_str(s);
        let end = self.buf.len();

        self.mappings.push(SourceMapping {
            lean_start: start,
            lean_end: end,
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

/// Generates the full Lean code for a given ParsedItem.
///
/// Dispatches to the appropriate generation function based on the item type.
pub fn generate_item(
    item: &crate::parse::ParsedLeanItem<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
) {
    match &item.item {
        ParsedItem::Function(func) => {
            generate_function(&func.item, &func.hermes, builder, &item.source_file)
        }
        ParsedItem::Type(ty) => generate_type(&ty.item, &ty.hermes, builder, &item.source_file),
        ParsedItem::Trait(tr) => {
            generate_trait(&tr.item.inner, &tr.hermes, builder, &item.source_file)
        }
        ParsedItem::Impl(_) => {}
    }
}

/// Generates the complete Lean file content for a single Hermes artifact.
///
/// This function:
/// 1. Writes the standard header and imports.
/// 2. Opens necessary namespaces (Aeneas, dependencies).
/// 3. Iterates over all items in the artifact, generating code for each.
/// 4. Wraps items in their respective module namespaces.
pub fn generate_artifact(artifact: &crate::scanner::HermesArtifact) -> GeneratedArtifact {
    let mut builder = LeanBuilder::new();
    builder.push_str("-- This file is automatically generated by Hermes.\n");
    builder.push_str("-- Do not edit manually.\n\n");

    let slug = artifact.artifact_slug();
    builder.push_str("import Hermes\n");
    builder.push_str("import Aeneas\n");
    builder.push_str("import Aeneas.ScalarTac.ScalarTac\n");
    builder.push_str(&format!("import «{}».Funs\n", slug));
    builder.push_str(&format!("import «{}».Types\n\n", slug));
    builder.push_str("open Aeneas Aeneas.Std Result\n");
    // Open the crate namespace so types are visible.
    //
    // Note: Aeneas uses the crate name (snake_case) as the top-level namespace.
    // We replace hyphens with underscores to match.
    let crate_namespace = artifact.name.package_name.to_string().replace('-', "_");
    builder.push_str(&format!("open {}\n\n", crate_namespace));

    // Naive namespacing: for each item, wrap in its module namespace.
    // Optimisation: group by namespace? For now, we keep it simple.

    for item in &artifact.items {
        let namespace = item
            .module_path
            .iter()
            .filter(|&p| p != "crate")
            .cloned()
            .collect::<Vec<_>>()
            .join(".");
        if !namespace.is_empty() {
            builder.push_str(&format!("namespace {}\n\n", namespace));
        }

        generate_item(item, &mut builder);
        builder.push('\n');

        if !namespace.is_empty() {
            builder.push_str(&format!("end {}\n\n", namespace));
        }
    }
    builder.finish()
}

struct ArgInfo {
    name: String,
    ty: String,
    is_mut_ref: bool,
}

/// Generates a Lean theorem or axiom for a function's specification.
///
/// This function performs the complex translation from a Rust function signature and Hermes
/// annotations into a Lean `Hermes.SpecificationHolds` theorem.
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
///   Hermes.SpecificationHolds (α := ResultType) (foo args...)
///     (fun result =>
///       let old_mut_arg := mut_arg
///       let (ret_val, new_mut_arg) := result
///       ensures) :=
///   by ...
/// ```
fn generate_function(
    func: &FunctionItem<crate::parse::hkd::Safe>,
    block: &FunctionHermesBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
) {
    let (fn_name, fn_span) = match func {
        FunctionItem::Free(n) => (n.inner.sig.ident.clone(), n.inner.sig.name_span),
        FunctionItem::Impl(n) => (n.inner.sig.ident.clone(), n.inner.sig.name_span),
        FunctionItem::Trait(n) => (n.inner.sig.ident.clone(), n.inner.sig.name_span),
    };

    let args = extract_args_metadata(func);
    let ret_is_unit = is_unit_return(func);

    // Namespace wrapping
    builder.push_str(&format!("namespace {}\n\n", fn_name));

    // 1. Generate the context
    for line in &block.common.context {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }
    builder.push('\n');

    // 2. Resolve Requires/Ensures
    // Note: ensure we join them with " ∧ \n" but distinct spans
    // This is tricky for `push_spanned`.
    // We'll trust the user to have written valid Lean or we'll format it.
    // Existing logic: `join_conjunctions`.
    // logic: lines.map(|l| format!("({})", l)).join(" ∧ \n")
    // If we want to map spans, we should push "(". Then push_spanned content. Then push ")". Then " ∧ \n".

    // 3. Determine if this is a Theorem or Axiom
    let (kind_keyword, body_lines, keyword_span) = match &block.inner {
        FunctionBlockInner::Proof { lines, keyword } => ("theorem", Some(lines), keyword),
        FunctionBlockInner::Axiom { keyword, .. } => ("axiom", None, keyword),
    };

    // 4. Build the Call String
    let call_str = std::iter::once(fn_name.clone())
        .chain(args.iter().map(|a| a.name.clone()))
        .collect::<Vec<_>>()
        .join(" ");

    // 5. Build the Precondition Binder

    // Signature
    let args_suffix = (!args.is_empty())
        .then(|| {
            format!(
                " {}",
                args.iter()
                    .map(|a| format!("({} : {})", a.name, a.ty))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        })
        .unwrap_or_default();

    if kind_keyword == "axiom" {
        if let Some(kw) = keyword_span {
            builder.push_mapped(kind_keyword, &kw.inner, source_file, MappingKind::Keyword);
        } else {
            builder.push_str(kind_keyword);
        }
    } else {
        builder.push_str(kind_keyword);
    }
    builder.push(' ');
    builder.push_mapped("spec", &fn_span, source_file, MappingKind::Synthetic);
    builder.push_str(args_suffix.as_str());

    let has_requires = !block.requires.is_empty();
    if has_requires {
        builder.push_str("\n  (h_req : ");
        for (i, clause) in block.requires.iter().enumerate() {
            if i > 0 {
                builder.push_str(" ∧ \n");
            }
            builder.push('(');
            for (j, line) in clause.lines.iter().enumerate() {
                if j > 0 {
                    builder.push('\n');
                }
                builder.push_spanned(&line.content, line, source_file);
            }
            builder.push('\n');
            builder.push(')');
        }
        builder.push(')');
    }

    builder.push_str(" :\n");

    // Result Spec
    let ret_type = get_return_type_string(func);
    builder.push_str(&format!("  Hermes.SpecificationHolds (α := {}) ({})", ret_type, call_str));

    let mut_args: Vec<&ArgInfo> = args.iter().filter(|a| a.is_mut_ref).collect();
    let has_muts = !mut_args.is_empty();
    let has_ensures = !block.ensures.is_empty();

    if has_ensures || has_muts {
        builder.push_str(" (fun result =>");

        if has_muts {
            builder.push('\n');
            for arg in &mut_args {
                builder.push_str(&format!("    let old_{} := {}\n", arg.name, arg.name));
            }

            let destructure_lhs = if ret_is_unit && mut_args.len() == 1 {
                format!("{}_new", mut_args[0].name)
            } else {
                let vars = mut_args
                    .iter()
                    .map(|a| format!("{}_new", a.name))
                    .collect::<Vec<_>>()
                    .join(", ");
                if ret_is_unit {
                    format!("({})", vars)
                } else {
                    format!("(result, {})", vars)
                }
            };

            builder.push_str(&format!("    let {} := result\n", destructure_lhs));

            if ret_is_unit {
                builder.push_str("    let result := ()\n");
            }

            for arg in &mut_args {
                builder.push_str(&format!("    let {} := {}_new\n", arg.name, arg.name));
            }
            builder.push_str("    ");
        } else {
            builder.push(' ');
        }

        if has_ensures {
            for (i, clause) in block.ensures.iter().enumerate() {
                if i > 0 {
                    builder.push_str(" ∧ \n");
                }
                builder.push('(');
                for (j, line) in clause.lines.iter().enumerate() {
                    if j > 0 {
                        builder.push('\n');
                    }
                    builder.push_spanned(&line.content, line, source_file);
                }
                builder.push('\n');
                builder.push(')');
            }
        } else {
            builder.push_str("True");
        }
        builder.push(')');
    } else {
        builder.push_str(" (fun _ => True)");
    }

    // Body
    if kind_keyword == "theorem" {
        if let Some(lines) = body_lines {
            if lines.is_empty() {
                builder.push_str(" := ");
                if let Some(kw) = keyword_span {
                    builder.push_mapped("by", &kw.inner, source_file, MappingKind::Keyword);
                } else {
                    builder.push_str("by");
                }
                builder.push_str("\n  sorry\n");
            } else {
                builder.push_str(" := ");
                // Map 'by' to the proof keyword span if available, otherwise first line
                if let Some(kw) = keyword_span {
                    builder.push_mapped("by", &kw.inner, source_file, MappingKind::Keyword);
                } else {
                    builder.push_spanned("by", &lines[0], source_file);
                }
                builder.push('\n');
                for line in lines {
                    builder.push_str("  ");
                    builder.push_spanned(&line.content, line, source_file);
                    builder.push('\n');
                }
            }
        }
    } else {
        builder.push('\n');
    }

    builder.push_str(&format!("\nend {}\n", fn_name));
}

/// Generates a `Hermes.IsValid` instance for a type (struct/enum/union).
///
/// This instance proves that a type maintains its validity invariants (if any).
/// If no invariants are specified, it generates a `True` invariant.
fn generate_type(
    item: &TypeItem<crate::parse::hkd::Safe>,
    block: &TypeHermesBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
) {
    let type_name = match item {
        TypeItem::Struct(s) => s.inner.ident.clone(),
        TypeItem::Enum(e) => e.inner.ident.clone(),
        TypeItem::Union(u) => u.inner.ident.clone(),
    };

    let generics = match item {
        crate::parse::TypeItem::Struct(AstNode { inner: s }) => &s.generics,
        crate::parse::TypeItem::Enum(AstNode { inner: e }) => &e.generics,
        crate::parse::TypeItem::Union(AstNode { inner: u }) => &u.generics,
    };
    let (generic_params, generic_args, generic_bounds) = extract_generic_params(generics);

    builder.push_str(&format!("namespace {}\n\n", type_name));

    for line in &block.common.context {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }
    builder.push('\n');

    let type_app = (!generic_args.is_empty())
        .then(|| format!("({type_name} {})", generic_args.join(" ")))
        .unwrap_or_else(|| type_name.clone());

    let instance_params = if !generic_params.is_empty() || !generic_bounds.is_empty() {
        let params = if !generic_params.is_empty() {
            format!("{{{}}}", generic_params.join(" "))
        } else {
            String::new()
        };
        let bounds = if !generic_bounds.is_empty() {
            format!(" {}", generic_bounds.join(" "))
        } else {
            String::new()
        };
        format!(" {}{}", params, bounds)
    } else {
        String::new()
    };

    builder.push_str(&format!("instance{instance_params} : Hermes.IsValid {type_app} where\n"));
    builder.push_str("  isValid \n");

    if block.is_valid.is_empty() {
        builder.push_str("    True\n");
    } else {
        for (i, clause) in block.is_valid.iter().enumerate() {
            if i > 0 {
                builder.push_str(" ∧ \n");
            }
            builder.push_str("    ");
            for (j, line) in clause.lines.iter().enumerate() {
                if j > 0 {
                    builder.push('\n');
                }
                builder.push_spanned(&line.content, line, source_file);
            }
            builder.push('\n');
        }
    }

    builder.push_str(&format!("\nend {}\n", type_name));
}

/// Generates a `Safe` class for a trait.
///
/// This defines what it means for a type to safely implement a trait, including any
/// `isSafe` invariants the trait imposes on its implementors.
fn generate_trait(
    item: &crate::parse::hkd::SafeItemTrait,
    block: &TraitHermesBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
) {
    let trait_name = item.ident.clone();
    let (generic_params, generic_args, generic_bounds) = extract_generic_params(&item.generics);

    builder.push_str(&format!("namespace {}\n\n", trait_name));

    for line in &block.common.context {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }
    builder.push('\n');

    // Class Definition
    // class Safe (Self : Type) {T} [Trait Self T] : Prop where
    let params_decl = if !generic_params.is_empty() || !generic_bounds.is_empty() {
        let params = if !generic_params.is_empty() {
            format!("{{{}}}", generic_params.join(" "))
        } else {
            String::new()
        };
        let bounds = if !generic_bounds.is_empty() {
            format!(" {}", generic_bounds.join(" "))
        } else {
            String::new()
        };
        format!(" {}{}", params, bounds)
    } else {
        String::new()
    };

    let trait_app = (!generic_args.is_empty())
        .then(|| format!("{trait_name} Self {}", generic_args.join(" ")))
        .unwrap_or_else(|| format!("{trait_name} Self"));

    builder
        .push_str(&format!("class Safe (Self : Type){params_decl} [{trait_app}] : Prop where\n"));
    builder.push_str("  isSafe :");

    if block.is_safe.is_empty() {
        builder.push_str(" True\n");
    } else {
        builder.push('\n');
        for (i, clause) in block.is_safe.iter().enumerate() {
            if i > 0 {
                builder.push_str(" ∧ \n");
            }
            builder.push_str("    (");
            for (j, line) in clause.lines.iter().enumerate() {
                if j > 0 {
                    builder.push('\n');
                }
                builder.push_spanned(&line.content, line, source_file);
            }
            builder.push_str("\n)\n");
        }
    }

    builder.push_str(&format!("\nend {}\n", trait_name));
}

/// Extracts generic parameters for Lean.
/// Returns a tuple: (list of param names, list of args, list of bounds).
fn extract_generic_params(
    generics: &crate::parse::hkd::SafeGenerics,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    use crate::parse::hkd::{SafeGenericParam, SafeTypeParamBound, SafeWherePredicate};
    let mut params = Vec::new();
    let mut args = Vec::new();
    let mut bounds = Vec::new();

    for param in &generics.params {
        match param {
            SafeGenericParam::Type { name, bounds: p_bounds } => {
                params.push(name.clone());
                args.push(name.clone());
                for bound in p_bounds {
                    if let SafeTypeParamBound::Trait(ty) = bound {
                        bounds.push(format!("[{} {}]", map_type(ty), name));
                    }
                }
            }
            SafeGenericParam::Const(c) => {
                params.push(c.clone());
                args.push(c.clone());
            }
            SafeGenericParam::Lifetime => {}
        }
    }

    for pred in &generics.where_clause {
        if let SafeWherePredicate::Type { bounded_ty, bounds: p_bounds } = pred {
            let ty_str = map_type(bounded_ty);
            for bound in p_bounds {
                if let SafeTypeParamBound::Trait(trait_ty) = bound {
                    bounds.push(format!("[{} {}]", map_type(trait_ty), ty_str));
                }
            }
        }
    }

    (params, args, bounds)
}

/// Recursively maps Rust types to Lean types.
///
/// This handles:
/// - **Primitives**: `u32` -> `Std.U32`, `bool` -> `Bool`.
/// - **References**: `&T` -> `T` (references are erased in the functional model).
/// - **Pointers**: `*mut T` -> `(MutRawPtr T)`, `*const T` -> `(ConstRawPtr T)`.
/// - **Slices/Arrays**: `[T]` -> `(Slice T)`, `[T; N]` -> `(Array T N)`.
/// - **Tuples**: `(A, B)` -> `A × B`.
/// - **Paths**: `std::vec::Vec` -> `std.vec.Vec` (with segments joined by `.`).
fn map_type(ty: &crate::parse::hkd::SafeType) -> String {
    use crate::parse::hkd::SafeType::*;
    match ty {
        Path { qself: _, segments } => {
            if let Some(segment) = segments.last() {
                let s = &segment.ident;
                match s.as_str() {
                    "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32"
                    | "i64" | "i128" | "isize" => {
                        let mut capital = s.clone();
                        capital.replace_range(0..1, &s[0..1].to_uppercase());
                        return format!("Std.{}", capital);
                    }
                    "bool" => return "Bool".to_string(),
                    _ => {}
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
                elems.iter().map(map_type).collect::<Vec<_>>().join(" × ")
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
        Other => "MatchError".to_string(),
    }
}

/// Extracts `(arg_name, lean_type, is_mut_ref)` metadata from a function signature.
///
/// This metadata is used to build the Lean function signature and handle mutable reference splitting.
fn extract_args_metadata(func: &FunctionItem<crate::parse::hkd::Safe>) -> Vec<ArgInfo> {
    use crate::parse::hkd::{SafeFnArg, SafeType};
    let sig = match func {
        FunctionItem::Free(AstNode { inner: i }) => &i.sig,
        FunctionItem::Impl(AstNode { inner: i }) => &i.sig,
        FunctionItem::Trait(AstNode { inner: i }) => &i.sig,
    };

    sig.inputs
        .iter()
        .filter_map(|arg| match arg {
            SafeFnArg::Typed { name, ty } => {
                let mut is_mut_ref = false;
                if let SafeType::Reference { mutability, .. } = ty {
                    is_mut_ref = *mutability;
                }
                Some(ArgInfo { name: name.clone(), ty: map_type(ty), is_mut_ref })
            }
            SafeFnArg::Receiver { mutability, reference } => Some(ArgInfo {
                name: "self".to_string(),
                ty: "Self".to_string(),
                is_mut_ref: *mutability && *reference,
            }),
        })
        .collect()
}

/// Computes the return type string for the Lean theorem.
///
/// If the function has mutable reference arguments, the return type becomes a tuple
/// containing the original return value (if any) and the new values of all mutable arguments.
/// e.g. `fn foo(x: &mut u32) -> bool` becomes `Bool × Std.U32` in Lean.
fn get_return_type_string(func: &FunctionItem<crate::parse::hkd::Safe>) -> String {
    use crate::parse::hkd::{SafeFnArg, SafeReturnType, SafeType};

    let sig = match func {
        FunctionItem::Free(AstNode { inner: i }) => &i.sig,
        FunctionItem::Impl(AstNode { inner: i }) => &i.sig,
        FunctionItem::Trait(AstNode { inner: i }) => &i.sig,
    };

    let mut ret_types = Vec::new();

    // 1. Original Return Type
    let orig_ret = match &sig.output {
        SafeReturnType::Default => "Unit".to_string(),
        SafeReturnType::Type(ty) => map_type(ty),
    };

    if orig_ret != "Unit" && orig_ret != "MatchError" {
        ret_types.push(orig_ret);
    }

    // 2. Mutable Arguments
    for arg in &sig.inputs {
        match arg {
            SafeFnArg::Receiver { mutability: true, .. } => {
                ret_types.push("Self".to_string());
            }
            SafeFnArg::Typed { ty: SafeType::Reference { mutability: true, elem }, .. } => {
                ret_types.push(map_type(elem));
            }
            _ => {}
        }
    }

    if ret_types.is_empty() {
        "Unit".to_string()
    } else if ret_types.len() == 1 {
        ret_types[0].clone()
    } else {
        ret_types.join(" × ")
    }
}

/// Checks if the function returns `Unit` (or equivalent).
fn is_unit_return(func: &FunctionItem<crate::parse::hkd::Safe>) -> bool {
    use crate::parse::hkd::SafeReturnType;
    let sig = match func {
        FunctionItem::Free(AstNode { inner: i }) => &i.sig,
        FunctionItem::Impl(AstNode { inner: i }) => &i.sig,
        FunctionItem::Trait(AstNode { inner: i }) => &i.sig,
    };
    match &sig.output {
        SafeReturnType::Default => true,
        SafeReturnType::Type(ty) => matches!(map_type(ty).as_str(), "Unit" | "MatchError"),
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use miette::SourceSpan;
    // use proc_macro2::Span;
    use syn::parse_quote;

    use super::*;
    use crate::parse::{
        attr::{Clause, FunctionBlockInner, HermesBlockCommon},
        hkd::Mirror,
    };

    // --- Helpers ---
    fn map_qt(ty: syn::Type) -> String {
        map_type(&ty.mirror())
    }

    fn mk_spanned(s: &str) -> SpannedLine<crate::parse::hkd::Safe> {
        SpannedLine {
            content: s.to_string(),
            span: SourceSpan::new(0.into(), 0),
            raw_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
        }
    }

    fn mk_clause(lines: Vec<&str>) -> Clause<crate::parse::hkd::Safe> {
        Clause {
            keyword_span: AstNode { inner: SourceSpan::new(0.into(), 0) }, // Dummy span
            lines: lines.into_iter().map(mk_spanned).collect(),
        }
    }

    fn mk_block(
        requires: Vec<Vec<&str>>,
        ensures: Vec<Vec<&str>>,
        proof: Option<Vec<&str>>,
        axiom: Option<Vec<&str>>,
        header: Vec<&str>,
    ) -> FunctionHermesBlock<crate::parse::hkd::Safe> {
        let inner = if let Some(p) = proof {
            FunctionBlockInner::Proof {
                lines: p.into_iter().map(mk_spanned).collect(),
                keyword: None,
            }
        } else {
            FunctionBlockInner::Axiom {
                lines: axiom.unwrap().into_iter().map(mk_spanned).collect(),
                keyword: None,
            }
        };

        FunctionHermesBlock {
            common: HermesBlockCommon {
                context: header.into_iter().map(mk_spanned).collect(),
                content_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
                start_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
            },
            requires: requires.into_iter().map(mk_clause).collect(),
            ensures: ensures.into_iter().map(mk_clause).collect(),
            inner,
        }
    }

    fn mk_type_block(
        is_valid: Vec<Vec<&str>>,
        header: Vec<&str>,
    ) -> TypeHermesBlock<crate::parse::hkd::Safe> {
        TypeHermesBlock {
            common: HermesBlockCommon {
                context: header.into_iter().map(mk_spanned).collect(),
                content_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
                start_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
            },
            is_valid: is_valid.into_iter().map(mk_clause).collect(),
        }
    }

    fn mk_trait_block(
        is_safe: Vec<Vec<&str>>,
        header: Vec<&str>,
    ) -> TraitHermesBlock<crate::parse::hkd::Safe> {
        TraitHermesBlock {
            common: HermesBlockCommon {
                context: header.into_iter().map(mk_spanned).collect(),
                content_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
                start_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
            },
            is_safe: is_safe.into_iter().map(mk_clause).collect(),
        }
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
        assert_eq!(map_qt(parse_quote!((u32, bool))), "Std.U32 × Bool");
    }

    // --- Generation Tests ---

    #[test]
    fn test_gen_empty_spec() {
        // Valid case: user wants to prove trivial properties or just existence
        let item: syn::ItemFn = parse_quote! { fn foo() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("theorem spec"));
        assert!(out.contains("Hermes.SpecificationHolds (α := Unit) (foo) (fun _ => True)"));
        assert!(out.contains("sorry")); // Empty proof body defaults to sorry
    }

    #[test]
    fn test_gen_multiline_requires() {
        let item: syn::ItemFn = parse_quote! { fn foo(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        // Old test "Multiline requires (implicit AND)" now becomes 2 clauses
        let block = mk_block(
            vec![vec!["x.val > 0"], vec!["x.val < 10"]],
            vec![],
            Some(vec!["simp"]),
            None,
            vec![],
        );

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should wrap each line in parens and join with AND
        // (x.val > 0\n) ∧ \n(x.val < 10\n)
        assert!(out.contains("(x.val > 0\n)"));
        assert!(out.contains(" ∧ \n"));
        assert!(out.contains("(x.val < 10\n)"));
    }

    #[test]
    fn test_gen_requires_ordering() {
        // Regression test: Ensure `requires` comes AFTER the theorem signature.
        let item: syn::ItemFn = parse_quote! { fn foo(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![vec!["x.val > 0"]], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        let theorem_idx = out.find("theorem spec (x : Std.U32)").expect("Theorem not found");
        let requires_idx = out.find("(h_req : (x.val > 0\n))").expect("Requires not found");
        let return_type_idx = out.find("Hermes.SpecificationHolds").expect("Return type not found");

        assert!(theorem_idx < requires_idx, "Theorem should come before requires");
        assert!(requires_idx < return_type_idx, "Requires should come before return type");
    }

    #[test]
    fn test_gen_unsafe_axiom() {
        let item: syn::ItemFn = parse_quote! { unsafe fn ffi(p: *const u8) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(
            vec![],
            vec![vec!["result = .ok ()"]],
            None,
            Some(vec![]), // Axiom
            vec![],
        );

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("axiom spec (p : (ConstRawPtr Std.U8))"));
        assert!(out.contains("Hermes.SpecificationHolds (α := Unit) (ffi p)"));
        // No proof block for axioms
        assert!(!out.contains(":= by"));
    }

    #[test]
    fn test_gen_method_receiver() {
        let item: syn::ImplItemFn = parse_quote! { fn get(&self) -> bool { true } };
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["rfl"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(self : Self)"));
        assert!(out.contains("get self"));
    }

    #[test]
    fn test_gen_context_injection() {
        let item: syn::ItemFn = parse_quote! { fn foo() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec!["import Foo", "open Bar"]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("namespace foo"));
        assert!(out.contains("import Foo\nopen Bar"));
        assert!(out.contains("theorem spec"));
    }

    #[test]
    fn test_gen_struct_simple() {
        let item: syn::ItemStruct = parse_quote! { struct Point { x: u32 } };
        let ty_item = TypeItem::Struct(AstNode { inner: item.mirror() });
        let block = mk_type_block(vec![vec!["self.x > 0"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("namespace Point"));
        assert!(out.contains("instance : Hermes.IsValid Point where"));

        // CHANGED: Expect isValid without automatic binder
        assert!(out.contains("isValid"));
        assert!(!out.contains("isValid self :=")); // Should NOT be auto-generated
        assert!(out.contains("self.x > 0"));
        assert!(out.contains("self.x > 0"));
    }

    #[test]
    fn test_gen_struct_const_generic() {
        // struct Array<const N: usize> { data: [u8; N] }
        let item: syn::ItemStruct = parse_quote! {
            struct Array<const N: usize> { data: [u8; N] }
        };
        let ty_item = TypeItem::Struct(AstNode { inner: item.mirror() });
        let block = mk_type_block(vec![vec!["true"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should use implicit binder {N} and app (Array N)
        // We do not strictly need {N : Usize} because usage (Array N) infers it.
        assert!(out.contains("instance {N} : Hermes.IsValid (Array N) where"));
    }

    #[test]
    fn test_gen_struct_mixed_generics_ordering() {
        // struct Mixed<T, const N: usize, U>
        let item: syn::ItemStruct = parse_quote! {
            struct Mixed<T, const N: usize, U> { t: T, u: U }
        };
        let ty_item = TypeItem::Struct(AstNode { inner: item.mirror() });
        let block = mk_type_block(vec![vec!["true"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Order must be preserved: T, N, U
        assert!(out.contains("instance {T N U} : Hermes.IsValid (Mixed T N U) where"));
    }

    #[test]
    fn test_gen_struct_with_where_clause() {
        // Where clauses should be ignored in the instance signature
        let item: syn::ItemStruct = parse_quote! {
            struct Bound<T> where T: Copy { val: T }
        };
        let ty_item = TypeItem::Struct(AstNode { inner: item.mirror() });
        let block = mk_type_block(vec![vec!["true"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("instance {T} [Copy T] : Hermes.IsValid (Bound T) where"));
        // Matches Aeneas style: no bounds in instance context usually, unless required for the type itself?
        // Wait, for IsValid, we might need bounds if the invariant depends on them.
        // But in this test case logic, we ARE generating them now.
        assert!(out.contains("[Copy T]"));
    }

    #[test]
    fn test_gen_struct_with_inline_bounds() {
        let item: syn::ItemStruct = parse_quote! {
            struct Inline<T: Clone> { val: T }
        };
        let ty_item = TypeItem::Struct(AstNode { inner: item.mirror() });
        let block = mk_type_block(vec![vec!["true"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("instance {T} [Clone T] : Hermes.IsValid (Inline T) where"));
    }

    #[test]
    fn test_gen_trait_simple() {
        let item: syn::ItemTrait = parse_quote! { trait Identifiable {} };
        let block = mk_trait_block(vec![vec!["self.id > 0"]], vec![]);
        let mut builder = LeanBuilder::new();
        generate_trait(&item.mirror(), &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("namespace Identifiable"));
        // Matches Aeneas style: Self is first arg to trait class
        assert!(out.contains("class Safe (Self : Type) [Identifiable Self] : Prop where"));
        assert!(out.contains("isSafe :"));
        assert!(!out.contains("∀ (self : Self),")); // Should NOT be auto-generated
        assert!(out.contains("self.id > 0"));
    }

    #[test]
    fn test_gen_trait_generic() {
        let item: syn::ItemTrait = parse_quote! { trait Converter<T> {} };
        let block = mk_trait_block(vec![vec!["true"]], vec![]);
        let mut builder = LeanBuilder::new();
        generate_trait(&item.mirror(), &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Check implicit binders and app arguments
        assert!(out.contains("class Safe (Self : Type) {T} [Converter Self T] : Prop where"));
    }

    #[test]
    fn test_gen_trait_const_generic() {
        let item: syn::ItemTrait = parse_quote! { trait Array<const N: usize> {} };
        let block = mk_trait_block(vec![vec!["true"]], vec![]);
        let mut builder = LeanBuilder::new();
        generate_trait(&item.mirror(), &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("class Safe (Self : Type) {N} [Array Self N] : Prop where"));
    }

    #[test]
    fn test_gen_mut_ref_unit_return() {
        // fn inc(x: &mut u32)
        let item: syn::ItemFn = parse_quote! { fn inc(x: &mut u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["x = old_x + 1"]], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Assert bindings logic
        assert!(out.contains("let old_x := x"));
        // Unit return with 1 mut: pattern is just the mut val
        assert!(out.contains("let x_new := result"));
        assert!(out.contains("let result := ()"));
        assert!(out.contains("let x := x_new"));
    }

    #[test]
    fn test_gen_mut_ref_value_return() {
        // fn swap_ret(x: &mut u32) -> bool
        let item: syn::ItemFn = parse_quote! { fn swap_ret(x: &mut u32) -> bool { true } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["result = true"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("let old_x := x"));
        // Value return: (res, x_new)
        assert!(out.contains("let (result, x_new) := result"));
        assert!(out.contains("let x := x_new"));
    }

    #[test]
    fn test_gen_multiple_mut_refs() {
        // fn swap(a: &mut u32, b: &mut u32)
        let item: syn::ItemFn = parse_quote! { fn swap(a: &mut u32, b: &mut u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["a = old_b"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("let old_a := a"));
        assert!(out.contains("let old_b := b"));
        // Unit return, 2 muts: tuple of muts
        assert!(out.contains("let (a_new, b_new) := result"));
        assert!(out.contains("let result := ()"));
        assert!(out.contains("let a := a_new"));
        assert!(out.contains("let b := b_new"));
    }

    #[test]
    fn test_gen_mut_self() {
        // fn update(&mut self)
        let item: syn::ImplItemFn = parse_quote! { fn update(&mut self) {} };
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("let old_self := self"));
        assert!(out.contains("let self_new := result"));
        assert!(out.contains("let self := self_new"));
    }

    #[test]
    fn test_gen_explicit_unit_return() {
        let item: syn::ItemFn = parse_quote! { fn explicit(x: &mut u32) -> () {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should behave like implicit unit
        assert!(out.contains("let result := ()"));
    }

    #[test]
    fn test_gen_slice_and_array_types() {
        // fn process(data: &[u8], buf: &mut [u8; 16])
        let item: syn::ItemFn = parse_quote! {
            fn process(data: &[u8], buf: &mut [u8; 16]) {}
        };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["true"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Check Slice mapping
        assert!(out.contains("(data : (Slice Std.U8))"));

        // Check Array mapping
        assert!(out.contains("(buf : (Array Std.U8 16))"));
    }

    #[test]
    fn test_gen_owned_mut_self_is_not_output() {
        // fn consume(mut self) -> ()
        // Owned 'mut self' is an input, but NOT a return value in Aeneas.
        let item: syn::ImplItemFn = parse_quote! {
            fn consume(mut self) {}
        };
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["true"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should NOT generate old_self/self_new logic
        assert!(!out.contains("let old_self := self"));
        assert!(!out.contains("let self := self_new"));

        // Should just be a normal argument
        assert!(out.contains("(self : Self)"));
    }

    #[test]
    fn test_gen_mixed_mut_and_owned_args() {
        // fn mix(a: &mut u32, mut b: u32)
        // 'a' is a mutable reference (input + output).
        // 'b' is a mutable binding (input only).
        let item: syn::ItemFn = parse_quote! {
            fn mix(a: &mut u32, mut b: u32) {}
        };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["true"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // 'a' handling
        assert!(out.contains("let old_a := a"));
        assert!(out.contains("let a := a_new"));

        // 'b' handling (should NOT be treated as mutable output)
        assert!(!out.contains("let old_b := b"));
        assert!(!out.contains("let b := b_new"));
    }
    #[test]
    fn test_gen_implicit_proof_no_keyword_mapping() {
        let item: syn::ItemFn = parse_quote! { fn foo() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        // Implicit proof means empty proof block and NO keyword span
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);
        // mk_block helper creates a Proof variant with None keyword by default for proof args

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));

        // Should NOT contain a Keyword mapping for "by"
        let has_keyword = builder.mappings.iter().any(|m| matches!(m.kind, MappingKind::Keyword));

        assert!(!has_keyword, "Implicit proof should NOT map 'by' to any keyword");
    }
}
