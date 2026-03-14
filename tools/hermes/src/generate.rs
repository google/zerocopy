use crate::parse::{
    FunctionItem, ParsedItem, TypeItem,
    attr::{
        Clause, FunctionBlockInner, FunctionHermesBlock, SpannedLine, TraitHermesBlock,
        TypeHermesBlock,
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
/// those byte ranges back into the originating `/// ````hermes`
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
    // We disable the `linter.dupNamespace` option globally in the generated Lean file.
    // Hermes translation commonly generates nested namespaces that trigger this linter.
    //
    // FIXME: Maybe set this in the lakefile instead?
    builder.push_str("set_option linter.dupNamespace false\n");
    builder.push_str("set_option linter.unusedVariables false\n");
    builder.push_str("open Aeneas Aeneas.Std Result\n\n");
    builder.push_str("noncomputable section\n\n");
    builder.push_str("-- Specification linking Aeneas's opaque generated built-ins to Hermes.\n");
    builder.push_str("inject_builtins\n\n");
    // Open the crate namespace so types are visible.
    //
    // Note: Aeneas uses the crate name (snake_case) as the top-level namespace.
    // We replace hyphens with underscores to match.
    let crate_namespace = artifact.name.target_name.replace('-', "_");
    builder.push_str(&format!("namespace {}\n\n", crate_namespace));

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

    builder.push_str(&format!("end {}\n", crate_namespace));
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

struct AstStruct<'a> {
    name: String,
    params: String,
    args: String,
    outputs: String,
    fields: Vec<AstField<'a>>,
}

struct AstTheorem<'a> {
    kind_keyword: &'a str,
    keyword_span: Option<&'a miette::SourceSpan>,
    fn_span: &'a miette::SourceSpan,
    args_suffix: &'a str,
    generate_pre: bool,
    instance_params: &'a str,
    pre_args: Vec<String>,
    call_str: String,
    destructure_lhs: Option<String>,
    intro_pattern: String,
    post_args: Vec<String>,
    proof_context: Option<&'a Vec<SpannedLine<crate::parse::hkd::Safe>>>,
    destructure_req: Option<Vec<String>>,
    provided_cases: std::collections::HashMap<String, &'a Clause<crate::parse::hkd::Safe>>,
    exact_fields: Vec<String>,
    source_file: &'a std::path::Path,
}

// Renderers
impl LeanBuilder {
    fn render_struct(&mut self, ast: &AstStruct<'_>, source_file: &std::path::Path) {
        let outputs =
            if ast.outputs.is_empty() { String::new() } else { format!(" {}", ast.outputs) };
        self.push_str(&format!(
            "  structure {}{}{} {} : Prop where\n",
            ast.name, ast.params, ast.args, outputs
        ));
        for field in &ast.fields {
            self.push_str(&format!("    {} : ", field.name));
            if let Some(lean_type) = &field.lean_type {
                self.push_str(lean_type);
            }
            if !field.lines.is_empty() {
                for (j, line) in field.lines.iter().enumerate() {
                    if j > 0 {
                        self.push_str("\n      ");
                    }
                    self.push_spanned(&line.content, line, source_file);
                }
            }
            if let Some(tactic) = &field.proof_tactic {
                self.push_str(&format!(" := by {}", tactic));
            }
            self.push('\n');
        }
        self.push('\n');
    }

    fn render_theorem(&mut self, ast: &AstTheorem<'_>) {
        if ast.kind_keyword == "axiom" {
            if let Some(kw) = ast.keyword_span {
                self.push_mapped(ast.kind_keyword, kw, ast.source_file, MappingKind::Keyword);
            } else {
                self.push_str(ast.kind_keyword);
            }
        } else {
            self.push_str(ast.kind_keyword);
        }
        self.push(' ');
        self.push_mapped("spec", ast.fn_span, ast.source_file, MappingKind::Synthetic);
        self.push_str(ast.instance_params);
        self.push_str(ast.args_suffix);

        if ast.generate_pre {
            self.push_str("\n  (h_req : Pre");
            for arg in &ast.pre_args {
                self.push_str(&format!(" {}", arg));
            }
            self.push(')');
        }

        self.push_str(" :\n");
        self.push_str(&format!("  Aeneas.Std.WP.spec ({})", ast.call_str));
        self.push_str(" (fun ret_ =>");

        if let Some(lhs) = &ast.destructure_lhs {
            self.push_str(&format!("\n    let {} := ret_\n    ", lhs));
        } else {
            self.push(' ');
        }

        self.push_str("Post");
        for arg in &ast.post_args {
            self.push_str(&format!(" {}", arg));
        }
        self.push_str(")");

        if ast.kind_keyword == "theorem" {
            self.push_str(" := ");
            let first_keyword = if let Some(ctx) = ast.proof_context {
                ctx.first().map(|l| &l.span)
            } else {
                ast.provided_cases.values().next().map(|c| &c.keyword_span.inner)
            };

            if let Some(kw) = first_keyword {
                self.push_mapped("by", kw, ast.source_file, MappingKind::Keyword);
            } else {
                self.push_str("by");
            }
            self.push('\n');

            let mut is_context_sorry_only = false;
            let mut context_indent = String::new();

            if let Some(ctx) = ast.proof_context {
                let non_empty: Vec<_> =
                    ctx.iter().filter(|l| !l.content.trim().is_empty()).collect();
                if non_empty.len() == 1 && non_empty[0].content.trim() == "sorry" {
                    is_context_sorry_only = true;
                }
                if let Some(first) = ctx.first() {
                    let trimmed = first.content.trim_start();
                    let indent_len = first.content.len() - trimmed.len();
                    context_indent = " ".repeat(indent_len);
                }
            }

            let block_padding = "    ";

            self.push_str("  apply Hermes.wp_prove_orthogonal\n");
            self.push_str("  · ");
            if let Some(progress_clause) = ast.provided_cases.get("h_progress") {
                if progress_clause.lines.is_empty() {
                    self.push_str("sorry\n");
                } else {
                    for (i, line) in progress_clause.lines.iter().enumerate() {
                        if i > 0 {
                            self.push_str("\n    ");
                        }
                        self.push_spanned(&line.content, line, ast.source_file);
                    }
                    self.push('\n');
                }
            } else {
                self.push_str("eval_progress \"Missing orthogonal progress proof. The function progress verification was not automatically solvable.\"\n");
            }

            self.push_str("  · rintro ");
            self.push_str(&ast.intro_pattern);
            self.push_str(" h_returns\n");

            if let Some(req_fields) = &ast.destructure_req {
                self.push_str(&format!(
                    "{}rcases h_req with ⟨{}⟩\n",
                    block_padding,
                    req_fields.join(", ")
                ));
            }

            if !is_context_sorry_only {
                let var_indent = block_padding;

                self.push_str(&format!("{}exact\n", var_indent));

                if let Some(ctx) = ast.proof_context {
                    for line in ctx {
                        // Prepend 6 spaces to force indentation deeper than exact,
                        // but strip the initial user indentation to align with exact scope.
                        let trimmed = if line.content.starts_with(&context_indent) {
                            &line.content[context_indent.len()..]
                        } else {
                            line.content.trim_start()
                        };
                        self.push_str(&format!("{}  ", block_padding));
                        self.push_spanned(trimmed, line, ast.source_file);
                        self.push('\n');
                    }
                }

                if ast.exact_fields.is_empty() {
                    self.push_str(&format!("{}  ⟨⟩\n", var_indent));
                } else {
                    self.push_str(&format!("{}  {{\n", var_indent));
                    for field in &ast.exact_fields {
                        if let Some(clause) = ast.provided_cases.get(field) {
                            self.push_str(&format!("{}    {} := by\n", var_indent, field));
                            if clause.lines.is_empty() {
                                self.push_str(&format!("{}      sorry\n", var_indent));
                            } else {
                                for line in &clause.lines {
                                    self.push_str(&format!("{}      ", var_indent));
                                    self.push_spanned(&line.content, line, ast.source_file);
                                    self.push('\n');
                                }
                            }
                        }
                    }
                    self.push_str(&format!("{}  }}\n", var_indent));
                }
            } else {
                // If it's literally just `sorry`, we just emit it natively to sink the goal
                if let Some(ctx) = ast.proof_context {
                    for line in ctx {
                        let trimmed = if line.content.starts_with(&context_indent) {
                            &line.content[context_indent.len()..]
                        } else {
                            line.content.trim_start()
                        };
                        self.push_str(block_padding);
                        self.push_spanned(trimmed, line, ast.source_file);
                        self.push('\n');
                    }
                }
            }
        } else {
            self.push('\n');
        }
    }
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
///   Aeneas.Std.WP.spec (foo args...)
///     (fun ret =>
///       let (ret, new_mut_arg) := ret
///       ret = 5 && new_mut_arg = 6
///       ensures) :=
///   by ...
/// ```
fn generate_function(
    func: &FunctionItem<crate::parse::hkd::Safe>,
    block: &FunctionHermesBlock<crate::parse::hkd::Safe>,
    builder: &mut LeanBuilder,
    source_file: &std::path::Path,
) {
    let (fn_name, fn_span, impl_struct_name, generics) = match func {
        FunctionItem::Free(n) => {
            (n.inner.sig.ident.clone(), n.inner.sig.name_span, None, &n.inner.generics)
        }
        FunctionItem::Impl(n, opt_struct) => (
            n.inner.sig.ident.clone(),
            n.inner.sig.name_span,
            opt_struct.clone(),
            &n.inner.generics,
        ),
        FunctionItem::Trait(n) => {
            (n.inner.sig.ident.clone(), n.inner.sig.name_span, None, &n.inner.generics)
        }
    };

    let (generic_params, _, generic_bounds, dict_args) = extract_generic_params(generics);
    let args = extract_args_metadata(func, &impl_struct_name);
    let has_return_value = !is_unit_return(func);

    builder.push_str(&format!("namespace {}\n\n", fn_name));

    for line in &block.common.context {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }
    if !block.common.context.is_empty() {
        builder.push('\n');
    }

    let mut prop_requires = Vec::new();
    let mut instance_requires = Vec::new();
    for clause in block.requires.iter() {
        let first_line_trimmed = clause.lines.first().map(|l| l.content.trim_start()).unwrap_or("");
        if first_line_trimmed.starts_with('[') {
            instance_requires.push(clause);
        } else {
            prop_requires.push(clause);
        }
    }

    let mut instance_params = if !generic_params.is_empty() || !generic_bounds.is_empty() {
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

    for clause in &instance_requires {
        let name = clause.name.as_ref().map(|n| n.content.clone());
        let mut content = String::new();
        for (j, line) in clause.lines.iter().enumerate() {
            if j > 0 {
                content.push(' ');
            }
            let mut l = line.content.trim();
            if j == 0 && l.starts_with('[') {
                l = &l[1..];
            }
            if j == clause.lines.len() - 1 && l.ends_with(']') {
                l = &l[..l.len() - 1];
            }
            content.push_str(l);
        }
        if let Some(n) = name {
            instance_params.push_str(&format!(" [{} : {}]", n, content));
        } else {
            instance_params.push_str(&format!(" [{}]", content));
        }
    }

    let args_suffix = if !args.is_empty() {
        format!(
            " {}",
            args.iter()
                .map(|a| format!("({} : {})", a.name, a.lean_type))
                .collect::<Vec<_>>()
                .join(" ")
        )
    } else {
        String::new()
    };

    let has_args = !args.is_empty();
    let generate_pre = has_args || !prop_requires.is_empty();

    if generate_pre {
        let mut pre_fields = Vec::new();
        for arg in &args {
            pre_fields.push(AstField {
                name: format!("h_{}_is_valid", arg.name),
                lean_type: Some(format!("Hermes.IsValid.isValid {}", arg.name)),
                proof_tactic: Some(format!("verify_is_valid h_{}_is_valid", arg.name)),
                lines: Vec::new(),
            });
        }
        for clause in &prop_requires {
            let name = clause
                .name
                .as_ref()
                .map(|n| n.content.clone())
                .unwrap_or_else(|| "h_anon".to_string());
            pre_fields.push(AstField {
                name: name.clone(),
                lean_type: None,
                proof_tactic: Some(format!("verify_user_bound {}", name)),
                lines: clause.lines.iter().collect(),
            });
        }

        builder.render_struct(
            &AstStruct {
                name: "Pre".to_string(),
                params: instance_params.clone(),
                args: args_suffix.clone(),
                outputs: String::new(),
                fields: pre_fields,
            },
            source_file,
        );
    }

    let mut_args: Vec<&ArgInfo> = args.iter().filter(|a| a.is_mut_ref).collect();
    let has_mut_args = !mut_args.is_empty();

    let mut post_outputs = String::new();
    if has_return_value {
        use crate::parse::hkd::SafeReturnType;
        let ret_lean_type = match &func.sig().output {
            SafeReturnType::Default => "Unit".to_string(),
            SafeReturnType::Type(ty) => map_type(ty),
        };
        post_outputs.push_str(&format!("(ret : {})", ret_lean_type));
    }
    for arg in &mut_args {
        if !post_outputs.is_empty() {
            post_outputs.push(' ');
        }
        post_outputs.push_str(&format!("({}' : {})", arg.name, arg.lean_type));
    }

    let mut post_fields = Vec::new();
    if has_return_value {
        post_fields.push(AstField {
            name: "h_ret_is_valid".to_string(),
            lean_type: Some("Hermes.IsValid.isValid ret".to_string()),
            proof_tactic: Some("verify_is_valid h_ret_is_valid".to_string()),
            lines: Vec::new(),
        });
    }
    for arg in &mut_args {
        post_fields.push(AstField {
            name: format!("h_{}'_is_valid", arg.name),
            lean_type: Some(format!("Hermes.IsValid.isValid {}'", arg.name)),
            proof_tactic: Some(format!("verify_is_valid h_{}'_is_valid", arg.name)),
            lines: Vec::new(),
        });
    }

    for clause in block.ensures.iter() {
        let name =
            clause.name.as_ref().map(|n| n.content.clone()).unwrap_or_else(|| "h_anon".to_string());
        post_fields.push(AstField {
            name: name.clone(),
            lean_type: None,
            proof_tactic: Some(format!("verify_user_bound {}", name)),
            lines: clause.lines.iter().collect(),
        });
    }

    builder.render_struct(
        &AstStruct {
            name: "Post".to_string(),
            params: instance_params.clone(),
            args: args_suffix.clone(),
            outputs: post_outputs,
            fields: post_fields,
        },
        source_file,
    );

    let (kind_keyword, proof_cases, proof_context, keyword_span) = match &block.inner {
        FunctionBlockInner::Proof { context, cases } => {
            ("theorem", Some(cases), Some(context), None)
        }
        FunctionBlockInner::Axiom { keyword, .. } => {
            ("axiom", None, None, keyword.as_ref().map(|k| &k.inner))
        }
    };

    let mut pre_args = Vec::new();
    if generate_pre {
        pre_args.extend(dict_args.iter().cloned());
        pre_args.extend(args.iter().map(|a| a.name.clone()));
    }

    let mut base_name = "".to_string();
    if let Some(struct_name_node) = &impl_struct_name
        && let crate::parse::hkd::SafeType::Path { segments, .. } = &struct_name_node.inner
        && let Some(seg) = segments.last()
    {
        base_name = seg.ident.clone();
    }
    let call_name =
        if !base_name.is_empty() { format!("{}.{}", base_name, fn_name) } else { fn_name.clone() };

    let call_str = std::iter::once(call_name)
        .chain(dict_args.iter().cloned())
        .chain(args.iter().map(|a| a.name.clone()))
        .collect::<Vec<_>>()
        .join(" ");

    let destructure_lhs = if has_mut_args {
        let vars = mut_args.iter().map(|a| format!("{}'", a.name)).collect::<Vec<_>>().join(", ");
        if has_return_value {
            Some(format!("(ret, {})", vars))
        } else {
            if mut_args.len() == 1 {
                Some(format!("{}'", mut_args[0].name))
            } else {
                Some(format!("({})", vars))
            }
        }
    } else {
        None
    };

    let intro_pattern = if has_mut_args {
        let vars = mut_args.iter().map(|a| format!("{}'", a.name)).collect::<Vec<_>>().join(", ");
        if has_return_value {
            format!("⟨ret, {}⟩", vars)
        } else {
            if mut_args.len() == 1 {
                format!("{}'", mut_args[0].name)
            } else {
                format!("⟨{}⟩", vars)
            }
        }
    } else {
        if has_return_value {
            "ret".to_string()
        } else {
            // Technically `Unit`, but `ret` is a valid name.
            "ret".to_string()
        }
    };

    let mut post_call_args = Vec::new();
    post_call_args.extend(dict_args.iter().cloned());
    post_call_args.extend(args.iter().map(|a| a.name.clone()));
    if has_return_value {
        post_call_args.push(if has_mut_args { "ret".to_string() } else { "ret_".to_string() });
    }
    post_call_args.extend(mut_args.iter().map(|a| format!("{}'", a.name)));

    let destructure_req = if generate_pre {
        let mut req_fields = Vec::new();
        for arg in &args {
            req_fields.push(format!("h_{}_is_valid", arg.name));
        }
        for clause in &prop_requires {
            req_fields.push(
                clause
                    .name
                    .as_ref()
                    .map(|n| n.content.clone())
                    .unwrap_or_else(|| "h_anon".to_string()),
            );
        }
        if req_fields.is_empty() { None } else { Some(req_fields) }
    } else {
        None
    };

    let provided_cases: std::collections::HashMap<String, &Clause<_>> = proof_cases
        .map(|cases| {
            cases
                .iter()
                .map(|c| {
                    (
                        c.name
                            .as_ref()
                            .map(|n| n.content.clone())
                            .unwrap_or_else(|| "h_anon".to_string()),
                        c,
                    )
                })
                .collect()
        })
        .unwrap_or_default();

    let mut exact_fields = Vec::new();
    if has_return_value {
        exact_fields.push("h_ret_is_valid".to_string());
    }
    for arg in &mut_args {
        exact_fields.push(format!("h_{}'_is_valid", arg.name));
    }
    for clause in block.ensures.iter() {
        exact_fields.push(
            clause.name.as_ref().map(|n| n.content.clone()).unwrap_or_else(|| "h_anon".to_string()),
        );
    }

    builder.render_theorem(&AstTheorem {
        kind_keyword,
        keyword_span,
        fn_span: &fn_span,
        instance_params: &instance_params,
        args_suffix: &args_suffix,
        generate_pre,
        pre_args,
        call_str,
        destructure_lhs,
        intro_pattern,
        post_args: post_call_args,
        proof_context,
        destructure_req,
        provided_cases,
        exact_fields,
        source_file,
    });

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
    let (generic_params, generic_args, generic_bounds, _) = extract_generic_params(generics);

    builder.push_str(&format!("namespace {}\n\n", type_name));

    for line in &block.common.context {
        builder.push_spanned(&line.content, line, source_file);
        builder.push('\n');
    }
    builder.push('\n');

    let type_app = if !generic_args.is_empty() {
        format!("({type_name} {})", generic_args.join(" "))
    } else {
        type_name.clone()
    };

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
    if block.is_valid.is_empty() {
        builder.push_str("  isValid \n    True\n");
    } else {
        for clause in block.is_valid.iter() {
            builder.push_str("  ");
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
    let (generic_params, generic_args, generic_bounds, _) = extract_generic_params(&item.generics);

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

    let trait_app = if !generic_args.is_empty() {
        format!("{trait_name} Self {}", generic_args.join(" "))
    } else {
        format!("{trait_name} Self")
    };

    // We pass the trait instance as an explicit dictionary argument (`inst`)
    // rather than relying on typeclass resolution (`[{trait_app}]`). This
    // mirrors Aeneas's lowering strategy, which also lowers trait bounds to
    // explicit dictionary arguments.
    builder.push_str(&format!(
        "class Safe (Self : Type){params_decl} (inst : {trait_app}) : Prop where\n"
    ));
    if block.is_safe.is_empty() {
        builder.push_str("  isSafe : True\n");
    } else {
        for clause in block.is_safe.iter() {
            builder.push_str("  ");
            for (j, line) in clause.lines.iter().enumerate() {
                if j > 0 {
                    builder.push('\n');
                }
                builder.push_spanned(&line.content, line, source_file);
            }
            builder.push('\n');
        }
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
            // Instead, we emit it as a typeclass `[Hermes.core.marker.Sized T]`
            // which resolves implicitly.
            if mapped_trait == "core.marker.Sized" || mapped_trait == "Sized" {
                bounds.push(format!("[Hermes.core.marker.Sized {}]", ty_str));
            } else {
                // We generate an explicit dictionary argument for each trait
                // bound rather than relying on typeclass resolution. This
                // matches Aeneas's behavior, which expects explicit dictionary
                // arguments for trait bounds. We construct the identifier by
                // appending `Inst` to the base trait name, mimicking Aeneas's
                // `Clause0Inst` and `TraitInst` naming patterns.
                let dict_name = if mapped_trait.contains('.') {
                    mapped_trait.split('.').next_back().unwrap().to_string()
                } else {
                    mapped_trait.clone()
                };
                let dict_ident = format!("{}Inst", dict_name);
                bounds.push(format!("({} : {} {})", dict_ident, mapped_trait, ty_str));
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
                process_bound(bound, &ty_str);
            }
        }
    }

    (params, args, bounds, dict_args)
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
                ArgInfo { name: name.clone(), lean_type: map_type(ty), is_mut_ref }
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
    use std::path::Path;

    use miette::SourceSpan;
    // use proc_macro2::Span;
    use syn::parse_quote;

    use super::*;
    use crate::parse::{
        attr::{Clause, FunctionBlockInner, HermesBlockCommon, Propositions},
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
            name: None,
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
                context: vec![],
                cases: std::iter::once(Clause {
                    keyword_span: AstNode { inner: SourceSpan::new(0.into(), 0) },
                    name: None,
                    lines: p.into_iter().map(mk_spanned).collect(),
                })
                .collect(),
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
        assert!(out.contains("Aeneas.Std.WP.spec (foo) (fun ret_ =>"));
        assert!(out.contains("Post)"));
        assert!(out.contains("exact"));
        assert!(out.contains("  ⟨⟩")); // Empty proof body defaults to instantiating Post
    }

    #[test]
    fn test_gen_multiline_requires() {
        let item: syn::ItemFn = parse_quote! { fn foo(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        // Old test "Multiline requires (implicit AND)" now becomes 2 clauses
        let block = mk_block(
            vec![vec!["x.val > 0", "x.val < 10"]],
            vec![],
            Some(vec!["simp"]),
            None,
            vec![],
        );

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;
        println!("OUT:\n{}", out);

        assert!(out.contains("h_anon : x.val > 0"));
        assert!(out.contains("x.val < 10"));
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
        println!("test_gen_requires_ordering output:\n{}", out);

        let theorem_idx = out.find("theorem spec (x : Std.U32)").expect("Theorem not found");
        let requires_idx = out.find("(h_req : Pre x)").expect("Requires not found");
        let return_type_idx = out.find("Aeneas.Std.WP.spec").expect("Return type not found");

        assert!(theorem_idx < requires_idx, "Theorem should come before requires");
        assert!(requires_idx < return_type_idx, "Requires should come before return type");
    }

    #[test]
    fn test_gen_unsafe_axiom() {
        let item: syn::ItemFn = parse_quote! { unsafe fn ffi(p: *const u8) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(
            vec![],
            vec![vec!["ret = .ok ()"]],
            None,
            Some(vec![]), // Axiom
            vec![],
        );

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;
        println!("test_gen_unsafe_axiom output:\n{}", out);

        assert!(out.contains("axiom spec (p : (ConstRawPtr Std.U8))\n  (h_req : Pre p) :"));
        assert!(out.contains("Aeneas.Std.WP.spec (ffi p)"));
        // No proof block for axioms
        assert!(!out.contains("proof ("));
    }

    #[test]
    fn test_gen_method_receiver() {
        let item: syn::ImplItemFn = parse_quote! { fn get(&self) -> bool { true } };
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() }, None);
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
        let block = mk_type_block(vec![vec!["isValid self := self.x > 0"]], vec![]);

        let mut builder = LeanBuilder::new();
        generate_type(&ty_item, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("namespace Point"));
        assert!(out.contains("instance : Hermes.IsValid Point where"));

        assert!(out.contains("isValid self := self.x > 0"));
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

        assert!(out.contains("instance {T} (CopyInst : Copy T) : Hermes.IsValid (Bound T) where"));
        // Matches Aeneas style: no bounds in instance context usually, unless required for the type itself?
        // Wait, for IsValid, we might need bounds if the invariant depends on them.
        // But in this test case logic, we ARE generating them now.
        assert!(out.contains("(CopyInst : Copy T)"));
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

        assert!(
            out.contains("instance {T} (CloneInst : Clone T) : Hermes.IsValid (Inline T) where")
        );
    }

    #[test]
    fn test_gen_trait_simple() {
        let item: syn::ItemTrait = parse_quote! { trait Identifiable {} };
        let block = mk_trait_block(vec![vec!["isSafe : self.id > 0"]], vec![]);
        let mut builder = LeanBuilder::new();
        generate_trait(&item.mirror(), &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("namespace Identifiable"));
        // Matches Aeneas style: Self is first arg to trait class
        assert!(out.contains("class Safe (Self : Type) (inst : Identifiable Self) : Prop where"));
        assert!(out.contains("isSafe :"));
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
        assert!(
            out.contains("class Safe (Self : Type) {T} (inst : Converter Self T) : Prop where")
        );
    }

    #[test]
    fn test_gen_trait_const_generic() {
        let item: syn::ItemTrait = parse_quote! { trait Array<const N: usize> {} };
        let block = mk_trait_block(vec![vec!["true"]], vec![]);
        let mut builder = LeanBuilder::new();
        generate_trait(&item.mirror(), &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("class Safe (Self : Type) {N} (inst : Array Self N) : Prop where"));
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

        println!("MUT_REF_UNIT_RETURN:\n{}", out);
        // Should generate:
        assert!(out.contains("let x' := ret_"));
        assert!(!out.contains("let old_x"));
        assert!(!out.contains("let x := x_new"));
    }

    #[test]
    fn test_gen_mut_ref_value_return() {
        // fn swap_ret(x: &mut u32) -> bool
        let item: syn::ItemFn = parse_quote! { fn swap_ret(x: &mut u32) -> bool { true } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![vec!["ret = .ok ()"]], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should generate:
        // let (ret, x') := ret
        assert!(out.contains("let (ret, x') := ret"));
        assert!(!out.contains("let old_x := x"));
        assert!(!out.contains("let x := x_new"));
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

        // Should generate:
        // let (a', b') := ret
        assert!(out.contains("let (a', b') := ret_"));
        assert!(!out.contains("let old_a"));
    }

    #[test]
    fn test_gen_mut_self() {
        // fn update(&mut self)
        let item: syn::ImplItemFn = parse_quote! { fn update(&mut self) {} };
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() }, None);
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Should generate:
        // let self' := ret
        assert!(out.contains("let self' := ret"));
        assert!(!out.contains("let self := self_new"));

        // Should just be a normal argument
        assert!(out.contains("(self : Self)"));
    }

    #[test]
    fn test_gen_explicit_unit_return() {
        let item: syn::ItemFn = parse_quote! { fn explicit(x: &mut u32) -> () {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
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
        let func = FunctionItem::Impl(AstNode { inner: item.mirror() }, None);
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
        assert!(out.contains("let a' := ret"));
        assert!(!out.contains("let old_a := a"));

        // 'b' handling (should NOT be treated as mutable output)
        assert!(!out.contains("b'"));
    }
    #[test]
    fn test_implicit_proof_no_keyword_mapping() {
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

    #[test]
    fn test_generate_artifact_namespace() {
        use crate::{
            resolve::{HermesTargetKind, HermesTargetName},
            scanner::HermesArtifact,
        };
        let name = HermesTargetName {
            package_name: cargo_metadata::PackageName::new("my-package".to_string()),
            target_name: "my-target".to_string(),
            kind: HermesTargetKind::Lib,
        };
        let artifact = HermesArtifact {
            name,
            target_kind: HermesTargetKind::Lib,
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
    fn test_gen_impl_generic_lifetimes() {
        let item: syn::ImplItemFn = parse_quote! {
            fn get(&self) -> bool { true }
        };
        // Construct an impl_struct_name with lifetimes: MyStruct<'a, T>
        let ty: syn::Type = parse_quote! { MyStruct<'a, T> };
        let func = FunctionItem::Impl(
            AstNode { inner: item.mirror() },
            Some(AstNode { inner: ty.mirror() }),
        );
        let block = mk_block(vec![], vec![], Some(vec!["rfl"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(self : (MyStruct T))"));
    }

    #[test]
    fn test_gen_impl_type_alias() {
        let item: syn::ImplItemFn = parse_quote! {
            fn get(&self) -> bool { true }
        };
        let ty: syn::Type = parse_quote! { MyAlias };
        let func = FunctionItem::Impl(
            AstNode { inner: item.mirror() },
            Some(AstNode { inner: ty.mirror() }),
        );
        let block = mk_block(vec![], vec![], Some(vec!["rfl"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(self : MyAlias)"));
    }

    #[test]
    fn test_gen_impl_tuple() {
        let item: syn::ImplItemFn = parse_quote! {
            fn get(&self) -> bool { true }
        };
        let ty: syn::Type = parse_quote! { (u32, u32) };
        let func = FunctionItem::Impl(
            AstNode { inner: item.mirror() },
            Some(AstNode { inner: ty.mirror() }),
        );
        let block = mk_block(vec![], vec![], Some(vec!["rfl"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(self : Std.U32 × Std.U32)"));
    }

    #[test]
    fn test_gen_no_args_no_return() {
        let item: syn::ItemFn = parse_quote! { fn empty() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("Aeneas.Std.WP.spec (empty) (fun ret_ =>"));
        assert!(out.contains("Post)"));
        assert!(!out.contains("h_req"));
    }

    #[test]
    fn test_gen_args_no_mut_no_return() {
        let item: syn::ItemFn = parse_quote! { fn takes_arg(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid⟩"));
        assert!(out.contains("Aeneas.Std.WP.spec (takes_arg x) (fun ret_ =>"));
        assert!(out.contains("Post x)"));
    }

    #[test]
    fn test_gen_mut_args_no_return() {
        let item: syn::ItemFn = parse_quote! { fn mut_arg(x: &mut u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid⟩"));
        assert!(out.contains("Aeneas.Std.WP.spec (mut_arg x) (fun ret_ =>"));
        assert!(out.contains("Post x x'"));
    }

    #[test]
    fn test_gen_args_return_no_mut() {
        let item: syn::ItemFn = parse_quote! { fn returns_val(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid⟩"));
        assert!(out.contains("Aeneas.Std.WP.spec (returns_val x) (fun ret_ =>"));
        assert!(out.contains("Post x ret_)"));
    }

    #[test]
    fn test_gen_no_args_return() {
        let item: syn::ItemFn = parse_quote! { fn returns_val() -> u32 { 0 } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(!out.contains("h_req"));
        assert!(out.contains("Aeneas.Std.WP.spec (returns_val) (fun ret_ =>"));
        assert!(out.contains("Post ret_)"));
    }

    #[test]
    fn test_gen_multiple_args() {
        let item: syn::ItemFn = parse_quote! { fn mult(x: u32, y: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x y)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid, h_y_is_valid⟩"));
    }

    #[test]
    fn test_gen_edge_case_named_requires() {
        let item: syn::ItemFn = parse_quote! { fn named_reqs(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![vec!["x > 0"]], vec![], Some(vec!["simp"]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["x > 0"]);
        clause.name = Some(mk_spanned("h_positive"));
        props.push(clause).unwrap();
        block.requires = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("h_x_is_valid : Hermes.IsValid.isValid x"));
        assert!(out.contains("h_positive : x > 0"));
    }

    #[test]
    fn test_gen_edge_case_named_ensures() {
        let item: syn::ItemFn = parse_quote! { fn named_ens(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block =
            mk_block(vec![], vec![vec!["ret = x"]], Some(vec!["exact h_identity"]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["ret = x"]);
        clause.name = Some(mk_spanned("h_identity"));
        props.push(clause).unwrap();
        block.ensures = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("h_ret_is_valid : Hermes.IsValid.isValid ret"));
        assert!(out.contains("h_identity : ret = x"));
    }

    #[test]
    fn test_gen_edge_case_multiple_named_proofs() {
        let item: syn::ItemFn = parse_quote! { fn multiple_proofs(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });

        let mut block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);
        let mut props = Propositions::default();
        let mut c1 = mk_clause(vec!["ret = x"]);
        c1.name = Some(mk_spanned("p_one"));
        let mut c2 = mk_clause(vec!["ret > 0"]);
        c2.name = Some(mk_spanned("p_two"));
        props.push(c1).unwrap();
        props.push(c2).unwrap();
        block.ensures = props;

        let mut proof1 = mk_clause(vec!["exact rfl"]);
        proof1.name = Some(mk_spanned("p_one"));
        let mut proof2 = mk_clause(vec!["omega"]);
        proof2.name = Some(mk_spanned("p_two"));

        block.inner = FunctionBlockInner::Proof {
            context: vec![],
            cases: vec![proof1, proof2].into_iter().collect(),
        };

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("exact"));
        assert!(out.contains("  {"));
        assert!(!out.contains("next =>"));
        assert!(out.contains("p_one := by"));
        assert!(out.contains("exact rfl"));
        assert!(out.contains("p_two := by"));
        assert!(out.contains("omega"));
        assert!(out.contains("}"));
    }

    #[test]
    fn test_gen_edge_case_missing_proof_fallback() {
        let item: syn::ItemFn = parse_quote! { fn missing_fallback() -> bool { true } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });

        let mut block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["ret = true"]);
        clause.name = Some(mk_spanned("h_true"));
        props.push(clause).unwrap();
        block.ensures = props;

        // Provide NO explicit cases for the proof
        block.inner = FunctionBlockInner::Proof { context: vec![], cases: Propositions::default() };

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;
        println!("{}", out);

        assert!(out.contains("exact"));
        assert!(out.contains("  {"));
        assert!(!out.contains("next =>"));
        assert!(out.contains("h_true : ret = true := by verify_user_bound h_true"));
        assert!(!out.contains("sorry")); // We no longer inject sorry; macro handles it natively
        assert!(out.contains("}"));
    }

    #[test]
    fn test_gen_edge_case_empty_pre_struct() {
        let item: syn::ItemFn = parse_quote! { fn empty_pre() -> bool { true } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        // No inputs, no requires -> no Pre struct should be generated.
        let mut block = mk_block(vec![], vec![], Some(vec!["exact h_true"]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["ret = true"]);
        clause.name = Some(mk_spanned("h_true"));
        props.push(clause).unwrap();
        block.ensures = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        // Ensure Pre structure is entirely absent
        assert!(!out.contains("structure Pre"));
        // Ensure the theorem signature doesn't require a `h_req`
        assert!(!out.contains("(h_req : "));
        assert!(out.contains("Aeneas.Std.WP.spec"));
    }

    #[test]
    fn test_gen_edge_case_proof_context_injection() {
        let item: syn::ItemFn = parse_quote! { fn with_context(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec!["exact rfl"]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["ret = x"]);
        clause.name = Some(mk_spanned("h_id"));
        props.push(clause).unwrap();
        block.ensures = props;

        let mut proof_case = mk_clause(vec!["exact rfl"]);
        proof_case.name = Some(mk_spanned("h_id"));

        // Add a context line
        let ctx_line = mk_spanned("have h_ctx : x = x := by rfl");
        block.inner = FunctionBlockInner::Proof {
            context: vec![ctx_line],
            cases: std::iter::once(proof_case).collect(),
        };

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        let ctx_idx = out.find("have h_ctx").expect("Context not found");
        let exact_idx = out.find("exact\n      have").expect("exact\\n have context not found");

        // Context MUST injected after exact
        assert!(ctx_idx > exact_idx);
    }

    #[test]
    fn test_gen_edge_case_unnamed_proof_mapping() {
        let item: syn::ItemFn = parse_quote! { fn single_unnamed(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });

        // Single unnamed ensures
        let block = mk_block(vec![], vec![vec!["ret = x"]], Some(vec!["exact rfl"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(!out.contains("next =>"));
        assert!(out.contains("h_anon := by"));
        assert!(out.contains("exact rfl"));
    }

    #[test]
    fn test_gen_edge_case_explicit_is_valid_proof() {
        let item: syn::ItemFn = parse_quote! { fn explicit_is_valid(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["ret = x"]);
        clause.name = Some(mk_spanned("h_id"));
        props.push(clause).unwrap();
        block.ensures = props;

        // User explicitly overrides the auto-injected h_ret_is_valid proof
        let mut valid_proof = mk_clause(vec!["my_custom_tactic"]);
        valid_proof.name = Some(mk_spanned("h_ret_is_valid"));
        block.inner = FunctionBlockInner::Proof {
            context: vec![],
            cases: std::iter::once(valid_proof).collect(),
        };

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(!out.contains("next =>"));
        assert!(out.contains("h_ret_is_valid := by"));
        assert!(out.contains("my_custom_tactic"));
    }

    #[test]
    fn test_gen_auto_param_is_valid() {
        let item: syn::ItemFn = parse_quote! { fn implicit_validity(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(
            vec![vec!["x > 0"]],
            vec![vec!["ret = x"]],
            Some(vec!["exact rfl"]),
            None,
            vec![],
        );

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains(
            "h_x_is_valid : Hermes.IsValid.isValid x := by verify_is_valid h_x_is_valid"
        ));
        assert!(out.contains(
            "h_ret_is_valid : Hermes.IsValid.isValid ret := by verify_is_valid h_ret_is_valid"
        ));
    }

    #[test]
    fn test_gen_auto_param_requires_user_bound() {
        let item: syn::ItemFn = parse_quote! { fn implicit_requires(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec!["exact rfl"]), None, vec![]);

        // Add one unnamed and one named requires clause
        let mut props = Propositions::default();
        props.push(mk_clause(vec!["x > 0"])).unwrap();
        let mut named_clause = mk_clause(vec!["x < 10"]);
        named_clause.name = Some(mk_spanned("h_less_than"));
        props.push(named_clause).unwrap();
        block.requires = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("h_anon : x > 0 := by verify_user_bound h_anon"));
        assert!(out.contains("h_less_than : x < 10 := by verify_user_bound h_less_than"));
    }

    #[test]
    fn test_gen_edge_case_destructure_multiple_named_preconditions() {
        let item: syn::ItemFn = parse_quote! { fn multiple_reqs(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);
        let mut props = Propositions::default();
        let mut c1 = mk_clause(vec!["x > 0"]);
        c1.name = Some(mk_spanned("h_pos"));
        let mut c2 = mk_clause(vec!["x < 10"]);
        c2.name = Some(mk_spanned("h_lt"));
        props.push(c1).unwrap();
        props.push(c2).unwrap();
        block.requires = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid, h_lt, h_pos⟩"));
    }

    #[test]
    fn test_gen_edge_case_destructure_mixed_named_unnamed_preconditions() {
        let item: syn::ItemFn = parse_quote! { fn mixed_reqs(x: u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);
        let mut props = Propositions::default();
        let mut c1 = mk_clause(vec!["x > 0"]);
        c1.name = Some(mk_spanned("h_pos"));
        props.push(c1).unwrap();
        props.push(mk_clause(vec!["x < 10"])).unwrap();
        block.requires = props;
        // Second requires is unnamed

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre x)"));
        assert!(out.contains("rcases h_req with ⟨h_x_is_valid, h_anon, h_pos⟩"));
    }

    #[test]
    fn test_gen_edge_case_destructure_no_args_but_requires() {
        let item: syn::ItemFn = parse_quote! { fn no_args() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);
        let mut props = Propositions::default();
        let mut clause = mk_clause(vec!["True"]);
        clause.name = Some(mk_spanned("h_true"));
        props.push(clause).unwrap();
        block.requires = props;

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("(h_req : Pre)"));
        assert!(out.contains("rcases h_req with ⟨h_true⟩"));
    }

    #[test]
    fn test_gen_edge_case_empty_post_with_anon_ignored() {
        let item: syn::ItemFn = parse_quote! { fn empty_post() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["trivial"]), None, vec![]);
        // The user provided an unnamed proof but there are no ensures.
        // This is caught by validate.rs usually, but we should generate `exact ⟨⟩` safely if it reaches here.

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("exact"));
        assert!(out.contains("  ⟨⟩"));
        assert!(!out.contains("trivial")); // The orphan proof is dropped safely
    }

    #[test]
    fn test_gen_edge_case_mixed_some_proofs_missing() {
        let item: syn::ItemFn = parse_quote! { fn partial_proofs(x: u32) -> u32 { x } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let mut block = mk_block(vec![], vec![], Some(vec![]), None, vec![]);
        let mut props = Propositions::default();
        let mut c1 = mk_clause(vec!["x > 0"]);
        c1.name = Some(mk_spanned("h_gt"));
        let mut c2 = mk_clause(vec!["x < 10"]);
        c2.name = Some(mk_spanned("h_lt"));
        props.push(c1).unwrap();
        props.push(c2).unwrap();
        block.ensures = props;

        // User only provided proof for `h_gt`
        let mut proof1 = mk_clause(vec!["exact rfl"]);
        proof1.name = Some(mk_spanned("h_gt"));
        block.inner =
            FunctionBlockInner::Proof { context: vec![], cases: std::iter::once(proof1).collect() };

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        println!("DEBUG_OUT:\n{}", out);
        assert!(out.contains("exact"));
        assert!(out.contains("  {"));
        assert!(out.contains("h_gt := by\n          exact rfl"));
        // `h_lt` is missing, so it should NOT be emitted explicitly (relies on autoParam)
        assert!(!out.contains("h_lt :="));
        assert!(out.contains("}"));
    }

    #[test]
    fn test_gen_rintro_unit_return_no_mut_args() {
        let item: syn::ItemFn = parse_quote! { fn f() {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro ret h_returns"));
    }

    #[test]
    fn test_gen_rintro_value_return_no_mut_args() {
        let item: syn::ItemFn = parse_quote! { fn f() -> u32 { 0 } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro ret h_returns"));
    }

    #[test]
    fn test_gen_rintro_unit_return_one_mut_arg() {
        let item: syn::ItemFn = parse_quote! { fn f(x: &mut u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro x' h_returns"));
    }

    #[test]
    fn test_gen_rintro_unit_return_two_mut_args() {
        let item: syn::ItemFn = parse_quote! { fn f(x: &mut u32, y: &mut u32) {} };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro ⟨x', y'⟩ h_returns"));
    }

    #[test]
    fn test_gen_rintro_value_return_one_mut_arg() {
        let item: syn::ItemFn = parse_quote! { fn f(x: &mut u32) -> u32 { 0 } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro ⟨ret, x'⟩ h_returns"));
    }

    #[test]
    fn test_gen_rintro_value_return_two_mut_args() {
        let item: syn::ItemFn = parse_quote! { fn f(x: &mut u32, y: &mut u32) -> u32 { 0 } };
        let func = FunctionItem::Free(AstNode { inner: item.mirror() });
        let block = mk_block(vec![], vec![], Some(vec!["simp"]), None, vec![]);

        let mut builder = LeanBuilder::new();
        generate_function(&func, &block, &mut builder, Path::new("test.rs"));
        let out = builder.buf;

        assert!(out.contains("rintro ⟨ret, x', y'⟩ h_returns"));
    }
}
