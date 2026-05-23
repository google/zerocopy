// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Handling of compiler diagnostics and source mapping.
//
// This module provides the [`crate::diagnostics::DiagnosticMapper`] struct, which is responsible
// for translating diagnostics from external tools, such as Charon, back to
// annotated Rust source code. It maps errors in generated intermediate files
// back to their origin spans in the user's codebase.

pub use cargo_metadata::diagnostic::{Diagnostic, DiagnosticLevel, DiagnosticSpan};

/// Maps diagnostics from generated intermediate code back to Rust source code.
///
/// The Charon compiler has no knowledge of the Rust workspace layout that
/// orchestrated its execution. It reports diagnostics against generated or
/// rewritten compilation inputs.
///
/// This mapper cross-references the compiler's emitted byte spans to
/// annotations in Rust source code, dynamically synthesizing a
/// [`miette::NamedSource`] that points into the user's `.rs` workspace files.
pub struct DiagnosticMapper {
    user_root: std::path::PathBuf,
    user_root_canonical: std::path::PathBuf,
    source_cache: std::collections::HashMap<std::path::PathBuf, String>,
}

#[derive(thiserror::Error, Debug)]
#[error("{message}")]
struct MappedError {
    message: String,
    src: miette::NamedSource<String>,
    labels: Vec<miette::LabeledSpan>,
    help: Option<String>,
    related: Vec<MappedError>,
    severity: Option<miette::Severity>,
}

impl miette::Diagnostic for MappedError {
    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.src)
    }

    fn labels(&self) -> Option<Box<dyn std::iter::Iterator<Item = miette::LabeledSpan> + '_>> {
        if self.labels.is_empty() { None } else { Some(Box::new(self.labels.iter().cloned())) }
    }

    fn help(&self) -> Option<Box<dyn std::fmt::Display + '_>> {
        self.help.as_ref().map(|h| Box::new(h.clone()) as Box<dyn std::fmt::Display>)
    }

    fn related<'a>(
        &'a self,
    ) -> Option<Box<dyn std::iter::Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        if self.related.is_empty() {
            None
        } else {
            let iter = self.related.iter().map(|e| e as &dyn miette::Diagnostic);
            Some(Box::new(iter))
        }
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.severity
    }
}

impl DiagnosticMapper {
    /// Creates a new mapper rooted at `user_root`.
    pub fn new(user_root: std::path::PathBuf) -> Self {
        let user_root_canonical =
            std::fs::canonicalize(&user_root).unwrap_or_else(|_| user_root.clone());
        Self { user_root, user_root_canonical, source_cache: std::collections::HashMap::new() }
    }

    /// Resolves a path relative to the user root, if applicable.
    ///
    /// This ensures we only report diagnostics for files within the user's
    /// workspace, avoiding noise from dependencies or system files.
    pub fn map_path(&self, path: &std::path::Path) -> Option<std::path::PathBuf> {
        let mut p = path.to_path_buf();
        if p.is_relative() {
            p = self.user_root.join(p);
        }

        p = {
            let mut normalized = std::path::PathBuf::new();
            for component in p.components() {
                let most_recent = normalized.components().next_back();
                match (component, most_recent) {
                    (std::path::Component::ParentDir, Some(std::path::Component::Normal(_))) => {
                        normalized.pop();
                    }
                    (std::path::Component::CurDir, _) => {}
                    _ => normalized.push(component),
                }
            }
            normalized
        };

        // Strategy B: Starts with user_root or user_root_canonical.
        (p.starts_with(&self.user_root) || p.starts_with(&self.user_root_canonical)).then_some(p)
    }

    fn get_source(&mut self, path: &std::path::Path) -> Option<String> {
        if let Some(src) = self.source_cache.get(path) {
            return Some(src.clone());
        }
        if let Ok(src) = std::fs::read_to_string(path) {
            self.source_cache.insert(path.to_path_buf(), src.clone());
            Some(src)
        } else {
            None
        }
    }

    /// Renders a diagnostic (from Cargo or Charon) using `miette`.
    ///
    /// This is strictly for rendering errors native to Rust processing (where
    /// the structured error originates from our `syn` parser or Charon's
    /// processing), bringing them into a unified, colorized `miette` format.
    pub fn render_miette<F>(&mut self, diag: &Diagnostic, mut printer: F)
    where
        F: FnMut(String),
    {
        let mut mapped_paths_and_spans: std::collections::HashMap<
            std::path::PathBuf,
            Vec<&DiagnosticSpan>,
        > = std::collections::HashMap::new();

        // 1) Group spans by mapped path.
        for s in &diag.spans {
            let p = std::path::PathBuf::from(&s.file_name);
            if let Some(mapped_path) = self.map_path(&p) {
                mapped_paths_and_spans.entry(mapped_path).or_default().push(s);
            }
        }

        // TODO: Should we be collecting all of them, not just the first?
        let help_msg = diag
            .children
            .iter()
            .find(|child| child.level == DiagnosticLevel::Help)
            .map(|child| child.message.clone());

        if !mapped_paths_and_spans.is_empty() {
            // Find the path that contains the primary span, or just take the
            // first one.
            let primary_path = diag
                .spans
                .iter()
                .find(|s| s.is_primary)
                .and_then(|s| self.map_path(&std::path::PathBuf::from(&s.file_name)))
                .or_else(|| mapped_paths_and_spans.keys().next().cloned());

            if let Some(main_path) = primary_path {
                let mut all_errors = Vec::new();

                // Sort the paths to have the primary path first.
                let mut paths: Vec<std::path::PathBuf> =
                    mapped_paths_and_spans.keys().cloned().collect();
                paths.sort_by_key(|p| p != &main_path);

                for p in paths {
                    if let Some(src) = self.get_source(&p) {
                        let labels: Vec<_> = mapped_paths_and_spans
                            .get(&p)
                            .unwrap()
                            .iter()
                            .filter_map(|s| {
                                let label_text = s.label.clone().unwrap_or_default();
                                let start: usize = s.byte_start.try_into().unwrap();
                                let len = (s.byte_end - s.byte_start).try_into().unwrap();
                                (start <= src.len() && start + len <= src.len()).then(|| {
                                    let offset = miette::SourceOffset::from(start);
                                    miette::LabeledSpan::new(Some(label_text), offset.offset(), len)
                                })
                            })
                            .collect();

                        let err = MappedError {
                            message: if p == main_path {
                                diag.message.clone()
                            } else {
                                format!("related to: {}", p.display())
                            },
                            src: miette::NamedSource::new(p.to_string_lossy(), src),
                            labels,
                            help: if p == main_path { help_msg.clone() } else { None },
                            related: Vec::new(),
                            severity: match diag.level {
                                DiagnosticLevel::Error | DiagnosticLevel::Ice => {
                                    Some(miette::Severity::Error)
                                }
                                DiagnosticLevel::Warning => Some(miette::Severity::Warning),
                                _ => Some(miette::Severity::Advice),
                            },
                        };
                        all_errors.push(err);
                    }
                }

                if !all_errors.is_empty() {
                    let mut main_err = all_errors.remove(0);
                    main_err.related = all_errors;
                    printer(format!("{:?}", miette::Report::new(main_err)));
                    return;
                }
            }
        }

        // If we get here, no span was successfully mapped.
        let prefix = match diag.level {
            DiagnosticLevel::Error | DiagnosticLevel::Ice => "[External Error]",
            DiagnosticLevel::Warning => "[External Warning]",
            _ => "[External Info]",
        };

        if let Some(span) = diag.spans.first() {
            printer(format!("{} {}:{}: {}", prefix, span.file_name, span.line_start, diag.message));
        } else {
            printer(format!("{} {}", prefix, diag.message));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_path_traversal() {
        let temp = tempfile::tempdir().unwrap();
        let user_root = temp.path().join("workspace");
        std::fs::create_dir(&user_root).unwrap();

        // Create a symlink in the workspace pointing outside.
        let outside = temp.path().join("outside");
        std::fs::create_dir(&outside).unwrap();
        std::os::unix::fs::symlink(&outside, user_root.join("symlink")).unwrap();

        let mapper = DiagnosticMapper::new(user_root.clone());

        let malicious_path = user_root.join("symlink/../passwd");

        let mapped = mapper.map_path(&malicious_path);

        // The path normalization routine relies on lexical analysis. It
        // normalizes `workspace/symlink/../passwd` into `workspace/passwd`.
        // Even though a physical resolution of this path would point to
        // `outside/passwd` via the symlink, the lexical flattening grounds it
        // back into the workspace root. Because the mapped path is inside the
        // tree, the logic considers it sound and explicitly strips the
        // traversal.
        //
        // Conversely, attempts to escape the root directory directly using `..`
        // without an internal symlink are trapped and rejected.
        let escaped_path = user_root.join("../outside/passwd");
        assert_eq!(mapper.map_path(&escaped_path), None, "Path traversal should be rejected");

        // The lexically normalized path inside the symlink safely maps to
        // `workspace/passwd`.
        assert_eq!(mapped, Some(user_root.join("passwd")));
    }
}
