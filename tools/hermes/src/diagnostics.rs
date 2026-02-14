use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

pub use cargo_metadata::diagnostic::{Diagnostic, DiagnosticLevel, DiagnosticSpan};
use miette::{NamedSource, Report, SourceOffset};
use thiserror::Error;

pub struct DiagnosticMapper {
    user_root: PathBuf,
    user_root_canonical: PathBuf,
    source_cache: HashMap<PathBuf, String>,
}

#[derive(Error, Debug)]
#[error("{message}")]
struct MappedError {
    message: String,
    src: NamedSource<String>,
    labels: Vec<miette::LabeledSpan>,
    help: Option<String>,
    related: Vec<MappedError>,
}

impl miette::Diagnostic for MappedError {
    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(&self.src)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        if self.labels.is_empty() {
            None
        } else {
            Some(Box::new(self.labels.iter().cloned()))
        }
    }

    fn help(&self) -> Option<Box<dyn std::fmt::Display + '_>> {
        self.help.as_ref().map(|h| Box::new(h.clone()) as Box<dyn std::fmt::Display>)
    }

    fn related<'a>(&'a self) -> Option<Box<dyn Iterator<Item = &'a dyn miette::Diagnostic> + 'a>> {
        if self.related.is_empty() {
            None
        } else {
            let iter = self.related.iter().map(|e| e as &dyn miette::Diagnostic);
            Some(Box::new(iter))
        }
    }
}

impl DiagnosticMapper {
    pub fn new(user_root: PathBuf) -> Self {
        let user_root_canonical =
            fs::canonicalize(&user_root).unwrap_or_else(|_| user_root.clone());
        Self { user_root, user_root_canonical, source_cache: HashMap::new() }
    }

    pub fn map_path(&self, path: &Path) -> Option<PathBuf> {
        let mut p = path.to_path_buf();
        if p.is_relative() {
            p = self.user_root.join(p);
        }

        // Strategy B: Starts with user_root or user_root_canonical
        (p.starts_with(&self.user_root) || p.starts_with(&self.user_root_canonical)).then_some(p)
    }

    fn get_source(&mut self, path: &Path) -> Option<String> {
        if let Some(src) = self.source_cache.get(path) {
            return Some(src.clone());
        }
        if let Ok(src) = fs::read_to_string(path) {
            self.source_cache.insert(path.to_path_buf(), src.clone());
            Some(src)
        } else {
            None
        }
    }

    pub fn render_miette<F>(&mut self, diag: &Diagnostic, mut printer: F)
    where
        F: FnMut(String),
    {
        let mut mapped_paths_and_spans: HashMap<PathBuf, Vec<&DiagnosticSpan>> = HashMap::new();

        // 1) Group spans by mapped path
        for s in &diag.spans {
            let p = PathBuf::from(&s.file_name);
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
            // Find the path that contains the primary span, or just take the first one
            let primary_path = diag
                .spans
                .iter()
                .find(|s| s.is_primary)
                .and_then(|s| self.map_path(&PathBuf::from(&s.file_name)))
                .or_else(|| mapped_paths_and_spans.keys().next().cloned());

            if let Some(main_path) = primary_path {
                let mut all_errors = Vec::new();

                // Sort the paths to have the primary path first
                let mut paths: Vec<PathBuf> = mapped_paths_and_spans.keys().cloned().collect();
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
                                    let offset = SourceOffset::from(start);
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
                            src: NamedSource::new(p.to_string_lossy(), src),
                            labels,
                            help: if p == main_path { help_msg.clone() } else { None },
                            related: Vec::new(),
                        };
                        all_errors.push(err);
                    }
                }

                if !all_errors.is_empty() {
                    let mut main_err = all_errors.remove(0);
                    main_err.related = all_errors;
                    printer(format!("{:?}", Report::new(main_err)));
                    return;
                }
            }
        }

        // If we get here, no span was successfully mapped
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

    pub fn render_raw<F>(
        &mut self,
        file_name: &str,
        message: String,
        level: DiagnosticLevel,
        byte_start: usize,
        byte_end: usize,
        mut printer: F,
    ) where
        F: FnMut(String),
    {
        let p = PathBuf::from(file_name);
        if let Some(mapped_path) = self.map_path(&p) {
            if let Some(src) = self.get_source(&mapped_path) {
                let start = byte_start;
                if byte_end >= start {
                    let len = byte_end - start;
                    if start <= src.len() && start + len <= src.len() {
                        let offset = SourceOffset::from(start);
                        let label = miette::LabeledSpan::new(
                            Some("here".to_string()),
                            offset.offset(),
                            len,
                        );
                        let err = MappedError {
                            message,
                            src: NamedSource::new(mapped_path.to_string_lossy(), src),
                            labels: vec![label],
                            help: None,
                            related: Vec::new(),
                        };
                        printer(format!("{:?}", Report::new(err)));
                        return;
                    }
                }
            }
        }

        // Fallback
        let prefix = match level {
            DiagnosticLevel::Error | DiagnosticLevel::Ice => "[External Error]",
            DiagnosticLevel::Warning => "[External Warning]",
            _ => "[External Info]",
        };
        printer(format!("{} {}: {}", prefix, file_name, message));
    }
}
