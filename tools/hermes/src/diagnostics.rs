use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

use cargo_metadata::diagnostic::{Diagnostic, DiagnosticLevel};
use miette::{NamedSource, Report, SourceOffset};
use thiserror::Error;

pub struct DiagnosticMapper {
    shadow_root: PathBuf,
    user_root: PathBuf,
    source_cache: HashMap<PathBuf, String>,
}

#[derive(Error, Debug)]
#[error("{message}")]
struct MappedError {
    message: String,
    src: NamedSource<String>,
    labels: Vec<miette::LabeledSpan>,
    help: Option<String>,
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
}

impl DiagnosticMapper {
    pub fn new(shadow_root: PathBuf, user_root: PathBuf) -> Self {
        Self { shadow_root, user_root, source_cache: HashMap::new() }
    }

    pub fn map_path(&self, path: &Path) -> Option<PathBuf> {
        path.strip_prefix(&self.shadow_root).ok().map(|suffix| self.user_root.join(suffix))
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

    pub fn render_miette(&mut self, diag: &Diagnostic) {
        let primary_span = diag.spans.iter().find(|s| s.is_primary);

        let mut mapped = false;
        if let Some(span) = primary_span {
            let path = PathBuf::from(&span.file_name);
            if let Some(mapped_path) = self.map_path(&path) {
                if let Some(src) = self.get_source(&mapped_path) {
                    let mut labels = Vec::new();

                    for s in &diag.spans {
                        let s_path = PathBuf::from(&s.file_name);
                        if s_path == path || self.map_path(&s_path).as_ref() == Some(&mapped_path) {
                            let label_text = s.label.clone().unwrap_or_default();
                            let start = s.byte_start as usize;
                            let len = (s.byte_end - s.byte_start) as usize;
                            if start <= src.len() && start + len <= src.len() {
                                let offset = SourceOffset::from(start);
                                labels.push(miette::LabeledSpan::new(
                                    Some(label_text),
                                    offset.offset(),
                                    len,
                                ));
                            }
                        }
                    }

                    // Check children for help messages
                    let mut help_msg = None;
                    for child in &diag.children {
                        if child.level == DiagnosticLevel::Help {
                            help_msg = Some(child.message.clone());
                        }
                    }

                    let err = MappedError {
                        message: diag.message.clone(),
                        src: NamedSource::new(mapped_path.to_string_lossy(), src),
                        labels,
                        help: help_msg,
                    };

                    eprintln!("{:?}", Report::new(err));
                    mapped = true;
                }
            }
        }

        if !mapped {
            if diag.spans.is_empty() {
                eprintln!("[External Error] {}", diag.message);
            } else {
                eprintln!("[External Error] {}", diag.message);
            }
        }
    }
}
