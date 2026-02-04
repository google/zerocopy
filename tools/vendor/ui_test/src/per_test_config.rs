//! This module allows you to configure the default settings for all
//! tests. All data structures here are normally parsed from `@` comments
//! in the files. These comments still overwrite the defaults, although
//! some boolean settings have no way to disable them.

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use spanned::Spanned;

use crate::build_manager::BuildManager;
use crate::custom_flags::Flag;
pub use crate::diagnostics::Level;
use crate::diagnostics::{Diagnostics, Message};
pub use crate::parser::{Comments, Condition, Revisioned};
use crate::parser::{ErrorMatch, ErrorMatchKind, OptWithLine};
use crate::status_emitter::TestStatus;
use crate::test_result::{Errored, TestOk, TestResult};
use crate::{core::strip_path_prefix, Config, Error, Errors, OutputConflictHandling, TestRun};

/// All information needed to run a single test
pub struct TestConfig<'a> {
    /// The generic config for all tests
    pub config: Config,
    pub(crate) comments: &'a Comments,
    /// The path to the folder where to look for aux files
    pub aux_dir: &'a Path,
    /// When doing long-running operations, you can inform the user about it here.
    pub status: Box<dyn TestStatus>,
}

impl TestConfig<'_> {
    pub(crate) fn patch_out_dir(&mut self) {
        // Put aux builds into a separate directory per path so that multiple aux files
        // from different directories (but with the same file name) don't collide.
        let relative =
            strip_path_prefix(self.status.path().parent().unwrap(), &self.config.out_dir);

        self.config.out_dir.extend(relative);
    }

    /// Create a file extension that includes the current revision if necessary.
    pub fn extension(&self, extension: &str) -> String {
        if self.status.revision().is_empty() {
            extension.to_string()
        } else {
            format!("{}.{extension}", self.status.revision())
        }
    }

    /// The test's expected exit status after applying all comments
    pub fn exit_status(&self) -> Result<Option<Spanned<i32>>, Errored> {
        self.comments.exit_status(self.status.revision())
    }

    /// Whether compiler messages require annotations
    pub fn require_annotations(&self) -> Option<Spanned<bool>> {
        self.comments.require_annotations(self.status.revision())
    }

    pub(crate) fn find_one<'a, T: 'a>(
        &'a self,
        kind: &str,
        f: impl Fn(&'a Revisioned) -> OptWithLine<T>,
    ) -> Result<OptWithLine<T>, Errored> {
        self.comments
            .find_one_for_revision(self.status.revision(), kind, f)
    }

    /// All comments that apply to the current test.
    pub fn comments(&self) -> impl Iterator<Item = &'_ Revisioned> {
        self.comments.for_revision(self.status.revision())
    }

    pub(crate) fn collect<'a, T, I: Iterator<Item = T>, R: FromIterator<T>>(
        &'a self,
        f: impl Fn(&'a Revisioned) -> I,
    ) -> R {
        self.comments().flat_map(f).collect()
    }

    fn apply_custom(
        &self,
        cmd: &mut Command,
        build_manager: &BuildManager<'_>,
    ) -> Result<(), Errored> {
        let mut all = BTreeMap::new();
        for rev in self.comments.for_revision(self.status.revision()) {
            for (&k, flags) in &rev.custom {
                for flag in &flags.content {
                    match all.entry(k) {
                        Entry::Vacant(v) => _ = v.insert(vec![flag]),
                        Entry::Occupied(mut o) => {
                            if o.get().last().unwrap().must_be_unique() {
                                // Overwrite previous value so that revisions overwrite default settings
                                // FIXME: report an error if multiple revisions conflict
                                assert_eq!(o.get().len(), 1);
                                o.get_mut()[0] = flag;
                            } else {
                                o.get_mut().push(flag);
                            }
                        }
                    }
                }
            }
        }
        for flags in all.values() {
            for flag in flags {
                flag.apply(cmd, self, build_manager)?;
            }
        }
        Ok(())
    }

    pub(crate) fn build_command(
        &self,
        build_manager: &BuildManager<'_>,
    ) -> Result<Command, Errored> {
        let mut cmd = self.config.program.build(&self.config.out_dir);
        cmd.arg(self.status.path());
        if !self.status.revision().is_empty() {
            cmd.arg(format!("--cfg={}", self.status.revision()));
        }
        for r in self.comments() {
            cmd.args(&r.compile_flags);
        }

        self.apply_custom(&mut cmd, build_manager)?;

        if let Some(target) = &self.config.target {
            // Adding a `--target` arg to calls to Cargo will cause target folders
            // to create a target-specific sub-folder. We can avoid that by just
            // not passing a `--target` arg if its the same as the host.
            if !self.config.host_matches_target() {
                cmd.arg("--target").arg(target);
            }
        }

        // False positive in miri, our `map` uses a ref pattern to get the references to the tuple fields instead
        // of a reference to a tuple
        #[allow(clippy::map_identity)]
        cmd.envs(
            self.comments()
                .flat_map(|r| r.env_vars.iter())
                .map(|(k, v)| (k, v)),
        );

        Ok(cmd)
    }

    pub(crate) fn output_path(&self, kind: &str) -> PathBuf {
        let ext = self.extension(kind);
        if self.comments().any(|r| r.stderr_per_bitwidth) {
            return self
                .status
                .path()
                .with_extension(format!("{}bit.{ext}", self.config.get_pointer_width()));
        }
        self.status.path().with_extension(ext)
    }

    pub(crate) fn normalize(&self, text: &[u8], kind: &str) -> Vec<u8> {
        let mut text = text.to_owned();

        for (from, to) in self.comments().flat_map(|r| match kind {
            _ if kind.ends_with("fixed") => &[] as &[_],
            "stderr" => &r.normalize_stderr,
            "stdout" => &r.normalize_stdout,
            _ => unreachable!(),
        }) {
            text = from.replace_all(&text, to).into_owned();
        }
        text
    }

    pub(crate) fn check_test_output(&self, errors: &mut Errors, stdout: &[u8], stderr: &[u8]) {
        // Check output files (if any)
        // Check output files against actual output
        self.check_output(stderr, errors, "stderr");
        self.check_output(stdout, errors, "stdout");
    }

    pub(crate) fn check_output(&self, output: &[u8], errors: &mut Errors, kind: &str) -> PathBuf {
        let output = self.normalize(output, kind);
        let path = self.output_path(kind);
        match &self.config.output_conflict_handling {
            OutputConflictHandling::Error => {
                let expected_output = std::fs::read(&path).unwrap_or_default();
                if output != expected_output {
                    errors.push(Error::OutputDiffers {
                        path: path.clone(),
                        actual: output.clone(),
                        expected: expected_output,
                        bless_command: self.config.bless_command.clone(),
                    });
                }
            }
            OutputConflictHandling::Bless => {
                if output.is_empty() {
                    let _ = std::fs::remove_file(&path);
                } else {
                    std::fs::write(&path, &output).unwrap();
                }
            }
            OutputConflictHandling::Ignore => {}
        }
        path
    }

    /// Read diagnostics from a test's output.
    pub fn process(&self, stderr: &[u8]) -> Diagnostics {
        (self.config.diagnostic_extractor)(self.status.path(), stderr)
    }

    fn check_test_result(&self, command: &Command, output: Output) -> Result<Output, Errored> {
        let mut errors = vec![];
        errors.extend(self.ok(output.status)?);
        // Always remove annotation comments from stderr.
        let diagnostics = self.process(&output.stderr);
        self.check_test_output(&mut errors, &output.stdout, &diagnostics.rendered);
        // Check error annotations in the source against output
        self.check_annotations(
            diagnostics.messages,
            diagnostics.messages_from_unknown_file_or_line,
            &mut errors,
        )?;
        if errors.is_empty() {
            Ok(output)
        } else {
            Err(Errored {
                command: format!("{command:?}"),
                errors,
                stderr: diagnostics.rendered,
                stdout: output.stdout,
            })
        }
    }

    pub(crate) fn check_annotations(
        &self,
        mut messages: Vec<Vec<Message>>,
        mut messages_from_unknown_file_or_line: Vec<Message>,
        errors: &mut Errors,
    ) -> Result<(), Errored> {
        let error_patterns = self.comments().flat_map(|r| r.error_in_other_files.iter());

        let mut seen_error_match = None;
        for error_pattern in error_patterns {
            seen_error_match = Some(error_pattern.span());
            // first check the diagnostics messages outside of our file. We check this first, so that
            // you can mix in-file annotations with //@error-in-other-file annotations, even if there is overlap
            // in the messages.
            if let Some(i) = messages_from_unknown_file_or_line
                .iter()
                .position(|msg| error_pattern.matches(&msg.message))
            {
                messages_from_unknown_file_or_line.remove(i);
            } else {
                errors.push(Error::PatternNotFound {
                    pattern: error_pattern.clone(),
                    expected_line: None,
                });
            }
        }
        let diagnostic_code_prefix = self
            .find_one("diagnostic_code_prefix", |r| {
                r.diagnostic_code_prefix.clone()
            })?
            .into_inner()
            .map(|s| s.content)
            .unwrap_or_default();

        // The order on `Level` is such that `Error` is the highest level.
        // We will ensure that *all* diagnostics of level at least `lowest_annotation_level`
        // are matched.
        let mut lowest_annotation_level = Level::Error;
        'err: for &ErrorMatch { ref kind, line } in
            self.comments().flat_map(|r| r.error_matches.iter())
        {
            match kind {
                ErrorMatchKind::Code(code) => {
                    seen_error_match = Some(code.span());
                }
                &ErrorMatchKind::Pattern { ref pattern, level } => {
                    seen_error_match = Some(pattern.span());
                    // If we found a diagnostic with a level annotation, make sure that all
                    // diagnostics of that level have annotations, even if we don't end up finding a matching diagnostic
                    // for this pattern.
                    if lowest_annotation_level > level {
                        lowest_annotation_level = level;
                    }
                }
            }

            if let Some(msgs) = messages.get_mut(line.get()) {
                match kind {
                    &ErrorMatchKind::Pattern { ref pattern, level } => {
                        let found = msgs
                            .iter()
                            .position(|msg| pattern.matches(&msg.message) && msg.level == level);
                        if let Some(found) = found {
                            msgs.remove(found);
                            continue;
                        }
                    }
                    ErrorMatchKind::Code(code) => {
                        for (i, msg) in msgs.iter().enumerate() {
                            if msg.level != Level::Error {
                                continue;
                            }
                            let Some(msg_code) = &msg.code else { continue };
                            let Some(msg) = msg_code.strip_prefix(&diagnostic_code_prefix) else {
                                continue;
                            };
                            if msg == **code {
                                msgs.remove(i);
                                continue 'err;
                            }
                        }
                    }
                }
            }

            errors.push(match kind {
                ErrorMatchKind::Pattern { pattern, .. } => Error::PatternNotFound {
                    pattern: pattern.clone(),
                    expected_line: Some(line),
                },
                ErrorMatchKind::Code(code) => Error::CodeNotFound {
                    code: Spanned::new(
                        format!("{}{}", diagnostic_code_prefix, **code),
                        code.span(),
                    ),
                    expected_line: Some(line),
                },
            });
        }

        let required_annotation_level = self
            .find_one("`require_annotations_for_level` annotations", |r| {
                r.require_annotations_for_level.clone()
            })?;

        let required_annotation_level = required_annotation_level
            .into_inner()
            .map_or(lowest_annotation_level, |l| *l);
        let filter = |mut msgs: Vec<Message>| -> Vec<_> {
            msgs.retain(|msg| msg.level >= required_annotation_level);
            msgs
        };

        let require_annotations = self.require_annotations();

        if let Some(Spanned { content: true, .. }) = require_annotations {
            let messages_from_unknown_file_or_line = filter(messages_from_unknown_file_or_line);
            if !messages_from_unknown_file_or_line.is_empty() {
                errors.push(Error::ErrorsWithoutPattern {
                    path: None,
                    msgs: messages_from_unknown_file_or_line,
                });
            }

            for (line, msgs) in messages.into_iter().enumerate() {
                let msgs = filter(msgs);
                if !msgs.is_empty() {
                    let line = NonZeroUsize::new(line).expect("line 0 is always empty");
                    errors.push(Error::ErrorsWithoutPattern {
                        path: Some((self.status.path().to_path_buf(), line)),
                        msgs,
                    });
                }
            }
        }

        match (require_annotations, seen_error_match) {
            (
                Some(Spanned {
                    content: false,
                    span: mode,
                }),
                Some(span),
            ) => errors.push(Error::PatternFoundInPassTest { mode, span }),
            (Some(Spanned { content: true, .. }), None) => errors.push(Error::NoPatternsFound),
            _ => {}
        }
        Ok(())
    }

    pub(crate) fn run_test(
        &mut self,
        build_manager: &BuildManager<'_>,
        runs: &mut Vec<TestRun>,
    ) -> TestResult {
        self.patch_out_dir();

        let mut cmd = self.build_command(build_manager)?;
        let stdin = self.status.path().with_extension(self.extension("stdin"));
        if stdin.exists() {
            cmd.stdin(std::fs::File::open(stdin).unwrap());
        }

        let output = crate::core::run_command(&mut cmd)?;

        let output = self.check_test_result(&cmd, output)?;

        for rev in self.comments() {
            for custom in rev.custom.values() {
                for flag in &custom.content {
                    runs.extend(flag.post_test_action(self, &mut cmd, &output, build_manager)?);
                }
            }
        }
        Ok(TestOk::Ok)
    }

    pub(crate) fn find_one_custom(&self, arg: &str) -> Result<OptWithLine<&dyn Flag>, Errored> {
        self.find_one(arg, |r| {
            r.custom
                .get(arg)
                .map(|s| {
                    assert_eq!(s.len(), 1);
                    Spanned::new(&*s[0], s.span())
                })
                .into()
        })
    }
}
