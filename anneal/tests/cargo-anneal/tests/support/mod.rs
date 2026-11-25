// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Thin compatibility shim forwarding `installed_smoke` to
//! [`anneal_testkit::case_runner`] (`process_group(0)` + subreaper teardown).

#![allow(dead_code)]

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    time::Duration,
};

pub use anneal_testkit::{ProcessOutcome, TestResult, select_cases, write_json};

#[derive(Clone, Debug)]
pub struct Invocation {
    pub executable: PathBuf,
    pub arguments: Vec<String>,
    pub environment: BTreeMap<String, String>,
}

impl Invocation {
    pub fn new(executable: impl Into<PathBuf>, arguments: &[&str]) -> Self {
        Self {
            executable: executable.into(),
            arguments: arguments.iter().map(|arg| (*arg).to_string()).collect(),
            environment: BTreeMap::new(),
        }
    }

    fn to_testkit(&self) -> anneal_testkit::Invocation {
        let mut inv = anneal_testkit::Invocation::with_os_args(&self.executable, &self.arguments);
        for (k, v) in &self.environment {
            inv.environment.insert(k.into(), v.into());
        }
        inv
    }
}

pub struct RunDirectory(anneal_testkit::RunDirectory);

impl RunDirectory {
    pub fn new(revision: &str, timeout: Duration) -> TestResult<Self> {
        anneal_testkit::RunDirectory::new(revision, timeout).map(Self)
    }

    pub fn path(&self) -> &Path {
        self.0.path()
    }

    pub fn case(&self, name: &str) -> TestResult<CaseDirectory<'_>> {
        self.0.case(name).map(CaseDirectory)
    }

    pub fn run_cases(
        &self,
        cases: &[&str],
        jobs: usize,
        body: impl Fn(&str, &mut CaseDirectory<'_>) -> TestResult + Sync,
    ) -> TestResult {
        self.0.run_cases_owned(cases, jobs, |name, case| {
            let mut wrapped = CaseDirectory(case);
            body(name, &mut wrapped)
        })
    }

    pub fn finish(self, result: TestResult, diagnostics: Option<&Path>) -> TestResult {
        self.0.finish(result, diagnostics)
    }
}

pub struct CaseDirectory<'run>(anneal_testkit::CaseDirectory<'run>);

impl CaseDirectory<'_> {
    pub fn path(&self) -> &Path {
        self.0.path()
    }

    pub fn write(&self, relative: impl AsRef<Path>, bytes: &[u8]) -> TestResult {
        self.0.write(relative, bytes)
    }

    pub fn copy(&self, source: &Path, relative: impl AsRef<Path>) -> TestResult {
        self.0.copy(source, relative)
    }

    pub fn run(&mut self, invocation: &Invocation) -> TestResult<ProcessOutcome> {
        self.0.run(&invocation.to_testkit())
    }

    pub fn run_shared(&self, invocation: &Invocation) -> TestResult<ProcessOutcome> {
        self.0.run_shared(&invocation.to_testkit())
    }
}
