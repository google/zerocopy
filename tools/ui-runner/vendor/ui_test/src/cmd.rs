use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

use crate::display;

#[derive(Debug, Clone)]
/// A command, its args and its environment. Used for
/// the main command, the dependency builder and the cfg-reader.
pub struct CommandBuilder {
    /// Path to the binary.
    pub program: PathBuf,
    /// Arguments to the binary.
    pub args: Vec<OsString>,
    /// A flag to prefix before the path to where output files should be written.
    pub out_dir_flag: Option<OsString>,
    /// A flag to set as the last flag in the command, so the `build` caller can
    /// append the filename themselves.
    pub input_file_flag: Option<OsString>,
    /// Environment variables passed to the binary that is executed.
    /// The environment variable is removed if the second tuple field is `None`
    pub envs: Vec<(OsString, Option<OsString>)>,
    /// A flag to add in order to make the command print the cfgs it supports
    pub cfg_flag: Option<OsString>,
}

impl CommandBuilder {
    /// Uses the `CARGO` env var or just a program named `cargo` and the argument `build`.
    pub fn cargo() -> Self {
        Self {
            program: PathBuf::from(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into())),
            args: vec![
                "build".into(),
                "--color=never".into(),
                "--quiet".into(),
                "--jobs".into(),
                "1".into(),
            ],
            out_dir_flag: Some("--target-dir".into()),
            input_file_flag: Some("--manifest-path".into()),
            envs: vec![],
            cfg_flag: None,
        }
    }

    /// Uses the `RUSTC` env var or just a program named `rustc` and the argument `--error-format=json`.
    ///
    /// Take care to only append unless you actually meant to overwrite the defaults.
    /// Overwriting the defaults may make `//~ ERROR` style comments stop working.
    pub fn rustc() -> Self {
        Self {
            program: PathBuf::from(std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into())),
            args: vec!["--error-format=json".into()],
            out_dir_flag: Some("--out-dir".into()),
            input_file_flag: None,
            envs: vec![],
            cfg_flag: Some("--print=cfg".into()),
        }
    }

    /// Build a `CommandBuilder` for a command without any argumemnts.
    /// You can still add arguments later.
    pub fn cmd(cmd: impl Into<PathBuf>) -> Self {
        Self {
            program: cmd.into(),
            args: vec![],
            out_dir_flag: None,
            input_file_flag: None,
            envs: vec![],
            cfg_flag: None,
        }
    }

    /// Render the command like you'd use it on a command line.
    pub fn display(&self) -> impl std::fmt::Display + '_ {
        struct Display<'a>(&'a CommandBuilder);
        impl std::fmt::Display for Display<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                for (var, val) in &self.0.envs {
                    if let Some(val) = val {
                        write!(f, "{var:?}={val:?} ")?;
                    }
                }
                display(&self.0.program).fmt(f)?;
                for arg in &self.0.args {
                    write!(f, " {arg:?}")?;
                }
                if let Some(flag) = &self.0.out_dir_flag {
                    write!(f, " {flag:?} OUT_DIR")?;
                }
                if let Some(flag) = &self.0.input_file_flag {
                    write!(f, " {flag:?}")?;
                }
                Ok(())
            }
        }
        Display(self)
    }

    /// Create a command with the given settings.
    pub fn build(&self, out_dir: &Path) -> Command {
        let mut cmd = Command::new(&self.program);
        cmd.args(self.args.iter());
        if let Some(flag) = &self.out_dir_flag {
            cmd.arg(flag).arg(out_dir);
        }
        if let Some(flag) = &self.input_file_flag {
            cmd.arg(flag);
        }
        self.apply_env(&mut cmd);
        cmd
    }

    pub(crate) fn apply_env(&self, cmd: &mut Command) {
        for (var, val) in self.envs.iter() {
            if let Some(val) = val {
                cmd.env(var, val);
            } else {
                cmd.env_remove(var);
            }
        }
    }
}
