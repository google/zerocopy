//! A couple of functions to enable and disable coloring.

use std::default::Default;
use std::env;
use std::io::{self, IsTerminal};
use std::sync::atomic::{AtomicBool, Ordering};

/// Sets a flag to the console to use a virtual terminal environment.
///
/// This is primarily used for Windows 10 environments which will not correctly colorize
/// the outputs based on ANSI escape codes.
///
/// The returned `Result` is _always_ `Ok(())`, the return type was kept to ensure backwards
/// compatibility.
///
/// # Notes
/// > Only available to `Windows` build targets.
///
/// # Example
/// ```rust
/// use colored::*;
/// control::set_virtual_terminal(false).unwrap();
/// println!("{}", "bright cyan".bright_cyan());    // will print '[96mbright cyan[0m' on windows 10
///
/// control::set_virtual_terminal(true).unwrap();
/// println!("{}", "bright cyan".bright_cyan());    // will print correctly
/// ```
#[allow(clippy::result_unit_err)]
#[cfg(windows)]
pub fn set_virtual_terminal(use_virtual: bool) -> Result<(), ()> {
    use windows_sys::Win32::System::Console::{
        GetConsoleMode, GetStdHandle, SetConsoleMode, ENABLE_VIRTUAL_TERMINAL_PROCESSING,
        STD_OUTPUT_HANDLE,
    };

    unsafe {
        let handle = GetStdHandle(STD_OUTPUT_HANDLE);
        let mut original_mode = 0;
        GetConsoleMode(handle, &mut original_mode);

        let enabled = original_mode & ENABLE_VIRTUAL_TERMINAL_PROCESSING
            == ENABLE_VIRTUAL_TERMINAL_PROCESSING;

        match (use_virtual, enabled) {
            // not enabled, should be enabled
            (true, false) => {
                SetConsoleMode(handle, ENABLE_VIRTUAL_TERMINAL_PROCESSING | original_mode)
            }
            // already enabled, should be disabled
            (false, true) => {
                SetConsoleMode(handle, ENABLE_VIRTUAL_TERMINAL_PROCESSING ^ original_mode)
            }
            _ => 0,
        };
    }

    Ok(())
}

/// A flag for whether coloring should occur.
pub struct ShouldColorize {
    clicolor: bool,
    clicolor_force: Option<bool>,
    // XXX we can't use Option<Atomic> because we can't use &mut references to ShouldColorize
    has_manual_override: AtomicBool,
    manual_override: AtomicBool,
}

/// Use this to force colored to ignore the environment and always/never colorize
/// See example/control.rs
pub fn set_override(override_colorize: bool) {
    SHOULD_COLORIZE.set_override(override_colorize);
}

/// Remove the manual override and let the environment decide if it's ok to colorize
/// See example/control.rs
pub fn unset_override() {
    SHOULD_COLORIZE.unset_override();
}

lazy_static! {
/// The persistent [`ShouldColorize`].
    pub static ref SHOULD_COLORIZE: ShouldColorize = ShouldColorize::from_env();
}

impl Default for ShouldColorize {
    fn default() -> ShouldColorize {
        ShouldColorize {
            clicolor: true,
            clicolor_force: None,
            has_manual_override: AtomicBool::new(false),
            manual_override: AtomicBool::new(false),
        }
    }
}

impl ShouldColorize {
    /// Reads environment variables and checks if output is a tty to determine
    /// whether colorization should be used or not.
    /// `CLICOLOR_FORCE` takes highest priority, followed by `NO_COLOR`,
    /// followed by `CLICOLOR` combined with tty check.
    pub fn from_env() -> Self {
        ShouldColorize {
            clicolor: ShouldColorize::normalize_env(env::var("CLICOLOR")).unwrap_or(true)
                && io::stdout().is_terminal(),
            clicolor_force: ShouldColorize::resolve_clicolor_force(
                env::var("NO_COLOR"),
                env::var("CLICOLOR_FORCE"),
            ),
            ..ShouldColorize::default()
        }
    }

    /// Returns if the current coloring is expected.
    pub fn should_colorize(&self) -> bool {
        if self.has_manual_override.load(Ordering::Relaxed) {
            return self.manual_override.load(Ordering::Relaxed);
        }

        if let Some(forced_value) = self.clicolor_force {
            return forced_value;
        }

        self.clicolor
    }

    /// Use this to force colored to ignore the environment and always/never colorize
    pub fn set_override(&self, override_colorize: bool) {
        self.has_manual_override.store(true, Ordering::Relaxed);
        self.manual_override
            .store(override_colorize, Ordering::Relaxed);
    }

    /// Remove the manual override and let the environment decide if it's ok to colorize
    pub fn unset_override(&self) {
        self.has_manual_override.store(false, Ordering::Relaxed);
    }

    /* private */

    fn normalize_env(env_res: Result<String, env::VarError>) -> Option<bool> {
        match env_res {
            Ok(string) => Some(string != "0"),
            Err(_) => None,
        }
    }

    fn resolve_clicolor_force(
        no_color: Result<String, env::VarError>,
        clicolor_force: Result<String, env::VarError>,
    ) -> Option<bool> {
        if ShouldColorize::normalize_env(clicolor_force) == Some(true) {
            Some(true)
        } else if ShouldColorize::normalize_env(no_color).is_some() {
            Some(false)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod specs {
    use super::*;
    use rspec;
    use std::env;

    #[test]
    fn clicolor_behavior() {
        rspec::run(&rspec::describe("ShouldColorize", (), |ctx| {
            ctx.specify("::normalize_env", |ctx| {
                ctx.it("should return None if error", |_| {
                    assert_eq!(
                        None,
                        ShouldColorize::normalize_env(Err(env::VarError::NotPresent))
                    );
                    assert_eq!(
                        None,
                        ShouldColorize::normalize_env(Err(env::VarError::NotUnicode("".into())))
                    );
                });

                ctx.it("should return Some(true) if != 0", |_| {
                    Some(true) == ShouldColorize::normalize_env(Ok(String::from("1")))
                });

                ctx.it("should return Some(false) if == 0", |_| {
                    Some(false) == ShouldColorize::normalize_env(Ok(String::from("0")))
                });
            });

            ctx.specify("::resolve_clicolor_force", |ctx| {
                ctx.it(
                    "should return None if NO_COLOR is not set and CLICOLOR_FORCE is not set or set to 0",
                    |_| {
                        assert_eq!(
                            None,
                            ShouldColorize::resolve_clicolor_force(
                                Err(env::VarError::NotPresent),
                                Err(env::VarError::NotPresent)
                            )
                        );
                        assert_eq!(
                            None,
                            ShouldColorize::resolve_clicolor_force(
                                Err(env::VarError::NotPresent),
                                Ok(String::from("0")),
                            )
                        );
                    },
                );

                ctx.it(
                    "should return Some(false) if NO_COLOR is set and CLICOLOR_FORCE is not enabled",
                    |_| {
                        assert_eq!(
                            Some(false),
                            ShouldColorize::resolve_clicolor_force(
                                Ok(String::from("0")),
                                Err(env::VarError::NotPresent)
                            )
                        );
                        assert_eq!(
                            Some(false),
                            ShouldColorize::resolve_clicolor_force(
                                Ok(String::from("1")),
                                Err(env::VarError::NotPresent)
                            )
                        );
                        assert_eq!(
                            Some(false),
                            ShouldColorize::resolve_clicolor_force(
                                Ok(String::from("1")),
                                Ok(String::from("0")),
                            )
                        );
                    },
                );

                ctx.it(
                    "should prioritize CLICOLOR_FORCE over NO_COLOR if CLICOLOR_FORCE is set to non-zero value",
                    |_| {
                        assert_eq!(
                            Some(true),
                            ShouldColorize::resolve_clicolor_force(
                                Ok(String::from("1")),
                                Ok(String::from("1")),
                            )
                        );
                        assert_eq!(
                            Some(false),
                            ShouldColorize::resolve_clicolor_force(
                                Ok(String::from("1")),
                                Ok(String::from("0")),
                            )
                        );
                        assert_eq!(
                            Some(true),
                            ShouldColorize::resolve_clicolor_force(
                                Err(env::VarError::NotPresent),
                                Ok(String::from("1")),
                            )
                        );
                    },
                );
            });

            ctx.specify("constructors", |ctx| {
                ctx.it("should have a default constructor", |_| {
                    ShouldColorize::default();
                });

                ctx.it("should have an environment constructor", |_| {
                    ShouldColorize::from_env();
                });
            });

            ctx.specify("when only changing clicolors", |ctx| {
                ctx.it("clicolor == false means no colors", |_| {
                    let colorize_control = ShouldColorize {
                        clicolor: false,
                        ..ShouldColorize::default()
                    };
                    !colorize_control.should_colorize()
                });

                ctx.it("clicolor == true means colors !", |_| {
                    let colorize_control = ShouldColorize {
                        clicolor: true,
                        ..ShouldColorize::default()
                    };
                    colorize_control.should_colorize()
                });

                ctx.it("unset clicolors implies true", |_| {
                    ShouldColorize::default().should_colorize()
                });
            });

            ctx.specify("when using clicolor_force", |ctx| {
                ctx.it(
                    "clicolor_force should force to true no matter clicolor",
                    |_| {
                        let colorize_control = ShouldColorize {
                            clicolor: false,
                            clicolor_force: Some(true),
                            ..ShouldColorize::default()
                        };

                        colorize_control.should_colorize()
                    },
                );

                ctx.it(
                    "clicolor_force should force to false no matter clicolor",
                    |_| {
                        let colorize_control = ShouldColorize {
                            clicolor: true,
                            clicolor_force: Some(false),
                            ..ShouldColorize::default()
                        };

                        !colorize_control.should_colorize()
                    },
                );
            });

            ctx.specify("using a manual override", |ctx| {
                ctx.it("shoud colorize if manual_override is true, but clicolor is false and clicolor_force also false", |_| {
                    let colorize_control = ShouldColorize {
                        clicolor: false,
                        clicolor_force: None,
                        has_manual_override: AtomicBool::new(true),
                        manual_override: AtomicBool::new(true),
                    };

                    colorize_control.should_colorize();
                });

                ctx.it("should not colorize if manual_override is false, but clicolor is true or clicolor_force is true", |_| {
                    let colorize_control = ShouldColorize {
                        clicolor: true,
                        clicolor_force: Some(true),
                        has_manual_override: AtomicBool::new(true),
                        manual_override: AtomicBool::new(false),
                    };

                    !colorize_control.should_colorize()
                });
            });

            ctx.specify("::set_override", |ctx| {
                ctx.it("should exists", |_| {
                    let colorize_control = ShouldColorize::default();
                    colorize_control.set_override(true);
                });

                ctx.it("set the manual_override property", |_| {
                    let colorize_control = ShouldColorize::default();
                    colorize_control.set_override(true);
                    {
                        assert!(colorize_control.has_manual_override.load(Ordering::Relaxed));
                        let val = colorize_control.manual_override.load(Ordering::Relaxed);
                        assert!(val);
                    }
                    colorize_control.set_override(false);
                    {
                        assert!(colorize_control.has_manual_override.load(Ordering::Relaxed));
                        let val = colorize_control.manual_override.load(Ordering::Relaxed);
                        assert!(!val);
                    }
                });
            });

            ctx.specify("::unset_override", |ctx| {
                ctx.it("should exists", |_| {
                    let colorize_control = ShouldColorize::default();
                    colorize_control.unset_override();
                });

                ctx.it("unset the manual_override property", |_| {
                    let colorize_control = ShouldColorize::default();
                    colorize_control.set_override(true);
                    colorize_control.unset_override();
                    assert!(!colorize_control.has_manual_override.load(Ordering::Relaxed));
                });
            });
        }));
    }
}
