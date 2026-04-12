#![allow(missing_docs)]
#![allow(unused_qualifications)] // for copy/paste sake
#![allow(unreachable_pub)] // for copy/paste sake

use anstyle::AnsiColor;
use anstyle::Effects;
use anstyle::Style;

pub const NOP: Style = Style::new();
pub const HEADER: Style = AnsiColor::BrightGreen.on_default().effects(Effects::BOLD);
pub const USAGE: Style = AnsiColor::BrightGreen.on_default().effects(Effects::BOLD);
pub const LITERAL: Style = AnsiColor::BrightCyan.on_default().effects(Effects::BOLD);
pub const PLACEHOLDER: Style = AnsiColor::Cyan.on_default();
pub const ERROR: Style = annotate_snippets::renderer::DEFAULT_ERROR_STYLE;
pub const WARN: Style = annotate_snippets::renderer::DEFAULT_WARNING_STYLE;
pub const NOTE: Style = annotate_snippets::renderer::DEFAULT_NOTE_STYLE;
pub const GOOD: Style = AnsiColor::BrightGreen.on_default().effects(Effects::BOLD);
pub const VALID: Style = AnsiColor::BrightCyan.on_default().effects(Effects::BOLD);
pub const INVALID: Style = annotate_snippets::renderer::DEFAULT_WARNING_STYLE;
pub const TRANSIENT: Style = annotate_snippets::renderer::DEFAULT_HELP_STYLE;
pub const CONTEXT: Style = annotate_snippets::renderer::DEFAULT_CONTEXT_STYLE;

pub const UPDATE_ADDED: Style = NOTE;
pub const UPDATE_REMOVED: Style = ERROR;
pub const UPDATE_UPGRADED: Style = GOOD;
pub const UPDATE_DOWNGRADED: Style = WARN;
pub const UPDATE_UNCHANGED: Style = anstyle::Style::new().bold();

pub const DEP_NORMAL: Style = anstyle::Style::new().effects(anstyle::Effects::DIMMED);
pub const DEP_BUILD: Style = anstyle::AnsiColor::Blue
    .on_default()
    .effects(anstyle::Effects::BOLD);
pub const DEP_DEV: Style = anstyle::AnsiColor::Cyan
    .on_default()
    .effects(anstyle::Effects::BOLD);
pub const DEP_FEATURE: Style = anstyle::AnsiColor::Magenta
    .on_default()
    .effects(anstyle::Effects::DIMMED);

/// For use with
/// [`clap::Command::styles`](https://docs.rs/clap/latest/clap/struct.Command.html#method.styles)
#[cfg(feature = "clap")]
pub const CLAP_STYLING: clap::builder::styling::Styles = clap::builder::styling::Styles::styled()
    .header(HEADER)
    .usage(USAGE)
    .literal(LITERAL)
    .placeholder(PLACEHOLDER)
    .error(ERROR)
    .valid(VALID)
    .invalid(INVALID);

// Copied from https://github.com/rust-lang/annotate-snippets-rs/blob/5a632cdfadb5902bf063722f80b37fcb50da0416/src/renderer/mod.rs
mod annotate_snippets {
    pub mod renderer {
        #![allow(dead_code)] // for copy/paste sake
        #![allow(rustdoc::broken_intra_doc_links)] // for copy/paste sake
        use anstyle::{AnsiColor, Effects, Style};

        const USE_WINDOWS_COLORS: bool = cfg!(windows) && !cfg!(feature = "testing_colors");
        const BRIGHT_BLUE: Style = if USE_WINDOWS_COLORS {
            AnsiColor::BrightCyan.on_default()
        } else {
            AnsiColor::BrightBlue.on_default()
        };
        /// [`Renderer::error`] applied by [`Renderer::styled`]
        pub const DEFAULT_ERROR_STYLE: Style =
            AnsiColor::BrightRed.on_default().effects(Effects::BOLD);
        /// [`Renderer::warning`] applied by [`Renderer::styled`]
        pub const DEFAULT_WARNING_STYLE: Style = if USE_WINDOWS_COLORS {
            AnsiColor::BrightYellow.on_default()
        } else {
            AnsiColor::Yellow.on_default()
        }
        .effects(Effects::BOLD);
        /// [`Renderer::info`] applied by [`Renderer::styled`]
        pub const DEFAULT_INFO_STYLE: Style = BRIGHT_BLUE.effects(Effects::BOLD);
        /// [`Renderer::note`] applied by [`Renderer::styled`]
        pub const DEFAULT_NOTE_STYLE: Style =
            AnsiColor::BrightGreen.on_default().effects(Effects::BOLD);
        /// [`Renderer::help`] applied by [`Renderer::styled`]
        pub const DEFAULT_HELP_STYLE: Style =
            AnsiColor::BrightCyan.on_default().effects(Effects::BOLD);
        /// [`Renderer::line_num`] applied by [`Renderer::styled`]
        pub const DEFAULT_LINE_NUM_STYLE: Style = BRIGHT_BLUE.effects(Effects::BOLD);
        /// [`Renderer::emphasis`] applied by [`Renderer::styled`]
        pub const DEFAULT_EMPHASIS_STYLE: Style = if USE_WINDOWS_COLORS {
            AnsiColor::BrightWhite.on_default()
        } else {
            Style::new()
        }
        .effects(Effects::BOLD);
        /// [`Renderer::none`] applied by [`Renderer::styled`]
        pub const DEFAULT_NONE_STYLE: Style = Style::new();
        /// [`Renderer::context`] applied by [`Renderer::styled`]
        pub const DEFAULT_CONTEXT_STYLE: Style = BRIGHT_BLUE.effects(Effects::BOLD);
        /// [`Renderer::addition`] applied by [`Renderer::styled`]
        pub const DEFAULT_ADDITION_STYLE: Style = AnsiColor::BrightGreen.on_default();
        /// [`Renderer::removal`] applied by [`Renderer::styled`]
        pub const DEFAULT_REMOVAL_STYLE: Style = AnsiColor::BrightRed.on_default();
    }
}
