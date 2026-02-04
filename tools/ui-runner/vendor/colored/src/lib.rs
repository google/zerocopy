//!Coloring terminal so simple, you already know how to do it !
//!
//!    use colored::Colorize;
//!
//!    "this is blue".blue();
//!    "this is red".red();
//!    "this is red on blue".red().on_blue();
//!    "this is also red on blue".on_blue().red();
//!    "you can use truecolor values too!".truecolor(0, 255, 136);
//!    "background truecolor also works :)".on_truecolor(135, 28, 167);
//!    "you can also make bold comments".bold();
//!    println!("{} {} {}", "or use".cyan(), "any".italic().yellow(), "string type".cyan());
//!    "or change advice. This is red".yellow().blue().red();
//!    "or clear things up. This is default color and style".red().bold().clear();
//!    "purple and magenta are the same".purple().magenta();
//!    "bright colors are also allowed".bright_blue().on_bright_white();
//!    "you can specify color by string".color("blue").on_color("red");
//!    "and so are normal and clear".normal().clear();
//!    String::from("this also works!").green().bold();
//!    format!("{:30}", "format works as expected. This will be padded".blue());
//!    format!("{:.3}", "and this will be green but truncated to 3 chars".green());
//!
//!
//! See [the `Colorize` trait](./trait.Colorize.html) for all the methods.
//!
//! Note: The methods of [`Colorize`], when used on [`str`]'s, return
//! [`ColoredString`]'s. See [`ColoredString`] to learn more about them and
//! what you can do with them beyond continue to use [`Colorize`] to further
//! modify them.
#![warn(missing_docs)]

#[macro_use]
extern crate lazy_static;

#[cfg(test)]
extern crate rspec;

mod color;
pub mod control;
mod error;
mod style;

pub use self::customcolors::CustomColor;

/// Custom colors support.
pub mod customcolors;

pub use color::*;

use std::{
    borrow::Cow,
    error::Error,
    fmt,
    ops::{Deref, DerefMut},
};

pub use style::{Style, Styles};

/// A string that may have color and/or style applied to it.
///
/// Commonly created via calling the methods of [`Colorize`] on a &str.
/// All methods of [`Colorize`] either create a new `ColoredString` from
/// the type called on or modify a callee `ColoredString`. See
/// [`Colorize`] for more.
///
/// The primary usage of `ColoredString`'s is as a way to take text,
/// apply colors and miscillaneous styling to it (such as bold or
/// underline), and then use it to create formatted strings that print
/// to the console with the special styling applied.
///
/// ## Usage
///
/// As stated, `ColoredString`'s, once created, can be printed to the
/// console with their colors and style or turned into a string
/// containing special console codes that has the same effect.
/// This is made easy via `ColoredString`'s implementations of
/// [`Display`](std::fmt::Display) and [`ToString`] for those purposes
/// respectively.
///
/// Printing a `ColoredString` with its style is as easy as:
///
/// ```
/// # use colored::*;
/// let cstring: ColoredString = "Bold and Red!".bold().red();
/// println!("{}", cstring);
/// ```
///
/// ## Manipulating the coloring/style of a `ColoredString`
///
/// Getting or changing the foreground color, background color, and or
/// style of a `ColoredString` is as easy as manually reading / modifying
/// the fields of `ColoredString`.
///
/// ```
/// # use colored::*;
/// let mut red_text = "Red".red();
/// // Changing color using re-assignment and [`Colorize`]:
/// red_text = red_text.blue();
/// // Manipulating fields of `ColoredString` in-place:
/// red_text.fgcolor = Some(Color::Blue);
///
/// let styled_text1 = "Bold".bold();
/// let styled_text2 = "Italic".italic();
/// let mut styled_text3 = ColoredString::from("Bold and Italic");
/// styled_text3.style = styled_text1.style | styled_text2.style;
/// ```
///
/// ## Modifying the text of a `ColoredString`
///
/// Modifying the text is as easy as modifying the `input` field of
/// `ColoredString`...
///
/// ```
/// # use colored::*;
/// let mut colored_text = "Magenta".magenta();
/// colored_text = colored_text.blue();
/// colored_text.input = "Blue".to_string();
/// // Note: The above is inefficient and `colored_text.input.replace_range(.., "Blue")` would
/// // be more proper. This is just for example.
///
/// assert_eq!(&*colored_text, "Blue");
/// ```
///
/// Notice how this process preserves the coloring and style.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ColoredString {
    /// The plain text that will have color and style applied to it.
    pub input: String,
    /// The color of the text as it will be printed.
    pub fgcolor: Option<Color>,
    /// The background color (if any). None means that the text will be printed
    /// without a special background.
    pub bgcolor: Option<Color>,
    /// Any special styling to be applied to the text (see Styles for a list of
    /// available options).
    pub style: style::Style,
}

/// The trait that enables something to be given color.
///
/// You can use `colored` effectively simply by importing this trait
/// and then using its methods on `String` and `&str`.
#[allow(missing_docs)]
pub trait Colorize {
    // Font Colors
    fn black(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Black)
    }
    fn red(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Red)
    }
    fn green(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Green)
    }
    fn yellow(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Yellow)
    }
    fn blue(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Blue)
    }
    fn magenta(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Magenta)
    }
    fn purple(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Magenta)
    }
    fn cyan(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::Cyan)
    }
    fn white(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::White)
    }
    fn bright_black(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightBlack)
    }
    fn bright_red(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightRed)
    }
    fn bright_green(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightGreen)
    }
    fn bright_yellow(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightYellow)
    }
    fn bright_blue(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightBlue)
    }
    fn bright_magenta(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightMagenta)
    }
    fn bright_purple(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightMagenta)
    }
    fn bright_cyan(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightCyan)
    }
    fn bright_white(self) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::BrightWhite)
    }
    fn truecolor(self, r: u8, g: u8, b: u8) -> ColoredString
    where
        Self: Sized,
    {
        self.color(Color::TrueColor { r, g, b })
    }
    fn custom_color<T>(self, color: T) -> ColoredString
    where
        Self: Sized,
        T: Into<CustomColor>,
    {
        let color = color.into();

        self.color(Color::TrueColor {
            r: color.r,
            g: color.g,
            b: color.b,
        })
    }
    fn color<S: Into<Color>>(self, color: S) -> ColoredString;
    // Background Colors
    fn on_black(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Black)
    }
    fn on_red(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Red)
    }
    fn on_green(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Green)
    }
    fn on_yellow(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Yellow)
    }
    fn on_blue(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Blue)
    }
    fn on_magenta(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Magenta)
    }
    fn on_purple(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Magenta)
    }
    fn on_cyan(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::Cyan)
    }
    fn on_white(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::White)
    }
    fn on_bright_black(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightBlack)
    }
    fn on_bright_red(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightRed)
    }
    fn on_bright_green(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightGreen)
    }
    fn on_bright_yellow(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightYellow)
    }
    fn on_bright_blue(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightBlue)
    }
    fn on_bright_magenta(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightMagenta)
    }
    fn on_bright_purple(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightMagenta)
    }
    fn on_bright_cyan(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightCyan)
    }
    fn on_bright_white(self) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::BrightWhite)
    }
    fn on_truecolor(self, r: u8, g: u8, b: u8) -> ColoredString
    where
        Self: Sized,
    {
        self.on_color(Color::TrueColor { r, g, b })
    }
    fn on_custom_color<T>(self, color: T) -> ColoredString
    where
        Self: Sized,
        T: Into<CustomColor>,
    {
        let color = color.into();

        self.on_color(Color::TrueColor {
            r: color.r,
            g: color.g,
            b: color.b,
        })
    }
    fn on_color<S: Into<Color>>(self, color: S) -> ColoredString;
    // Styles
    fn clear(self) -> ColoredString;
    fn normal(self) -> ColoredString;
    fn bold(self) -> ColoredString;
    fn dimmed(self) -> ColoredString;
    fn italic(self) -> ColoredString;
    fn underline(self) -> ColoredString;
    fn blink(self) -> ColoredString;
    #[deprecated(since = "1.5.2", note = "Users should use reversed instead")]
    fn reverse(self) -> ColoredString;
    fn reversed(self) -> ColoredString;
    fn hidden(self) -> ColoredString;
    fn strikethrough(self) -> ColoredString;
}

impl ColoredString {
    /// Get the current background color applied.
    ///
    /// ```rust
    /// # use colored::*;
    /// let cstr = "".blue();
    /// assert_eq!(cstr.fgcolor(), Some(Color::Blue));
    /// let cstr = cstr.clear();
    /// assert_eq!(cstr.fgcolor(), None);
    /// ```
    #[deprecated(note = "Deprecated due to the exposing of the fgcolor struct field.")]
    pub fn fgcolor(&self) -> Option<Color> {
        self.fgcolor.as_ref().copied()
    }

    /// Get the current background color applied.
    ///
    /// ```rust
    /// # use colored::*;
    /// let cstr = "".on_blue();
    /// assert_eq!(cstr.bgcolor(), Some(Color::Blue));
    /// let cstr = cstr.clear();
    /// assert_eq!(cstr.bgcolor(), None);
    /// ```
    #[deprecated(note = "Deprecated due to the exposing of the bgcolor struct field.")]
    pub fn bgcolor(&self) -> Option<Color> {
        self.bgcolor.as_ref().copied()
    }

    /// Get the current [`Style`] which can be check if it contains a [`Styles`].
    ///
    /// ```rust
    /// # use colored::*;
    /// let colored = "".bold().italic();
    /// assert_eq!(colored.style().contains(Styles::Bold), true);
    /// assert_eq!(colored.style().contains(Styles::Italic), true);
    /// assert_eq!(colored.style().contains(Styles::Dimmed), false);
    /// ```
    #[deprecated(note = "Deprecated due to the exposing of the style struct field.")]
    pub fn style(&self) -> style::Style {
        self.style
    }

    /// Clears foreground coloring on this `ColoredString`, meaning that it
    /// will be printed with the default terminal text color.
    pub fn clear_fgcolor(&mut self) {
        self.fgcolor = None;
    }

    /// Gets rid of this `ColoredString`'s background.
    pub fn clear_bgcolor(&mut self) {
        self.bgcolor = None;
    }

    /// Clears any special styling and sets it back to the default (plain,
    /// maybe colored, text).
    pub fn clear_style(&mut self) {
        self.style = Style::default();
    }

    /// Checks if the colored string has no color or styling.
    ///
    /// ```rust
    /// # use colored::*;
    /// let cstr = "".red();
    /// assert_eq!(cstr.is_plain(), false);
    /// let cstr = cstr.clear();
    /// assert_eq!(cstr.is_plain(), true);
    /// ```
    pub fn is_plain(&self) -> bool {
        self.bgcolor.is_none() && self.fgcolor.is_none() && self.style == style::CLEAR
    }

    #[cfg(not(feature = "no-color"))]
    fn has_colors() -> bool {
        control::SHOULD_COLORIZE.should_colorize()
    }

    #[cfg(feature = "no-color")]
    fn has_colors() -> bool {
        false
    }

    fn compute_style(&self) -> String {
        if !ColoredString::has_colors() || self.is_plain() {
            return String::new();
        }

        let mut res = String::from("\x1B[");
        let mut has_wrote = if self.style != style::CLEAR {
            res.push_str(&self.style.to_str());
            true
        } else {
            false
        };

        if let Some(ref bgcolor) = self.bgcolor {
            if has_wrote {
                res.push(';');
            }

            res.push_str(&bgcolor.to_bg_str());
            has_wrote = true;
        }

        if let Some(ref fgcolor) = self.fgcolor {
            if has_wrote {
                res.push(';');
            }

            res.push_str(&fgcolor.to_fg_str());
        }

        res.push('m');
        res
    }

    fn escape_inner_reset_sequences(&self) -> Cow<str> {
        if !ColoredString::has_colors() || self.is_plain() {
            return self.input.as_str().into();
        }

        // TODO: BoyScoutRule
        let reset = "\x1B[0m";
        let style = self.compute_style();
        let matches: Vec<usize> = self
            .input
            .match_indices(reset)
            .map(|(idx, _)| idx)
            .collect();
        if matches.is_empty() {
            return self.input.as_str().into();
        }

        let mut input = self.input.clone();
        input.reserve(matches.len() * style.len());

        for (idx_in_matches, offset) in matches.into_iter().enumerate() {
            // shift the offset to the end of the reset sequence and take in account
            // the number of matches we have escaped (which shift the index to insert)
            let mut offset = offset + reset.len() + idx_in_matches * style.len();

            for cchar in style.chars() {
                input.insert(offset, cchar);
                offset += 1;
            }
        }

        input.into()
    }
}

impl Deref for ColoredString {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.input
    }
}

impl DerefMut for ColoredString {
    fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
        &mut self.input
    }
}

impl From<String> for ColoredString {
    fn from(s: String) -> Self {
        ColoredString {
            input: s,
            ..ColoredString::default()
        }
    }
}

impl<'a> From<&'a str> for ColoredString {
    fn from(s: &'a str) -> Self {
        ColoredString {
            input: String::from(s),
            ..ColoredString::default()
        }
    }
}

impl Colorize for ColoredString {
    fn color<S: Into<Color>>(mut self, color: S) -> ColoredString {
        self.fgcolor = Some(color.into());
        self
    }
    fn on_color<S: Into<Color>>(mut self, color: S) -> ColoredString {
        self.bgcolor = Some(color.into());
        self
    }

    fn clear(self) -> ColoredString {
        ColoredString {
            input: self.input,
            ..ColoredString::default()
        }
    }
    fn normal(self) -> ColoredString {
        self.clear()
    }
    fn bold(mut self) -> ColoredString {
        self.style.add(style::Styles::Bold);
        self
    }
    fn dimmed(mut self) -> ColoredString {
        self.style.add(style::Styles::Dimmed);
        self
    }
    fn italic(mut self) -> ColoredString {
        self.style.add(style::Styles::Italic);
        self
    }
    fn underline(mut self) -> ColoredString {
        self.style.add(style::Styles::Underline);
        self
    }
    fn blink(mut self) -> ColoredString {
        self.style.add(style::Styles::Blink);
        self
    }
    fn reverse(self) -> ColoredString {
        self.reversed()
    }
    fn reversed(mut self) -> ColoredString {
        self.style.add(style::Styles::Reversed);
        self
    }
    fn hidden(mut self) -> ColoredString {
        self.style.add(style::Styles::Hidden);
        self
    }
    fn strikethrough(mut self) -> ColoredString {
        self.style.add(style::Styles::Strikethrough);
        self
    }
}

impl Colorize for &str {
    fn color<S: Into<Color>>(self, color: S) -> ColoredString {
        ColoredString {
            fgcolor: Some(color.into()),
            input: String::from(self),
            ..ColoredString::default()
        }
    }

    fn on_color<S: Into<Color>>(self, color: S) -> ColoredString {
        ColoredString {
            bgcolor: Some(color.into()),
            input: String::from(self),
            ..ColoredString::default()
        }
    }

    fn clear(self) -> ColoredString {
        ColoredString {
            input: String::from(self),
            style: style::CLEAR,
            ..ColoredString::default()
        }
    }
    fn normal(self) -> ColoredString {
        self.clear()
    }
    fn bold(self) -> ColoredString {
        ColoredString::from(self).bold()
    }
    fn dimmed(self) -> ColoredString {
        ColoredString::from(self).dimmed()
    }
    fn italic(self) -> ColoredString {
        ColoredString::from(self).italic()
    }
    fn underline(self) -> ColoredString {
        ColoredString::from(self).underline()
    }
    fn blink(self) -> ColoredString {
        ColoredString::from(self).blink()
    }
    fn reverse(self) -> ColoredString {
        self.reversed()
    }
    fn reversed(self) -> ColoredString {
        ColoredString::from(self).reversed()
    }
    fn hidden(self) -> ColoredString {
        ColoredString::from(self).hidden()
    }
    fn strikethrough(self) -> ColoredString {
        ColoredString::from(self).strikethrough()
    }
}

impl fmt::Display for ColoredString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !ColoredString::has_colors() || self.is_plain() {
            return <String as fmt::Display>::fmt(&self.input, f);
        }

        // XXX: see tests. Useful when nesting colored strings
        let escaped_input = self.escape_inner_reset_sequences();

        f.write_str(&self.compute_style())?;
        escaped_input.fmt(f)?;
        f.write_str("\x1B[0m")?;
        Ok(())
    }
}

impl From<ColoredString> for Box<dyn Error> {
    fn from(cs: ColoredString) -> Box<dyn Error> {
        Box::from(error::ColoredStringError(cs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{error::Error, fmt::Write};

    #[test]
    fn formatting() {
        // respect the formatting. Escape sequence add some padding so >= 40
        assert!(format!("{:40}", "".blue()).len() >= 40);
        // both should be truncated to 1 char before coloring
        assert_eq!(
            format!("{:1.1}", "toto".blue()).len(),
            format!("{:1.1}", "1".blue()).len()
        )
    }

    #[test]
    fn it_works() -> Result<(), Box<dyn Error>> {
        let mut buf = String::new();
        let toto = "toto";
        writeln!(&mut buf, "{}", toto.red())?;
        writeln!(&mut buf, "{}", String::from(toto).red())?;
        writeln!(&mut buf, "{}", toto.blue())?;

        writeln!(&mut buf, "blue style ****")?;
        writeln!(&mut buf, "{}", toto.bold())?;
        writeln!(&mut buf, "{}", "yeah ! Red bold !".red().bold())?;
        writeln!(&mut buf, "{}", "yeah ! Yellow bold !".bold().yellow())?;
        writeln!(&mut buf, "{}", toto.bold().blue())?;
        writeln!(&mut buf, "{}", toto.blue().bold())?;
        writeln!(&mut buf, "{}", toto.blue().bold().underline())?;
        writeln!(&mut buf, "{}", toto.blue().italic())?;
        writeln!(&mut buf, "******")?;
        writeln!(&mut buf, "test clearing")?;
        writeln!(&mut buf, "{}", "red cleared".red().clear())?;
        writeln!(&mut buf, "{}", "bold cyan cleared".bold().cyan().clear())?;
        writeln!(&mut buf, "******")?;
        writeln!(&mut buf, "Bg tests")?;
        writeln!(&mut buf, "{}", toto.green().on_blue())?;
        writeln!(&mut buf, "{}", toto.on_magenta().yellow())?;
        writeln!(&mut buf, "{}", toto.purple().on_yellow())?;
        writeln!(&mut buf, "{}", toto.magenta().on_white())?;
        writeln!(&mut buf, "{}", toto.cyan().on_green())?;
        writeln!(&mut buf, "{}", toto.black().on_white())?;
        writeln!(&mut buf, "******")?;
        writeln!(&mut buf, "{}", toto.green())?;
        writeln!(&mut buf, "{}", toto.yellow())?;
        writeln!(&mut buf, "{}", toto.purple())?;
        writeln!(&mut buf, "{}", toto.magenta())?;
        writeln!(&mut buf, "{}", toto.cyan())?;
        writeln!(&mut buf, "{}", toto.white())?;
        writeln!(&mut buf, "{}", toto.white().red().blue().green())?;
        writeln!(&mut buf, "{}", toto.truecolor(255, 0, 0))?;
        writeln!(&mut buf, "{}", toto.truecolor(255, 255, 0))?;
        writeln!(&mut buf, "{}", toto.on_truecolor(0, 80, 80))?;
        writeln!(&mut buf, "{}", toto.custom_color((255, 255, 0)))?;
        writeln!(&mut buf, "{}", toto.on_custom_color((0, 80, 80)))?;
        #[cfg(feature = "no-color")]
        insta::assert_snapshot!("it_works_no_color", buf);
        #[cfg(not(feature = "no-color"))]
        insta::assert_snapshot!("it_works", buf);
        Ok(())
    }

    #[test]
    fn compute_style_empty_string() {
        assert_eq!("", "".clear().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_simple_fg_blue() {
        let blue = "\x1B[34m";

        assert_eq!(blue, "".blue().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_simple_bg_blue() {
        let on_blue = "\x1B[44m";

        assert_eq!(on_blue, "".on_blue().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_blue_on_blue() {
        let blue_on_blue = "\x1B[44;34m";

        assert_eq!(blue_on_blue, "".blue().on_blue().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_simple_fg_bright_blue() {
        let blue = "\x1B[94m";

        assert_eq!(blue, "".bright_blue().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_simple_bg_bright_blue() {
        let on_blue = "\x1B[104m";

        assert_eq!(on_blue, "".on_bright_blue().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_bright_blue_on_bright_blue() {
        let blue_on_blue = "\x1B[104;94m";

        assert_eq!(
            blue_on_blue,
            "".bright_blue().on_bright_blue().compute_style()
        );
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_simple_bold() {
        let bold = "\x1B[1m";

        assert_eq!(bold, "".bold().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_blue_bold() {
        let blue_bold = "\x1B[1;34m";

        assert_eq!(blue_bold, "".blue().bold().compute_style());
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn compute_style_blue_bold_on_blue() {
        let blue_bold_on_blue = "\x1B[1;44;34m";

        assert_eq!(
            blue_bold_on_blue,
            "".blue().bold().on_blue().compute_style()
        );
    }

    #[test]
    fn escape_reset_sequence_spec_should_do_nothing_on_empty_strings() {
        let style = ColoredString::default();
        let expected = String::new();

        let output = style.escape_inner_reset_sequences();

        assert_eq!(expected, output);
    }

    #[test]
    fn escape_reset_sequence_spec_should_do_nothing_on_string_with_no_reset() {
        let style = ColoredString {
            input: String::from("hello world !"),
            ..ColoredString::default()
        };

        let expected = String::from("hello world !");
        let output = style.escape_inner_reset_sequences();

        assert_eq!(expected, output);
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn escape_reset_sequence_spec_should_replace_inner_reset_sequence_with_current_style() {
        let input = format!("start {} end", String::from("hello world !").red());
        let style = input.blue();

        let output = style.escape_inner_reset_sequences();
        let blue = "\x1B[34m";
        let red = "\x1B[31m";
        let reset = "\x1B[0m";
        let expected = format!("start {}hello world !{}{} end", red, reset, blue);
        assert_eq!(expected, output);
    }

    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn escape_reset_sequence_spec_should_replace_multiple_inner_reset_sequences_with_current_style()
    {
        let italic_str = String::from("yo").italic();
        let input = format!(
            "start 1:{} 2:{} 3:{} end",
            italic_str, italic_str, italic_str
        );
        let style = input.blue();

        let output = style.escape_inner_reset_sequences();
        let blue = "\x1B[34m";
        let italic = "\x1B[3m";
        let reset = "\x1B[0m";
        let expected = format!(
            "start 1:{}yo{}{} 2:{}yo{}{} 3:{}yo{}{} end",
            italic, reset, blue, italic, reset, blue, italic, reset, blue
        );

        println!("first: {}\nsecond: {}", expected, output);

        assert_eq!(expected, output);
    }

    #[test]
    fn color_fn() {
        assert_eq!("blue".blue(), "blue".color("blue"));
    }

    #[test]
    fn on_color_fn() {
        assert_eq!("blue".on_blue(), "blue".on_color("blue"));
    }

    #[test]
    fn bright_color_fn() {
        assert_eq!("blue".bright_blue(), "blue".color("bright blue"));
    }

    #[test]
    fn on_bright_color_fn() {
        assert_eq!("blue".on_bright_blue(), "blue".on_color("bright blue"));
    }

    #[test]
    fn exposing_tests() {
        #![allow(deprecated)]

        let cstring = "".red();
        assert_eq!(cstring.fgcolor(), Some(Color::Red));
        assert_eq!(cstring.bgcolor(), None);

        let cstring = cstring.clear();
        assert_eq!(cstring.fgcolor(), None);
        assert_eq!(cstring.bgcolor(), None);

        let cstring = cstring.blue().on_bright_yellow();
        assert_eq!(cstring.fgcolor(), Some(Color::Blue));
        assert_eq!(cstring.bgcolor(), Some(Color::BrightYellow));

        let cstring = cstring.bold().italic();
        assert_eq!(cstring.fgcolor(), Some(Color::Blue));
        assert_eq!(cstring.bgcolor(), Some(Color::BrightYellow));
        assert!(cstring.style().contains(Styles::Bold));
        assert!(cstring.style().contains(Styles::Italic));
        assert!(!cstring.style().contains(Styles::Dimmed));
    }
}
