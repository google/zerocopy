#![deny(unsafe_code)]

#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unused_results)]


//! This is a library for padding strings at runtime.
//!
//! It provides four helper functions for the most common use cases, and one
//! main function (`pad`) to cover the other cases.
//!
//! String length is determined with the
//! [width](http://doc.rust-lang.org/nightly/std/str/trait.StrExt.html#tymethod.width)
//! function, without assuming CJK.
//!
//! Padding in the stdlib
//! ---------------------
//!
//! **You do not need this crate for simple padding!**
//! It’s possible to pad strings using the Rust standard library.
//!
//! For example, to pad a number with zeroes:
//!
//! ```
//! // Padding using std::fmt
//! assert_eq!("0000012345", format!("{:0>10}", 12345));
//! ```
//!
//! You can even use a variable for the padding width:
//!
//! ```
//! // Padding using std::fmt
//! assert_eq!("hello       ", format!("{:width$}", "hello", width=12));
//! ```
//!
//! The [Rust documentation for `std::fmt`](https://doc.rust-lang.org/std/fmt/)
//! contains more examples. The rest of the examples will use the `pad` crate.
//!
//! Examples
//! --------
//!
//! You can pad a string to have a minimum width with the `pad_to_width`
//! method:
//!
//! ```
//! use pad::PadStr;
//!
//! println!("{}", "Hi there!".pad_to_width(16));
//! ```
//!
//! This will print out “Hi there!” followed by seven spaces, which is the
//! number of spaces necessary to bring it up to a total of sixteen characters
//! wide.
//!
//!
//! Alignment
//! ---------
//!
//! By default, strings are left-aligned: any extra characters are added on
//! the right. To change this, pass in an `Alignment` value:
//!
//! ```
//! use pad::{PadStr, Alignment};
//!
//! let s = "I'm over here".pad_to_width_with_alignment(20, Alignment::Right);
//! ```
//!
//! There are four of these in total:
//!
//! - **Left**, which puts the text on the left and spaces on the right;
//! - **Right**, which puts the text on the right and spaces on the left;
//! - **Middle**, which centres the text evenly, putting it slightly to the
//!   left if it can’t be exactly centered;
//! - **MiddleRight**, as above, but to the right.
//!
//!
//! Characters
//! ----------
//!
//! Another thing that’s set by default is the character that’s used to pad
//! the strings — by default, it’s space, but you can change it:
//!
//! ```
//! use pad::PadStr;
//!
//! let s = "Example".pad_to_width_with_char(10, '_');
//! ```
//!
//!
//! Truncation
//! ----------
//!
//! Finally, you can override what happens when a value exceeds the width you
//! give. By default, the width parameter indicates a *minimum width*: any
//! string less will be padded, but any string greater will still be returned
//! in its entirety.
//!
//! You can instead tell it to pad with a maximum value, which will truncate
//! the input when a string longer than the width is passed in.
//!
//! ```
//! use pad::PadStr;
//!
//! let short = "short".with_exact_width(10);                // "short     "
//! let long  = "this string is long".with_exact_width(10);  // "this strin"
//! ```
//!
//!
//! A Full Example
//! --------------
//!
//! All of the above functions delegate to the `pad` function, which you can
//! use in special cases. Here, in order to **right**-pad a number with
//! **zeroes**, pass in all the arguments:
//!
//! ```
//! use pad::{PadStr, Alignment};
//!
//! let s = "12345".pad(10, '0', Alignment::Right, true);
//! ```
//!
//! (The `true` at the end governs whether to truncate or not.)
//!
//!
//! Note on Debugging
//! -----------------
//!
//! One very last point: the width function takes a `usize`, rather than a
//! signed number type. This means that if you try to pass in a negative size,
//! it’ll wrap around to a positive size, and produce a massive string and
//! possibly crash your program. So if your padding calls are failing for some
//! reason, this is probably why.


extern crate unicode_width;
use unicode_width::UnicodeWidthStr;


/// An **alignment** tells the padder where to put the spaces.
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum Alignment {

    /// Text on the left, spaces on the right.
    Left,

    /// Text on the right, spaces on the left.
    Right,

    /// Text in the middle, spaces around it, but **shifted to the left** if it can’t be exactly central.
    Middle,

    /// Text in the middle, spaces around it, but **shifted to the right** if it can’t be exactly central.
    MiddleRight,
}

/// Functions to do with string padding.
pub trait PadStr {

    /// Pad a string to be at least the given width by adding spaces on the
    /// right.
    fn pad_to_width(&self, width: usize) -> String {
        self.pad(width, ' ', Alignment::Left, false)
    }

    /// Pad a string to be at least the given width by adding the given
    /// character on the right.
    fn pad_to_width_with_char(&self, width: usize, pad_char: char) -> String {
        self.pad(width, pad_char, Alignment::Left, false)
    }

    /// Pad a string to be at least the given with by adding spaces around it.
    fn pad_to_width_with_alignment(&self, width: usize, alignment: Alignment) -> String {
        self.pad(width, ' ', alignment, false)
    }

    /// Pad a string to be *exactly* the given width by either adding spaces
    /// on the right, or by truncating it to that width.
    fn with_exact_width(&self, width: usize) -> String {
        self.pad(width, ' ', Alignment::Left, true)
    }

    /// Pad a string to the given width somehow.
    fn pad(&self, width: usize, pad_char: char, alignment: Alignment, truncate: bool) -> String;
}

impl PadStr for str {
    fn pad(&self, width: usize, pad_char: char, alignment: Alignment, truncate: bool) -> String {
        // Use width instead of len for graphical display
        let cols = UnicodeWidthStr::width(self);

        if cols >= width {
            if truncate {
                return self[..width].to_string();
            }
            else {
                return self.to_string();
            }
        }

        let diff = width - cols;

        let (left_pad, right_pad) = match alignment {
            Alignment::Left         => (0, diff),
            Alignment::Right        => (diff, 0),
            Alignment::Middle       => (diff / 2, diff - diff / 2),
            Alignment::MiddleRight  => (diff - diff / 2, diff / 2),
        };

        let mut s = String::new();
        for _ in 0..left_pad { s.push(pad_char) }
        s.push_str(self);
        for _ in 0..right_pad { s.push(pad_char) }
        s
    }
}


#[cfg(test)]
mod test {
    use super::PadStr;
    use super::Alignment::*;

    macro_rules! test {
    	($name: ident: $input: expr => $result: expr) => {
    		#[test]
    		fn $name() {
    			assert_eq!($result.to_string(), $input)
    		}
    	};
    }

    test!(zero: "".pad_to_width(0) => "");

    test!(simple: "hello".pad_to_width(10) => "hello     ");
    test!(spaces: "".pad_to_width(6)       => "      ");

    test!(too_long:      "hello".pad_to_width(2)      => "hello");
    test!(still_to_long: "hi there".pad_to_width(0)   => "hi there");
    test!(exact_length:  "greetings".pad_to_width(9)  => "greetings");
    test!(one_more:      "greetings".pad_to_width(10) => "greetings ");
    test!(one_less:      "greetings".pad_to_width(8)  => "greetings");

    test!(left:  "left align".pad_to_width_with_alignment(13, Left)   => "left align   ");
    test!(right: "right align".pad_to_width_with_alignment(13, Right) => "  right align");

    test!(centre_even:     "good day".pad_to_width_with_alignment(12, Middle)    => "  good day  ");
    test!(centre_odd:      "salutations".pad_to_width_with_alignment(13, Middle) => " salutations ");
    test!(centre_offset:   "odd".pad_to_width_with_alignment(6, Middle)          => " odd  ");
    test!(centre_offset_2: "odd".pad_to_width_with_alignment(6, MiddleRight)     => "  odd ");

    test!(character: "testing".pad_to_width_with_char(10, '_') => "testing___");

    test!(accent: "pâté".pad_to_width(6) => "pâté  ");

    test!(truncate:  "this song is just six words long".with_exact_width(7) => "this so");
    test!(too_short: "stormclouds".with_exact_width(15) => "stormclouds    ");
}
