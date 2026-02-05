use std::{borrow::Cow, cmp, env, str::FromStr};
use Color::{
    AnsiColor, Black, Blue, BrightBlack, BrightBlue, BrightCyan, BrightGreen, BrightMagenta,
    BrightRed, BrightWhite, BrightYellow, Cyan, Green, Magenta, Red, TrueColor, White, Yellow,
};

/// The 8 standard colors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Color {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
    BrightBlack,
    BrightRed,
    BrightGreen,
    BrightYellow,
    BrightBlue,
    BrightMagenta,
    BrightCyan,
    BrightWhite,
    AnsiColor(u8),
    TrueColor { r: u8, g: u8, b: u8 },
}

fn truecolor_support() -> bool {
    let truecolor = env::var("COLORTERM");
    truecolor.is_ok_and(|truecolor| truecolor == "truecolor" || truecolor == "24bit")
}

#[allow(missing_docs)]
impl Color {
    #[must_use]
    pub fn to_fg_str(&self) -> Cow<'static, str> {
        match *self {
            Self::Black => "30".into(),
            Self::Red => "31".into(),
            Self::Green => "32".into(),
            Self::Yellow => "33".into(),
            Self::Blue => "34".into(),
            Self::Magenta => "35".into(),
            Self::Cyan => "36".into(),
            Self::White => "37".into(),
            Self::BrightBlack => "90".into(),
            Self::BrightRed => "91".into(),
            Self::BrightGreen => "92".into(),
            Self::BrightYellow => "93".into(),
            Self::BrightBlue => "94".into(),
            Self::BrightMagenta => "95".into(),
            Self::BrightCyan => "96".into(),
            Self::BrightWhite => "97".into(),
            Self::TrueColor { .. } if !truecolor_support() => {
                self.closest_color_euclidean().to_fg_str()
            }
            Self::AnsiColor(code) => format!("38;5;{code}").into(),
            Self::TrueColor { r, g, b } => format!("38;2;{r};{g};{b}").into(),
        }
    }

    #[must_use]
    pub fn to_bg_str(&self) -> Cow<'static, str> {
        match *self {
            Self::Black => "40".into(),
            Self::Red => "41".into(),
            Self::Green => "42".into(),
            Self::Yellow => "43".into(),
            Self::Blue => "44".into(),
            Self::Magenta => "45".into(),
            Self::Cyan => "46".into(),
            Self::White => "47".into(),
            Self::BrightBlack => "100".into(),
            Self::BrightRed => "101".into(),
            Self::BrightGreen => "102".into(),
            Self::BrightYellow => "103".into(),
            Self::BrightBlue => "104".into(),
            Self::BrightMagenta => "105".into(),
            Self::BrightCyan => "106".into(),
            Self::BrightWhite => "107".into(),
            Self::AnsiColor(code) => format!("48;5;{code}").into(),
            Self::TrueColor { .. } if !truecolor_support() => {
                self.closest_color_euclidean().to_bg_str()
            }
            Self::TrueColor { r, g, b } => format!("48;2;{r};{g};{b}").into(),
        }
    }

    /// Gets the closest plain color to the `TrueColor`
    fn closest_color_euclidean(self) -> Self {
        match self {
            TrueColor {
                r: r1,
                g: g1,
                b: b1,
            } => {
                let colors = vec![
                    Black,
                    Red,
                    Green,
                    Yellow,
                    Blue,
                    Magenta,
                    Cyan,
                    White,
                    BrightBlack,
                    BrightRed,
                    BrightGreen,
                    BrightYellow,
                    BrightBlue,
                    BrightMagenta,
                    BrightCyan,
                    BrightWhite,
                ]
                .into_iter()
                .map(|c| (c, c.into_truecolor()));
                let distances = colors.map(|(c_original, c)| {
                    if let TrueColor { r, g, b } = c {
                        let rd = cmp::max(r, r1) - cmp::min(r, r1);
                        let gd = cmp::max(g, g1) - cmp::min(g, g1);
                        let bd = cmp::max(b, b1) - cmp::min(b, b1);
                        let rd: u32 = rd.into();
                        let gd: u32 = gd.into();
                        let bd: u32 = bd.into();
                        let distance = rd.pow(2) + gd.pow(2) + bd.pow(2);
                        (c_original, distance)
                    } else {
                        unimplemented!("{:?} not a TrueColor", c)
                    }
                });
                distances.min_by(|(_, d1), (_, d2)| d1.cmp(d2)).unwrap().0
            }
            c => c,
        }
    }

    const fn into_truecolor(self) -> Self {
        match self {
            Black => TrueColor { r: 0, g: 0, b: 0 },
            Red => TrueColor { r: 205, g: 0, b: 0 },
            Green => TrueColor { r: 0, g: 205, b: 0 },
            Yellow => TrueColor {
                r: 205,
                g: 205,
                b: 0,
            },
            Blue => TrueColor { r: 0, g: 0, b: 238 },
            Magenta => TrueColor {
                r: 205,
                g: 0,
                b: 205,
            },
            Cyan => TrueColor {
                r: 0,
                g: 205,
                b: 205,
            },
            White => TrueColor {
                r: 229,
                g: 229,
                b: 229,
            },
            BrightBlack => TrueColor {
                r: 127,
                g: 127,
                b: 127,
            },
            BrightRed => TrueColor { r: 255, g: 0, b: 0 },
            BrightGreen => TrueColor { r: 0, g: 255, b: 0 },
            BrightYellow => TrueColor {
                r: 255,
                g: 255,
                b: 0,
            },
            BrightBlue => TrueColor {
                r: 92,
                g: 92,
                b: 255,
            },
            BrightMagenta => TrueColor {
                r: 255,
                g: 0,
                b: 255,
            },
            BrightCyan => TrueColor {
                r: 0,
                g: 255,
                b: 255,
            },
            BrightWhite => TrueColor {
                r: 255,
                g: 255,
                b: 255,
            },
            AnsiColor(color) => AnsiColor(color),
            TrueColor { r, g, b } => TrueColor { r, g, b },
        }
    }
}

impl From<&str> for Color {
    fn from(src: &str) -> Self {
        src.parse().unwrap_or(Self::White)
    }
}

impl From<String> for Color {
    fn from(src: String) -> Self {
        src.parse().unwrap_or(Self::White)
    }
}

impl FromStr for Color {
    type Err = ();

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let src = src.to_lowercase();

        match src.as_ref() {
            "black" => Ok(Self::Black),
            "red" => Ok(Self::Red),
            "green" => Ok(Self::Green),
            "yellow" => Ok(Self::Yellow),
            "blue" => Ok(Self::Blue),
            "magenta" | "purple" => Ok(Self::Magenta),
            "cyan" => Ok(Self::Cyan),
            "white" => Ok(Self::White),
            "bright black" => Ok(Self::BrightBlack),
            "bright red" => Ok(Self::BrightRed),
            "bright green" => Ok(Self::BrightGreen),
            "bright yellow" => Ok(Self::BrightYellow),
            "bright blue" => Ok(Self::BrightBlue),
            "bright magenta" => Ok(Self::BrightMagenta),
            "bright cyan" => Ok(Self::BrightCyan),
            "bright white" => Ok(Self::BrightWhite),
            s if s.starts_with('#') => parse_hex(&s[1..]).ok_or(()),
            _ => Err(()),
        }
    }
}

fn parse_hex(s: &str) -> Option<Color> {
    if s.len() == 6 {
        let r = u8::from_str_radix(&s[0..2], 16).ok()?;
        let g = u8::from_str_radix(&s[2..4], 16).ok()?;
        let b = u8::from_str_radix(&s[4..6], 16).ok()?;
        Some(Color::TrueColor { r, g, b })
    } else if s.len() == 3 {
        let r = u8::from_str_radix(&s[0..1], 16).ok()?;
        let r = r | (r << 4);
        let g = u8::from_str_radix(&s[1..2], 16).ok()?;
        let g = g | (g << 4);
        let b = u8::from_str_radix(&s[2..3], 16).ok()?;
        let b = b | (b << 4);
        Some(Color::TrueColor { r, g, b })
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    pub use super::*;

    mod from_str {
        pub use super::*;

        macro_rules! make_test {
            ( $( $name:ident: $src:expr => $dst:expr),* ) => {

                $(
                    #[test]
                    fn $name() {
                        let color : Color = $src.into();
                        assert_eq!($dst, color)
                    }
                )*
            }
        }

        make_test!(
            black: "black" => Color::Black,
            red: "red" => Color::Red,
            green: "green" => Color::Green,
            yellow: "yellow" => Color::Yellow,
            blue: "blue" => Color::Blue,
            magenta: "magenta" => Color::Magenta,
            purple: "purple" => Color::Magenta,
            cyan: "cyan" => Color::Cyan,
            white: "white" => Color::White,
            brightblack: "bright black" => Color::BrightBlack,
            brightred: "bright red" => Color::BrightRed,
            brightgreen: "bright green" => Color::BrightGreen,
            brightyellow: "bright yellow" => Color::BrightYellow,
            brightblue: "bright blue" => Color::BrightBlue,
            brightmagenta: "bright magenta" => Color::BrightMagenta,
            brightcyan: "bright cyan" => Color::BrightCyan,
            brightwhite: "bright white" => Color::BrightWhite,

            invalid: "invalid" => Color::White,
            capitalized: "BLUE" => Color::Blue,
            mixed_case: "bLuE" => Color::Blue,

            hex3_lower: "#abc" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex3_upper: "#ABC" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex3_mixed: "#aBc" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex6_lower: "#abcdef" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex6_upper: "#ABCDEF" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex6_mixed: "#aBcDeF" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex_too_short: "#aa" => Color::White,
            hex_too_long: "#aaabbbccc" => Color::White,
            hex_invalid: "#abcxyz" => Color::White
        );
    }

    mod from_string {
        pub use super::*;

        macro_rules! make_test {
            ( $( $name:ident: $src:expr => $dst:expr),* ) => {

                $(
                    #[test]
                    fn $name() {
                        let src = String::from($src);
                        let color : Color = src.into();
                        assert_eq!($dst, color)
                    }
                )*
            }
        }

        make_test!(
            black: "black" => Color::Black,
            red: "red" => Color::Red,
            green: "green" => Color::Green,
            yellow: "yellow" => Color::Yellow,
            blue: "blue" => Color::Blue,
            magenta: "magenta" => Color::Magenta,
            cyan: "cyan" => Color::Cyan,
            white: "white" => Color::White,
            brightblack: "bright black" => Color::BrightBlack,
            brightred: "bright red" => Color::BrightRed,
            brightgreen: "bright green" => Color::BrightGreen,
            brightyellow: "bright yellow" => Color::BrightYellow,
            brightblue: "bright blue" => Color::BrightBlue,
            brightmagenta: "bright magenta" => Color::BrightMagenta,
            brightcyan: "bright cyan" => Color::BrightCyan,
            brightwhite: "bright white" => Color::BrightWhite,

            invalid: "invalid" => Color::White,
            capitalized: "BLUE" => Color::Blue,
            mixed_case: "bLuE" => Color::Blue,

            hex3_lower: "#abc" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex3_upper: "#ABC" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex3_mixed: "#aBc" => Color::TrueColor { r: 170, g: 187, b: 204 },
            hex6_lower: "#abcdef" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex6_upper: "#ABCDEF" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex6_mixed: "#aBcDeF" => Color::TrueColor { r: 171, g: 205, b: 239 },
            hex_too_short: "#aa" => Color::White,
            hex_too_long: "#aaabbbccc" => Color::White,
            hex_invalid: "#abcxyz" => Color::White
        );
    }

    mod fromstr {
        pub use super::*;

        #[test]
        fn parse() {
            let color: Result<Color, _> = "blue".parse();
            assert_eq!(Ok(Color::Blue), color);
        }

        #[test]
        fn error() {
            let color: Result<Color, ()> = "bloublou".parse();
            assert_eq!(Err(()), color);
        }
    }

    mod closest_euclidean {
        use super::*;

        macro_rules! make_euclidean_distance_test {
            ( $test:ident : ( $r:literal, $g: literal, $b:literal ), $expected:expr ) => {
                #[test]
                fn $test() {
                    let true_color = Color::TrueColor {
                        r: $r,
                        g: $g,
                        b: $b,
                    };
                    let actual = true_color.closest_color_euclidean();
                    assert_eq!(actual, $expected);
                }
            };
        }

        make_euclidean_distance_test! { exact_black: (0, 0, 0), Color::Black }
        make_euclidean_distance_test! { exact_red: (205, 0, 0), Color::Red }
        make_euclidean_distance_test! { exact_green: (0, 205, 0), Color::Green }
        make_euclidean_distance_test! { exact_yellow: (205, 205, 0), Color::Yellow }
        make_euclidean_distance_test! { exact_blue: (0, 0, 238), Color::Blue }
        make_euclidean_distance_test! { exact_magenta: (205, 0, 205), Color::Magenta }
        make_euclidean_distance_test! { exact_cyan: (0, 205, 205), Color::Cyan }
        make_euclidean_distance_test! { exact_white: (229, 229, 229), Color::White }

        make_euclidean_distance_test! { almost_black: (10, 15, 10), Color::Black }
        make_euclidean_distance_test! { almost_red: (215, 10, 10), Color::Red }
        make_euclidean_distance_test! { almost_green: (10, 195, 10), Color::Green }
        make_euclidean_distance_test! { almost_yellow: (195, 215, 10), Color::Yellow }
        make_euclidean_distance_test! { almost_blue: (0, 0, 200), Color::Blue }
        make_euclidean_distance_test! { almost_magenta: (215, 0, 195), Color::Magenta }
        make_euclidean_distance_test! { almost_cyan: (10, 215, 215), Color::Cyan }
        make_euclidean_distance_test! { almost_white: (209, 209, 229), Color::White }
    }
}
