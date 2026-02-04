use std::{borrow::Cow, env, str::FromStr};

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
    TrueColor { r: u8, g: u8, b: u8 },
}

fn truecolor_support() -> bool {
    let truecolor = env::var("COLORTERM");
    if let Ok(truecolor) = truecolor {
        truecolor == "truecolor" || truecolor == "24bit"
    } else {
        false
    }
}

#[allow(missing_docs)]
impl Color {
    pub fn to_fg_str(&self) -> Cow<'static, str> {
        match *self {
            Color::Black => "30".into(),
            Color::Red => "31".into(),
            Color::Green => "32".into(),
            Color::Yellow => "33".into(),
            Color::Blue => "34".into(),
            Color::Magenta => "35".into(),
            Color::Cyan => "36".into(),
            Color::White => "37".into(),
            Color::BrightBlack => "90".into(),
            Color::BrightRed => "91".into(),
            Color::BrightGreen => "92".into(),
            Color::BrightYellow => "93".into(),
            Color::BrightBlue => "94".into(),
            Color::BrightMagenta => "95".into(),
            Color::BrightCyan => "96".into(),
            Color::BrightWhite => "97".into(),
            Color::TrueColor { .. } if !truecolor_support() => {
                self.closest_color_euclidean().to_fg_str()
            }
            Color::TrueColor { r, g, b } => format!("38;2;{};{};{}", r, g, b).into(),
        }
    }

    pub fn to_bg_str(&self) -> Cow<'static, str> {
        match *self {
            Color::Black => "40".into(),
            Color::Red => "41".into(),
            Color::Green => "42".into(),
            Color::Yellow => "43".into(),
            Color::Blue => "44".into(),
            Color::Magenta => "45".into(),
            Color::Cyan => "46".into(),
            Color::White => "47".into(),
            Color::BrightBlack => "100".into(),
            Color::BrightRed => "101".into(),
            Color::BrightGreen => "102".into(),
            Color::BrightYellow => "103".into(),
            Color::BrightBlue => "104".into(),
            Color::BrightMagenta => "105".into(),
            Color::BrightCyan => "106".into(),
            Color::BrightWhite => "107".into(),
            Color::TrueColor { .. } if !truecolor_support() => {
                self.closest_color_euclidean().to_bg_str()
            }
            Color::TrueColor { r, g, b } => format!("48;2;{};{};{}", r, g, b).into(),
        }
    }

    /// Gets the closest plain color to the TrueColor
    fn closest_color_euclidean(self) -> Self {
        use std::cmp;
        use Color::*;

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

    fn into_truecolor(self) -> Self {
        use Color::*;
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
            TrueColor { r, g, b } => TrueColor { r, g, b },
        }
    }
}

impl From<&str> for Color {
    fn from(src: &str) -> Self {
        src.parse().unwrap_or(Color::White)
    }
}

impl From<String> for Color {
    fn from(src: String) -> Self {
        src.parse().unwrap_or(Color::White)
    }
}

impl FromStr for Color {
    type Err = ();

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let src = src.to_lowercase();

        match src.as_ref() {
            "black" => Ok(Color::Black),
            "red" => Ok(Color::Red),
            "green" => Ok(Color::Green),
            "yellow" => Ok(Color::Yellow),
            "blue" => Ok(Color::Blue),
            "magenta" => Ok(Color::Magenta),
            "purple" => Ok(Color::Magenta),
            "cyan" => Ok(Color::Cyan),
            "white" => Ok(Color::White),
            "bright black" => Ok(Color::BrightBlack),
            "bright red" => Ok(Color::BrightRed),
            "bright green" => Ok(Color::BrightGreen),
            "bright yellow" => Ok(Color::BrightYellow),
            "bright blue" => Ok(Color::BrightBlue),
            "bright magenta" => Ok(Color::BrightMagenta),
            "bright cyan" => Ok(Color::BrightCyan),
            "bright white" => Ok(Color::BrightWhite),
            _ => Err(()),
        }
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
            mixed_case: "bLuE" => Color::Blue
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
            mixed_case: "bLuE" => Color::Blue
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
