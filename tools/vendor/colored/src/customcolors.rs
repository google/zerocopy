/// Custom color structure, it will generate a true color in the result
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct CustomColor {
    /// Red
    pub r: u8,
    /// Green
    pub g: u8,
    /// Blue
    pub b: u8,
}

/// This only makes custom color creation easier.
impl CustomColor {
    /// Create a new custom color
    pub fn new(r: u8, g: u8, b: u8) -> Self {
        Self { r, g, b }
    }
}

impl From<(u8, u8, u8)> for CustomColor {
    fn from((r, g, b): (u8, u8, u8)) -> Self {
        Self::new(r, g, b)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    #[cfg_attr(feature = "no-color", ignore)]
    #[test]
    fn main() {
        let my_color = CustomColor::new(0, 120, 120);
        insta::assert_snapshot!("Greetings from Ukraine".custom_color(my_color));
    }

    #[test]
    fn from_tuple() {
        let tuple = (1u8, 255u8, 0u8);
        let cc = CustomColor::from(tuple);

        assert_eq!(cc.r, tuple.0);
        assert_eq!(cc.g, tuple.1);
        assert_eq!(cc.b, tuple.2);
    }
}
