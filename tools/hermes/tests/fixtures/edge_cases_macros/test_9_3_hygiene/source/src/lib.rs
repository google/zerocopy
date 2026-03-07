
macro_rules! hygiene_check {
    () => {
        let x = 1;
        let x = x + 1;
    };
}

/// ```lean, hermes
/// proof context:
///   sorry
/// ```
pub fn check_hygiene() {
    hygiene_check!();
}
