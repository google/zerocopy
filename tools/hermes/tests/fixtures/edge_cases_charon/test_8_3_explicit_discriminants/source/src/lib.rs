pub enum Color {
    Red = 0xff,
    Green = 0x00,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
