
/// @spec
/// isValid self := match self.next with | .none => True | .some n => isValid n
pub struct Node {
    pub next: Option<Box<Node>>,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_hermes_padding() {}
