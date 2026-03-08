
/// @spec
/// isValid self := match self.next with | .none => True | .some n => isValid n
pub struct Node {
    pub next: Option<Box<Node>>,
}


/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold dummy_hermes_padding at *
///   simp_all
/// ```
pub fn dummy_hermes_padding() {}
