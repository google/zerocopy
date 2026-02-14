
/// @spec
/// isValid self := match self.next with | .none => True | .some n => isValid n
pub struct Node {
    pub next: Option<Box<Node>>,
}
