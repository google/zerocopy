
/// @spec
/// isValid self := if self.check then self.val > 0 else self.val == 0
pub struct Checked {
    pub check: bool,
    pub val: u32,
}
