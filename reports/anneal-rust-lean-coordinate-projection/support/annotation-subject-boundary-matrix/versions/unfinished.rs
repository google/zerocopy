#![allow(dead_code)]
pub const SOURCE: &str = include_str!("lib.rs");
pub const BUILD_PROOF: &str = env!("PROOF_STAMP");
pub fn source_len() -> usize { SOURCE.len() }

//% begin shared scope=module
//% def helper : Nat := 7
//% end

pub mod left {
    //% begin claim-a scope=next
    //% namespace Left
    //% theorem checked : helper = 7 := by rfl
    //% end Left
    //% end
    /// proof-id: claim-a
    pub fn alpha() -> u32 { 7 }
}

pub mod right {
    //% begin claim-b scope=next
    //% namespace Right
    //% theorem checked : helper = 7 := by rfl
    //% end Right
    //% end
    /// proof-id: claim-b
    pub fn beta() -> u32 { 7 }
}

//% begin selected scope=next
//% namespace Selected
//% theorem checked : helper = 7 := by rfl
//% end Selected
//% end
#[cfg(feature = "selected")]
/// proof-id: selected
pub fn selected_only() -> u32 { 7 }

#[cfg(test)]
mod tests {
    //% begin test-only scope=next
    //% namespace Test
    //% theorem checked : helper = 7 := by rfl
    //% end Test
    //% end
    /// proof-id: test-only
    pub fn test_only() -> u32 { 7 }
    #[test] fn smoke() { assert_eq!(test_only(), 7); }
}

//% begin orphan scope=next
//% theorem unfinished : True := by
