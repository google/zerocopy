generated_macro::emit_helper!();
include!(concat!(env!("OUT_DIR"), "/generated.rs"));

pub fn library_subject() -> u32 { shared::target_value() + BUILD_VALUE + proc_generated() }

/// ```lean, anneal, spec
/// ensures (h0): ret.val = 101
/// proof (h0):
///   simp [selected_feature_subject] at h_returns
///   subst ret
///   rfl
/// ```
#[cfg(feature = "selected")]
pub fn selected_feature_subject() -> u32 { 101 }

#[cfg(test)]
mod unit_tests {
    #[test]
    fn sees_dev_dependency_context() { assert_eq!(shared::dev_value(), 23); }
}
