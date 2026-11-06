fn main() {
    let _ = coverage_app::library_subject();
    #[cfg(feature = "selected")]
    { let _ = coverage_app::selected_feature_subject(); }
}
