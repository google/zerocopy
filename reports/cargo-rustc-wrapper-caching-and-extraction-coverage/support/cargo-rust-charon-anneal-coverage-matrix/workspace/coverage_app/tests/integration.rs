#[test]
fn integration_target_observes_library() {
    assert!(coverage_app::library_subject() > 0);
}
