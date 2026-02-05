use ui_test::dependencies::DependencyBuilder;
use ui_test::spanned::Spanned;
use ui_test::Config;

#[test]
fn test() {
    let mut config = Config::rustc("tests/build_std");
    let revisioned = config.comment_defaults.base();

    revisioned.exit_status = Spanned::dummy(0).into();
    revisioned.require_annotations = Spanned::dummy(false).into();
    revisioned.set_custom(
        "dependencies",
        DependencyBuilder {
            build_std: Some(String::new()),
            ..DependencyBuilder::default()
        },
    );

    ui_test::run_tests(config).unwrap();
}
