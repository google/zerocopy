use cargo_metadata::{CrateType, Metadata, Target, TargetKind};
use fixtures::json::JsonFixture;
use guppy::{Error, PackageId, errors::FeatureGraphWarning, graph::PackageGraph};

#[test]
fn optional_dev_dep() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/optional_dev_dep.json"),
        "dependency 'lazy_static' marked optional",
    );
}

#[test]
fn duplicate_workspace_names() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/duplicate_workspace_names.json"),
        "duplicate package name in workspace: 'pkg' is name for",
    );
}

#[test]
fn invalid_default_member() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/invalid_default_member.json"),
        "workspace default member 'fake-package 1.0.0 (path+file:///fakepath/fake-package)' not found in workspace members",
    );
}

#[test]
fn build_targets_empty_kinds() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/build_targets_empty_kinds.json"),
        "build target 'bench1' has no kinds",
    );
}

#[test]
fn build_targets_non_bin() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/build_targets_non_bin.json"),
        "build target 'Binary(\"testcrate\")' has invalid crate types '{cdylib}'",
    );
}

#[test]
fn build_targets_duplicate_lib() {
    assert_invalid(
        include_str!("../../../fixtures/invalid/build_targets_duplicate_lib.json"),
        "duplicate build targets for Library",
    );
}

static SELF_LOOP_B: &str = "path+file:///home/fakeuser/dev/tmp/named-feature-self/b#0.1.0";

#[test]
fn named_feature_self_loop() {
    // This is not detected as invalid at construction time, but is instead detected while
    // constructing the feature graph.
    //
    // TODO: ideally, this would be detected at PackageGraph construction time.
    //
    // TODO: We currently do not detect loops consisting of multiple named features. We should do
    // this at construction time.
    let graph = PackageGraph::from_json(include_str!(
        "../../../fixtures/invalid/named_feature_self_loop.json"
    ))
    .expect("expected metadata to be valid");
    let feature_graph = graph.feature_graph();
    let warnings = feature_graph.build_warnings();
    assert_eq!(warnings.len(), 1);
    assert_eq!(
        warnings[0],
        FeatureGraphWarning::SelfLoop {
            package_id: PackageId::new(SELF_LOOP_B),
            feature_name: "a".into(),
        }
    );
}

#[test]
fn proc_macro_mixed_kinds() {
    fn macro_target(metadata: &mut Metadata) -> &mut Target {
        let package = metadata
            .packages
            .iter_mut()
            .find(|p| p.name.as_str() == "macro")
            .expect("valid package");
        package
            .targets
            .iter_mut()
            .find(|t| t.name == "macro")
            .expect("valid target")
    }

    let mut metadata: Metadata = serde_json::from_str(JsonFixture::metadata_proc_macro1().json())
        .expect("parsing metadata JSON should succeed");
    {
        let target = macro_target(&mut metadata);
        target.kind = vec![TargetKind::Lib, TargetKind::ProcMacro];
    }

    let json = serde_json::to_string(&metadata).expect("serializing worked");
    assert_invalid(&json, "proc-macro mixed with other kinds");

    {
        let target = macro_target(&mut metadata);

        // Reset target.kind to its old value.
        target.kind = vec![TargetKind::ProcMacro];

        target.crate_types = vec![CrateType::Lib, CrateType::ProcMacro];
    }

    let json = serde_json::to_string(&metadata).expect("serializing worked");
    assert_invalid(&json, "proc-macro mixed with other crate types");
}

fn assert_invalid(json: &str, search_str: &str) {
    let err = PackageGraph::from_json(json).expect_err("expected error for invalid metadata");
    let Error::PackageGraphConstructError(s) = err else {
        panic!("expected PackageGraphConstructError, got: {err} ({err:?}");
    };
    assert!(
        s.contains(search_str),
        "expected error to contain '{search_str}', got: {s}"
    );
}
