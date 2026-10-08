// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Native protocol coverage tests. The admitted synthetic helper emits status
//! records only; these do not substitute for the real Lean capability controls.

use super::*;
use crate::lean_sdk::{LakeLibrary, LeanSdk, tests::Fixture};
use sha2::{Digest as _, Sha256};
use std::os::unix::fs::PermissionsExt as _;

fn with_workspace(mode: &str, test: impl FnOnce(&Workspace<'_>)) {
    let fixture = Fixture::new(&["Shared.A"]);
    let sdk_root = fixture.sdk.root();
    let helper = format!(
        r#"#!/usr/bin/python3
import sys
sys.dont_write_bytecode = True
import json
from pathlib import Path
mode = {mode:?}
plan = json.load(sys.stdin)
root = Path(sys.argv[1])
op = plan['opId']
requests = plan['requests']
def emit(event, **fields):
    print(json.dumps(dict(protocol=1, opId=op, event=event, **fields)), flush=True)
(root / '.lake' / ('finite-plan-' + requests[0]['requestId'] + '.json')).write_text(json.dumps(plan))
emit('load', outcome='loaded')
if mode == 'fatalLate' and requests[0]['requestId'] == 'root-32':
    emit('fatal', error='injected late fatal', errorTruncated=False)
    sys.exit(2)
failed = False
for index, request in enumerate(requests):
    if mode == 'failedFirst' and index == 0:
        failed = True
        emit('root', index=index, requestId=request['requestId'], outcome='buildFailed',
             error='injected shared-target failure', errorTruncated=False)
    else:
        outcome = 'prepared' if request['setup'] is not None else 'buildOnly'
        emit('root', index=index, requestId=request['requestId'], outcome=outcome)
emit('complete', count=len(requests), failed=failed)
sys.exit(1 if failed else 0)
"#
    );
    let helper_path = sdk_root.join("bin/anneal-finite-lake");
    fs::write(&helper_path, &helper).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o755)).unwrap();
    let mut descriptor: Value =
        serde_json::from_slice(&fs::read(sdk_root.join("sdk.json")).unwrap()).unwrap();
    descriptor["schema"] = json!(2);
    descriptor["finite_lake"] = json!({"path":"bin/anneal-finite-lake",
        "sha256": format!("{:x}", Sha256::digest(helper.as_bytes())), "protocol":1});
    fs::write(sdk_root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
    let sdk = LeanSdk::load(sdk_root).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let workspace = Workspace::create(&sdk, &dir.path().join("workspace"), &["."]).unwrap();
    Workspace::write_lakefile(
        &sdk,
        workspace.root(),
        &[LakeLibrary { name: "User", source_root: ".", modules: &[] }],
    )
    .unwrap();
    fs::write(workspace.root().join("Shared.lean"), "def shared := 1\n").unwrap();
    test(&workspace);
}

fn open_document(state: &mut State, path: &Path, text: &str) {
    state.update_document(&json!({"method":"textDocument/didOpen","params":{"textDocument":{
        "uri":format!("file://{}",path.display()), "languageId":"lean4", "version":1,"text":text
    }}}), false).unwrap();
}

fn state(workspace: &Workspace<'_>) -> State {
    State::new(
        workspace.root().to_owned(),
        vec![workspace.root().to_owned()],
        workspace.source_stamp().unwrap(),
        false,
    )
    .unwrap()
}

fn build(workspace: &Workspace<'_>, state: &State) -> Build {
    let writer = workspace.writer_lock().unwrap();
    let documents = state.build_documents(true);
    let batches = build_commands(workspace, state, &documents).unwrap();
    assert!(batches.iter().any(BuildBatch::has_commands));
    let preparation = workspace.prepare_local_outputs().unwrap();
    assert_eq!(preparation.stamp(), state.stamp);
    Build::spawn(batches, documents, state.stamp, Some(preparation), writer).unwrap()
}

fn poll(build: &mut Build) -> Result<BuildOutcome> {
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(outcome) = build.poll()? {
            return Ok(outcome);
        }
        ensure!(Instant::now() < deadline, "Native editor test exceeded its deadline");
        thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn native_unsaved_zero_work_does_not_start_helper_or_output_preparation() {
    with_workspace("normal", |workspace| {
        let mut state = state(workspace);
        let path = workspace.root().join("New.lean");
        open_document(&mut state, &path, "example : True := by trivial\n");
        let documents = state.build_documents(true);
        assert_eq!(documents.len(), 1);
        let writer = workspace.writer_lock().unwrap();
        let before = workspace.source_stamp().unwrap();
        let batches = build_commands(workspace, &state, &documents).unwrap();
        assert!(!batches.iter().any(BuildBatch::has_commands));
        let mut build = Build::spawn(batches, documents, before, None, writer).unwrap();
        let outcome = poll(&mut build).unwrap();
        assert!(!outcome.failed && outcome.covered.contains_key(&path));
        assert!(build.preparation.is_none());
        assert!(!path.exists());
        assert!(!workspace.root().join(".lake/finite-plan-root-0.json").exists());
        assert_eq!(workspace.source_stamp().unwrap(), before);
    });
}

#[test]
fn native_ordinary_failure_retains_only_healthy_shared_target_coverage() {
    with_workspace("failedFirst", |workspace| {
        for name in ["A", "B"] {
            fs::write(
                workspace.root().join(format!("{name}.lean")),
                "import Shared\nexample : True := by trivial\n",
            )
            .unwrap();
        }
        let mut state = state(workspace);
        for name in ["A", "B"] {
            open_document(
                &mut state,
                &workspace.root().join(format!("{name}.lean")),
                "import Shared\nexample : True := by trivial\n-- retained live buffer\n",
            );
        }
        let mut build = build(workspace, &state);
        let outcome = poll(&mut build).unwrap();
        assert!(outcome.failed);
        assert_eq!(outcome.attempted.len(), 2);
        assert_eq!(outcome.covered.len(), 1);
        assert!(outcome.covered.contains_key(&workspace.root().join("B.lean")));
        assert!(!workspace.root().join(".lake/.anneal-local-inputs").exists());
        let plan: Value = serde_json::from_slice(
            &fs::read(workspace.root().join(".lake/finite-plan-root-0.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(plan["requests"][0]["targets"], plan["requests"][1]["targets"]);
        assert_eq!(
            plan["requests"][0]["setup"]["header"],
            module_header(
                &state.documents.values().find(|doc| doc.path.ends_with("A.lean")).unwrap().text
            )
            .unwrap()
        );
        assert!(
            fs::read_to_string(workspace.root().join("A.lean")).unwrap().ends_with("trivial\n")
        );
    });
}

#[test]
fn native_later_chunk_fatal_never_returns_prior_chunk_coverage() {
    with_workspace("fatalLate", |workspace| {
        for index in 0..33 {
            fs::write(
                workspace.root().join(format!("C{index:02}.lean")),
                "import Shared\nexample : True := by trivial\n",
            )
            .unwrap();
        }
        let mut state = state(workspace);
        for index in 0..33 {
            open_document(
                &mut state,
                &workspace.root().join(format!("C{index:02}.lean")),
                "import Shared\nexample : True := by trivial\n",
            );
        }
        let mut build = build(workspace, &state);
        let error = poll(&mut build).err().expect("Late fatal must reject the entire operation");
        assert!(error.to_string().contains("injected late fatal"), "{error:#}");
        assert_eq!(build.covered.len(), 32, "First chunk was never reached");
        assert!(!workspace.root().join(".lake/.anneal-local-inputs").exists());
        build.stop();
        assert!(build.native.is_none() && build.process.is_none());
    });
}
