// Copyright (c) The debug-ignore Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

extern crate debug_ignore;

use debug_ignore::DebugIgnore;

#[test]
fn test_transparent() {
    assert_eq!(
        serde_json::from_str::<DebugIgnore<_>>(r#""foo""#).unwrap(),
        DebugIgnore("foo")
    );
    assert_eq!(
        serde_json::to_string(&DebugIgnore("bar")).unwrap(),
        r#""bar""#,
    )
}
