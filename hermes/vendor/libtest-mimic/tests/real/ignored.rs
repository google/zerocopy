#[test]
fn not_ignored() {}

#[test]
#[ignore]
fn normally_ignored() {}

#[test]
#[ignore = "special message"]
fn ignored_with_message() {}
