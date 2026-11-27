// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The decoupled correspondence provenance sentinel.

use super::*;

#[test]
fn decoupled_correspondence_provenance_sentinel_is_exact() {
    let tmp = tempfile::tempdir().unwrap();
    let (mut base, _, _, _, _) = sample_receipt_bundle(&tmp.path().join("artifacts"));
    let record_path = tmp.path().join("record.json");
    fs::write(&record_path, serde_json::to_vec(&base).unwrap()).unwrap();
    base["correspondence_provenance"] = json!({
        "applicable": false,
        "reason": cargo_anneal::bundle::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
    });
    let base_path = tmp.path().join("decoupled.json");
    fs::write(&base_path, serde_json::to_vec(&base).unwrap()).unwrap();

    // The exact sentinel stands in for pinned Profile v1 provenance, even
    // under `--unknown-fields deny`.
    let ok = run_inspect(&[base_path.to_str().unwrap(), "--unknown-fields", "deny"], None);
    assert_eq!(ok.status.code(), Some(0), "{}", String::from_utf8_lossy(&ok.stderr));

    // Every renderer surfaces the sentinel's reason and qualifies the success,
    // since no Pass 2 record binds the model the receipt relied on.
    let reason = cargo_anneal::bundle::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON;
    let render = |format: &str| {
        let out = run_inspect(&[base_path.to_str().unwrap(), "--format", format], None);
        assert_eq!(out.status.code(), Some(0), "{format}: {out:?}");
        String::from_utf8(out.stdout).unwrap()
    };
    let human = render("human");
    assert!(human.contains(" [QUALIFIED]\n"), "{human}");
    assert!(human.contains("correspondence=inapplicable"), "{human}");
    assert!(human.contains(&format!("  correspondence: inapplicable ({reason})\n")), "{human}");
    let md = render("markdown");
    assert!(md.contains("**QUALIFIED ASSURANCE:**"), "{md}");
    assert!(md.contains("`correspondence=inapplicable`"), "{md}");
    assert!(
        md.contains(&format!("| Correspondence Provenance | not applicable: `{reason}` |")),
        "{md}"
    );
    let ledger = render("ledger");
    assert!(ledger.contains("correspondence_provenance.applicable=false\n"), "{ledger}");
    assert!(ledger.contains(&format!("correspondence_provenance.reason={reason}\n")), "{ledger}");
    let json_out = render("json");
    let parsed: Value = serde_json::from_str(&json_out).unwrap();
    assert_eq!(parsed["receipt"]["correspondence_applicable"], false, "{json_out}");
    assert_eq!(parsed["receipt"]["correspondence_inapplicable_reason"], reason, "{json_out}");

    // Replacing an applicable record with the sentinel is a `--no-regressions`
    // failure; the reverse is not.
    let diff = |b: &std::path::Path, h: &std::path::Path| {
        run_inspect(&["--diff", b.to_str().unwrap(), h.to_str().unwrap(), "--no-regressions"], None)
    };
    let lost = diff(&record_path, &base_path);
    assert_eq!(lost.status.code(), Some(1), "{lost:?}");
    assert!(
        String::from_utf8_lossy(&lost.stdout).contains("correspondence_provenance.applicable"),
        "{lost:?}"
    );
    let gained = diff(&base_path, &record_path);
    assert_eq!(gained.status.code(), Some(0), "{gained:?}");

    // Any other `applicable: false` reason on a pinned Profile v1 receipt is
    // an envelope violation.
    let mut altered = base;
    altered["correspondence_provenance"]["reason"] = json!(format!(
        "{} (altered)",
        cargo_anneal::bundle::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON
    ));
    let altered_path = tmp.path().join("altered.json");
    fs::write(&altered_path, serde_json::to_vec(&altered).unwrap()).unwrap();
    let bad = run_inspect(&[altered_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(bad.status.code(), Some(1), "{bad:?}");
    assert!(
        String::from_utf8_lossy(&bad.stdout)
            .contains("correspondence_provenance must omit `applicable: false`"),
        "{bad:?}"
    );
}
