// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::sync::LazyLock;

use anyhow::Result;
use regex::Regex;

/// Represents a specification block extracted from the source code.
///
/// Contains the function name it applies to and the raw body of the specification.
#[derive(Debug, Clone)]
pub struct SpecBlock {
    pub function_name: String,
    pub body: String,
}

/// Represents a proof block extracted from the source code.
///
/// Contains the raw body of the proof.
#[derive(Debug, Clone)]
pub struct ProofBlock {
    pub body: String,
}

#[derive(Debug, Clone)]
pub struct ExtractedBlocks {
    pub specs: Vec<SpecBlock>,
    pub proofs: Vec<ProofBlock>,
}

/// Extracts both specification and proof blocks from the provided source content.
///
/// This function uses regular expressions to find blocks formatted as:
/// - `/*@ lean spec function_name ... @*/`
/// - `/*@ proof ... @*/`
pub fn extract_blocks(content: &str) -> Result<ExtractedBlocks> {
    // Regex matches:
    // - Start with `/*@`
    // - `lean spec` followed by function name
    // - Capture function name in `fn_name`
    // - Capture content in `body` (non-greedy)
    // - End with `@*/`
    static SPEC_RE: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(r"(?ms)/\*\@\s*lean\s+spec\s+(?P<fn_name>\w+)\s+(?P<body>.*?)\s*@\*/").unwrap()
    });

    // Regex matches:
    // - Start with `/*@`
    // - `proof`
    // - Capture content in `body` (non-greedy)
    // - End with `@*/`
    static PROOF_RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"(?ms)/\*\@\s*proof\s+(?P<body>.*?)\s*@\*/").unwrap());

    let mut specs = Vec::new();
    for cap in SPEC_RE.captures_iter(content) {
        specs.push(SpecBlock {
            function_name: cap["fn_name"].to_string(),
            body: cap["body"].trim().to_string(),
        });
    }

    let mut proofs = Vec::new();
    for cap in PROOF_RE.captures_iter(content) {
        proofs.push(ProofBlock { body: cap["body"].trim().to_string() });
    }

    Ok(ExtractedBlocks { specs, proofs })
}
