// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Parser-backed preconditions for the canonical workflow source scanner.

use std::{ffi::CStr, marker::PhantomData, mem::MaybeUninit};

use libyaml_rs::{
    yaml_event_delete, yaml_event_t, yaml_parser_delete, yaml_parser_initialize, yaml_parser_parse,
    yaml_parser_set_encoding, yaml_parser_set_input_string, yaml_parser_t, YAML_ALIAS_EVENT,
    YAML_BLOCK_MAPPING_STYLE, YAML_BLOCK_SEQUENCE_STYLE, YAML_DOCUMENT_END_EVENT,
    YAML_DOCUMENT_START_EVENT, YAML_DOUBLE_QUOTED_SCALAR_STYLE, YAML_FLOW_MAPPING_STYLE,
    YAML_FLOW_SEQUENCE_STYLE, YAML_FOLDED_SCALAR_STYLE, YAML_LITERAL_SCALAR_STYLE,
    YAML_MAPPING_END_EVENT, YAML_MAPPING_START_EVENT, YAML_PLAIN_SCALAR_STYLE, YAML_SCALAR_EVENT,
    YAML_SEQUENCE_END_EVENT, YAML_SEQUENCE_START_EVENT, YAML_SINGLE_QUOTED_SCALAR_STYLE,
    YAML_STREAM_END_EVENT, YAML_STREAM_START_EVENT, YAML_UTF8_ENCODING,
};

use crate::workflow_protocol::MATRIX_STEP_ANCHORS;

#[derive(Debug)]
pub(super) struct Violation {
    pub line: Option<usize>,
    pub message: &'static str,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CollectionKind {
    Mapping,
    Sequence,
}

struct OpenCollection {
    kind: CollectionKind,
    flow: bool,
    line: usize,
}

/// Rejects YAML constructs which can make source indentation misleading.
///
/// The bridge audit intentionally scans a small, canonical block-style source
/// grammar. YAML normally permits quoted and plain scalars, flow mappings, and
/// flow sequences to continue across line boundaries while ignoring block
/// indentation. Without this precondition, text inside one of those nodes can
/// look exactly like an audited job, field, or step even though Actions sees
/// only inert scalar text or a child of an unrelated flow collection.
///
/// Literal and folded block scalars remain multiline because their content is
/// bounded by indentation. Block mappings and sequences likewise retain
/// YAML's indentation structure. Flow nodes remain available in their ordinary
/// single-line form, such as a canonical `needs: [first, second]` value.
pub(super) fn require_line_local_flow_nodes(source: &str) -> Result<(), Violation> {
    let Some(mut parser) = EventParser::new(source.as_bytes()) else {
        return Err(Violation {
            line: None,
            message: "could not initialize the YAML parser for the canonical source audit",
        });
    };
    let mut collections = Vec::new();
    let mut documents = 0;

    loop {
        let mut event = MaybeUninit::<yaml_event_t>::uninit();
        // SAFETY: `EventParser` owns a successfully initialized parser whose
        // input bytes remain borrowed for its complete lifetime. On success,
        // libyaml fully initializes `event`; each such event is deleted once
        // after the fields needed below have been copied. On failure, no event
        // fields are read or deleted, and the parser's `Drop` still releases
        // all parser-owned allocations.
        let parsed = unsafe { yaml_parser_parse(parser.raw_mut(), event.as_mut_ptr()) };
        if parsed.fail {
            return Err(Violation {
                line: parser.problem_line(),
                message: "workflow must be valid YAML before its canonical source is audited",
            });
        }
        // SAFETY: the successful parse above initialized the complete event.
        let mut event = unsafe { event.assume_init() };
        let event_type = event.type_;
        let start_line = mark_line(event.start_mark.line);
        let end_line = mark_line(event.end_mark.line);

        let violation = match event_type {
            YAML_DOCUMENT_START_EVENT => {
                documents += 1;
                None
            }
            YAML_SCALAR_EVENT => {
                // SAFETY: libyaml's event tag proves that the scalar union arm
                // is active until `yaml_event_delete` below.
                let scalar = unsafe { event.data.scalar };
                if let Some(violation) =
                    node_property_violation(scalar.anchor, scalar.tag, start_line)
                {
                    Some(violation)
                } else if start_line == end_line {
                    None
                } else {
                    match scalar.style {
                        YAML_LITERAL_SCALAR_STYLE | YAML_FOLDED_SCALAR_STYLE => None,
                        YAML_PLAIN_SCALAR_STYLE
                        | YAML_SINGLE_QUOTED_SCALAR_STYLE
                        | YAML_DOUBLE_QUOTED_SCALAR_STYLE => Some(Violation {
                            line: Some(start_line),
                            message: "plain and quoted YAML scalars must stay on one source line so canonical indentation cannot be borrowed from scalar text",
                        }),
                        _ => Some(Violation {
                            line: Some(start_line),
                            message: "the canonical source audit does not recognize this multiline YAML scalar style",
                        }),
                    }
                }
            }
            YAML_MAPPING_START_EVENT => {
                // SAFETY: this event tag activates the mapping-start arm.
                let mapping = unsafe { event.data.mapping_start };
                if let Some(violation) =
                    node_property_violation(mapping.anchor, mapping.tag, start_line)
                {
                    Some(violation)
                } else {
                    match mapping.style {
                        YAML_BLOCK_MAPPING_STYLE | YAML_FLOW_MAPPING_STYLE => {
                            collections.push(OpenCollection {
                                kind: CollectionKind::Mapping,
                                flow: mapping.style == YAML_FLOW_MAPPING_STYLE,
                                line: start_line,
                            });
                            None
                        }
                        _ => Some(Violation {
                            line: Some(start_line),
                            message: "the canonical source audit does not recognize this YAML mapping style",
                        }),
                    }
                }
            }
            YAML_SEQUENCE_START_EVENT => {
                // SAFETY: this event tag activates the sequence-start arm.
                let sequence = unsafe { event.data.sequence_start };
                if let Some(violation) =
                    node_property_violation(sequence.anchor, sequence.tag, start_line)
                {
                    Some(violation)
                } else {
                    match sequence.style {
                        YAML_BLOCK_SEQUENCE_STYLE | YAML_FLOW_SEQUENCE_STYLE => {
                            collections.push(OpenCollection {
                                kind: CollectionKind::Sequence,
                                flow: sequence.style == YAML_FLOW_SEQUENCE_STYLE,
                                line: start_line,
                            });
                            None
                        }
                        _ => Some(Violation {
                            line: Some(start_line),
                            message: "the canonical source audit does not recognize this YAML sequence style",
                        }),
                    }
                }
            }
            YAML_MAPPING_END_EVENT => close_collection(
                &mut collections,
                CollectionKind::Mapping,
                start_line,
                "flow mappings must stay on one source line so canonical indentation remains structural",
            ),
            YAML_SEQUENCE_END_EVENT => close_collection(
                &mut collections,
                CollectionKind::Sequence,
                start_line,
                "flow sequences must stay on one source line so canonical indentation remains structural",
            ),
            YAML_ALIAS_EVENT => {
                // SAFETY: this event tag activates the alias arm, whose
                // anchor remains allocated until the event is deleted.
                let anchor = unsafe { event.data.alias.anchor };
                (!reviewed_anchor(anchor)).then_some(Violation {
                    line: Some(start_line),
                    message: "only the reviewed matrix step aliases may appear in the canonical workflow source",
                })
            }
            YAML_STREAM_START_EVENT | YAML_STREAM_END_EVENT | YAML_DOCUMENT_END_EVENT => None,
            _ => Some(Violation {
                line: Some(start_line),
                message: "the canonical source audit does not recognize this YAML parser event",
            }),
        };

        // SAFETY: this event was initialized successfully and has not been
        // deleted or moved into libyaml. No union field is read afterward.
        unsafe { yaml_event_delete(&raw mut event) };
        if let Some(violation) = violation {
            return Err(violation);
        }
        if event_type == YAML_STREAM_END_EVENT {
            if !collections.is_empty() {
                return Err(Violation {
                    line: None,
                    message: "YAML parser returned unclosed collection boundaries",
                });
            }
            return (documents == 1).then_some(()).ok_or(Violation {
                line: None,
                message: "the canonical workflow source must contain exactly one YAML document",
            });
        }
    }
}

fn node_property_violation(anchor: *const u8, tag: *const u8, line: usize) -> Option<Violation> {
    if !tag.is_null() {
        return Some(Violation {
            line: Some(line),
            message: "explicit YAML tags are not supported by the canonical workflow source",
        });
    }
    (!anchor.is_null() && !reviewed_anchor(anchor)).then_some(Violation {
        line: Some(line),
        message:
            "only the reviewed matrix step anchors may appear in the canonical workflow source",
    })
}

fn reviewed_anchor(anchor: *const u8) -> bool {
    if anchor.is_null() {
        return false;
    }
    // SAFETY: libyaml supplies every non-null anchor as a NUL-terminated byte
    // string owned by the current event. Callers invoke this helper before
    // deleting that event, and the bytes are only compared, never retained.
    let anchor = unsafe { CStr::from_ptr(anchor.cast()) }.to_bytes();
    MATRIX_STEP_ANCHORS.iter().any(|reviewed| anchor == reviewed.as_bytes())
}

fn close_collection(
    collections: &mut Vec<OpenCollection>,
    expected: CollectionKind,
    end_line: usize,
    message: &'static str,
) -> Option<Violation> {
    let Some(open) = collections.pop() else {
        return Some(Violation {
            line: Some(end_line),
            message: "YAML parser returned an unmatched collection boundary",
        });
    };
    if open.kind != expected {
        return Some(Violation {
            line: Some(end_line),
            message: "YAML parser returned mismatched collection boundaries",
        });
    }
    (open.flow && open.line != end_line).then_some(Violation { line: Some(open.line), message })
}

fn mark_line(line: u64) -> usize {
    usize::try_from(line).unwrap_or(usize::MAX - 1).saturating_add(1)
}

/// A pinned-by-allocation libyaml parser borrowing `source`.
///
/// `yaml_parser_set_input_string` stores both the source pointer and a pointer
/// back to the parser. Keeping the parser in one `Box` allocation ensures that
/// moving this Rust wrapper never invalidates libyaml's self-reference.
struct EventParser<'source> {
    raw: Box<yaml_parser_t>,
    _source: PhantomData<&'source [u8]>,
}

impl<'source> EventParser<'source> {
    fn new(source: &'source [u8]) -> Option<Self> {
        let mut raw = Box::<yaml_parser_t>::new_uninit();
        // SAFETY: `raw` points to storage of the exact required type. A
        // successful call initializes it completely. `Box::assume_init`
        // preserves the allocation address before libyaml records that address
        // in `yaml_parser_set_input_string`.
        if unsafe { yaml_parser_initialize(raw.as_mut_ptr()) }.fail {
            return None;
        }
        // SAFETY: initialization succeeded immediately above.
        let mut raw = unsafe { raw.assume_init() };
        // SAFETY: the parser is initialized, its heap address is now stable,
        // and the lifetime marker prevents this wrapper from outliving source.
        unsafe {
            yaml_parser_set_encoding(&raw mut *raw, YAML_UTF8_ENCODING);
            yaml_parser_set_input_string(&raw mut *raw, source.as_ptr(), source.len() as u64);
        }
        Some(Self { raw, _source: PhantomData })
    }

    fn raw_mut(&mut self) -> *mut yaml_parser_t {
        &raw mut *self.raw
    }

    fn problem_line(&self) -> Option<usize> {
        Some(mark_line(self.raw.problem_mark.line))
    }
}

impl Drop for EventParser<'_> {
    fn drop(&mut self) {
        // SAFETY: construction returned `Some` only after successful
        // initialization, and this is the parser's single deletion point.
        unsafe { yaml_parser_delete(&raw mut *self.raw) }
    }
}

#[cfg(test)]
mod tests {
    use super::require_line_local_flow_nodes;

    const LIVE_WORKFLOW: &str = include_str!("../../../../.github/workflows/ci.yml");

    fn rejected(source: &str, expected: &str) {
        let error = require_line_local_flow_nodes(source).unwrap_err();
        assert!(error.message.contains(expected), "unexpected violation: {}", error.message);
    }

    #[test]
    fn live_workflow_uses_only_line_local_flow_nodes() {
        require_line_local_flow_nodes(LIVE_WORKFLOW).unwrap();
    }

    #[test]
    fn multiline_flow_scalars_are_rejected_but_block_scalars_remain_supported() {
        for source in [
            "value: first\n  second\n",
            "value: 'first\n  second'\n",
            "value: \"first\n  second\"\n",
        ] {
            rejected(source, "scalars must stay on one source line");
        }

        require_line_local_flow_nodes("value: |\n  first\n  second\n").unwrap();
        require_line_local_flow_nodes("value: >\n  first\n  second\n").unwrap();
    }

    #[test]
    fn multiline_flow_collections_are_rejected_without_scalar_decoys() {
        rejected("value: {first: one,\n  second: two}\n", "flow mappings must stay");
        rejected("value: [one,\n  two]\n", "flow sequences must stay");
        rejected("value: [{first: one,\n  second: two}]\n", "flow mappings must stay");

        require_line_local_flow_nodes("value: {first: one, second: two}\n").unwrap();
        require_line_local_flow_nodes("value: [one, two]\n").unwrap();
    }

    #[test]
    fn exactly_one_yaml_document_is_required() {
        rejected("first: document\n---\nsecond: document\n", "exactly one YAML document");
    }

    #[test]
    fn only_reviewed_matrix_anchors_and_aliases_are_supported() {
        rejected("value: &replay_planner text\n", "reviewed matrix step anchors");
        rejected(
            "first: &matrix_checkout value\nsecond: *replay_planner\n",
            "reviewed matrix step aliases",
        );

        require_line_local_flow_nodes(
            "first: &matrix_checkout {value: one}\nsecond: *matrix_checkout\n",
        )
        .unwrap();
    }

    #[test]
    fn explicit_tags_are_rejected() {
        rejected("value: !!str text\n", "explicit YAML tags");
        rejected("value: !!map {first: one}\n", "explicit YAML tags");
    }
}
