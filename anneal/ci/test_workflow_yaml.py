# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise shared YAML decoding independently of workflow field checks."""

import json
from pathlib import Path
import tempfile
import unittest

import yaml

from workflow_yaml import load_workflow_yaml


class WorkflowYamlTests(unittest.TestCase):
    def test_scalars_keep_their_lexical_values(self):
        self.assertEqual(
            load_workflow_yaml("on: off\nyes: no\nnull: ~\nnumber: 42\nflag: true\n"),
            {"on": "off", "yes": "no", "null": "~", "number": "42", "flag": "true"},
        )

    def test_decoding_leaves_workflow_shape_validation_to_consumers(self):
        self.assertEqual(load_workflow_yaml("[1, 2]\n"), ["1", "2"])
        self.assertEqual(load_workflow_yaml("uses: 42\n"), {"uses": "42"})
        self.assertIsNone(load_workflow_yaml(""))

    def test_anchors_share_decoded_values_without_cycles(self):
        decoded = load_workflow_yaml(
            "events: &events [push, pull_request]\n"
            "on: *events\n"
            "first: &step {uses: owner/action@abc}\n"
            "second: *step\n"
        )
        self.assertEqual(decoded["on"], ["push", "pull_request"])
        self.assertIs(decoded["on"], decoded["events"])
        self.assertIs(decoded["first"], decoded["second"])

    def test_duplicate_keys_fail_at_every_mapping_depth(self):
        for text in (
            "on: push\non: pull_request\n",
            "jobs: {build: {}, build: {}}\n",
            "step: {uses: owner/action@v1, uses: owner/action@v2}\n",
            "x: &key jobs\n*key: one\njobs: two\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "duplicate workflow key"):
                    load_workflow_yaml(text)

    def test_sequence_and_mapping_keys_fail_with_focused_errors(self):
        for text in ("? [a, b]\n: value\n", "? {a: b}\n: value\n"):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "keys must be scalars"):
                    load_workflow_yaml(text)

    def test_merge_keys_are_rejected_even_when_quoted(self):
        for text in (
            "base: &base {uses: owner/action@v1}\nstep: {<<: *base}\n",
            "step: {'<<': {uses: owner/action@v1}}\n",
            "step: {\"<<\": {uses: owner/action@v1}}\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "merge keys"):
                    load_workflow_yaml(text)

    def test_yaml_parser_rejects_direct_and_indirect_cycles(self):
        for text in (
            "value: &cycle [*cycle]\n",
            "value: &cycle {back: *cycle}\n",
            "value: &cycle [{back: *cycle}]\n",
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(yaml.YAMLError, "recursive node"):
                    load_workflow_yaml(text)

    def test_python_tags_cannot_construct_objects_or_execute_payloads(self):
        with tempfile.TemporaryDirectory(prefix="anneal-yaml-tags-") as directory:
            sentinel = Path(directory) / "executed"
            payload = f"__import__('pathlib').Path({str(sentinel)!r}).touch()"
            text = (
                "value: !!python/object/apply:builtins.eval\n"
                f"  - {json.dumps(payload)}\n"
            )
            self.assertEqual(load_workflow_yaml(text), {"value": [payload]})
            self.assertFalse(sentinel.exists())
        self.assertEqual(
            load_workflow_yaml("value: !!python/name:os.system ''\n"),
            {"value": ""},
        )

    def test_malformed_yaml_and_multiple_documents_are_rejected(self):
        for text in ("on: [\n", "on: push\n---\non: pull_request\n"):
            with self.subTest(text=text):
                with self.assertRaises(yaml.YAMLError):
                    load_workflow_yaml(text)


if __name__ == "__main__":
    unittest.main()
