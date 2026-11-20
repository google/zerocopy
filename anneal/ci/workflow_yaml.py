# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Decode workflow YAML into strings, lists, and string-keyed mappings.

The field checkers inspect this data; action-validator validates the workflow
schema. BaseLoader preserves names such as unquoted `on` and constructs only
strings and collection containers, including for Python-specific YAML tags.
"""

import yaml


class _WorkflowLoader(yaml.BaseLoader):
    def construct_mapping(self, node, deep=False):
        result = {}
        for key_node, value_node in node.value:
            key = self.construct_object(key_node, deep=deep)
            if not isinstance(key, str):
                raise yaml.YAMLError("workflow mapping keys must be scalars")
            # BaseLoader treats merge keys as ordinary fields. Reject them so
            # inherited events, dependencies, or Action references cannot hide
            # from checks that inspect the decoded mapping.
            if key == "<<":
                raise yaml.YAMLError("workflow YAML merge keys are unsupported")
            # Last-key-wins parsing can make separate checks disagree about
            # the same security-relevant field. Reject the ambiguity itself.
            if key in result:
                raise yaml.YAMLError(f"duplicate workflow key: {key}")
            result[key] = self.construct_object(value_node, deep=deep)
        return result


def load_workflow_yaml(text):
    """Decode one document, rejecting ambiguous keys and recursive aliases."""
    return yaml.load(text, Loader=_WorkflowLoader)
