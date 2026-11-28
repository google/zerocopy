# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Standalone zero-dependency Lean 4 LSP helper package (`anneal-lsp`)."""

from .cli import SERVER_NAME, SERVER_VERSION, main
from .discovery import WorkspaceContext, discover_workspace, find_lean_binary
from .workspace import WorkspacePool

__all__ = [
    "SERVER_NAME",
    "SERVER_VERSION",
    "WorkspaceContext",
    "WorkspacePool",
    "discover_workspace",
    "find_lean_binary",
    "main",
]
