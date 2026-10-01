# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Keep generated output timestamps stable when its bytes have not changed.

Local Lean builds use those timestamps to decide what to recompile. Generation
must still compute the whole output; this helper only avoids rewriting identical
bytes. It never caches a verification result. CI replaces its proof projects and
rebuilds their mutable sources independently of these timestamps.
"""


def write_bytes(path, contents):
    if not path.is_file() or path.read_bytes() != contents:
        path.write_bytes(contents)


def write_text(path, contents):
    write_bytes(path, contents.encode('utf-8'))
