#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"
LEAN="${LEAN:-lean}"
trap 'rm -f SingleSourceCodegen.olean SingleSourceCodegen.ilean Prog_tampered.s test_bin' EXIT

echo "=== 1. Kernel-Typecheck SingleSourceCodegen.lean and Emit .olean ==="
"$LEAN" -DElab.async=false -Ddebug.skipKernelTC=false \
  -o SingleSourceCodegen.olean SingleSourceCodegen.lean

echo "=== 2. Emit Prog.s Directly from Trusted.emitX86CrateAsm Prog.x86Crate ==="
LEAN_PATH="." "$LEAN" -DElab.async=false -Ddebug.skipKernelTC=false \
  --run AuditMain.lean emit Prog.s

echo "=== 3. Audit Genuine Prog.s Against SingleSourceCodegen.olean ==="
LEAN_PATH="." "$LEAN" -DElab.async=false -Ddebug.skipKernelTC=false \
  --run AuditMain.lean audit . Prog.s

echo "=== 4. Audit Tampered Prog_tampered.s (Simulating Shadow-Artifact Drift) ==="
sed 's/add rax, rcx/sub rax, rcx/' Prog.s > Prog_tampered.s
if LEAN_PATH="." "$LEAN" -DElab.async=false -Ddebug.skipKernelTC=false \
  --run AuditMain.lean audit . Prog_tampered.s 2>&1; then
  echo "ERROR: tampered Prog.s was unexpectedly accepted!"
  exit 1
else
  echo "expected rejection of tampered Prog_tampered.s confirmed."
fi

echo "=== 5. Assemble Genuine Prog.s with cc and Execute on x86-64 CPU ==="
cc -O2 main.c Prog.s -o test_bin
./test_bin
