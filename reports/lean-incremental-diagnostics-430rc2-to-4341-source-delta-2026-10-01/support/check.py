#!/usr/bin/env python3
"""Check exact Lean source evidence only; never builds or launches Lean."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess

OLD = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
NEW = "5045d0056413266e57c625dcd7c365b10e377c52"
BLOBS = {
    "src/Lean/Data/Lsp/Capabilities.lean": ("886e54140b4571bfc1e6b28fcb75ad196df0199e", "12eec11b4270702ec13990fce25913b7f1c67ba4"),
    "src/Lean/Data/Lsp/Diagnostics.lean": ("d15c1ce80d3699be7a5d92ebf6cea6725c3a4b34", "9353793f7316dca0ba36b16a9fd6cec46e487441"),
    "src/Lean/Server/FileWorker.lean": ("c803034ed8810f13a5ef38a603a21e610efca2bc", "cf8058ac800a67394e26aa4752539ddd979877c1"),
    "src/Lean/Server/FileWorker/Utils.lean": ("824a52e3de861ffbdde9597078d7946cb0306436", "e46f44a1599800a6bd6bedb8db9729235d37f49e"),
}
FIXTURES = {
    "Open.lean": "d42fbf3d79611aa442bb233680e4f20af6848dc8f1f0c7be3c3dd4df22b5dcc7",
    "Edited.lean": "9caea97a94d2d9d37a3cb507278414674d173507a0ebf9db9e3c5024dc3ebfeb",
}

def git(root, *args):
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1")
    return subprocess.check_output(["git", *args], cwd=root, env=env).decode()

def require(text, needle):
    assert needle in text, f"missing expected source text: {needle}"

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, default=Path(os.environ["LEAN4_SOURCE_ROOT"]) if os.environ.get("LEAN4_SOURCE_ROOT") else None)
    args = parser.parse_args()
    root = args.source_root
    if root is None:
        parser.error("pass --source-root or set LEAN4_SOURCE_ROOT to a Lean 4 checkout")
    source = {}
    for path, (old_blob, new_blob) in BLOBS.items():
        for rev, expected in ((OLD, old_blob), (NEW, new_blob)):
            got = git(root, "rev-parse", f"{rev}:{path}").strip()
            assert got == expected, f"blob mismatch {rev}:{path}: {got}"
            source[(rev, path)] = git(root, "show", f"{rev}:{path}")
    old_caps = source[(OLD, "src/Lean/Data/Lsp/Capabilities.lean")]
    new_caps = source[(NEW, "src/Lean/Data/Lsp/Capabilities.lean")]
    old_diag = source[(OLD, "src/Lean/Data/Lsp/Diagnostics.lean")]
    new_diag = source[(NEW, "src/Lean/Data/Lsp/Diagnostics.lean")]
    old_worker = source[(OLD, "src/Lean/Server/FileWorker.lean")]
    new_worker = source[(NEW, "src/Lean/Server/FileWorker.lean")]
    new_utils = source[(NEW, "src/Lean/Server/FileWorker/Utils.lean")]
    assert "incrementalDiagnosticSupport?" not in old_caps
    require(new_caps, "incrementalDiagnosticSupport? : Option Bool := none")
    require(new_caps, "def ClientCapabilities.incrementalDiagnosticSupport")
    assert "isIncremental? : Option Bool" not in old_diag
    require(new_diag, "isIncremental? : Option Bool := none")
    require(old_worker, "stickyInteractiveDiagnostics ++ docInteractiveDiagnostics")
    require(old_worker, "mkPublishDiagnosticsNotification doc.meta diagnostics")
    require(new_worker, "ctx.initParams.capabilities.incrementalDiagnosticSupport")
    require(new_worker, "doc.publishDiagnostics supportsIncremental")
    for needle in (
        "isIncremental : Bool := false",
        "publishedDiagsAmount : Nat := 0",
        "set { ds with isIncremental := false }",
        "let useIncremental := incrementalDiagnosticSupport && ds.isIncremental",
        "(newDiags, true)",
        "(allDiags, false)",
        "if incrementalDiagnosticSupport then",
        "some isIncremental",
        "doc.diagnosticsMutex.atomically do",
    ):
        require(new_utils, needle)
    fixture_dir = Path(__file__).resolve().parents[1] / "fixture"
    for name, expected in FIXTURES.items():
        got = hashlib.sha256((fixture_dir / name).read_bytes()).hexdigest()
        assert got == expected, f"fixture mismatch {name}: {got}"
    print("PASS: exact source blobs, diagnostic branches, and unexecuted fixture bytes")

if __name__ == "__main__":
    main()
