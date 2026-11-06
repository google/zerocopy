#!/usr/bin/env python3
"""Pinned diagnostic/provenance stage specimens, preserving raw artifacts."""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import select
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
FIX = HERE / "fixture"
ART = HERE / "artifacts"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin/rustc"
CHARON = TOOLS / "bin/charon"
AENEAS = TOOLS / "bin/aeneas"
LEAN = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"
LAKE = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake"
AENEAS_PROJECT = TOOLS / "aeneas-release/backends/lean"
AENEAS_LIB = TOOLS / "aeneas-release/backends/lean/.lake/build/lib/lean"
RESULT = HERE / "raw-results.json"
MANIFEST = HERE / "mapping-manifest.json"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def files(root):
    return {str(p.relative_to(root)): {"sha256": sha(p), "bytes": p.stat().st_size}
            for p in sorted(root.rglob("*")) if p.is_file()}


def execute(label, argv, cwd, env):
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env,
                       capture_output=True, text=True, timeout=30)
    return {"label": label, "argv": [str(x) for x in argv], "cwd": str(cwd),
            "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr}


def llbc_items(path):
    data = json.loads(path.read_text())
    return {"has_errors": data["has_errors"], "sha256": sha(path),
            "files": [{"id": f["id"], "name": f["name"],
                       "contents_sha256": hashlib.sha256(f["contents"].encode()).hexdigest()
                       if f.get("contents") is not None else None}
                      for f in data["translated"]["files"]],
            "functions": [{"id": item["def_id"],
                           "name": "::".join(part["Ident"][0] for part in item["item_meta"]["name"]
                                            if "Ident" in part),
                           "source_span": item["item_meta"].get("span", {}).get("data"),
                           "source_text": item["item_meta"].get("source_text")}
                          for item in data["translated"].get("fun_decls", [])
                          if item["item_meta"].get("is_local")]}


def lexical_edges(case, llbc, lean_dir):
    if not llbc:
        return []
    funs = lean_dir / "Funs.lean"
    text = funs.read_text() if funs.exists() else ""
    lines = text.splitlines()
    result = []
    for item in llbc["functions"]:
        suffix = item["name"].split("::")[-1]
        matches = [n for n, line in enumerate(lines, 1)
                   if re.match(r"^def\s+" + re.escape(suffix) + r"(?:\s|$)", line)]
        comments = [n for n, line in enumerate(lines, 1) if f"[{item['name']}]" in line]
        result.append({"case": case, "rust_item": item["name"], "llbc_def_id": item["id"],
                       "llbc_source_span": item["source_span"], "lean_path": str(funs.relative_to(ART)),
                       "candidate_lean_def_lines": matches, "candidate_origin_comment_lines": comments,
                       "edge_kind": "lexical printed-name/source-comment match; not compiler authenticated"})
    return result


def lsp_session(path, env):
    p = subprocess.Popen([str(LEAN), "--server"], cwd=path.parent, env=env,
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    messages = []
    buffer = b""
    next_id = 1

    def send(msg):
        raw = json.dumps(msg, ensure_ascii=False, separators=(",", ":")).encode()
        p.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        p.stdin.flush()
        messages.append({"direction": "client", "message": msg})

    def receive(predicate, seconds=12):
        nonlocal buffer
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            while b"\r\n\r\n" in buffer:
                header, tail = buffer.split(b"\r\n\r\n", 1)
                length = next((int(v.split(b":", 1)[1]) for v in header.split(b"\r\n")
                               if v.lower().startswith(b"content-length:")), None)
                if length is None or len(tail) < length:
                    break
                raw, buffer = tail[:length], tail[length:]
                msg = json.loads(raw)
                messages.append({"direction": "server", "message": msg})
                if msg.get("method") == "client/registerCapability" and "id" in msg:
                    send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
                if predicate(msg):
                    return msg
            ready, _, _ = select.select([p.stdout], [], [], min(.2, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(p.stdout.fileno(), 65536)
                if not chunk:
                    break
                buffer += chunk
        raise TimeoutError("Lean LSP response timed out")

    def request(method, params):
        nonlocal next_id
        rid = next_id
        next_id += 1
        send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        return receive(lambda msg: msg.get("id") == rid and "method" not in msg)

    source = path.read_text()
    uri = path.as_uri()
    try:
        initialize = request("initialize", {"processId": os.getpid(), "rootUri": path.parent.as_uri(),
                                            "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
        send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
        send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri, "languageId": "lean", "version": 1, "text": source}}})
        settled = request("textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
        request("shutdown", None)
        send({"jsonrpc": "2.0", "method": "exit"})
        p.wait(timeout=3)
        return {"argv": [str(LEAN), "--server"], "cwd": str(path.parent),
                "env_LEAN_PATH": env["LEAN_PATH"], "source_sha256": sha(path),
                "initialize": initialize, "settled": settled, "exit_code": p.returncode,
                "messages": messages, "stderr": p.stderr.read().decode(errors="replace")}
    finally:
        if p.poll() is None:
            p.kill()
            p.wait()


def main():
    if ART.exists():
        shutil.rmtree(ART)
    ART.mkdir()
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(RUST.parent), str(TOOLS / "bin"), env.get("PATH", "")])})
    records = {}
    llbcs = {}
    for case, source in (("A", "source-A.rs"), ("deleted", "source-deleted.rs"),
                         ("unsupported", "source-unsupported.rs"),
                         ("rustc-error", "source-rustc-error.rs"),
                         ("charon-coroutine", "charon-coroutine.rs")):
        dest = ART / case
        dest.mkdir()
        src = FIX / source
        rust_out = dest / "rustc.rmeta"
        rust = execute(case + ":rustc", [RUST, "--crate-type", "lib", "--crate-name", "snapshot_probe",
                                        "--edition", "2021", "--emit", "metadata", "-o", rust_out,
                                        "--error-format=json", src], HERE, env)
        charon_out = dest / "snapshot.llbc"
        charon = execute(case + ":charon", [CHARON, "rustc", "--preset", "aeneas",
                                            "--abort-on-error", "--dest-file", charon_out,
                                            "--", src, "--crate-type", "lib", "--crate-name",
                                            "snapshot_probe", "--edition", "2021"], HERE, env)
        llbc = llbc_items(charon_out) if charon_out.exists() else None
        if llbc:
            llbcs[case] = llbc
        records[case] = {"source": source, "source_sha256": sha(src), "rustc": rust,
                         "charon": charon, "llbc": llbc}
        if llbc:
            lean_dir = dest / "lean"
            lean_dir.mkdir()
            aeneas = execute(case + ":aeneas", [AENEAS, "-backend", "lean", "-no-progress-bar",
                                                  "-sequential", "-split-files", "-gen-lib-entry",
                                                  "-dest", lean_dir, charon_out], HERE, env)
            records[case]["aeneas"] = aeneas
            records[case]["lean_files"] = files(lean_dir)

    assert records["rustc-error"]["rustc"]["exit_code"] != 0
    assert records["rustc-error"]["charon"]["exit_code"] == 2
    assert records["charon-coroutine"]["rustc"]["exit_code"] == 0
    assert records["charon-coroutine"]["charon"]["exit_code"] != 0
    assert records["A"]["aeneas"]["exit_code"] == 0
    assert records["deleted"]["aeneas"]["exit_code"] == 0
    assert records["unsupported"]["aeneas"]["exit_code"] != 0

    # Preserve successful generated code and compile it in a private module tree.
    a_dir = ART / "A/lean"
    mod = ART / "lean-check/Snapshot"
    mod.mkdir(parents=True)
    for name in ("Types", "Funs"):
        shutil.copy2(a_dir / f"{name}.lean", mod / f"{name}.lean")
    proof = ART / "lean-check/Proof.lean"
    shutil.copy2(FIX / "Proof-error.lean", proof)
    project_lean_path = subprocess.check_output([str(LAKE), "env", "printenv", "LEAN_PATH"],
                                                cwd=AENEAS_PROJECT, env=env, text=True).strip()
    lean_env = dict(env, LEAN_NUM_THREADS="1", LEAN_PATH=os.pathsep.join([project_lean_path, str(mod.parent)]))
    lean_records = []
    for name in ("Types", "Funs"):
        lean_records.append(execute(name + ":lean-build", [LEAN, "-o", mod / f"{name}.olean",
                            mod / f"{name}.lean"], mod.parent, lean_env))
    assert all(x["exit_code"] == 0 for x in lean_records), lean_records
    lean_batch = execute("proof:lean-json", [LEAN, "--json", proof], proof.parent, lean_env)
    assert lean_batch["exit_code"] != 0, lean_batch
    server = lsp_session(proof, lean_env)

    original = llbcs["A"]["functions"]
    remaining = llbcs["deleted"]["functions"]
    old_names = {f["name"] for f in original}
    new_names = {f["name"] for f in remaining}
    assert "snapshot_probe::select" in old_names - new_names
    new_funs = (ART / "deleted/lean/Funs.lean").read_text()
    assert "def select" not in new_funs
    unsupported_funs = (ART / "unsupported/lean/Funs.lean").read_text()
    assert "sorry" in unsupported_funs

    rust_diags = [json.loads(x) for x in records["rustc-error"]["rustc"]["stderr"].splitlines()
                  if x.startswith("{")]
    lean_diags = [json.loads(x) for x in lean_batch["stdout"].splitlines() if x.startswith("{")]
    lsp_diags = [m["message"] for m in server["messages"] if m["direction"] == "server"
                 and m["message"].get("method") == "textDocument/publishDiagnostics"]
    proof_line = proof.read_text().splitlines()[3]
    rfl_scalar = proof_line.index("rfl")
    rfl_utf16 = len(proof_line[:rfl_scalar].encode("utf-16-le")) // 2
    rfl_utf8 = len(proof_line[:rfl_scalar].encode("utf-8"))
    final_lsp = next(d for event in lsp_diags for d in event["params"]["diagnostics"]
                     if "Tactic `rfl` failed" in d["message"])
    assert lean_diags[0]["pos"] == {"line": 4, "column": rfl_scalar}
    assert final_lsp["range"]["start"] == {"line": 3, "character": rfl_utf16}
    rust_source = (FIX / "source-rustc-error.rs").read_text()
    rust_line = rust_source.splitlines()[1]
    marker_scalar = rust_line.rfind("marker")
    rust_primary = next(span for diag in rust_diags if diag.get("level") == "error"
                        for span in diag.get("spans", []) if span.get("is_primary"))
    assert rust_primary["column_start"] == marker_scalar + 1
    assert rust_primary["byte_start"] == len((rust_source.splitlines()[0] + "\n").encode()) + len(rust_line[:marker_scalar].encode())
    mappings = {"edge_authentication": "Only LLBC internal item/file/span references are serialized Charon data. Rust-to-Lean declaration candidates below are lexical matches, not compiler-authenticated mappings.",
                "first_failure_stage": {"A": None, "deleted": None, "rustc-error": "rustc",
                                        "charon-coroutine": "charon", "unsupported": "aeneas",
                                        "proof-error-from-A": "lean"},
                "coordinate_observations": {"rustc_json": {"line_basis": "one-based", "column_basis_observed": "one-based Unicode scalar in this fixture", "absolute_byte_offset": rust_primary["byte_start"], "column_start": rust_primary["column_start"], "marker_scalar_index_zero_based": marker_scalar},
                                            "lean_batch": {"line_basis": "one-based", "column_basis_observed": "zero-based Unicode scalar offset in this fixture", "raw_position": lean_diags[0]["pos"]},
                                            "lean_lsp": {"line_basis": "zero-based", "character_basis_observed": "UTF-16 code units in this fixture", "raw_start": final_lsp["range"]["start"]},
                                            "proof_rfl_prefix": {"unicode_scalars": rfl_scalar, "utf16_code_units": rfl_utf16, "utf8_bytes": rfl_utf8}},
                "rustc_error": {"source_sha256": records["rustc-error"]["source_sha256"],
                                "structured_diagnostics": rust_diags},
                "charon_coroutine": {"rustc_exit": records["charon-coroutine"]["rustc"]["exit_code"],
                                     "charon_exit": records["charon-coroutine"]["charon"]["exit_code"],
                                     "charon_stderr": records["charon-coroutine"]["charon"]["stderr"]},
                "aeneas_unsupported": {"charon_llbc": llbcs["unsupported"],
                                       "aeneas_exit": records["unsupported"]["aeneas"]["exit_code"],
                                       "generated_funs_sha256": sha(ART / "unsupported/lean/Funs.lean"),
                                       "contains_sorry": True},
                "lean_error": {"batch_json": lean_diags, "lsp_publish_diagnostics": lsp_diags,
                               "lsp_settled": server["settled"], "proof_sha256": sha(proof)},
                "A_to_deleted": {"removed_llbc_names": sorted(old_names - new_names),
                                 "old_llbc": llbcs["A"], "new_llbc": llbcs["deleted"],
                                 "deleted_generated_inventory": records["deleted"]["lean_files"]},
                "candidate_edges": lexical_edges("A", llbcs["A"], ART / "A/lean")
                                   + lexical_edges("deleted", llbcs["deleted"], ART / "deleted/lean")
                                   + lexical_edges("unsupported", llbcs["unsupported"], ART / "unsupported/lean")}
    result = {"environment": {"platform": platform.platform(), "python": sys.version,
                              "tools": {name: {"path": str(path), "sha256": sha(path)}
                                        for name, path in (("rustc", RUST), ("charon", CHARON),
                                                           ("aeneas", AENEAS), ("lean", LEAN))},
                              "aeneas_lean_library_path": str(AENEAS_LIB),
                              "aeneas_olean_sha256": sha(AENEAS_LIB / "Aeneas.olean"),
                              "project_lean_path": project_lean_path,
                              "fixture_hashes": files(FIX), "script_sha256": sha(__file__)},
              "cases": records, "lean_build": lean_records, "lean_batch": lean_batch,
              "lean_server": server, "artifact_inventory": files(ART)}
    RESULT.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    MANIFEST.write_text(json.dumps(mappings, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"stage_exits": {k: {stage: r[stage]["exit_code"] for stage in ("rustc", "charon", "aeneas") if stage in r}
                                      for k, r in records.items()},
                      "lean_batch_exit": lean_batch["exit_code"], "lean_lsp_events": len(lsp_diags),
                      "removed": sorted(old_names-new_names)}, sort_keys=True))


if __name__ == "__main__":
    main()
