#!/usr/bin/env python3
"""Temporary native validation; run only in the reviewed ephemeral checkout."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess

root = Path.cwd()
evidence = root / "validation-evidence"
evidence.mkdir(exist_ok=False)
flake = root / "anneal/flake.nix"
ref = "path:" + str(flake.parent)
system = os.environ["EXPECTED_SYSTEM"]
report = {"system": system, "validated": False, "hashes": {}}
counter = 0

def save():
    (evidence / "hashes.json").write_text(json.dumps(report, indent=2) + "\n")

def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

def mathlib_manifest(store):
    destination, count = evidence / "mathlib-download-manifest.jsonl", 0
    with destination.open("w") as stream:
        for directory, dirs, files in os.walk(store, followlinks=False):
            dirs.sort()
            for name in sorted(dirs + files):
                path = Path(directory) / name
                mode = path.lstat().st_mode
                entry = {"path": path.relative_to(store).as_posix(), "mode": oct(stat.S_IMODE(mode))}
                if stat.S_ISREG(mode):
                    entry.update(type="file", sha256=file_hash(path), size=path.stat().st_size)
                elif stat.S_ISLNK(mode):
                    entry.update(type="symlink", target=os.readlink(path))
                else:
                    assert stat.S_ISDIR(mode), f"Unsupported FOD entry: {entry['path']}"
                    entry.update(type="directory")
                stream.write(json.dumps(entry, sort_keys=True) + "\n")
                count += 1
                assert count <= 250000 and stream.tell() <= 50 * 1024**2, "Manifest limit exceeded"
    report["mathlib_manifest"] = {"file": destination.name, "entries": count,
                                  "sha256": file_hash(destination), "bytes": destination.stat().st_size}

def run(args, *, cwd=root, env=None, allow_failure=False):
    global counter
    counter += 1
    print("RUN", args, flush=True)
    p = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=7200)
    (evidence / f"{counter:02d}.log").write_text(
        json.dumps(args) + "\n" + p.stdout + "\nSTDERR\n" + p.stderr)
    print(p.stdout + p.stderr, flush=True)
    if p.returncode and not allow_failure:
        raise RuntimeError(f"Command failed ({p.returncode}): {args}")
    return p

def evaluate(attr):
    return run(["nix", "eval", "--no-write-lock-file", "--raw", ref + "#" + attr]).stdout.strip()

def build(pkg):
    assert shutil.disk_usage(root).free > 3 * 1024**3, "Less than 3 GiB available; stopping"
    return run(["nix", "build", "--max-jobs", "2", "--cores", "2", "--no-write-lock-file", "--no-link", "--json", "-L",
                ref + "#" + pkg])

save()
report["commit"] = run(["git", "rev-parse", "HEAD"]).stdout.strip()
assert run(["nix", "eval", "--impure", "--raw", "--expr", "builtins.currentSystem"]).stdout.strip() == system
for pkg, pin in [("rust-toolchain", "rustToolchainSha256"),
                 ("lean-toolchain", "leanToolchainSha256"),
                 ("mathlib-cache-download", "mathlibCacheDownloadSha256")]:
    attr = f"packages.{system}.{pkg}"
    drv, expected = evaluate(attr + ".drvPath"), evaluate(attr + ".outputHash")
    # All four native hashes are known now. Let Nix enforce them directly;
    # build output can contain arbitrary diagnostic-looking filenames.
    p = build(pkg)
    output = json.loads(p.stdout)
    assert len(output) == 1
    store = output[0]["outputs"]["out"]
    actual = run(["nix", "hash", "path", "--type", "sha256", "--sri", store]).stdout.strip()
    assert actual == expected, (pkg, expected, actual)
    report["hashes"][pin] = {"original": expected, "actual": actual, "store": store,
                              "derivation": output[0]["drvPath"]}
    if pkg == "mathlib-cache-download":
        mathlib_manifest(Path(store))
    save()
(evidence / "flake-hashes.patch").write_text(run(["git", "diff", "--", "anneal/flake.nix"]).stdout)
archive = Path(json.loads(build("omnibus-archive-ci").stdout)[0]["outputs"]["out"])
report["archive_store"] = str(archive)
build("omnibus-archive-layout-check")
report["archive_sha256"] = file_hash(archive)
unpacked = root / "validation-unpacked"
unpacked.mkdir()
utilities = {}
for name in ["gnutar", "zstd"]:
    expr = f'(builtins.getFlake "{ref}").inputs.nixpkgs.legacyPackages.{system}.{name}'
    p = run(["nix", "build", "--impure", "--no-link", "--json", "--expr", expr])
    utilities[name] = Path(json.loads(p.stdout)[0]["outputs"]["bin" if name == "zstd" else "out"])
run([str(utilities["gnutar"] / "bin/tar"),
     "--use-compress-program=" + str(utilities["zstd"] / "bin/zstd"),
     "-xf", str(archive), "-C", str(unpacked)])
bundle = root / "validation-relocated/bundle"
bundle.parent.mkdir()
unpacked.rename(bundle)
metadata = json.loads((bundle / "aeneas/metadata.json").read_text())
assert metadata["aeneas-revision"] == "ca282ec2312a96f6a985a4d23a663690816d3f3e"
assert metadata["rust-toolchain-version"] == "nightly-2026-09-17"
assert metadata["lean-toolchain"] == "4.31.0"
report["metadata"] = metadata
env = dict(os.environ, CHARON_TOOLCHAIN_IS_IN_PATH="1", MATHLIB_NO_CACHE_ON_UPDATE="1", LEAN_NUM_THREADS="2")
env["PATH"] = f"{bundle}/rust/bin:{bundle}/lean/bin:{bundle}/aeneas/bin:" + env["PATH"]
env["LEAN_SYSROOT"] = str(bundle / "lean")
libvar = "DYLD_LIBRARY_PATH" if system.endswith("darwin") else "LD_LIBRARY_PATH"
env[libvar] = f"{bundle}/rust/lib:{bundle}/lean/lib:{bundle}/lean/lib/lean"
for command in [["rustc", "--version"], ["lean", "--version"], ["charon", "version"],
                ["charon", "toolchain-version"], ["aeneas", "-version"]]:
    report.setdefault("versions", []).append(run(command, env=env).stdout.strip())
assert "4.31.0" in report["versions"][1]
assert metadata["charon-revision"][:7] in report["versions"][2]
assert report["versions"][3] == metadata["rust-toolchain-version"]
assert (metadata["aeneas-release"] in report["versions"][4] or
        metadata["aeneas-revision"][:7] in report["versions"][4])
save()
smoke = bundle.parent / "smoke"
(smoke / "src").mkdir(parents=True)
(smoke / "generated/Smoke").mkdir(parents=True)
(smoke / "Cargo.toml").write_text('[package]\nname="smoke"\nversion="0.0.0"\nedition="2021"\n')
(smoke / "src/lib.rs").write_text("pub fn identity(x: u32) -> u32 { x }\n")
run(["cargo", "generate-lockfile", "--offline"], cwd=smoke, env=env)
run(["charon", "cargo", "--preset=aeneas", "--start-from", "smoke::identity",
     "--dest-file", str(smoke / "smoke.llbc"), "--abort-on-error", "--error-on-warnings",
     "--", "--lib", "--locked", "--offline"], cwd=smoke, env=env)
run(["aeneas", "-backend", "lean", "-namespace", "Smoke", "-dest", str(smoke / "generated/Smoke"),
     "-split-files", "-abort-on-error", "-warnings-as-errors", "-no-progress-bar",
     str(smoke / "smoke.llbc")], cwd=smoke, env=env)
(smoke / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
(smoke / "lakefile.lean").write_text('import Lake\nopen Lake DSL\n'
    'require aeneas from "../bundle/aeneas/backends/lean"\n'
    'require rust_model from "../bundle/rust-model"\npackage smoke\n'
    '@[default_target]\nlean_lib Generated where\n  srcDir := "generated"\n  roots := #[`SmokeProof, `Smoke.Funs, `Smoke.Types]\n')
(smoke / "generated/SmokeProof.lean").write_text('import Smoke.Funs\nimport Rust\n'
    'theorem smoke_identity_spec (x : Aeneas.Std.U32) : Smoke.identity x = .ok x := by rfl\n'
    '#print axioms smoke_identity_spec\n')
run(["lake", "--keep-toolchain", "--old", "build", "Generated"], cwd=smoke, env=env)
proof = run(["lake", "--keep-toolchain", "env", "lean", "-DwarningAsError=true",
             "generated/SmokeProof.lean"], cwd=smoke, env=env)
audit = re.fullmatch(r"'smoke_identity_spec' depends on axioms: \[([^\]\n]*)\]", proof.stdout.strip())
assert audit, proof.stdout
report["proof_axioms"] = [name.strip() for name in audit[1].split(",") if name.strip()]
assert set(report["proof_axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}, report["proof_axioms"]
for file in (smoke / "generated").rglob("*.lean"):
    assert not re.search(r"\b(sorry|axiom)\b", file.read_text()), file
report["validated"] = True
save()
