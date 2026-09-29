#!/usr/bin/env python3
"""Read-only validation of retained Anneal resolver and Cargo controls."""
import hashlib
import json
from pathlib import Path

support = Path(__file__).resolve().parent
report = support.parent
metadata = json.loads((report / "REPORT.json").read_text())
environment = json.loads((support / "environment.json").read_text())
commands = json.loads((support / "commands.json").read_text())
build_commands = json.loads((support / "build-commands.json").read_text())
manifest = json.loads((support / "artifacts.sha256.json").read_text())

def sha(data):
    return hashlib.sha256(data).hexdigest()

for name, digest in manifest.items():
    assert sha((support / name).read_bytes()) == digest, name

source_hash = sha((support / "harness/src/resolve.rs").read_bytes())
subject = metadata["subjects"][0]["identity"]
assert subject["revision"] == environment["source"]["revision"]
assert source_hash == subject["sha256"] == environment["source"]["sha256"]

fixture = support / "fixture"
fixture_rows = [
    f"{path.relative_to(fixture).as_posix()}\0{sha(path.read_bytes())}"
    for path in sorted(fixture.rglob("*")) if path.is_file()
]
fixture_hash = sha(("\n".join(fixture_rows) + "\n").encode())
assert fixture_hash == metadata["subjects"][1]["identity"]["fixture_tree_sha256"]
assert fixture_hash == environment["fixture_tree_sha256"]

expected_cases = {
    "root_default", "workspace", "alpha_lib", "alpha_bins",
    "alpha_bins_feature", "alpha_tests", "alpha_dir_default", "beta_default",
    "cargo_metadata", "cargo_default", "cargo_workspace", "cargo_alpha_bins",
    "cargo_alpha_bins_feature", "cargo_alpha_tests",
}
assert set(commands) == expected_cases
assert set(build_commands) == {"harness_lock", "harness_build"}
for name, command in build_commands.items():
    assert command["exit_code"] == 0
    assert command["argv"][0] == "$CARGO_HOME/bin/cargo"
    assert "--offline" in command["argv"]
    assert (support / command["stdout_file"]).is_file()
    assert (support / command["stderr_file"]).is_file()
assert "--locked" in build_commands["harness_build"]["argv"]
for name, command in commands.items():
    assert command["exit_code"] == 0, name
    assert command["stdout_file"] == f"raw/{name}.stdout"
    assert command["stderr_file"] == f"raw/{name}.stderr"
    assert (support / command["stdout_file"]).is_file(), name
    assert (support / command["stderr_file"]).is_file(), name
    if name.startswith("cargo_") and name != "cargo_metadata":
        assert "--offline" in command["argv"] and "--locked" in command["argv"], name
assert "--offline" in commands["cargo_metadata"]["argv"]
assert "--locked" in commands["cargo_metadata"]["argv"]

def root_set(name):
    lines = (support / f"raw/{name}.stdout").read_text().splitlines()
    roots = set()
    for line in lines:
        fields = line.split("|")
        assert len(fields) == 4 and fields[3].startswith("$PROBE_ROOT/fixture/"), (name, line)
        roots.add(tuple(fields[:3]))
    assert len(roots) == len(lines), name
    return roots

alpha = {("alpha", "alpha", "RLib"), ("alpha", "alpha", "CDyLib")}
alpha_always = {("alpha", "always", "Bin")}
alpha_gated = {("alpha", "gated", "Bin")}
beta = {("beta", "beta", "RLib"), ("beta", "always", "Bin")}
assert root_set("root_default") == root_set("workspace") == alpha | alpha_always | alpha_gated | beta
assert root_set("alpha_lib") == alpha
assert root_set("alpha_bins") == root_set("alpha_bins_feature") == alpha_always | alpha_gated
assert root_set("alpha_tests") == {("alpha", "alpha_integration", "Test")}
assert root_set("alpha_dir_default") == alpha | alpha_always | alpha_gated
assert root_set("beta_default") == beta

cargo_metadata = json.loads((support / "raw/cargo_metadata.stdout").read_text())
packages = {package["name"]: package for package in cargo_metadata["packages"]}
assert set(packages) == {"alpha", "beta"}
assert cargo_metadata["workspace_default_members"] == [packages["alpha"]["id"]]
assert set(cargo_metadata["workspace_members"]) == {packages["alpha"]["id"], packages["beta"]["id"]}
targets = {target["name"]: target for target in packages["alpha"]["targets"]}
assert targets["alpha"]["kind"] == ["rlib", "cdylib"]
assert targets["gated"]["required-features"] == ["gated"]
assert targets["alpha_integration"]["kind"] == ["test"]
assert any(target["name"] == "always" for target in packages["beta"]["targets"])

def cargo_artifacts(name):
    messages = [
        json.loads(line) for line in
        (support / f"raw/{name}.stdout").read_text().splitlines()
    ]
    assert messages[-1]["reason"] == "build-finished" and messages[-1]["success"], name
    artifacts = set()
    for message in messages:
        if message["reason"] == "compiler-artifact":
            pkg_id = message["package_id"]
            package = next(pkg for pkg in ("alpha", "beta") if pkg_id == packages[pkg]["id"])
            artifacts.add((package, message["target"]["name"], tuple(message["target"]["kind"])))
    return artifacts

alpha_lib = ("alpha", "alpha", ("rlib", "cdylib"))
beta_lib = ("beta", "beta", ("rlib",))
alpha_bin = ("alpha", "always", ("bin",))
beta_bin = ("beta", "always", ("bin",))
gated_bin = ("alpha", "gated", ("bin",))
assert cargo_artifacts("cargo_default") == {alpha_lib, alpha_bin}
assert cargo_artifacts("cargo_workspace") == {alpha_lib, alpha_bin, beta_lib, beta_bin}
assert cargo_artifacts("cargo_alpha_bins") == {alpha_lib, alpha_bin}
assert cargo_artifacts("cargo_alpha_bins_feature") == {alpha_lib, alpha_bin, gated_bin}
assert ("alpha", "alpha_integration", ("test",)) in cargo_artifacts("cargo_alpha_tests")
print("PASS: exact source/fixture hashes, 16 offline commands, resolver roots, Cargo default-member and required-feature controls")
