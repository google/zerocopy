import json
import tomllib

def to_toml_inline_table(d):
    items = []
    for k, v in d.items():
        items.append(f"{k} = {json.dumps(v)}")
    return "{ " + ", ".join(items) + " }"

with open("Cargo.toml", "rb") as f:
    data = tomllib.load(f)

print("[package]")
print(f'name = {json.dumps(data["package"]["name"])}')
print(f'version = {json.dumps(data["package"]["version"])}')
print(f'edition = {json.dumps(data["package"]["edition"])}')

deps = data["dependencies"]
print("[dependencies]")
for dep in ["anyhow", "flate2", "sha2", "tar", "fs2", "log", "reqwest", "dirs"]:
    val = deps[dep]
    if isinstance(val, dict):
        print(f"{dep} = {to_toml_inline_table(val)}")
    else:
        print(f"{dep} = {json.dumps(val)}")

print("[build-dependencies]")
print(f'toml = {json.dumps(data["build-dependencies"]["toml"])}')

print("[package.metadata.build_rs]")
for k, v in data["package"]["metadata"]["build_rs"].items():
    print(f"{k} = {json.dumps(v)}")

print("[package.metadata.anneal.dependencies.aeneas]")
for k, v in data["package"]["metadata"]["anneal"]["dependencies"]["aeneas"].items():
    if k != "checksums":
        print(f"{k} = {json.dumps(v)}")

print("[package.metadata.anneal.dependencies.aeneas.checksums]")
for k, v in data["package"]["metadata"]["anneal"]["dependencies"]["aeneas"]["checksums"].items():
    print(f"{k} = {json.dumps(v)}")
