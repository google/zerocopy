#!/usr/bin/env bash
set -euo pipefail

WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"' EXIT

NIXPKGS_SRC="${NIXPKGS_SRC:-/nix/store/wjfxdzblindbl9sp2hbwhi4iyh5jh348-source}"
BUSYBOX="${BUSYBOX:-/nix/store/cs8vhk2f293lp26mjnmjz04aqj4m3bj9-busybox-1.37.0/bin/busybox}"

mkdir -p "$WORKDIR/repo/crates/core/src" "$WORKDIR/repo/crates/leaf/src"
cd "$WORKDIR/repo"
git init --ref-format=files -q
git config user.email "probe@example.com"
git config user.name "Probe"

cat > README.md <<'EOF'
# Sample Workspace v1
EOF
cat > crates/core/src/lib.rs <<'EOF'
pub fn core_val() -> u32 { 1 }
EOF
cat > crates/leaf/src/lib.rs <<'EOF'
pub fn leaf_val() -> u32 { 2 }
EOF

cat > flake.nix <<EOF
{
  description = "Probe 1: lib.fileset.toSource vs whole-tree self invalidation";
  inputs = {
    nixpkgs.url = "path:${NIXPKGS_SRC}";
  };
  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      fs = lib.fileset;
      system = "x86_64-linux";
      mkCheck = name: src: derivation {
        inherit name system src;
        builder = "${BUSYBOX}";
        args = [ "sh" "-c" "echo checked > \$out" ];
      };
      coreSrc = fs.toSource {
        root = ./.;
        fileset = fs.unions [ ./crates/core ];
      };
      leafSrc = fs.toSource {
        root = ./.;
        fileset = fs.unions [ ./crates/core ./crates/leaf ];
      };
      naiveSelfSrc = self;
      checks = {
        check-core-fileset = mkCheck "check-core-fileset" coreSrc;
        check-leaf-fileset = mkCheck "check-leaf-fileset" leafSrc;
        check-naive-self   = mkCheck "check-naive-self" naiveSelfSrc;
      };
    in {
      checks.\${system} = checks;
      # Note: attrsets containing a key literally named 'outPath' are coerced by Nix toJSON
      # to just that string; use 'drv_path' and 'out_path' for structured planner JSON.
      planRaw = builtins.mapAttrs (_: d: { drv_path = d.drvPath; out_path = d.outPath; }) checks;
      planRawToFile = builtins.toFile "plan.json" (builtins.toJSON (
        builtins.mapAttrs (_: d: { drv_path = d.drvPath; out_path = d.outPath; }) checks
      ));
      planSafe = builtins.mapAttrs (_: d: {
        drv_path = builtins.unsafeDiscardStringContext d.drvPath;
        out_path = builtins.unsafeDiscardStringContext d.outPath;
      }) checks;
      planSafeToFile = builtins.toFile "plan-safe.json" (builtins.toJSON (
        builtins.mapAttrs (_: d: {
          drv_path = builtins.unsafeDiscardStringContext d.drvPath;
          out_path = builtins.unsafeDiscardStringContext d.outPath;
        }) checks
      ));
    };
}
EOF

git add -A
git commit -q -m "initial"
# Lock flake once and commit flake.lock so git tree is clean
nix flake lock 2>/dev/null
git add flake.lock
git commit -q -m "add flake.lock"

echo "=== 1a. String context check: nix eval --json .#planRaw (succeeds in Nix 2.33.3 but DOES NOT realize) ==="
nix eval --json .#planRaw
echo ""

echo "=== 1b. String context error WITHOUT unsafeDiscardStringContext in builtins.toFile ==="
if nix eval --raw .#planRawToFile 2>&1; then
  echo "(unexpectedly succeeded)"
else
  echo "(failed as expected without unsafeDiscardStringContext)"
fi

echo "=== 1c. String context discarded WITH unsafeDiscardStringContext in builtins.toFile ==="
nix eval --raw .#planSafeToFile
echo ""

echo ""
echo "=== 2. Baseline plan ==="
nix eval --json .#planSafe | tee "$WORKDIR/base.json"
echo ""

echo ""
echo "=== 3. Edit unrelated README.md ==="
echo "Extra docs line" >> README.md
git add README.md
nix eval --json .#planSafe | tee "$WORKDIR/after_readme.json"
echo ""

echo ""
echo "=== 4. Edit crates/leaf/src/lib.rs ==="
echo "// leaf edit" >> crates/leaf/src/lib.rs
git add crates/leaf/src/lib.rs
nix eval --json .#planSafe | tee "$WORKDIR/after_leaf.json"
echo ""

echo ""
echo "=== 5. Edit crates/core/src/lib.rs ==="
echo "// core edit" >> crates/core/src/lib.rs
git add crates/core/src/lib.rs
nix eval --json .#planSafe | tee "$WORKDIR/after_core.json"
echo ""

python3 - "$WORKDIR" <<'PY'
import json, sys, os
w = sys.argv[1]
base = json.load(open(os.path.join(w, "base.json")))
readme = json.load(open(os.path.join(w, "after_readme.json")))
leaf = json.load(open(os.path.join(w, "after_leaf.json")))
core = json.load(open(os.path.join(w, "after_core.json")))

def cmp(label, a, b):
    print(f"\n--- Diff: {label} ---")
    for k in sorted(a):
        drv_same = a[k]["drv_path"] == b[k]["drv_path"]
        out_same = a[k]["out_path"] == b[k]["out_path"]
        print(f"  {k:20s}: drvPath={'UNCHANGED' if drv_same else 'CHANGED  '} | outPath={'UNCHANGED' if out_same else 'CHANGED'}")

cmp("Edit README.md (unrelated)", base, readme)
cmp("Edit crates/leaf/src/lib.rs", readme, leaf)
cmp("Edit crates/core/src/lib.rs", leaf, core)
PY
