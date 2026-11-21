#!/usr/bin/env bash
set -euo pipefail

WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"' EXIT

NIXPKGS_SRC="${NIXPKGS_SRC:-/nix/store/wjfxdzblindbl9sp2hbwhi4iyh5jh348-source}"

mkdir -p "$WORKDIR/repo/crates/core" "$WORKDIR/cache"
cd "$WORKDIR/repo"
git init --ref-format=files -q
git config user.email "probe@example.com"
git config user.name "Probe"

UNIQUE_TAG="PROBE2_UNRELATED_$(date +%s)_$$"
python3 - "$UNIQUE_TAG" <<'PY'
import sys
tag = sys.argv[1].encode()
with open("unrelated-large.bin", "wb") as f:
    f.write(tag + b"\n" + b"X" * (2 * 1024 * 1024))
PY

echo "core-v1-$UNIQUE_TAG" > crates/core/hello.txt
echo "other-v1-$UNIQUE_TAG" > crates/core/other.txt

cat > flake.nix <<EOF
{
  description = "Probe 2: lazy-trees, binary cache probing, and ca-derivations";
  inputs = {
    nixpkgs.url = "path:${NIXPKGS_SRC}";
  };
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.\${system};
      lib = nixpkgs.lib;
      fs = lib.fileset;
      coreSrc = fs.toSource {
        root = ./.;
        fileset = ./crates/core/hello.txt;
      };
      otherSrc = fs.toSource {
        root = ./.;
        fileset = ./crates/core/other.txt;
      };
      # Use pkgs.busybox so its store path carries string context and is mounted in the Nix sandbox
      mkCheck = name: src: derivation {
        inherit name system src;
        builder = "\${pkgs.busybox}/bin/busybox";
        args = [ "sh" "-c" "\${pkgs.busybox}/bin/busybox cat \$src/crates/core/*.txt > \$out" ];
      };
      mkCaCheck = name: src: derivation {
        inherit name system src;
        __contentAddressed = true;
        outputHashMode = "recursive";
        outputHashAlgo = "sha256";
        builder = "\${pkgs.busybox}/bin/busybox";
        args = [ "sh" "-c" "\${pkgs.busybox}/bin/busybox cat \$src/crates/core/*.txt > \$out" ];
      };
    in {
      checks.\${system} = {
        core = mkCheck "probe2-core" coreSrc;
        other = mkCheck "probe2-other" otherSrc;
        caCore = mkCaCheck "probe2-ca-core" coreSrc;
      };
    };
}
EOF

git add -A
git commit -q -m "initial"
nix flake lock 2>/dev/null
git add flake.lock
git commit -q -m "add flake.lock"

echo "=== Part A: Lazy Trees (--lazy-trees vs --no-lazy-trees) ==="
echo "--- Running nix eval --lazy-trees .#checks.x86_64-linux.core.drvPath ---"
DRV_LAZY="$(nix eval --raw --lazy-trees .#checks.x86_64-linux.core.drvPath)"
echo "drvPath (lazy): $DRV_LAZY"
echo "Checking if unrelated-large.bin was copied into /nix/store during --lazy-trees eval:"
FOUND_LAZY="$(ls /nix/store/*-source/unrelated-large.bin 2>/dev/null | xargs -r grep -l "$UNIQUE_TAG" 2>/dev/null || true)"
echo "Found in /nix/store after --lazy-trees: ${FOUND_LAZY:-NONE}"

echo "--- Running nix eval --no-lazy-trees .#checks.x86_64-linux.core.drvPath ---"
DRV_NOLAZY="$(nix eval --raw --no-lazy-trees .#checks.x86_64-linux.core.drvPath)"
echo "drvPath (no-lazy): $DRV_NOLAZY"
echo "Checking if unrelated-large.bin was copied into /nix/store during --no-lazy-trees eval:"
FOUND_NOLAZY="$(ls /nix/store/*-source/unrelated-large.bin 2>/dev/null | xargs -r grep -l "$UNIQUE_TAG" 2>/dev/null || true)"
echo "Found in /nix/store after --no-lazy-trees: ${FOUND_NOLAZY:-NONE}"

echo ""
echo "=== Part B: Realize ONLY 'core', upload to local binary cache, probe BOTH 'core' and 'other' ==="
CORE_OUT="$(nix eval --raw .#checks.x86_64-linux.core.outPath)"
OTHER_OUT="$(nix eval --raw .#checks.x86_64-linux.other.outPath)"
echo "core  outPath: $CORE_OUT"
echo "other outPath: $OTHER_OUT"

nix build --no-link .#checks.x86_64-linux.core
nix copy --to "file://$WORKDIR/cache" "$CORE_OUT"

HASH32="$(basename "$CORE_OUT" | cut -c1-32)"
echo "--- Exact narinfo file ($HASH32.narinfo) in binary cache ---"
cat "$WORKDIR/cache/$HASH32.narinfo"

echo "--- Probe cached 'core' outPath via nix path-info --store ---"
nix path-info --store "file://$WORKDIR/cache" --json "$CORE_OUT"
echo ""

echo "--- Probe unbuilt 'other' outPath via nix path-info --store (no realization) ---"
if nix path-info --store "file://$WORKDIR/cache" --json "$OTHER_OUT" 2>&1; then
  echo "(unexpected hit)"
else
  echo "(cache miss as expected, exit=$?)"
fi
echo "Verify 'other' was NOT realized locally:"
test -e "$OTHER_OUT" && echo "EXISTS" || echo "NOT_IN_LOCAL_STORE"

echo ""
echo "=== Part C: Experimental ca-derivations outPath before realization ==="
CA_DRV="$(nix eval --raw --extra-experimental-features ca-derivations .#checks.x86_64-linux.caCore.drvPath)"
CA_OUT="$(nix eval --raw --extra-experimental-features ca-derivations .#checks.x86_64-linux.caCore.outPath)"
echo "caCore drvPath: $CA_DRV"
echo "caCore outPath (pre-build): $CA_OUT"
