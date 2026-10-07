#!/usr/bin/env bash
# Run on the native Intel Mac runner after Nix installation, before core builds.
set -euo pipefail
test "$(uname -s)" = Darwin
test "$(uname -m)" = x86_64
evidence="$PWD/intel-signing-evidence"
mkdir "$evidence"
fixture="$(nix build --impure --no-link --print-out-paths --max-jobs 2 --cores 2 \
  --expr '(import ./ci/intel-signing-preflight.nix) { flake = builtins.getFlake ("path:" + toString ./anneal); }' \
  2> >(tee "$evidence/build.log" >&2))"
printf '%s\n' "$fixture" > "$evidence/store-path"
workspace="$(mktemp -d "$RUNNER_TEMP/anneal-intel-signing.XXXXXX")"
# Copy out of the store to test relocation while retaining read-only files.
cp -R "$fixture" "$workspace/relocated"
relocated="$workspace/relocated"
test -x "$relocated/factor"
test -n "$(find "$relocated/libs" -type f -name '*gmp*.dylib' -print -quit)"
while IFS= read -r -d '' file; do
  /usr/bin/codesign --verify --strict "$file" 2>&1 | tee -a "$evidence/codesign.log"
  /usr/bin/otool -L "$file" | tee -a "$evidence/dependencies.log"
done < <(find "$relocated/libs" -type f -name '*.dylib' -print0)
/usr/bin/codesign --verify --strict "$relocated/factor" 2>&1 | tee -a "$evidence/codesign.log"
/usr/bin/otool -L "$relocated/factor" | tee -a "$evidence/dependencies.log"
if /usr/bin/grep -F /nix/store "$evidence/dependencies.log"; then
  echo 'Nix store dependency remains after relocation' >&2
  exit 1
fi
actual="$("$relocated/factor" 15)"
printf '%s\n' "$actual" | tee "$evidence/execution.log"
test "$actual" = '15: 3 5'
printf '{"validated":true,"native_system":"x86_64-darwin","fixture":"GMP-linked factor"}\n' \
  > "$evidence/result.json"
