#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/../.."

helper=.github/scripts/install-apt-packages.sh
test_root="$(mktemp -d "${TMPDIR:-/tmp}/zerocopy-apt-test.XXXXXXXX")"
trap 'rm -rf "$test_root"' EXIT
fake_bin="$test_root/bin"
mkdir "$fake_bin"

cat > "$fake_bin/sudo" <<'EOF'
#!/usr/bin/env bash
set -eu
exec "$@"
EOF

cat > "$fake_bin/timeout" <<'EOF'
#!/usr/bin/env bash
set -eu
printf 'timeout:%s\n' "$*" >> "$APT_TEST_LOG"
case "$1" in
    --kill-after=*) shift ;;
    *) exit 97 ;;
esac
shift
exec "$@"
EOF

cat > "$fake_bin/sleep" <<'EOF'
#!/usr/bin/env bash
set -eu
printf 'sleep:%s\n' "$*" >> "$APT_TEST_LOG"
EOF

cat > "$fake_bin/apt-get" <<'EOF'
#!/usr/bin/env bash
set -eu
count=0
if [[ -f "$APT_TEST_COUNT" ]]; then
    count="$(cat "$APT_TEST_COUNT")"
fi
count=$((count + 1))
printf '%s\n' "$count" > "$APT_TEST_COUNT"
printf 'apt:%s\n' "$*" >> "$APT_TEST_LOG"

case "${APT_TEST_MODE:-success}" in
    success) ;;
    fail-first-update)
        [[ $count -ne 1 ]] || exit 42
        ;;
    always-fail) exit 42 ;;
    *) exit 98 ;;
esac
EOF

chmod +x "$fake_bin"/*

run_helper() {
    local case_name="$1"
    local mode="$2"
    shift 2
    export APT_TEST_LOG="$test_root/$case_name.log"
    export APT_TEST_COUNT="$test_root/$case_name.count"
    export APT_TEST_MODE="$mode"
    PATH="$fake_bin:$PATH" bash "$helper" "$@"
}

run_helper success success ripgrep llvm
success_log="$test_root/success.log"
[[ "$(grep -c '^apt:' "$success_log")" -eq 2 ]]
grep -F 'timeout:--kill-after=10s 120s env DEBIAN_FRONTEND=noninteractive apt-get' \
    "$success_log" >/dev/null
grep -F 'timeout:--kill-after=10s 300s env DEBIAN_FRONTEND=noninteractive apt-get' \
    "$success_log" >/dev/null
grep -F -- '--yes --no-install-recommends install -- ripgrep llvm' \
    "$success_log" >/dev/null
! grep -q '^sleep:' "$success_log"

run_helper retry fail-first-update ripgrep
retry_log="$test_root/retry.log"
[[ "$(grep -c '^apt:' "$retry_log")" -eq 3 ]]
[[ "$(grep -c '^sleep:' "$retry_log")" -eq 1 ]]

if run_helper exhausted always-fail ripgrep; then
    echo "expected exhausted apt retries to fail" >&2
    exit 1
fi
exhausted_log="$test_root/exhausted.log"
[[ "$(grep -c '^apt:' "$exhausted_log")" -eq 3 ]]
[[ "$(grep -c '^sleep:' "$exhausted_log")" -eq 2 ]]

if run_helper invalid success --option; then
    echo "expected an invalid package name to fail" >&2
    exit 1
fi
[[ ! -e "$test_root/invalid.log" ]]

echo "apt setup retry tests passed"
