#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
set -euo pipefail

experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
linux_dir="$(dirname -- "$experiment_dir")/rfl-linux"
revision=0fcb05b72344f40806cbe810de8872f1698bf053

if [[ -e "$linux_dir" ]]; then
    if [[ ! -d "$linux_dir/.git" ]]; then
        echo "Refusing to replace existing non-Git directory: $linux_dir" >&2
        exit 1
    fi
    if [[ "$(git -C "$linux_dir" rev-parse HEAD)" != "$revision" ]]; then
        echo "Existing Linux checkout is at a different revision; left unchanged." >&2
        exit 1
    fi
    if [[ -n "$(git -C "$linux_dir" status --porcelain)" ]]; then
        echo "Existing Linux checkout has changes; left unchanged." >&2
        exit 1
    fi
    echo "Pinned Linux checkout already prepared: $linux_dir"
    exit 0
fi

git init -q "$linux_dir"
git -C "$linux_dir" remote add origin https://github.com/torvalds/linux.git
git -C "$linux_dir" config remote.origin.promisor true
git -C "$linux_dir" config remote.origin.partialclonefilter blob:none
git -C "$linux_dir" sparse-checkout init --cone
git -C "$linux_dir" sparse-checkout set \
    rust samples/rust Documentation/rust \
    drivers/android/binder drivers/gpu/drm/tyr drivers/gpu/drm/nova
git -C "$linux_dir" fetch --depth=1 --filter=blob:none origin "$revision"
git -C "$linux_dir" checkout --detach "$revision"
echo "Prepared pinned Linux checkout: $linux_dir"
