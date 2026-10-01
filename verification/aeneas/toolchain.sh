# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Upgrade the bundle as a unit; Charon is selected by Aeneas's charon-pin.
AENEAS_RELEASE=nightly-2026.10.01-ca282ec
AENEAS_REV=ca282ec2312a96f6a985a4d23a663690816d3f3e
CHARON_VERSION=0.1.276
CHARON_REV=cf02e3f228f97ee7be3a415be56989053063326d
AENEAS_RUST_TOOLCHAIN=nightly-2026-09-17
AENEAS_LEAN_TOOLCHAIN=leanprover/lean4:v4.31.0
AENEAS_LEAN_VERSION=4.31.0

case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)
        AENEAS_PLATFORM=linux-x86_64
        AENEAS_SHA256=473df2e5bab0439bfd1a68503ae02c7f88a8de4182e98e4e281590285ab01dee
        AENEAS_LEAN_PLATFORM=linux
        AENEAS_LEAN_SHA256=07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f
        ;;
    Darwin-arm64)
        AENEAS_PLATFORM=macos-aarch64
        AENEAS_SHA256=fac88099e9d687eb321499e43aef1418a4d06f7ae72ecba0b5fd7d38cf013ddd
        AENEAS_LEAN_PLATFORM=darwin_aarch64
        AENEAS_LEAN_SHA256=264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27
        ;;
    *) echo "Unsupported Aeneas CI toolchain platform" >&2; return 1 ;;
esac
