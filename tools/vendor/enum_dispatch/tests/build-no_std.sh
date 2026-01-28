#!/bin/sh

set -eux

TARGET="thumbv7em-none-eabi"
rustup target add $TARGET
cargo build --verbose --target $TARGET --release
