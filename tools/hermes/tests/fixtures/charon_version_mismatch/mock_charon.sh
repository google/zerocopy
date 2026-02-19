#!/bin/sh
echo "DEBUG: mismatch script called with args: $@" >&2
if [ "$1" = "version" ]; then
    echo "0.0.0"
else
    exit 1
fi
