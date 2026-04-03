#!/bin/sh
if [ "$1" = "version" ]; then
    echo "0.1.163"
else
    # Fallback to real charon if available, or just exit successfully if we only care about version check passing
    # For this test, we want to ensure Hermes *proceeds* to call Charon.
    # The integration test framework will capture this invocation.
    # We can just exit 0 to simulate success, or exit 101 if we want to test that Hermes calls checking.
    # Actually, Hermes calls `charon version` THEN `charon ...`.
    # If we are in the "else" block, it means `charon ...` (extraction) was called.
    # We can just exit 0.
    exit 0
fi
