#!/bin/sh
if [ "$1" = "version" ] || [ "$1" = "--version" ]; then
    echo "0.1.163"
    exit 0
fi
cat "$(dirname "$0")/mock_charon_output.json"
exit 101
