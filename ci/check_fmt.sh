#!/usr/bin/env bash
set -eo pipefail
files=$(find . -iname '*.rs' -type f -not -path './target/*')
# check that find succeeded
if [[ -z $files ]]
then
	exit 1
fi
rustfmt --check $files
