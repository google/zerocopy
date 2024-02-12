#!/bin/bash
set -eo pipefail
rustfmt --check $(find . -iname '*.rs' -type f -not -path './target/*')
