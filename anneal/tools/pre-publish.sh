#!/bin/bash
set -eo pipefail

# Remove cargo configs if they exist
rm -f .cargo/config.toml
rm -f ../.cargo/config.toml

# Verify exactly one occurrence of the relative path
COUNT=$(grep -c "docs/images/logo.svg" README.md || true)
if [ "$COUNT" -ne 1 ]; then
  echo "Error: Found $COUNT occurrences of 'docs/images/logo.svg' in README.md, expected exactly 1."
  exit 1
fi

# Replace it
sed -i 's|docs/images/logo.svg|https://raw.githubusercontent.com/google/zerocopy/main/anneal/docs/images/logo.svg|g' README.md

echo "Pre-publish steps completed successfully."
