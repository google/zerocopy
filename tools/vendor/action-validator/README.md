The `action-validator` is a standalone tool designed to "lint" the YAML files
used to define GitHub Actions and Workflows. It ensures that they are well-formed,
by checking them against published JSON schemas, and it makes sure that any
globs used in `paths` / `paths-ignore` match at least one file in the repo.

The intended use case for `action-validator` is in Git pre-commit hooks and
similar situations.


# Funding Development

I am currently experimenting with ways to fund development of new features in `action-validator`.
You can find more details of this approach at [the `action-validator` code fund page](https://hezmatt.org/~mpalmer/code-fund.html).


# Installation

We have many ways to install `action-validator`.

## Pre-built binaries

The [GitHub releases](https://github.com/mpalmer/action-validator/releases)
have some pre-built binaries -- just download and put them in your path. If a
binary for your platform isn't available, let me know and I'll see what I can
figure out.


## Using cargo

If you've got a Rust toolchain installed, running `cargo install action-validator` should give you the latest release.


## Using asdf

If you're a proponent of the [asdf tool](https://asdf-vm.com/), then you can
use that to install and manage `action-validator`:

```shell
asdf plugin add action-validator
# or
asdf plugin add action-validator https://github.com/mpalmer/action-validator.git
```

Install/configure action-validator:

```shell
# Show all installable versions
asdf list-all action-validator

# Install specific version
asdf install action-validator latest

# Set a version globally (on your ~/.tool-versions file)
asdf set -u action-validator latest

# Now action-validator commands are available
action-validator --help
```

## Using NPM

Node users can install the latest version using NPM:

> ℹ️ The `@action-validator/core` package can be used directly within Node.js applications.

```sh
npm install -g @action-validator/core @action-validator/cli --save-dev
```

## Building from the repo

If you want to build locally, you'll need to:

1. Checkout the git repository somewhere;

1. Grab the `SchemaStore` submodule, by running `git submodule init && git submodule update`;

1. Install a [Rust](https://rust-lang.org) toolchain; and then

1. run `cargo build`.


# Usage

Couldn't be simpler: just pass a file to the program:

```shell
action-validator .github/workflows/build.yml
```

Use `action-validator -h` to see additional options.


## In a GitHub Action

The action-validator can be run in a Github action itself, as a pull request job. See the `actions` job in the [QA workflow](https://github.com/mpalmer/action-validator/tree/main/.github/workflows/qa.yml), in this repository, as an example of how to use action-validator + asdf in a GitHub workflow.
This may seem a little redundant (after all, an action has to be valid in order for GitHub to run it), but this job will make sure that all your *other* actions are also valid.

## Using pre-commit

Update your .pre-commit-config.yaml:

```yaml
repos:
- repo: https://github.com/mpalmer/action-validator
  rev: v<version>
  hooks:
    - id: action-validator
```

## Pre-commit hook example

Create an executable file in the .git/hooks directory of the target repository:
`touch .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit` and paste the following example code:

```bash
#!/bin/bash
if ! command -v action-validator >/dev/null; then
  echo "action-validator is not installed."
  echo "Installation instructions: https://github.com/mpalmer/action-validator"
  exit 1
fi
echo "Running pre-commit hook for GitHub Actions: https://github.com/mpalmer/action-validator"
scan_count=0
for action in $(git diff --cached --name-only --diff-filter=ACM | grep -E '^\.github/(workflows|actions)/.*\.ya?ml$'); do
  if action-validator "$action"; then
    echo "✅ $action"
  else
    echo "❌ $action"
    exit 1
  fi
  scan_count=$((scan_count+1))
done
echo "action-validator scanned $scan_count GitHub Actions and found no errors!"
```

This script will run on every commit to the target repository, whether the github action yaml files are being committed, or not and prevent any commit if there are linting errors.

```
# All action-validator linting errors must be resolved before any commit will succeed.
$ echo "" >> README.md && git add README.md && git commit -m "Update read-me"
Running pre-commit hook for GitHub Actions: https://github.com/mpalmer/action-validator
Validation failed: ValidationState {
    errors: [
        Properties {
            path: "",
            detail: "Additional property 'aname' is not allowed",
        },
    ],
    missing: [],
    replacement: None,
}
❌ .github/workflows/ci.yaml
Fatal error validating .github/workflows/ci.yaml: validation failed


# Fix error and try again
$ echo "" >> README.md && git add README.md && git commit -m "Update read-me"
Running pre-commit hook for GitHub Actions: https://github.com/mpalmer/action-validator
✅ .github/workflows/ci.yaml
✅ .github/workflows/release.yml
action-validator scanned 2 GitHub Actions found no errors!
[main c34fda3] Update read-me
 1 file changed, 2 insertions(+)
```

## NPM

Provided you have followed the [installation instructions for NPM](#using-npm), you can run the action
validator CLI as follows

```sh
npx action-validator <path_to_action_yaml>
```

Or, if you've installed the package globally:

```sh
action-validator <path_to_action_yaml>
```

## Node API

The Node API can be used to validate action and workflow files from Node.js as follows:

> ⚠️ The Node API does not currently support glob validation.

```ts
import { readFileSync } from "fs";
import { validateAction, validateWorkflow } from "@action-validator/core";

// Validate Action
const actionSource = readFileSync("action.yml", "utf8");
const state = validator.validateAction(actionSource);
const isValid = state.errors.length === 0;

// Validate Workflow
const workflowSource = readFileSync("workflow.yml", "utf8");
const state = validator.validateWorkflow(workflowSource);
const isValid = state.errors.length === 0;
```

# Contributing

Please see [CONTRIBUTING.md](CONTRIBUTING.md).


# Licence

Unless otherwise stated, everything in this repo is covered by the following
copyright notice:

    Copyright (C) 2021  Matt Palmer <matt@hezmatt.org>

    This program is free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License version 3, as
    published by the Free Software Foundation.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
