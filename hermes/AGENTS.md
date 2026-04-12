<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Hermes

> **Note to AI Agents:** This document is intended for agents **developing** the
> Hermes toolchain itself. If you are an agent **using** Hermes, please refer to
> the `llms.txt` and `docs/agent/` directory instead.

## Basic commands

1. Run with `cargo run verify`.
2. Run unit tests with `cargo test --bin hermes`.
3. Run all tests (including integration tests) with `./docker.sh cargo test`.
4. Run a *specific* integration test fixture with `./docker.sh cargo test --test integration fixture_name`.

## Tips

1. Integration tests are expensive. Prefer `cargo test --bin hermes` for quick verification and iteration,
   and only run `./docker.sh cargo test --test integration` when you need to verify the integration tests.
2. To see the generated Lean code for a module, use `cargo run expand`. This will run Aeneas and Hermes but skip verification, outputting the generated `.lean` definitions to the terminal.
   ```bash
   cargo run expand --example abs
   ```
3. To see where intermediate artifacts are placed on disk, run with `RUST_LOG=hermes=trace` as a fallback:
  ```bash
  RUST_LOG=hermes=trace cargo run verify --example abs
  ```

## Integration Testing

1. **Updating Expected Output:** Hermes integration tests (stored in `tests/fixtures/<test_name>`) assert against an `expected.stderr` or `out.txt` file. When you intentionally change the behavior or output of a test, do not edit these files manually. Instead, run the integration test with `BLESS=1` to automatically overwrite the snapshot files:
   ```bash
   BLESS=1 ./docker.sh cargo test --test integration fixture_name
   ```

2. **Allowing `sorry`:** While developing and ensuring Aeneas translates Rust correctly, you don't have to write the full Lean proof immediately. You can write `sorry` inside the `proof` block. However, you must pass `--allow-sorry` to Hermes so the verifier doesn't fail immediately on the unimplemented proof. For integration tests, this is done by adding `--allow-sorry` to the `args` array in the fixture's `anneal.toml`:
   ```toml
   args = ["verify", "--allow-sorry"]
   ```

## Running Tests in Docker

Due to the complex toolchains required by Hermes (Rust, Lean 4, Aeneas, and Charon), it is recommended to run integration tests within the provided Docker container. The container handles all system dependencies and provides an isolated environment for the test runner.

The `docker.sh` script should be used. It handles building and caching the Docker image, mounting compilation cache volumes, mapping local user IDs (so that files are not owned by `root` on your host), and forwarding environment variables.

Simply prefix your normal Cargo tests with `./docker.sh`:
```bash
./docker.sh cargo test --test integration

# You can pass standard environment variables. They will be forwarded!
BLESS=1 ./docker.sh cargo test --test integration
```

*(Under the hood, this evaluates your path and places you in the same working directory inside the container's bound `/workspace` volume)*

## Debugging Tips

1. **Debugging Aeneas vs Hermes Mismatches**
   - If you encounter Lean type mismatches (e.g., `Application type mismatch`), it's often a mismatch between what Aeneas generated for the function and what Hermes assumed Aeneas generated in the theorem signature.
   - Standard integration tests (`./docker.sh cargo test --test integration`) delete their temporary output directory (`/cache/hermes_target/hermes-test-XXX` inside Docker) upon completion.
   - If a test fails and you want to inspect the generated Lean code, use the `ANNEAL_KEEP_TEST_DIR=1` environment variable.
   - The test runner will preserve the directory and print its path to stderr:
     ```bash
     ANNEAL_KEEP_TEST_DIR=1 ./docker.sh cargo test --test integration macro_edge_cases
     ```
   - **Note:** Because the test runner operates inside Docker, the printed path will reside within the container's isolated `/cache` volume. To explore it, you must open a shell inside the container:
     ```bash
     ./docker.sh bash
     # Then inside the container, navigate to the path printed to stderr:
     cd /cache/hermes_target/hermes-test-XXX
     ```
   - Look at `Funs.lean` to see the actual Aeneas parameters, and `[TestName].lean` to see the Hermes theorem signature.

2. **Caches Need Busting**
   - Sometimes `cargo test` fails with bizarre syntax errors that persist despite fixing the code.
   - If this happens, clear the integration caches. If you are using `./docker.sh`, the caches reside inside the container's `/cache` volume, so you must clear them from within by running:
     ```bash
     ./docker.sh rm -rf /cache/hermes_target/hermes_integration_cache
     ```
