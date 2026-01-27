## zipsign-api

Sign and verify `.zip` and `.tar.gz` files with an ed25519 signing key.

[![GitHub Workflow Status](https://img.shields.io/github/actions/workflow/status/Kijewski/zipsign/ci.yml?branch=main&style=flat-square&logoColor=white)](https://github.com/Kijewski/zipsign/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/zipsign-api?logo=rust&style=flat-square&logoColor=white)](https://crates.io/crates/zipsign-api)
[![docs.rs](https://img.shields.io/docsrs/zipsign-api?logo=docsdotrs&style=flat-square&logoColor=white "docs.rs")](https://docs.rs/zipsign-api/)

This library contains the brains of [`zipsign`](https://github.com/Kijewski/zipsign).
You can use it in your projects to verify and sign `.zip` and `.tar.gz` files
without running a separate application, e.g. to verify a self-update.

### Features

* `default`: sign and verify `.tar.gz` and `.zip` files
* `sign-tar`: sign a `.tar.gz` file
* `verify-tar`: verify a signed `.tar.gz` file
* `sign-zip`: sign a `.zip` file
* `verify-zip`: verify a signed `.zip` file
* `tar`: combines `sign-tar` and `verify-tar`
* `zip`: combines `sign-zip` and `verify-zip`
