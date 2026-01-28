# v5.1.0

Released 2026-01-10.

This release contains no functional changes compared to v5.0.0. Updating is not
needed for users who do not build for Windows, nor for users who have
`windows-sys` 0.59 in their dependency tree anyway.

**Compatibility:**

 * The minimum supported Rust version is now 1.71.0.
   (This requirement is imposed by the `windows-link` crate.)
 * The `i686-pc-windows-gnu` target can no longer be tested,
   and as such is no longer guaranteed to work.
   `i868-pc-windows-msvc` is still tested.

Changes:

 * Bump `windows-sys` dependency from 0.59 to 0.61.

# v5.0.0

Released 2024-10-22.

This release contains no functional changes compared to v4.2.2. Users who have
no issues with the `winapi` crate are not advised to update.

**Compatibility:**

 * The minimum supported Rust version is now 1.60.0.
   (This requirement is imposed by the `windows-sys` crate.)

Changes:

 * Replace the `winapi` dependency with `windows-sys`. They are functionally
   equivalent, however `windows-sys` is published first-party by Microsoft.
   ([#19][19])
 * Uses Rust edition 2021 rather than 2015.
 * CI configuration is now generated with [RCL](https://rcl-lang.org/),
   to make it easier to bump the MSRV in the future.
 * Ensures compatibility with Rust 1.60.0 through 1.82.0.

[19]: https://github.com/ruuda/thread-id/issues/19

# v4.2.2

Released 2024-07-18.

 * Support SGX target. ([#18][18])
 * Ensures compatibility with Rust 1.34.2 through 1.79.0.

Thanks to Arash Sahebolamri for contributing to this release.

[18]: https://github.com/ruuda/thread-id/pull/18

# v4.2.1

Released 2023-10-16.

 * Remove Redox-specific dependencies in favor of the `libc` crate, in
   accordance [with Redox' ABI stability plans][redox-abi]. This makes Redox
   use the same pthreads calls as the other Unix-like platforms. ([#15][15])
 * Ensures compatibility with Rust 1.34.2 through 1.73.0.

Thanks to 4lDO2 for contributing to this release.

[redox-abi]: https://redox-os.org/news/development-priorities-2023-09/
[15]: https://github.com/ruuda/thread-id/pull/15

# v4.2.0

Released 2023-08-20.

 * Switch to `pthread_threadid_np` instead of `pthread_self` on Apple platforms.
   The latter was not guaranteed to be unique for the lifetime of the process.
 * Ensures compatibility with Rust 1.34.2 through 1.72.0.

Thanks to Charles Hubain for contributing to this release.

# v4.1.0

Released 2023-05-15.

 * Add support for the `wasm32-unknown-unknown` target.
 * Ensures compatibility with Rust 1.34.2 through 1.69.0.

Thanks to dAxpeDDa for contributing to this release.

# v4.0.0

Released 2021-03-24.

**Compatibility**:

 * The minimum supported Rust version is now 1.34.2.

Changes:

 * Bump `redox_syscall` dependency to v0.2.
 * Ensures compatibility with Rust 1.34.2 through 1.50.0.

Thanks to zonyitoo for contributing to this release.

# v3.3.0

Released 2018-03-23.

 * Bump `winapi` dependency to v0.3.
 * Add CI badges to crate metadata.
 * Ensures compatibility with Rust 1.8.0 through 1.24.0.

Thanks to Martin Geisler and Bastien Orivel for contributing to this release.

# v3.2.0

Released 2017-06-26.

 * Add support for the Redox operating system.
 * Ensures compatibility with Rust 1.8.0 through 1.18.0.

Thanks to Ian Douglas Scott for contributing to this release.

# v3.1.0

Released 2017-05-13.

 * Add the MIT license as an alternative to the Apache 2.0 license. This license
   change applies retroactively to all versions, this is only a metadata change.

# v3.0.0

Released 2016-10-29.

 * Depend on libc only on Unix-like environments, and on kernel32-sys only
   on Windows. This requires Rust 1.8 or later, hence the major version
   bump.

# v2.0.0

Released 2016-04-09.

 * Change ID type to `usize` to better reflect the underlying platform IDs.
   This is a breaking change.
 * Allow functions to be inlined to avoid call overhead.

Many thanks to Amanieu d'Antras for contributing to this release.

# v1.0.0

Released 2016-03-13.

Initial release with Windows and Linux support.
