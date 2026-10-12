# Playground crate inclusion policy

The playground selects a number of root crates to include:

- The top 100 crates based on [all time downloads][]
- Crates from the [Rust cookbook][]

A recent non-[prerelease][] version of these crates are available, as
well as whatever dependencies these crates require.

Please do not open issues or pull requests about adding or updating
crates available in the playground. This list is maintained
semi-automatically and all crates are updated at once to reduce
duplicate work. The update frequency is sporadic, but usually
corresponds to when a new stable version of Rust is released: every
six weeks.

## Why is there a policy?

The number of crates must be restricted because time and space are
limited resources and the playground is a volunteer-supported open source
project. It would be infeasible to provide every possible crate.

This inclusion policy is used to avoid "playing favorites" for which
crates are available. Hand-picking crates will lead to resentment
about which crates were not included between the playground
maintainers and crate authors or even the broader Rust community.
Neither of these outcomes is desired.

## Exclusion policy

Occasionally, some crates that would otherwise meet the above criteria
will not be available on the playground. A non-exhaustive list of
reasons is:

- Does not compile on Linux
- Does not compile on the stable release channel
- Does not compile due to invalid feature flag selection

In these cases, we will temporarily exclude the crate to allow the
playground to continue to be updated. We usually also notify the crate
maintainers so they can adjust their crates and be re-included.

## I don't like the current system!

We are open to well-reasoned [alternate algorithms][], but be aware
that any proposal would likely be expected to also provide the
majority of implementation work.

## I am a crate author and I want to control which features are available

When a crate is included in the playground, its Cargo.toml is
inspected for special metadata, similar to the [docs.rs
metadata][]. This will control what features we enable in addition to
the features needed by dependencies.

```toml
[package]
name = "test"

[package.metadata.playground]
default-features = true
features = ["std", "extra-traits"]
all-features = false
```

[prerelease]: https://semver.org/#spec-item-9
[all time downloads]: https://crates.io/crates?sort=downloads
[Rust cookbook]: https://rust-lang-nursery.github.io/rust-cookbook/
[alternate algorithms]: https://github.com/rust-lang/rust-playground/issues/101
[docs.rs metadata]: https://docs.rs/about/metadata
