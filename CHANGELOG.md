# Changelog

## Releases

We track releases and release notes using [GitHub
Releases](https://github.com/google/zerocopy/releases).

## Yanks and Regressions

### 0.2.2 through 0.2.8, 0.3.0 through 0.3.1, 0.4.0, 0.5.0, 0.6.0 through 0.6.5, 0.7.0 through 0.7.30

In these versions, the `Ref` methods `into_ref`, `into_mut`, `into_slice`, and
`into_mut_slice` were permitted in combination with the standard library
`cell::Ref` and `cell::RefMut` types for `Ref<B, T>`'s `B` type parameter. These
combinations are unsound, and may permit safe code to exhibit undefined
behavior. Fixes have been published to each affected minor version which do not
permit this code to compile.

See [#716][issue-716] for more details.

[issue-716]: https://github.com/google/zerocopy/issues/716

### 0.7.27, 0.7.28

These versions were briefly yanked due to a non-soundness regression reported in
[#672][pull-672]. After reconsidering our yanking policy in [#679][issue-679],
we un-yanked these versions.

[pull-672]: https://github.com/google/zerocopy/pull/672
[issue-679]: https://github.com/google/zerocopy/issues/679
