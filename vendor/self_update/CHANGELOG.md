# Changelog

## [unreleased]
### Added
### Changed
### Removed

## [0.42.0]
### Added
- Improved release search/lookup capability to support filtering assets by identifier
- Improved version specifications to support prelease tags and parallel supported versions
### Changed
- Update reqwest features to allow http2 negotiation
- Update quick-xml (0.37) and zipsign (0.1)
- Specify per_page=100 when fetching github releases
### Removed

## [0.41.0]
### Added
### Changed
- Update to zip 2.x
### Removed

## [0.40.0]
### Added
### Changed
- `Release::asset_for` now searches for current `OS` and `ARCH` inside `asset.name` if `target` failed to match
- Update `reqwest` to `0.12.0`
- Update `hyper` to `1.2.0`
- Support variable substitutions in `bin_path_in_archive` at runtime
### Removed

## [0.39.0]
### Added
- Add `signatures` feature to support verifying zip/tar.gz artifacts using [zipsign](https://github.com/Kijewski/zipsign)
### Changed
- MSRV = 1.64
### Removed

## [0.38.0]
### Added
### Changed
- Use `self-replace` to replace the current executable
### Removed

## [0.37.0]
### Added
### Changed
- Bugfix: use appropriate auth headers for each backend (fix gitlab private repo updates)
### Removed

## [0.36.0]
### Added
### Changed
- For the gitlab backend, urlencode the repo owner in API calls to handle cases where the repo is owned by a subgroup
### Removed

## [0.35.0]
### Added
### Changed
- Support selecting from multiple release artifacts by specifying an `identifier`
- Update `quick-xml` to `0.23.0`
### Removed

## [0.34.0]
### Added
- Add `with_url` method to `UpdateBuilder`
### Changed
### Removed

## [0.33.0]
### Added
- Support for Gitea / Forgejo
### Changed
### Removed

## [0.32.0]
### Added
- Support for self hosted gitlab servers
### Changed
### Removed

## [0.31.0]
### Added
- Support S3 dualstack endpoints
### Changed
- Update `indicatif` 0.16.0 -> 0.17.0
### Removed

## [0.30.0]
### Added
### Changed
- Bump `semver` 0.11 -> 1.0
### Removed

## [0.29.0]
### Added
### Changed
- Bump `zip` 0.5 -> 0.6
- Bump `quick-xml` 0.20 -> 0.22
### Removed

## [0.28.0]
### Added
### Changed
- Bump indicatif 0.15 -> 0.16
### Removed

## [0.27.0]
### Added
### Changed
- Switch gitlab authorization header prefix from `token` to `Bearer`
### Removed

## [0.26.0]
### Added
### Changed
- Clean up dangling temporary directories on Windows.
### Removed

## [0.25.0]
### Added
### Changed
- Fix io error triggered when updating binary contained in a zipped folder.
- Fix issues updating Windows binaries on non-`C:` drives.
### Removed

## [0.24.0]
### Added
### Changed
- `UpdateBuilder.bin_name` will add the platform-specific exe suffix on the S3 backend.
### Removed

## [0.23.0]
### Added
### Changed
- update `reqwest` to `0.11`
- remove `hyper-old-types` dependency, replace the rel-link-header parsing
  with a manual parsing function: `find_rel_next_link`
### Removed

## [0.22.0]
### Added
### Changed
- bump dependencies
- print out tooling versions in CI
### Removed

## [0.21.0]
### Added
- Add GCS support to S3 backend
### Changed
- Fixed docs refering to github in s3 backend
### Removed

## [0.20.0]
### Added
- Add DigitalOcean Spaces support to S3 backend
### Changed
### Removed

## [0.19.0]
### Added
- Add `Download::set_header` for inserting into the download request's headers.
### Changed
- Update readme example to add `Accept: application/octet-stream` header. Release parsing
  was updated in 0.7.0 to use the github-api download url instead of the browser
  url so auth headers can be passed. When using the github-api download url, you
  need to pass `Accept: application/octet-stream` in order to get back a 302
  redirecting you to the "raw" download url. This was already being handled in
  `ReleaseUpdate::update_extended`, but wasn't added to the readme example.
### Removed

## [0.18.0]
### Added
- Allow specifying a custom github api url
### Changed
### Removed

## [0.17.0]
### Added
- Support for Gitlab
- Gitlab example
### Changed
- `UpdateBuilder.bin_name` will add the platform-specific exe suffix (defined
  by `std::env::consts::EXE_SUFFIX`) to the end of binary names if it's missing.
  This was a fix for windows.
### Removed

## [0.16.0]
### Added
### Changed
- switch from `tempdir` to `tempfile`
### Removed

## [0.15.0]
### Added
- Handling for `.tgz` files
### Changed
- Support version tags with or without leading `v`
- S3, support path prefixes that contain directories
### Removed

## [0.14.0]
### Added
- Expose `body` string in `Release` data
### Changed
### Removed

## [0.13.0]
### Added
- Feature flag `rustls` to enable using [rustls](https://github.com/ctz/rustls) instead of native openssl implementations.
### Changed
### Removed

## [0.12.0]
### Added
### Changed
- Make all archive and compression dependencies optional, available behind
  feature flags, and off by default. The feature flags are listed in the
  README. The common github-release use-case (tar.gz) requires the features
  `archive-tar compression-flate2`
- Make the `update` module public
### Removed

## [0.11.1]
### Added
### Changed
- add rust highlighting tag to doc example
### Removed

## [0.11.0]
### Added
### Changed
- set executable bits on non-windows
### Removed

## [0.10.0]
### Added
### Changed
- update reqwest to 0.10, add default user-agent to requests
- update indicatif to 0.13
### Removed

## [0.9.0]
### Added
- support for Amazon S3 as releases backend server
### Changed
- use `Update` trait in GitHub backend implementation for code re-usability
### Removed

## [0.8.0]
### Added

### Changed
- use the system temp directory on windows

### Removed

## [0.7.0]
### Added
### Changed
- accept `auth_token` in `Update` to allow obtaining releases from private GitHub repos
- use GitHub api url instead of browser url to download assets so that auth can be used for private repos
- accept headers in `Download` that can be used in GET request to download url (required for passing in auth token for private GitHub repos)
### Removed

## [0.6.0]
### Added
### Changed
- use indicatif instead of pbr
- update to rust 2018
- determine target arch at build time
### Removed


## [0.5.1]
### Added
- expose a more detailed `GitHubUpdateStatus`

### Changed
### Removed


## [0.5.0]
### Added
- zip archive support
- option to extract a single file

### Changed
- renamed github-updater `bin_path_in_tarball` to `bin_path_in_archive`

### Removed


## [0.4.5]
### Added
- freebsd support

### Changed

### Removed


## [0.4.4]
### Added

### Changed
- bump reqwest

### Removed


## [0.4.3]
### Added

### Changed
- Update readme - mention `trust` for producing releases
- Update `version` module docs

### Removed
- `macro` module is no longer public
    - `cargo_crate_version!` is still exported


## [0.4.2]
### Added
- `version` module for comparing semver tags more explicitly

### Changed
- Add deprecation warning for replacing `should_update` with `version::bump_is_compatible`
- Update the github `update` method to display the compatibility of new release versions.

### Removed
