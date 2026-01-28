// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Demonstration how `CargoSet` algorithm can accept links that are present on:
//!
//! 1) any/all platforms (using default `CargoOptions` and `CargoSet::new`)
//! 2) a single platform (using `CargoOptions::set_target_platform`)
//! 3) a set of platforms (using `CargoSet::with_resolver`)
//!
//! The last example uses `PackageResolver` as a filter - this is a very
//! generic mechanism and can be used to not only filter by platforms,
//! but also implement a variety of other filtering options.  For example,
//! `CargoOptions::add_omitted_packages` could also be implemented using
//! `CargoSet::with_resolver` and an appropriate `PackageResolver`.

use guppy::{
    CargoMetadata, Error,
    graph::{
        DependencyDirection, DependencyReq, PackageLink, PackageQuery, PackageResolver,
        cargo::{CargoOptions, CargoSet},
        feature::StandardFeatures,
    },
    platform::{EnabledTernary, PlatformSpec, PlatformStatus, Triple},
};

/// Custom `guppy::graph::PackageResolver` that will only accept `PackageLink`s
/// that are enabled on at least one from the given set of platforms.
struct PackageResolverForPlatformSet(Vec<PlatformSpec>);

impl PackageResolverForPlatformSet {
    fn new(platform_set: Vec<PlatformSpec>) -> Self {
        Self(platform_set)
    }

    fn can_platform_status_be_true(&self, platform_status: PlatformStatus) -> bool {
        self.0.iter().any(|platform_spec| {
            let is_enabled = platform_status.enabled_on(platform_spec);
            is_enabled == EnabledTernary::Enabled
        })
    }

    fn should_include_dependency_req(&self, dependency_req: DependencyReq) -> bool {
        dependency_req.is_present()
            && (self.can_platform_status_be_true(dependency_req.status().optional_status())
                || self.can_platform_status_be_true(dependency_req.status().required_status()))
    }
}

impl<'g> PackageResolver<'g> for PackageResolverForPlatformSet {
    fn accept(&mut self, _query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        self.should_include_dependency_req(link.normal())
            || self.should_include_dependency_req(link.build())
    }
}

fn win32_platform_spec() -> PlatformSpec {
    PlatformSpec::Platform(std::sync::Arc::new(target_spec::Platform::from_triple(
        Triple::new_strict("i686-pc-windows-gnu").unwrap(),
        target_spec::TargetFeatures::features([
            // The full feature list for this target triple can be found with
            // `rustc --target i686-pc-windows-gnu --print=cfg`, but for
            // simplicity we only list ones that are relevant for `region` and
            // `winapi` dependency selection).
            "windows",
        ]),
    )))
}

fn win64_platform_spec() -> PlatformSpec {
    PlatformSpec::Platform(std::sync::Arc::new(target_spec::Platform::from_triple(
        Triple::new_strict("x86_64-pc-windows-gnu").unwrap(),
        target_spec::TargetFeatures::features([
            // The full feature list for this target triple can be found with
            // `rustc --target x86_64-pc-windows-gnu --print=cfg`, but for
            // simplicity we only list ones that are relevant for `region` and
            // `winapi` dependency selection).
            "windows",
        ]),
    )))
}

fn cargo_set_to_package_names(cargo_set: CargoSet) -> Vec<String> {
    let mut result = cargo_set
        .target_features()
        .packages_with_features(DependencyDirection::Forward)
        .map(|feature_list| {
            format!(
                "{}-{}",
                feature_list.package().name(),
                feature_list.package().version(),
            )
        })
        .collect::<Vec<_>>();
    result.sort();
    result
}

fn main() -> Result<(), Error> {
    // `guppy` accepts as input the JSON output from `cargo metadata`.
    // In this example we use a pre-recorded metadata that has been stored in `metadata1.json`.
    // In this example metadata:
    //
    // * The `winapi` crate depends on either `winapi-i686-pc-windows-gnu` or
    //   `winapi-x86_64-pc-windows-gnu` crate:
    //
    //     ```
    //     [target.i686-pc-windows-gnu.dependencies.winapi-i686-pc-windows-gnu]
    //     version = "0.4"
    //     [target.x86_64-pc-windows-gnu.dependencies.winapi-x86_64-pc-windows-gnu]
    //     version = "0.4"
    //     ```
    //
    // * The `region-2.1.2` package depends on either `mach` or `winapi`:
    //
    //     ```
    //     [target."cfg(any(target_os = \"macos\", target_os = \"ios\"))".dependencies.mach]
    //     version = "0.2"
    //     [target."cfg(windows)".dependencies.winapi]
    //     version = "0.3"
    //     ```
    let metadata = CargoMetadata::parse_json(include_str!("../../fixtures/small/metadata1.json"))?;
    let package_graph = metadata.build_graph()?;
    let initials = package_graph
        .resolve_package_name("region")
        .to_feature_set(StandardFeatures::Default);
    let no_extra_features = package_graph
        .resolve_none()
        .to_feature_set(StandardFeatures::Default);

    // First, we get a set of packages that will be built on **any/all** possible platforms.
    let all_platforms_package_names = {
        let cargo_options = CargoOptions::new();
        let cargo_set = CargoSet::new(initials.clone(), no_extra_features.clone(), &cargo_options)?;
        cargo_set_to_package_names(cargo_set)
    };
    assert_eq!(
        all_platforms_package_names,
        vec![
            "bitflags-1.1.0",
            "libc-0.2.62",
            "mach-0.2.3",
            "region-2.1.2",
            "winapi-0.3.8",
            "winapi-i686-pc-windows-gnu-0.4.0",
            "winapi-x86_64-pc-windows-gnu-0.4.0"
        ],
    );

    // Then, get a set of packages for a **single** platform (by using
    // `CargoOptions.set_target_platform`).
    let single_platform_package_names = {
        let mut cargo_options = CargoOptions::new();
        cargo_options.set_target_platform(win32_platform_spec());
        let cargo_set = CargoSet::new(initials.clone(), no_extra_features.clone(), &cargo_options)?;
        cargo_set_to_package_names(cargo_set)
    };
    assert_eq!(
        single_platform_package_names,
        vec![
            "bitflags-1.1.0",
            "libc-0.2.62",
            // No "mach-0.2.3" on `win32_platform_spec`.
            "region-2.1.2",
            "winapi-0.3.8",
            // No "winapi-x86_64-pc-windows-gnu-0.4.0" on `win32_platform_spec`.
            "winapi-i686-pc-windows-gnu-0.4.0",
        ],
    );

    // Finally, get a set of packages for a set of target platforms
    // (by passing a custom resolver to `CargoSet::with_resolver`).
    let platform_set_package_names = {
        let cargo_options = CargoOptions::new();
        let resolver =
            PackageResolverForPlatformSet::new(vec![win32_platform_spec(), win64_platform_spec()]);
        let cargo_set =
            CargoSet::with_package_resolver(initials, no_extra_features, resolver, &cargo_options)?;
        cargo_set_to_package_names(cargo_set)
    };
    assert_eq!(
        platform_set_package_names,
        vec![
            "bitflags-1.1.0",
            "libc-0.2.62",
            // No "mach-0.2.3" in a union of `win32_platform_spec` and `win64_platform_spec`.
            "region-2.1.2",
            "winapi-0.3.8",
            // Both `winapi-i686-...` and `winapi-x86_64-...` crates are present in
            // a union of `win32_platform_spec` and `win64_platform_spec`.
            "winapi-i686-pc-windows-gnu-0.4.0",
            "winapi-x86_64-pc-windows-gnu-0.4.0"
        ],
    );

    Ok(())
}
