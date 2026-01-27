// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, PackageId,
    graph::{
        DependencyDirection, PackageGraph, PackageIx, PackageLink, PackageResolver, PackageSet,
        cargo::build::CargoSetBuildState,
        feature::{FeatureGraph, FeatureSet},
    },
    platform::PlatformSpec,
    sorted_set::SortedSet,
};
use petgraph::prelude::*;
use serde::{Deserialize, Serialize};
use std::{collections::HashSet, fmt};

/// Options for queries which simulate what Cargo does.
///
/// This provides control over the resolution algorithm used by `guppy`'s simulation of Cargo.
#[derive(Clone, Debug)]
pub struct CargoOptions<'a> {
    pub(crate) resolver: CargoResolverVersion,
    pub(crate) include_dev: bool,
    pub(crate) initials_platform: InitialsPlatform,
    // Use Supercow here to ensure that owned Platform instances are boxed, to reduce stack size.
    pub(crate) host_platform: PlatformSpec,
    pub(crate) target_platform: PlatformSpec,
    pub(crate) omitted_packages: HashSet<&'a PackageId>,
}

impl<'a> CargoOptions<'a> {
    /// Creates a new `CargoOptions` with this resolver version and default settings.
    ///
    /// The default settings are similar to what a plain `cargo build` does:
    ///
    /// * use version 1 of the Cargo resolver
    /// * exclude dev-dependencies
    /// * do not build proc macros specified in the query on the target platform
    /// * resolve dependencies assuming any possible host or target platform
    /// * do not omit any packages.
    pub fn new() -> Self {
        Self {
            resolver: CargoResolverVersion::V1,
            include_dev: false,
            initials_platform: InitialsPlatform::Standard,
            host_platform: PlatformSpec::Any,
            target_platform: PlatformSpec::Any,
            omitted_packages: HashSet::new(),
        }
    }

    /// Sets the Cargo feature resolver version.
    ///
    /// For more about feature resolution, see the documentation for `CargoResolverVersion`.
    pub fn set_resolver(&mut self, resolver: CargoResolverVersion) -> &mut Self {
        self.resolver = resolver;
        self
    }

    /// If set to true, causes dev-dependencies of the initial set to be followed.
    ///
    /// This does not affect transitive dependencies -- for example, a build or dev-dependency's
    /// further dev-dependencies are never followed.
    ///
    /// The default is false, which matches what a plain `cargo build` does.
    pub fn set_include_dev(&mut self, include_dev: bool) -> &mut Self {
        self.include_dev = include_dev;
        self
    }

    /// Configures the way initials are treated on the target and the host.
    ///
    /// The default is a "standard" build and this does not usually need to be set, but some
    /// advanced use cases may require it. For more about this option, see the documentation for
    /// [`InitialsPlatform`](InitialsPlatform).
    pub fn set_initials_platform(&mut self, initials_platform: InitialsPlatform) -> &mut Self {
        self.initials_platform = initials_platform;
        self
    }

    /// Sets both the target and host platforms to the provided spec.
    pub fn set_platform(&mut self, platform_spec: impl Into<PlatformSpec>) -> &mut Self {
        let platform_spec = platform_spec.into();
        self.target_platform = platform_spec.clone();
        self.host_platform = platform_spec;
        self
    }

    /// Sets the target platform to the provided spec.
    pub fn set_target_platform(&mut self, target_platform: impl Into<PlatformSpec>) -> &mut Self {
        self.target_platform = target_platform.into();
        self
    }

    /// Sets the host platform to the provided spec.
    pub fn set_host_platform(&mut self, host_platform: impl Into<PlatformSpec>) -> &mut Self {
        self.host_platform = host_platform.into();
        self
    }

    /// Omits edges into the given packages.
    ///
    /// This may be useful in order to figure out what additional dependencies or features a
    /// particular set of packages pulls in.
    ///
    /// This method is additive.
    pub fn add_omitted_packages(
        &mut self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> &mut Self {
        self.omitted_packages.extend(package_ids);
        self
    }
}

impl Default for CargoOptions<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// The version of Cargo's feature resolver to use.
#[derive(Copy, Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[cfg_attr(feature = "proptest1", derive(proptest_derive::Arbitrary))]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum CargoResolverVersion {
    /// The "classic" feature resolver in Rust.
    ///
    /// This feature resolver unifies features across inactive platforms, and also unifies features
    /// across normal, build and dev dependencies for initials. This may produce results that are
    /// surprising at times.
    #[serde(rename = "1", alias = "v1")]
    V1,

    /// The "classic" feature resolver in Rust, as used by commands like `cargo install`.
    ///
    /// This resolver is the same as `V1`, except it doesn't unify features across dev dependencies
    /// for initials. However, if `CargoOptions::with_dev_deps` is set to true, it behaves
    /// identically to the V1 resolver.
    ///
    /// For more, see
    /// [avoid-dev-deps](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#avoid-dev-deps)
    /// in the Cargo reference.
    #[serde(rename = "install", alias = "v1-install")]
    V1Install,

    /// [Version 2 of the feature resolver](https://doc.rust-lang.org/cargo/reference/resolver.html#feature-resolver-version-2),
    /// available since Rust 1.51. This feature resolver does not unify features:
    ///
    /// * across host (build) and target (regular) dependencies
    /// * with dev-dependencies for initials, if tests aren't currently being built
    /// * with [platform-specific dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies) that are currently inactive
    ///
    /// Version 2 of the feature resolver can be enabled by specifying `resolver
    /// = "2"` in the workspace's `Cargo.toml`. It is also [the default resolver
    /// version](https://doc.rust-lang.org/beta/edition-guide/rust-2021/default-cargo-resolver.html)
    /// for [the Rust 2021
    /// edition](https://doc.rust-lang.org/edition-guide/rust-2021/index.html).
    #[serde(rename = "2", alias = "v2")]
    V2,

    /// [Version 3 of the dependency
    /// resolver](https://doc.rust-lang.org/beta/cargo/reference/resolver.html#resolver-versions),
    /// available since Rust 1.84.
    ///
    /// Version 3 of the resolver enables [MSRV-aware dependency
    /// resolution](https://doc.rust-lang.org/beta/cargo/reference/config.html#resolverincompatible-rust-versions).
    /// There are no changes to feature resolution compared to version 2.
    ///
    /// Version 3 of the feature resolver can be enabled by specifying `resolver
    /// = "3"` in the workspace's `Cargo.toml`. It is also [the default resolver
    /// version](https://doc.rust-lang.org/beta/edition-guide/rust-2024/cargo-resolver.html)
    /// for [the Rust 2024
    /// edition](https://doc.rust-lang.org/beta/edition-guide/rust-2024/index.html).
    #[serde(rename = "3", alias = "v3")]
    V3,
}

/// For a given Cargo build simulation, what platform to assume the initials are being built on.
#[derive(Copy, Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[cfg_attr(feature = "proptest1", derive(proptest_derive::Arbitrary))]
#[serde(rename_all = "kebab-case")]
pub enum InitialsPlatform {
    /// Assume that the initials are being built on the host platform.
    ///
    /// This is most useful for "continuing" simulations, where it is already known that some
    /// packages are being built on the host and one wishes to find their dependencies.
    Host,

    /// Assume a standard build.
    ///
    /// In this mode, all initials other than proc-macros are built on the target platform. Proc-
    /// macros, being compiler plugins, are built on the host.
    ///
    /// This is the default for `InitialsPlatform`.
    Standard,

    /// Perform a standard build, and also build proc-macros on the target.
    ///
    /// Proc-macro crates may include tests, which are run on the target platform. This option is
    /// most useful for such situations.
    ProcMacrosOnTarget,
}

/// The default for `InitialsPlatform`: the `Standard` option.
impl Default for InitialsPlatform {
    fn default() -> Self {
        InitialsPlatform::Standard
    }
}

/// A set of packages and features, as would be built by Cargo.
///
/// Cargo implements a set of algorithms to figure out which packages or features are built in
/// a given situation. `guppy` implements those algorithms.
#[derive(Clone, Debug)]
pub struct CargoSet<'g> {
    pub(super) initials: FeatureSet<'g>,
    pub(super) features_only: FeatureSet<'g>,
    pub(super) target_features: FeatureSet<'g>,
    pub(super) host_features: FeatureSet<'g>,
    pub(super) target_direct_deps: PackageSet<'g>,
    pub(super) host_direct_deps: PackageSet<'g>,
    pub(super) proc_macro_edge_ixs: SortedSet<EdgeIndex<PackageIx>>,
    pub(super) build_dep_edge_ixs: SortedSet<EdgeIndex<PackageIx>>,
    pub(super) target_edge_ixs: SortedSet<EdgeIndex<PackageIx>>,
    pub(super) host_edge_ixs: SortedSet<EdgeIndex<PackageIx>>,
}

assert_covariant!(CargoSet);

impl<'g> CargoSet<'g> {
    /// Simulates a Cargo build of this feature set, with the given options.
    ///
    /// The feature sets are expected to be entirely within the workspace. Its behavior outside the
    /// workspace isn't defined and may be surprising.
    ///
    /// `CargoSet::new` takes two `FeatureSet` instances:
    /// * `initials`, from which dependencies are followed to build the `CargoSet`.
    /// * `features_only`, which are additional inputs that are only used for feature
    ///   unification. This may be used to simulate, e.g. `cargo build --package foo --package bar`,
    ///   when you only care about the results of `foo` but specifying `bar` influences the build.
    ///
    /// Note that even if a package is in `features_only`, it may be included in the final build set
    /// through other means (for example, if it is also in `initials` or it is a dependency of one
    /// of them).
    ///
    /// In many cases `features_only` is empty -- in that case you may wish to use
    /// `FeatureSet::into_cargo_set()`, and it may be more convenient to use that if the code is
    /// written in a "fluent" style.
    ///
    ///
    pub fn new(
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        opts: &CargoOptions<'_>,
    ) -> Result<Self, Error> {
        Self::new_internal(initials, features_only, None, opts)
    }

    /// Like `Cargo.new`, but takes an additional [`PackageResolver`] which can
    /// be used to filter out some dependency edges, or to collect additional
    /// information.
    ///
    /// [`resolver.accept`] is called for both target and host dependencies. It
    /// is called after static filtering through
    /// [`CargoOptions::add_omitted_packages`], but before any other decisions
    /// are made.
    ///
    /// [`resolver.accept`]: PackageResolver::accept
    pub fn with_package_resolver(
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        mut resolver: impl PackageResolver<'g>,
        opts: &CargoOptions<'_>,
    ) -> Result<Self, Error> {
        Self::new_internal(initials, features_only, Some(&mut resolver), opts)
    }

    /// Internal helper to deduplicate code across `CargoSet::new` and `CargoSet::with_resolver`.
    fn new_internal(
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        resolver: Option<&mut dyn PackageResolver<'g>>,
        opts: &CargoOptions<'_>,
    ) -> Result<Self, Error> {
        let build_state = CargoSetBuildState::new(initials.graph().package_graph, opts)?;
        Ok(build_state.build(initials, features_only, resolver))
    }

    /// Creates a new `CargoIntermediateSet` based on the given query and options.
    ///
    /// This set contains an over-estimate of targets and features.
    ///
    /// Not part of the stable API, exposed for testing.
    #[doc(hidden)]
    pub fn new_intermediate(
        initials: &FeatureSet<'g>,
        opts: &CargoOptions<'_>,
    ) -> Result<CargoIntermediateSet<'g>, Error> {
        let build_state = CargoSetBuildState::new(initials.graph().package_graph, opts)?;
        Ok(build_state.build_intermediate(initials.to_feature_query(DependencyDirection::Forward)))
    }

    /// Returns the feature graph for this `CargoSet` instance.
    pub fn feature_graph(&self) -> &FeatureGraph<'g> {
        self.initials.graph()
    }

    /// Returns the package graph for this `CargoSet` instance.
    pub fn package_graph(&self) -> &'g PackageGraph {
        self.feature_graph().package_graph
    }

    /// Returns the initial packages and features from which the `CargoSet` instance was
    /// constructed.
    pub fn initials(&self) -> &FeatureSet<'g> {
        &self.initials
    }

    /// Returns the packages and features that took part in feature unification but were not
    /// considered part of the final result.
    ///
    /// For more about `features_only` and how it influences the build, see the documentation for
    /// [`CargoSet::new`](CargoSet::new).
    pub fn features_only(&self) -> &FeatureSet<'g> {
        &self.features_only
    }

    /// Returns the feature set enabled on the target platform.
    ///
    /// This represents the packages and features that are included as code in the final build
    /// artifacts. This is relevant for both cross-compilation and auditing.
    pub fn target_features(&self) -> &FeatureSet<'g> {
        &self.target_features
    }

    /// Returns the feature set enabled on the host platform.
    ///
    /// This represents the packages and features that influence the final build artifacts, but
    /// whose code is generally not directly included.
    ///
    /// This includes all procedural macros, including those specified in the initial query.
    pub fn host_features(&self) -> &FeatureSet<'g> {
        &self.host_features
    }

    /// Returns the feature set enabled on the specified build platform.
    pub fn platform_features(&self, build_platform: BuildPlatform) -> &FeatureSet<'g> {
        match build_platform {
            BuildPlatform::Target => self.target_features(),
            BuildPlatform::Host => self.host_features(),
        }
    }

    /// Returns the feature sets across the target and host build platforms.
    pub fn all_features(&self) -> [(BuildPlatform, &FeatureSet<'g>); 2] {
        [
            (BuildPlatform::Target, self.target_features()),
            (BuildPlatform::Host, self.host_features()),
        ]
    }

    /// Returns the set of workspace and direct dependency packages on the target platform.
    ///
    /// The packages in this set are a subset of the packages in `target_features`.
    pub fn target_direct_deps(&self) -> &PackageSet<'g> {
        &self.target_direct_deps
    }

    /// Returns the set of workspace and direct dependency packages on the host platform.
    ///
    /// The packages in this set are a subset of the packages in `host_features`.
    pub fn host_direct_deps(&self) -> &PackageSet<'g> {
        &self.host_direct_deps
    }

    /// Returns the set of workspace and direct dependency packages on the specified build platform.
    pub fn platform_direct_deps(&self, build_platform: BuildPlatform) -> &PackageSet<'g> {
        match build_platform {
            BuildPlatform::Target => self.target_direct_deps(),
            BuildPlatform::Host => self.host_direct_deps(),
        }
    }

    /// Returns the set of workspace and direct dependency packages across the target and host
    /// build platforms.
    pub fn all_direct_deps(&self) -> [(BuildPlatform, &PackageSet<'g>); 2] {
        [
            (BuildPlatform::Target, self.target_direct_deps()),
            (BuildPlatform::Host, self.host_direct_deps()),
        ]
    }

    /// Returns `PackageLink` instances for procedural macro dependencies from target packages.
    ///
    /// Procedural macros straddle the line between target and host: they're built for the host
    /// but generate code that is compiled for the target platform.
    ///
    /// ## Notes
    ///
    /// Procedural macro packages will be included in the *host* feature set.
    /// See also [`Self::host_features`].
    ///
    /// The returned iterator will include proc macros that are depended on normally or in dev
    /// builds from initials (if `include_dev` is set), but not the ones in the
    /// `[build-dependencies]` section.
    pub fn proc_macro_links<'a>(&'a self) -> impl ExactSizeIterator<Item = PackageLink<'g>> + 'a {
        let package_graph = self.target_features.graph().package_graph;
        self.proc_macro_edge_ixs
            .iter()
            .map(move |edge_ix| package_graph.edge_ix_to_link(*edge_ix))
    }

    /// Returns `PackageLink` instances for build dependencies from target packages.
    ///
    /// ## Notes
    ///
    /// For each link, the `from` is built on the target while the `to` is built on the host.
    /// It is possible (though rare) that a build dependency is also included as a normal
    /// dependency, or as a dev dependency in which case it will also be built on the target.
    ///
    /// The returned iterators will not include build dependencies of host packages -- those are
    /// also built on the host.
    pub fn build_dep_links<'a>(&'a self) -> impl ExactSizeIterator<Item = PackageLink<'g>> + 'a {
        let package_graph = self.target_features.graph().package_graph;
        self.build_dep_edge_ixs
            .iter()
            .map(move |edge_ix| package_graph.edge_ix_to_link(*edge_ix))
    }

    /// Returns `PackageLink` instances for normal dependencies between target packages.
    ///
    /// ## Notes
    ///
    /// For each link, both the `from` and the `to` package are built on the target.
    ///
    /// Target packages will be included in the *target* feature set.
    /// See also [`Self::target_features`].
    pub fn target_links<'a>(&'a self) -> impl ExactSizeIterator<Item = PackageLink<'g>> + 'a {
        let package_graph = self.target_features.graph().package_graph;
        self.target_edge_ixs
            .iter()
            .map(move |edge_ix| package_graph.edge_ix_to_link(*edge_ix))
    }

    /// Returns `PackageLink` instances for dependencies between host packages.
    ///
    /// ## Notes
    ///
    /// For each link, both the `from` and the `to` package are built on the host.
    /// Typically most links are normal dependencies, but it is possible to have
    /// build dependencies as well (e.g. dependencies of a build script used
    /// in a proc-macro package).
    ///
    /// Host packages will be included in the *host* feature set.
    /// See also [`Self::host_features`].
    pub fn host_links<'a>(&'a self) -> impl ExactSizeIterator<Item = PackageLink<'g>> + 'a {
        let package_graph = self.target_features.graph().package_graph;
        self.host_edge_ixs
            .iter()
            .map(move |edge_ix| package_graph.edge_ix_to_link(*edge_ix))
    }
}

/// Either the target or the host platform.
///
/// When Cargo computes the platforms it is building on, it computes two separate build graphs: one
/// for the target platform and one for the host. This is most useful in cross-compilation
/// situations where the target is different from the host, but the separate graphs are computed
/// whether or not a build cross-compiles.
///
/// A `cargo check` can be looked at as a kind of cross-compilation as well--machine code is
/// generated and run for the host platform but not the target platform. This is why `cargo check`
/// output usually has some lines that say `Compiling` (for the host platform) and some that say
/// `Checking` (for the target platform).
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BuildPlatform {
    /// The target platform.
    ///
    /// This represents the packages and features that are included as code in the final build
    /// artifacts.
    Target,

    /// The host platform.
    ///
    /// This represents build scripts, proc macros and other code that is run on the machine doing
    /// the compiling.
    Host,
}

impl BuildPlatform {
    /// A list of all possible variants of `BuildPlatform`.
    pub const VALUES: &'static [Self; 2] = &[BuildPlatform::Target, BuildPlatform::Host];

    /// Returns the build platform that's not `self`.
    pub fn flip(self) -> Self {
        match self {
            BuildPlatform::Host => BuildPlatform::Target,
            BuildPlatform::Target => BuildPlatform::Host,
        }
    }
}

impl fmt::Display for BuildPlatform {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildPlatform::Target => write!(f, "target"),
            BuildPlatform::Host => write!(f, "host"),
        }
    }
}

/// An intermediate set representing an overestimate of what packages are built, but an accurate
/// summary of what features are built given a particular package.
///
/// Not part of the stable API, exposed for cargo-compare.
#[doc(hidden)]
#[derive(Debug)]
pub enum CargoIntermediateSet<'g> {
    Unified(FeatureSet<'g>),
    TargetHost {
        target: FeatureSet<'g>,
        host: FeatureSet<'g>,
    },
}

impl<'g> CargoIntermediateSet<'g> {
    #[doc(hidden)]
    pub fn target_host_sets(&self) -> (&FeatureSet<'g>, &FeatureSet<'g>) {
        match self {
            CargoIntermediateSet::Unified(set) => (set, set),
            CargoIntermediateSet::TargetHost { target, host } => (target, host),
        }
    }
}
