// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    DependencyKind, Error,
    graph::{
        DependencyDirection, PackageGraph, PackageIx, PackageLink, PackageResolver, PackageSet,
        cargo::{
            CargoIntermediateSet, CargoOptions, CargoResolverVersion, CargoSet, InitialsPlatform,
        },
        feature::{ConditionalLink, FeatureLabel, FeatureQuery, FeatureSet, StandardFeatures},
    },
    platform::{EnabledTernary, PlatformSpec},
    sorted_set::SortedSet,
};
use fixedbitset::FixedBitSet;
use petgraph::{prelude::*, visit::VisitMap};

pub(super) struct CargoSetBuildState<'a> {
    opts: &'a CargoOptions<'a>,
    omitted_packages: SortedSet<NodeIndex<PackageIx>>,
}

impl<'a> CargoSetBuildState<'a> {
    pub(super) fn new<'g>(
        graph: &'g PackageGraph,
        opts: &'a CargoOptions<'a>,
    ) -> Result<Self, Error> {
        let omitted_packages: SortedSet<_> =
            graph.package_ixs(opts.omitted_packages.iter().copied())?;

        Ok(Self {
            opts,
            omitted_packages,
        })
    }

    pub(super) fn build<'g>(
        self,
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        resolver: Option<&mut dyn PackageResolver<'g>>,
    ) -> CargoSet<'g> {
        match self.opts.resolver {
            CargoResolverVersion::V1 => self.new_v1(initials, features_only, resolver, false),
            CargoResolverVersion::V1Install => {
                let avoid_dev_deps = !self.opts.include_dev;
                self.new_v1(initials, features_only, resolver, avoid_dev_deps)
            }
            // V2 and V3 do the same feature resolution.
            CargoResolverVersion::V2 | CargoResolverVersion::V3 => {
                self.new_v2(initials, features_only, resolver)
            }
        }
    }

    pub(super) fn build_intermediate(self, query: FeatureQuery) -> CargoIntermediateSet {
        match self.opts.resolver {
            CargoResolverVersion::V1 => self.new_v1_intermediate(query, false),
            CargoResolverVersion::V1Install => {
                let avoid_dev_deps = !self.opts.include_dev;
                self.new_v1_intermediate(query, avoid_dev_deps)
            }
            CargoResolverVersion::V2 | CargoResolverVersion::V3 => self.new_v2_intermediate(query),
        }
    }

    fn new_v1<'g>(
        self,
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        resolver: Option<&mut dyn PackageResolver<'g>>,
        avoid_dev_deps: bool,
    ) -> CargoSet<'g> {
        self.build_set(initials, features_only, resolver, |query| {
            self.new_v1_intermediate(query, avoid_dev_deps)
        })
    }

    fn new_v2<'g>(
        self,
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        resolver: Option<&mut dyn PackageResolver<'g>>,
    ) -> CargoSet<'g> {
        self.build_set(initials, features_only, resolver, |query| {
            self.new_v2_intermediate(query)
        })
    }

    // ---
    // Helper methods
    // ---

    fn is_omitted(&self, package_ix: NodeIndex<PackageIx>) -> bool {
        self.omitted_packages.contains(&package_ix)
    }

    fn build_set<'g>(
        &self,
        initials: FeatureSet<'g>,
        features_only: FeatureSet<'g>,
        mut resolver: Option<&mut dyn PackageResolver<'g>>,
        intermediate_fn: impl FnOnce(FeatureQuery<'g>) -> CargoIntermediateSet<'g>,
    ) -> CargoSet<'g> {
        // Prepare a package query for step 2.
        let graph = *initials.graph();
        // Note that currently, proc macros specified in initials are built on both the target and
        // the host.
        let mut host_ixs = Vec::new();
        let target_ixs: Vec<_> = initials
            .ixs_unordered()
            .filter_map(|feature_ix| {
                let metadata = graph.metadata_for_ix(feature_ix);
                let package_ix = metadata.package_ix();
                match self.opts.initials_platform {
                    InitialsPlatform::Host => {
                        // Always build on the host.
                        host_ixs.push(package_ix);
                        None
                    }
                    InitialsPlatform::Standard => {
                        // Proc macros on the host platform, everything else on the target platform.
                        if metadata.package().is_proc_macro() {
                            host_ixs.push(package_ix);
                            None
                        } else {
                            Some(package_ix)
                        }
                    }
                    InitialsPlatform::ProcMacrosOnTarget => {
                        // Proc macros on both the host and the target platforms, everything else
                        // on the target platform.
                        if metadata.package().is_proc_macro() {
                            host_ixs.push(package_ix);
                        }
                        Some(package_ix)
                    }
                }
            })
            .collect();
        let target_query = graph
            .package_graph
            .query_from_parts(SortedSet::new(target_ixs), DependencyDirection::Forward);

        // 1. Build the intermediate set containing the features for any possible package that can
        // be built, including features-only packages.
        let initials_plus_features_only = initials.union(&features_only);
        let intermediate_set = intermediate_fn(
            initials_plus_features_only.to_feature_query(DependencyDirection::Forward),
        );
        let (target_set, host_set) = intermediate_set.target_host_sets();

        // While doing traversal 2 below, record any packages discovered along build edges for use
        // in host ixs, to prepare for step 3. This will also include proc-macros.

        // This list will contain proc-macro edges out of target packages.
        let mut proc_macro_edge_ixs = Vec::new();
        // This list will contain build dep edges out of target packages.
        let mut build_dep_edge_ixs = Vec::new();
        // This list will contain edges between target packages.
        let mut target_edge_ixs = Vec::new();
        // This list will contain edges between host packages.
        let mut host_edge_ixs = Vec::new();

        let is_enabled = |feature_set: &FeatureSet<'_>,
                          link: &PackageLink<'_>,
                          kind: DependencyKind,
                          platform_spec: &PlatformSpec| {
            let (from, to) = link.endpoints();
            let req_status = link.req_for_kind(kind).status();
            // Check the complete set to figure out whether we look at required_on or
            // enabled_on.
            let consider_optional = feature_set
                .contains((from.id(), FeatureLabel::OptionalDependency(link.dep_name())))
                .unwrap_or_else(|_| {
                    // If the feature ID isn't present, it means the dependency wasn't declared
                    // as optional. In that case the value doesn't matter.
                    debug_assert!(
                        req_status.optional_status().is_never(),
                        "for {} -> {}, dep '{}' not declared as optional",
                        from.name(),
                        to.name(),
                        link.dep_name()
                    );
                    false
                });

            if consider_optional {
                req_status.enabled_on(platform_spec) != EnabledTernary::Disabled
            } else {
                req_status.required_on(platform_spec) != EnabledTernary::Disabled
            }
        };

        // Record workspace + direct third-party deps in these sets.
        let mut target_direct_deps =
            FixedBitSet::with_capacity(graph.package_graph.package_count());
        let mut host_direct_deps = FixedBitSet::with_capacity(graph.package_graph.package_count());

        // 2. Figure out what packages will be included on the target platform, i.e. normal + dev
        // (if requested).
        let target_platform = &self.opts.target_platform;
        let host_platform = &self.opts.host_platform;

        let target_packages = target_query.resolve_with_fn(|query, link| {
            let (from, to) = link.endpoints();

            if from.in_workspace() {
                // Mark initials in target_direct_deps.
                target_direct_deps.visit(from.package_ix());
            }

            if self.is_omitted(to.package_ix()) {
                // Pretend that the omitted set doesn't exist.
                return false;
            }

            let accepted = resolver
                .as_mut()
                .map(|r| r.accept(query, link))
                .unwrap_or(true);
            if !accepted {
                return false;
            }

            // Dev-dependencies are only considered if `from` is an initial.
            let consider_dev =
                self.opts.include_dev && query.starts_from(from.id()).expect("valid ID");
            // Build dependencies are only considered if there's a build script.
            let consider_build = from.has_build_script();

            let mut follow_target =
                is_enabled(target_set, &link, DependencyKind::Normal, target_platform)
                    || (consider_dev
                        && is_enabled(
                            target_set,
                            &link,
                            DependencyKind::Development,
                            target_platform,
                        ));

            // Proc macros build on the host, so for normal/dev dependencies redirect it to the host
            // instead.
            let proc_macro_redirect = follow_target && to.is_proc_macro();

            // Build dependencies are evaluated against the host platform.
            let build_dep_redirect = consider_build
                && is_enabled(target_set, &link, DependencyKind::Build, host_platform);

            // Finally, process what needs to be done.
            if build_dep_redirect || proc_macro_redirect {
                if from.in_workspace() {
                    // The 'to' node is either in the workspace or a direct dependency [a].
                    host_direct_deps.visit(to.package_ix());
                }
                host_ixs.push(to.package_ix());
            }
            if build_dep_redirect {
                build_dep_edge_ixs.push(link.edge_ix());
            }
            if proc_macro_redirect {
                proc_macro_edge_ixs.push(link.edge_ix());
                follow_target = false;
            }

            if from.in_workspace() && follow_target {
                // The 'to' node is either in the workspace or a direct dependency.
                target_direct_deps.visit(to.package_ix());
            }

            if follow_target {
                target_edge_ixs.push(link.edge_ix());
            }
            follow_target
        });

        // 3. Figure out what packages will be included on the host platform.
        let host_ixs = SortedSet::new(host_ixs);
        let host_packages = graph
            .package_graph
            .query_from_parts(host_ixs, DependencyDirection::Forward)
            .resolve_with_fn(|query, link| {
                let (from, to) = link.endpoints();
                if self.is_omitted(to.package_ix()) {
                    // Pretend that the omitted set doesn't exist.
                    return false;
                }

                let accepted = resolver
                    .as_mut()
                    .map(|r| r.accept(query, link))
                    .unwrap_or(true);
                if !accepted {
                    return false;
                }

                // All relevant nodes in host_ixs have already been added to host_direct_deps at [a].

                // Dev-dependencies are only considered if `from` is an initial.
                let consider_dev =
                    self.opts.include_dev && query.starts_from(from.id()).expect("valid ID");
                let consider_build = from.has_build_script();

                // Only normal and build dependencies are typically considered. Dev-dependencies of
                // initials are also considered.
                let res = is_enabled(host_set, &link, DependencyKind::Normal, host_platform)
                    || (consider_build
                        && is_enabled(host_set, &link, DependencyKind::Build, host_platform))
                    || (consider_dev
                        && is_enabled(host_set, &link, DependencyKind::Development, host_platform));

                if res {
                    if from.in_workspace() {
                        // The 'to' node is either in the workspace or a direct dependency.
                        host_direct_deps.visit(to.package_ix());
                    }
                    host_edge_ixs.push(link.edge_ix());
                    true
                } else {
                    false
                }
            });

        // Finally, the features are whatever packages were selected, intersected with whatever
        // features were selected.
        let target_features = target_packages
            .to_feature_set(StandardFeatures::All)
            .intersection(target_set);
        let host_features = host_packages
            .to_feature_set(StandardFeatures::All)
            .intersection(host_set);

        // Also construct the direct dep sets.
        let target_direct_deps =
            PackageSet::from_included(graph.package_graph(), target_direct_deps);
        let host_direct_deps = PackageSet::from_included(graph.package_graph, host_direct_deps);

        CargoSet {
            initials,
            features_only,
            target_features,
            host_features,
            target_direct_deps,
            host_direct_deps,
            proc_macro_edge_ixs: SortedSet::new(proc_macro_edge_ixs),
            build_dep_edge_ixs: SortedSet::new(build_dep_edge_ixs),
            target_edge_ixs: SortedSet::new(target_edge_ixs),
            host_edge_ixs: SortedSet::new(host_edge_ixs),
        }
    }

    fn new_v1_intermediate<'g>(
        &self,
        query: FeatureQuery<'g>,
        avoid_dev_deps: bool,
    ) -> CargoIntermediateSet<'g> {
        // Perform a "complete" feature query. This will provide more packages than will be
        // included in the final build, but for each package it will have the correct feature set.
        let complete_set = query.resolve_with_fn(|query, link| {
            if self.is_omitted(link.to().package_ix()) {
                // Pretend that the omitted set doesn't exist.
                false
            } else if !avoid_dev_deps
                && query
                    .starts_from(link.from().feature_id())
                    .expect("valid ID")
            {
                // Follow everything for initials.
                true
            } else {
                // Follow normal and build edges for everything else.
                !link.dev_only()
            }
        });

        CargoIntermediateSet::Unified(complete_set)
    }

    fn new_v2_intermediate<'g>(&self, query: FeatureQuery<'g>) -> CargoIntermediateSet<'g> {
        let graph = *query.graph();
        // Note that proc macros specified in initials take part in feature resolution
        // for both target and host ixs. If they didn't, then the query would be partitioned into
        // host and target ixs instead.
        // https://github.com/rust-lang/cargo/issues/8312
        let mut host_ixs: Vec<_> = query
            .params
            .initials()
            .iter()
            .filter_map(|feature_ix| {
                let metadata = graph.metadata_for_ix(*feature_ix);
                if self.opts.initials_platform == InitialsPlatform::Host
                    || metadata.package().is_proc_macro()
                {
                    // Proc macros are always unified on the host.
                    Some(metadata.feature_ix())
                } else {
                    // Everything else is built on the target.
                    None
                }
            })
            .collect();

        let is_enabled =
            |link: &ConditionalLink<'_>, kind: DependencyKind, platform_spec: &PlatformSpec| {
                let platform_status = link.status_for_kind(kind);
                platform_status.enabled_on(platform_spec) != EnabledTernary::Disabled
            };

        let target_query = if self.opts.initials_platform == InitialsPlatform::Host {
            // Empty query on the target.
            graph.query_from_parts(SortedSet::new(vec![]), DependencyDirection::Forward)
        } else {
            query
        };

        // Keep a copy of the target query for use in step 2.
        let target_query_2 = target_query.clone();

        // 1. Perform a feature query for the target.
        let target_platform = &self.opts.target_platform;
        let host_platform = &self.opts.host_platform;
        let target = target_query.resolve_with_fn(|query, link| {
            let (from, to) = link.endpoints();

            if self.is_omitted(to.package_ix()) {
                // Pretend that the omitted set doesn't exist.
                return false;
            }

            let consider_dev =
                self.opts.include_dev && query.starts_from(from.feature_id()).expect("valid ID");
            // This resolver doesn't check for whether this package has a build script.
            let mut follow_target = is_enabled(&link, DependencyKind::Normal, target_platform)
                || (consider_dev
                    && is_enabled(&link, DependencyKind::Development, target_platform));

            // Proc macros build on the host, so for normal/dev dependencies redirect it to the host
            // instead.
            let proc_macro_redirect = follow_target && to.package().is_proc_macro();

            // Build dependencies are evaluated against the host platform.
            let build_dep_redirect = {
                // If this is a dependency like:
                //
                // ```
                // [build-dependencies]
                // cc = { version = "1.0", optional = true }
                //
                // [features]
                // bundled = ["cc"]
                // ```
                //
                // Then, there is an implicit named feature here called "cc" on the target platform,
                // which enables the optional dependency "cc". But this does not mean that this
                // package itself is built on the host platform!
                //
                // Detect this situation by ensuring that the package ID of the `from` and `to`
                // nodes are different.
                from.package_id() != to.package_id()
                    && is_enabled(&link, DependencyKind::Build, host_platform)
            };

            // Finally, process what needs to be done.
            if build_dep_redirect || proc_macro_redirect {
                host_ixs.push(to.feature_ix());
            }
            if proc_macro_redirect {
                follow_target = false;
            }

            follow_target
        });

        // 2. Perform a feature query for the host.
        let host = graph
            .query_from_parts(SortedSet::new(host_ixs), DependencyDirection::Forward)
            .resolve_with_fn(|_, link| {
                let (from, to) = link.endpoints();
                if self.is_omitted(to.package_ix()) {
                    // Pretend that the omitted set doesn't exist.
                    return false;
                }
                // During feature resolution, the v2 resolver doesn't check for whether this package
                // has a build script. It also unifies dev dependencies of initials, even on the
                // host platform.
                let consider_dev = self.opts.include_dev
                    && target_query_2
                        .starts_from(from.feature_id())
                        .expect("valid ID");

                is_enabled(&link, DependencyKind::Normal, host_platform)
                    || is_enabled(&link, DependencyKind::Build, host_platform)
                    || (consider_dev
                        && is_enabled(&link, DependencyKind::Development, host_platform))
            });

        CargoIntermediateSet::TargetHost { target, host }
    }
}
