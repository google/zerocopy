// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use fixtures::json::JsonFixture;
use guppy::graph::{
    DependencyDirection, PackageLink, PackageQuery, PackageResolver,
    cargo::{CargoOptions, CargoSet},
    feature::StandardFeatures,
};
use std::collections::HashSet;

struct PackageResolverForTesting<'a, 'g> {
    /// Optional filter of `link`s.  If `None`, then all links are accepted.
    link_filter: Option<&'a dyn Fn(PackageLink<'g>) -> bool>,

    /// The `trace` field stores `link`s that were passed to `fn accept`.
    /// The links are formatted as `"foo@1.2.3 => bar@4.5.6"`.
    /// The links are stored in the order of `fn accept` calls.
    trace: Vec<String>,
}

impl<'a, 'g> PackageResolverForTesting<'a, 'g> {
    fn new() -> Self {
        Self {
            link_filter: None,
            trace: vec![],
        }
    }

    fn with_filter(f: &'a impl Fn(PackageLink<'g>) -> bool) -> Self {
        Self {
            link_filter: Some(f),
            trace: vec![],
        }
    }
}

fn link_to_string(link: &PackageLink) -> String {
    format!(
        "{}@{} => {}@{}",
        link.from().name(),
        link.from().version(),
        link.to().name(),
        link.to().version(),
    )
}

fn links_to_strings<'g>(links: impl IntoIterator<Item = PackageLink<'g>>) -> Vec<String> {
    let mut result = links
        .into_iter()
        .map(|link| link_to_string(&link))
        .collect::<Vec<_>>();
    result.sort();
    result
}

impl<'g> PackageResolver<'g> for PackageResolverForTesting<'_, 'g> {
    fn accept(&mut self, _query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        self.trace.push(link_to_string(&link));
        self.link_filter.map(|f| f(link)).unwrap_or(true)
    }
}

fn cargo_set_with_resolver<'g>(
    test_fixture: &'g JsonFixture,
    root_package_name: &str,
    resolver: &mut dyn PackageResolver<'g>,
) -> CargoSet<'g> {
    let package_graph = test_fixture.graph();

    let initials = package_graph
        .resolve_package_name(root_package_name)
        .to_feature_set(StandardFeatures::Default);
    let no_extra_features = package_graph
        .resolve_none()
        .to_feature_set(StandardFeatures::Default);

    let cargo_options = CargoOptions::new();
    CargoSet::with_package_resolver(initials, no_extra_features, resolver, &cargo_options).unwrap()
}

fn cargo_set_package_names(cargo_set: &CargoSet) -> Vec<String> {
    let mut result = cargo_set
        .target_features()
        .union(cargo_set.host_features())
        .packages_with_features(DependencyDirection::Forward)
        .map(|feature_list| feature_list.package().name().to_string())
        .collect::<Vec<_>>();
    result.sort();
    result
}

#[test]
fn test_package_resolver_visits() {
    let mut resolver = PackageResolverForTesting::new();
    let cargo_set = cargo_set_with_resolver(JsonFixture::metadata1(), "testcrate", &mut resolver);
    assert_eq!(
        cargo_set_package_names(&cargo_set),
        vec![
            "aho-corasick",
            "bitflags",
            "ctor",
            "datatest",
            "datatest-derive",
            "dtoa",
            "lazy_static",
            "libc",
            "linked-hash-map",
            "mach",
            "memchr",
            "proc-macro2",
            "quote",
            "regex",
            "regex-syntax",
            "region",
            "same-file",
            "serde",
            "serde_yaml",
            "syn",
            "testcrate",
            "thread_local",
            "unicode-xid",
            "version_check",
            "walkdir",
            "winapi",
            "winapi-i686-pc-windows-gnu",
            "winapi-util",
            "winapi-x86_64-pc-windows-gnu",
            "yaml-rust",
        ],
    );
    assert_eq!(
        resolver.trace,
        vec![
            "testcrate@0.1.0 => datatest@0.4.2",
            "datatest@0.4.2 => yaml-rust@0.4.3",
            "datatest@0.4.2 => walkdir@2.2.9",
            "datatest@0.4.2 => version_check@0.9.1",
            "datatest@0.4.2 => serde_yaml@0.8.9",
            "datatest@0.4.2 => serde@1.0.100",
            "datatest@0.4.2 => region@2.1.2",
            "datatest@0.4.2 => regex@1.3.1",
            "datatest@0.4.2 => datatest-derive@0.4.0",
            "datatest@0.4.2 => ctor@0.1.10",
            "regex@1.3.1 => thread_local@0.3.6",
            "regex@1.3.1 => regex-syntax@0.6.12",
            "regex@1.3.1 => memchr@2.2.1",
            "regex@1.3.1 => aho-corasick@0.7.6",
            "aho-corasick@0.7.6 => memchr@2.2.1",
            "thread_local@0.3.6 => lazy_static@1.4.0",
            "region@2.1.2 => winapi@0.3.8",
            "region@2.1.2 => mach@0.2.3",
            "region@2.1.2 => libc@0.2.62",
            "region@2.1.2 => bitflags@1.1.0",
            "mach@0.2.3 => libc@0.2.62",
            "winapi@0.3.8 => winapi-x86_64-pc-windows-gnu@0.4.0",
            "winapi@0.3.8 => winapi-i686-pc-windows-gnu@0.4.0",
            "serde_yaml@0.8.9 => yaml-rust@0.4.3",
            "serde_yaml@0.8.9 => serde@1.0.100",
            "serde_yaml@0.8.9 => linked-hash-map@0.5.2",
            "serde_yaml@0.8.9 => dtoa@0.4.4",
            "yaml-rust@0.4.3 => linked-hash-map@0.5.2",
            "walkdir@2.2.9 => winapi-util@0.1.2",
            "walkdir@2.2.9 => winapi@0.3.8",
            "walkdir@2.2.9 => same-file@1.0.5",
            "same-file@1.0.5 => winapi-util@0.1.2",
            "winapi-util@0.1.2 => winapi@0.3.8",
            "ctor@0.1.10 => syn@1.0.5",
            "ctor@0.1.10 => quote@1.0.2",
            "quote@1.0.2 => proc-macro2@1.0.3",
            "proc-macro2@1.0.3 => unicode-xid@0.2.0",
            "syn@1.0.5 => unicode-xid@0.2.0",
            "syn@1.0.5 => quote@1.0.2",
            "syn@1.0.5 => proc-macro2@1.0.3",
            "datatest-derive@0.4.0 => syn@1.0.5",
            "datatest-derive@0.4.0 => quote@1.0.2",
            "datatest-derive@0.4.0 => proc-macro2@1.0.3",
        ],
    );

    // In this test input none of the links are trimmed by cargo algorithm.
    let count_of_links_visited_by_resolver = resolver.trace.len();
    let count_of_cargo_set_links = cargo_set.proc_macro_links().count()
        + cargo_set.build_dep_links().count()
        + cargo_set.target_links().count()
        + cargo_set.host_links().count();
    assert_eq!(count_of_links_visited_by_resolver, count_of_cargo_set_links);

    assert_eq!(
        links_to_strings(cargo_set.proc_macro_links()),
        vec![
            "datatest@0.4.2 => ctor@0.1.10",
            "datatest@0.4.2 => datatest-derive@0.4.0",
        ],
    );
    assert_eq!(
        links_to_strings(cargo_set.build_dep_links()),
        vec!["datatest@0.4.2 => version_check@0.9.1",],
    );
    assert_eq!(
        links_to_strings(cargo_set.target_links()),
        vec![
            "aho-corasick@0.7.6 => memchr@2.2.1",
            "datatest@0.4.2 => regex@1.3.1",
            "datatest@0.4.2 => region@2.1.2",
            "datatest@0.4.2 => serde@1.0.100",
            "datatest@0.4.2 => serde_yaml@0.8.9",
            "datatest@0.4.2 => walkdir@2.2.9",
            "datatest@0.4.2 => yaml-rust@0.4.3",
            "mach@0.2.3 => libc@0.2.62",
            "regex@1.3.1 => aho-corasick@0.7.6",
            "regex@1.3.1 => memchr@2.2.1",
            "regex@1.3.1 => regex-syntax@0.6.12",
            "regex@1.3.1 => thread_local@0.3.6",
            "region@2.1.2 => bitflags@1.1.0",
            "region@2.1.2 => libc@0.2.62",
            "region@2.1.2 => mach@0.2.3",
            "region@2.1.2 => winapi@0.3.8",
            "same-file@1.0.5 => winapi-util@0.1.2",
            "serde_yaml@0.8.9 => dtoa@0.4.4",
            "serde_yaml@0.8.9 => linked-hash-map@0.5.2",
            "serde_yaml@0.8.9 => serde@1.0.100",
            "serde_yaml@0.8.9 => yaml-rust@0.4.3",
            "testcrate@0.1.0 => datatest@0.4.2",
            "thread_local@0.3.6 => lazy_static@1.4.0",
            "walkdir@2.2.9 => same-file@1.0.5",
            "walkdir@2.2.9 => winapi-util@0.1.2",
            "walkdir@2.2.9 => winapi@0.3.8",
            "winapi-util@0.1.2 => winapi@0.3.8",
            "winapi@0.3.8 => winapi-i686-pc-windows-gnu@0.4.0",
            "winapi@0.3.8 => winapi-x86_64-pc-windows-gnu@0.4.0",
            "yaml-rust@0.4.3 => linked-hash-map@0.5.2",
        ],
    );
    assert_eq!(
        links_to_strings(cargo_set.host_links()),
        vec![
            "ctor@0.1.10 => quote@1.0.2",
            "ctor@0.1.10 => syn@1.0.5",
            "datatest-derive@0.4.0 => proc-macro2@1.0.3",
            "datatest-derive@0.4.0 => quote@1.0.2",
            "datatest-derive@0.4.0 => syn@1.0.5",
            "proc-macro2@1.0.3 => unicode-xid@0.2.0",
            "quote@1.0.2 => proc-macro2@1.0.3",
            "syn@1.0.5 => proc-macro2@1.0.3",
            "syn@1.0.5 => quote@1.0.2",
            "syn@1.0.5 => unicode-xid@0.2.0",
        ],
    );
}

#[test]
fn test_package_resolver_filtering_normal_links_on_target() {
    let mut resolver = PackageResolverForTesting::with_filter(&|link| {
        // Remove `winapi` and `winapu-util` links.  This should transitively remove `winapi =>
        // winapi-x86_64-pc-windows-gnu` and `winapi => winapi-i686-pc-windows-gnu`.
        //
        // This filter is meant to test whether `CargoSet` algotithm consults the `resolver`
        // in all required cases.  The filter may or may not make sense in practice (here we
        // can pretend that we are filtering all packages that are only needed on Windows).
        !link.to().name().starts_with("winapi")
    });
    let cargo_set = cargo_set_with_resolver(JsonFixture::metadata1(), "testcrate", &mut resolver);

    // No `winapi...` packages (unlike in `test_package_resolver_visits`).
    let package_names = cargo_set_package_names(&cargo_set)
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!package_names.contains("winapi"));
    assert!(!package_names.contains("winapi-util"));

    // No `winapi...` => ... links (unlike in `test_package_resolver_visits`).
    let trace = resolver.trace.into_iter().collect::<HashSet<_>>();
    assert!(!trace.contains("winapi@0.3.8 => winapi-x86_64-pc-windows-gnu@0.4.0"));
    assert!(!trace.contains("winapi@0.3.8 => winapi-i686-pc-windows-gnu@0.4.0"));
    assert!(!trace.contains("winapi-util@0.1.2 => winapi@0.3.8"));

    // The resolver was asked about these links, but didn't `accept` them.
    // Therefore these links should be present in the `trace`, but missing from
    // the final `cargo_set`.
    let cargo_set_links = links_to_strings(cargo_set.target_links())
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!cargo_set_links.contains("walkdir@2.2.9 => winapi@0.3.8"));
    assert!(!cargo_set_links.contains("region@2.1.2 => winapi@0.3.8"));
    assert!(!cargo_set_links.contains("same-file@1.0.5 => winapi-util@0.1.2"));
    assert!(trace.contains("walkdir@2.2.9 => winapi@0.3.8"));
    assert!(trace.contains("region@2.1.2 => winapi@0.3.8"));
    assert!(trace.contains("same-file@1.0.5 => winapi-util@0.1.2"));
}

#[test]
fn test_package_resolver_filtering_build_links_on_target() {
    let mut resolver = PackageResolverForTesting::with_filter(&|link| {
        // Remove `datatest` => `version_check` build dependency.
        //
        // This filter is meant to test whether `CargoSet` algotithm consults the `resolver`
        // in all required cases.  The filter may or may not make sense in practice (here
        // the trimmed down graph would fail to build...).
        link.to().name() != "version_check"
    });
    let cargo_set = cargo_set_with_resolver(JsonFixture::metadata1(), "testcrate", &mut resolver);

    // No `version_check...` packages (unlike in `test_package_resolver_visits`).
    let package_names = cargo_set_package_names(&cargo_set)
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!package_names.contains("version_check"));

    // If `version_check` has transitive dependencies, then we would test here that
    // they were not visited/consulted by the `resolver`.

    // The resolver was asked about these links, but didn't `accept` them.
    // Therefore these links should be present in the `trace`, but missing from
    // the final `cargo_set`.
    let trace = resolver.trace.into_iter().collect::<HashSet<_>>();
    let cargo_set_links = links_to_strings(cargo_set.build_dep_links())
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!cargo_set_links.contains("datatest@0.4.2 => version_check@0.9.1"));
    dbg!(&trace);
    assert!(trace.contains("datatest@0.4.2 => version_check@0.9.1"));
}

#[test]
fn test_package_resolver_filtering_links_on_host() {
    let mut resolver = PackageResolverForTesting::with_filter(&|link| {
        // Remove dependencies of `ctor` and `datatest-derive` packages.  This should transitively
        // remove `proc-macro2`, `quote`, `syn`, and `unicode-xid` packages.
        //
        // This filter is meant to test whether `CargoSet` algotithm consults the `resolver`
        // in all required cases.  The filter may or may not make sense in practice (here
        // the trimmed down graph would fail to build...).
        link.from().name() != "ctor" && link.from().name() != "datatest-derive"
    });
    let cargo_set = cargo_set_with_resolver(JsonFixture::metadata1(), "testcrate", &mut resolver);

    // No `ctor` not `datatest-derive` dependencies (unlike in `test_package_resolver_visits`).
    let package_names = cargo_set_package_names(&cargo_set)
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!package_names.contains("proc-macro2"));
    assert!(!package_names.contains("quote"));
    assert!(!package_names.contains("syn"));
    assert!(!package_names.contains("unicode-xid"));

    // No `syn` => ... links (unlike in `test_package_resolver_visits`).
    // No `quote` => ... links (unlike in `test_package_resolver_visits`).
    // No `proc-macro2` ... => links (unlike in `test_package_resolver_visits`).
    let trace = resolver.trace.into_iter().collect::<HashSet<_>>();
    assert!(!trace.contains("syn@1.0.5 => unicode-xid@0.2.0"));
    assert!(!trace.contains("syn@1.0.5 => quote@1.0.2"));
    assert!(!trace.contains("syn@1.0.5 => proc-macro2@1.0.3"));
    assert!(!trace.contains("quote@1.0.2 => proc-macro2@1.0.3"));
    assert!(!trace.contains("proc-macro2@1.0.3 => unicode-xid@0.2.0"));

    // The resolver was asked about these links, but didn't `accept` them.
    // Therefore these links should be present in the `trace`, but missing from
    // the final `cargo_set`.
    let cargo_set_links = links_to_strings(cargo_set.host_links())
        .into_iter()
        .collect::<HashSet<_>>();
    assert!(!cargo_set_links.contains("ctor@0.1.10 => syn@1.0.5"));
    assert!(!cargo_set_links.contains("ctor@0.1.10 => quote@1.0.2"));
    assert!(!cargo_set_links.contains("datatest-derive@0.4.0 => syn@1.0.5"));
    assert!(!cargo_set_links.contains("datatest-derive@0.4.0 => quote@1.0.2"));
    assert!(!cargo_set_links.contains("datatest-derive@0.4.0 => proc-macro2@1.0.3"));
    assert!(trace.contains("ctor@0.1.10 => syn@1.0.5"));
    assert!(trace.contains("ctor@0.1.10 => quote@1.0.2"));
    assert!(trace.contains("datatest-derive@0.4.0 => syn@1.0.5"));
    assert!(trace.contains("datatest-derive@0.4.0 => quote@1.0.2"));
    assert!(trace.contains("datatest-derive@0.4.0 => proc-macro2@1.0.3"));
}
