#![deny(rust_2018_idioms)]

use cargo::{
    core::{
        compiler::{CompileKind, CompileTarget, TargetInfo},
        package::PackageSet,
        resolver::{self},
        Dependency, Package, PackageId, SourceId, Summary, Target,
    },
    sources::{
        source::{QueryKind, Source, SourceMap},
        SourceConfigMap,
    },
    util::{cache_lock::CacheLockMode, interning::InternedString, VersionExt},
    GlobalContext,
};
use itertools::Itertools;
use semver::Version;
use serde::{Deserialize, Serialize};
use std::collections::{btree_map::Entry, BTreeMap, BTreeSet, HashSet};

const PLAYGROUND_TARGET_PLATFORM: &str = "x86_64-unknown-linux-gnu";

struct GlobalState<'cfg> {
    config: &'cfg GlobalContext,
    compile_kind: CompileKind,
    target_info: TargetInfo,
    crates_io: SourceId,
    source: Box<dyn Source + 'cfg>,
    modifications: &'cfg Modifications,
}

/// The list of crates from crates.io
#[derive(Debug, Deserialize)]
struct TopCrates {
    crates: Vec<Crate>,
}

/// The shared description of a crate
#[derive(Debug, Deserialize)]
struct Crate {
    #[serde(rename = "id")]
    name: InternedString,
}

/// A mapping of a crates name to its identifier used in source code
#[derive(Debug, Serialize)]
pub struct CrateInformation {
    pub name: String,
    pub version: Version,
    pub id: String,
}

/// Hand-curated changes to the crate list
#[derive(Debug, Default, Deserialize)]
pub struct Modifications {
    #[serde(default)]
    pub exclusions: Vec<Exclusion>,
    #[serde(default)]
    pub additions: BTreeSet<InternedString>,
}

#[derive(Debug, Deserialize)]
pub struct Exclusion {
    name: InternedString,
    versions: Option<semver::Comparator>,
}

#[derive(Debug, Serialize, Clone)]
#[serde(rename_all = "kebab-case")]
pub struct DependencySpec {
    #[serde(skip_serializing_if = "String::is_empty")]
    pub package: String,
    #[serde(serialize_with = "exact_version")]
    pub version: Version,
    #[serde(skip_serializing_if = "BTreeSet::is_empty")]
    pub features: BTreeSet<InternedString>,
    #[serde(skip_serializing_if = "is_true")]
    pub default_features: bool,
}

#[derive(Debug)]
struct ResolvedDep {
    summary: Summary,
    lib_target: Target,
    features: FeaturesLite,
}

#[derive(Debug)]
struct FeaturesLite {
    features: BTreeSet<InternedString>,
    uses_default_features: bool,
}

impl Default for FeaturesLite {
    fn default() -> Self {
        Self {
            features: Default::default(),
            uses_default_features: true,
        }
    }
}

impl FeaturesLite {
    fn merge(&mut self, other: FeaturesLite) -> &mut Self {
        self.features.extend(other.features);
        self.uses_default_features = self.uses_default_features || other.uses_default_features;
        self
    }

    fn finalize(&self) -> Self {
        let mut features = self.features.clone();
        let mut uses_default_features = self.uses_default_features;

        // This is probably not needed, but keeping it for
        // belt-and-suspenders.
        if features.remove("default") {
            uses_default_features = true;
        }

        Self {
            features,
            uses_default_features,
        }
    }

    fn feature_strings(&self) -> Vec<String> {
        self.features.iter().map(|s| s.to_string()).collect()
    }
}

fn exact_version<S>(version: &Version, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    semver::Comparator {
        op: semver::Op::Exact,
        major: version.major,
        minor: Some(version.minor),
        patch: Some(version.patch),
        pre: version.pre.clone(),
    }
    .serialize(serializer)
}

fn is_true(b: &bool) -> bool {
    *b
}

impl Modifications {
    fn excluded(&self, name: &str, version: &Version) -> bool {
        let Some(exclusion) = self.exclusions.iter().find(|n| n.name == name) else {
            return false;
        };

        match &exclusion.versions {
            Some(versions) => versions.matches(version),

            // An unspecified version selector means to exclude all versions
            _ => true,
        }
    }
}

async fn simple_get(url: &str) -> reqwest::Result<reqwest::Response> {
    reqwest::ClientBuilder::new()
        .user_agent("Rust Playground - Top Crates Utility")
        .build()?
        .get(url)
        .send()
        .await
}

impl TopCrates {
    /// List top 100 crates by number of downloads on crates.io.
    async fn download() -> TopCrates {
        let resp = simple_get("https://crates.io/api/v1/crates?page=1&per_page=100&sort=downloads")
            .await
            .expect("Could not fetch top crates");
        assert!(
            resp.status().is_success(),
            "Could not download top crates; HTTP status was {}",
            resp.status(),
        );

        resp.json().await.expect("Invalid JSON")
    }

    async fn add_rust_cookbook_crates(&mut self) {
        let resp = simple_get(
            "https://raw.githubusercontent.com/rust-lang-nursery/rust-cookbook/master/Cargo.toml",
        )
        .await
        .expect("Could not fetch cookbook manifest");
        assert!(
            resp.status().is_success(),
            "Could not download cookbook; HTTP status was {}",
            resp.status(),
        );

        let content = resp.text().await.expect("could not read cookbook manifest");

        let manifest = content
            .parse::<toml::Table>()
            .expect("could not parse cookbook manifest");

        let dependencies = manifest["dependencies"]
            .as_table()
            .expect("no dependencies found for cookbook manifest");
        self.crates.extend({
            dependencies.iter().map(|(name, _)| Crate {
                name: InternedString::new(name),
            })
        })
    }

    /// Add crates that have been hand-picked
    fn add_curated_crates(&mut self, modifications: &Modifications) {
        self.crates.extend({
            modifications
                .additions
                .iter()
                .copied()
                .map(|name| Crate { name })
        });
    }
}

/// Finds the features specified by the custom metadata of `pkg`.
///
/// Our custom metadata format looks like:
///
///     [package.metadata.playground]
///     default-features = true
///     features = ["std", "extra-traits"]
///     all-features = false
///
/// All fields are optional.
fn playground_metadata_features(pkg: &Package) -> Option<FeaturesLite> {
    let custom_metadata = pkg.manifest().custom_metadata()?;
    let playground_metadata = custom_metadata.get("playground")?;

    #[derive(Deserialize)]
    #[serde(default, rename_all = "kebab-case")]
    struct Metadata {
        features: BTreeSet<InternedString>,
        default_features: bool,
        all_features: bool,
    }

    impl Default for Metadata {
        fn default() -> Self {
            Metadata {
                features: BTreeSet::new(),
                default_features: true,
                all_features: false,
            }
        }
    }

    let metadata = match playground_metadata.clone().try_into::<Metadata>() {
        Ok(metadata) => metadata,
        Err(err) => {
            eprintln!(
                "Failed to parse custom metadata for {} {}: {}",
                pkg.name(),
                pkg.version(),
                err
            );
            return None;
        }
    };

    // If `all-features` is set then we ignore `features`.
    let summary = pkg.summary();
    let enabled_features: BTreeSet<InternedString> = if metadata.all_features {
        summary.features().keys().copied().collect()
    } else {
        metadata.features
    };

    Some(FeaturesLite {
        features: enabled_features,
        uses_default_features: metadata.default_features,
    })
}

fn make_global_state<'cfg>(
    config: &'cfg GlobalContext,
    modifications: &'cfg Modifications,
) -> GlobalState<'cfg> {
    // Information about the playground's target platform.
    let compile_target = CompileTarget::new(PLAYGROUND_TARGET_PLATFORM, false)
        .expect("Unable to create a CompileTarget");
    let compile_kind = CompileKind::Target(compile_target);
    let rustc = config
        .load_global_rustc(None)
        .expect("Unable to load the global rustc");
    let target_info = TargetInfo::new(config, &[compile_kind], &rustc, compile_kind)
        .expect("Unable to create a TargetInfo");

    // Source for obtaining packages from the crates.io registry.
    let crates_io = SourceId::crates_io(config).expect("Unable to create crates.io source ID");

    let source_config_map = SourceConfigMap::new(config).unwrap();
    let yanked_whitelist = HashSet::new();
    let source = source_config_map
        .load(crates_io, &yanked_whitelist)
        .expect("Unable to create registry source");

    GlobalState {
        config,
        compile_kind,
        target_info,
        crates_io,
        source,
        modifications,
    }
}

fn bulk_download(global: &mut GlobalState<'_>, package_ids: &[PackageId]) -> Vec<Package> {
    let mut sources = SourceMap::new();
    sources.insert(Box::new(&mut *global.source));

    let package_set = PackageSet::new(package_ids, sources, global.config)
        .expect("Unable to create a PackageSet");

    package_set
        .get_many(package_set.package_ids())
        .expect("Unable to download packages")
        .into_iter()
        .cloned()
        .collect()
}

async fn populate_initial_direct_dependencies(
    global: &mut GlobalState<'_>,
) -> BTreeMap<PackageId, ResolvedDep> {
    let mut top = TopCrates::download().await;
    top.add_rust_cookbook_crates().await;
    top.add_curated_crates(global.modifications);

    // Find the newest (non-prerelease, non-yanked) versions of all
    // the interesting crates.
    let mut package_ids = Vec::new();
    for Crate { name } in top.crates {
        // Query the registry for a summary of this crate.
        // Usefully, this doesn't seem to include yanked versions
        let version = None;
        let dep = Dependency::parse(name, version, global.crates_io)
            .unwrap_or_else(|e| panic!("Unable to parse dependency for {}: {}", name, e));

        let matches = global
            .source
            .query_vec(&dep, QueryKind::Exact)
            .await
            .unwrap_or_else(|e| panic!("Unable to query registry for {}: {}", name, e));

        // Find the newest non-prelease version
        let summary = matches
            .into_iter()
            .filter(|summary| !summary.as_summary().version().is_prerelease())
            .max_by_key(|summary| summary.as_summary().version().clone())
            .unwrap_or_else(|| panic!("Registry has no viable versions of {}", name));

        let version = summary.as_summary().version().clone();

        if global.modifications.excluded(&name, &version) {
            continue;
        }

        let package_id = PackageId::new(name, version, global.crates_io);
        package_ids.push(package_id);
    }

    let packages = bulk_download(global, &package_ids);

    let mut initial_direct_dependencies = BTreeMap::new();
    for download in packages {
        let id = download.package_id();
        let lib_target = download
            .library()
            .unwrap_or_else(|| panic!("{} did not have a library", id))
            .clone();

        let features = playground_metadata_features(&download).unwrap_or_default();

        let dep = ResolvedDep {
            summary: download.summary().clone(),
            lib_target,
            features,
        };

        initial_direct_dependencies.insert(id, dep);
    }

    initial_direct_dependencies
}

fn write_scratch_cargo_toml(
    package_name: &str,
    crates: &BTreeMap<PackageId, ResolvedDep>,
) -> (tempfile::TempDir, std::path::PathBuf) {
    use cargo_util_schemas::manifest::{
        InheritableDependency, PackageName, TomlDependency, TomlDetailedDependency, TomlManifest,
    };
    use std::fs;

    let scratch_dir = tempfile::tempdir().expect("Could not create scratch directory");
    let o = std::process::Command::new("cargo")
        .arg("init")
        .arg("--vcs=none")
        .args(["--name", package_name])
        .arg(scratch_dir.path())
        .output()
        .expect("Could not initialize scratch project");
    assert!(o.status.success(), "{}", String::from_utf8_lossy(&o.stderr));

    let manifest_path = scratch_dir.path().join("Cargo.toml");

    let manifest_content = fs::read(&manifest_path).expect("Could not read manifest");
    let mut manifest = ::toml::from_slice::<TomlManifest>(&manifest_content)
        .expect("Could not deserialize manifest");

    let deps = manifest.dependencies.get_or_insert_default();
    for (pkg_id, details) in crates {
        let name = pkg_id.name();
        let version = pkg_id.version();

        let name = PackageName::new(name.to_string()).expect("Package name invalid");

        let dep = TomlDetailedDependency {
            version: Some(version.to_string()),
            features: Some(details.features.feature_strings()),
            default_features: Some(details.features.uses_default_features),

            ..Default::default()
        };

        let version = InheritableDependency::Value(TomlDependency::Detailed(dep));
        deps.insert(name, version);
    }
    let manifest_content = ::toml::to_string(&manifest).expect("Could not serialize manifest");
    fs::write(&manifest_path, manifest_content).expect("Could not write manifest");

    (scratch_dir, manifest_path)
}

fn load_workspace<'ctx>(
    global: &GlobalState<'ctx>,
    manifest_path: &std::path::Path,
) -> cargo::core::Workspace<'ctx> {
    let manifest = cargo::util::toml::read_manifest(manifest_path, global.crates_io, global.config)
        .expect("Could not read the manifest");
    let cargo::core::EitherManifest::Real(manifest) = manifest else {
        panic!("Only real manifests are supported")
    };

    let package = Package::new(manifest, manifest_path);
    let target_dir = None;
    let require_optional_deps = false;
    cargo::core::Workspace::ephemeral(package, global.config, target_dir, require_optional_deps)
        .expect("Could not construct a workspace")
}

fn resolve_dependencies(
    global: &GlobalState<'_>,
    scratch_package_name: String,
    ws: &cargo::core::Workspace<'_>,
) -> (resolver::Resolve, resolver::features::ResolvedFeatures) {
    let dry_run = true;
    let (pkg_set, resolve) =
        cargo::ops::resolve_ws(ws, dry_run).expect("Could not resolve the workspace");

    let requested_kinds = &[global.compile_kind];
    let mut target_data = cargo::core::compiler::RustcTargetData::new(ws, requested_kinds)
        .expect("Could not construct target data");
    let cli_features = resolver::CliFeatures {
        features: Default::default(),
        all_features: false,
        uses_default_features: true,
    };
    let spec = cargo::core::PackageIdSpec::new(scratch_package_name);
    let specs = &[spec];
    let requested_targets = &[];
    let opts = resolver::features::FeatureOpts::default();

    let feature_resolve = resolver::features::FeatureResolver::resolve(
        ws,
        &mut target_data,
        &resolve,
        &pkg_set,
        &cli_features,
        specs,
        requested_targets,
        opts,
    )
    .expect("Could not resolve features");

    (resolve, feature_resolve)
}

fn extend_direct_dependencies(
    global: &mut GlobalState<'_>,
    crates: &mut BTreeMap<PackageId, ResolvedDep>,
) {
    let scratch_package_name = "top-crates-scratch-space".to_owned();

    // Adds a direct dependency on each starting crate.
    let (_scratch_dir, manifest_path) = write_scratch_cargo_toml(&scratch_package_name, crates);

    let ws = load_workspace(global, &manifest_path);

    // Resolve transitive dependencies.
    let (resolve, feature_resolve) = resolve_dependencies(global, scratch_package_name, &ws);

    let root_package_names = ws
        .members()
        .flat_map(|member| member.dependencies().iter().map(|d| d.package_name()))
        .collect::<BTreeSet<_>>();

    let root_package_ids = resolve
        .iter()
        .filter(|pkg_id| root_package_names.contains(&pkg_id.name()))
        .collect::<BTreeSet<_>>();

    let mut visited = BTreeMap::new();
    let mut to_visit = root_package_ids;

    // Find all transitive dependencies that are compatible with the
    // playground's platform and are activated (if optional).
    while !to_visit.is_empty() {
        let mut next_to_visit = BTreeSet::new();

        for pkg_id in to_visit {
            for (dep_pkg_id, deps) in resolve.deps(pkg_id) {
                // Don't add excluded packages
                if global
                    .modifications
                    .excluded(&dep_pkg_id.name(), dep_pkg_id.version())
                {
                    continue;
                }

                // A package may depend on the same dependency
                // multiple times. A key case for this is
                // platform-specific dependencies. For example:
                //
                // ```toml
                // [dependencies]
                // jiff = { version = "0.2", optional = true, default-features = false, features = [ "std" ] }
                //
                // [target.'cfg(all(target_family = "wasm", target_os = "unknown"))'.dependencies]
                // jiff = { version = "0.2", optional = true, default-features = false, features = ["js"] }
                // ```
                for dep in deps {
                    let dep_name = dep.name_in_toml();

                    let active = if dep.is_optional() {
                        feature_resolve.is_dep_activated(
                            pkg_id,
                            resolver::features::FeaturesFor::default(),
                            dep_name,
                        )
                    } else {
                        true
                    };

                    if !active {
                        continue;
                    }

                    let for_our_platform = dep.platform().is_none_or(|platform| {
                        platform.matches(PLAYGROUND_TARGET_PLATFORM, global.target_info.cfg())
                    });

                    if !for_our_platform {
                        continue;
                    }

                    let features = FeaturesLite {
                        features: dep.features().iter().cloned().collect(),
                        uses_default_features: dep.uses_default_features(),
                    };

                    match visited.entry(dep_pkg_id) {
                        Entry::Vacant(entry) => entry.insert(features),
                        Entry::Occupied(mut entry) => entry.get_mut().merge(features),
                    };

                    next_to_visit.insert(dep_pkg_id);
                }
            }
        }

        to_visit = next_to_visit;
    }

    let package_ids = visited.keys().cloned().collect::<Vec<_>>();
    let packages = bulk_download(global, &package_ids);

    for download in packages {
        let id = download.package_id();
        let lib_target = download
            .library()
            .unwrap_or_else(|| panic!("{} did not have a library", id))
            .clone();

        let mut features = visited.remove(&id).unwrap_or_else(|| {
            unreachable!("Downloaded a crate that we didn't visit");
        });

        if let Some(metadata_features) = playground_metadata_features(&download) {
            features.merge(metadata_features);
        }

        let dep = ResolvedDep {
            summary: download.summary().clone(),
            lib_target,
            features,
        };

        crates.insert(id, dep);
    }
}

pub async fn generate_info(
    modifications: &Modifications,
) -> (BTreeMap<String, DependencySpec>, Vec<CrateInformation>) {
    // Setup to interact with cargo.
    let config = GlobalContext::default().expect("Unable to create default Cargo config");
    let _lock = config.acquire_package_cache_lock(CacheLockMode::DownloadExclusive);
    let mut global = make_global_state(&config, modifications);

    let mut resolved_crates = populate_initial_direct_dependencies(&mut global).await;

    loop {
        let num_crates_before = resolved_crates.len();
        extend_direct_dependencies(&mut global, &mut resolved_crates);
        let num_crates_after = resolved_crates.len();
        if num_crates_before == num_crates_after {
            break;
        }
    }

    let dependencies = generate_dependency_specs(&resolved_crates);
    let infos = generate_crate_information(&dependencies);
    (dependencies, infos)
}

fn generate_dependency_specs(
    crates: &BTreeMap<PackageId, ResolvedDep>,
) -> BTreeMap<String, DependencySpec> {
    // Sort all packages by name then version (descending), so that
    // when we group them we know we get all the same crates together
    // and the newest version first.
    let mut crates = crates.values().collect_vec();
    crates.sort_by(|a, b| {
        let name_cmp = a.summary.name().as_str().cmp(b.summary.name().as_str());
        let version_cmp = a.summary.version().cmp(b.summary.version());
        name_cmp.then(version_cmp.reverse())
    });

    let mut dependencies = BTreeMap::new();
    for (name, pkgs) in &crates.iter().chunk_by(|dep| dep.summary.name()) {
        let mut first = true;

        for dep in pkgs {
            let summary = &dep.summary;
            let version = summary.version();

            // We see the newest version first. Any subsequent
            // versions will have their version appended so that they
            // are uniquely named
            let crate_name = dep.lib_target.crate_name();
            let exposed_name = if first {
                crate_name
            } else {
                format!(
                    "{}_{}_{}_{}",
                    crate_name, version.major, version.minor, version.patch
                )
            };

            let features = dep.features.finalize();

            dependencies.insert(
                exposed_name,
                DependencySpec {
                    package: name.to_string(),
                    version: version.clone(),
                    features: features.features,
                    default_features: features.uses_default_features,
                },
            );

            first = false;
        }
    }

    dependencies
}

fn generate_crate_information(
    dependencies: &BTreeMap<String, DependencySpec>,
) -> Vec<CrateInformation> {
    let mut infos = Vec::new();

    for (exposed_name, dependency_spec) in dependencies {
        infos.push(CrateInformation {
            name: dependency_spec.package.clone(),
            version: dependency_spec.version.clone(),
            id: exposed_name.clone(),
        });
    }

    infos
}
