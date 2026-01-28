//! Read crate information from `Cargo.toml`

use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use toml;

use super::badges;

/// Try to get manifest info from Cargo.toml
pub fn get_manifest(project_root: &Path) -> Result<Manifest, String> {
    let mut cargo_toml = File::open(project_root.join("Cargo.toml"))
        .map_err(|e| format!("Could not read Cargo.toml: {}", e))?;

    let buf = {
        let mut buf = String::new();
        cargo_toml
            .read_to_string(&mut buf)
            .map_err(|e| format!("{}", e))?;
        buf
    };

    let cargo_toml: CargoToml = toml::from_str(&buf).map_err(|e| format!("{}", e))?;

    let manifest = Manifest::new(cargo_toml);

    Ok(manifest)
}

#[derive(Debug)]
pub struct Manifest {
    pub name: String,
    pub license: Option<String>,
    pub lib: Option<ManifestLib>,
    pub bin: Vec<ManifestLib>,
    pub badges: Vec<String>,
    pub version: String,
}

impl Manifest {
    fn new(cargo_toml: CargoToml) -> Manifest {
        Manifest {
            name: cargo_toml.package.name,
            license: cargo_toml.package.license,
            lib: cargo_toml.lib.map(|lib| ManifestLib::from_cargo_toml(lib)),
            bin: cargo_toml
                .bin
                .map(|bin_vec| {
                    bin_vec
                        .into_iter()
                        .map(|bin| ManifestLib::from_cargo_toml(bin))
                        .collect()
                })
                .unwrap_or_default(),
            badges: cargo_toml
                .badges
                .map(|b| process_badges(b))
                .unwrap_or_default(),
            version: cargo_toml.package.version,
        }
    }
}

#[derive(Debug)]
pub struct ManifestLib {
    pub path: PathBuf,
    pub doc: bool,
}

impl ManifestLib {
    fn from_cargo_toml(lib: CargoTomlLib) -> Self {
        ManifestLib {
            path: PathBuf::from(lib.path),
            doc: lib.doc.unwrap_or(true),
        }
    }
}

fn process_badges(badges: BTreeMap<String, BTreeMap<String, String>>) -> Vec<String> {
    let mut b: Vec<(u16, _)> = badges
        .into_iter()
        .filter_map(|(name, attrs)| match name.as_ref() {
            "appveyor" => Some((0, badges::appveyor(attrs))),
            "circle-ci" => Some((1, badges::circle_ci(attrs))),
            "gitlab" => Some((2, badges::gitlab(attrs))),
            "travis-ci" => Some((3, badges::travis_ci(attrs))),
            "github" => Some((4, badges::github(attrs))),
            "codecov" => Some((5, badges::codecov(attrs))),
            "coveralls" => Some((6, badges::coveralls(attrs))),
            "is-it-maintained-issue-resolution" => {
                Some((7, badges::is_it_maintained_issue_resolution(attrs)))
            }
            "is-it-maintained-open-issues" => {
                Some((8, badges::is_it_maintained_open_issues(attrs)))
            }
            "maintenance" => Some((9, badges::maintenance(attrs))),
            _ => return None,
        })
        .collect();

    b.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    b.into_iter().map(|(_, badge)| badge).collect()
}

/// Cargo.toml crate information
#[derive(Clone, Deserialize)]
struct CargoToml {
    pub package: CargoTomlPackage,
    pub lib: Option<CargoTomlLib>,
    pub bin: Option<Vec<CargoTomlLib>>,
    pub badges: Option<BTreeMap<String, BTreeMap<String, String>>>,
}

/// Cargo.toml crate package information
#[derive(Clone, Deserialize)]
struct CargoTomlPackage {
    pub name: String,
    pub license: Option<String>,
    pub version: String,
}

/// Cargo.toml crate lib information
#[derive(Clone, Deserialize)]
struct CargoTomlLib {
    pub path: String,
    pub doc: Option<bool>,
}
