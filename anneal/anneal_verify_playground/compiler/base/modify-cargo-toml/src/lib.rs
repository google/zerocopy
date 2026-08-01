extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate toml;

use std::collections::BTreeMap;
use toml::Value;

type Other = BTreeMap<String, Value>;

fn modify<F, T>(cargo_toml: Value, f: F) -> Value
where
    F: FnOnce(T) -> T,
    T: serde::Serialize + for<'de> serde::Deserialize<'de>,
{
    let cargo_toml = cargo_toml.try_into().unwrap();

    let cargo_toml = f(cargo_toml);

    Value::try_from(cargo_toml).unwrap()
}

fn ensure_string_in_vec(values: &mut Vec<String>, val: &str) {
    if !values.iter().any(|f| f == val) {
        values.push(val.into());
    }
}

pub fn set_edition(cargo_toml: Value, edition: &str) -> Value {
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct CargoToml {
        package: Package,
        #[serde(flatten)]
        other: Other,
    }

    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct Package {
        #[serde(default)]
        edition: String,
        #[serde(flatten)]
        other: Other,
    }

    modify(cargo_toml, |mut cargo_toml: CargoToml| {
        cargo_toml.package.edition = edition.into();
        cargo_toml
    })
}

pub fn remove_dependencies(cargo_toml: Value) -> Value {
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct CargoToml {
        dependencies: BTreeMap<String, Value>,
        #[serde(flatten)]
        other: Other,
    }

    modify(cargo_toml, |mut cargo_toml: CargoToml| {
        cargo_toml.dependencies.clear();
        cargo_toml
    })
}

pub fn set_crate_type(cargo_toml: Value, crate_type: &str) -> Value {
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct CargoToml {
        #[serde(default)]
        lib: Lib,
        #[serde(flatten)]
        other: Other,
    }

    #[derive(Debug, Default, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct Lib {
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        crate_type: Vec<String>,
        #[serde(default)]
        proc_macro: bool,
        #[serde(flatten)]
        other: Other,
    }

    modify(cargo_toml, |mut cargo_toml: CargoToml| {
        if crate_type == "proc-macro" {
            cargo_toml.lib.proc_macro = true;
        } else {
            ensure_string_in_vec(&mut cargo_toml.lib.crate_type, crate_type);
        }
        cargo_toml
    })
}

pub fn set_release_lto(cargo_toml: Value, lto: bool) -> Value {
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct CargoToml {
        #[serde(default)]
        profile: Profiles,
        #[serde(flatten)]
        other: Other,
    }

    #[derive(Debug, Default, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct Profiles {
        #[serde(default)]
        release: Profile,
        #[serde(flatten)]
        other: Other,
    }

    #[derive(Debug, Default, Serialize, Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct Profile {
        #[serde(default)]
        lto: bool,
        #[serde(flatten)]
        other: Other,
    }

    modify(cargo_toml, |mut cargo_toml: CargoToml| {
        cargo_toml.profile.release.lto = lto;
        cargo_toml
    })
}
