// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(clippy::needless_pass_by_value)]

mod helper;

use std::{collections::HashMap, path::Path, process::Command};

use build_context::TARGET;
use cargo_config2::*;

use self::helper::*;

fn test_options() -> ResolveOptions {
    ResolveOptions::default()
        .env(HashMap::<String, String>::default())
        .cargo_home(None)
        .rustc(PathAndArgs::new("rustc"))
}

fn assert_reference_example(de: fn(&Path, ResolveOptions) -> Result<Config, Error>) {
    let (_tmp, root) = test_project("reference");
    let dir = &root;
    let base_config = &de(dir, test_options()).unwrap();
    let config = base_config.clone();

    // [alias]
    for (k, v) in &config.alias {
        match k.as_str() {
            "b" => assert_eq!(*v, "build".into()),
            "c" => assert_eq!(*v, "check".into()),
            "t" => assert_eq!(*v, "test".into()),
            "r" => assert_eq!(*v, "run".into()),
            "rr" => assert_eq!(*v, "run --release".into()),
            "recursive_example" => assert_eq!(*v, "rr --example recursions".into()),
            "space_example" => {
                assert_eq!(*v, ["run", "--release", "--", "\"command list\""].into());
            }
            _ => panic!("unexpected alias: name={k}, value={v:?}"),
        }
    }

    // [build]
    assert_eq!(config.build.rustc.as_ref().unwrap().as_os_str(), "rustc");
    assert_eq!(config.build.rustc_wrapper.as_ref().unwrap().as_os_str(), "…");
    assert_eq!(config.build.rustc_workspace_wrapper.as_ref().unwrap().as_os_str(), "…");
    assert_eq!(config.build.rustdoc.as_ref().unwrap().as_os_str(), "rustdoc");
    assert_eq!(config.build.target.as_ref().unwrap(), &vec!["triple".into()]);
    assert_eq!(config.build.target_dir.as_ref().unwrap(), &dir.join("target"));
    assert_eq!(config.build.build_dir.as_ref().unwrap(), &dir.join("target"));
    assert_eq!(config.build.rustflags, Some(["…", "…"].into()));
    assert_eq!(config.build.rustdocflags, Some(["…", "…"].into()));
    assert_eq!(config.build.incremental, Some(true));
    assert_eq!(config.build.dep_info_basedir.as_ref().unwrap(), &dir.join("…"));

    // [credential-alias]
    for (k, v) in &config.credential_alias {
        match k.as_str() {
            "my-alias" => {
                // TODO
                #[cfg(windows)]
                assert_eq!(
                    *v,
                    *PathAndArgs::new("C:/usr/bin/cargo-credential-example").args([
                        "--argument",
                        "value",
                        "--flag"
                    ])
                );
                #[cfg(not(windows))]
                assert_eq!(
                    *v,
                    *PathAndArgs::new("/usr/bin/cargo-credential-example").args([
                        "--argument",
                        "value",
                        "--flag"
                    ])
                );
            }
            _ => panic!("unexpected credential-alias: name={k}, value={v:?}"),
        }
    }

    // [doc]
    assert_eq!(config.doc.browser.as_ref().unwrap().path.as_os_str(), "chromium");
    assert!(config.doc.browser.as_ref().unwrap().args.is_empty());

    // [env]
    assert_eq!(config.env["ENV_VAR_NAME"].value, "value");
    assert_eq!(config.env["ENV_VAR_NAME"].force, false);
    assert_eq!(config.env["ENV_VAR_NAME"].relative, false);
    assert_eq!(config.env["ENV_VAR_NAME_2"].value, "value");
    assert_eq!(config.env["ENV_VAR_NAME_2"].force, true);
    assert_eq!(config.env["ENV_VAR_NAME_2"].relative, false);
    assert_eq!(config.env["ENV_VAR_NAME_3"].value, dir.join("relative/path"));
    assert_eq!(config.env["ENV_VAR_NAME_3"].force, false);
    assert_eq!(config.env["ENV_VAR_NAME_3"].relative, false); // false because it has been resolved

    // [future-incompat-report]
    assert_eq!(config.future_incompat_report.frequency, Some(Frequency::Always));

    // TODO:
    // [cache]

    // [cargo-new]
    assert_eq!(config.cargo_new.vcs, Some(VersionControlSoftware::None));

    // [http]
    assert_eq!(config.http.debug, Some(false));
    assert_eq!(config.http.proxy.as_deref(), Some("host:port"));
    assert_eq!(config.http.timeout, Some(30));
    assert_eq!(config.http.low_speed_limit, Some(10));
    assert_eq!(config.http.cainfo.as_deref(), Some("cert.pem"));
    assert_eq!(config.http.check_revoke, Some(true));
    assert_eq!(config.http.multiplexing, Some(true));
    assert_eq!(config.http.user_agent.as_deref(), Some("foo-usr-agt"));

    // TODO
    // [install]

    // [net]
    assert_eq!(config.net.retry, Some(3));
    assert_eq!(config.net.git_fetch_with_cli, Some(true));
    assert_eq!(config.net.offline, Some(true));
    // TODO
    // [net.ssh]

    // TODO
    // [patch.<registry>]
    // [profile.<name>]
    // [resolver]

    // [registries.<name>]
    assert_eq!(config.registries.len(), 6);
    assert_eq!(config.registries["custom-token"].index.as_deref(), Some("registry-index"));
    assert_eq!(
        config.registries["custom-token"].token.as_deref(),
        Some("00000000000000000000000000000000001")
    );
    assert_eq!(config.registries["custom-token"].protocol, None);
    assert_eq!(
        config.registries["custom-single-word-plugin"].credential_provider,
        Some(CredentialProvider::Plugin(PathAndArgs::new("cargo-credential-example"))),
    );
    assert_eq!(
        config.registries["alias"].credential_provider,
        Some(CredentialProvider::Alias("my-alias".into())),
    );
    let mut many_word_plugins = PathAndArgs::new("cargo-credential-example");
    many_word_plugins.arg("--some-argument");
    assert_eq!(
        config.registries["custom-many-words-plugin"].credential_provider,
        Some(CredentialProvider::Plugin(many_word_plugins)),
    );
    assert_eq!(
        config.registries["custom-token-from-stdout"].credential_provider,
        Some(CredentialProvider::CargoTokenFromStdout(PathAndArgs::new(
            "cargo-credential-example"
        ))),
    );
    assert_eq!(
        config.registries["crates-io"].index.as_deref(),
        Some("https://github.com/rust-lang/crates.io-index")
    );
    assert_eq!(
        config.registries["crates-io"].token.as_deref(),
        Some("00000000000000000000000000000000000")
    );
    assert_eq!(config.registries["crates-io"].protocol, Some(RegistriesProtocol::Git));
    assert_eq!(config.registries["crates-io"].credential_provider, None);
    // [registry]
    assert_eq!(config.registry.default.as_deref(), Some("crates-io"));
    assert_eq!(config.registry.token.as_deref(), Some("00000000000000000000000000000000000"));
    assert_eq!(config.registry.credential_provider, Some(CredentialProvider::CargoToken));
    assert_eq!(config.registry.global_credential_providers.as_ref(), [
        CredentialProvider::CargoToken
    ]);

    // [source.<name>]
    assert_eq!(config.source["vendored-sources"].directory, Some(dir.join("vendor")));
    assert_eq!(config.source["crates-io"].replace_with.as_deref(), Some("vendored-sources"));
    assert_eq!(
        config.source["git+https://github.com/taiki-e/test-helper.git?rev=f38a7f5"].git.as_deref(),
        Some("https://github.com/taiki-e/test-helper.git"),
    );
    assert_eq!(
        config.source["git+https://github.com/taiki-e/test-helper.git?rev=f38a7f5"].rev.as_deref(),
        Some("f38a7f5"),
    );
    assert_eq!(
        config.source["git+https://github.com/taiki-e/test-helper.git?rev=f38a7f5"]
            .replace_with
            .as_deref(),
        Some("vendored-sources")
    );

    // [target.<triple>] and [target.<cfg>]
    assert_eq!(config.target("x86_64-unknown-linux-gnu").unwrap().linker.unwrap().as_os_str(), "b");
    assert_eq!(
        config.target("x86_64-unknown-linux-gnu").unwrap().runner.unwrap().path.as_os_str(),
        "b"
    );
    assert!(config.target("x86_64-unknown-linux-gnu").unwrap().runner.unwrap().args.is_empty());
    assert_eq!(
        config.target("x86_64-unknown-linux-gnu").unwrap().rustflags,
        Some(["b", "bb", "c", "cc"].into())
    );
    assert_eq!(
        config.target("x86_64-unknown-linux-gnu").unwrap().rustdocflags,
        Some(["d", "dd"].into())
    );
    assert_eq!(config.linker("x86_64-unknown-linux-gnu").unwrap().unwrap().as_os_str(), "b");
    assert_eq!(config.runner("x86_64-unknown-linux-gnu").unwrap().unwrap().path.as_os_str(), "b");
    assert!(config.runner("x86_64-unknown-linux-gnu").unwrap().unwrap().args.is_empty());
    assert_eq!(
        config.rustflags("x86_64-unknown-linux-gnu").unwrap(),
        Some(["b", "bb", "c", "cc"].into())
    );
    assert_eq!(config.rustdocflags("x86_64-unknown-linux-gnu").unwrap(), Some(["d", "dd"].into()));
    assert_eq!(
        config.rustflags("thumbv8m.main-none-eabi").unwrap(),
        Some(["-Z", "panic-abort-tests"].into())
    );
    assert_eq!(
        config.rustflags("thumbv8m.base-none-eabi").unwrap(),
        Some(["-Z", "panic-abort-tests"].into())
    );
    // TODO: [target.<triple>.<links>]

    // resolved target config cannot be accessed by cfg(...)
    assert!(
        config
            .target("cfg(target_arch = \"x86_64\")")
            .unwrap_err()
            .to_string()
            .contains("not valid target triple")
    );
    assert!(
        config
            .linker("cfg(target_arch = \"x86_64\")")
            .unwrap_err()
            .to_string()
            .contains("not valid target triple")
    );
    assert!(
        config
            .runner("cfg(target_arch = \"x86_64\")")
            .unwrap_err()
            .to_string()
            .contains("not valid target triple")
    );
    assert!(
        config
            .rustflags("cfg(target_arch = \"x86_64\")")
            .unwrap_err()
            .to_string()
            .contains("not valid target triple")
    );

    // [term]
    assert_eq!(config.term.quiet, Some(false));
    assert_eq!(config.term.verbose, Some(false));
    assert_eq!(config.term.color, Some(Color::Auto));
    // TODO: hyperlinks, unicode
    assert_eq!(config.term.progress.when, Some(When::Auto));
    assert_eq!(config.term.progress.width, Some(80));
    // TODO: progress.term-integration

    let _config = toml::to_string(&config).unwrap();
}

fn easy_load(dir: &Path, options: ResolveOptions) -> Result<Config, Error> {
    Config::load_with_options(dir, options)
}
#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support file with non-default mode: https://github.com/rust-lang/miri/pull/2720
fn easy() {
    use easy_load as de;

    assert_reference_example(de);
}

#[test]
fn no_manifest_dir() {
    let tmpdir = tempfile::tempdir().unwrap();
    assert_eq!(
        "",
        toml::to_string(&Config::load_with_options(tmpdir.path(), test_options()).unwrap())
            .unwrap()
    );
}

fn de_load(dir: &Path, _cx: ResolveOptions) -> Result<de::Config, Error> {
    de::Config::load_with_options(dir, None)
}
#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support file with non-default mode: https://github.com/rust-lang/miri/pull/2720
fn de() {
    use de_load as de;

    let (_tmp, root) = test_project("reference");
    let dir = &root;
    let base_config = &de(dir, test_options()).unwrap();
    let config = base_config.clone();

    let _config = toml::to_string(&config).unwrap();

    assert_eq!("", toml::to_string(&de::Config::default()).unwrap());
}

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support file with non-default mode: https://github.com/rust-lang/miri/pull/2720
fn custom_target() {
    use easy_load as de;
    struct IsBuiltin(bool);
    #[track_caller]
    fn t(target: &str, IsBuiltin(is_builtin): IsBuiltin) {
        let (_tmp, root) = test_project("empty");
        let dir = &root;
        fs::write(
            root.join(".cargo/config.toml"),
            r#"
                target.'cfg(target_arch = "avr")'.linker = "avr-gcc"
                target.'cfg(target_arch = "avr")'.rustflags = "-C opt-level=s"
                "#,
        )
        .unwrap();
        let spec_path = fixtures_dir().join(format!("target-specs/{target}.json"));
        assert_eq!(spec_path.exists(), !is_builtin);
        let cli_target = if spec_path.exists() { spec_path.to_str().unwrap() } else { target };

        let config = de(dir, test_options()).unwrap();
        assert_eq!(
            config
                .build_target_for_config([cli_target])
                .unwrap()
                .iter()
                .map(|t| t.triple().to_owned())
                .collect::<Vec<_>>(),
            vec![target.to_owned()]
        );
        assert_eq!(config.build_target_for_cli([cli_target]).unwrap(), vec![cli_target.to_owned()]);

        assert_eq!(config.linker(cli_target).unwrap().unwrap().as_os_str(), "avr-gcc");
        assert_eq!(config.rustflags(cli_target).unwrap(), Some(["-C", "opt-level=s"].into()));

        // only resolve relative path from config or environment variables
        let spec_file_name = spec_path.file_name().unwrap().to_str().unwrap();
        assert_eq!(
            config.build_target_for_config([spec_file_name]).unwrap()[0]
                .spec_path()
                .unwrap()
                .as_os_str(),
            spec_file_name
        );
        assert_eq!(config.build_target_for_cli([spec_file_name]).unwrap(), vec![
            spec_file_name.to_owned()
        ]);

        let _config = toml::to_string(&config).unwrap();
    }

    if rustversion::cfg!(since(1.87)) {
        t("avr-none", IsBuiltin(true));
    } else {
        t("avr-unknown-gnu-atmega328", IsBuiltin(true));
    }
    // Skip pre-1.91 because target-pointer-width change
    if rustversion::cfg!(since(1.91)) {
        t("avr-unknown-gnu-atmega2560", IsBuiltin(false));
    }
}

#[rustversion::attr(not(nightly), ignore)]
#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
#[cfg_attr(careful, ignore)] // TODO: Unexpected TomlError (bug in toml crate?)
fn cargo_config_toml() {
    fn de(dir: &Path) -> de::Config {
        // remove CARGO_PKG_DESCRIPTION -- if field in Cargo.toml contains newline, --format=toml display invalid toml
        let output = Command::new("cargo")
            .args(["-Z", "unstable-options", "config", "get", "--format=toml"])
            .current_dir(dir)
            .env_remove("CARGO_PKG_DESCRIPTION")
            .output()
            .unwrap();
        assert!(output.status.success());
        let s = str::from_utf8(&output.stdout).unwrap();
        toml::from_str(s).unwrap()
    }

    let _config = de(&fixtures_dir().join("reference"));
}

#[rustversion::attr(not(nightly), ignore)]
#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn cargo_config_json() {
    fn de(dir: &Path) -> de::Config {
        let output = Command::new("cargo")
            .args(["-Z", "unstable-options", "config", "get", "--format=json"])
            .current_dir(dir)
            .output()
            .unwrap();
        assert!(output.status.success());
        let s = str::from_utf8(&output.stdout).unwrap();
        serde_json::from_str(s).unwrap()
    }

    let _config = de(&fixtures_dir().join("reference"));
}

#[test]
#[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
fn test_cargo_behavior() {
    let (_tmp, root) = test_project("empty");
    let dir = &root;

    // [env] table doesn't affect config resolution
    // https://github.com/taiki-e/cargo-config2/issues/2
    fs::write(
        root.join(".cargo/config.toml"),
        r#"
            [env]
            RUSTFLAGS = "--cfg a"
            [build]
            rustflags = "--cfg b"
            "#,
    )
    .unwrap();
    let output = Command::new("cargo")
        .args(["build", "-v"])
        .current_dir(dir)
        .env("CARGO_HOME", root.join(".cargo"))
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTFLAGS")
        .env_remove(format!("CARGO_TARGET_{}_RUSTFLAGS", TARGET.replace(['-', '.'], "_")))
        .env_remove("CARGO_BUILD_RUSTFLAGS")
        .output()
        .unwrap();
    assert!(output.status.success());
    let stderr = str::from_utf8(&output.stderr).unwrap();
    assert!(!stderr.contains("--cfg a"), "actual:\n---\n{stderr}\n---\n");
    assert!(stderr.contains("--cfg b"), "actual:\n---\n{stderr}\n---\n");
}
