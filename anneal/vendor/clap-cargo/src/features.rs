//! Cargo Feature Flags.

/// Cargo Feature Flags.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
#[cfg_attr(feature = "clap", command(about = None, long_about = None))]
#[non_exhaustive]
pub struct Features {
    #[cfg_attr(feature = "clap", arg(long))]
    /// Activate all available features
    pub all_features: bool,
    #[cfg_attr(feature = "clap", arg(long))]
    /// Do not activate the `default` feature
    pub no_default_features: bool,
    #[cfg_attr(feature = "clap", arg(short = 'F', long, value_delimiter = ' '))]
    /// Space-separated list of features to activate
    pub features: Vec<String>,
}

#[cfg(feature = "cargo_metadata")]
impl Features {
    /// Forward these flags to the `cargo_metadata` crate.
    ///
    /// Note: Requires the features `cargo_metadata`.
    pub fn forward_metadata<'m>(
        &self,
        meta: &'m mut cargo_metadata::MetadataCommand,
    ) -> &'m mut cargo_metadata::MetadataCommand {
        if self.all_features {
            meta.features(cargo_metadata::CargoOpt::AllFeatures);
        }
        if self.no_default_features {
            meta.features(cargo_metadata::CargoOpt::NoDefaultFeatures);
        }
        if !self.features.is_empty() {
            meta.features(cargo_metadata::CargoOpt::SomeFeatures(
                self.features.clone(),
            ));
        }
        meta
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[cfg(feature = "clap")]
    fn verify_app() {
        #[derive(Debug, clap::Parser)]
        struct Cli {
            #[command(flatten)]
            features: Features,
        }

        use clap::CommandFactory;
        Cli::command().debug_assert();
    }

    #[test]
    #[cfg(feature = "clap")]
    fn parse_multiple_occurrences() {
        use clap::Parser;

        #[derive(PartialEq, Eq, Debug, Parser)]
        struct Args {
            positional: Option<String>,
            #[command(flatten)]
            features: Features,
        }

        assert_eq!(
            Args {
                positional: None,
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec![]
                }
            },
            Args::parse_from(["test"])
        );
        assert_eq!(
            Args {
                positional: Some("foo".to_owned()),
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec![]
                }
            },
            Args::parse_from(["test", "foo"])
        );
        assert_eq!(
            Args {
                positional: None,
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec!["foo".to_owned()]
                }
            },
            Args::parse_from(["test", "--features", "foo"])
        );
        assert_eq!(
            Args {
                positional: None,
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec!["foo".to_owned(), "bar".to_owned()]
                }
            },
            Args::parse_from(["test", "--features", "foo bar"])
        );
        assert_eq!(
            Args {
                positional: Some("baz".to_owned()),
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec!["foo".to_owned(), "bar".to_owned()]
                }
            },
            Args::parse_from(["test", "--features", "foo bar", "baz"])
        );
        assert_eq!(
            Args {
                positional: Some("baz".to_owned()),
                features: Features {
                    all_features: false,
                    no_default_features: false,
                    features: vec!["foo".to_owned(), "bar".to_owned()]
                }
            },
            Args::parse_from(["test", "--features", "foo", "--features", "bar", "baz"])
        );
    }

    #[cfg(feature = "cargo_metadata")]
    #[test]
    fn features_all() {
        let mut metadata = cargo_metadata::MetadataCommand::new();
        metadata.manifest_path("tests/fixtures/simple/Cargo.toml");

        let features = Features {
            all_features: true,
            ..Default::default()
        };
        features.forward_metadata(&mut metadata);
        metadata.exec().unwrap();
        // TODO verify we forwarded correctly.
    }

    #[cfg(feature = "cargo_metadata")]
    #[test]
    fn features_none() {
        let mut metadata = cargo_metadata::MetadataCommand::new();
        metadata.manifest_path("tests/fixtures/simple/Cargo.toml");

        let features = Features {
            no_default_features: true,
            ..Default::default()
        };
        features.forward_metadata(&mut metadata);
        metadata.exec().unwrap();
        // TODO verify we forwarded correctly.
    }
}
