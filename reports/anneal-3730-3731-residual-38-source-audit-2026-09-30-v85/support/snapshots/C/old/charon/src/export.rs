pub mod multi_target;

use crate::ast::*;
use crate::options::SerializationFormat;
use crate::transform::TransformCtx;
use serde::{Deserialize, Deserializer, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::fs::File;
use std::io::{BufReader, BufWriter, Read};
use std::path::{Path, PathBuf};

/// The data of a generic crate. We serialize this to pass it to `charon-ml`, so this must be as
/// stable as possible. This is used for both ULLBC and LLBC.
#[derive(SerializeState, DeserializeState)]
pub struct CrateData {
    /// The version of charon currently being used. `charon-ml` inspects this and errors if it is
    /// trying to read an incompatible version (for now we compare versions for equality).
    #[serde_state(stateless)]
    pub charon_version: CharonVersion,
    pub translated: TranslatedCrate,
    #[serde_state(stateless)]
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)] // Don't change, this would break version detection for old charon-ml
    /// If there were errors, this contains only a partial description of the input crate.
    pub has_errors: bool,
}

impl Serialize for CrateData {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.translated.options.no_dedup_serialized_ast {
            self.serialize_state(&(), serializer)
        } else {
            let state = HashConsDedupSerializer::default();
            self.serialize_state(&state, serializer)
        }
    }
}

impl<'de> Deserialize<'de> for CrateData {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Always provide the state, just in case.
        let state = HashConsDedupSerializer::default();
        Self::deserialize_state(&state, deserializer)
    }
}

#[derive(Serialize)]
pub struct CharonVersion(pub String);

impl<'de> Deserialize<'de> for CharonVersion {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde::de::Error;
        let version = String::deserialize(deserializer)?;
        if version != crate::VERSION {
            return Err(D::Error::custom(format!(
                "Incompatible version of charon: \
                this program supports llbc emitted by charon v{} \
                but attempted to read a file emitted by charon v{}",
                crate::VERSION,
                version,
            )));
        }
        Ok(CharonVersion(version))
    }
}

impl CrateData {
    pub fn new(ctx: TransformCtx) -> Self {
        CrateData {
            charon_version: CharonVersion(crate::VERSION.to_owned()),
            has_errors: ctx.has_errors(),
            translated: ctx.translated,
        }
    }

    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_files(
        &self,
        targets: Vec<(PathBuf, SerializationFormat)>,
    ) -> Result<(), ()> {
        for (target_filename, format) in targets {
            self.serialize_to_file(&target_filename, format)?;
        }
        Ok(())
    }

    /// Export the translated definitions to a file.
    #[allow(clippy::result_unit_err)]
    pub fn serialize_to_file(
        &self,
        target_filename: &Path,
        format: SerializationFormat,
    ) -> Result<(), ()> {
        // Create the directory, if necessary (note that if the target directory
        // is not specified, there is no need to create it: otherwise we
        // couldn't have read the input file in the first place).
        let target_dir = target_filename.parent().unwrap();
        match std::fs::create_dir_all(target_dir) {
            Ok(()) => (),
            Err(_) => {
                error!("Could not create the directory: {:?}", target_dir);
                return Err(());
            }
        };

        // Create the file.
        let std::io::Result::Ok(outfile) = File::create(target_filename) else {
            error!("Could not open: {:?}", target_filename);
            return Err(());
        };
        // Write to the file.
        let mut writer = BufWriter::new(outfile);
        match format {
            SerializationFormat::Json => {
                if let Err(err) = serde_json::to_writer(&mut writer, self) {
                    error!("Could not serialize to `{target_filename:?}`: {err:?}");
                    return Err(());
                }
            }
            SerializationFormat::Postcard => {
                if let Err(err) = postcard::to_io(self, &mut writer) {
                    error!("Could not serialize to `{target_filename:?}`: {err:?}");
                    return Err(());
                }
            }
        }

        // We canonicalize (i.e., make absolute) the path before printing it; this makes it clearer
        // to the user where to find the file.
        let target_filename = std::fs::canonicalize(target_filename).unwrap();
        if self.has_errors {
            info!(
                "Generated the partial (because we encountered errors) file: {}",
                target_filename.to_str().unwrap()
            );
        } else {
            info!("Generated the file: {}", target_filename.to_str().unwrap());
        }
        Ok(())
    }

    pub fn deserialize_from_file(
        path: &std::path::Path,
        format: SerializationFormat,
    ) -> anyhow::Result<Self> {
        use crate::export::CrateData;
        use anyhow::Context;
        use serde::Deserialize;
        use std::fs::File;
        let file = File::open(path)
            .with_context(|| format!("Failed to read llbc file {}", path.display()))?;
        match format {
            SerializationFormat::Json => {
                let reader = BufReader::new(file);
                let mut deserializer = serde_json::Deserializer::from_reader(reader);
                // Deserialize without recursion limit.
                deserializer.disable_recursion_limit();
                // Grow stack space as needed.
                let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
                Ok(CrateData::deserialize(deserializer)?)
            }
            SerializationFormat::Postcard => {
                let mut reader = BufReader::new(file);
                let mut bytes = Vec::new();
                reader.read_to_end(&mut bytes)?;
                let (crate_data, rem) = postcard::take_from_bytes::<CrateData>(&bytes)
                    .map_err(|err| anyhow::anyhow!("postcard deserialize error: {err:?}"))?;
                if !rem.is_empty() {
                    anyhow::bail!("postcard deserialize error: trailing bytes left in input");
                }
                Ok(crate_data)
            }
        }
    }
}
