use regex::Regex;
use reqwest::{self, header};
use std::borrow::Cow;
use std::env::consts::{ARCH, OS};
use std::fs;
use std::path::PathBuf;

use crate::{confirm, errors::*, version, Download, Extract, Status};

/// Release asset information
#[derive(Clone, Debug, Default)]
pub struct ReleaseAsset {
    pub download_url: String,
    pub name: String,
}

/// Update status with extended information
pub enum UpdateStatus {
    /// Crate is up to date
    UpToDate,
    /// Crate was updated to the contained release
    Updated(Release),
}

impl UpdateStatus {
    /// Turn the extended information into the crate's standard `Status` enum
    pub fn into_status(self, current_version: String) -> Status {
        match self {
            UpdateStatus::UpToDate => Status::UpToDate(current_version),
            UpdateStatus::Updated(release) => Status::Updated(release.version),
        }
    }

    /// Returns `true` if `Status::UpToDate`
    pub fn uptodate(&self) -> bool {
        matches!(*self, UpdateStatus::UpToDate)
    }

    /// Returns `true` if `Status::Updated`
    pub fn updated(&self) -> bool {
        !self.uptodate()
    }
}

/// Release information
#[derive(Clone, Debug, Default)]
pub struct Release {
    pub name: String,
    pub version: String,
    pub date: String,
    pub body: Option<String>,
    pub assets: Vec<ReleaseAsset>,
}

impl Release {
    /// Check if release has an asset who's name contains the specified `target`
    pub fn has_target_asset(&self, target: &str) -> bool {
        self.assets.iter().any(|asset| asset.name.contains(target))
    }

    /// Return the first `ReleaseAsset` for the current release who's name
    /// contains the specified `target` and possibly `identifier`
    pub fn asset_for(&self, target: &str, identifier: Option<&str>) -> Option<ReleaseAsset> {
        self.assets
            .iter()
            .find(|asset| {
                (asset.name.contains(target)
                    || (asset.name.contains(OS) && asset.name.contains(ARCH)))
                    && if let Some(i) = identifier {
                        asset.name.contains(i)
                    } else {
                        true
                    }
            })
            .cloned()
    }
}

/// Updates to a specified or latest release
pub trait ReleaseUpdate {
    /// Fetch details of the latest release from the backend
    fn get_latest_release(&self) -> Result<Release>;

    /// Fetch details of the latest release from the backend
    fn get_latest_releases(&self, current_version: &str) -> Result<Vec<Release>>;

    /// Fetch details of the release matching the specified version
    fn get_release_version(&self, ver: &str) -> Result<Release>;

    /// Current version of binary being updated
    fn current_version(&self) -> String;

    /// Target platform the update is being performed for
    fn target(&self) -> String;

    /// Target version optionally specified for the update
    fn target_version(&self) -> Option<String>;

    /// Optional identifier of determining the asset among multiple matches
    fn identifier(&self) -> Option<String> {
        None
    }

    /// Name of the binary being updated
    fn bin_name(&self) -> String;

    /// Installation path for the binary being updated
    fn bin_install_path(&self) -> PathBuf;

    /// Path of the binary to be extracted from release package
    fn bin_path_in_archive(&self) -> String;

    /// Flag indicating if progress information shall be output when downloading a release
    fn show_download_progress(&self) -> bool;

    /// Flag indicating if process informative messages shall be output
    fn show_output(&self) -> bool;

    /// Flag indicating if the user shouldn't be prompted to confirm an update
    fn no_confirm(&self) -> bool;

    // message template to use if `show_download_progress` is set (see `indicatif::ProgressStyle`)
    fn progress_template(&self) -> String;

    // progress_chars to use if `show_download_progress` is set (see `indicatif::ProgressStyle`)
    fn progress_chars(&self) -> String;

    /// Authorisation token for communicating with backend
    fn auth_token(&self) -> Option<String>;

    /// ed25519ph verifying keys to validate a download's authenticy
    #[cfg(feature = "signatures")]
    fn verifying_keys(&self) -> &[[u8; zipsign_api::PUBLIC_KEY_LENGTH]] {
        &[]
    }

    /// Construct a header with an authorisation entry if an auth token is provided
    fn api_headers(&self, auth_token: &Option<String>) -> Result<header::HeaderMap> {
        let mut headers = header::HeaderMap::new();

        if auth_token.is_some() {
            headers.insert(
                header::AUTHORIZATION,
                (String::from("token ") + &auth_token.clone().unwrap())
                    .parse()
                    .unwrap(),
            );
        };

        Ok(headers)
    }

    /// Display release information and update the current binary to the latest release, pending
    /// confirmation from the user
    fn update(&self) -> Result<Status> {
        let current_version = self.current_version();
        self.update_extended()
            .map(|s| s.into_status(current_version))
    }

    /// Same as `update`, but returns `UpdateStatus`.
    fn update_extended(&self) -> Result<UpdateStatus> {
        let bin_install_path = self.bin_install_path();
        let bin_name = self.bin_name();

        let current_version = self.current_version();
        let target = self.target();
        let show_output = self.show_output();
        println(show_output, &format!("Checking target-arch... {}", target));
        println(
            show_output,
            &format!("Checking current version... v{}", current_version),
        );

        let release = match self.target_version() {
            None => {
                print_flush(show_output, "Checking latest released version... ")?;
                let releases = self.get_latest_releases(&current_version)?;
                let release = {
                    // Filter compatible version
                    let compatible_releases = releases
                        .iter()
                        .filter(|r| {
                            version::bump_is_compatible(&current_version, &r.version)
                                .unwrap_or(false)
                        })
                        .collect::<Vec<_>>();

                    // Get the first version
                    let release = compatible_releases.first().cloned();
                    if let Some(release) = release {
                        println(
                            show_output,
                            &format!(
                                "v{} ({} versions compatible)",
                                release.version,
                                compatible_releases.len()
                            ),
                        );
                        release.clone()
                    } else {
                        let release = releases.first();
                        if let Some(release) = release {
                            println(
                                show_output,
                                &format!(
                                    "v{} ({} versions available)",
                                    release.version,
                                    releases.len()
                                ),
                            );
                            release.clone()
                        } else {
                            return Ok(UpdateStatus::UpToDate);
                        }
                    }
                };

                {
                    println(
                        show_output,
                        &format!(
                            "New release found! v{} --> v{}",
                            current_version, release.version
                        ),
                    );
                    let qualifier =
                        if version::bump_is_compatible(&current_version, &release.version)? {
                            ""
                        } else {
                            "*NOT* "
                        };
                    println(
                        show_output,
                        &format!("New release is {}compatible", qualifier),
                    );
                }

                release
            }
            Some(ref ver) => {
                println(show_output, &format!("Looking for tag: {}", ver));
                self.get_release_version(ver)?
            }
        };

        let target_asset = release
            .asset_for(&target, self.identifier().as_deref())
            .ok_or_else(|| {
                format_err!(Error::Release, "No asset found for target: `{}`", target)
            })?;

        let prompt_confirmation = !self.no_confirm();
        if self.show_output() || prompt_confirmation {
            println!("\n{} release status:", bin_name);
            println!("  * Current exe: {:?}", bin_install_path);
            println!("  * New exe release: {:?}", target_asset.name);
            println!("  * New exe download url: {:?}", target_asset.download_url);
            println!("\nThe new release will be downloaded/extracted and the existing binary will be replaced.");
        }
        if prompt_confirmation {
            confirm("Do you want to continue? [Y/n] ")?;
        }

        let tmp_archive_dir = tempfile::TempDir::new()?;
        let tmp_archive_path = tmp_archive_dir.path().join(&target_asset.name);
        let mut tmp_archive = fs::File::create(&tmp_archive_path)?;

        println(show_output, "Downloading...");
        let mut download = Download::from_url(&target_asset.download_url);
        let mut headers = self.api_headers(&self.auth_token())?;
        headers.insert(header::ACCEPT, "application/octet-stream".parse().unwrap());
        download.set_headers(headers);
        download.show_progress(self.show_download_progress());

        download.progress_template = self.progress_template();
        download.progress_chars = self.progress_chars();

        download.download_to(&mut tmp_archive)?;

        #[cfg(feature = "signatures")]
        verify_signature(&tmp_archive_path, self.verifying_keys())?;

        print_flush(show_output, "Extracting archive... ")?;

        let bin_path_str = Cow::Owned(self.bin_path_in_archive());

        /// Substitute the `var` variable in a string with the given `val` value.
        ///
        /// Variable format: `{{ var }}`
        fn substitute<'a: 'b, 'b>(str: &'a str, var: &str, val: &str) -> Cow<'b, str> {
            let format = format!(r"\{{\{{[[:space:]]*{}[[:space:]]*\}}\}}", var);
            Regex::new(&format).unwrap().replace_all(str, val)
        }

        let bin_path_str = substitute(&bin_path_str, "version", &release.version);
        let bin_path_str = substitute(&bin_path_str, "target", &target);
        let bin_path_str = substitute(&bin_path_str, "bin", &bin_name);
        let bin_path_str = bin_path_str.as_ref();

        Extract::from_source(&tmp_archive_path)
            .extract_file(tmp_archive_dir.path(), bin_path_str)?;
        let new_exe = tmp_archive_dir.path().join(bin_path_str);

        println(show_output, "Done");

        print_flush(show_output, "Replacing binary file... ")?;
        self_replace::self_replace(new_exe)?;
        println(show_output, "Done");

        Ok(UpdateStatus::Updated(release))
    }
}

// Print out message based on provided flag and flush the output buffer
fn print_flush(show_output: bool, msg: &str) -> Result<()> {
    if show_output {
        print_flush!("{}", msg);
    }
    Ok(())
}

// Print out message based on provided flag
fn println(show_output: bool, msg: &str) {
    if show_output {
        println!("{}", msg);
    }
}

#[cfg(feature = "signatures")]
fn verify_signature(
    archive_path: &std::path::Path,
    keys: &[[u8; zipsign_api::PUBLIC_KEY_LENGTH]],
) -> crate::Result<()> {
    if keys.is_empty() {
        return Ok(());
    }

    println!("Verifying downloaded file...");

    let archive_kind = crate::detect_archive(archive_path)?;
    #[cfg(any(feature = "archive-tar", feature = "archive-zip"))]
    {
        let context = archive_path
            .file_name()
            .and_then(|s| s.to_str())
            .map(|s| s.as_bytes())
            .ok_or(Error::NonUTF8)?;

        let keys = keys.iter().copied().map(Ok);
        let keys =
            zipsign_api::verify::collect_keys(keys).map_err(zipsign_api::ZipsignError::from)?;

        let mut exe = std::fs::File::open(archive_path)?;

        match archive_kind {
            #[cfg(feature = "archive-tar")]
            crate::ArchiveKind::Tar(Some(crate::Compression::Gz)) => {
                zipsign_api::verify::verify_tar(&mut exe, &keys, Some(context))
                    .map_err(zipsign_api::ZipsignError::from)?;
                return Ok(());
            }
            #[cfg(feature = "archive-zip")]
            crate::ArchiveKind::Zip => {
                zipsign_api::verify::verify_zip(&mut exe, &keys, Some(context))
                    .map_err(zipsign_api::ZipsignError::from)?;
                return Ok(());
            }
            _ => {}
        }
    }
    Err(Error::NoSignatures(archive_kind))
}
