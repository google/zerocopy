/*!
Amazon S3 releases
*/
use crate::{
    errors::*,
    get_target,
    update::{Release, ReleaseAsset, ReleaseUpdate},
    version::bump_is_greater,
    DEFAULT_PROGRESS_CHARS, DEFAULT_PROGRESS_TEMPLATE,
};
use quick_xml::events::Event;
use quick_xml::Reader;
use regex::Regex;
use std::cmp::Ordering;
use std::env::{self, consts::EXE_SUFFIX};
use std::path::{Path, PathBuf};

/// Maximum number of items to retrieve from S3 API
const MAX_KEYS: u8 = 100;

/// The service end point.
///
/// Currently S3, GCS, and DigitalOcean Spaces supported.
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug, Default)]
pub enum EndPoint {
    #[default]
    S3,
    S3DualStack,
    GCS,
    DigitalOceanSpaces,
}

/// `ReleaseList` Builder
#[derive(Clone, Debug)]
pub struct ReleaseListBuilder {
    end_point: EndPoint,
    bucket_name: Option<String>,
    asset_prefix: Option<String>,
    target: Option<String>,
    region: Option<String>,
}

impl ReleaseListBuilder {
    /// Set the bucket name, used to build an S3 api url
    pub fn bucket_name(&mut self, name: &str) -> &mut Self {
        self.bucket_name = Some(name.to_owned());
        self
    }

    /// Set the optional asset name prefix, used to filter available assets with a prefix string
    pub fn asset_prefix(&mut self, prefix: &str) -> &mut Self {
        self.asset_prefix = Some(prefix.to_owned());
        self
    }

    /// Set the S3 region used in the download url
    pub fn region(&mut self, region: &str) -> &mut Self {
        self.region = Some(region.to_owned());
        self
    }

    /// Set the end point
    pub fn end_point(&mut self, end_point: EndPoint) -> &mut Self {
        self.end_point = end_point;
        self
    }

    /// Set the optional arch `target` name, used to filter available releases
    pub fn with_target(&mut self, target: &str) -> &mut Self {
        self.target = Some(target.to_owned());
        self
    }

    /// Verify builder args, returning a `ReleaseList`
    pub fn build(&self) -> Result<ReleaseList> {
        Ok(ReleaseList {
            end_point: self.end_point,
            bucket_name: if let Some(ref name) = self.bucket_name {
                name.to_owned()
            } else {
                bail!(Error::Config, "`bucket_name` required")
            },
            region: self.region.clone(),
            asset_prefix: self.asset_prefix.clone(),
            target: self.target.clone(),
        })
    }
}

/// `ReleaseList` provides a builder api for querying an S3 bucket,
/// returning a `Vec` of available `Release`s
#[derive(Clone, Debug)]
pub struct ReleaseList {
    end_point: EndPoint,
    bucket_name: String,
    asset_prefix: Option<String>,
    target: Option<String>,
    region: Option<String>,
}

impl ReleaseList {
    /// Initialize a ReleaseListBuilder
    pub fn configure() -> ReleaseListBuilder {
        ReleaseListBuilder {
            end_point: EndPoint::default(),
            bucket_name: None,
            asset_prefix: None,
            target: None,
            region: None,
        }
    }

    /// Retrieve a list of `Release`s.
    /// If specified, filter for those containing a specified `target`
    pub fn fetch(&self) -> Result<Vec<Release>> {
        let releases = fetch_releases_from_s3(
            self.end_point,
            &self.bucket_name,
            &self.region,
            &self.asset_prefix,
        )?;
        let releases = match self.target {
            None => releases,
            Some(ref target) => releases
                .into_iter()
                .filter(|r| r.has_target_asset(target))
                .collect::<Vec<_>>(),
        };
        Ok(releases)
    }
}

/// `s3::Update` builder
///
/// Configure download and installation from
/// `https://<bucket_name>.s3.<region>.amazonaws.com/<asset filename>`
#[derive(Debug)]
pub struct UpdateBuilder {
    end_point: EndPoint,
    bucket_name: Option<String>,
    asset_prefix: Option<String>,
    target: Option<String>,
    region: Option<String>,
    bin_name: Option<String>,
    bin_install_path: Option<PathBuf>,
    bin_path_in_archive: Option<String>,
    show_download_progress: bool,
    show_output: bool,
    no_confirm: bool,
    current_version: Option<String>,
    target_version: Option<String>,
    progress_template: String,
    progress_chars: String,
    auth_token: Option<String>,
    #[cfg(feature = "signatures")]
    verifying_keys: Vec<[u8; zipsign_api::PUBLIC_KEY_LENGTH]>,
}

impl Default for UpdateBuilder {
    fn default() -> Self {
        Self {
            end_point: EndPoint::default(),
            bucket_name: None,
            asset_prefix: None,
            target: None,
            region: None,
            bin_name: None,
            bin_install_path: None,
            bin_path_in_archive: None,
            show_download_progress: false,
            show_output: true,
            no_confirm: false,
            current_version: None,
            target_version: None,
            progress_template: DEFAULT_PROGRESS_TEMPLATE.to_string(),
            progress_chars: DEFAULT_PROGRESS_CHARS.to_string(),
            auth_token: None,
            #[cfg(feature = "signatures")]
            verifying_keys: vec![],
        }
    }
}

/// Configure download and installation from bucket
impl UpdateBuilder {
    /// Initialize a new builder
    pub fn new() -> Self {
        Default::default()
    }

    /// Set the end point
    pub fn end_point(&mut self, end_point: EndPoint) -> &mut Self {
        self.end_point = end_point;
        self
    }

    /// Set the bucket name, used to build a s3 api url
    pub fn bucket_name(&mut self, name: &str) -> &mut Self {
        self.bucket_name = Some(name.to_owned());
        self
    }

    /// Set the optional asset name prefix, used to filter available assets with a prefix string
    pub fn asset_prefix(&mut self, prefix: &str) -> &mut Self {
        self.asset_prefix = Some(prefix.to_owned());
        self
    }

    /// Set the S3 region used in the download url
    pub fn region(&mut self, region: &str) -> &mut Self {
        self.region = Some(region.to_owned());
        self
    }

    /// Set the current app version, used to compare against the latest available version.
    /// The `cargo_crate_version!` macro can be used to pull the version from your `Cargo.toml`
    pub fn current_version(&mut self, ver: &str) -> &mut Self {
        self.current_version = Some(ver.to_owned());
        self
    }

    /// Set the target version tag to update to. This will be used to search for a release
    /// by tag name:
    /// `/repos/:owner/:repo/releases/tags/:tag`
    ///
    /// If not specified, the latest available release is used.
    pub fn target_version_tag(&mut self, ver: &str) -> &mut Self {
        self.target_version = Some(ver.to_owned());
        self
    }

    /// Set the target triple that will be downloaded, e.g. `x86_64-unknown-linux-gnu`.
    ///
    /// If unspecified, the build target of the crate will be used
    pub fn target(&mut self, target: &str) -> &mut Self {
        self.target = Some(target.to_owned());
        self
    }

    /// Set the exe's name. Also sets `bin_path_in_archive` if it hasn't already been set.
    pub fn bin_name(&mut self, name: &str) -> &mut Self {
        let raw_bin_name = format!("{}{}", name.trim_end_matches(EXE_SUFFIX), EXE_SUFFIX);
        if self.bin_path_in_archive.is_none() {
            self.bin_path_in_archive = Some(raw_bin_name.to_owned());
        }
        self.bin_name = Some(raw_bin_name);
        self
    }

    /// Set the installation path for the new exe, defaults to the current
    /// executable's path
    pub fn bin_install_path<A: AsRef<Path>>(&mut self, bin_install_path: A) -> &mut Self {
        self.bin_install_path = Some(PathBuf::from(bin_install_path.as_ref()));
        self
    }

    /// Set the path of the exe inside the release tarball. This is the location
    /// of the executable relative to the base of the tar'd directory and is the
    /// path that will be copied to the `bin_install_path`. If not specified, this
    /// will default to the value of `bin_name`. This only needs to be specified if
    /// the path to the binary (from the root of the tarball) is not equal to just
    /// the `bin_name`.
    ///
    /// This also supports variable paths:
    /// - `{{ bin }}` is replaced with the value of `bin_name`
    /// - `{{ target }}` is replaced with the value of `target`
    /// - `{{ version }}` is replaced with the value of `target_version` if set,
    /// otherwise the value of the latest available release version is used.
    ///
    /// # Example
    ///
    /// For a `myapp` binary with `windows` target and latest release version `1.2.3`,
    /// the tarball `myapp.tar.gz` has the contents:
    ///
    /// ```shell
    /// myapp.tar/
    ///  |------- windows-1.2.3-bin/
    ///  |         |--- myapp  # <-- executable
    /// ```
    ///
    /// The path provided should be:
    ///
    /// ```
    /// # use self_update::backends::s3::Update;
    /// # fn run() -> Result<(), Box<::std::error::Error>> {
    /// Update::configure()
    ///     .bin_path_in_archive("{{ target }}-{{ version }}-bin/{{ bin }}")
    /// #   .build()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn bin_path_in_archive(&mut self, bin_path: &str) -> &mut Self {
        self.bin_path_in_archive = Some(bin_path.to_owned());
        self
    }

    /// Toggle download progress bar, defaults to `off`.
    pub fn show_download_progress(&mut self, show: bool) -> &mut Self {
        self.show_download_progress = show;
        self
    }

    /// Set download progress style.
    pub fn set_progress_style(
        &mut self,
        progress_template: String,
        progress_chars: String,
    ) -> &mut Self {
        self.progress_template = progress_template;
        self.progress_chars = progress_chars;
        self
    }

    /// Toggle update output information, defaults to `true`.
    pub fn show_output(&mut self, show: bool) -> &mut Self {
        self.show_output = show;
        self
    }

    /// Toggle download confirmation. Defaults to `false`.
    pub fn no_confirm(&mut self, no_confirm: bool) -> &mut Self {
        self.no_confirm = no_confirm;
        self
    }

    pub fn auth_token(&mut self, auth_token: &str) -> &mut Self {
        self.auth_token = Some(auth_token.to_owned());
        self
    }

    /// Specify a slice of ed25519ph verifying keys to validate a download's authenticy
    ///
    /// If the feature is activated AND at least one key was provided, a download is verifying.
    /// At least one key has to match.
    #[cfg(feature = "signatures")]
    pub fn verifying_keys(
        &mut self,
        keys: impl Into<Vec<[u8; zipsign_api::PUBLIC_KEY_LENGTH]>>,
    ) -> &mut Self {
        self.verifying_keys = keys.into();
        self
    }

    /// Confirm config and create a ready-to-use `Update`
    ///
    /// * Errors:
    ///     * Config - Invalid `Update` configuration
    pub fn build(&self) -> Result<Box<dyn ReleaseUpdate>> {
        let bin_install_path = if let Some(v) = &self.bin_install_path {
            v.clone()
        } else {
            env::current_exe()?
        };

        Ok(Box::new(Update {
            end_point: self.end_point,
            bucket_name: if let Some(ref name) = self.bucket_name {
                name.to_owned()
            } else {
                bail!(Error::Config, "`bucket_name` required")
            },
            region: self.region.clone(),
            asset_prefix: self.asset_prefix.clone(),
            target: self
                .target
                .as_ref()
                .map(|t| t.to_owned())
                .unwrap_or_else(|| get_target().to_owned()),
            bin_name: if let Some(ref name) = self.bin_name {
                name.to_owned()
            } else {
                bail!(Error::Config, "`bin_name` required")
            },
            bin_install_path,
            bin_path_in_archive: if let Some(ref bin_path) = self.bin_path_in_archive {
                bin_path.to_owned()
            } else {
                bail!(Error::Config, "`bin_path_in_archive` required")
            },
            current_version: if let Some(ref ver) = self.current_version {
                ver.to_owned()
            } else {
                bail!(Error::Config, "`current_version` required")
            },
            target_version: self.target_version.as_ref().map(|v| v.to_owned()),
            show_download_progress: self.show_download_progress,
            progress_template: self.progress_template.clone(),
            progress_chars: self.progress_chars.clone(),
            show_output: self.show_output,
            no_confirm: self.no_confirm,
            auth_token: self.auth_token.clone(),
            #[cfg(feature = "signatures")]
            verifying_keys: self.verifying_keys.clone(),
        }))
    }
}

/// Updates to a specified or latest release distributed via S3
#[derive(Debug)]
pub struct Update {
    end_point: EndPoint,
    bucket_name: String,
    asset_prefix: Option<String>,
    target: String,
    region: Option<String>,
    current_version: String,
    target_version: Option<String>,
    bin_name: String,
    bin_install_path: PathBuf,
    bin_path_in_archive: String,
    show_download_progress: bool,
    show_output: bool,
    no_confirm: bool,
    progress_template: String,
    progress_chars: String,
    auth_token: Option<String>,
    #[cfg(feature = "signatures")]
    verifying_keys: Vec<[u8; zipsign_api::PUBLIC_KEY_LENGTH]>,
}

impl Update {
    /// Initialize a new `Update` builder
    pub fn configure() -> UpdateBuilder {
        UpdateBuilder::new()
    }
}

impl ReleaseUpdate for Update {
    fn get_latest_release(&self) -> Result<Release> {
        let releases = fetch_releases_from_s3(
            self.end_point,
            &self.bucket_name,
            &self.region,
            &self.asset_prefix,
        )?;
        let rel = releases
            .iter()
            .max_by(|x, y| match bump_is_greater(&y.version, &x.version) {
                Ok(is_greater) => {
                    if is_greater {
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    }
                }
                Err(_) => {
                    // Ignoring release due to an unexpected failure in parsing its version string
                    Ordering::Less
                }
            });

        match rel {
            Some(r) => Ok(r.clone()),
            None => bail!(Error::Release, "No release was found"),
        }
    }

    fn get_latest_releases(&self, current_version: &str) -> Result<Vec<Release>> {
        let releases = fetch_releases_from_s3(
            self.end_point,
            &self.bucket_name,
            &self.region,
            &self.asset_prefix,
        )?;

        let mut releases = releases
            .iter()
            .filter(|r| bump_is_greater(current_version, &r.version).unwrap_or(false))
            .cloned()
            .collect::<Vec<_>>();

        releases.sort_by(|x, y| match bump_is_greater(&y.version, &x.version) {
            Ok(is_greater) => {
                if is_greater {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            }
            Err(_) => {
                // Ignoring release due to an unexpected failure in parsing its version string
                Ordering::Less
            }
        });

        Ok(releases)
    }

    fn get_release_version(&self, ver: &str) -> Result<Release> {
        let releases = fetch_releases_from_s3(
            self.end_point,
            &self.bucket_name,
            &self.region,
            &self.asset_prefix,
        )?;
        let rel = releases.iter().find(|x| x.version == ver);
        match rel {
            Some(r) => Ok(r.clone()),
            None => bail!(
                Error::Release,
                "No release with version '{}' was found",
                ver
            ),
        }
    }

    fn current_version(&self) -> String {
        self.current_version.to_owned()
    }

    fn target(&self) -> String {
        self.target.clone()
    }

    fn target_version(&self) -> Option<String> {
        self.target_version.clone()
    }

    fn bin_name(&self) -> String {
        self.bin_name.clone()
    }

    fn bin_install_path(&self) -> PathBuf {
        self.bin_install_path.clone()
    }

    fn bin_path_in_archive(&self) -> String {
        self.bin_path_in_archive.clone()
    }

    fn show_download_progress(&self) -> bool {
        self.show_download_progress
    }

    fn show_output(&self) -> bool {
        self.show_output
    }

    fn no_confirm(&self) -> bool {
        self.no_confirm
    }

    fn progress_template(&self) -> String {
        self.progress_template.to_owned()
    }

    fn progress_chars(&self) -> String {
        self.progress_chars.to_owned()
    }

    fn auth_token(&self) -> Option<String> {
        self.auth_token.clone()
    }

    #[cfg(feature = "signatures")]
    fn verifying_keys(&self) -> &[[u8; zipsign_api::PUBLIC_KEY_LENGTH]] {
        &self.verifying_keys
    }
}

/// Obtain list of releases from AWS S3 API, from bucket and region specified,
/// filtering assets which don't match the prefix string if provided.
///
/// This will strip the prefix from provided file names, allowing use with subdirectories
fn fetch_releases_from_s3(
    end_point: EndPoint,
    bucket_name: &str,
    region: &Option<String>,
    asset_prefix: &Option<String>,
) -> Result<Vec<Release>> {
    let prefix = match asset_prefix {
        Some(prefix) => format!("&prefix={}", prefix),
        None => "".to_string(),
    };

    let region = region
        .as_ref()
        .ok_or_else(|| Error::Config("`region` required".to_string()));

    let download_base_url = match end_point {
        EndPoint::S3 => format!("https://{}.s3.{}.amazonaws.com/", bucket_name, region?),
        EndPoint::S3DualStack => format!(
            "https://{}.s3.dualstack.{}.amazonaws.com/",
            bucket_name, region?
        ),
        EndPoint::DigitalOceanSpaces => format!(
            "https://{}.{}.digitaloceanspaces.com/",
            bucket_name, region?
        ),
        EndPoint::GCS => format!("https://storage.googleapis.com/{}/", bucket_name),
    };

    let api_url = match end_point {
        EndPoint::S3 | EndPoint::S3DualStack | EndPoint::DigitalOceanSpaces => format!(
            "{}?list-type=2&max-keys={}{}",
            download_base_url, MAX_KEYS, prefix
        ),
        EndPoint::GCS => format!("{}?max-keys={}{}", download_base_url, MAX_KEYS, prefix),
    };

    debug!("using api url: {:?}", api_url);

    let client = reqwest::blocking::ClientBuilder::new()
        .use_rustls_tls()
        .http2_adaptive_window(true)
        .build()?;
    let resp = client.get(&api_url).send()?;
    if !resp.status().is_success() {
        bail!(
            Error::Network,
            "S3 API request failed with status: {:?} - for: {:?}",
            resp.status(),
            api_url
        )
    }

    let body = resp.text()?;
    let mut reader = Reader::from_str(&body);
    reader.config_mut().trim_text(true);

    // Let's now parse the response to extract the releases
    enum Tag {
        Contents,
        Key,
        LastModified,
        Other,
    }

    let mut current_tag = Tag::Other;
    let mut current_release: Option<Release> = None;
    let regex =
        Regex::new(r"(?i)(?P<prefix>.*/)*(?P<name>.+)-[v]{0,1}(?P<version>\d+\.\d+\.\d+)-.+")
            .map_err(|err| {
                Error::Release(format!(
                    "Failed constructing regex to parse S3 filenames: {}",
                    err
                ))
            })?;

    // inspecting each XML element we populate our releases list
    let mut buf = Vec::new();
    let mut releases: Vec<Release> = vec![];
    loop {
        match reader.read_event_into(&mut buf) {
            Ok(Event::Start(ref e)) => match e.name().into_inner() {
                b"Contents" => {
                    current_tag = Tag::Contents;
                    if let Some(release) = current_release {
                        add_to_releases_list(&mut releases, release);
                    }
                    current_release = None;
                }
                b"Key" => current_tag = Tag::Key,
                b"LastModified" => current_tag = Tag::LastModified,
                _ => current_tag = Tag::Other,
            },
            Ok(Event::Text(e)) => {
                // if we cannot decode a tag text we just ignore it
                if let Ok(txt) = e.unescape().map(|r| r.into_owned()) {
                    match current_tag {
                        Tag::Key => {
                            let p = PathBuf::from(&txt);
                            let exe_name = match p.file_name().map(|v| v.to_str()) {
                                Some(Some(v)) => v,
                                _ => &txt,
                            };

                            if let Some(captures) = regex.captures(&txt) {
                                let release = current_release.get_or_insert(Release::default());
                                release.name = captures["name"].to_string();
                                release.version =
                                    captures["version"].trim_start_matches('v').to_string();
                                release.assets = vec![ReleaseAsset {
                                    name: exe_name.to_string(),
                                    download_url: format!("{}{}", download_base_url, txt),
                                }];
                                debug!("Matched release: {:?}", release);
                            } else {
                                debug!("Regex mismatch: {:?}", &txt);
                            }
                        }
                        Tag::LastModified => {
                            let release = current_release.get_or_insert(Release::default());
                            release.date = txt;
                        }
                        _ => (),
                    }
                }
            }
            Ok(Event::Eof) => {
                if let Some(release) = current_release {
                    add_to_releases_list(&mut releases, release);
                }
                break; // exits the loop when reaching end of file
            }
            Err(e) => bail!(
                Error::Release,
                "Failed when parsing S3 XML response at position {}: {:?}",
                reader.buffer_position(),
                e
            ),
            _ => (), // There are several other `Event`s we ignore here
        }

        buf.clear();
    }

    Ok(releases)
}

// Add a release to the list if it's doesn't exist yet, or merge its asset/s
// details into the release item already existing in the list
fn add_to_releases_list(releases: &mut Vec<Release>, mut rel: Release) {
    if !rel.version.is_empty() && !rel.name.is_empty() {
        match releases
            .iter()
            .position(|curr| curr.name == rel.name && curr.version == rel.version)
        {
            Some(index) => {
                rel.assets.append(&mut releases[index].assets);
                releases.push(rel);
                releases.swap_remove(index);
            }
            None => releases.push(rel),
        }
    }
}
