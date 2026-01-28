/*!
GitHub releases
*/
use hyper::HeaderMap;
use std::env::{self, consts::EXE_SUFFIX};
use std::path::{Path, PathBuf};

use reqwest::{self, header};

use crate::backends::find_rel_next_link;
use crate::version::bump_is_greater;
use crate::{
    errors::*,
    get_target,
    update::{Release, ReleaseAsset, ReleaseUpdate},
    DEFAULT_PROGRESS_CHARS, DEFAULT_PROGRESS_TEMPLATE,
};

impl ReleaseAsset {
    /// Parse a release-asset json object
    ///
    /// Errors:
    ///     * Missing required name & download-url keys
    fn from_asset(asset: &serde_json::Value) -> Result<ReleaseAsset> {
        let download_url = asset["url"]
            .as_str()
            .ok_or_else(|| format_err!(Error::Release, "Asset missing `url`"))?;
        let name = asset["name"]
            .as_str()
            .ok_or_else(|| format_err!(Error::Release, "Asset missing `name`"))?;
        Ok(ReleaseAsset {
            download_url: download_url.to_owned(),
            name: name.to_owned(),
        })
    }
}

impl Release {
    fn from_release(release: &serde_json::Value) -> Result<Release> {
        let tag = release["tag_name"]
            .as_str()
            .ok_or_else(|| format_err!(Error::Release, "Release missing `tag_name`"))?;
        let date = release["created_at"]
            .as_str()
            .ok_or_else(|| format_err!(Error::Release, "Release missing `created_at`"))?;
        let name = release["name"].as_str().unwrap_or(tag);
        let assets = release["assets"]
            .as_array()
            .ok_or_else(|| format_err!(Error::Release, "No assets found"))?;
        let body = release["body"].as_str().map(String::from);
        let assets = assets
            .iter()
            .map(ReleaseAsset::from_asset)
            .collect::<Result<Vec<ReleaseAsset>>>()?;
        Ok(Release {
            name: name.to_owned(),
            version: tag.trim_start_matches('v').to_owned(),
            date: date.to_owned(),
            body,
            assets,
        })
    }
}

/// `ReleaseList` Builder
#[derive(Clone, Debug)]
pub struct ReleaseListBuilder {
    repo_owner: Option<String>,
    repo_name: Option<String>,
    target: Option<String>,
    auth_token: Option<String>,
    custom_url: Option<String>,
}
impl ReleaseListBuilder {
    /// Set the repo owner, used to build a github api url
    pub fn repo_owner(&mut self, owner: &str) -> &mut Self {
        self.repo_owner = Some(owner.to_owned());
        self
    }

    /// Set the repo name, used to build a github api url
    pub fn repo_name(&mut self, name: &str) -> &mut Self {
        self.repo_name = Some(name.to_owned());
        self
    }

    /// Set the optional arch `target` name, used to filter available releases
    pub fn with_target(&mut self, target: &str) -> &mut Self {
        self.target = Some(target.to_owned());
        self
    }

    /// Set the optional github url, e.g. for a github enterprise installation.
    /// The url should provide the path to your API endpoint and end without a trailing slash,
    /// for example `https://api.github.com` or `https://github.mycorp.com/api/v3`
    pub fn with_url(&mut self, url: &str) -> &mut Self {
        self.custom_url = Some(url.to_owned());
        self
    }

    /// Set the authorization token, used in requests to the github api url
    ///
    /// This is to support private repos where you need a GitHub auth token.
    /// **Make sure not to bake the token into your app**; it is recommended
    /// you obtain it via another mechanism, such as environment variables
    /// or prompting the user for input
    pub fn auth_token(&mut self, auth_token: &str) -> &mut Self {
        self.auth_token = Some(auth_token.to_owned());
        self
    }

    /// Verify builder args, returning a `ReleaseList`
    pub fn build(&self) -> Result<ReleaseList> {
        Ok(ReleaseList {
            repo_owner: if let Some(ref owner) = self.repo_owner {
                owner.to_owned()
            } else {
                bail!(Error::Config, "`repo_owner` required")
            },
            repo_name: if let Some(ref name) = self.repo_name {
                name.to_owned()
            } else {
                bail!(Error::Config, "`repo_name` required")
            },
            target: self.target.clone(),
            auth_token: self.auth_token.clone(),
            custom_url: self.custom_url.clone(),
        })
    }
}

/// `ReleaseList` provides a builder api for querying a GitHub repo,
/// returning a `Vec` of available `Release`s
#[derive(Clone, Debug)]
pub struct ReleaseList {
    repo_owner: String,
    repo_name: String,
    target: Option<String>,
    auth_token: Option<String>,
    custom_url: Option<String>,
}
impl ReleaseList {
    /// Initialize a ReleaseListBuilder
    pub fn configure() -> ReleaseListBuilder {
        ReleaseListBuilder {
            repo_owner: None,
            repo_name: None,
            target: None,
            auth_token: None,
            custom_url: None,
        }
    }

    /// Retrieve a list of `Release`s.
    /// If specified, filter for those containing a specified `target`
    pub fn fetch(self) -> Result<Vec<Release>> {
        set_ssl_vars!();
        let api_url = format!(
            "{}/repos/{}/{}/releases",
            self.custom_url
                .as_ref()
                .unwrap_or(&"https://api.github.com".to_string()),
            self.repo_owner,
            self.repo_name
        );
        let releases = self.fetch_releases(&api_url)?;
        let releases = match self.target {
            None => releases,
            Some(ref target) => releases
                .into_iter()
                .filter(|r| r.has_target_asset(target))
                .collect::<Vec<_>>(),
        };
        Ok(releases)
    }

    fn fetch_releases(&self, url: &str) -> Result<Vec<Release>> {
        let client = reqwest::blocking::ClientBuilder::new()
            .use_rustls_tls()
            .http2_adaptive_window(true)
            .build()?;
        let resp = client
            .get(url)
            .headers(api_headers(&self.auth_token)?)
            .query(&[("per_page", "100")])
            .send()?;
        if !resp.status().is_success() {
            bail!(
                Error::Network,
                "api request failed with status: {:?} - for: {:?}",
                resp.status(),
                url
            )
        }
        let headers = resp.headers().clone();

        let releases = resp.json::<serde_json::Value>()?;
        let releases = releases
            .as_array()
            .ok_or_else(|| format_err!(Error::Release, "No releases found"))?;
        let mut releases = releases
            .iter()
            .map(Release::from_release)
            .collect::<Result<Vec<Release>>>()?;

        // handle paged responses containing `Link` header:
        // `Link: <https://api.github.com/resource?page=2>; rel="next"`
        let links = headers.get_all(reqwest::header::LINK);

        let next_link = links
            .iter()
            .filter_map(|link| {
                if let Ok(link) = link.to_str() {
                    find_rel_next_link(link)
                } else {
                    None
                }
            })
            .next();

        Ok(match next_link {
            None => releases,
            Some(link) => {
                releases.extend(self.fetch_releases(link)?);
                releases
            }
        })
    }
}

/// `github::Update` builder
///
/// Configure download and installation from
/// `https://api.github.com/repos/<repo_owner>/<repo_name>/releases/latest`
#[derive(Debug)]
pub struct UpdateBuilder {
    repo_owner: Option<String>,
    repo_name: Option<String>,
    target: Option<String>,
    identifier: Option<String>,
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
    custom_url: Option<String>,
    #[cfg(feature = "signatures")]
    verifying_keys: Vec<[u8; zipsign_api::PUBLIC_KEY_LENGTH]>,
}

impl UpdateBuilder {
    /// Initialize a new builder
    pub fn new() -> Self {
        Default::default()
    }

    /// Set the repo owner, used to build a github api url
    pub fn repo_owner(&mut self, owner: &str) -> &mut Self {
        self.repo_owner = Some(owner.to_owned());
        self
    }

    /// Set the repo name, used to build a github api url
    pub fn repo_name(&mut self, name: &str) -> &mut Self {
        self.repo_name = Some(name.to_owned());
        self
    }

    /// Set the optional github url, e.g. for a github enterprise installation.
    /// The url should provide the path to your API endpoint and end without a trailing slash,
    /// for example `https://api.github.com` or `https://github.mycorp.com/api/v3`
    pub fn with_url(&mut self, url: &str) -> &mut Self {
        self.custom_url = Some(url.to_owned());
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

    /// Set the identifiable token for the asset in case of multiple compatible assets
    ///
    /// If unspecified, the first asset matching the target will be chosen
    pub fn identifier(&mut self, identifier: &str) -> &mut Self {
        self.identifier = Some(identifier.to_owned());
        self
    }

    /// Set the exe's name. Also sets `bin_path_in_archive` if it hasn't already been set.
    ///
    /// This method will append the platform specific executable file suffix
    /// (see `std::env::consts::EXE_SUFFIX`) to the name if it's missing.
    pub fn bin_name(&mut self, name: &str) -> &mut Self {
        let raw_bin_name = format!("{}{}", name.trim_end_matches(EXE_SUFFIX), EXE_SUFFIX);
        if self.bin_path_in_archive.is_none() {
            self.bin_path_in_archive = Some(raw_bin_name.clone());
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
    /// # use self_update::backends::github::Update;
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

    /// Set the authorization token, used in requests to the github api url
    ///
    /// This is to support private repos where you need a GitHub auth token.
    /// **Make sure not to bake the token into your app**; it is recommended
    /// you obtain it via another mechanism, such as environment variables
    /// or prompting the user for input
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
            repo_owner: if let Some(ref owner) = self.repo_owner {
                owner.to_owned()
            } else {
                bail!(Error::Config, "`repo_owner` required")
            },
            repo_name: if let Some(ref name) = self.repo_name {
                name.to_owned()
            } else {
                bail!(Error::Config, "`repo_name` required")
            },
            target: self
                .target
                .as_ref()
                .map(|t| t.to_owned())
                .unwrap_or_else(|| get_target().to_owned()),
            identifier: self.identifier.clone(),
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
            custom_url: self.custom_url.clone(),
            #[cfg(feature = "signatures")]
            verifying_keys: self.verifying_keys.clone(),
        }))
    }
}

/// Updates to a specified or latest release distributed via GitHub
#[derive(Debug)]
pub struct Update {
    repo_owner: String,
    repo_name: String,
    target: String,
    identifier: Option<String>,
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
    custom_url: Option<String>,
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
        set_ssl_vars!();
        let api_url = format!(
            "{}/repos/{}/{}/releases/latest",
            self.custom_url
                .as_ref()
                .unwrap_or(&"https://api.github.com".to_string()),
            self.repo_owner,
            self.repo_name
        );
        let client = reqwest::blocking::ClientBuilder::new()
            .use_rustls_tls()
            .http2_adaptive_window(true)
            .build()?;
        let resp = client
            .get(&api_url)
            .headers(api_headers(&self.auth_token)?)
            .send()?;
        if !resp.status().is_success() {
            bail!(
                Error::Network,
                "api request failed with status: {:?} - for: {:?}",
                resp.status(),
                api_url
            )
        }
        let json = resp.json::<serde_json::Value>()?;
        Release::from_release(&json)
    }

    fn get_latest_releases(&self, current_version: &str) -> Result<Vec<Release>> {
        set_ssl_vars!();
        let api_url = format!(
            "{}/repos/{}/{}/releases",
            self.custom_url
                .as_ref()
                .unwrap_or(&"https://api.github.com".to_string()),
            self.repo_owner,
            self.repo_name
        );
        let resp = reqwest::blocking::Client::new()
            .get(&api_url)
            .headers(api_headers(&self.auth_token)?)
            .send()?;
        if !resp.status().is_success() {
            bail!(
                Error::Network,
                "api request failed with status: {:?} - for: {:?}",
                resp.status(),
                api_url
            )
        }

        let json = resp.json::<serde_json::Value>()?;
        json.as_array()
            .ok_or_else(|| format_err!(Error::Release, "No releases found"))
            .and_then(|releases| {
                releases
                    .iter()
                    .map(Release::from_release)
                    .filter(|r| {
                        r.as_ref().map_or(false, |r| {
                            bump_is_greater(current_version, &r.version).unwrap_or(false)
                        })
                    })
                    .collect::<Result<Vec<Release>>>()
            })
    }

    fn get_release_version(&self, ver: &str) -> Result<Release> {
        set_ssl_vars!();
        let api_url = format!(
            "{}/repos/{}/{}/releases/tags/{}",
            self.custom_url
                .as_ref()
                .unwrap_or(&"https://api.github.com".to_string()),
            self.repo_owner,
            self.repo_name,
            ver
        );
        let client = reqwest::blocking::ClientBuilder::new()
            .use_rustls_tls()
            .http2_adaptive_window(true)
            .build()?;
        let resp = client
            .get(&api_url)
            .headers(api_headers(&self.auth_token)?)
            .send()?;
        if !resp.status().is_success() {
            bail!(
                Error::Network,
                "api request failed with status: {:?} - for: {:?}",
                resp.status(),
                api_url
            )
        }
        let json = resp.json::<serde_json::Value>()?;
        Release::from_release(&json)
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

    fn identifier(&self) -> Option<String> {
        self.identifier.clone()
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

    fn api_headers(&self, auth_token: &Option<String>) -> Result<HeaderMap> {
        api_headers(auth_token)
    }

    #[cfg(feature = "signatures")]
    fn verifying_keys(&self) -> &[[u8; zipsign_api::PUBLIC_KEY_LENGTH]] {
        &self.verifying_keys
    }
}

impl Default for UpdateBuilder {
    fn default() -> Self {
        Self {
            repo_owner: None,
            repo_name: None,
            target: None,
            identifier: None,
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
            custom_url: None,
            #[cfg(feature = "signatures")]
            verifying_keys: vec![],
        }
    }
}

fn api_headers(auth_token: &Option<String>) -> Result<header::HeaderMap> {
    let mut headers = header::HeaderMap::new();
    headers.insert(
        header::USER_AGENT,
        "rust-reqwest/self-update"
            .parse()
            .expect("github invalid user-agent"),
    );

    if let Some(token) = auth_token {
        headers.insert(
            header::AUTHORIZATION,
            format!("token {}", token)
                .parse()
                .map_err(|err| Error::Config(format!("Failed to parse auth token: {}", err)))?,
        );
    };

    Ok(headers)
}
