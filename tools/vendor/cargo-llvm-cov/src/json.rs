// SPDX-License-Identifier: Apache-2.0 OR MIT

// Refs: https://github.com/llvm/llvm-project/blob/llvmorg-18.1.2/llvm/tools/llvm-cov/CoverageExporterJson.cpp
// TODO: reflect https://github.com/llvm/llvm-project/commit/8ecbb0404d740d1ab173554e47cef39cd5e3ef8c#diff-e5de2b538138d03e13b43901f61adc61992516c742991ebaf1a13f2f8623910a?

use std::{
    collections::{BTreeMap, HashMap},
    fmt,
};

use anyhow::{Context as _, Result};
use camino::Utf8PathBuf;
use regex::Regex;
use serde::ser::{Serialize, SerializeMap as _, Serializer};
use serde_derive::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
pub struct LlvmCovJsonExport {
    /// List of one or more export objects
    pub data: Vec<Export>,
    // llvm.coverage.json.export
    #[serde(rename = "type")]
    type_: String,
    version: String,
    /// Additional information injected into the export data.
    #[serde(skip_deserializing, skip_serializing_if = "Option::is_none")]
    cargo_llvm_cov: Option<CargoLlvmCov>,
}

/// <https://docs.codecov.com/docs/codecov-custom-coverage-format>
///
/// This represents the fraction: `{covered}/{count}`.
#[derive(Debug, Default)]
struct CodeCovCoverage {
    count: u64,
    covered: u64,
}

impl Serialize for CodeCovCoverage {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}/{}", self.covered, self.count))
    }
}

/// line -> coverage in fraction
#[derive(Default)]
struct CodeCovExport(BTreeMap<u64, CodeCovCoverage>);

/// Custom serialize [`CodeCovExport`] as "string" -> JSON (as function)
/// Serialize as "string" -> JSON
impl Serialize for CodeCovExport {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.0.len()))?;
        for (key, value) in &self.0 {
            map.serialize_entry(&key.to_string(), value)?;
        }
        map.end()
    }
}

#[derive(Default, Serialize)]
pub struct CodeCovJsonExport {
    /// filename -> list of uncovered lines.
    coverage: BTreeMap<String, CodeCovExport>,
}

impl CodeCovJsonExport {
    fn from_export(value: Export, ignore_filename_regex: Option<&Regex>) -> Self {
        let functions = value.functions.unwrap_or_default();

        let mut regions = HashMap::new();

        for func in functions {
            for filename in func.filenames {
                if let Some(re) = ignore_filename_regex {
                    if re.is_match(&filename) {
                        continue;
                    }
                }
                // region location to covered
                let coverage: &mut HashMap<RegionLocation, bool> =
                    regions.entry(filename).or_default();
                for region in &func.regions {
                    let loc = RegionLocation::from(region);

                    let covered = coverage.entry(loc).or_default();

                    *covered = *covered || region.execution_count() > 0;
                }
            }
        }

        let mut coverage = BTreeMap::new();

        for (filename, regions) in regions {
            let coverage: &mut CodeCovExport = coverage.entry(filename).or_default();

            for (loc, covered) in regions {
                for line in loc.lines() {
                    let coverage = coverage.0.entry(line).or_default();
                    coverage.count += 1;
                    coverage.covered += covered as u64;
                }
            }
        }

        Self { coverage }
    }

    #[must_use]
    pub fn from_llvm_cov_json_export(
        value: LlvmCovJsonExport,
        ignore_filename_regex: Option<&str>,
    ) -> Self {
        let re = ignore_filename_regex.map(|s| Regex::new(s).unwrap());
        let exports: Vec<_> =
            value.data.into_iter().map(|v| Self::from_export(v, re.as_ref())).collect();

        let mut combined = CodeCovJsonExport::default();

        // combine
        for export in exports {
            for (filename, coverage) in export.coverage {
                let combined = combined.coverage.entry(filename).or_default();
                for (line, coverage) in coverage.0 {
                    let combined = combined
                        .0
                        .entry(line)
                        .or_insert_with(|| CodeCovCoverage { count: 0, covered: 0 });
                    combined.count += coverage.count;
                    combined.covered += coverage.covered;
                }
            }
        }

        combined
    }
}

/// Files -> list of uncovered lines.
type UncoveredLines = BTreeMap<String, Vec<u64>>;

#[non_exhaustive]
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug))]
pub enum CoverageKind {
    Functions,
    Lines,
    Regions,
}

impl CoverageKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Functions => "functions",
            Self::Lines => "lines",
            Self::Regions => "regions",
        }
    }
}

impl LlvmCovJsonExport {
    pub fn demangle(&mut self) {
        for data in &mut self.data {
            if let Some(functions) = &mut data.functions {
                for func in functions {
                    func.name = format!("{:#}", rustc_demangle::demangle(&func.name));
                }
            }
        }
    }

    pub fn inject(&mut self, manifest_path: Utf8PathBuf) {
        self.cargo_llvm_cov = Some(CargoLlvmCov {
            version: env!("CARGO_PKG_VERSION"),
            manifest_path: manifest_path.into_string(),
        });
    }

    /// Gets the minimal lines coverage of all files.
    pub fn get_coverage_percent(&self, kind: CoverageKind) -> Result<f64> {
        let mut count = 0_f64;
        let mut covered = 0_f64;
        for data in &self.data {
            let totals = &data.totals.as_object().context("totals is not an object")?;
            let lines =
                &totals[kind.as_str()].as_object().context(format!("no {}", kind.as_str()))?;
            count += lines["count"].as_f64().context("no count")?;
            covered += lines["covered"].as_f64().context("no covered")?;
        }

        if count == 0_f64 {
            return Ok(0_f64);
        }

        Ok(covered * 100_f64 / count)
    }

    /// Gets the list of uncovered lines of all files.
    #[must_use]
    pub fn get_uncovered_lines(&self, ignore_filename_regex: Option<&str>) -> UncoveredLines {
        let mut uncovered_files: UncoveredLines = BTreeMap::new();
        let mut covered_files: UncoveredLines = BTreeMap::new();
        let re = ignore_filename_regex.map(|s| Regex::new(s).unwrap());
        for data in &self.data {
            if let Some(ref functions) = data.functions {
                // Iterate over all functions inside the coverage data.
                for function in functions {
                    if function.filenames.is_empty() {
                        continue;
                    }
                    let file_name = &function.filenames[0];
                    if let Some(ref re) = re {
                        if re.is_match(file_name) {
                            continue;
                        }
                    }
                    let mut lines: BTreeMap<u64, u64> = BTreeMap::new();
                    // Iterate over all possible regions inside a function:
                    for region in &function.regions {
                        // LineStart, ColumnStart, LineEnd, ColumnEnd, ExecutionCount, FileID, ExpandedFileID, Kind
                        let line_start = region.0;
                        let line_end = region.2;
                        let exec_count = region.4;
                        // Remember the execution count for each line of that region:
                        for line in line_start..=line_end {
                            *lines.entry(line).or_insert(0) += exec_count;
                        }
                    }

                    let mut uncovered_lines: Vec<u64> = lines
                        .iter()
                        .filter(|(_line, exec_count)| **exec_count == 0)
                        .map(|(line, _exec_count)| *line)
                        .collect();
                    let mut covered_lines: Vec<u64> = lines
                        .iter()
                        .filter(|(_line, exec_count)| **exec_count > 0)
                        .map(|(line, _exec_count)| *line)
                        .collect();
                    if !uncovered_lines.is_empty() {
                        uncovered_files
                            .entry(file_name.clone())
                            .or_default()
                            .append(&mut uncovered_lines);
                    }
                    if !covered_lines.is_empty() {
                        covered_files
                            .entry(file_name.clone())
                            .or_default()
                            .append(&mut covered_lines);
                    }
                }
            }
        }

        for uncovered_file in &mut uncovered_files {
            // Check if a line is both covered and non-covered. It's covered in this case.
            let file_name = uncovered_file.0;
            let uncovered_lines = uncovered_file.1;
            if let Some(covered_lines) = covered_files.get(file_name) {
                uncovered_lines.retain(|&x| !covered_lines.contains(&x));
            }

            // Remove duplicates.
            uncovered_lines.sort_unstable();
            uncovered_lines.dedup();
        }

        // Remove empty keys.
        uncovered_files.retain(|_, v| !v.is_empty());

        uncovered_files
    }

    pub fn count_uncovered_functions(&self) -> Result<u64> {
        let mut count = 0_u64;
        let mut covered = 0_u64;
        for data in &self.data {
            let totals = &data.totals.as_object().context("totals is not an object")?;
            let functions = &totals["functions"].as_object().context("no functions")?;
            count += functions["count"].as_u64().context("no count")?;
            covered += functions["covered"].as_u64().context("no covered")?;
        }
        Ok(count.saturating_sub(covered))
    }

    pub fn count_uncovered_lines(&self) -> Result<u64> {
        let mut count = 0_u64;
        let mut covered = 0_u64;
        for data in &self.data {
            let totals = &data.totals.as_object().context("totals is not an object")?;
            let lines = &totals["lines"].as_object().context("no lines")?;
            count += lines["count"].as_u64().context("no count")?;
            covered += lines["covered"].as_u64().context("no covered")?;
        }
        Ok(count.saturating_sub(covered))
    }

    pub fn count_uncovered_regions(&self) -> Result<u64> {
        let mut count = 0_u64;
        let mut covered = 0_u64;
        for data in &self.data {
            let totals = &data.totals.as_object().context("totals is not an object")?;
            let regions = &totals["regions"].as_object().context("no regions")?;
            count += regions["count"].as_u64().context("no count")?;
            covered += regions["covered"].as_u64().context("no covered")?;
        }
        Ok(count.saturating_sub(covered))
    }
}

/// Json representation of one `CoverageMapping`
#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
pub struct Export {
    /// List of objects describing coverage for files
    pub files: Vec<File>,
    /// List of objects describing coverage for functions
    ///
    /// This is None if report is summary-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    functions: Option<Vec<Function>>,
    totals: serde_json::Value,
}

/// Coverage for a single file
#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
pub struct File {
    /// List of Branches in the file
    ///
    /// This is None if report is summary-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    branches: Option<Vec<serde_json::Value>>,
    /// List of MC/DC records contained in the file
    ///
    /// This is None if report is summary-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    mcdc_records: Option<Vec<serde_json::Value>>,
    /// List of expansion records
    ///
    /// This is None if report is summary-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    expansions: Option<Vec<serde_json::Value>>,
    pub filename: String,
    /// List of Segments contained in the file
    ///
    /// This is None if report is summary-only.
    #[serde(skip_serializing_if = "Option::is_none")]
    segments: Option<Vec<Segment>>,
    /// Object summarizing the coverage for this file
    summary: Summary,
}

/// Describes a segment of the file with a counter
#[derive(Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
struct Segment(
    /* Line */ u64,
    /* Col */ u64,
    /* Count */ u64,
    /* HasCount */ bool,
    /* IsRegionEntry */ bool,
    /* IsGapRegion */ bool,
);

impl Segment {
    fn line(&self) -> u64 {
        self.0
    }
    fn col(&self) -> u64 {
        self.1
    }
    fn count(&self) -> u64 {
        self.2
    }
    fn has_count(&self) -> bool {
        self.3
    }
    fn is_region_entry(&self) -> bool {
        self.4
    }
    fn is_gap_region(&self) -> bool {
        self.5
    }
}

impl fmt::Debug for Segment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Segment")
            .field("line", &self.line())
            .field("col", &self.col())
            .field("count", &self.count())
            .field("has_count", &self.has_count())
            .field("is_region_entry", &self.is_region_entry())
            .field("is_gap_region", &self.is_gap_region())
            .finish()
    }
}

/// Coverage info for a single function
#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
struct Function {
    branches: Vec<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    mcdc_records: Option<Vec<serde_json::Value>>,
    count: u64,
    /// List of filenames that the function relates to
    filenames: Vec<String>,
    name: String,
    regions: Vec<Region>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
struct Region(
    /* LineStart */ u64,
    /* ColumnStart */ u64,
    /* LineEnd */ u64,
    /* ColumnEnd */ u64,
    /* ExecutionCount */ u64,
    /* FileID */ u64,
    /* ExpandedFileID */ u64,
    /* Kind */ u64,
);

impl Region {
    fn line_start(&self) -> u64 {
        self.0
    }
    fn column_start(&self) -> u64 {
        self.1
    }
    fn line_end(&self) -> u64 {
        self.2
    }
    fn column_end(&self) -> u64 {
        self.3
    }
    fn execution_count(&self) -> u64 {
        self.4
    }
    fn file_id(&self) -> u64 {
        self.5
    }
    fn expanded_file_id(&self) -> u64 {
        self.6
    }
    fn kind(&self) -> u64 {
        self.7
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Region")
            .field("line_start", &self.line_start())
            .field("column_start", &self.column_start())
            .field("line_end", &self.line_end())
            .field("column_end", &self.column_end())
            .field("execution_count", &self.execution_count())
            .field("file_id", &self.file_id())
            .field("expanded_file_id", &self.expanded_file_id())
            .field("kind", &self.kind())
            .finish()
    }
}

/// The location of a region
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
struct RegionLocation {
    start_line: u64,
    end_line: u64,
    start_column: u64,
    end_column: u64,
}

impl From<&Region> for RegionLocation {
    fn from(region: &Region) -> Self {
        Self {
            start_line: region.line_start(),
            end_line: region.line_end(),
            start_column: region.column_start(),
            end_column: region.column_end(),
        }
    }
}

impl RegionLocation {
    fn lines(&self) -> impl Iterator<Item = u64> {
        self.start_line..=self.end_line
    }
}

/// Object summarizing the coverage for this file
#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
struct Summary {
    /// Object summarizing branch coverage
    branches: CoverageCounts,
    /// Object summarizing mcdc coverage
    #[serde(skip_serializing_if = "Option::is_none")]
    mcdc: Option<CoverageCounts>,
    /// Object summarizing function coverage
    functions: CoverageCounts,
    instantiations: CoverageCounts,
    /// Object summarizing line coverage
    lines: CoverageCounts,
    /// Object summarizing region coverage
    regions: CoverageCounts,
}

#[derive(Debug, Serialize, Deserialize)]
#[cfg_attr(test, serde(deny_unknown_fields))]
struct CoverageCounts {
    count: u64,
    covered: u64,
    // Currently only branches and regions has this field.
    #[serde(skip_serializing_if = "Option::is_none")]
    notcovered: Option<u64>,
    percent: f64,
}

/// Information that is not part of the llvm-cov JSON export, but instead injected afterwards by us.
#[derive(Debug, Default, Serialize)]
#[cfg_attr(test, derive(PartialEq))]
struct CargoLlvmCov {
    /// Version of this project, which allows projects that depend on it, to express and verify
    /// requirements on specific versions.
    version: &'static str,
    /// Resolved path to the `Cargo.toml` manifest.
    manifest_path: String,
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use fs_err as fs;

    use super::*;

    #[test]
    fn test_parse_llvm_cov_json() {
        let files: Vec<_> = glob::glob(&format!(
            "{}/tests/fixtures/coverage-reports/**/*.json",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|path| !path.to_str().unwrap().contains("codecov.json"))
        .collect();
        assert!(!files.is_empty());

        for file in files {
            let s = fs::read_to_string(file).unwrap();
            let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();
            assert_eq!(json.type_, "llvm.coverage.json.export");
            assert!(json.version.starts_with("3.0."));
            assert_eq!(json.cargo_llvm_cov, None);
            serde_json::to_string(&json).unwrap();
        }
    }

    fn test_get_coverage_percent(kind: CoverageKind) {
        let expected = match kind {
            CoverageKind::Functions => 100_f64,
            CoverageKind::Lines => 57.142_857_142_857_146,
            CoverageKind::Regions => 61.538_461_538_461_54,
        };

        // There are 5 different percentages, make sure we pick the correct one.
        let file = format!(
            "{}/tests/fixtures/coverage-reports/no_coverage/no_coverage.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let s = fs::read_to_string(file).unwrap();
        let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();

        let actual = json.get_coverage_percent(kind).unwrap();
        assert_eq!(actual, expected, "kind={kind:?},actual={actual}");
    }

    #[test]
    fn test_get_functions_percent() {
        test_get_coverage_percent(CoverageKind::Functions);
    }

    #[test]
    fn test_get_lines_percent() {
        test_get_coverage_percent(CoverageKind::Lines);
    }

    #[test]
    fn test_get_regions_percent() {
        test_get_coverage_percent(CoverageKind::Regions);
    }

    #[test]
    fn test_count_uncovered() {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));

        let cases = &[
            // (path, uncovered_functions, uncovered_lines, uncovered_regions)
            ("tests/fixtures/coverage-reports/no_coverage/no_coverage.json", 0, 6, 5),
            ("tests/fixtures/coverage-reports/no_test/no_test.json", 1, 7, 7),
        ];

        for &(file, uncovered_functions, uncovered_lines, uncovered_regions) in cases {
            let file = &manifest_dir.join(file);
            let s = fs::read_to_string(file).unwrap();
            let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();
            assert_eq!(json.count_uncovered_functions().unwrap(), uncovered_functions, "{file:?}");
            assert_eq!(json.count_uncovered_lines().unwrap(), uncovered_lines, "{file:?}");
            assert_eq!(json.count_uncovered_regions().unwrap(), uncovered_regions, "{file:?}");
        }
    }

    #[test]
    fn test_get_uncovered_lines() {
        // Given a coverage report which includes function regions:
        // There are 5 different percentages, make sure we pick the correct one.
        let file = format!("{}/tests/fixtures/show-missing-lines.json", env!("CARGO_MANIFEST_DIR"));
        let s = fs::read_to_string(file).unwrap();
        let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();

        // When finding uncovered lines in that report:
        let ignore_filename_regex = None;
        let uncovered_lines = json.get_uncovered_lines(ignore_filename_regex);

        // Then make sure the file / line data matches the `llvm-cov report` output:
        let expected: UncoveredLines =
            vec![("src/lib.rs".to_owned(), vec![7, 8, 9])].into_iter().collect();
        assert_eq!(uncovered_lines, expected);
    }

    #[test]
    /// This was a case when counting line coverage based on the segments in files lead to
    /// incorrect results but doing it based on regions inside functions (the way `llvm-cov
    /// report`) leads to complete line coverage.
    fn test_get_uncovered_lines_complete() {
        let file = format!(
            "{}/tests/fixtures/show-missing-lines-complete.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let s = fs::read_to_string(file).unwrap();
        let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();

        let ignore_filename_regex = None;
        let uncovered_lines = json.get_uncovered_lines(ignore_filename_regex);

        let expected: UncoveredLines = UncoveredLines::new();
        assert_eq!(uncovered_lines, expected);
    }

    #[test]
    fn test_get_uncovered_lines_multi_missing() {
        // Given a coverage report which includes a line with multiple functions via macros + two
        // other uncovered lines:
        let file = format!(
            "{}/tests/fixtures/show-missing-lines-multi-missing.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let s = fs::read_to_string(file).unwrap();
        let json = serde_json::from_str::<LlvmCovJsonExport>(&s).unwrap();

        // When finding uncovered lines in that report:
        let ignore_filename_regex = None;
        let uncovered_lines = json.get_uncovered_lines(ignore_filename_regex);

        // Then make sure the file / line data matches the `llvm-cov report` output:
        let expected: UncoveredLines =
            vec![("src/lib.rs".to_owned(), vec![15, 17])].into_iter().collect();
        // This was just '11', i.e. there were two problems:
        // 1) line 11 has a serde macro which expands to multiple functions; some of those were
        //    covered, which should be presented as a "covered" 11th line.
        // 2) only the last function with missing lines were reported, so 15 and 17 was missing.
        assert_eq!(uncovered_lines, expected);
    }
}
