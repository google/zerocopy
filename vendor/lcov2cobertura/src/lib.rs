//! Library to convert lcov data to cobertura XML files
use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, Cursor, Lines, Write};
use std::path::Path;

use quick_xml::events::{BytesEnd, BytesStart, BytesText, Event};
use quick_xml::writer::Writer;

mod cobertura_split;
mod demangle;
mod tests;

pub use cobertura_split::corbertura_xml_split;
pub use demangle::{CppDemangler, Demangler, NullDemangler, RustDemangler};

fn percent(a: usize, b: usize) -> f64 {
    if a == 0 {
        0.
    } else {
        b as f64 / a as f64
    }
}

/// Summary of coverage info
#[derive(Debug, Default, Clone)]
struct Summary {
    lines_total: usize,
    lines_covered: usize,
    branches_total: usize,
    branches_covered: usize,
}

impl Summary {
    fn branch_rate(&self) -> f64 {
        percent(self.branches_total, self.branches_covered)
    }
    fn line_rate(&self) -> f64 {
        percent(self.lines_total, self.lines_covered)
    }
}

impl std::ops::Add for Summary {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            lines_total: self.lines_total + other.lines_total,
            lines_covered: self.lines_covered + other.lines_covered,
            branches_total: self.branches_total + other.branches_total,
            branches_covered: self.branches_covered + other.branches_covered,
        }
    }
}

impl std::iter::Sum<Self> for Summary {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(Self::default(), |a, b| a + b)
    }
}

trait CompSummary {
    fn summary(&self) -> Summary;
}

/// Package data of coverage info
#[derive(Debug, Default)]
struct Package {
    classes: HashMap<String, Class>,
}

impl Package {
    fn insert_class(&mut self, relative_file_name: &str) -> Option<Class> {
        let class = Class::from_fn(relative_file_name);
        self.classes.insert(relative_file_name.to_owned(), class)
    }
}

impl CompSummary for Package {
    fn summary(&self) -> Summary {
        let lines_total = self.classes.values().map(|c| c.lines.len()).sum();
        let lines_covered = self.classes.values().map(|c| c.lines_covered).sum();
        let branches_total = self
            .classes
            .values()
            .map(|c| c.lines.values().map(|b| b.branches_total).sum::<usize>())
            .sum();
        let branches_covered = self
            .classes
            .values()
            .map(|c| c.lines.values().map(|b| b.branches_covered).sum::<usize>())
            .sum();

        Summary {
            lines_total,
            lines_covered,
            branches_total,
            branches_covered,
        }
    }
}

type FunctionHit = (usize, usize);

/// Class data of coverage info
#[derive(Debug, Default)]
pub struct Class {
    name: String,
    lines: HashMap<usize, Branch>,
    methods: BTreeMap<String, FunctionHit>, // for deterministic sorted xml
    lines_covered: usize,
}

impl Class {
    fn from_fn(relative_file_name: &str) -> Self {
        let elems = relative_file_name
            .split(std::path::MAIN_SEPARATOR)
            .collect::<Vec<&str>>();
        let name = elems.join(".");
        Self {
            name,
            ..Self::default()
        }
    }
}

impl CompSummary for Class {
    fn summary(&self) -> Summary {
        let lines_total = self.lines.len();
        let lines_covered = self.lines_covered;
        let branches_total = self.lines.values().map(|b| b.branches_total).sum::<usize>();
        let branches_covered = self
            .lines
            .values()
            .map(|b| b.branches_covered)
            .sum::<usize>();

        Summary {
            lines_total,
            lines_covered,
            branches_total,
            branches_covered,
        }
    }
}

/// Branch data of coverage info
#[derive(Debug, Default)]
pub struct Branch {
    branch: bool,
    branches_total: usize,
    branches_covered: usize,
    hits: usize,
}

/// Coverage information collected while parsing
#[derive(Debug, Default)]
pub struct CoverageData {
    packages: HashMap<String, Package>,
    base_dir: String,
    cdsummary: Summary, // FIXME remove this, done by summary trait!?
}

impl CompSummary for CoverageData {
    fn summary(&self) -> Summary {
        let all = self.packages.values().map(|v| v.summary()).sum();
        all
        //self.cdsummary.clone() + all
    }
}

// safety: using lots of unwraps on HashMap entries, should be safe because only internal use
// based on already parsed data which should have integrity. Malformed LCOV files might cause a
// panic though.
#[allow(clippy::unwrap_used)]
impl CoverageData {
    fn update_line_hits(
        &mut self,
        package_name: &str,
        relative_file_name: &str,
        line_number: usize,
        line_hits: usize,
    ) {
        // avoid allocation if entry exists
        if let Some(class) = self
            .packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(relative_file_name)
        {
            class.lines.entry(line_number).or_default().hits = line_hits;
        } else {
            self.packages
                .get_mut(package_name)
                .unwrap()
                .classes
                .entry(relative_file_name.to_owned())
                .or_insert_with(|| Class::from_fn(relative_file_name))
                .lines
                .entry(line_number)
                .or_default()
                .hits = line_hits;
        }
    }

    fn inc_branches(
        &mut self,
        package_name: &str,
        class_name: &str,
        line_number: usize,
        branch_hits: usize,
    ) {
        // insert default if missing to ensure entry exists
        self.packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(class_name)
            .unwrap()
            .lines
            .entry(line_number)
            .or_default();
        // do update
        self.packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(class_name)
            .unwrap()
            .lines
            .entry(line_number)
            .and_modify(|branch| {
                branch.branch = true;
                branch.branches_total += 1;
                if branch_hits > 0 {
                    branch.branches_covered += 1;
                }
            });
    }

    fn insert_method(
        &mut self,
        package_name: &str,
        class_name: &str,
        method_name: &str,
        method_line: usize,
    ) {
        self.packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(class_name)
            .unwrap()
            .methods
            .insert(method_name.to_owned(), (method_line, 0));
    }

    fn update_method_hits(
        &mut self,
        package_name: &str,
        class_name: &str,
        method_name: &str,
        method_hits: usize,
    ) {
        self.packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(class_name)
            .unwrap()
            .methods
            .entry(method_name.to_owned())
            .and_modify(|e| e.1 = method_hits)
            .or_insert((0, method_hits));
    }

    fn inc_lines_covered(&mut self, package_name: &str, class_name: &str) {
        self.packages
            .get_mut(package_name)
            .unwrap()
            .classes
            .get_mut(class_name)
            .unwrap()
            .lines_covered += 1;
    }

    fn inc_lines_total(&mut self) {
        self.cdsummary.lines_total += 1;
    }
}

/// parses from filename
pub fn parse_file<P: AsRef<Path>>(
    filename: P,
    base_dir: P,
    excludes: &[&str],
) -> anyhow::Result<CoverageData> {
    let file = std::fs::File::open(filename)?;
    let lines = std::io::BufReader::new(file).lines();

    parse_lines(lines, base_dir, excludes)
}

/// parses from iterator
pub fn parse_lines<P: AsRef<Path>, B: BufRead>(
    lines: Lines<B>,
    base_dir: P,
    excludes: &[&str],
) -> anyhow::Result<CoverageData> {
    let base_dir: &Path = base_dir.as_ref();
    let mut cov_data = CoverageData {
        base_dir: base_dir
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("base_dir cannot be converted to string"))?
            .to_string(),
        ..Default::default()
    };
    let mut relative_file_name = String::new();
    let mut package_name = String::new();
    // TODO use https://docs.rs/lcov/latest/lcov/ existing parser
    for line in lines {
        let line = line?;
        let mut split = line.splitn(2, ':');
        let (input_type, line) = (split.next(), split.last());

        match input_type {
            Some("SF") => {
                let file_name = line.ok_or_else(|| anyhow::anyhow!("SF entry has no filename"))?;
                let file_path = Path::new(file_name);
                // TODO: was `relative_file_name = os.path.relpath(file_name, self.base_dir)`
                // does not do the same as strip_prefix, but I am fairly certain it was the idea
                // TODO: proper unwrap error handling
                file_path
                    .strip_prefix(base_dir)
                    .unwrap_or(file_path)
                    .to_str()
                    .ok_or_else(|| {
                        anyhow::anyhow!("relative_file_name cannot be converted to string")
                    })?
                    .clone_into(&mut relative_file_name);
                let elems = relative_file_name
                    .split(std::path::MAIN_SEPARATOR)
                    .collect::<Vec<&str>>();
                package_name = elems[..elems.len() - 1].join(".");
                cov_data
                    .packages
                    .entry(package_name.clone())
                    .or_default()
                    .insert_class(&relative_file_name);
            }
            Some("DA") => {
                let mut split = line
                    .ok_or_else(|| anyhow::anyhow!("DA entry has no fields"))?
                    .split(',');
                let (line_number, line_hits) = (split.next(), split.next()); // ignore checksum
                if let (Some(number), Some(hits)) = (line_number, line_hits) {
                    let line_number: usize = number.parse()?;
                    let line_hits = hits.parse::<usize>().unwrap_or(0);
                    cov_data.update_line_hits(
                        &package_name,
                        &relative_file_name,
                        line_number,
                        line_hits,
                    );

                    if line_hits > 0 {
                        cov_data.inc_lines_covered(&package_name, &relative_file_name);
                    }
                    cov_data.inc_lines_total();
                }
            }
            Some("BRDA") => {
                if let [line_number, _block_number, _branch_number, branch_hits] = line
                    .ok_or_else(|| anyhow::anyhow!("BRDA entry has no fields"))?
                    .splitn(4, ',')
                    .map(|v| v.parse::<usize>().unwrap_or(0))
                    .collect::<Vec<usize>>()
                    .as_slice()
                {
                    cov_data.inc_branches(
                        &package_name,
                        &relative_file_name,
                        *line_number,
                        *branch_hits,
                    );
                }
            }
            Some("BRF") => {
                cov_data.cdsummary.branches_total += line
                    .ok_or_else(|| anyhow::anyhow!("BRF without value"))?
                    .parse::<usize>()
                    .unwrap_or(0);
            }
            Some("BRH") => {
                cov_data.cdsummary.branches_covered += line
                    .ok_or_else(|| anyhow::anyhow!("BRH without value"))?
                    .parse::<usize>()
                    .unwrap_or(0);
            }
            Some("FN") => {
                let mut split = line
                    .ok_or_else(|| anyhow::anyhow!("FN without fields"))?
                    .splitn(2, ',');
                let (function_line, function_name) = (split.next(), split.last());
                if let (Some(function_line), Some(function_name)) = (function_line, function_name) {
                    let function_line: usize = function_line.parse()?;
                    cov_data.insert_method(
                        &package_name,
                        &relative_file_name,
                        function_name,
                        function_line,
                    );
                }
            }
            Some("FNDA") => {
                let mut split = line
                    .ok_or_else(|| anyhow::anyhow!("FNDA without fields"))?
                    .splitn(2, ',');
                let (function_hits, function_name) = (split.next(), split.last());
                if let (Some(function_hits), Some(function_name)) = (function_hits, function_name) {
                    let function_hits: usize = function_hits.parse()?;
                    cov_data.update_method_hits(
                        &package_name,
                        &relative_file_name,
                        function_name,
                        function_hits,
                    );
                }
            }
            Some("end_of_record") => (),
            Some("FNF") => (), // FIXME  in real world data
            Some("FNH") => (), // FIXME  in real world data
            Some("LF") => (),  // FIXME  in real world data
            Some("LH") => (),  // FIXME  in real world data
            Some("TN") => (),  // is in tests input, does nothing?
            Some("") => (),    // empty line, skip
            Some(it) => anyhow::bail!("unknown type{:?}", it),
            None => anyhow::bail!("no input type for this line"),
        }
    }
    // remove unwanted packages
    let mut to_remove = vec![];
    let excludes: Result<Vec<regex::Regex>, _> =
        excludes.iter().map(|v| regex::Regex::new(v)).collect();
    let excludes = excludes?;
    for pkg_key in cov_data.packages.keys() {
        for re in &excludes {
            if re.is_match(pkg_key) {
                to_remove.push(pkg_key.to_owned());
                continue;
            }
        }
    }
    for ex in to_remove {
        cov_data.packages.remove(&ex);
    }
    Ok(cov_data)
}

macro_rules! s {
    ( $e:expr ) => {
        $e.to_string().as_str()
    };
}

/// dumps cobertura XML into given Writer object
pub fn dump_xml<D: for<'a> Demangler<'a, 'a>, W: Write>(
    writer: W,
    cov_data: &CoverageData,
    timestamp: u64,
    mut demangler: D,
) -> anyhow::Result<W> {
    let mut writer = Writer::new_with_indent(writer, b' ', 4);

    let mut elem = BytesStart::new("coverage");
    let cdsummary = cov_data.summary();
    elem.push_attribute(("branch-rate", s!(cdsummary.branch_rate())));
    elem.push_attribute(("branches-covered", s!(cdsummary.branches_covered)));
    elem.push_attribute(("branches-valid", s!(cdsummary.branches_total)));
    elem.push_attribute(("complexity", "0"));
    elem.push_attribute(("line-rate", s!(cdsummary.line_rate())));
    elem.push_attribute(("lines-covered", s!(cdsummary.lines_covered)));
    elem.push_attribute(("lines-valid", s!(cdsummary.lines_total)));
    elem.push_attribute(("timestamp", s!(timestamp)));
    elem.push_attribute(("version", "2.0.3"));
    writer.write_event(Event::Start(elem))?;

    // Sources
    writer.write_event(Event::Start(BytesStart::new("sources")))?;

    writer.write_event(Event::Start(BytesStart::new("source")))?;
    writer.write_event(Event::Text(BytesText::new(&cov_data.base_dir)))?;
    writer.write_event(Event::End(BytesEnd::new("source")))?;

    writer.write_event(Event::End(BytesEnd::new("sources")))?;
    // packages
    writer.write_event(Event::Start(BytesStart::new("packages")))?;

    for (pkg_name, package) in &cov_data.packages {
        let mut pkg = BytesStart::new("package");
        let pkg_sum = package.summary();
        pkg.push_attribute(("line-rate", s!(pkg_sum.line_rate())));
        pkg.push_attribute(("branch-rate", s!(pkg_sum.branch_rate())));
        pkg.push_attribute(("name", pkg_name.as_str()));
        pkg.push_attribute(("complexity", "0"));
        writer.write_event(Event::Start(pkg))?;
        // classes
        writer.write_event(Event::Start(BytesStart::new("classes")))?;

        for (class_name, cd) in &package.classes {
            let mut class = BytesStart::new("class");
            let cd_sum = cd.summary();
            class.push_attribute(("branch-rate", s!(cd_sum.branch_rate())));
            class.push_attribute(("complexity", "0"));
            class.push_attribute(("filename", class_name.as_str()));
            class.push_attribute(("line-rate", s!(cd_sum.line_rate())));
            class.push_attribute(("name", cd.name.as_str()));
            writer.write_event(Event::Start(class))?;
            // methods
            writer.write_event(Event::Start(BytesStart::new("methods")))?;

            for (method_name, (line, hits)) in &cd.methods {
                let mut method = BytesStart::new("method");
                let line_rate = if *hits > 0 { 1. } else { 0. };
                let branch_rate = if *hits > 0 { 1. } else { 0. };
                method.push_attribute(("name", demangler.demangle(method_name.as_str())?.as_ref()));
                method.push_attribute(("signature", ""));
                method.push_attribute(("complexity", "0"));
                method.push_attribute(("line-rate", s!(line_rate)));
                method.push_attribute(("branch-rate", s!(branch_rate)));
                writer.write_event(Event::Start(method))?;
                // method lines (always exactly one?)
                writer.write_event(Event::Start(BytesStart::new("lines")))?;

                writer
                    .create_element("line")
                    .with_attributes([
                        ("hits", s!(hits)),
                        ("number", s!(line)),
                        ("branch", "false"),
                    ])
                    .write_empty()?;

                // close method lines
                writer.write_event(Event::End(BytesEnd::new("lines")))?;

                // close methods
                writer.write_event(Event::End(BytesEnd::new("method")))?;
            }
            writer.write_event(Event::End(BytesEnd::new("methods")))?;
            // add class lines
            writer.write_event(Event::Start(BytesStart::new("lines")))?;
            let mut line_keys: Vec<usize> = cd.lines.keys().copied().collect();
            line_keys.sort();
            for line_number in &line_keys {
                // safety: guaranteed, using sorted keys as input
                #[allow(clippy::unwrap_used)]
                let cd_line = cd.lines.get(line_number).unwrap();
                let branch = cd_line.branch.to_string();
                let hits = cd_line.hits.to_string();
                let number = line_number.to_string();
                let cond_cov;
                let mut attrs = vec![
                    ("branch", branch.as_str()),
                    ("hits", hits.as_str()),
                    ("number", number.as_str()),
                ];
                if cd_line.branch {
                    let total = cd_line.branches_total;
                    let covered = cd_line.branches_covered;
                    let percentage = covered * 100 / total;
                    cond_cov = format!("{}% ({}/{})", percentage, covered, total);
                    attrs.push(("condition-coverage", cond_cov.as_str()));
                }
                writer
                    .create_element("line")
                    .with_attributes(attrs.into_iter())
                    .write_empty()?;

                // close class lines
            }
            writer.write_event(Event::End(BytesEnd::new("lines")))?;
            // close class
            writer.write_event(Event::End(BytesEnd::new("class")))?;
        }
        writer.write_event(Event::End(BytesEnd::new("classes")))?;
        // close package
        writer.write_event(Event::End(BytesEnd::new("package")))?;
    }
    demangler.stop()?;
    writer.write_event(Event::End(BytesEnd::new("packages")))?;

    // close coverage
    writer.write_event(Event::End(BytesEnd::new("coverage")))?;

    Ok(writer.into_inner())
}

/// convenience function to convert coverage data into a XML String
pub fn coverage_to_string<D: for<'a> Demangler<'a, 'a>>(
    cov_data: &CoverageData,
    timestamp: u64,
    demangler: D,
) -> anyhow::Result<String> {
    let buffer = Cursor::new(Vec::new());
    let buffer = dump_xml(buffer, cov_data, timestamp, demangler)?;
    let result = buffer.into_inner();
    let mut output = String::with_capacity(result.len() * 3 / 2);
    output.push_str(XML_HEADER);
    output.push_str(std::str::from_utf8(&result)?);
    Ok(output)
}

/// convenience function to write coverage data to a XML file
pub fn coverage_to_file<P: AsRef<Path>, D: for<'a> Demangler<'a, 'a>>(
    filename: P,
    cov_data: &CoverageData,
    timestamp: u64,
    demangler: D,
) -> anyhow::Result<()> {
    let mut buffer = std::fs::File::create(filename)?;
    buffer.write_all(XML_HEADER.as_bytes())?;
    dump_xml(buffer, cov_data, timestamp, demangler)?;
    Ok(())
}

const XML_HEADER: &str = r#"<?xml version="1.0" ?>
<!DOCTYPE coverage SYSTEM "https://cobertura.sourceforge.net/xml/coverage-04.dtd">
"#;
