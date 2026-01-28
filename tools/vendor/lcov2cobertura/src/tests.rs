// safety: if tests panic we see it on CI
#![allow(clippy::unwrap_used)]

#[cfg(test)]
use super::*;

// TODO follow https://github.com/eriwen/lcov-to-cobertura-xml/blob/master/test/test_lcov_cobertura.py
#[test]
fn test_parse() {
    let lcov = r"
SF:foo/file.ext
DA:1,1
DA:2,0
BRDA:1,1,1,1
BRDA:1,1,2,0
end_of_record
";
    let result = parse_lines(lcov.as_bytes().lines(), "", &[]).unwrap();

    assert!(result.packages.contains_key("foo"));
    let foo = result.packages.get("foo").unwrap();
    assert!(foo.classes.contains_key("foo/file.ext"));
    let foo_summary = foo.summary();
    assert_eq!(foo_summary.branches_covered, 1);
    assert_eq!(foo_summary.branches_total, 2);
    assert_eq!(foo_summary.branch_rate(), 0.5);
    assert_eq!(foo_summary.line_rate(), 0.5);
    assert_eq!(foo_summary.lines_covered, 1);
    assert_eq!(foo_summary.lines_total, 2);
    let class = foo.classes.get("foo/file.ext").unwrap();
    let class_summary = class.summary();
    assert_eq!(class_summary.branches_covered, 1);
    assert_eq!(class_summary.branches_total, 2);
    assert!(class.methods.is_empty());
}

#[test]
fn test_parse_with_functions() {
    let lcov = "TN:\nSF:foo/file.ext\nDA:1,1\nDA:2,0\nFN:1,(anonymous_1)\nFN:2,namedFn\nFNDA:1,(anonymous_1)\nend_of_record\n";
    let result = parse_lines(lcov.as_bytes().lines(), "", &[]).unwrap();
    let foo = result.packages.get("foo").unwrap();
    let class = foo.classes.get("foo/file.ext").unwrap();
    let foo_summary = foo.summary();
    assert_eq!(foo_summary.line_rate(), 0.5);
    assert_eq!(foo_summary.lines_covered, 1);
    assert_eq!(foo_summary.lines_total, 2);
    assert_eq!(class.methods.get("(anonymous_1)"), Some(&(1, 1)));
    assert_eq!(class.methods.get("namedFn"), Some(&(2, 0)));
}

#[test]
fn test_parse_with_checksum() {
    let lcov = "SF:foo/file.ext\nDA:1,1,dummychecksum\nDA:2,0,dummychecksum\nBRDA:1,1,1,1\nBRDA:1,1,2,0\nend_of_record\n";
    let result = parse_lines(lcov.as_bytes().lines(), "", &[]).unwrap();
    let foo = result.packages.get("foo").unwrap();
    let foo_summary = foo.summary();
    assert_eq!(foo_summary.branches_covered, 1);
    assert_eq!(foo_summary.branches_total, 2);
    assert_eq!(foo_summary.lines_covered, 1);
    assert_eq!(foo_summary.lines_total, 2);
    let class = foo.classes.get("foo/file.ext").unwrap();
    let class_summary = class.summary();
    assert_eq!(class_summary.branches_covered, 1);
    assert_eq!(class_summary.branches_total, 2);
    assert!(class.methods.is_empty());
}

#[test]
fn test_exclude_package() {
    let lcov = "SF:foo/file.ext\nDA:1,1\nDA:2,0\nend_of_record\nSF:bar/file.ext\nDA:1,1\nDA:2,1\nend_of_record\n";
    let excludes = &["foo"];
    let result = parse_lines(lcov.as_bytes().lines(), "", excludes).unwrap();
    assert!(result.packages.contains_key("bar"));
    assert!(!result.packages.contains_key("foo"));
    // test regex support
    let excludes = &["(foo|bar)"];
    let result = parse_lines(lcov.as_bytes().lines(), "", excludes).unwrap();
    assert!(!result.packages.contains_key("bar"));
    assert!(!result.packages.contains_key("foo"));
}

#[test]
fn test_method_name_with_comma() {
    let lcov =  "TN:\nSF:foo/file.ext\nDA:1,1\nDA:2,0\nFN:1,(anonymous_1<foo, bar>)\nFN:2,namedFn\nFNDA:1,(anonymous_1<foo, bar>)\nend_of_record\n";
    let result = parse_lines(lcov.as_bytes().lines(), "", &[]).unwrap();
    let foo = result.packages.get("foo").unwrap();
    let class = foo.classes.get("foo/file.ext").unwrap();
    assert!(class.methods.contains_key("namedFn"));
    assert!(class.methods.contains_key("(anonymous_1<foo, bar>)"));
}

#[test]
fn test_treat_non_integer_line_execution_count_as_zero() {
    let lcov = "SF:foo/file.ext\nDA:1,=====\nDA:2,2\nBRDA:1,1,1,1\nBRDA:1,1,2,0\nend_of_record\n";
    let result = parse_lines(lcov.as_bytes().lines(), "", &[]).unwrap();
    let foo = result.packages.get("foo").unwrap();
    let foo_summary = foo.summary();
    assert_eq!(foo_summary.lines_covered, 1);
    assert_eq!(foo_summary.lines_total, 2);
}

#[test]
fn test_generate_cobertura_xml() {
    let lcov =
            "TN:\nSF:foo/file.ext\nDA:1,1\nDA:2,0\nBRDA:1,1,1,1\nBRDA:1,1,2,0\nFN:1,(anonymous_1)\nFN:2,namedFn\nFNDA:1,(anonymous_1)\nend_of_record\n";
    let xml = r#"<?xml version="1.0" ?>
<!DOCTYPE coverage SYSTEM "https://cobertura.sourceforge.net/xml/coverage-04.dtd">
<coverage branch-rate="0.5" branches-covered="1" branches-valid="2" complexity="0" line-rate="0.5" lines-covered="1" lines-valid="2" timestamp="1346815648000" version="2.0.3">
    <sources>
        <source>.</source>
    </sources>
    <packages>
        <package line-rate="0.5" branch-rate="0.5" name="foo" complexity="0">
            <classes>
                <class branch-rate="0.5" complexity="0" filename="foo/file.ext" line-rate="0.5" name="foo.file.ext">
                    <methods>
                        <method name="(anonymous_1)" signature="" complexity="0" line-rate="1" branch-rate="1">
                            <lines>
                                <line hits="1" number="1" branch="false"/>
                            </lines>
                        </method>
                        <method name="namedFn" signature="" complexity="0" line-rate="0" branch-rate="0">
                            <lines>
                                <line hits="0" number="2" branch="false"/>
                            </lines>
                        </method>
                    </methods>
                    <lines>
                        <line branch="true" hits="1" number="1" condition-coverage="50% (1/2)"/>
                        <line branch="false" hits="0" number="2"/>
                    </lines>
                </class>
            </classes>
        </package>
    </packages>
</coverage>"#;
    let demangler = demangle::NullDemangler::new();
    let result = parse_lines(lcov.as_bytes().lines(), ".", &[]).unwrap();
    let lcov_xml = coverage_to_string(&result, 1346815648000, demangler).unwrap();
    assert_eq!(lcov_xml, xml);
}

#[test]
fn test_demangle() {
    let lcov = "TN:\nSF:foo/foo.cpp\nFN:3,_ZN3Foo6answerEv\nFNDA:1,_ZN3Foo6answerEv\nFN:8,_ZN3Foo3sqrEi\nFNDA:1,_ZN3Foo3sqrEi\nDA:3,1\nDA:5,1\nDA:8,1\nDA:10,1\nend_of_record";
    #[cfg(target_os = "macos")]
    let demangler = demangle::CppDemangler::new("/opt/homebrew/opt/binutils/bin/c++filt").unwrap();
    #[cfg(not(target_os = "macos"))]
    let demangler = demangle::CppDemangler::new("c++filt").unwrap();
    let result = parse_lines(lcov.as_bytes().lines(), ".", &[]).unwrap();
    let lcov_xml = coverage_to_string(&result, 1346815648000, demangler).unwrap();
    let xml = r#"<?xml version="1.0" ?>
<!DOCTYPE coverage SYSTEM "https://cobertura.sourceforge.net/xml/coverage-04.dtd">
<coverage branch-rate="0" branches-covered="0" branches-valid="0" complexity="0" line-rate="1" lines-covered="4" lines-valid="4" timestamp="1346815648000" version="2.0.3">
    <sources>
        <source>.</source>
    </sources>
    <packages>
        <package line-rate="1" branch-rate="0" name="foo" complexity="0">
            <classes>
                <class branch-rate="0" complexity="0" filename="foo/foo.cpp" line-rate="1" name="foo.foo.cpp">
                    <methods>
                        <method name="Foo::sqr(int)" signature="" complexity="0" line-rate="1" branch-rate="1">
                            <lines>
                                <line hits="1" number="8" branch="false"/>
                            </lines>
                        </method>
                        <method name="Foo::answer()" signature="" complexity="0" line-rate="1" branch-rate="1">
                            <lines>
                                <line hits="1" number="3" branch="false"/>
                            </lines>
                        </method>
                    </methods>
                    <lines>
                        <line branch="false" hits="1" number="3"/>
                        <line branch="false" hits="1" number="5"/>
                        <line branch="false" hits="1" number="8"/>
                        <line branch="false" hits="1" number="10"/>
                    </lines>
                </class>
            </classes>
        </package>
    </packages>
</coverage>"#;
    assert_eq!(lcov_xml, xml);
}

#[test]
fn test_demangle_rust() {
    let lcov = "TN:\nSF:foo/foo.cpp\nFN:3,_RNvC6_123foo3bar\nFNDA:1,_RINbNbCskIICzLVDPPb_5alloc5alloc8box_freeDINbNiB4_5boxed5FnBoxuEp6OutputuEL_ECs1iopQbuBiw2_3std\nFN:8,_RC3foo.llvm.9D1C9369\nFNDA:1,_RC3foo.llvm.9D1C9369\nDA:3,1\nDA:5,1\nDA:8,1\nDA:10,1\nend_of_record";
    let demangler = demangle::RustDemangler::new();
    let result = parse_lines(lcov.as_bytes().lines(), ".", &[]).unwrap();
    let lcov_xml = coverage_to_string(&result, 1346815648000, demangler).unwrap();
    let xml = r#"<?xml version="1.0" ?>
<!DOCTYPE coverage SYSTEM "https://cobertura.sourceforge.net/xml/coverage-04.dtd">
<coverage branch-rate="0" branches-covered="0" branches-valid="0" complexity="0" line-rate="1" lines-covered="4" lines-valid="4" timestamp="1346815648000" version="2.0.3">
    <sources>
        <source>.</source>
    </sources>
    <packages>
        <package line-rate="1" branch-rate="0" name="foo" complexity="0">
            <classes>
                <class branch-rate="0" complexity="0" filename="foo/foo.cpp" line-rate="1" name="foo.foo.cpp">
                    <methods>
                        <method name="foo" signature="" complexity="0" line-rate="1" branch-rate="1">
                            <lines>
                                <line hits="1" number="8" branch="false"/>
                            </lines>
                        </method>
                        <method name="alloc::alloc::box_free::&lt;dyn alloc::boxed::FnBox&lt;(), Output = ()&gt;&gt;" signature="" complexity="0" line-rate="1" branch-rate="1">
                            <lines>
                                <line hits="1" number="0" branch="false"/>
                            </lines>
                        </method>
                        <method name="123foo::bar" signature="" complexity="0" line-rate="0" branch-rate="0">
                            <lines>
                                <line hits="0" number="3" branch="false"/>
                            </lines>
                        </method>
                    </methods>
                    <lines>
                        <line branch="false" hits="1" number="3"/>
                        <line branch="false" hits="1" number="5"/>
                        <line branch="false" hits="1" number="8"/>
                        <line branch="false" hits="1" number="10"/>
                    </lines>
                </class>
            </classes>
        </package>
    </packages>
</coverage>"#;
    assert_eq!(lcov_xml, xml);
}
