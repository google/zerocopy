use serde_json::{from_str, to_string_pretty, to_value, Value};
use std::fs;
use std::io::Read;
use std::path;
use valico::json_schema::{self, SchemaVersion};

fn visit_specs<F>(dir: &path::Path, cb: F)
where
    F: Fn(&path::Path, Value) + Copy,
{
    let mut contents = fs::read_dir(dir)
        .unwrap_or_else(|_| panic!("cannot list directory {dir:?}"))
        .collect::<Vec<_>>();
    contents.sort_by_key(|v| v.as_ref().unwrap().file_name());
    for entry in contents {
        let entry = entry.unwrap();
        let path = entry.path();
        if entry.file_type().unwrap().is_dir() {
            visit_specs(&path, cb);
        } else {
            match fs::File::open(&path) {
                Err(_) => continue,
                Ok(mut file) => {
                    let metadata = file.metadata().unwrap();
                    if metadata.is_file() {
                        let mut content = String::new();
                        file.read_to_string(&mut content).ok().unwrap();
                        let json: Value = from_str(&content).unwrap();
                        cb(&path, json);
                    }
                }
            }
        }
    }
}

#[test]
fn test_suite_draft7() {
    let mut content = String::new();

    fs::File::open(path::Path::new("tests/schema/schema.json"))
        .ok()
        .unwrap()
        .read_to_string(&mut content)
        .ok()
        .unwrap();

    let json_v7_schema: Value = from_str(&content).unwrap();

    println!("test json_schema::test_suite_draft7");

    visit_specs(
        path::Path::new("tests/schema/JSON-Schema-Test-Suite/tests/draft7"),
        |path, spec_set: Value| {
            let spec_set = spec_set.as_array().unwrap();

            println!(
                "\t{}",
                path.file_name()
                    .unwrap_or_default()
                    .to_str()
                    .unwrap_or_default()
            );

            let exceptions: Vec<(String, String)> = vec![
                (
                    "minLength.json".to_string(),
                    "one supplementary Unicode code point is not long enough".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "remote ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "remote fragment invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "ref within ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "changed scope ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "base URI change ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "string is invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "object is invalid".to_string(),
                ),
                (
                    "bignum.json".to_string(),
                    "a bignum is an integer".to_string(),
                ),
                (
                    "bignum.json".to_string(),
                    "a negative bignum is an integer".to_string(),
                ),
                (
                    "uri-reference.json".to_string(),
                    "an invalid URI Reference".to_string(),
                ),
                (
                    "uri-reference.json".to_string(),
                    "an invalid URI fragment".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 has no support for \\Z anchor from .NET".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "latin-1 non-breaking-space does not match (unlike e.g. Python)".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "latin-1 non-breaking-space matches (unlike e.g. Python)".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "zero-width whitespace matches".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "zero-width whitespace does not match".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #1".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #2".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #3".to_string(),
                ),
                (
                    // I believe it is trimmed as it is at the beginning, it works when inside.
                    "idn-hostname.json".to_string(),
                    "contains illegal char U+302E Hangul single dot tone mark".to_string(),
                ),
                (
                    // TODO uritemplate needs fixes/changes but the maintainer is inactive.
                    "uri-template.json".to_string(),
                    "an invalid uri-template".to_string(),
                ),
                (
                    // https://github.com/chronotope/chrono/issues/288
                    "time.json".to_string(),
                    "a valid time string".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "ref.json".to_string(),
                    "remote ref invalid".to_string(),
                ),
                (
                    // same as URI
                    "iri-reference.json".to_string(),
                    "an invalid IRI Reference".to_string(),
                ),
                (
                    // same as URI
                    "iri-reference.json".to_string(),
                    "an invalid IRI fragment".to_string(),
                ),
            ];
            let group_exceptions: Vec<(String, String)> = vec![
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 regex escapes control codes with \\c and upper letter".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 regex escapes control codes with \\c and lower letter".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\d matches ascii digits only".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\D matches everything but ascii digits".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\w matches ascii letters only".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\W matches everything but ascii letters".to_string(),
                ),
                (
                    // TODO json-pointer needs to handle relative JSON pointers
                    "relative-json-pointer.json".to_string(),
                    "validation of Relative JSON Pointers (RJP)".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "definitions.json".to_string(),
                    "invalid definition".to_string(),
                ),
                (
                    "idn-hostname.json".to_string(),
                    "validation of internationalized host names".to_string(),
                ),
                (
                    "email.json".to_string(),
                    "validation of e-mail addresses".to_string(),
                ),
                (
                    // optional overflow handling is not implemented
                    "float-overflow.json".to_string(),
                    "all integers are multiples of 0.5, if overflow is handled".to_string(),
                ),
            ];

            for spec in spec_set.iter() {
                let spec = spec.as_object().unwrap();
                let mut scope = json_schema::Scope::new();

                scope.compile(json_v7_schema.clone(), true).ok().unwrap();

                let spec_desc = spec
                    .get("description")
                    .map(|v| v.as_str().unwrap())
                    .unwrap_or("");
                let spec_exception_found = group_exceptions[..].contains(&(
                    path.file_name().unwrap().to_str().unwrap().to_string(),
                    spec_desc.to_string(),
                ));
                if spec_exception_found {
                    println!("\t\t{spec_desc} .. skipped");
                    continue;
                } else {
                    println!("\t\t{spec_desc}");
                }

                let schema =
                    match scope.compile_and_return(spec.get("schema").unwrap().clone(), false) {
                        Ok(schema) => schema,
                        Err(err) => panic!(
                            "Error in schema {} {}: {:?}",
                            path.file_name().unwrap().to_str().unwrap(),
                            spec.get("description").unwrap().as_str().unwrap(),
                            err
                        ),
                    };

                let tests = spec.get("tests").unwrap().as_array().unwrap();

                for test in tests.iter() {
                    let test = test.as_object().unwrap();
                    let description = test.get("description").unwrap().as_str().unwrap();
                    let data = test.get("data").unwrap();
                    let valid = test.get("valid").unwrap().as_bool().unwrap();

                    let exception_found = exceptions[..].contains(&(
                        path.file_name().unwrap().to_str().unwrap().to_string(),
                        description.to_string(),
                    ));
                    if exception_found {
                        println!("\t\t\t{description} .. skipped");
                        continue;
                    }

                    let state = schema.validate(data);

                    // TODO implement remote schema download for strict validation
                    if state.is_valid() != valid {
                        panic!(
                            "Failure: \"{}\" in \"{}\" -> \"{}\" with state: \n {}",
                            path.file_name().unwrap().to_str().unwrap(),
                            spec_desc,
                            description,
                            to_string_pretty(&to_value(&state).unwrap()).unwrap()
                        )
                    } else {
                        println!("\t\t\t{description} .. ok");
                    }
                }
            }
        },
    )
}

#[test]
fn test_suite_draft201909() {
    let mut content = String::new();

    fs::File::open(path::Path::new("tests/schema/schema.json"))
        .ok()
        .unwrap()
        .read_to_string(&mut content)
        .ok()
        .unwrap();

    let json_v7_schema: Value = from_str(&content).unwrap();

    println!("test json_schema::test_suite_draft201909");

    visit_specs(
        path::Path::new("tests/schema/JSON-Schema-Test-Suite/tests/draft2019-09"),
        |path, spec_set: Value| {
            let spec_set = spec_set.as_array().unwrap();

            println!(
                "\t{}",
                path.file_name()
                    .unwrap_or_default()
                    .to_str()
                    .unwrap_or_default()
            );

            let exceptions: Vec<(String, String)> = vec![
                (
                    "minLength.json".to_string(),
                    "one supplementary Unicode code point is not long enough".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "remote ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "remote fragment invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "ref within ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "changed scope ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "base URI change ref invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "string is invalid".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "refRemote.json".to_string(),
                    "object is invalid".to_string(),
                ),
                (
                    "bignum.json".to_string(),
                    "a bignum is an integer".to_string(),
                ),
                (
                    "bignum.json".to_string(),
                    "a negative bignum is an integer".to_string(),
                ),
                (
                    "uri-reference.json".to_string(),
                    "an invalid URI Reference".to_string(),
                ),
                (
                    "uri-reference.json".to_string(),
                    "an invalid URI fragment".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 has no support for \\Z anchor from .NET".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "latin-1 non-breaking-space does not match (unlike e.g. Python)".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "latin-1 non-breaking-space matches (unlike e.g. Python)".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "zero-width whitespace matches".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "zero-width whitespace does not match".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #1".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #2".to_string(),
                ),
                (
                    // TODO handle these "empty" edge cases in json-pointer
                    "json-pointer.json".to_string(),
                    "not a valid JSON-pointer (URI Fragment Identifier) #3".to_string(),
                ),
                (
                    // I believe it is trimmed as it is at the beginning, it works when inside.
                    "idn-hostname.json".to_string(),
                    "contains illegal char U+302E Hangul single dot tone mark".to_string(),
                ),
                (
                    // TODO uritemplate needs fixes/changes but the maintainer is inactive.
                    "uri-template.json".to_string(),
                    "an invalid uri-template".to_string(),
                ),
                (
                    // https://github.com/chronotope/chrono/issues/288
                    "time.json".to_string(),
                    "a valid time string".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "ref.json".to_string(),
                    "remote ref invalid".to_string(),
                ),
                (
                    // same as URI
                    "iri-reference.json".to_string(),
                    "an invalid IRI Reference".to_string(),
                ),
                (
                    // same as URI
                    "iri-reference.json".to_string(),
                    "an invalid IRI fragment".to_string(),
                ),
            ];
            let group_exceptions: Vec<(String, String)> = vec![
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 regex escapes control codes with \\c and upper letter".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 regex escapes control codes with \\c and lower letter".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\d matches ascii digits only".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\D matches everything but ascii digits".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\w matches ascii letters only".to_string(),
                ),
                (
                    "ecmascript-regex.json".to_string(),
                    "ECMA 262 \\W matches everything but ascii letters".to_string(),
                ),
                (
                    // TODO json-pointer needs to handle relative JSON pointers
                    "relative-json-pointer.json".to_string(),
                    "validation of Relative JSON Pointers (RJP)".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "defs.json".to_string(),
                    "invalid definition".to_string(),
                ),
                (
                    // TODO implement remote schema download
                    "id.json".to_string(),
                    "Invalid use of fragments in location-independent $id".to_string(),
                ),
                (
                    "idn-hostname.json".to_string(),
                    "validation of internationalized host names".to_string(),
                ),
                (
                    "email.json".to_string(),
                    "validation of e-mail addresses".to_string(),
                ),
                (
                    // optional overflow handling is not implemented
                    "float-overflow.json".to_string(),
                    "all integers are multiples of 0.5, if overflow is handled".to_string(),
                ),
                (
                    // TODO implement duration validation
                    "duration.json".to_string(),
                    "validation of duration strings".to_string(),
                ),
                (
                    // TODO implement UUID validation
                    "uuid.json".to_string(),
                    "uuid format".to_string(),
                ),
            ];

            for spec in spec_set.iter() {
                let spec = spec.as_object().unwrap();
                let mut scope = json_schema::Scope::new().set_version(SchemaVersion::Draft2019_09);

                scope.compile(json_v7_schema.clone(), true).ok().unwrap();

                let spec_desc = spec
                    .get("description")
                    .map(|v| v.as_str().unwrap())
                    .unwrap_or("");
                let spec_exception_found = group_exceptions[..].contains(&(
                    path.file_name().unwrap().to_str().unwrap().to_string(),
                    spec_desc.to_string(),
                ));
                if spec_exception_found {
                    println!("\t\t{spec_desc} .. skipped");
                    continue;
                } else {
                    println!("\t\t{spec_desc}");
                }

                let schema =
                    match scope.compile_and_return(spec.get("schema").unwrap().clone(), false) {
                        Ok(schema) => schema,
                        Err(err) => panic!(
                            "Error in schema {} {}: {:?}",
                            path.file_name().unwrap().to_str().unwrap(),
                            spec.get("description").unwrap().as_str().unwrap(),
                            err
                        ),
                    };

                let tests = spec.get("tests").unwrap().as_array().unwrap();

                for test in tests.iter() {
                    let test = test.as_object().unwrap();
                    let description = test.get("description").unwrap().as_str().unwrap();
                    let data = test.get("data").unwrap();
                    let valid = test.get("valid").unwrap().as_bool().unwrap();

                    let exception_found = exceptions[..].contains(&(
                        path.file_name().unwrap().to_str().unwrap().to_string(),
                        description.to_string(),
                    ));
                    if exception_found {
                        println!("\t\t\t{description} .. skipped");
                        continue;
                    }

                    let state = schema.validate(data);

                    // TODO implement remote schema download for strict validation
                    if state.is_valid() != valid {
                        panic!(
                            "Failure: \"{}\" in \"{}\" -> \"{}\" with state: \n {}",
                            path.file_name().unwrap().to_str().unwrap(),
                            spec_desc,
                            description,
                            to_string_pretty(&to_value(&state).unwrap()).unwrap()
                        )
                    } else {
                        println!("\t\t\t{description} .. ok");
                    }
                }
            }
        },
    )
}
