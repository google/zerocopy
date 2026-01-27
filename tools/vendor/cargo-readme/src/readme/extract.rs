//! Extract raw doc comments from rust source code

use std::io::{self, BufRead, BufReader, Read};

/// Read the given `Read`er and return a `Vec` of the rustdoc lines found
pub fn extract_docs<R: Read>(reader: R) -> io::Result<Vec<String>> {
    let mut reader = BufReader::new(reader);
    let mut line = String::new();

    while reader.read_line(&mut line)? > 0 {
        if line.starts_with("//!") {
            return extract_docs_singleline_style(line, reader);
        }

        if line.starts_with("/*!") {
            return extract_docs_multiline_style(line, reader);
        }

        line.clear();
    }

    Ok(Vec::new())
}

fn extract_docs_singleline_style<R: Read>(
    first_line: String,
    reader: BufReader<R>,
) -> io::Result<Vec<String>> {
    let mut result = vec![normalize_line(first_line)];

    for line in reader.lines() {
        let line = line?;

        if line.starts_with("//!") {
            result.push(normalize_line(line));
        } else if line.trim().len() > 0 {
            // doc ends, code starts
            break;
        }
    }

    Ok(result)
}

fn extract_docs_multiline_style<R: Read>(
    first_line: String,
    reader: BufReader<R>,
) -> io::Result<Vec<String>> {
    let mut result = Vec::new();
    if first_line.starts_with("/*!") && first_line.trim().len() > "/*!".len() {
        result.push(normalize_line(first_line));
    }

    let mut nesting: isize = 0;

    for line in reader.lines() {
        let line = line?;
        nesting += line.matches("/*").count() as isize;

        if let Some(pos) = line.rfind("*/") {
            nesting -= line.matches("*/").count() as isize;
            if nesting < 0 {
                let mut line = line;
                let _ = line.split_off(pos);
                if !line.trim().is_empty() {
                    result.push(line);
                }
                break;
            }
        }

        result.push(line.trim_end().to_owned());
    }

    Ok(result)
}

/// Strip the "//!" or "/*!" from a line and a single whitespace
fn normalize_line(mut line: String) -> String {
    if line.trim() == "//!" || line.trim() == "/*!" {
        line.clear();
        line
    } else {
        // if the first character after the comment mark is " ", remove it
        let split_at = if line.find(" ") == Some(3) { 4 } else { 3 };
        line.split_at(split_at).1.trim_end().to_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    const EXPECTED: &[&str] = &[
        "first line",
        "",
        "```",
        "let rust_code = \"safe\";",
        "```",
        "",
        "```C",
        "int i = 0; // no rust code",
        "```",
    ];

    const INPUT_SINGLELINE: &str = "\
                                    //! first line \n\
                                    //! \n\
                                    //! ``` \n\
                                    //! let rust_code = \"safe\"; \n\
                                    //! ``` \n\
                                    //! \n\
                                    //! ```C \n\
                                    //! int i = 0; // no rust code \n\
                                    //! ``` \n\
                                    use std::any::Any; \n\
                                    fn main() {}";

    #[test]
    fn extract_docs_singleline_style() {
        let reader = Cursor::new(INPUT_SINGLELINE.as_bytes());
        let result = extract_docs(reader).unwrap();
        assert_eq!(result, EXPECTED);
    }

    const INPUT_MULTILINE: &str = "\
                                   /*! \n\
                                   first line \n\
                                   \n\
                                   ``` \n\
                                   let rust_code = \"safe\"; \n\
                                   ``` \n\
                                   \n\
                                   ```C \n\
                                   int i = 0; // no rust code \n\
                                   ``` \n\
                                   */ \n\
                                   use std::any::Any; \n\
                                   fn main() {}";

    #[test]
    fn extract_docs_multiline_style() {
        let reader = Cursor::new(INPUT_MULTILINE.as_bytes());
        let result = extract_docs(reader).unwrap();
        assert_eq!(result, EXPECTED);
    }

    const INPUT_MIXED_SINGLELINE: &str = "\
                                          //! singleline \n\
                                          /*! \n\
                                          multiline \n\
                                          */";

    #[test]
    fn extract_docs_mix_styles_singleline() {
        let input = Cursor::new(INPUT_MIXED_SINGLELINE.as_bytes());
        let expected = "singleline";
        let result = extract_docs(input).unwrap();
        assert_eq!(result, &[expected])
    }

    const INPUT_MIXED_MULTILINE: &str = "\
                                         /*! \n\
                                         multiline \n\
                                         */ \n\
                                         //! singleline";

    #[test]
    fn extract_docs_mix_styles_multiline() {
        let input = Cursor::new(INPUT_MIXED_MULTILINE.as_bytes());
        let expected = "multiline";
        let result = extract_docs(input).unwrap();
        assert_eq!(result, &[expected]);
    }

    const INPUT_MULTILINE_NESTED_1: &str = "\
                                            /*! \n\
                                            level 0 \n\
                                            /* \n\
                                            level 1 \n\
                                            */ \n\
                                            level 0 \n\
                                            */ \n\
                                            fn main() {}";

    const EXPECTED_MULTILINE_NESTED_1: &[&str] = &["level 0", "/*", "level 1", "*/", "level 0"];

    #[test]
    fn extract_docs_nested_level_1() {
        let input = Cursor::new(INPUT_MULTILINE_NESTED_1.as_bytes());
        let result = extract_docs(input).unwrap();
        assert_eq!(result, EXPECTED_MULTILINE_NESTED_1);
    }

    const INPUT_MULTILINE_NESTED_2: &str = "\
                                            /*! \n\
                                            level 0 \n\
                                            /* \n\
                                            level 1 \n\
                                            /* \n\
                                            level 2 \n\
                                            */ \n\
                                            level 1 \n\
                                            */ \n\
                                            level 0 \n\
                                            */ \n\
                                            fn main() {}";

    const EXPECTED_MULTILINE_NESTED_2: &[&str] = &[
        "level 0", "/*", "level 1", "/*", "level 2", "*/", "level 1", "*/", "level 0",
    ];

    #[test]
    fn extract_docs_nested_level_2() {
        let input = Cursor::new(INPUT_MULTILINE_NESTED_2.as_bytes());
        let result = extract_docs(input).unwrap();
        assert_eq!(result, EXPECTED_MULTILINE_NESTED_2);
    }
}
