use super::*;
use crate::diagnostics::Level;
use crate::diagnostics::Message;
use spanned::{Span, Spanned};
use std::path::PathBuf;

fn config() -> Config {
    Config {
        root_dir: PathBuf::from("$RUSTROOT"),
        program: CommandBuilder::cmd("cake"),
        ..Config::dummy()
    }
}

macro_rules! config {
    ($config:ident = $s:expr) => {
        let path = Path::new("moobar");
        let comments = Comments::parse(
            Spanned::new(
                $s.as_bytes(),
                Span {
                    file: path.to_path_buf(),
                    bytes: 0..$s.len(),
                },
            ),
            &$config,
        )
        .unwrap();
        #[allow(unused_mut)]
        let mut $config = TestConfig {
            config: $config,
            comments: Arc::new(comments),
            aux_dir: PathBuf::from("unused_doesnt_exist"),
            status: Box::new(crate::status_emitter::SilentStatus {
                path: path.to_path_buf(),
                revision: String::new(),
            }),
        };
    };
}

macro_rules! line {
    ($thing:expr, $s:expr) => {{
        let file = Spanned::new(
            $s.as_bytes(),
            Span {
                file: PathBuf::new(),
                bytes: 0..$s.len(),
            },
        );
        let pos = file
            .lines()
            .position(|line| line.span.bytes.contains(&$thing.bytes.start))
            .unwrap();
        pos + 1
    }};
}

#[test]
fn issue_2156() {
    let s = r"
use std::mem;

fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address $HEX is unallocated)
}
    ";
    let config = config();
    config!(config = s);
    let mut errors = vec![];
    let messages = vec![
        vec![], vec![], vec![], vec![], vec![],
        vec![
            Message {
                message:"Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: None,
            }
        ]
    ];
    config
        .check_annotations(messages, vec![], &mut errors)
        .unwrap();
    match &errors[..] {
        [Error::PatternNotFound { pattern, .. }, Error::ErrorsWithoutPattern { path, .. }]
            if path.as_ref().is_some_and(|(_p, line)| line.get() == 5)
                && line!(pattern.span, s) == 5 => {}
        _ => panic!("{:#?}", errors),
    }
}

#[test]
fn find_pattern() {
    let s = r"
use std::mem;

fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address 0x10 is unallocated)
}
    ";
    let config = config();
    config!(config = s);
    {
        let messages = vec![vec![], vec![], vec![], vec![], vec![], vec![
                Message {
                    message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                    level: Level::Error,
                    line: None,
                    span: None,
                    code: None,
                }
            ]
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [] => {}
            _ => panic!("{:#?}", errors),
        }
    }

    // only difference to above is a wrong line number
    {
        let messages = vec![vec![], vec![], vec![], vec![], vec![
                Message {
                    message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                    level: Level::Error,
                    line: None,
                    span: None,
                    code: None,
                }
            ]
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [Error::PatternNotFound { pattern, .. }, Error::ErrorsWithoutPattern { path, .. }]
                if path.as_ref().is_some_and(|(_, line)| line.get() == 4)
                    && line!(pattern.span, s) == 5 => {}
            _ => panic!("not the expected error: {:#?}", errors),
        }
    }

    // only difference to first is a wrong level
    {
        let messages = vec![
            vec![], vec![], vec![], vec![], vec![],
            vec![
                Message {
                    message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                    level: Level::Note,
                    line: None,
                    span: None,
                    code: None,
                }
            ]
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            // Note no `ErrorsWithoutPattern`, because there are no `//~NOTE` in the test file, so we ignore them
            [Error::PatternNotFound { pattern, .. }] if line!(pattern.span, s) == 5 => {}
            _ => panic!("not the expected error: {:#?}", errors),
        }
    }
}

#[test]
fn duplicate_pattern() {
    let s = r"
use std::mem;

fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address 0x10 is unallocated)
    //~^ ERROR: encountered a dangling reference (address 0x10 is unallocated)
}
    ";
    let config = config();
    config!(config = s);
    let messages = vec![
        vec![], vec![], vec![], vec![], vec![],
        vec![
            Message {
                message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: None,
            }
        ]
    ];
    let mut errors = vec![];
    config
        .check_annotations(messages, vec![], &mut errors)
        .unwrap();
    match &errors[..] {
        [Error::PatternNotFound { pattern, .. }] if line!(pattern.span, s) == 6 => {}
        _ => panic!("{:#?}", errors),
    }
}

#[test]
fn missing_pattern() {
    let s = r"
use std::mem;

fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address 0x10 is unallocated)
}
    ";
    let config = config();
    config!(config = s);
    let messages = vec![
        vec![], vec![], vec![], vec![], vec![],
        vec![
            Message {
                message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                    line: None,
                    span: None,
                code: None,
            },
            Message {
                message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                    line: None,
                    span: None,
                code: None,
            }
        ]
    ];
    let mut errors = vec![];
    config
        .check_annotations(messages, vec![], &mut errors)
        .unwrap();
    match &errors[..] {
        [Error::ErrorsWithoutPattern { path, .. }]
            if path.as_ref().is_some_and(|(_, line)| line.get() == 5) => {}
        _ => panic!("{:#?}", errors),
    }
}

#[test]
fn missing_warn_pattern() {
    let s = r"
use std::mem;

fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address 0x10 is unallocated)
    //~^ WARN: cake
}
    ";
    let config = config();
    config!(config = s);
    let messages= vec![
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![
            Message {
                message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                    line: None,
                    span: None,
                code: None,
            },
            Message {
                message: "kaboom".to_string(),
                level: Level::Warn,
                    line: None,
                    span: None,
                code: None,
            },
            Message {
                message: "cake".to_string(),
                level: Level::Warn,
                    line: None,
                    span: None,
                code: None,
            },
        ],
    ];
    let mut errors = vec![];
    config
        .check_annotations(messages, vec![], &mut errors)
        .unwrap();
    match &errors[..] {
        [Error::ErrorsWithoutPattern { path, msgs, .. }]
            if path.as_ref().is_some_and(|(_, line)| line.get() == 5) =>
        {
            match &msgs[..] {
                [Message {
                    message,
                    level: Level::Warn,
                    line: _,
                    span: _,
                    code: None,
                }] if message == "kaboom" => {}
                _ => panic!("{:#?}", msgs),
            }
        }
        _ => panic!("{:#?}", errors),
    }
}

#[test]
fn missing_implicit_warn_pattern() {
    let s = r"
use std::mem;
//@require-annotations-for-level: ERROR
fn main() {
    let _x: &i32 = unsafe { mem::transmute(16usize) }; //~ ERROR: encountered a dangling reference (address 0x10 is unallocated)
    //~^ WARN: cake
}
    ";
    let config = config();
    config!(config = s);
    let messages = vec![
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![
            Message {
                message: "Undefined Behavior: type validation failed: encountered a dangling reference (address 0x10 is unallocated)".to_string(),
                level: Level::Error,
                    line: None,
                    span: None,
                code: None,
            },
            Message {
                message: "kaboom".to_string(),
                level: Level::Warn,
                    line: None,
                    span: None,
                code: None,
            },
            Message {
                message: "cake".to_string(),
                level: Level::Warn,
                    line: None,
                    span: None,
                code: None,
            },
        ],
    ];
    let mut errors = vec![];
    config
        .check_annotations(messages, vec![], &mut errors)
        .unwrap();
    match &errors[..] {
        [] => {}
        _ => panic!("{:#?}", errors),
    }
}

#[test]
fn find_code() {
    let s = r"
fn main() {
    let _x: i32 = 0u32; //~ E0308
}
    ";
    let config = config();
    config!(config = s);
    {
        let messages = vec![
            vec![],
            vec![],
            vec![],
            vec![Message {
                message: "mismatched types".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: Some("E0308".into()),
            }],
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [] => {}
            _ => panic!("{:#?}", errors),
        }
    }

    // different error code
    {
        let messages = vec![
            vec![],
            vec![],
            vec![],
            vec![Message {
                message: "mismatched types".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: Some("SomeError".into()),
            }],
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [Error::CodeNotFound { code, .. }, Error::ErrorsWithoutPattern { msgs, .. }]
                if **code == "E0308" && line!(code.span, s) == 3 && msgs.len() == 1 => {}
            _ => panic!("{:#?}", errors),
        }
    }

    // warning instead of error
    {
        let messages = vec![
            vec![],
            vec![],
            vec![],
            vec![Message {
                message: "mismatched types".to_string(),
                level: Level::Warn,
                line: None,
                span: None,
                code: Some("E0308".into()),
            }],
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [Error::CodeNotFound { code, .. }] if **code == "E0308" && line!(code.span, s) == 3 => {
            }
            _ => panic!("{:#?}", errors),
        }
    }
}

#[test]
fn find_code_with_prefix() {
    let s = r"
fn main() {
    let _x: i32 = 0u32; //~ E0308
}
    ";
    let mut config = config();
    config.comment_defaults.base().diagnostic_code_prefix =
        Spanned::dummy("prefix::".to_string()).into();
    config!(config = s);
    {
        let messages = vec![
            vec![],
            vec![],
            vec![],
            vec![Message {
                message: "mismatched types".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: Some("prefix::E0308".into()),
            }],
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [] => {}
            _ => panic!("{:#?}", errors),
        }
    }

    // missing prefix
    {
        let messages = vec![
            vec![],
            vec![],
            vec![],
            vec![Message {
                message: "mismatched types".to_string(),
                level: Level::Error,
                line: None,
                span: None,
                code: Some("E0308".into()),
            }],
        ];
        let mut errors = vec![];
        config
            .check_annotations(messages, vec![], &mut errors)
            .unwrap();
        match &errors[..] {
            [Error::CodeNotFound { code, .. }, Error::ErrorsWithoutPattern { msgs, .. }]
                if **code == "prefix::E0308" && line!(code.span, s) == 3 && msgs.len() == 1 => {}
            _ => panic!("{:#?}", errors),
        }
    }
}
