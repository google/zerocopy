#[cfg(feature = "idna")]
use rspec::report::ExampleResult;
#[cfg(feature = "idna")]
use serde::Deserialize;

#[cfg(feature = "idna")]
#[derive(Debug, Deserialize)]
struct JsonSchemaTestSuite {
    description: String,
    schema: Format,
    tests: Vec<Test>,
}

#[cfg(feature = "idna")]
#[derive(Debug, Deserialize)]
struct Format {
    format: String,
}

#[cfg(feature = "idna")]
#[derive(Debug, Deserialize)]
struct Test {
    description: String,
    data: String,
    valid: bool,
}

#[test]
fn addr_parsing() {
    rspec::run(&rspec::given("a domain", (), |ctx| {
        ctx.it("should allow non-fully qualified domain names", |_| {
            assert!(addr::parse_domain_name("example.com").is_ok())
        });

        ctx.it("should allow fully qualified domain names", |_| {
            assert!(addr::parse_domain_name("example.com.").is_ok())
        });

        ctx.it("should allow sub-domains", |_| {
            let domain = addr::parse_domain_name("www.example.com.").unwrap();
            assert_eq!(domain.suffix(), "com.");
            assert_eq!(domain.root(), Some("example.com."));
            assert_eq!(domain.prefix(), Some("www"));
        });

        ctx.it("should allow IDNs", |_| {
            assert!(addr::parse_domain_name("københavn.eu").is_ok())
        });

        ctx.it("should not allow more than 1 trailing dot", |_| {
            assert!(addr::parse_domain_name("example.com..").is_err());
        });

        ctx.it("should allow single-label domains", |_| {
            let domains = vec![
                // real TLDs
                "com",
                "saarland",
                "museum.",
                // non-existant TLDs
                "localhost",
                "madeup",
                "with-dot.",
                "y̆es",
                "y̆",
                "❤",
            ];
            for domain in domains {
                let name = addr::parse_domain_name(domain).unwrap();
                assert_eq!(name.root(), None);
                assert_eq!(name.suffix(), domain);

                let name = addr::parse_dns_name(domain).unwrap();
                assert_eq!(name.root(), None);
                assert_eq!(name.suffix(), Some(domain));
            }
        });

        ctx.it(
            "should not have the same result with or without the trailing dot",
            |_| {
                assert_ne!(
                    addr::parse_domain_name("example.com.").unwrap(),
                    addr::parse_domain_name("example.com").unwrap()
                );
            },
        );

        ctx.it("should not have empty labels", |_| {
            assert!(addr::parse_domain_name("exa..mple.com").is_err());
        });

        ctx.it("should not contain spaces", |_| {
            assert!(addr::parse_domain_name("exa mple.com").is_err());
        });

        ctx.it("should not start with a dash", |_| {
            assert!(addr::parse_domain_name("-example.com").is_err());
        });

        ctx.it("should not end with a dash", |_| {
            assert!(addr::parse_domain_name("example-.com").is_err());
        });

        ctx.it("should not contain /", |_| {
            assert!(addr::parse_domain_name("exa/mple.com").is_err());
        });

        ctx.it("should not have a label > 63 characters", |_| {
            let mut too_long_domain = String::from("a");
            for _ in 0..64 {
                too_long_domain.push_str("a");
            }
            too_long_domain.push_str(".com");
            assert!(addr::parse_domain_name(too_long_domain.as_str()).is_err());
        });

        ctx.it("should not be an IPv4 address", |_| {
            assert!(addr::parse_domain_name("127.38.53.247").is_err());
        });

        ctx.it("should not be an IPv6 address", |_| {
            assert!(addr::parse_domain_name("fd79:cdcb:38cc:9dd:f686:e06d:32f3:c123").is_err());
        });

        ctx.it(
            "should allow numbers only labels that are not the tld",
            |_| {
                assert!(addr::parse_domain_name("127.com").is_ok());
            },
        );

        ctx.it("should not allow number only tlds", |_| {
            assert!(addr::parse_domain_name("example.127").is_err());
        });

        ctx.it("should not have more than 127 labels", |_| {
            let mut too_many_labels_domain = String::from("a");
            for _ in 0..126 {
                too_many_labels_domain.push_str(".a");
            }
            too_many_labels_domain.push_str(".com");
            assert!(addr::parse_domain_name(too_many_labels_domain.as_str()).is_err());
        });

        ctx.it("should not have more than 253 characters", |_| {
            let mut too_many_chars_domain = String::from("aaaaa");
            for _ in 0..50 {
                too_many_chars_domain.push_str(".aaaaaa");
            }
            too_many_chars_domain.push_str(".com");
            assert!(addr::parse_domain_name(too_many_chars_domain.as_str()).is_err());
        });

        ctx.it("should handle lifetimes correctly", |_| {
            let input = "sub.example.com";
            let root_domain = addr::parse_domain_name(input).unwrap().root().unwrap();
            assert_eq!(root_domain, "example.com");
        });
    }));

    #[cfg(all(feature = "idna", feature = "psl"))]
    rspec::run(&rspec::given("the JSON schema test suite", (), |ctx| {
        // The JSON schema test suite is downloaded from
        // https://raw.githubusercontent.com/json-schema-org/JSON-Schema-Test-Suite/master/tests/draft7/optional/format/idn-hostname.json
        let suites: Vec<JsonSchemaTestSuite> =
            serde_json::from_slice(include_bytes!("idn-hostname.json")).unwrap();
        for suite in suites {
            // we only care about IDNs
            if suite.schema.format == "idn-hostname" {
                for Test {
                    valid,
                    description,
                    data,
                } in suite.tests
                {
                    let label = format!(
                        "{} {}",
                        if valid {
                            "validates"
                        } else {
                            "doesn't validate"
                        },
                        description
                    );
                    ctx.it(msg(label), move |_| {
                        if parse_domain_name(&data).is_ok() == valid {
                            ExampleResult::Success
                        } else {
                            let msg = format!(
                                "failed the test; `{}` {}",
                                data,
                                if valid {
                                    "should be valid"
                                } else {
                                    "shouldn't be valid"
                                }
                            );
                            ExampleResult::Failure(Some(msg))
                        }
                    });
                }
            }
        }
    }));

    rspec::run(&rspec::given("a DNS name", (), |ctx| {
        ctx.it("should allow extended characters", |_| {
            let names = vec![
                "example.com.",
                "_tcp.example.com.",
                "_telnet._tcp.example.com.",
                "*.example.com.",
                "!.example.com.",
                "Elgato Ring Light A4EE",
                "fc:fc:f2:a1:e1:51@fe80::ee2c:e2ff:fea1:e151",
            ];
            for name in names {
                assert!(addr::parse_dns_name(name).is_ok());
            }
        });

        ctx.it(
            "should allow extracting the correct root and suffix where possible",
            |_| {
                let names = vec![
                    ("_tcp.example.com.", Some("example.com."), Some("com.")),
                    (
                        "_telnet._tcp.example.com.",
                        Some("example.com."),
                        Some("com."),
                    ),
                    ("example.com", Some("example.com"), Some("com")),
                    ("example.com.com", Some("com.com"), Some("com")),
                ];
                for (input, root, suffix) in names {
                    let name = addr::parse_dns_name(input).unwrap();
                    assert_eq!(name.root(), root);
                    assert_eq!(name.suffix(), suffix);
                }
            },
        );

        ctx.it("should not require a valid root domain", |_| {
            let names = vec!["_tcp.com.", "_telnet._tcp.com.", "*.com.", "ex!mple.com."];
            for name in names {
                assert!(addr::parse_dns_name(name).is_ok());
            }
        });

        ctx.it("should not allow more than 1 trailing dot", |_| {
            assert!(addr::parse_dns_name("example.com..").is_err());
        });
    }));

    rspec::run(&rspec::given("a parsed email", (), |ctx| {
        ctx.it("should allow valid email addresses", |_| {
            let emails = vec![
                "prettyandsimple@example.com",
                "prettyandsimple@1example.com",
                "very.common@example.com",
                "disposable.style.email.with+symbol@example.com",
                "other.email-with-dash@example.com",
                "x@example.com",
                "example-indeed@strange-example.com",
                "#!$%&'*+-/=?^_`{}|~@example.org",
                "example@s.solutions",
                #[cfg(any(feature = "net", feature = "std"))]
                "user@[fd79:cdcb:38cc:9dd:f686:e06d:32f3:c123]",
                #[cfg(any(feature = "net", feature = "std"))]
                "user@[127.0.0.1]",
                r#""Abc\@def"@example.com"#,
                r#""Fred Bloggs"@example.com"#,
                r#""Joe\\Blow"@example.com"#,
                r#""Abc@def"@example.com"#,
                r#"customer/department=shipping@example.com"#,
                "$A12345@example.com",
                "!def!xyz%abc@example.com",
                "_somename@example.com",
            ];
            for email in emails {
                assert_eq!(addr::parse_email_address(email).unwrap().as_str(), email);
            }
        });

        ctx.it("should reject invalid email addresses", |_| {
            let emails = vec![
                "Abc.example.com",
                "A@b@c@example.com",
                r#"a"b(c)d,e:f;g<h>i[j\k]l@example.com"#,
                r#""just"not"right@example.com"#,
                r#"this is"not\allowed@example.com"#,
                r#"this\ still\"not\\allowed@example.com"#,
                "1234567890123456789012345678901234567890123456789012345678901234+x@example.com",
                "john..doe@example.com",
                "john.doe@example..com",
                " prettyandsimple@example.com",
                "prettyandsimple@example.com ",
                "@example.com",
            ];
            for email in emails {
                assert!(addr::parse_email_address(email).is_err(), "{}", email);
            }
        });

        ctx.it("should allow parsing IDN email addresses", |_| {
            let emails = vec![
                r#"Pelé@example.com"#,
                r#"δοκιμή@παράδειγμα.δοκιμή"#,
                r#"我買@屋企.香港"#,
                r#"甲斐@黒川.日本"#,
                r#"二ノ宮@黒川.日本"#,
                r#"чебурашка@ящик-с-апельсинами.рф"#,
                r#"медведь@с-балалайкой.рф"#,
                r#"संपर्क@डाटामेल.भारत"#,
                r#"用户@例子.广告"#,
            ];
            for email in emails {
                assert!(addr::parse_email_address(email).is_ok(), "{}", email);
            }
        });
    }));
}

// Converts a String to &'static str
//
// This will leak memory but that's OK for our testing purposes
#[cfg(feature = "idna")]
fn msg(s: String) -> &'static str {
    unsafe {
        let ret = std::mem::transmute(&s as &str);
        std::mem::forget(s);
        ret
    }
}
