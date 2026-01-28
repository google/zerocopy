# Robust and fast domain name parsing

[![CI](https://github.com/addr-rs/addr/actions/workflows/ci.yml/badge.svg)](https://github.com/addr-rs/addr/actions/workflows/ci.yml) [![Latest Version](https://img.shields.io/crates/v/addr.svg)](https://crates.io/crates/addr) [![Docs](https://docs.rs/addr/badge.svg)](https://docs.rs/addr)

This library uses Mozilla's [Public Suffix List](https://publicsuffix.org) to reliably parse domain names in [Rust](https://www.rust-lang.org). It will reliably check if a domain has valid syntax. It also checks the length restrictions for each label, total number of labels and full length of domain name.

## Examples

```rust
use addr::{parse_domain_name, parse_dns_name};

// You can find out the root domain
// or extension of any given domain name
let domain = parse_domain_name("www.example.com")?;
assert_eq!(domain.root(), Some("example.com"));
assert_eq!(domain.suffix(), "com");
assert_eq!(domain.prefix(), Some("www"));

let domain = parse_domain_name("www.食狮.中国")?;
assert_eq!(domain.root(), Some("食狮.中国"));
assert_eq!(domain.suffix(), "中国");

let domain = parse_domain_name("www.xn--85x722f.xn--55qx5d.cn")?;
assert_eq!(domain.root(), Some("xn--85x722f.xn--55qx5d.cn"));
assert_eq!(domain.suffix(), "xn--55qx5d.cn");

let domain = parse_domain_name("a.b.example.uk.com")?;
assert_eq!(domain.root(), Some("example.uk.com"));
assert_eq!(domain.suffix(), "uk.com");

let name = parse_dns_name("_tcp.example.com.")?;
assert_eq!(name.suffix(), Some("com."));

// In any case if the domain's suffix is in the list
// then this is definately a registrable domain name
assert!(domain.has_known_suffix());
```

## TODO

[Strict internationalized domain names (IDN) validation](https://github.com/addr-rs/addr/issues/13) (use the `idna` feature flag)

## Use Cases

For those who work with domain names the use cases of this library are plenty. [publicsuffix.org/learn](https://publicsuffix.org/learn/) lists quite a few. For the sake of brevity, I'm not going to repeat them here. I work for a domain registrar so we make good use of this library. Here are some of the ways this library can be used:

* Validating domain names. This one is probably obvious. If a `domain.has_known_suffix()` you can be absolutely sure this is a valid domain name. A regular expression is simply not robust enough.
* Blacklisting or whitelisting domain names. You can't just blindly do this without knowing the actual registrable domain name otherwise you risk being too restrictive or too lenient. Bad news either way...
* Extracting the registrable part of a domain name so you can check whether the domain is registered or not.
* Storing details about a domain name in a DBMS using the registrable part of a domain name as the primary key.
