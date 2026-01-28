use addr::parser::{DnsName, DomainName, EmailAddress};
use criterion::{criterion_group, criterion_main, Criterion};
use psl_types::List as Psl;
use publicsuffix::List;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

lazy_static::lazy_static! {
    static ref LIST: List = {
        let root = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let path = Path::new(&root)
            .join("tests")
            .join("public_suffix_list.dat");
        let mut file = File::open(path).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        contents.parse().unwrap()
    };
}

fn psl(c: &mut Criterion) {
    c.bench_function("psl::List::suffix", |b| {
        use psl::List;

        b.iter(|| {
            List.suffix(b"example.com").unwrap();
        })
    });

    c.bench_function("psl::List::domain", |b| {
        use psl::List;

        b.iter(|| {
            List.domain(b"example.com").unwrap();
        })
    });

    c.bench_function("publicsuffix::List::suffix", |b| {
        b.iter(|| {
            LIST.suffix(b"example.com").unwrap();
        })
    });

    c.bench_function("publicsuffix::List::domain", |b| {
        b.iter(|| {
            LIST.domain(b"example.com").unwrap();
        })
    });

    c.bench_function("addr::parser::DomainName", |b| {
        use psl::List;

        b.iter(|| {
            List.parse_domain_name("example.com").unwrap();
        })
    });

    c.bench_function("addr::parser::DnsName", |b| {
        use psl::List;

        b.iter(|| {
            List.parse_dns_name("_example.com").unwrap();
        })
    });

    c.bench_function("addr::email::Address::parse", |b| {
        use psl::List;

        b.iter(|| {
            List.parse_email_address("john.doe@example.com").unwrap();
        })
    });
}

criterion_group!(benches, psl);
criterion_main!(benches);
