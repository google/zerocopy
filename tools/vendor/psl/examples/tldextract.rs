use psl_types::List;

pub trait TldExtract {
    fn extract<'a>(&self, host: &'a str) -> Option<Parts<'a>>;
}

impl<T: List> TldExtract for T {
    fn extract<'a>(&self, host: &'a str) -> Option<Parts<'a>> {
        let host_len = host.len();
        let suffix_len = self.suffix(host.as_bytes())?.as_bytes().len();
        let suffix = {
            let offset = host_len - suffix_len;
            &host[offset..]
        };
        let suffix_plus_dot = suffix_len + 1;
        let (subdomain, domain) = if host_len > suffix_plus_dot {
            match host.get(..host_len - suffix_plus_dot) {
                Some(prefix) => match prefix.rfind('.') {
                    Some(offset) => (prefix.get(..offset), prefix.get(offset + 1..)),
                    None => (None, Some(prefix)),
                },
                None => (None, None),
            }
        } else {
            (None, None)
        };
        Some(Parts {
            suffix,
            domain,
            subdomain,
        })
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Parts<'a> {
    pub suffix: &'a str,
    pub domain: Option<&'a str>,
    pub subdomain: Option<&'a str>,
}

// This example is inspired by https://github.com/john-kurkowski/tldextract
// Unlike that project, we don't try to parse URLs though. That can easily
// be done by using the `url` crate and feeding the output of `Url::domain`
// to `TldExtract::extract`.
fn main() {
    use psl::List;
    use std::env;

    let domain = match env::args().nth(1) {
        Some(name) => name,
        None => {
            eprintln!("Usage: {} <domain name>", env::args().nth(0).unwrap());
            std::process::exit(1);
        }
    };

    match List.extract(&domain) {
        Some(info) => println!(
            "{} {} {}",
            info.subdomain.unwrap_or("(None)"),
            info.domain.unwrap_or("(None)"),
            info.suffix
        ),
        None => eprintln!("`{}` is not domain name", domain),
    }
}
