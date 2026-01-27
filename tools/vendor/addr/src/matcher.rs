use crate::error::{Kind, Result};

const MAX_DOMAIN_LEN: usize = 253;
const MAX_LABELS_COUNT: usize = 127;
const MAX_LABEL_LEN: usize = 63;

/// Check if a domain has valid syntax
// https://en.wikipedia.org/wiki/Domain_name#Domain_name_syntax
// http://blog.sacaluta.com/2011/12/dns-domain-names-253-or-255-bytesoctets.html
// https://blogs.msdn.microsoft.com/oldnewthing/20120412-00/?p=7873/
#[inline]
pub(crate) fn is_domain_name(domain: &str) -> Result<()> {
    // check total lengths
    if domain.chars().count() > MAX_DOMAIN_LEN {
        return Err(Kind::NameTooLong);
    }

    let dot_count = domain.matches('.').count();

    if dot_count + 1 > MAX_LABELS_COUNT {
        return Err(Kind::TooManyLabels);
    }

    for (i, label) in domain.split('.').enumerate() {
        is_label(label, i == dot_count)?;
    }

    Ok(())
}

pub(crate) fn is_label(label: &str, label_is_tld: bool) -> Result<()> {
    if label.is_empty() {
        return Err(Kind::EmptyLabel);
    }

    if label.chars().count() > MAX_LABEL_LEN {
        return Err(Kind::LabelTooLong);
    }

    if label_is_tld && is_num(label) {
        return Err(Kind::NumericTld);
    }

    if label.starts_with(|c: char| c.is_ascii() && !c.is_alphanumeric()) {
        return Err(Kind::LabelStartNotAlnum);
    }

    if label.ends_with(|c: char| c.is_ascii() && !c.is_alphanumeric()) {
        return Err(Kind::LabelEndNotAlnum);
    }

    if label.contains(|c: char| c != '-' && c.is_ascii() && !c.is_alphanumeric()) {
        return Err(Kind::IllegalCharacter);
    }

    Ok(())
}

pub(crate) fn is_num(label: &str) -> bool {
    label.parse::<f64>().is_ok()
}

// https://tools.ietf.org/html/rfc2181#section-11
#[inline]
pub(crate) fn is_dns_name(name: &str) -> Result<()> {
    if name.is_empty() {
        return Err(Kind::EmptyName);
    }

    if name.contains("..") {
        return Err(Kind::EmptyLabel);
    }

    let domain = if name.ends_with('.') {
        name.get(..name.len() - 1).unwrap_or_default()
    } else {
        name
    };

    // check total lengths
    if domain.len() > MAX_DOMAIN_LEN {
        return Err(Kind::NameTooLong);
    }

    for label in domain.split('.') {
        if label.len() > MAX_LABEL_LEN {
            return Err(Kind::LabelTooLong);
        }
    }

    Ok(())
}

pub(crate) fn is_email_local(local: &str) -> Result<()> {
    let mut chars = local.chars();

    let first = chars.next().ok_or(Kind::NoUserPart)?;

    let last_index = chars.clone().count().max(1) - 1;

    if last_index > MAX_LABEL_LEN {
        return Err(Kind::EmailLocalTooLong);
    }

    if first == '"' {
        // quoted
        if last_index == 0 {
            return Err(Kind::QuoteUnclosed);
        }
        for (index, c) in chars.enumerate() {
            if index == last_index {
                if c != '"' {
                    return Err(Kind::QuoteUnclosed);
                }
            } else if !is_combined(c) && !is_quoted(c) {
                return Err(Kind::IllegalCharacter);
            }
        }
    } else {
        // not quoted
        if first == ' ' || first == '.' || local.contains("..") {
            return Err(Kind::IllegalCharacter);
        }
        for (index, c) in chars.enumerate() {
            if !is_combined(c) && (index == last_index || c != '.') {
                return Err(Kind::IllegalCharacter);
            }
        }
    }

    Ok(())
}

// these characters can be anywhere in the expresion
// [[:alnum:]!#$%&'*+/=?^_`{|}~-]
fn is_global(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '-'
        || c == '!'
        || c == '#'
        || c == '$'
        || c == '%'
        || c == '&'
        || c == '\''
        || c == '*'
        || c == '+'
        || c == '/'
        || c == '='
        || c == '?'
        || c == '^'
        || c == '_'
        || c == '`'
        || c == '{'
        || c == '|'
        || c == '}'
        || c == '~'
}

fn is_non_ascii(c: char) -> bool {
    c as u32 > 0x7f // non-ascii characters (can also be unquoted)
}

fn is_quoted(c: char) -> bool {
    // ["(),\\:;<>@\[\]. ]
    c == '"'
        || c == '.'
        || c == ' '
        || c == '('
        || c == ')'
        || c == ','
        || c == '\\'
        || c == ':'
        || c == ';'
        || c == '<'
        || c == '>'
        || c == '@'
        || c == '['
        || c == ']'
}

fn is_combined(c: char) -> bool {
    is_global(c) || is_non_ascii(c)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_label_domain() {
        assert!(is_domain_name("xn--example").is_ok());
    }

    #[test]
    fn plain_domain() {
        assert!(is_domain_name("example.com").is_ok());
    }

    #[test]
    fn subdomains() {
        assert!(is_domain_name("a.b.c.d.e.f").is_ok());
    }
}
