// SPDX-License-Identifier: Apache-2.0 OR MIT

// TODO: this may no longer needed since regex 1.9.

use std::mem;

use anyhow::Result;
use regex::Regex;

pub(crate) struct RegexVecBuilder {
    filled: Vec<String>,
    current: String,
    first: bool,
    num_pats: usize,
    leading: &'static str,
    trailing: &'static str,
}

impl RegexVecBuilder {
    const LIMIT: usize = 4096;

    pub(crate) fn new(leading: &'static str, trailing: &'static str) -> Self {
        let mut current = String::with_capacity(256);
        current.push_str(leading);
        Self { filled: Vec::with_capacity(1), current, first: true, num_pats: 0, leading, trailing }
    }

    pub(crate) fn or(&mut self, pat: &str) {
        let len = pat.len() / usize::BITS as usize + 1;
        self.num_pats += len;
        if self.num_pats > Self::LIMIT && self.num_pats != len {
            self.current.push_str(self.trailing);
            self.filled.push(mem::replace(&mut self.current, String::with_capacity(256)));
            self.current.push_str(self.leading);
            self.first = true;
            self.num_pats = len;
        }
        if self.first {
            debug_assert_eq!(self.current, self.leading);
            self.first = false;
        } else {
            self.current.push('|');
        }
        self.current.push_str(pat);
    }

    pub(crate) fn build(mut self) -> Result<RegexVec> {
        debug_assert_ne!(self.current.len(), 0);
        if self.current != self.leading {
            self.current.push_str(self.trailing);
            self.filled.push(mem::take(&mut self.current));
        }
        let mut v = Vec::with_capacity(self.filled.len());
        for re in &self.filled {
            v.push(Regex::new(re)?);
        }
        Ok(RegexVec(v))
    }
}

pub(crate) struct RegexVec(Vec<Regex>);

impl RegexVec {
    pub(crate) fn is_match(&self, text: &str) -> bool {
        for re in &self.0 {
            if re.is_match(text) {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn smoke() {
        let mut re = RegexVecBuilder::new("^(", ")$");
        re.or(&"a".repeat(64 * 4100));
        assert!(re.filled.is_empty());
        let re = re.build().unwrap();
        assert_eq!(re.0.len(), 1);

        let mut re = RegexVecBuilder::new("^(", ")$");
        while re.filled.is_empty() {
            re.or("a");
        }
        re.or("b");
        re.or("c");
        assert_eq!(re.filled.len(), 1);
        let re = re.build().unwrap();
        assert_eq!(re.0.len(), 2);
        assert!(re.is_match("a"));
        assert!(!re.is_match("aa"));
        assert!(re.is_match("b"));
        assert!(!re.is_match("bb"));
        assert!(re.is_match("c"));
        assert!(!re.is_match("cc"));
        assert!(!re.is_match("d"));
    }

    fn gen_pkg_names(num_pkg: usize, pkg_name_size: usize) -> Vec<String> {
        (0..num_pkg)
            .map(|n| ('a'..='z').cycle().skip(n).take(pkg_name_size).collect())
            .collect::<Vec<_>>()
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn regex_pkg_hash_re_size_limit() {
        fn pkg_hash_re(pkg_names: &[String]) -> Result<Regex, regex::Error> {
            let mut re = String::from("^(lib)?(");
            let mut first = true;
            for name in pkg_names {
                if first {
                    first = false;
                } else {
                    re.push('|');
                }
                re.push_str(&name.replace('-', "(-|_)"));
            }
            re.push_str(")(-[0-9a-f]{7,})?$");
            Regex::new(&re)
        }

        let names = gen_pkg_names(12000, 64);
        pkg_hash_re(&names).unwrap();

        let names = gen_pkg_names(6000, 128);
        pkg_hash_re(&names).unwrap();

        let names = gen_pkg_names(3000, 256);
        pkg_hash_re(&names).unwrap();
    }

    fn pkg_hash_re_builder(pkg_names: &[String]) -> RegexVecBuilder {
        let mut re = RegexVecBuilder::new("^(lib)?(", ")(-[0-9a-f]{7,})?$");
        for name in pkg_names {
            re.or(&name.replace('-', "(-|_)"));
        }
        re
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn regex_vec_pkg_hash_re_size_limit() {
        let names = gen_pkg_names(12000, 64);
        pkg_hash_re_builder(&names).build().unwrap();

        let names = gen_pkg_names(6000, 128);
        pkg_hash_re_builder(&names).build().unwrap();

        let names = gen_pkg_names(3000, 256);
        pkg_hash_re_builder(&names).build().unwrap();
    }
}
