//! `rust-uritemplate` is a Rust implementation of
//! [RFC6570  - URI Template](http://tools.ietf.org/html/rfc6570) that can
//! process URI Templates up to and including ones designated as Level 4 by the
//! specification. It passes all of the tests in the
//! [uritemplate-test](https://github.com/uri-templates/uritemplate-test) test
//! suite.
//!
//! Basic Usage
//! -----------
//! Variable setting can be chained for nice, clean code.
//!
//! ```ignore
//! extern crate uritemplate;
//! use uritemplate::UriTemplate;
//!
//! let uri = UriTemplate::new("/view/{object:1}/{/object,names}{?query*}")
//!     .set("object", "lakes")
//!     .set("names", &["Erie", "Superior", "Ontario"])
//!     .set("query", &[("size", "15"), ("lang", "en")])
//!     .build();
//!
//! assert_eq!(uri, "/view/l/lakes/Erie,Superior,Ontario?size=15&lang=en");
//! ```
//!
//! It is not possible to set a variable to the value "undefined". Instead,
//! simply delete the variable if you have already set it.
//!
//! ```ignore
//! let mut t = UriTemplate::new("{hello}");
//! t.set("hello", "Hello World!");
//! assert_eq!(t.build(), "Hello%20World%21");
//!
//! t.delete("hello");
//! assert_eq!(t.build(), "");
//! ```
//!
//! The `delete` function returns `true` if the variable existed and `false`
//! otherwise.
//!
//! Supported Types
//! ---------------
//! Any type that implements `IntoTemplateVar` can be set as the value of a
//! `UriTemplate` variable. The following implementations are provided by
//! default for each type of variable:
//!
//! - Scalar Values: `String`, `&str`
//! - Lists: `Vec<String>`, `&[String]`, `&[str]`
//! - Associative Arrays: `Vec<(String, String)>`, `&[(String, String)]`,
//!   `&[(&str, &str)]`, `&HashMap<String, String>`
//!
//! In addition, you can implement `IntoTemplateVar` for your own types. View the
//! documentation for `IntoTemplateVar` for information on how that works.

mod percent_encoding;
mod templatevar;

use crate::percent_encoding::{encode_reserved, encode_unreserved};
use std::collections::HashMap;
use std::str::FromStr;

pub use crate::templatevar::{IntoTemplateVar, TemplateVar};

enum VarSpecType {
    Raw,
    Prefixed(u16),
    Exploded,
}

struct VarSpec {
    name: String,
    var_type: VarSpecType,
}

#[derive(PartialEq)]
enum Operator {
    Null,
    Plus,
    Dot,
    Slash,
    Semi,
    Question,
    Ampersand,
    Hash,
}

enum TemplateComponent {
    Literal(String),
    VarList(Operator, Vec<VarSpec>),
}

/// The main struct that processes and builds URI Templates.
pub struct UriTemplate {
    components: Vec<TemplateComponent>,
    vars: HashMap<String, TemplateVar>,
}

fn prefixed(s: &str, prefix: u16) -> String {
    let prefix = prefix as usize;
    if prefix >= s.len() {
        s.to_string()
    } else {
        s[0..prefix].to_string()
    }
}

fn parse_varlist(varlist: &str) -> TemplateComponent {
    let mut varlist = varlist.to_string();
    let operator = match varlist.chars().nth(0) {
        Some(ch) => ch,
        None => {
            return TemplateComponent::VarList(Operator::Null, Vec::new());
        }
    };
    let operator = match operator {
        '+' => Operator::Plus,
        '.' => Operator::Dot,
        '/' => Operator::Slash,
        ';' => Operator::Semi,
        '?' => Operator::Question,
        '&' => Operator::Ampersand,
        '#' => Operator::Hash,
        _ => Operator::Null,
    };
    if operator != Operator::Null {
        varlist.remove(0);
    }
    let varspecs = varlist.split(",");
    let mut varspec_list = Vec::new();
    for varspec in varspecs {
        let mut varspec = varspec.to_string();
        let len = varspec.len();
        if len >= 1 && varspec.chars().nth(len - 1).unwrap() == '*' {
            varspec.pop();
            varspec_list.push(VarSpec {
                name: varspec,
                var_type: VarSpecType::Exploded,
            });
            continue;
        }
        if varspec.contains(":") {
            let parts: Vec<_> = varspec.splitn(2, ":").collect();
            let prefix = u16::from_str(parts[1]).ok();
            let prefix = match prefix {
                Some(p) => p,
                None => 9999u16,
            };
            varspec_list.push(VarSpec {
                name: parts[0].to_string(),
                var_type: VarSpecType::Prefixed(prefix),
            });
            continue;
        }
        varspec_list.push(VarSpec {
            name: varspec,
            var_type: VarSpecType::Raw,
        });
    }

    TemplateComponent::VarList(operator, varspec_list)
}

fn encode_vec<E>(v: &Vec<String>, encoder: E) -> Vec<String>
where
    E: Fn(&str) -> String,
{
    v.iter().map(|s| encoder(&s)).collect()
}

impl UriTemplate {
    /// Creates a new URI Template from the given template string.
    ///
    /// Example
    /// -------
    /// ```ignore
    /// let t = UriTemplate::new("http://example.com/{name}");
    /// ```
    pub fn new(template: &str) -> UriTemplate {
        let mut components = Vec::new();
        let mut buf = String::new();
        let mut in_varlist = false;

        for ch in template.chars() {
            if in_varlist && ch == '}' {
                components.push(parse_varlist(&buf));
                buf = String::new();
                in_varlist = false;
                continue;
            }
            if !in_varlist && ch == '{' {
                if buf.len() > 0 {
                    components.push(TemplateComponent::Literal(buf));
                    buf = String::new();
                }
                in_varlist = true;
                continue;
            }
            buf.push(ch);
        }

        if buf.len() > 0 {
            components.push(TemplateComponent::Literal(buf));
        }

        UriTemplate {
            components: components,
            vars: HashMap::new(),
        }
    }

    /// Sets the value of a variable in the URI Template.
    ///
    /// Example
    /// -------
    /// ```ignore
    /// let mut t = UriTemplate::new("{name}");
    /// t.set("name", "John Smith");
    /// ```
    ///
    /// This function returns the `URITemplate` so that the `set()` calls can
    /// be chained before building.
    ///
    /// ```ignore
    /// let uri = UriTemplate::new("{firstname}/{lastname}")
    ///     .set("firstname", "John")
    ///     .set("lastname", "Smith")
    ///     .build();
    /// assert_eq!(uri, "John/Smith");
    /// ```
    pub fn set<I: IntoTemplateVar>(&mut self, varname: &str, var: I) -> &mut UriTemplate {
        self.vars
            .insert(varname.to_string(), var.into_template_var());
        self
    }

    /// Deletes the value of a variable in the URI Template. Returns `true` if
    /// the variable existed and `false` otherwise.
    ///
    /// Example
    ///
    /// ```ignore
    /// let mut t = UriTemplate::new("{animal}");
    /// t.set("animal", "dog");
    /// assert_eq!(t.delete("house"), false);
    /// assert_eq!(t.delete("animal"), true);
    /// ```
    pub fn delete(&mut self, varname: &str) -> bool {
        match self.vars.remove(varname) {
            Some(_) => true,
            None => false,
        }
    }

    /// Deletes the values of all variables currently set in the `URITemplate`.
    pub fn delete_all(&mut self) {
        self.vars.clear();
    }

    fn build_varspec<E>(
        &self,
        v: &VarSpec,
        sep: &str,
        named: bool,
        ifemp: &str,
        encoder: E,
    ) -> Option<String>
    where
        E: Fn(&str) -> String,
    {
        let mut res = String::new();

        let var = match self.vars.get(&v.name) {
            Some(v) => v,
            None => return None,
        };

        match *var {
            TemplateVar::Scalar(ref s) => {
                if named {
                    res.push_str(&encode_reserved(&v.name));
                    if s == "" {
                        res.push_str(ifemp);
                        return Some(res);
                    }
                    res.push('=');
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Exploded => {
                        res.push_str(&encoder(s));
                    }
                    VarSpecType::Prefixed(p) => {
                        res.push_str(&encoder(&prefixed(s, p)));
                    }
                };
            }
            TemplateVar::List(ref l) => {
                if l.len() == 0 {
                    return None;
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Prefixed(_) => {
                        if named {
                            res.push_str(&encode_reserved(&v.name));
                            if l.join("").len() == 0 {
                                res.push_str(ifemp);
                                return Some(res);
                            }
                            res.push('=');
                        }
                        res.push_str(&encode_vec(l, encoder).join(","));
                    }
                    VarSpecType::Exploded => {
                        if named {
                            let pairs: Vec<String> = l
                                .iter()
                                .map(|x| {
                                    let val: String = if x == "" {
                                        format!("{}{}", &encode_reserved(&v.name), ifemp)
                                    } else {
                                        format!("{}={}", &encode_reserved(&v.name), &encoder(x))
                                    };
                                    val
                                })
                                .collect();
                            res.push_str(&pairs.join(sep));
                        } else {
                            res.push_str(&encode_vec(&l, encoder).join(sep));
                        }
                    }
                }
            }
            TemplateVar::AssociativeArray(ref a) => {
                if a.len() == 0 {
                    return None;
                }
                match v.var_type {
                    VarSpecType::Raw | VarSpecType::Prefixed(_) => {
                        if named {
                            res.push_str(&encode_reserved(&v.name));
                            res.push('=');
                        }
                        let pairs: Vec<String> = a
                            .iter()
                            .map(|&(ref k, ref v)| {
                                format!("{},{}", &encode_reserved(k), &encoder(v))
                            })
                            .collect();
                        res.push_str(&pairs.join(","));
                    }
                    VarSpecType::Exploded => {
                        if named {
                            let pairs: Vec<String> = a
                                .iter()
                                .map(|&(ref k, ref v)| {
                                    let val: String = if v == "" {
                                        format!("{}{}", &encode_reserved(k), ifemp)
                                    } else {
                                        format!("{}={}", &encode_reserved(k), &encoder(v))
                                    };
                                    val
                                })
                                .collect();
                            res.push_str(&pairs.join(sep));
                        } else {
                            let pairs: Vec<String> = a
                                .iter()
                                .map(|&(ref k, ref v)| {
                                    format!("{}={}", &encode_reserved(k), &encoder(v))
                                })
                                .collect();
                            res.push_str(&pairs.join(sep));
                        }
                    }
                }
            }
        }

        Some(res)
    }

    fn build_varlist(&self, operator: &Operator, varlist: &Vec<VarSpec>) -> String {
        let mut values: Vec<String> = Vec::new();
        let (first, sep, named, ifemp, allow_reserved) = match *operator {
            Operator::Null => ("", ",", false, "", false),
            Operator::Plus => ("", ",", false, "", true),
            Operator::Dot => (".", ".", false, "", false),
            Operator::Slash => ("/", "/", false, "", false),
            Operator::Semi => (";", ";", true, "", false),
            Operator::Question => ("?", "&", true, "=", false),
            Operator::Ampersand => ("&", "&", true, "=", false),
            Operator::Hash => ("#", ",", false, "", true),
        };

        for varspec in varlist {
            let built = if allow_reserved {
                self.build_varspec(varspec, sep, named, ifemp, encode_reserved)
            } else {
                self.build_varspec(varspec, sep, named, ifemp, encode_unreserved)
            };
            match built {
                Some(s) => values.push(s),
                None => {}
            }
        }

        let mut res = String::new();
        if values.len() != 0 {
            res.push_str(first);
            res.push_str(&values.join(sep));
        }

        res
    }

    /// Expands the template using the set variable values and returns the
    /// final String.
    ///
    /// Example
    /// -------
    ///
    /// ```ignore
    /// let mut t = UriTemplate::new("{hello}");
    /// t.set("hello", "Hello World!");
    /// assert_eq!(t.build(), "Hello%20World%21");
    /// ```
    pub fn build(&self) -> String {
        let mut res = String::new();
        for component in &self.components {
            let next = match *component {
                TemplateComponent::Literal(ref s) => encode_reserved(s),
                TemplateComponent::VarList(ref op, ref varlist) => self.build_varlist(op, varlist),
            };
            res.push_str(&next);
        }
        res
    }
}
