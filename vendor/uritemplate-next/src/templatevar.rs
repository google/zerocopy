use std::collections::HashMap;

/// TemplateVar represents the value of a template variable, which can be a
/// scalar (a simple string), a list of strings, or an associative array of
/// strings.
///
/// Normally, it is not necessary to use this class unless you are implementing
/// the `IntoTemplateVar` trait for your own classes.
#[derive(Clone)]
pub enum TemplateVar {
    /// A simple string such as `"foo"`
    Scalar(String),
    /// A list of strings such as `["foo", "bar"]`
    List(Vec<String>),
    /// An associative array of strings, such as
    /// `[("key1", "value1"), ("key2", "value2")]`
    AssociativeArray(Vec<(String, String)>),
}

/// IntoTemplateVar represents any type that can be converted into a TemplateVar
/// for use as the value of a template variable, such as a `String`,
/// `Vec<String>`, or `Vec<(String, String)>`. Default implementations are
/// available for those three types, as well as the `&str` versions.
///
/// Example
/// -------
/// Here is an example of implementing `IntoTemplateVar` for your own `Address`
/// struct. Note that you should probably implement the trait for a reference to
/// your struct, not the actual struct, unless you intend to move the value
/// efficiently.
///
/// ```ignore
/// struct Address {
///     city: String,
///     state: String
/// }
///
/// impl <'a> IntoTemplateVar for &'a Address {
///     fn into_template_var(self) -> TemplateVar {
///         TemplateVar::AssociativeArray(vec![
///             ("city".to_string(), self.city.clone()),
///             ("state".to_string(), self.state.clone())
///         ])
///     }
/// }
/// ```
///
/// Now, `Address` variables can be set as `UriTemplate` variables.
///
/// ```ignore
/// let address = Address {
///     city: "Los Angelos".to_string(),
///     state: "California".to_string()
/// };
///
/// let uri = UriTemplate::new("http://example.com/view{?address*}")
///     .set("address", &address)
///     .build();
///
/// assert_eq!(
///     uri,
///     "http://example.com/view?city=Los%20Angelos&state=California"
/// );
/// ```
pub trait IntoTemplateVar {
    fn into_template_var(self) -> TemplateVar;
}

impl IntoTemplateVar for TemplateVar {
    fn into_template_var(self) -> TemplateVar {
        self.clone()
    }
}

impl<'a> IntoTemplateVar for &'a str {
    fn into_template_var(self) -> TemplateVar {
        TemplateVar::Scalar(self.to_string())
    }
}

impl IntoTemplateVar for String {
    fn into_template_var(self) -> TemplateVar {
        TemplateVar::Scalar(self)
    }
}

impl<'a> IntoTemplateVar for &'a [String] {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for s in self {
            vec.push(s.clone());
        }
        TemplateVar::List(vec)
    }
}

impl IntoTemplateVar for Vec<String> {
    fn into_template_var(self) -> TemplateVar {
        TemplateVar::List(self)
    }
}

impl<'a, 'b> IntoTemplateVar for &'a [&'b str] {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for s in self {
            vec.push(s.to_string());
        }
        TemplateVar::List(vec)
    }
}

impl<'a> IntoTemplateVar for &'a [(String, String)] {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for s in self {
            vec.push(s.clone());
        }
        TemplateVar::AssociativeArray(vec)
    }
}

impl IntoTemplateVar for Vec<(String, String)> {
    fn into_template_var(self) -> TemplateVar {
        TemplateVar::AssociativeArray(self)
    }
}

impl<'a, 'b, 'c> IntoTemplateVar for &'a [(&'b str, &'c str)] {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for s in self {
            vec.push((s.0.to_string(), s.1.to_string()));
        }
        TemplateVar::AssociativeArray(vec)
    }
}

impl<'a> IntoTemplateVar for &'a HashMap<String, String> {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for (k, v) in self {
            vec.push((k.clone(), v.clone()));
        }
        TemplateVar::AssociativeArray(vec)
    }
}

impl<'a, 'b, 'c> IntoTemplateVar for &'a HashMap<&'b str, &'c str> {
    fn into_template_var(self) -> TemplateVar {
        let mut vec = Vec::new();
        for (k, v) in self {
            vec.push((k.to_string(), v.to_string()));
        }
        TemplateVar::AssociativeArray(vec)
    }
}

macro_rules! array_impls {
    ($($N:expr)+) => {$(
        impl <'a> IntoTemplateVar for &'a [String; $N] {
            fn into_template_var(self) -> TemplateVar {
                self[..].into_template_var()
            }
        }

        impl <'a, 'b> IntoTemplateVar for &'a[&'b str; $N] {
            fn into_template_var(self) -> TemplateVar {
                self[..].into_template_var()
            }
        }

        impl <'a> IntoTemplateVar for &'a [(String, String); $N] {
            fn into_template_var(self) -> TemplateVar {
                self[..].into_template_var()
            }
        }

        impl <'a, 'b, 'c> IntoTemplateVar for &'a[(&'b str, &'c str); $N] {
            fn into_template_var(self) -> TemplateVar {
                self[..].into_template_var()
            }
        }
    )+}
}

array_impls!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25
    26 27 28 29 30 31 32);
