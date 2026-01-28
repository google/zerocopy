use uritemplate::{IntoTemplateVar, TemplateVar, UriTemplate};

#[test]
fn test_example() {
    let uri = UriTemplate::new("/view/{object:1}{/object,names}{?query*}")
        .set("object", "lakes")
        .set("names", &["Erie", "Superior", "Ontario"])
        .set("query", &[("size", "15"), ("lang", "en")])
        .build();
    assert_eq!(uri, "/view/l/lakes/Erie,Superior,Ontario?size=15&lang=en");
}

#[test]
fn test_deletion_example() {
    let mut t = UriTemplate::new("{hello}");
    t.set("hello", "Hello World!");
    assert_eq!(t.build(), "Hello%20World%21");

    t.delete("hello");
    assert_eq!(t.build(), "");
}

#[test]
fn test_delete() {
    let mut t = UriTemplate::new("{foo}");
    t.set("foo", "123");

    assert_eq!(t.build(), "123");

    // Deleting nonexistent variable has no effect
    assert_eq!(t.delete("bar"), false);
    assert_eq!(t.build(), "123");

    // Deleting existing variable works
    assert_eq!(t.delete("foo"), true);
    assert_eq!(t.build(), "");
}

#[test]
fn test_delete_all() {
    let mut t = UriTemplate::new("{A}{B}{C}");
    t.set("A", "alpha");
    t.set("B", "beta");
    t.set("C", "charlie");
    assert_eq!(t.build(), "alphabetacharlie");

    t.delete_all();
    assert_eq!(t.build(), "");
}

struct Address {
    city: String,
    state: String,
}

impl<'a> IntoTemplateVar for &'a Address {
    fn into_template_var(self) -> TemplateVar {
        TemplateVar::AssociativeArray(vec![
            ("city".to_string(), self.city.clone()),
            ("state".to_string(), self.state.clone()),
        ])
    }
}

#[test]
fn test_intotemplatevar() {
    let address = Address {
        city: "Los Angelos".to_string(),
        state: "California".to_string(),
    };
    let uri = UriTemplate::new("http://example.com/view{?address*}")
        .set("address", &address)
        .build();
    assert_eq!(
        uri,
        "http://example.com/view?city=Los%20Angelos&state=California"
    );
}

#[test]
fn test_set() {
    let mut t = UriTemplate::new("");
    t.set("hello", "hello".to_string());
    t.set("listvar", Vec::<String>::new());
    t.set("assocvar", Vec::<(String, String)>::new());
}

#[test]
fn test_literal_expansion() {
    let uri = UriTemplate::new("hey!%%25").build();
    assert_eq!(uri, "hey!%25%25");
}
