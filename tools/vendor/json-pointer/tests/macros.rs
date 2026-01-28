#[allow(unused_macros)]
macro_rules! assert_unparse {
    ($expr:expr) => {
        let ptr = $expr.parse::<JsonPointer<_, _>>().unwrap();
        assert_eq!(ptr.to_string(), $expr);
    };
    (uri $expr:expr) => {
        let ptr = $expr.parse::<JsonPointer<_, _>>().unwrap();
        assert_eq!(ptr.uri_fragment(), $expr);
    };
}
