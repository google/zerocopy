use serde_json::{from_str, to_string_pretty};
use valico::json_dsl;

fn main() {
    let params = json_dsl::Builder::build(|params| {
        params.req_nested("user", json_dsl::array(), |params| {
            params.req_typed("name", json_dsl::string());
            params.req_typed("friend_ids", json_dsl::array_of(json_dsl::u64()))
        });
    });

    let mut obj = from_str(r#"{"user": {"name": "Frodo", "friend_ids": ["1223"]}}"#).unwrap();

    let state = params.process(&mut obj, None);
    if state.is_valid() {
        println!("Result object is {}", to_string_pretty(&obj).unwrap());
    } else {
        panic!("Errors during process: {:?}", state);
    }
}
