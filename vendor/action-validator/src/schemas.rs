use serde_json::Value;

use crate::validation_state::ValidationState;

pub fn validate_as_action(doc: &Value) -> ValidationState {
    validate_with_schema(
        doc,
        include_bytes!("schemastore/src/schemas/json/github-action.json"),
    )
}

pub fn validate_as_workflow(doc: &Value) -> ValidationState {
    validate_with_schema(
        doc,
        include_bytes!("schemastore/src/schemas/json/github-workflow.json"),
    )
}

fn validate_with_schema(doc: &Value, schema: &[u8]) -> ValidationState {
    let schema_json: serde_json::Value =
        serde_json::from_str(String::from_utf8_lossy(schema).as_ref()).unwrap();

    let mut scope = valico::json_schema::Scope::new();
    let validator = scope.compile_and_return(schema_json, false).unwrap();

    validator.validate(doc).into()
}
