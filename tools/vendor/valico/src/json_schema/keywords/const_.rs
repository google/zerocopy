use serde_json::Value;

use super::super::schema;
use super::super::validators;

#[allow(missing_copy_implementations)]
pub struct Const;
impl super::Keyword for Const {
    fn compile(&self, def: &Value, _ctx: &schema::WalkContext) -> super::KeywordResult {
        let const_ = keyword_key_exists!(def, "const");

        Ok(Some(Box::new(validators::Const {
            item: const_.clone(),
        })))
    }
}
