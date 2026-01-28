use serde_json::Value;
use std::any;
use std::collections;
use std::fmt;
use std::sync::Arc;

use super::schema;
use super::validators;
use super::SchemaVersion;

pub type KeywordResult = Result<Option<validators::BoxedValidator>, schema::SchemaError>;
pub type KeywordPair = (Vec<&'static str>, Box<dyn Keyword + 'static>);
pub type KeywordPairs = Vec<KeywordPair>;
pub type KeywordMap = collections::HashMap<&'static str, Arc<KeywordConsumer>>;

pub trait Keyword: Send + Sync + any::Any {
    fn compile(&self, def: &Value, ctx: &schema::WalkContext) -> KeywordResult;
    fn is_exclusive(&self, _version: SchemaVersion) -> bool {
        false
    }
    fn place_first(&self) -> bool {
        false
    }
    fn place_last(&self) -> bool {
        false
    }
}

impl<T: 'static + Send + Sync + any::Any> Keyword for T
where
    T: Fn(&Value, &schema::WalkContext<'_>) -> KeywordResult,
{
    fn compile(&self, def: &Value, ctx: &schema::WalkContext<'_>) -> KeywordResult {
        self(def, ctx)
    }
}

impl fmt::Debug for dyn Keyword + 'static {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.write_str("<keyword>")
    }
}

macro_rules! keyword_key_exists {
    ($val:expr, $key:expr) => {{
        let maybe_val = $val.get($key);
        if let Some(maybe_val) = maybe_val {
            maybe_val
        } else {
            return Ok(None);
        }
    }};
}

#[macro_use]
pub mod maxmin_length;

pub mod conditional;
pub mod const_;
pub mod contains;
pub mod content_media;
pub mod dependencies;
pub mod enum_;
pub mod format;
pub mod items;
pub mod maxmin;
pub mod maxmin_items;
pub mod maxmin_properties;
pub mod multiple_of;
pub mod not;
pub mod of;
pub mod pattern;
pub mod properties;
pub mod property_names;
pub mod ref_;
pub mod required;
pub mod type_;
mod unevaluated;
pub mod unique_items;

pub fn default() -> KeywordMap {
    let mut map = collections::HashMap::new();

    decouple_keyword((vec!["$ref"], Box::new(ref_::Ref)), &mut map);
    decouple_keyword((vec!["allOf"], Box::new(of::AllOf)), &mut map);
    decouple_keyword((vec!["anyOf"], Box::new(of::AnyOf)), &mut map);
    decouple_keyword((vec!["const"], Box::new(const_::Const)), &mut map);
    decouple_keyword(
        (
            vec!["contains", "minContains", "maxContains"],
            Box::new(contains::Contains),
        ),
        &mut map,
    );
    decouple_keyword(
        (
            vec!["dependencies", "dependentRequired", "dependentSchemas"],
            Box::new(dependencies::Dependencies),
        ),
        &mut map,
    );
    decouple_keyword((vec!["enum"], Box::new(enum_::Enum)), &mut map);
    decouple_keyword(
        (vec!["exclusiveMaximum"], Box::new(maxmin::ExclusiveMaximum)),
        &mut map,
    );
    decouple_keyword(
        (vec!["exclusiveMinimum"], Box::new(maxmin::ExclusiveMinimum)),
        &mut map,
    );
    decouple_keyword(
        (vec!["items", "additionalItems"], Box::new(items::Items)),
        &mut map,
    );
    decouple_keyword(
        (vec!["maxItems"], Box::new(maxmin_items::MaxItems)),
        &mut map,
    );
    decouple_keyword(
        (vec!["maxLength"], Box::new(maxmin_length::MaxLength)),
        &mut map,
    );
    decouple_keyword(
        (
            vec!["maxProperties"],
            Box::new(maxmin_properties::MaxProperties),
        ),
        &mut map,
    );
    decouple_keyword((vec!["maximum"], Box::new(maxmin::Maximum)), &mut map);
    decouple_keyword(
        (vec!["minItems"], Box::new(maxmin_items::MinItems)),
        &mut map,
    );
    decouple_keyword(
        (vec!["minLength"], Box::new(maxmin_length::MinLength)),
        &mut map,
    );
    decouple_keyword(
        (
            vec!["minProperties"],
            Box::new(maxmin_properties::MinProperties),
        ),
        &mut map,
    );
    decouple_keyword((vec!["minimum"], Box::new(maxmin::Minimum)), &mut map);
    decouple_keyword(
        (vec!["multipleOf"], Box::new(multiple_of::MultipleOf)),
        &mut map,
    );
    decouple_keyword((vec!["not"], Box::new(not::Not)), &mut map);
    decouple_keyword((vec!["oneOf"], Box::new(of::OneOf)), &mut map);
    decouple_keyword((vec!["pattern"], Box::new(pattern::Pattern)), &mut map);
    decouple_keyword(
        (
            vec!["properties", "additionalProperties", "patternProperties"],
            Box::new(properties::Properties),
        ),
        &mut map,
    );
    decouple_keyword(
        (
            vec!["propertyNames"],
            Box::new(property_names::PropertyNames),
        ),
        &mut map,
    );
    decouple_keyword((vec!["required"], Box::new(required::Required)), &mut map);
    decouple_keyword((vec!["type"], Box::new(type_::Type)), &mut map);
    decouple_keyword(
        (
            vec!["unevaluatedItems"],
            Box::new(unevaluated::UnevaluatedItems),
        ),
        &mut map,
    );
    decouple_keyword(
        (
            vec!["unevaluatedProperties"],
            Box::new(unevaluated::UnevaluatedProperties),
        ),
        &mut map,
    );

    decouple_keyword(
        (vec!["uniqueItems"], Box::new(unique_items::UniqueItems)),
        &mut map,
    );

    decouple_keyword(
        (
            vec!["contentMediaType", "contentEncoding"],
            Box::new(content_media::ContentMedia),
        ),
        &mut map,
    );

    decouple_keyword(
        (
            vec!["if", "then", "else"],
            Box::new(conditional::Conditional),
        ),
        &mut map,
    );

    map
}

#[derive(Debug)]
pub struct KeywordConsumer {
    pub keys: Vec<&'static str>,
    pub keyword: Box<dyn Keyword + 'static>,
}

impl KeywordConsumer {
    pub fn consume(&self, set: &mut collections::HashSet<&str>) {
        for key in self.keys.iter() {
            if set.contains(key) {
                set.remove(key);
            }
        }
    }
}

pub fn decouple_keyword(keyword_pair: KeywordPair, map: &mut KeywordMap) {
    let (keys, keyword) = keyword_pair;

    let consumer = Arc::new(KeywordConsumer {
        keys: keys.clone(),
        keyword,
    });

    for key in keys.iter() {
        map.insert(key, consumer.clone());
    }
}
