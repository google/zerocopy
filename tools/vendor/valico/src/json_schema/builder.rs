use serde::{Serialize, Serializer};
use serde_json::value::{to_value, Value};
use std::collections;

pub struct SchemaArray {
    items: Vec<Value>,
}

impl SchemaArray {
    pub fn new() -> SchemaArray {
        SchemaArray { items: vec![] }
    }

    pub fn push<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.items.push(Builder::build(build).into_json())
    }
}

pub struct SchemaHash {
    items: collections::HashMap<String, Value>,
}

impl SchemaHash {
    pub fn new() -> SchemaHash {
        SchemaHash {
            items: collections::HashMap::new(),
        }
    }

    pub fn insert<F>(&mut self, key: &str, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.items
            .insert(key.to_string(), Builder::build(build).into_json());
    }
}

pub struct Dependencies {
    deps: collections::HashMap<String, Dependency>,
}

impl Dependencies {
    pub fn new() -> Dependencies {
        Dependencies {
            deps: collections::HashMap::new(),
        }
    }

    pub fn schema<F>(&mut self, property: &str, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.deps.insert(
            property.to_string(),
            Dependency::Schema(Builder::build(build).into_json()),
        );
    }

    pub fn property(&mut self, property: &str, properties: Vec<String>) {
        self.deps
            .insert(property.to_string(), Dependency::Property(properties));
    }

    pub fn build<F>(build: F) -> Dependencies
    where
        F: FnOnce(&mut Dependencies),
    {
        let mut deps = Dependencies::new();
        build(&mut deps);
        deps
    }
}

impl Serialize for Dependencies {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.deps.serialize(serializer)
    }
}

pub enum Dependency {
    Schema(Value),
    Property(Vec<String>),
}

impl Serialize for Dependency {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            Dependency::Schema(ref json) => json.serialize(serializer),
            Dependency::Property(ref array) => array.serialize(serializer),
        }
    }
}

/// Builder provides simple DSL to build Schema. It allows you not to use
/// strings and raw JSON manipulation. It also prevent some kinds of spelling
/// and type errors.
pub struct Builder {
    obj_builder: jsonway::ObjectBuilder,
}

impl Builder {
    pub fn new() -> Builder {
        Builder {
            obj_builder: jsonway::ObjectBuilder::new(),
        }
    }

    pub fn id(&mut self, url: &str) {
        self.obj_builder.set("$id", url.to_string())
    }

    pub fn ref_(&mut self, url: &str) {
        self.obj_builder.set("$ref", url.to_string())
    }

    pub fn schema(&mut self, url: &str) {
        self.obj_builder.set("$schema", url.to_string())
    }

    pub fn desc(&mut self, text: &str) {
        self.obj_builder.set("description", text.to_string())
    }

    pub fn title(&mut self, text: &str) {
        self.obj_builder.set("title", text.to_string())
    }

    pub fn default<T>(&mut self, default: T)
    where
        T: Serialize,
    {
        self.obj_builder.set("default", default)
    }

    pub fn multiple_of(&mut self, number: f64) {
        self.obj_builder.set("multipleOf", number)
    }

    pub fn maximum(&mut self, number: f64) {
        self.obj_builder.set("maximum", number);
    }

    pub fn exclusive_maximum(&mut self, number: f64) {
        self.obj_builder.set("exclusiveMaximum", number);
    }

    pub fn minimum(&mut self, number: f64) {
        self.obj_builder.set("minimum", number);
    }

    pub fn exclusive_minimum(&mut self, number: f64) {
        self.obj_builder.set("exclusiveMinimum", number);
    }

    pub fn max_length(&mut self, number: u64) {
        self.obj_builder.set("maxLength", number)
    }

    pub fn min_length(&mut self, number: u64) {
        self.obj_builder.set("minLength", number)
    }

    pub fn pattern(&mut self, pattern: &str) {
        self.obj_builder.set("pattern", pattern.to_string())
    }

    pub fn format(&mut self, format: &str) {
        self.obj_builder.set("format", format.to_string())
    }

    pub fn items_schema<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("items", Builder::build(build).into_json())
    }

    pub fn items_array<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaArray),
    {
        let mut items = SchemaArray::new();
        build(&mut items);
        self.obj_builder.set("items", items.items)
    }

    pub fn additional_items(&mut self, allow: bool) {
        self.obj_builder.set("additionalItems", allow)
    }

    pub fn additional_items_schema<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("additionalItems", Builder::build(build).into_json())
    }

    pub fn max_items(&mut self, number: u64) {
        self.obj_builder.set("maxItems", number)
    }

    pub fn min_items(&mut self, number: u64) {
        self.obj_builder.set("minItems", number)
    }

    pub fn unique_items(&mut self, unique: bool) {
        self.obj_builder.set("uniqueItems", unique)
    }

    pub fn max_properties(&mut self, number: u64) {
        self.obj_builder.set("maxProperties", number)
    }

    pub fn min_properties(&mut self, number: u64) {
        self.obj_builder.set("minProperties", number)
    }

    pub fn required(&mut self, items: Vec<String>) {
        self.obj_builder.set("required", items)
    }

    pub fn properties<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaHash),
    {
        let mut items = SchemaHash::new();
        build(&mut items);
        self.obj_builder.set("properties", items.items)
    }

    pub fn pattern_properties<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaHash),
    {
        let mut items = SchemaHash::new();
        build(&mut items);
        self.obj_builder.set("patternProperties", items.items)
    }

    pub fn additional_properties(&mut self, allow: bool) {
        self.obj_builder.set("additionalProperties", allow)
    }

    pub fn additional_properties_schema<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("additionalProperties", Builder::build(build).into_json())
    }

    pub fn dependencies<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Dependencies),
    {
        self.obj_builder
            .set("dependencies", Dependencies::build(build))
    }

    pub fn enum_<F>(&mut self, build: F)
    where
        F: FnOnce(&mut jsonway::ArrayBuilder),
    {
        self.obj_builder.set("enum", jsonway::array(build).unwrap())
    }

    pub fn array(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Array.to_string())
    }
    pub fn boolean(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Boolean.to_string())
    }
    pub fn integer(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Integer.to_string())
    }
    pub fn number(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Number.to_string())
    }
    pub fn null(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Null.to_string())
    }
    pub fn object(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::Object.to_string())
    }
    pub fn string(&mut self) {
        self.obj_builder
            .set("type", super::PrimitiveType::String.to_string())
    }
    pub fn type_(&mut self, type_: super::PrimitiveType) {
        self.obj_builder.set("type", type_.to_string())
    }
    pub fn types(&mut self, types: &[super::PrimitiveType]) {
        self.obj_builder.set(
            "type",
            to_value(types.iter().map(|t| t.to_string()).collect::<Vec<String>>()).unwrap(),
        )
    }

    pub fn all_of<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaArray),
    {
        let mut items = SchemaArray::new();
        build(&mut items);
        self.obj_builder.set("allOf", items.items)
    }

    pub fn any_of<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaArray),
    {
        let mut items = SchemaArray::new();
        build(&mut items);
        self.obj_builder.set("anyOf", items.items)
    }

    pub fn one_of<F>(&mut self, build: F)
    where
        F: FnOnce(&mut SchemaArray),
    {
        let mut items = SchemaArray::new();
        build(&mut items);
        self.obj_builder.set("oneOf", items.items)
    }

    pub fn not<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("not", Builder::build(build).into_json())
    }

    pub fn build<F>(build: F) -> Builder
    where
        F: FnOnce(&mut Builder),
    {
        let mut builder = Builder::new();
        build(&mut builder);
        builder
    }

    pub fn into_json(self) -> Value {
        self.obj_builder.unwrap()
    }

    pub fn content_media_type(&mut self, type_: super::keywords::content_media::ContentMediaType) {
        self.obj_builder.set("contentMediaType", type_.as_str())
    }

    pub fn content_encoding(&mut self, type_: super::keywords::content_media::ContentEncoding) {
        self.obj_builder.set("contentEncoding", type_.as_str())
    }

    pub fn if_<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("if", Builder::build(build).into_json())
    }

    pub fn then_<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("then", Builder::build(build).into_json())
    }

    pub fn else_<F>(&mut self, build: F)
    where
        F: FnOnce(&mut Builder),
    {
        self.obj_builder
            .set("else", Builder::build(build).into_json())
    }

    pub fn custom_vocabulary<V: Serialize, N: Into<String>>(&mut self, name: N, value: V) {
        self.obj_builder.set(name, value);
    }
}

impl Serialize for Builder {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.obj_builder.serialize(serializer)
    }
}

pub fn schema<F>(build: F) -> Builder
where
    F: FnOnce(&mut Builder),
{
    Builder::build(build)
}

pub fn schema_box(build: Box<dyn Fn(&mut Builder) + Send>) -> Builder {
    let mut builder = Builder::new();
    build(&mut builder);
    builder
}
