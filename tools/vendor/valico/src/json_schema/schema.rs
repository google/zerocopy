use serde_json::Value;
use std::borrow::Cow;
use std::cell::{Ref, RefCell};
use std::collections;
use std::ops;
use url::Url;

use super::keywords;
use super::scope;
use super::validators;
use super::{helpers, SchemaVersion};
use std::error::Error;
use std::fmt;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub struct WalkContext<'a> {
    pub url: &'a Url,
    pub fragment: Vec<String>,
    pub scopes: &'a mut collections::HashMap<String, Vec<String>>,
    pub version: SchemaVersion,
}

impl<'a> WalkContext<'a> {
    pub fn escaped_fragment(&self) -> String {
        helpers::connect(
            self.fragment
                .iter()
                .map(|s| s.as_ref())
                .collect::<Vec<&str>>()
                .as_ref(),
        )
    }
}

#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub enum SchemaError {
    WrongId,
    IdConflicts,
    NotAnObject,
    UrlParseError(url::ParseError),
    UnknownKey(String),
    Malformed { path: String, detail: String },
}

impl Display for SchemaError {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match *self {
            SchemaError::WrongId => write!(f, "wrong id"),
            SchemaError::IdConflicts => write!(f, "id conflicts"),
            SchemaError::NotAnObject => write!(f, "not an object"),
            SchemaError::UrlParseError(ref e) => write!(f, "url parse error: {e}"),
            SchemaError::UnknownKey(ref k) => write!(f, "unknown key: {k}"),
            SchemaError::Malformed {
                ref path,
                ref detail,
            } => write!(f, "malformed path: `{path}`, details: {detail}"),
        }
    }
}

impl Error for SchemaError {}

#[derive(Debug)]
pub struct ScopedSchema<'a> {
    scope: &'a scope::Scope,
    schema: &'a Schema,
}

impl<'a> ops::Deref for ScopedSchema<'a> {
    type Target = Schema;

    fn deref(&self) -> &Schema {
        self.schema
    }
}

impl<'a> ScopedSchema<'a> {
    pub fn new(scope: &'a scope::Scope, schema: &'a Schema) -> ScopedSchema<'a> {
        ScopedSchema { scope, schema }
    }

    pub fn validate(&self, data: &Value) -> validators::ValidationState {
        self.schema.validate_in_scope(data, "", self.scope)
    }

    pub fn validate_in(&self, data: &Value, path: &str) -> validators::ValidationState {
        self.schema.validate_in_scope(data, path, self.scope)
    }
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct Schema {
    pub id: Option<Url>,
    schema: Option<Url>,
    original: Value,
    tree: collections::BTreeMap<String, Schema>,
    validators: validators::Validators,
    scopes: collections::HashMap<String, Vec<String>>,
    default: RefCell<Option<Value>>,
}

include!(concat!(env!("OUT_DIR"), "/codegen.rs"));

pub struct CompilationSettings<'a> {
    pub keywords: &'a keywords::KeywordMap,
    pub ban_unknown_keywords: bool,
    pub schema_version: SchemaVersion,
}

impl<'a> CompilationSettings<'a> {
    pub fn new(
        keywords: &'a keywords::KeywordMap,
        ban_unknown_keywords: bool,
        schema_version: SchemaVersion,
    ) -> CompilationSettings<'a> {
        CompilationSettings {
            keywords,
            ban_unknown_keywords,
            schema_version,
        }
    }
}

impl Schema {
    fn compile(
        def: Value,
        external_id: Option<Url>,
        settings: CompilationSettings,
    ) -> Result<Schema, SchemaError> {
        let def = helpers::convert_boolean_schema(def);

        if !def.is_object() {
            return Err(SchemaError::NotAnObject);
        }

        let mut id = if let Some(id) = external_id {
            id
        } else {
            helpers::parse_url_key("$id", &def)?.unwrap_or_else(helpers::generate_id)
        };

        if settings.schema_version >= SchemaVersion::Draft2019_09 {
            if let Some(anchor) = def.get("$anchor") {
                let anchor = anchor.as_str().ok_or_else(|| SchemaError::Malformed {
                    path: "".to_string(),
                    detail: "$anchor must be a string".to_string(),
                })?;
                id.set_fragment(Some(anchor));
            };
        }

        let schema = helpers::parse_url_key("$schema", &def)?;

        let (tree, mut scopes) = {
            let mut tree = collections::BTreeMap::new();
            let obj = def.as_object().unwrap();

            let mut scopes = collections::HashMap::new();

            for (key, value) in obj.iter() {
                if !value.is_object() && !value.is_array() && !value.is_boolean() {
                    continue;
                }
                if FINAL_KEYS.contains(&key[..]) {
                    continue;
                }

                let mut context = WalkContext {
                    url: &id,
                    fragment: vec![key.clone()],
                    scopes: &mut scopes,
                    version: settings.schema_version,
                };

                let scheme = Schema::compile_sub(
                    value.clone(),
                    &mut context,
                    &settings,
                    !NON_SCHEMA_KEYS.contains(&key[..]),
                )?;

                tree.insert(helpers::encode(key), scheme);
            }

            (tree, scopes)
        };

        let validators = Schema::compile_keywords(
            &def,
            &WalkContext {
                url: &id,
                fragment: vec![],
                scopes: &mut scopes,
                version: settings.schema_version,
            },
            &settings,
        )?;

        let schema = Schema {
            id: Some(id),
            schema,
            original: def,
            tree,
            validators,
            scopes,
            default: RefCell::new(None),
        };

        Ok(schema)
    }

    /// The issue here is that it is impossible to explain
    /// to the Rust borrow checker that I’m traversing a tree, mutating it at the same
    /// time, and need to occasionally jump back to the root — which is safe in this
    /// particular case because the tree structure is not touched!
    ///
    /// This operation is safe (i.e. it will not panic) as long as it is not called
    /// while the default value is borrowed, hence unsafe_get_default must not be used
    /// directly, only via `get_default()` and `has_default()`.
    fn unsafe_set_default(&self, default: Option<Value>) {
        self.default.replace(default);
    }

    /// Getting references to internally mutable memory is finicky business, we must
    /// not allow these references to escape. Therefore only internal code is allowed
    /// to use this function to
    ///
    ///  - take a peek at the value, to see whether the option is set, or
    ///  - take a peek at the value just long enough to clone it.
    fn unsafe_get_default(&self) -> Ref<Option<Value>> {
        self.default.borrow()
    }

    pub fn get_default(&self) -> Option<Value> {
        self.unsafe_get_default().clone()
    }

    pub fn has_default(&self) -> bool {
        self.unsafe_get_default().is_some()
    }

    pub fn add_defaults(&mut self, id: &Url, scope: &scope::Scope) {
        self.add_defaults_recursive(self, id, scope);
    }

    fn add_defaults_recursive(&self, top: &Schema, id: &Url, scope: &scope::Scope) {
        // step 0: bail out if we already have a default (i.e. proof that traversal got here before)
        if self.has_default() {
            return;
        }

        // step 1: walk the tree to apply this recursively
        for (_, schema) in self.tree.iter() {
            schema.add_defaults_recursive(top, id, scope);
        }

        // step 2: use explicit default if present
        if let Some(default) = self.original.get("default") {
            self.unsafe_set_default(Some(default.clone()));
            return;
        }

        // step 3: propagate defaults according to the rules
        // 3a: $ref
        if let Some(ref_) = self.original.get("$ref").and_then(|r| r.as_str()) {
            if let Ok(url) = Url::options().base_url(Some(id)).parse(ref_) {
                // first try to resolve this Url internally so that we can then modify the schema
                // in case this one has not yet been traversed
                if let Some(schema) = top.resolve_internal(&url) {
                    schema.add_defaults_recursive(top, id, scope);
                    self.unsafe_set_default(schema.get_default());
                } else if let Some(schema) = scope.resolve(&url) {
                    self.unsafe_set_default(schema.get_default());
                }
            }
            // $ref is exclusive, i.e. does not tolerate other keywords to be present
            return;
        }
        // 3b: properties
        if let Some(properties) = self.tree.get("properties") {
            let mut default = serde_json::Map::default();
            for (key, schema) in properties.tree.iter() {
                if let Some(value) = schema.get_default() {
                    default.insert(key.clone(), value);
                }
            }
            if !default.is_empty() {
                self.unsafe_set_default(Some(default.into()));
                return;
            }
        }
        // 3c: items, if array
        // only create a default, if there are defaults given for all items
        if self
            .original
            .get("items")
            .map(|i| i.is_array())
            .unwrap_or(false)
        {
            let items = self.tree.get("items").unwrap();
            let mut default = vec![];
            for idx in 0.. {
                if let Some(schema) = items.tree.get(&idx.to_string()) {
                    if let Some(def) = schema.get_default() {
                        default.push(def);
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            if default.len() == items.tree.len() {
                self.unsafe_set_default(Some(default.into()));
            }
        }
    }

    fn compile_keywords(
        def: &Value,
        context: &WalkContext,
        settings: &CompilationSettings,
    ) -> Result<validators::Validators, SchemaError> {
        let mut validators = vec![];
        let mut end_validators = vec![];
        let mut keys: collections::HashSet<&str> = def
            .as_object()
            .unwrap()
            .keys()
            .map(|key| key.as_ref())
            .collect();
        let mut not_consumed = collections::HashSet::new();

        loop {
            let key = keys.iter().next().cloned();
            if let Some(key) = key {
                match settings.keywords.get(&key) {
                    Some(keyword) => {
                        keyword.consume(&mut keys);

                        let is_exclusive_keyword =
                            keyword.keyword.is_exclusive(settings.schema_version);

                        if let Some(validator) = keyword.keyword.compile(def, context)? {
                            if is_exclusive_keyword {
                                validators = vec![validator];
                                end_validators = vec![];
                            } else if keyword.keyword.place_first() {
                                validators.splice(0..0, std::iter::once(validator));
                            } else if keyword.keyword.place_last() {
                                end_validators.push(validator);
                            } else {
                                validators.push(validator);
                            }
                        }

                        if is_exclusive_keyword {
                            break;
                        }
                    }
                    None => {
                        keys.remove(&key);
                        if settings.ban_unknown_keywords {
                            not_consumed.insert(key);
                        }
                    }
                }
            } else {
                break;
            }
        }

        if settings.ban_unknown_keywords && !not_consumed.is_empty() {
            for key in not_consumed.iter() {
                if !ALLOW_NON_CONSUMED_KEYS.contains(&key[..]) {
                    return Err(SchemaError::UnknownKey((*key).to_string()));
                }
            }
        }

        validators.extend(end_validators);
        Ok(validators)
    }

    fn compile_sub(
        def: Value,
        context: &mut WalkContext,
        keywords: &CompilationSettings,
        is_schema: bool,
    ) -> Result<Schema, SchemaError> {
        let def = helpers::convert_boolean_schema(def);

        let id = if is_schema {
            let mut id_url = helpers::parse_url_key_with_base("$id", &def, context.url)?;
            if keywords.schema_version >= SchemaVersion::Draft2019_09 {
                if let Some(anchor) = def.get("$anchor") {
                    let anchor = anchor.as_str().ok_or_else(|| SchemaError::Malformed {
                        path: "".to_string(),
                        detail: "$anchor must be a string".to_string(),
                    })?;

                    // If the "$id" URL is not explicitly overridden, implicitly inherit the parent's URL.
                    if id_url.is_none() {
                        id_url = Some(context.url.clone());
                    }

                    id_url.as_mut().unwrap().set_fragment(Some(anchor));
                }
            }
            id_url
        } else {
            None
        };

        let schema = if is_schema {
            helpers::parse_url_key("$schema", &def)?
        } else {
            None
        };

        let tree = {
            let mut tree = collections::BTreeMap::new();

            if def.is_object() {
                let obj = def.as_object().unwrap();
                let parent_key = &context.fragment[context.fragment.len() - 1];

                for (key, value) in obj.iter() {
                    if !value.is_object() && !value.is_array() && !value.is_boolean() {
                        continue;
                    }
                    if !PROPERTY_KEYS.contains(&parent_key[..]) && FINAL_KEYS.contains(&key[..]) {
                        continue;
                    }

                    let mut current_fragment = context.fragment.clone();
                    current_fragment.push(key.clone());

                    let is_schema = PROPERTY_KEYS.contains(&parent_key[..])
                        || !NON_SCHEMA_KEYS.contains(&key[..]);

                    let mut context = WalkContext {
                        url: id.as_ref().unwrap_or(context.url),
                        fragment: current_fragment,
                        scopes: context.scopes,
                        version: keywords.schema_version,
                    };

                    let scheme =
                        Schema::compile_sub(value.clone(), &mut context, keywords, is_schema)?;

                    tree.insert(helpers::encode(key), scheme);
                }
            } else if def.is_array() {
                let array = def.as_array().unwrap();
                let parent_key = &context.fragment[context.fragment.len() - 1];

                for (idx, value) in array.iter().enumerate() {
                    let mut value = value.clone();

                    if BOOLEAN_SCHEMA_ARRAY_KEYS.contains(&parent_key[..]) {
                        value = helpers::convert_boolean_schema(value);
                    }

                    if !value.is_object() && !value.is_array() {
                        continue;
                    }

                    let mut current_fragment = context.fragment.clone();
                    current_fragment.push(idx.to_string().clone());

                    let mut context = WalkContext {
                        url: id.as_ref().unwrap_or(context.url),
                        fragment: current_fragment,
                        scopes: context.scopes,
                        version: keywords.schema_version,
                    };

                    let scheme = Schema::compile_sub(value.clone(), &mut context, keywords, true)?;

                    tree.insert(idx.to_string().clone(), scheme);
                }
            }

            tree
        };

        if id.is_some() {
            context
                .scopes
                .insert(id.clone().unwrap().into(), context.fragment.clone());
        }

        let validators = if is_schema && def.is_object() {
            Schema::compile_keywords(&def, context, keywords)?
        } else {
            vec![]
        };

        let schema = Schema {
            id,
            schema,
            original: def,
            tree,
            validators,
            scopes: collections::HashMap::new(),
            default: RefCell::new(None),
        };

        Ok(schema)
    }

    pub fn resolve(&self, id: &str) -> Option<&Schema> {
        let path = self.scopes.get(id);
        path.map(|path| {
            let mut schema = self;
            for item in path.iter() {
                schema = &schema.tree[item]
            }
            schema
        })
    }

    fn resolve_internal(&self, url: &Url) -> Option<&Schema> {
        let (schema_path, fragment) = helpers::serialize_schema_path(url);
        if self.id.is_some() && schema_path.as_str() == self.id.as_ref().unwrap().as_str() {
            if let Some(fragment) = fragment {
                self.resolve_fragment(fragment.as_str())
            } else {
                Some(self)
            }
        } else if let Some(id_path) = self.scopes.get(&schema_path) {
            let mut schema = self;
            for item in id_path.iter() {
                schema = &schema.tree[item]
            }
            if let Some(fragment) = fragment {
                schema.resolve_fragment(fragment.as_str())
            } else {
                Some(schema)
            }
        } else {
            None
        }
    }

    pub fn resolve_fragment(&self, fragment: &str) -> Option<&Schema> {
        assert!(fragment.starts_with('/'), "Can't resolve id fragments");

        let parts = fragment[1..].split('/');
        let mut schema = self;
        for part in parts {
            match schema.tree.get(part) {
                Some(sch) => schema = sch,
                None => return None,
            }
        }

        Some(schema)
    }
}

impl Schema {
    fn validate_in_scope(
        &self,
        data: &Value,
        path: &str,
        scope: &scope::Scope,
    ) -> validators::ValidationState {
        let mut state = validators::ValidationState::new();
        let mut data = Cow::Borrowed(data);

        for validator in self.validators.iter() {
            let mut result = validator.validate(&data, path, scope, &state);
            if result.is_valid() && result.replacement.is_some() {
                *data.to_mut() = result.replacement.take().unwrap();
            }
            state.append(result);
        }

        state.set_replacement(data);
        state
    }
}

pub fn compile(
    def: Value,
    external_id: Option<Url>,
    settings: CompilationSettings<'_>,
) -> Result<Schema, SchemaError> {
    Schema::compile(def, external_id, settings)
}

#[test]
fn schema_doesnt_compile_not_object() {
    assert!(Schema::compile(
        json!(0),
        None,
        CompilationSettings::new(&keywords::default(), true, SchemaVersion::Draft7)
    )
    .is_err());
}

#[test]
fn schema_compiles_boolean_schema() {
    assert!(Schema::compile(
        json!(true),
        None,
        CompilationSettings::new(&keywords::default(), true, SchemaVersion::Draft7)
    )
    .is_ok());
}
