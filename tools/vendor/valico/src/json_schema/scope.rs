use serde_json::Value;
use std::collections;

use super::helpers;
use super::keywords;
use super::schema;
use super::SchemaVersion;

#[allow(dead_code)]
#[derive(Debug)]
pub struct Scope {
    keywords: keywords::KeywordMap,
    schemes: collections::HashMap<String, schema::Schema>,
    pub(crate) supply_defaults: bool,
    schema_version: SchemaVersion,
}

#[allow(dead_code)]
impl Scope {
    pub fn new() -> Scope {
        let mut scope = Scope::without_formats(SchemaVersion::Draft7);
        scope.add_keyword(vec!["format"], keywords::format::Format::new());
        scope
    }

    pub fn without_formats(version: SchemaVersion) -> Scope {
        Scope {
            keywords: keywords::default(),
            schemes: collections::HashMap::new(),
            supply_defaults: false,
            schema_version: version,
        }
    }

    pub fn with_formats<F>(build_formats: F, version: SchemaVersion) -> Scope
    where
        F: FnOnce(&mut keywords::format::FormatBuilders),
    {
        let mut scope = Scope::without_formats(version);
        scope.add_keyword(
            vec!["format"],
            keywords::format::Format::with(build_formats),
        );
        scope
    }

    pub fn set_version(mut self, version: SchemaVersion) -> Self {
        self.schema_version = version;
        self
    }

    /// ### use `default` values to compute an enriched version of the input
    ///
    /// JSON schema foresees the `default` attribute in any schema but does not assign
    /// it a specific semantics; it is merely suggested that it may be used to supply
    /// default values, e.g. for use in an interactive editor. The only specification
    /// is that the value of a `default` attribute shall be a JSON value that SHOULD
    /// validate its schema if supplied.
    ///
    /// This feature activates defaults as a mechanism for schema authors to include
    /// defaults such that consuming programs can rely upon the presence of such paths
    /// even if the validated JSON object does not contain values at these paths. This
    /// allows for example non-`required` properties to be parsed as mandatory by
    /// supplying the fallback within the schema.
    ///
    /// The most basic usage is to add defaults to scalar properties (like strings or
    /// numbers). A more interesting aspect is that defaults bubble up through the
    /// property tree:
    ///
    ///  - an element of `properties` with a default value will create a default value
    ///    for its parent unless that one declares a default itself
    ///  - if an array is given as the value of an `items` property and all schemas in
    ///    that array provide a default, then a default is created for the schema
    ///    containing the `items` clause unless that schema declares a default itself
    ///  - the default of a `$ref` schema is the default of its referenced schema
    ///
    /// When validating an instance against the thus enriched schema, each path that
    /// has a default in the schema and no value in the instance will have the default
    /// added at that path (a copy will be made and returned within the ValidationState
    /// structure).
    ///
    /// The following validators interact additionally with the defaults:
    ///
    ///  - `contains`: if there is an object in the array that validates the supplied schema,
    ///    then that object is outfitted with the defaults of that schema; all other
    ///    array elements remain unchanged (i.e. only the first match gets defaults)
    ///  - `dependencies`: if the instance triggers a dependent schema and validates it,
    ///    then that schema’s defaults will be applied
    ///  - `not`: the supplied schema is used to validate a copy of the instance with
    ///    defaults added to determine whether to reject the original instance, but
    ///    the enriched instance is then discarded
    ///  - `anyOf`: the search of a schema for which the supplied instance is valid is
    ///    conducted with enriched instances according to the schema being tried; the
    ///    first enrichted instance that validates the schema is returned
    ///  - `oneOf`: just as for `anyOf`, apart from checking that the instance does not
    ///    validate the remaining schemas
    ///  - `allOf`: first, make one pass over the supplied schemas, handing each one the
    ///    enriched instance from the previous (aborting in case of errors); second,
    ///    another such pass, starting with the result from the first; third, a check
    ///    whether the enrichment results from the two passes match (it is an error
    ///    if they are different — this is an approximation, but a reasonable one)
    ///
    /// Please note that supplying default values this way can lead to a schema that
    /// equates to the `false` schema, i.e. does not match any instance, so don’t try
    /// to be too clever, especially with the `not`, `allOf`, and `oneOf` validators.
    ///
    /// ### Caveat emptor
    ///
    /// The order in which validators are applied to an instance is UNDEFINED apart from
    /// the rule that `properties` and `items` will be moved to the front (but the order
    /// between these is UNDEFINED as well). Therefore, if one validator depends on the
    /// fact that a default value has been injected by processing another validator, then
    /// the result is UNDEFINED (with the exception stated in the previous sentence).
    #[must_use]
    pub fn supply_defaults(self) -> Self {
        Scope {
            keywords: self.keywords,
            schemes: self.schemes,
            supply_defaults: true,
            schema_version: SchemaVersion::Draft7,
        }
    }

    pub fn compile(
        &mut self,
        def: Value,
        ban_unknown: bool,
    ) -> Result<url::Url, schema::SchemaError> {
        let mut schema = schema::compile(
            def,
            None,
            schema::CompilationSettings::new(&self.keywords, ban_unknown, self.schema_version),
        )?;
        let id = schema.id.clone().unwrap();
        if self.supply_defaults {
            schema.add_defaults(&id, self);
        }
        self.add(&id, schema)?;
        Ok(id)
    }

    pub fn compile_with_id(
        &mut self,
        id: &url::Url,
        def: Value,
        ban_unknown: bool,
    ) -> Result<(), schema::SchemaError> {
        let mut schema = schema::compile(
            def,
            Some(id.clone()),
            schema::CompilationSettings::new(&self.keywords, ban_unknown, self.schema_version),
        )?;
        if self.supply_defaults {
            schema.add_defaults(id, self);
        }
        self.add(id, schema)
    }

    pub fn compile_and_return(
        &'_ mut self,
        def: Value,
        ban_unknown: bool,
    ) -> Result<schema::ScopedSchema<'_>, schema::SchemaError> {
        let mut schema = schema::compile(
            def,
            None,
            schema::CompilationSettings::new(&self.keywords, ban_unknown, self.schema_version),
        )?;
        let id = schema.id.clone().unwrap();
        if self.supply_defaults {
            schema.add_defaults(&id, self);
        }
        self.add_and_return(&id, schema)
    }

    pub fn compile_and_return_with_id<'a>(
        &'a mut self,
        id: &url::Url,
        def: Value,
        ban_unknown: bool,
    ) -> Result<schema::ScopedSchema<'a>, schema::SchemaError> {
        let mut schema = schema::compile(
            def,
            Some(id.clone()),
            schema::CompilationSettings::new(&self.keywords, ban_unknown, self.schema_version),
        )?;
        if self.supply_defaults {
            schema.add_defaults(id, self);
        }
        self.add_and_return(id, schema)
    }

    pub fn add_keyword<T>(&mut self, keys: Vec<&'static str>, keyword: T)
    where
        T: keywords::Keyword + 'static,
    {
        keywords::decouple_keyword((keys, Box::new(keyword)), &mut self.keywords);
    }

    #[allow(clippy::map_entry)] // allowing for the return values
    fn add(&mut self, id: &url::Url, schema: schema::Schema) -> Result<(), schema::SchemaError> {
        let (id_str, fragment) = helpers::serialize_schema_path(id);

        if fragment.is_some() {
            return Err(schema::SchemaError::WrongId);
        }

        if !self.schemes.contains_key(&id_str) {
            self.schemes.insert(id_str, schema);
            Ok(())
        } else {
            Err(schema::SchemaError::IdConflicts)
        }
    }

    #[allow(clippy::map_entry)] // allowing for the return values
    fn add_and_return<'a>(
        &'a mut self,
        id: &url::Url,
        schema: schema::Schema,
    ) -> Result<schema::ScopedSchema<'a>, schema::SchemaError> {
        let (id_str, fragment) = helpers::serialize_schema_path(id);

        if fragment.is_some() {
            return Err(schema::SchemaError::WrongId);
        }

        if !self.schemes.contains_key(&id_str) {
            self.schemes.insert(id_str.clone(), schema);
            Ok(schema::ScopedSchema::new(self, &self.schemes[&id_str]))
        } else {
            Err(schema::SchemaError::IdConflicts)
        }
    }

    pub fn resolve<'a>(&'a self, id: &url::Url) -> Option<schema::ScopedSchema<'a>> {
        let (schema_path, fragment) = helpers::serialize_schema_path(id);

        let schema = self.schemes.get(&schema_path).or_else(|| {
            // Searching for inline schema in O(N)
            for (_, schema) in self.schemes.iter() {
                let internal_schema = schema.resolve(schema_path.as_ref());
                if internal_schema.is_some() {
                    return internal_schema;
                }
            }

            None
        });

        schema.and_then(|schema| match fragment {
            Some(ref fragment) => schema
                .resolve_fragment(fragment)
                .map(|schema| schema::ScopedSchema::new(self, schema)),
            None => Some(schema::ScopedSchema::new(self, schema)),
        })
    }
}

#[test]
fn lookup() {
    let mut scope = Scope::new();

    scope
        .compile(
            jsonway::object(|schema| schema.set("$id", "http://example.com/schema".to_string()))
                .unwrap(),
            false,
        )
        .ok()
        .unwrap();

    scope
        .compile(
            jsonway::object(|schema| {
                schema.set("$id", "http://example.com/schema#sub".to_string());
                schema.object("subschema", |subschema| {
                    subschema.set("$id", "#subschema".to_string());
                })
            })
            .unwrap(),
            false,
        )
        .ok()
        .unwrap();

    assert!(scope
        .resolve(&url::Url::parse("http://example.com/schema").ok().unwrap())
        .is_some());
    assert!(scope
        .resolve(
            &url::Url::parse("http://example.com/schema#sub")
                .ok()
                .unwrap()
        )
        .is_some());
    assert!(scope
        .resolve(
            &url::Url::parse("http://example.com/schema#sub/subschema")
                .ok()
                .unwrap()
        )
        .is_some());
    assert!(scope
        .resolve(
            &url::Url::parse("http://example.com/schema#subschema")
                .ok()
                .unwrap()
        )
        .is_some());
}
