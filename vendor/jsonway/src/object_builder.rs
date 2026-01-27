use serde_json::{Value, to_value};
use serde::{Serialize, Serializer};

pub type Object = ::serde_json::Map<String, Value>;
use array_builder;

pub struct ObjectBuilder {
    pub object: Object,
    pub null: bool,
    pub skip: bool,
    pub root: Option<String>
}

/// ObjectBuilder is used to produce JSON objects
impl ObjectBuilder {
    pub fn new() -> ObjectBuilder {
        ObjectBuilder {
            object: ::serde_json::Map::new(),
            null: false,
            skip: false,
            root: None
        }
    }

    /// Initialize builder with initial value.
    pub fn from_json(object: Value) -> Option<ObjectBuilder> {
        match object {
            Value::Object(object) => Some(ObjectBuilder {
                object: object,
                null: false,
                skip: false,
                root: None
            }),
            _ => None
        }
    }

    /// Create new builder, pass it to closure as mutable ref and return.
    pub fn build<F>(builder: F) -> ObjectBuilder where F: FnOnce(&mut ObjectBuilder) {
        let mut bldr = ObjectBuilder::new();
        builder(&mut bldr);

        bldr
    }

    /// It you call `null`, this object will be converted to null.
    pub fn null(&mut self) {
        self.null = true;
    }

    /// It you call `skip`, this object will be skipped.
    pub fn skip(&mut self) {
        self.skip = true;
    }

    // Set custom root for result Value object
    pub fn root(&mut self, root: &str) {
        self.root = Some(root.to_string());
    }

    pub fn has_root(&mut self) -> bool {
        self.root.is_some()
    }

    /// Move out internal JSON value.
    pub fn unwrap(self) -> Value {
        if self.root.is_some() {
            let mut obj = ::serde_json::Map::new();
            let root = self.root.as_ref().unwrap().to_string();
            let self_json = self.unwrap_internal();
            obj.insert(root, self_json);
            Value::Object(obj)
        } else {
            self.unwrap_internal()
        }
    }

    #[inline]
    fn unwrap_internal(self) -> Value {
        if self.null {
            Value::Null
        } else {
            Value::Object(self.object)
        }
    }
}

impl ObjectBuilder {
    /// Set object's `name` field with something that can be
    /// converted to Value value.
    pub fn set<V: Serialize, N: Into<String>>(&mut self, name: N, value: V) {
        self.set_json(name, to_value(&value).unwrap());
    }

    /// Stub for future use
    pub fn call<V: Serialize, N: Into<String>>(&mut self, name: N, value: V) {
        self.set(name, value);
    }
}

impl ObjectBuilder {
    /// Set object's `name` field with raw Value value.
    pub fn set_json<N: Into<String>>(&mut self, name: N, value: Value) {
        self.object.insert(name.into(), value);
    }

    /// Build new array and set object's `name` field with it.
    pub fn array<N: Into<String>, F>(&mut self, name: N, builder: F) where F: FnOnce(&mut array_builder::ArrayBuilder) {
        self.set(name.into(), array_builder::ArrayBuilder::build(builder).unwrap());
    }

    /// Build new object and set object's `name` field with it.
    pub fn object<N: Into<String>, F>(&mut self, name: N, builder: F) where F: FnOnce(&mut ObjectBuilder) {
        self.set(name.into(), ObjectBuilder::build(builder).unwrap());
    }
}

impl Serialize for ObjectBuilder {
    /// Copy self to new JSON instance.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        let json_object = if self.null { Value::Null } else { to_value(&self.object).unwrap() };
        json_object.serialize(serializer)
    }
}

