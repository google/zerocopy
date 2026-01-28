## What is Valico?

[![Build Status](https://travis-ci.org/rustless/valico.svg?branch=master)](https://travis-ci.org/rustless/valico)

Valico is a validation and coercion tool for JSON objects, written in Rust. It designed to be a support library for the various REST-like frameworks or other tools that need to validate and coerce JSON input from outside world.

Valico has two features:

* **DSL** — a set of simple validators and coercers inspired by [Grape]. It has built-in support for common coercers, validators and can return detailed error messages if something goes wrong.
* **JSON Schema** — An implementation of JSON Schema, based on IETF's draft v7.

References:

* http://json-schema.org
* http://json-schema.org/latest/json-schema-core.html
* http://json-schema.org/latest/json-schema-validation.html

```toml
# Cargo.toml
valico = "2"
```

[API docs](http://rustless.org/valico/doc/valico/)

## JSON Schema

It passes the entire [JSON-Schema-Test-Suite](https://github.com/json-schema/JSON-Schema-Test-Suite/tree/develop/tests/draft4) except for remoteRefs and maxLength/minLength when using unicode surrogate pairs. It also can validate your schema and give you an explanation about what is wrong in it.

### Example

~~~rust
extern crate serde_json;
extern crate valico;

use serde_json::Value;
use valico::json_schema;
use std::fs::File;

fn main() {
    let json_schema: Value = serde_json::from_reader(File::open("tests/schema/schema.json").unwrap()).unwrap();

    let mut scope = json_schema::Scope::new();
    let schema = scope.compile_and_return(json_v4_schema.clone(), false).unwrap();

    println!("Is valid: {}", schema.validate(&json_v4_schema).is_valid());
}
~~~

### JSON Schema builder

Valico goes with `valico::json_schema::schema(|scheme| { /* .. */ }) -> json::Json` function that allows to use simple DSL to generate your schemes. It allows you not to use strings and raw JSON manipulation. It also prevent some kinds of spelling and type errors.

~~~rust
builder::schema(|s| {
    s.properties(|properties| {
        properties.insert("prop1", |prop1| {
            prop1.maximum(10f64, false);
        });
    });
    s.pattern_properties(|properties| {
        properties.insert("prop.*", |prop| {
            prop.maximum(1000f64, false);
        });
    });
    s.additional_properties_schema(|additional| {
        additional.maximum(5f64, false)
    });
})
~~~

TODO more docs about JSON Schema here

## DSL

### Basic Usage

All Valico stuff is making by Builder instance. Below is a simple example showing how one can create and setup Builder:

~~~rust
let params = Builder::build(|params| {
	params.req_nested("user", Builder::list(), |params| {
		params.req_typed("name", json_dsl::string());
		params.req_typed("friend_ids", json_dsl::array_of(json_dsl::u64()))
	});
});
~~~

Later `params` instance can be used to process one or more JSON objects with it's `process` method with signature `fn process(&self, tree: &mut JsonObject) -> ValicoResult<()>`.

**Note** that Valico will **mutate** borrowed JSON value if some coercion is needed.

Example:

~~~rust
extern crate valico;
extern crate serde_json;

use valico::json_dsl;
use serde_json::{from_str, to_string_pretty};

fn main() {

    let params = json_dsl::Builder::build(|params| {
        params.req_nested("user", json_dsl::array(), |params| {
            params.req_typed("name", json_dsl::string());
            params.req_typed("friend_ids", json_dsl::array_of(json_dsl::u64()))
        });
    });

    let mut obj = from_str(r#"{"user": {"name": "Frodo", "friend_ids": ["1223"]}}"#).unwrap();

    let state = params.process(&mut obj, &None);
    if state.is_valid() {
        println!("Result object is {}", to_string_pretty(&obj).unwrap());
    } else {
        panic!("Errors during process: {:?}", state);
    }

}
~~~

Also you can look to the [specs] for more details and examples.

[specs]: https://github.com/s-panferov/valico/blob/master/tests/builder.rs

### Validation and coercion

You can define validations and coercion options for your parameters using a `Builder::build` block. Parameters can be **optional** and **required**. Requires parameters must be always present. Optional parameters can be omitted.

When parameter is present in JSON all validation and coercions will be applied and error fired if something goes wrong.

#### Builder

This functions are available in Builder to define parameters:

~~~rust

// Parameter is required, no coercion
fn req_defined(&mut self, name: &str);

// Parameter is required, with coercion
fn req_typed(&mut self, name: &str, coercer: Box<Coercer>);

// Parameter is required, with coercion and nested checks
fn req_nested(&mut self, name: &str, coercer: Box<Coercer>, nest_def: |&mut Builder|);

// Parameter is required, setup with Param DSL
fn req(&mut self, name: &str, param_builder: |&mut Param|);

// Parameter is optional, no coercion
fn opt_defined(&mut self, name: &str);

// Parameter is optional, with coercion
fn opt_typed(&mut self, name: &str, coercer: Box<Coercer>);

// Parameter is optional, with coercion and nested checks
fn opt_nested(&mut self, name: &str, coercer: Box<Coercer>, nest_def: |&mut Builder|);

// Parameter is required, setup with Param DSL
fn opt(&mut self, name: &str, param_builder: |&mut Param|);

~~~

#### Built-in Coercers

Available list of coercers:

* json_dsl::i64()
* json_dsl::u64()
* json_dsl::f64()
* json_dsl::string()
* json_dsl::boolean()
* json_dsl::null()
* json_dsl::array()
* json_dsl::array_of()
* json_dsl::encoded_array() — use it for string-encoded arrays e.g. "red,green,blue" -> ["red", "green", "blue"]
* json_dsl::encoded_array_of() — use it for string-encoded arrays of some type e.g. "1,2,3" -> [1, 2, 3]
* json_dsl::object()

Example of usage:

~~~rust
let params = Builder::build(|params| {
    params.req_typed("id", json_dsl::u64());
    params.req_typed("name", json_dsl::string());
    params.opt_typed("is_active", json_dsl::boolean());
    params.opt_typed("tags", json_dsl::array_of(json_dsl::strings()));
});
~~~

#### Nested processing

You can specify rules to nesting processing for **lists** and **objects**:

~~~rust
let params = Builder::build(|params| {
    params.req_nested("user", json_dsl::object(), |params| {
        params.req_typed("name", json_dsl::string());
        params.opt_typed("is_active", json_dsl::boolean());
        params.opt_typed("tags", json_dsl::array_of(json_dsl::strings()));
    });
});

let params = Builder::build(|params| {
    params.req_nested("users", Builder::list(), |params| {
        params.req_typed("name", json_dsl::string());
        params.opt_typed("is_active", json_dsl::boolean());
        params.opt_typed("tags", json_dsl::array_of(json_dsl::strings()));
    });
});
~~~

Nesting level is not limited in Valico.

#### Validate with JSON Schema

DSL allows to use JSON Schema validations to validate objects at the Builder level and the Param level:

~~~rust
let params = json_dsl::Builder::build(|params| {
    params.req("a", |a| {
        a.schema(|schema| {
            schema.integer();
            schema.maximum(10f64, false);
        })
    });
});
~~~

Note that JSON Schema validates object AFTER coerce pass:

~~~rust
let mut params = json_dsl::Builder::build(|params| {
    params.req("a", |a| {
        a.coerce(json_dsl::u64());
        a.schema(|schema| {
            schema.maximum(10f64, false);
        })
    });
});
~~~

Don't forget to create a `json_schema::Scope` BEFORE processing:

~~~rust
let mut scope = json_schema::Scope::new();
params.build_schemes(&mut scope).unwrap();
~~~

#### Parameters DSL

You can use DSL block to setup parameters with more flexible way:

~~~rust
let params = Builder::build(|params| {
    params.req("user", |user| {
        user.desc("Parameter is used to create new user");
        user.coerce(json_dsl::object());

        // this allows null to be a valid value
        user.allow_null();

        user.nest(|params| {
            params.req_typed("name", json_dsl::string());
            params.opt("kind", |kind| {
                kind.coerce(json_dsl::string());

                // optional parameters can have default values
                kind.default("simeple_user".to_string())
            });
        });
    });
});
~~~

#### Parameter validations

DSL supports several parameter validations. They considered outdated and likely to be **removed** in the future in favour of JSON Schema validation.

##### allow_values

Parameters can be restricted to a specific set of values with **allow_values**:

~~~rust
let params = Builder::build(|params| {
    params.req("kind", |kind| {
        kind.coerce(json_dsl::string());
        kind.allow_values(&["circle".to_string(), "square".to_string()]);
    })
})
~~~

##### reject_values

Some values can be rejected with **reject_values**:

~~~rust
let params = Builder::build(|params| {
    params.req("user_role", |kind| {
        kind.coerce(json_dsl::string());
        kind.reject_values(&["admin".to_string(), "manager".to_string()]);
    })
})
~~~

##### regex

String values can be tested with Regex:

~~~rust
let params = Builder::build(|params| {
    params.req("nickname", |a| {
        a.coerce(json_dsl::string());

        // force all nicknames to start with "Amazing"
        a.regex(regex!("^Amazing"));
    })
});
~~~

##### validate_with

Sometimes it's usefull to use some custom function as validator:

~~~rust
let params = Builder::build(|params| {
    params.req("pushkin_birthday", |a| {
        a.coerce(json_dsl::u64());

        fn guess(val: &Json) -> Result<(), String> {
            if *val == 1799u.to_json() {
                Ok(())
            } else {
                Err("No!".to_string())
            }
        }

        a.validate_with(guess);
    });
});
~~~

##### validate

One can use custom validator. Docs in Progress.

#### Builder validations

Some validators can be specified in Builder DSL block to validate a set of parameters.

##### mutually_exclusive

Parameters can be defined as mutually_exclusive, ensuring that they aren't present at the same time in a request.

~~~rust
let params = Builder::build(|params| {
    params.opt_defined("vodka");
    params.opt_defined("beer");

    params.mutually_exclusive(&["vodka", "beer"]);
});
~~~

Multiple sets can be defined:

~~~rust
let params = Builder::build(|params| {
    params.opt_defined("vodka");
    params.opt_defined("beer");
    params.mutually_exclusive(&["vodka", "beer"]);

    params.opt_defined("lard");
    params.opt_defined("jamon");
    params.mutually_exclusive(&["lard", "jamon"]);
});
~~~

**Warning**: Never define mutually exclusive sets with any required params. Two mutually exclusive required params will mean params are never valid. One required param mutually exclusive with an optional param will mean the latter is never valid.

##### exactly_one_of

Parameters can be defined as 'exactly_one_of', ensuring that exactly one parameter gets selected.

~~~rust
let params = Builder::build(|params| {
    params.opt_defined("vodka");
    params.opt_defined("beer");
    params.exactly_one_of(["vodka", "beer"]);
});
~~~

##### at_least_one_of

Parameters can be defined as 'at_least_one_of', ensuring that at least one parameter gets selected.

~~~rust
let params = Builder::build(|params| {
    params.opt_defined("vodka");
    params.opt_defined("beer");
    params.opt_defined("wine");
    params.exactly_one_of(["vodka", "beer", "wine"]);
});
~~~

##### validate_with

Sometimes it's usefull to use some custom function as validator:

~~~rust
let params = Builder::build(|params| {
    params.req_defined("monster_name");

    fn validate_params(_: &JsonObject) -> Result<(),String> {
        Err("YOU SHALL NOT PASS".to_string())
    }

    params.validate_with(validate_params);
});
~~~

##### validate

One can use custom validator. Docs in Progress.

## Building for other targets

### Web Assembly

For WebAssembly, enable the `js` feature:

```toml
# Cargo.toml
valico = { version = "2", features = ["js"] }
```
