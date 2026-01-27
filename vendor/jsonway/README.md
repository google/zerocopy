# JsonWay

[![Build Status](https://travis-ci.org/rustless/jsonway.svg?branch=master)](https://travis-ci.org/rustless/jsonway)

JsonWay gives you a simple DSL for declaring JSON structures.
This is particularly helpful when the generation process is fraught with conditionals and loops.
It is inspired by [jbuilder](https://github.com/rails/jbuilder) and has similar functionality.

```toml
# Cargo.toml
[dependencies.jsonway]
git = "https://github.com/rustless/jsonway"
```

[API docs](http://rustless.org/jsonway/doc/jsonway/)

## Simple example

``` rust
jsonway::object(|json| {
    json.set("first_name", "Luke".to_string());
    json.set("last_name", "Skywalker".to_string());

    json.object("info", |json| {
        json.set("homeworld", "Tatooine".to_string());
        json.set("born", "19 BBY".to_string());
        json.set("died", "Between 45 ABY and 137 ABY".to_string());
    });

    json.array("masters", |json| {
        json.push("Obi-Wan Kenobi".to_string());
        json.push("Yoda".to_string());
        json.push("Joruus C'baoth (Briefly)".to_string());
        json.push("Darth Sidious (Briefly)".to_string());
    });
});

// {
//   "first_name": "Luke",
//   "last_name": "Skywalker",
//   "info": {
//     "born": "19 BBY",
//     "died": "Between 45 ABY and 137 ABY",
//     "homeworld": "Tatooine"
//   },
//   "masters": [
//     "Obi-Wan Kenobi",
//     "Yoda",
//     "Joruus C'baoth (Briefly)",
//     "Darth Sidious (Briefly)"
//   ]
// }
```

## Build with iterators

~~~rust
#[derive(Debug)]
enum Side {
    Light,
    Dark
}

struct Jedi {
    name: String,
    side: Side
}

let jedi = vec![
    Jedi { name: "Saes Rrogon".to_string(), side: Side::Dark },
    Jedi { name: "Qui-Gon Jinn".to_string(), side: Side::Light },
    Jedi { name: "Obi-Wan Kenobi".to_string(), side: Side::Light }
];

let light_jedi_objects_list = jsonway::array(|json| {
    // Use `objects` method to make list of objects
    json.objects(&mut jedi.iter(), |jedi, json| {
        match jedi.side {
            Side::Light => {
                json.set("name".to_string(), jedi.name.to_string());
                json.set("side".to_string(), format!("{:?}", jedi.side));
            }
            Side::Dark => json.skip(),
        }
    })
});

// [
//   {
//     "name": "Qui-Gon Jinn",
//     "side": "Light"
//   },
//   {
//     "name": "Obi-Wan Kenobi",
//     "side": "Light"
//   }
// ]

let light_jedi_tuple_list = jsonway::array(|json| {
    // Use `arrays` method to make list of lists
    json.arrays(&mut jedi.iter(), |jedi, json| {
        match jedi.side {
            Side::Light => {
                json.push(jedi.name.to_string());
                json.push(format!("{:?}", jedi.side));
            }
            Side::Dark => json.skip(),
        }
    })
});

// [
//   [
//     "Qui-Gon Jinn",
//     "Light"
//   ],
//   [
//     "Obi-Wan Kenobi",
//     "Light"
//   ]
// ]

~~~

You can explicitly make `JsonWay` object return `null` if you want:

~~~rust
// ..
match jedi.side {
    Side::Light => {
        json.push(jedi.name.to_string());
        json.push(format!("{:?}", jedi.side));
    },
    Side::Dark => json.null()
}
~~~

## Serializers

### Serializier

Provides convention and functionality to create custom JSON presenters for any struct.

```rust
use jsonway::{ObjectBuilder, Serializer};

struct Jedi {
    name: String
}

struct JediSerializer<'a> {
    jedi: &'a Jedi
}

impl<'a> Serializer for JediSerializer<'a> {
    fn root(&self) -> Option<&str> { Some("jedi") }
    fn build(&self, json: &mut ObjectBuilder) {
        json.set("name", self.jedi.name.to_string());
    }
}

let jedi = Jedi { name: "Saes Rrogon".to_string() };
let json = JediSerializer{jedi: &jedi}.serialize();
```

### ObjectSerializer

`ObjectSerializer<T>` is a generic struct for single `object:T` serialization.

```rust
use jsonway::{ObjectBuilder, ObjectSerializer};

struct Jedi {
    name: String
}

struct JediSerializer;

impl ObjectSerializer<Jedi> for JediSerializer {
    fn root(&self) -> Option<&str> { Some("jedi") }
    fn build(&self, jedi: &Jedi, json: &mut ObjectBuilder) {
        json.set("name", jedi.name.to_string());
    }
}

let jedi = Jedi { name: "Saes Rrogon".to_string() };
let json = JediSerializer.serialize(&jedi);
```

### ObjectScopeSerializer

`ObjectScopeSerializer<T, S>` is a generic struct for `object:T` and `scope:S` serialization.

```rust
use jsonway::{ObjectBuilder, ObjectScopeSerializer};

struct User {
    id: uint,
    is_admin: bool
}

struct Jedi {
    name: String,
    secret: String
}

struct JediSerializer;

impl ObjectScopeSerializer<Jedi, User> for JediSerializer {
    fn root(&self) -> Option<&str> { Some("jedi") }
    fn build(&self, jedi: &Jedi, current_user: &User, json: &mut ObjectBuilder) {
        json.set("name", jedi.name.to_string());

        if current_user.is_admin {
            json.set("secret", jedi.secret.to_string());
        }
    }
}

let jedi = Jedi {
    name: "Palpatine".to_string(),
    secret: "Dark side".to_string()
};
let current_user = User { id: 1, is_admin: true };
let json = JediSerializer.serialize(&jedi, &current_user);
```

## ListSerializer

Provides convention and functionality to create custom JSON presenters for the list of resources including `meta` information.

TODO: Example
