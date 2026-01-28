//! Basic usage example for iddqd with schemars.

use iddqd::{
    BiHashItem, BiHashMap, IdHashItem, IdHashMap, TriHashItem, TriHashMap,
    bi_upcast, id_upcast, tri_upcast,
};
use schemars::{JsonSchema, schema_for};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
struct User {
    name: String,
    email: String,
    age: u32,
}

impl IdHashItem for User {
    type Key<'a> = &'a str;

    fn key(&self) -> Self::Key<'_> {
        &self.name
    }

    id_upcast!();
}

impl BiHashItem for User {
    type K1<'a> = &'a str; // name
    type K2<'a> = &'a str; // email

    fn key1(&self) -> Self::K1<'_> {
        &self.name
    }

    fn key2(&self) -> Self::K2<'_> {
        &self.email
    }

    bi_upcast!();
}

impl TriHashItem for User {
    type K1<'a> = &'a str; // name
    type K2<'a> = &'a str; // email
    type K3<'a> = u32; // age

    fn key1(&self) -> Self::K1<'_> {
        &self.name
    }

    fn key2(&self) -> Self::K2<'_> {
        &self.email
    }

    fn key3(&self) -> Self::K3<'_> {
        self.age
    }

    tri_upcast!();
}

// Example container struct that uses iddqd maps with schema generation
#[derive(Serialize, Deserialize, JsonSchema)]
struct UserDatabase {
    /// Users indexed by name
    users_by_name: IdHashMap<User>,

    /// Users with bidirectional lookup by name and email
    users_bi: BiHashMap<User>,

    /// Users with three-way lookup by name, email, and age
    users_tri: TriHashMap<User>,

    /// Regular HashMap for comparison
    metadata: HashMap<String, String>,
}

fn main() {
    println!("* schemas:\n");

    // Generate schemas for individual map types.
    println!("*** schema for IdHashMap<User>:");
    let id_hash_schema = schema_for!(IdHashMap<User>);
    println!("{}\n", serde_json::to_string_pretty(&id_hash_schema).unwrap());

    println!("*** schema for BiHashMap<User>:");
    let bi_hash_schema = schema_for!(BiHashMap<User>);
    println!("{}\n", serde_json::to_string_pretty(&bi_hash_schema).unwrap());

    println!("*** schema for TriHashMap<User>:");
    let tri_hash_schema = schema_for!(TriHashMap<User>);
    println!("{}\n", serde_json::to_string_pretty(&tri_hash_schema).unwrap());

    // Generate a schema for the container struct.
    println!("schema for UserDatabase (container with multiple map types):");
    let database_schema = schema_for!(UserDatabase);
    println!("{}\n", serde_json::to_string_pretty(&database_schema).unwrap());

    let mut users = IdHashMap::new();
    users
        .insert_unique(User {
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
            age: 30,
        })
        .unwrap();
    users
        .insert_unique(User {
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
            age: 25,
        })
        .unwrap();

    println!("IdHashMap<User> serializes as:");
    println!("{}", serde_json::to_string_pretty(&users).unwrap());
}
