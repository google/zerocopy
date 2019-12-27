// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use syn::{Data, DataEnum, DataStruct, DataUnion, Field, Fields, Type};

pub trait DataExt {
    fn nested_types(&self) -> Vec<&Type>;
}

impl DataExt for Data {
    fn nested_types(&self) -> Vec<&Type> {
        match self {
            Data::Struct(strc) => strc.nested_types(),
            Data::Enum(enm) => enm.nested_types(),
            Data::Union(un) => un.nested_types(),
        }
    }
}

impl DataExt for DataStruct {
    fn nested_types(&self) -> Vec<&Type> {
        fields_to_types(&self.fields)
    }
}

impl DataExt for DataEnum {
    fn nested_types(&self) -> Vec<&Type> {
        self.variants.iter().map(|var| fields_to_types(&var.fields)).fold(Vec::new(), |mut a, b| {
            a.extend(b);
            a
        })
    }
}

pub trait EnumExt {
    fn is_c_like(&self) -> bool;
}

impl EnumExt for DataEnum {
    fn is_c_like(&self) -> bool {
        self.nested_types().is_empty()
    }
}

impl DataExt for DataUnion {
    fn nested_types(&self) -> Vec<&Type> {
        field_iter_to_types(&self.fields.named)
    }
}

fn fields_to_types(fields: &Fields) -> Vec<&Type> {
    match fields {
        Fields::Named(named) => field_iter_to_types(&named.named),
        Fields::Unnamed(unnamed) => field_iter_to_types(&unnamed.unnamed),
        Fields::Unit => Vec::new(),
    }
}

fn field_iter_to_types<'a, I: IntoIterator<Item = &'a Field>>(fields: I) -> Vec<&'a Type> {
    fields.into_iter().map(|f| &f.ty).collect()
}
