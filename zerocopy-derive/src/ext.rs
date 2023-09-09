// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use syn::{Data, DataEnum, DataStruct, DataUnion, Type};

pub trait DataExt {
    /// Extract the types of all fields. For enums, extract the types of fields
    /// from each variant.
    fn field_types(&self) -> Vec<&Type>;
}

impl DataExt for Data {
    fn field_types(&self) -> Vec<&Type> {
        match self {
            Data::Struct(strc) => strc.field_types(),
            Data::Enum(enm) => enm.field_types(),
            Data::Union(un) => un.field_types(),
        }
    }
}

impl DataExt for DataStruct {
    fn field_types(&self) -> Vec<&Type> {
        self.fields.iter().map(|f| &f.ty).collect()
    }
}

impl DataExt for DataEnum {
    fn field_types(&self) -> Vec<&Type> {
        self.variants.iter().flat_map(|var| &var.fields).map(|f| &f.ty).collect()
    }
}

impl DataExt for DataUnion {
    fn field_types(&self) -> Vec<&Type> {
        self.fields.named.iter().map(|f| &f.ty).collect()
    }
}

pub trait EnumExt {
    fn is_c_like(&self) -> bool;
}

impl EnumExt for DataEnum {
    fn is_c_like(&self) -> bool {
        self.field_types().is_empty()
    }
}
