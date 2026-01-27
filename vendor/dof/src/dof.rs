//! Types representing DTrace Object Format data structures.
//!
//! The [`Section`] struct is used to represent a complete DTrace Object Format section as
//! contained in an object file. It contains one or more [`Provider`]s, each with one or more
//! [`Probe`]s. The `Probe` type contains all the information required to locate a probe callsite
//! within an object file.

// Copyright 2021 Oxide Computer Company
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::mem::size_of;
use std::{
    collections::BTreeMap,
    convert::{TryFrom, TryInto},
};

use serde::Serialize;
use thiserror::Error;

// Magic bytes for a DOF section
pub(crate) const DOF_MAGIC: [u8; 4] = [0x7F, b'D', b'O', b'F'];

/// Errors related to building or manipulating the DOF format
#[derive(Error, Debug)]
pub enum Error {
    /// The DOF identifier is invalid, such as invalid magic bytes
    #[error("invalid DOF identifier (magic bytes, endianness, or version)")]
    InvalidIdentifier,

    /// An error occurred parsing a type from an underlying byte slice
    #[error("data does not match expected struct layout or is misaligned")]
    ParseError,

    /// Attempt to read from an unsupported object file format
    #[error("unsupported object file format")]
    UnsupportedObjectFile,

    /// An error related to parsing the object file
    #[cfg(feature = "des")]
    #[error(transparent)]
    ObjectError(#[from] goblin::error::Error),

    /// An error during IO
    #[error(transparent)]
    IO(#[from] std::io::Error),
}

/// Represents the DTrace data model, e.g. the pointer width of the platform
#[derive(Debug, Clone, Copy, Serialize)]
#[repr(u8)]
pub enum DataModel {
    None = 0,
    ILP32 = 1,
    LP64 = 2,
}

impl Default for DataModel {
    fn default() -> Self {
        if cfg!(target_pointer_width = "64") {
            DataModel::LP64
        } else {
            DataModel::ILP32
        }
    }
}

impl TryFrom<u8> for DataModel {
    type Error = Error;
    fn try_from(x: u8) -> Result<Self, Self::Error> {
        match x {
            0 => Ok(DataModel::None),
            1 => Ok(DataModel::ILP32),
            2 => Ok(DataModel::LP64),
            _ => Err(Error::InvalidIdentifier),
        }
    }
}

/// Represents the endianness of the platform
#[derive(Debug, Clone, Copy, Serialize)]
#[repr(u8)]
pub enum DataEncoding {
    None = 0,
    LittleEndian = 1,
    BigEndian = 2,
}

impl Default for DataEncoding {
    fn default() -> Self {
        if cfg!(target_endian = "big") {
            DataEncoding::BigEndian
        } else {
            DataEncoding::LittleEndian
        }
    }
}

impl TryFrom<u8> for DataEncoding {
    type Error = Error;
    fn try_from(x: u8) -> Result<Self, Self::Error> {
        match x {
            0 => Ok(DataEncoding::None),
            1 => Ok(DataEncoding::LittleEndian),
            2 => Ok(DataEncoding::BigEndian),
            _ => Err(Error::InvalidIdentifier),
        }
    }
}

/// Static identifying information about a DOF section (such as version numbers)
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Ident {
    pub magic: [u8; 4],
    pub model: DataModel,
    pub encoding: DataEncoding,
    pub version: u8,
    pub dif_vers: u8,
    pub dif_ireg: u8,
    pub dif_treg: u8,
}

impl<'a> TryFrom<&'a [u8]> for Ident {
    type Error = Error;
    fn try_from(buf: &'a [u8]) -> Result<Self, Self::Error> {
        if buf.len() < size_of::<Ident>() {
            return Err(Error::ParseError);
        }
        let magic = &buf[..DOF_MAGIC.len()];
        if magic != DOF_MAGIC {
            return Err(Error::InvalidIdentifier);
        }
        let model = DataModel::try_from(buf[crate::dof_bindings::DOF_ID_MODEL as usize])?;
        let encoding = DataEncoding::try_from(buf[crate::dof_bindings::DOF_ID_ENCODING as usize])?;
        let version = buf[crate::dof_bindings::DOF_ID_VERSION as usize];
        let dif_vers = buf[crate::dof_bindings::DOF_ID_DIFVERS as usize];
        let dif_ireg = buf[crate::dof_bindings::DOF_ID_DIFIREG as usize];
        let dif_treg = buf[crate::dof_bindings::DOF_ID_DIFTREG as usize];
        Ok(Ident {
            // Unwrap is safe if the above check against DOF_MAGIC passes
            magic: magic.try_into().unwrap(),
            model,
            encoding,
            version,
            dif_vers,
            dif_ireg,
            dif_treg,
        })
    }
}

impl Ident {
    pub fn as_bytes(&self) -> [u8; 16] {
        let mut out = [0; 16];
        let start = self.magic.len();
        out[..start].copy_from_slice(&self.magic[..]);
        out[start] = self.model as _;
        out[start + 1] = self.encoding as _;
        out[start + 2] = self.version;
        out[start + 3] = self.dif_vers;
        out[start + 4] = self.dif_ireg;
        out[start + 5] = self.dif_treg;
        out
    }
}

/// Representation of a DOF section of an object file
#[derive(Debug, Clone, Serialize)]
pub struct Section {
    /// The identifying bytes of this section
    pub ident: Ident,
    /// The list of providers defined in this section
    pub providers: BTreeMap<String, Provider>,
}

impl Section {
    /// Construct a section from a DOF byte array.
    #[cfg(feature = "des")]
    pub fn from_bytes(buf: &[u8]) -> Result<Section, Error> {
        crate::des::deserialize_section(buf)
    }

    /// Serialize a section into DOF object file section.
    pub fn as_bytes(&self) -> Vec<u8> {
        crate::ser::serialize_section(self)
    }

    /// Serialize a section into a JSON representation of the DOF object file section.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
}

impl Default for Section {
    fn default() -> Self {
        Self {
            ident: Ident {
                magic: DOF_MAGIC,
                model: DataModel::LP64,
                encoding: DataEncoding::LittleEndian,
                version: crate::dof_bindings::DOF_VERSION as u8,
                dif_vers: crate::dof_bindings::DIF_VERSION as u8,
                dif_ireg: crate::dof_bindings::DIF_DIR_NREGS as u8,
                dif_treg: crate::dof_bindings::DIF_DTR_NREGS as u8,
            },
            providers: BTreeMap::new(),
        }
    }
}

/// Information about a single DTrace probe
#[derive(Debug, Clone, Serialize)]
pub struct Probe {
    /// Name of this probe
    pub name: String,
    /// Name of the function containing this probe
    pub function: String,
    /// Address or offset in the resulting object code
    pub address: u64,
    /// Offsets in containing function at which this probe occurs.
    pub offsets: Vec<u32>,
    /// Offsets in the containing function at which this probe's is-enabled functions occur.
    pub enabled_offsets: Vec<u32>,
    /// Type information for each argument
    pub arguments: Vec<String>,
}

/// Information about a single provider
#[derive(Debug, Clone, Serialize)]
pub struct Provider {
    /// Name of the provider
    pub name: String,
    /// List of probes this provider exports
    pub probes: BTreeMap<String, Probe>,
}
