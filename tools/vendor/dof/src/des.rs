//! Functions to deserialize crate types from DOF.

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

use std::convert::{TryFrom, TryInto};
use std::mem::size_of;
use std::path::Path;

use goblin::Object;
use zerocopy::Ref;

use crate::dof::DOF_MAGIC;
use crate::dof_bindings::*;
use crate::{Error, Ident, Probe, Provider, Section};

// Extract one or more null-terminated strings from the given byte slice.
fn extract_strings(buf: &[u8], count: Option<usize>) -> Vec<String> {
    let chunks = buf.split(|&x| x == 0);
    if let Some(count) = count {
        chunks
            .take(count)
            .map(|chunk| String::from_utf8(chunk.to_vec()).unwrap())
            .collect()
    } else {
        chunks
            .map(|chunk| String::from_utf8(chunk.to_vec()).unwrap())
            .collect()
    }
}

// Parse a section of probes. The buffer must already be guaranteed to come from a DOF_SECT_PROBES
// section, and be the correct length.
fn parse_probe_section(
    buf: &[u8],
    strtab: &[u8],
    offsets: &[u32],
    enabled_offsets: &[u32],
    _argument_indices: &[u8],
) -> Vec<Probe> {
    let parse_probe = |buf| {
        let probe = *Ref::<_, dof_probe>::from_bytes(buf).unwrap();
        let offset_index = probe.dofpr_offidx as usize;
        let offs = (offset_index..offset_index + probe.dofpr_noffs as usize)
            .map(|index| offsets[index])
            .collect();
        let enabled_offset_index = probe.dofpr_enoffidx as usize;
        let enabled_offs = (enabled_offset_index
            ..enabled_offset_index + probe.dofpr_nenoffs as usize)
            .map(|index| enabled_offsets[index])
            .collect();
        let arg_base = probe.dofpr_nargv as usize;
        let arguments = extract_strings(&strtab[arg_base..], Some(probe.dofpr_nargc as _));
        Probe {
            name: extract_strings(&strtab[probe.dofpr_name as _..], Some(1))[0].clone(),
            function: extract_strings(&strtab[probe.dofpr_func as _..], Some(1))[0].clone(),
            address: probe.dofpr_addr,
            offsets: offs,
            enabled_offsets: enabled_offs,
            arguments,
        }
    };
    buf.chunks(size_of::<dof_probe>())
        .map(parse_probe)
        .collect()
}

// Extract the bytes of a section by index
fn extract_section<'a>(sections: &[dof_sec], index: usize, buf: &'a [u8]) -> &'a [u8] {
    let offset = sections[index].dofs_offset as usize;
    let size = sections[index].dofs_size as usize;
    &buf[offset..offset + size]
}

// Parse all provider sections
fn parse_providers(sections: &[dof_sec], buf: &[u8]) -> Vec<Provider> {
    let provider_sections = sections
        .iter()
        .filter(|sec| sec.dofs_type == DOF_SECT_PROVIDER);
    let mut providers = Vec::new();
    for section_header in provider_sections {
        let section_start = section_header.dofs_offset as usize;
        let section_size = section_header.dofs_size as usize;
        let provider =
            *Ref::<_, dof_provider>::from_bytes(&buf[section_start..section_start + section_size])
                .unwrap();

        let strtab = extract_section(sections, provider.dofpv_strtab as _, buf);
        let name = extract_strings(&strtab[provider.dofpv_name as _..], Some(1))[0].clone();

        // Extract the offset/index sections as vectors of a specific type
        let offsets: Vec<_> = extract_section(sections, provider.dofpv_proffs as _, buf)
            .chunks(size_of::<u32>())
            .map(|chunk| u32::from_ne_bytes(chunk.try_into().unwrap()))
            .collect();
        let enabled_offsets: Vec<_> = extract_section(sections, provider.dofpv_prenoffs as _, buf)
            .chunks(size_of::<u32>())
            .map(|chunk| u32::from_ne_bytes(chunk.try_into().unwrap()))
            .collect();
        let arguments = extract_section(sections, provider.dofpv_prargs as _, buf).to_vec();
        let probes_list = parse_probe_section(
            extract_section(sections, provider.dofpv_probes as _, buf),
            strtab,
            &offsets,
            &enabled_offsets,
            &arguments,
        );

        let probes = probes_list
            .into_iter()
            .map(|probe| (probe.name.clone(), probe))
            .collect();

        providers.push(Provider { name, probes });
    }
    providers
}

fn deserialize_raw_headers(buf: &[u8]) -> Result<(dof_hdr, Vec<dof_sec>), Error> {
    let file_header = *Ref::<_, dof_hdr>::from_bytes(&buf[..size_of::<dof_hdr>()])
        .map_err(|_| Error::ParseError)?;
    let n_sections: usize = file_header.dofh_secnum as _;
    let mut section_headers = Vec::with_capacity(n_sections);
    for i in 0..n_sections {
        let start = file_header.dofh_secoff as usize + file_header.dofh_secsize as usize * i;
        let end = start + file_header.dofh_secsize as usize;
        section_headers
            .push(*Ref::<_, dof_sec>::from_bytes(&buf[start..end]).map_err(|_| Error::ParseError)?);
    }
    Ok((file_header, section_headers))
}

/// Simple container for raw DOF data, including header and sections.
#[derive(Clone, Debug)]
pub struct RawSections {
    /// The DOF header.
    pub header: dof_hdr,
    /// A list of each section, along with its raw bytes.
    pub sections: Vec<(dof_sec, Vec<u8>)>,
}

/// Deserialize the raw C-structs for the file header and each section header, along with the byte
/// array for those sections.
pub fn deserialize_raw_sections(buf: &[u8]) -> Result<RawSections, Error> {
    let (file_headers, section_headers) = deserialize_raw_headers(buf)?;
    let sections = section_headers
        .into_iter()
        .map(|header| {
            let start = header.dofs_offset as usize;
            let end = start + header.dofs_size as usize;
            (header, buf[start..end].to_vec())
        })
        .collect();
    Ok(RawSections {
        header: file_headers,
        sections,
    })
}

/// Deserialize a `Section` from a slice of DOF bytes
pub fn deserialize_section(buf: &[u8]) -> Result<Section, Error> {
    let (file_header, section_headers) = deserialize_raw_headers(buf)?;
    let ident = Ident::try_from(&file_header.dofh_ident[..])?;
    let providers_list = parse_providers(&section_headers, buf);
    let providers = providers_list
        .into_iter()
        .map(|provider| (provider.name.clone(), provider))
        .collect();
    Ok(Section { ident, providers })
}

/// Return true if the given byte slice is a DOF section of an object file.
pub fn is_dof_section(buf: &[u8]) -> bool {
    buf.len() >= DOF_MAGIC.len() && buf.starts_with(&DOF_MAGIC)
}

/// Return the raw byte blobs for each DOF section in the given object file
pub fn collect_dof_sections<P: AsRef<Path>>(path: P) -> Result<Vec<Vec<u8>>, Error> {
    let data = std::fs::read(path)?;
    match Object::parse(&data)? {
        Object::Elf(elf) => Ok(elf
            .section_headers
            .iter()
            .filter_map(|section| {
                let start = section.sh_offset as usize;
                let end = start + section.sh_size as usize;
                if is_dof_section(&data[start..end]) {
                    Some(data[start..end].to_vec())
                } else {
                    None
                }
            })
            .collect()),
        Object::Mach(goblin::mach::Mach::Binary(mach)) => Ok(mach
            .segments
            .sections()
            .flatten()
            .filter_map(|item| {
                if let Ok((_, section_data)) = item {
                    if is_dof_section(section_data) {
                        Some(section_data.to_vec())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()),
        _ => Err(Error::UnsupportedObjectFile),
    }
}

/// Extract DOF sections from the given object file (ELF or Mach-O)
pub fn extract_dof_sections<P: AsRef<Path>>(path: P) -> Result<Vec<Section>, Error> {
    collect_dof_sections(path)?
        .into_iter()
        .map(|sect| Section::from_bytes(&sect))
        .collect()
}
