//! Functions to serialize crate types into DOF.

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

use zerocopy::IntoBytes;

use crate::dof_bindings::*;
use crate::Section;

// Build the binary data for each section of a serialized Section object, as a vector of
// (section_type, section_data) tuples.
fn build_section_data(section: &Section) -> Vec<(u32, Vec<u8>)> {
    let mut probe_sections = Vec::new();
    let mut provider_sections = Vec::new();
    let mut strings = Vec::<u8>::new();
    strings.push(0); // starts with a NULL byte
    let mut arguments = Vec::<u8>::new();
    let mut offsets = Vec::new();
    let mut enabled_offsets = Vec::new();

    for (i, provider) in section.providers.values().enumerate() {
        let mut provider_section = dof_provider {
            dofpv_name: strings.len() as _,
            ..Default::default()
        };
        strings.extend_from_slice(provider.name.as_bytes());
        strings.push(0);

        // Links to the constituent sections for this provider. Note that the probes are all placed
        // first, with one section (array of probes) for each provider.
        provider_section.dofpv_strtab = 0;
        provider_section.dofpv_prargs = 1;
        provider_section.dofpv_proffs = 2;
        provider_section.dofpv_prenoffs = 3;
        provider_section.dofpv_probes = (4 + i) as _;

        let mut probe_section = Vec::with_capacity(provider.probes.len() * size_of::<dof_probe>());
        for probe in provider.probes.values() {
            let mut probe_t = dof_probe {
                dofpr_addr: probe.address,
                ..Default::default()
            };

            // Insert function name and store strtab index
            probe_t.dofpr_func = strings.len() as _;
            strings.extend_from_slice(probe.function.as_bytes());
            strings.push(0);

            // Insert probe name and store strtab index
            probe_t.dofpr_name = strings.len() as _;
            strings.extend_from_slice(probe.name.as_bytes());
            strings.push(0);

            // Insert argument strings and store strtab indices
            probe_t.dofpr_argidx = arguments.len() as _;
            let argv = strings.len() as u32;
            for (i, arg) in probe.arguments.iter().enumerate() {
                strings.extend_from_slice(arg.as_bytes());
                strings.push(0);
                arguments.push(i as _);
            }
            probe_t.dofpr_nargv = argv;
            probe_t.dofpr_nargc = probe.arguments.len() as _;
            probe_t.dofpr_xargv = argv;
            probe_t.dofpr_xargc = probe.arguments.len() as _;

            // Insert probe offsets and store indices
            probe_t.dofpr_offidx = offsets.len() as _;
            offsets.extend_from_slice(&probe.offsets);
            probe_t.dofpr_noffs = probe.offsets.len() as _;

            // Insert is-enabled offset and store indices
            probe_t.dofpr_enoffidx = enabled_offsets.len() as _;
            enabled_offsets.extend_from_slice(&probe.enabled_offsets);
            probe_t.dofpr_nenoffs = probe.enabled_offsets.len() as _;

            probe_section.extend_from_slice(probe_t.as_bytes());
        }
        probe_sections.push(probe_section);
        provider_sections.push(provider_section.as_bytes().to_vec());
    }

    // Construct the string table.
    let mut section_data = Vec::with_capacity(4 + 2 * probe_sections.len());
    section_data.push((DOF_SECT_STRTAB, strings));

    // Construct the argument mappings table
    if arguments.is_empty() {
        arguments.push(0);
    }
    section_data.push((DOF_SECT_PRARGS, arguments));

    // Construct the offset table
    let offset_section = offsets
        .iter()
        .flat_map(|offset| offset.to_ne_bytes().to_vec())
        .collect::<Vec<_>>();
    section_data.push((DOF_SECT_PROFFS, offset_section));

    // Construct enabled offset table
    let enabled_offset_section = enabled_offsets
        .iter()
        .flat_map(|offset| offset.to_ne_bytes().to_vec())
        .collect::<Vec<_>>();
    section_data.push((DOF_SECT_PRENOFFS, enabled_offset_section));

    // Push remaining probe and provider data. They must be done in this order so the indices to
    // the probe section for each provider is accurate.
    for probe_section in probe_sections.into_iter() {
        section_data.push((DOF_SECT_PROBES, probe_section));
    }
    for provider_section in provider_sections.into_iter() {
        section_data.push((DOF_SECT_PROVIDER, provider_section));
    }

    section_data
}

fn build_section_headers(
    sections: Vec<(u32, Vec<u8>)>,
    mut offset: usize,
) -> (Vec<dof_sec>, Vec<Vec<u8>>, usize) {
    let mut section_headers = Vec::with_capacity(sections.len());
    let mut section_data = Vec::<Vec<u8>>::with_capacity(sections.len());

    for (sec_type, data) in sections.into_iter() {
        // Different sections expect different alignment and entry sizes.
        let (alignment, entry_size) = match sec_type {
            DOF_SECT_STRTAB | DOF_SECT_PRARGS => (1, 1),
            DOF_SECT_PROFFS | DOF_SECT_PRENOFFS => (size_of::<u32>(), size_of::<u32>()),
            DOF_SECT_PROVIDER => (size_of::<u32>(), 0),
            DOF_SECT_PROBES => (size_of::<u64>(), size_of::<dof_probe>()),
            _ => unimplemented!(),
        };

        // Pad the data of the *previous* section as needed. Note that this space
        // is not accounted for by the dofs_size field of any section, but it
        // is--of course--part of the total dofh_filesz.
        if offset % alignment > 0 {
            let padding = alignment - offset % alignment;
            section_data.last_mut().unwrap().extend(vec![0; padding]);
            offset += padding;
        }

        let header = dof_sec {
            dofs_type: sec_type,
            dofs_align: alignment as u32,
            dofs_flags: DOF_SECF_LOAD,
            dofs_entsize: entry_size as u32,
            dofs_offset: offset as u64,
            dofs_size: data.len() as u64,
        };

        offset += data.len();
        section_headers.push(header);
        section_data.push(data);
    }

    (section_headers, section_data, offset)
}

/// Serialize a Section into a vector of DOF bytes
pub fn serialize_section(section: &Section) -> Vec<u8> {
    let sections = build_section_data(section);
    let hdr_size = size_of::<dof_hdr>() + sections.len() * size_of::<dof_sec>();
    let (section_headers, section_data, size) = build_section_headers(sections, hdr_size);

    let header = dof_hdr {
        dofh_ident: section.ident.as_bytes(),
        dofh_flags: 0,
        dofh_hdrsize: size_of::<dof_hdr>() as _,
        dofh_secsize: size_of::<dof_sec>() as _,
        dofh_secnum: section_headers.len() as _,
        dofh_secoff: size_of::<dof_hdr>() as _,
        dofh_loadsz: size as _,
        dofh_filesz: size as _,
        dofh_pad: 0,
    };

    let mut file_data = Vec::with_capacity(header.dofh_filesz as _);
    file_data.extend(header.as_bytes());
    for header in section_headers.into_iter() {
        file_data.extend(header.as_bytes());
    }
    for data in section_data.into_iter() {
        file_data.extend(data);
    }
    file_data
}

#[cfg(test)]
mod test {
    use super::build_section_headers;
    use crate::dof_bindings::*;
    #[test]
    fn test_padding() {
        let sections = vec![
            (DOF_SECT_STRTAB, vec![96_u8]),
            (DOF_SECT_PROFFS, vec![0x11_u8, 0x22_u8, 0x33_u8, 0x44_u8]),
        ];

        assert_eq!(sections[0].1.len(), 1);

        let (_, section_data, size) = build_section_headers(sections, 0);

        assert_eq!(section_data[0].len(), 4);
        assert_eq!(size, 8);
    }
}
