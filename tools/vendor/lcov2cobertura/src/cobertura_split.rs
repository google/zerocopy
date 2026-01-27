//! Module with a helper to split cobertura files into smaller chunks
use std::io::{Cursor, Write};
use std::path::Path;

use crate::XML_HEADER;
use quick_xml::events::BytesEnd;
use quick_xml::events::Event;
use quick_xml::reader::Reader;
use quick_xml::writer::Writer;

const MAX_SIZE: usize = 9_500_000; // use below 10MB to be on the safe side

/// Algorithm:
/// - read from XML file using streaming parser
/// - write to temporary bytes buffer until package tag is closed
/// - verify that buffer appended to existing outfile does not surpass desired size
/// - if surpassed, write and close current file then start new file with buffer contents
pub fn corbertura_xml_split<P: AsRef<Path>>(filename: P) -> anyhow::Result<()> {
    let source_fn = std::path::PathBuf::from(filename.as_ref());
    let mut file_no = 1;
    let mut file_size = 0;
    let mut reader = Reader::from_file(filename)?;
    reader.config_mut().trim_text(true); // should be fine for cobertura files
    loop {
        let mut target_fn = source_fn.clone();
        let target_stem = target_fn
            .file_stem()
            .ok_or_else(|| anyhow::anyhow!("no file stem"))?;
        let target_stem_str = target_stem
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("no file stem"))?
            .to_string();
        target_fn.set_file_name(format!("{}-{}.xml", target_stem_str, file_no).as_str());

        let mut buf = Vec::new();
        let mut xml_buf = Vec::with_capacity(MAX_SIZE);
        let mut coverage_head = Vec::new();
        let mut writer = Writer::new_with_indent(Cursor::new(Vec::new()), b' ', 4);
        loop {
            match reader.read_event_into(&mut buf) {
                Err(e) => anyhow::bail!("Error at position {}: {:?}", reader.buffer_position(), e),
                // exits the loop when reaching end of file
                Ok(Event::Eof) => break,
                Ok(Event::DocType(_)) | Ok(Event::Decl(_)) => (),

                // write all OK events to output
                Ok(e) => {
                    let write_event = match &e {
                        Event::Start(e) => {
                            if e.name().as_ref() == b"package" {
                                // write coverage/sources "header" to buffer for later use
                                if coverage_head.is_empty() {
                                    coverage_head.extend_from_slice(writer.get_ref().get_ref());
                                }
                            }
                            true
                        }
                        Event::End(e) => {
                            let write_file = |xml_buf: &[u8]| -> anyhow::Result<()> {
                                let mut outfile = std::fs::File::create(&target_fn)?;
                                outfile.write_all(XML_HEADER.as_bytes())?;
                                if file_no > 1 {
                                    // write first found coverage element with all attributes!
                                    // write sources with all source elements
                                    outfile.write_all(&coverage_head)?;
                                }
                                outfile.write_all(xml_buf)?;
                                Ok(())
                            };
                            if e.name().as_ref() == b"package" {
                                // important close outer tags
                                writer.write_event(Event::End(BytesEnd::new("package")))?;
                                let pos = writer.get_ref().get_ref().len();
                                //println!("ENDED {}", pos);
                                if xml_buf.len() + pos < MAX_SIZE {
                                    xml_buf.extend_from_slice(writer.get_ref().get_ref());
                                    writer =
                                        Writer::new_with_indent(Cursor::new(Vec::new()), b' ', 4);
                                } else {
                                    // too big, write out current buffer
                                    xml_buf.extend_from_slice(b"\n    </packages>\n</coverage>");
                                    write_file(&xml_buf)?;
                                    xml_buf.clear();
                                    xml_buf.extend_from_slice(writer.get_ref().get_ref());
                                    writer =
                                        Writer::new_with_indent(Cursor::new(Vec::new()), b' ', 4);
                                    file_no += 1;
                                    target_fn.set_file_name(
                                        format!("{}-{}.xml", target_stem_str, file_no).as_str(),
                                    );
                                }
                                false
                            } else if e.name().as_ref() == b"coverage" {
                                // XML finished write out current buffer
                                xml_buf.extend_from_slice(b"\n    </packages>\n</coverage>");
                                write_file(&xml_buf)?;
                                xml_buf.clear(); // not really needed but why not
                                false
                            } else {
                                true
                            }
                        }
                        _ => true,
                    };
                    if write_event {
                        writer.write_event(e)?;
                    }
                }
            }
            buf.clear();
        }

        file_size += 10_000_000;
        if file_size >= MAX_SIZE {
            file_size = 0;
            file_no += 1;
        }
        if file_no > 3 {
            break;
        }
    }
    Ok(())
}
