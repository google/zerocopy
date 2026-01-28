#[cfg(test)]
use alloc::vec;

#[cfg(test)]
use alloc::vec::Vec;

#[cfg(test)]
extern crate std;

#[cfg(all(test, not(feature = "std")))]
impl crate::io_nostd::Read for std::fs::File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, crate::io_nostd::Error> {
        std::io::Read::read(self, buf).map_err(|e| {
            if e.get_ref().is_none() {
                crate::io_nostd::Error::from(crate::io_nostd::ErrorKind::Other)
            } else {
                crate::io_nostd::Error::new(
                    crate::io_nostd::ErrorKind::Other,
                    alloc::boxed::Box::new(e.into_inner().unwrap()),
                )
            }
        })
    }
}

#[cfg(all(test, feature = "std"))]
#[allow(dead_code)]
fn assure_error_impl() {
    // not a real test just there to throw an compiler error if Error is not derived correctly

    use crate::decoding::errors::FrameDecoderError;
    let _err: &dyn std::error::Error = &FrameDecoderError::NotYetInitialized;
}

#[cfg(all(test, feature = "std"))]
#[allow(dead_code)]
fn assure_decoder_send_sync() {
    // not a real test just there to throw an compiler error if FrameDecoder is Send + Sync

    use crate::decoding::FrameDecoder;
    let decoder = FrameDecoder::new();
    std::thread::spawn(move || {
        drop(decoder);
    });
}

#[test]
fn skippable_frame() {
    use crate::decoding::errors;
    use crate::decoding::frame;

    let mut content = vec![];
    content.extend_from_slice(&0x184D2A50u32.to_le_bytes());
    content.extend_from_slice(&300u32.to_le_bytes());
    assert_eq!(8, content.len());
    let err = frame::read_frame_header(content.as_slice());
    assert!(matches!(
        err,
        Err(errors::ReadFrameHeaderError::SkipFrame {
            magic_number: 0x184D2A50u32,
            length: 300
        })
    ));

    content.clear();
    content.extend_from_slice(&0x184D2A5Fu32.to_le_bytes());
    content.extend_from_slice(&0xFFFFFFFFu32.to_le_bytes());
    assert_eq!(8, content.len());
    let err = frame::read_frame_header(content.as_slice());
    assert!(matches!(
        err,
        Err(errors::ReadFrameHeaderError::SkipFrame {
            magic_number: 0x184D2A5Fu32,
            length: 0xFFFFFFFF
        })
    ));
}

#[cfg(test)]
#[test]
fn test_frame_header_reading() {
    use crate::decoding::frame;
    use std::fs;

    let mut content = fs::File::open("./decodecorpus_files/z000088.zst").unwrap();
    let (_frame, _) = frame::read_frame_header(&mut content).unwrap();
}

#[test]
fn test_block_header_reading() {
    use crate::decoding;
    use crate::decoding::frame;
    use std::fs;

    let mut content = fs::File::open("./decodecorpus_files/z000088.zst").unwrap();
    let (_frame, _) = frame::read_frame_header(&mut content).unwrap();

    let mut block_dec = decoding::block_decoder::new();
    let block_header = block_dec.read_block_header(&mut content).unwrap();
    let _ = block_header; //TODO validate blockheader in a smart way
}

#[test]
fn test_frame_decoder() {
    use crate::decoding::BlockDecodingStrategy;
    use crate::decoding::FrameDecoder;
    use std::fs;

    let mut content = fs::File::open("./decodecorpus_files/z000088.zst").unwrap();

    struct NullWriter(());
    impl std::io::Write for NullWriter {
        fn write(&mut self, buf: &[u8]) -> Result<usize, std::io::Error> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> Result<(), std::io::Error> {
            Ok(())
        }
    }
    let mut _null_target = NullWriter(());

    let mut frame_dec = FrameDecoder::new();
    frame_dec.reset(&mut content).unwrap();
    frame_dec
        .decode_blocks(&mut content, BlockDecodingStrategy::All)
        .unwrap();
}

#[test]
fn test_decode_from_to() {
    use crate::decoding::FrameDecoder;
    use std::fs::File;
    use std::io::BufReader;
    use std::io::Read;
    let f = BufReader::new(File::open("./decodecorpus_files/z000088.zst").unwrap());
    let mut frame_dec = FrameDecoder::new();

    let content: Vec<u8> = f.bytes().map(|x| x.unwrap()).collect();

    let mut target = vec![0u8; 1024 * 1024];

    // first part
    let source1 = &content[..50 * 1024];
    let (read1, written1) = frame_dec
        .decode_from_to(source1, target.as_mut_slice())
        .unwrap();

    //second part explicitely without checksum
    let source2 = &content[read1..content.len() - 4];
    let (read2, written2) = frame_dec
        .decode_from_to(source2, &mut target[written1..])
        .unwrap();

    //must have decoded until checksum
    assert!(read1 + read2 == content.len() - 4);

    //insert checksum separatly to test that this is handled correctly
    let chksum_source = &content[read1 + read2..];
    let (read3, written3) = frame_dec
        .decode_from_to(chksum_source, &mut target[written1 + written2..])
        .unwrap();

    //this must result in these values because just the checksum was processed
    assert!(read3 == 4);
    assert!(written3 == 0);

    let read = read1 + read2 + read3;
    let written = written1 + written2;

    let result = &target.as_slice()[..written];

    if read != content.len() {
        panic!(
            "Byte counter: {} was wrong. Should be: {}",
            read,
            content.len()
        );
    }

    match frame_dec.get_checksum_from_data() {
        Some(chksum) => {
            #[cfg(feature = "hash")]
            if frame_dec.get_calculated_checksum().unwrap() != chksum {
                std::println!(
                    "Checksum did not match! From data: {}, calculated while decoding: {}\n",
                    chksum,
                    frame_dec.get_calculated_checksum().unwrap()
                );
            } else {
                std::println!("Checksums are ok!\n");
            }
            #[cfg(not(feature = "hash"))]
            std::println!(
                "Checksum feature not enabled, skipping. From data: {}\n",
                chksum
            );
        }
        None => std::println!("No checksums to test\n"),
    }

    let original_f = BufReader::new(File::open("./decodecorpus_files/z000088").unwrap());
    let original: Vec<u8> = original_f.bytes().map(|x| x.unwrap()).collect();

    if original.len() != result.len() {
        panic!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        panic!("Result differs in at least {} bytes from original", counter);
    }
}

#[test]
fn test_specific_file() {
    use crate::decoding::BlockDecodingStrategy;
    use crate::decoding::FrameDecoder;
    use std::fs;
    use std::io::BufReader;
    use std::io::Read;

    let path = "./decodecorpus_files/z000068.zst";
    let mut content = fs::File::open(path).unwrap();

    struct NullWriter(());
    impl std::io::Write for NullWriter {
        fn write(&mut self, buf: &[u8]) -> Result<usize, std::io::Error> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> Result<(), std::io::Error> {
            Ok(())
        }
    }
    let mut _null_target = NullWriter(());

    let mut frame_dec = FrameDecoder::new();
    frame_dec.reset(&mut content).unwrap();
    frame_dec
        .decode_blocks(&mut content, BlockDecodingStrategy::All)
        .unwrap();
    let result = frame_dec.collect().unwrap();

    let original_f = BufReader::new(fs::File::open("./decodecorpus_files/z000088").unwrap());
    let original: Vec<u8> = original_f.bytes().map(|x| x.unwrap()).collect();

    std::println!("Results for file: {path}");

    if original.len() != result.len() {
        std::println!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        std::println!("Result differs in at least {counter} bytes from original");
    }
}

#[test]
#[cfg(feature = "std")]
fn test_streaming() {
    use std::fs;
    use std::io::BufReader;
    use std::io::Read;

    let mut content = fs::File::open("./decodecorpus_files/z000088.zst").unwrap();
    let mut stream = crate::decoding::StreamingDecoder::new(&mut content).unwrap();

    let mut result = Vec::new();
    Read::read_to_end(&mut stream, &mut result).unwrap();

    let original_f = BufReader::new(fs::File::open("./decodecorpus_files/z000088").unwrap());
    let original: Vec<u8> = original_f.bytes().map(|x| x.unwrap()).collect();

    if original.len() != result.len() {
        panic!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        panic!("Result differs in at least {} bytes from original", counter);
    }

    // Test resetting to a new file while keeping the old decoder

    let mut content = fs::File::open("./decodecorpus_files/z000068.zst").unwrap();
    let mut stream = crate::decoding::StreamingDecoder::new_with_decoder(
        &mut content,
        stream.into_frame_decoder(),
    )
    .unwrap();

    let mut result = Vec::new();
    Read::read_to_end(&mut stream, &mut result).unwrap();

    let original_f = BufReader::new(fs::File::open("./decodecorpus_files/z000068").unwrap());
    let original: Vec<u8> = original_f.bytes().map(|x| x.unwrap()).collect();

    std::println!("Results for file:");

    if original.len() != result.len() {
        panic!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        panic!("Result differs in at least {} bytes from original", counter);
    }
}

#[test]
fn test_incremental_read() {
    use crate::decoding::FrameDecoder;

    let mut unread_compressed_content =
        include_bytes!("../../decodecorpus_files/abc.txt.zst").as_slice();

    let mut frame_dec = FrameDecoder::new();
    frame_dec.reset(&mut unread_compressed_content).unwrap();

    let mut output = [0u8; 3];
    let (_, written) = frame_dec
        .decode_from_to(unread_compressed_content, &mut output)
        .unwrap();

    assert_eq!(written, 3);
    assert_eq!(output.map(char::from), ['a', 'b', 'c']);

    assert!(frame_dec.is_finished());
    let written = frame_dec.collect_to_writer(&mut &mut output[..]).unwrap();
    assert_eq!(written, 3);
    assert_eq!(output.map(char::from), ['d', 'e', 'f']);
}

#[test]
#[cfg(not(feature = "std"))]
fn test_streaming_no_std() {
    use crate::io::Read;

    let content = include_bytes!("../../decodecorpus_files/z000088.zst");
    let mut content = content.as_slice();
    let mut stream = crate::decoding::StreamingDecoder::new(&mut content).unwrap();

    let original = include_bytes!("../../decodecorpus_files/z000088");
    let mut result = vec![0; original.len()];
    Read::read_exact(&mut stream, &mut result).unwrap();

    if original.len() != result.len() {
        panic!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        panic!("Result differs in at least {} bytes from original", counter);
    }

    // Test resetting to a new file while keeping the old decoder

    let content = include_bytes!("../../decodecorpus_files/z000068.zst");
    let mut content = content.as_slice();
    let mut stream = crate::decoding::StreamingDecoder::new_with_decoder(
        &mut content,
        stream.into_frame_decoder(),
    )
    .unwrap();

    let original = include_bytes!("../../decodecorpus_files/z000068");
    let mut result = vec![0; original.len()];
    Read::read_exact(&mut stream, &mut result).unwrap();

    std::println!("Results for file:");

    if original.len() != result.len() {
        panic!(
            "Result has wrong length: {}, should be: {}",
            result.len(),
            original.len()
        );
    }

    let mut counter = 0;
    let min = if original.len() < result.len() {
        original.len()
    } else {
        result.len()
    };
    for idx in 0..min {
        if original[idx] != result[idx] {
            counter += 1;
            //std::println!(
            //    "Original {:3} not equal to result {:3} at byte: {}",
            //    original[idx], result[idx], idx,
            //);
        }
    }
    if counter > 0 {
        panic!("Result differs in at least {} bytes from original", counter);
    }
}

#[test]
fn test_decode_all() {
    use crate::decoding::errors::FrameDecoderError;
    use crate::decoding::FrameDecoder;

    let skip_frame = |input: &mut Vec<u8>, length: usize| {
        input.extend_from_slice(&0x184D2A50u32.to_le_bytes());
        input.extend_from_slice(&(length as u32).to_le_bytes());
        input.resize(input.len() + length, 0);
    };

    let mut original = Vec::new();
    let mut input = Vec::new();

    skip_frame(&mut input, 300);
    input.extend_from_slice(include_bytes!("../../decodecorpus_files/z000089.zst"));
    original.extend_from_slice(include_bytes!("../../decodecorpus_files/z000089"));
    skip_frame(&mut input, 400);
    input.extend_from_slice(include_bytes!("../../decodecorpus_files/z000090.zst"));
    original.extend_from_slice(include_bytes!("../../decodecorpus_files/z000090"));
    skip_frame(&mut input, 500);

    let mut decoder = FrameDecoder::new();

    // decode_all with correct buffers.
    let mut output = vec![0; original.len()];
    let result = decoder.decode_all(&input, &mut output).unwrap();
    assert_eq!(result, original.len());
    assert_eq!(output, original);

    // decode_all with smaller output length.
    let mut output = vec![0; original.len() - 1];
    let result = decoder.decode_all(&input, &mut output);
    assert!(
        matches!(result, Err(FrameDecoderError::TargetTooSmall)),
        "{:?}",
        result
    );

    // decode_all with larger output length.
    let mut output = vec![0; original.len() + 1];
    let result = decoder.decode_all(&input, &mut output).unwrap();
    assert_eq!(result, original.len());
    assert_eq!(&output[..result], original);

    // decode_all with truncated regular frame.
    let mut output = vec![0; original.len()];
    let result = decoder.decode_all(&input[..input.len() - 600], &mut output);
    assert!(
        matches!(result, Err(FrameDecoderError::FailedToReadBlockBody(_))),
        "{:?}",
        result
    );

    // decode_all with truncated skip frame.
    let mut output = vec![0; original.len()];
    let result = decoder.decode_all(&input[..input.len() - 1], &mut output);
    assert!(
        matches!(result, Err(FrameDecoderError::FailedToSkipFrame)),
        "{:?}",
        result
    );

    // decode_all_to_vec with correct output capacity.
    let mut output = Vec::new();
    output.reserve_exact(original.len());
    decoder.decode_all_to_vec(&input, &mut output).unwrap();
    assert_eq!(output, original);

    // decode_all_to_vec with smaller output capacity.
    let mut output = Vec::new();
    output.reserve_exact(original.len() - 1);
    let result = decoder.decode_all_to_vec(&input, &mut output);
    assert!(
        matches!(result, Err(FrameDecoderError::TargetTooSmall)),
        "{:?}",
        result
    );

    // decode_all_to_vec with larger output capacity.
    let mut output = Vec::new();
    output.reserve_exact(original.len() + 1);
    decoder.decode_all_to_vec(&input, &mut output).unwrap();
    assert_eq!(output, original);
}

pub mod bit_reader;
pub mod decode_corpus;
pub mod dict_test;
#[cfg(feature = "std")]
pub mod encode_corpus;
pub mod fuzz_regressions;

#[cfg(feature = "std")]
#[test]
fn verbose_disabled() {
    use crate::VERBOSE;
    assert_eq!(VERBOSE, false);
}
