#[test]
fn test_encode_corpus_files_uncompressed_our_decompressor() {
    extern crate std;
    use crate::encoding::FrameCompressor;
    use alloc::borrow::ToOwned;
    use alloc::vec::Vec;
    use std::ffi::OsStr;
    use std::fs;
    use std::io::Read;
    use std::path::PathBuf;
    use std::println;

    let mut failures: Vec<PathBuf> = Vec::new();
    let mut files: Vec<_> = fs::read_dir("./decodecorpus_files").unwrap().collect();
    if fs::read_dir("./local_corpus_files").is_ok() {
        files.extend(fs::read_dir("./local_corpus_files").unwrap());
    }

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    for entry in files.iter().map(|f| f.as_ref().unwrap()) {
        let path = entry.path();
        if path.extension() == Some(OsStr::new("zst")) {
            continue;
        }

        println!("Trying file: {path:?}");
        let input = fs::read(entry.path()).unwrap();
        let mut compressed_file: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(crate::encoding::CompressionLevel::Fastest);
        compressor.set_source(input.as_slice());
        compressor.set_drain(&mut compressed_file);

        compressor.compress();
        let mut decompressed_output = Vec::new();
        let mut decoder =
            crate::decoding::StreamingDecoder::new(compressed_file.as_slice()).unwrap();
        decoder.read_to_end(&mut decompressed_output).unwrap();

        if input != decompressed_output {
            failures.push(path);
        }
    }

    if !failures.is_empty() {
        panic!(
            "Decompression of compressed file failed on the following files: {:?}",
            failures
        );
    }
}

#[test]
fn test_encode_corpus_files_uncompressed_original_decompressor() {
    extern crate std;
    use crate::encoding::FrameCompressor;
    use alloc::borrow::ToOwned;
    use alloc::format;
    use alloc::vec::Vec;
    use std::ffi::OsStr;
    use std::fs;
    use std::path::PathBuf;
    use std::println;
    use std::string::String;

    let mut failures: Vec<(PathBuf, String)> = Vec::new();
    let mut files: Vec<_> = fs::read_dir("./decodecorpus_files").unwrap().collect();
    if fs::read_dir("./local_corpus_files").is_ok() {
        files.extend(fs::read_dir("./local_corpus_files").unwrap());
    }

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    for entry in files.iter().map(|f| f.as_ref().unwrap()) {
        let path = entry.path();
        if path.extension() == Some(OsStr::new("zst")) {
            continue;
        }
        println!("Trying file: {path:?}");
        let input = fs::read(entry.path()).unwrap();

        let mut compressed_file: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(crate::encoding::CompressionLevel::Fastest);
        compressor.set_source(input.as_slice());
        compressor.set_drain(&mut compressed_file);
        compressor.compress();
        let mut decompressed_output = Vec::new();
        // zstd::stream::copy_decode(compressed_file.as_slice(), &mut decompressed_output).unwrap();
        match zstd::stream::copy_decode(compressed_file.as_slice(), &mut decompressed_output) {
            Ok(()) => {
                if input != decompressed_output {
                    failures.push((path.to_owned(), "Input didn't equal output".to_owned()));
                }
            }
            Err(e) => {
                failures.push((
                    path.to_owned(),
                    format!("Decompressor threw an error: {e:?}"),
                ));
            }
        };

        if !failures.is_empty() {
            panic!(
                "Decompression of the compressed file fails on the following files: {:?}",
                failures
            );
        }
    }
}

#[test]
fn test_encode_corpus_files_compressed_our_decompressor() {
    extern crate std;
    use crate::encoding::FrameCompressor;
    use alloc::borrow::ToOwned;
    use alloc::vec::Vec;
    use std::ffi::OsStr;
    use std::fs;
    use std::io::Read;
    use std::path::PathBuf;
    use std::println;

    let mut failures: Vec<PathBuf> = Vec::new();
    let mut files: Vec<_> = fs::read_dir("./decodecorpus_files").unwrap().collect();
    if fs::read_dir("./local_corpus_files").is_ok() {
        files.extend(fs::read_dir("./local_corpus_files").unwrap());
    }

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    for entry in files.iter().map(|f| f.as_ref().unwrap()) {
        let path = entry.path();
        if path.extension() == Some(OsStr::new("zst")) {
            continue;
        }
        println!("Trying file: {path:?}");
        let input = fs::read(entry.path()).unwrap();

        let mut compressed_file: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(crate::encoding::CompressionLevel::Fastest);
        compressor.set_source(input.as_slice());
        compressor.set_drain(&mut compressed_file);

        compressor.compress();
        let mut decompressed_output = Vec::new();
        let mut decoder =
            crate::decoding::StreamingDecoder::new(compressed_file.as_slice()).unwrap();
        decoder.read_to_end(&mut decompressed_output).unwrap();

        if input != decompressed_output {
            failures.push(path);
        }
    }

    if !failures.is_empty() {
        panic!(
            "Decompression of compressed file failed on the following files: {:?}",
            failures
        );
    }
}

#[test]
fn test_encode_corpus_files_compressed_original_decompressor() {
    extern crate std;
    use crate::encoding::FrameCompressor;
    use alloc::borrow::ToOwned;
    use alloc::format;
    use alloc::vec::Vec;
    use std::ffi::OsStr;
    use std::fs;
    use std::path::PathBuf;
    use std::println;
    use std::string::String;

    let mut failures: Vec<(PathBuf, String)> = Vec::new();
    let mut files: Vec<_> = fs::read_dir("./decodecorpus_files").unwrap().collect();
    if fs::read_dir("./local_corpus_files").is_ok() {
        files.extend(fs::read_dir("./local_corpus_files").unwrap());
    }

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    for entry in files.iter().map(|f| f.as_ref().unwrap()) {
        let path = entry.path();
        if path.extension() == Some(OsStr::new("zst")) {
            continue;
        }
        println!("Trying file: {path:?}");
        let input = fs::read(entry.path()).unwrap();

        let mut compressed_file: Vec<u8> = Vec::new();
        let mut compressor = FrameCompressor::new(crate::encoding::CompressionLevel::Fastest);
        compressor.set_source(input.as_slice());
        compressor.set_drain(&mut compressed_file);
        compressor.compress();
        let mut decompressed_output = Vec::new();
        // zstd::stream::copy_decode(compressed_file.as_slice(), &mut decompressed_output).unwrap();
        match zstd::stream::copy_decode(compressed_file.as_slice(), &mut decompressed_output) {
            Ok(()) => {
                if input != decompressed_output {
                    failures.push((path.to_owned(), "Input didn't equal output".to_owned()));
                }
            }
            Err(e) => {
                failures.push((
                    path.to_owned(),
                    format!("Decompressor threw an error: {e:?}"),
                ));
            }
        };

        if !failures.is_empty() {
            panic!(
                "Decompression of the compressed file fails on the following files: {:?}",
                failures
            );
        }
    }
}
