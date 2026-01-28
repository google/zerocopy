#[test]
fn test_decode_corpus_files() {
    extern crate std;
    use crate::decoding::BlockDecodingStrategy;
    use crate::decoding::FrameDecoder;
    use alloc::borrow::ToOwned;
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;
    use std::fs;
    use std::io::BufReader;
    use std::io::Read;
    use std::println;

    let mut success_counter = 0;
    let mut fail_counter_diff = 0;
    let mut fail_counter_size = 0;
    let mut fail_counter_bytes_read = 0;
    #[cfg_attr(not(feature = "hash"), allow(unused_mut))]
    let mut fail_counter_chksum = 0;
    let mut total_counter = 0;
    let mut failed: Vec<String> = Vec::new();

    let mut speeds = Vec::new();
    let mut speeds_read = Vec::new();

    let mut files: Vec<_> = fs::read_dir("./decodecorpus_files").unwrap().collect();
    if fs::read_dir("./local_corpus_files").is_ok() {
        files.extend(fs::read_dir("./local_corpus_files").unwrap());
    }

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    let mut frame_dec = FrameDecoder::new();

    for file in files {
        let f = file.unwrap();
        let metadata = f.metadata().unwrap();
        let file_size = metadata.len();

        let p = String::from(f.path().to_str().unwrap());
        if !p.ends_with(".zst") {
            continue;
        }
        println!("Trying file: {p}");

        let mut content = fs::File::open(f.path()).unwrap();

        frame_dec.reset(&mut content).unwrap();

        let start_time = std::time::Instant::now();
        /////DECODING
        frame_dec
            .decode_blocks(&mut content, BlockDecodingStrategy::All)
            .unwrap();
        let result = frame_dec.collect().unwrap();
        let end_time = start_time.elapsed();

        match frame_dec.get_checksum_from_data() {
            Some(chksum) => {
                #[cfg(feature = "hash")]
                if frame_dec.get_calculated_checksum().unwrap() != chksum {
                    println!(
                        "Checksum did not match! From data: {}, calculated while decoding: {}\n",
                        chksum,
                        frame_dec.get_calculated_checksum().unwrap()
                    );
                    fail_counter_chksum += 1;
                    failed.push(p.clone().to_string());
                } else {
                    println!("Checksums are ok!\n");
                }
                #[cfg(not(feature = "hash"))]
                println!(
                    "Checksum feature not enabled, skipping. From data: {}\n",
                    chksum
                );
            }
            None => println!("No checksums to test\n"),
        }

        let mut original_p = p.clone();
        original_p.truncate(original_p.len() - 4);
        let original_f = BufReader::new(fs::File::open(original_p).unwrap());
        let original: Vec<u8> = original_f.bytes().map(|x| x.unwrap()).collect();

        println!("Results for file: {}", p.clone());
        let mut success = true;

        if original.len() != result.len() {
            println!(
                "Result has wrong length: {}, should be: {}",
                result.len(),
                original.len()
            );
            success = false;
            fail_counter_size += 1;
        }

        if frame_dec.bytes_read_from_source() != file_size {
            println!(
                "Framedecoder counted wrong amount of bytes: {}, should be: {}",
                frame_dec.bytes_read_from_source(),
                file_size
            );
            success = false;
            fail_counter_bytes_read += 1;
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
                //println!(
                //    "Original {} not equal to result {} at byte: {}",
                //    original[idx], result[idx], idx,
                //);
            }
        }

        if counter > 0 {
            println!("Result differs in at least {counter} bytes from original");
            success = false;
            fail_counter_diff += 1;
        }

        if success {
            success_counter += 1;
        } else {
            failed.push(p.clone().to_string());
        }
        total_counter += 1;

        let dur = end_time.as_micros() as usize;
        let speed = result.len() / if dur == 0 { 1 } else { dur };
        let speed_read = file_size as usize / if dur == 0 { 1 } else { dur };
        println!("SPEED: {speed}");
        println!("SPEED_read: {speed_read}");
        speeds.push(speed);
        speeds_read.push(speed_read);
    }

    println!("###################");
    println!("Summary:");
    println!("###################");
    println!(
        "Total: {total_counter}, Success: {success_counter}, WrongSize: {fail_counter_size}, WrongBytecount: {fail_counter_bytes_read}, WrongChecksum: {fail_counter_chksum}, Diffs: {fail_counter_diff}"
    );
    println!("Failed files: ");
    for f in &failed {
        println!("{f}");
    }

    let speed_len = speeds.len();
    let sum_speed: usize = speeds.into_iter().sum();
    let avg_speed = sum_speed / speed_len;
    let avg_speed_bps = avg_speed * 1_000_000;
    if avg_speed_bps < 1000 {
        println!("Average speed: {avg_speed_bps} B/s");
    } else if avg_speed_bps < 1_000_000 {
        println!("Average speed: {} KB/s", avg_speed_bps / 1000);
    } else {
        println!("Average speed: {} MB/s", avg_speed_bps / 1_000_000);
    }

    let speed_read_len = speeds_read.len();
    let sum_speed_read: usize = speeds_read.into_iter().sum();
    let avg_speed_read = sum_speed_read / speed_read_len;
    let avg_speed_read_bps = avg_speed_read * 1_000_000;
    if avg_speed_read_bps < 1000 {
        println!("Average speed reading: {avg_speed_read_bps} B/s");
    } else if avg_speed_bps < 1_000_000 {
        println!("Average speed reading: {} KB/s", avg_speed_read_bps / 1000);
    } else {
        println!(
            "Average speed reading: {} MB/s",
            avg_speed_read_bps / 1_000_000
        );
    }

    assert!(failed.is_empty());
}
