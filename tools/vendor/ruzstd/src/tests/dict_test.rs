#[test]
fn test_dict_parsing() {
    use crate::decoding::dictionary::Dictionary;
    use alloc::vec;
    let mut raw = vec![0u8; 8];

    // correct magic num
    raw[0] = 0x37;
    raw[1] = 0xA4;
    raw[2] = 0x30;
    raw[3] = 0xEC;

    //dict-id
    let dict_id = 0x47232101;
    raw[4] = 0x01;
    raw[5] = 0x21;
    raw[6] = 0x23;
    raw[7] = 0x47;

    // tables copied from ./dict_tests/dictionary
    let raw_tables = &[
        54, 16, 192, 155, 4, 0, 207, 59, 239, 121, 158, 116, 220, 93, 114, 229, 110, 41, 249, 95,
        165, 255, 83, 202, 254, 68, 74, 159, 63, 161, 100, 151, 137, 21, 184, 183, 189, 100, 235,
        209, 251, 174, 91, 75, 91, 185, 19, 39, 75, 146, 98, 177, 249, 14, 4, 35, 0, 0, 0, 40, 40,
        20, 10, 12, 204, 37, 196, 1, 173, 122, 0, 4, 0, 128, 1, 2, 2, 25, 32, 27, 27, 22, 24, 26,
        18, 12, 12, 15, 16, 11, 69, 37, 225, 48, 20, 12, 6, 2, 161, 80, 40, 20, 44, 137, 145, 204,
        46, 0, 0, 0, 0, 0, 116, 253, 16, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    raw.extend(&raw_tables[..]);

    //offset history 3,10,0x00ABCDEF
    raw.extend(vec![3, 0, 0, 0]);
    raw.extend(vec![10, 0, 0, 0]);
    raw.extend(vec![0xEF, 0xCD, 0xAB, 0]);

    //just some random bytes
    let raw_content = vec![
        1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 123, 3, 234, 23, 234, 34, 23, 234, 34, 34, 234, 234,
    ];
    raw.extend(&raw_content);

    let dict = Dictionary::decode_dict(&raw).unwrap();

    if dict.id != dict_id {
        panic!(
            "Dict-id did not get parsed correctly. Is: {}, Should be: {}",
            dict.id, dict_id
        );
    }

    if !dict.dict_content.eq(&raw_content) {
        panic!(
            "dict content did not get parsed correctly. Is: {:?}, Should be: {:?}",
            dict.dict_content, raw_content
        );
    }

    if !dict.offset_hist.eq(&[3, 10, 0x00ABCDEF]) {
        panic!(
            "offset history did not get parsed correctly. Is: {:?}, Should be: {:?}",
            dict.offset_hist,
            [3, 10, 0x00ABCDEF]
        );
    }

    // test magic num checking
    raw[0] = 1;
    raw[1] = 1;
    raw[2] = 1;
    raw[3] = 1;
    match Dictionary::decode_dict(&raw) {
        Ok(_) => panic!("The dict got decoded but the magic num was incorrect!"),
        Err(_) => { /* This is what should happen*/ }
    }
}

#[test]
fn test_dict_decoding() {
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
    let mut total_counter = 0;
    let mut failed: Vec<String> = Vec::new();

    let mut speeds = Vec::new();
    let mut speeds_read = Vec::new();

    let mut files: Vec<_> = fs::read_dir("./dict_tests/files").unwrap().collect();
    let dict = BufReader::new(fs::File::open("./dict_tests/dictionary").unwrap());
    let dict: Vec<u8> = dict.bytes().map(|x| x.unwrap()).collect();

    files.sort_by_key(|x| match x {
        Err(_) => "".to_owned(),
        Ok(entry) => entry.path().to_str().unwrap().to_owned(),
    });

    let mut frame_dec = FrameDecoder::new();
    let dict = crate::decoding::dictionary::Dictionary::decode_dict(&dict).unwrap();
    frame_dec.add_dict(dict).unwrap();

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
        "Total: {total_counter}, Success: {success_counter}, WrongSize: {fail_counter_size}, WrongBytecount: {fail_counter_bytes_read}, Diffs: {fail_counter_diff}"
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
