#[cfg(not(all(target_arch = "aarch64", target_os = "macos")))]
compile_error!("this specimen requires the reviewed aarch64-apple-darwin target");

#[cfg(not(any(boundary_positive, boundary_wrong_slot)))]
compile_error!("select exactly one of boundary_positive or boundary_wrong_slot");

#[cfg(all(boundary_positive, boundary_wrong_slot))]
compile_error!("boundary_positive and boundary_wrong_slot are mutually exclusive");

#[cfg(boundary_positive)]
const VARIANT: &str = "positive";

#[cfg(boundary_wrong_slot)]
const VARIANT: &str = "wrong_slot";

/// Reads the first word, replaces one word, and returns the old first word.
///
/// # Safety
/// `words` must point into a live, initialized, aligned two-word array with both
/// words exclusively readable and writable throughout this call. The selected
/// control writes the second word; the positive writes the first word.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn anneal_exchange(_words: *mut u64, _replacement: u64) -> u64 {
    #[cfg(boundary_positive)]
    core::arch::naked_asm!(
        "ldr x2, [x0]",
        "str x1, [x0]",
        "mov x0, x2",
        "ret",
    );

    #[cfg(boundary_wrong_slot)]
    core::arch::naked_asm!(
        "ldr x2, [x0]",
        "str x1, [x0, #8]",
        "mov x0, x2",
        "ret",
    );
}

/// The Rust continuation observes both actual post-call array elements.
/// The four returned fields are the scalar return, first word, second word,
/// and the prescribed wrapping continuation value.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn anneal_call(mut words: [u64; 2], replacement: u64) -> (u64, u64, u64, u64) {
    let whole_array_pointer = words.as_mut_ptr();
    // SAFETY: This local whole array remains live and initialized. Its pointer
    // is properly aligned, both elements are writable, and no competing access
    // occurs during the call. Both cfg variants fit this two-word domain.
    let returned = unsafe { anneal_exchange(whole_array_pointer, replacement) };
    let first_after = words[0];
    let second_after = words[1];
    let continuation = returned
        .rotate_left(7)
        .wrapping_add(first_after.rotate_left(23))
        .wrapping_mul(0x9e3779b97f4a7c15)
        .wrapping_add(second_after.rotate_left(41));
    (returned, first_after, second_after, continuation)
}

const FIXTURES: [(u64, u64, u64); 4] = [
    (0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978),
    (0, u64::MAX, 1),
    (u64::MAX, 1, 0),
    (0x8000000000000000, 0x0102030405060708, 0x7fffffffffffffff),
];

fn main() {
    let u64_size = core::mem::size_of::<u64>();
    let u64_align = core::mem::align_of::<u64>();
    let array_size = core::mem::size_of::<[u64; 2]>();
    let array_align = core::mem::align_of::<[u64; 2]>();
    let layout_ok = u64_size == 8 && u64_align == 8 && array_size == 16 && array_align == 8;
    println!(
        "{{\"kind\":\"layout\",\"variant\":\"{VARIANT}\",\"u64_size\":{u64_size},\"u64_align\":{u64_align},\"array_size\":{array_size},\"array_align\":{array_align},\"expected_u64_size\":8,\"expected_u64_align\":8,\"expected_array_size\":16,\"expected_array_align\":8,\"ok\":{layout_ok}}}"
    );
    if !layout_ok {
        std::process::exit(1);
    }

    for (index, fixture) in FIXTURES.into_iter().enumerate() {
        // Keep the actual caller's inputs opaque to optimization in both cells.
        let (a, b, replacement) = std::hint::black_box(fixture);
        let (returned, first_after, second_after, continuation) =
            anneal_call([a, b], replacement);

        // Expectations depend only on the input triple and selected variant.
        // Neither expected post-call word is copied from an observation.
        let (expected_returned, expected_first, expected_second) = if cfg!(boundary_positive) {
            (a, replacement, b)
        } else {
            (a, a, replacement)
        };
        let expected_continuation = expected_returned
            .rotate_left(7)
            .wrapping_add(expected_first.rotate_left(23))
            .wrapping_mul(0x9e3779b97f4a7c15)
            .wrapping_add(expected_second.rotate_left(41));
        let own_tuple_ok = (returned, first_after, second_after)
            == (expected_returned, expected_first, expected_second);
        let own_continuation_ok = continuation == expected_continuation;
        let advertised_contract = (returned, first_after, second_after) == (a, replacement, b);
        let advertised_as_expected = advertised_contract == cfg!(boundary_positive);

        // Hex strings retain every u64 bit without JSON-number precision loss.
        println!(
            "{{\"kind\":\"case\",\"variant\":\"{VARIANT}\",\"index\":{index},\"a\":\"{a:016x}\",\"b\":\"{b:016x}\",\"replacement\":\"{replacement:016x}\",\"returned\":\"{returned:016x}\",\"first_after\":\"{first_after:016x}\",\"second_after\":\"{second_after:016x}\",\"continuation\":\"{continuation:016x}\",\"expected_returned\":\"{expected_returned:016x}\",\"expected_first\":\"{expected_first:016x}\",\"expected_second\":\"{expected_second:016x}\",\"expected_continuation\":\"{expected_continuation:016x}\",\"own_tuple_ok\":{own_tuple_ok},\"own_continuation_ok\":{own_continuation_ok},\"advertised_contract\":{advertised_contract},\"advertised_as_expected\":{advertised_as_expected}}}"
        );

        if !(own_tuple_ok && own_continuation_ok && advertised_as_expected) {
            std::process::exit(1);
        }
    }

    println!("{{\"kind\":\"summary\",\"variant\":\"{VARIANT}\",\"cases\":4,\"ok\":true}}");
}
