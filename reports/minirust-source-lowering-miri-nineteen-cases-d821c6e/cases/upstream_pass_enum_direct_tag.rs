enum A {
    A1(u8),
    A2,
}

fn check_a(a: &A, is_a1: bool) {
    if let A::A1(x) = a {
        assert!(is_a1 & (*x == 12))
    } else {
        assert!(!is_a1);
    }

    match a {
        A::A1(x) => assert!(is_a1 & (*x == 12)),
        A::A2 => assert!(!is_a1),
    }
}

#[repr(i16)]
enum I16Repr {
    Min = i16::MIN,
    Minus1 = -1,
    Zero = 0,
    Max = i16::MAX,
}

fn get_i16_repr(a: I16Repr) -> i16 {
    match a {
        I16Repr::Min => -2,
        I16Repr::Minus1 => -1,
        I16Repr::Zero => 0,
        I16Repr::Max => 1,
    }
}

fn main() {
    let x = A::A1(12);
    check_a(&x, true);
    let x = A::A2;
    check_a(&x, false);

    assert!(get_i16_repr(I16Repr::Min) == -2);
    assert!(get_i16_repr(I16Repr::Minus1) == -1);
    assert!(get_i16_repr(I16Repr::Zero) == 0);
    assert!(get_i16_repr(I16Repr::Max) == 1);
}
