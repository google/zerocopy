// This test serves as a control case for issue #2177.
// It manually expands the code that KnownLayout generates, but inside a macro_rules! macro.
// This does NOT trigger the private_bounds lint, proving that the issue is specific to
// the interaction between proc-macro generated spans and macro_rules! expansion.

#![allow(missing_docs)]
use zerocopy::KnownLayout;

// Mimic the internal Field trait
pub unsafe trait Field<T> {
    type Type;
}

macro_rules! define {
    ($name:ident) => {
        pub struct $name(u8);

        const _: () = {
            #[allow(non_camel_case_types)]
            struct __Zerocopy_Field_0; // Private struct

            unsafe impl Field<__Zerocopy_Field_0> for $name {
                type Type = u8;
            }

            #[repr(C)]
            #[doc(hidden)]
            // The lint triggers on the following struct in the actual derive usage,
            // claiming __Zerocopy_Field_0 is leaked.
            // Here, it does not trigger.
            pub struct __ZerocopyKnownLayoutMaybeUninit
            where
                <$name as Field<__Zerocopy_Field_0>>::Type: KnownLayout
            {
                _marker: (),
            }
        };
    }
}

define!(Foo);

#[test]
fn test_issue_2177_control() {
    let _ = Foo(0);
}
