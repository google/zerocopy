use crate::rref::RRef;

pub unsafe auto trait RRefable {}
impl<T> !RRefable for *mut T {}
impl<T> !RRefable for *const T {}
impl<T> !RRefable for &T {}
impl<T> !RRefable for &mut T {}
impl<T> !RRefable for [T] {}

pub trait TypeIdentifiable {
    fn type_id() -> u64;
}

macro_rules! int_typeid {
    ($int_type:ty) => {
        impl TypeIdentifiable for $int_type {
            fn type_id() -> u64 {
                <$int_type>::max_value() as u64
            }
        }
    };
}

int_typeid!(u8);
int_typeid!(u16);
int_typeid!(u32);
int_typeid!(u64);
int_typeid!(usize);
int_typeid!(i8);
int_typeid!(i16);
int_typeid!(i32);
int_typeid!(i64);
int_typeid!(isize);

impl TypeIdentifiable for f32 {
    fn type_id() -> u64 {
        56342334 as u64
    }
}
impl TypeIdentifiable for f64 {
    fn type_id() -> u64 {
        25134214 as u64
    }
}
impl TypeIdentifiable for bool {
    fn type_id() -> u64 {
        22342342
    }
}

impl<T: TypeIdentifiable + RRefable> TypeIdentifiable for RRef<T> {
    fn type_id() -> u64 {
        (T::type_id().wrapping_add(123)).wrapping_pow(2).wrapping_sub(1)
    }
}

impl<T: TypeIdentifiable + RRefable> TypeIdentifiable for Option<T> {
    fn type_id() -> u64 {
        (T::type_id().wrapping_add(123)).wrapping_pow(3).wrapping_sub(1)
    }
}

impl<T: TypeIdentifiable, const N: usize> TypeIdentifiable for [T; N] {
    fn type_id() -> u64 {
        (T::type_id().wrapping_add(123)).wrapping_pow(2).wrapping_sub(N as u64)
    }
}

pub trait CustomCleanup: RRefable {
    fn cleanup(&mut self);
}

// blanket implementation, overriden by RRef, RRefArray, RRefDeque
impl<T: RRefable> CustomCleanup for T {
    default fn cleanup(&mut self) {
        // no-op by default
    }
}

// TODO: any other implementations?

impl<T: RRefable> CustomCleanup for Option<T> {
    fn cleanup(&mut self) {
        if let Some(val) = self {
            val.cleanup();
        }
    }
}

impl<T: RRefable, const N: usize> CustomCleanup for [T; N] {
    fn cleanup(&mut self) {
        for el in self.iter_mut() {
            el.cleanup();
        }
    }
}
