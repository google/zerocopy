///@ lean invariant MyStruct
///@ is_valid self := self.val < 100
pub struct MyStruct {
    pub val: u32,
}

///@ lean invariant Wrapper
///@ is_valid self := self.inner.val > 0
pub struct Wrapper<T> {
    pub inner: MyStruct,
    pub data: T,
}

///@ lean spec use_invariant (s : MyStruct)
///@ ensures |ret| ret = s.val /\ ret < 100
///@ proof
///@   simp_all [use_invariant]
pub fn use_invariant(s: MyStruct) -> u32 {
    s.val
}

///@ lean spec generic_invariant (w : Wrapper U32)
///@ ensures |ret| ret = w.inner.val /\ ret > 0
///@ proof
///@   simp_all [generic_invariant]
pub fn generic_invariant<T>(w: Wrapper<T>) -> u32 {
    w.inner.val
}

///@ lean spec make_mystruct (val : U32)
///@ requires h : val < 100
///@ ensures |ret| ret.val = val
///@ proof
///@   simp_all [make_mystruct]
pub fn make_mystruct(val: u32) -> MyStruct {
    MyStruct { val }
}

///@ lean spec make_wrapper (inner : MyStruct) (data : U32)
///@ requires h : inner.val > 0
///@ ensures |ret| ret.inner = inner /\ ret.data = data
///@ proof
///@   simp_all [make_wrapper]
pub fn make_wrapper(inner: MyStruct, data: u32) -> Wrapper<u32> {
    Wrapper { inner, data }
}

fn main() {}
