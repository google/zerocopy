/// ```lean
/// model async_foo
/// ```
async unsafe fn async_foo() -> i32 { 0 }

/// ```lean
/// model const_foo
/// ```
const unsafe fn const_foo() -> i32 { 0 }

/// ```lean
/// model extern_foo
/// ```
unsafe extern "C" fn extern_foo() -> i32 { 0 }
