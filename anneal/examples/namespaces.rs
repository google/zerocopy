pub mod outer {
    pub mod inner {
        /// ```lean, anneal, spec
        /// theorem spec (x : Std.U32) (h_req : x.val + 1 ≤ 4294967295) :
        ///   Aeneas.Std.WP.spec (outer.inner.deep_function x) (fun ret_ => ret_.val = x.val + 1) := by
        ///   sorry
        /// ```
        pub unsafe fn deep_function(x: u32) -> u32 {
            x + 1
        }
    }
}

pub fn call_deep() -> u32 {
    unsafe { outer::inner::deep_function(42) }
}

fn main() {}
