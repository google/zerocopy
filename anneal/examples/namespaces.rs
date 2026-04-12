pub mod outer {
    pub mod inner {
        /// ```lean, anneal, spec
        /// requires: x.val + 1 <= 4294967295
        /// ensures: ret.val = x.val + 1
        /// proof:
        ///   unfold deep_function at h_returns
        ///   have h := Aeneas.Std.U32.add_bv_spec (x := x) (y := 1#u32) (by scalar_tac)
        ///   unfold Aeneas.Std.WP.spec at h
        ///   try unfold Aeneas.Std.WP.theta at h
        ///   try unfold Aeneas.Std.WP.wp_return at h
        ///   simp_all
        /// proof (h_progress):
        ///   unfold deep_function
        ///   rcases h_req with ⟨_, h_bound⟩
        ///   have h := Aeneas.Std.U32.add_bv_spec (x := x) (y := 1#u32) (by scalar_tac)
        ///   have ⟨y, hy⟩ := Aeneas.Std.WP.spec_imp_exists h
        ///   simp_all
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
