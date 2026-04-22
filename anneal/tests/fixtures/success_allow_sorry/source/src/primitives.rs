pub mod primitives_layout {
    #![crate_type = "lib"]
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_u8) (fun ret_ =>
    ///     ret_.1.val = 1 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_u8() -> (usize, usize) {
        (core::mem::size_of::<u8>(), core::mem::align_of::<u8>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_i8) (fun ret_ =>
    ///     ret_.1.val = 1 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_i8() -> (usize, usize) {
        (core::mem::size_of::<i8>(), core::mem::align_of::<i8>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_bool) (fun ret_ =>
    ///     ret_.1.val = 1 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_bool() -> (usize, usize) {
        (core::mem::size_of::<bool>(), core::mem::align_of::<bool>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_char) (fun ret_ =>
    ///     ret_.1.val = 4 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_char() -> (usize, usize) {
        (core::mem::size_of::<char>(), core::mem::align_of::<char>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_u16) (fun ret_ =>
    ///     ret_.1.val = 2 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_u16() -> (usize, usize) {
        (core::mem::size_of::<u16>(), core::mem::align_of::<u16>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_i16) (fun ret_ =>
    ///     ret_.1.val = 2 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_i16() -> (usize, usize) {
        (core::mem::size_of::<i16>(), core::mem::align_of::<i16>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_u32) (fun ret_ =>
    ///     ret_.1.val = 4 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_u32() -> (usize, usize) {
        (core::mem::size_of::<u32>(), core::mem::align_of::<u32>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_i32) (fun ret_ =>
    ///     ret_.1.val = 4 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_i32() -> (usize, usize) {
        (core::mem::size_of::<i32>(), core::mem::align_of::<i32>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_u64) (fun ret_ =>
    ///     ret_.1.val = 8 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_u64() -> (usize, usize) {
        (core::mem::size_of::<u64>(), core::mem::align_of::<u64>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_i64) (fun ret_ =>
    ///     ret_.1.val = 8 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_i64() -> (usize, usize) {
        (core::mem::size_of::<i64>(), core::mem::align_of::<i64>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_u128) (fun ret_ =>
    ///     ret_.1.val = 16 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_u128() -> (usize, usize) {
        (core::mem::size_of::<u128>(), core::mem::align_of::<u128>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_i128) (fun ret_ =>
    ///     ret_.1.val = 16 ∧
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_i128() -> (usize, usize) {
        (core::mem::size_of::<i128>(), core::mem::align_of::<i128>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_usize) (fun ret_ =>
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_usize() -> (usize, usize) {
        (core::mem::size_of::<usize>(), core::mem::align_of::<usize>())
    }
    
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (test_isize) (fun ret_ =>
    ///     Anneal.IsAlignment ret_.2.val ∧
    ///     ret_.2.val ∣ ret_.1.val) := by
    ///   sorry
    /// ```
    pub fn test_isize() -> (usize, usize) {
        (core::mem::size_of::<isize>(), core::mem::align_of::<isize>())
    }
}

