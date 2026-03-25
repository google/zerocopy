pub mod missing_cfg_file {
    #[cfg(target_os = "windows")]
    mod windows_sys; // This file will intentionally not exist
    
    /// ```lean, hermes
    /// context:
    /// theorem my_demo : True := trivial
    /// ```
    pub fn demo() {}
}

pub mod missing_cfg_mod {
    #[cfg(target_os = "fake_os")]
    mod fake;
    
    
    /// ```lean, hermes
    /// ```
    fn _hermes_dummy() {}
}

pub mod warn_cfg_attr_path {
    #[cfg_attr(unix, path = "sys_unix.rs")]
    mod sys; // This triggers the warning
    
    /// ```lean, hermes
    /// context:
    /// theorem my_demo : True := trivial
    /// ```
    pub fn demo() {} // Included so the overall verification command succeeds
}

pub mod macro_blind_spot {
    macro_rules! gen_mod { ($n:ident) => { mod $n; } }
    gen_mod!(hidden);
}

