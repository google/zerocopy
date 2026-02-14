
pub struct Config {
    #[cfg(target_os = "linux")]
    pub fd: i32,
    #[cfg(target_os = "windows")]
    pub handle: i32,
}
