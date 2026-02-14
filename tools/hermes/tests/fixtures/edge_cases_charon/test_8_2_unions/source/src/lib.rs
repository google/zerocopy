
pub union U {
    pub f1: u32,
    pub f2: f32,
}

pub fn access(u: U) -> u32 {
    unsafe { u.f1 }
}
