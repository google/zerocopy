pub fn flavor() -> &'static str {
    if cfg!(feature = "host") { "host" }
    else if cfg!(feature = "normal") { "normal" }
    else { "none" }
}

