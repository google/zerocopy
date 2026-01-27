/// Allows you to pull the version from your Cargo.toml at compile time as
/// `MAJOR.MINOR.PATCH_PKGVERSION_PRE`
#[macro_export]
macro_rules! cargo_crate_version {
    // -- Pulled from clap.rs src/macros.rs
    () => {
        env!("CARGO_PKG_VERSION")
    };
}

/// Set ssl cert env. vars to make sure openssl can find required files
macro_rules! set_ssl_vars {
    () => {
        #[cfg(target_os = "linux")]
        {
            if ::std::env::var_os("SSL_CERT_FILE").is_none() {
                ::std::env::set_var("SSL_CERT_FILE", "/etc/ssl/certs/ca-certificates.crt");
            }
            if ::std::env::var_os("SSL_CERT_DIR").is_none() {
                ::std::env::set_var("SSL_CERT_DIR", "/etc/ssl/certs");
            }
        }
    };
}

/// Helper to `print!` and immediately `flush` `stdout`
macro_rules! print_flush {
    ($literal:expr) => {
        print!($literal);
        ::std::io::Write::flush(&mut ::std::io::stdout())?;
    };
    ($literal:expr, $($arg:expr),*) => {
        print!($literal, $($arg),*);
        ::std::io::Write::flush(&mut ::std::io::stdout())?;
    }
}

/// Helper for formatting `errors::Error`s
macro_rules! format_err {
    ($e_type:expr, $literal:expr) => {
        $e_type(format!($literal))
    };
    ($e_type:expr, $literal:expr, $($arg:expr),*) => {
        $e_type(format!($literal, $($arg),*))
    };
}

/// Helper for formatting `errors::Error`s and returning early
macro_rules! bail {
    ($e_type:expr, $literal:expr) => {
        return Err(format_err!($e_type, $literal))
    };
    ($e_type:expr, $literal:expr, $($arg:expr),*) => {
        return Err(format_err!($e_type, $literal, $($arg),*))
    };
}
