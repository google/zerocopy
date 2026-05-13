use anyhow::Context as _;

pub fn write_toolchain_definition(
    toolchain_config_toml: impl std::io::Read,
    toolchain_config_rs: impl std::io::Write,
) -> Result<(), anyhow::Error> {
    write_toolchain_definition_custom(
        std::env::consts::OS,
        std::env::consts::ARCH,
        toolchain_config_toml,
        toolchain_config_rs,
    )
}

pub fn write_toolchain_definition_custom(
    os: &str,
    arch: &str,
    mut toolchain_config_toml_read: impl std::io::Read,
    mut toolchain_config_rs: impl std::io::Write,
) -> Result<(), anyhow::Error> {
    let mut toolchain_config_toml_string = String::new();
    toolchain_config_toml_read
        .read_to_string(&mut toolchain_config_toml_string)
        .context("failed to read toolchain config toml")?;
    let toolchain_config_toml: toml::Value = toml::from_str(&toolchain_config_toml_string)
        .context("failed to parse toml string from toolchain config")?;

    let this_toolchain_config_toml = toolchain_config_toml
        .get("toolchain")
        .context("toolchain config toml missing 'toolchain' key")?
        .get(os)
        .with_context(|| format!("toolchain config toml missing 'toolchain.{os}' key"))?
        .get(arch)
        .with_context(|| format!("toolchain config toml missing 'toolchain.{os}.{arch}' key"))?;

    let Some(toml::Value::String(archive_sha256_string)) =
        this_toolchain_config_toml.get("archive-sha256")
    else {
        anyhow::bail!("toolchain config toml missing 'toolchain.{os}.{arch}.archive-sha256' key");
    };
    let archive_sha256 = decode_hex_256(archive_sha256_string)
        .with_context(|| format!("toolchain config toml missing 'toolchain.{os}.{arch}.archive-sha256' value not a 256-bit hex value; found: {:?}", archive_sha256_string))?;
    let Some(toml::Value::String(archive_url)) = this_toolchain_config_toml.get("archive-url")
    else {
        anyhow::bail!("toolchain config toml missing 'toolchain.{os}.{arch}.archive-url' key");
    };

    let output = format!(
        r#"
            use toolchain_config::Config as ToolchainConfigTrait;

            struct ToolchainConfig;

            impl ToolchainConfigTrait for ToolchainConfig {{
                const OS: &str = {:?};
                const ARCH: &str = {:?};
                const ARCHIVE_SHA256: [u8; 32] = {:?};
                const ARCHIVE_URL: &'static str = {:?};
            }}
        "#,
        os, arch, archive_sha256, archive_url,
    );
    Ok(toolchain_config_rs
        .write_all(output.as_bytes())
        .context("failed to write to toolchain config rust source file")?)
}

const fn decode_hex_256(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut res = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let (h, l) = (bytes[i * 2], bytes[i * 2 + 1]);
        let h_nib = match decode_nibble(h) {
            Some(n) => n,
            None => return None,
        };
        let l_nib = match decode_nibble(l) {
            Some(n) => n,
            None => return None,
        };
        res[i] = (h_nib << 4) | l_nib;
        i += 1;
    }
    Some(res)
}

const fn decode_nibble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_toml_succeed_self_platform() {
        let toolchain_config_toml_string = format!(
            r#"
            [toolchain.{}.{}]
            archive-sha256 = "0000000000000000000000000000000000000000000000000000000000000000"
            archive-url = "http://example.com/archive.tar.zst"
        "#,
            std::env::consts::OS,
            std::env::consts::ARCH
        );

        write_toolchain_definition(toolchain_config_toml_string.as_bytes(), &mut std::io::sink())
            .expect("failed to write toolchain definition from valid toolchain config toml");
    }
}
