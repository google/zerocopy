use crate::config::Manifest;

/// Renders the template
///
/// This is not a real template engine, it just processes a few substitutions.
pub fn render(
    template: Option<String>,
    readme: String,
    cargo: &Manifest,
    add_title: bool,
    add_badges: bool,
    add_license: bool,
) -> Result<String, String> {
    let title: &str = &cargo.name;

    let badges: Vec<&str> = cargo.badges.iter().map(AsRef::as_ref).collect();
    let badges: &[&str] = badges.as_ref();

    let license: Option<&str> = cargo.license.as_ref().map(AsRef::as_ref);

    let version: &str = cargo.version.as_ref();

    if let Some(template) = template {
        process_template(template, readme, title, badges, license, version)
    } else {
        process_string(
            readme,
            title,
            badges,
            license,
            add_title,
            add_badges,
            add_license,
        )
    }
}

/// Process the substitutions of the template
///
/// Available variable:
/// - `{{readme}}` documentation extracted from the rust docs
/// - `{{crate}}` crate name defined in `Cargo.toml`
/// - `{{badges}}` badges defined in `Cargo.toml`
/// - `{{license}}` license defined in `Cargo.toml`
/// - `{{version}}` version defined in `Cargo.toml`
fn process_template(
    mut template: String,
    readme: String,
    title: &str,
    badges: &[&str],
    license: Option<&str>,
    version: &str,
) -> Result<String, String> {
    template = template.trim_end_matches("\n").to_owned();

    if !template.contains("{{readme}}") {
        return Err("Missing `{{readme}}` in template".to_owned());
    }

    if template.contains("{{crate}}") {
        template = template.replace("{{crate}}", &title);
    }

    if template.contains("{{badges}}") {
        if badges.is_empty() {
            return Err(
                "`{{badges}}` was found in template but no badges were provided".to_owned(),
            );
        }
        let badges = badges.join("\n");
        template = template.replace("{{badges}}", &badges);
    }

    if template.contains("{{license}}") {
        if let Some(license) = license {
            template = template.replace("{{license}}", &license);
        } else {
            return Err(
                "`{{license}}` was found in template but no license was provided".to_owned(),
            );
        }
    }

    template = template.replace("{{version}}", version);

    let result = template.replace("{{readme}}", &readme);
    Ok(result)
}

/// Process output without template
fn process_string(
    mut readme: String,
    title: &str,
    badges: &[&str],
    license: Option<&str>,
    add_title: bool,
    add_badges: bool,
    add_license: bool,
) -> Result<String, String> {
    if add_title {
        readme = prepend_title(readme, title);
    }

    if add_badges {
        readme = prepend_badges(readme, badges);
    }

    if add_license {
        if let Some(license) = license {
            readme = append_license(readme, license);
        }
    }

    Ok(readme)
}

/// Prepend badges to output string
fn prepend_badges(readme: String, badges: &[&str]) -> String {
    if badges.len() > 0 {
        let badges = badges.join("\n");
        if !readme.is_empty() {
            format!("{}\n\n{}", badges, readme)
        } else {
            badges
        }
    } else {
        readme
    }
}

/// Prepend title (crate name) to output string
fn prepend_title(readme: String, crate_name: &str) -> String {
    let title = format!("# {}", crate_name);
    if !readme.trim().is_empty() {
        format!("{}\n\n{}", title, readme)
    } else {
        title
    }
}

/// Append license to output string
fn append_license(readme: String, license: &str) -> String {
    let license = format!("License: {}", license);
    if !readme.trim().is_empty() {
        format!("{}\n\n{}", readme, license)
    } else {
        license
    }
}

#[cfg(test)]
mod tests {
    const TEMPLATE_MINIMAL: &str = "{{readme}}";
    const TEMPLATE_WITH_TITLE: &str = "# {{crate}}\n\n{{readme}}";
    const TEMPLATE_WITH_BADGES: &str = "{{badges}}\n\n{{readme}}";
    const TEMPLATE_WITH_LICENSE: &str = "{{readme}}\n\n{{license}}";
    const TEMPLATE_WITH_VERSION: &str = "{{readme}}\n\n{{version}}";
    const TEMPLATE_FULL: &str =
        "{{badges}}\n\n# {{crate}}\n\n{{readme}}\n\n{{license}}\n\n{{version}}";

    // process template
    #[test]
    fn template_without_readme_should_fail() {
        let result = super::process_template(String::new(), String::new(), "", &[], None, "");
        assert!(result.is_err());
        assert_eq!("Missing `{{readme}}` in template", result.unwrap_err());
    }

    #[test]
    fn template_with_badge_tag_but_missing_badges_should_fail() {
        let result = super::process_template(
            TEMPLATE_WITH_BADGES.to_owned(),
            String::new(),
            "",
            &[],
            None,
            "",
        );
        assert!(result.is_err());
        assert_eq!(
            "`{{badges}}` was found in template but no badges were provided",
            result.unwrap_err()
        );
    }

    #[test]
    fn template_with_license_tag_but_missing_license_should_fail() {
        let result = super::process_template(
            TEMPLATE_WITH_LICENSE.to_owned(),
            String::new(),
            "",
            &[],
            None,
            "",
        );
        assert!(result.is_err());
        assert_eq!(
            "`{{license}}` was found in template but no license was provided",
            result.unwrap_err()
        );
    }

    #[test]
    fn template_minimal() {
        let result = super::process_template(
            TEMPLATE_MINIMAL.to_owned(),
            "readme".to_owned(),
            "",
            &[],
            None,
            "",
        );
        assert!(result.is_ok());
        assert_eq!("readme", result.unwrap());
    }

    #[test]
    fn template_with_title() {
        let result = super::process_template(
            TEMPLATE_WITH_TITLE.to_owned(),
            "readme".to_owned(),
            "title",
            &[],
            None,
            "",
        );
        assert!(result.is_ok());
        assert_eq!("# title\n\nreadme", result.unwrap());
    }

    #[test]
    fn template_with_badges() {
        let result = super::process_template(
            TEMPLATE_WITH_BADGES.to_owned(),
            "readme".to_owned(),
            "",
            &["badge1", "badge2"],
            None,
            "",
        );
        assert!(result.is_ok());
        assert_eq!("badge1\nbadge2\n\nreadme", result.unwrap());
    }

    #[test]
    fn template_with_license() {
        let result = super::process_template(
            TEMPLATE_WITH_LICENSE.to_owned(),
            "readme".to_owned(),
            "",
            &[],
            Some("license"),
            "",
        );
        assert!(result.is_ok());
        assert_eq!("readme\n\nlicense", result.unwrap());
    }

    #[test]
    fn template_with_version() {
        let result = super::process_template(
            TEMPLATE_WITH_VERSION.to_owned(),
            "readme".to_owned(),
            "",
            &[],
            None,
            "3.0.1",
        );
        assert!(result.is_ok());
        assert_eq!("readme\n\n3.0.1", result.unwrap());
    }

    #[test]
    fn template_full() {
        let result = super::process_template(
            TEMPLATE_FULL.to_owned(),
            "readme".to_owned(),
            "title",
            &["badge1", "badge2"],
            Some("license"),
            "3.0.2",
        );
        assert!(result.is_ok());
        assert_eq!(
            "badge1\nbadge2\n\n# title\n\nreadme\n\nlicense\n\n3.0.2",
            result.unwrap()
        );
    }

    // process string
    #[test]
    fn render_minimal() {
        let result = super::process_string("readme".to_owned(), "", &[], None, false, false, false);
        assert!(result.is_ok());
        assert_eq!("readme", result.unwrap());
    }

    #[test]
    fn render_title() {
        let result =
            super::process_string("readme".to_owned(), "title", &[], None, true, false, false);
        assert!(result.is_ok());
        assert_eq!("# title\n\nreadme", result.unwrap());
    }

    #[test]
    fn render_badges() {
        let result = super::process_string(
            "readme".to_owned(),
            "",
            &["badge1", "badge2"],
            None,
            false,
            true,
            false,
        );
        assert!(result.is_ok());
        assert_eq!("badge1\nbadge2\n\nreadme", result.unwrap());
    }

    #[test]
    fn render_license() {
        let result = super::process_string(
            "readme".to_owned(),
            "",
            &[],
            Some("license"),
            false,
            false,
            true,
        );
        assert!(result.is_ok());
        assert_eq!("readme\n\nLicense: license", result.unwrap());
    }

    #[test]
    fn render_full() {
        let result = super::process_string(
            "readme".to_owned(),
            "title",
            &["badge1", "badge2"],
            Some("license"),
            true,
            true,
            true,
        );
        assert!(result.is_ok());
        assert_eq!(
            "badge1\nbadge2\n\n# title\n\nreadme\n\nLicense: license",
            result.unwrap()
        );
    }

    #[test]
    fn render_nothing() {
        let result = super::process_string(
            "readme".to_owned(),
            "title",
            &["badge1", "badge2"],
            Some("license"),
            false,
            false,
            false,
        );
        assert!(result.is_ok());
        assert_eq!("readme", result.unwrap());
    }

    // prepend badges
    #[test]
    fn prepend_badges_with_filled_readme_and_non_empty_badges() {
        let result = super::prepend_badges("readme".into(), &["badge1", "badge2"]);
        assert_eq!("badge1\nbadge2\n\nreadme", result);
    }

    #[test]
    fn prepend_badges_with_empty_readme_and_non_empty_badges() {
        let result = super::prepend_badges("".into(), &["badge1", "badge2"]);
        assert_eq!("badge1\nbadge2", result);
    }

    #[test]
    fn prepend_badges_with_filled_readme_and_empty_badges() {
        let result = super::prepend_badges("readme".into(), &[]);
        assert_eq!("readme", result);
    }

    #[test]
    fn prepend_badges_with_empty_readme_and_empty_badges() {
        let result = super::prepend_badges("".into(), &[]);
        assert_eq!("", result);
    }

    // prepend title
    #[test]
    fn prepend_title_with_filled_readme() {
        let result = super::prepend_title("readme".into(), "title");
        assert_eq!("# title\n\nreadme", result);
    }

    #[test]
    fn prepend_title_with_empty_readme() {
        let result = super::prepend_title("".into(), "title");
        assert_eq!("# title", result);
    }

    // append license
    #[test]
    fn append_license_with_filled_readme() {
        let result = super::append_license("readme".into(), "license");
        assert_eq!("readme\n\nLicense: license", result);
    }

    #[test]
    fn append_license_with_empty_readme() {
        let result = super::append_license("".into(), "license");
        assert_eq!("License: license", result);
    }
}
