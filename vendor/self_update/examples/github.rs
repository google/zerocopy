/*!
Example updating an executable to the latest version released via GitHub

`cargo run --example github --features "archive-tar archive-zip compression-flate2 compression-zip-deflate"`.

Include `signatures` in the features list to enable zipsign verification
*/

// For the `cargo_crate_version!` macro
#[macro_use]
extern crate self_update;

fn run() -> Result<(), Box<dyn ::std::error::Error>> {
    let mut rel_builder = self_update::backends::github::ReleaseList::configure();

    #[cfg(feature = "signatures")]
    rel_builder.repo_owner("Kijewski");
    #[cfg(not(feature = "signatures"))]
    rel_builder.repo_owner("jaemk");

    let releases = rel_builder.repo_name("self_update").build()?.fetch()?;
    println!("found releases:");
    println!("{:#?}\n", releases);

    let mut status_builder = self_update::backends::github::Update::configure();

    #[cfg(feature = "signatures")]
    status_builder
        .repo_owner("Kijewski")
        .verifying_keys([*include_bytes!("github-public.key")]);
    #[cfg(not(feature = "signatures"))]
    status_builder.repo_owner("jaemk");

    let status = status_builder
        .repo_name("self_update")
        .bin_name("github")
        .show_download_progress(true)
        //.target_version_tag("v9.9.10")
        //.show_output(false)
        //.no_confirm(true)
        //
        // For private repos, you will need to provide a GitHub auth token
        // **Make sure not to bake the token into your app**; it is recommended
        // you obtain it via another mechanism, such as environment variables
        // or prompting the user for input
        //.auth_token(env!("DOWNLOAD_AUTH_TOKEN"))
        .current_version(cargo_crate_version!())
        .build()?
        .update()?;
    println!("Update status: `{}`!", status.version());
    Ok(())
}

pub fn main() {
    if let Err(e) = run() {
        println!("[ERROR] {}", e);
        ::std::process::exit(1);
    }
}
