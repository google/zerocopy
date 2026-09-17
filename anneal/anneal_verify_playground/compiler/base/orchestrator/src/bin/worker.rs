use orchestrator::worker::{listen, Error};
use std::env;

#[tokio::main(flavor = "current_thread")]
#[snafu::report]
pub async fn main() -> Result<(), Error> {
    let project_dir = env::args_os()
        .nth(1)
        .expect("Please specify project directory as the first argument");

    listen(project_dir).await
}
