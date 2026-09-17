use octocrab::Octocrab;

const FILENAME: &str = "playground.rs";
const DESCRIPTION: &str = "Code shared from the Rust Playground";

pub struct Gist {
    pub id: String,
    pub url: String,
    pub code: String,
}

impl From<octocrab::models::gists::Gist> for Gist {
    fn from(other: octocrab::models::gists::Gist) -> Self {
        let mut files: Vec<_> = other
            .files
            .into_iter()
            .map(|(name, file)| (name, file.content.unwrap_or_default()))
            .collect();

        files.sort_by(|(name1, _), (name2, _)| name1.cmp(name2));

        let code = match files.len() {
            0 | 1 => files.into_iter().map(|(_, content)| content).collect(),
            _ => files
                .into_iter()
                .map(|(name, content)| format!("// {name}\n{content}\n\n"))
                .collect(),
        };

        Gist {
            id: other.id,
            url: other.html_url.into(),
            code,
        }
    }
}

pub async fn create_future(token: String, code: String) -> octocrab::Result<Gist> {
    github(token)?
        .gists()
        .create()
        .description(DESCRIPTION)
        .public(false)
        .file(FILENAME, code)
        .send()
        .await
        .map(Into::into)
}

pub async fn load_future(token: String, id: &str) -> octocrab::Result<Gist> {
    let github = github(token)?;

    github.gists().get(id).await.map(Into::into)
}

fn github(token: String) -> octocrab::Result<Octocrab> {
    octocrab::OctocrabBuilder::new()
        .personal_token(token)
        .build()
}
