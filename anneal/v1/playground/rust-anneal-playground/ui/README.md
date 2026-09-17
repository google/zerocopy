## Configuration

When developing, you can place these in a [`.env`][dotenv] file on
disk in this directory.

In production, these should be set according to your deployment method
of choice.

| Key                        | Required | Default Value     | Description                                                                           |
| -------------------------- | -------- | ----------------- | ------------------------------------------------------------------------------------- |
| `PLAYGROUND_UI_ROOT`       | No       |                   | The path to the HTML, CSS, and Javascript files (the directory containing index.html) |
| `PLAYGROUND_GITHUB_TOKEN`  | No       |                   | The [GitHub API token][gist] to read and write Gists                                  |
| `PLAYGROUND_UI_ADDRESS`    | No       | 127.0.0.1         | The address to listen on                                                              |
| `PLAYGROUND_UI_PORT`       | No       | 5000              | The port to listen on                                                                 |
| `PLAYGROUND_METRICS_TOKEN` | No       |                   | If set, will require authentication for the metrics endpoint                          |
| `PLAYGROUND_CORS_ENABLED`  | No       |                   | If set, will enable CORS support                                                      |
| `TMPDIR`                   | No       | system-provided   | Where compilation artifacts will be saved. Must be accessible to Docker               |

[dotenv]: https://crates.io/crates/dotenv
[gist]: https://developer.github.com/v3/gists/#authentication

### Troubleshooting

#### macOS

After launching `ui`, when you try to do any action (ex. `build`, `rustfmt`, `run` and so on), you get errors from Docker about "Mounts denied":

```
docker: Error response from daemon: Mounts denied:
The paths /var/folders/dx/l5pn75zx5v9_cwstvgwc5qyc0000gn/T/playground.6gEHdGUM6XPU/output and /var/folders/dx/l5pn75zx5v9_cwstvgwc5qyc0000gn/T/playground.6gEHdGUM6XPU/input.rs
are not shared from OS X and are not known to Docker.
You can configure shared paths from Docker -> Preferences... -> File Sharing.
See https://docs.docker.com/docker-for-mac/osxfs/#namespaces for more info.
.
time="2099-12-31T00:00:00+00:00" level=error msg="error waiting for container: context canceled"
```

To fix this issue, set the `TMPDIR` environment variable to a path that Docker can mount:

```
mkdir tmp
TMPDIR=$PWD/tmp cargo run
```

(Note: This was reported at [#480](https://github.com/rust-lang/rust-playground/issues/480))
