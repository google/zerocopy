These unmodified Lake configurations are regression inputs for vendoring, not
dependency pins. They come from the dependency revisions in Anneal's pinned
Aeneas archive:

- `aesop.toml`: aesop `e3cb2f741431ce31bf73549fb52316a57368b06f`.
- `importGraph.toml`: import-graph `5c7542ed018c78194f1e2b903eaf6a792b74c03d`.

Both projects distribute these files under Apache-2.0; see the repository's
`LICENSE-APACHE`. The regression checks that replacing a remote dependency does
not remove the library and executable declarations that follow it.
