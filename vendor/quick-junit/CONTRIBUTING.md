## Pull Requests

If you have a new feature in mind, please discuss the feature in an issue to ensure that your
contributions will be accepted.

1. Fork the repo and create your branch from `main`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes with `cargo nextest run --all-features`.
5. Run `cargo xfmt` to automatically format your changes (CI will let you know if you missed this).

## Logically Separate Commits

As far as possible, please try and make commits
[atomic](https://en.wikipedia.org/wiki/Atomic_commit#Atomic_commit_convention) and logically
separate. We understand that GitHub's pull request model doesn't work well with "stacked diffs", so
if your changes are complex, then a single PR with a series of commits is preferred.

## Bisectable History

It is important that the project history is bisectable, so that when regressions are identified we
can easily use `git bisect` to be able to pinpoint the exact commit which introduced the regression.
We'll land your commits with:

- "Rebase and merge" if your commits are atomic and each commit passes CI.
- "Squash and merge" if they are not.

## Maintainers Editing Commits

For efficiency reasons, maintainers may choose to edit your commits before landing them. The commits
will still be credited to you, and the edits will be limited to reasonable changes that are in the
spirit of the PR. (Think of the changes that the maintainers would have done anyway.)

To make this easier, please check the box that allows maintainers to edit your branch:

![Screenshot of GitHub new pull request page, showing "Allow edits and access to secrets by maintainers" checked](https://github.com/nextest-rs/quick-junit/assets/180618/9f4074fa-4f52-4735-af19-144464f0fb8d)

If maintainers need to make changes and that box is checked, then your PR can be marked as "merged"
in the web UI. Otherwise, it will be marked as "closed".

## License

By contributing to `quick-junit`, you agree that your contributions will be dual-licensed under the
terms of the [`LICENSE-MIT`](LICENSE-MIT) and [`LICENSE-APACHE`](LICENSE-APACHE) files in the root
directory of this source tree.
