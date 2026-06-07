window.BENCHMARK_DATA = {
  "lastUpdate": 1780793139145,
  "repoUrl": "https://github.com/google/zerocopy",
  "entries": {
    "Docker Image Size": [
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "ad9d69b15961fba811a2049c2fedc22da62afce2",
          "message": "[ci][anneal] Install fewer, smaller Rust toolchains (#3277)\n\nNow that `cargo anneal setup` downloads Rust toolchains (specifically,\nthe toolchain pinned by Charon), we no longer need to separately install\nthese when setting up the Docker image. We also pass `--minimal` when\ninstalling the default toolchain.\n\ngherrit-pr-id: Gtk6iuxmege4csoh6ypqysrrdt47l6luz",
          "timestamp": "2026-04-15T21:58:13-04:00",
          "tree_id": "a38c480ad74f28c3baa0cbd39a142e60a4fccecc",
          "url": "https://github.com/google/zerocopy/commit/ad9d69b15961fba811a2049c2fedc22da62afce2"
        },
        "date": 1776305579264,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9850,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "962a5a3a82822f05b6201d475e737a1615f28f3e",
          "message": "[ci][anneal] Track more metrics in dashboard (#3279)\n\ngherrit-pr-id: Gx7nzhourvbqnu7rpvavtjhunxbi4xsbn",
          "timestamp": "2026-04-16T05:27:28-04:00",
          "tree_id": "0570063aab2555920ed432be9f4d5b64b05a7dc7",
          "url": "https://github.com/google/zerocopy/commit/962a5a3a82822f05b6201d475e737a1615f28f3e"
        },
        "date": 1776331906164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9850,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "15639839eafdc9f22448b1e2d6c30ff45f80f080",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow (#3281)\n\nTo automate the creation of precompiled artifacts for the Anneal\ntoolchain, we add a build script and integrate it into the release\nworkflow. This will allow us to simplify the `setup` command to simply\ndownload these pre-built artifacts from a single location, avoid needing\nto build from source on the user's machine, and download fewer artifacts\n(in particular, stripping out Mathlib modules which are unused by\nAnneal). This is especially important for development *on* Anneal and\nfor CI, which run the `setup` command frequently.\n\ngherrit-pr-id: Gigvceuv7utvaq4hymnx3dl22qewo6vuz",
          "timestamp": "2026-04-16T14:28:47Z",
          "tree_id": "b585065db60a134b371f49b13b9b75c1406b6d8d",
          "url": "https://github.com/google/zerocopy/commit/15639839eafdc9f22448b1e2d6c30ff45f80f080"
        },
        "date": 1776351093601,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9850,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be",
          "message": "[anneal] Release 0.1.0-alpha.18 (#3282)\n\ngherrit-pr-id: Gkbtn5ebnp72mu2i4uwnpr35uwig5qgwq",
          "timestamp": "2026-04-16T15:36:32Z",
          "tree_id": "f541fb5afc67bec6cf778ed136875845b1c6d3d0",
          "url": "https://github.com/google/zerocopy/commit/0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be"
        },
        "date": 1776356119353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9848,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "748177693d1907006da102d49fd71071504b10ca",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job (#3283)\n\ngherrit-pr-id: Gcqmoot6ezcmsbvzyvus2klwwinl46j37",
          "timestamp": "2026-04-16T11:39:48-07:00",
          "tree_id": "f397797cfc16d3c01e639fdb3a59128b75858959",
          "url": "https://github.com/google/zerocopy/commit/748177693d1907006da102d49fd71071504b10ca"
        },
        "date": 1776364929918,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9848,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b943232a98fa7c9994151a765d52b1989a982048",
          "message": "[ci][anneal] Add `workflow_dispatch` Action to release new version (#3284)\n\nRelease 0.1.0-alpha.19.\n\ngherrit-pr-id: G3sy75s2atk44kjhhoymwugs6wvpbfn4t",
          "timestamp": "2026-04-16T15:19:24-04:00",
          "tree_id": "c9f611ffd299eb3e0e9dea4702f3b30b5189fedb",
          "url": "https://github.com/google/zerocopy/commit/b943232a98fa7c9994151a765d52b1989a982048"
        },
        "date": 1776368017180,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "479bc21ac4356293462e7d3a73f65ce7fbefa3cf",
          "message": "[ci][anneal] Add manual trigger to publish precompiled artifacts (#3286)\n\nThis is part of a soft migration to the new system. It allows us to\npublish precompiled artifacts that will let us land a subsequent commit\nwhich makes use of them in `cargo-anneal`.\n\ngherrit-pr-id: Grdbltxkqkgnaqxnlrx4425qspr7nqrmw",
          "timestamp": "2026-04-18T08:16:10-04:00",
          "tree_id": "d591da17dc3a317f0821cf55f77f93344036f3b2",
          "url": "https://github.com/google/zerocopy/commit/479bc21ac4356293462e7d3a73f65ce7fbefa3cf"
        },
        "date": 1776514789126,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d",
          "message": "[ci][anneal] Make concurrency group dynamic by branch/PR (#3287)\n\ngherrit-pr-id: Gofynwkutejony366jjuzz2odt4a56v2g",
          "timestamp": "2026-04-18T08:25:45-04:00",
          "tree_id": "7c11975b9cc8f34223d23b1c0a55a4460f99c5ae",
          "url": "https://github.com/google/zerocopy/commit/b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d"
        },
        "date": 1776515364269,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2e69086d4e8951404a0ff12b31da02ae4950f589",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error (#3288)\n\ngherrit-pr-id: Gtfo4rh2ird3aqm57btkd3l7zpsknc7y7",
          "timestamp": "2026-04-18T08:53:08-04:00",
          "tree_id": "6a3c4dbb13fa3fb4e2edbacc36b7a98143e5342c",
          "url": "https://github.com/google/zerocopy/commit/2e69086d4e8951404a0ff12b31da02ae4950f589"
        },
        "date": 1776517018559,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec",
          "message": "[ci][anneal] Use unique tags for manual artifact releases (#3289)\n\ngherrit-pr-id: Gqrfvtkdyjezdwwai5d37vq5omydsrajc",
          "timestamp": "2026-04-18T09:51:02-04:00",
          "tree_id": "457b1ff2bfdd5f79fd50c5e190a8047b24ace7ee",
          "url": "https://github.com/google/zerocopy/commit/f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec"
        },
        "date": 1776520481691,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "00c910938978083a5405faed719ca02dcec730ad",
          "message": "[ci][anneal] When publishing, prune Mathlib rather than removing it (#3290)\n\ngherrit-pr-id: Gob4ak2l443wyguc6vd6uej7wndlqzhis",
          "timestamp": "2026-04-18T11:18:01-04:00",
          "tree_id": "f83185dc52b9877770089fc9e13f3aba0ca5dab7",
          "url": "https://github.com/google/zerocopy/commit/00c910938978083a5405faed719ca02dcec730ad"
        },
        "date": 1776525751202,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b04142396963357c0bf3cf3d9e42e21070e38bfb",
          "message": "[ci][anneal] Fix sysroot layout and exclude tests in builder script (#3291)\n\ngherrit-pr-id: Gxhjefmzsst6q46o4l36bblw2nfrkwncy",
          "timestamp": "2026-04-18T14:15:01-04:00",
          "tree_id": "aa056420098859d5eb3a1185b40c9c371163e624",
          "url": "https://github.com/google/zerocopy/commit/b04142396963357c0bf3cf3d9e42e21070e38bfb"
        },
        "date": 1776536302587,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fbdeab52de993f2bad6b650acd6aa8353d9edc89",
          "message": "[ci][anneal] In release, don't build tests; fix location of charon artifacts (#3293)\n\ngherrit-pr-id: Gblquwd2ikf5wze73xm7jfvth2rkkodn4",
          "timestamp": "2026-04-18T14:29:47-04:00",
          "tree_id": "58dd5ab95050f64eb5daeb42cd0f16b5db09d1e4",
          "url": "https://github.com/google/zerocopy/commit/fbdeab52de993f2bad6b650acd6aa8353d9edc89"
        },
        "date": 1776537200686,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "234b7e0927728428e836aa455a1960bca7cd52c3",
          "message": "[ci][anneal] Remove tests before building Lean library in release (#3294)\n\ngherrit-pr-id: Gzcu4ycvlg2exazk6idhxol3x7mrndvgg",
          "timestamp": "2026-04-18T16:48:59-04:00",
          "tree_id": "4e11b4b4883ef6eb56a4c282538d0d5c9ce4d421",
          "url": "https://github.com/google/zerocopy/commit/234b7e0927728428e836aa455a1960bca7cd52c3"
        },
        "date": 1776545564558,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "62d9816418bdb3d566381c1a4070784f7cf5380e",
          "message": "[ci][anneal] Unset CI variable to force precompilation in release (#3295)\n\ngherrit-pr-id: Gqyhjsrpqtnwssq7yrc7pgbciwjphfzjb",
          "timestamp": "2026-04-19T04:43:16-04:00",
          "tree_id": "1dafb6b1066e3e9fb1d974499739b7f95db50bcf",
          "url": "https://github.com/google/zerocopy/commit/62d9816418bdb3d566381c1a4070784f7cf5380e"
        },
        "date": 1776588422075,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c97dbc6586c7c62decf3263c180e089f1c0f2771",
          "message": "[ci][anneal] Add workflow_dispatch argument for zstd compression level (#3296)\n\ngherrit-pr-id: Gqzpjc5efiwdcr4aqpzvz5nft7wfg43yo",
          "timestamp": "2026-04-19T04:52:09-04:00",
          "tree_id": "cb8d60712d6a66ca7c073d3f562146adac18c677",
          "url": "https://github.com/google/zerocopy/commit/c97dbc6586c7c62decf3263c180e089f1c0f2771"
        },
        "date": 1776588966385,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "3a99d7582663d8082df5b23ed4fd793b4e124211",
          "message": "[anneal] Make logo stroke width thicker (#3300)\n\ngherrit-pr-id: G6f3ij3lhnfnk4nvvj2ogaihrcweoqglb",
          "timestamp": "2026-04-20T08:40:34Z",
          "tree_id": "aa347751babb591182f2408e231a3bd5157aa8ac",
          "url": "https://github.com/google/zerocopy/commit/3a99d7582663d8082df5b23ed4fd793b4e124211"
        },
        "date": 1776675744089,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9849,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d410c162d51977635ca5afac67d99a3b10327a94",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep (#3304)\n\n- Store build artifacts in a user-global Lean content-addressed artifact\n  cache, populating it during `setup`.\n- Specify the dependency on the Aeneas Lean library as follows:\n  - During `setup`, initialize the Aeneas Lean library as a git repo\n  - During `generate`/`verify`, specify the dependency as a git\n    dependency on a local filesystem path\n\nPrior to this change, we specified the dependency as a non-git\nfilesystem dep, which had the effect of causing Lean to think it could\nmutate the user-global directory, causing races when multiple `anneal`\ncommands were run in parallel.\n\nRelease 0.1.0-alpha.20\n\ngherrit-pr-id: Gyo2pqvhru3x4cyrj6bhrnjtx7gamwkfr",
          "timestamp": "2026-04-20T23:47:08Z",
          "tree_id": "7e016397325b6d9523d680ba36126c476aaa7aa6",
          "url": "https://github.com/google/zerocopy/commit/d410c162d51977635ca5afac67d99a3b10327a94"
        },
        "date": 1776731406940,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11191,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "11515dce44b88a626b31d1fea053754dcb7331ca",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup (#3305)\n\n- Remove obsolete worker pool and smart cache cloning from integration\n  tests\n- Configure tests to use the shared global Lean artifact cache via\n  `LAKE_CACHE_DIR`\n- Simplify `src/setup.rs` by assuming only fresh installations:\n  - Remove `verify_tools` and individual binary checksums for Aeneas\n  - Simplify toolchain directory hashing to use the Rust tag\n  - Make installation and Git initialization unconditional\n- Implement atomic installation in `setup` using a temporary directory\n  and rename\n- Remove setup-related tests which are less useful now, and will become\n  even less useful than that going forward as we simplify the setup\n  logic\n\nPrior to this change, the integration tests relied on a complex worker\npool and symlinking infrastructure to isolate tests and share build\nartifacts. This required large amounts of disk space (e.g., a specific\nrun with ~100 parallel worker threads and caches consumed ~100GB). In\nthis commit, removing the worker pool and cache cloning approach lets us\nsave significant disk space usage during integration test runs.\n\ngherrit-pr-id: G4c76oil24wlyjqav3c5s5woakn5rcxpm",
          "timestamp": "2026-04-21T10:28:40Z",
          "tree_id": "833adf0febc61c567363031fad512ce313ed7401",
          "url": "https://github.com/google/zerocopy/commit/11515dce44b88a626b31d1fea053754dcb7331ca"
        },
        "date": 1776770322949,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 9812,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9329ada1b2801e305cd00db7c62b6987f8b7c80c",
          "message": "[anneal] In `setup`, recursively cache Lean sources (#3306)\n\nInitialize all transitive Lean library dependencies of the Aeneas Lean\nlibrary as local Git repositories, and rewrite dependencies to point to\nthese as filesystem-local Git remotes. During `verify`, `lake build`\nclones any source code it doesn't already have access to. This ensures\nthat this at least clones from the local filesystem instead of from the\ninternet.\n\ngherrit-pr-id: Ghmd3zurxjuy6q66eay4blnbt7sfg7wlz",
          "timestamp": "2026-04-21T21:21:56Z",
          "tree_id": "35fb101371c1e4ebb6fb1c0798abadb812c383ed",
          "url": "https://github.com/google/zerocopy/commit/9329ada1b2801e305cd00db7c62b6987f8b7c80c"
        },
        "date": 1776809699339,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16277,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a27cb57734782db8f7ba9da14e3aa8fd6ea200f9",
          "message": "[ci][anneal] Track total CI duration in benchmark dashboard (#3323)",
          "timestamp": "2026-04-22T11:11:58Z",
          "tree_id": "22f1c20b8a2fe8fc6e2010a70b7e0c0b573332b6",
          "url": "https://github.com/google/zerocopy/commit/a27cb57734782db8f7ba9da14e3aa8fd6ea200f9"
        },
        "date": 1776857364610,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16277,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a51752bdff4d521681a8c2d5d97396015114d6d8",
          "message": "[anneal] Isolate docker images, not just volumes (#3322)",
          "timestamp": "2026-04-22T11:31:34Z",
          "tree_id": "733e7fc815782bd3e1b3ba6ad4af32aa90a0566f",
          "url": "https://github.com/google/zerocopy/commit/a51752bdff4d521681a8c2d5d97396015114d6d8"
        },
        "date": 1776858647728,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16277,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f896a6890a1e6feb01d3c26364bf674f0573321e",
          "message": "[anneal][README] Document TCB shrinking (#3326)\n\ngherrit-pr-id: Gy4y7cstkui5s6c7jletzjbu37xtjglxm",
          "timestamp": "2026-04-28T18:10:09Z",
          "tree_id": "04fd33df84b5b512246673abd226b3bf491693a7",
          "url": "https://github.com/google/zerocopy/commit/f896a6890a1e6feb01d3c26364bf674f0573321e"
        },
        "date": 1777401765380,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16277,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc525228994b0eafbc600981e1955f2f442c5e0b",
          "message": "[anneal][README] Tighten wording (#3328)\n\nRelease 0.1.0-alpha.21.\n\ngherrit-pr-id: Ggwzrriapr76e6dx74cv4skvdp7ikd37h",
          "timestamp": "2026-04-28T23:20:52Z",
          "tree_id": "ed7bfb5b08e51dfc389d3beadf64648ab5bea3b3",
          "url": "https://github.com/google/zerocopy/commit/bc525228994b0eafbc600981e1955f2f442c5e0b"
        },
        "date": 1777421515640,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16282,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c67c8ecc912d7f45e68b5274de789a15b42cf4aa",
          "message": "[ci] Run Anneal jobs on free-tier runners (#3330)\n\ngherrit-pr-id: Gl375z4s3fozt4u74gde7bzsp3ey4fi3n",
          "timestamp": "2026-05-01T17:07:29Z",
          "tree_id": "a24079fd4d2bb340570f054bd0bf6c414eba80f0",
          "url": "https://github.com/google/zerocopy/commit/c67c8ecc912d7f45e68b5274de789a15b42cf4aa"
        },
        "date": 1777657905310,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 16282,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "be6f199fdbe4e568ac63289e2bdbd4a5f783d444",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal` (#3344)\n\nPrior to this change, Lake verification relied on recursively copying\nthe entire global precompiled toolchain package directory (~5,000\n`.olean` files, ~5GB) into a build directory. This was obviously slow\nand caused massive disk bloat.\n\nIn this commit, we instead:\n- Copy only those files which Lake will attempt to write, and symlink\n  all other files. In practice, this means that only the smallest files\n  are actually copied. (Note: Copying is necessary *at all* because Lake\n  will write to some files in the directories of a package's\n  *dependencies* if those dependencies are filesystem-local. Without\n  copying, this would result in concurrent writes to the user-global\n  `~/.anneal/toolchain` directory.)\n- Mark the `~/.anneal/toolchain/<toolchain>` directory as recursively\n  read-only to ensure that any attempted writes fail loudly.\n\nRelease 0.1.0-alpha.22.\n\ngherrit-pr-id: Gks63dnqyjzxt6s6sgowdaz63rogw5kz3",
          "timestamp": "2026-05-06T19:44:41Z",
          "tree_id": "73f8ba779cf997b8e10d15cfb9573283a6ee505b",
          "url": "https://github.com/google/zerocopy/commit/be6f199fdbe4e568ac63289e2bdbd4a5f783d444"
        },
        "date": 1778099907151,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11598,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a3ad195abf85896be6f07f11acb486ceb7d61900",
          "message": "[anneal] README: Explain philosophy w.r.t. typing (#3351)\n\nRelease 0.1.0-alpha.23.\n\ngherrit-pr-id: Gpeqma2krsi7flwaeyjlum23s7znxuhms",
          "timestamp": "2026-05-18T16:03:33-04:00",
          "tree_id": "42557b2a78eba0ec7aaa24b045a0f4e098ac18eb",
          "url": "https://github.com/google/zerocopy/commit/a3ad195abf85896be6f07f11acb486ceb7d61900"
        },
        "date": 1779135862350,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "8772fc4b3c36778c5cdb4adc7eaa8825541b2418",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T23:46:42Z",
          "tree_id": "fe5018c83ed57d2fd917f95cfbc9e62e4d068c89",
          "url": "https://github.com/google/zerocopy/commit/8772fc4b3c36778c5cdb4adc7eaa8825541b2418"
        },
        "date": 1779236391310,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "0402dfa593751057a357c89fb8bd140780abd8d5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg` (#3387)\n\nRelease 0.8.49-alpha.\n\ngherrit-pr-id: Gblc7dfltwcey7wvtj3gjkseaqcltgwvf",
          "timestamp": "2026-05-21T13:53:30Z",
          "tree_id": "4107ade63e23461c265e5d6eac61e3103e733349",
          "url": "https://github.com/google/zerocopy/commit/0402dfa593751057a357c89fb8bd140780abd8d5"
        },
        "date": 1779373968315,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "881160631750e2e1a5876327f5f14804a77d4cc8",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs (#3388)\n\ngherrit-pr-id: G7p44q5rcehvy46vrrowj5vxxkgp3xuw7",
          "timestamp": "2026-05-21T15:41:06Z",
          "tree_id": "fd526a60e3a69ed5ade2900feffae0c14d7ab32b",
          "url": "https://github.com/google/zerocopy/commit/881160631750e2e1a5876327f5f14804a77d4cc8"
        },
        "date": 1779380143954,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2fcfb3371cdc0f6ca1c16ab6c18253de09194113",
          "message": "[anneal][v2] Initial commit of `exocrate` (#3376)\n\ngherrit-pr-id: G34qjom3lz7cc6hd57tgp44t4pzlstdhj\n\nCo-authored-by: Mark Dittmer <markdittmer@google.com>",
          "timestamp": "2026-05-25T15:20:48-04:00",
          "tree_id": "602fe9e513bae3aa5ba6dcf91e4b5b93cf8d59dd",
          "url": "https://github.com/google/zerocopy/commit/2fcfb3371cdc0f6ca1c16ab6c18253de09194113"
        },
        "date": 1779737022121,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "275aff21f3b22c4c4db0311576b897b8d5805fa8",
          "message": "[anneal][v2] Independently vendor and patch toml_const (#3381)\n\n- Vendor `anneal/v2` dependencies independently\n- Patch `toml_const` to avoid breakage on `'cfg(...)'` keys in\n  `Cargo.toml` files\n\ngherrit-pr-id: Ga27arw5h5oz3ldi25ijsj2rsbzuqictv",
          "timestamp": "2026-05-25T19:51:17Z",
          "tree_id": "bb9133d186a3e0b671544c47ee9211654e81bc5f",
          "url": "https://github.com/google/zerocopy/commit/275aff21f3b22c4c4db0311576b897b8d5805fa8"
        },
        "date": 1779740713029,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0321b8e7055ae7159280930753924207775dc35a",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0 (#3415)\n\ngherrit-pr-id: Gz2xxcekiwax6yzlsfzuwlzh4mcfd5nms",
          "timestamp": "2026-05-26T16:20:03Z",
          "tree_id": "0b33f6617272bf085e9e17ced8468c3c66b75681",
          "url": "https://github.com/google/zerocopy/commit/0321b8e7055ae7159280930753924207775dc35a"
        },
        "date": 1779814509629,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "145818923+google-pr-creation-bot@users.noreply.github.com",
            "name": "Google PR Creation Bot",
            "username": "google-pr-creation-bot"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5fc5d5bef889bbf81ab5bae500758979d5978a08",
          "message": "Release 0.8.49 (#3417)",
          "timestamp": "2026-05-27T11:55:29-04:00",
          "tree_id": "4b298b6678caa62663f284dce3339ee15b73f7cd",
          "url": "https://github.com/google/zerocopy/commit/5fc5d5bef889bbf81ab5bae500758979d5978a08"
        },
        "date": 1779897492200,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f70e4224996ed73b2cd927719246361d977a629e",
          "message": "[pointer] `Ptr::iter` takes `self` by value (#3421)\n\nThis fixes a prior soundness hole - `Ptr::iter` took `&self`, permitting\nmultiple overlapping `Exclusive` `Ptr`s to be created at the same time.\n\nIn CI, when running `cargo-semver-checks`, don't pass `--cfg\nzerocopy_unstable_ptr`, as we don't want to semver-check unstable APIs.\n\nRelease 0.8.50.\n\nFixes #3419\n\ngherrit-pr-id: Ibb7d512d9e12ecfd118bb018bcae10d17279c2ed",
          "timestamp": "2026-05-29T17:01:13Z",
          "tree_id": "5d0f67bd945a1ceeab35e9cc06db105ebf037300",
          "url": "https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e"
        },
        "date": 1780076364072,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cf7cf6154867078e8b994ae981959edffaf724a9",
          "message": "Handle fork PR Docker cache permissions (#3423)\n\n### Motivation\n- External fork PRs were failing CI at Docker build/cache steps because the runner `GITHUB_TOKEN` for forks does not have permission to write GHCR packages or cache entries.\n\n### Description\n- In `.github/workflows/ci.yml` conditionally disable `cache-to` exports to GHCR for external pull requests while preserving cache exports for same-repo runs, pushes, merge groups, and workflow dispatches.\n- In `.github/workflows/anneal.yml` conditionally disable `cache-to` and guard the `Build and push Docker image` step so image push/cache writes are only attempted when the run is allowed to write to GHCR.\n- In `.github/workflows/anneal.yml` add `if:` guards on Anneal consumer jobs (`anneal_tests` and `verify_examples`) so those consumer jobs are skipped for external fork PRs that cannot publish the GHCR image they would consume.\n\n### Testing\n- Ran `./ci/check_actions.sh` and it completed successfully.\n- Ran `git diff --check` and it produced no issues.\n- Ran `CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 ./githooks/pre-push` to exercise the repo hooks in a non-interactive way and it completed successfully (the initial pre-push without auto-install hit local tooling prompts).",
          "timestamp": "2026-05-31T19:36:24Z",
          "tree_id": "0c131497ef5db2f7d6f3a9f16795ee729af0212b",
          "url": "https://github.com/google/zerocopy/commit/cf7cf6154867078e8b994ae981959edffaf724a9"
        },
        "date": 1780258254338,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11596,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cacc81c2bdb1efa169bed1dda231d89590539f7b",
          "message": "[ci][anneal] Don't publish fork PR benchmarks (#3430)",
          "timestamp": "2026-06-03T13:54:01-07:00",
          "tree_id": "489e52a87f260a77311791b511785c53a13c281d",
          "url": "https://github.com/google/zerocopy/commit/cacc81c2bdb1efa169bed1dda231d89590539f7b"
        },
        "date": 1780521405771,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11674,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "87631534+platonicsock@users.noreply.github.com",
            "name": "Sock",
            "username": "platonicsock"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bd37d45186e8f846df74da6f2d17ded4e19b4bd4",
          "message": "Typo fixes (#3425)\n\nTwo instances of changing \"Anneal'\" to \"Anneal's\"",
          "timestamp": "2026-06-03T14:30:13-07:00",
          "tree_id": "735cf8abf0171da25ea8da7e0e8363d301df4f0a",
          "url": "https://github.com/google/zerocopy/commit/bd37d45186e8f846df74da6f2d17ded4e19b4bd4"
        },
        "date": 1780522677771,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11674,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a773081477608b799ccdd48de490de139e19873c",
          "message": "[zerocopy] Move to `zerocopy` subdirectory (#3434)\n\nMove the Zerocopy crate and its vendored Cargo configuration under\n`zerocopy/`, and update CI, docs, hooks, and helper scripts to run\nzerocopy commands from that directory.\n\nThis keeps zerocopy in its own vendored Cargo world while allowing\ntools, Anneal, and future crates to use normal Cargo resolution and not\nrequire vendoring their dependencies.\n\nAlso move `anneal/v2/exocrate` to the repository root.\n\ngherrit-pr-id: Ghuilhfh6h4womt35vc6domtloovmnnhl",
          "timestamp": "2026-06-05T04:04:48Z",
          "tree_id": "60647c9d9df642af06edc6597d6f373d203aaccc",
          "url": "https://github.com/google/zerocopy/commit/a773081477608b799ccdd48de490de139e19873c"
        },
        "date": 1780634388236,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11674,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc0bb77346772be0e80aeb68f8f3f9b2e58a1612",
          "message": "Bump the cargo group across 1 directory with 4 updates (#3435)\n\nBumps the cargo group with 4 updates in the /anneal directory: [tar](https://github.com/composefs/tar-rs), [openssl](https://github.com/rust-openssl/rust-openssl), [rand](https://github.com/rust-random/rand) and [rustls-webpki](https://github.com/rustls/webpki).\n\n\nUpdates `tar` from 0.4.45 to 0.4.46\n- [Release notes](https://github.com/composefs/tar-rs/releases)\n- [Commits](https://github.com/composefs/tar-rs/compare/0.4.45...0.4.46)\n\nUpdates `openssl` from 0.10.76 to 0.10.80\n- [Release notes](https://github.com/rust-openssl/rust-openssl/releases)\n- [Commits](https://github.com/rust-openssl/rust-openssl/compare/openssl-v0.10.76...openssl-v0.10.80)\n\nUpdates `rand` from 0.9.2 to 0.9.4\n- [Release notes](https://github.com/rust-random/rand/releases)\n- [Changelog](https://github.com/rust-random/rand/blob/0.9.4/CHANGELOG.md)\n- [Commits](https://github.com/rust-random/rand/compare/rand_core-0.9.2...0.9.4)\n\nUpdates `rustls-webpki` from 0.103.10 to 0.103.13\n- [Release notes](https://github.com/rustls/webpki/releases)\n- [Commits](https://github.com/rustls/webpki/compare/v/0.103.10...v/0.103.13)\n\n---\nupdated-dependencies:\n- dependency-name: tar\n  dependency-version: 0.4.46\n  dependency-type: direct:production\n  dependency-group: cargo\n- dependency-name: openssl\n  dependency-version: 0.10.80\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rand\n  dependency-version: 0.9.4\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rustls-webpki\n  dependency-version: 0.103.13\n  dependency-type: indirect\n  dependency-group: cargo\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>",
          "timestamp": "2026-06-05T05:08:07Z",
          "tree_id": "46c88fe74ea7fb7b5b5974d81872b4129e09ac82",
          "url": "https://github.com/google/zerocopy/commit/bc0bb77346772be0e80aeb68f8f3f9b2e58a1612"
        },
        "date": 1780639309725,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11650,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "laniel_francis@privacyrequired.com",
            "name": "eiffel-fl",
            "username": "eiffel-fl"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "c97143cb09c7edb578c4a9edaf50d8db720f60a9",
          "message": "[byteorder] Add cfg no_fp_fmt_parse (#3429)\n\nThis cfg deactivates Debug and Display for floatting point numbers, this is\nparticluarly useful in kernel context.\nThe implementation is inspired by:\nhttps://github.com/rust-lang/rust/commit/ec7292ad3c35\n\nFixes #3426",
          "timestamp": "2026-06-05T13:59:43Z",
          "tree_id": "6709fbc182f55d749bc31796fd2fb83d2e017624",
          "url": "https://github.com/google/zerocopy/commit/c97143cb09c7edb578c4a9edaf50d8db720f60a9"
        },
        "date": 1780670073913,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11650,
            "unit": "Megabytes"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b7d9acf849ef9791776ad100da386ac67b8a8a60",
          "message": "[anneal][v2] Add and integrate nix-built exocrate (#3383)\n\n- Add nix derivations for exocrate\n- Add `setup` sub-command to locate-or-install exocrate\n- Add integration test for \"developer mode\" `setup` that presumes local\n  exocrate archive\n- Add github workflows to:\n  - Warm nix cache\n  - Locally link exocrate archive from nix, then run all tests\n\ngherrit-pr-id: Gwhroikc5idscowxamayknlke2uiddzv3",
          "timestamp": "2026-06-05T18:00:27-04:00",
          "tree_id": "ead44d2b940c9097c6db13604d193d3f48190e3e",
          "url": "https://github.com/google/zerocopy/commit/b7d9acf849ef9791776ad100da386ac67b8a8a60"
        },
        "date": 1780697039289,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Image Size",
            "value": 11650,
            "unit": "Megabytes"
          }
        ]
      }
    ],
    "Docker Build Time": [
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9aff71ca5af1f9bf05382c0ad6a8bbb1cb9cf8cd",
          "message": "[ci][anneal] Track more metrics in dashboard",
          "timestamp": "2026-04-16T01:58:18Z",
          "url": "https://github.com/google/zerocopy/pull/3279/commits/9aff71ca5af1f9bf05382c0ad6a8bbb1cb9cf8cd"
        },
        "date": 1776306898438,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bccab1f6c5b371ddbcfe2eaa2cd63ef14c30c970",
          "message": "[ci][anneal] Track more metrics in dashboard",
          "timestamp": "2026-04-16T01:58:18Z",
          "url": "https://github.com/google/zerocopy/pull/3279/commits/bccab1f6c5b371ddbcfe2eaa2cd63ef14c30c970"
        },
        "date": 1776307100135,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "962a5a3a82822f05b6201d475e737a1615f28f3e",
          "message": "[ci][anneal] Track more metrics in dashboard (#3279)\n\ngherrit-pr-id: Gx7nzhourvbqnu7rpvavtjhunxbi4xsbn",
          "timestamp": "2026-04-16T05:27:28-04:00",
          "tree_id": "0570063aab2555920ed432be9f4d5b64b05a7dc7",
          "url": "https://github.com/google/zerocopy/commit/962a5a3a82822f05b6201d475e737a1615f28f3e"
        },
        "date": 1776331687681,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "af4f6c55393e631f101312618a205613e27f1a21",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T09:27:34Z",
          "url": "https://github.com/google/zerocopy/pull/3280/commits/af4f6c55393e631f101312618a205613e27f1a21"
        },
        "date": 1776342511777,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f2557edfe3700e59ab0aa4667d9565211b19815d",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T09:27:34Z",
          "url": "https://github.com/google/zerocopy/pull/3281/commits/f2557edfe3700e59ab0aa4667d9565211b19815d"
        },
        "date": 1776343678028,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4ae7abd41d63c34fe97977ca584b3fdbf737ae45",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T09:27:34Z",
          "url": "https://github.com/google/zerocopy/pull/3281/commits/4ae7abd41d63c34fe97977ca584b3fdbf737ae45"
        },
        "date": 1776343849245,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4eec77e0a32ad6648b8ab7fe96cbc983bb75ecaf",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T12:55:23Z",
          "url": "https://github.com/google/zerocopy/pull/3281/commits/4eec77e0a32ad6648b8ab7fe96cbc983bb75ecaf"
        },
        "date": 1776348999761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "15639839eafdc9f22448b1e2d6c30ff45f80f080",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow (#3281)\n\nTo automate the creation of precompiled artifacts for the Anneal\ntoolchain, we add a build script and integrate it into the release\nworkflow. This will allow us to simplify the `setup` command to simply\ndownload these pre-built artifacts from a single location, avoid needing\nto build from source on the user's machine, and download fewer artifacts\n(in particular, stripping out Mathlib modules which are unused by\nAnneal). This is especially important for development *on* Anneal and\nfor CI, which run the `setup` command frequently.\n\ngherrit-pr-id: Gigvceuv7utvaq4hymnx3dl22qewo6vuz",
          "timestamp": "2026-04-16T14:28:47Z",
          "url": "https://github.com/google/zerocopy/commit/15639839eafdc9f22448b1e2d6c30ff45f80f080"
        },
        "date": 1776349779762,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "15639839eafdc9f22448b1e2d6c30ff45f80f080",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow (#3281)\n\nTo automate the creation of precompiled artifacts for the Anneal\ntoolchain, we add a build script and integrate it into the release\nworkflow. This will allow us to simplify the `setup` command to simply\ndownload these pre-built artifacts from a single location, avoid needing\nto build from source on the user's machine, and download fewer artifacts\n(in particular, stripping out Mathlib modules which are unused by\nAnneal). This is especially important for development *on* Anneal and\nfor CI, which run the `setup` command frequently.\n\ngherrit-pr-id: Gigvceuv7utvaq4hymnx3dl22qewo6vuz",
          "timestamp": "2026-04-16T14:28:47Z",
          "tree_id": "b585065db60a134b371f49b13b9b75c1406b6d8d",
          "url": "https://github.com/google/zerocopy/commit/15639839eafdc9f22448b1e2d6c30ff45f80f080"
        },
        "date": 1776350888394,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4772174ed32ccbec723fecd5a4cd8ceebcd18e6d",
          "message": "[anneal] Release 0.1.0-alpha.18",
          "timestamp": "2026-04-16T14:47:33Z",
          "url": "https://github.com/google/zerocopy/pull/3282/commits/4772174ed32ccbec723fecd5a4cd8ceebcd18e6d"
        },
        "date": 1776352842973,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 704,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be",
          "message": "[anneal] Release 0.1.0-alpha.18 (#3282)\n\ngherrit-pr-id: Gkbtn5ebnp72mu2i4uwnpr35uwig5qgwq",
          "timestamp": "2026-04-16T15:36:32Z",
          "url": "https://github.com/google/zerocopy/commit/0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be"
        },
        "date": 1776354535795,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 701,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be",
          "message": "[anneal] Release 0.1.0-alpha.18 (#3282)\n\ngherrit-pr-id: Gkbtn5ebnp72mu2i4uwnpr35uwig5qgwq",
          "timestamp": "2026-04-16T15:36:32Z",
          "tree_id": "f541fb5afc67bec6cf778ed136875845b1c6d3d0",
          "url": "https://github.com/google/zerocopy/commit/0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be"
        },
        "date": 1776356010869,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 709,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e4bcb9706d73c8382594f0269046d5377efa8574",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job",
          "timestamp": "2026-04-16T16:01:32Z",
          "url": "https://github.com/google/zerocopy/pull/3283/commits/e4bcb9706d73c8382594f0269046d5377efa8574"
        },
        "date": 1776363248505,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "731729da7f955e3b81ebdfbc0ac03770fc6d2bf2",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job",
          "timestamp": "2026-04-16T16:01:32Z",
          "url": "https://github.com/google/zerocopy/pull/3283/commits/731729da7f955e3b81ebdfbc0ac03770fc6d2bf2"
        },
        "date": 1776363695925,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "1cabbac4ac001a79c8fef799ef779750b3253023",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job (#3283)\n\ngherrit-pr-id: Gcqmoot6ezcmsbvzyvus2klwwinl46j37",
          "timestamp": "2026-04-16T18:34:15Z",
          "url": "https://github.com/google/zerocopy/commit/1cabbac4ac001a79c8fef799ef779750b3253023"
        },
        "date": 1776364500773,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "748177693d1907006da102d49fd71071504b10ca",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job (#3283)\n\ngherrit-pr-id: Gcqmoot6ezcmsbvzyvus2klwwinl46j37",
          "timestamp": "2026-04-16T11:39:48-07:00",
          "tree_id": "f397797cfc16d3c01e639fdb3a59128b75858959",
          "url": "https://github.com/google/zerocopy/commit/748177693d1907006da102d49fd71071504b10ca"
        },
        "date": 1776364828055,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "867cd3a9a52ce81c4083c2a68299e33560e7a2c2",
          "message": "[ci][anneal] Add `workflow_dispatch` Action to release new version",
          "timestamp": "2026-04-16T18:39:54Z",
          "url": "https://github.com/google/zerocopy/pull/3284/commits/867cd3a9a52ce81c4083c2a68299e33560e7a2c2"
        },
        "date": 1776367496564,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 657,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b943232a98fa7c9994151a765d52b1989a982048",
          "message": "[ci][anneal] Add `workflow_dispatch` Action to release new version (#3284)\n\nRelease 0.1.0-alpha.19.\n\ngherrit-pr-id: G3sy75s2atk44kjhhoymwugs6wvpbfn4t",
          "timestamp": "2026-04-16T15:19:24-04:00",
          "tree_id": "c9f611ffd299eb3e0e9dea4702f3b30b5189fedb",
          "url": "https://github.com/google/zerocopy/commit/b943232a98fa7c9994151a765d52b1989a982048"
        },
        "date": 1776367908232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 716,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d2f7a6be7539321c975ea479324d2a4272f176af",
          "message": "[ci][anneal] Overhaul release process to support manual trigger and PR generation",
          "timestamp": "2026-04-16T19:19:30Z",
          "url": "https://github.com/google/zerocopy/pull/3285/commits/d2f7a6be7539321c975ea479324d2a4272f176af"
        },
        "date": 1776381674908,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c5b13a1ef79cc2488b8c15e414bd516632c0e351",
          "message": "[ci][anneal] Overhaul release process to support manual trigger and PR generation",
          "timestamp": "2026-04-17T02:13:33Z",
          "url": "https://github.com/google/zerocopy/pull/3285/commits/c5b13a1ef79cc2488b8c15e414bd516632c0e351"
        },
        "date": 1776415526560,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3112444f6eca22cf442f830212c03cd2388c3943",
          "message": "[ci][anneal] Add manual trigger to publish precompiled artifacts",
          "timestamp": "2026-04-18T11:58:41Z",
          "url": "https://github.com/google/zerocopy/pull/3286/commits/3112444f6eca22cf442f830212c03cd2388c3943"
        },
        "date": 1776513915732,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "650bf82c23492562c55a5ad5083e4a464fd5292d",
          "message": "[ci][anneal] Add manual trigger to publish precompiled artifacts",
          "timestamp": "2026-04-18T11:58:41Z",
          "url": "https://github.com/google/zerocopy/pull/3286/commits/650bf82c23492562c55a5ad5083e4a464fd5292d"
        },
        "date": 1776514041532,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "479bc21ac4356293462e7d3a73f65ce7fbefa3cf",
          "message": "[ci][anneal] Add manual trigger to publish precompiled artifacts (#3286)\n\nThis is part of a soft migration to the new system. It allows us to\npublish precompiled artifacts that will let us land a subsequent commit\nwhich makes use of them in `cargo-anneal`.\n\ngherrit-pr-id: Grdbltxkqkgnaqxnlrx4425qspr7nqrmw",
          "timestamp": "2026-04-18T08:16:10-04:00",
          "tree_id": "d591da17dc3a317f0821cf55f77f93344036f3b2",
          "url": "https://github.com/google/zerocopy/commit/479bc21ac4356293462e7d3a73f65ce7fbefa3cf"
        },
        "date": 1776514604771,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0cf19a0dab9a54ab95a4cc163cb76b245fc684a5",
          "message": "[ci][anneal] Make concurrency group dynamic by branch/PR",
          "timestamp": "2026-04-18T12:16:17Z",
          "url": "https://github.com/google/zerocopy/pull/3287/commits/0cf19a0dab9a54ab95a4cc163cb76b245fc684a5"
        },
        "date": 1776515117956,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 5,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d",
          "message": "[ci][anneal] Make concurrency group dynamic by branch/PR (#3287)\n\ngherrit-pr-id: Gofynwkutejony366jjuzz2odt4a56v2g",
          "timestamp": "2026-04-18T08:25:45-04:00",
          "tree_id": "7c11975b9cc8f34223d23b1c0a55a4460f99c5ae",
          "url": "https://github.com/google/zerocopy/commit/b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d"
        },
        "date": 1776515186015,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 5,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "744f9b633f1024c518ce97848941baaf82cdde99",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error",
          "timestamp": "2026-04-18T12:25:49Z",
          "url": "https://github.com/google/zerocopy/pull/3288/commits/744f9b633f1024c518ce97848941baaf82cdde99"
        },
        "date": 1776516587963,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2e69086d4e8951404a0ff12b31da02ae4950f589",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error (#3288)\n\ngherrit-pr-id: Gtfo4rh2ird3aqm57btkd3l7zpsknc7y7",
          "timestamp": "2026-04-18T08:53:08-04:00",
          "tree_id": "6a3c4dbb13fa3fb4e2edbacc36b7a98143e5342c",
          "url": "https://github.com/google/zerocopy/commit/2e69086d4e8951404a0ff12b31da02ae4950f589"
        },
        "date": 1776516817407,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "23ff5079038cc931d8c3c1e65142e3fcb7225ec4",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error",
          "timestamp": "2026-04-18T12:25:49Z",
          "url": "https://github.com/google/zerocopy/pull/3288/commits/23ff5079038cc931d8c3c1e65142e3fcb7225ec4"
        },
        "date": 1776516956643,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3638097edac2d1c9a5416788fcc427b739573e3",
          "message": "[ci][anneal] Use unique tags for manual artifact releases",
          "timestamp": "2026-04-18T12:53:13Z",
          "url": "https://github.com/google/zerocopy/pull/3289/commits/a3638097edac2d1c9a5416788fcc427b739573e3"
        },
        "date": 1776520254372,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec",
          "message": "[ci][anneal] Use unique tags for manual artifact releases (#3289)\n\ngherrit-pr-id: Gqrfvtkdyjezdwwai5d37vq5omydsrajc",
          "timestamp": "2026-04-18T09:51:02-04:00",
          "tree_id": "457b1ff2bfdd5f79fd50c5e190a8047b24ace7ee",
          "url": "https://github.com/google/zerocopy/commit/f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec"
        },
        "date": 1776520353417,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a70cac3cdaaff55316ffc9d06ac81ec304fd6bca",
          "message": "[ci][anneal] When publishing, prune Mathlib rather than removing it",
          "timestamp": "2026-04-18T13:51:08Z",
          "url": "https://github.com/google/zerocopy/pull/3290/commits/a70cac3cdaaff55316ffc9d06ac81ec304fd6bca"
        },
        "date": 1776525470914,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "00c910938978083a5405faed719ca02dcec730ad",
          "message": "[ci][anneal] When publishing, prune Mathlib rather than removing it (#3290)\n\ngherrit-pr-id: Gob4ak2l443wyguc6vd6uej7wndlqzhis",
          "timestamp": "2026-04-18T11:18:01-04:00",
          "tree_id": "f83185dc52b9877770089fc9e13f3aba0ca5dab7",
          "url": "https://github.com/google/zerocopy/commit/00c910938978083a5405faed719ca02dcec730ad"
        },
        "date": 1776525568154,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d38da7f292ab8f6f07773b1415448512c4419df2",
          "message": "[ci][anneal] Fix sysroot layout and exclude tests in builder script",
          "timestamp": "2026-04-18T15:18:08Z",
          "url": "https://github.com/google/zerocopy/pull/3291/commits/d38da7f292ab8f6f07773b1415448512c4419df2"
        },
        "date": 1776536034753,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b04142396963357c0bf3cf3d9e42e21070e38bfb",
          "message": "[ci][anneal] Fix sysroot layout and exclude tests in builder script (#3291)\n\ngherrit-pr-id: Gxhjefmzsst6q46o4l36bblw2nfrkwncy",
          "timestamp": "2026-04-18T14:15:01-04:00",
          "tree_id": "aa056420098859d5eb3a1185b40c9c371163e624",
          "url": "https://github.com/google/zerocopy/commit/b04142396963357c0bf3cf3d9e42e21070e38bfb"
        },
        "date": 1776536133230,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "56518f056f4547b74e710f0fc9bb3e5257fd3994",
          "message": "[ci][anneal] In release, don't build tests; fix location of charon artifacts",
          "timestamp": "2026-04-18T18:15:06Z",
          "url": "https://github.com/google/zerocopy/pull/3293/commits/56518f056f4547b74e710f0fc9bb3e5257fd3994"
        },
        "date": 1776536989486,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fbdeab52de993f2bad6b650acd6aa8353d9edc89",
          "message": "[ci][anneal] In release, don't build tests; fix location of charon artifacts (#3293)\n\ngherrit-pr-id: Gblquwd2ikf5wze73xm7jfvth2rkkodn4",
          "timestamp": "2026-04-18T14:29:47-04:00",
          "tree_id": "58dd5ab95050f64eb5daeb42cd0f16b5db09d1e4",
          "url": "https://github.com/google/zerocopy/commit/fbdeab52de993f2bad6b650acd6aa8353d9edc89"
        },
        "date": 1776537012841,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8f72d85e3d0ba9a84cfc02d7ad3e3c895bc5e33f",
          "message": "[ci][anneal] Remove tests before building Lean library in release",
          "timestamp": "2026-04-18T18:29:51Z",
          "url": "https://github.com/google/zerocopy/pull/3294/commits/8f72d85e3d0ba9a84cfc02d7ad3e3c895bc5e33f"
        },
        "date": 1776545349566,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "234b7e0927728428e836aa455a1960bca7cd52c3",
          "message": "[ci][anneal] Remove tests before building Lean library in release (#3294)\n\ngherrit-pr-id: Gzcu4ycvlg2exazk6idhxol3x7mrndvgg",
          "timestamp": "2026-04-18T16:48:59-04:00",
          "tree_id": "4e11b4b4883ef6eb56a4c282538d0d5c9ce4d421",
          "url": "https://github.com/google/zerocopy/commit/234b7e0927728428e836aa455a1960bca7cd52c3"
        },
        "date": 1776545448212,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ccb611083f8a1cf2850455810c2efda327b8b6a7",
          "message": "WIP: Local testing workarounds and crate migration",
          "timestamp": "2026-04-18T18:29:51Z",
          "url": "https://github.com/google/zerocopy/pull/3292/commits/ccb611083f8a1cf2850455810c2efda327b8b6a7"
        },
        "date": 1776546290527,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 853,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d96ae3425fbffb13a9bb252fadb57ecbf119fcdc",
          "message": "[ci][anneal] Unset CI variable to force precompilation in release",
          "timestamp": "2026-04-18T20:49:04Z",
          "url": "https://github.com/google/zerocopy/pull/3295/commits/d96ae3425fbffb13a9bb252fadb57ecbf119fcdc"
        },
        "date": 1776588208762,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bd315f7a62c5a9e3d8e69f2dd08d252902b514f7",
          "message": "WIP: Local testing workarounds and crate migration",
          "timestamp": "2026-04-18T20:49:04Z",
          "url": "https://github.com/google/zerocopy/pull/3292/commits/bd315f7a62c5a9e3d8e69f2dd08d252902b514f7"
        },
        "date": 1776588308226,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "62d9816418bdb3d566381c1a4070784f7cf5380e",
          "message": "[ci][anneal] Unset CI variable to force precompilation in release (#3295)\n\ngherrit-pr-id: Gqyhjsrpqtnwssq7yrc7pgbciwjphfzjb",
          "timestamp": "2026-04-19T04:43:16-04:00",
          "tree_id": "1dafb6b1066e3e9fb1d974499739b7f95db50bcf",
          "url": "https://github.com/google/zerocopy/commit/62d9816418bdb3d566381c1a4070784f7cf5380e"
        },
        "date": 1776588316877,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9c57c85e7a39f4029fbe3a17f501af1cf5ec590a",
          "message": "[ci][anneal] Add workflow_dispatch argument for zstd compression level",
          "timestamp": "2026-04-19T08:43:21Z",
          "url": "https://github.com/google/zerocopy/pull/3296/commits/9c57c85e7a39f4029fbe3a17f501af1cf5ec590a"
        },
        "date": 1776588714381,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6253233e91f7caa4e5201aa5dcb23a3a6706c4b0",
          "message": "WIP: Local testing workarounds and crate migration",
          "timestamp": "2026-04-19T08:43:21Z",
          "url": "https://github.com/google/zerocopy/pull/3292/commits/6253233e91f7caa4e5201aa5dcb23a3a6706c4b0"
        },
        "date": 1776588724904,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c97dbc6586c7c62decf3263c180e089f1c0f2771",
          "message": "[ci][anneal] Add workflow_dispatch argument for zstd compression level (#3296)\n\ngherrit-pr-id: Gqzpjc5efiwdcr4aqpzvz5nft7wfg43yo",
          "timestamp": "2026-04-19T04:52:09-04:00",
          "tree_id": "cb8d60712d6a66ca7c073d3f562146adac18c677",
          "url": "https://github.com/google/zerocopy/commit/c97dbc6586c7c62decf3263c180e089f1c0f2771"
        },
        "date": 1776588776456,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8b193d7338e5d19ee86186ab0fa2118caf819d05",
          "message": "[anneal] Adopt Lake artifact cache and share packages in workspace generation",
          "timestamp": "2026-04-19T09:07:58Z",
          "url": "https://github.com/google/zerocopy/pull/3298/commits/8b193d7338e5d19ee86186ab0fa2118caf819d05"
        },
        "date": 1776616308821,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 973,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cf2f44e9dc4c95fe64345635c378fb4feb68c122",
          "message": "WIP",
          "timestamp": "2026-04-19T09:07:58Z",
          "url": "https://github.com/google/zerocopy/pull/3299/commits/cf2f44e9dc4c95fe64345635c378fb4feb68c122"
        },
        "date": 1776637586984,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1022,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6aadac41296d8c218eb786d578657ed7ba10b14a",
          "message": "[anneal] Make logo stroke width thicker",
          "timestamp": "2026-04-20T01:38:32Z",
          "url": "https://github.com/google/zerocopy/pull/3300/commits/6aadac41296d8c218eb786d578657ed7ba10b14a"
        },
        "date": 1776673696509,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "3a99d7582663d8082df5b23ed4fd793b4e124211",
          "message": "[anneal] Make logo stroke width thicker (#3300)\n\ngherrit-pr-id: G6f3ij3lhnfnk4nvvj2ogaihrcweoqglb",
          "timestamp": "2026-04-20T08:40:34Z",
          "url": "https://github.com/google/zerocopy/commit/3a99d7582663d8082df5b23ed4fd793b4e124211"
        },
        "date": 1776674484299,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "3a99d7582663d8082df5b23ed4fd793b4e124211",
          "message": "[anneal] Make logo stroke width thicker (#3300)\n\ngherrit-pr-id: G6f3ij3lhnfnk4nvvj2ogaihrcweoqglb",
          "timestamp": "2026-04-20T08:40:34Z",
          "tree_id": "aa347751babb591182f2408e231a3bd5157aa8ac",
          "url": "https://github.com/google/zerocopy/commit/3a99d7582663d8082df5b23ed4fd793b4e124211"
        },
        "date": 1776675558736,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "46a430c37c828efce073211d3c64c0000e84f5ef",
          "message": "[CI] Bump the all-actions group with 8 updates",
          "timestamp": "2026-04-20T08:58:54Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/46a430c37c828efce073211d3c64c0000e84f5ef"
        },
        "date": 1776682991584,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a402330b52d2858335aa35b69fa0d0e680e0bc69",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep",
          "timestamp": "2026-04-20T13:24:00Z",
          "url": "https://github.com/google/zerocopy/pull/3304/commits/a402330b52d2858335aa35b69fa0d0e680e0bc69"
        },
        "date": 1776723272253,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 832,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "69e77a55f1b80f051b9dd9555363d2e074c48d3a",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep",
          "timestamp": "2026-04-20T13:24:00Z",
          "url": "https://github.com/google/zerocopy/pull/3304/commits/69e77a55f1b80f051b9dd9555363d2e074c48d3a"
        },
        "date": 1776728079205,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 768,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "d410c162d51977635ca5afac67d99a3b10327a94",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep (#3304)\n\n- Store build artifacts in a user-global Lean content-addressed artifact\n  cache, populating it during `setup`.\n- Specify the dependency on the Aeneas Lean library as follows:\n  - During `setup`, initialize the Aeneas Lean library as a git repo\n  - During `generate`/`verify`, specify the dependency as a git\n    dependency on a local filesystem path\n\nPrior to this change, we specified the dependency as a non-git\nfilesystem dep, which had the effect of causing Lean to think it could\nmutate the user-global directory, causing races when multiple `anneal`\ncommands were run in parallel.\n\nRelease 0.1.0-alpha.20\n\ngherrit-pr-id: Gyo2pqvhru3x4cyrj6bhrnjtx7gamwkfr",
          "timestamp": "2026-04-20T23:47:08Z",
          "url": "https://github.com/google/zerocopy/commit/d410c162d51977635ca5afac67d99a3b10327a94"
        },
        "date": 1776729690945,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 823,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d410c162d51977635ca5afac67d99a3b10327a94",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep (#3304)\n\n- Store build artifacts in a user-global Lean content-addressed artifact\n  cache, populating it during `setup`.\n- Specify the dependency on the Aeneas Lean library as follows:\n  - During `setup`, initialize the Aeneas Lean library as a git repo\n  - During `generate`/`verify`, specify the dependency as a git\n    dependency on a local filesystem path\n\nPrior to this change, we specified the dependency as a non-git\nfilesystem dep, which had the effect of causing Lean to think it could\nmutate the user-global directory, causing races when multiple `anneal`\ncommands were run in parallel.\n\nRelease 0.1.0-alpha.20\n\ngherrit-pr-id: Gyo2pqvhru3x4cyrj6bhrnjtx7gamwkfr",
          "timestamp": "2026-04-20T23:47:08Z",
          "tree_id": "7e016397325b6d9523d680ba36126c476aaa7aa6",
          "url": "https://github.com/google/zerocopy/commit/d410c162d51977635ca5afac67d99a3b10327a94"
        },
        "date": 1776731267889,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 804,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a71a6d5cd7992d285245277601df2ecd6dbce471",
          "message": "[anneal] WIP: Burn integration cache to the ground",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/a71a6d5cd7992d285245277601df2ecd6dbce471"
        },
        "date": 1776757599273,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 768,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "20034af4d4bf69e059be930f8b21174ff78f6aef",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/20034af4d4bf69e059be930f8b21174ff78f6aef"
        },
        "date": 1776760453750,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 713,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7f5cca48d25df90e1d400f49902c4d1a1c13b5c5",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/7f5cca48d25df90e1d400f49902c4d1a1c13b5c5"
        },
        "date": 1776764997233,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 693,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f98458e7eaf54ff34b69e417ee34e79036f06547",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/f98458e7eaf54ff34b69e417ee34e79036f06547"
        },
        "date": 1776765817619,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 700,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "11515dce44b88a626b31d1fea053754dcb7331ca",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup (#3305)\n\n- Remove obsolete worker pool and smart cache cloning from integration\n  tests\n- Configure tests to use the shared global Lean artifact cache via\n  `LAKE_CACHE_DIR`\n- Simplify `src/setup.rs` by assuming only fresh installations:\n  - Remove `verify_tools` and individual binary checksums for Aeneas\n  - Simplify toolchain directory hashing to use the Rust tag\n  - Make installation and Git initialization unconditional\n- Implement atomic installation in `setup` using a temporary directory\n  and rename\n- Remove setup-related tests which are less useful now, and will become\n  even less useful than that going forward as we simplify the setup\n  logic\n\nPrior to this change, the integration tests relied on a complex worker\npool and symlinking infrastructure to isolate tests and share build\nartifacts. This required large amounts of disk space (e.g., a specific\nrun with ~100 parallel worker threads and caches consumed ~100GB). In\nthis commit, removing the worker pool and cache cloning approach lets us\nsave significant disk space usage during integration test runs.\n\ngherrit-pr-id: G4c76oil24wlyjqav3c5s5woakn5rcxpm",
          "timestamp": "2026-04-21T10:28:40Z",
          "url": "https://github.com/google/zerocopy/commit/11515dce44b88a626b31d1fea053754dcb7331ca"
        },
        "date": 1776768050331,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 690,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "11515dce44b88a626b31d1fea053754dcb7331ca",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup (#3305)\n\n- Remove obsolete worker pool and smart cache cloning from integration\n  tests\n- Configure tests to use the shared global Lean artifact cache via\n  `LAKE_CACHE_DIR`\n- Simplify `src/setup.rs` by assuming only fresh installations:\n  - Remove `verify_tools` and individual binary checksums for Aeneas\n  - Simplify toolchain directory hashing to use the Rust tag\n  - Make installation and Git initialization unconditional\n- Implement atomic installation in `setup` using a temporary directory\n  and rename\n- Remove setup-related tests which are less useful now, and will become\n  even less useful than that going forward as we simplify the setup\n  logic\n\nPrior to this change, the integration tests relied on a complex worker\npool and symlinking infrastructure to isolate tests and share build\nartifacts. This required large amounts of disk space (e.g., a specific\nrun with ~100 parallel worker threads and caches consumed ~100GB). In\nthis commit, removing the worker pool and cache cloning approach lets us\nsave significant disk space usage during integration test runs.\n\ngherrit-pr-id: G4c76oil24wlyjqav3c5s5woakn5rcxpm",
          "timestamp": "2026-04-21T10:28:40Z",
          "tree_id": "833adf0febc61c567363031fad512ce313ed7401",
          "url": "https://github.com/google/zerocopy/commit/11515dce44b88a626b31d1fea053754dcb7331ca"
        },
        "date": 1776770215388,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 661,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c326102fba9d8cfff7f64cb55b763db3fc6388db",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/c326102fba9d8cfff7f64cb55b763db3fc6388db"
        },
        "date": 1776775359442,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1063,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "75549b547463fed9471b5510f95a2127bffe3003",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/75549b547463fed9471b5510f95a2127bffe3003"
        },
        "date": 1776791235228,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1086,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b5befce1232199b60348d2ef9c7e003dafe42e59",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/b5befce1232199b60348d2ef9c7e003dafe42e59"
        },
        "date": 1776804375975,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1069,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "37d1fef927ec84a9086312ad1bb9840c205b0d87",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/37d1fef927ec84a9086312ad1bb9840c205b0d87"
        },
        "date": 1776805952348,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1074,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9329ada1b2801e305cd00db7c62b6987f8b7c80c",
          "message": "[anneal] In `setup`, recursively cache Lean sources (#3306)\n\nInitialize all transitive Lean library dependencies of the Aeneas Lean\nlibrary as local Git repositories, and rewrite dependencies to point to\nthese as filesystem-local Git remotes. During `verify`, `lake build`\nclones any source code it doesn't already have access to. This ensures\nthat this at least clones from the local filesystem instead of from the\ninternet.\n\ngherrit-pr-id: Ghmd3zurxjuy6q66eay4blnbt7sfg7wlz",
          "timestamp": "2026-04-21T21:21:56Z",
          "url": "https://github.com/google/zerocopy/commit/9329ada1b2801e305cd00db7c62b6987f8b7c80c"
        },
        "date": 1776807726965,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1171,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9329ada1b2801e305cd00db7c62b6987f8b7c80c",
          "message": "[anneal] In `setup`, recursively cache Lean sources (#3306)\n\nInitialize all transitive Lean library dependencies of the Aeneas Lean\nlibrary as local Git repositories, and rewrite dependencies to point to\nthese as filesystem-local Git remotes. During `verify`, `lake build`\nclones any source code it doesn't already have access to. This ensures\nthat this at least clones from the local filesystem instead of from the\ninternet.\n\ngherrit-pr-id: Ghmd3zurxjuy6q66eay4blnbt7sfg7wlz",
          "timestamp": "2026-04-21T21:21:56Z",
          "tree_id": "35fb101371c1e4ebb6fb1c0798abadb812c383ed",
          "url": "https://github.com/google/zerocopy/commit/9329ada1b2801e305cd00db7c62b6987f8b7c80c"
        },
        "date": 1776809517999,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1096,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5a5f7b593978cc5326e8ea785d15ff3803551806",
          "message": "Translate remaining annotations in logic_and_control.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3309/commits/5a5f7b593978cc5326e8ea785d15ff3803551806"
        },
        "date": 1776846205007,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "aaaa71e4bbc874d39acb7556fe2ef46eff287946",
          "message": "Save more work",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3308/commits/aaaa71e4bbc874d39acb7556fe2ef46eff287946"
        },
        "date": 1776846208012,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b1fdafb152f643383365c75682d3ca2a26628fce",
          "message": "Save work: Translated integration tests to new syntax",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3307/commits/b1fdafb152f643383365c75682d3ca2a26628fce"
        },
        "date": 1776846209442,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6515957a25a4a2e1130213684a65a5876cc5ea4f",
          "message": "Add stderr_file to success_allow_sorry_is_valid anneal.toml",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3310/commits/6515957a25a4a2e1130213684a65a5876cc5ea4f"
        },
        "date": 1776846299166,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6acd8b409f306433335df1044f39e37fd7c70087",
          "message": "Revert empty spec blocks in success_allow_sorry_is_valid",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3312/commits/6acd8b409f306433335df1044f39e37fd7c70087"
        },
        "date": 1776846303073,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "affd27ff3190f76c374f8985c589f9ca8a9c6391",
          "message": "Add dummy theorems to spec_syntax.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3315/commits/affd27ff3190f76c374f8985c589f9ca8a9c6391"
        },
        "date": 1776846304756,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e8b19d15dc991389600b50246a0e8323272a10a2",
          "message": "Remove isValid from S in logic_and_control.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3313/commits/e8b19d15dc991389600b50246a0e8323272a10a2"
        },
        "date": 1776846303593,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1da7ff4244f19e6c5816bad3d2fae6b875cc9378",
          "message": "Remove all isValid annotations in logic_and_control.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3311/commits/1da7ff4244f19e6c5816bad3d2fae6b875cc9378"
        },
        "date": 1776846303662,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6213ce106972645c8919a402c00678eea844e38e",
          "message": "Use sorry for invert in types_and_data.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3314/commits/6213ce106972645c8919a402c00678eea844e38e"
        },
        "date": 1776846306578,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "204014111e0f5679f226b19a328370f91aeff0bf",
          "message": "Loosen sorry detection in aeneas.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3317/commits/204014111e0f5679f226b19a328370f91aeff0bf"
        },
        "date": 1776846313249,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dcfc92ba7e6c0249b27b2bb20e8073ce39767750",
          "message": "Translate memory_and_borrows.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3316/commits/dcfc92ba7e6c0249b27b2bb20e8073ce39767750"
        },
        "date": 1776846315496,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e0a1dc6c006368f856ab5ea0069772bba390263e",
          "message": "Add dummy theorem to lib.rs",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3319/commits/e0a1dc6c006368f856ab5ea0069772bba390263e"
        },
        "date": 1776846317898,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "809337c3f4ad5d7b48d4853bd13ef8aa7bba1948",
          "message": "Add dummy theorems to all remaining empty spec blocks",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3318/commits/809337c3f4ad5d7b48d4853bd13ef8aa7bba1948"
        },
        "date": 1776846319083,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7b6e86ba98576dad6eee26e3827513e4ca5846ec",
          "message": "[anneal] Translate and verify integration tests for new syntax",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3320/commits/7b6e86ba98576dad6eee26e3827513e4ca5846ec"
        },
        "date": 1776846331050,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b7cea6d7aad7e78365ff98d643adf4f43ec760c5",
          "message": "[anneal] Translate and verify integration tests for new syntax",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3321/commits/b7cea6d7aad7e78365ff98d643adf4f43ec760c5"
        },
        "date": 1776848417620,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 23,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3ec6470264b9b1acb525ff4ed1834b2ed03500b4",
          "message": "Make Docker image tag and cache volume unique per worktree",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3322/commits/3ec6470264b9b1acb525ff4ed1834b2ed03500b4"
        },
        "date": 1776854973479,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fa91316f61deeda4fe2d77de7db494fc1f3103b5",
          "message": "Make Docker image tag and cache volume unique per worktree",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3322/commits/fa91316f61deeda4fe2d77de7db494fc1f3103b5"
        },
        "date": 1776855500494,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0497a2dd3a4bbf07b2f4540f788255404b151784",
          "message": "Add Total CI Duration benchmark to anneal workflow",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3323/commits/0497a2dd3a4bbf07b2f4540f788255404b151784"
        },
        "date": 1776855737107,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a27cb57734782db8f7ba9da14e3aa8fd6ea200f9",
          "message": "[ci][anneal] Track total CI duration in benchmark dashboard (#3323)",
          "timestamp": "2026-04-22T11:11:58Z",
          "url": "https://github.com/google/zerocopy/commit/a27cb57734782db8f7ba9da14e3aa8fd6ea200f9"
        },
        "date": 1776856362618,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2a269c55f4ee2fc3ee14ab1323cd3a63fe4817cf",
          "message": "Make Docker image tag and cache volume unique per worktree",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3322/commits/2a269c55f4ee2fc3ee14ab1323cd3a63fe4817cf"
        },
        "date": 1776856944766,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a27cb57734782db8f7ba9da14e3aa8fd6ea200f9",
          "message": "[ci][anneal] Track total CI duration in benchmark dashboard (#3323)",
          "timestamp": "2026-04-22T11:11:58Z",
          "tree_id": "22f1c20b8a2fe8fc6e2010a70b7e0c0b573332b6",
          "url": "https://github.com/google/zerocopy/commit/a27cb57734782db8f7ba9da14e3aa8fd6ea200f9"
        },
        "date": 1776857109240,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e1005b0f51361317d1f4883a6d3138c567301b22",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-04-22T11:24:42Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/e1005b0f51361317d1f4883a6d3138c567301b22"
        },
        "date": 1776857288674,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a51752bdff4d521681a8c2d5d97396015114d6d8",
          "message": "[anneal] Isolate docker images, not just volumes (#3322)",
          "timestamp": "2026-04-22T11:31:34Z",
          "url": "https://github.com/google/zerocopy/commit/a51752bdff4d521681a8c2d5d97396015114d6d8"
        },
        "date": 1776857542390,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a51752bdff4d521681a8c2d5d97396015114d6d8",
          "message": "[anneal] Isolate docker images, not just volumes (#3322)",
          "timestamp": "2026-04-22T11:31:34Z",
          "tree_id": "733e7fc815782bd3e1b3ba6ad4af32aa90a0566f",
          "url": "https://github.com/google/zerocopy/commit/a51752bdff4d521681a8c2d5d97396015114d6d8"
        },
        "date": 1776858397029,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "060fa19351a96e39a97ab4c17d017855834d3a98",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-04-27T05:44:52Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/060fa19351a96e39a97ab4c17d017855834d3a98"
        },
        "date": 1777288488802,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f55a6dde7143cf5519c1e0ea628d358222364cf3",
          "message": "[anneal][README] Document TCB shrinking",
          "timestamp": "2026-04-27T05:44:52Z",
          "url": "https://github.com/google/zerocopy/pull/3326/commits/f55a6dde7143cf5519c1e0ea628d358222364cf3"
        },
        "date": 1777386093100,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4d84f92ef43313e54eac77228cedd08889058ef8",
          "message": "[anneal][README] Document TCB shrinking",
          "timestamp": "2026-04-27T05:44:52Z",
          "url": "https://github.com/google/zerocopy/pull/3326/commits/4d84f92ef43313e54eac77228cedd08889058ef8"
        },
        "date": 1777386248931,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 31,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "f896a6890a1e6feb01d3c26364bf674f0573321e",
          "message": "[anneal][README] Document TCB shrinking (#3326)\n\ngherrit-pr-id: Gy4y7cstkui5s6c7jletzjbu37xtjglxm",
          "timestamp": "2026-04-28T18:10:09Z",
          "url": "https://github.com/google/zerocopy/commit/f896a6890a1e6feb01d3c26364bf674f0573321e"
        },
        "date": 1777399859380,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f896a6890a1e6feb01d3c26364bf674f0573321e",
          "message": "[anneal][README] Document TCB shrinking (#3326)\n\ngherrit-pr-id: Gy4y7cstkui5s6c7jletzjbu37xtjglxm",
          "timestamp": "2026-04-28T18:10:09Z",
          "tree_id": "04fd33df84b5b512246673abd226b3bf491693a7",
          "url": "https://github.com/google/zerocopy/commit/f896a6890a1e6feb01d3c26364bf674f0573321e"
        },
        "date": 1777401474494,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3574989f7d011165c447a005e12901f0690a6a04",
          "message": "[anneal][README] Tighten wording",
          "timestamp": "2026-04-28T18:37:26Z",
          "url": "https://github.com/google/zerocopy/pull/3328/commits/3574989f7d011165c447a005e12901f0690a6a04"
        },
        "date": 1777416543853,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a0600ed391d85fa2cd1b0d62b233277712ef7731",
          "message": "[anneal][README] Tighten wording",
          "timestamp": "2026-04-28T18:37:26Z",
          "url": "https://github.com/google/zerocopy/pull/3328/commits/a0600ed391d85fa2cd1b0d62b233277712ef7731"
        },
        "date": 1777417697880,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1040,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "bc525228994b0eafbc600981e1955f2f442c5e0b",
          "message": "[anneal][README] Tighten wording (#3328)\n\nRelease 0.1.0-alpha.21.\n\ngherrit-pr-id: Ggwzrriapr76e6dx74cv4skvdp7ikd37h",
          "timestamp": "2026-04-28T23:20:52Z",
          "url": "https://github.com/google/zerocopy/commit/bc525228994b0eafbc600981e1955f2f442c5e0b"
        },
        "date": 1777419570763,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1076,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc525228994b0eafbc600981e1955f2f442c5e0b",
          "message": "[anneal][README] Tighten wording (#3328)\n\nRelease 0.1.0-alpha.21.\n\ngherrit-pr-id: Ggwzrriapr76e6dx74cv4skvdp7ikd37h",
          "timestamp": "2026-04-28T23:20:52Z",
          "tree_id": "ed7bfb5b08e51dfc389d3beadf64648ab5bea3b3",
          "url": "https://github.com/google/zerocopy/commit/bc525228994b0eafbc600981e1955f2f442c5e0b"
        },
        "date": 1777421326597,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1154,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0fc280083ba437f6717e994c27169f36ff64b669",
          "message": "[ci] Run Anneal jobs on free-tier runners",
          "timestamp": "2026-04-29T03:07:30Z",
          "url": "https://github.com/google/zerocopy/pull/3330/commits/0fc280083ba437f6717e994c27169f36ff64b669"
        },
        "date": 1777652916529,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "c67c8ecc912d7f45e68b5274de789a15b42cf4aa",
          "message": "[ci] Run Anneal jobs on free-tier runners (#3330)\n\ngherrit-pr-id: Gl375z4s3fozt4u74gde7bzsp3ey4fi3n",
          "timestamp": "2026-05-01T17:07:29Z",
          "url": "https://github.com/google/zerocopy/commit/c67c8ecc912d7f45e68b5274de789a15b42cf4aa"
        },
        "date": 1777655298202,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c67c8ecc912d7f45e68b5274de789a15b42cf4aa",
          "message": "[ci] Run Anneal jobs on free-tier runners (#3330)\n\ngherrit-pr-id: Gl375z4s3fozt4u74gde7bzsp3ey4fi3n",
          "timestamp": "2026-05-01T17:07:29Z",
          "tree_id": "a24079fd4d2bb340570f054bd0bf6c414eba80f0",
          "url": "https://github.com/google/zerocopy/commit/c67c8ecc912d7f45e68b5274de789a15b42cf4aa"
        },
        "date": 1777657745285,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7fcad56fadd04c5ebfbde1f837003851fbea63c4",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-05-01T17:48:36Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/7fcad56fadd04c5ebfbde1f837003851fbea63c4"
        },
        "date": 1777657904360,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "44c9b1430f14d621ee57516893e59b216911ebaf",
          "message": "[anneal] Replace Docker with Nix",
          "timestamp": "2026-05-04T18:39:21Z",
          "url": "https://github.com/google/zerocopy/pull/3336/commits/44c9b1430f14d621ee57516893e59b216911ebaf"
        },
        "date": 1777939708374,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2224c4c6d258baa161adb7d76eb6aab0de25e68b",
          "message": "[anneal] Replace annotation syntax with verbatim Lean",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3321/commits/2224c4c6d258baa161adb7d76eb6aab0de25e68b"
        },
        "date": 1778005475575,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "54bd85c25824a1dba5cc245d9358ffbf2b63e91f",
          "message": "[anneal] Replace annotation syntax with verbatim Lean",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3321/commits/54bd85c25824a1dba5cc245d9358ffbf2b63e91f"
        },
        "date": 1778015417580,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1992,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dc12610c8cefb5fdc890e91dbc22ce186a864465",
          "message": "[anneal] Replace annotation syntax with verbatim Lean",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3321/commits/dc12610c8cefb5fdc890e91dbc22ce186a864465"
        },
        "date": 1778019958274,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d38657fc5f3b41967cd5478f4ba125ea5a1ddad0",
          "message": "Implement optimized symlink-copy package materializer and static commit hash bypass to achieve 40x speedup and 100% concurrent safety",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3340/commits/d38657fc5f3b41967cd5478f4ba125ea5a1ddad0"
        },
        "date": 1778032510404,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 953,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8ec4371ce2524cb3f86c1ca1c1b6c5ae39a5abb3",
          "message": "Polish code comments across setup.rs and aeneas.rs to strictly conform to comment-guidelines (80-column wrapping, objective tone, self-contained descriptions)",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3342/commits/8ec4371ce2524cb3f86c1ca1c1b6c5ae39a5abb3"
        },
        "date": 1778035209025,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1065,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6ee85014a75f4ecbde8091c0fff0cbb7c668c931",
          "message": "Optimize run_lake by copying precompiled config folders, renaming Aeneas config, and dynamically patching trace indices to achieve a ~19% run_lake speedup",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3341/commits/6ee85014a75f4ecbde8091c0fff0cbb7c668c931"
        },
        "date": 1778035223747,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1075,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "344fa4d987e5c17cd669377699404d38ebadbc4b",
          "message": "[anneal] WIP",
          "timestamp": "2026-05-06T05:47:52Z",
          "url": "https://github.com/google/zerocopy/pull/3344/commits/344fa4d987e5c17cd669377699404d38ebadbc4b"
        },
        "date": 1778091004357,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1071,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0f5260ebe9491eae50e4489d6decd6a025a34fdd",
          "message": "[anneal] WIP",
          "timestamp": "2026-05-06T05:47:52Z",
          "url": "https://github.com/google/zerocopy/pull/3344/commits/0f5260ebe9491eae50e4489d6decd6a025a34fdd"
        },
        "date": 1778094450423,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1112,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2f1d4dfe3fb6309820f61fc2f57cae83e152d2dc",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal`",
          "timestamp": "2026-05-06T05:47:52Z",
          "url": "https://github.com/google/zerocopy/pull/3344/commits/2f1d4dfe3fb6309820f61fc2f57cae83e152d2dc"
        },
        "date": 1778095997188,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1062,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "be6f199fdbe4e568ac63289e2bdbd4a5f783d444",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal` (#3344)\n\nPrior to this change, Lake verification relied on recursively copying\nthe entire global precompiled toolchain package directory (~5,000\n`.olean` files, ~5GB) into a build directory. This was obviously slow\nand caused massive disk bloat.\n\nIn this commit, we instead:\n- Copy only those files which Lake will attempt to write, and symlink\n  all other files. In practice, this means that only the smallest files\n  are actually copied. (Note: Copying is necessary *at all* because Lake\n  will write to some files in the directories of a package's\n  *dependencies* if those dependencies are filesystem-local. Without\n  copying, this would result in concurrent writes to the user-global\n  `~/.anneal/toolchain` directory.)\n- Mark the `~/.anneal/toolchain/<toolchain>` directory as recursively\n  read-only to ensure that any attempted writes fail loudly.\n\nRelease 0.1.0-alpha.22.\n\ngherrit-pr-id: Gks63dnqyjzxt6s6sgowdaz63rogw5kz3",
          "timestamp": "2026-05-06T19:44:41Z",
          "url": "https://github.com/google/zerocopy/commit/be6f199fdbe4e568ac63289e2bdbd4a5f783d444"
        },
        "date": 1778097785714,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1057,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "be6f199fdbe4e568ac63289e2bdbd4a5f783d444",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal` (#3344)\n\nPrior to this change, Lake verification relied on recursively copying\nthe entire global precompiled toolchain package directory (~5,000\n`.olean` files, ~5GB) into a build directory. This was obviously slow\nand caused massive disk bloat.\n\nIn this commit, we instead:\n- Copy only those files which Lake will attempt to write, and symlink\n  all other files. In practice, this means that only the smallest files\n  are actually copied. (Note: Copying is necessary *at all* because Lake\n  will write to some files in the directories of a package's\n  *dependencies* if those dependencies are filesystem-local. Without\n  copying, this would result in concurrent writes to the user-global\n  `~/.anneal/toolchain` directory.)\n- Mark the `~/.anneal/toolchain/<toolchain>` directory as recursively\n  read-only to ensure that any attempted writes fail loudly.\n\nRelease 0.1.0-alpha.22.\n\ngherrit-pr-id: Gks63dnqyjzxt6s6sgowdaz63rogw5kz3",
          "timestamp": "2026-05-06T19:44:41Z",
          "tree_id": "73f8ba779cf997b8e10d15cfb9573283a6ee505b",
          "url": "https://github.com/google/zerocopy/commit/be6f199fdbe4e568ac63289e2bdbd4a5f783d444"
        },
        "date": 1778099690734,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1085,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d43dde17f9bd6d1273569ce58f30a64809a21ad7",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-09T12:52:12Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/d43dde17f9bd6d1273569ce58f30a64809a21ad7"
        },
        "date": 1778482857382,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 20,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ef1a886451b2871c2fe6ffd0eeb10a4108d4d580",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-09T12:52:12Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/ef1a886451b2871c2fe6ffd0eeb10a4108d4d580"
        },
        "date": 1778487513683,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5eaabf9abe92019696a261f302fa84c6272e6a6d",
          "message": "[CI] Bump the all-actions group across 1 directory with 10 updates",
          "timestamp": "2026-05-11T13:28:45Z",
          "url": "https://github.com/google/zerocopy/pull/3349/commits/5eaabf9abe92019696a261f302fa84c6272e6a6d"
        },
        "date": 1778508712800,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 57,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "92fa010ec3ef75ca0093b765b92172e2663bfedd",
          "message": "[anneal] README: Explain philosophy wrt typing",
          "timestamp": "2026-05-11T13:28:45Z",
          "url": "https://github.com/google/zerocopy/pull/3351/commits/92fa010ec3ef75ca0093b765b92172e2663bfedd"
        },
        "date": 1778546364837,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1018,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "31c878bf0e4301fba3b74d88d2927ea7a82ef539",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/31c878bf0e4301fba3b74d88d2927ea7a82ef539"
        },
        "date": 1778598521923,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 32,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c51884e94262f3f9d5dead155f0ef806d424c989",
          "message": "Add to anneal-setup-v2: non-UNIX support; doc-comments; tests",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3353/commits/c51884e94262f3f9d5dead155f0ef806d424c989"
        },
        "date": 1778612032980,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7127a9536f05a3f486ef39f21f3dcfaf5fdd2d14",
          "message": "WIP: Start building thin setup that presumes carefully prepared dependencies archive",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3352/commits/7127a9536f05a3f486ef39f21f3dcfaf5fdd2d14"
        },
        "date": 1778612037533,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 14,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5592b2be1f587b882462913c632dfa9ee6c01ab9",
          "message": "anneal-setup-v2: simplify extractor into single-threaded implementation",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3357/commits/5592b2be1f587b882462913c632dfa9ee6c01ab9"
        },
        "date": 1778613022288,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1006,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "03f497ea94807c49fc43043f0d46a05922789746",
          "message": "Modify anneal/Cargo to admit v2/setup workspace",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3354/commits/03f497ea94807c49fc43043f0d46a05922789746"
        },
        "date": 1778613046935,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1030,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "421342304f51114aaddd133c638ba199957a3dcc",
          "message": "anneal-setup-v2: switch from shelling out to tar to managing archives with libraries",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3356/commits/421342304f51114aaddd133c638ba199957a3dcc"
        },
        "date": 1778613094479,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1066,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5b0642ee112a48b0554a58e5a820b24bbdf70a9d",
          "message": "anneal-setup-v2: update vendored rust dependencies",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3355/commits/5b0642ee112a48b0554a58e5a820b24bbdf70a9d"
        },
        "date": 1778613122114,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1094,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8811a40e19c2ab108c4c7b74134b4b5db108b30",
          "message": "anneal-setup-v2: Copy nix flake from #3336",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3358/commits/b8811a40e19c2ab108c4c7b74134b4b5db108b30"
        },
        "date": 1778613125977,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1100,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c862a246e91d85f4bca9202b02994ac576825c76",
          "message": "anneal-setup-v2: Update nix flake to package Lean toolchain",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3359/commits/c862a246e91d85f4bca9202b02994ac576825c76"
        },
        "date": 1778613138401,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1113,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "72b79672a65fb514a33a8ba68591dee09dcab4e3",
          "message": "anneal-setup-v2: More robust bash scripts in nix flake",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3360/commits/72b79672a65fb514a33a8ba68591dee09dcab4e3"
        },
        "date": 1778624645566,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1142,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d64055e99e1826f7e0411789cadc6e2298c974d2",
          "message": "[anneal][v2] Introduce nix-based toolchain management",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3361/commits/d64055e99e1826f7e0411789cadc6e2298c974d2"
        },
        "date": 1778675663860,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8c6bd235d543b36ce71b9c65314dc7486ce0b890",
          "message": "[anneal][v2] Initial `setup` implementation",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3362/commits/8c6bd235d543b36ce71b9c65314dc7486ce0b890"
        },
        "date": 1778676717714,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1081,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8d67b0302edbe4dd818d3603d0430ca33b2f648e",
          "message": "[WIP] Experiment rewriting setup in toolchain-config directory",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3363/commits/8d67b0302edbe4dd818d3603d0430ca33b2f648e"
        },
        "date": 1778702957330,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1007,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f590be17467609aa773c9163b0f27c0f046a1600",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/f590be17467609aa773c9163b0f27c0f046a1600"
        },
        "date": 1778708700481,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "422235dad9be97a1f2cb5106da6fb44f5f303a49",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests (#3365)\n\nThis puts the use of the unstable feature `layout_for_ptr` behind\n`all(test, miri)`, since it is only necessary for zerocopy tests, not\nfor downstream users.\n\nRelease 0.8.49.\n\ngherrit-pr-id: Gouy5nmgied3joawzp6mdecm3nuhi35jh\n\nCo-authored-by: Erick Tryzelaar <etryzelaar@google.com>",
          "timestamp": "2026-05-14T07:41:16Z",
          "url": "https://github.com/google/zerocopy/commit/422235dad9be97a1f2cb5106da6fb44f5f303a49"
        },
        "date": 1778744522902,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "05d57bc60c4fd3ce1734574632a1bc97a459322d",
          "message": "Start cleaning up vibe-coded 'Rename v2..Introduce standalone' changes",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3371/commits/05d57bc60c4fd3ce1734574632a1bc97a459322d"
        },
        "date": 1778786591832,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1017,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "82b260af1624870a6cc8087c00506015fd94d4d8",
          "message": "Move from type params to &dyn T; start trying to work with toml_const",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3373/commits/82b260af1624870a6cc8087c00506015fd94d4d8"
        },
        "date": 1778786605766,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1029,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "12c798fa9a58e94436b17c5fcbfd65a91b30bcfd",
          "message": "Abstract ArchiveFormat and HashReader over generic Extractor and Digest boundaries",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3369/commits/12c798fa9a58e94436b17c5fcbfd65a91b30bcfd"
        },
        "date": 1778786620645,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1044,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "05dd9ae24f6824827c817414ce7fdc9e19fdff99",
          "message": "Introduce standalone static-toml integration example and robust parent directory creation interfaces",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3370/commits/05dd9ae24f6824827c817414ce7fdc9e19fdff99"
        },
        "date": 1778786669203,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1094,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0106dd73bfa19b2c73aa436e8bab3240f237aaf3",
          "message": "Refactor Config layout and rework platform binding parameters",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3368/commits/0106dd73bfa19b2c73aa436e8bab3240f237aaf3"
        },
        "date": 1778786683631,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1111,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f89f0b43d3004c662f702b1f82fabf2306c13a9f",
          "message": "Introduce toml_const dependency; r/Setup/Install; bind url<->archive-format and checksum<->digest-algorithm",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3372/commits/f89f0b43d3004c662f702b1f82fabf2306c13a9f"
        },
        "date": 1778786702500,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1110,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "030de3fb0032ba041bc84e1f9ffb017033a3a848",
          "message": "Rename v2 setup crate to toolchain-config",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3367/commits/030de3fb0032ba041bc84e1f9ffb017033a3a848"
        },
        "date": 1778786753817,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1180,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1cb115367ed399840c08dfd4a75fa6b9016d15bf",
          "message": "[anneal][v2] (Buggy) atomic toolchain management",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3375/commits/1cb115367ed399840c08dfd4a75fa6b9016d15bf"
        },
        "date": 1778803612920,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b9bf484e83a8c2000c5eafd07d6561464caccbeb",
          "message": "[anneal][v2] Atomic toolchain management via directory locking",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/b9bf484e83a8c2000c5eafd07d6561464caccbeb"
        },
        "date": 1778806016974,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "36d8147c815e919835b7f4be5cfa349e694c2703",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/36d8147c815e919835b7f4be5cfa349e694c2703"
        },
        "date": 1778811928160,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb6caf382d0a49db0263724b90cee88b64ad7b11",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/cb6caf382d0a49db0263724b90cee88b64ad7b11"
        },
        "date": 1778849930408,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1652fd0c9717b844f6a30e6b494cbb72aa5bc21f",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1652fd0c9717b844f6a30e6b494cbb72aa5bc21f"
        },
        "date": 1778850650351,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "af503ff97de621d3585b230395f548aedba66a6c",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/af503ff97de621d3585b230395f548aedba66a6c"
        },
        "date": 1778850777190,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1f95236b0081b736384eba75baac4fb51cc1000d",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1f95236b0081b736384eba75baac4fb51cc1000d"
        },
        "date": 1778860897524,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 51,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "639939fbd0688f0a9898788a54ebb6be3e24ab62",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/639939fbd0688f0a9898788a54ebb6be3e24ab62"
        },
        "date": 1778865978931,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dc34ec95153a8d2239917137613800ca04474696",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/dc34ec95153a8d2239917137613800ca04474696"
        },
        "date": 1778870681136,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1cb13961f8c8bb14c77d427b694851ebdc9d4b65",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1cb13961f8c8bb14c77d427b694851ebdc9d4b65"
        },
        "date": 1778870948520,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e26ffc16650d8948eae9e0616f800b0dc5661fd9",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3377/commits/e26ffc16650d8948eae9e0616f800b0dc5661fd9"
        },
        "date": 1778871177711,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "24f27be1965c03c6fc493c2179a6bd3d29ba6ec0",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/24f27be1965c03c6fc493c2179a6bd3d29ba6ec0"
        },
        "date": 1778883667573,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "adeb3742c91b34404ae47b4ddc64c42b685e8163",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/adeb3742c91b34404ae47b4ddc64c42b685e8163"
        },
        "date": 1778883871255,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5624a71c3e182b4e1a9552bf5cff77b803af8034",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/5624a71c3e182b4e1a9552bf5cff77b803af8034"
        },
        "date": 1778884263796,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "01bba6bc21a667df3fbbbaabca114b7158a8c546",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/01bba6bc21a667df3fbbbaabca114b7158a8c546"
        },
        "date": 1778884404003,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b2045d774da6dda9e85e195dfefd75d5c313a07d",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/b2045d774da6dda9e85e195dfefd75d5c313a07d"
        },
        "date": 1778885602417,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "19f13f31f97fddf47aada2426645b707d2a052e2",
          "message": "[anneal][v2][exocrate] Pass manifest/lockfile paths explicitly",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3378/commits/19f13f31f97fddf47aada2426645b707d2a052e2"
        },
        "date": 1778886032325,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 41,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "21a18fd83dde223c6cb0343d7cc8de2a3d346eb6",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/21a18fd83dde223c6cb0343d7cc8de2a3d346eb6"
        },
        "date": 1778886605857,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "156018c368c62dc4625038dedcbd5fdc7c02a94b",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/156018c368c62dc4625038dedcbd5fdc7c02a94b"
        },
        "date": 1778886656329,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8afd4850b94fe690b7bdb3f3e2c717e19fb99ab",
          "message": "[anneal] README: Explain philosophy w.r.t. typing",
          "timestamp": "2026-05-18T16:47:14Z",
          "url": "https://github.com/google/zerocopy/pull/3351/commits/b8afd4850b94fe690b7bdb3f3e2c717e19fb99ab"
        },
        "date": 1779133125217,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a3ad195abf85896be6f07f11acb486ceb7d61900",
          "message": "[anneal] README: Explain philosophy w.r.t. typing (#3351)\n\nRelease 0.1.0-alpha.23.\n\ngherrit-pr-id: Gpeqma2krsi7flwaeyjlum23s7znxuhms",
          "timestamp": "2026-05-18T16:03:33-04:00",
          "tree_id": "42557b2a78eba0ec7aaa24b045a0f4e098ac18eb",
          "url": "https://github.com/google/zerocopy/commit/a3ad195abf85896be6f07f11acb486ceb7d61900"
        },
        "date": 1779135709020,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1069,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e58c6dc36be5cbabc15a88bdc61a1a18658c5f95",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-18T20:59:32Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/e58c6dc36be5cbabc15a88bdc61a1a18658c5f95"
        },
        "date": 1779145630249,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8db11399c64069d2ab12130e3a8c540da81592a",
          "message": "[ci] Don't run on large runners",
          "timestamp": "2026-05-19T08:50:26Z",
          "url": "https://github.com/google/zerocopy/pull/3379/commits/b8db11399c64069d2ab12130e3a8c540da81592a"
        },
        "date": 1779185478885,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 30,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "d0764df9d9b668b8178340168da36f209c732821",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T10:29:24Z",
          "url": "https://github.com/google/zerocopy/commit/d0764df9d9b668b8178340168da36f209c732821"
        },
        "date": 1779186642227,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 31,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "db28e0ef51864bb5f817eb3e5929b5b01c3c8efa",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T12:05:21Z",
          "url": "https://github.com/google/zerocopy/commit/db28e0ef51864bb5f817eb3e5929b5b01c3c8efa"
        },
        "date": 1779192420860,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 36,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "837d76d830653021e6a6a5fc3cade5e911b831ad",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/837d76d830653021e6a6a5fc3cade5e911b831ad"
        },
        "date": 1779210087343,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e4463478772bf064fe0d401f60d41c31bf269d63",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/e4463478772bf064fe0d401f60d41c31bf269d63"
        },
        "date": 1779211161490,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1080,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d564da0e05ea1f07f7a34474f1d30fe7d8a25dfc",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/d564da0e05ea1f07f7a34474f1d30fe7d8a25dfc"
        },
        "date": 1779211178552,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1103,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a64d7d94a32626c3fb26300effba717a8b74267f",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/a64d7d94a32626c3fb26300effba717a8b74267f"
        },
        "date": 1779212321263,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "445857068ada89c3e3a0e5fc64deca4a627e6647",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/445857068ada89c3e3a0e5fc64deca4a627e6647"
        },
        "date": 1779212321796,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "41bb90ed3ad4664afd5d98a04047782b9e720f44",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T17:39:49Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/41bb90ed3ad4664afd5d98a04047782b9e720f44"
        },
        "date": 1779212642119,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4cf5c9545b171bba0b912b84a58a734ca12606e3",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T17:39:49Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/4cf5c9545b171bba0b912b84a58a734ca12606e3"
        },
        "date": 1779212648990,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ba490b4d08980b4c7bf53888cb81cccc8dafce49",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:07:43Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/ba490b4d08980b4c7bf53888cb81cccc8dafce49"
        },
        "date": 1779223070313,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1138,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "40494d65dbddce23cfa56b509d95a947d2293845",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3384/commits/40494d65dbddce23cfa56b509d95a947d2293845"
        },
        "date": 1779226186386,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "40494d65dbddce23cfa56b509d95a947d2293845",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/40494d65dbddce23cfa56b509d95a947d2293845"
        },
        "date": 1779226252571,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34394dc744493d2b7cdda5bef1699f7fc8b7630b",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/34394dc744493d2b7cdda5bef1699f7fc8b7630b"
        },
        "date": 1779234283424,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ca9434eef2e08e0ab8638e5eb2e548ba4fad4df2",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/ca9434eef2e08e0ab8638e5eb2e548ba4fad4df2"
        },
        "date": 1779234284792,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f849827512305da338f044b1e195a2ef2fc3378a",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/f849827512305da338f044b1e195a2ef2fc3378a"
        },
        "date": 1779234290546,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34e3c2d72feeba99b4c2e640971fb641184ea3f0",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/34e3c2d72feeba99b4c2e640971fb641184ea3f0"
        },
        "date": 1779234290507,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "8772fc4b3c36778c5cdb4adc7eaa8825541b2418",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T23:46:42Z",
          "url": "https://github.com/google/zerocopy/commit/8772fc4b3c36778c5cdb4adc7eaa8825541b2418"
        },
        "date": 1779234454954,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d22541fa193b6594621ff12d4ea3fe8f124c2290",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/d22541fa193b6594621ff12d4ea3fe8f124c2290"
        },
        "date": 1779235250886,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 16,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dbfad857fc9fdb7ce2a5900e60e4d46ca1b434a7",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/dbfad857fc9fdb7ce2a5900e60e4d46ca1b434a7"
        },
        "date": 1779235259401,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 18,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "71b1c404f0c8566268b3aa95c389448b180a87ce",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/71b1c404f0c8566268b3aa95c389448b180a87ce"
        },
        "date": 1779235289922,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 54,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b45304bdbf11f5c2bebf555ce00743e8e4ef1a2c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/b45304bdbf11f5c2bebf555ce00743e8e4ef1a2c"
        },
        "date": 1779235444669,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "8772fc4b3c36778c5cdb4adc7eaa8825541b2418",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T23:46:42Z",
          "tree_id": "fe5018c83ed57d2fd917f95cfbc9e62e4d068c89",
          "url": "https://github.com/google/zerocopy/commit/8772fc4b3c36778c5cdb4adc7eaa8825541b2418"
        },
        "date": 1779236265364,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb85c7399f2f163e1cb574a5e40ee552c2588507",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/cb85c7399f2f163e1cb574a5e40ee552c2588507"
        },
        "date": 1779236278058,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d060c9263e3bf09b141fb4b67873045540c333d4",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/d060c9263e3bf09b141fb4b67873045540c333d4"
        },
        "date": 1779236457686,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cf1754b9dd5ef754c073bfc2edea7f375e349610",
          "message": "[CI] Bump the all-actions group across 1 directory with 11 updates",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3385/commits/cf1754b9dd5ef754c073bfc2edea7f375e349610"
        },
        "date": 1779236493278,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "929a91bc0aa2fcf577dbe31b414c5c44e2248b8c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/929a91bc0aa2fcf577dbe31b414c5c44e2248b8c"
        },
        "date": 1779238276135,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f2d675b038e8aef08e084d884bf575e23dafaf31",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/f2d675b038e8aef08e084d884bf575e23dafaf31"
        },
        "date": 1779284220669,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 14,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bf31762bb99e34e91c1ae5b723038786163f9c46",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/bf31762bb99e34e91c1ae5b723038786163f9c46"
        },
        "date": 1779284227013,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 15,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "82c32c94605f4da4c4bb6d8bd2511793cbbdefbc",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/82c32c94605f4da4c4bb6d8bd2511793cbbdefbc"
        },
        "date": 1779290401143,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5f697f9b8202c1801175ae302d06714b5c3e6edb",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/5f697f9b8202c1801175ae302d06714b5c3e6edb"
        },
        "date": 1779291051591,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "87b36e66abcc3630fd992105799fa41567b474b0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/87b36e66abcc3630fd992105799fa41567b474b0"
        },
        "date": 1779297105570,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6504e9b6f183a7a5342af41804ae6fa23afd6cac",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/6504e9b6f183a7a5342af41804ae6fa23afd6cac"
        },
        "date": 1779297116918,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ebd42456124ca861f32d62c5fccd1f12116c4418",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/ebd42456124ca861f32d62c5fccd1f12116c4418"
        },
        "date": 1779297122104,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34120789d87efa88e9be36a2a82f1fb2dafbd4c5",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/34120789d87efa88e9be36a2a82f1fb2dafbd4c5"
        },
        "date": 1779297716984,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "acd7129840a5974ac91b2ad745e2282ead9ff051",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-20T18:49:44Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/acd7129840a5974ac91b2ad745e2282ead9ff051"
        },
        "date": 1779303924745,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5909564f60c5fda0f57a18fa2754e97645bf9935",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T18:49:44Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/5909564f60c5fda0f57a18fa2754e97645bf9935"
        },
        "date": 1779311335736,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ad88583ad51cf5328f506f90cf8fa1547236924c",
          "message": "Add experimental `ptr` crate to workspace re-exporting zerocopy pointer APIs",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3386/commits/ad88583ad51cf5328f506f90cf8fa1547236924c"
        },
        "date": 1779354581530,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "17d32bcbd4f06e016f52cdbd5db1c8648eb0f2d8",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/17d32bcbd4f06e016f52cdbd5db1c8648eb0f2d8"
        },
        "date": 1779367058750,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "97b876f689ad7b51f191ba5764d4011a0008e91e",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/97b876f689ad7b51f191ba5764d4011a0008e91e"
        },
        "date": 1779367537995,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fc9bc30fe54bb79950e5b2b3e340b5c958fe55ae",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/fc9bc30fe54bb79950e5b2b3e340b5c958fe55ae"
        },
        "date": 1779368183127,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a39dd5d889ba3fb40e67a11697ea372292135fc5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/a39dd5d889ba3fb40e67a11697ea372292135fc5"
        },
        "date": 1779368555910,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 41,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "520256aa96ef90aaa189aef2dd36fec45d74c9fd",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/520256aa96ef90aaa189aef2dd36fec45d74c9fd"
        },
        "date": 1779368885483,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b121141ca81985cc301d23e6079022b71fc61c02",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/b121141ca81985cc301d23e6079022b71fc61c02"
        },
        "date": 1779369202281,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "01a58ac62b72f5f196513a22f54fef82f18228dc",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/01a58ac62b72f5f196513a22f54fef82f18228dc"
        },
        "date": 1779369823746,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "277ebf3707b38060311af4f9a221b0ce8df27f06",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/277ebf3707b38060311af4f9a221b0ce8df27f06"
        },
        "date": 1779370934704,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0402dfa593751057a357c89fb8bd140780abd8d5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg` (#3387)\n\nRelease 0.8.49-alpha.\n\ngherrit-pr-id: Gblc7dfltwcey7wvtj3gjkseaqcltgwvf",
          "timestamp": "2026-05-21T13:53:30Z",
          "url": "https://github.com/google/zerocopy/commit/0402dfa593751057a357c89fb8bd140780abd8d5"
        },
        "date": 1779371673299,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "0402dfa593751057a357c89fb8bd140780abd8d5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg` (#3387)\n\nRelease 0.8.49-alpha.\n\ngherrit-pr-id: Gblc7dfltwcey7wvtj3gjkseaqcltgwvf",
          "timestamp": "2026-05-21T13:53:30Z",
          "tree_id": "4107ade63e23461c265e5d6eac61e3103e733349",
          "url": "https://github.com/google/zerocopy/commit/0402dfa593751057a357c89fb8bd140780abd8d5"
        },
        "date": 1779373834199,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 17,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "da65c51ab65456b58fda1a5193b8081ac338fc38",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on docs.rs",
          "timestamp": "2026-05-21T14:39:27Z",
          "url": "https://github.com/google/zerocopy/pull/3388/commits/da65c51ab65456b58fda1a5193b8081ac338fc38"
        },
        "date": 1779374475353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "edbfc855a61d62bfdd80738ad359c98cc0974339",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on docs.rs",
          "timestamp": "2026-05-21T14:39:27Z",
          "url": "https://github.com/google/zerocopy/pull/3388/commits/edbfc855a61d62bfdd80738ad359c98cc0974339"
        },
        "date": 1779374863381,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a8e831be33afc8a7f1e7cb3e776a83249c78d64c",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs",
          "timestamp": "2026-05-21T14:39:27Z",
          "url": "https://github.com/google/zerocopy/pull/3388/commits/a8e831be33afc8a7f1e7cb3e776a83249c78d64c"
        },
        "date": 1779375295719,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "881160631750e2e1a5876327f5f14804a77d4cc8",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs (#3388)\n\ngherrit-pr-id: G7p44q5rcehvy46vrrowj5vxxkgp3xuw7",
          "timestamp": "2026-05-21T15:41:06Z",
          "url": "https://github.com/google/zerocopy/commit/881160631750e2e1a5876327f5f14804a77d4cc8"
        },
        "date": 1779378124547,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "881160631750e2e1a5876327f5f14804a77d4cc8",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs (#3388)\n\ngherrit-pr-id: G7p44q5rcehvy46vrrowj5vxxkgp3xuw7",
          "timestamp": "2026-05-21T15:41:06Z",
          "tree_id": "fd526a60e3a69ed5ade2900feffae0c14d7ab32b",
          "url": "https://github.com/google/zerocopy/commit/881160631750e2e1a5876327f5f14804a77d4cc8"
        },
        "date": 1779379983550,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5e92221cebe3e206737f21a4769dfc96b67e351b",
          "message": "SQUASH ME: More minor fix-ups and a parallel strategy for invoking charon",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3391/commits/5e92221cebe3e206737f21a4769dfc96b67e351b"
        },
        "date": 1779487743941,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 981,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "722d82fc782f492fae901812589761e691834f9a",
          "message": "SQUASH ME: More fix-ups on things the agent got wrong, and some initial lock tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3392/commits/722d82fc782f492fae901812589761e691834f9a"
        },
        "date": 1779487755484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 991,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0ff00c6cc1807676a369d744e147571446ce53ab",
          "message": "SQUASH ME: Eliminate rust code parsing; simplify charon invocation; add tests to confirm charon is consuming all of workspace/project code",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3397/commits/0ff00c6cc1807676a369d744e147571446ce53ab"
        },
        "date": 1779487780035,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1006,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "39670e80a75cf768c9f715cfa60d49f93b4de489",
          "message": "SQUASH ME: More clarifying tweaks, plus new (unreviewed) locking tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3394/commits/39670e80a75cf768c9f715cfa60d49f93b4de489"
        },
        "date": 1779487795614,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1032,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "09f2e98d8a8f0a61e8838cb518d0b740d3c6d1dc",
          "message": "SQUASH ME: More clarifying tweaks, plus new (unreviewed) locking tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3395/commits/09f2e98d8a8f0a61e8838cb518d0b740d3c6d1dc"
        },
        "date": 1779487811316,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1039,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d48a2766ccaffa7f283474bdfd204c0612fd7272",
          "message": "SQUASH ME: First round of review focused on charon.rs; mostly style and comment changes",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3390/commits/d48a2766ccaffa7f283474bdfd204c0612fd7272"
        },
        "date": 1779487817376,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1053,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3ea68daa599483adfe1a4a6708d1cfa2c4694275",
          "message": "SQUASH ME: Initial port of run_charon and Expand",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3389/commits/3ea68daa599483adfe1a4a6708d1cfa2c4694275"
        },
        "date": 1779487832304,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1068,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1fb175297d7bdf03187f2399cb7404962954ed39",
          "message": "SQUASH ME: Add copyright/licenses to rust code; drop skipping behaviour from charon invocaitons loop; light code cleanup; a little documentation for generated test helper",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3396/commits/1fb175297d7bdf03187f2399cb7404962954ed39"
        },
        "date": 1779487836404,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1069,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9e7244b81bea553cd376f610409cc91c4ea462de",
          "message": "SQUASH ME: Add vendored dependencies; might have been required by previous iterations; oops",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3393/commits/9e7244b81bea553cd376f610409cc91c4ea462de"
        },
        "date": 1779487878525,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1114,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1f8bc9ee29fb6517819de1d00ce92ca9f29be253",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/1f8bc9ee29fb6517819de1d00ce92ca9f29be253"
        },
        "date": 1779719665779,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1022,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "128ab952cb5778efce34384f9a8bc2c5a95e88dc",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/128ab952cb5778efce34384f9a8bc2c5a95e88dc"
        },
        "date": 1779719677913,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1037,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3da3a84415ef0ec408e4dacde1e5ce5e109ba069",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/3da3a84415ef0ec408e4dacde1e5ce5e109ba069"
        },
        "date": 1779719681799,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1042,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1261a6811c0a0df31c98620a0c0c9e46378dcccd",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/1261a6811c0a0df31c98620a0c0c9e46378dcccd"
        },
        "date": 1779719683548,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1036,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "758f29023c9588793b2a54d19d87c450ab068e4d",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/758f29023c9588793b2a54d19d87c450ab068e4d"
        },
        "date": 1779719689470,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1049,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e8af624f0a27fd4ad304b5dd2e7c54cea743b6d8",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/e8af624f0a27fd4ad304b5dd2e7c54cea743b6d8"
        },
        "date": 1779719690609,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1042,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "17613f21e365ac963bc74a6349e2265f9a53b874",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/17613f21e365ac963bc74a6349e2265f9a53b874"
        },
        "date": 1779719717582,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1062,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5339ec75605af1b57dbd98733833461fb3ae9025",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/5339ec75605af1b57dbd98733833461fb3ae9025"
        },
        "date": 1779719748829,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1103,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "600a18b5bf48ef192e61dda5d44821e0a309e181",
          "message": "[CI] Bump the all-actions group with 12 updates",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/600a18b5bf48ef192e61dda5d44821e0a309e181"
        },
        "date": 1779720755049,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1af7238e8da43249587ed42444de44092b0804f4",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1af7238e8da43249587ed42444de44092b0804f4"
        },
        "date": 1779733863463,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "30344a26fa13fd857c2ffcd6462a6ac0eb7e2da8",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/30344a26fa13fd857c2ffcd6462a6ac0eb7e2da8"
        },
        "date": 1779733864353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e8924f2dc907cdbd9b3c71c64cce2342944e2527",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/e8924f2dc907cdbd9b3c71c64cce2342944e2527"
        },
        "date": 1779733866413,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3d47a32c21279e551eb30400e95ba3e147d1675",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/a3d47a32c21279e551eb30400e95ba3e147d1675"
        },
        "date": 1779733867632,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1c62cfdaa9078c649c15b374fdee2c9e214dbbf7",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/1c62cfdaa9078c649c15b374fdee2c9e214dbbf7"
        },
        "date": 1779733866055,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f549d170be5eef4481a45f436510b9ee3326d706",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/f549d170be5eef4481a45f436510b9ee3326d706"
        },
        "date": 1779733867780,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4827fa1e3199e99d13fcec9868efcf249a090fdd",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/4827fa1e3199e99d13fcec9868efcf249a090fdd"
        },
        "date": 1779733870694,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "84de2552b3140f5d16626eaa2212396310f8368c",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/84de2552b3140f5d16626eaa2212396310f8368c"
        },
        "date": 1779733870001,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f0ebc056e646c38bb2ee34fb87c14ce75624fbe9",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/f0ebc056e646c38bb2ee34fb87c14ce75624fbe9"
        },
        "date": 1779733864218,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e229a984fc689f56bc396b0cc8da6ec021d2cce6",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/e229a984fc689f56bc396b0cc8da6ec021d2cce6"
        },
        "date": 1779733869516,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fe814939a6469ef85bd86d0ce162544cd52e66f9",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/fe814939a6469ef85bd86d0ce162544cd52e66f9"
        },
        "date": 1779733865592,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "29a832dee34788cf73fb1f1ab14833c17e38cb0a",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/29a832dee34788cf73fb1f1ab14833c17e38cb0a"
        },
        "date": 1779733872761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "632f851f0a3ff3b8e5b4168a40e559d9cbf582fb",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/632f851f0a3ff3b8e5b4168a40e559d9cbf582fb"
        },
        "date": 1779736397243,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0133269f943a3ed9c2d80d6d26b11f715be7a9b4",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/0133269f943a3ed9c2d80d6d26b11f715be7a9b4"
        },
        "date": 1779736397541,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "43a1ef4e0e09638d38bad90ab29d945cea99a8cb",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/43a1ef4e0e09638d38bad90ab29d945cea99a8cb"
        },
        "date": 1779736401532,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b10330bfaee0a1b2beb53dfab08ad3e7b652c696",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/b10330bfaee0a1b2beb53dfab08ad3e7b652c696"
        },
        "date": 1779736404829,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e60c407e7fc952258e9d32ab08e84d8e50e9f008",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/e60c407e7fc952258e9d32ab08e84d8e50e9f008"
        },
        "date": 1779736403739,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "785ffee6aea00b0cbe84b64d156ad3dae730054f",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/785ffee6aea00b0cbe84b64d156ad3dae730054f"
        },
        "date": 1779736403477,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0d0579829c4aa7402cdbee7f3c513c6bdedacc14",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/0d0579829c4aa7402cdbee7f3c513c6bdedacc14"
        },
        "date": 1779736412813,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 5,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f300c70eb6104a5a175d5c0de463f32de3316d9c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f300c70eb6104a5a175d5c0de463f32de3316d9c"
        },
        "date": 1779736415002,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8815480d922eb5f7827aed0ea7e54073b1c950e5",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/8815480d922eb5f7827aed0ea7e54073b1c950e5"
        },
        "date": 1779736420177,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9450f8623c20666f74b78f56950bbcc9241abd0c",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/9450f8623c20666f74b78f56950bbcc9241abd0c"
        },
        "date": 1779736434227,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dd2f402ef606665ce4beca1793b09db4c7ebba7d",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/dd2f402ef606665ce4beca1793b09db4c7ebba7d"
        },
        "date": 1779736435830,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2fcfb3371cdc0f6ca1c16ab6c18253de09194113",
          "message": "[anneal][v2] Initial commit of `exocrate` (#3376)\n\ngherrit-pr-id: G34qjom3lz7cc6hd57tgp44t4pzlstdhj\n\nCo-authored-by: Mark Dittmer <markdittmer@google.com>",
          "timestamp": "2026-05-25T15:20:48-04:00",
          "tree_id": "602fe9e513bae3aa5ba6dcf91e4b5b93cf8d59dd",
          "url": "https://github.com/google/zerocopy/commit/2fcfb3371cdc0f6ca1c16ab6c18253de09194113"
        },
        "date": 1779736884872,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2ae5a009ac0b70ae5c20111ec18e5a84c3f79716",
          "message": "SQUASH ME into toml_cost dep",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3413/commits/2ae5a009ac0b70ae5c20111ec18e5a84c3f79716"
        },
        "date": 1779737430884,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1041,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4f657b10c5c84de1faa6807531050d66fc49930a",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/4f657b10c5c84de1faa6807531050d66fc49930a"
        },
        "date": 1779737715595,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b59e6f0c61374b8a757b6c756c03e8fae8bf8317",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/b59e6f0c61374b8a757b6c756c03e8fae8bf8317"
        },
        "date": 1779737717171,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "41c40c7db5b733eb7180fc351b8c94c5ba1e185f",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/41c40c7db5b733eb7180fc351b8c94c5ba1e185f"
        },
        "date": 1779737719130,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1e8210d44264d23cfb599c49a169d0b467a5bead",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/1e8210d44264d23cfb599c49a169d0b467a5bead"
        },
        "date": 1779737724117,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "56d3125c79237a68329ccd7d4d7a92189673a9db",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/56d3125c79237a68329ccd7d4d7a92189673a9db"
        },
        "date": 1779737735264,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fa0696c4f6e5baf684d3f87217c93a15dfe91013",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/fa0696c4f6e5baf684d3f87217c93a15dfe91013"
        },
        "date": 1779737736437,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ef3dd8b8f7476f7ac3afe98afec7d304c80c0f72",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/ef3dd8b8f7476f7ac3afe98afec7d304c80c0f72"
        },
        "date": 1779737738301,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f8d740b542136a96f94df3296a38c839b82e2959",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/f8d740b542136a96f94df3296a38c839b82e2959"
        },
        "date": 1779737736569,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f3e3b5ecb8fab65be756f2aafa3047886f06eaae",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f3e3b5ecb8fab65be756f2aafa3047886f06eaae"
        },
        "date": 1779737737533,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb7cac5546d5c9256786007391790a6ff775f67c",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/cb7cac5546d5c9256786007391790a6ff775f67c"
        },
        "date": 1779737744470,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c7bc3352a1c146f92395b500d61791385d0898f3",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/c7bc3352a1c146f92395b500d61791385d0898f3"
        },
        "date": 1779737743171,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Mark Dittmer",
            "username": "mdittmer",
            "email": "mdittmer@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "275aff21f3b22c4c4db0311576b897b8d5805fa8",
          "message": "[anneal][v2] Independently vendor and patch toml_const (#3381)\n\n- Vendor `anneal/v2` dependencies independently\n- Patch `toml_const` to avoid breakage on `'cfg(...)'` keys in\n  `Cargo.toml` files\n\ngherrit-pr-id: Ga27arw5h5oz3ldi25ijsj2rsbzuqictv",
          "timestamp": "2026-05-25T19:51:17Z",
          "url": "https://github.com/google/zerocopy/commit/275aff21f3b22c4c4db0311576b897b8d5805fa8"
        },
        "date": 1779738726362,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "275aff21f3b22c4c4db0311576b897b8d5805fa8",
          "message": "[anneal][v2] Independently vendor and patch toml_const (#3381)\n\n- Vendor `anneal/v2` dependencies independently\n- Patch `toml_const` to avoid breakage on `'cfg(...)'` keys in\n  `Cargo.toml` files\n\ngherrit-pr-id: Ga27arw5h5oz3ldi25ijsj2rsbzuqictv",
          "timestamp": "2026-05-25T19:51:17Z",
          "tree_id": "bb9133d186a3e0b671544c47ee9211654e81bc5f",
          "url": "https://github.com/google/zerocopy/commit/275aff21f3b22c4c4db0311576b897b8d5805fa8"
        },
        "date": 1779740589301,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9606fecb64feec3aba8a78fc135667f7c06ec097",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/9606fecb64feec3aba8a78fc135667f7c06ec097"
        },
        "date": 1779749326194,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "25f8010762c0f7915218c94fb5d019b4b1381812",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/25f8010762c0f7915218c94fb5d019b4b1381812"
        },
        "date": 1779749327747,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ebd26a04cf7bed697c35bad7f6feae340fcb07c1",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/ebd26a04cf7bed697c35bad7f6feae340fcb07c1"
        },
        "date": 1779749329121,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "64753f4d4fb2454579dc32791cfed49ab3855a14",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/64753f4d4fb2454579dc32791cfed49ab3855a14"
        },
        "date": 1779749331191,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f838f8ebae2730fa468f9001522603869c6095aa",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f838f8ebae2730fa468f9001522603869c6095aa"
        },
        "date": 1779749329182,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7035d4bf1e1d5b271e25c1fdfca8fb36ce881eb0",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/7035d4bf1e1d5b271e25c1fdfca8fb36ce881eb0"
        },
        "date": 1779749331808,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "82160afdc28389bda8429edd8f19555dec8a3816",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/82160afdc28389bda8429edd8f19555dec8a3816"
        },
        "date": 1779749336442,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7e1f72e47a46abdc46a797e73eed1b86b6191a3f",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/7e1f72e47a46abdc46a797e73eed1b86b6191a3f"
        },
        "date": 1779749335583,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "26c45cf3848f5b65df19e6f01d2dfcf9fe4e93db",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/26c45cf3848f5b65df19e6f01d2dfcf9fe4e93db"
        },
        "date": 1779749333541,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fafcee46f6866df9d56f36cf6f7d069b830b5452",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/fafcee46f6866df9d56f36cf6f7d069b830b5452"
        },
        "date": 1779749334139,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d0babbacd343fc7132a8171c5eeb7b1754561159",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0",
          "timestamp": "2026-05-26T12:42:10Z",
          "url": "https://github.com/google/zerocopy/pull/3415/commits/d0babbacd343fc7132a8171c5eeb7b1754561159"
        },
        "date": 1779811651855,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0321b8e7055ae7159280930753924207775dc35a",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0 (#3415)\n\ngherrit-pr-id: Gz2xxcekiwax6yzlsfzuwlzh4mcfd5nms",
          "timestamp": "2026-05-26T16:20:03Z",
          "url": "https://github.com/google/zerocopy/commit/0321b8e7055ae7159280930753924207775dc35a"
        },
        "date": 1779812461307,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0321b8e7055ae7159280930753924207775dc35a",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0 (#3415)\n\ngherrit-pr-id: Gz2xxcekiwax6yzlsfzuwlzh4mcfd5nms",
          "timestamp": "2026-05-26T16:20:03Z",
          "tree_id": "0b33f6617272bf085e9e17ced8468c3c66b75681",
          "url": "https://github.com/google/zerocopy/commit/0321b8e7055ae7159280930753924207775dc35a"
        },
        "date": 1779814330835,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9e20917878209f411fe3f16323c70e2eccea2d56",
          "message": "[wip] Introduce unstable `derive(most_traits)`",
          "timestamp": "2026-05-26T16:51:55Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/9e20917878209f411fe3f16323c70e2eccea2d56"
        },
        "date": 1779878620154,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9a0d277803d54383a7ae40348856e390c322ae25",
          "message": "[wip] Introduce unstable `derive(most_traits)`",
          "timestamp": "2026-05-26T16:51:55Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/9a0d277803d54383a7ae40348856e390c322ae25"
        },
        "date": 1779880465946,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "145818923+google-pr-creation-bot@users.noreply.github.com",
            "name": "Google PR Creation Bot",
            "username": "google-pr-creation-bot"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5fc5d5bef889bbf81ab5bae500758979d5978a08",
          "message": "Release 0.8.49 (#3417)",
          "timestamp": "2026-05-27T11:55:29-04:00",
          "tree_id": "4b298b6678caa62663f284dce3339ee15b73f7cd",
          "url": "https://github.com/google/zerocopy/commit/5fc5d5bef889bbf81ab5bae500758979d5978a08"
        },
        "date": 1779897366078,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d3b95475a24f7b287ee37ecaff4ea6271c369881",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/d3b95475a24f7b287ee37ecaff4ea6271c369881"
        },
        "date": 1779905775572,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "98f4d2f73fb213c8700d3688adb27104c1a01018",
          "message": "[anneal][v2] Vendor charon_lib",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/98f4d2f73fb213c8700d3688adb27104c1a01018"
        },
        "date": 1779905816887,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9f295066c87989fc930838ef171ddaf8bb1de5e0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/9f295066c87989fc930838ef171ddaf8bb1de5e0"
        },
        "date": 1779905821790,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4488992b0c74134e39a647ad3160cd596838823a",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/4488992b0c74134e39a647ad3160cd596838823a"
        },
        "date": 1779905826164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1faae2d750595519e398f2f4364bff2aa861f6f5",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/1faae2d750595519e398f2f4364bff2aa861f6f5"
        },
        "date": 1779905857136,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0cf1bf4a1eeae8d8c3f711f8e2545e9e34c1344d",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/0cf1bf4a1eeae8d8c3f711f8e2545e9e34c1344d"
        },
        "date": 1779905864982,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3bc3a25735f833f02603005c6e64151d5a20a9a",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/a3bc3a25735f833f02603005c6e64151d5a20a9a"
        },
        "date": 1779905874241,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "88f14ff06f5a7da6baeca4b34c45e031c0c27d42",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/88f14ff06f5a7da6baeca4b34c45e031c0c27d42"
        },
        "date": 1779905878047,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c8aa431253246e619045b8cbdabedb327ab03b3a",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/c8aa431253246e619045b8cbdabedb327ab03b3a"
        },
        "date": 1779905890681,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c63a42248a93ff6fe32f7575fdc50dd531ecc547",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/c63a42248a93ff6fe32f7575fdc50dd531ecc547"
        },
        "date": 1779905897090,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5cf75ddb427040e4b0bc61aea0d7d7b2351543d1",
          "message": "[pointer] `Ptr::iter` takes `self` by value",
          "timestamp": "2026-05-28T17:15:11Z",
          "url": "https://github.com/google/zerocopy/pull/3421/commits/5cf75ddb427040e4b0bc61aea0d7d7b2351543d1"
        },
        "date": 1779996407905,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a108b904cd2b4d03efe7a54f8dcd8fc13dcc536e",
          "message": "[pointer] `Ptr::iter` takes `self` by value",
          "timestamp": "2026-05-28T17:15:11Z",
          "url": "https://github.com/google/zerocopy/pull/3421/commits/a108b904cd2b4d03efe7a54f8dcd8fc13dcc536e"
        },
        "date": 1779996526236,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "eaec844201fd1ee229c6af68440cbc202f68eccc",
          "message": "[pointer] `Ptr::iter` takes `self` by value",
          "timestamp": "2026-05-28T17:15:11Z",
          "url": "https://github.com/google/zerocopy/pull/3421/commits/eaec844201fd1ee229c6af68440cbc202f68eccc"
        },
        "date": 1779997314278,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "f70e4224996ed73b2cd927719246361d977a629e",
          "message": "[pointer] `Ptr::iter` takes `self` by value (#3421)\n\nThis fixes a prior soundness hole - `Ptr::iter` took `&self`, permitting\nmultiple overlapping `Exclusive` `Ptr`s to be created at the same time.\n\nIn CI, when running `cargo-semver-checks`, don't pass `--cfg\nzerocopy_unstable_ptr`, as we don't want to semver-check unstable APIs.\n\nRelease 0.8.50.\n\nFixes #3419\n\ngherrit-pr-id: Ibb7d512d9e12ecfd118bb018bcae10d17279c2ed",
          "timestamp": "2026-05-29T17:01:13Z",
          "url": "https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e"
        },
        "date": 1780074132704,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f70e4224996ed73b2cd927719246361d977a629e",
          "message": "[pointer] `Ptr::iter` takes `self` by value (#3421)\n\nThis fixes a prior soundness hole - `Ptr::iter` took `&self`, permitting\nmultiple overlapping `Exclusive` `Ptr`s to be created at the same time.\n\nIn CI, when running `cargo-semver-checks`, don't pass `--cfg\nzerocopy_unstable_ptr`, as we don't want to semver-check unstable APIs.\n\nRelease 0.8.50.\n\nFixes #3419\n\ngherrit-pr-id: Ibb7d512d9e12ecfd118bb018bcae10d17279c2ed",
          "timestamp": "2026-05-29T17:01:13Z",
          "tree_id": "5d0f67bd945a1ceeab35e9cc06db105ebf037300",
          "url": "https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e"
        },
        "date": 1780076229082,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "10a3239fe6afd068b249aee8ed7d37ff6ac3f37c",
          "message": "[CI] Bump the all-actions group across 1 directory with 12 updates",
          "timestamp": "2026-05-29T17:36:36Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/10a3239fe6afd068b249aee8ed7d37ff6ac3f37c"
        },
        "date": 1780076474863,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "76e1c7ebf4c09a90b7f3efbd3bc8393825cf3cd8",
          "message": "Make GHCR cache exports and consumer pushes conditional for external PRs",
          "timestamp": "2026-05-31T08:45:06Z",
          "url": "https://github.com/google/zerocopy/pull/3423/commits/76e1c7ebf4c09a90b7f3efbd3bc8393825cf3cd8"
        },
        "date": 1780249251028,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "cf7cf6154867078e8b994ae981959edffaf724a9",
          "message": "Handle fork PR Docker cache permissions (#3423)\n\n### Motivation\n- External fork PRs were failing CI at Docker build/cache steps because the runner `GITHUB_TOKEN` for forks does not have permission to write GHCR packages or cache entries.\n\n### Description\n- In `.github/workflows/ci.yml` conditionally disable `cache-to` exports to GHCR for external pull requests while preserving cache exports for same-repo runs, pushes, merge groups, and workflow dispatches.\n- In `.github/workflows/anneal.yml` conditionally disable `cache-to` and guard the `Build and push Docker image` step so image push/cache writes are only attempted when the run is allowed to write to GHCR.\n- In `.github/workflows/anneal.yml` add `if:` guards on Anneal consumer jobs (`anneal_tests` and `verify_examples`) so those consumer jobs are skipped for external fork PRs that cannot publish the GHCR image they would consume.\n\n### Testing\n- Ran `./ci/check_actions.sh` and it completed successfully.\n- Ran `git diff --check` and it produced no issues.\n- Ran `CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 ./githooks/pre-push` to exercise the repo hooks in a non-interactive way and it completed successfully (the initial pre-push without auto-install hit local tooling prompts).",
          "timestamp": "2026-05-31T19:36:24Z",
          "url": "https://github.com/google/zerocopy/commit/cf7cf6154867078e8b994ae981959edffaf724a9"
        },
        "date": 1780256228069,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cf7cf6154867078e8b994ae981959edffaf724a9",
          "message": "Handle fork PR Docker cache permissions (#3423)\n\n### Motivation\n- External fork PRs were failing CI at Docker build/cache steps because the runner `GITHUB_TOKEN` for forks does not have permission to write GHCR packages or cache entries.\n\n### Description\n- In `.github/workflows/ci.yml` conditionally disable `cache-to` exports to GHCR for external pull requests while preserving cache exports for same-repo runs, pushes, merge groups, and workflow dispatches.\n- In `.github/workflows/anneal.yml` conditionally disable `cache-to` and guard the `Build and push Docker image` step so image push/cache writes are only attempted when the run is allowed to write to GHCR.\n- In `.github/workflows/anneal.yml` add `if:` guards on Anneal consumer jobs (`anneal_tests` and `verify_examples`) so those consumer jobs are skipped for external fork PRs that cannot publish the GHCR image they would consume.\n\n### Testing\n- Ran `./ci/check_actions.sh` and it completed successfully.\n- Ran `git diff --check` and it produced no issues.\n- Ran `CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 ./githooks/pre-push` to exercise the repo hooks in a non-interactive way and it completed successfully (the initial pre-push without auto-install hit local tooling prompts).",
          "timestamp": "2026-05-31T19:36:24Z",
          "tree_id": "0c131497ef5db2f7d6f3a9f16795ee729af0212b",
          "url": "https://github.com/google/zerocopy/commit/cf7cf6154867078e8b994ae981959edffaf724a9"
        },
        "date": 1780258120442,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "00a7076e157d1469041eaac25b6fa3094b2144f0",
          "message": "[CI] Bump the all-actions group across 1 directory with 12 updates",
          "timestamp": "2026-05-31T20:08:06Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/00a7076e157d1469041eaac25b6fa3094b2144f0"
        },
        "date": 1780258357102,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "92d264efb130c8253e7a95de749fa2567e868b88",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/92d264efb130c8253e7a95de749fa2567e868b88"
        },
        "date": 1780492705632,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1112,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1da6e9a7fafa4ba605b548ef8010b32ec188dae0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/1da6e9a7fafa4ba605b548ef8010b32ec188dae0"
        },
        "date": 1780492708684,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1113,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5ad38a52b02aea911c3192fe890071517e51bb54",
          "message": "Prevent external PRs from pushing benchmark data in anneal CI workflow",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3430/commits/5ad38a52b02aea911c3192fe890071517e51bb54"
        },
        "date": 1780518289873,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1170,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cacc81c2bdb1efa169bed1dda231d89590539f7b",
          "message": "[ci][anneal] Don't publish fork PR benchmarks (#3430)",
          "timestamp": "2026-06-03T13:54:01-07:00",
          "tree_id": "489e52a87f260a77311791b511785c53a13c281d",
          "url": "https://github.com/google/zerocopy/commit/cacc81c2bdb1efa169bed1dda231d89590539f7b"
        },
        "date": 1780521205563,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1132,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "63a83e13e35d91481778e9942aa2ca4f11f16cb9",
          "message": "[CI] Bump the all-actions group across 1 directory with 13 updates",
          "timestamp": "2026-06-03T20:54:07Z",
          "url": "https://github.com/google/zerocopy/pull/3431/commits/63a83e13e35d91481778e9942aa2ca4f11f16cb9"
        },
        "date": 1780521525549,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1200,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Sock",
            "username": "platonicsock",
            "email": "87631534+platonicsock@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "eb1191c8eac66a19a3e6e0ec3cd88fa457553a64",
          "message": "Fixed section reference (#3424)\n\nSyntax description is in Section 6, not Section 5",
          "timestamp": "2026-06-03T21:26:04Z",
          "url": "https://github.com/google/zerocopy/commit/eb1191c8eac66a19a3e6e0ec3cd88fa457553a64"
        },
        "date": 1780522015268,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "87631534+platonicsock@users.noreply.github.com",
            "name": "Sock",
            "username": "platonicsock"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bd37d45186e8f846df74da6f2d17ded4e19b4bd4",
          "message": "Typo fixes (#3425)\n\nTwo instances of changing \"Anneal'\" to \"Anneal's\"",
          "timestamp": "2026-06-03T14:30:13-07:00",
          "tree_id": "735cf8abf0171da25ea8da7e0e8363d301df4f0a",
          "url": "https://github.com/google/zerocopy/commit/bd37d45186e8f846df74da6f2d17ded4e19b4bd4"
        },
        "date": 1780522458476,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d7628df296e7b763217ed75462507c746c335946",
          "message": "[wip] Introduce unstable `derive(most_traits)`, linux cfg.",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/d7628df296e7b763217ed75462507c746c335946"
        },
        "date": 1780620277735,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c0960e362b384b7b97e863e6a5521b8faaa8c83a",
          "message": "[wip] Introduce unstable `derive(most_traits)`, linux cfg.",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/c0960e362b384b7b97e863e6a5521b8faaa8c83a"
        },
        "date": 1780620510375,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "80544d91c9f08540c76c52d7df093a2b811872c5",
          "message": "[wip] Introduce unstable `derive(most_traits)`, linux cfg.",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/80544d91c9f08540c76c52d7df093a2b811872c5"
        },
        "date": 1780620589608,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1fa66dc492fd697eb58bc2d206c971d59d61b439",
          "message": "[zerocopy] Move to `zerocopy` subdirectory",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3434/commits/1fa66dc492fd697eb58bc2d206c971d59d61b439"
        },
        "date": 1780623602896,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2e0a025108c8169b15ce72405b08df41d8f62660",
          "message": "[zerocopy] Move to `zerocopy` subdirectory",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3434/commits/2e0a025108c8169b15ce72405b08df41d8f62660"
        },
        "date": 1780631580138,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a773081477608b799ccdd48de490de139e19873c",
          "message": "[zerocopy] Move to `zerocopy` subdirectory (#3434)\n\nMove the Zerocopy crate and its vendored Cargo configuration under\n`zerocopy/`, and update CI, docs, hooks, and helper scripts to run\nzerocopy commands from that directory.\n\nThis keeps zerocopy in its own vendored Cargo world while allowing\ntools, Anneal, and future crates to use normal Cargo resolution and not\nrequire vendoring their dependencies.\n\nAlso move `anneal/v2/exocrate` to the repository root.\n\ngherrit-pr-id: Ghuilhfh6h4womt35vc6domtloovmnnhl",
          "timestamp": "2026-06-05T04:04:48Z",
          "url": "https://github.com/google/zerocopy/commit/a773081477608b799ccdd48de490de139e19873c"
        },
        "date": 1780632339822,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a773081477608b799ccdd48de490de139e19873c",
          "message": "[zerocopy] Move to `zerocopy` subdirectory (#3434)\n\nMove the Zerocopy crate and its vendored Cargo configuration under\n`zerocopy/`, and update CI, docs, hooks, and helper scripts to run\nzerocopy commands from that directory.\n\nThis keeps zerocopy in its own vendored Cargo world while allowing\ntools, Anneal, and future crates to use normal Cargo resolution and not\nrequire vendoring their dependencies.\n\nAlso move `anneal/v2/exocrate` to the repository root.\n\ngherrit-pr-id: Ghuilhfh6h4womt35vc6domtloovmnnhl",
          "timestamp": "2026-06-05T04:04:48Z",
          "tree_id": "60647c9d9df642af06edc6597d6f373d203aaccc",
          "url": "https://github.com/google/zerocopy/commit/a773081477608b799ccdd48de490de139e19873c"
        },
        "date": 1780634270719,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "366d9ad222be87ad1311a0fb45e96d23f25381f0",
          "message": "[CI] Bump the all-actions group across 1 directory with 13 updates",
          "timestamp": "2026-06-05T04:37:36Z",
          "url": "https://github.com/google/zerocopy/pull/3431/commits/366d9ad222be87ad1311a0fb45e96d23f25381f0"
        },
        "date": 1780634517078,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b33d9a0254ff8b1fddceaa6e675020168d8aedf1",
          "message": "Bump the cargo group across 1 directory with 4 updates",
          "timestamp": "2026-06-05T04:37:36Z",
          "url": "https://github.com/google/zerocopy/pull/3435/commits/b33d9a0254ff8b1fddceaa6e675020168d8aedf1"
        },
        "date": 1780635427526,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1066,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "dependabot[bot]",
            "username": "dependabot[bot]",
            "email": "49699333+dependabot[bot]@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "bc0bb77346772be0e80aeb68f8f3f9b2e58a1612",
          "message": "Bump the cargo group across 1 directory with 4 updates (#3435)\n\nBumps the cargo group with 4 updates in the /anneal directory: [tar](https://github.com/composefs/tar-rs), [openssl](https://github.com/rust-openssl/rust-openssl), [rand](https://github.com/rust-random/rand) and [rustls-webpki](https://github.com/rustls/webpki).\n\n\nUpdates `tar` from 0.4.45 to 0.4.46\n- [Release notes](https://github.com/composefs/tar-rs/releases)\n- [Commits](https://github.com/composefs/tar-rs/compare/0.4.45...0.4.46)\n\nUpdates `openssl` from 0.10.76 to 0.10.80\n- [Release notes](https://github.com/rust-openssl/rust-openssl/releases)\n- [Commits](https://github.com/rust-openssl/rust-openssl/compare/openssl-v0.10.76...openssl-v0.10.80)\n\nUpdates `rand` from 0.9.2 to 0.9.4\n- [Release notes](https://github.com/rust-random/rand/releases)\n- [Changelog](https://github.com/rust-random/rand/blob/0.9.4/CHANGELOG.md)\n- [Commits](https://github.com/rust-random/rand/compare/rand_core-0.9.2...0.9.4)\n\nUpdates `rustls-webpki` from 0.103.10 to 0.103.13\n- [Release notes](https://github.com/rustls/webpki/releases)\n- [Commits](https://github.com/rustls/webpki/compare/v/0.103.10...v/0.103.13)\n\n---\nupdated-dependencies:\n- dependency-name: tar\n  dependency-version: 0.4.46\n  dependency-type: direct:production\n  dependency-group: cargo\n- dependency-name: openssl\n  dependency-version: 0.10.80\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rand\n  dependency-version: 0.9.4\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rustls-webpki\n  dependency-version: 0.103.13\n  dependency-type: indirect\n  dependency-group: cargo\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>",
          "timestamp": "2026-06-05T05:08:07Z",
          "url": "https://github.com/google/zerocopy/commit/bc0bb77346772be0e80aeb68f8f3f9b2e58a1612"
        },
        "date": 1780637187925,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1066,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc0bb77346772be0e80aeb68f8f3f9b2e58a1612",
          "message": "Bump the cargo group across 1 directory with 4 updates (#3435)\n\nBumps the cargo group with 4 updates in the /anneal directory: [tar](https://github.com/composefs/tar-rs), [openssl](https://github.com/rust-openssl/rust-openssl), [rand](https://github.com/rust-random/rand) and [rustls-webpki](https://github.com/rustls/webpki).\n\n\nUpdates `tar` from 0.4.45 to 0.4.46\n- [Release notes](https://github.com/composefs/tar-rs/releases)\n- [Commits](https://github.com/composefs/tar-rs/compare/0.4.45...0.4.46)\n\nUpdates `openssl` from 0.10.76 to 0.10.80\n- [Release notes](https://github.com/rust-openssl/rust-openssl/releases)\n- [Commits](https://github.com/rust-openssl/rust-openssl/compare/openssl-v0.10.76...openssl-v0.10.80)\n\nUpdates `rand` from 0.9.2 to 0.9.4\n- [Release notes](https://github.com/rust-random/rand/releases)\n- [Changelog](https://github.com/rust-random/rand/blob/0.9.4/CHANGELOG.md)\n- [Commits](https://github.com/rust-random/rand/compare/rand_core-0.9.2...0.9.4)\n\nUpdates `rustls-webpki` from 0.103.10 to 0.103.13\n- [Release notes](https://github.com/rustls/webpki/releases)\n- [Commits](https://github.com/rustls/webpki/compare/v/0.103.10...v/0.103.13)\n\n---\nupdated-dependencies:\n- dependency-name: tar\n  dependency-version: 0.4.46\n  dependency-type: direct:production\n  dependency-group: cargo\n- dependency-name: openssl\n  dependency-version: 0.10.80\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rand\n  dependency-version: 0.9.4\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rustls-webpki\n  dependency-version: 0.103.13\n  dependency-type: indirect\n  dependency-group: cargo\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>",
          "timestamp": "2026-06-05T05:08:07Z",
          "tree_id": "46c88fe74ea7fb7b5b5974d81872b4129e09ac82",
          "url": "https://github.com/google/zerocopy/commit/bc0bb77346772be0e80aeb68f8f3f9b2e58a1612"
        },
        "date": 1780639156784,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 1218,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "eiffel-fl",
            "username": "eiffel-fl",
            "email": "laniel_francis@privacyrequired.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "c97143cb09c7edb578c4a9edaf50d8db720f60a9",
          "message": "[byteorder] Add cfg no_fp_fmt_parse (#3429)\n\nThis cfg deactivates Debug and Display for floatting point numbers, this is\nparticluarly useful in kernel context.\nThe implementation is inspired by:\nhttps://github.com/rust-lang/rust/commit/ec7292ad3c35\n\nFixes #3426",
          "timestamp": "2026-06-05T13:59:43Z",
          "url": "https://github.com/google/zerocopy/commit/c97143cb09c7edb578c4a9edaf50d8db720f60a9"
        },
        "date": 1780668074653,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 50,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "laniel_francis@privacyrequired.com",
            "name": "eiffel-fl",
            "username": "eiffel-fl"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "c97143cb09c7edb578c4a9edaf50d8db720f60a9",
          "message": "[byteorder] Add cfg no_fp_fmt_parse (#3429)\n\nThis cfg deactivates Debug and Display for floatting point numbers, this is\nparticluarly useful in kernel context.\nThe implementation is inspired by:\nhttps://github.com/rust-lang/rust/commit/ec7292ad3c35\n\nFixes #3426",
          "timestamp": "2026-06-05T13:59:43Z",
          "tree_id": "6709fbc182f55d749bc31796fd2fb83d2e017624",
          "url": "https://github.com/google/zerocopy/commit/c97143cb09c7edb578c4a9edaf50d8db720f60a9"
        },
        "date": 1780669934374,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "033adcefe4b458766f1b1d90884d40f806f8fa1a",
          "message": "Introduce `derive(most_traits)` and rename unstable linux cfg",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/033adcefe4b458766f1b1d90884d40f806f8fa1a"
        },
        "date": 1780671248293,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "61f280f44d4450f21041adbb88cd41c8a72efa98",
          "message": "Introduce `derive(most_traits)` and rename unstable linux cfg",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/61f280f44d4450f21041adbb88cd41c8a72efa98"
        },
        "date": 1780671462177,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 6,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb7c1ea5c58cf7c49eb48227eb29ff99718f6490",
          "message": "Introduce `derive(most_traits)` and rename unstable linux cfg",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/cb7c1ea5c58cf7c49eb48227eb29ff99718f6490"
        },
        "date": 1780671533483,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "da15155d75a90ea73fdbdf3bc16d1d447ff3fcd5",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/da15155d75a90ea73fdbdf3bc16d1d447ff3fcd5"
        },
        "date": 1780675371377,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ea0358ed52b7bd3ed92443a2c83a57d1abfe0465",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/ea0358ed52b7bd3ed92443a2c83a57d1abfe0465"
        },
        "date": 1780675376666,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 15,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "616962d5f9a8212858c6ee9ad81022cf5edc1403",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/616962d5f9a8212858c6ee9ad81022cf5edc1403"
        },
        "date": 1780675380557,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 10,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ab47687955605152b7e48c017b638520f2dcbee5",
          "message": "[anneal][v2][exocrate] Add install fixup hook",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3436/commits/ab47687955605152b7e48c017b638520f2dcbee5"
        },
        "date": 1780675382146,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cc455f23a36ba3c5557833b715abd806b7a9a7b8",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/cc455f23a36ba3c5557833b715abd806b7a9a7b8"
        },
        "date": 1780675386703,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 12,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "012f46ef310d195c7257acb245e7d2fecd90022e",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/012f46ef310d195c7257acb245e7d2fecd90022e"
        },
        "date": 1780675391956,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "491140c513436cf4393c075811a2159bb48cc4e2",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/491140c513436cf4393c075811a2159bb48cc4e2"
        },
        "date": 1780675396318,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "10684dbad1d5c5f994a274ddfd3b7db9f6ebcedc",
          "message": "[anneal][v2] Vendor charon_lib",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/10684dbad1d5c5f994a274ddfd3b7db9f6ebcedc"
        },
        "date": 1780675396734,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "964666dcdf6424e494e25da0ba8749bbc91dca67",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/964666dcdf6424e494e25da0ba8749bbc91dca67"
        },
        "date": 1780675407498,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "99996e42477579faa684a3a86b860998f9bf70a1",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/99996e42477579faa684a3a86b860998f9bf70a1"
        },
        "date": 1780675407770,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 13,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "06a06836795d8dfb109e56f4f813970beab79e73",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/06a06836795d8dfb109e56f4f813970beab79e73"
        },
        "date": 1780675411617,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 11,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "86ea86c44eec663397077a020102c8b0bb28e6d9",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T16:17:53Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/86ea86c44eec663397077a020102c8b0bb28e6d9"
        },
        "date": 1780681712148,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "75c8f447736105f681c52d3e88928df2815dc661",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T16:17:53Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/75c8f447736105f681c52d3e88928df2815dc661"
        },
        "date": 1780688740344,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Mark Dittmer",
            "username": "mdittmer",
            "email": "mdittmer@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "4d76e9893f4ff90ddaf16bbad68f9c148df35cb0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate (#3383)\n\n- Add nix derivations for exocrate\n- Add `setup` sub-command to locate-or-install exocrate\n- Add integration test for \"developer mode\" `setup` that presumes local\n  exocrate archive\n- Add github workflows to:\n  - Warm nix cache\n  - Locally link exocrate archive from nix, then run all tests\n\ngherrit-pr-id: Gwhroikc5idscowxamayknlke2uiddzv3",
          "timestamp": "2026-06-05T21:51:39Z",
          "url": "https://github.com/google/zerocopy/commit/4d76e9893f4ff90ddaf16bbad68f9c148df35cb0"
        },
        "date": 1780696650305,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 9,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b7d9acf849ef9791776ad100da386ac67b8a8a60",
          "message": "[anneal][v2] Add and integrate nix-built exocrate (#3383)\n\n- Add nix derivations for exocrate\n- Add `setup` sub-command to locate-or-install exocrate\n- Add integration test for \"developer mode\" `setup` that presumes local\n  exocrate archive\n- Add github workflows to:\n  - Warm nix cache\n  - Locally link exocrate archive from nix, then run all tests\n\ngherrit-pr-id: Gwhroikc5idscowxamayknlke2uiddzv3",
          "timestamp": "2026-06-05T18:00:27-04:00",
          "tree_id": "ead44d2b940c9097c6db13604d193d3f48190e3e",
          "url": "https://github.com/google/zerocopy/commit/b7d9acf849ef9791776ad100da386ac67b8a8a60"
        },
        "date": 1780696920342,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 8,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "588d46cae38288eabdc18670ba68cdc353d1b420",
          "message": "[CI] Bump the all-actions group across 1 directory with 14 updates",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3439/commits/588d46cae38288eabdc18670ba68cdc353d1b420"
        },
        "date": 1780697189842,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Build Time",
            "value": 7,
            "unit": "seconds"
          }
        ]
      }
    ],
    "CI Durations": [
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bccab1f6c5b371ddbcfe2eaa2cd63ef14c30c970",
          "message": "[ci][anneal] Track more metrics in dashboard",
          "timestamp": "2026-04-16T01:58:18Z",
          "url": "https://github.com/google/zerocopy/pull/3279/commits/bccab1f6c5b371ddbcfe2eaa2cd63ef14c30c970"
        },
        "date": 1776307815424,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 586,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "962a5a3a82822f05b6201d475e737a1615f28f3e",
          "message": "[ci][anneal] Track more metrics in dashboard (#3279)\n\ngherrit-pr-id: Gx7nzhourvbqnu7rpvavtjhunxbi4xsbn",
          "timestamp": "2026-04-16T05:27:28-04:00",
          "tree_id": "0570063aab2555920ed432be9f4d5b64b05a7dc7",
          "url": "https://github.com/google/zerocopy/commit/962a5a3a82822f05b6201d475e737a1615f28f3e"
        },
        "date": 1776332542409,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 613,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "af4f6c55393e631f101312618a205613e27f1a21",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T09:27:34Z",
          "url": "https://github.com/google/zerocopy/pull/3280/commits/af4f6c55393e631f101312618a205613e27f1a21"
        },
        "date": 1776343229865,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 75,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 582,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4ae7abd41d63c34fe97977ca584b3fdbf737ae45",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T09:27:34Z",
          "url": "https://github.com/google/zerocopy/pull/3281/commits/4ae7abd41d63c34fe97977ca584b3fdbf737ae45"
        },
        "date": 1776345181782,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 73,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1183,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4eec77e0a32ad6648b8ab7fe96cbc983bb75ecaf",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow",
          "timestamp": "2026-04-16T12:55:23Z",
          "url": "https://github.com/google/zerocopy/pull/3281/commits/4eec77e0a32ad6648b8ab7fe96cbc983bb75ecaf"
        },
        "date": 1776349716674,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 74,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 582,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "15639839eafdc9f22448b1e2d6c30ff45f80f080",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow (#3281)\n\nTo automate the creation of precompiled artifacts for the Anneal\ntoolchain, we add a build script and integrate it into the release\nworkflow. This will allow us to simplify the `setup` command to simply\ndownload these pre-built artifacts from a single location, avoid needing\nto build from source on the user's machine, and download fewer artifacts\n(in particular, stripping out Mathlib modules which are unused by\nAnneal). This is especially important for development *on* Anneal and\nfor CI, which run the `setup` command frequently.\n\ngherrit-pr-id: Gigvceuv7utvaq4hymnx3dl22qewo6vuz",
          "timestamp": "2026-04-16T14:28:47Z",
          "url": "https://github.com/google/zerocopy/commit/15639839eafdc9f22448b1e2d6c30ff45f80f080"
        },
        "date": 1776350809248,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 777,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "15639839eafdc9f22448b1e2d6c30ff45f80f080",
          "message": "[ci][anneal] Add precompiled artifact build script and workflow (#3281)\n\nTo automate the creation of precompiled artifacts for the Anneal\ntoolchain, we add a build script and integrate it into the release\nworkflow. This will allow us to simplify the `setup` command to simply\ndownload these pre-built artifacts from a single location, avoid needing\nto build from source on the user's machine, and download fewer artifacts\n(in particular, stripping out Mathlib modules which are unused by\nAnneal). This is especially important for development *on* Anneal and\nfor CI, which run the `setup` command frequently.\n\ngherrit-pr-id: Gigvceuv7utvaq4hymnx3dl22qewo6vuz",
          "timestamp": "2026-04-16T14:28:47Z",
          "tree_id": "b585065db60a134b371f49b13b9b75c1406b6d8d",
          "url": "https://github.com/google/zerocopy/commit/15639839eafdc9f22448b1e2d6c30ff45f80f080"
        },
        "date": 1776351737339,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 101,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 585,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4772174ed32ccbec723fecd5a4cd8ceebcd18e6d",
          "message": "[anneal] Release 0.1.0-alpha.18",
          "timestamp": "2026-04-16T14:47:33Z",
          "url": "https://github.com/google/zerocopy/pull/3282/commits/4772174ed32ccbec723fecd5a4cd8ceebcd18e6d"
        },
        "date": 1776353781505,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 71,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 804,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be",
          "message": "[anneal] Release 0.1.0-alpha.18 (#3282)\n\ngherrit-pr-id: Gkbtn5ebnp72mu2i4uwnpr35uwig5qgwq",
          "timestamp": "2026-04-16T15:36:32Z",
          "url": "https://github.com/google/zerocopy/commit/0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be"
        },
        "date": 1776355221691,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 64,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be",
          "message": "[anneal] Release 0.1.0-alpha.18 (#3282)\n\ngherrit-pr-id: Gkbtn5ebnp72mu2i4uwnpr35uwig5qgwq",
          "timestamp": "2026-04-16T15:36:32Z",
          "tree_id": "f541fb5afc67bec6cf778ed136875845b1c6d3d0",
          "url": "https://github.com/google/zerocopy/commit/0b1feb6aca6fd24e2a3cfa14bea7cc4cef0981be"
        },
        "date": 1776356707392,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 71,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "731729da7f955e3b81ebdfbc0ac03770fc6d2bf2",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job",
          "timestamp": "2026-04-16T16:01:32Z",
          "url": "https://github.com/google/zerocopy/pull/3283/commits/731729da7f955e3b81ebdfbc0ac03770fc6d2bf2"
        },
        "date": 1776364444000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 576,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "748177693d1907006da102d49fd71071504b10ca",
          "message": "[ci][anneal] Grant write permissions to publish-artifacts job (#3283)\n\ngherrit-pr-id: Gcqmoot6ezcmsbvzyvus2klwwinl46j37",
          "timestamp": "2026-04-16T11:39:48-07:00",
          "tree_id": "f397797cfc16d3c01e639fdb3a59128b75858959",
          "url": "https://github.com/google/zerocopy/commit/748177693d1907006da102d49fd71071504b10ca"
        },
        "date": 1776366128232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 69,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1176,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "867cd3a9a52ce81c4083c2a68299e33560e7a2c2",
          "message": "[ci][anneal] Add `workflow_dispatch` Action to release new version",
          "timestamp": "2026-04-16T18:39:54Z",
          "url": "https://github.com/google/zerocopy/pull/3284/commits/867cd3a9a52ce81c4083c2a68299e33560e7a2c2"
        },
        "date": 1776368194348,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 73,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 560,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b943232a98fa7c9994151a765d52b1989a982048",
          "message": "[ci][anneal] Add `workflow_dispatch` Action to release new version (#3284)\n\nRelease 0.1.0-alpha.19.\n\ngherrit-pr-id: G3sy75s2atk44kjhhoymwugs6wvpbfn4t",
          "timestamp": "2026-04-16T15:19:24-04:00",
          "tree_id": "c9f611ffd299eb3e0e9dea4702f3b30b5189fedb",
          "url": "https://github.com/google/zerocopy/commit/b943232a98fa7c9994151a765d52b1989a982048"
        },
        "date": 1776368607407,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 71,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 568,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c5b13a1ef79cc2488b8c15e414bd516632c0e351",
          "message": "[ci][anneal] Overhaul release process to support manual trigger and PR generation",
          "timestamp": "2026-04-17T02:13:33Z",
          "url": "https://github.com/google/zerocopy/pull/3285/commits/c5b13a1ef79cc2488b8c15e414bd516632c0e351"
        },
        "date": 1776416283253,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 577,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "650bf82c23492562c55a5ad5083e4a464fd5292d",
          "message": "[ci][anneal] Add manual trigger to publish precompiled artifacts",
          "timestamp": "2026-04-18T11:58:41Z",
          "url": "https://github.com/google/zerocopy/pull/3286/commits/650bf82c23492562c55a5ad5083e4a464fd5292d"
        },
        "date": 1776514727568,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 565,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d",
          "message": "[ci][anneal] Make concurrency group dynamic by branch/PR (#3287)\n\ngherrit-pr-id: Gofynwkutejony366jjuzz2odt4a56v2g",
          "timestamp": "2026-04-18T08:25:45-04:00",
          "tree_id": "7c11975b9cc8f34223d23b1c0a55a4460f99c5ae",
          "url": "https://github.com/google/zerocopy/commit/b79927b84d7e2e7ea4b4edb7b8dad8fbdcfa882d"
        },
        "date": 1776515953121,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 569,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0cf19a0dab9a54ab95a4cc163cb76b245fc684a5",
          "message": "[ci][anneal] Make concurrency group dynamic by branch/PR",
          "timestamp": "2026-04-18T12:16:17Z",
          "url": "https://github.com/google/zerocopy/pull/3287/commits/0cf19a0dab9a54ab95a4cc163cb76b245fc684a5"
        },
        "date": 1776516096714,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 863,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2e69086d4e8951404a0ff12b31da02ae4950f589",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error (#3288)\n\ngherrit-pr-id: Gtfo4rh2ird3aqm57btkd3l7zpsknc7y7",
          "timestamp": "2026-04-18T08:53:08-04:00",
          "tree_id": "6a3c4dbb13fa3fb4e2edbacc36b7a98143e5342c",
          "url": "https://github.com/google/zerocopy/commit/2e69086d4e8951404a0ff12b31da02ae4950f589"
        },
        "date": 1776517621782,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 582,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "23ff5079038cc931d8c3c1e65142e3fcb7225ec4",
          "message": "[ci][anneal] Use draft release pattern to avoid immutable release error",
          "timestamp": "2026-04-18T12:25:49Z",
          "url": "https://github.com/google/zerocopy/pull/3288/commits/23ff5079038cc931d8c3c1e65142e3fcb7225ec4"
        },
        "date": 1776517643930,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 70,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 567,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3638097edac2d1c9a5416788fcc427b739573e3",
          "message": "[ci][anneal] Use unique tags for manual artifact releases",
          "timestamp": "2026-04-18T12:53:13Z",
          "url": "https://github.com/google/zerocopy/pull/3289/commits/a3638097edac2d1c9a5416788fcc427b739573e3"
        },
        "date": 1776521017444,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 580,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec",
          "message": "[ci][anneal] Use unique tags for manual artifact releases (#3289)\n\ngherrit-pr-id: Gqrfvtkdyjezdwwai5d37vq5omydsrajc",
          "timestamp": "2026-04-18T09:51:02-04:00",
          "tree_id": "457b1ff2bfdd5f79fd50c5e190a8047b24ace7ee",
          "url": "https://github.com/google/zerocopy/commit/f83d13e3ee1e5cba9e8cc8bf10cfdc321b43c4ec"
        },
        "date": 1776521693497,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1185,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a70cac3cdaaff55316ffc9d06ac81ec304fd6bca",
          "message": "[ci][anneal] When publishing, prune Mathlib rather than removing it",
          "timestamp": "2026-04-18T13:51:08Z",
          "url": "https://github.com/google/zerocopy/pull/3290/commits/a70cac3cdaaff55316ffc9d06ac81ec304fd6bca"
        },
        "date": 1776526241669,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 79,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 579,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "00c910938978083a5405faed719ca02dcec730ad",
          "message": "[ci][anneal] When publishing, prune Mathlib rather than removing it (#3290)\n\ngherrit-pr-id: Gob4ak2l443wyguc6vd6uej7wndlqzhis",
          "timestamp": "2026-04-18T11:18:01-04:00",
          "tree_id": "f83185dc52b9877770089fc9e13f3aba0ca5dab7",
          "url": "https://github.com/google/zerocopy/commit/00c910938978083a5405faed719ca02dcec730ad"
        },
        "date": 1776526341480,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 108,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 571,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d38da7f292ab8f6f07773b1415448512c4419df2",
          "message": "[ci][anneal] Fix sysroot layout and exclude tests in builder script",
          "timestamp": "2026-04-18T15:18:08Z",
          "url": "https://github.com/google/zerocopy/pull/3291/commits/d38da7f292ab8f6f07773b1415448512c4419df2"
        },
        "date": 1776536787777,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 578,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b04142396963357c0bf3cf3d9e42e21070e38bfb",
          "message": "[ci][anneal] Fix sysroot layout and exclude tests in builder script (#3291)\n\ngherrit-pr-id: Gxhjefmzsst6q46o4l36bblw2nfrkwncy",
          "timestamp": "2026-04-18T14:15:01-04:00",
          "tree_id": "aa056420098859d5eb3a1185b40c9c371163e624",
          "url": "https://github.com/google/zerocopy/commit/b04142396963357c0bf3cf3d9e42e21070e38bfb"
        },
        "date": 1776536829353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 580,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "56518f056f4547b74e710f0fc9bb3e5257fd3994",
          "message": "[ci][anneal] In release, don't build tests; fix location of charon artifacts",
          "timestamp": "2026-04-18T18:15:06Z",
          "url": "https://github.com/google/zerocopy/pull/3293/commits/56518f056f4547b74e710f0fc9bb3e5257fd3994"
        },
        "date": 1776537677965,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 572,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fbdeab52de993f2bad6b650acd6aa8353d9edc89",
          "message": "[ci][anneal] In release, don't build tests; fix location of charon artifacts (#3293)\n\ngherrit-pr-id: Gblquwd2ikf5wze73xm7jfvth2rkkodn4",
          "timestamp": "2026-04-18T14:29:47-04:00",
          "tree_id": "58dd5ab95050f64eb5daeb42cd0f16b5db09d1e4",
          "url": "https://github.com/google/zerocopy/commit/fbdeab52de993f2bad6b650acd6aa8353d9edc89"
        },
        "date": 1776538402221,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 70,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1179,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8f72d85e3d0ba9a84cfc02d7ad3e3c895bc5e33f",
          "message": "[ci][anneal] Remove tests before building Lean library in release",
          "timestamp": "2026-04-18T18:29:51Z",
          "url": "https://github.com/google/zerocopy/pull/3294/commits/8f72d85e3d0ba9a84cfc02d7ad3e3c895bc5e33f"
        },
        "date": 1776546110260,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 66,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 586,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "234b7e0927728428e836aa455a1960bca7cd52c3",
          "message": "[ci][anneal] Remove tests before building Lean library in release (#3294)\n\ngherrit-pr-id: Gzcu4ycvlg2exazk6idhxol3x7mrndvgg",
          "timestamp": "2026-04-18T16:48:59-04:00",
          "tree_id": "4e11b4b4883ef6eb56a4c282538d0d5c9ce4d421",
          "url": "https://github.com/google/zerocopy/commit/234b7e0927728428e836aa455a1960bca7cd52c3"
        },
        "date": 1776546783315,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 72,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1191,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c97dbc6586c7c62decf3263c180e089f1c0f2771",
          "message": "[ci][anneal] Add workflow_dispatch argument for zstd compression level (#3296)\n\ngherrit-pr-id: Gqzpjc5efiwdcr4aqpzvz5nft7wfg43yo",
          "timestamp": "2026-04-19T04:52:09-04:00",
          "tree_id": "cb8d60712d6a66ca7c073d3f562146adac18c677",
          "url": "https://github.com/google/zerocopy/commit/c97dbc6586c7c62decf3263c180e089f1c0f2771"
        },
        "date": 1776589549758,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 570,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d96ae3425fbffb13a9bb252fadb57ecbf119fcdc",
          "message": "[ci][anneal] Unset CI variable to force precompilation in release",
          "timestamp": "2026-04-18T20:49:04Z",
          "url": "https://github.com/google/zerocopy/pull/3295/commits/d96ae3425fbffb13a9bb252fadb57ecbf119fcdc"
        },
        "date": 1776589612066,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 96,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1187,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9c57c85e7a39f4029fbe3a17f501af1cf5ec590a",
          "message": "[ci][anneal] Add workflow_dispatch argument for zstd compression level",
          "timestamp": "2026-04-19T08:43:21Z",
          "url": "https://github.com/google/zerocopy/pull/3296/commits/9c57c85e7a39f4029fbe3a17f501af1cf5ec590a"
        },
        "date": 1776590019400,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 68,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1186,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6aadac41296d8c218eb786d578657ed7ba10b14a",
          "message": "[anneal] Make logo stroke width thicker",
          "timestamp": "2026-04-20T01:38:32Z",
          "url": "https://github.com/google/zerocopy/pull/3300/commits/6aadac41296d8c218eb786d578657ed7ba10b14a"
        },
        "date": 1776674423915,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "3a99d7582663d8082df5b23ed4fd793b4e124211",
          "message": "[anneal] Make logo stroke width thicker (#3300)\n\ngherrit-pr-id: G6f3ij3lhnfnk4nvvj2ogaihrcweoqglb",
          "timestamp": "2026-04-20T08:40:34Z",
          "url": "https://github.com/google/zerocopy/commit/3a99d7582663d8082df5b23ed4fd793b4e124211"
        },
        "date": 1776675490227,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 67,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 787,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "3a99d7582663d8082df5b23ed4fd793b4e124211",
          "message": "[anneal] Make logo stroke width thicker (#3300)\n\ngherrit-pr-id: G6f3ij3lhnfnk4nvvj2ogaihrcweoqglb",
          "timestamp": "2026-04-20T08:40:34Z",
          "tree_id": "aa347751babb591182f2408e231a3bd5157aa8ac",
          "url": "https://github.com/google/zerocopy/commit/3a99d7582663d8082df5b23ed4fd793b4e124211"
        },
        "date": 1776676344822,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 71,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 581,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "46a430c37c828efce073211d3c64c0000e84f5ef",
          "message": "[CI] Bump the all-actions group with 8 updates",
          "timestamp": "2026-04-20T08:58:54Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/46a430c37c828efce073211d3c64c0000e84f5ef"
        },
        "date": 1776683727469,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 72,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 575,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "69e77a55f1b80f051b9dd9555363d2e074c48d3a",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep",
          "timestamp": "2026-04-20T13:24:00Z",
          "url": "https://github.com/google/zerocopy/pull/3304/commits/69e77a55f1b80f051b9dd9555363d2e074c48d3a"
        },
        "date": 1776728691804,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 454,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "d410c162d51977635ca5afac67d99a3b10327a94",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep (#3304)\n\n- Store build artifacts in a user-global Lean content-addressed artifact\n  cache, populating it during `setup`.\n- Specify the dependency on the Aeneas Lean library as follows:\n  - During `setup`, initialize the Aeneas Lean library as a git repo\n  - During `generate`/`verify`, specify the dependency as a git\n    dependency on a local filesystem path\n\nPrior to this change, we specified the dependency as a non-git\nfilesystem dep, which had the effect of causing Lean to think it could\nmutate the user-global directory, causing races when multiple `anneal`\ncommands were run in parallel.\n\nRelease 0.1.0-alpha.20\n\ngherrit-pr-id: Gyo2pqvhru3x4cyrj6bhrnjtx7gamwkfr",
          "timestamp": "2026-04-20T23:47:08Z",
          "url": "https://github.com/google/zerocopy/commit/d410c162d51977635ca5afac67d99a3b10327a94"
        },
        "date": 1776730326066,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 117,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 454,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d410c162d51977635ca5afac67d99a3b10327a94",
          "message": "[anneal] Use Lean artifact cache; use local-filesystem git dep (#3304)\n\n- Store build artifacts in a user-global Lean content-addressed artifact\n  cache, populating it during `setup`.\n- Specify the dependency on the Aeneas Lean library as follows:\n  - During `setup`, initialize the Aeneas Lean library as a git repo\n  - During `generate`/`verify`, specify the dependency as a git\n    dependency on a local filesystem path\n\nPrior to this change, we specified the dependency as a non-git\nfilesystem dep, which had the effect of causing Lean to think it could\nmutate the user-global directory, causing races when multiple `anneal`\ncommands were run in parallel.\n\nRelease 0.1.0-alpha.20\n\ngherrit-pr-id: Gyo2pqvhru3x4cyrj6bhrnjtx7gamwkfr",
          "timestamp": "2026-04-20T23:47:08Z",
          "tree_id": "7e016397325b6d9523d680ba36126c476aaa7aa6",
          "url": "https://github.com/google/zerocopy/commit/d410c162d51977635ca5afac67d99a3b10327a94"
        },
        "date": 1776731870152,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 444,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a71a6d5cd7992d285245277601df2ecd6dbce471",
          "message": "[anneal] WIP: Burn integration cache to the ground",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/a71a6d5cd7992d285245277601df2ecd6dbce471"
        },
        "date": 1776758545853,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 80,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 797,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f98458e7eaf54ff34b69e417ee34e79036f06547",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup",
          "timestamp": "2026-04-21T07:30:20Z",
          "url": "https://github.com/google/zerocopy/pull/3305/commits/f98458e7eaf54ff34b69e417ee34e79036f06547"
        },
        "date": 1776767301864,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 100,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1321,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "11515dce44b88a626b31d1fea053754dcb7331ca",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup (#3305)\n\n- Remove obsolete worker pool and smart cache cloning from integration\n  tests\n- Configure tests to use the shared global Lean artifact cache via\n  `LAKE_CACHE_DIR`\n- Simplify `src/setup.rs` by assuming only fresh installations:\n  - Remove `verify_tools` and individual binary checksums for Aeneas\n  - Simplify toolchain directory hashing to use the Rust tag\n  - Make installation and Git initialization unconditional\n- Implement atomic installation in `setup` using a temporary directory\n  and rename\n- Remove setup-related tests which are less useful now, and will become\n  even less useful than that going forward as we simplify the setup\n  logic\n\nPrior to this change, the integration tests relied on a complex worker\npool and symlinking infrastructure to isolate tests and share build\nartifacts. This required large amounts of disk space (e.g., a specific\nrun with ~100 parallel worker threads and caches consumed ~100GB). In\nthis commit, removing the worker pool and cache cloning approach lets us\nsave significant disk space usage during integration test runs.\n\ngherrit-pr-id: G4c76oil24wlyjqav3c5s5woakn5rcxpm",
          "timestamp": "2026-04-21T10:28:40Z",
          "url": "https://github.com/google/zerocopy/commit/11515dce44b88a626b31d1fea053754dcb7331ca"
        },
        "date": 1776769498387,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 81,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1302,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "11515dce44b88a626b31d1fea053754dcb7331ca",
          "message": "[anneal] Cleanup test infrastructure and implement atomic setup (#3305)\n\n- Remove obsolete worker pool and smart cache cloning from integration\n  tests\n- Configure tests to use the shared global Lean artifact cache via\n  `LAKE_CACHE_DIR`\n- Simplify `src/setup.rs` by assuming only fresh installations:\n  - Remove `verify_tools` and individual binary checksums for Aeneas\n  - Simplify toolchain directory hashing to use the Rust tag\n  - Make installation and Git initialization unconditional\n- Implement atomic installation in `setup` using a temporary directory\n  and rename\n- Remove setup-related tests which are less useful now, and will become\n  even less useful than that going forward as we simplify the setup\n  logic\n\nPrior to this change, the integration tests relied on a complex worker\npool and symlinking infrastructure to isolate tests and share build\nartifacts. This required large amounts of disk space (e.g., a specific\nrun with ~100 parallel worker threads and caches consumed ~100GB). In\nthis commit, removing the worker pool and cache cloning approach lets us\nsave significant disk space usage during integration test runs.\n\ngherrit-pr-id: G4c76oil24wlyjqav3c5s5woakn5rcxpm",
          "timestamp": "2026-04-21T10:28:40Z",
          "tree_id": "833adf0febc61c567363031fad512ce313ed7401",
          "url": "https://github.com/google/zerocopy/commit/11515dce44b88a626b31d1fea053754dcb7331ca"
        },
        "date": 1776771660935,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 69,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1317,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c326102fba9d8cfff7f64cb55b763db3fc6388db",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/c326102fba9d8cfff7f64cb55b763db3fc6388db"
        },
        "date": 1776776765992,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 139,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 1198,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "37d1fef927ec84a9086312ad1bb9840c205b0d87",
          "message": "[anneal] In `setup`, recursively cache Lean sources",
          "timestamp": "2026-04-21T11:39:33Z",
          "url": "https://github.com/google/zerocopy/pull/3306/commits/37d1fef927ec84a9086312ad1bb9840c205b0d87"
        },
        "date": 1776806480484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 134,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 333,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "9329ada1b2801e305cd00db7c62b6987f8b7c80c",
          "message": "[anneal] In `setup`, recursively cache Lean sources (#3306)\n\nInitialize all transitive Lean library dependencies of the Aeneas Lean\nlibrary as local Git repositories, and rewrite dependencies to point to\nthese as filesystem-local Git remotes. During `verify`, `lake build`\nclones any source code it doesn't already have access to. This ensures\nthat this at least clones from the local filesystem instead of from the\ninternet.\n\ngherrit-pr-id: Ghmd3zurxjuy6q66eay4blnbt7sfg7wlz",
          "timestamp": "2026-04-21T21:21:56Z",
          "url": "https://github.com/google/zerocopy/commit/9329ada1b2801e305cd00db7c62b6987f8b7c80c"
        },
        "date": 1776808360871,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 132,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 442,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9329ada1b2801e305cd00db7c62b6987f8b7c80c",
          "message": "[anneal] In `setup`, recursively cache Lean sources (#3306)\n\nInitialize all transitive Lean library dependencies of the Aeneas Lean\nlibrary as local Git repositories, and rewrite dependencies to point to\nthese as filesystem-local Git remotes. During `verify`, `lake build`\nclones any source code it doesn't already have access to. This ensures\nthat this at least clones from the local filesystem instead of from the\ninternet.\n\ngherrit-pr-id: Ghmd3zurxjuy6q66eay4blnbt7sfg7wlz",
          "timestamp": "2026-04-21T21:21:56Z",
          "tree_id": "35fb101371c1e4ebb6fb1c0798abadb812c383ed",
          "url": "https://github.com/google/zerocopy/commit/9329ada1b2801e305cd00db7c62b6987f8b7c80c"
        },
        "date": 1776810028566,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 139,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 308,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fa91316f61deeda4fe2d77de7db494fc1f3103b5",
          "message": "Make Docker image tag and cache volume unique per worktree",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3322/commits/fa91316f61deeda4fe2d77de7db494fc1f3103b5"
        },
        "date": 1776856073693,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 126,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 388,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0497a2dd3a4bbf07b2f4540f788255404b151784",
          "message": "Add Total CI Duration benchmark to anneal workflow",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3323/commits/0497a2dd3a4bbf07b2f4540f788255404b151784"
        },
        "date": 1776856306061,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 186,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 329,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 547,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a27cb57734782db8f7ba9da14e3aa8fd6ea200f9",
          "message": "[ci][anneal] Track total CI duration in benchmark dashboard (#3323)",
          "timestamp": "2026-04-22T11:11:58Z",
          "url": "https://github.com/google/zerocopy/commit/a27cb57734782db8f7ba9da14e3aa8fd6ea200f9"
        },
        "date": 1776857036671,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 151,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 357,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 545,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2a269c55f4ee2fc3ee14ab1323cd3a63fe4817cf",
          "message": "Make Docker image tag and cache volume unique per worktree",
          "timestamp": "2026-04-21T21:53:26Z",
          "url": "https://github.com/google/zerocopy/pull/3322/commits/2a269c55f4ee2fc3ee14ab1323cd3a63fe4817cf"
        },
        "date": 1776857483266,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 125,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 364,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e1005b0f51361317d1f4883a6d3138c567301b22",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-04-22T11:24:42Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/e1005b0f51361317d1f4883a6d3138c567301b22"
        },
        "date": 1776857820495,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 117,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 361,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 508,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a27cb57734782db8f7ba9da14e3aa8fd6ea200f9",
          "message": "[ci][anneal] Track total CI duration in benchmark dashboard (#3323)",
          "timestamp": "2026-04-22T11:11:58Z",
          "tree_id": "22f1c20b8a2fe8fc6e2010a70b7e0c0b573332b6",
          "url": "https://github.com/google/zerocopy/commit/a27cb57734782db8f7ba9da14e3aa8fd6ea200f9"
        },
        "date": 1776857849484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 154,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 435,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 622,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a51752bdff4d521681a8c2d5d97396015114d6d8",
          "message": "[anneal] Isolate docker images, not just volumes (#3322)",
          "timestamp": "2026-04-22T11:31:34Z",
          "url": "https://github.com/google/zerocopy/commit/a51752bdff4d521681a8c2d5d97396015114d6d8"
        },
        "date": 1776858324891,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 113,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 522,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 667,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a51752bdff4d521681a8c2d5d97396015114d6d8",
          "message": "[anneal] Isolate docker images, not just volumes (#3322)",
          "timestamp": "2026-04-22T11:31:34Z",
          "tree_id": "733e7fc815782bd3e1b3ba6ad4af32aa90a0566f",
          "url": "https://github.com/google/zerocopy/commit/a51752bdff4d521681a8c2d5d97396015114d6d8"
        },
        "date": 1776859038514,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 148,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 351,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 533,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "060fa19351a96e39a97ab4c17d017855834d3a98",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-04-27T05:44:52Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/060fa19351a96e39a97ab4c17d017855834d3a98"
        },
        "date": 1777289075821,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 122,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 349,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 506,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4d84f92ef43313e54eac77228cedd08889058ef8",
          "message": "[anneal][README] Document TCB shrinking",
          "timestamp": "2026-04-27T05:44:52Z",
          "url": "https://github.com/google/zerocopy/pull/3326/commits/4d84f92ef43313e54eac77228cedd08889058ef8"
        },
        "date": 1777386890125,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 123,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 439,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 592,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "f896a6890a1e6feb01d3c26364bf674f0573321e",
          "message": "[anneal][README] Document TCB shrinking (#3326)\n\ngherrit-pr-id: Gy4y7cstkui5s6c7jletzjbu37xtjglxm",
          "timestamp": "2026-04-28T18:10:09Z",
          "url": "https://github.com/google/zerocopy/commit/f896a6890a1e6feb01d3c26364bf674f0573321e"
        },
        "date": 1777400440256,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 119,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 320,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 474,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f896a6890a1e6feb01d3c26364bf674f0573321e",
          "message": "[anneal][README] Document TCB shrinking (#3326)\n\ngherrit-pr-id: Gy4y7cstkui5s6c7jletzjbu37xtjglxm",
          "timestamp": "2026-04-28T18:10:09Z",
          "tree_id": "04fd33df84b5b512246673abd226b3bf491693a7",
          "url": "https://github.com/google/zerocopy/commit/f896a6890a1e6feb01d3c26364bf674f0573321e"
        },
        "date": 1777402117876,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 168,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 329,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 532,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a0600ed391d85fa2cd1b0d62b233277712ef7731",
          "message": "[anneal][README] Tighten wording",
          "timestamp": "2026-04-28T18:37:26Z",
          "url": "https://github.com/google/zerocopy/pull/3328/commits/a0600ed391d85fa2cd1b0d62b233277712ef7731"
        },
        "date": 1777418245455,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 149,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 330,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 515,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "bc525228994b0eafbc600981e1955f2f442c5e0b",
          "message": "[anneal][README] Tighten wording (#3328)\n\nRelease 0.1.0-alpha.21.\n\ngherrit-pr-id: Ggwzrriapr76e6dx74cv4skvdp7ikd37h",
          "timestamp": "2026-04-28T23:20:52Z",
          "url": "https://github.com/google/zerocopy/commit/bc525228994b0eafbc600981e1955f2f442c5e0b"
        },
        "date": 1777420106535,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 137,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 329,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 497,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc525228994b0eafbc600981e1955f2f442c5e0b",
          "message": "[anneal][README] Tighten wording (#3328)\n\nRelease 0.1.0-alpha.21.\n\ngherrit-pr-id: Ggwzrriapr76e6dx74cv4skvdp7ikd37h",
          "timestamp": "2026-04-28T23:20:52Z",
          "tree_id": "ed7bfb5b08e51dfc389d3beadf64648ab5bea3b3",
          "url": "https://github.com/google/zerocopy/commit/bc525228994b0eafbc600981e1955f2f442c5e0b"
        },
        "date": 1777421841719,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 142,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 306,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 481,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0fc280083ba437f6717e994c27169f36ff64b669",
          "message": "[ci] Run Anneal jobs on free-tier runners",
          "timestamp": "2026-04-29T03:07:30Z",
          "url": "https://github.com/google/zerocopy/pull/3330/commits/0fc280083ba437f6717e994c27169f36ff64b669"
        },
        "date": 1777655236361,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 120,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2086,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2291,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "c67c8ecc912d7f45e68b5274de789a15b42cf4aa",
          "message": "[ci] Run Anneal jobs on free-tier runners (#3330)\n\ngherrit-pr-id: Gl375z4s3fozt4u74gde7bzsp3ey4fi3n",
          "timestamp": "2026-05-01T17:07:29Z",
          "url": "https://github.com/google/zerocopy/commit/c67c8ecc912d7f45e68b5274de789a15b42cf4aa"
        },
        "date": 1777657659255,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 131,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2123,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2337,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c67c8ecc912d7f45e68b5274de789a15b42cf4aa",
          "message": "[ci] Run Anneal jobs on free-tier runners (#3330)\n\ngherrit-pr-id: Gl375z4s3fozt4u74gde7bzsp3ey4fi3n",
          "timestamp": "2026-05-01T17:07:29Z",
          "tree_id": "a24079fd4d2bb340570f054bd0bf6c414eba80f0",
          "url": "https://github.com/google/zerocopy/commit/c67c8ecc912d7f45e68b5274de789a15b42cf4aa"
        },
        "date": 1777660125425,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 150,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2118,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2348,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7fcad56fadd04c5ebfbde1f837003851fbea63c4",
          "message": "[CI] Bump the all-actions group across 1 directory with 8 updates",
          "timestamp": "2026-05-01T17:48:36Z",
          "url": "https://github.com/google/zerocopy/pull/3301/commits/7fcad56fadd04c5ebfbde1f837003851fbea63c4"
        },
        "date": 1777660194661,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 129,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2056,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2268,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "44c9b1430f14d621ee57516893e59b216911ebaf",
          "message": "[anneal] Replace Docker with Nix",
          "timestamp": "2026-05-04T18:39:21Z",
          "url": "https://github.com/google/zerocopy/pull/3336/commits/44c9b1430f14d621ee57516893e59b216911ebaf"
        },
        "date": 1777942053177,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 129,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2113,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2320,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "54bd85c25824a1dba5cc245d9358ffbf2b63e91f",
          "message": "[anneal] Replace annotation syntax with verbatim Lean",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3321/commits/54bd85c25824a1dba5cc245d9358ffbf2b63e91f"
        },
        "date": 1778018345291,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 157,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 2319,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 2564,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d38657fc5f3b41967cd5478f4ba125ea5a1ddad0",
          "message": "Implement optimized symlink-copy package materializer and static commit hash bypass to achieve 40x speedup and 100% concurrent safety",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3340/commits/d38657fc5f3b41967cd5478f4ba125ea5a1ddad0"
        },
        "date": 1778033666692,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 160,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 872,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1130,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6ee85014a75f4ecbde8091c0fff0cbb7c668c931",
          "message": "Optimize run_lake by copying precompiled config folders, renaming Aeneas config, and dynamically patching trace indices to achieve a ~19% run_lake speedup",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3341/commits/6ee85014a75f4ecbde8091c0fff0cbb7c668c931"
        },
        "date": 1778035928633,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 503,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 678,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8ec4371ce2524cb3f86c1ca1c1b6c5ae39a5abb3",
          "message": "Polish code comments across setup.rs and aeneas.rs to strictly conform to comment-guidelines (80-column wrapping, objective tone, self-contained descriptions)",
          "timestamp": "2026-05-05T12:39:38Z",
          "url": "https://github.com/google/zerocopy/pull/3342/commits/8ec4371ce2524cb3f86c1ca1c1b6c5ae39a5abb3"
        },
        "date": 1778035967681,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 93,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 555,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 731,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "344fa4d987e5c17cd669377699404d38ebadbc4b",
          "message": "[anneal] WIP",
          "timestamp": "2026-05-06T05:47:52Z",
          "url": "https://github.com/google/zerocopy/pull/3344/commits/344fa4d987e5c17cd669377699404d38ebadbc4b"
        },
        "date": 1778091758242,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 717,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2f1d4dfe3fb6309820f61fc2f57cae83e152d2dc",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal`",
          "timestamp": "2026-05-06T05:47:52Z",
          "url": "https://github.com/google/zerocopy/pull/3344/commits/2f1d4dfe3fb6309820f61fc2f57cae83e152d2dc"
        },
        "date": 1778096668408,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 85,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 475,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 641,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "be6f199fdbe4e568ac63289e2bdbd4a5f783d444",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal` (#3344)\n\nPrior to this change, Lake verification relied on recursively copying\nthe entire global precompiled toolchain package directory (~5,000\n`.olean` files, ~5GB) into a build directory. This was obviously slow\nand caused massive disk bloat.\n\nIn this commit, we instead:\n- Copy only those files which Lake will attempt to write, and symlink\n  all other files. In practice, this means that only the smallest files\n  are actually copied. (Note: Copying is necessary *at all* because Lake\n  will write to some files in the directories of a package's\n  *dependencies* if those dependencies are filesystem-local. Without\n  copying, this would result in concurrent writes to the user-global\n  `~/.anneal/toolchain` directory.)\n- Mark the `~/.anneal/toolchain/<toolchain>` directory as recursively\n  read-only to ensure that any attempted writes fail loudly.\n\nRelease 0.1.0-alpha.22.\n\ngherrit-pr-id: Gks63dnqyjzxt6s6sgowdaz63rogw5kz3",
          "timestamp": "2026-05-06T19:44:41Z",
          "url": "https://github.com/google/zerocopy/commit/be6f199fdbe4e568ac63289e2bdbd4a5f783d444"
        },
        "date": 1778098554560,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 735,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "be6f199fdbe4e568ac63289e2bdbd4a5f783d444",
          "message": "[anneal] Don't copy Lean build artifacts from `~/.anneal` (#3344)\n\nPrior to this change, Lake verification relied on recursively copying\nthe entire global precompiled toolchain package directory (~5,000\n`.olean` files, ~5GB) into a build directory. This was obviously slow\nand caused massive disk bloat.\n\nIn this commit, we instead:\n- Copy only those files which Lake will attempt to write, and symlink\n  all other files. In practice, this means that only the smallest files\n  are actually copied. (Note: Copying is necessary *at all* because Lake\n  will write to some files in the directories of a package's\n  *dependencies* if those dependencies are filesystem-local. Without\n  copying, this would result in concurrent writes to the user-global\n  `~/.anneal/toolchain` directory.)\n- Mark the `~/.anneal/toolchain/<toolchain>` directory as recursively\n  read-only to ensure that any attempted writes fail loudly.\n\nRelease 0.1.0-alpha.22.\n\ngherrit-pr-id: Gks63dnqyjzxt6s6sgowdaz63rogw5kz3",
          "timestamp": "2026-05-06T19:44:41Z",
          "tree_id": "73f8ba779cf997b8e10d15cfb9573283a6ee505b",
          "url": "https://github.com/google/zerocopy/commit/be6f199fdbe4e568ac63289e2bdbd4a5f783d444"
        },
        "date": 1778100474991,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 577,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 750,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d43dde17f9bd6d1273569ce58f30a64809a21ad7",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-09T12:52:12Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/d43dde17f9bd6d1273569ce58f30a64809a21ad7"
        },
        "date": 1778483611089,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 719,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ef1a886451b2871c2fe6ffd0eeb10a4108d4d580",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-09T12:52:12Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/ef1a886451b2871c2fe6ffd0eeb10a4108d4d580"
        },
        "date": 1778488237608,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 534,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 699,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5eaabf9abe92019696a261f302fa84c6272e6a6d",
          "message": "[CI] Bump the all-actions group across 1 directory with 10 updates",
          "timestamp": "2026-05-11T13:28:45Z",
          "url": "https://github.com/google/zerocopy/pull/3349/commits/5eaabf9abe92019696a261f302fa84c6272e6a6d"
        },
        "date": 1778509507347,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 578,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 753,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "92fa010ec3ef75ca0093b765b92172e2663bfedd",
          "message": "[anneal] README: Explain philosophy wrt typing",
          "timestamp": "2026-05-11T13:28:45Z",
          "url": "https://github.com/google/zerocopy/pull/3351/commits/92fa010ec3ef75ca0093b765b92172e2663bfedd"
        },
        "date": 1778547080453,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 522,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 689,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "31c878bf0e4301fba3b74d88d2927ea7a82ef539",
          "message": "[wip] Introduce `InitializeIntoBytes`",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3347/commits/31c878bf0e4301fba3b74d88d2927ea7a82ef539"
        },
        "date": 1778599328379,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 587,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 763,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c51884e94262f3f9d5dead155f0ef806d424c989",
          "message": "Add to anneal-setup-v2: non-UNIX support; doc-comments; tests",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3353/commits/c51884e94262f3f9d5dead155f0ef806d424c989"
        },
        "date": 1778612883449,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 86,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 456,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 624,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7127a9536f05a3f486ef39f21f3dcfaf5fdd2d14",
          "message": "WIP: Start building thin setup that presumes carefully prepared dependencies archive",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3352/commits/7127a9536f05a3f486ef39f21f3dcfaf5fdd2d14"
        },
        "date": 1778612978458,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 550,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 720,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5592b2be1f587b882462913c632dfa9ee6c01ab9",
          "message": "anneal-setup-v2: simplify extractor into single-threaded implementation",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3357/commits/5592b2be1f587b882462913c632dfa9ee6c01ab9"
        },
        "date": 1778613753226,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 531,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 700,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "03f497ea94807c49fc43043f0d46a05922789746",
          "message": "Modify anneal/Cargo to admit v2/setup workspace",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3354/commits/03f497ea94807c49fc43043f0d46a05922789746"
        },
        "date": 1778613841761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 584,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 758,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "421342304f51114aaddd133c638ba199957a3dcc",
          "message": "anneal-setup-v2: switch from shelling out to tar to managing archives with libraries",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3356/commits/421342304f51114aaddd133c638ba199957a3dcc"
        },
        "date": 1778613865900,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 569,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 739,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8811a40e19c2ab108c4c7b74134b4b5db108b30",
          "message": "anneal-setup-v2: Copy nix flake from #3336",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3358/commits/b8811a40e19c2ab108c4c7b74134b4b5db108b30"
        },
        "date": 1778613881600,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 545,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 718,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c862a246e91d85f4bca9202b02994ac576825c76",
          "message": "anneal-setup-v2: Update nix flake to package Lean toolchain",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3359/commits/c862a246e91d85f4bca9202b02994ac576825c76"
        },
        "date": 1778614170232,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 162,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 729,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1000,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "72b79672a65fb514a33a8ba68591dee09dcab4e3",
          "message": "anneal-setup-v2: More robust bash scripts in nix flake",
          "timestamp": "2026-05-12T05:19:23Z",
          "url": "https://github.com/google/zerocopy/pull/3360/commits/72b79672a65fb514a33a8ba68591dee09dcab4e3"
        },
        "date": 1778625382695,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 538,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 704,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d64055e99e1826f7e0411789cadc6e2298c974d2",
          "message": "[anneal][v2] Introduce nix-based toolchain management",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3361/commits/d64055e99e1826f7e0411789cadc6e2298c974d2"
        },
        "date": 1778676412918,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 94,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 716,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8c6bd235d543b36ce71b9c65314dc7486ce0b890",
          "message": "[anneal][v2] Initial `setup` implementation",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3362/commits/8c6bd235d543b36ce71b9c65314dc7486ce0b890"
        },
        "date": 1778677433550,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 114,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 446,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 640,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f590be17467609aa773c9163b0f27c0f046a1600",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/f590be17467609aa773c9163b0f27c0f046a1600"
        },
        "date": 1778709526951,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 559,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 726,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "05d57bc60c4fd3ce1734574632a1bc97a459322d",
          "message": "Start cleaning up vibe-coded 'Rename v2..Introduce standalone' changes",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3371/commits/05d57bc60c4fd3ce1734574632a1bc97a459322d"
        },
        "date": 1778787333735,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 86,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 550,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 715,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "82b260af1624870a6cc8087c00506015fd94d4d8",
          "message": "Move from type params to &dyn T; start trying to work with toml_const",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3373/commits/82b260af1624870a6cc8087c00506015fd94d4d8"
        },
        "date": 1778787352046,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 550,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 717,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f89f0b43d3004c662f702b1f82fabf2306c13a9f",
          "message": "Introduce toml_const dependency; r/Setup/Install; bind url<->archive-format and checksum<->digest-algorithm",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3372/commits/f89f0b43d3004c662f702b1f82fabf2306c13a9f"
        },
        "date": 1778787509725,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 116,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 764,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1cb115367ed399840c08dfd4a75fa6b9016d15bf",
          "message": "[anneal][v2] (Buggy) atomic toolchain management",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3375/commits/1cb115367ed399840c08dfd4a75fa6b9016d15bf"
        },
        "date": 1778804235259,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 483,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 596,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b9bf484e83a8c2000c5eafd07d6561464caccbeb",
          "message": "[anneal][v2] Atomic toolchain management via directory locking",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/b9bf484e83a8c2000c5eafd07d6561464caccbeb"
        },
        "date": 1778806910399,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 155,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 677,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 871,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "36d8147c815e919835b7f4be5cfa349e694c2703",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/36d8147c815e919835b7f4be5cfa349e694c2703"
        },
        "date": 1778812468308,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 101,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 390,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 517,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb6caf382d0a49db0263724b90cee88b64ad7b11",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/cb6caf382d0a49db0263724b90cee88b64ad7b11"
        },
        "date": 1778850573913,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 98,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 491,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 621,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "af503ff97de621d3585b230395f548aedba66a6c",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/af503ff97de621d3585b230395f548aedba66a6c"
        },
        "date": 1778851419473,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 499,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 616,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1f95236b0081b736384eba75baac4fb51cc1000d",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1f95236b0081b736384eba75baac4fb51cc1000d"
        },
        "date": 1778861585395,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 101,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 500,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 629,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "639939fbd0688f0a9898788a54ebb6be3e24ab62",
          "message": "[anneal][v2] Initial commit",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/639939fbd0688f0a9898788a54ebb6be3e24ab62"
        },
        "date": 1778866787411,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 144,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 606,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 782,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1cb13961f8c8bb14c77d427b694851ebdc9d4b65",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1cb13961f8c8bb14c77d427b694851ebdc9d4b65"
        },
        "date": 1778871695173,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 110,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 533,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 723,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e26ffc16650d8948eae9e0616f800b0dc5661fd9",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3377/commits/e26ffc16650d8948eae9e0616f800b0dc5661fd9"
        },
        "date": 1778871898552,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 534,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 701,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "01bba6bc21a667df3fbbbaabca114b7158a8c546",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/01bba6bc21a667df3fbbbaabca114b7158a8c546"
        },
        "date": 1778885121379,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 527,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 695,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b2045d774da6dda9e85e195dfefd75d5c313a07d",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/b2045d774da6dda9e85e195dfefd75d5c313a07d"
        },
        "date": 1778886339331,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 546,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 716,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "19f13f31f97fddf47aada2426645b707d2a052e2",
          "message": "[anneal][v2][exocrate] Pass manifest/lockfile paths explicitly",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3378/commits/19f13f31f97fddf47aada2426645b707d2a052e2"
        },
        "date": 1778887110398,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 165,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 783,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1045,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "156018c368c62dc4625038dedcbd5fdc7c02a94b",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-13T06:01:31Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/156018c368c62dc4625038dedcbd5fdc7c02a94b"
        },
        "date": 1778887520546,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 134,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 612,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 839,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8afd4850b94fe690b7bdb3f3e2c717e19fb99ab",
          "message": "[anneal] README: Explain philosophy w.r.t. typing",
          "timestamp": "2026-05-18T16:47:14Z",
          "url": "https://github.com/google/zerocopy/pull/3351/commits/b8afd4850b94fe690b7bdb3f3e2c717e19fb99ab"
        },
        "date": 1779133888488,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 734,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a3ad195abf85896be6f07f11acb486ceb7d61900",
          "message": "[anneal] README: Explain philosophy w.r.t. typing (#3351)\n\nRelease 0.1.0-alpha.23.\n\ngherrit-pr-id: Gpeqma2krsi7flwaeyjlum23s7znxuhms",
          "timestamp": "2026-05-18T16:03:33-04:00",
          "tree_id": "42557b2a78eba0ec7aaa24b045a0f4e098ac18eb",
          "url": "https://github.com/google/zerocopy/commit/a3ad195abf85896be6f07f11acb486ceb7d61900"
        },
        "date": 1779136522997,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 583,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 757,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e58c6dc36be5cbabc15a88bdc61a1a18658c5f95",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-18T20:59:32Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/e58c6dc36be5cbabc15a88bdc61a1a18658c5f95"
        },
        "date": 1779146394333,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 99,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 561,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 744,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b8db11399c64069d2ab12130e3a8c540da81592a",
          "message": "[ci] Don't run on large runners",
          "timestamp": "2026-05-19T08:50:26Z",
          "url": "https://github.com/google/zerocopy/pull/3379/commits/b8db11399c64069d2ab12130e3a8c540da81592a"
        },
        "date": 1779186543496,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 158,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 763,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1019,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "d0764df9d9b668b8178340168da36f209c732821",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T10:29:24Z",
          "url": "https://github.com/google/zerocopy/commit/d0764df9d9b668b8178340168da36f209c732821"
        },
        "date": 1779187441504,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 116,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 545,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 747,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "db28e0ef51864bb5f817eb3e5929b5b01c3c8efa",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T12:05:21Z",
          "url": "https://github.com/google/zerocopy/commit/db28e0ef51864bb5f817eb3e5929b5b01c3c8efa"
        },
        "date": 1779193247029,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 123,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 752,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "837d76d830653021e6a6a5fc3cade5e911b831ad",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/837d76d830653021e6a6a5fc3cade5e911b831ad"
        },
        "date": 1779210992347,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 551,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 719,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e4463478772bf064fe0d401f60d41c31bf269d63",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/e4463478772bf064fe0d401f60d41c31bf269d63"
        },
        "date": 1779211937761,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 738,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d564da0e05ea1f07f7a34474f1d30fe7d8a25dfc",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T10:50:50Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/d564da0e05ea1f07f7a34474f1d30fe7d8a25dfc"
        },
        "date": 1779211952885,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 95,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 553,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 735,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4cf5c9545b171bba0b912b84a58a734ca12606e3",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T17:39:49Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/4cf5c9545b171bba0b912b84a58a734ca12606e3"
        },
        "date": 1779213372736,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 504,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 694,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "41bb90ed3ad4664afd5d98a04047782b9e720f44",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T17:39:49Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/41bb90ed3ad4664afd5d98a04047782b9e720f44"
        },
        "date": 1779213388264,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 721,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ba490b4d08980b4c7bf53888cb81cccc8dafce49",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:07:43Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/ba490b4d08980b4c7bf53888cb81cccc8dafce49"
        },
        "date": 1779224009640,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 158,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 657,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 908,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "40494d65dbddce23cfa56b509d95a947d2293845",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3384/commits/40494d65dbddce23cfa56b509d95a947d2293845"
        },
        "date": 1779226944257,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 557,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 732,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "40494d65dbddce23cfa56b509d95a947d2293845",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/40494d65dbddce23cfa56b509d95a947d2293845"
        },
        "date": 1779226997176,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 549,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 720,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34e3c2d72feeba99b4c2e640971fb641184ea3f0",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/34e3c2d72feeba99b4c2e640971fb641184ea3f0"
        },
        "date": 1779235034352,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 86,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 714,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34394dc744493d2b7cdda5bef1699f7fc8b7630b",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/34394dc744493d2b7cdda5bef1699f7fc8b7630b"
        },
        "date": 1779235037398,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 560,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 732,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f849827512305da338f044b1e195a2ef2fc3378a",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/f849827512305da338f044b1e195a2ef2fc3378a"
        },
        "date": 1779235068906,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 97,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 572,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 753,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ca9434eef2e08e0ab8638e5eb2e548ba4fad4df2",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/ca9434eef2e08e0ab8638e5eb2e548ba4fad4df2"
        },
        "date": 1779235074189,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 118,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 765,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "8772fc4b3c36778c5cdb4adc7eaa8825541b2418",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T23:46:42Z",
          "url": "https://github.com/google/zerocopy/commit/8772fc4b3c36778c5cdb4adc7eaa8825541b2418"
        },
        "date": 1779235174562,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 526,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 693,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d22541fa193b6594621ff12d4ea3fe8f124c2290",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/d22541fa193b6594621ff12d4ea3fe8f124c2290"
        },
        "date": 1779235991132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 541,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dbfad857fc9fdb7ce2a5900e60e4d46ca1b434a7",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/dbfad857fc9fdb7ce2a5900e60e4d46ca1b434a7"
        },
        "date": 1779236032059,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 550,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 721,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b45304bdbf11f5c2bebf555ce00743e8e4ef1a2c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/b45304bdbf11f5c2bebf555ce00743e8e4ef1a2c"
        },
        "date": 1779236198959,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 551,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 729,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "71b1c404f0c8566268b3aa95c389448b180a87ce",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/71b1c404f0c8566268b3aa95c389448b180a87ce"
        },
        "date": 1779236324795,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 162,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 747,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1007,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb85c7399f2f163e1cb574a5e40ee552c2588507",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/cb85c7399f2f163e1cb574a5e40ee552c2588507"
        },
        "date": 1779236914239,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 85,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 451,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 611,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "8772fc4b3c36778c5cdb4adc7eaa8825541b2418",
          "message": "[ci] Don't run on large runners (#3379)",
          "timestamp": "2026-05-19T23:46:42Z",
          "tree_id": "fe5018c83ed57d2fd917f95cfbc9e62e4d068c89",
          "url": "https://github.com/google/zerocopy/commit/8772fc4b3c36778c5cdb4adc7eaa8825541b2418"
        },
        "date": 1779237015007,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 99,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 546,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 728,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d060c9263e3bf09b141fb4b67873045540c333d4",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-19T20:28:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/d060c9263e3bf09b141fb4b67873045540c333d4"
        },
        "date": 1779237239416,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 111,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 559,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 759,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cf1754b9dd5ef754c073bfc2edea7f375e349610",
          "message": "[CI] Bump the all-actions group across 1 directory with 11 updates",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3385/commits/cf1754b9dd5ef754c073bfc2edea7f375e349610"
        },
        "date": 1779237262477,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 97,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 748,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "929a91bc0aa2fcf577dbe31b414c5c44e2248b8c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/929a91bc0aa2fcf577dbe31b414c5c44e2248b8c"
        },
        "date": 1779239035476,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 738,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bf31762bb99e34e91c1ae5b723038786163f9c46",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/bf31762bb99e34e91c1ae5b723038786163f9c46"
        },
        "date": 1779284897735,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 111,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 450,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 639,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f2d675b038e8aef08e084d884bf575e23dafaf31",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/f2d675b038e8aef08e084d884bf575e23dafaf31"
        },
        "date": 1779284990820,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 99,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 739,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5f697f9b8202c1801175ae302d06714b5c3e6edb",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/5f697f9b8202c1801175ae302d06714b5c3e6edb"
        },
        "date": 1779291803111,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 560,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 729,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ebd42456124ca861f32d62c5fccd1f12116c4418",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/ebd42456124ca861f32d62c5fccd1f12116c4418"
        },
        "date": 1779297802214,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 429,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 599,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6504e9b6f183a7a5342af41804ae6fa23afd6cac",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/6504e9b6f183a7a5342af41804ae6fa23afd6cac"
        },
        "date": 1779297968708,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 545,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 718,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "34120789d87efa88e9be36a2a82f1fb2dafbd4c5",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T00:17:26Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/34120789d87efa88e9be36a2a82f1fb2dafbd4c5"
        },
        "date": 1779298507862,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 85,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 491,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 664,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "acd7129840a5974ac91b2ad745e2282ead9ff051",
          "message": "Only use `layout_for_ptr` feature for zerocopy tests",
          "timestamp": "2026-05-20T18:49:44Z",
          "url": "https://github.com/google/zerocopy/pull/3365/commits/acd7129840a5974ac91b2ad745e2282ead9ff051"
        },
        "date": 1779304640980,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 526,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 693,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5909564f60c5fda0f57a18fa2754e97645bf9935",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-20T18:49:44Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/5909564f60c5fda0f57a18fa2754e97645bf9935"
        },
        "date": 1779312058407,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 529,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 702,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ad88583ad51cf5328f506f90cf8fa1547236924c",
          "message": "Add experimental `ptr` crate to workspace re-exporting zerocopy pointer APIs",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3386/commits/ad88583ad51cf5328f506f90cf8fa1547236924c"
        },
        "date": 1779355298424,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 531,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 698,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "01a58ac62b72f5f196513a22f54fef82f18228dc",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/01a58ac62b72f5f196513a22f54fef82f18228dc"
        },
        "date": 1779370576180,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 731,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "277ebf3707b38060311af4f9a221b0ce8df27f06",
          "message": "Publish `Ptr[Inner]` behind a `--cfg`",
          "timestamp": "2026-05-21T06:03:35Z",
          "url": "https://github.com/google/zerocopy/pull/3387/commits/277ebf3707b38060311af4f9a221b0ce8df27f06"
        },
        "date": 1779371594340,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 466,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 636,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0402dfa593751057a357c89fb8bd140780abd8d5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg` (#3387)\n\nRelease 0.8.49-alpha.\n\ngherrit-pr-id: Gblc7dfltwcey7wvtj3gjkseaqcltgwvf",
          "timestamp": "2026-05-21T13:53:30Z",
          "url": "https://github.com/google/zerocopy/commit/0402dfa593751057a357c89fb8bd140780abd8d5"
        },
        "date": 1779372440098,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 94,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 561,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 737,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "0402dfa593751057a357c89fb8bd140780abd8d5",
          "message": "Publish `Ptr[Inner]` behind a `--cfg` (#3387)\n\nRelease 0.8.49-alpha.\n\ngherrit-pr-id: Gblc7dfltwcey7wvtj3gjkseaqcltgwvf",
          "timestamp": "2026-05-21T13:53:30Z",
          "tree_id": "4107ade63e23461c265e5d6eac61e3103e733349",
          "url": "https://github.com/google/zerocopy/commit/0402dfa593751057a357c89fb8bd140780abd8d5"
        },
        "date": 1779374608488,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 110,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 551,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 741,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a8e831be33afc8a7f1e7cb3e776a83249c78d64c",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs",
          "timestamp": "2026-05-21T14:39:27Z",
          "url": "https://github.com/google/zerocopy/pull/3388/commits/a8e831be33afc8a7f1e7cb3e776a83249c78d64c"
        },
        "date": 1779376424324,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 164,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 828,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1101,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "881160631750e2e1a5876327f5f14804a77d4cc8",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs (#3388)\n\ngherrit-pr-id: G7p44q5rcehvy46vrrowj5vxxkgp3xuw7",
          "timestamp": "2026-05-21T15:41:06Z",
          "url": "https://github.com/google/zerocopy/commit/881160631750e2e1a5876327f5f14804a77d4cc8"
        },
        "date": 1779378857951,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 543,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "881160631750e2e1a5876327f5f14804a77d4cc8",
          "message": "[docs] Document `--cfg=zerocopy_unstable_ptr` on internal rendered docs (#3388)\n\ngherrit-pr-id: G7p44q5rcehvy46vrrowj5vxxkgp3xuw7",
          "timestamp": "2026-05-21T15:41:06Z",
          "tree_id": "fd526a60e3a69ed5ade2900feffae0c14d7ab32b",
          "url": "https://github.com/google/zerocopy/commit/881160631750e2e1a5876327f5f14804a77d4cc8"
        },
        "date": 1779380714965,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 537,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 707,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5e92221cebe3e206737f21a4769dfc96b67e351b",
          "message": "SQUASH ME: More minor fix-ups and a parallel strategy for invoking charon",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3391/commits/5e92221cebe3e206737f21a4769dfc96b67e351b"
        },
        "date": 1779488467065,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 86,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 528,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 693,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d48a2766ccaffa7f283474bdfd204c0612fd7272",
          "message": "SQUASH ME: First round of review focused on charon.rs; mostly style and comment changes",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3390/commits/d48a2766ccaffa7f283474bdfd204c0612fd7272"
        },
        "date": 1779488566235,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 719,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "722d82fc782f492fae901812589761e691834f9a",
          "message": "SQUASH ME: More fix-ups on things the agent got wrong, and some initial lock tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3392/commits/722d82fc782f492fae901812589761e691834f9a"
        },
        "date": 1779488566743,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 606,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 783,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0ff00c6cc1807676a369d744e147571446ce53ab",
          "message": "SQUASH ME: Eliminate rust code parsing; simplify charon invocation; add tests to confirm charon is consuming all of workspace/project code",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3397/commits/0ff00c6cc1807676a369d744e147571446ce53ab"
        },
        "date": 1779488579262,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 101,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 574,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 762,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3ea68daa599483adfe1a4a6708d1cfa2c4694275",
          "message": "SQUASH ME: Initial port of run_charon and Expand",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3389/commits/3ea68daa599483adfe1a4a6708d1cfa2c4694275"
        },
        "date": 1779488585896,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 546,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 722,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "09f2e98d8a8f0a61e8838cb518d0b740d3c6d1dc",
          "message": "SQUASH ME: More clarifying tweaks, plus new (unreviewed) locking tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3395/commits/09f2e98d8a8f0a61e8838cb518d0b740d3c6d1dc"
        },
        "date": 1779488597748,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 570,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 752,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "39670e80a75cf768c9f715cfa60d49f93b4de489",
          "message": "SQUASH ME: More clarifying tweaks, plus new (unreviewed) locking tests",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3394/commits/39670e80a75cf768c9f715cfa60d49f93b4de489"
        },
        "date": 1779488613359,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 605,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 789,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1fb175297d7bdf03187f2399cb7404962954ed39",
          "message": "SQUASH ME: Add copyright/licenses to rust code; drop skipping behaviour from charon invocaitons loop; light code cleanup; a little documentation for generated test helper",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3396/commits/1fb175297d7bdf03187f2399cb7404962954ed39"
        },
        "date": 1779488620283,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 97,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 571,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 753,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9e7244b81bea553cd376f610409cc91c4ea462de",
          "message": "SQUASH ME: Add vendored dependencies; might have been required by previous iterations; oops",
          "timestamp": "2026-05-22T19:11:41Z",
          "url": "https://github.com/google/zerocopy/pull/3393/commits/9e7244b81bea553cd376f610409cc91c4ea462de"
        },
        "date": 1779488931846,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 399,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 539,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1022,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1f8bc9ee29fb6517819de1d00ce92ca9f29be253",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/1f8bc9ee29fb6517819de1d00ce92ca9f29be253"
        },
        "date": 1779720402268,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 533,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 705,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "3da3a84415ef0ec408e4dacde1e5ce5e109ba069",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/3da3a84415ef0ec408e4dacde1e5ce5e109ba069"
        },
        "date": 1779720412607,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 536,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 703,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e8af624f0a27fd4ad304b5dd2e7c54cea743b6d8",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/e8af624f0a27fd4ad304b5dd2e7c54cea743b6d8"
        },
        "date": 1779720438029,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 85,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 549,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 716,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "758f29023c9588793b2a54d19d87c450ab068e4d",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/758f29023c9588793b2a54d19d87c450ab068e4d"
        },
        "date": 1779720439771,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 551,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 722,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "128ab952cb5778efce34384f9a8bc2c5a95e88dc",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/128ab952cb5778efce34384f9a8bc2c5a95e88dc"
        },
        "date": 1779720452449,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 573,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 747,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "17613f21e365ac963bc74a6349e2265f9a53b874",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/17613f21e365ac963bc74a6349e2265f9a53b874"
        },
        "date": 1779720457290,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 538,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 705,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5339ec75605af1b57dbd98733833461fb3ae9025",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/5339ec75605af1b57dbd98733833461fb3ae9025"
        },
        "date": 1779720489578,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 536,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 706,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "600a18b5bf48ef192e61dda5d44821e0a309e181",
          "message": "[CI] Bump the all-actions group with 12 updates",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/600a18b5bf48ef192e61dda5d44821e0a309e181"
        },
        "date": 1779721415974,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 122,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 439,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 639,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "30344a26fa13fd857c2ffcd6462a6ac0eb7e2da8",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/30344a26fa13fd857c2ffcd6462a6ac0eb7e2da8"
        },
        "date": 1779734639702,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 81,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 444,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 603,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "84de2552b3140f5d16626eaa2212396310f8368c",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/84de2552b3140f5d16626eaa2212396310f8368c"
        },
        "date": 1779734764257,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 519,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 687,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e8924f2dc907cdbd9b3c71c64cce2342944e2527",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/e8924f2dc907cdbd9b3c71c64cce2342944e2527"
        },
        "date": 1779734780909,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 554,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 723,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f0ebc056e646c38bb2ee34fb87c14ce75624fbe9",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/f0ebc056e646c38bb2ee34fb87c14ce75624fbe9"
        },
        "date": 1779734789081,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 540,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 711,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4827fa1e3199e99d13fcec9868efcf249a090fdd",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/4827fa1e3199e99d13fcec9868efcf249a090fdd"
        },
        "date": 1779734798554,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 730,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "29a832dee34788cf73fb1f1ab14833c17e38cb0a",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/29a832dee34788cf73fb1f1ab14833c17e38cb0a"
        },
        "date": 1779734799546,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 717,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e229a984fc689f56bc396b0cc8da6ec021d2cce6",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/e229a984fc689f56bc396b0cc8da6ec021d2cce6"
        },
        "date": 1779734802358,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 94,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 547,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 722,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3d47a32c21279e551eb30400e95ba3e147d1675",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/a3d47a32c21279e551eb30400e95ba3e147d1675"
        },
        "date": 1779734802139,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 739,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1c62cfdaa9078c649c15b374fdee2c9e214dbbf7",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/1c62cfdaa9078c649c15b374fdee2c9e214dbbf7"
        },
        "date": 1779734828884,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 587,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 765,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fe814939a6469ef85bd86d0ce162544cd52e66f9",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/fe814939a6469ef85bd86d0ce162544cd52e66f9"
        },
        "date": 1779734832303,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 118,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 553,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 753,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f549d170be5eef4481a45f436510b9ee3326d706",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/f549d170be5eef4481a45f436510b9ee3326d706"
        },
        "date": 1779734839703,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 125,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 560,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 771,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1af7238e8da43249587ed42444de44092b0804f4",
          "message": "[anneal][v2] Initial commit of `exocrate`",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3376/commits/1af7238e8da43249587ed42444de44092b0804f4"
        },
        "date": 1779734867484,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 96,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 660,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 849,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0d0579829c4aa7402cdbee7f3c513c6bdedacc14",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/0d0579829c4aa7402cdbee7f3c513c6bdedacc14"
        },
        "date": 1779737127351,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 79,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 432,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 589,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "dd2f402ef606665ce4beca1793b09db4c7ebba7d",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/dd2f402ef606665ce4beca1793b09db4c7ebba7d"
        },
        "date": 1779737163001,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 95,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 436,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 611,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b10330bfaee0a1b2beb53dfab08ad3e7b652c696",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/b10330bfaee0a1b2beb53dfab08ad3e7b652c696"
        },
        "date": 1779737233139,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 713,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0133269f943a3ed9c2d80d6d26b11f715be7a9b4",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/0133269f943a3ed9c2d80d6d26b11f715be7a9b4"
        },
        "date": 1779737232196,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 723,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "43a1ef4e0e09638d38bad90ab29d945cea99a8cb",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/43a1ef4e0e09638d38bad90ab29d945cea99a8cb"
        },
        "date": 1779737237189,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 532,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 703,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "632f851f0a3ff3b8e5b4168a40e559d9cbf582fb",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/632f851f0a3ff3b8e5b4168a40e559d9cbf582fb"
        },
        "date": 1779737239279,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 94,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 559,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 735,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9450f8623c20666f74b78f56950bbcc9241abd0c",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/9450f8623c20666f74b78f56950bbcc9241abd0c"
        },
        "date": 1779737268870,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 104,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 535,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 719,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f300c70eb6104a5a175d5c0de463f32de3316d9c",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f300c70eb6104a5a175d5c0de463f32de3316d9c"
        },
        "date": 1779737279865,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 85,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 569,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 739,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "e60c407e7fc952258e9d32ab08e84d8e50e9f008",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/e60c407e7fc952258e9d32ab08e84d8e50e9f008"
        },
        "date": 1779737280274,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 118,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 542,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 745,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8815480d922eb5f7827aed0ea7e54073b1c950e5",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/8815480d922eb5f7827aed0ea7e54073b1c950e5"
        },
        "date": 1779737282316,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 99,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 738,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "785ffee6aea00b0cbe84b64d156ad3dae730054f",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/785ffee6aea00b0cbe84b64d156ad3dae730054f"
        },
        "date": 1779737306088,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 106,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 574,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 764,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2fcfb3371cdc0f6ca1c16ab6c18253de09194113",
          "message": "[anneal][v2] Initial commit of `exocrate` (#3376)\n\ngherrit-pr-id: G34qjom3lz7cc6hd57tgp44t4pzlstdhj\n\nCo-authored-by: Mark Dittmer <markdittmer@google.com>",
          "timestamp": "2026-05-25T15:20:48-04:00",
          "tree_id": "602fe9e513bae3aa5ba6dcf91e4b5b93cf8d59dd",
          "url": "https://github.com/google/zerocopy/commit/2fcfb3371cdc0f6ca1c16ab6c18253de09194113"
        },
        "date": 1779737513799,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 82,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 445,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 605,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2ae5a009ac0b70ae5c20111ec18e5a84c3f79716",
          "message": "SQUASH ME into toml_cost dep",
          "timestamp": "2026-05-25T04:56:36Z",
          "url": "https://github.com/google/zerocopy/pull/3413/commits/2ae5a009ac0b70ae5c20111ec18e5a84c3f79716"
        },
        "date": 1779738198698,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 96,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 737,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4f657b10c5c84de1faa6807531050d66fc49930a",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/4f657b10c5c84de1faa6807531050d66fc49930a"
        },
        "date": 1779738548925,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 539,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 711,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c7bc3352a1c146f92395b500d61791385d0898f3",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/c7bc3352a1c146f92395b500d61791385d0898f3"
        },
        "date": 1779738565135,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 81,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 442,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 602,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b59e6f0c61374b8a757b6c756c03e8fae8bf8317",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/b59e6f0c61374b8a757b6c756c03e8fae8bf8317"
        },
        "date": 1779738626132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 525,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 695,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "56d3125c79237a68329ccd7d4d7a92189673a9db",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/56d3125c79237a68329ccd7d4d7a92189673a9db"
        },
        "date": 1779738645701,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 530,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 698,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fa0696c4f6e5baf684d3f87217c93a15dfe91013",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/fa0696c4f6e5baf684d3f87217c93a15dfe91013"
        },
        "date": 1779738660181,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 542,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1e8210d44264d23cfb599c49a169d0b467a5bead",
          "message": "[anneal][v2] Independently vendor and patch toml_const",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3381/commits/1e8210d44264d23cfb599c49a169d0b467a5bead"
        },
        "date": 1779738661880,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 714,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb7cac5546d5c9256786007391790a6ff775f67c",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/cb7cac5546d5c9256786007391790a6ff775f67c"
        },
        "date": 1779738669693,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 539,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 708,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "41c40c7db5b733eb7180fc351b8c94c5ba1e185f",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/41c40c7db5b733eb7180fc351b8c94c5ba1e185f"
        },
        "date": 1779738668825,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 732,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f3e3b5ecb8fab65be756f2aafa3047886f06eaae",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f3e3b5ecb8fab65be756f2aafa3047886f06eaae"
        },
        "date": 1779738672268,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 538,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ef3dd8b8f7476f7ac3afe98afec7d304c80c0f72",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/ef3dd8b8f7476f7ac3afe98afec7d304c80c0f72"
        },
        "date": 1779738672567,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 546,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 716,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f8d740b542136a96f94df3296a38c839b82e2959",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T19:20:57Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/f8d740b542136a96f94df3296a38c839b82e2959"
        },
        "date": 1779738713321,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 576,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 754,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Mark Dittmer",
            "username": "mdittmer",
            "email": "mdittmer@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "275aff21f3b22c4c4db0311576b897b8d5805fa8",
          "message": "[anneal][v2] Independently vendor and patch toml_const (#3381)\n\n- Vendor `anneal/v2` dependencies independently\n- Patch `toml_const` to avoid breakage on `'cfg(...)'` keys in\n  `Cargo.toml` files\n\ngherrit-pr-id: Ga27arw5h5oz3ldi25ijsj2rsbzuqictv",
          "timestamp": "2026-05-25T19:51:17Z",
          "url": "https://github.com/google/zerocopy/commit/275aff21f3b22c4c4db0311576b897b8d5805fa8"
        },
        "date": 1779739514778,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 124,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 764,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "275aff21f3b22c4c4db0311576b897b8d5805fa8",
          "message": "[anneal][v2] Independently vendor and patch toml_const (#3381)\n\n- Vendor `anneal/v2` dependencies independently\n- Patch `toml_const` to avoid breakage on `'cfg(...)'` keys in\n  `Cargo.toml` files\n\ngherrit-pr-id: Ga27arw5h5oz3ldi25ijsj2rsbzuqictv",
          "timestamp": "2026-05-25T19:51:17Z",
          "tree_id": "bb9133d186a3e0b671544c47ee9211654e81bc5f",
          "url": "https://github.com/google/zerocopy/commit/275aff21f3b22c4c4db0311576b897b8d5805fa8"
        },
        "date": 1779742022568,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 610,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 712,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 1411,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ebd26a04cf7bed697c35bad7f6feae340fcb07c1",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/ebd26a04cf7bed697c35bad7f6feae340fcb07c1"
        },
        "date": 1779750049603,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 530,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 699,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9606fecb64feec3aba8a78fc135667f7c06ec097",
          "message": "[anneal][v2][exocrate] Crate-level documentation",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3382/commits/9606fecb64feec3aba8a78fc135667f7c06ec097"
        },
        "date": 1779750050580,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 537,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 706,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f838f8ebae2730fa468f9001522603869c6095aa",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/f838f8ebae2730fa468f9001522603869c6095aa"
        },
        "date": 1779750065321,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 525,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 694,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "64753f4d4fb2454579dc32791cfed49ab3855a14",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/64753f4d4fb2454579dc32791cfed49ab3855a14"
        },
        "date": 1779750076833,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 95,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 547,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 723,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "25f8010762c0f7915218c94fb5d019b4b1381812",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/25f8010762c0f7915218c94fb5d019b4b1381812"
        },
        "date": 1779750091791,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 98,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 556,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 740,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7035d4bf1e1d5b271e25c1fdfca8fb36ce881eb0",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/7035d4bf1e1d5b271e25c1fdfca8fb36ce881eb0"
        },
        "date": 1779750130852,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 534,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 702,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "82160afdc28389bda8429edd8f19555dec8a3816",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/82160afdc28389bda8429edd8f19555dec8a3816"
        },
        "date": 1779750147249,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 529,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 697,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7e1f72e47a46abdc46a797e73eed1b86b6191a3f",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/7e1f72e47a46abdc46a797e73eed1b86b6191a3f"
        },
        "date": 1779750178204,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 531,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 701,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "26c45cf3848f5b65df19e6f01d2dfcf9fe4e93db",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/26c45cf3848f5b65df19e6f01d2dfcf9fe4e93db"
        },
        "date": 1779750246407,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 527,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 695,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "fafcee46f6866df9d56f36cf6f7d069b830b5452",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-25T20:22:43Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/fafcee46f6866df9d56f36cf6f7d069b830b5452"
        },
        "date": 1779750283359,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 559,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 729,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d0babbacd343fc7132a8171c5eeb7b1754561159",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0",
          "timestamp": "2026-05-26T12:42:10Z",
          "url": "https://github.com/google/zerocopy/pull/3415/commits/d0babbacd343fc7132a8171c5eeb7b1754561159"
        },
        "date": 1779812387129,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 95,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 535,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "0321b8e7055ae7159280930753924207775dc35a",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0 (#3415)\n\ngherrit-pr-id: Gz2xxcekiwax6yzlsfzuwlzh4mcfd5nms",
          "timestamp": "2026-05-26T16:20:03Z",
          "url": "https://github.com/google/zerocopy/commit/0321b8e7055ae7159280930753924207775dc35a"
        },
        "date": 1779813239729,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 577,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 751,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0321b8e7055ae7159280930753924207775dc35a",
          "message": "[anneal][exocrate] Upgrade to toml_const 1.3.0 (#3415)\n\ngherrit-pr-id: Gz2xxcekiwax6yzlsfzuwlzh4mcfd5nms",
          "timestamp": "2026-05-26T16:20:03Z",
          "tree_id": "0b33f6617272bf085e9e17ced8468c3c66b75681",
          "url": "https://github.com/google/zerocopy/commit/0321b8e7055ae7159280930753924207775dc35a"
        },
        "date": 1779815152220,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 109,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 568,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 763,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9e20917878209f411fe3f16323c70e2eccea2d56",
          "message": "[wip] Introduce unstable `derive(most_traits)`",
          "timestamp": "2026-05-26T16:51:55Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/9e20917878209f411fe3f16323c70e2eccea2d56"
        },
        "date": 1779879343204,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 529,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 701,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9a0d277803d54383a7ae40348856e390c322ae25",
          "message": "[wip] Introduce unstable `derive(most_traits)`",
          "timestamp": "2026-05-26T16:51:55Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/9a0d277803d54383a7ae40348856e390c322ae25"
        },
        "date": 1779881243216,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 122,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 753,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "145818923+google-pr-creation-bot@users.noreply.github.com",
            "name": "Google PR Creation Bot",
            "username": "google-pr-creation-bot"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5fc5d5bef889bbf81ab5bae500758979d5978a08",
          "message": "Release 0.8.49 (#3417)",
          "timestamp": "2026-05-27T11:55:29-04:00",
          "tree_id": "4b298b6678caa62663f284dce3339ee15b73f7cd",
          "url": "https://github.com/google/zerocopy/commit/5fc5d5bef889bbf81ab5bae500758979d5978a08"
        },
        "date": 1779898123000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 736,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d3b95475a24f7b287ee37ecaff4ea6271c369881",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/d3b95475a24f7b287ee37ecaff4ea6271c369881"
        },
        "date": 1779906664613,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 538,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 709,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "98f4d2f73fb213c8700d3688adb27104c1a01018",
          "message": "[anneal][v2] Vendor charon_lib",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/98f4d2f73fb213c8700d3688adb27104c1a01018"
        },
        "date": 1779906822359,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 737,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "4488992b0c74134e39a647ad3160cd596838823a",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/4488992b0c74134e39a647ad3160cd596838823a"
        },
        "date": 1779906841155,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 532,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 699,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "9f295066c87989fc930838ef171ddaf8bb1de5e0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/9f295066c87989fc930838ef171ddaf8bb1de5e0"
        },
        "date": 1779906963737,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 155,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 613,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 854,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0cf1bf4a1eeae8d8c3f711f8e2545e9e34c1344d",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/0cf1bf4a1eeae8d8c3f711f8e2545e9e34c1344d"
        },
        "date": 1779907088796,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 518,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 687,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1faae2d750595519e398f2f4364bff2aa861f6f5",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/1faae2d750595519e398f2f4364bff2aa861f6f5"
        },
        "date": 1779907138194,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 119,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 566,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 772,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a3bc3a25735f833f02603005c6e64151d5a20a9a",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/a3bc3a25735f833f02603005c6e64151d5a20a9a"
        },
        "date": 1779907170591,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 549,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 730,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "88f14ff06f5a7da6baeca4b34c45e031c0c27d42",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/88f14ff06f5a7da6baeca4b34c45e031c0c27d42"
        },
        "date": 1779907224133,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 543,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 724,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c8aa431253246e619045b8cbdabedb327ab03b3a",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/c8aa431253246e619045b8cbdabedb327ab03b3a"
        },
        "date": 1779907264427,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 715,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c63a42248a93ff6fe32f7575fdc50dd531ecc547",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-05-27T17:46:42Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/c63a42248a93ff6fe32f7575fdc50dd531ecc547"
        },
        "date": 1779907409264,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 557,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 734,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "eaec844201fd1ee229c6af68440cbc202f68eccc",
          "message": "[pointer] `Ptr::iter` takes `self` by value",
          "timestamp": "2026-05-28T17:15:11Z",
          "url": "https://github.com/google/zerocopy/pull/3421/commits/eaec844201fd1ee229c6af68440cbc202f68eccc"
        },
        "date": 1779997990007,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 84,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 443,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 606,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "f70e4224996ed73b2cd927719246361d977a629e",
          "message": "[pointer] `Ptr::iter` takes `self` by value (#3421)\n\nThis fixes a prior soundness hole - `Ptr::iter` took `&self`, permitting\nmultiple overlapping `Exclusive` `Ptr`s to be created at the same time.\n\nIn CI, when running `cargo-semver-checks`, don't pass `--cfg\nzerocopy_unstable_ptr`, as we don't want to semver-check unstable APIs.\n\nRelease 0.8.50.\n\nFixes #3419\n\ngherrit-pr-id: Ibb7d512d9e12ecfd118bb018bcae10d17279c2ed",
          "timestamp": "2026-05-29T17:01:13Z",
          "url": "https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e"
        },
        "date": 1780074819160,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 124,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 447,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 652,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f70e4224996ed73b2cd927719246361d977a629e",
          "message": "[pointer] `Ptr::iter` takes `self` by value (#3421)\n\nThis fixes a prior soundness hole - `Ptr::iter` took `&self`, permitting\nmultiple overlapping `Exclusive` `Ptr`s to be created at the same time.\n\nIn CI, when running `cargo-semver-checks`, don't pass `--cfg\nzerocopy_unstable_ptr`, as we don't want to semver-check unstable APIs.\n\nRelease 0.8.50.\n\nFixes #3419\n\ngherrit-pr-id: Ibb7d512d9e12ecfd118bb018bcae10d17279c2ed",
          "timestamp": "2026-05-29T17:01:13Z",
          "tree_id": "5d0f67bd945a1ceeab35e9cc06db105ebf037300",
          "url": "https://github.com/google/zerocopy/commit/f70e4224996ed73b2cd927719246361d977a629e"
        },
        "date": 1780076996662,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 565,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 740,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "10a3239fe6afd068b249aee8ed7d37ff6ac3f37c",
          "message": "[CI] Bump the all-actions group across 1 directory with 12 updates",
          "timestamp": "2026-05-29T17:36:36Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/10a3239fe6afd068b249aee8ed7d37ff6ac3f37c"
        },
        "date": 1780077133091,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 94,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 447,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 623,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "76e1c7ebf4c09a90b7f3efbd3bc8393825cf3cd8",
          "message": "Make GHCR cache exports and consumer pushes conditional for external PRs",
          "timestamp": "2026-05-31T08:45:06Z",
          "url": "https://github.com/google/zerocopy/pull/3423/commits/76e1c7ebf4c09a90b7f3efbd3bc8393825cf3cd8"
        },
        "date": 1780250038764,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 127,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 552,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 759,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "cf7cf6154867078e8b994ae981959edffaf724a9",
          "message": "Handle fork PR Docker cache permissions (#3423)\n\n### Motivation\n- External fork PRs were failing CI at Docker build/cache steps because the runner `GITHUB_TOKEN` for forks does not have permission to write GHCR packages or cache entries.\n\n### Description\n- In `.github/workflows/ci.yml` conditionally disable `cache-to` exports to GHCR for external pull requests while preserving cache exports for same-repo runs, pushes, merge groups, and workflow dispatches.\n- In `.github/workflows/anneal.yml` conditionally disable `cache-to` and guard the `Build and push Docker image` step so image push/cache writes are only attempted when the run is allowed to write to GHCR.\n- In `.github/workflows/anneal.yml` add `if:` guards on Anneal consumer jobs (`anneal_tests` and `verify_examples`) so those consumer jobs are skipped for external fork PRs that cannot publish the GHCR image they would consume.\n\n### Testing\n- Ran `./ci/check_actions.sh` and it completed successfully.\n- Ran `git diff --check` and it produced no issues.\n- Ran `CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 ./githooks/pre-push` to exercise the repo hooks in a non-interactive way and it completed successfully (the initial pre-push without auto-install hit local tooling prompts).",
          "timestamp": "2026-05-31T19:36:24Z",
          "url": "https://github.com/google/zerocopy/commit/cf7cf6154867078e8b994ae981959edffaf724a9"
        },
        "date": 1780256940478,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 525,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 693,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cf7cf6154867078e8b994ae981959edffaf724a9",
          "message": "Handle fork PR Docker cache permissions (#3423)\n\n### Motivation\n- External fork PRs were failing CI at Docker build/cache steps because the runner `GITHUB_TOKEN` for forks does not have permission to write GHCR packages or cache entries.\n\n### Description\n- In `.github/workflows/ci.yml` conditionally disable `cache-to` exports to GHCR for external pull requests while preserving cache exports for same-repo runs, pushes, merge groups, and workflow dispatches.\n- In `.github/workflows/anneal.yml` conditionally disable `cache-to` and guard the `Build and push Docker image` step so image push/cache writes are only attempted when the run is allowed to write to GHCR.\n- In `.github/workflows/anneal.yml` add `if:` guards on Anneal consumer jobs (`anneal_tests` and `verify_examples`) so those consumer jobs are skipped for external fork PRs that cannot publish the GHCR image they would consume.\n\n### Testing\n- Ran `./ci/check_actions.sh` and it completed successfully.\n- Ran `git diff --check` and it produced no issues.\n- Ran `CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 ./githooks/pre-push` to exercise the repo hooks in a non-interactive way and it completed successfully (the initial pre-push without auto-install hit local tooling prompts).",
          "timestamp": "2026-05-31T19:36:24Z",
          "tree_id": "0c131497ef5db2f7d6f3a9f16795ee729af0212b",
          "url": "https://github.com/google/zerocopy/commit/cf7cf6154867078e8b994ae981959edffaf724a9"
        },
        "date": 1780258918144,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 124,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 560,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 771,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "00a7076e157d1469041eaac25b6fa3094b2144f0",
          "message": "[CI] Bump the all-actions group across 1 directory with 12 updates",
          "timestamp": "2026-05-31T20:08:06Z",
          "url": "https://github.com/google/zerocopy/pull/3406/commits/00a7076e157d1469041eaac25b6fa3094b2144f0"
        },
        "date": 1780259105047,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 548,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 722,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "92d264efb130c8253e7a95de749fa2567e868b88",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/92d264efb130c8253e7a95de749fa2567e868b88"
        },
        "date": 1780493374534,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 108,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 445,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 633,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1da6e9a7fafa4ba605b548ef8010b32ec188dae0",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/1da6e9a7fafa4ba605b548ef8010b32ec188dae0"
        },
        "date": 1780493505209,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 107,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 563,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 756,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "5ad38a52b02aea911c3192fe890071517e51bb54",
          "message": "Prevent external PRs from pushing benchmark data in anneal CI workflow",
          "timestamp": "2026-06-03T00:39:32Z",
          "url": "https://github.com/google/zerocopy/pull/3430/commits/5ad38a52b02aea911c3192fe890071517e51bb54"
        },
        "date": 1780519054987,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 97,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 725,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "cacc81c2bdb1efa169bed1dda231d89590539f7b",
          "message": "[ci][anneal] Don't publish fork PR benchmarks (#3430)",
          "timestamp": "2026-06-03T13:54:01-07:00",
          "tree_id": "489e52a87f260a77311791b511785c53a13c281d",
          "url": "https://github.com/google/zerocopy/commit/cacc81c2bdb1efa169bed1dda231d89590539f7b"
        },
        "date": 1780521892694,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 82,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 438,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 599,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "63a83e13e35d91481778e9942aa2ca4f11f16cb9",
          "message": "[CI] Bump the all-actions group across 1 directory with 13 updates",
          "timestamp": "2026-06-03T20:54:07Z",
          "url": "https://github.com/google/zerocopy/pull/3431/commits/63a83e13e35d91481778e9942aa2ca4f11f16cb9"
        },
        "date": 1780522188517,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 446,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 619,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "87631534+platonicsock@users.noreply.github.com",
            "name": "Sock",
            "username": "platonicsock"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bd37d45186e8f846df74da6f2d17ded4e19b4bd4",
          "message": "Typo fixes (#3425)\n\nTwo instances of changing \"Anneal'\" to \"Anneal's\"",
          "timestamp": "2026-06-03T14:30:13-07:00",
          "tree_id": "735cf8abf0171da25ea8da7e0e8363d301df4f0a",
          "url": "https://github.com/google/zerocopy/commit/bd37d45186e8f846df74da6f2d17ded4e19b4bd4"
        },
        "date": 1780523255510,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 98,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 544,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 728,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "80544d91c9f08540c76c52d7df093a2b811872c5",
          "message": "[wip] Introduce unstable `derive(most_traits)`, linux cfg.",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/80544d91c9f08540c76c52d7df093a2b811872c5"
        },
        "date": 1780621314432,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 535,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 701,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1fa66dc492fd697eb58bc2d206c971d59d61b439",
          "message": "[zerocopy] Move to `zerocopy` subdirectory",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3434/commits/1fa66dc492fd697eb58bc2d206c971d59d61b439"
        },
        "date": 1780624218138,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 485,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 598,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2e0a025108c8169b15ce72405b08df41d8f62660",
          "message": "[zerocopy] Move to `zerocopy` subdirectory",
          "timestamp": "2026-06-04T14:36:20Z",
          "url": "https://github.com/google/zerocopy/pull/3434/commits/2e0a025108c8169b15ce72405b08df41d8f62660"
        },
        "date": 1780632276476,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 120,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 534,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 679,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf",
            "email": "joshlf@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "a773081477608b799ccdd48de490de139e19873c",
          "message": "[zerocopy] Move to `zerocopy` subdirectory (#3434)\n\nMove the Zerocopy crate and its vendored Cargo configuration under\n`zerocopy/`, and update CI, docs, hooks, and helper scripts to run\nzerocopy commands from that directory.\n\nThis keeps zerocopy in its own vendored Cargo world while allowing\ntools, Anneal, and future crates to use normal Cargo resolution and not\nrequire vendoring their dependencies.\n\nAlso move `anneal/v2/exocrate` to the repository root.\n\ngherrit-pr-id: Ghuilhfh6h4womt35vc6domtloovmnnhl",
          "timestamp": "2026-06-05T04:04:48Z",
          "url": "https://github.com/google/zerocopy/commit/a773081477608b799ccdd48de490de139e19873c"
        },
        "date": 1780632969588,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 497,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 614,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "joshlf@users.noreply.github.com",
            "name": "Joshua Liebow-Feeser",
            "username": "joshlf"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a773081477608b799ccdd48de490de139e19873c",
          "message": "[zerocopy] Move to `zerocopy` subdirectory (#3434)\n\nMove the Zerocopy crate and its vendored Cargo configuration under\n`zerocopy/`, and update CI, docs, hooks, and helper scripts to run\nzerocopy commands from that directory.\n\nThis keeps zerocopy in its own vendored Cargo world while allowing\ntools, Anneal, and future crates to use normal Cargo resolution and not\nrequire vendoring their dependencies.\n\nAlso move `anneal/v2/exocrate` to the repository root.\n\ngherrit-pr-id: Ghuilhfh6h4womt35vc6domtloovmnnhl",
          "timestamp": "2026-06-05T04:04:48Z",
          "tree_id": "60647c9d9df642af06edc6597d6f373d203aaccc",
          "url": "https://github.com/google/zerocopy/commit/a773081477608b799ccdd48de490de139e19873c"
        },
        "date": 1780634932153,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 102,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 518,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 643,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "366d9ad222be87ad1311a0fb45e96d23f25381f0",
          "message": "[CI] Bump the all-actions group across 1 directory with 13 updates",
          "timestamp": "2026-06-05T04:37:36Z",
          "url": "https://github.com/google/zerocopy/pull/3431/commits/366d9ad222be87ad1311a0fb45e96d23f25381f0"
        },
        "date": 1780635242428,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 110,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 567,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 708,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b33d9a0254ff8b1fddceaa6e675020168d8aedf1",
          "message": "Bump the cargo group across 1 directory with 4 updates",
          "timestamp": "2026-06-05T04:37:36Z",
          "url": "https://github.com/google/zerocopy/pull/3435/commits/b33d9a0254ff8b1fddceaa6e675020168d8aedf1"
        },
        "date": 1780636078729,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 508,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 621,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "dependabot[bot]",
            "username": "dependabot[bot]",
            "email": "49699333+dependabot[bot]@users.noreply.github.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "bc0bb77346772be0e80aeb68f8f3f9b2e58a1612",
          "message": "Bump the cargo group across 1 directory with 4 updates (#3435)\n\nBumps the cargo group with 4 updates in the /anneal directory: [tar](https://github.com/composefs/tar-rs), [openssl](https://github.com/rust-openssl/rust-openssl), [rand](https://github.com/rust-random/rand) and [rustls-webpki](https://github.com/rustls/webpki).\n\n\nUpdates `tar` from 0.4.45 to 0.4.46\n- [Release notes](https://github.com/composefs/tar-rs/releases)\n- [Commits](https://github.com/composefs/tar-rs/compare/0.4.45...0.4.46)\n\nUpdates `openssl` from 0.10.76 to 0.10.80\n- [Release notes](https://github.com/rust-openssl/rust-openssl/releases)\n- [Commits](https://github.com/rust-openssl/rust-openssl/compare/openssl-v0.10.76...openssl-v0.10.80)\n\nUpdates `rand` from 0.9.2 to 0.9.4\n- [Release notes](https://github.com/rust-random/rand/releases)\n- [Changelog](https://github.com/rust-random/rand/blob/0.9.4/CHANGELOG.md)\n- [Commits](https://github.com/rust-random/rand/compare/rand_core-0.9.2...0.9.4)\n\nUpdates `rustls-webpki` from 0.103.10 to 0.103.13\n- [Release notes](https://github.com/rustls/webpki/releases)\n- [Commits](https://github.com/rustls/webpki/compare/v/0.103.10...v/0.103.13)\n\n---\nupdated-dependencies:\n- dependency-name: tar\n  dependency-version: 0.4.46\n  dependency-type: direct:production\n  dependency-group: cargo\n- dependency-name: openssl\n  dependency-version: 0.10.80\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rand\n  dependency-version: 0.9.4\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rustls-webpki\n  dependency-version: 0.103.13\n  dependency-type: indirect\n  dependency-group: cargo\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>",
          "timestamp": "2026-06-05T05:08:07Z",
          "url": "https://github.com/google/zerocopy/commit/bc0bb77346772be0e80aeb68f8f3f9b2e58a1612"
        },
        "date": 1780637839306,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 518,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 630,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc0bb77346772be0e80aeb68f8f3f9b2e58a1612",
          "message": "Bump the cargo group across 1 directory with 4 updates (#3435)\n\nBumps the cargo group with 4 updates in the /anneal directory: [tar](https://github.com/composefs/tar-rs), [openssl](https://github.com/rust-openssl/rust-openssl), [rand](https://github.com/rust-random/rand) and [rustls-webpki](https://github.com/rustls/webpki).\n\n\nUpdates `tar` from 0.4.45 to 0.4.46\n- [Release notes](https://github.com/composefs/tar-rs/releases)\n- [Commits](https://github.com/composefs/tar-rs/compare/0.4.45...0.4.46)\n\nUpdates `openssl` from 0.10.76 to 0.10.80\n- [Release notes](https://github.com/rust-openssl/rust-openssl/releases)\n- [Commits](https://github.com/rust-openssl/rust-openssl/compare/openssl-v0.10.76...openssl-v0.10.80)\n\nUpdates `rand` from 0.9.2 to 0.9.4\n- [Release notes](https://github.com/rust-random/rand/releases)\n- [Changelog](https://github.com/rust-random/rand/blob/0.9.4/CHANGELOG.md)\n- [Commits](https://github.com/rust-random/rand/compare/rand_core-0.9.2...0.9.4)\n\nUpdates `rustls-webpki` from 0.103.10 to 0.103.13\n- [Release notes](https://github.com/rustls/webpki/releases)\n- [Commits](https://github.com/rustls/webpki/compare/v/0.103.10...v/0.103.13)\n\n---\nupdated-dependencies:\n- dependency-name: tar\n  dependency-version: 0.4.46\n  dependency-type: direct:production\n  dependency-group: cargo\n- dependency-name: openssl\n  dependency-version: 0.10.80\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rand\n  dependency-version: 0.9.4\n  dependency-type: indirect\n  dependency-group: cargo\n- dependency-name: rustls-webpki\n  dependency-version: 0.103.13\n  dependency-type: indirect\n  dependency-group: cargo\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>",
          "timestamp": "2026-06-05T05:08:07Z",
          "tree_id": "46c88fe74ea7fb7b5b5974d81872b4129e09ac82",
          "url": "https://github.com/google/zerocopy/commit/bc0bb77346772be0e80aeb68f8f3f9b2e58a1612"
        },
        "date": 1780639791254,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 491,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 605,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "eiffel-fl",
            "username": "eiffel-fl",
            "email": "laniel_francis@privacyrequired.com"
          },
          "committer": {
            "name": "GitHub",
            "username": "web-flow",
            "email": "noreply@github.com"
          },
          "id": "c97143cb09c7edb578c4a9edaf50d8db720f60a9",
          "message": "[byteorder] Add cfg no_fp_fmt_parse (#3429)\n\nThis cfg deactivates Debug and Display for floatting point numbers, this is\nparticluarly useful in kernel context.\nThe implementation is inspired by:\nhttps://github.com/rust-lang/rust/commit/ec7292ad3c35\n\nFixes #3426",
          "timestamp": "2026-06-05T13:59:43Z",
          "url": "https://github.com/google/zerocopy/commit/c97143cb09c7edb578c4a9edaf50d8db720f60a9"
        },
        "date": 1780668748361,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 100,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 511,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 636,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "laniel_francis@privacyrequired.com",
            "name": "eiffel-fl",
            "username": "eiffel-fl"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": false,
          "id": "c97143cb09c7edb578c4a9edaf50d8db720f60a9",
          "message": "[byteorder] Add cfg no_fp_fmt_parse (#3429)\n\nThis cfg deactivates Debug and Display for floatting point numbers, this is\nparticluarly useful in kernel context.\nThe implementation is inspired by:\nhttps://github.com/rust-lang/rust/commit/ec7292ad3c35\n\nFixes #3426",
          "timestamp": "2026-06-05T13:59:43Z",
          "tree_id": "6709fbc182f55d749bc31796fd2fb83d2e017624",
          "url": "https://github.com/google/zerocopy/commit/c97143cb09c7edb578c4a9edaf50d8db720f60a9"
        },
        "date": 1780670479073,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 86,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 397,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 506,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cb7c1ea5c58cf7c49eb48227eb29ff99718f6490",
          "message": "Introduce `derive(most_traits)` and rename unstable linux cfg",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3416/commits/cb7c1ea5c58cf7c49eb48227eb29ff99718f6490"
        },
        "date": 1780672190287,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 522,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 635,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ea0358ed52b7bd3ed92443a2c83a57d1abfe0465",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/ea0358ed52b7bd3ed92443a2c83a57d1abfe0465"
        },
        "date": 1780676114326,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 475,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 589,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "da15155d75a90ea73fdbdf3bc16d1d447ff3fcd5",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/da15155d75a90ea73fdbdf3bc16d1d447ff3fcd5"
        },
        "date": 1780676114842,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 88,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 486,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 595,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cc455f23a36ba3c5557833b715abd806b7a9a7b8",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/cc455f23a36ba3c5557833b715abd806b7a9a7b8"
        },
        "date": 1780676300660,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 398,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 512,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "616962d5f9a8212858c6ee9ad81022cf5edc1403",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/616962d5f9a8212858c6ee9ad81022cf5edc1403"
        },
        "date": 1780676354734,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 91,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 500,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 615,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ab47687955605152b7e48c017b638520f2dcbee5",
          "message": "[anneal][v2][exocrate] Add install fixup hook",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3436/commits/ab47687955605152b7e48c017b638520f2dcbee5"
        },
        "date": 1780676367976,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 503,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 619,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "012f46ef310d195c7257acb245e7d2fecd90022e",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/012f46ef310d195c7257acb245e7d2fecd90022e"
        },
        "date": 1780676395339,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 87,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 507,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 617,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "491140c513436cf4393c075811a2159bb48cc4e2",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/491140c513436cf4393c075811a2159bb48cc4e2"
        },
        "date": 1780676419358,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 93,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 493,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 613,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "10684dbad1d5c5f994a274ddfd3b7db9f6ebcedc",
          "message": "[anneal][v2] Vendor charon_lib",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/10684dbad1d5c5f994a274ddfd3b7db9f6ebcedc"
        },
        "date": 1780676444163,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 106,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 506,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 642,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "964666dcdf6424e494e25da0ba8749bbc91dca67",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/964666dcdf6424e494e25da0ba8749bbc91dca67"
        },
        "date": 1780676480752,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 506,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 627,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "99996e42477579faa684a3a86b860998f9bf70a1",
          "message": "[anneal][v2] Import vendored cargo dependencies",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/99996e42477579faa684a3a86b860998f9bf70a1"
        },
        "date": 1780676560321,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 518,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 635,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "06a06836795d8dfb109e56f4f813970beab79e73",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T14:31:56Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/06a06836795d8dfb109e56f4f813970beab79e73"
        },
        "date": 1780676569896,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 89,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 519,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 631,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "86ea86c44eec663397077a020102c8b0bb28e6d9",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T16:17:53Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/86ea86c44eec663397077a020102c8b0bb28e6d9"
        },
        "date": 1780682478885,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 122,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 530,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 679,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "75c8f447736105f681c52d3e88928df2815dc661",
          "message": "[anneal][v2] Add and integrate nix-built exocrate",
          "timestamp": "2026-06-05T16:17:53Z",
          "url": "https://github.com/google/zerocopy/pull/3383/commits/75c8f447736105f681c52d3e88928df2815dc661"
        },
        "date": 1780689585414,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 92,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 480,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 596,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "mdittmer@users.noreply.github.com",
            "name": "Mark Dittmer",
            "username": "mdittmer"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b7d9acf849ef9791776ad100da386ac67b8a8a60",
          "message": "[anneal][v2] Add and integrate nix-built exocrate (#3383)\n\n- Add nix derivations for exocrate\n- Add `setup` sub-command to locate-or-install exocrate\n- Add integration test for \"developer mode\" `setup` that presumes local\n  exocrate archive\n- Add github workflows to:\n  - Warm nix cache\n  - Locally link exocrate archive from nix, then run all tests\n\ngherrit-pr-id: Gwhroikc5idscowxamayknlke2uiddzv3",
          "timestamp": "2026-06-05T18:00:27-04:00",
          "tree_id": "ead44d2b940c9097c6db13604d193d3f48190e3e",
          "url": "https://github.com/google/zerocopy/commit/b7d9acf849ef9791776ad100da386ac67b8a8a60"
        },
        "date": 1780697551375,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 90,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 501,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 610,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "588d46cae38288eabdc18670ba68cdc353d1b420",
          "message": "[CI] Bump the all-actions group across 1 directory with 14 updates",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3439/commits/588d46cae38288eabdc18670ba68cdc353d1b420"
        },
        "date": 1780697829083,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Docker Pull Time",
            "value": 93,
            "unit": "seconds"
          },
          {
            "name": "Test Time",
            "value": 495,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 608,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bf4008843abe287138188cbb4f00a3a72873b7ca",
          "message": "[anneal] Move setup and CI onto Nix archive",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3438/commits/bf4008843abe287138188cbb4f00a3a72873b7ca"
        },
        "date": 1780711175598,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 474,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 767,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b7c6f430649ddae2ab8025b54e009c3ef98e4b3d",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/b7c6f430649ddae2ab8025b54e009c3ef98e4b3d"
        },
        "date": 1780711206348,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 446,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 738,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0e18ff4a9c1a37cf7b058f6be14be885dda988f6",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/0e18ff4a9c1a37cf7b058f6be14be885dda988f6"
        },
        "date": 1780711299164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 577,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 845,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "77d5af07608327e18540bb65ce2f5b931f057bb3",
          "message": "[anneal] Move setup and CI onto Nix archive",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3438/commits/77d5af07608327e18540bb65ce2f5b931f057bb3"
        },
        "date": 1780713536144,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 585,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 790,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "37c4195552b9535590ee35e0bbe5460b2afc2be3",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/37c4195552b9535590ee35e0bbe5460b2afc2be3"
        },
        "date": 1780713536653,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 573,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 797,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "00cfb440a37155581688dcc00839de8cdfbdd93e",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/00cfb440a37155581688dcc00839de8cdfbdd93e"
        },
        "date": 1780713576271,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 576,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 819,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "6c7b7575c1cb8eac740f26e02c19d7a01a12fc3f",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/6c7b7575c1cb8eac740f26e02c19d7a01a12fc3f"
        },
        "date": 1780715885346,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 568,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 801,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7b65834bb38476da5b0d14ad60c56d0976dde7ad",
          "message": "[anneal][release] Publish Nix-built toolchain archives",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3441/commits/7b65834bb38476da5b0d14ad60c56d0976dde7ad"
        },
        "date": 1780715896208,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 597,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 802,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "0135a80656f2d09324765c41d63edf99f009ac96",
          "message": "[anneal][v2] Add pinned charon_lib dependency",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/0135a80656f2d09324765c41d63edf99f009ac96"
        },
        "date": 1780715905077,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 608,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 813,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f0ac12e96d19609ccd7a396bf61034b928aa82e7",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/f0ac12e96d19609ccd7a396bf61034b928aa82e7"
        },
        "date": 1780715920865,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 575,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 807,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "cbc23ce569b19a1ad2c83077534b7f97642ebc12",
          "message": "[anneal][v2] Add Cargo dependencies",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/cbc23ce569b19a1ad2c83077534b7f97642ebc12"
        },
        "date": 1780715928233,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 556,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 820,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "99d70d3e2720a89b0eb0ef05d91ea31a2efcfb13",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/99d70d3e2720a89b0eb0ef05d91ea31a2efcfb13"
        },
        "date": 1780715930748,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 587,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 839,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d8a3f05e82e4669e13ceb907a581a3c9b4236bf4",
          "message": "[anneal][v2][exocrate] Add install fixup hook",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3436/commits/d8a3f05e82e4669e13ceb907a581a3c9b4236bf4"
        },
        "date": 1780716035604,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 600,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 948,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "f6938c0dd02c2f2b0a5806d0fb04d425fcd9342e",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/f6938c0dd02c2f2b0a5806d0fb04d425fcd9342e"
        },
        "date": 1780717811216,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 608,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 831,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2a71cc0a657d03771178c350473b1f182ee498e5",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/2a71cc0a657d03771178c350473b1f182ee498e5"
        },
        "date": 1780717976843,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 585,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 803,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "47d907d6fa27610a0900f075c0bec879777107a9",
          "message": "[anneal] Move setup and CI onto Nix archive",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3438/commits/47d907d6fa27610a0900f075c0bec879777107a9"
        },
        "date": 1780718081832,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 608,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 817,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "8b2c02386b63cbb7d036de14575f314c8faac96c",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/8b2c02386b63cbb7d036de14575f314c8faac96c"
        },
        "date": 1780718090478,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 566,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 787,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "69f2632b55b2a42e78d52db9b8eda488d90cdd4e",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/69f2632b55b2a42e78d52db9b8eda488d90cdd4e"
        },
        "date": 1780718143375,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 578,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 914,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "2f8bc3f5b8a7a82de3a175b3735f1b615d70f3af",
          "message": "[anneal][release] Add exocrate archive metadata helpers",
          "timestamp": "2026-06-05T22:00:32Z",
          "url": "https://github.com/google/zerocopy/pull/3440/commits/2f8bc3f5b8a7a82de3a175b3735f1b615d70f3af"
        },
        "date": 1780718275178,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 577,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 790,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "352e0bfd35058cc2b04d433613e016ab4db51664",
          "message": "[anneal][release] Add exocrate archive metadata helpers",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3440/commits/352e0bfd35058cc2b04d433613e016ab4db51664"
        },
        "date": 1780721664201,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 500,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 735,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c34277bb4c0a5e7f84a9b166c4babe761d16b333",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/c34277bb4c0a5e7f84a9b166c4babe761d16b333"
        },
        "date": 1780721740854,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 606,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 820,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "c5ea83e45ab005604f61a6931b9da017987e02b3",
          "message": "[CI] Bump the all-actions group across 1 directory with 15 updates",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3442/commits/c5ea83e45ab005604f61a6931b9da017987e02b3"
        },
        "date": 1780723303142,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 604,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 814,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "efc62daca15f92b53b9d40b498c0ec3d04d6844e",
          "message": "[anneal][v2] Add pinned charon_lib dependency",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/efc62daca15f92b53b9d40b498c0ec3d04d6844e"
        },
        "date": 1780723616371,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 594,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 799,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "bcd9f3ecc23f1a5eca4143ff7c246331b73b6ecc",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/bcd9f3ecc23f1a5eca4143ff7c246331b73b6ecc"
        },
        "date": 1780723692841,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 449,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 725,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "1f43ec33c3c95d6ab6d76be7f48b878fb5047dce",
          "message": "[anneal][v2][exocrate] Add install fixup hook",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3436/commits/1f43ec33c3c95d6ab6d76be7f48b878fb5047dce"
        },
        "date": 1780723740465,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 561,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 848,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "caa2f88191d4411bd2c026ff1367a6341f94a711",
          "message": "[anneal][release] Publish Nix-built toolchain archives",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3441/commits/caa2f88191d4411bd2c026ff1367a6341f94a711"
        },
        "date": 1780723780497,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 562,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 778,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d49f8f0c162401735b6393cc5733103e5e318f00",
          "message": "[anneal][v2] Add Cargo dependencies",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/d49f8f0c162401735b6393cc5733103e5e318f00"
        },
        "date": 1780723790081,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 596,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 811,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a34ef3f76041e27609fb34c311eaa481946900d5",
          "message": "[anneal][v2] Add scanner module to map workspace packages to AnnealArtifacts",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3402/commits/a34ef3f76041e27609fb34c311eaa481946900d5"
        },
        "date": 1780723825998,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 595,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 805,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "407f096134e46622dd35159b7bf5d266e3088a71",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/407f096134e46622dd35159b7bf5d266e3088a71"
        },
        "date": 1780723835743,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 623,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 835,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "084eff282c97b1350d6f7e2404da40703abb4443",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/084eff282c97b1350d6f7e2404da40703abb4443"
        },
        "date": 1780723836690,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 580,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 834,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a4f11d7870760b8c576c741182d644e534650405",
          "message": "[anneal][v2] Add exocrate toolchain setup and Toolchain resolver",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3400/commits/a4f11d7870760b8c576c741182d644e534650405"
        },
        "date": 1780723903725,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 588,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 929,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "b0ef58ac14b0b2560831374440f354351f861c83",
          "message": "[anneal][v2] Add Cargo workspace resolution and target resolution logic",
          "timestamp": "2026-06-06T04:22:48Z",
          "url": "https://github.com/google/zerocopy/pull/3401/commits/b0ef58ac14b0b2560831374440f354351f861c83"
        },
        "date": 1780724122958,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 566,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 878,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d8aa61be1782681521656903bf880a7c3a8678d5",
          "message": "[anneal][v2] Add Cargo dependencies",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3398/commits/d8aa61be1782681521656903bf880a7c3a8678d5"
        },
        "date": 1780792601108,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 578,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 723,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "344aa64cafe0fdb9f7ba493d1cea636233d78387",
          "message": "[anneal][release] Publish Nix-built toolchain archives",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3441/commits/344aa64cafe0fdb9f7ba493d1cea636233d78387"
        },
        "date": 1780792612567,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 569,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 738,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "a27ecdefec86148bb43f9cfe5c0e1c9517ef413a",
          "message": "[anneal][v2] Add DiagnosticMapper to map compiler errors back to Rust source code",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3403/commits/a27ecdefec86148bb43f9cfe5c0e1c9517ef413a"
        },
        "date": 1780792976164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 448,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 579,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "ede12abefcf4bdc0e9a31daec5c664b8ae8d0e76",
          "message": "[anneal][v2] Add pinned charon_lib dependency",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3418/commits/ede12abefcf4bdc0e9a31daec5c664b8ae8d0e76"
        },
        "date": 1780793120546,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 558,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 710,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "7a481b39546744bf5452a9d2d132974f31dfe2a3",
          "message": "[anneal][v2] Add charon execution engine, expand command CLI, and integration tests",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3404/commits/7a481b39546744bf5452a9d2d132974f31dfe2a3"
        },
        "date": 1780793123784,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 550,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 696,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "03d57dde65aa9e9baf736af6ef65727fabbb0b29",
          "message": "[anneal][v2] Add utility functions: environment helpers and DirLock",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3399/commits/03d57dde65aa9e9baf736af6ef65727fabbb0b29"
        },
        "date": 1780793126867,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 564,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 715,
            "unit": "seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "name": "google",
            "username": "google"
          },
          "committer": {
            "name": "google",
            "username": "google"
          },
          "id": "d9027184e0ac64bcb7ba9a366a120bc663540c65",
          "message": "[anneal][v2] Implement out-of-tree dependency chasing for expand command",
          "timestamp": "2026-06-06T18:05:15Z",
          "url": "https://github.com/google/zerocopy/pull/3405/commits/d9027184e0ac64bcb7ba9a366a120bc663540c65"
        },
        "date": 1780793137315,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Test Time",
            "value": 542,
            "unit": "seconds"
          },
          {
            "name": "Total CI Duration (All Steps)",
            "value": 730,
            "unit": "seconds"
          }
        ]
      }
    ]
  }
}