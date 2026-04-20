window.BENCHMARK_DATA = {
  "lastUpdate": 1776675560707,
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
      }
    ]
  }
}