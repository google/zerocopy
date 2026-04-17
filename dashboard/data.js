window.BENCHMARK_DATA = {
  "lastUpdate": 1776416284984,
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
      }
    ]
  }
}