window.BENCHMARK_DATA = {
  "lastUpdate": 1776342514481,
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
      }
    ]
  }
}