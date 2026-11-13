#!/usr/bin/env python3
import json, os, shutil, subprocess
from pathlib import Path

RUSTC = "rustc"
OUT_DIR = Path(".")

TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

work = OUT_DIR / "tmp/t9_work"
if work.exists():
    shutil.rmtree(work)
work.mkdir(parents=True)

bin_src = work / "main.rs"
bin_src.write_text('fn main() { println!("hello {}", std::env::consts::ARCH); }\n')

lib_src = work / "lib.rs"
lib_src.write_text('#[no_mangle] pub extern "C" fn exported_api(x: u32) -> u32 { x + 1 }\npub fn rust_api(x: u32) -> u32 { x + 2 }\n')

pm_src = work / "pm.rs"
pm_src.write_text('extern crate proc_macro;\nuse proc_macro::TokenStream;\n#[proc_macro]\npub fn my_macro(input: TokenStream) -> TokenStream { input }\n')

link_args_matrix = {}
for t in TARGETS:
    link_args_matrix[t] = {}
    t_dir = work / t
    t_dir.mkdir()
    for ctype, src in [("bin", bin_src), ("cdylib", lib_src), ("dylib", lib_src), ("proc-macro", pm_src)]:
        if ctype == "proc-macro" and t != "x86_64-unknown-linux-gnu":
            # Also test proc-macro on target where proc_macro rlib exists
            pass
        cmd = [
            RUSTC, "+1.99.1", "--target", t, f"--crate-type={ctype}",
            "--print", "link-args", "-C", "opt-level=2",
            "-C", "linker=/bin/true", str(src), "--out-dir", str(t_dir)
        ]
        # On windows-gnu, raw-dylib in std calls dlltool unless linker flavor is lld or we provide a dummy dlltool
        if t == "x86_64-pc-windows-gnu":
            dummy_dlltool = work / "dummy_dlltool.sh"
            dummy_dlltool.write_text("#!/bin/sh\n# create empty archive at -l arg\nwhile [ $# -gt 0 ]; do\n  if [ \"$1\" = \"-l\" ]; then\n    printf '!<arch>\\n' > \"$2\"\n    shift 2\n  else\n    shift\n  fi\ndone\n")
            dummy_dlltool.chmod(0o755)
            cmd.extend(["-C", f"dlltool={dummy_dlltool}"])
        res = subprocess.run(cmd, text=True, capture_output=True)
        link_args_matrix[t][ctype] = {
            "returncode": res.returncode,
            "stdout": res.stdout.strip(),
            "stderr": res.stderr.strip()[:500],
        }
        print(f"{t} [{ctype}]: rc={res.returncode}, len={len(res.stdout.strip())}")

(OUT_DIR / "t9_link_args_matrix.json").write_text(json.dumps(link_args_matrix, indent=2))
print("Saved t9_link_args_matrix.json")
