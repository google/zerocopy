#!/usr/bin/env python3
"""Fixed readelf library metadata reads only; no ldd/loader/image execution."""
import sys
sys.dont_write_bytecode = True
from inspect_static import capture

for arch, prefix in [("aarch64", "/lib/aarch64-linux-gnu"),
                     ("x86_64", "/usr/x86_64-linux-gnu/lib")]:
    loader = "ld-linux-aarch64.so.1" if arch == "aarch64" else "ld-linux-x86-64.so.2"
    for name in [loader, "libc.so.6", "libgcc_s.so.1"]:
        capture(arch + "-library-" + name.replace(".", "-"),
                ["/usr/bin/readelf", "-h", "-d", "--version-info", prefix + "/" + name])
