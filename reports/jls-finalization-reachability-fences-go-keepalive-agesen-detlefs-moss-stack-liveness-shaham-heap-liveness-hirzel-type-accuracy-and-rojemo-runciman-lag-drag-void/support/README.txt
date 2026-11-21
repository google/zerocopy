Support material for REPORT.md (text only).

go/early.go        Go probe: an object wrapping a pipe write descriptor, released by
                   runtime.AddCleanup or runtime.SetFinalizer; a function reads the
                   descriptor (last use of the object), forces GC, then writes.
                   Usage: go run early.go <cleanup|finalizer> <nofence|keepalive> <trials>
go/output.txt      Raw output of the default and "-gcflags='all=-N -l'" builds.
go/asm_amd64.txt   Instruction listing (go build -gcflags=-S) of useNoFence and
                   useKeepAlive, pseudo-instructions retained, source positions elided.
java/EarlyReclaim.java  Java probe: a Cleaner-registered object; an instance method
                   reads this.idx (last use of this), forces GC, then checks whether
                   the cleaning action already ran; optional reachabilityFence(this).
                   Usage: java EarlyReclaim <nofence|fence> <trials>
java/output.txt    Raw output for -Xint, C1 -Xcomp, C2 -Xcomp, default tiered, and a
                   -XX:+PrintCompilation run (filtered). The JVM vendor build suffix in
                   the version string is redacted as VENDOR-BUILD.
